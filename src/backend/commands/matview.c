/*-------------------------------------------------------------------------
 *
 * matview.c
 *	  use rewrite rules to construct matviews
 *
 * Portions Copyright (c) 1996-2011, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/commands/matview.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/heapam.h"
#include "access/xact.h"
#include "catalog/namespace.h"
#include "commands/defrem.h"
#include "commands/tablecmds.h"
#include "commands/matview.h"
#include "executor/execdesc.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "parser/analyze.h"
#include "parser/parse_relation.h"
#include "rewrite/rewriteDefine.h"
#include "rewrite/rewriteManip.h"
#include "rewrite/rewriteSupport.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"

static void checkMatViewTupleDesc(TupleDesc newdesc, TupleDesc olddesc);
static bool isMatViewOnTempTable_walker(Node *node, void *context);
// extern void getRelationDescription(StringInfo buffer, Oid relid);

/*---------------------------------------------------------------------
 * isMatViewOnTempTable
 *
 * Returns true iff any of the relations underlying this matview are
 * temporary tables.
 *---------------------------------------------------------------------
 */
static bool
isMatViewOnTempTable(Query *matViewParse)
{
	return isMatViewOnTempTable_walker((Node *) matViewParse, NULL);
}

static bool
isMatViewOnTempTable_walker(Node *node, void *context)
{
	if (node == NULL)
		return false;

	if (IsA(node, Query))
	{
		Query	   *query = (Query *) node;
		ListCell   *rtable;

		foreach(rtable, query->rtable)
		{
			RangeTblEntry *rte = lfirst(rtable);

			if (rte->rtekind == RTE_RELATION)
			{
				Relation	rel = heap_open(rte->relid, AccessShareLock);
				char		relpersistence = rel->rd_rel->relpersistence;

				heap_close(rel, AccessShareLock);
				if (relpersistence == RELPERSISTENCE_TEMP)
					return true;
			}
		}

		return query_tree_walker(query,
								 isMatViewOnTempTable_walker,
								 context,
								 QTW_IGNORE_JOINALIASES);
	}

	return expression_tree_walker(node,
								  isMatViewOnTempTable_walker,
								  context);
}

/*---------------------------------------------------------------------
 * DefineMaterializedVirtualRelation
 *
 * Create the "matview" relation. `DefineRelation' does all the work,
 * we just provide the correct arguments ... at least when we're
 * creating a matview.  If we're updating an existing matview, we have to
 * work harder.
 *---------------------------------------------------------------------
 */
static Oid
DefineMaterializedVirtualRelation(const RangeVar *relation, List *tlist, bool replace,
					  Oid namespaceId)
{
	Oid			matViewOid;
	CreateStmt *createStmt = makeNode(CreateStmt);
	List	   *attrList;
	ListCell   *t;

	/*
	 * create a list of ColumnDef nodes based on the names and types of the
	 * (non-junk) targetlist items from the matView's SELECT list.
	 */
	attrList = NIL;
	foreach(t, tlist)
	{
		TargetEntry *tle = lfirst(t);

		if (!tle->resjunk)
		{
			ColumnDef  *def = makeNode(ColumnDef);

			def->colname = pstrdup(tle->resname);
			def->typeName = makeTypeNameFromOid(exprType((Node *) tle->expr),
											 exprTypmod((Node *) tle->expr));
			def->inhcount = 0;
			def->is_local = true;
			def->is_not_null = false;
			def->is_from_type = false;
			def->storage = 0;
			def->raw_default = NULL;
			def->cooked_default = NULL;
			def->collClause = NULL;
			def->collOid = exprCollation((Node *) tle->expr);

			/*
			 * It's possible that the column is of a collatable type but the
			 * collation could not be resolved, so double-check.
			 */
			if (type_is_collatable(exprType((Node *) tle->expr)))
			{
				if (!OidIsValid(def->collOid))
					ereport(ERROR,
							(errcode(ERRCODE_INDETERMINATE_COLLATION),
							 errmsg("could not determine which collation to use for mat view column \"%s\"",
									def->colname),
							 errhint("Use the COLLATE clause to set the collation explicitly.")));
			}
			else
				Assert(!OidIsValid(def->collOid));
			def->constraints = NIL;

			attrList = lappend(attrList, def);
		}
	}

	if (attrList == NIL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
				 errmsg("mat view must have at least one column")));

	/*
	 * Check to see if we want to replace an existing mat view.
	 */
	matViewOid = get_relname_relid(relation->relname, namespaceId);

	if (OidIsValid(matViewOid) && replace)
	{
		Relation	rel;
		TupleDesc	descriptor;

		/*
		 * Yes.  Get exclusive lock on the existing mat view ...
		 */
		rel = relation_open(matViewOid, AccessExclusiveLock);

		/*
		 * Make sure it *is* a mat view, and do permissions checks.
		 */
		if (rel->rd_rel->relkind != RELKIND_MAT_VIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("\"%s\" is not a mat view",
							RelationGetRelationName(rel))));

		if (!pg_class_ownercheck(matViewOid, GetUserId()))
			aclcheck_error(ACLCHECK_NOT_OWNER, ACL_KIND_CLASS,
						   RelationGetRelationName(rel));

		/* Also check it's not in use already */
		CheckTableNotInUse(rel, "CREATE OR REPLACE MATVIEW");

		/*
		 * Due to the namespace visibility rules for temporary objects, we
		 * should only end up replacing a temporary mat view with another
		 * temporary mat view, and similarly for permanent mat views.
		 */
		Assert(relation->relpersistence == rel->rd_rel->relpersistence);

		/*
		 * Create a tuple descriptor to compare against the existing mat view, and
		 * verify that the old column list is an initial prefix of the new
		 * column list.
		 */
		descriptor = BuildDescForRelation(attrList);
		checkMatViewTupleDesc(descriptor, rel->rd_att);

		/*
		 * If new attributes have been added, we must add pg_attribute entries
		 * for them.  It is convenient (although overkill) to use the ALTER
		 * TABLE ADD COLUMN infrastructure for this.
		 */
		if (list_length(attrList) > rel->rd_att->natts)
		{
			List	   *atcmds = NIL;
			ListCell   *c;
			int			skip = rel->rd_att->natts;

			foreach(c, attrList)
			{
				AlterTableCmd *atcmd;

				if (skip > 0)
				{
					skip--;
					continue;
				}
				atcmd = makeNode(AlterTableCmd);
				atcmd->subtype = AT_AddColumnToMatView;
				atcmd->def = (Node *) lfirst(c);
				atcmds = lappend(atcmds, atcmd);
			}
			AlterTableInternal(matViewOid, atcmds, true);
		}

		/*
		 * Seems okay, so return the OID of the pre-existing mat view.
		 */
		relation_close(rel, NoLock);	/* keep the lock! */

		return matViewOid;
	}
	else
	{
		Oid			relid;

		/*
		 * now set the parameters for keys/inheritance etc. All of these are
		 * uninteresting for mat views...
		 */
		createStmt->relation = (RangeVar *) relation;
		createStmt->tableElts = attrList;
		createStmt->inhRelations = NIL;
		createStmt->constraints = NIL;
		createStmt->options = list_make1(defWithOids(false));
		createStmt->oncommit = ONCOMMIT_NOOP;
		createStmt->tablespacename = NULL;
		createStmt->if_not_exists = false;

		/*
		 * finally create the relation (this will error out if there's an
		 * existing mat view, so we don't need more code to complain if "replace"
		 * is false).
		 */
		relid = DefineRelation(createStmt, RELKIND_MAT_VIEW, InvalidOid);

		printf("matview.c 263: Defined Relation for MatView\n");
		Assert(relid != InvalidOid);
		return relid;
	}
}

/*
 * Verify that tupledesc associated with proposed new mat view definition
 * matches tupledesc of old mat view.  This is basically a cut-down version
 * of equalTupleDescs(), with code added to generate specific complaints.
 * Also, we allow the new tupledesc to have more columns than the old.
 */
static void
checkMatViewTupleDesc(TupleDesc newdesc, TupleDesc olddesc)
{
	int			i;

	if (newdesc->natts < olddesc->natts)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
				 errmsg("cannot drop columns from mat view")));
	/* we can ignore tdhasoid */

	for (i = 0; i < olddesc->natts; i++)
	{
		Form_pg_attribute newattr = newdesc->attrs[i];
		Form_pg_attribute oldattr = olddesc->attrs[i];

		/* XXX msg not right, but we don't support DROP COL on mat view anyway */
		if (newattr->attisdropped != oldattr->attisdropped)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
					 errmsg("cannot drop columns from mat view")));

		if (strcmp(NameStr(newattr->attname), NameStr(oldattr->attname)) != 0)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
				 errmsg("cannot change name of mat view column \"%s\" to \"%s\"",
						NameStr(oldattr->attname),
						NameStr(newattr->attname))));
		/* XXX would it be safe to allow atttypmod to change?  Not sure */
		if (newattr->atttypid != oldattr->atttypid ||
			newattr->atttypmod != oldattr->atttypmod)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
					 errmsg("cannot change data type of mat view column \"%s\" from %s to %s",
							NameStr(oldattr->attname),
							format_type_with_typemod(oldattr->atttypid,
													 oldattr->atttypmod),
							format_type_with_typemod(newattr->atttypid,
													 newattr->atttypmod))));
		/* We can ignore the remaining attributes of an attribute... */
	}

	/*
	 * We ignore the constraint fields.  The new mat view desc can't have any
	 * constraints, and the only ones that could be on the old mat view are
	 * defaults, which we are happy to leave in place.
	 */
}

static void
DefineMatViewRules(Oid matViewOid, Query *matViewParse, bool replace)
{
	/*
	 * Set up the ON SELECT rule.  Since the query has already been through
	 * parse analysis, we use DefineQueryRewrite() directly.
	 */
  // Rule should be changed here. But changing it causes error. Hence not done as of yet.
	DefineQueryRewrite(pstrdup(ViewSelectRuleName),
					   matViewOid,
					   NULL,
					   CMD_SELECT,
					   true,
					   replace,
					   list_make1(matViewParse));

	/*
	 * Someday: automatic ON INSERT, etc
	 */
}

/*---------------------------------------------------------------
 * UpdateRangeTableOfMatViewParse
 *
 * Update the range table of the given parsetree.
 * This update consists of adding two new entries IN THE BEGINNING
 * of the range table (otherwise the rule system will die a slow,
 * horrible and painful death, and we do not want that now, do we?)
 * one for the OLD relation and one for the NEW one (both of
 * them refer in fact to the "view" relation).
 *
 * Of course we must also increase the 'varnos' of all the Var nodes
 * by 2...
 *
 * These extra RT entries are not actually used in the query,
 * except for run-time permission checking.
 *---------------------------------------------------------------
 */
static Query *
UpdateRangeTableOfMatViewParse(Oid matViewOid, Query *matViewParse)
{
	Relation	matViewRel;
	List	   *new_rt;
	RangeTblEntry *rt_entry1,
			   *rt_entry2;

	/*
	 * Make a copy of the given parsetree.	It's not so much that we don't
	 * want to scribble on our input, it's that the parser has a bad habit of
	 * outputting multiple links to the same subtree for constructs like
	 * BETWEEN, and we mustn't have OffsetVarNodes increment the varno of a
	 * Var node twice.	copyObject will expand any multiply-referenced subtree
	 * into multiple copies.
	 */
	matViewParse = (Query *) copyObject(matViewParse);

	/* need to open the rel for addRangeTableEntryForRelation */
	matViewRel = relation_open(matViewOid, AccessShareLock);

	/*
	 * Create the 2 new range table entries and form the new range table...
	 * OLD first, then NEW....
	 */
	rt_entry1 = addRangeTableEntryForRelation(NULL, matViewRel,
											  makeAlias("old", NIL),
											  false, false);
	rt_entry2 = addRangeTableEntryForRelation(NULL, matViewRel,
											  makeAlias("new", NIL),
											  false, false);
	/* Must override addRangeTableEntry's default access-check flags */
	rt_entry1->requiredPerms = 0;
	rt_entry2->requiredPerms = 0;

	new_rt = lcons(rt_entry1, lcons(rt_entry2, matViewParse->rtable));

	matViewParse->rtable = new_rt;

	/*
	 * Now offset all var nodes by 2, and jointree RT indexes too.
	 */
	OffsetVarNodes((Node *) matViewParse, 2, 0);

	relation_close(matViewRel, AccessShareLock);

	return matViewParse;
}

/*
 * DefineMatView
 *		Execute a CREATE MATVIEW command.
 */
void
DefineMatView(MatViewStmt *stmt, const char *queryString)
{
	Query	   *matViewParse;
	Oid			matViewOid;
	Oid			namespaceId;
	RangeVar   *matView;

	/*
	 * Run parse analysis to convert the raw parse tree to a Query.  Note this
	 * also acquires sufficient locks on the source table(s).
	 *
	 * Since parse analysis scribbles on its input, copy the raw parse tree;
	 * this ensures we don't corrupt a prepared statement, for example.
	 */
	/* 
         * ListCell * lc;
	 * foreach(lc, ((SelectStmt *)(stmt -> query)) -> fromClause){
	 *   printf("From Clause: %s\n", (char *) lc -> data.ptr_value);
	 * }
         */
	// Assert(1 == 0);
	printf("matview.c 439: calling parse_analyze\n");
	matViewParse = parse_analyze((Node *) copyObject(stmt->query),
							  queryString, NULL, 0);
	printf("matview.c 442: parse_analyze call ended\n");
	/*
	 * The grammar should ensure that the result is a single SELECT Query.
	 */
	if (!IsA(matViewParse, Query) ||
		matViewParse->commandType != CMD_SELECT)
		elog(ERROR, "unexpected parse analysis result");

	/*
	 * Check for unsupported cases.  These tests are redundant with ones in
	 * DefineQueryRewrite(), but that function will complain about a bogus ON
	 * SELECT rule, and we'd rather the message complain about a view.
	 */
	if (matViewParse->intoClause != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("mat views must not contain SELECT INTO")));
	if (matViewParse->hasModifyingCTE)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
		errmsg("mat views must not contain data-modifying statements in WITH")));


	/*
	 * If a list of column names was given, run through and insert these into
	 * the actual query tree. - thomas 2000-03-08
	 */
	if (stmt->aliases != NIL)
	{
		ListCell   *alist_item = list_head(stmt->aliases);
		ListCell   *targetList;

		foreach(targetList, matViewParse->targetList)
		{
			TargetEntry *te = (TargetEntry *) lfirst(targetList);

			Assert(IsA(te, TargetEntry));
			/* junk columns don't get aliases */
			if (te->resjunk)
				continue;
			te->resname = pstrdup(strVal(lfirst(alist_item)));
			alist_item = lnext(alist_item);
			if (alist_item == NULL)
				break;			/* done assigning aliases */
		}

		if (alist_item != NULL)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("CREATE MAT VIEW specifies more column "
							"names than columns")));
	}
	printf("matview.c 492:\n");

	/* Unlogged views are not sensible. */
	if (stmt->matView->relpersistence == RELPERSISTENCE_UNLOGGED)
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
		errmsg("views cannot be unlogged because they do not have storage")));

	/*
	 * If the user didn't explicitly ask for a temporary view, check whether
	 * we need one implicitly.	We allow TEMP to be inserted automatically as
	 * long as the CREATE command is consistent with that --- no explicit
	 * schema name.
	 */

	matView = copyObject(stmt->matView);  /* don't corrupt original command */	
	printf("matview.c 508:\n");
	if (matView->relpersistence == RELPERSISTENCE_PERMANENT
		&& isMatViewOnTempTable(matViewParse))
	  {
		printf("matview.c 512: Inside\n");
		matView->relpersistence = RELPERSISTENCE_TEMP;
		printf("matview.c 512: Giving Error\n");
		ereport(NOTICE,
				(errmsg("view \"%s\" will be a temporary view",
						matView->relname)));
	}
	printf("matview.c 517:\n");
	/* Might also need to make it temporary if placed in temp schema. */
	namespaceId = RangeVarGetCreationNamespace(matView);
	RangeVarAdjustRelationPersistence(matView, namespaceId);

	/*
	 * Create the materialized view relation
	 *
	 * NOTE: if it already exists and replace is false, the xact will be
	 * aborted.
	 */
	printf("matview.c 527: Calling DefineMaterializedVirtualRelation\n");
	matViewOid = DefineMaterializedVirtualRelation(matView,
						       matViewParse->targetList,
						       stmt->replace,
												   namespaceId);

	/*Unclear bisiness begins 
	PlannedStmt * PlannedMatViewParse;
	PlannedMatViewParse = pg_plan_query(matViewParse, 0, NULL);
	printf("matview.c 532: DefineMaterializedVirtualRelation returned\n");

	QueryDesc *queryDesc = CreateQueryDesc(PlannedMatViewParse,
										   queryString,
										   GetActiveSnapshot(),
										   InvalidSnapshot,
										   None_Receiver, NULL, 0);

	queryDesc->dest = CreateDestReceiver(DestIntoRel);

	CmdType		operation;
	bool		sendTuples;
	DestReceiver *dest;
 
	operation = queryDesc->operation;
	dest = queryDesc->dest;
	sendTuples = (operation == CMD_SELECT ||
				  queryDesc->plannedstmt->hasReturning);

	if (sendTuples)
		(*dest->rStartup) (dest, operation, queryDesc->tupDesc);

	if (!ScanDirectionIsNoMovement(ForwardScanDirection))
		ExecutePlan(estate,
					queryDesc->planstate,
					operation,
					sendTuples,
					count,
					direction,
					dest);

	if (sendTuples)
		(*dest->rShutdown) (dest);

	/*Unclear bisiness ends*/ 
	/*
	 * The relation we have just created is not visible to any other commands
	 * running with the same transaction & command id. So, increment the
	 * command id counter (but do NOT pfree any memory!!!!)
	 */
	CommandCounterIncrement();

	/*
	 * The range table of 'viewParse' does not contain entries for the "OLD"
	 * and "NEW" relations. So... add them!
	 */
	// matViewParse = UpdateRangeTableOfMatViewParse(matViewOid, matViewParse);

	/*
	 * Now create the rules associated with the view.
	 */
	DefineMatViewRules(matViewOid, matViewParse, stmt->replace);
	printf("MatView defined\n");
}
