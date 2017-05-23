(*---------------------------------------------------------------------------*
 * The "imperative" library. This provides a collection of proof tactics     *
 * that are called upon by imperativeTheory                                  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure imperativeLib :> imperativeLib =
struct

open HolKernel Parse boolLib bossLib ptopTheory ;

fun APPLY_DEFINITIONS_TO_THEOREM definitions th = 
	(
		BETA_RULE
		(
			GEN_ALL
			(
				PURE_ONCE_REWRITE_RULE definitions th
			)
		)
	)
;

fun APPLY_DEFINITIONS_TAC definitions = 
	(PURE_ONCE_REWRITE_TAC definitions )
	THEN
		(REPEAT GEN_TAC)	
	THEN
		(BETA_TAC)
;

(*
val REFINEMENT_RATOR = rator(rator(``u [=. v``));

val REFINEMENT_NOT_RATOR = rator(rator(``u [<>. v``));
*)

val REFINEMENT_RATOR = ``$[=.``;

val REFINEMENT_NOT_RATOR = ``$[<>.``;

fun REFINEMENT_RULE th = APPLY_DEFINITIONS_TO_THEOREM [ptopTheory.bRefinement_def,ptopTheory.bRefinementNot_def] th ;

val REFINEMENT_TAC = APPLY_DEFINITIONS_TAC [ptopTheory.bRefinement_def, ptopTheory.bRefinementNot_def];


fun SWAPLR_RULE th =(PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] th);

fun EXHAUSTIVELY x = 
	(REPEAT (CHANGED_TAC x))
;

val REP_EVAL_TAC = 
	(EXHAUSTIVELY EVAL_TAC)
;

fun USE_CONTEXT (asl:term list) (th:thm) =   
	if (null asl) then th else (UNDISCH (USE_CONTEXT (tl(asl)) th))
;

fun VSUB (v:term) (e:term) (th:thm) =
	USE_CONTEXT (hyp th) (SPEC e (GEN v (DISCH_ALL th)))
;

fun MAKE_IT_SO (th:thm) = 
	((SUBST_TAC [(VSUB ``v:bool`` (concl th) PTOP_ACCEPT_IN_PLACE)]) THEN EVAL_TAC)
;

fun MAKE_IT_NO (th:thm)  = 
	if(is_neg(concl th)) then
		((SUBST_TAC [(VSUB ``v:bool`` (dest_neg(concl th)) PTOP_REJECT_IN_PLACE)]) THEN EVAL_TAC)
	else
		((SUBST_TAC [(VSUB ``v:bool`` (mk_neg(concl th)) PTOP_REJECT_IN_PLACE)]) THEN EVAL_TAC)
;

fun EVAL_FOR_STATEVARS valList =
	if(null valList) then 
	(
		(REPEAT DISCH_TAC) 
		THEN
		(REPEAT (FIRST_ASSUM (fn th => (CHANGED_TAC (SUBST_TAC [th]))) ))
	)
	else
	(
		(EVERY_ASSUM 
			(fn th =>	let val instance = (SPECL [(hd valList)] th) 
					in 
					( 
						(ASSUME_TAC instance) THEN 
						(UNDISCH_TAC (concl instance))	THEN
						(REP_EVAL_TAC)
 					)
					end
			)
		)
		THEN
		(
			EVAL_FOR_STATEVARS (tl valList)
		)
	)
;

fun DISTINCT_STATEVARS (boundVarAndType: term) (disjList: term) (asl : term list) =
	if( is_disj(disjList) ) then (
		let val lhsRhs = (dest_disj(disjList)) in 
			let val asm = mk_forall ( boundVarAndType, ( mk_imp ( #2(lhsRhs), (mk_neg (#1(lhsRhs)) )  )  ) ) in
				DISTINCT_STATEVARS boundVarAndType (#1(lhsRhs)) (asm :: asl)
			end
		end
	) else
		asl
;

fun DECL_NEXT_DISJLIST (boundVarAndType:term) (stateVars: term list) (disjList: term) =
	if(null stateVars) then (
		disjList
	) else (
		DECL_NEXT_DISJLIST boundVarAndType (tl stateVars) ( mk_disj ( disjList, (mk_eq ( boundVarAndType, (hd stateVars) ) ) ) )
	)
;

fun DECL_DISJLIST (boundVarAndType:term) (stateVars: term list) =
	if (null stateVars) then ( 
		mk_eq (boundVarAndType,boundVarAndType )
	) else (
		DECL_NEXT_DISJLIST boundVarAndType (tl stateVars) ( mk_eq( boundVarAndType, (hd stateVars) ) )
	)
;

fun DECL_STATEVARS (boundVarAndType : term) ( stateVars : term list) = 
	let val disjList = (DECL_DISJLIST boundVarAndType stateVars)
	in (	
		if (null stateVars) then ( 
			[]
		) else (
			DISTINCT_STATEVARS boundVarAndType disjList [ ( mk_forall (boundVarAndType,disjList) ) ]
		)
	) 
	end
;

end
