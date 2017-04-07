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

fun REFINEMENT_RULE th = APPLY_DEFINITIONS_TO_THEOREM [ptopTheory.bRefinement_def] th ;

val REFINEMENT_TAC = APPLY_DEFINITIONS_TAC [ptopTheory.bRefinement_def];

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

end
