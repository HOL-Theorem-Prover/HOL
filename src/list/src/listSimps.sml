structure listSimps :> listSimps =
struct

open HolKernel Parse basicHol90Lib simpLib listTheory;
infix THEN THENQC;

val MAP_EQ_NIL = prove(
  (--`!(l:'a list) (f:'a->'b). (MAP f l = []) = (l = [])`--),
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN
  REWRITE_TAC [MAP, NOT_CONS_NIL]);

val quant_CONV = RAND_CONV o ABS_CONV
val lhs_CONV   = RATOR_CONV o RAND_CONV
val gMAP_EQ_NIL =
  CONV_RULE (quant_CONV (quant_CONV (lhs_CONV (REWR_CONV EQ_SYM_EQ))))
            MAP_EQ_NIL;

(*---------------------------------------------------------------------------
        For the simplifier.
 ---------------------------------------------------------------------------*)
val list_ss = rewrites 
       [APPEND, EL, EVERY_DEF, FLAT, HD, LENGTH, MAP, MAP2, NULL_DEF, SUM, TL,
        APPEND_ASSOC, CONS, CONS_11, LENGTH_APPEND, LENGTH_MAP, MAP_APPEND,
        NOT_CONS_NIL, NOT_NIL_CONS, MAP_EQ_NIL, gMAP_EQ_NIL, APPEND_NIL,
        CONS_ACYCLIC, list_case_def, APPEND_eq_NIL];


(*---------------------------------------------------------------------------
     For computeLib.
 ---------------------------------------------------------------------------*)
local 
  val MEM_IF = prove(Term 
       `!(x:'a) h t. MEM x (h::t) = if x=h then T else MEM x t`,
       REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MEM])
  val EXISTS_IF = prove(Term
       `!P (h:'a) t. EXISTS P (h::t) = if P h then T else EXISTS P t`,
       REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [EXISTS_DEF])
  val EVERY_IF = prove(Term
     `!P (h:'a) t. EVERY P (h::t) = if P h then EVERY P t else F`,
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [EVERY_DEF])
  val MEM_DEF'    = CONJ (CONJUNCT1 MEM) MEM_IF
  val EXISTS_DEF' = CONJ (CONJUNCT1 EXISTS_DEF) EXISTS_IF
  val EVERY_DEF' = CONJ (CONJUNCT1  EVERY_DEF) EVERY_IF

in
 val list_rws = computeLib.add_thms
     [ APPEND,APPEND_NIL, FLAT, HD, TL, LENGTH, MAP, MAP2,
       NULL_DEF, CONS_11, NOT_CONS_NIL, NOT_NIL_CONS,
       MEM_DEF', EXISTS_DEF', EVERY_DEF',
       FILTER, FOLDR, FOLDL, EL_compute,
       computeLib.lazyfy_thm list_case_compute]
end;

end (* struct *)

