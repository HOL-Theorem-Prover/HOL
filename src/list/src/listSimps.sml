structure listSimps :> listSimps =
struct

open HolKernel Parse basicHol90Lib simpLib;
infix THEN THENQC;

val MAP_EQ_NIL = Tactical.prove(
  (--`!(l:'a list) (f:'a->'b). (MAP f l = []) = (l = [])`--),
  INDUCT_THEN listTheory.list_INDUCT ASSUME_TAC THEN
  REWRITE_TAC [listTheory.MAP, listTheory.NOT_CONS_NIL]);

val quant_CONV = RAND_CONV o ABS_CONV
val lhs_CONV   = RATOR_CONV o RAND_CONV
val gMAP_EQ_NIL =
  CONV_RULE (quant_CONV (quant_CONV (lhs_CONV (REWR_CONV EQ_SYM_EQ))))
            MAP_EQ_NIL;

val list_ss = rewrites 
  [listTheory.APPEND, listTheory.EL, listTheory.EVERY_DEF, 
   listTheory.FLAT, listTheory.HD, listTheory.LENGTH, listTheory.MAP,
   listTheory.MAP2, listTheory.NULL_DEF, listTheory.SUM, listTheory.TL,
   listTheory.APPEND_ASSOC, listTheory.CONS, listTheory.CONS_11, 
   listTheory.LENGTH_APPEND, listTheory.LENGTH_MAP, listTheory.MAP_APPEND,
   listTheory.NOT_CONS_NIL, listTheory.NOT_NIL_CONS,
   MAP_EQ_NIL, gMAP_EQ_NIL, listTheory.APPEND_NIL,listTheory.CONS_ACYCLIC,
   listTheory.list_case_def, listTheory.APPEND_eq_NIL];



end (* struct *)
