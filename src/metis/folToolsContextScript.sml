Theory folToolsContext[bare]
Ancestors
  normalForms
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Equality and boolean lemmas for folTools.  Formerly proved as folTools    *)
(* loaded, which made those proofs sensitive to link-order-dependent         *)
(* ambient state (parser and current theory).                                *)
(* ------------------------------------------------------------------------- *)

Theorem EQ_SYMTRANS:
  !x y z. ~(x:'a = y) \/ ~(x = z) \/ (y = z)
Proof
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``x:'a = y`` THEN
  ASM_REWRITE_TAC
    [ONCE_REWRITE_RULE [boolTheory.DISJ_SYM]
       (REWRITE_RULE[] boolTheory.BOOL_CASES_AX)]
QED

Theorem EQ_COMB:
  !f g x y. ~(f:'a->'b = g) \/ ~(x = y) \/ (f x = g y)
Proof
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC ``x:'a = y`` THEN
  ASM_CASES_TAC ``f:'a->'b = g`` THEN
  ASM_REWRITE_TAC []
QED

Theorem EQ_BOOL_CONJ:
  (!x y. ~x \/ ~(x = y) \/ y) /\
  (!x y. x \/ (x = y) \/ y) /\
  (!x y. ~x \/ (x = y) \/ ~y)
Proof
  REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC ``x:bool`` THEN
  ASM_CASES_TAC ``y:bool`` THEN
  ASM_REWRITE_TAC []
QED
