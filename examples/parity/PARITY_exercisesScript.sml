open HolKernel Parse boolLib bossLib

open PARITYTheory

val _ = new_theory "PARITY_exercises"

(* Exercise 1 *)
val RESET_REG_def = Define`
  RESET_REG(reset,inp,out) =
    (!t. reset t ==> (out t = T)) /\
    (!t. out (t + 1) = if reset t \/ reset (t + 1) then T else inp t)
`

val RESET_REG_IMP_def = Define`
  RESET_REG_IMP (reset,inp,out) =
   ?ro1 ro2 mo.
      MUX(reset,reset,ro1,mo) /\
      REG(reset,ro1) /\
      REG(inp,ro2) /\
      MUX(mo,mo,ro2,out)
`;

(* there are no loops in the implementation so simple rewriting is enough to prove the goal.
   PROVE_TAC is used to prove the final goal, which is of the form
      (p ∨ q) ∨ r ⇔ (q ∨ p) ∨ r
*)
val EX1_CORRECTNESS = store_thm(
  "EX1_CORRECTNESS",
  ``RESET_REG_IMP(reset,inp,out) ==>
    RESET_REG(reset,inp,out)``,
  SRW_TAC [][RESET_REG_IMP_def, RESET_REG_def, MUX_def, REG_def] THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val _ = export_theory()
