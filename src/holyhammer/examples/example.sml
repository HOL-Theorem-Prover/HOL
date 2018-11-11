(*--------------------------------------------------------------------------
  Example 1
  -------------------------------------------------------------------------- *)

load "holyHammer";
open holyHammer;
open arithmeticTheory;
val cj = ``a <= b ==> (g ** (b - a) * g ** a = g ** b)``;
(* holyhammer cj; *)
val tactic = METIS_TAC [SUB_ADD, EXP_ADD];
val th = store_thm ("EXP_NEG", cj, tactic);

(*--------------------------------------------------------------------------
  Example 2
  -------------------------------------------------------------------------- *)

load "holyHammer";
load "complexTheory";
open holyHammer;
open complexTheory;
open realTheory;
val cj = ``i * i = -1``;
(* set_timeout 60; holyhammer cj; *)
val tactic =
  METIS_TAC [IM, RE, complex_mul, complex_neg, complex_of_num, complex_of_real,
  i, pairTheory.FST, pairTheory.SND, REAL_ADD_LID, REAL_MUL_RID, REAL_MUL_RZERO,
  REAL_NEG_0, real_sub]
val thm = store_thm ("isquare", cj, tactic);
