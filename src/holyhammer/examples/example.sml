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
(* set_timeout 30; holyhammer cj; *)
val tactic =
  METIS_TAC [COMPLEX_NEGNEG, COMPLEX_DIV_REFL, COMPLEX_INVINV, complex_div,
  REAL_INV1, REAL_MUL_RID, REAL_NEG_NEG, POW_2, REAL_MUL_RNEG, REAL_MUL_LZERO,
  real_div, complex_inv, REAL_10, pairTheory.CLOSED_PAIR_EQ, COMPLEX_NEG_RMUL,
  i, complex_of_num, complex_neg, REAL_ADD_RID, pairTheory.FST, complex_of_real, 
  REAL_ADD_SYM];
val thm = store_thm ("isquare", cj, tactic);
