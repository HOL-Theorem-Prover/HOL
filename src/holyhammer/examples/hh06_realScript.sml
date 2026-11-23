(* ========================================================================= *)
(* FILE          : hh06_realScript.sml                                       *)
(* DESCRIPTION   : HolyHammer examples: real numbers and analysis            *)
(* ADAPTED FROM  : Thibault Gauthier's HolyHammer demos.                     *)
(*                                                                           *)
(* Every proof below calls the hammer: each hh runs HolyHammer when the      *)
(* theory is built, so building needs a prover (see README.md).  The         *)
(* comment after each hh is the verified, minimised proof that               *)
(* HolyHammer printed when the example was written.                          *)
(* ========================================================================= *)
Theory hh06_real
Ancestors
  real transc
Libs
  realLib holyHammer

(* -------------------------------------------------------------------------
   The real-number libraries are large, spread over several theories
   (realax, real, real_sigma, transc, ...) and their naming is irregular:
   compare REAL_LE_SQUARE, POW_2_SQRT and EXP_MONO_LE.  As with natural
   numbers, linear goals belong to REAL_ARITH_TAC; the hammer is for
   everything that needs library knowledge: inverses, absolute values,
   exp/ln, trigonometry.  Facts from theories that are loaded but not
   opened come back fully qualified (realaxTheory.REAL_LE_SQUARE).
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Field and order facts
   ------------------------------------------------------------------------- *)

Theorem halve_double:
  a = b * 2 ==> b = a / 2
Proof
  hh
  (* metis_tac [REAL_DIV_OUTER_CANCEL2, REAL_MUL_LZERO, REAL_EQ_RDIV_EQ'] *)
QED

Theorem sum_one_sub:
  a + b = 1 ==> b = 1 - a
Proof
  hh
  (* metis_tac [REAL_ADD_SUB] *)
QED

Theorem inv_antimono:
  0 < x /\ x < y ==> inv y < inv x
Proof
  hh
  (* metis_tac [REAL_LT_INV2] *)
QED

Theorem inv_mul_distrib:
  x <> 0 /\ y <> 0 ==> inv (x * y) = inv x * inv y
Proof
  hh
  (* metis_tac [REAL_INV_MUL'] *)
QED

Theorem square_nonneg:
  0 <= x * x
Proof
  hh
  (* metis_tac [REAL_LE_SQUARE] *)
QED

Theorem le_mul_nonneg_right:
  x <= y /\ 0 <= z ==> x * z <= y * z
Proof
  hh
  (* metis_tac [REAL_LE_RMUL_IMP] *)
QED

(* -------------------------------------------------------------------------
   Absolute value, max: typical epsilon-management lemmas
   ------------------------------------------------------------------------- *)

Theorem abs_sub_comm:
  abs (x - y) = abs (y - x)
Proof
  hh
  (* metis_tac [ABS_SUB] *)
QED

Theorem abs_triangle:
  abs (x + y) <= abs x + abs y
Proof
  hh
  (* metis_tac [REAL_ABS_TRIANGLE] *)
QED

(* The kind of estimate that appears in every epsilon-delta proof.  The
   hammer combined six lemmas: the triangle inequality, |-y| = |y|,
   adding strict inequalities, and e + e = 2 * e. *)
Theorem abs_diff_lt_twice:
  abs x < e /\ abs y < e ==> abs (x - y) < 2 * e
Proof
  hh
  (* metis_tac [ABS_NEG, REAL_LET_TRANS, realaxTheory.REAL_POLY_NEG_CLAUSES,
                REAL_DOUBLE, REAL_LT_ADD2, ABS_TRIANGLE] *)
QED

(* A seven-lemma case analysis on which argument is the maximum. *)
Theorem max_le_abs_sum:
  max x y <= abs x + abs y
Proof
  hh
  (* metis_tac [real_sigmaTheory.REAL_MAX_REDUCE, REAL_LE_TRANS, ABS_LE,
                REAL_ABS_POS, REAL_LTE_TOTAL, REAL_LE_ADDR, REAL_LE_ADDL] *)
QED

(* -------------------------------------------------------------------------
   Exponential and logarithm
   ------------------------------------------------------------------------- *)

Theorem exp_of_sum:
  exp (x + y) = exp x * exp y
Proof
  hh
  (* metis_tac [REAL_EXP_ADD] *)
QED

Theorem exp_positive:
  0 < exp x
Proof
  hh
  (* metis_tac [EXP_POS_LT] *)
QED

Theorem exp_le_iff:
  exp x <= exp y <=> x <= y
Proof
  hh
  (* metis_tac [EXP_MONO_LE] *)
QED

Theorem exp_neg_cancel:
  exp (-x) * exp x = 1
Proof
  hh
  (* metis_tac [REAL_MUL_SYM, EXP_NEG_MUL] *)
QED

Theorem ln_of_product:
  0 < x /\ 0 < y ==> ln (x * y) = ln x + ln y
Proof
  hh
  (* metis_tac [LN_MUL] *)
QED

(* The library states this as an equivalence (EXP_LN).  The hammer
   found another route: every positive number is some exp y (EXP_TOTAL),
   and ln (exp y) = y (LN_EXP). *)
Theorem exp_ln_pos:
  0 < x ==> exp (ln x) = x
Proof
  hh
  (* metis_tac [EXP_TOTAL, LN_EXP] *)
QED

Theorem sqrt_of_square:
  0 <= x ==> sqrt (x pow 2) = x
Proof
  hh
  (* metis_tac [POW_2_SQRT] *)
QED

(* -------------------------------------------------------------------------
   Trigonometry
   ------------------------------------------------------------------------- *)

Theorem sin_cos_squares:
  sin x pow 2 + cos x pow 2 = 1
Proof
  hh
  (* metis_tac [SIN_CIRCLE] *)
QED

Theorem sin_odd:
  sin (-x) = - sin x
Proof
  hh
  (* metis_tac [SIN_NEG] *)
QED

Theorem cos_bounded:
  abs (cos x) <= 1
Proof
  hh
  (* metis_tac [COS_BOUND] *)
QED

(* -------------------------------------------------------------------------
   A derivation in small steps

   The linearisation formula cos x * cos x = (cos (2 * x) + 1) / 2 is
   too far from the library for one hammer call: the hammer fails on
   it, and also on the intermediate cos (2 * x) = 2 * (cos x * cos x) - 1.
   Following tip 3 of README.md, split the derivation into steps.  Each
   step is either library knowledge, which the hammer finds, or algebra,
   which REAL_ARITH_TAC does.
   ------------------------------------------------------------------------- *)

(* Library knowledge: the addition formula, with 2 * x = x + x. *)
Theorem cos_double_expand:
  cos (2 * x) = cos x * cos x - sin x * sin x
Proof
  hh
  (* metis_tac [COS_ADD, REAL_DOUBLE] *)
QED

(* Library knowledge: sin x pow 2 + cos x pow 2 = 1, rearranged. *)
Theorem sin_square:
  sin x * sin x = 1 - cos x * cos x
Proof
  hh
  (* metis_tac [REAL_EQ_SUB_LADD, POW_2, SIN_CIRCLE] *)
QED

(* Algebra: substitute and simplify.  No library facts are needed, so
   this is a job for REAL_ARITH_TAC, not for the hammer. *)
Theorem cos_double_cos:
  cos (2 * x) = 2 * (cos x * cos x) - 1
Proof
  rewrite_tac [cos_double_expand, sin_square] >> REAL_ARITH_TAC
QED

Theorem cos_square_linear:
  cos x * cos x = (cos (2 * x) + 1) / 2
Proof
  rewrite_tac [cos_double_cos] >> REAL_ARITH_TAC
QED
