(* Arithmetic rewrites consumed by numContext.sml.  These used to be
   proved via DECIDE_TAC/RW_TAC at every load, firing the TAC_PROOF
   with-no-current-theory warning ~60 times per client theory. *)

Theory numContextContext[bare]
Ancestors
  arithmetic
Libs
  HolKernel Parse boolLib bossLib

(* Addition rewrites *)

Theorem NUM_ADD_LZERO:
  !n : num. 0 + n = n
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RZERO:
  !n : num. n + 0 = n
Proof DECIDE_TAC
QED

Theorem NUM_ADD_EQ_0:
  !m n : num. (m + n = 0) <=> (m = 0) /\ (n = 0)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_EQ_1:
  !m n : num. (m + n = 1) <=>
              ((m = 1) /\ (n = 0)) \/ ((m = 0) /\ (n = 1))
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LCANCEL:
  !n a b : num. (n + a = n + b) <=> (a = b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RCANCEL:
  !n a b : num. (a + n = b + n) <=> (a = b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LR_CANCEL:
  !n a b : num. (n + a = b + n) <=> (a = b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RL_CANCEL:
  !n a b : num. (a + n = n + b) <=> (a = b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LCANCEL_LE:
  !n a b : num. (n + a <= n + b) <=> (a <= b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RCANCEL_LE:
  !n a b : num. (a + n <= b + n) <=> (a <= b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LR_CANCEL_LE:
  !n a b : num. (n + a <= b + n) <=> (a <= b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RL_CANCEL_LE:
  !n a b : num. (a + n <= n + b) <=> (a <= b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LCANCEL_LT:
  !n a b : num. (n + a < n + b) <=> (a < b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RCANCEL_LT:
  !n a b : num. (a + n < b + n) <=> (a < b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_LR_CANCEL_LT:
  !n a b : num. (n + a < b + n) <=> (a < b)
Proof DECIDE_TAC
QED

Theorem NUM_ADD_RL_CANCEL_LT:
  !n a b : num. (a + n < n + b) <=> (a < b)
Proof DECIDE_TAC
QED

(* Subtraction rewrites *)

Theorem NUM_SUB_RZERO:
  !n : num. n - 0 = n
Proof RW_TAC arith_ss []
QED

Theorem NUM_SUB_SELF:
  !n : num. n - n = 0
Proof RW_TAC arith_ss []
QED

Theorem NUM_SUB_LZERO:
  !n : num. 0 - n = 0
Proof RW_TAC arith_ss []
QED

Theorem NUM_SUB_EQ_0:
  !m n : num. (m - n = 0) <=> m <= n
Proof RW_TAC arith_ss [SUB_EQUAL_0]
QED

Theorem NUM_SUB_SUC:
  !m n : num. SUC m - SUC n = m - n
Proof RW_TAC arith_ss [SUB_MONO_EQ]
QED

Theorem NUM_LE_ADD_SUB:
  !m n : num. n <= m ==> (n + (m - n) = m)
Proof RW_TAC arith_ss []
QED

Theorem NUM_LE_SUB_ADD:
  !m n : num. n <= m ==> ((m - n) + n = m)
Proof RW_TAC arith_ss []
QED

(* Order rewrites *)

Theorem NUM_LT_0_1:
  0n < 1
Proof DECIDE_TAC
QED

Theorem NUM_LT_0_SUC:
  !n : num. 0 < SUC n
Proof DECIDE_TAC
QED

Theorem NUM_NOT_LT_0:
  !n : num. ~(n < 0)
Proof DECIDE_TAC
QED

Theorem NUM_NOT_LT_SELF:
  !n : num. ~(n < n)
Proof DECIDE_TAC
QED

Theorem NUM_LT_SUC:
  !n : num. n < SUC n
Proof DECIDE_TAC
QED

Theorem NUM_NOT_SUC_LT:
  !n : num. ~(SUC n < n)
Proof DECIDE_TAC
QED

Theorem NUM_LT_SUC_SUC:
  !m n : num. SUC m < SUC n <=> m < n
Proof DECIDE_TAC
QED

Theorem NUM_LE_0_1:
  0n <= 1
Proof DECIDE_TAC
QED

Theorem NUM_LE_0:
  !n : num. 0 <= n
Proof DECIDE_TAC
QED

Theorem NUM_LE_0_EQ:
  !n : num. (n <= 0) <=> (n = 0)
Proof DECIDE_TAC
QED

Theorem NUM_LE_SELF:
  !n : num. n <= n
Proof DECIDE_TAC
QED

Theorem NUM_LE_SUC:
  !n : num. n <= SUC n
Proof DECIDE_TAC
QED

Theorem NUM_NOT_SUC_LE:
  !n : num. ~(SUC n <= n)
Proof DECIDE_TAC
QED

Theorem NUM_LE_SUC_SUC:
  !m n : num. SUC m <= SUC n <=> m <= n
Proof DECIDE_TAC
QED

Theorem NUM_LT_IMP_LE:
  !m n : num. m < n ==> m <= n
Proof DECIDE_TAC
QED

(* Multiplication rewrites *)

Theorem NUM_MUL_L1:
  !n : num. 1 * n = n
Proof RW_TAC arith_ss []
QED

Theorem NUM_MUL_R1:
  !n : num. n * 1 = n
Proof RW_TAC arith_ss []
QED

Theorem NUM_MUL_L0:
  !n : num. 0 * n = 0
Proof RW_TAC arith_ss []
QED

Theorem NUM_MUL_R0:
  !n : num. n * 0 = 0
Proof RW_TAC arith_ss []
QED

Theorem NUM_MUL_EQ_0:
  !m n : num. (m * n = 0) <=> (m = 0) \/ (n = 0)
Proof METIS_TAC [MULT_EQ_0]
QED

Theorem NUM_MUL_EQ_1:
  !m n : num. (m * n = 1) <=> (m = 1) /\ (n = 1)
Proof METIS_TAC [MULT_EQ_1]
QED

Theorem NUM_LT_0_MUL:
  !m n : num. 0 < m * n <=> 0 < m /\ 0 < n
Proof
  Cases_on `m` THEN Cases_on `n` THEN RW_TAC arith_ss []
QED

Theorem NUM_MUL_LCANCEL:
  !n a b : num. 0 < n ==> ((n * a = n * b) <=> (a = b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_MONO_EQ, MULT_COMM]
QED

Theorem NUM_MUL_RCANCEL:
  !n a b : num. 0 < n ==> ((a * n = b * n) <=> (a = b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_MONO_EQ, MULT_COMM]
QED

Theorem NUM_MUL_LR_CANCEL:
  !n a b : num. 0 < n ==> ((n * a = b * n) <=> (a = b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_MONO_EQ, MULT_COMM]
QED

Theorem NUM_MUL_RL_CANCEL:
  !n a b : num. 0 < n ==> ((a * n = n * b) <=> (a = b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_MONO_EQ, MULT_COMM]
QED

Theorem NUM_MUL_LCANCEL_LE:
  !n a b : num. 0 < n ==> ((n * a <= n * b) <=> (a <= b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_LESS_EQ_SUC, MULT_COMM]
QED

Theorem NUM_MUL_RCANCEL_LE:
  !n a b : num. 0 < n ==> ((a * n <= b * n) <=> (a <= b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_LESS_EQ_SUC, MULT_COMM]
QED

Theorem NUM_MUL_LR_CANCEL_LE:
  !n a b : num. 0 < n ==> ((n * a <= b * n) <=> (a <= b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_LESS_EQ_SUC, MULT_COMM]
QED

Theorem NUM_MUL_RL_CANCEL_LE:
  !n a b : num. 0 < n ==> ((a * n <= n * b) <=> (a <= b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [MULT_LESS_EQ_SUC, MULT_COMM]
QED

Theorem NUM_MUL_LCANCEL_LT:
  !n a b : num. 0 < n ==> ((n * a < n * b) <=> (a < b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [LESS_MULT_MONO, MULT_COMM]
QED

Theorem NUM_MUL_RCANCEL_LT:
  !n a b : num. 0 < n ==> ((a * n < b * n) <=> (a < b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [LESS_MULT_MONO, MULT_COMM]
QED

Theorem NUM_MUL_LR_CANCEL_LT:
  !n a b : num. 0 < n ==> ((n * a < b * n) <=> (a < b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [LESS_MULT_MONO, MULT_COMM]
QED

Theorem NUM_MUL_RL_CANCEL_LT:
  !n a b : num. 0 < n ==> ((a * n < n * b) <=> (a < b))
Proof
  Cases_on `n` THEN RW_TAC arith_ss [] THEN
  PROVE_TAC [LESS_MULT_MONO, MULT_COMM]
QED

(* Exponentiation rewrites *)

Theorem NUM_EXP_R0:
  !n : num. n EXP 0 = 1
Proof RW_TAC arith_ss [EXP]
QED

Theorem NUM_EXP_R1:
  !n : num. n EXP 1 = n
Proof RW_TAC arith_ss [EXP_1]
QED

Theorem NUM_EXP_L0:
  !n : num. 0 < n ==> (0 EXP n = 0)
Proof
  Cases_on `n` THEN RW_TAC arith_ss [EXP]
QED

Theorem NUM_EXP_L1:
  !n : num. 1 EXP n = 1
Proof
  Induct THEN RW_TAC arith_ss [EXP]
QED
