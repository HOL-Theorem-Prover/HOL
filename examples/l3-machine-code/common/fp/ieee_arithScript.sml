open HolKernel boolLib bossLib
open lcsymtacs realLib wordsLib

val () = new_theory "ieee_arith"

infix \\
val op \\ = op THEN;

val rsimp = ASM_SIMP_TAC (srw_ss()++realSimps.REAL_ARITH_ss)
val rrw = SRW_TAC [boolSimps.LET_ss, realSimps.REAL_ARITH_ss]

(* ------------------------------------------------------------------------
   Some arithmetic theorems
   ------------------------------------------------------------------------ *)

(* |- !n. 0 < 2 pow n *)
val zero_lt_twopow = Theory.save_thm("zero_lt_twopow",
   realTheory.REAL_POW_LT
   |> Q.SPEC `2`
   |> SIMP_RULE (srw_ss()) []
   )

(* |- !n. 0 <= 2 pow n *)
val zero_le_twopow = Theory.save_thm("zero_le_twopow",
   MATCH_MP realTheory.REAL_LT_IMP_LE (Drule.SPEC_ALL zero_lt_twopow)
   |> GEN_ALL
   )

(* |- !n. 2 pow n <> 0 *)
val zero_neq_twopow = Theory.save_thm("zero_neq_twopow",
   realTheory.POW_ZERO
   |> Q.SPECL [`n`, `2`]
   |> SIMP_RULE (srw_ss()) []
   |> GEN_ALL
   )

val () = bossLib.export_rewrites
           ["zero_lt_twopow", "zero_le_twopow", "zero_neq_twopow"]

val zero_le_pos_div_twopow = Q.store_thm("zero_le_pos_div_twopow",
   `!m n. 0 <= &m / 2 pow n`,
   rw [realTheory.REAL_LE_DIV, realTheory.REAL_LT_IMP_LE])

val div_eq0 = Q.store_thm("div_eq0",
   `!a b. 0 < b ==> ((a / b = 0) = (a = 0))`,
   rw [realTheory.REAL_EQ_LDIV_EQ])

val () = bossLib.export_rewrites ["zero_le_pos_div_twopow", "div_eq0"]

(* !b. 2 <= 2 ** b <=> 1 <= b *)
val exp_ge2 = Theory.save_thm("exp_ge2",
  logrootTheory.LE_EXP_ISO
  |> Q.SPECL [`2`, `1`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  )

(* !b. 4 <= 2 ** b <=> 2 <= b *)
val exp_ge4 = Theory.save_thm("exp_ge4",
  logrootTheory.LE_EXP_ISO
  |> Q.SPECL [`2`, `2`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  )

val exp_gt2 = Theory.save_thm("exp_gt2",
  logrootTheory.LT_EXP_ISO
  |> Q.SPECL [`2`, `1`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  )

val () = bossLib.export_rewrites ["exp_ge2", "exp_gt2"]

(* !n x u. (x / 2 pow n = u / 2 pow n) <=> (x = u) *)
val div_twopow = Theory.save_thm("div_twopow",
   realTheory.eq_rat
   |> Q.INST [`y` |-> `2 pow n`, `v` |-> `2 pow n`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`u`, `x`, `n`]
   )

val div_le = Q.store_thm("div_le",
   `!a b c. 0r < a ==> (b / a <= c / a = b <= c)`,
   metis_tac [realTheory.REAL_LE_LMUL, realTheory.REAL_DIV_RMUL,
              realTheory.REAL_POS_NZ, realTheory.REAL_MUL_COMM]
   )

val tac =
   NTAC 2 strip_tac
   \\ Cases_on `n <= 2`
   >- (`(n = 1) \/ (n = 2)` by decide_tac \\ rw [])
   \\ `2 < n` by decide_tac
   \\ lrw []

val two_mod_not_one = Q.store_thm("two_mod_not_one",
   `!n. 0 < n ==> 2 MOD n <> 1`, tac)

val two_mod_eq_zero = Q.store_thm("two_mod_eq_zero",
   `!n. 0 < n ==> ((2 MOD n = 0) = (n = 1) \/ (n = 2))`,
   tac
   )

(* |- !c a. c <> 0 ==> (c * a / c = a) *)
val mul_cancel = Theory.save_thm("mul_cancel",
   realTheory.REAL_DIV_LMUL_CANCEL
   |> Drule.SPEC_ALL
   |> Q.INST [`b` |-> `1`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`c`, `a`]
   )

val ge2 = Q.store_thm("ge2",
   `dimindex(:'a) <> 1 ==> 2 <= dimindex (:'a)`,
   rw [DECIDE ``0 < a /\ a <> 1 ==> 2n <= a``])

val ge2b = Q.store_thm("ge2b",
   `!n. 2n <= n ==> 1 <= 2 ** (n - 1) - 1`,
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.EXP_ADD, DECIDE ``0 < n ==> 1n <= 2 * n - 1``])

val ge2c = Q.store_thm("ge2c",
   `!n m. 1r <= n /\ 2 < m ==> 2 < n * m`,
   rrw [GSYM realTheory.REAL_LT_LDIV_EQ]
   \\ `2r / m < 1` by (match_mp_tac realTheory.REAL_LT_1 \\ simp [])
   \\ METIS_TAC [realTheory.REAL_LTE_TRANS]
   )

val ge1_pow = Q.store_thm("ge1_pow",
   `!a b. 1 <= a /\ 1n <= b ==> a <= a pow b`,
   Induct_on `b`
   \\ rw [realTheory.pow]
   \\ once_rewrite_tac [realTheory.REAL_MUL_COMM]
   \\ `0r < a /\ a <> 0`
   by METIS_TAC [realLib.REAL_ARITH ``1 <= a ==> 0r < a``,
                 realTheory.REAL_POS_NZ]
   \\ simp [GSYM realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_DIV_REFL]
   \\ Cases_on `b = 0`
   \\ simp []
   \\ `1 <= b` by decide_tac
   \\ metis_tac [realTheory.REAL_LE_TRANS]
   )

(* |- !n x. 1 < x /\ 1 < n ==> x < x pow n *)
val gt1_pow = Theory.save_thm("gt1_pow",
   realTheory.REAL_POW_MONO_LT
   |> Q.SPEC `1`
   |> REWRITE_RULE [realTheory.POW_1]
   )

(* |- !a b. 2 <= a /\ 1 <= b ==> 2 <= a * b *)
val prod_ge2 = Theory.save_thm("prod_ge2",
   realTheory.REAL_LE_MUL2
   |> Q.SPECL [`2`, `a`, `1`, `b`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`b`, `a`]
   )

val le1 = Q.store_thm("le1",
   `!x y. 0 < y /\ x <= y ==> x / y <= 1r`,
   REPEAT STRIP_TAC
   \\ Cases_on `x = y`
   \\ ASM_SIMP_TAC bool_ss
        [realTheory.REAL_LE_REFL, realTheory.REAL_DIV_REFL,
         realTheory.REAL_POS_NZ]
   \\ ASM_SIMP_TAC bool_ss [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_MUL_LID]
   )

val le2 = Q.store_thm("le2",
   `!n m. 2r <= n /\ 2 <= m ==> 2 <= n * m`,
   rrw [prod_ge2]
   )

val ge4 = Q.store_thm("ge4",
   `!n. n <> 0 ==> 4 <= 2 EXP n * 2`,
   Cases
   \\ simp [arithmeticTheory.EXP]
   )

val ge2d = Q.store_thm("ge2d",
   `!n m. 2r <= n /\ 2 <= m ==> 2 < n * m`,
   rrw [GSYM realTheory.REAL_LT_LDIV_EQ]
   \\ `2r / m <= 1` by (match_mp_tac le1 \\ rsimp [])
   \\ imp_res_tac (realLib.REAL_ARITH ``a <= 1 ==> a < 2r``)
   \\ METIS_TAC [realTheory.REAL_LTE_TRANS]
   )

(* |- !b. 0 < w2n b <=> b <> 0w *)
val word_lt0 = Theory.save_thm("word_lt0",
   wordsTheory.WORD_LO
   |> Q.SPEC `0w`
   |> REWRITE_RULE [wordsTheory.word_0_n2w, wordsTheory.WORD_LO_word_0]
   |> GSYM
   )

val word_ge1 = Q.store_thm("word_ge1",
   `!x. x <> 0w ==> 1 <= w2n x`,
   simp [GSYM word_lt0]
   )

val not_max_suc_lt_dimword = Q.store_thm("not_max_suc_lt_dimword",
   `!a:'a word. a <> -1w ==> w2n a + 1 < 2 ** dimindex(:'a)`,
   Cases
   \\ lrw [wordsTheory.word_eq_n2w, bitTheory.MOD_2EXP_MAX_def,
           bitTheory.MOD_2EXP_def, GSYM wordsTheory.dimword_def]
   )

(* |- !a. a <> 0w ==> 2 <= 2 pow w2n a *)
val pow_ge2 = Theory.save_thm("pow_ge2",
   ge1_pow
   |> Q.SPECL [`2`, `w2n (a:'w word)`]
   |> SIMP_RULE (srw_ss()) [DECIDE ``1n <= n = 0 < n``, word_lt0]
   |> GEN_ALL
   )

val mult_id = Q.store_thm("mult_id",
  `!a b. 1 < a ==> ((a * b = a) = (b = 1n))`,
  Induct_on `b`
  \\ lrw [arithmeticTheory.MULT_CLAUSES]
  )

(* |- !x y. 1 <= y /\ 0 < x ==> x <= x * y *)
val le_mult = Theory.save_thm("le_mult",
   realTheory.REAL_LE_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 <= y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM]
   |> Q.GENL [`y`, `x`]
   )

(* |- !x y. x < 1 /\ 0 < y ==> y * x < y *)
val lt_mult = Theory.save_thm("lt_mult",
   realTheory.REAL_LT_RDIV_EQ
   |> Q.SPECL [`x`, `y`, `y`]
   |> Q.DISCH `x < 1`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM]
   |> Q.GENL [`y`, `x`]
   )

(*  |- !x y. 1 < y /\ 0 < x ==> x < y * x  *)
val gt_mult = Theory.save_thm("gt_mult",
   realTheory.REAL_LT_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 < y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> Q.GENL [`y`, `x`]
   )

val exp_id = Q.store_thm("exp_id",
  `!a b. 1 < a ==> ((a EXP b = a) = (b = 1))`,
  REPEAT strip_tac
  \\ Cases_on `b = 0`
  >- lrw [arithmeticTheory.EXP]
  \\ Cases_on `b = 1`
  >- lrw [arithmeticTheory.EXP]
  \\ `1 < b` by decide_tac
  \\ imp_res_tac arithmeticTheory.LESS_ADD
  \\ pop_assum kall_tac
  \\ pop_assum (SUBST1_TAC o REWRITE_RULE [GSYM arithmeticTheory.ADD1] o SYM)
  \\ lrw [arithmeticTheory.EXP, mult_id])

val sub_rat_same_base = Q.store_thm("sub_rat_same_base",
   `!a b d. 0 < d ==> (a / d - b / d = (a - b) / d)`,
   rrw [realTheory.REAL_EQ_RDIV_EQ, realTheory.REAL_SUB_RDISTRIB,
        realTheory.REAL_DIV_RMUL]
   )

(* |- !x. 0 <= x ==> (abs x = x) *)
val gt0_abs = Theory.save_thm("gt0_abs",
   realTheory.ABS_REFL
   |> Q.SPEC `x`
   |> Q.DISCH `0 <= x`
   |> SIMP_RULE bool_ss []
   |> Drule.GEN_ALL
   )

(*
(* !z x y. 0 <> z ==> ((x = y) <=> (x * z = y * z)) *)
val mul_into = Theory.save_thm("mul_into",
   realTheory.REAL_EQ_RMUL
   |> Drule.SPEC_ALL
   |> Q.DISCH `z <> 0`
   |> SIMP_RULE std_ss []
   |> Conv.GSYM
   |> Q.GENL [`y`, `x`, `z`]
   )
*)

(* ------------------------------------------------------------------------ *)

val () = export_theory ()

