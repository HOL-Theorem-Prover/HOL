(* -------------------------------------------------------------------------
   A bridging theory between integers and reals
   ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib
open intLib

local open realSimps in end

val _ = new_theory "intreal"

(* -------------------------------------------------------------------------
   Define the inclusion homomorphism real_of_int :int->real.
   ------------------------------------------------------------------------- *)

val real_of_int = Lib.with_flag (boolLib.def_suffix, "") Define
  `real_of_int i =
   if i < 0 then ~(real_of_num (Num (~i))) else real_of_num (Num i)`

val real_of_int_def = save_thm("real_of_int_def", real_of_int);

(* -------------------------------------------------------------------------
   Floor and ceiling (ints)
   ------------------------------------------------------------------------- *)

val INT_FLOOR_def = zDefine `INT_FLOOR x = LEAST_INT i. x < real_of_int (i + 1)`
val INT_CEILING_def = zDefine `INT_CEILING x = LEAST_INT i. x <= real_of_int i`

val _ = Parse.overload_on ("flr", ``INT_FLOOR``)
val _ = Parse.overload_on ("clg", ``INT_CEILING``)

(* -------------------------------------------------------------------------
   is_int
   ------------------------------------------------------------------------- *)

val is_int_def = Define `is_int (x:real) = (x = real_of_int (INT_FLOOR x))`

(* -------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------- *)

val real_of_int_monotonic = Q.store_thm("real_of_int_monotonic",
  `!i j. i < j ==> real_of_int i < real_of_int j`,
  Cases \\ Cases \\ srw_tac[][real_of_int] \\ intLib.ARITH_TAC)

val real_arch_least1 =
  realTheory.REAL_ARCH_LEAST
  |> Q.SPEC `1r`
  |> SIMP_RULE (srw_ss()) []

val Num_suc1 = intLib.ARITH_PROVE ``Num (&n + 1) = n + 1``

val lem = Q.prove( `!n. -&n <= 0r`, simp [realTheory.REAL_NEG_LE0])

val lem2 = Q.prove(
  `!n. -&(n + 1n) = -&n - 1r`,
  once_rewrite_tac [GSYM realTheory.add_ints]
  \\ simp [realTheory.real_sub]
  )

val lem3 = intLib.ARITH_PROVE ``-&n + 1 < 0i ==> (Num (&n + -1i) = (n - 1))``

val lem4 = Q.prove(
  `!n. n <> 0 ==> (-&(n - 1n) = -&n + 1r)`,
  strip_tac
  \\ Cases_on `n = 1` >- simp []
  \\ metis_tac [realTheory.REAL_SUB, realTheory.REAL_NEG_SUB,
                RealArith.REAL_ARITH ``-a + b = b - a: real``,
                DECIDE ``n <> 0 /\ n <> 1 ==> (n - 1 <> 0n)``]
  )

val lem5 = Q.prove(
  `!m n. n + 1 < m ==> -&m + 1 <= -&n - 1r`,
  REPEAT strip_tac
  \\ once_rewrite_tac [GSYM realTheory.REAL_LE_NEG]
  \\ rewrite_tac [realTheory.REAL_NEG_SUB, realTheory.REAL_NEG_ADD,
                  realTheory.REAL_SUB_RNEG]
  \\ Cases_on `m`
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD1]
  \\ REWRITE_TAC [GSYM realTheory.REAL_ADD,
                  RealArith.REAL_ARITH ``a + b + -b = a: real``]
  \\ simp []
  )

val INT_FLOOR_BOUNDS = Q.store_thm("INT_FLOOR_BOUNDS",
  `!r. real_of_int (INT_FLOOR r) <= r /\ r < real_of_int (INT_FLOOR r + 1)`,
  srw_tac[][INT_FLOOR_def, integerTheory.LEAST_INT_DEF] \\ SELECT_ELIM_TAC \\ (
  REVERSE conj_tac
  >- (srw_tac[][realTheory.REAL_NOT_LT]
      \\ pop_assum (qspec_then `x - 1` assume_tac)
      \\ full_simp_tac(srw_ss())[intLib.ARITH_PROVE ``a - 1 < a: int``])
  \\ Cases_on `0 <= r`
  >- (imp_res_tac real_arch_least1
      \\ qexists_tac `&n`
      \\ srw_tac[][real_of_int, realTheory.REAL_NOT_LT,
             REWRITE_RULE [GSYM arithmeticTheory.ADD1] Num_suc1,
             intLib.ARITH_PROVE ``~(&n + 1i < 0)``]
      >- metis_tac [lem, realTheory.REAL_LE_TRANS]
      \\ Cases_on `i'`
      \\ full_simp_tac(srw_ss())[Num_suc1]
      >| [`n' + 1 <= n` by decide_tac
          \\ metis_tac [realTheory.REAL_LE, realTheory.REAL_LE_TRANS],
          imp_res_tac
            (intLib.ARITH_PROVE ``n <> 0 /\ ~(-&n + 1i < 0) ==> (n = 1)``)
          \\ full_simp_tac(srw_ss())[],
          `1 <= n` by decide_tac
          \\ metis_tac [realTheory.REAL_LE, realTheory.REAL_LE_TRANS]
      ]
  )
  \\ imp_res_tac (RealArith.REAL_ARITH ``~(0r <= r) ==> 0 <= -r /\ r <> 0``)
  \\ imp_res_tac real_arch_least1
  \\ rev_full_simp_tac(srw_ss())[arithmeticTheory.ADD1, integerTheory.INT_NEG_ADD,
          RealArith.REAL_ARITH ``r <= 0r ==> (&(n: num) <= -r <=> r <= -&n)``,
          RealArith.REAL_ARITH ``r <= 0r ==> (-r < &n <=> -&n < r)``]
  \\ Cases_on `r = -&n`
  >| [qexists_tac `~&n`, qexists_tac `~&(SUC n)`]
  \\ rev_full_simp_tac(srw_ss())[real_of_int, integerTheory.INT_NEG_ADD]
  \\ (conj_tac
      >- (srw_tac[][lem3]
          \\ Cases_on `n`
          \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD1,
                 RealArith.REAL_ARITH ``r <= 0r /\ r <> 0 ==> r < 0``,
                 RealArith.REAL_ARITH ``a <= b - 1 ==> a < b: real``,
                 intLib.ARITH_PROVE ``-&(n + 1) + 1 < 0i <=> n <> 0``,
                 RealArith.REAL_ARITH ``r <= -1r ==> r < 0``,
                 RealArith.REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``])
      \\ srw_tac[][realTheory.REAL_NOT_LT]
      \\ Cases_on `i'`
      \\ rev_full_simp_tac(srw_ss())[lem2, lem3, lem4, arithmeticTheory.ADD1]
      \\ (intLib.ARITH_TAC ORELSE
          imp_res_tac (intLib.ARITH_PROVE ``n + 1 < m ==> (-&m + 1 < 0i)``)
          \\ metis_tac
               [realTheory.REAL_LET_TRANS, realTheory.REAL_LT_IMP_LE, lem5])
     )
  )
  )

Theorem INT_FLOOR:
  !r i. (INT_FLOOR r = i) <=> real_of_int i <= r /\ r < real_of_int (i + 1)
Proof
  REPEAT strip_tac
  \\ eq_tac
  >- metis_tac [INT_FLOOR_BOUNDS]
  \\ srw_tac[][INT_FLOOR_def, integerTheory.LEAST_INT_DEF]
  \\ SELECT_ELIM_TAC
  \\ conj_tac
  >- (
    SPOSE_NOT_THEN strip_assume_tac
    \\ res_tac
    \\ Cases_on `i`
    \\ Cases_on `i'`
    \\ full_simp_tac(srw_ss())[real_of_int, intLib.ARITH_PROVE ``~(&n + 1i < 0)``]
    >| [
      all_tac,
      Cases_on `-&n' + 1 < 0i`,
      all_tac,
      Cases_on `-&n' + 1 < 0i`,
      Cases_on `-&n + 1 < 0i`
    ]
    \\ full_simp_tac(srw_ss())[Num_suc1]
    \\ imp_res_tac realTheory.REAL_LET_TRANS
    \\ full_simp_tac(srw_ss())[integerTheory.INT_NOT_LT]
    \\ intLib.ARITH_TAC
  )
  \\ srw_tac[][]
  \\ Cases_on `i < x`
  >- res_tac
  \\ Cases_on `i = x`
  >- asm_rewrite_tac []
  \\ `x < i` by intLib.ARITH_TAC
  \\ Cases_on `i`
  \\ Cases_on `x`
  \\ full_simp_tac(srw_ss())[real_of_int]
  >| [
    Cases_on `&n + 1 < 0i`
    \\ Cases_on `&n' + 1 < 0i`,
    Cases_on `&n + 1 < 0i`
    \\ Cases_on `-&n' + 1 < 0i`,
    Cases_on `&n + 1 < 0i`,
    Cases_on `-&n + 1 < 0i`
    \\ Cases_on `-&n' + 1 < 0i`,
    Cases_on `-&n + 1 < 0i`
  ]
  \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac realTheory.REAL_LET_TRANS
  \\ full_simp_tac(srw_ss())[integerTheory.INT_NOT_LT]
  \\ intLib.ARITH_TAC
QED

val int_floor_1 = Q.prove(
  `(INT_FLOOR &n = &n) /\ (INT_FLOOR (-&n) = -&n)`,
  srw_tac[][INT_FLOOR, real_of_int] \\ intLib.ARITH_TAC)

val tac =
  imp_res_tac arithmeticTheory.DIVISION
  \\ pop_assum (qspec_then `n` assume_tac)
  \\ first_assum (qspec_then `n` assume_tac)
  \\ TRY decide_tac

val int_floor_2 = Q.prove(
  `0 < m ==> (INT_FLOOR (&n / &m) = &n / &m)`,
  strip_tac
  \\ rewrite_tac [INT_FLOOR]
  \\ srw_tac[][real_of_int, realTheory.le_ratr, realTheory.lt_ratl, Num_suc1]
  \\ TRY decide_tac
  >- tac
  >- intLib.ARITH_TAC
  \\ tac
  )

val lem1 =
  metisLib.METIS_PROVE
    [realTheory.REAL_POS_NZ, realTheory.REAL_DIV_REFL, realTheory.neg_rat]
    ``!a. 0r < a ==> (-a / a = -1)``

val lem2 = Q.prove(
  `!n. 0n < n ==> (-&n / &n = -1i)`,
  REPEAT strip_tac
  \\ `0i < &n` by intLib.ARITH_TAC
  \\ simp [integerTheory.int_div]
  )

val lem3 = Q.prove(
  `!n m. 0n < n /\ n < m ==> (-&n / &m = -1i)`,
  REPEAT strip_tac
  \\ `0i < &n` by intLib.ARITH_TAC
  \\ simp [integerTheory.int_div, arithmeticTheory.LESS_DIV_EQ_ZERO]
  )

val tac2 =
   metis_tac [arithmeticTheory.X_MOD_Y_EQ_X, DECIDE ``x < y ==> ~(y < x:num)``]

val lem4 = Q.prove(
  `!n m. 0 < m /\ m < n ==> -&n / &m < -1i`,
  NTAC 3 strip_tac
  \\ `&m <> 0i` by intLib.ARITH_TAC
  \\ simp [integerTheory.int_div]
  \\ srw_tac[][intLib.ARITH_PROVE ``a + -1 < -1 <=> a < 0i``]
  \\ tac
  >- (SPOSE_NOT_THEN strip_assume_tac
      \\ `(n DIV m = 0) \/ (n DIV m = 1)` by decide_tac
      \\ full_simp_tac(srw_ss())[]
      >- tac2
      \\ decide_tac
  )
  \\ strip_tac
  \\ full_simp_tac(srw_ss())[]
  \\ tac2
  )

val lem5 = Q.prove(
  `!n m. 0n < m /\ n <> 0 /\ (n MOD m = 0) /\ n <> m ==> 1 < n DIV m`,
  srw_tac[][arithmeticTheory.X_LT_DIV]
  \\ imp_res_tac arithmeticTheory.MOD_EQ_0_DIVISOR
  \\ Cases_on `d = 0` >- full_simp_tac(srw_ss())[]
  \\ Cases_on `d = 1` >- full_simp_tac(srw_ss())[]
  \\ `2 <= d` by decide_tac
  \\ metis_tac [arithmeticTheory.LESS_MONO_MULT]
  )

val int_floor_3 = Q.prove(
  `0 < m ==> (INT_FLOOR (-&n / &m) = -&n / &m)`,
  strip_tac
  \\ rewrite_tac [INT_FLOOR]
  \\ Cases_on `n = 0`
  >- simp [real_of_int, arithmeticTheory.ZERO_DIV]
  \\ Cases_on `n = m`
  >- simp [lem1, lem2, real_of_int]
  \\ Cases_on `n < m`
  >- simp [lem3, real_of_int, realTheory.le_ratr, realTheory.lt_ratl]
  \\ `m < n` by decide_tac
  \\ simp [lem4, real_of_int, realTheory.le_ratr, realTheory.lt_ratl,
           intLib.ARITH_PROVE ``a < -1i ==> a < 0 /\ a + 1 < 0``]
  \\ simp [integerTheory.int_div]
  \\ srw_tac[][integerTheory.INT_NEG_ADD, lem5, Num_suc1,
         intLib.ARITH_PROVE ``a + 1 + -1 = a: int``,
         intLib.ARITH_PROVE ``1n < a ==> (Num (&a + -1) = a - 1)``]
  \\ tac
  )

val INT_CEILING_IMP = Q.prove (
  `!r i. real_of_int (i - 1) < r /\ r <= real_of_int i ==> (INT_CEILING r = i)`,
  srw_tac[][INT_CEILING_def, integerTheory.LEAST_INT_DEF]
  \\ SELECT_ELIM_TAC
  \\ conj_tac
  >- (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC
    \\ res_tac
    \\ Cases_on `i`
    \\ Cases_on `i'`
    \\ full_simp_tac(srw_ss())[real_of_int]
    >| [
      Cases_on `&n - 1 < 0i`,
      Cases_on `&n - 1 < 0i`,
      Cases_on `&n - 1 < 0i`,
      Cases_on `-&n - 1 < 0i`,
      all_tac
    ]
    \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac realTheory.REAL_LTE_TRANS
    \\ full_simp_tac(srw_ss())[]
    \\ intLib.ARITH_TAC
  )
  \\ srw_tac[][]
  \\ Cases_on `i < x`
  >- res_tac
  \\ Cases_on `i = x`
  >- asm_rewrite_tac []
  \\ `x < i` by intLib.ARITH_TAC
  \\ Cases_on `i`
  \\ Cases_on `x`
  \\ full_simp_tac(srw_ss())[real_of_int]
  >| [
    Cases_on `&n - 1 < 0i`,
    Cases_on `&n - 1 < 0i`,
    Cases_on `&n - 1 < 0i`,
    Cases_on `-&n - 1 < 0i`,
    all_tac
  ]
  \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac realTheory.REAL_LTE_TRANS
  \\ full_simp_tac(srw_ss())[]
  \\ intLib.ARITH_TAC
  )

val INT_CEILING_INT_FLOOR = Q.store_thm("INT_CEILING_INT_FLOOR",
  `!r. INT_CEILING r =
       let i = INT_FLOOR r in if real_of_int i = r then i else i + 1`,
  lrw []
  \\ match_mp_tac INT_CEILING_IMP
  >- (`INT_FLOOR r - 1 < INT_FLOOR r` by intLib.ARITH_TAC
      \\ imp_res_tac real_of_int_monotonic
      \\ simp []
      \\ metis_tac [INT_FLOOR_BOUNDS, realTheory.REAL_LTE_TRANS])
  \\ simp [intLib.ARITH_PROVE ``a + 1 -1i = a``,
           RealArith.REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``,
           INT_FLOOR_BOUNDS, realTheory.REAL_LT_IMP_LE]
  )

val INT_CEILING_BOUNDS = Q.store_thm("INT_CEILING_BOUNDS",
  `!r. real_of_int (INT_CEILING r - 1) < r /\ r <= real_of_int (INT_CEILING r)`,
  lrw [INT_CEILING_INT_FLOOR, INT_FLOOR_BOUNDS, realTheory.REAL_LT_IMP_LE,
       intLib.ARITH_PROVE ``a + 1i - 1 = a``,
       RealArith.REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``]
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th])))
  \\ match_mp_tac real_of_int_monotonic
  \\ intLib.ARITH_TAC
  )

Theorem INT_CEILING:
  !r i. (INT_CEILING r = i) <=> real_of_int (i - 1) < r /\ r <= real_of_int i
Proof
  metis_tac [INT_CEILING_BOUNDS, INT_CEILING_IMP]
QED

local
  val rule =
    REWRITE_RULE [numeralTheory.numeral_distrib, numeralTheory.numeral_lt]
  val r1 = rule o Q.INST [`m` |-> `NUMERAL (BIT1 m)`]
  val r2 = rule o Q.INST [`m` |-> `NUMERAL (BIT2 m)`]
  val (t1, t2) = Drule.CONJ_PAIR int_floor_1
in
  val INT_FLOOR_EQNS = Theory.save_thm("INT_FLOOR_EQNS",
    Drule.LIST_CONJ (List.map Drule.GEN_ALL [t1, t2, int_floor_2, int_floor_3]))
  val INT_FLOOR_compute = Theory.save_thm ("INT_FLOOR_compute",
    Drule.LIST_CONJ
      [t1,t2, r1 int_floor_2, r2 int_floor_2, r1 int_floor_3, r2 int_floor_3])
  val () = computeLib.add_persistent_funs
             ["INT_FLOOR_compute", "INT_CEILING_INT_FLOOR"]
end

open arithmeticTheory
val real_of_int_num = store_thm("real_of_int_num[simp]",
  ``real_of_int (& n) = &n``,
  rewrite_tac[real_of_int_def]
  \\ Cases_on `(&n):int`
  \\ fs []);

val real_of_int_add = store_thm("real_of_int_add[simp]",
  ``real_of_int (m + n) = real_of_int m + real_of_int n``,
  Cases_on `m` \\ Cases_on `n` \\ fs [real_of_int_def] \\ rw []
  \\ fs [integerTheory.INT_ADD_CALCULATE]
  \\ rw [] \\ fs [] \\ fs [GSYM NOT_LESS,realTheory.add_ints]);

val real_of_int_neg = store_thm("real_of_int_neg[simp]",
  ``real_of_int (-m) = -real_of_int m``,
  Cases_on `m` \\ fs [real_of_int_def]);

val real_of_int_sub = store_thm("real_of_int_sub[simp]",
  ``real_of_int (m - n) = real_of_int m - real_of_int n``,
  fs [integerTheory.int_sub,realTheory.real_sub]);

val real_of_int_mul = store_thm("real_of_int_mul[simp]",
  ``real_of_int (m * n) = real_of_int m * real_of_int n``,
  Cases_on `m` \\ Cases_on `n` \\ fs [real_of_int_def] \\ rw []
  \\ fs [integerTheory.INT_MUL_CALCULATE]);

val real_of_int_lt = store_thm("real_of_int_lt[simp]",
  “real_of_int m < real_of_int n <=> m < n”,
  simp[real_of_int_def] >> map_every Cases_on [‘m’, ‘n’] >>
  simp[]);

val real_of_int_11 = store_thm("real_of_int_11[simp]",
  “(real_of_int m = real_of_int n) <=> (m = n)”,
  simp[real_of_int_def] >> map_every Cases_on [‘m’, ‘n’] >>
  simp[]);

val real_of_int_le = store_thm("real_of_int_le[simp]",
  “real_of_int m <= real_of_int n <=> m <= n”,
  simp[realTheory.REAL_LE_LT, integerTheory.INT_LE_LT]);

val _ = export_theory ()
