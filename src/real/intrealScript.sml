(* -------------------------------------------------------------------------
   A bridging theory between integers and reals
   ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory integerTheory intLib realTheory RealArith hurdUtils;

local open realSimps in end

val _ = new_theory "intreal"

(* -------------------------------------------------------------------------
   Define the inclusion homomorphism real_of_int :int->real.
   ------------------------------------------------------------------------- *)

Definition real_of_int:
  real_of_int i =
  if i < 0 then ~(real_of_num (Num (~i))) else real_of_num (Num i)
End

Theorem real_of_int_def = real_of_int;

(* -------------------------------------------------------------------------
   Floor and ceiling (ints)
   ------------------------------------------------------------------------- *)

Definition INT_FLOOR_def[nocompute]:
  INT_FLOOR x = LEAST_INT i. x < real_of_int (i + 1)
End
Definition INT_CEILING_def[nocompute]:
  INT_CEILING x = LEAST_INT i. x <= real_of_int i
End

Overload flr = “INT_FLOOR”
Overload clg = “INT_CEILING”

val _ = add_rule {
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
  fixity = Closefix,
  paren_style = OnlyIfNecessary,
  pp_elements = [TOK UnicodeChars.clgl, TM, TOK UnicodeChars.clgr],
  term_name = "clgtoks"}
Overload clgtoks = “INT_CEILING”

val _ = add_rule {
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
  fixity = Closefix,
  paren_style = OnlyIfNecessary,
  pp_elements = [TOK UnicodeChars.flrl, TM, TOK UnicodeChars.flrr],
  term_name = "flrtoks"}
Overload flrtoks = “INT_FLOOR”


(* -------------------------------------------------------------------------
   is_int
   ------------------------------------------------------------------------- *)

Definition is_int_def: is_int (x:real) <=> x = real_of_int (INT_FLOOR x)
End

(* -------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------- *)

val real_of_int_monotonic = Q.store_thm("real_of_int_monotonic",
  `!i j. i < j ==> real_of_int i < real_of_int j`,
  Cases \\ Cases \\ srw_tac[][real_of_int] \\ ARITH_TAC)

val real_arch_least1 =
  REAL_ARCH_LEAST
  |> Q.SPEC `1r`
  |> SIMP_RULE (srw_ss()) []

val Num_suc1 = ARITH_PROVE ``Num (&n + 1) = n + 1``

val lem = Q.prove( `!n. -&n <= 0r`, simp [REAL_NEG_LE0])

val lem2 = Q.prove(
  `!n. -&(n + 1n) = -&n - 1r`,
  once_rewrite_tac [GSYM add_ints]
  \\ simp [real_sub]
  )

val lem3 = ARITH_PROVE ``-&n + 1 < 0i ==> (Num (&n + -1i) = (n - 1))``

val lem4 = Q.prove(
  `!n. n <> 0 ==> (-&(n - 1n) = -&n + 1r)`,
  strip_tac
  \\ Cases_on `n = 1` >- simp []
  \\ metis_tac [REAL_SUB, REAL_NEG_SUB,
                REAL_ARITH ``-a + b = b - a: real``,
                DECIDE ``n <> 0 /\ n <> 1 ==> (n - 1 <> 0n)``]
  )

val lem5 = Q.prove(
  `!m n. n + 1 < m ==> -&m + 1 <= -&n - 1r`,
  REPEAT strip_tac
  \\ once_rewrite_tac [GSYM REAL_LE_NEG]
  \\ rewrite_tac [REAL_NEG_SUB, REAL_NEG_ADD,
                  REAL_SUB_RNEG]
  \\ Cases_on `m`
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD1]
  \\ REWRITE_TAC [GSYM REAL_ADD,
                  REAL_ARITH ``a + b + -b = a: real``]
  \\ simp []
  )

(* cf. INT_FLOOR_BOUNDS' for another form where ‘real_of_int (INT_FLOOR r)’
       stays in the middle.
 *)
Theorem INT_FLOOR_BOUNDS :
    !r. real_of_int (INT_FLOOR r) <= r /\ r < real_of_int (INT_FLOOR r + 1)
Proof
  srw_tac[][INT_FLOOR_def, LEAST_INT_DEF] \\ SELECT_ELIM_TAC \\ (
  REVERSE conj_tac
  >- (srw_tac[][REAL_NOT_LT]
      \\ pop_assum (qspec_then `x - 1` assume_tac)
      \\ full_simp_tac(srw_ss())[ARITH_PROVE ``a - 1 < a: int``])
  \\ Cases_on `0 <= r`
  >- (imp_res_tac real_arch_least1
      \\ qexists_tac `&n`
      \\ srw_tac[][real_of_int, REAL_NOT_LT,
             REWRITE_RULE [GSYM arithmeticTheory.ADD1] Num_suc1,
             ARITH_PROVE ``~(&n + 1i < 0)``]
      >- metis_tac [lem, REAL_LE_TRANS]
      \\ Cases_on `i'`
      \\ full_simp_tac(srw_ss())[Num_suc1]
      >| [`n' + 1 <= n` by decide_tac
          \\ metis_tac [REAL_LE, REAL_LE_TRANS],
          imp_res_tac
            (ARITH_PROVE ``n <> 0 /\ ~(-&n + 1i < 0) ==> (n = 1)``)
          \\ full_simp_tac(srw_ss())[],
          `1 <= n` by decide_tac
          \\ metis_tac [REAL_LE, REAL_LE_TRANS]
      ]
  )
  \\ imp_res_tac (REAL_ARITH ``~(0r <= r) ==> 0 <= -r /\ r <> 0``)
  \\ imp_res_tac real_arch_least1
  \\ rev_full_simp_tac(srw_ss())[arithmeticTheory.ADD1, INT_NEG_ADD,
          REAL_ARITH ``r <= 0r ==> (&(n: num) <= -r <=> r <= -&n)``,
          REAL_ARITH ``r <= 0r ==> (-r < &n <=> -&n < r)``]
  \\ Cases_on `r = -&n`
  >| [qexists_tac `~&n`, qexists_tac `~&(SUC n)`]
  \\ rev_full_simp_tac(srw_ss())[real_of_int, INT_NEG_ADD]
  \\ (conj_tac
      >- (srw_tac[][lem3]
          \\ Cases_on `n`
          \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD1,
                 REAL_ARITH ``r <= 0r /\ r <> 0 ==> r < 0``,
                 REAL_ARITH ``a <= b - 1 ==> a < b: real``,
                 ARITH_PROVE ``-&(n + 1) + 1 < 0i <=> n <> 0``,
                 REAL_ARITH ``r <= -1r ==> r < 0``,
                 REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``])
      \\ srw_tac[][REAL_NOT_LT]
      \\ Cases_on `i'`
      \\ rev_full_simp_tac(srw_ss())[lem2, lem3, lem4, arithmeticTheory.ADD1]
      \\ (ARITH_TAC ORELSE
          imp_res_tac (ARITH_PROVE ``n + 1 < m ==> (-&m + 1 < 0i)``)
          \\ metis_tac
               [REAL_LET_TRANS, REAL_LT_IMP_LE, lem5])
     )
  )
QED

Theorem INT_FLOOR:
  !r i. (INT_FLOOR r = i) <=> real_of_int i <= r /\ r < real_of_int (i + 1)
Proof
  REPEAT strip_tac
  \\ eq_tac
  >- metis_tac [INT_FLOOR_BOUNDS]
  \\ srw_tac[][INT_FLOOR_def, LEAST_INT_DEF]
  \\ SELECT_ELIM_TAC
  \\ conj_tac
  >- (
    SPOSE_NOT_THEN strip_assume_tac
    \\ res_tac
    \\ Cases_on `i`
    \\ Cases_on `i'`
    \\ full_simp_tac(srw_ss())[real_of_int, ARITH_PROVE ``~(&n + 1i < 0)``]
    >| [
      all_tac,
      Cases_on `-&n' + 1 < 0i`,
      all_tac,
      Cases_on `-&n' + 1 < 0i`,
      Cases_on `-&n + 1 < 0i`
    ]
    \\ full_simp_tac(srw_ss())[Num_suc1]
    \\ imp_res_tac REAL_LET_TRANS
    \\ full_simp_tac(srw_ss())[INT_NOT_LT]
    \\ ARITH_TAC
  )
  \\ srw_tac[][]
  \\ Cases_on `i < x`
  >- res_tac
  \\ Cases_on `i = x`
  >- asm_rewrite_tac []
  \\ `x < i` by ARITH_TAC
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
  \\ imp_res_tac REAL_LET_TRANS
  \\ full_simp_tac(srw_ss())[INT_NOT_LT]
  \\ ARITH_TAC
QED

val int_floor_1 = Q.prove(
  `(INT_FLOOR &n = &n) /\ (INT_FLOOR (-&n) = -&n)`,
  srw_tac[][INT_FLOOR, real_of_int] \\ ARITH_TAC)

val tac =
  imp_res_tac arithmeticTheory.DIVISION
  \\ pop_assum (qspec_then `n` assume_tac)
  \\ first_assum (qspec_then `n` assume_tac)
  \\ TRY decide_tac

val int_floor_2 = Q.prove(
  `0 < m ==> (INT_FLOOR (&n / &m) = &n / &m)`,
  strip_tac
  \\ rewrite_tac [INT_FLOOR]
  \\ srw_tac[][real_of_int, le_ratr, lt_ratl, Num_suc1]
  \\ TRY decide_tac
  >- tac
  >- ARITH_TAC
  \\ tac
  )

val lem1 =
  metisLib.METIS_PROVE
    [REAL_POS_NZ, REAL_DIV_REFL, neg_rat]
    ``!a. 0r < a ==> (-a / a = -1)``

val lem2 = Q.prove(
  `!n. 0n < n ==> (-&n / &n = -1i)`,
  REPEAT strip_tac
  \\ `0i < &n` by ARITH_TAC
  \\ simp [int_div]
  )

val lem3 = Q.prove(
  `!n m. 0n < n /\ n < m ==> (-&n / &m = -1i)`,
  REPEAT strip_tac
  \\ `0i < &n` by ARITH_TAC
  \\ simp [int_div, arithmeticTheory.LESS_DIV_EQ_ZERO]
  )

val tac2 =
   metis_tac [arithmeticTheory.X_MOD_Y_EQ_X, DECIDE ``x < y ==> ~(y < x:num)``]

val lem4 = Q.prove(
  `!n m. 0 < m /\ m < n ==> -&n / &m < -1i`,
  NTAC 3 strip_tac
  \\ `&m <> 0i` by ARITH_TAC
  \\ simp [int_div]
  \\ srw_tac[][ARITH_PROVE ``a + -1 < -1 <=> a < 0i``]
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
  >- simp [lem3, real_of_int, le_ratr, lt_ratl]
  \\ `m < n` by decide_tac
  \\ simp [lem4, real_of_int, le_ratr, lt_ratl,
           ARITH_PROVE ``a < -1i ==> a < 0 /\ a + 1 < 0``]
  \\ simp [int_div]
  \\ srw_tac[][INT_NEG_ADD, lem5, Num_suc1,
         ARITH_PROVE ``a + 1 + -1 = a: int``,
         ARITH_PROVE ``1n < a ==> (Num (&a + -1) = a - 1)``]
  \\ tac
  )

val INT_CEILING_IMP = Q.prove (
  `!r i. real_of_int (i - 1) < r /\ r <= real_of_int i ==> (INT_CEILING r = i)`,
  srw_tac[][INT_CEILING_def, LEAST_INT_DEF]
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
    \\ imp_res_tac REAL_LTE_TRANS
    \\ full_simp_tac(srw_ss())[]
    \\ ARITH_TAC
  )
  \\ srw_tac[][]
  \\ Cases_on `i < x`
  >- res_tac
  \\ Cases_on `i = x`
  >- asm_rewrite_tac []
  \\ `x < i` by ARITH_TAC
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
  \\ imp_res_tac REAL_LTE_TRANS
  \\ full_simp_tac(srw_ss())[]
  \\ ARITH_TAC
  )

val INT_CEILING_INT_FLOOR = Q.store_thm("INT_CEILING_INT_FLOOR",
  `!r. INT_CEILING r =
       let i = INT_FLOOR r in if real_of_int i = r then i else i + 1`,
  lrw []
  \\ match_mp_tac INT_CEILING_IMP
  >- (`INT_FLOOR r - 1 < INT_FLOOR r` by ARITH_TAC
      \\ imp_res_tac real_of_int_monotonic
      \\ simp []
      \\ metis_tac [INT_FLOOR_BOUNDS, REAL_LTE_TRANS])
  \\ simp [ARITH_PROVE ``a + 1 -1i = a``,
           REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``,
           INT_FLOOR_BOUNDS, REAL_LT_IMP_LE]
  )

(* cf. INT_CEILING_BOUNDS' for another form where ‘real_of_int (INT_CEILING r)’
       stays in the middle.
 *)
Theorem INT_CEILING_BOUNDS :
    !r. real_of_int (INT_CEILING r - 1) < r /\ r <= real_of_int (INT_CEILING r)
Proof
  lrw [INT_CEILING_INT_FLOOR, INT_FLOOR_BOUNDS, REAL_LT_IMP_LE,
       ARITH_PROVE ``a + 1i - 1 = a``,
       REAL_ARITH ``a <= b /\ a <> b ==> a < b: real``]
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th])))
  \\ match_mp_tac real_of_int_monotonic
  \\ ARITH_TAC
QED

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

val real_of_int_num = store_thm("real_of_int_num[simp]",
  ``real_of_int (& n) = &n``,
  rewrite_tac[real_of_int_def]
  \\ Cases_on `(&n):int`
  \\ fs []);

val real_of_int_add = store_thm("real_of_int_add[simp]",
  ``real_of_int (m + n) = real_of_int m + real_of_int n``,
  Cases_on `m` \\ Cases_on `n` \\ fs [real_of_int_def] \\ rw []
  \\ fs [INT_ADD_CALCULATE]
  \\ rw [] \\ fs [] \\ fs [GSYM NOT_LESS,add_ints]);

val real_of_int_neg = store_thm("real_of_int_neg[simp]",
  ``real_of_int (-m) = -real_of_int m``,
  Cases_on `m` \\ fs [real_of_int_def]);

val real_of_int_sub = store_thm("real_of_int_sub[simp]",
  ``real_of_int (m - n) = real_of_int m - real_of_int n``,
  fs [int_sub,real_sub]);

val real_of_int_mul = store_thm("real_of_int_mul[simp]",
  ``real_of_int (m * n) = real_of_int m * real_of_int n``,
  Cases_on `m` \\ Cases_on `n` \\ fs [real_of_int_def] \\ rw []
  \\ fs [INT_MUL_CALCULATE]);

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
  simp[REAL_LE_LT, INT_LE_LT]);

Theorem INT_FLOOR_MONO:
  x < y ==> INT_FLOOR x <= INT_FLOOR y
Proof
  CCONTR_TAC >> gs[INT_NOT_LE] >>
  ‘flr y + 1i <= flr x’ by simp[GSYM INT_LT_LE1] >>
  ‘y < real_of_int (flr y + 1)’ by simp[INT_FLOOR_BOUNDS] >>
  ‘real_of_int (flr x) <= x’ by simp[INT_FLOOR_BOUNDS] >>
  metis_tac[REAL_LET_TRANS, REAL_LTE_TRANS,
            REAL_LT_TRANS,
            real_of_int_le, REAL_LT_REFL]
QED

Theorem INT_FLOOR_SUCa[local]:
  INT_FLOOR r + 1 <= INT_FLOOR (r + 1)
Proof
  CCONTR_TAC >> gs[INT_NOT_LE] >>
  ‘INT_FLOOR (r + 1) + 1 <= INT_FLOOR r + 1’ by gs[INT_LT_LE1] >>
  ‘real_of_int (flr r) + 1 <= r + 1’ by simp[INT_FLOOR_BOUNDS] >>
  ‘r + 1 < real_of_int (flr (r + 1) + 1)’ by simp[INT_FLOOR_BOUNDS] >>
  ‘real_of_int(flr (r + 1) + 1) <= real_of_int (flr r + 1)’ by simp[] >>
  ‘r + 1 < real_of_int (flr r + 1)’ by metis_tac[REAL_LTE_TRANS] >>
  metis_tac[real_of_int_num, REAL_LTE_TRANS, REAL_LT_REFL,
            real_of_int_add]
QED

Theorem INT_FLOOR_SUCb[local]:
  INT_FLOOR (r + 1) <= INT_FLOOR r + 1
Proof
  CCONTR_TAC >> gs[INT_NOT_LE] >>
  qabbrev_tac ‘i = (flr r:int) + 1’ >> qabbrev_tac ‘j:int = flr (r + 1)’ >>
  ‘i + 1 <= j’ by gs[INT_LT_LE1] >>
  ‘r < real_of_int i’ by simp[INT_FLOOR_BOUNDS, Abbr‘i’] >>
  ‘real_of_int j <= r + 1’ by simp[INT_FLOOR_BOUNDS, Abbr‘j’] >>
  ‘r + 1 < real_of_int j’
    by (irule REAL_LTE_TRANS >>
        irule_at Any (iffRL real_of_int_le) >> first_assum $ irule_at Any >>
        simp[]) >>
  metis_tac[REAL_LTE_TRANS, REAL_LT_REFL]
QED

Theorem INT_FLOOR_SUC:
  INT_FLOOR (x + 1) = INT_FLOOR x + 1
Proof
  simp[GSYM INT_LE_ANTISYM, INT_FLOOR_SUCb, INT_FLOOR_SUCa]
QED

Theorem INT_FLOOR_SUB1:
  INT_FLOOR (x - 1) = INT_FLOOR x - 1
Proof
  simp[INT_EQ_SUB_LADD, GSYM INT_FLOOR_SUC,
       REAL_ARITH “x - 1r + 1 = x”]
QED

Theorem INT_FLOOR_SUM_NUM[simp]:
  INT_FLOOR (x + &n) = INT_FLOOR x + &n /\
  INT_FLOOR (&n + x) = INT_FLOOR x + &n
Proof
  csimp[REAL_ADD_COMM] >>
  Induct_on‘n’>>
  simp[REAL, GSYM REAL_ADD, Excl "REAL_ADD",
       INT, REAL_ADD_ASSOC, INT_FLOOR_SUC,
       INT_ADD_ASSOC
      ]
QED

(* Add an alias for better naming *)
Theorem INT_FLOOR_ADD_NUM = INT_FLOOR_SUM_NUM

Theorem INT_FLOOR_SUB_NUM[simp]:
  INT_FLOOR (x - &n) = INT_FLOOR x - &n /\
  INT_FLOOR (&n - x) = INT_FLOOR (-x) + &n
Proof
  reverse conj_tac >- simp[real_sub] >>
  Induct_on ‘n’ >>
  simp[REAL, Excl "REAL_ADD", GSYM REAL_ADD,
       REAL_ARITH “x - (y + z) = x - y - z:real”, INT_FLOOR_SUB1,
       INT] >>
  ARITH_TAC
QED

Theorem INT_FLOOR_SUM[simp]:
  INT_FLOOR (x + real_of_int y) = INT_FLOOR x + y /\
  INT_FLOOR (real_of_int y + x) = INT_FLOOR x + y
Proof
  csimp[REAL_ADD_COMM] >>
  Cases_on ‘y’ >> simp[GSYM real_sub, GSYM int_sub]
QED

Theorem ints_exist_in_gaps:
  !a b. a + 1 < b ==> ?i. a < real_of_int i /\ real_of_int i < b
Proof
  rpt strip_tac >> irule_at Any (cj 2 INT_FLOOR_BOUNDS) >> simp[] >>
  irule REAL_LET_TRANS >> first_assum $ irule_at Any >>
  simp[INT_FLOOR_BOUNDS]
QED

(* Alternative definition of is_int by INT_CEILING *)
Theorem is_int_alt :
    !x. is_int x <=> x = real_of_int (INT_CEILING x)
Proof
    rw [is_int_def]
 >> EQ_TAC >- rw [INT_CEILING_INT_FLOOR]
 >> DISCH_TAC
 >> CCONTR_TAC
 >> fs [INT_CEILING_INT_FLOOR]
 >> ‘1 = real_of_int 1’ by rw [real_of_int_num, real_of_num]
 >> METIS_TAC [REAL_LT_IMP_NE, INT_FLOOR_BOUNDS, real_of_int_add]
QED

Theorem is_int_thm :
    !x. is_int x <=> real_of_int (INT_FLOOR x) = real_of_int (INT_CEILING x)
Proof
    Q.X_GEN_TAC ‘x’
 >> EQ_TAC >- METIS_TAC [is_int_def, is_int_alt]
 >> DISCH_TAC
 >> Suff ‘real_of_int (INT_FLOOR x) = x’ >- rw [GSYM is_int_def]
 >> CCONTR_TAC
 >> fs [INT_CEILING_INT_FLOOR]
 >> Suff ‘INT_FLOOR x < INT_FLOOR x + 1’ >- PROVE_TAC [INT_LT_IMP_NE]
 >> rw [INT_LT_ADDR]
QED

Theorem INT_CEILING_ADD_NUM :
    INT_CEILING (x + &n) = INT_CEILING x + &n /\
    INT_CEILING (&n + x) = INT_CEILING x + &n
Proof
    CONJ_TAC >> simp [INT_CEILING_INT_FLOOR]
 >| [ (* goal 1 (of 2) *)
      Cases_on ‘real_of_int (INT_FLOOR x) = x’ >> simp [] \\
      ARITH_TAC,
      (* goal 2 (of 2) *)
      Cases_on ‘real_of_int (INT_FLOOR x) = x’ >> simp []
      >- PROVE_TAC [REAL_ADD_COMM] \\
     ‘&n + x = x + &n’ by PROVE_TAC [REAL_ADD_COMM] >> POP_ORW \\
      simp [] >> ARITH_TAC ]
QED

Theorem INT_CEILING_SUB_NUM :
    INT_CEILING (x - &n) = INT_CEILING x - &n /\
    INT_CEILING (&n - x) = INT_CEILING (-x) + &n
Proof
    CONJ_TAC >> simp [INT_CEILING_INT_FLOOR]
 >| [ (* goal 1 (of 2) *)
      Cases_on ‘real_of_int (INT_FLOOR x) = x’ >> simp [real_sub] \\
      ARITH_TAC,
      (* goal 2 (of 2) *)
      Cases_on ‘real_of_int (INT_FLOOR ~x) = ~x’ >> simp [real_sub]
      >- PROVE_TAC [REAL_ADD_COMM] \\
     ‘&n + -x = -x + &n’ by PROVE_TAC [REAL_ADD_COMM] >> POP_ORW \\
      simp [] >> ARITH_TAC ]
QED

Theorem INT_CEILING_BOUNDS' :
    !r. r <= real_of_int (INT_CEILING r) /\ real_of_int (INT_CEILING r) < r + 1
Proof
    rw [INT_CEILING_BOUNDS]
 >> Suff ‘real_of_int (INT_CEILING r) - 1 < r’ >- rw [REAL_LT_SUB_RADD]
 >> Suff ‘real_of_int (INT_CEILING r) - 1 = real_of_int (INT_CEILING r - 1)’
 >- (Rewr' >> REWRITE_TAC [INT_CEILING_BOUNDS])
 >> rw [real_of_num, INT_CEILING_SUB_NUM]
QED

Theorem INT_FLOOR_BOUNDS' :
    !r. r - 1 < real_of_int (INT_FLOOR r) /\ real_of_int (INT_FLOOR r) <= r
Proof
    rw [INT_FLOOR_BOUNDS]
 >> Suff ‘r < real_of_int (INT_FLOOR r) + 1’ >- rw [REAL_LT_SUB_RADD]
 >> Suff ‘real_of_int (INT_FLOOR r) + 1 = real_of_int (INT_FLOOR r + 1)’
 >- (Rewr' >> REWRITE_TAC [INT_FLOOR_BOUNDS])
 >> rw [real_of_num, INT_CEILING_ADD_NUM]
QED

Theorem INT_FLOOR':
    !r i. (INT_FLOOR r = i) <=> r - 1 < real_of_int i /\ real_of_int i <= r
Proof
    rw [INT_FLOOR]
 >> Suff ‘r < real_of_int i + 1 <=> r - 1 < real_of_int i’ >- METIS_TAC []
 >> simp [REAL_LT_SUB_RADD]
QED

Theorem INT_CEILING':
    !r i. (INT_CEILING r = i) <=> r <= real_of_int i /\ real_of_int i < r + 1
Proof
    rw [INT_CEILING]
 >> Suff ‘real_of_int i - 1 < r <=> real_of_int i < r + 1’ >- METIS_TAC []
 >> simp [REAL_LT_SUB_RADD]
QED

(* https://proofwiki.org/wiki/Floor_of_Negative_equals_Negative_of_Ceiling *)
Theorem INT_FLOOR_NEG :
    !x. INT_FLOOR (~x) = ~INT_CEILING x
Proof
    Q.X_GEN_TAC ‘x’
 >> simp [INT_FLOOR', INT_CEILING_BOUNDS']
 >> ‘-x - 1 = ~(x + 1)’ by REAL_ARITH_TAC >> POP_ORW
 >> simp [REAL_LT_NEG, INT_CEILING_BOUNDS']
QED

Theorem INT_CEILING_NEG :
    !x. INT_CEILING (~x) = ~INT_FLOOR x
Proof
    Q.X_GEN_TAC ‘x’
 >> simp [INT_CEILING', INT_FLOOR_BOUNDS']
 >> ‘-x + 1 = ~(x - 1)’ by REAL_ARITH_TAC >> POP_ORW
 >> simp [REAL_LT_NEG, INT_FLOOR_BOUNDS']
QED

(*---------------------------------------------------------------------------*
 *  Fractional part                                                          *
 *---------------------------------------------------------------------------*)

 (* ‘frac x’ to mean x mod 1 or ‘x - flr x’, the fractional part of x [1]

   NOTE: For the negative numbers, here it is defined in the same way as for
   positive numbers [2] (thus ‘frac 3.6 = 0.6’ but ‘frac ~3.6 = 0.4’.)
 *)
Definition frac_def :
    frac x = x - real_of_int (INT_FLOOR x)
End

Theorem is_int_eq_frac_0 :
    !x. is_int x <=> frac x = 0
Proof
    rw [frac_def, is_int_def, REAL_SUB_0]
QED

val _ = export_theory ()

(* References:

   [1] Graham, R.L., Knuth, D.E., Patashnik, O.: Concrete Mathematics. 2nd Eds.
       Addison-Wesley Publishing Company (1994).
   [2] https://en.wikipedia.org/wiki/Floor_and_ceiling_functions
   [3] https://en.wikipedia.org/wiki/Fractional_part
 *)
