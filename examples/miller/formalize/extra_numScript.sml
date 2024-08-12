open HolKernel Parse boolLib bossLib;

open arithmeticTheory hurdUtils res_quanTools
     pred_setTheory subtypeTheory extra_boolTheory combinTheory;

val _ = new_theory "extra_num";

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val Simplify = RW_TAC arith_ss;
val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

(* ------------------------------------------------------------------------- *)
(* Needed for definitions.                                                   *)
(* ------------------------------------------------------------------------- *)

val DIV_THEN_MULT = store_thm
  ("DIV_THEN_MULT",
   ``!p q. SUC q * (p DIV SUC q) <= p``,
   NTAC 2 STRIP_TAC
   >> Know `?r. p = (p DIV SUC q) * SUC q + r`
   >- (Know `0 < SUC q` >- DECIDE_TAC
       >> PROVE_TAC [DIVISION])
   >> STRIP_TAC
   >> Suff `p = SUC q * (p DIV SUC q) + r`
   >- (KILL_TAC >> DECIDE_TAC)
   >> PROVE_TAC [MULT_COMM]);

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = hide "min"; (* already defined for real numbers *)
val min_def = Define `min (m:num) n = if m <= n then m else n`;

val gtnum_def = Define `gtnum (n : num) x = (n < x)`;

val (log2_def, log2_ind) = Defn.tprove
  let val d = Hol_defn "log2"
        `(log2 0 = 0)
         /\ (log2 n = SUC (log2 (n DIV 2)))`
      val g = `measure (\x. x)`
  in (d, WF_REL_TAC g)
  end;

val _ = save_thm ("log2_def", log2_def);
val _ = save_thm ("log2_ind", log2_ind);

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val SUC_0 = store_thm
  ("SUC_0",
   ``SUC 0 = 1``,
   DECIDE_TAC);

val LESS_0_MULT2 = store_thm
  ("LESS_0_MULT2",
   ``!m n : num. 0 < m * n <=> 0 < m /\ 0 < n``,
   rpt STRIP_TAC
   >> Cases_on `m` >- RW_TAC arith_ss []
   >> Cases_on `n` >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [MULT]);

val LESS_1_MULT2 = store_thm
  ("LESS_1_MULT2",
   ``!m n : num. 1 < m /\ 1 < n ==> 1 < m * n``,
   rpt STRIP_TAC
   >> Suff `~(m * n = 0) /\ ~(m * n = 1)` >- DECIDE_TAC
   >> CONJ_TAC
   >> ONCE_REWRITE_TAC [MULT_EQ_0, MULT_EQ_1]
   >> DECIDE_TAC);

val FUNPOW_SUC = store_thm
  ("FUNPOW_SUC",
   ``!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)``,
   Induct_on `n` >- RW_TAC std_ss [FUNPOW]
   >> ONCE_REWRITE_TAC [FUNPOW]
   >> RW_TAC std_ss []);

val EVEN_ODD_BASIC = store_thm
  ("EVEN_ODD_BASIC",
   ``EVEN 0 /\ ~EVEN 1 /\ EVEN 2 /\ ~ODD 0 /\ ODD 1 /\ ~ODD 2``,
   CONV_TAC (TOP_DEPTH_CONV Num_conv.num_CONV)
   >> RW_TAC arith_ss [EVEN, ODD]);

val EVEN_ODD_EXISTS_EQ = store_thm
  ("EVEN_ODD_EXISTS_EQ",
   ``!n. (EVEN n = ?m. n = 2 * m) /\ (ODD n = ?m. n = SUC (2 * m))``,
   PROVE_TAC [EVEN_ODD_EXISTS, EVEN_DOUBLE, ODD_DOUBLE]);

val MOD_1 = store_thm
  ("MOD_1",
   ``!n : num. n MOD 1 = 0``,
   PROVE_TAC [SUC_0, MOD_ONE]);

val DIV_1 = store_thm
  ("DIV_1",
   ``!n : num. n DIV 1 = n``,
   PROVE_TAC [SUC_0, DIV_ONE]);

val MOD_LESS = store_thm
  ("MOD_LESS",
   ``!n k : num. 0 < n ==> k MOD n < n``,
   PROVE_TAC [DIVISION]);

val X_MOD_X = store_thm
  ("X_MOD_X",
   ``!n. 0 < n ==> (n MOD n = 0)``, PROVE_TAC [DIVMOD_ID]);

val LESS_MOD_EQ = store_thm
  ("LESS_MOD_EQ",
   ``!x n. x < n ==> (x MOD n = x)``,
   REPEAT STRIP_TAC
   >> MP_TAC (Q.SPECL [`x`, `n`] LESS_DIV_EQ_ZERO)
   >> ASM_REWRITE_TAC []
   >> STRIP_TAC
   >> MP_TAC (Q.SPEC `n` DIVISION)
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `x`)
   >> RW_TAC arith_ss []);

val MOD_PLUS1 = store_thm
  ("MOD_PLUS1",
   ``!n a b. 0 < n ==> ((a MOD n + b) MOD n = (a + b) MOD n)``,
   RW_TAC arith_ss []
   >> MP_TAC (Q.SPEC `n` MOD_PLUS)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   >> RW_TAC arith_ss [MOD_MOD]);

val MOD_PLUS2 = store_thm
  ("MOD_PLUS2",
   ``!n a b. 0 < n ==> ((a + b MOD n) MOD n = (a + b) MOD n)``,
   PROVE_TAC [MOD_PLUS1, ADD_COMM]);

val MOD_MULT1 = store_thm
  ("MOD_MULT1",
   ``!n a b. 0 < n ==> ((a MOD n * b) MOD n = (a * b) MOD n)``,
   RW_TAC std_ss []
   >> Induct_on `b` >- RW_TAC arith_ss [MULT_CLAUSES]
   >> RW_TAC std_ss [MULT_CLAUSES]
   >> MP_TAC (Q.SPEC `n` (GSYM MOD_PLUS2))
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `n` MOD_PLUS1)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss []);

val MOD_MULT2 = store_thm
  ("MOD_MULT2",
   ``!n a b. 0 < n ==> ((a * b MOD n) MOD n = (a * b) MOD n)``,
   PROVE_TAC [MOD_MULT1, MULT_COMM]);

val DIVISION_ALT = store_thm
  ("DIVISION_ALT",
   ``!n k. 0 < n ==> (k DIV n * n + k MOD n = k)``,
   PROVE_TAC [DIVISION]);

val MOD_EQ_X = store_thm
  ("MOD_EQ_X",
   ``!n r. 0 < n ==> ((r MOD n = r) <=> r < n)``,
   rpt STRIP_TAC
   >> REVERSE EQ_TAC >- PROVE_TAC [LESS_MOD]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [SYM th])
   >> RW_TAC std_ss [MOD_LESS]);

val DIV_EQ_0 = store_thm
  ("DIV_EQ_0",
   ``!n r. 0 < n ==> ((r DIV n = 0) <=> r < n)``,
   rpt STRIP_TAC
   >> REVERSE EQ_TAC >- PROVE_TAC [LESS_DIV_EQ_ZERO]
   >> STRIP_TAC
   >> Know `r DIV n * n + r MOD n = r`
   >- RW_TAC std_ss [DIVISION_ALT]
   >> RW_TAC arith_ss [MOD_EQ_X]);

val MOD_EXP = store_thm
  ("MOD_EXP",
   ``!n a b. 0 < n ==> ((a MOD n) EXP b MOD n = a EXP b MOD n)``,
   NTAC 2 STRIP_TAC
   >> Induct >- RW_TAC std_ss [EXP]
   >> STRIP_TAC
   >> RES_TAC
   >> RW_TAC std_ss
      [EXP, GSYM (Q.SPECL [`n`, `a MOD n`, `(a MOD n) EXP b`] MOD_MULT2)]
   >> RW_TAC std_ss [MOD_MULT1, MOD_MULT2]);

Theorem DIV_TWO_UNIQUE:
  !n q r. n = 2 * q + r /\ (r = 0 \/ r = 1) ==>
          q = n DIV 2 /\ r = n MOD 2
Proof
  simp[DISJ_IMP_THM]
QED

val DIVISION_TWO = store_thm
  ("DIVISION_TWO",
   ``!n. (n = 2 * (n DIV 2) + (n MOD 2)) /\ ((n MOD 2 = 0) \/ (n MOD 2 = 1))``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `2` DIVISION)
   >> Know `0:num < 2` >- DECIDE_TAC
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
   >> RW_TAC bool_ss [] >|
   [PROVE_TAC [MULT_COMM],
    DECIDE_TAC]);

val DIV_TWO = store_thm
  ("DIV_TWO",
   ``!n. n = 2 * (n DIV 2) + (n MOD 2)``,
   PROVE_TAC [DIVISION_TWO]);

val MOD_TWO = store_thm
  ("MOD_TWO",
   ``!n. n MOD 2 = if EVEN n then 0 else 1``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `n` DIVISION_TWO)
   >> STRIP_TAC >|
   [Q.PAT_ASSUM `n = X` MP_TAC
    >> RW_TAC std_ss []
    >> PROVE_TAC [EVEN_DOUBLE, ODD_EVEN, ADD_CLAUSES],
    Q.PAT_ASSUM `n = X` MP_TAC
    >> RW_TAC std_ss []
    >> PROVE_TAC [ODD_DOUBLE, ODD_EVEN, ADD1]]);

val DIV_TWO_BASIC = store_thm
  ("DIV_TWO_BASIC",
   ``(0 DIV 2 = 0) /\ (1 DIV 2 = 0) /\ (2 DIV 2 = 1)``,
   Know `(0:num = 2 * 0 + 0) /\ (1:num = 2 * 0 + 1) /\ (2:num = 2 * 1 + 0)`
   >- RW_TAC arith_ss []
   >> PROVE_TAC [DIV_TWO_UNIQUE]);

val DIV_TWO_MONO = store_thm
  ("DIV_TWO_MONO",
   ``!m n. m DIV 2 < n DIV 2 ==> m < n``,
   NTAC 2 STRIP_TAC
   >> (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   >> Q.SPEC_TAC (`m DIV 2`, `p`)
   >> Q.SPEC_TAC (`n DIV 2`, `q`)
   >> REPEAT STRIP_TAC
   >> Know `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> Know `(n MOD 2 = 0) \/ (n MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> DECIDE_TAC);

val DIV_TWO_MONO_EVEN = store_thm
  ("DIV_TWO_MONO_EVEN",
   ``!m n. EVEN n ==> (m DIV 2 < n DIV 2 <=> m < n)``,
   RW_TAC std_ss []
   >> EQ_TAC >- PROVE_TAC [DIV_TWO_MONO]
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   >> Q.SPEC_TAC (`m DIV 2`, `p`)
   >> Q.SPEC_TAC (`n DIV 2`, `q`)
   >> REPEAT STRIP_TAC
   >> Know `n MOD 2 = 0` >- PROVE_TAC [MOD_TWO]
   >> Know `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> DECIDE_TAC);

Theorem DIV_TWO_CANCEL:
  !n. (2 * n DIV 2 = n) /\ (SUC (2 * n) DIV 2 = n)
Proof
  RW_TAC std_ss [ADD1]
QED

val EXP_DIV_TWO = store_thm
  ("EXP_DIV_TWO",
   ``!n. 2 EXP SUC n DIV 2 = 2 EXP n``,
   RW_TAC std_ss [EXP, DIV_TWO_CANCEL]);

val EVEN_EXP_TWO = store_thm
  ("EVEN_EXP_TWO",
   ``!n. EVEN (2 EXP n) = ~(n = 0)``,
   Cases >- RW_TAC arith_ss [EXP, EVEN_ODD_BASIC]
   >> RW_TAC arith_ss [EXP, EVEN_DOUBLE]);

val DIV_TWO_EXP = store_thm
  ("DIV_TWO_EXP",
   ``!n k. k DIV 2 < 2 EXP n <=> k < 2 EXP SUC n``,
   RW_TAC std_ss []
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [GSYM EXP_DIV_TWO]
   >> MATCH_MP_TAC DIV_TWO_MONO_EVEN
   >> RW_TAC std_ss [EVEN_EXP_TWO]);

val MIN_0L = store_thm
  ("MIN_0L",
   ``!n : num. min 0 n = 0``,
   RW_TAC arith_ss [min_def]);

val MIN_0R = store_thm
  ("MIN_0R",
   ``!n : num. min n 0 = 0``,
   RW_TAC arith_ss [min_def]);

val MIN_REFL = store_thm
  ("MIN_REFL",
   ``!a : num. min a a = a``,
   RW_TAC arith_ss [min_def]);

val MIN_SYM = store_thm
  ("MIN_SYM",
   ``!a b : num. min a b = min b a``,
   RW_TAC arith_ss [min_def]);

val LEQ_MINL = store_thm
  ("LEQ_MINL",
   ``!a b : num. a <= b ==> (min a b = a)``,
   RW_TAC arith_ss [min_def]);

val LEQ_MINR = store_thm
  ("LEQ_MINR",
   ``!a b : num. a <= b ==> (min b a = a)``,
   RW_TAC arith_ss [min_def]);

val LESS_MINL = store_thm
  ("LESS_MINL",
   ``!a b : num. a < b ==> (min a b = a)``,
   RW_TAC arith_ss [min_def]);

val LESS_MINR = store_thm
  ("LESS_MINR",
   ``!a b : num. a < b ==> (min b a = a)``,
   RW_TAC arith_ss [min_def]);

val IN_GTNUM = store_thm
  ("IN_GTNUM",
   ``!x n : num. x IN gtnum n <=> n < x``,
   RW_TAC std_ss [gtnum_def, SPECIFICATION]);

val GTNUM0_SUBTYPE_JUDGEMENT = store_thm
  ("GTNUM0_SUBTYPE_JUDGEMENT",
   ``!m n.
       SUC m <= n \/ m < n \/ ~(0 = n) \/ ~(n = 0) \/
       (n = SUC m) \/ (SUC m = n) ==> n IN gtnum 0``,
   RW_TAC std_ss [IN_GTNUM]
   >> DECIDE_TAC);

val GTNUM1_SUBTYPE_JUDGEMENT = store_thm
  ("GTNUM1_SUBTYPE_JUDGEMENT",
   ``!m n. SUC (SUC m) <= n \/ SUC m < n \/ 1 < n \/
           (n = SUC (SUC m)) \/ (SUC (SUC m) = n) ==> n IN gtnum 1``,
   RW_TAC std_ss [IN_GTNUM]
   >> DECIDE_TAC);

val GTNUM1_SUBSET_GTNUM0 = store_thm
  ("GTNUM1_SUBSET_GTNUM0",
   ``gtnum 1 SUBSET gtnum 0``,
   RW_TAC std_ss [SUBSET_DEF, IN_GTNUM]
   >> DECIDE_TAC);

val SUC_SUBTYPE = store_thm
  ("SUC_SUBTYPE",
   ``SUC IN ((UNIV -> gtnum 0) INTER (gtnum 0 -> gtnum 1))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
   >> DECIDE_TAC);

val ADD_SUBTYPE = store_thm
  ("ADD_SUBTYPE",
   ``!n. $+ IN ((UNIV -> gtnum n -> gtnum n) INTER (gtnum n -> UNIV -> gtnum n)
                INTER (gtnum 0 -> gtnum 0 -> gtnum 1))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
   >> DECIDE_TAC);

val MULT_SUBTYPE = store_thm
  ("MULT_SUBTYPE",
   ``$* IN ((gtnum 0 -> gtnum 0 -> gtnum 0) INTER
            (gtnum 1 -> gtnum 0 -> gtnum 1) INTER
            (gtnum 0 -> gtnum 1 -> gtnum 1))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM, LESS_MULT2] >|
   [Cases_on `x' = 1` >- RW_TAC arith_ss []
    >> Know `1 < x'` >- DECIDE_TAC
    >> RW_TAC std_ss [LESS_1_MULT2],
    Cases_on `x = 1` >- RW_TAC arith_ss []
    >> Know `1 < x` >- DECIDE_TAC
    >> RW_TAC std_ss [LESS_1_MULT2]]);

val MIN_SUBTYPE = store_thm
  ("MIN_SUBTYPE",
   ``!x. min IN (x -> x -> x)``,
   RW_TAC arith_ss [IN_FUNSET, min_def]
   >> PROVE_TAC []);

Theorem EXP_SUBTYPE:
  $EXP IN ((gtnum 0 -> UNIV -> gtnum 0) INTER
           (gtnum 1 -> gtnum 0 -> gtnum 1))
Proof
  RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
QED

val FUNPOW_SUBTYPE = store_thm
  ("FUNPOW_SUBTYPE",
   ``!(x:'a->bool). FUNPOW IN ((x -> x) -> UNIV -> x -> x)``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`x'''`, `y`)
   >> Induct_on `x''` >- RW_TAC std_ss [FUNPOW]
   >> RW_TAC std_ss [FUNPOW]);

val NUMERAL_BIT1_SUBTYPE = store_thm
  ("NUMERAL_BIT1_SUBTYPE",
   ``BIT1 IN ((UNIV -> gtnum 0) INTER (gtnum 0 -> gtnum 1))``,
   RW_TAC bool_ss [IN_FUNSET, IN_GTNUM, BIT1, IN_INTER, IN_UNIV,
                   NUMERAL_DEF, ALT_ZERO, BIT2]
   >> DECIDE_TAC);

val NUMERAL_BIT2_SUBTYPE = store_thm
  ("NUMERAL_BIT2_SUBTYPE",
   ``BIT2 IN (UNIV -> gtnum 1)``,
   RW_TAC bool_ss [IN_FUNSET, IN_GTNUM, BIT1, IN_INTER, IN_UNIV,
                   NUMERAL_DEF, ALT_ZERO, BIT2]
   >> DECIDE_TAC);

val NUMERAL_SUBTYPE = store_thm
  ("NUMERAL_SUBTYPE",
   ``!x. NUMERAL IN (x -> x)``,
   RW_TAC std_ss [IN_FUNSET, NUMERAL_DEF]);

val GTNUM0_SUBTYPE_REWRITE = store_thm
  ("GTNUM0_SUBTYPE_REWRITE",
   ``!n. n IN gtnum 0 ==> 0 < n /\ ~(n = 0) /\ ~(0 = n)``,
   RW_TAC arith_ss [IN_GTNUM]);

val GTNUM1_SUBTYPE_REWRITE = store_thm
  ("GTNUM1_SUBTYPE_REWRITE",
   ``!n. n IN gtnum 1 ==> 1 < n /\ ~(n = 1) /\ ~(1 = n)``,
   RW_TAC arith_ss [IN_GTNUM]);

val SQUARED_GT_1 = store_thm
  ("SQUARED_GT_1",
   ``!n : num. (n * n = n) <=> ~(1 < n)``,
   Cases >- RW_TAC arith_ss []
   >> Cases_on `n'` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [MULT]
   >> DECIDE_TAC);

val MOD_LESS_1 = store_thm
  ("MOD_LESS_1",
   ``!a n. 0 < n ==> (a MOD n <= a)``,
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`n`, `a`] DIVISION_ALT)
   >> DECIDE_TAC);

val MULT_EXP = store_thm
  ("MULT_EXP",
   ``!a b n. (a * b) EXP n = a EXP n * b EXP n``,
   Induct_on `n` >- RW_TAC arith_ss [EXP]
   >> RW_TAC arith_ss [EXP]
   >> KILL_TAC
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]);

val EXP_MULT = store_thm
  ("EXP_MULT",
   ``!n a b. (n EXP a) EXP b = n EXP (a * b)``,
   rpt STRIP_TAC
   >> Induct_on `b` >- RW_TAC arith_ss [EXP]
   >> RW_TAC arith_ss [EXP, MULT_CLAUSES, EXP_ADD]);

val LT_LE_1_MULT = store_thm
  ("LT_LE_1_MULT",
   ``!m n : num. 1 < m /\ 0 < n ==> 1 < m * n``,
   rpt STRIP_TAC
   >> Suff `~(m * n = 0) /\ ~(m * n = 1)` >- DECIDE_TAC
   >> RW_TAC arith_ss []);

Theorem EXP_MONO :
    !p a b. 1 < p ==> (p EXP a < p EXP b <=> a < b)
Proof
    Induct_on `b` >- RW_TAC arith_ss [EXP]
 >> rpt STRIP_TAC
 >> Cases_on `a`
 >> RW_TAC arith_ss [EXP]
QED

val MINUS_1_SQUARED_MOD = store_thm
  ("MINUS_1_SQUARED_MOD",
   ``!n. 1 < n ==> (((n - 1) * (n - 1)) MOD n = 1)``,
   rpt STRIP_TAC
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> RW_TAC std_ss [LEFT_SUB_DISTRIB]
   >> Suff `(n + ((n - 1) * n - (n - 1) * 1)) MOD n = 1`
   >- (Suff `!a. (n + a) MOD n = a MOD n`
       >- DISCH_THEN (fn th => REWRITE_TAC [th] >> RW_TAC std_ss [])
       >> Suff `!a. (n MOD n + a) MOD n = a MOD n`
       >- RW_TAC std_ss [MOD_PLUS1]
       >> RW_TAC arith_ss [X_MOD_X])
   >> Know `!a. n - 1 <= a ==> (n + (a - (n - 1)) = a + (n - (n - 1)))`
   >- DECIDE_TAC
   >> DISCH_THEN (MP_TAC o Q.SPEC `(n - 1) * n`)
   >> Know `n - 1 <= (n - 1) * n`
   >- (Cases_on `n` >- DECIDE_TAC
       >> RW_TAC arith_ss [MULT_CLAUSES])
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> STRIP_TAC
   >> ASM_REWRITE_TAC [MULT_RIGHT_1]
   >> Suff `(((n - 1) * (n MOD n)) MOD n + (n - (n - 1))) MOD n = 1`
   >- (EVERY (map (MP_TAC o Q.SPEC `n`) [MOD_PLUS1, MOD_MULT2])
       >> ASM_REWRITE_TAC []
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> DISCH_THEN (REWRITE_TAC o wrap))
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Know `n - (n - 1) = 1` >- DECIDE_TAC
   >> DISCH_THEN (fn th => RW_TAC arith_ss [th, X_MOD_X, LESS_MOD]));

val NUM_DOUBLE = store_thm
  ("NUM_DOUBLE",
   ``!n : num. n + n = 2 * n``,
   DECIDE_TAC);

val MOD_POWER_EQ_1 = store_thm
  ("MOD_POWER_EQ_1",
   ``!n x a b.
       1 < n /\ (x EXP a MOD n = 1) ==> (x EXP (a * b) MOD n = 1)``,
   Strip
   >> Simplify [GSYM EXP_MULT]
   >> Suff `((x EXP a) MOD n) EXP b MOD n = 1`
   >- RW_TAC arith_ss [MOD_EXP]
   >> ASM_REWRITE_TAC []
   >> RW_TAC arith_ss [EXP_1, LESS_MOD]);

val ODD_EXP = store_thm
  ("ODD_EXP",
   ``!n a. 0 < a ==> (ODD (n EXP a) = ODD n)``,
   STRIP_TAC
   >> Induct >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [EXP, ODD_MULT]
   >> Cases_on `a` >- RW_TAC arith_ss [EVEN_ODD_BASIC, EXP]
   >> RW_TAC arith_ss []);

val ODD_GT_1 = store_thm
  ("ODD_GT_1",
   ``!n. 1 < n /\ ODD n ==> 2 < n``,
   Cases >- Simplify []
   >> Cases_on `n'` >- Simplify []
   >> Cases_on `n` >- Simplify [GSYM ONE, GSYM TWO, EVEN_ODD_BASIC]
   >> DISCH_THEN K_TAC
   >> DECIDE_TAC);

val MINUS_1_MULT_MOD = store_thm
  ("MINUS_1_MULT_MOD",
   ``!a b. 0 < a /\ 0 < b ==> ((a * b - 1) MOD b = b - 1)``,
   Strip
   >> Cases_on `a` >- DECIDE_TAC
   >> RW_TAC std_ss [MULT]
   >> Know `!c. c + b - 1 = c + (b - 1)` >- DECIDE_TAC
   >> RW_TAC std_ss []
   >> POP_ASSUM K_TAC
   >> Suff `((n * b) MOD b + (b - 1)) MOD b = b - 1`
   >- RW_TAC std_ss [MOD_PLUS1]
   >> RW_TAC std_ss [MOD_EQ_0]
   >> RW_TAC arith_ss [MOD_EQ_X]);

Theorem EXP2_MONO_LE :
    !a b n. 0 < n /\ a <= b ==> a EXP n <= b EXP n
Proof
    Strip
 >> Induct_on `n` >- DECIDE_TAC
 >> RW_TAC arith_ss [EXP]
QED

val EXP1_MONO_LE = store_thm
  ("EXP1_MONO_LE",
   ``!n a b. 0 < n /\ a <= b ==> n EXP a <= n EXP b``,
   Strip
   >> Cases_on `a = b` >- Simplify []
   >> Cases_on `n = 1` >- Simplify [EXP_1]
   >> Suff `n EXP a < n EXP b` >- DECIDE_TAC
   >> Know `1 < n /\ a < b` >- DECIDE_TAC
   >> RW_TAC std_ss [EXP_MONO]);

val TRANSFORM_2D_NUM = store_thm
  ("TRANSFORM_2D_NUM",
   ``!P.
       (!m n : num. P m n ==> P n m) /\ (!m n. P m (m + n)) ==> (!m n. P m n)``,
   Strip
   >> Know `m <= n \/ n <= m` >- DECIDE_TAC
   >> RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC []);

val TRIANGLE_2D_NUM = store_thm
  ("TRIANGLE_2D_NUM",
   ``!P. (!d n. P n (d + n)) ==> (!m n : num. m <= n ==> P m n)``,
   RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC [ADD_COMM]);

val MAX_LE_X = store_thm
  ("MAX_LE_X",
   ``!m n k. MAX m n <= k <=> m <= k /\ n <= k``,
   RW_TAC arith_ss [MAX_DEF]);

val X_LE_MAX = store_thm
  ("X_LE_MAX",
   ``!m n k. k <= MAX m n <=> k <= m \/ k <= n``,
   RW_TAC arith_ss [MAX_DEF]);

val SUC_DIV_TWO_ZERO = store_thm
  ("SUC_DIV_TWO_ZERO",
   ``!n. (SUC n DIV 2 = 0) <=> (n = 0)``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC
   >- (MP_TAC DIV_TWO_BASIC
       >> Know `SUC 0 = 1` >- DECIDE_TAC
       >> RW_TAC arith_ss [])
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `SUC n` DIV_TWO)
   >> RW_TAC arith_ss [MULT_CLAUSES, MOD_TWO]);

val LOG2_LOWER = store_thm
  ("LOG2_LOWER",
   ``!n. n < 2 EXP log2 n``,
   recInduct log2_ind
   >> RW_TAC arith_ss [log2_def, EXP]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [DIV_TWO_EXP, EXP]);

val LOG2_LOWER_SUC = store_thm
  ("LOG2_LOWER_SUC",
   ``!n. SUC n <= 2 EXP log2 n``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `n` LOG2_LOWER)
   >> DECIDE_TAC);

val LOG2_UPPER = store_thm
  ("LOG2_UPPER",
   ``!n. ~(n = 0) ==> 2 EXP log2 n <= 2 * n``,
   recInduct log2_ind
   >> RW_TAC arith_ss [log2_def, EXP]
   >> Cases_on `SUC v DIV 2 = 0`
   >- (POP_ASSUM MP_TAC
       >> RW_TAC std_ss [SUC_DIV_TWO_ZERO]
       >> RW_TAC arith_ss [DECIDE ``SUC 0 = 1``, DIV_TWO_BASIC,
                           log2_def, EXP])
   >> RES_TAC
   >> POP_ASSUM MP_TAC
   >> KILL_TAC
   >> Q.SPEC_TAC (`SUC v`, `n`)
   >> GEN_TAC
   >> Q.SPEC_TAC (`2 EXP log2 (n DIV 2)`, `m`)
   >> GEN_TAC
   >> Suff `2 * (n DIV 2) <= n` >- DECIDE_TAC
   >> MP_TAC (Q.SPEC `n` DIV_TWO)
   >> DECIDE_TAC);

val LOG2_UPPER_SUC = store_thm
  ("LOG2_UPPER_SUC",
   ``!n. 2 EXP log2 n <= SUC (2 * n)``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `n` LOG2_UPPER)
   >> REVERSE (Cases_on `n = 0`) >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [log2_def, EXP]);

val _ = export_theory ();
