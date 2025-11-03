Theory extra_num
Ancestors
  arithmetic pred_set subtype extra_bool combin
Libs
  hurdUtils res_quanTools

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val Simplify = RW_TAC arith_ss;
val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

(* ------------------------------------------------------------------------- *)
(* Needed for definitions.                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem DIV_THEN_MULT:
     !p q. SUC q * (p DIV SUC q) <= p
Proof
   NTAC 2 STRIP_TAC
   >> Know `?r. p = (p DIV SUC q) * SUC q + r`
   >- (Know `0 < SUC q` >- DECIDE_TAC
       >> PROVE_TAC [DIVISION])
   >> STRIP_TAC
   >> Suff `p = SUC q * (p DIV SUC q) + r`
   >- (KILL_TAC >> DECIDE_TAC)
   >> PROVE_TAC [MULT_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = hide "min"; (* already defined for real numbers *)
Definition min_def:   min (m:num) n = if m <= n then m else n
End

Definition gtnum_def:   gtnum (n : num) x = (n < x)
End

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

Theorem SUC_0:
     SUC 0 = 1
Proof
   DECIDE_TAC
QED

Theorem LESS_0_MULT2:
     !m n : num. 0 < m * n <=> 0 < m /\ 0 < n
Proof
   rpt STRIP_TAC
   >> Cases_on `m` >- RW_TAC arith_ss []
   >> Cases_on `n` >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [MULT]
QED

Theorem LESS_1_MULT2:
     !m n : num. 1 < m /\ 1 < n ==> 1 < m * n
Proof
   rpt STRIP_TAC
   >> Suff `~(m * n = 0) /\ ~(m * n = 1)` >- DECIDE_TAC
   >> CONJ_TAC
   >> ONCE_REWRITE_TAC [MULT_EQ_0, MULT_EQ_1]
   >> DECIDE_TAC
QED

Theorem FUNPOW_SUC:
     !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
Proof
   Induct_on `n` >- RW_TAC std_ss [FUNPOW]
   >> ONCE_REWRITE_TAC [FUNPOW]
   >> RW_TAC std_ss []
QED

Theorem EVEN_ODD_BASIC:
     EVEN 0 /\ ~EVEN 1 /\ EVEN 2 /\ ~ODD 0 /\ ODD 1 /\ ~ODD 2
Proof
   CONV_TAC (TOP_DEPTH_CONV Num_conv.num_CONV)
   >> RW_TAC arith_ss [EVEN, ODD]
QED

Theorem EVEN_ODD_EXISTS_EQ:
     !n. (EVEN n = ?m. n = 2 * m) /\ (ODD n = ?m. n = SUC (2 * m))
Proof
   PROVE_TAC [EVEN_ODD_EXISTS, EVEN_DOUBLE, ODD_DOUBLE]
QED

Theorem MOD_1:
     !n : num. n MOD 1 = 0
Proof
   PROVE_TAC [SUC_0, MOD_ONE]
QED

Theorem DIV_1:
     !n : num. n DIV 1 = n
Proof
   PROVE_TAC [SUC_0, DIV_ONE]
QED

Theorem MOD_LESS:
     !n k : num. 0 < n ==> k MOD n < n
Proof
   PROVE_TAC [DIVISION]
QED

Theorem X_MOD_X:
     !n. 0 < n ==> (n MOD n = 0)
Proof PROVE_TAC [DIVMOD_ID]
QED

Theorem LESS_MOD_EQ:
     !x n. x < n ==> (x MOD n = x)
Proof
   REPEAT STRIP_TAC
   >> MP_TAC (Q.SPECL [`x`, `n`] LESS_DIV_EQ_ZERO)
   >> ASM_REWRITE_TAC []
   >> STRIP_TAC
   >> MP_TAC (Q.SPEC `n` DIVISION)
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `x`)
   >> RW_TAC arith_ss []
QED

Theorem MOD_PLUS1:
     !n a b. 0 < n ==> ((a MOD n + b) MOD n = (a + b) MOD n)
Proof
   RW_TAC arith_ss []
   >> MP_TAC (Q.SPEC `n` MOD_PLUS)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   >> RW_TAC arith_ss [MOD_MOD]
QED

Theorem MOD_PLUS2:
     !n a b. 0 < n ==> ((a + b MOD n) MOD n = (a + b) MOD n)
Proof
   PROVE_TAC [MOD_PLUS1, ADD_COMM]
QED

Theorem MOD_MULT1:
     !n a b. 0 < n ==> ((a MOD n * b) MOD n = (a * b) MOD n)
Proof
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
   >> RW_TAC std_ss []
QED

Theorem MOD_MULT2:
     !n a b. 0 < n ==> ((a * b MOD n) MOD n = (a * b) MOD n)
Proof
   PROVE_TAC [MOD_MULT1, MULT_COMM]
QED

Theorem DIVISION_ALT:
     !n k. 0 < n ==> (k DIV n * n + k MOD n = k)
Proof
   PROVE_TAC [DIVISION]
QED

Theorem MOD_EQ_X:
     !n r. 0 < n ==> ((r MOD n = r) <=> r < n)
Proof
   rpt STRIP_TAC
   >> REVERSE EQ_TAC >- PROVE_TAC [LESS_MOD]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [SYM th])
   >> RW_TAC std_ss [MOD_LESS]
QED

Theorem DIV_EQ_0:
     !n r. 0 < n ==> ((r DIV n = 0) <=> r < n)
Proof
   rpt STRIP_TAC
   >> REVERSE EQ_TAC >- PROVE_TAC [LESS_DIV_EQ_ZERO]
   >> STRIP_TAC
   >> Know `r DIV n * n + r MOD n = r`
   >- RW_TAC std_ss [DIVISION_ALT]
   >> RW_TAC arith_ss [MOD_EQ_X]
QED

Theorem MOD_EXP:
     !n a b. 0 < n ==> ((a MOD n) EXP b MOD n = a EXP b MOD n)
Proof
   NTAC 2 STRIP_TAC
   >> Induct >- RW_TAC std_ss [EXP]
   >> STRIP_TAC
   >> RES_TAC
   >> RW_TAC std_ss
      [EXP, GSYM (Q.SPECL [`n`, `a MOD n`, `(a MOD n) EXP b`] MOD_MULT2)]
   >> RW_TAC std_ss [MOD_MULT1, MOD_MULT2]
QED

Theorem DIV_TWO_UNIQUE:
  !n q r. n = 2 * q + r /\ (r = 0 \/ r = 1) ==>
          q = n DIV 2 /\ r = n MOD 2
Proof
  simp[DISJ_IMP_THM]
QED

Theorem DIVISION_TWO:
     !n. (n = 2 * (n DIV 2) + (n MOD 2)) /\ ((n MOD 2 = 0) \/ (n MOD 2 = 1))
Proof
   STRIP_TAC
   >> MP_TAC (Q.SPEC `2` DIVISION)
   >> Know `0:num < 2` >- DECIDE_TAC
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
   >> RW_TAC bool_ss [] >|
   [PROVE_TAC [MULT_COMM],
    DECIDE_TAC]
QED

Theorem DIV_TWO:
     !n. n = 2 * (n DIV 2) + (n MOD 2)
Proof
   PROVE_TAC [DIVISION_TWO]
QED

Theorem MOD_TWO:
     !n. n MOD 2 = if EVEN n then 0 else 1
Proof
   STRIP_TAC
   >> MP_TAC (Q.SPEC `n` DIVISION_TWO)
   >> STRIP_TAC >|
   [Q.PAT_ASSUM `n = X` MP_TAC
    >> RW_TAC std_ss []
    >> PROVE_TAC [EVEN_DOUBLE, ODD_EVEN, ADD_CLAUSES],
    Q.PAT_ASSUM `n = X` MP_TAC
    >> RW_TAC std_ss []
    >> PROVE_TAC [ODD_DOUBLE, ODD_EVEN, ADD1]]
QED

Theorem DIV_TWO_BASIC:
     (0 DIV 2 = 0) /\ (1 DIV 2 = 0) /\ (2 DIV 2 = 1)
Proof
   Know `(0:num = 2 * 0 + 0) /\ (1:num = 2 * 0 + 1) /\ (2:num = 2 * 1 + 0)`
   >- RW_TAC arith_ss []
   >> PROVE_TAC [DIV_TWO_UNIQUE]
QED

Theorem DIV_TWO_MONO:
     !m n. m DIV 2 < n DIV 2 ==> m < n
Proof
   NTAC 2 STRIP_TAC
   >> (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   >> Q.SPEC_TAC (`m DIV 2`, `p`)
   >> Q.SPEC_TAC (`n DIV 2`, `q`)
   >> REPEAT STRIP_TAC
   >> Know `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> Know `(n MOD 2 = 0) \/ (n MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> DECIDE_TAC
QED

Theorem DIV_TWO_MONO_EVEN:
     !m n. EVEN n ==> (m DIV 2 < n DIV 2 <=> m < n)
Proof
   RW_TAC std_ss []
   >> EQ_TAC >- PROVE_TAC [DIV_TWO_MONO]
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [DIV_TWO]
   >> Q.SPEC_TAC (`m DIV 2`, `p`)
   >> Q.SPEC_TAC (`n DIV 2`, `q`)
   >> REPEAT STRIP_TAC
   >> Know `n MOD 2 = 0` >- PROVE_TAC [MOD_TWO]
   >> Know `(m MOD 2 = 0) \/ (m MOD 2 = 1)` >- PROVE_TAC [MOD_TWO]
   >> DECIDE_TAC
QED

Theorem DIV_TWO_CANCEL:
  !n. (2 * n DIV 2 = n) /\ (SUC (2 * n) DIV 2 = n)
Proof
  RW_TAC std_ss [ADD1]
QED

Theorem EXP_DIV_TWO:
     !n. 2 EXP SUC n DIV 2 = 2 EXP n
Proof
   RW_TAC std_ss [EXP, DIV_TWO_CANCEL]
QED

Theorem EVEN_EXP_TWO:
     !n. EVEN (2 EXP n) = ~(n = 0)
Proof
   Cases >- RW_TAC arith_ss [EXP, EVEN_ODD_BASIC]
   >> RW_TAC arith_ss [EXP, EVEN_DOUBLE]
QED

Theorem DIV_TWO_EXP:
     !n k. k DIV 2 < 2 EXP n <=> k < 2 EXP SUC n
Proof
   RW_TAC std_ss []
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [GSYM EXP_DIV_TWO]
   >> MATCH_MP_TAC DIV_TWO_MONO_EVEN
   >> RW_TAC std_ss [EVEN_EXP_TWO]
QED

Theorem MIN_0L:
     !n : num. min 0 n = 0
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem MIN_0R:
     !n : num. min n 0 = 0
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem MIN_REFL:
     !a : num. min a a = a
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem MIN_SYM:
     !a b : num. min a b = min b a
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem LEQ_MINL:
     !a b : num. a <= b ==> (min a b = a)
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem LEQ_MINR:
     !a b : num. a <= b ==> (min b a = a)
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem LESS_MINL:
     !a b : num. a < b ==> (min a b = a)
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem LESS_MINR:
     !a b : num. a < b ==> (min b a = a)
Proof
   RW_TAC arith_ss [min_def]
QED

Theorem IN_GTNUM:
     !x n : num. x IN gtnum n <=> n < x
Proof
   RW_TAC std_ss [gtnum_def, SPECIFICATION]
QED

Theorem GTNUM0_SUBTYPE_JUDGEMENT:
     !m n.
       SUC m <= n \/ m < n \/ ~(0 = n) \/ ~(n = 0) \/
       (n = SUC m) \/ (SUC m = n) ==> n IN gtnum 0
Proof
   RW_TAC std_ss [IN_GTNUM]
   >> DECIDE_TAC
QED

Theorem GTNUM1_SUBTYPE_JUDGEMENT:
     !m n. SUC (SUC m) <= n \/ SUC m < n \/ 1 < n \/
           (n = SUC (SUC m)) \/ (SUC (SUC m) = n) ==> n IN gtnum 1
Proof
   RW_TAC std_ss [IN_GTNUM]
   >> DECIDE_TAC
QED

Theorem GTNUM1_SUBSET_GTNUM0:
     gtnum 1 SUBSET gtnum 0
Proof
   RW_TAC std_ss [SUBSET_DEF, IN_GTNUM]
   >> DECIDE_TAC
QED

Theorem SUC_SUBTYPE:
     SUC IN ((UNIV -> gtnum 0) INTER (gtnum 0 -> gtnum 1))
Proof
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
   >> DECIDE_TAC
QED

Theorem ADD_SUBTYPE:
     !n. $+ IN ((UNIV -> gtnum n -> gtnum n) INTER (gtnum n -> UNIV -> gtnum n)
                INTER (gtnum 0 -> gtnum 0 -> gtnum 1))
Proof
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
   >> DECIDE_TAC
QED

Theorem MULT_SUBTYPE:
     $* IN ((gtnum 0 -> gtnum 0 -> gtnum 0) INTER
            (gtnum 1 -> gtnum 0 -> gtnum 1) INTER
            (gtnum 0 -> gtnum 1 -> gtnum 1))
Proof
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM, LESS_MULT2] >|
   [Cases_on `x' = 1` >- RW_TAC arith_ss []
    >> Know `1 < x'` >- DECIDE_TAC
    >> RW_TAC std_ss [LESS_1_MULT2],
    Cases_on `x = 1` >- RW_TAC arith_ss []
    >> Know `1 < x` >- DECIDE_TAC
    >> RW_TAC std_ss [LESS_1_MULT2]]
QED

Theorem MIN_SUBTYPE:
     !x. min IN (x -> x -> x)
Proof
   RW_TAC arith_ss [IN_FUNSET, min_def]
   >> PROVE_TAC []
QED

Theorem EXP_SUBTYPE:
  $EXP IN ((gtnum 0 -> UNIV -> gtnum 0) INTER
           (gtnum 1 -> gtnum 0 -> gtnum 1))
Proof
  RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_UNIV, IN_GTNUM]
QED

Theorem FUNPOW_SUBTYPE:
     !(x:'a->bool). FUNPOW IN ((x -> x) -> UNIV -> x -> x)
Proof
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`x'''`, `y`)
   >> Induct_on `x''` >- RW_TAC std_ss [FUNPOW]
   >> RW_TAC std_ss [FUNPOW]
QED

Theorem NUMERAL_BIT1_SUBTYPE:
     BIT1 IN ((UNIV -> gtnum 0) INTER (gtnum 0 -> gtnum 1))
Proof
   RW_TAC bool_ss [IN_FUNSET, IN_GTNUM, BIT1, IN_INTER, IN_UNIV,
                   NUMERAL_DEF, ALT_ZERO, BIT2]
   >> DECIDE_TAC
QED

Theorem NUMERAL_BIT2_SUBTYPE:
     BIT2 IN (UNIV -> gtnum 1)
Proof
   RW_TAC bool_ss [IN_FUNSET, IN_GTNUM, BIT1, IN_INTER, IN_UNIV,
                   NUMERAL_DEF, ALT_ZERO, BIT2]
   >> DECIDE_TAC
QED

Theorem NUMERAL_SUBTYPE:
     !x. NUMERAL IN (x -> x)
Proof
   RW_TAC std_ss [IN_FUNSET, NUMERAL_DEF]
QED

Theorem GTNUM0_SUBTYPE_REWRITE:
     !n. n IN gtnum 0 ==> 0 < n /\ ~(n = 0) /\ ~(0 = n)
Proof
   RW_TAC arith_ss [IN_GTNUM]
QED

Theorem GTNUM1_SUBTYPE_REWRITE:
     !n. n IN gtnum 1 ==> 1 < n /\ ~(n = 1) /\ ~(1 = n)
Proof
   RW_TAC arith_ss [IN_GTNUM]
QED

Theorem SQUARED_GT_1:
     !n : num. (n * n = n) <=> ~(1 < n)
Proof
   Cases >- RW_TAC arith_ss []
   >> Cases_on `n'` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [MULT]
   >> DECIDE_TAC
QED

Theorem MOD_LESS_1:
     !a n. 0 < n ==> (a MOD n <= a)
Proof
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`n`, `a`] DIVISION_ALT)
   >> DECIDE_TAC
QED

Theorem MULT_EXP:
     !a b n. (a * b) EXP n = a EXP n * b EXP n
Proof
   Induct_on `n` >- RW_TAC arith_ss [EXP]
   >> RW_TAC arith_ss [EXP]
   >> KILL_TAC
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]
QED

Theorem EXP_MULT:
     !n a b. (n EXP a) EXP b = n EXP (a * b)
Proof
   rpt STRIP_TAC
   >> Induct_on `b` >- RW_TAC arith_ss [EXP]
   >> RW_TAC arith_ss [EXP, MULT_CLAUSES, EXP_ADD]
QED

Theorem LT_LE_1_MULT:
     !m n : num. 1 < m /\ 0 < n ==> 1 < m * n
Proof
   rpt STRIP_TAC
   >> Suff `~(m * n = 0) /\ ~(m * n = 1)` >- DECIDE_TAC
   >> RW_TAC arith_ss []
QED

Theorem EXP_MONO :
    !p a b. 1 < p ==> (p EXP a < p EXP b <=> a < b)
Proof
    Induct_on `b` >- RW_TAC arith_ss [EXP]
 >> rpt STRIP_TAC
 >> Cases_on `a`
 >> RW_TAC arith_ss [EXP]
QED

Theorem MINUS_1_SQUARED_MOD:
     !n. 1 < n ==> (((n - 1) * (n - 1)) MOD n = 1)
Proof
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
   >> DISCH_THEN (fn th => RW_TAC arith_ss [th, X_MOD_X, LESS_MOD])
QED

Theorem NUM_DOUBLE:
     !n : num. n + n = 2 * n
Proof
   DECIDE_TAC
QED

Theorem MOD_POWER_EQ_1:
     !n x a b.
       1 < n /\ (x EXP a MOD n = 1) ==> (x EXP (a * b) MOD n = 1)
Proof
   Strip
   >> Simplify [GSYM EXP_MULT]
   >> Suff `((x EXP a) MOD n) EXP b MOD n = 1`
   >- RW_TAC arith_ss [MOD_EXP]
   >> ASM_REWRITE_TAC []
   >> RW_TAC arith_ss [EXP_1, LESS_MOD]
QED

Theorem ODD_EXP:
     !n a. 0 < a ==> (ODD (n EXP a) = ODD n)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [EXP, ODD_MULT]
   >> Cases_on `a` >- RW_TAC arith_ss [EVEN_ODD_BASIC, EXP]
   >> RW_TAC arith_ss []
QED

Theorem ODD_GT_1:
     !n. 1 < n /\ ODD n ==> 2 < n
Proof
   Cases >- Simplify []
   >> Cases_on `n'` >- Simplify []
   >> Cases_on `n` >- Simplify [GSYM ONE, GSYM TWO, EVEN_ODD_BASIC]
   >> DISCH_THEN K_TAC
   >> DECIDE_TAC
QED

Theorem MINUS_1_MULT_MOD:
     !a b. 0 < a /\ 0 < b ==> ((a * b - 1) MOD b = b - 1)
Proof
   Strip
   >> Cases_on `a` >- DECIDE_TAC
   >> RW_TAC std_ss [MULT]
   >> Know `!c. c + b - 1 = c + (b - 1)` >- DECIDE_TAC
   >> RW_TAC std_ss []
   >> POP_ASSUM K_TAC
   >> Suff `((n * b) MOD b + (b - 1)) MOD b = b - 1`
   >- RW_TAC std_ss [MOD_PLUS1]
   >> RW_TAC std_ss [MOD_EQ_0]
   >> RW_TAC arith_ss [MOD_EQ_X]
QED

Theorem EXP2_MONO_LE :
    !a b n. 0 < n /\ a <= b ==> a EXP n <= b EXP n
Proof
    Strip
 >> Induct_on `n` >- DECIDE_TAC
 >> RW_TAC arith_ss [EXP]
QED

Theorem EXP1_MONO_LE:
     !n a b. 0 < n /\ a <= b ==> n EXP a <= n EXP b
Proof
   Strip
   >> Cases_on `a = b` >- Simplify []
   >> Cases_on `n = 1` >- Simplify [EXP_1]
   >> Suff `n EXP a < n EXP b` >- DECIDE_TAC
   >> Know `1 < n /\ a < b` >- DECIDE_TAC
   >> RW_TAC std_ss [EXP_MONO]
QED

Theorem TRANSFORM_2D_NUM:
     !P.
       (!m n : num. P m n ==> P n m) /\ (!m n. P m (m + n)) ==> (!m n. P m n)
Proof
   Strip
   >> Know `m <= n \/ n <= m` >- DECIDE_TAC
   >> RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC []
QED

Theorem TRIANGLE_2D_NUM:
     !P. (!d n. P n (d + n)) ==> (!m n : num. m <= n ==> P m n)
Proof
   RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC [ADD_COMM]
QED

Theorem MAX_LE_X:
     !m n k. MAX m n <= k <=> m <= k /\ n <= k
Proof
   RW_TAC arith_ss [MAX_DEF]
QED

Theorem X_LE_MAX:
     !m n k. k <= MAX m n <=> k <= m \/ k <= n
Proof
   RW_TAC arith_ss [MAX_DEF]
QED

Theorem SUC_DIV_TWO_ZERO:
     !n. (SUC n DIV 2 = 0) <=> (n = 0)
Proof
   RW_TAC std_ss []
   >> REVERSE EQ_TAC
   >- (MP_TAC DIV_TWO_BASIC
       >> Know `SUC 0 = 1` >- DECIDE_TAC
       >> RW_TAC arith_ss [])
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `SUC n` DIV_TWO)
   >> RW_TAC arith_ss [MULT_CLAUSES, MOD_TWO]
QED

Theorem LOG2_LOWER:
     !n. n < 2 EXP log2 n
Proof
   recInduct log2_ind
   >> RW_TAC arith_ss [log2_def, EXP]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [DIV_TWO_EXP, EXP]
QED

Theorem LOG2_LOWER_SUC:
     !n. SUC n <= 2 EXP log2 n
Proof
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `n` LOG2_LOWER)
   >> DECIDE_TAC
QED

Theorem LOG2_UPPER:
     !n. ~(n = 0) ==> 2 EXP log2 n <= 2 * n
Proof
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
   >> DECIDE_TAC
QED

Theorem LOG2_UPPER_SUC:
     !n. 2 EXP log2 n <= SUC (2 * n)
Proof
   STRIP_TAC
   >> MP_TAC (Q.SPEC `n` LOG2_UPPER)
   >> REVERSE (Cases_on `n = 0`) >- RW_TAC arith_ss []
   >> RW_TAC arith_ss [log2_def, EXP]
QED

