open HolKernel Parse boolLib bossLib;

open arithmeticTheory dividesTheory gcdTheory res_quanTheory pred_setTheory
     subtypeTheory res_quanTools subtypeTools ho_proverTools numContext
     hurdUtils extra_numTheory ho_basicTools;

val _ = new_theory "extra_arith";
val _ = ParseExtras.temp_loose_equality()

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS num_c;

val Strip = S_TAC;
val Simplify = R_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val is_lcm_def = Define
  `is_lcm a b l =
   divides a l /\ divides b l /\
   !n. divides a n /\ divides b n ==> divides l n`;

val lcm_def = Define
  `lcm a b = if (a = 0) /\ (b = 0) then 0 else (a * b) DIV gcd a b`;

Definition exponent_def:
  exponent m n = LEAST k. ~divides (m EXP SUC k) n
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val PRIME_SUBSET_GTNUM1 = store_thm
  ("PRIME_SUBSET_GTNUM1",
   ``!p. prime p ==> p IN gtnum 1``,
   S_TAC
   >> R_TAC [IN_GTNUM]
   >> Suff `~(p = 0) /\ ~(p = 1)` >- DECIDE_TAC
   >> PROVE_TAC [NOT_PRIME_1, NOT_PRIME_0]);

Theorem DIVIDES_ONE_UNIQUE = dividesTheory.DIVIDES_ONE

Theorem DIVIDES_MOD:
  !n a. 0 < n ==> ((a MOD n = 0) = divides n a)
Proof
  simp[dividesTheory.compute_divides, EQ_IMP_THM, DISJ_IMP_THM]
QED

val DIVIDES_UPR = store_thm
  ("DIVIDES_UPR",
   ``!n a. divides n (n * a)``,
   PROVE_TAC [DIVIDES_MULT, DIVIDES_REFL]);

val DIVIDES_UPL = store_thm
  ("DIVIDES_UPL",
   ``!n a. divides n (a * n)``,
   PROVE_TAC [DIVIDES_UPR, MULT_COMM]);

val DIVIDES_CANCEL = store_thm
  ("DIVIDES_CANCEL",
   ``!p a b. 0 < p ==> (divides (p * a) (p * b) = divides a b)``,
   S_TAC
   >> EQ_TAC >|
   [R_TAC [divides_def]
    >> S_TAC
    >> Q.EXISTS_TAC `q`
    >> Cases_on `p` >- AR_TAC []
    >> PROVE_TAC [MULT_COMM, MULT_ASSOC, MULT_MONO_EQ],
    R_TAC [divides_def]
    >> S_TAC
    >> Q.EXISTS_TAC `q`
    >> PROVE_TAC [MULT_COMM, MULT_ASSOC]]);

val DIVIDES_SUB = store_thm
  ("DIVIDES_SUB",
   ``!n a b. divides n a /\ divides n b ==> divides n (a - b)``,
   R_TAC [divides_def]
   >> S_TAC
   >> Q.EXISTS_TAC `q - q'`
   >> AR_TAC [RIGHT_SUB_DISTRIB]);

val DIFF_EXISTS = store_thm
  ("DIFF_EXISTS",
   ``!x:num y. ?c. (y = x + c) \/ (x = y + c)``,
   S_TAC
   >> (Know `y <= x \/ x <= y` >- DECIDE_TAC)
   >> S_TAC >|
   [Q.EXISTS_TAC `x - y`
    >> DECIDE_TAC,
    Q.EXISTS_TAC `y - x`
    >> DECIDE_TAC]);

val GCD_SUBTYPE = store_thm
  ("GCD_SUBTYPE",
   ``gcd IN ((gtnum 0 -> UNIV -> gtnum 0) INTER (UNIV -> gtnum 0 -> gtnum 0))``,
   R_TAC [IN_FUNSET, IN_GTNUM, IN_UNIV, IN_INTER]
   >> S_TAC >|
   [Suff `~(gcd x' x = 0)` >- DECIDE_TAC
    >> Know `~(x' = 0)` >- DECIDE_TAC
    >> R_TAC [GCD_EQ_0],
    Suff `~(gcd x' x = 0)` >- DECIDE_TAC
    >> Know `~(x = 0)` >- DECIDE_TAC
    >> R_TAC [GCD_EQ_0]]);

(* Consolidate theorems so far in a simplification context *)

val arith1_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [PRIME_SUBSET_GTNUM1] @
  map SC_SUBTYPE
  [GCD_SUBTYPE];

val arith1_pc =
  precontext_add
  ("arith1",
   map C_SUBTYPE arith1_sc @
   map C_THM
   [ALL_DIVIDES_0,
    DIVIDES_REFL,
    ONE_DIVIDES_ALL,
    DIVIDES_ONE_UNIQUE,
    DIVIDES_UPL,
    DIVIDES_UPR,
    DIVIDES_CANCEL,
    GCD_EQ_0])
  num_pc;

val arith1_c = precontext_compile arith1_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS arith1_c;

(* back to proving *)
val NOT_LT_DIV = dividesTheory.NOT_LT_DIVIDES

val PRIME_2 = store_thm
  ("PRIME_2",
   ``prime 2``,
   R_TAC [prime_def]
   >> S_TAC
   >> Cases_on `2 < b`
   >- (Know `0:num < 2` >- DECIDE_TAC
       >> PROVE_TAC [NOT_LT_DIV])
   >> Cases_on `b = 0` >- AR_TAC [divides_def]
   >> DECIDE_TAC);

val EXISTS_PRIME_DIVISOR = store_thm
  ("EXISTS_PRIME_DIVISOR",
   ``!n. ~(n = 1) = ?p. prime p /\ divides p n``,
   S_TAC
   >> REVERSE EQ_TAC >- (S_TAC >> AR_TAC [NOT_PRIME_1])
   >> Cases_on `n = 0` >- (R_TAC [] >> ho_PROVE_TAC [PRIME_2])
   >> completeInduct_on `n`
   >> S_TAC
   >> Cases_on `prime n` >- PROVE_TAC [DIVIDES_REFL]
   >> POP_ASSUM (MP_TAC o REWRITE_RULE [prime_def])
   >> R_TAC []
   >> S_TAC
   >> Cases_on `x = 0` >- AR_TAC [divides_def]
   >> Know `x < n`
   >- (Suff `~(n < x)` >- DECIDE_TAC
       >> Know `0 < n` >- DECIDE_TAC
       >> PROVE_TAC [NOT_LT_DIV])
   >> S_TAC
   >> RES_TAC
   >> PROVE_TAC [DIVIDES_TRANS]);

val DIVIDES_GCD = store_thm
  ("DIVIDES_GCD",
   ``!p a b. divides p (gcd a b) = divides p a /\ divides p b``,
   S_TAC
   >> EQ_TAC >|
   [Suff `!p a b g. divides p g /\ is_gcd a b g ==> divides p a`
    >- PROVE_TAC [GCD_SYM, GCD_IS_GCD]
    >> S_TAC
    >> AR_TAC [is_gcd_def]
    >> ho_PROVE_TAC [DIVIDES_TRANS],
    S_TAC
    >> Suff `!g. is_gcd a b g ==> divides p g` >- PROVE_TAC [GCD_IS_GCD]
    >> R_TAC [is_gcd_def]
    >> PROVE_TAC []]);

val GCD_1R = store_thm
  ("GCD_1R",
   ``!n. gcd n 1 = 1``,
   Suff `!n g. is_gcd n 1 g ==> (g = 1)` >- PROVE_TAC [GCD_IS_GCD]
   >> R_TAC [is_gcd_def]);

val GCD_1L = store_thm
  ("GCD_1L",
   ``!n. gcd 1 n = 1``,
   PROVE_TAC [GCD_1R, GCD_SYM]);

val GCD_1_MULTR = store_thm
  ("GCD_1_MULTR",
   ``!n a b. (gcd n (a * b) = 1) = (gcd n a = 1) /\ (gcd n b = 1)``,
   S_TAC
   >> EQ_TAC >|
   [Q.SPEC_TAC (`a`, `a`)
    >> Q.SPEC_TAC (`b`, `b`)
    >> Suff `!a b. (gcd n (a * b) = 1) ==> (gcd n a = 1)`
    >- ho_PROVE_TAC [MULT_COMM]
    >> S_TAC
    >> CCONTR_TAC
    >> MP_TAC (Q.SPEC `gcd n a` EXISTS_PRIME_DIVISOR)
    >> R_TAC []
    >> S_TAC
    >> Know `divides x (gcd n (a * b))`
    >- PROVE_TAC [DIVIDES_GCD, DIVIDES_MULT]
    >> ASM_REWRITE_TAC []
    >> R_TAC []
    >> PROVE_TAC [NOT_PRIME_1],
    S_TAC
    >> Suff `(?p. prime p /\ divides p (gcd n (a * b))) ==> F`
    >- ho_PROVE_TAC [EXISTS_PRIME_DIVISOR]
    >> R_TAC [DIVIDES_GCD]
    >> S_TAC
    >> MP_TAC (Q.SPECL [`x`, `a`, `b`] P_EUCLIDES)
    >> R_TAC []
    >> S_TAC >|
    [Know `divides x (gcd n a)` >- PROVE_TAC [DIVIDES_GCD]
     >> S_TAC
     >> AR_TAC [NOT_PRIME_1],
     Know `divides x (gcd n b)` >- PROVE_TAC [DIVIDES_GCD]
     >> S_TAC
     >> AR_TAC [NOT_PRIME_1]]]);

val GCD_1_MULTL = store_thm
  ("GCD_1_MULTL",
   ``!n a b. (gcd (a * b) n = 1) = (gcd a n = 1) /\ (gcd b n = 1)``,
   PROVE_TAC [GCD_1_MULTR, GCD_SYM]);

val SUC_MOD = store_thm
  ("SUC_MOD",
   ``!m n.
       0 < n ==>
       (SUC m MOD n = if divides n (SUC m) then 0 else SUC (m MOD n))``,
   S_TAC
   >> MATCH_MP_TAC MOD_UNIQUE
   >> Cases_on `divides n (SUC m)` >- AR_TAC [divides_def]
   >> R_TAC []
   >> Q.EXISTS_TAC `m DIV n`
   >> R_TAC [DIVISION_ALT, ADD_CLAUSES]
   >> Suff `~(SUC (m MOD n) = n)`
   >- (Know `m MOD n < n` >- R_TAC []
       >> Q.SPEC_TAC (`m MOD n`, `a`)
       >> KILL_TAC
       >> DECIDE_TAC)
   >> Cases_on `n` >- R_TAC []
   >> R_TAC []
   >> S_TAC
   >> Q.PAT_X_ASSUM `~divides x y` MP_TAC
   >> R_TAC [divides_def]
   >> Q.EXISTS_TAC `SUC (m DIV SUC n')`
   >> R_TAC [MULT, ADD_CLAUSES]
   >> PROVE_TAC [Q.SPEC `SUC n'` DIVISION_ALT]);

val DIVIDES_ALT = store_thm
  ("DIVIDES_ALT",
   ``!a b. 0 < a ==> (divides a b = ((b DIV a) * a = b))``,
   S_TAC
   >> R_TAC [divides_def]
   >> REVERSE EQ_TAC >- PROVE_TAC []
   >> S_TAC
   >> Suff `b DIV a = q` >- R_TAC []
   >> MATCH_MP_TAC DIV_UNIQUE
   >> Q.EXISTS_TAC `0`
   >> R_TAC []);

val SUC_DIV = store_thm
  ("SUC_DIV",
   ``!n m.
       0 < n ==>
       (SUC m DIV n = if divides n (SUC m) then SUC (m DIV n) else m DIV n)``,
   S_TAC
   >> MATCH_MP_TAC DIV_UNIQUE
   >> Q.EXISTS_TAC `SUC m MOD n`
   >> R_TAC []
   >> REVERSE (Cases_on `divides n (SUC m)`)
   >- R_TAC [ADD_CLAUSES, SUC_MOD, DIVISION_ALT]
   >> R_TAC [MULT_CLAUSES, SUC_MOD]
   >> POP_ASSUM MP_TAC
   >> R_TAC [divides_def]
   >> S_TAC
   >> Cases_on `q` >- AR_TAC []
   >> Know `m DIV n = n'`
   >- (MATCH_MP_TAC DIV_UNIQUE
       >> Cases_on `n` >- AR_TAC []
       >> Q.EXISTS_TAC `n''`
       >> Know `SUC m = n' * SUC n'' + SUC n''` >- AR_TAC [MULT_CLAUSES]
       >> KILL_TAC
       >> R_TAC []
       >> DECIDE_TAC)
   >> R_TAC [MULT_CLAUSES]);

val GCD_1_PRIMEL = store_thm
  ("GCD_1_PRIMEL",
   ``!p b. prime p ==> ((gcd p b = 1) = ~divides p b)``,
   S_TAC
   >> REVERSE EQ_TAC >- ho_PROVE_TAC [PRIME_GCD]
   >> S_TAC
   >> Suff `divides p 1` >- PROVE_TAC [DIVIDES_ONE_UNIQUE, NOT_PRIME_1]
   >> Suff `divides p (gcd p b)` >- R_TAC []
   >> R_TAC [DIVIDES_GCD]);

val GCD_1_PRIMER = store_thm
  ("GCD_1_PRIMER",
   ``!p b. prime p ==> ((gcd b p = 1) = ~divides p b)``,
   PROVE_TAC [GCD_1_PRIMEL, GCD_SYM]);

val DIVIDES_PRIME = store_thm
  ("DIVIDES_PRIME",
   ``!p n. prime p ==> (divides n p = (n = 1) \/ (n = p))``,
   R_TAC [prime_def]
   >> S_TAC
   >> EQ_TAC >- PROVE_TAC []
   >> S_TAC
   >> R_TAC []);

val DIVIDES_PRIME_POWER = store_thm
  ("DIVIDES_PRIME_POWER",
   ``!p n r. prime p ==> (divides n (p EXP r) = ?s. s <= r /\ (n = p EXP s))``,
   S_TAC
   >> Q.SPEC_TAC (`n`, `n`)
   >> Induct_on `r` >- (R_TAC [EXP] >> ho_PROVE_TAC [])
   >> S_TAC
   >> REVERSE EQ_TAC
   >- (S_TAC
       >> R_TAC []
       >> Cases_on `s` >- R_TAC [EXP]
       >> R_TAC [EXP, DIVIDES_CANCEL]
       >> Q.EXISTS_TAC `n'`
       >> AR_TAC [])
   >> R_TAC [EXP]
   >> S_TAC
   >> Cases_on `gcd p n = 1` >|
   [MP_TAC (Q.SPECL [`p`, `n`, `p EXP r`] L_EUCLIDES)
    >> R_TAC []
    >> S_TAC
    >> Q.EXISTS_TAC `s`
    >> R_TAC []
    >> DECIDE_TAC,
    POP_ASSUM MP_TAC
    >> R_TAC [GCD_1_PRIMEL, divides_def]
    >> ONCE_REWRITE_TAC [MULT_COMM]
    >> S_TAC
    >> AR_TAC []
    >> S_TAC
    >> Q.EXISTS_TAC `SUC s`
    >> R_TAC [EXP]]);

val PRIME_DIVIDES_PRIME = store_thm
  ("PRIME_DIVIDES_PRIME",
   ``!p q. prime p /\ prime q ==> (divides p q = (p = q))``,
   R_TAC [DIVIDES_PRIME]);

val EUCLID = store_thm
  ("EUCLID",
   ``!p a b. prime p ==> (divides p (a * b) = divides p a \/ divides p b)``,
   PROVE_TAC [P_EUCLIDES, MULT_COMM, DIVIDES_MULT]);

val PRIME_DIVIDES_PRIME_POWER = store_thm
  ("PRIME_DIVIDES_PRIME_POWER",
   ``!p q a.
       prime p /\ prime q /\ 0 < a ==> (divides p (q EXP a) = (p = q))``,
   S_TAC
   >> R_TAC [DIVIDES_PRIME_POWER]
   >> Cases_on `p = q`
   >- (R_TAC []
       >> Q.EXISTS_TAC `1`
       >> R_TAC []
       >> DECIDE_TAC)
   >> R_TAC []
   >> Suff `!x. ~divides p (q EXP x)` >- ho_PROVE_TAC [DIVIDES_REFL]
   >> Induct >- R_TAC []
   >> R_TAC [EXP, EUCLID, PRIME_DIVIDES_PRIME]);

val GCD_1_PRIME_POWERL = store_thm
  ("GCD_1_PRIME_POWERL",
   ``!p n a. prime p /\ 0 < a ==> ((gcd (p EXP a) n = 1) = ~divides p n)``,
   S_TAC
   >> EQ_TAC >|
   [S_TAC
    >> Know `divides p (p EXP a)`
    >- (Cases_on `a` >- AR_TAC [] >> R_TAC [EXP])
    >> STRIP_TAC
    >> Know `divides p (gcd (p EXP a) n)` >- R_TAC [DIVIDES_GCD]
    >> R_TAC []
    >> PROVE_TAC [NOT_PRIME_1],
    S_TAC
    >> Suff `!q. prime q ==> ~divides q (gcd (p EXP a) n)`
    >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
    >> R_TAC [DIVIDES_GCD, PRIME_DIVIDES_PRIME_POWER]]);

val GCD_1_PRIME_POWERR = store_thm
  ("GCD_1_PRIME_POWERR",
   ``!p n a. prime p /\ 0 < a ==> ((gcd n (p EXP a) = 1) = ~divides p n)``,
   S_TAC
   >> MP_TAC (Q.SPECL [`p`, `n`, `a`] GCD_1_PRIME_POWERL)
   >> PROVE_TAC [GCD_SYM]);

val FACTOR_INDUCT = store_thm
  ("FACTOR_INDUCT",
   ``!prop.
        prop 0 /\
        prop 1 /\
        (!n p. prime p /\ prop n ==> prop (p * n)) ==>
        !n. prop n``,
   S_TAC
   >> completeInduct_on `n`
   >> Cases_on `n = 0` >- (Q.PAT_X_ASSUM `!n p. P n p` K_TAC >> R_TAC [])
   >> Cases_on `n = 1` >- (Q.PAT_X_ASSUM `!n p. P n p` K_TAC >> R_TAC [])
   >> MP_TAC (Q.SPEC `n` EXISTS_PRIME_DIVISOR)
   >> R_TAC []
   >> S_TAC
   >> POP_ASSUM
      (fn th =>
       MP_TAC th
       >> R_TAC [DIVIDES_ALT]
       >> ASSUME_TAC th)
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
   >> Q.PAT_X_ASSUM `!n p. P n p` MATCH_MP_TAC
   >> R_TAC []
   >> S_TAC
   >> Q.PAT_X_ASSUM `!m. P m` MATCH_MP_TAC
   >> MATCH_MP_TAC DIV_LESS
   >> Know `~(p = 0) /\ ~(p = 1)` >- PROVE_TAC [NOT_PRIME_0, NOT_PRIME_1]
   >> DECIDE_TAC);

val FACTOR_INDUCT_DIV = store_thm
  ("FACTOR_INDUCT_DIV",
   ``!prop.
        prop 0 /\
        prop 1 /\
        (!n p.
           prime p /\ divides p n /\ prop (n DIV p) /\ ~(n DIV p = 0) ==>
           prop n) ==>
        !n. prop n``,
   S_TAC
   >> completeInduct_on `n`
   >> Cases_on `n = 0` >- (Q.PAT_X_ASSUM `!n p. P n p` K_TAC >> R_TAC [])
   >> Cases_on `n = 1` >- (Q.PAT_X_ASSUM `!n p. P n p` K_TAC >> R_TAC [])
   >> MP_TAC (Q.SPEC `n` EXISTS_PRIME_DIVISOR)
   >> S_TAC
   >> Q.PAT_X_ASSUM `!n p. P n p` MATCH_MP_TAC
   >> AR_TAC []
   >> S_TAC
   >> Q.EXISTS_TAC `p`
   >> R_TAC [DIV_EQ_0, PRIME_SUBSET_GTNUM1]
   >> S_TAC >|
   [Q.PAT_X_ASSUM `!m. P m` MATCH_MP_TAC
    >> MATCH_MP_TAC DIV_LESS
    >> Know `~(p = 0) /\ ~(p = 1)` >- PROVE_TAC [NOT_PRIME_0, NOT_PRIME_1]
    >> DECIDE_TAC,
    MP_TAC (Q.SPECL [`p`, `n`] NOT_LT_DIV)
    >> ASM_REWRITE_TAC [DE_MORGAN_THM]
    >> DECIDE_TAC]);

val PRIME_EXP = store_thm
  ("PRIME_EXP",
   ``!m n. prime (m EXP n) = prime m /\ (n = 1)``,
   S_TAC
   >> Cases_on `n` >- R_TAC [NOT_PRIME_1]
   >> Cases_on `n'` >- R_TAC []
   >> R_TAC []
   >> REVERSE (Cases_on `1 < m`)
   >- (Know `(m = 0) \/ (m = 1)` >- DECIDE_TAC
       >> S_TAC
       >> AR_TAC [NOT_PRIME_0, NOT_PRIME_1])
   >> R_TAC [prime_def, EXP]
   >> Q.EXISTS_TAC `m`
   >> R_TAC [divides_def]
   >> CONJ_TAC >- ho_PROVE_TAC []
   >> Suff `~(m * 1 = m * (m * m EXP n))` >- RW_TAC std_ss [MULT_CLAUSES]
   >> R_TAC []);

(* Consolidate theorems so far in a simplification context *)

val arith2_pc = precontext_add
  ("arith2",
   map (C_SUBTYPE o SC_JUDGEMENT)
   [] @
   map C_THM
   [NOT_PRIME_0,
    NOT_PRIME_1,
    PRIME_2,
    GCD_0L,
    GCD_0R,
    GCD_1L,
    GCD_1R,
    DIVIDES_PRIME,
    DIVIDES_PRIME_POWER,
    PRIME_EXP])
  arith1_pc;

val arith2_c = precontext_compile arith2_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS arith2_c;

(* back to proving *)

val DIVIDES_PRIME_MOD = store_thm
  ("DIVIDES_PRIME_MOD",
   ``!a p. prime p ==> (divides p (a MOD p) = divides p a)``,
   S_TAC
   >> Suff `(gcd p (a MOD p) = 1) = (gcd p a = 1)`
   >- R_TAC [GCD_1_PRIMEL]
   >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GCD_EFFICIENTLY]))
   >> R_TAC []
   >> PROVE_TAC [GCD_SYM]);

val DIVIDES_DIV = store_thm
  ("DIVIDES_DIV",
   ``!a m n.
       0 < a /\ divides a m /\ divides a n ==>
       (divides (m DIV a) (n DIV a) = divides m n)``,
   R_TAC [DIVIDES_ALT]
   >> R_TAC [divides_def]
   >> S_TAC
   >> EQ_TAC
   >- (S_TAC
       >> Q.EXISTS_TAC `q`
       >> PROVE_TAC [MULT_COMM, MULT_ASSOC])
   >> S_TAC
   >> Q.EXISTS_TAC `q`
   >> Cases_on `a` >- AR_TAC []
   >> Suff `n DIV SUC n' * SUC n' = (q * (m DIV SUC n')) * SUC n'`
   >- R_TAC [MULT_SUC_EQ]
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]);

val GCD_1_DIVL = store_thm
  ("GCD_1_DIVL",
   ``!a m n. 0 < a /\ divides a m /\ (gcd m n = 1) ==> (gcd (m DIV a) n = 1)``,
   S_TAC
   >> Suff `!p. prime p ==> ~divides p (gcd (m DIV a) n)`
   >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
   >> R_TAC [DIVIDES_GCD]
   >> S_TAC
   >> Q.PAT_X_ASSUM `divides a m` MP_TAC
   >> R_TAC [DIVIDES_ALT]
   >> S_TAC
   >> Know `divides p m` >- PROVE_TAC [DIVIDES_MULT, MULT_COMM]
   >> POP_ASSUM K_TAC
   >> S_TAC
   >> Know `divides p (gcd m n)` >- R_TAC [DIVIDES_GCD]
   >> R_TAC []);

val GCD_1_DIVR = store_thm
  ("GCD_1_DIVR",
   ``!a m n. 0 < a /\ divides a n /\ (gcd m n = 1) ==> (gcd m (n DIV a) = 1)``,
   PROVE_TAC [GCD_1_DIVL, GCD_SYM]);

val DIVIDES_MULTR = store_thm
  ("DIVIDES_MULTR",
   ``!a b c. divides a b ==> divides a (b * c)``,
   PROVE_TAC [DIVIDES_MULT]);

val DIVIDES_MULTL = store_thm
  ("DIVIDES_MULTL",
   ``!a b c. divides a b ==> divides a (c * b)``,
   PROVE_TAC [DIVIDES_MULTR, MULT_COMM]);

val DIVIDES_MULT_PRIME = store_thm
  ("DIVIDES_MULT_PRIME",
   ``!p a n.
       prime p /\ divides a n /\ divides p n /\ ~divides p a ==>
       divides (p * a) n``,
   S_TAC
   >> Q.PAT_X_ASSUM `divides a n` MP_TAC
   >> R_TAC [divides_def]
   >> S_TAC
   >> POP_ASSUM (ASSUME_TAC o SYM)
   >> Know `divides p (q * a)` >- R_TAC []
   >> R_TAC [EUCLID]
   >> R_TAC [divides_def]
   >> S_TAC
   >> POP_ASSUM (ASSUME_TAC o SYM)
   >> Q.EXISTS_TAC `q'`
   >> Suff `n = q' * p * a` >- PROVE_TAC [MULT_COMM, MULT_ASSOC]
   >> ASM_REWRITE_TAC []);

val DIVIDES_DIV_PRIME = store_thm
  ("DIVIDES_DIV_PRIME",
   ``!p a n.
       prime p /\ divides a n /\ divides p n /\ ~divides p a ==>
       divides a (n DIV p)``,
   S_TAC
   >> Suff `divides (a * p DIV p) (n DIV p)`
   >- (Suff `0 < p` >- PROVE_TAC [MULT_DIV]
       >> Suff `~(p = 0)` >- DECIDE_TAC
       >> PROVE_TAC [NOT_PRIME_0])
   >> R_TAC [DIVIDES_DIV, DIVIDES_MULT]
   >> PROVE_TAC [DIVIDES_MULT_PRIME, MULT_COMM]);

val GCD_1_LCM = store_thm
  ("GCD_1_LCM",
   ``!n a b.
       (gcd a b = 1) ==> (divides (a * b) n = divides a n /\ divides b n)``,
   S_TAC
   >> EQ_TAC
   >- (R_TAC [divides_def]
       >> PROVE_TAC [MULT_COMM, MULT_ASSOC])
   >> POP_ASSUM MP_TAC
   >> R_TAC [AND_IMP_INTRO]
   >> Q.SPEC_TAC (`b`, `b`)
   >> Q.SPEC_TAC (`a`, `a`)
   >> Q.SPEC_TAC (`n`, `n`)
   >> HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- R_TAC []
   >> CONJ_TAC >- R_TAC []
   >> S_TAC
   >> (Cases_on `divides p a` >> Cases_on `divides p b`) >|
   [Know `divides p (gcd a b)` >- R_TAC [DIVIDES_GCD]
    >> R_TAC [],
    Know `?a'. a = p * a'` >- PROVE_TAC [divides_def, MULT_COMM]
    >> S_TAC
    >> AR_TAC [GSYM MULT_ASSOC]
    >> Q.PAT_X_ASSUM `!a. P a` MATCH_MP_TAC
    >> AR_TAC [GCD_1_MULTL]
    >> PROVE_TAC [L_EUCLIDES],
    Know `?b'. b = p * b'` >- PROVE_TAC [divides_def, MULT_COMM]
    >> S_TAC
    >> AR_TAC []
    >> Suff `divides (p * (a * b')) (p * n)`
    >- PROVE_TAC [MULT_ASSOC, MULT_COMM]
    >> R_TAC []
    >> Q.PAT_X_ASSUM `!a. P a` MATCH_MP_TAC
    >> AR_TAC [GCD_1_MULTR]
    >> PROVE_TAC [L_EUCLIDES, GCD_SYM],
    Suff `divides (a * b) n` >- PROVE_TAC [DIVIDES_MULTL]
    >> Q.PAT_X_ASSUM `!a. P a` MATCH_MP_TAC
    >> AR_TAC [GSYM GCD_1_PRIMEL]
    >> PROVE_TAC [L_EUCLIDES]]);

val GCD_IS_GCD_UNIQUE = store_thm
  ("GCD_IS_GCD_UNIQUE",
   ``!a b g. is_gcd a b g = (g = gcd a b)``,
   S_TAC
   >> REVERSE EQ_TAC >- R_TAC [GCD_IS_GCD]
   >> S_TAC
   >> Know `is_gcd a b (gcd a b)` >- R_TAC [GCD_IS_GCD]
   >> Q.SPEC_TAC (`gcd a b`, `h`)
   >> S_TAC
   >> AR_TAC [is_gcd_def]
   >> PROVE_TAC [DIVIDES_ANTISYM]);

val GCD_MULT = store_thm
  ("GCD_MULT",
   ``!p a b. gcd (p * a) (p * b) = p * gcd a b``,
   HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- R_TAC []
   >> CONJ_TAC >- R_TAC []
   >> S_TAC
   >> Suff `gcd (p * (p' * a)) (p * (p' * b)) = p * (p' * gcd a b)`
   >- (KILL_TAC
       >> Suff
         `(p' * p * a = p * (p' * a)) /\
          (p' * p * b = p * (p' * b)) /\
          (p' * p * gcd a b = p * (p' * gcd a b))`
       >- PROVE_TAC []
       >> PROVE_TAC [MULT_COMM, MULT_ASSOC])
   >> R_TAC []
   >> Cases_on `p` >- AR_TAC []
   >> R_TAC [MULT_MONO_EQ]
   >> POP_ASSUM K_TAC
   >> Suff
     `!g. is_gcd (p' * a) (p' * b) (p' * g) = is_gcd a b g`
   >- PROVE_TAC [GCD_IS_GCD_UNIQUE]
   >> S_TAC
   >> AR_TAC [is_gcd_def, DIVIDES_CANCEL]
   >> EQ_TAC >|
   [S_TAC >- R_TAC [] >- R_TAC []
    >> Suff `divides (p' * d) (p' * g)`
    >- (Q.PAT_X_ASSUM `!s. P s` K_TAC
        >> R_TAC [DIVIDES_CANCEL])
    >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
    >> R_TAC [DIVIDES_CANCEL],
    S_TAC >- R_TAC [] >- R_TAC []
    >> Cases_on `divides p' d` >|
    [Know `?x. d = p' * x` >- PROVE_TAC [MULT_COMM, divides_def]
     >> S_TAC
     >> AR_TAC [DIVIDES_CANCEL],
     Know `gcd p' d = 1` >- PROVE_TAC [PRIME_GCD]
     >> S_TAC
     >> Know `divides d a` >- PROVE_TAC [L_EUCLIDES]
     >> S_TAC
     >> Know `divides d b` >- PROVE_TAC [L_EUCLIDES]
     >> S_TAC
     >> RES_TAC
     >> PROVE_TAC [DIVIDES_MULTL]]]);

val DIV_DIVIDES = store_thm
  ("DIV_DIVIDES",
   ``!a b c. 0 < a /\ divides a b ==> ((c * b) DIV a = c * (b DIV a))``,
   R_TAC [divides_def]
   >> S_TAC
   >> ASM_REWRITE_TAC [MULT_ASSOC]
   >> AR_TAC [MULT_DIV]);

val GCD_DIVIDESL = store_thm
  ("GCD_DIVIDESL",
   ``!a b. divides (gcd a b) a``,
   PROVE_TAC [GCD_IS_GCD_UNIQUE, is_gcd_def]);

val GCD_DIVIDESR = store_thm
  ("GCD_DIVIDESR",
   ``!a b. divides (gcd a b) b``,
   PROVE_TAC [GCD_DIVIDESL, GCD_SYM]);

val DIVIDES_DOWNR = store_thm
  ("DIVIDES_DOWNR",
   ``!a b c. divides (a * b) c ==> divides b c``,
   R_TAC [divides_def]
   >> S_TAC
   >> Q.EXISTS_TAC `q * a`
   >> R_TAC [GSYM MULT_ASSOC]);

val DIVIDES_DOWNL = store_thm
  ("DIVIDES_DOWNL",
   ``!a b c. divides (a * b) c ==> divides a c``,
   PROVE_TAC [DIVIDES_DOWNR, MULT_COMM]);

val LCM_IS_LCM = store_thm
  ("LCM_IS_LCM",
   ``!a b. is_lcm a b (lcm a b)``,
   S_TAC
   >> R_TAC [is_lcm_def, lcm_def]
   >> Cases_on `(a = 0) /\ (b = 0)` >- R_TAC []
   >> R_TAC []
   >> Know `0 < gcd a b`
   >- (Suff `~(gcd a b = 0)` >- DECIDE_TAC
       >> R_TAC [])
   >> POP_ASSUM K_TAC
   >> Know `?g. gcd a b = g` >- PROVE_TAC []
   >> STRIP_TAC
   >> R_TAC []
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`b`, `b`)
   >> Q.SPEC_TAC (`a`, `a`)
   >> Q.SPEC_TAC (`g`, `g`)
   >> HO_MATCH_MP_TAC FACTOR_INDUCT
   >> STRIP_TAC >- R_TAC []
   >> STRIP_TAC >- R_TAC [GCD_1_LCM]
   >> REWRITE_TAC [LESS_0_MULT2]
   >> NTAC 7 RESQ_STRIP_TAC
   >> Know `divides p (gcd a b)` >- PROVE_TAC [divides_def, MULT_COMM]
   >> R_TAC [DIVIDES_GCD]
   >> DISCH_THEN
        (fn th => Know `(?a'. a = p * a') /\ (?b'. b = p * b')`
         >- PROVE_TAC [th, MULT_COMM, divides_def])
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `!b. P b`
      (fn th => AR_TAC [GCD_MULT] >> MP_TAC (Q.SPECL [`a'`, `b'`] th))
   >> Q.PAT_X_ASSUM `a = p * a'` K_TAC
   >> Q.PAT_X_ASSUM `b = p * b'` K_TAC
   >> R_TAC []
   >> STRIP_TAC
   >> Know `p * (a' * (p * b')) DIV (p * g) = p * (a' * b' DIV g)`
   >- (Suff `(p * (a' * b')) * p DIV (p * g) = p * (a' * b' DIV g)`
       >- PROVE_TAC [MULT_ASSOC, MULT_COMM]
       >> R_TAC [GSYM DIV_DIV_DIV_MULT, MULT_DIV]
       >> Know `divides g (a' * b')`
       >- PROVE_TAC [GCD_DIVIDESL, DIVIDES_MULT]
       >> S_TAC
       >> R_TAC [DIV_DIVIDES])
   >> DISCH_THEN (fn th => R_TAC [th, DIVIDES_CANCEL, GSYM MULT_ASSOC])
   >> S_TAC
   >> Know `divides p n` >- PROVE_TAC [DIVIDES_DOWNL]
   >> S_TAC
   >> Know `?n'. n = p * n'` >- PROVE_TAC [divides_def, MULT_COMM]
   >> S_TAC
   >> AR_TAC [DIVIDES_CANCEL]);

val LCM_IS_LCM_UNIQUE = store_thm
  ("LCM_IS_LCM_UNIQUE",
   ``!l a b. is_lcm a b l = (l = lcm a b)``,
   S_TAC
   >> REVERSE EQ_TAC >- R_TAC [LCM_IS_LCM]
   >> S_TAC
   >> Know `is_lcm a b (lcm a b)` >- R_TAC [LCM_IS_LCM]
   >> Q.SPEC_TAC (`lcm a b`, `h`)
   >> S_TAC
   >> AR_TAC [is_lcm_def]
   >> PROVE_TAC [DIVIDES_ANTISYM]);

(* Consolidate theorems so far in a simplification context *)

val arith3_pc = precontext_add
  ("arith3",
   map (C_SUBTYPE o SC_JUDGEMENT)
   [] @
   map C_THM
   [GCD_MULT,
    GCD_DIVIDESR,
    GCD_DIVIDESL,
    GCD_REF])
  arith2_pc;

val arith3_c = precontext_compile arith3_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS arith3_c;

(* back to proving *)

val DIV_CANCEL = store_thm
  ("DIV_CANCEL",
   ``!p a b. 0 < p /\ 0 < b ==> (p * a DIV (p * b) = a DIV b)``,
   S_TAC
   >> AR_TAC []
   >> R_TAC [GSYM DIV_DIV_DIV_MULT]
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> R_TAC [MULT_DIV]);

val DIV_GCD = store_thm
  ("DIV_GCD",
   ``!a b. 0 < a ==> (gcd (a DIV gcd a b) (b DIV gcd a b) = 1)``,
   Suff
     `!g a b. 0 < a /\ (gcd a b = g) ==> (gcd (a DIV g) (b DIV g) = 1)`
   >- (S_TAC
       >> Q.PAT_X_ASSUM `!g. P g` (MP_TAC o Q_RESQ_SPECL [`gcd a b`, `a`, `b`])
       >> R_TAC [])
   >> HO_MATCH_MP_TAC FACTOR_INDUCT
   >> R_TAC []
   >> S_TAC
   >> Know `(?a'. a = p * a') /\ (?b'. b = p * b')`
   >- (Know `divides p (gcd a b)` >- PROVE_TAC [divides_def, MULT_COMM]
       >> R_TAC [DIVIDES_GCD]
       >> PROVE_TAC [divides_def, MULT_COMM])
   >> Know `0 < g`
   >- (Suff `~(g = 0)` >- (KILL_TAC >> DECIDE_TAC)
       >> S_TAC
       >> AR_TAC [])
   >> S_TAC
   >> AR_TAC [GCD_MULT, DIV_CANCEL]);

val PRIME_EXPONENT_EXISTS0 = store_thm
  ("PRIME_EXPONENT_EXISTS0",
   ``!n p. 0 < n /\ prime p ==> ?k. ~divides (p EXP (SUC k)) n``,
   HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- R_TAC []
   >> CONJ_TAC >- R_TAC []
   >> S_TAC
   >> AR_TAC []
   >> RES_TAC
   >> POP_ASSUM K_TAC
   >> Q.PAT_X_ASSUM `!p. P p` K_TAC
   >> Cases_on `p' = p` >- (R_TAC [DIVIDES_CANCEL, EXP] >> PROVE_TAC [])
   >> Q.EXISTS_TAC `k`
   >> S_TAC
   >> Q.PAT_X_ASSUM `~divides x y` MP_TAC
   >> R_TAC []
   >> MATCH_MP_TAC L_EUCLIDES
   >> Q.EXISTS_TAC `p`
   >> R_TAC [GCD_1_PRIME_POWERR]);

Theorem PRIME_EXPONENT:
   !n p.
     0 < n /\ prime p ==>
     divides (p EXP exponent p n) n /\
     ~divides (p EXP (SUC (exponent p n))) n
Proof
   NTAC 3 STRIP_TAC
   >> simp[exponent_def]
   >> numLib.LEAST_ELIM_TAC
   >> conj_tac >- simp[PRIME_EXPONENT_EXISTS0, SF SFY_ss]
   >> rpt strip_tac
   >> rename [‘¬divides (p ** SUC k) n’]
   >> Cases_on ‘k’ >- R_TAC [EXP]
   >> gs[]
QED

val PRIME_EXPONENT_DIVIDES = store_thm
  ("PRIME_EXPONENT_DIVIDES",
   ``!n p k.
       0 < n /\ prime p ==> (divides (p EXP k) n = k <= exponent p n)``,
   S_TAC
   >> REVERSE EQ_TAC
   >- (S_TAC
       >> MATCH_MP_TAC DIVIDES_DOWNR
       >> Q.EXISTS_TAC `p EXP (exponent p n - k)`
       >> R_TAC [GSYM EXP_ADD, PRIME_EXPONENT])
   >> S_TAC
   >> Suff `exponent p n < k ==> F` >- DECIDE_TAC
   >> Cases_on `k` >- DECIDE_TAC
   >> Suff `exponent p n <= n' ==> F` >- DECIDE_TAC
   >> S_TAC
   >> Know `SUC n' = SUC (exponent p n) + (n' - exponent p n)`
   >- DECIDE_TAC
   >> S_TAC
   >> Q.PAT_X_ASSUM `divides x y` MP_TAC
   >> R_TAC [EXP_ADD]
   >> S_TAC
   >> Know `divides (p EXP SUC (exponent p n)) n`
   >- PROVE_TAC [DIVIDES_DOWNL]
   >> R_TAC [PRIME_EXPONENT]);

val PRIME_EXPONENT_UNIQUE = store_thm
  ("PRIME_EXPONENT_UNIQUE",
   ``!n p e.
       0 < n /\ prime p /\ divides (p EXP e) n /\ ~divides (p EXP (SUC e)) n ==>
       (exponent p n = e)``,
   R_TAC [PRIME_EXPONENT_DIVIDES]
   >> S_TAC
   >> DECIDE_TAC);

val IS_PRIME_EXPONENT = store_thm
  ("IS_PRIME_EXPONENT",
   ``!n p e.
       0 < n /\ prime p ==>
       ((exponent p n = e) =
        divides (p EXP e) n /\ ~divides (p EXP (SUC e)) n)``,
   S_TAC
   >> EQ_TAC >|
   [DISCH_THEN (R_TAC o wrap o SYM)
    >> R_TAC [PRIME_EXPONENT],
    S_TAC
    >> R_TAC [Q_RESQ_SPEC `n` PRIME_EXPONENT_UNIQUE]]);

val GCD_PRIME_EXPONENT = store_thm
  ("GCD_PRIME_EXPONENT",
   ``!a b p.
       0 < a /\ 0 < b /\ prime p ==>
       (exponent p (gcd a b) = min (exponent p a) (exponent p b))``,
   S_TAC
   >> Know `exponent p a <= exponent p b \/ exponent p b <= exponent p a`
   >- DECIDE_TAC
   >> S_TAC >|
   [R_TAC [IS_PRIME_EXPONENT, PRIME_EXPONENT, DIVIDES_GCD]
    >> R_TAC [PRIME_EXPONENT_DIVIDES],
    R_TAC [IS_PRIME_EXPONENT, PRIME_EXPONENT, DIVIDES_GCD]
    >> R_TAC [PRIME_EXPONENT_DIVIDES]]);

val PRIME_EXPONENT_PRIME_MULT = store_thm
  ("PRIME_EXPONENT_PRIME_MULT",
   ``!a p q.
       0 < a /\ prime p /\ prime q ==>
       (exponent p (q * a) =
        if p = q then SUC (exponent p a) else exponent p a)``,
   S_TAC
   >> R_TAC [IS_PRIME_EXPONENT]
   >> Cases_on `p = q`
   >- (R_TAC []
       >> ONCE_REWRITE_TAC [EXP]
       >> R_TAC [DIVIDES_CANCEL, PRIME_EXPONENT])
   >> R_TAC []
   >> S_TAC
   >- (Suff `divides (p EXP exponent p a) a` >- PROVE_TAC [DIVIDES_MULTL]
       >> R_TAC [PRIME_EXPONENT])
   >> Suff `divides (p EXP SUC (exponent p a)) a` >- R_TAC [PRIME_EXPONENT]
   >> MATCH_MP_TAC L_EUCLIDES
   >> Q.EXISTS_TAC `q`
   >> REVERSE CONJ_TAC >- R_TAC []
   >> R_TAC [GCD_1_PRIME_POWERR]);

val PRIME_EXPONENT_1 = store_thm
  ("PRIME_EXPONENT_1",
   ``!p. prime p ==> (exponent p 1 = 0)``,
   S_TAC
   >> R_TAC [IS_PRIME_EXPONENT, EXP]);

val PRIME_EXPONENT_1_UNIQUE = store_thm
  ("PRIME_EXPONENT_1_UNIQUE",
   ``!n. 0 < n ==> ((!p. prime p ==> (exponent p n = 0)) = (n = 1))``,
   S_TAC
   >> REVERSE EQ_TAC >- R_TAC [PRIME_EXPONENT_1]
   >> S_TAC
   >> Suff `!p. prime p ==> ~divides p n`
   >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
   >> S_TAC
   >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`)
   >> R_TAC [IS_PRIME_EXPONENT]
   >> R_TAC [EXP]);

val PRIME_EXPONENTS_EQ = store_thm
  ("PRIME_EXPONENTS_EQ",
   ``!a b.
       0 < a /\ 0 < b /\ (!p. prime p ==> (exponent p a = exponent p b)) ==>
       (a = b)``,
   HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- R_TAC []
   >> CONJ_TAC
   >- (R_TAC [PRIME_EXPONENT_1]
       >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> R_TAC [PRIME_EXPONENT_1_UNIQUE])
   >> S_TAC
   >> AR_TAC []
   >> Know `?b'. b = p * b'`
   >- (Suff `divides p b` >- PROVE_TAC [divides_def, MULT_COMM]
       >> Suff `divides (p EXP 1) b` >- R_TAC [EXP_1]
       >> R_TAC [PRIME_EXPONENT_DIVIDES]
       >> POP_ASSUM (MP_TAC o Q.SPEC `p`)
       >> R_TAC [PRIME_EXPONENT_PRIME_MULT]
       >> DECIDE_TAC)
   >> S_TAC
   >> AR_TAC []
   >> POP_ASSUM K_TAC
   >> Q.PAT_X_ASSUM `!b. P b /\ Q b ==> R b` MATCH_MP_TAC
   >> R_TAC []
   >> S_TAC
   >> Q.PAT_X_ASSUM `!p'. P p'` (MP_TAC o Q.SPEC `p'`)
   >> R_TAC [PRIME_EXPONENT_PRIME_MULT]
   >> Cases_on `p' = p`
   >> R_TAC []);

val FACTOR_GCD = store_thm
  ("FACTOR_GCD",
   ``!a b p.
       prime p /\ 0 < a /\ 0 < b ==>
       (gcd (p * a) b = gcd a b) \/
       (gcd a (p * b) = gcd a b)``,
   S_TAC
   >> Know `exponent p a <= exponent p b \/ exponent p b <= exponent p a`
   >- DECIDE_TAC
   >> S_TAC >|
   [DISJ2_TAC
    >> MATCH_MP_TAC PRIME_EXPONENTS_EQ
    >> R_TAC []
    >> S_TAC
    >> R_TAC [PRIME_EXPONENT_PRIME_MULT, GCD_PRIME_EXPONENT]
    >> REVERSE (Cases_on `p' = p`) >- R_TAC []
    >> R_TAC [min_def]
    >> DECIDE_TAC,
    DISJ1_TAC
    >> MATCH_MP_TAC PRIME_EXPONENTS_EQ
    >> R_TAC []
    >> S_TAC
    >> R_TAC [PRIME_EXPONENT_PRIME_MULT, GCD_PRIME_EXPONENT]
    >> REVERSE (Cases_on `p' = p`) >- R_TAC []
    >> R_TAC [min_def]
    >> DECIDE_TAC]);

val LCM_SYM = store_thm
  ("LCM_SYM",
   ``!a b. lcm a b = lcm b a``,
   R_TAC [lcm_def]
   >> PROVE_TAC [MULT_COMM, GCD_SYM]);

val DIVIDES_LCM_L = store_thm
  ("DIVIDES_LCM_L",
   ``!a b. divides a (lcm a b)``,
   Suff `!a b l. is_lcm a b l ==> divides a l`
   >- PROVE_TAC [LCM_IS_LCM_UNIQUE]
   >> R_TAC [is_lcm_def]);

val DIVIDES_LCM_R = store_thm
  ("DIVIDES_LCM_R",
   ``!a b. divides b (lcm a b)``,
   PROVE_TAC [LCM_SYM, DIVIDES_LCM_L]);

val LCM_REFL = store_thm
  ("LCM_REFL",
   ``!a. lcm a a = a``,
   R_TAC [lcm_def]
   >> S_TAC
   >> REVERSE (Cases_on `0 < a`)
   >- (Know `a = 0` >- DECIDE_TAC >> R_TAC [])
   >> R_TAC []);

val FUNPOW_SUC = store_thm
  ("FUNPOW_SUC",
   ``!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)``,
   S_TAC
   >> Q.SPEC_TAC (`x`, `x`)
   >> Induct_on `n` >- RW_TAC std_ss [FUNPOW]
   >> ONCE_REWRITE_TAC [FUNPOW]
   >> RW_TAC std_ss [FUNPOW]);

val MOD_PRIME_INTEGRAL = store_thm
  ("MOD_PRIME_INTEGRAL",
   ``!p a b.
       prime p ==>
       (((a * b) MOD p = 0) = (a MOD p = 0) \/ (b MOD p = 0))``,
   R_TAC [EUCLID, DIVIDES_MOD]);

(* Consolidate theorems so far in a simplification context *)

val arith4_pc = precontext_add
  ("arith4",
   map C_THM
   [DIV_CANCEL,
    PRIME_EXPONENT_1,
    DIVIDES_LCM_L,
    DIVIDES_LCM_R,
    LCM_REFL])
  arith3_pc;

val arith4_c = precontext_compile arith4_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS arith4_c;

val Simplify = R_TAC;

(* back to proving *)

val DIVIDES_0L = store_thm
  ("DIVIDES_0L",
   ``!n. divides 0 n = (n = 0)``,
   R_TAC [divides_def]);

val DIVIDES_POWER_CANCEL = store_thm
  ("DIVIDES_POWER_CANCEL",
   ``!a b c d.
       0 < a ==>
       (divides (a EXP b) (a EXP d * c) =
        divides (a EXP (b - d)) c)``,
   Induct_on `d` >- R_TAC []
   >> S_TAC
   >> Cases_on `b` >- R_TAC []
   >> R_TAC [EXP, GSYM MULT_ASSOC]);

val DIVIDES_SUB_2 = store_thm
  ("DIVIDES_SUB_2",
   ``!n a b. divides n a /\ b <= a /\ divides n (a - b) ==> divides n b``,
   R_TAC [divides_def]
   >> S_TAC
   >> Q.EXISTS_TAC `q - q'`
   >> R_TAC [RIGHT_SUB_DISTRIB]
   >> Q.PAT_X_ASSUM `x = y` (ONCE_REWRITE_TAC o wrap o SYM)
   >> Q.PAT_X_ASSUM `x = y` (ONCE_REWRITE_TAC o wrap o SYM)
   >> DECIDE_TAC);

val PRIME_POWER_GE = store_thm
  ("PRIME_POWER_GE",
   ``!p n. prime p /\ ODD p /\ 0 < n ==> n + 2 <= p EXP n``,
   S_TAC
   >> Cases_on `p` >- AR_TAC []
   >> Cases_on `n'` >- AR_TAC []
   >> Cases_on `n''` >- AR_TAC [ODD]
   >> Know `n + 2 = SUC (SUC n)` >- DECIDE_TAC
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Induct_on `n` >- AR_TAC []
   >> Cases_on `n` >- (R_TAC [] >> DECIDE_TAC)
   >> AR_TAC []
   >> ONCE_REWRITE_TAC [EXP]
   >> Know `SUC (SUC (SUC n')) * SUC (SUC (SUC n'')) <=
                SUC (SUC (SUC n')) * SUC (SUC (SUC n')) EXP SUC n''`
   >- R_TAC []
   >> Suff
      `SUC (SUC (SUC (SUC n''))) <= SUC (SUC (SUC n')) * SUC (SUC (SUC n''))`
   >- DECIDE_TAC
   >> ONCE_REWRITE_TAC [MULT]
   >> ONCE_REWRITE_TAC [MULT]
   >> DECIDE_TAC);

val FACTOR_PRIME_POWER = store_thm
  ("FACTOR_PRIME_POWER",
   ``!p n r s.
       prime p ==>
       (divides n ((p EXP r) * s) =
        ?r' s'. ((p EXP r') * s' = n) /\ r' <= r /\ divides s' s)``,
   S_TAC
   >> Q.SPEC_TAC (`s`, `s`)
   >> Q.SPEC_TAC (`n`, `n`)
   >> Q.SPEC_TAC (`r`, `r`)
   >> Induct
   >- (R_TAC []
       >> PROVE_TAC [])
   >> S_TAC
   >> Cases_on `divides p n` >|
   [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [MULT_COMM] o
               ONCE_REWRITE_RULE [divides_def])
    >> S_TAC
    >> AR_TAC [EXP, GSYM MULT_ASSOC, DIVIDES_CANCEL]
    >> POP_ASSUM K_TAC
    >> POP_ASSUM K_TAC
    >> EQ_TAC >|
    [S_TAC
     >> Q.EXISTS_TAC `SUC r'`
     >> Q.EXISTS_TAC `s'`
     >> R_TAC [EXP, GSYM MULT_ASSOC],
     S_TAC
     >> Cases_on `r'`
     >- (AR_TAC []
         >> Q.EXISTS_TAC `0`
         >> Q.EXISTS_TAC `q`
         >> R_TAC []
         >> PROVE_TAC [DIVIDES_DOWNR])
     >> Q.EXISTS_TAC `n`
     >> Q.EXISTS_TAC `s'`
     >> AR_TAC [EXP, GSYM MULT_ASSOC]],
    EQ_TAC >|
    [S_TAC
     >> Suff `divides n (p EXP r * s)`
     >- (S_TAC
         >> RES_TAC
         >> Q.EXISTS_TAC `r'`
         >> Q.EXISTS_TAC `s'`
         >> R_TAC []
         >> DECIDE_TAC)
     >> MATCH_MP_TAC L_EUCLIDES
     >> Q.EXISTS_TAC `p`
     >> R_TAC [GCD_1_PRIMEL]
     >> AR_TAC [EXP, MULT_ASSOC],
     S_TAC
     >> REVERSE (Cases_on `r'`)
     >- (AR_TAC [EXP, GSYM MULT_ASSOC]
         >> PROVE_TAC [divides_def, MULT_COMM])
     >> AR_TAC []
     >> PROVE_TAC [DIVIDES_MULTL]]]);

val FACTOR_PRIME_POWER_SANDWICH = store_thm
  ("FACTOR_PRIME_POWER_SANDWICH",
   ``!p n r s.
       prime p /\ ~divides n ((p EXP r) * s) /\
       divides n ((p EXP SUC r) * s) ==>
       divides (p EXP SUC r) n``,
   R_TAC [FACTOR_PRIME_POWER]
   >> S_TAC
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`r'`, `s'`])
   >> R_TAC []
   >> S_TAC
   >> Know `r' = SUC r` >- DECIDE_TAC
   >> S_TAC
   >> AR_TAC []
   >> PROVE_TAC [divides_def, MULT_COMM]);

val PRIME_POWER_SANDWICH = store_thm
  ("PRIME_POWER_SANDWICH",
   ``!p n r s.
       prime p /\ divides s n /\ divides n (p EXP r * s) ==>
       ?k. k <= r /\ (p EXP k * s = n)``,
   S_TAC
   >> Q.PAT_X_ASSUM `divides s n` MP_TAC
   >> R_TAC [divides_def]
   >> S_TAC
   >> POP_ASSUM (AR_TAC o wrap)
   >> Cases_on `s` >- (R_TAC [] >> Q.EXISTS_TAC `0` >> DECIDE_TAC)
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> AR_TAC []
   >> PROVE_TAC []);

val PRIME_EXPONENT_REFL = store_thm
  ("PRIME_EXPONENT_REFL",
   ``!p. prime p ==> (exponent p p = 1)``,
   S_TAC
   >> R_TAC [IS_PRIME_EXPONENT, EXP, SQUARED_GT_1]);

val PRIME_EXPONENT_MULT = store_thm
  ("PRIME_EXPONENT_MULT",
   ``!a b p.
       prime p /\ 0 < a /\ 0 < b ==>
       (exponent p (a * b) = exponent p a + exponent p b)``,
   HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- R_TAC []
   >> CONJ_TAC >- R_TAC [PRIME_EXPONENT_1]
   >> S_TAC
   >> AR_TAC [GSYM MULT_ASSOC, PRIME_EXPONENT_PRIME_MULT]
   >> Q.PAT_X_ASSUM `!b. P b` (MP_TAC o Q.SPECL [`b`, `p`])
   >> Cases_on `p' = p`
   >> R_TAC [ADD_CLAUSES]);

val PRIME_EXPONENT_POWER = store_thm
  ("PRIME_EXPONENT_POWER",
   ``!p n. prime p ==> (exponent p (p EXP n) = n)``,
   S_TAC
   >> Induct_on `n` >- R_TAC [PRIME_EXPONENT_1]
   >> R_TAC [EXP, PRIME_EXPONENT_MULT, PRIME_EXPONENT_REFL]
   >> DECIDE_TAC);

val PRIME_EXPONENT_EQ = store_thm
  ("PRIME_EXPONENT_EQ",
   ``!p a b.
       prime p /\ 0 < a /\ 0 < b ==>
       ((exponent p a = exponent p b) =
        !n. divides (p EXP n) a = divides (p EXP n) b)``,
   S_TAC
   >> R_TAC [PRIME_EXPONENT_DIVIDES]
   >> EQ_TAC >|
   [S_TAC
    >> DECIDE_TAC,
    S_TAC
    >> POP_ASSUM
       (fn th =>
        MP_TAC (Q.SPEC `exponent p a` th) >> MP_TAC (Q.SPEC `exponent p b` th))
    >> DECIDE_TAC]);

val NUM_DECOMPOSE = store_thm
  ("NUM_DECOMPOSE",
   ``!n.
       1 < n ==>
       (~(?p q. 1 < p /\ 1 < q /\ (p * q = n) /\ (gcd p q = 1)) =
        (?p a. prime p /\ 0 < a /\ (p EXP a = n)))``,
   Strip
   >> Know `?p. prime p /\ divides p n`
   >- (Suff `~(n = 1)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
       >> DECIDE_TAC)
   >> Strip
   >> MP_TAC (Q.SPECL [`n`, `p`] PRIME_EXPONENT)
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> Cases_on `exponent p n` >- Simplify []
   >> STRIP_TAC
   >> Know `?q. p EXP SUC n' * q = n` >- PROVE_TAC [divides_def, MULT_COMM]
   >> Strip
   >> REVERSE (Cases_on `1 < q`) >|
   [Know `(q = 0) \/ (q = 1)` >- DECIDE_TAC
    >> Strip >- AR_TAC []
    >> AR_TAC []
    >> Know `(?p a. prime p /\ 0 < a /\ (p EXP a = n))`
    >- (Q.EXISTS_TAC `p`
        >> Q.EXISTS_TAC `SUC n'`
        >> Simplify [])
    >> DISCH_THEN (REWRITE_TAC o wrap)
    >> Strip
    >> Know `divides p (x' * x)` >- PROVE_TAC []
    >> Simplify [EUCLID]
    >> Strip >|
    [Know `?q. prime q /\ divides q x`
     >- (Suff `~(x = 1)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
         >> DECIDE_TAC)
     >> Strip
     >> Know `divides q' (p EXP SUC n')`
     >- (Suff `divides x n` >- PROVE_TAC [DIVIDES_TRANS]
         >> PROVE_TAC [divides_def, MULT_COMM])
     >> Simplify [PRIME_DIVIDES_PRIME_POWER]
     >> Strip
     >> RW_TAC std_ss []
     >> Suff `divides p (gcd x' x)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
     >> Simplify [DIVIDES_GCD],
     Know `?q. prime q /\ divides q x'`
     >- (Suff `~(x' = 1)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
         >> DECIDE_TAC)
     >> Strip
     >> Know `divides q' (p EXP SUC n')`
     >- (Suff `divides x' n` >- PROVE_TAC [DIVIDES_TRANS]
         >> PROVE_TAC [divides_def, MULT_COMM])
     >> Simplify [PRIME_DIVIDES_PRIME_POWER]
     >> Strip
     >> RW_TAC std_ss []
     >> Suff `divides p (gcd x' x)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
     >> Simplify [DIVIDES_GCD]],
    Know `~divides p q`
    >- (Simplify [divides_def]
        >> Strip
        >> Q.PAT_X_ASSUM `xx = n` MP_TAC
        >> PURE_ONCE_REWRITE_TAC [MULT_COMM]
        >> Simplify [GSYM MULT_ASSOC, GSYM EXP]
        >> PROVE_TAC [divides_def, MULT_COMM])
    >> Strip
    >> Know `?p q. 1 < p /\ 1 < q /\ (p * q = n) /\ (gcd p q = 1)`
    >- (Q.EXISTS_TAC `p EXP SUC n'`
        >> Q.EXISTS_TAC `q`
        >> Simplify [GCD_1_PRIME_POWERL])
    >> DISCH_THEN (fn th => REWRITE_TAC [th])
    >> Strip
    >> Know `divides p (p' EXP a)` >- ASM_REWRITE_TAC []
    >> Simplify [PRIME_DIVIDES_PRIME_POWER]
    >> Strip
    >> Know `?r. prime r /\ divides r q`
    >- (Suff `~(q = 1)` >- PROVE_TAC [EXISTS_PRIME_DIVISOR]
        >> DECIDE_TAC)
    >> Strip
    >> Know `divides r (p EXP a)` >- PROVE_TAC [divides_def, DIVIDES_TRANS]
    >> Simplify [PRIME_DIVIDES_PRIME_POWER]
    >> Strip
    >> RW_TAC std_ss []
    >> PROVE_TAC []]);

val MULT_EQ_PRIME = store_thm
  ("MULT_EQ_PRIME",
   ``!p a b. prime p /\ (a * b = p) ==> (a = 1) \/ (a = p)``,
   Strip
   >> Cases_on `a = 1` >- RW_TAC arith_ss []
   >> Simplify []
   >> Q.PAT_X_ASSUM `prime p` MP_TAC
   >> Simplify [prime_def]
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `a`)
   >> Simplify [divides_def]
   >> PROVE_TAC [MULT_COMM]);

val NOT_PRIME_EVEN = store_thm
  ("NOT_PRIME_EVEN",
   ``!n. EVEN n /\ prime n ==> (n = 2)``,
   RW_TAC std_ss [EVEN_EXISTS]
   >> Know `divides 2 (2 * m)` >- PROVE_TAC [divides_def, MULT_COMM]
   >> Simplify [PRIME_DIVIDES_PRIME]
   >> PROVE_TAC []);

val _ = export_theory ();
