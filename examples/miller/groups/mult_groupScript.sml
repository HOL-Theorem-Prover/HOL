(* interactive mode
show_assums := true;
loadPath := ["../ho_prover","../subtypes","../RSA","../formalize"] @ !loadPath;
app load
  ["bossLib", "listTheory", "subtypeTools", "res_quanTools",
   "pred_setTheory", "extra_pred_setTheory", "arithContext",
   "ho_proverTools", "extra_listTheory", "subtypeTheory",
   "listContext", "arithmeticTheory", "groupTheory", "groupContext",
   "extra_numTheory", "gcdTheory", "dividesTheory",
   "extra_arithTheory", "finite_groupTheory", "finite_groupContext",
   "abelian_groupTheory", "num_polyTheory", "extra_binomialTheory",
   "binomialTheory", "summationTheory", "prob_extraTheory",
   "pred_setContext"];
quietdec := true;
*)

open HolKernel Parse boolLib;
open bossLib listTheory subtypeTools res_quanTools res_quanTheory
     pred_setTheory extra_pred_setTheory arithContext
     ho_proverTools extra_listTheory subtypeTheory
     listContext arithmeticTheory groupTheory hurdUtils
     groupContext extra_numTheory gcdTheory dividesTheory
     extra_arithTheory finite_groupTheory finite_groupContext
     abelian_groupTheory num_polyTheory extra_binomialTheory
     binomialTheory summationTheory pred_setContext;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "mult_group";
val _ = ParseExtras.temp_loose_equality()

val EXISTS_DEF = boolTheory.EXISTS_DEF;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;

val std_pc = precontext_mergel [arith_pc, list_pc, pred_set_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group_c;

val Strip = S_TAC;
val Simplify = R_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val mult_group_def = Define
  `mult_group n =
   ((\x. x IN gset (add_group n) /\ (gcd n x = 1)), (\x y. (x * y) MOD n))`;

val totient_def = Define `totient n = CARD (gset (mult_group n))`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val MULT_GROUP_SET = store_thm
  ("MULT_GROUP_SET",
   ``!n x.
       x IN gset (mult_group n) = x IN gset (add_group n) /\ (gcd n x = 1)``,
   R_TAC [SPECIFICATION, gset_def, mult_group_def]);

val MULT_GROUP_OP = store_thm
  ("MULT_GROUP_OP",
   ``!n x y. gop (mult_group n) x y = (x * y) MOD n``,
   R_TAC [mult_group_def, gop_def]);

val MULT_GROUP_SET_0 = store_thm
  ("MULT_GROUP_SET_0",
   ``!n. 1 < n ==> ~(0 IN gset (mult_group n))``,
   S_TAC
   ++ AR_TAC [MULT_GROUP_SET, GCD_0R]
   ++ DECIDE_TAC);

val MULT_SUBSET_ADD = store_thm
  ("MULT_SUBSET_ADD",
   ``!n. gset (mult_group n) SUBSET gset (add_group n)``,
   R_TAC [SUBSET_DEF, MULT_GROUP_SET]);

val MULT_GROUP_OP_SUBTYPE = store_thm
  ("MULT_GROUP_OP_SUBTYPE",
   ``!n.
       1 < n ==>
       gop (mult_group n) IN
       (gset (mult_group n) -> gset (mult_group n) -> gset (mult_group n))``,
   R_TAC [IN_FUNSET, MULT_GROUP_SET, ADD_GROUP_SET, MULT_GROUP_OP]
   ++ S_TAC
   ++ ONCE_REWRITE_TAC [GCD_SYM]
   ++ Cases_on `n = 0` >> DECIDE_TAC
   ++ Suff `gcd n (x' * x) = 1`
   >> (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GCD_EFFICIENTLY]))
       ++ R_TAC [])
   ++ PROVE_TAC [GCD_1_MULTR]);

val MULT_GROUP_ASSOC = store_thm
  ("MULT_GROUP_ASSOC",
   ``!n x y z.
       1 < n ==>
       (gop (mult_group n) (gop (mult_group n) x y) z
        = gop (mult_group n) x (gop (mult_group n) y z))``,
   S_TAC
   ++ G_TAC [MULT_GROUP_OP, MULT_ASSOC]);

val MULT_GROUP_COMM = store_thm
  ("MULT_GROUP_COMM",
   ``!n x y. 1 < n ==> (gop (mult_group n) x y = gop (mult_group n) y x)``,
   S_TAC
   ++ G_TAC [MULT_GROUP_OP]
   ++ PROVE_TAC [MULT_COMM]);

val MULT_GROUP_ID_WITNESS = store_thm
  ("MULT_GROUP_ID_WITNESS",
   ``!n.
       1 < n ==>
       1 IN gset (mult_group n) /\
       !x :: gset (mult_group n). gop (mult_group n) 1 x = x``,
   S_TAC >> AG_TAC [MULT_GROUP_SET, ADD_GROUP_SET]
   ++ AG_TAC [MULT_GROUP_SET, ADD_GROUP_SET, MULT_GROUP_OP]);

val MULT_GROUP_INV = store_thm
  ("MULT_GROUP_INV",
   ``!n. !x :: gset (mult_group n).
       1 < n ==>
       ?y :: gset (mult_group n). gop (mult_group n) y x = 1``,
   S_TAC
   ++ Cases_on `x = 0` >> AR_TAC [MULT_GROUP_SET_0]
   ++ AR_TAC [MULT_GROUP_SET, MULT_GROUP_OP, ADD_GROUP_SET]
   ++ MP_TAC (Q.SPECL [`x`, `n`] LINEAR_GCD)
   ++ R_TAC []
   ++ S_TAC
   ++ Q_RESQ_EXISTS_TAC `p MOD n`
   ++ REVERSE S_TAC >> G_TAC []
   ++ G_TAC [MULT_GROUP_SET, ADD_GROUP_SET]
   ++ Suff `gcd p n = 1`
   >> (Know `~(n = 0)` >> DECIDE_TAC
       ++ PROVE_TAC [GCD_EFFICIENTLY, GCD_SYM])
   ++ Suff `!g. is_gcd p n g ==> (g = 1)` >> PROVE_TAC [GCD_IS_GCD]
   ++ R_TAC [is_gcd_def, divides_def]
   ++ S_TAC
   ++ POP_ASSUM K_TAC
   ++ AR_TAC []
   ++ Q.PAT_X_ASSUM `a:num * b = c` MP_TAC
   ++ POP_ASSUM_LIST K_TAC
   ++ Suff `(g * (q' * x) = g * (q * q'') + 1) ==> (g = 1)`
   >> PROVE_TAC [MULT_ASSOC, MULT_COMM]
   ++ DISCH_THEN (ASSUME_TAC o SYM)
   ++ Suff `divides g 1` >> R_TAC []
   ++ MATCH_MP_TAC DIVIDES_ADD_2
   ++ Q.EXISTS_TAC `g * (q * q'')`
   ++ R_TAC [DIVIDES_MULT]);

val MULT_GROUP_SET_FINITE = store_thm
  ("MULT_GROUP_SET_FINITE",
   ``!n. FINITE (gset (mult_group n))``,
   PROVE_TAC [MULT_SUBSET_ADD, SUBSET_FINITE, ADD_GROUP_SET_FINITE]);

val MULT_GROUP = store_thm
  ("MULT_GROUP",
   ``!n. 1 < n ==> mult_group n IN finite_group``,
   R_TAC [IN_GROUP, MULT_GROUP_OP_SUBTYPE, MULT_GROUP_ASSOC, IN_FINITE_GROUP]
   ++ REVERSE S_TAC >> R_TAC [MULT_GROUP_SET_FINITE]
   ++ Q_RESQ_EXISTS_TAC `1`
   ++ R_TAC [MULT_GROUP_ID_WITNESS, MULT_GROUP_INV]);

val MULT_GROUP_SUBTYPE = store_thm
  ("MULT_GROUP_SUBTYPE",
   ``mult_group IN (gtnum 1 -> finite_group)``,
   R_TAC [IN_FUNSET, MULT_GROUP, IN_GTNUM]);

val MULT_GROUP_ID = store_thm
  ("MULT_GROUP_ID",
   ``!n. 1 < n ==> (gid (mult_group n) = 1)``,
   S_TAC
   ++ Know `mult_group n IN group` >> G_TAC [Q_RESQ_SPEC `n` MULT_GROUP]
   ++ STRIP_TAC
   ++ Know `1 IN gset (mult_group n)` >> R_TAC [MULT_GROUP_ID_WITNESS]
   ++ STRIP_TAC
   ++ MP_TAC (Q_RESQ_ISPECL [`mult_group n`, `1:num`] GID_UNIQUE)
   ++ Suff `gop (mult_group n) 1 1 = 1` >> PROVE_TAC []
   ++ R_TAC [MULT_GROUP_OP]
   ++ AG_TAC []);

val MULT_GROUP_GPOW = store_thm
  ("MULT_GROUP_GPOW",
   ``!n. !g :: gset (mult_group n). !m.
       1 < n ==>
       (gpow (mult_group n) g m = (g EXP m) MOD n)``,
   S_TAC
   ++ Induct_on `m` >> AG_TAC [EXP, MULT_GROUP_ID]
   ++ G_TAC [MULT_GROUP_OP, EXP]);

val FERMAT_LITTLE = store_thm
  ("FERMAT_LITTLE",
   ``!n. !a :: gset (mult_group n). 1 < n ==> ((a EXP totient n) MOD n = 1)``,
   S_TAC
   ++ Suff `gpow (mult_group n) a (totient n) = gid (mult_group n)`
   >> R_TAC [MULT_GROUP_GPOW, MULT_GROUP_ID]
   ++ G_TAC [totient_def, MULT_GROUP]);

val CARD_COPRIME_PRIME = store_thm
  ("CARD_COPRIME_PRIME",
   ``!p n.
       0 < n /\ prime p ==>
       (CARD (gset (add_group n) INTER (\x. ~divides p x)) =
        n - (((n - 1) DIV p) + 1))``,
   S_TAC
   ++ Cases_on `n` >> AR_TAC []
   ++ AR_TAC []
   ++ Q.SPEC_TAC (`n'`, `n`)
   ++ Induct
   >> (G_TAC [INSERT_INTER, ADD_GROUP_SET_SUC, ADD_GROUP_SET_ZERO]
       ++ G_TAC [SPECIFICATION])
   ++ POP_ASSUM MP_TAC
   ++ Know `SUC (SUC n) - 1 = SUC (SUC n - 1)` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Know `SUC n - 1 = n` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ STRIP_TAC
   ++ ONCE_REWRITE_TAC [ADD_GROUP_SET_SUC]
   ++ R_TAC [INSERT_INTER, SUC_DIV]
   ++ R_TAC [SPECIFICATION]
   ++ Cases_on `divides p (SUC n)`
   >> (R_TAC [] ++ DECIDE_TAC)
   ++ R_TAC []
   ++ Know `FINITE (gset (add_group (SUC n)) INTER (\x. ~divides p x))`
   >> PROVE_TAC [ADD_GROUP_SET_FINITE, INTER_FINITE]
   ++ STRIP_TAC
   ++ G_TAC [CARD_INSERT, IN_INTER, ADD_GROUP_SET_MAX]
   ++ Know `n DIV p <= n` >> R_TAC [DIV_LESS_EQ]
   ++ STRIP_TAC
   ++ R_TAC [GSYM ADD1]
   ++ POP_ASSUM MP_TAC
   ++ KILL_TAC
   ++ DECIDE_TAC);

val MULT_GROUP_SET_ALT = store_thm
  ("MULT_GROUP_SET_ALT",
   ``!n. gset (mult_group n) = gset (add_group n) INTER (\x. gcd n x = 1)``,
   SET_EQ_TAC
   ++ R_TAC [MULT_GROUP_SET, IN_INTER]
   ++ R_TAC [SPECIFICATION]);

val MULT_GROUP_SET_PRIME_POWER = store_thm
  ("MULT_GROUP_SET_PRIME_POWER",
   ``!p a.
       0 < a /\ prime p ==>
       (CARD (gset (mult_group (p EXP a))) = p EXP (a - 1) * (p - 1))``,
   S_TAC
   ++ R_TAC [CARD_COPRIME_PRIME, MULT_GROUP_SET_ALT, GCD_1_PRIME_POWERL]
   ++ Know `0 < p EXP a` >> R_TAC []
   ++ STRIP_TAC
   ++ Know `(p EXP a - 1) DIV p = (p EXP a) DIV p - 1`
   >> (Know `SUC (p EXP a - 1) = p EXP a` >> DECIDE_TAC
       ++ STRIP_TAC
       ++ Suff `(p EXP a - 1) DIV p = SUC ((p EXP a) - 1) DIV p - 1`
       >> R_TAC []
       ++ R_TAC [SUC_DIV]
       ++ Know `?s. s <= a /\ (p = p EXP s)`
       >> (Q.EXISTS_TAC `1`
           ++ R_TAC []
           ++ DECIDE_TAC)
       ++ DISCH_THEN (R_TAC o wrap)
       ++ DECIDE_TAC)
   ++ STRIP_TAC
   ++ R_TAC []
   ++ Know `1 <= p EXP a DIV p`
   >> (Suff `~(p EXP a DIV p = 0)` >> DECIDE_TAC
       ++ R_TAC []
       ++ Cases_on `a` >> AR_TAC []
       ++ R_TAC [EXP]
       ++ Suff `p * 1 <= p * p EXP n` >> DECIDE_TAC
       ++ R_TAC []
       ++ Suff `0 < p EXP n` >> DECIDE_TAC
       ++ R_TAC [])
   ++ STRIP_TAC
   ++ R_TAC []
   ++ Cases_on `a` >> AR_TAC []
   ++ R_TAC [EXP, LEFT_SUB_DISTRIB]
   ++ Know `SUC n - 1 = n` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ R_TAC [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
   ++ PROVE_TAC [MULT_COMM]);

val TOTIENT_PRIME_POWER = store_thm
  ("TOTIENT_PRIME_POWER",
   ``!p a.
        0 < a /\ prime p ==> (totient (p EXP a) = p EXP (a - 1) * (p - 1))``,
   R_TAC [totient_def, MULT_GROUP_SET_PRIME_POWER]);

val TOTIENT_PRIME = store_thm
  ("TOTIENT_PRIME",
   ``!p. prime p ==> (totient p = p - 1)``,
   S_TAC
   ++ MP_TAC (Q_RESQ_SPECL [`p`, `1`] TOTIENT_PRIME_POWER)
   ++ R_TAC [EXP, EXP_1]);

val FERMAT_LITTLE_PRIME = store_thm
  ("FERMAT_LITTLE_PRIME",
   ``!p a. prime p /\ ~(divides p a) ==> ((a EXP (p - 1)) MOD p = 1)``,
   S_TAC
   ++ Suff `(a MOD p) EXP (p - 1) MOD p = 1` >> R_TAC [MOD_EXP]
   ++ Know `(a MOD p) IN gset (mult_group p)`
   >> R_TAC [MULT_GROUP_SET, ADD_GROUP_SET, DIVIDES_PRIME_MOD, GCD_1_PRIMEL]
   ++ STRIP_TAC
   ++ MP_TAC (Q_RESQ_SPECL [`p`, `a MOD p`] FERMAT_LITTLE)
   ++ R_TAC [TOTIENT_PRIME]);

val CHINESE_INJ = store_thm
  ("CHINESE_INJ",
   ``!p q x y.
       1 < p /\ 1 < q /\ (gcd p q = 1) /\ (x MOD p = y MOD p) /\
       (x MOD q = y MOD q) ==>
       (x MOD (p * q) = y MOD (p * q))``,
   S_TAC
   ++ Know `1 < p * q` >> R_TAC []
   ++ S_TAC
   ++ Suff
      `x MOD (p * q) < y MOD (p * q) \/ y MOD (p * q) < x MOD (p * q) ==> F`
   >> DECIDE_TAC
   ++ S_TAC <<
   [Know `x MOD (p * q) + (y MOD (p * q) - x MOD (p * q)) = y MOD (p * q)`
    >> DECIDE_TAC
    ++ Know `~(divides (p * q) (y MOD (p * q) - x MOD (p * q)))`
    >> (Suff
          `0 < y MOD (p * q) - x MOD (p * q) /\
           ~(p * q <= y MOD (p * q) - x MOD (p * q))`
        >> PROVE_TAC [DIVIDES_LE]
        ++ Know `y MOD (p * q) < p * q` >> R_TAC []
        ++ DECIDE_TAC)
    ++ Q.SPEC_TAC (`y MOD (p * q) - x MOD (p * q)`, `d`)
    ++ POP_ASSUM K_TAC
    ++ S_TAC
    ++ Know `(x MOD (p * q) + d) MOD p = (y MOD (p * q)) MOD p` >> R_TAC []
    ++ PURE_ONCE_REWRITE_TAC [MULT_COMM]
    ++ POP_ASSUM (fn th => R_TAC [MOD_MULT_MOD] ++ ASSUME_TAC th)
    ++ S_TAC
    ++ Know `d MOD p = 0`
    >> (POP_ASSUM MP_TAC
        ++ R_TAC [MOD_ADD_CANCEL])
    ++ Know `(x MOD (p * q) + d) MOD q = (y MOD (p * q)) MOD q` >> R_TAC []
    ++ POP_ASSUM (fn th => R_TAC [MOD_MULT_MOD] ++ ASSUME_TAC th)
    ++ RESQ_STRIP_TAC
    ++ Know `d MOD q = 0`
    >> (POP_ASSUM MP_TAC
        ++ R_TAC [MOD_ADD_CANCEL])
    ++ NTAC 3 (POP_ASSUM K_TAC)
    ++ R_TAC [DIVIDES_MOD]
    ++ S_TAC
    ++ PROVE_TAC [GCD_1_LCM],
    Know `y MOD (p * q) + (x MOD (p * q) - y MOD (p * q)) = x MOD (p * q)`
    >> DECIDE_TAC
    ++ Know `~(divides (p * q) (x MOD (p * q) - y MOD (p * q)))`
    >> (Suff
          `0 < x MOD (p * q) - y MOD (p * q) /\
           ~(p * q <= x MOD (p * q) - y MOD (p * q))`
        >> PROVE_TAC [DIVIDES_LE]
        ++ Know `x MOD (p * q) < p * q` >> R_TAC []
        ++ DECIDE_TAC)
    ++ Q.SPEC_TAC (`x MOD (p * q) - y MOD (p * q)`, `d`)
    ++ POP_ASSUM K_TAC
    ++ S_TAC
    ++ Know `(y MOD (p * q) + d) MOD p = (x MOD (p * q)) MOD p` >> R_TAC []
    ++ PURE_ONCE_REWRITE_TAC [MULT_COMM]
    ++ POP_ASSUM (fn th => R_TAC [MOD_MULT_MOD] ++ ASSUME_TAC th)
    ++ S_TAC
    ++ Know `d MOD p = 0`
    >> (POP_ASSUM MP_TAC
        ++ R_TAC [MOD_ADD_CANCEL])
    ++ Know `(y MOD (p * q) + d) MOD q = (x MOD (p * q)) MOD q` >> R_TAC []
    ++ POP_ASSUM (fn th => R_TAC [MOD_MULT_MOD] ++ ASSUME_TAC th)
    ++ RESQ_STRIP_TAC
    ++ Know `d MOD q = 0`
    >> (POP_ASSUM MP_TAC
        ++ R_TAC [MOD_ADD_CANCEL])
    ++ NTAC 3 (POP_ASSUM K_TAC)
    ++ R_TAC [DIVIDES_MOD]
    ++ S_TAC
    ++ PROVE_TAC [GCD_1_LCM]]);

val CHINESE_REMAINDER_WITNESS = store_thm
  ("CHINESE_REMAINDER_WITNESS",
   ``!p q.
       1 < p /\ 1 < q /\ (gcd p q = 1) ==>
       (\x. (x MOD p, x MOD q)) IN
       group_iso (mult_group (p * q))
       (prod_group (mult_group p) (mult_group q))``,
   S_TAC
   ++ Know `?n. p * q = n` >> PROVE_TAC []
   ++ STRIP_TAC
   ++ Know `1 < p * q` >> R_TAC []
   ++ ASM_REWRITE_TAC []
   ++ STRIP_TAC
   ++ R_TAC [IN_GROUP_ISO, IN_GROUP_HOMO, PROD_GROUP_SET, PROD_GROUP_OP]
   ++ STRONG_CONJ_TAC <<
   [S_TAC <<
    [R_TAC [IN_FUNSET, MULT_GROUP_SET, IN_CROSS, ADD_GROUP_SET]
     ++ NTAC 2 RESQ_STRIP_TAC
     ++ Know `gcd (p * q) x = 1` >> PROVE_TAC []
     ++ R_TAC [GCD_1_MULTL]
     ++ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GCD_EFFICIENTLY]))
     ++ Cases_on `x = 0` >> AR_TAC []
     ++ Cases_on `p = 0` >> AR_TAC []
     ++ Cases_on `q = 0` >> AR_TAC []
     ++ R_TAC []
     ++ METIS_TAC [GCD_SYM],
     R_TAC [MULT_GROUP_OP]
     ++ Suff `(x * y) MOD p = (x * y) MOD (q * p) MOD p`
     >> METIS_TAC [MULT_COMM]
     ++ R_TAC [MOD_MULT_MOD],
     R_TAC [MULT_GROUP_OP]
     ++ Suff `(x * y) MOD q = (x * y) MOD (p * q) MOD q` >> R_TAC []
     ++ R_TAC [MOD_MULT_MOD]],
    R_TAC [BIJ_ALT_RES]
    ++ DISCH_THEN K_TAC
    ++ S_TAC
    ++ POP_ASSUM MP_TAC
    ++ R_TAC [IN_CROSS, MULT_GROUP_SET]
    ++ Cases_on `y`
    ++ R_TAC []
    ++ R_TAC [RES_EXISTS_UNIQUE]
    ++ S_TAC <<
    [MP_TAC (Q.SPECL [`p`, `q`] LINEAR_GCD)
     ++ MP_TAC (Q.SPECL [`q`, `p`] LINEAR_GCD)
     ++ Know `~(p = 0) /\ ~(q = 0)` >> DECIDE_TAC
     ++ Know `gcd q p = 1` >> METIS_TAC [GCD_SYM]
     ++ R_TAC []
     ++ DISCH_THEN K_TAC
     ++ S_TAC
     ++ Q_RESQ_EXISTS_TAC `(p * (p'' * r) + q * (p' * q')) MOD n`
     ++ S_TAC <<
     [R_TAC [MULT_GROUP_SET, ADD_GROUP_SET]
      ++ Suff `gcd n (p * (p'' * r) + q * (p' * q')) = 1`
      >> (Know `~(n = 0)` >> DECIDE_TAC
          ++ METIS_TAC [GCD_EFFICIENTLY, GCD_SYM])
      ++ Suff
      `(?a. prime a /\ divides a (gcd n (p * (p'' * r) + q * (p' * q')))) ==> F`
      >> (KILL_TAC
          ++ Q.SPEC_TAC (`gcd n (p * (p'' * r) + q * (p' * q'))`, `m`)
          ++ METIS_TAC [EXISTS_PRIME_DIVISOR])
      ++ S_TAC
      ++ AR_TAC [DIVIDES_GCD]
      ++ Know `divides a (q * p)` >> METIS_TAC [MULT_COMM]
      ++ R_TAC [EUCLID]
      ++ S_TAC <<
      [Suff `~divides a (p * (p'' * r))`
       >> METIS_TAC [ADD_COMM, DIVIDES_ADD_2, DIVIDES_MULT]
       ++ Suff `~divides a ((p'' * p) * r)`
       >> METIS_TAC [MULT_COMM, MULT_ASSOC]
       ++ ASM_REWRITE_TAC []
       ++ R_TAC [RIGHT_ADD_DISTRIB]
       ++ Suff `~divides a r`
       >> METIS_TAC [MULT_COMM, MULT_ASSOC, DIVIDES_ADD_2, DIVIDES_MULT]
       ++ S_TAC
       ++ Know `divides a (gcd q r)` >> R_TAC [DIVIDES_GCD]
       ++ R_TAC [],
       Suff `~divides a (q * (p' * q'))`
       >> METIS_TAC [ADD_COMM, DIVIDES_ADD_2, DIVIDES_MULT]
       ++ Suff `~divides a ((p' * q) * q')`
       >> METIS_TAC [MULT_COMM, MULT_ASSOC]
       ++ ASM_REWRITE_TAC []
       ++ R_TAC [RIGHT_ADD_DISTRIB]
       ++ Suff `~divides a q'`
       >> METIS_TAC [MULT_COMM, MULT_ASSOC, DIVIDES_ADD_2, DIVIDES_MULT]
       ++ S_TAC
       ++ Know `divides a (gcd p q')` >> R_TAC [DIVIDES_GCD]
       ++ R_TAC []],
      Q.PAT_X_ASSUM `p * q = n`
        (fn th => ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [MULT_COMM] (SYM th)])
      ++ R_TAC [MOD_MULT_MOD]
      ++ Suff `q' = ((p' * q) * q') MOD p`
      >> METIS_TAC [MULT_COMM, MULT_ASSOC]
      ++ R_TAC [RIGHT_ADD_DISTRIB]
      ++ AR_TAC [ADD_GROUP_SET],
      Q.PAT_X_ASSUM `p * q = n` (fn th => ONCE_REWRITE_TAC [SYM th])
      ++ R_TAC [MOD_MULT_MOD]
      ++ Suff `r = ((p'' * p) * r) MOD q`
      >> METIS_TAC [MULT_COMM, MULT_ASSOC]
      ++ R_TAC [RIGHT_ADD_DISTRIB]
      ++ AR_TAC [ADD_GROUP_SET]],
     Suff `x MOD (p * q) = y MOD (p * q)`
     >> (Suff `(x MOD (p * q) = x) /\ (y MOD (p * q) = y)` >> R_TAC []
         ++ AR_TAC [MULT_GROUP_SET, ADD_GROUP_SET])
     ++ MATCH_MP_TAC (Q_RESQ_SPECL [`p`, `q`] CHINESE_INJ)
     ++ R_TAC []]]);

val CHINESE_REMAINDER = store_thm
  ("CHINESE_REMAINDER",
   ``!p q.
       1 < p /\ 1 < q /\ (gcd p q = 1) ==>
       ?f.
         f IN
         group_iso (mult_group (p * q))
         (prod_group (mult_group p) (mult_group q))``,
   ho_PROVE_TAC [CHINESE_REMAINDER_WITNESS]);

val MULT_GROUP_ABELIAN = store_thm
  ("MULT_GROUP_ABELIAN",
   ``!n. 1 < n ==> abelian (mult_group n)``,
   S_TAC
   ++ G_TAC [abelian_def]
   ++ S_TAC
   ++ MP_TAC (Q.SPECL [`n`, `g`, `h`] MULT_GROUP_COMM)
   ++ PROVE_TAC []);

val MULT_GROUP_PRIME_CYCLIC = store_thm
  ("MULT_GROUP_PRIME_CYCLIC",
   ``!p. prime p ==> cyclic (mult_group p)``,
   S_TAC
   ++ G_TAC [CYCLIC_ALT, MULT_GROUP_SUBTYPE]
   ++ MP_TAC (Q_RESQ_HALF_ISPEC `mult_group p` STRUCTURE_THM)
   ++ G_TAC' [MULT_GROUP_SUBTYPE, MULT_GROUP_ABELIAN]
   ++ S_TAC
   ++ Q_RESQ_EXISTS_TAC `g`
   ++ R_TAC []
   ++ G_TAC [EQ_LESS_EQ, GORD_LE_CARD, MULT_GROUP_SUBTYPE]
   ++ MP_TAC (Q.SPECL [`p`, `gord (mult_group p) g`] MOD_POLY_NTH_ROOTS)
   ++ G_TAC [MULT_GROUP_SUBTYPE]
   ++ Suff `FINITE (\x. x < p /\ (x EXP gord (mult_group p) g MOD p = 1)) /\
                (gset (mult_group p)) SUBSET
                (\x. x < p /\ (x EXP gord (mult_group p) g MOD p = 1))`
   >> (Q.SPEC_TAC (`gset (mult_group p)`, `s`)
       ++ Q.SPEC_TAC (`(\x. x < p /\ (x EXP gord (mult_group p) g MOD p = 1))`,
                      `t`)
       ++ Q.SPEC_TAC (`gord (mult_group p) g`, `n`)
       ++ KILL_TAC
       ++ S_TAC
       ++ Suff `CARD s <= CARD t` >> DECIDE_TAC
       ++ PROVE_TAC [CARD_SUBSET])
   ++ CONJ_TAC
   >> (R_TAC [GSYM INTER_DEF_ALT]
       ++ MATCH_MP_TAC FINITE_INTER_DISJ
       ++ DISJ1_TAC
       ++ MP_TAC (Q.SPEC `p` ADD_GROUP_SET_FINITE)
       ++ R_TAC [add_group_def, gset_def])
   ++ R_TAC [SUBSET_DEF]
   ++ Q.X_GEN_TAC `x`
   ++ S_TAC
   ++ R_TAC [SPECIFICATION]
   ++ Q.PAT_X_ASSUM `!h :: P. Q h` (MP_TAC o Q_RESQ_SPEC `x`)
   ++ S_TAC
   >> (Q.PAT_X_ASSUM `x IN s` MP_TAC
       ++ R_TAC [mult_group_def, add_group_def, gset_def]
       ++ R_TAC [SPECIFICATION])
   ++ POP_ASSUM MP_TAC
   ++ G_TAC [MULT_GROUP_GPOW, MULT_GROUP_ID]);

val GPOW_PRIME_POWER = store_thm
  ("GPOW_PRIME_POWER",
   ``!p n. !g :: gset (mult_group (p EXP n)).
       0 < n /\ prime p ==>
       (gpow (mult_group (p EXP n)) g (p EXP n) =
        gpow (mult_group (p EXP n)) g (p EXP (n - 1)))``,
   S_TAC
   ++ MP_TAC (Q_RESQ_HALF_ISPECL [`mult_group (p EXP n)`, `g:num`]
              GPOW_MOD_CARD)
   ++ G_TAC' [MULT_GROUP_SUBTYPE]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
   ++ Know `?c. CARD (gset (mult_group (p EXP n))) = c`
   >> PROVE_TAC []
   ++ S_TAC
   ++ R_TAC []
   ++ Know `0 < c`
   >> (POP_ASSUM (R_TAC o wrap o GSYM)
       ++ G_TAC [MULT_GROUP_SUBTYPE])
   ++ S_TAC
   ++ Suff `p EXP n = c + p EXP (n - 1)`
   >> R_TAC []
   ++ POP_ASSUM K_TAC
   ++ POP_ASSUM (R_TAC o wrap o GSYM)
   ++ G_TAC [MULT_GROUP_SET_PRIME_POWER]
   ++ ONCE_REWRITE_TAC [MULT_COMM]
   ++ R_TAC [RIGHT_SUB_DISTRIB]
   ++ Cases_on `n` >> AR_TAC []
   ++ R_TAC [SUC_SUB1]
   ++ Know `p EXP n' <= p * p EXP n'`
   >> (Suff `p EXP n' * 1 <= p * p EXP n'` >> RW_TAC arith_ss []
       ++ R_TAC [])
   ++ R_TAC [EXP]);

val STRONG_MULT_GROUP_PRIME_POWER_CYCLIC_LEMMA = store_thm
  ("STRONG_MULT_GROUP_PRIME_POWER_CYCLIC_LEMMA",
   ``!p g.
       ODD p /\ prime p /\ (g EXP (p - 1) MOD p = 1) ==>
       ?x z. ~divides p z /\ ((g + p * x) EXP (p - 1) = 1 + p * z)``,
   S_TAC
   ++ Know `?y. g EXP (p - 1) = 1 + p * y`
   >> (MP_TAC (Q.SPECL [`p`, `g EXP (p - 1)`] DIVISION_ALT)
       ++ R_TAC []
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
       ++ PROVE_TAC [ADD_COMM, MULT_COMM])
   ++ S_TAC
   ++ R_TAC [EXP_PASCAL]
   ++ Cases_on `p` >> PROVE_TAC [NOT_PRIME_0]
   ++ R_TAC [summation_def, BINOMIAL_DEF1, GSYM ADD_ASSOC]
   ++ REWRITE_TAC [ONE]
   ++ R_TAC [SUMMATION_SHIFT_P]
   ++ R_TAC [GSYM ADD1, EXP]
   ++ Know `!a b c d : num. a * (b * (c * d)) = c * (a * b * d)`
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM SUMMATION_TIMES]
   ++ R_TAC [GSYM MULT_ASSOC, GSYM LEFT_ADD_DISTRIB]
   ++ Cases_on `n` >> AR_TAC [GSYM ONE]
   ++ R_TAC [summation_def]
   ++ REWRITE_TAC [ONE]
   ++ R_TAC [SUMMATION_SHIFT_P]
   ++ R_TAC [GSYM ADD1, EXP]
   ++ Know `!a b c d : num. a * (b * (c * d)) = c * (a * b * d)`
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM SUMMATION_TIMES]
   ++ R_TAC [GSYM MULT_ASSOC]
   ++ Q.EXISTS_TAC `SUC n' * g * (1 + (SUC (SUC n') - y MOD SUC (SUC n')))`
   ++ Q.EXISTS_TAC `y +
       SUC n' * g * (1 + (SUC (SUC n') - y MOD SUC (SUC n'))) *
       (binomial (SUC n') 1 * g EXP n' +
        SUC (SUC n') *
        (SUC n' * g * (1 + (SUC (SUC n') - y MOD SUC (SUC n'))) *
         summation 0 n'
           (\n.
              binomial (SUC n') (SUC (SUC n)) *
              (g EXP (n' - SUC n) *
               (SUC (SUC n') * (SUC n' * g * (1 + (SUC (SUC n') - y MOD SUC (SUC n'))))) EXP
               n))))`
   ++ R_TAC []
   ++ ONCE_REWRITE_TAC [LEFT_ADD_DISTRIB]
   ++ R_TAC [ADD_ASSOC]
   ++ Know `!a b c. ~divides a b /\ divides a c ==> ~divides a (b + c)`
   >> PROVE_TAC [DIVIDES_ADD_2, ADD_COMM]
   ++ DISCH_THEN MATCH_MP_TAC
   ++ Know `!a b c : num. a * (b * c) = b * (a * c)`
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC []
   ++ Cases_on `n'` >> AR_TAC [ODD]
   ++ R_TAC [BINOMIAL_1]
   ++ Know `!a b c d : num. a * b * c * d = a * (b * d) * c`
   >> PROVE_TAC [MULT_ASSOC, MULT_COMM]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `!a b c d : num. a * (b * c * d) = (a * b) * (c * d)`
   >> PROVE_TAC [MULT_ASSOC, MULT_COMM]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM EXP]
   ++ Know `SUC (SUC n) = SUC (SUC (SUC n)) - 1` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ POP_ASSUM_TAC (Q.SPEC_TAC (`SUC (SUC (SUC n))`, `p`))
   ++ S_TAC
   ++ POP_ASSUM MP_TAC
   ++ Know `SUC (p - 1) = p`
   >> (Suff `0 < p` >> DECIDE_TAC
       ++ R_TAC [])
   ++ DISCH_THEN (R_TAC o wrap)
   ++ R_TAC [GSYM DIVIDES_MOD, MINUS_1_SQUARED_MOD]
   ++ Know `!a b c : num. a + (b + c) = b + (a + c)`
   >> PROVE_TAC [ADD_COMM, ADD_ASSOC]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Suff `(1 + (y + (p - y MOD p))) MOD p = 1 MOD p`
   >> R_TAC []
   ++ R_TAC [MOD_ADD_CANCEL]
   ++ Know `!a b c : num. a <= b /\ a <= c ==> (b + (c - a) = c + (b - a))`
   >> DECIDE_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`y MOD p`, `y`, `p`])
   ++ R_TAC [MOD_LESS_1]
   ++ DISCH_THEN K_TAC
   ++ Know `y - y MOD p = (y DIV p) * p`
   >> (MP_TAC (Q.SPECL [`p`, `y`] DIVISION_ALT)
       ++ R_TAC []
       ++ DECIDE_TAC)
   ++ R_TAC []);

val STRONG_MULT_GROUP_PRIME_POWER_CYCLIC = store_thm
  ("STRONG_MULT_GROUP_PRIME_POWER_CYCLIC",
   ``!p.
       ODD p /\ prime p ==>
       ?x. !n.
         0 < n ==>
         (x MOD (p EXP n)) IN gset (mult_group (p EXP n)) /\
         (gord (mult_group (p EXP n)) (x MOD (p EXP n)) =
          totient (p EXP n))``,
   S_TAC
   ++ MP_TAC (Q.SPEC `p` MULT_GROUP_PRIME_CYCLIC)
   ++ R_TAC [CYCLIC_ALT, MULT_GROUP_SUBTYPE, GSYM totient_def]
   ++ R_TAC [TOTIENT_PRIME, TOTIENT_PRIME_POWER]
   ++ S_TAC
   ++ MP_TAC (Q.SPECL [`p`, `g`] STRONG_MULT_GROUP_PRIME_POWER_CYCLIC_LEMMA)
   ++ R_TAC []
   ++ Know `g EXP (p - 1) MOD p = 1`
   >> (Suff `gpow (mult_group p) g (p - 1) = gid (mult_group p)`
       >> R_TAC [MULT_GROUP_GPOW, MULT_GROUP_ID]
       ++ POP_ASSUM (fn th => G_TAC [SYM th, MULT_GROUP_SUBTYPE]))
   ++ DISCH_THEN (fn th => R_TAC [th])
   ++ S_TAC
   ++ Q.EXISTS_TAC `g + p * x`
   ++ NTAC 2 STRIP_TAC
   ++ STRONG_CONJ_TAC
   >> (Q.PAT_X_ASSUM `g IN X` MP_TAC
       ++ R_TAC [MULT_GROUP_SET, ADD_GROUP_SET, GCD_1_PRIMEL]
       ++ STRIP_TAC
       ++ ONCE_REWRITE_TAC [GCD_SYM]
       ++ MP_TAC (SYM (Q.SPECL [`p EXP n`, `g + p * x`] GCD_EFFICIENTLY))
       ++ R_TAC []
       ++ DISCH_THEN K_TAC
       ++ R_TAC [GCD_1_PRIME_POWERL]
       ++ PROVE_TAC [DIVIDES_UPR, DIVIDES_ADD_2, ADD_COMM])
   ++ Know `?g'. (g + p * x) MOD (p EXP n) = g'` >> PROVE_TAC []
   ++ STRIP_TAC
   ++ R_TAC []
   ++ STRIP_TAC
   ++ MATCH_MP_TAC DIVIDES_ANTISYM
   ++ STRONG_CONJ_TAC
   >> (R_TAC [GSYM MULT_GROUP_SET_PRIME_POWER]
       ++ G_TAC [MULT_GROUP_SUBTYPE, GSYM GPOW_GID_GORD])
   ++ S_TAC
   ++ ONCE_REWRITE_TAC [MULT_COMM]
   ++ Know `gcd (p - 1) (p EXP (n - 1)) = 1`
   >> (Cases_on `n - 1` >> R_TAC []
       ++ R_TAC [GCD_1_PRIME_POWERR]
       ++ Suff `0 < (p - 1) /\ ~(p <= p - 1)` >> PROVE_TAC [DIVIDES_LE]
       ++ Know `1 < p` >> R_TAC []
       ++ DECIDE_TAC)
   ++ R_TAC [GCD_1_LCM]
   ++ DISCH_THEN K_TAC
   ++ STRONG_CONJ_TAC
   >> (Suff `gpow (mult_group p) g (gord (mult_group (p EXP n)) g') =
                 gid (mult_group p)`
       >> R_TAC [GPOW_GID_GORD, MULT_GROUP_SUBTYPE]
       ++ Know
          `gpow (mult_group (p EXP n)) g' (gord (mult_group (p EXP n)) g') =
           gid (mult_group (p EXP n))`
       >> G_TAC [MULT_GROUP_SUBTYPE]
       ++ R_TAC [MULT_GROUP_GPOW, MULT_GROUP_ID]
       ++ Q.SPEC_TAC (`gord (mult_group (p EXP n)) g'`, `m`)
       ++ STRIP_TAC
       ++ Q.PAT_X_ASSUM `gg = g'` (REWRITE_TAC o wrap o SYM)
       ++ R_TAC []
       ++ S_TAC
       ++ Know `((g + p * x) EXP m MOD p EXP n) MOD p = 1 MOD p`
       >> PROVE_TAC []
       ++ POP_ASSUM K_TAC
       ++ Cases_on `n` >> DECIDE_TAC
       ++ REWRITE_TAC [EXP]
       ++ ONCE_REWRITE_TAC [MULT_COMM]
       ++ R_TAC [MOD_MULT_MOD]
       ++ STRIP_TAC
       ++ Know `((g + x * p) MOD p) EXP m MOD p = 1`
       >> R_TAC []
       ++ Know `(g + x * p) MOD p = g MOD p` >> R_TAC []
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ R_TAC [])
   ++ S_TAC
   ++ Know
      `?k. k <= n - 1 /\
           (p EXP k * (p - 1) = gord (mult_group (p EXP n)) g')`
   >> (MP_TAC (Q.SPECL [`p`, `gord (mult_group (p EXP n)) g'`, `n - 1`, `p - 1`]
               PRIME_POWER_SANDWICH)
       ++ R_TAC [])
   ++ NTAC 2 (POP_ASSUM K_TAC)
   ++ S_TAC
   ++ POP_ASSUM (fn th => ASSUME_TAC (SYM th) ++ REWRITE_TAC [SYM th])
   ++ Suff `k = n - 1` >> R_TAC []
   ++ MP_TAC (Q.SPECL [`p`, `z`, `k`] PRIME_ADD_1_EXP)
   ++ R_TAC []
   ++ S_TAC
   ++ Suff `(1 + p EXP (k + 1) * zk) MOD (p EXP n) = 1 MOD (p EXP n)`
   >> (R_TAC [MOD_ADD_CANCEL, DIVIDES_MOD]
       ++ Know `n = k + 1 + (n - (k + 1))` >> DECIDE_TAC
       ++ DISCH_THEN (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV o wrap)
       ++ R_TAC [EXP_ADD]
       ++ Cases_on `n - (k + 1)`
       >> (STRIP_TAC
           ++ Know `n = k + 1` >> DECIDE_TAC
           ++ Q.PAT_X_ASSUM `0 < n` MP_TAC
           ++ KILL_TAC
           ++ DECIDE_TAC)
       ++ R_TAC [EXP]
       ++ STRIP_TAC
       ++ Suff `divides p zk` >> PROVE_TAC []
       ++ PROVE_TAC [DIVIDES_DOWNL])
   ++ R_TAC []
   ++ POP_ASSUM (REWRITE_TAC o wrap o SYM)
   ++ Q.PAT_X_ASSUM `q = 1 + p * z` (REWRITE_TAC o wrap o SYM)
   ++ REWRITE_TAC [ONCE_REWRITE_RULE [MULT_COMM] EXP_MULT]
   ++ Q.PAT_X_ASSUM `gord gp g' = q` (REWRITE_TAC o wrap o SYM)
   ++ Suff `g' EXP gord (mult_group (p EXP n)) g' MOD p EXP n = 1`
   >> (Q.PAT_X_ASSUM `q = g'` (REWRITE_TAC o wrap o SYM)
       ++ Q.SPEC_TAC (`gord (mult_group (p EXP n)) ((g + p * x) MOD p EXP n)`,
                      `m`)
       ++ Q.SPEC_TAC (`g + p * x`, `gg`)
       ++ R_TAC [])
   ++ R_TAC [GSYM MULT_GROUP_GPOW]
   ++ G_TAC [MULT_GROUP_SUBTYPE]
   ++ R_TAC [MULT_GROUP_ID]);

val MULT_GROUP_PRIME_POWER_CYCLIC = store_thm
  ("MULT_GROUP_PRIME_POWER_CYCLIC",
   ``!p n. ODD p /\ prime p /\ 0 < n ==> cyclic (mult_group (p EXP n))``,
   S_TAC
   ++ MP_TAC (Q.SPEC `p` STRONG_MULT_GROUP_PRIME_POWER_CYCLIC)
   ++ R_TAC []
   ++ S_TAC
   ++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
   ++ R_TAC []
   ++ R_TAC [CYCLIC_ALT, totient_def, MULT_GROUP_SUBTYPE]
   ++ S_TAC
   ++ Q_RESQ_EXISTS_TAC `x MOD p EXP n`
   ++ R_TAC []);

val MULT_GROUP_SET_CARD = store_thm
  ("MULT_GROUP_SET_CARD",
   ``!n. 1 < n ==> CARD (gset (mult_group n)) <= n - 1``,
   Strip
   ++ Simplify [ADD_GROUP_SET, mult_group_def, gset_def]
   ++ Know `FINITE ((\x. x < n) DIFF {0})`
   >> (MATCH_MP_TAC FINITE_DIFF
       ++ ho_PROVE_TAC [FINITE_LESS])
   ++ Strip
   ++ Know `CARD (\x. x < n /\ (gcd n x = 1)) <= CARD ((\x. x < n) DIFF {0})`
   >> (MP_TAC (Q.ISPEC `((\x : num. x < n) DIFF {0})` CARD_SUBSET)
       ++ Simplify []
       ++ DISCH_THEN MATCH_MP_TAC
       ++ Simplify [SUBSET_DEF, IN_DIFF]
       ++ Simplify [SPECIFICATION]
       ++ Strip
       ++ AR_TAC [])
   ++ Suff `CARD ((\x. x < n) DIFF {0}) = n - 1` >> DECIDE_TAC
   ++ Simplify [CARD_DIFF, FINITE_LESS, CARD_LESS]
   ++ Suff `{0} SUBSET (\x. x < n)` >> Simplify [SUBSET_INTER2]
   ++ Simplify [SUBSET_DEF]
   ++ Simplify [SPECIFICATION]
   ++ DECIDE_TAC);

val POWER_IN_MULT_GROUP = store_thm
  ("POWER_IN_MULT_GROUP",
   ``!n x y i.
       1 < n /\ x < n /\ 0 < i /\ ((x EXP i) MOD n = y) /\
       y IN gset (mult_group n) ==>
       x IN gset (mult_group n)``,
   Cases_on `i` >> Simplify []
   ++ Simplify [EXP, MULT_GROUP_SET, ADD_GROUP_SET]
   ++ Strip
   ++ Suff `!p. prime p ==> ~divides p (gcd n' x)`
   >> PROVE_TAC [EXISTS_PRIME_DIVISOR]
   ++ Simplify [DIVIDES_GCD]
   ++ Strip
   ++ Suff `divides p (gcd n' y)`
   >> PROVE_TAC [EXISTS_PRIME_DIVISOR]
   ++ Simplify [DIVIDES_GCD]
   ++ Simplify [GSYM DIVIDES_MOD]
   ++ Q.PAT_X_ASSUM `z = y` (ONCE_REWRITE_TAC o wrap o SYM)
   ++ Q.PAT_X_ASSUM `divides p n'` MP_TAC
   ++ REWRITE_TAC [divides_def]
   ++ Strip
   ++ Know `0 < q` >> (Suff `~(q = 0)` >> DECIDE_TAC ++ Strip ++ AR_TAC [])
   ++ POP_ASSUM (REWRITE_TAC o wrap)
   ++ Q.PAT_X_ASSUM `divides p x` MP_TAC
   ++ Simplify [MOD_MULT_MOD, GSYM DIVIDES_MOD]);

val POWER_ID_IN_MULT_GROUP = store_thm
  ("POWER_ID_IN_MULT_GROUP",
   ``!n x i.
       1 < n /\ x < n /\ 0 < i /\ ((x EXP i) MOD n = 1) ==>
       x IN gset (mult_group n)``,
   Strip
   ++ MATCH_MP_TAC POWER_IN_MULT_GROUP
   ++ Q.EXISTS_TAC `gid (mult_group n)`
   ++ Q.EXISTS_TAC `i`
   ++ ASSUME_TAC (Q.SPEC `n` MULT_GROUP)
   ++ RES_TAC
   ++ G_TAC' []
   ++ Simplify [MULT_GROUP_ID]);

val MULT_GROUP_1 = store_thm
  ("MULT_GROUP_1",
   ``!n. 1 < n ==> 1 IN gset (mult_group n)``,
   Strip
   ++ MATCH_MP_TAC POWER_ID_IN_MULT_GROUP
   ++ Q.EXISTS_TAC `1`
   ++ Simplify []);

val MINUS_1_IN_MULT_GROUP = store_thm
  ("MINUS_1_IN_MULT_GROUP",
   ``!n. 1 < n ==> (n - 1) IN gset (mult_group n)``,
   Strip
   ++ MATCH_MP_TAC POWER_ID_IN_MULT_GROUP
   ++ Q.EXISTS_TAC `2`
   ++ REWRITE_TAC [TWO, ONE, EXP]
   ++ Simplify [MINUS_1_SQUARED_MOD]
   ++ DECIDE_TAC);

val MULT_GROUP_GORD_MINUS_1 = store_thm
  ("MULT_GROUP_GORD_MINUS_1",
   ``!n. 2 < n ==> (gord (mult_group n) (n - 1) = 2)``,
   Strip
   ++ Know `1 < n` >> DECIDE_TAC
   ++ Strip
   ++ MP_TAC (Q.SPEC `n` MINUS_1_IN_MULT_GROUP)
   ++ G_TAC [MULT_GROUP_SUBTYPE, IS_GORD]
   ++ Simplify [MULT_GROUP_GPOW, MULT_GROUP_ID]
   ++ DISCH_THEN K_TAC
   ++ Know `!m : num. 0 < m /\ m < 2 = (m = 1)` >> DECIDE_TAC
   ++ Know `n - 1 < n` >> DECIDE_TAC
   ++ Simplify [TWO, EXP, MINUS_1_SQUARED_MOD]
   ++ Strip
   ++ POP_ASSUM MP_TAC
   ++ Q.PAT_X_ASSUM `2 < n` MP_TAC
   ++ KILL_TAC
   ++ DECIDE_TAC);

val IN_MULT_GROUP_UP = store_thm
  ("IN_MULT_GROUP_UP",
   ``!x p q.
       1 < p /\ 1 < q /\ x IN gset (mult_group (p * q)) ==>
       x MOD p IN gset (mult_group p)``,
   Simplify [MULT_GROUP_SET, ADD_GROUP_SET]
   ++ Strip
   ++ ONCE_REWRITE_TAC [GCD_SYM]
   ++ Suff `~(p = 0) /\ (gcd p x = 1)` >> PROVE_TAC [GCD_EFFICIENTLY]
   ++ Simplify []
   ++ PROVE_TAC [GCD_1_MULTL]);

val SQUARE_1_MOD_PRIME = store_thm
  ("SQUARE_1_MOD_PRIME",
   ``!p n.
       prime p ==>
       (((n * n) MOD p = 1) = (n MOD p = 1) \/ (n MOD p = p - 1))``,
   Strip
   ++ Cases_on `p = 2`
   >> (Cases_on `EVEN n`
       ++ Simplify [MOD_TWO, EVEN_ODD_BASIC]
       ++ DECIDE_TAC)
   ++ ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [CONJ_COMM] EQ_IMP_THM]
   ++ Q.SPEC_TAC (`n`, `n`)
   ++ CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
   ++ STRONG_CONJ_TAC >> (Strip ++ Simplify [MINUS_1_SQUARED_MOD])
   ++ Know `!n. n * n = n EXP 2`
   >> (REWRITE_TAC [TWO, ONE, EXP]
       ++ Simplify [])
   ++ DISCH_THEN (Simplify o wrap)
   ++ Strip
   ++ MP_TAC (Q.SPECL [`p`, `2`] MOD_POLY_NTH_ROOTS)
   ++ Simplify []
   ++ Strip
   ++ Suff `(\x. x < p /\ (x EXP 2 MOD p = 1)) = {1; p - 1}`
   >> (SET_EQ_TAC
       ++ Simplify [IN_INSERT]
       ++ Simplify [SPECIFICATION]
       ++ DISCH_THEN (MP_TAC o Q.SPEC `n MOD p`)
       ++ Simplify [])
   ++ MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC FINITE_SUBSET_CARD_EQ
   ++ STRONG_CONJ_TAC >> Simplify [FINITE_LESS1]
   ++ STRIP_TAC
   ++ STRONG_CONJ_TAC
   >> (Simplify [SUBSET_DEF, IN_INSERT]
       ++ Simplify [SPECIFICATION]
       ++ (Strip ++ Simplify [])
       ++ Suff `0 < p` >> (KILL_TAC ++ DECIDE_TAC)
       ++ Simplify [])
   ++ STRIP_TAC
   ++ ONCE_REWRITE_TAC [EQ_LESS_EQ]
   ++ CONJ_TAC >> Simplify [CARD_SUBSET]
   ++ Know `~(1 = p - 1)`
   >> (Suff `1 < p /\ ~(p = 2)` >> (KILL_TAC ++ DECIDE_TAC)
       ++ Simplify [])
   ++ Simplify [GSYM TWO]);

val _ = export_theory ();
