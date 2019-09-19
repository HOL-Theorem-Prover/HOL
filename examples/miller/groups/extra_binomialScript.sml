(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "extra_binomial";

(* interactive mode
show_assums := true;
loadPath := union ["../finished"] (!loadPath);
app load
  ["bossLib",
   "arithmeticTheory",
   "dividesTheory",
   "gcdTheory",
   "primeTheory",
   "res_quan2Theory",
   "pred_setTheory",
   "boolContextTheory",
   "numContextTheory",
   "res_quanTools",
   "subtypeTools",
   "ho_proverTools",
   "numContext",
   "millerTools",
   "extra_numTheory",
   "ho_basicTools"];
installPP subtypeTools.pp_precontext;
installPP subtypeTools.pp_context;
*)

open bossLib arithmeticTheory dividesTheory gcdTheory
     res_quanTheory pred_setTheory subtypeTheory
     res_quanTools subtypeTools ho_proverTools numContext hurdUtils
     extra_numTheory ho_basicTools arithContext extra_arithTheory
     binomialTheory summationTheory;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS arith_c;


(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val BINOMIAL_1 = store_thm
  ("BINOMIAL_1",
   ``!n. 1 < n ==> (binomial n 1 = n)``,
   Induct >> AR_TAC []
   ++ REWRITE_TAC [ONE, binomial_def]
   ++ Cases_on `n` >> R_TAC []
   ++ Cases_on `n'`
   >> (REWRITE_TAC [ONE, binomial_def]
       ++ DECIDE_TAC)
   ++ AR_TAC []
   ++ R_TAC [binomial_def]
   ++ DECIDE_TAC);

val BINOMIAL_GT_0 = store_thm
  ("BINOMIAL_GT_0",
   ``!a b. 0 < binomial (a + b) b``,
   Induct_on `b` >> R_TAC [BINOMIAL_DEF1]
   ++ R_TAC [ADD_CLAUSES, BINOMIAL_DEF4]);

val BINOMIAL_LESS = store_thm
  ("BINOMIAL_LESS",
   ``!n r. r <= n ==> 0 < binomial n r``,
   S_TAC
   ++ Know `n = (n - r) + r` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [BINOMIAL_GT_0]);

val PRIME_EXPONENT_BINOMIAL = store_thm
  ("PRIME_EXPONENT_BINOMIAL",
   ``!a b p.
       prime p ==>
       (exponent p (binomial (a + b) b) + exponent p (FACT a) +
        exponent p (FACT b) =
        exponent p (FACT (a + b)))``,
   S_TAC
   ++ R_TAC [GSYM PRIME_EXPONENT_MULT, BINOMIAL_GT_0, FACT_LESS,
             GSYM MULT_ASSOC, BINOMIAL_FACT]);

val PRIME_ADD_1_EXP = store_thm
  ("PRIME_ADD_1_EXP",
   ``!p z k.
       prime p /\ ODD p /\ ~divides p z ==>
       ?zk.
         ~divides p zk /\
         ((1 + p * z) EXP (p EXP k) = 1 + p EXP (k + 1) * zk)``,
   S_TAC
   ++ REVERSE (Cases_on `0 < k`)
   >> (Know `k = 0` >> DECIDE_TAC
       ++ R_TAC []
       ++ PROVE_TAC [])
   ++ R_TAC [EXP_PASCAL]
   ++ R_TAC [GSYM ADD1, summation_def]
   ++ Cases_on `p EXP k` >> AR_TAC []
   ++ R_TAC [summation_def]
   ++ Suff
      `divides (p EXP (k + 2))
       (summation (SUC 1) n (\k'. binomial (SUC n) k' * (p * z) EXP k'))`
   >> (DISCH_THEN (MP_TAC o REWRITE_RULE [divides_def])
       ++ S_TAC
       ++ R_TAC []
       ++ Q.EXISTS_TAC `z + q * p`
       ++ S_TAC >> PROVE_TAC [DIVIDES_ADD_2, DIVIDES_UPL, ADD_COMM]
       ++ Cases_on `n`
       >> (Cases_on `k` >> DECIDE_TAC
           ++ AR_TAC [EXP])
       ++ R_TAC [BINOMIAL_1, binomial_def]
       ++ Know `k + 2 = SUC (SUC k)` >> DECIDE_TAC
       ++ DISCH_THEN (fn th => R_TAC [th, EXP, LEFT_ADD_DISTRIB])
       ++ RW_TAC arith_ss [MULT_ASSOC, ADD_ASSOC]
       ++ Know `!a b c d : num. (a = b) /\ (c = d) ==> (a + c = b + d)`
       >> DECIDE_TAC
       ++ DISCH_THEN MATCH_MP_TAC
       ++ PROVE_TAC [MULT_COMM, MULT_ASSOC])
   ++ HO_MATCH_MP_TAC INV_SUMMATION
   ++ R_TAC []
   ++ CONJ_TAC >> PROVE_TAC [DIVIDES_ADD_1]
   ++ S_TAC
   ++ Q.PAT_X_ASSUM `x = y` (REWRITE_TAC o wrap o SYM)
   ++ Know `k' + SUC 1 = k' + 2` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ R_TAC [MULT_EXP, MULT_ASSOC]
   ++ MATCH_MP_TAC DIVIDES_MULTR
   ++ ONCE_REWRITE_TAC [MULT_COMM]
   ++ R_TAC [DIVIDES_POWER_CANCEL]
   ++ Know `k + 2 - (k' + 2) = k - k' : num` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM K_TAC
   ++ REVERSE (Cases_on `k' < k`)
   >> (Know `k - k' = 0` >> DECIDE_TAC
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ R_TAC [])
   ++ MP_TAC (Q.SPECL [`p`, `k`] PRIME_POWER_GE)
   ++ R_TAC []
   ++ S_TAC
   ++ Know `k' + 2 <= p EXP k` >> DECIDE_TAC
   ++ R_TAC [PRIME_EXPONENT_DIVIDES, BINOMIAL_LESS]
   ++ S_TAC
   ++ Know `p EXP k = (p EXP k - (k' + 2)) + (k' + 2)` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `!a b c d : num. a + c + d <= b + c + d ==> a <= b` >> DECIDE_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ Q.EXISTS_TAC `exponent p (FACT (p EXP k - (k' + 2)))`
   ++ Q.EXISTS_TAC `exponent p (FACT (k' + 2))`
   ++ MP_TAC (Q.SPECL [`(p EXP k - (k' + 2))`, `k' + 2`, `p`]
              PRIME_EXPONENT_BINOMIAL)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC []
   ++ Know `k' + 2 = SUC (k' + 1)` >> DECIDE_TAC
   ++ S_TAC
   ++ R_TAC [FACT, PRIME_EXPONENT_MULT, FACT_LESS]
   ++ Cases_on `p EXP k` >> AR_TAC []
   ++ R_TAC [FACT, PRIME_EXPONENT_MULT, FACT_LESS]
   ++ Know
      `!a b c d e f : num.
         a + c <= e /\ (b + d = f) ==> a + b + (c + d) <= e + f` >> DECIDE_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ S_TAC <<
   [POP_ASSUM (AR_TAC o wrap o SYM)
    ++ R_TAC [PRIME_EXPONENT_POWER]
    ++ Suff `~(SUC k' <= exponent p (SUC (k' + 1)))` >> DECIDE_TAC
    ++ R_TAC [GSYM PRIME_EXPONENT_DIVIDES]
    ++ Suff `0 < SUC (k' + 1) /\ ~(p EXP SUC k' <= SUC (k' + 1))`
    >> PROVE_TAC [DIVIDES_LE]
    ++ Suff `SUC k' + 2 <= p EXP SUC k'` >> DECIDE_TAC
    ++ MATCH_MP_TAC (Q.SPECL [`p`, `SUC k'`] PRIME_POWER_GE)
    ++ R_TAC [],
    Know `n = p EXP k - 1` >> DECIDE_TAC
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ Know `k' + 1 <= k` >> DECIDE_TAC
    ++ Know `k + 2 <= p EXP k` >> DECIDE_TAC
    ++ NTAC 5 (POP_ASSUM K_TAC)
    ++ STRIP_TAC
    ++ Q.SPEC_TAC (`k' + 1`, `i`)
    ++ Induct >> R_TAC [FACT, PRIME_EXPONENT_1]
    ++ S_TAC
    ++ Know `i <= k` >> DECIDE_TAC
    ++ S_TAC
    ++ AR_TAC []
    ++ Q.PAT_X_ASSUM `a = b` (ONCE_REWRITE_TAC o wrap o SYM)
    ++ R_TAC [FACT, PRIME_EXPONENT_MULT, FACT_LESS, ADD_ASSOC]
    ++ Know `p EXP k - 1 - i = SUC (p EXP k - 1 - SUC i)` >> DECIDE_TAC
    ++ S_TAC
    ++ R_TAC [FACT, PRIME_EXPONENT_MULT, FACT_LESS, ADD_ASSOC]
    ++ POP_ASSUM (REWRITE_TAC o wrap o SYM)
    ++ Know `p EXP k - 1 - i = p EXP k - SUC i` >> DECIDE_TAC
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ Know `0 < p EXP k - SUC i` >> DECIDE_TAC
    ++ S_TAC
    ++ R_TAC [PRIME_EXPONENT_EQ]
    ++ S_TAC
    ++ EQ_TAC <<
    [S_TAC
     ++ Know `n < k`
     >> (Suff `p EXP n < p EXP k` >> R_TAC [EXP_MONO]
         ++ Suff `p EXP n <= SUC i` >> DECIDE_TAC
         ++ MATCH_MP_TAC DIVIDES_LE
         ++ R_TAC [])
     ++ S_TAC
     ++ Know `p EXP k = p EXP (k - n) * p EXP n`
     >> R_TAC [GSYM EXP_ADD]
     ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
     ++ Know `?q. SUC i = q * p EXP n` >> PROVE_TAC [divides_def]
     ++ S_TAC
     ++ R_TAC [GSYM RIGHT_SUB_DISTRIB],
     S_TAC
     ++ MATCH_MP_TAC DIVIDES_SUB_2
     ++ Q.EXISTS_TAC `p EXP k`
     ++ R_TAC []
     ++ REVERSE CONJ_TAC >> DECIDE_TAC
     ++ Q.EXISTS_TAC `n`
     ++ R_TAC []
     ++ Suff `n < k` >> DECIDE_TAC
     ++ Suff `p EXP n < p EXP k` >> R_TAC [EXP_MONO]
     ++ Suff `p EXP n <= p EXP k - SUC i` >> DECIDE_TAC
     ++ MATCH_MP_TAC DIVIDES_LE
     ++ R_TAC []]]);

(* non-interactive mode
*)
val _ = export_theory ();
