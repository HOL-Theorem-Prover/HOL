(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "num_poly";
val _ = ParseExtras.temp_loose_equality()

(* interactive mode
show_assums := true;
loadPath := union ["..", "../finished"] (!loadPath);
app load
["bossLib", "listTheory", "millerTools", "subtypeTools",
"res_quanTools", "res_quan2Theory", "pred_setTheory",
"extra_pred_setTheory", "arithContext", "relationTheory",
"ho_proverTools", "prob_extraTools", "prob_extraTheory",
"extra_listTheory", "orderTheory", "subtypeTheory", "listContext",
"arithmeticTheory", "groupTheory", "groupContext", "extra_numTheory",
"gcdTheory", "dividesTheory", "primeTheory", "extra_arithTheory",
"finite_groupTheory", "finite_groupContext"];
*)

open bossLib listTheory hurdUtils subtypeTools res_quanTools
     res_quanTheory pred_setTheory extra_pred_setTheory arithContext
     relationTheory ho_proverTools extra_listTheory orderTheory
     subtypeTheory listContext arithmeticTheory extra_numTheory
     gcdTheory dividesTheory extra_arithTheory
     finite_groupTheory pred_setContext rich_listTheory;

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val REVERSE = Tactical.REVERSE;

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


(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val eval_poly_def = Define
  `(eval_poly [] x = 0:num) /\
   (eval_poly (a :: rest) x = a + x * eval_poly rest x)`;

val factor_poly_def = Define
  `(factor_poly [x] a = [0:num])
   /\ (factor_poly (x :: y :: z) a =
       let l = factor_poly (y :: z) a in (y + a * HD l) :: l)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val EVAL_POLY_0 = store_thm
  ("EVAL_POLY_0",
   ``!h t. eval_poly (h :: t) 0 = h``,
   R_TAC [eval_poly_def]);

val EVAL_POLY_BUTLAST = store_thm
  ("EVAL_POLY_BUTLAST",
   ``!h t.
       (LAST (h :: t) = 0) ==>
       (eval_poly (BUTLAST (h :: t)) = eval_poly (h :: t))``,
   !! GEN_TAC
   ++ Q.SPEC_TAC (`h`, `h`)
   ++ Q.SPEC_TAC (`t`, `t`)
   ++ FUN_EQ_TAC
   ++ Induct >> R_TAC [BUTLAST_CONS, LAST_CONS, eval_poly_def]
   ++ R_TAC [BUTLAST_CONS, LAST_CONS, eval_poly_def]);

val MOD_POLY_1_ROOT = store_thm
  ("MOD_POLY_1_ROOT",
   ``!p a x.
       a < p ==>
       ((eval_poly [p - a; 1] x MOD p = 0) = (x MOD p = a))``,
   S_TAC
   ++ R_TAC [eval_poly_def]
   ++ Suff `((a + (p - a + x)) MOD p = a MOD p) = (x MOD p = a)`
   >> R_TAC [MOD_ADD_CANCEL]
   ++ R_TAC [ADD_ASSOC]);

val EVAL_MOD_EQ = store_thm
  ("EVAL_MOD_EQ",
   ``!f p a b.
       0 < p /\ (a MOD p = b MOD p) ==>
       (eval_poly f a MOD p = eval_poly f b MOD p)``,
   S_TAC
   ++ Induct_on `f` >> R_TAC [eval_poly_def]
   ++ R_TAC [eval_poly_def]);

val FACTOR_POLY_LENGTH = store_thm
  ("FACTOR_POLY_LENGTH",
   ``!h t a. LENGTH (factor_poly (h :: t) a) = LENGTH (h :: t)``,
   S_TAC
   ++ Q.SPEC_TAC (`h`, `h`)
   ++ Induct_on `t` >> R_TAC [factor_poly_def, LENGTH]
   ++ R_TAC [factor_poly_def, LENGTH, LET_DEF]);

val FACTOR_POLY_EQ_NIL = store_thm
  ("FACTOR_POLY_EQ_NIL",
   ``!h t a. ~(factor_poly (h :: t) a = [])``,
   S_TAC
   ++ Suff `~(LENGTH (factor_poly (h :: t) a) = LENGTH ([] : num list))`
   >> PROVE_TAC []
   ++ R_TAC [FACTOR_POLY_LENGTH]
   ++ R_TAC [LENGTH]);

val FACTOR_POLY_LAST = store_thm
  ("FACTOR_POLY_LAST",
   ``!h t a. LAST (factor_poly (h :: t) a) = 0``,
   S_TAC
   ++ Q.SPEC_TAC (`h`, `h`)
   ++ Induct_on `t` >> R_TAC [factor_poly_def, LAST_CONS]
   ++ R_TAC [factor_poly_def, LAST_CONS, LET_DEF]
   ++ S_TAC
   ++ POP_ASSUM (MP_TAC o Q.SPEC `h`)
   ++ Cases_on `factor_poly (h :: t) a`
   >> (Suff `~(LENGTH (factor_poly (h :: t) a) = LENGTH ([]:num list))`
       >> PROVE_TAC []
       ++ R_TAC [FACTOR_POLY_LENGTH, LENGTH])
   ++ R_TAC [LAST_CONS]);

val FACTOR_POLY_HD = store_thm
  ("FACTOR_POLY_HD",
   ``!h t a. HD (factor_poly (h :: t) a) = eval_poly t a``,
   S_TAC
   ++ Q.SPEC_TAC (`h`, `h`)
   ++ Induct_on `t` >> R_TAC [eval_poly_def, factor_poly_def]
   ++ R_TAC [eval_poly_def, factor_poly_def]
   ++ S_TAC
   ++ R_TAC [LET_DEF]);

val FACTOR_POLY = store_thm
  ("FACTOR_POLY",
   ``!f a x.
       ~(f = []) /\ a < x ==>
       (((x - a) * eval_poly (factor_poly f a) x + eval_poly f a) =
        eval_poly f x)``,
   S_TAC
   ++ Induct_on `f` >> R_TAC []
   ++ Cases_on `f` >> AR_TAC [eval_poly_def, factor_poly_def]
   ++ AR_TAC [factor_poly_def, LET_DEF, FACTOR_POLY_HD]
   ++ S_TAC
   ++ ONCE_REWRITE_TAC [eval_poly_def]
   ++ Know `!x y z : num. x + (y + z) = y + (x + z)` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC []
   ++ Know `h + a * eval_poly t a = eval_poly (h :: t) a`
   >> R_TAC [eval_poly_def]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [LEFT_ADD_DISTRIB]
   ++ Know `!x y z : num. x + y + z = (x + z) + y` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM RIGHT_ADD_DISTRIB]
   ++ Know `!x y z : num. x * (y * z) = y * (x * z)`
   >> PROVE_TAC [MULT_COMM, MULT_ASSOC]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM LEFT_ADD_DISTRIB]
   ++ PROVE_TAC [ADD_COMM]);

val FACTOR_MOD_POLY = store_thm
  ("FACTOR_MOD_POLY",
   ``!p f a.
       a < p /\ ~(f = []) ==>
       ((eval_poly f a MOD p = 0) =
        ?g.
          LENGTH g < LENGTH f /\
          !x.
            (eval_poly [p - a; 1] x * eval_poly g x) MOD p =
            eval_poly f x MOD p)``,
   S_TAC
   ++ REVERSE EQ_TAC
   >> (S_TAC
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
       ++ R_TAC [eval_poly_def])
   ++ S_TAC
   ++ R_TAC [eval_poly_def]
   ++ Q.EXISTS_TAC `BUTLAST (factor_poly f a)`
   ++ Cases_on `f` >> AR_TAC []
   ++ S_TAC
   >> (Cases_on `factor_poly (h :: t) a`
       >> (Suff `~(LENGTH (factor_poly (h :: t) a) = LENGTH ([]:num list))`
           >> PROVE_TAC []
           ++ R_TAC [FACTOR_POLY_LENGTH, LENGTH])
       ++ R_TAC [LENGTH_BUTLAST]
       ++ POP_ASSUM (fn th => R_TAC [FACTOR_POLY_LENGTH, SYM th])
       ++ R_TAC [LENGTH]
       ++ DECIDE_TAC)
   ++ Cases_on `factor_poly (h :: t) a` >> AR_TAC [FACTOR_POLY_EQ_NIL]
   ++ Know `LAST (h' :: t') = 0` >> PROVE_TAC [FACTOR_POLY_LAST]
   ++ R_TAC [EVAL_POLY_BUTLAST]
   ++ DISCH_THEN K_TAC
   ++ Know `p - a + x = (x + p) - a` >> DECIDE_TAC
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know
      `eval_poly (h' :: t') x MOD p = eval_poly (h' :: t') (x + p) MOD p`
   >> (MATCH_MP_TAC EVAL_MOD_EQ
       ++ R_TAC [])
   ++ DISCH_THEN (R_TAC o wrap)
   ++ Know
      `!x y. (x * y) MOD p = (x * y + eval_poly (h :: t) a) MOD p` >> R_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
   ++ Know `a < x + p` >> DECIDE_TAC
   ++ S_TAC
   ++ Q.PAT_X_ASSUM `_ = _` K_TAC
   ++ R_TAC [FACTOR_POLY]
   ++ MATCH_MP_TAC EVAL_MOD_EQ
   ++ R_TAC []);

val MOD_POLY_ROOTS = store_thm
  ("MOD_POLY_ROOTS",
   ``!p f.
       prime p /\ ~(!x. eval_poly f x MOD p = 0) ==>
       CARD (\x. x < p /\ (eval_poly f x MOD p = 0)) < LENGTH f``,
   S_TAC
   ++ completeInduct_on `LENGTH f`
   ++ STRIP_TAC
   ++ Cases_on `f = []` >> R_TAC [eval_poly_def]
   ++ DISCH_THEN (AR_TAC o wrap)
   ++ S_TAC
   ++ Cases_on `(\x. x < p /\ (eval_poly f x MOD p = 0)) = {}`
   >> R_TAC []
   ++ POP_ASSUM MP_TAC
   ++ R_TAC [GSYM MEMBER_NOT_EMPTY, SPECIFICATION]
   ++ S_TAC
   ++ POP_ASSUM MP_TAC
   ++ MP_TAC (Q.SPECL [`p`, `f`, `x'`] FACTOR_MOD_POLY)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ S_TAC
   ++ Know `~(eval_poly g x MOD p = 0)`
   >> (S_TAC
       ++ Q.PAT_X_ASSUM `!x. P x = Q x` (MP_TAC o Q.SPEC `x`)
       ++ R_TAC [])
   ++ S_TAC
   ++ Q.PAT_X_ASSUM `!m. P m ==> Q m` (MP_TAC o Q.SPEC `LENGTH (g : num list)`)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPEC `g`)
   ++ REWRITE_TAC []
   ++ CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
   ++ DISCH_THEN (MP_TAC o Q.SPEC `x`)
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM K_TAC
   ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
   ++ R_TAC [MOD_PRIME_INTEGRAL]
   ++ REWRITE_TAC [LEFT_AND_OVER_OR]
   ++ RW_TAC std_ss [GSYM UNION_DEF_ALT]
   ++ R_TAC [MOD_POLY_1_ROOT]
   ++ Know `(\x. x = x') = {x'}`
   >> (SET_EQ_TAC
       ++ R_TAC []
       ++ R_TAC [SPECIFICATION])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [GSYM INSERT_SING_UNION]
   ++ Know `FINITE (\x. x < p /\ (eval_poly g x MOD p = 0))`
   >> (R_TAC [GSYM INTER_DEF_ALT]
       ++ MATCH_MP_TAC FINITE_INTER_DISJ
       ++ DISJ1_TAC
       ++ KILL_TAC
       ++ Induct_on `p` >> R_TAC [GSYM EMPTY_DEF]
       ++ Know `!x. x < SUC p = (x = p) \/ x < p` >> DECIDE_TAC
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ R_TAC [GSYM UNION_DEF_ALT]
       ++ KILL_TAC
       ++ Know `(\x. x = p) = {p}`
       >> (SET_EQ_TAC
           ++ R_TAC [IN_SING]
           ++ R_TAC [SPECIFICATION])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ R_TAC [FINITE_SING])
   ++ S_TAC
   ++ R_TAC [CARD_INSERT]
   ++ POP_ASSUM K_TAC
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`(\x. x < p /\ (eval_poly g x MOD p = 0))`, `a`)
   ++ STRIP_TAC
   ++ Q.SPEC_TAC (`CARD a`, `b`)
   ++ STRIP_TAC
   ++ Cases_on `x' IN a`
   ++ RW_TAC arith_ss []);

val NTH_ROOT_MOD_POLY = store_thm
  ("NTH_ROOT_MOD_POLY",
   ``!p n.
       prime p ==>
       ?f.
         (LENGTH f <= SUC n) /\
         !x. ((x EXP n) MOD p = 1) = (eval_poly f x MOD p = 0)``,
   S_TAC
   ++ Know `!x. (x MOD p = 0) = ((1 + x) MOD p = 1 MOD p)`
   >> (S_TAC
       ++ R_TAC [MOD_ADD_CANCEL])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `1 MOD p = 1` >> R_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Cases_on `n`
   >> (Q.EXISTS_TAC `[]`
       ++ R_TAC [eval_poly_def, LENGTH])
   ++ Q.SPEC_TAC (`n'`, `n`)
   ++ STRIP_TAC
   ++ Q.EXISTS_TAC `(p - 1) :: (APPEND (FUNPOW (CONS 0) n []) [1]) : num list`
   ++ STRIP_TAC
   >> (R_TAC [LENGTH]
       ++ Induct_on `n` >> R_TAC [LENGTH, APPEND, FUNPOW]
       ++ R_TAC [LENGTH, APPEND, FUNPOW_SUC])
   ++ STRIP_TAC
   ++ Know `!x y : num. (x = y) ==> ((x = 1) = (y = 1))` >> PROVE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ RW_TAC std_ss [eval_poly_def, ADD_ASSOC]
   ++ R_TAC []
   ++ Know `x * eval_poly (APPEND (FUNPOW (CONS 0) n []) [1]) x =
                eval_poly (APPEND (FUNPOW (CONS 0) (SUC n) []) [1]) x`
   >> RW_TAC arith_ss [eval_poly_def, FUNPOW_SUC, APPEND]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Q.SPEC_TAC (`SUC n`, `n`)
   ++ Induct >> RW_TAC arith_ss [EXP, eval_poly_def, APPEND, FUNPOW]
   ++ RW_TAC arith_ss [EXP, eval_poly_def, APPEND, FUNPOW_SUC]
   ++ POP_ASSUM (fn th => R_TAC [GSYM th]));

val MOD_POLY_NTH_ROOTS = store_thm
  ("MOD_POLY_NTH_ROOTS",
   ``!p n.
       0 < n /\ prime p ==>
       CARD (\x. x < p /\ ((x EXP n) MOD p = 1)) <= n``,
   S_TAC
   ++ MP_TAC (Q.SPECL [`p`, `n`] NTH_ROOT_MOD_POLY)
   ++ R_TAC []
   ++ S_TAC
   ++ Know `?x. ~(eval_poly f x MOD p = 0)`
   >> (Q.EXISTS_TAC `0`
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
       ++ R_TAC [])
   ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap)
   ++ DISCH_TAC
   ++ MP_TAC (Q.SPECL [`p`, `f`] MOD_POLY_ROOTS)
   ++ R_TAC []
   ++ DECIDE_TAC);

(* non-interactive mode
*)
val _ = export_theory ();
