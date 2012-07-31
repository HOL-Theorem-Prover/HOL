(*---------------------------------------------------------------------------*)
(* Constant zero function.                                                   *)
(*---------------------------------------------------------------------------*)

set_trace "Unicode" 0;
set_trace "pp_annotations" 0;

use (HOLDIR^"/src/pfl/defchoose");
use (HOLDIR^"/src/pfl/tactics.sml");

quietdec := true;
open arithmeticTheory optionTheory;
quietdec := false;

(*---------------------------------------------------------------------------*)
(* General purpose support.                                                  *)
(*---------------------------------------------------------------------------*)

val MAX_LE_THM = Q.prove
(`!m n. m <= MAX m n /\ n <= MAX m n`,
 RW_TAC arith_ss [MAX_DEF]);

val IS_SOME_EXISTS = Q.prove
(`!x. IS_SOME x = ?y. x = SOME y`,
 Cases THEN METIS_TAC [optionTheory.IS_SOME_DEF]);

(*---------------------------------------------------------------------------*)
(* Indexed function definition                                               *)
(*---------------------------------------------------------------------------*)

val izero_def =
 Define
  `izero d x =
    if d=0 then NONE else
    if x=0 then SOME 0
     else case izero (d-1) (x-1)
           of NONE -> NONE
           || SOME n -> izero (d-1) n`;

(*---------------------------------------------------------------------------*)
(* Domain of the function.                                                   *)
(*---------------------------------------------------------------------------*)

val dom_def = Define `dom x = ?d. IS_SOME(izero d x)`;

(*---------------------------------------------------------------------------*)
(* Measure on recursion depth.                                               *)
(*---------------------------------------------------------------------------*)

val rdepth_thm =
 MINCHOOSE ("rdepth_thm", "rdepth",
            ``!x. ?d. IS_SOME (izero d x)``);

(*---------------------------------------------------------------------------*)
(* Define zero                                                               *)
(*---------------------------------------------------------------------------*)

val zero_0_def = Define `zero_0 x = THE (izero (rdepth x) x)`;

(*---------------------------------------------------------------------------*)
(* Lemmas about izero and definedness                                        *)
(*---------------------------------------------------------------------------*)

val IS_SOME_IZERO = Q.prove
(`!d n. IS_SOME (izero d n) ==> d <> 0`,
 Cases THEN RW_TAC std_ss [Once izero_def]);

val IZERO_SOME = Q.prove
(`!d n a. (izero d n = SOME a) ==> d <> 0`,
 Cases THEN RW_TAC std_ss [Once izero_def]);

val izero_dlem = Q.prove
(`!d n. IS_SOME (izero d n) ==> (izero d n = izero (SUC d) n)`,
 DLEM_TAC izero_def IZERO_SOME);

val izero_monotone = Q.prove
(`!d1 d2 n. IS_SOME(izero d1 n) /\ d1 <= d2 ==> (izero d1 n = izero d2 n)`,
 RW_TAC arith_ss [LESS_EQ_EXISTS] THEN
 Induct_on `p` THEN METIS_TAC [ADD_CLAUSES,izero_dlem]);

val izero_norm = Q.prove
(`!d n. IS_SOME(izero d n) ==> (izero d n = izero (rdepth n) n)`,
 METIS_TAC [izero_monotone,rdepth_thm]);

val izero_determ = Q.prove
(`!d1 d2 n. IS_SOME(izero d1 n) /\ IS_SOME(izero d2 n)
            ==> (izero d1 n = izero d2 n)`,
 METIS_TAC [izero_norm]);

(*---------------------------------------------------------------------------*)
(* Recursion equations for zero                                              *)
(*---------------------------------------------------------------------------*)

val zero_base = Q.prove
(`!n. dom n /\ (n=0) ==> (zero_0 n = 0)`,
 RW_TAC std_ss [zero_0_def,dom_def] THEN
 `rdepth 0 <> 0` by METIS_TAC [IS_SOME_IZERO,rdepth_thm] THEN
 RW_TAC arith_ss [Once izero_def]);

val zero_step = Q.prove
(`!n. dom n /\ n<>0 ==> (zero_0 n = zero_0 (zero_0 (n-1)))`,
 RW_TAC std_ss [zero_0_def,dom_def] THEN
 `d <> 0` by METIS_TAC [IS_SOME_IZERO] THEN
 `izero d n = case izero (d-1) (n-1) of
                NONE -> NONE
             || SOME v -> izero (d - 1) v` by METIS_TAC [izero_def] THEN
 POP_ASSUM MP_TAC THEN CASE_TAC THEN
 METIS_TAC [IS_SOME_EXISTS,NOT_SOME_NONE,THE_DEF,izero_norm]);

(*---------------------------------------------------------------------------*)
(* Equational characterization of zero.                                       *)
(*---------------------------------------------------------------------------*)

val zero_0_eqns = Q.prove
(`!n. dom n ==> (zero_0 n = if n=0 then 0 else zero_0(zero_0(n-1)))`,
 METIS_TAC [zero_base, zero_step]);

(*---------------------------------------------------------------------------*)
(* Now derive eqns for dom                                                   *)
(*---------------------------------------------------------------------------*)

val lem = Q.prove
(`IS_SOME (izero 1 0)`,
 RW_TAC arith_ss [Once izero_def]);

val dom_base_case = Q.prove
(`dom 0`,
 METIS_TAC [dom_def, lem]);

val step2_lem1a = Q.prove
(`!n. n<>0 /\ dom n ==> dom (n-1)`,
 RW_TAC std_ss [dom_def] THEN
 `d<>0` by METIS_TAC [IS_SOME_IZERO] THEN
 Q.EXISTS_TAC `d-1` THEN
 Q.PAT_ASSUM `IS_SOME arg` (MP_TAC o ONCE_REWRITE_RULE [izero_def]) THEN
 CASE_TAC THEN RW_TAC arith_ss []);

val step2_lem1b = Q.prove
(`!n. n<>0 /\ dom n ==> dom (zero_0(n-1))`,
 RW_TAC std_ss [dom_def,zero_0_def] THEN
 `d<>0` by METIS_TAC [IS_SOME_IZERO] THEN
 Q.EXISTS_TAC `d-1` THEN
 Q.PAT_ASSUM `IS_SOME arg` (MP_TAC o ONCE_REWRITE_RULE [izero_def]) THEN
 CASE_TAC THEN RW_TAC arith_ss [] THEN
 METIS_TAC [izero_norm,IS_SOME_EXISTS,THE_DEF]);

val step2_lem2 = Q.prove
(`!n. n<>0 /\ dom (n-1) /\ dom (zero_0(n-1)) ==> dom n`,
 RW_TAC std_ss [dom_def,zero_0_def] THEN
 Q.EXISTS_TAC `SUC (MAX d d')` THEN
 RW_TAC arith_ss [Once izero_def] THEN
 CASE_TAC THENL
 [METIS_TAC [izero_monotone,MAX_LE_THM,NOT_SOME_NONE],
  METIS_TAC [izero_monotone,IS_SOME_EXISTS,MAX_LE_THM,izero_norm,THE_DEF]]);

(*---------------------------------------------------------------------------*)
(* Equational characterization of dom.                                       *)
(*---------------------------------------------------------------------------*)

val dom_eqns = Q.prove
(`dom n =
    if n=0 then T
    else dom (n-1) /\ dom (zero_0 (n-1))`,
 METIS_TAC [dom_base_case, step2_lem1a,step2_lem1b,step2_lem2]);

(*---------------------------------------------------------------------------*)
(* Now prove induction theorem. This is based on using rdepth as a measure   *)
(* on the recursion. Thus we first have some lemmas about how rdepth         *)
(* decreases in recursive calls.                                             *)
(*---------------------------------------------------------------------------*)

val inner_lt = Q.prove
(`!n. dom n /\ n<>0 ==> rdepth (n-1) < rdepth n`,
 RW_TAC std_ss [dom_def] THEN IMP_RES_TAC rdepth_thm THEN
   `rdepth n <> 0` by METIS_TAC [IS_SOME_IZERO] THEN
   `rdepth n - 1 < rdepth n` by DECIDE_TAC THEN
   `IS_SOME (izero (rdepth n - 1) (n-1))`
     by (Q.PAT_ASSUM `IS_SOME (izero (rdepth n) n)` MP_TAC THEN
         SIMP_TAC arith_ss [Once izero_def] THEN CASE_TAC THEN
         SIMP_TAC std_ss [IS_SOME_DEF]) THEN
   `rdepth (n-1) <= rdepth n - 1` by METIS_TAC [rdepth_thm] THEN
 DECIDE_TAC);

val outer_lt = Q.prove
(`!n. dom n /\ n<>0 ==> rdepth (zero_0 (n-1)) < rdepth n`,
 RW_TAC std_ss [dom_def] THEN IMP_RES_TAC rdepth_thm THEN
   `rdepth n <> 0` by METIS_TAC [IS_SOME_IZERO] THEN
   `rdepth n - 1 < rdepth n` by DECIDE_TAC THEN
   `IS_SOME (izero (rdepth n - 1) (zero_0 (n-1)))`
     by (Q.PAT_ASSUM `IS_SOME (izero (rdepth n) n)` MP_TAC THEN
         SIMP_TAC arith_ss [Once izero_def] THEN CASE_TAC THEN
         RW_TAC std_ss [zero_0_def] THEN
        `IS_SOME (izero (rdepth n - 1) (n-1))` by METIS_TAC [IS_SOME_EXISTS] THEN
        `IS_SOME (izero (rdepth (n-1)) (n-1))` by METIS_TAC [rdepth_thm] THEN
        METIS_TAC [izero_determ,THE_DEF]) THEN
   `rdepth (zero_0(n-1)) <= rdepth n - 1` by METIS_TAC [rdepth_thm] THEN
 DECIDE_TAC);

(*---------------------------------------------------------------------------*)
(* Induction for f91 is obtained by instantiating the well-founded induction *)
(* theorem with the rdepth measure and then simplifying.                     *)
(*---------------------------------------------------------------------------*)

val ind0 = MATCH_MP relationTheory.WF_INDUCTION_THM
                    (Q.ISPEC `rdepth` prim_recTheory.WF_measure);
val ind1 = SIMP_RULE std_ss [prim_recTheory.measure_thm] ind0;
val ind2 = SIMP_RULE std_ss [pairTheory.FORALL_PROD]
                    (Q.ISPEC `\n. dom n ==> P n` ind1);

val zero_0_ind = Q.prove
(`!P.
   (!n. dom n /\
          (n<>0 ==> P (n-1))  /\
          (n<>0 ==> P (zero_0 (n-1)))
         ==> P n)
  ==> !n. dom n ==> P n`,
 GEN_TAC THEN DISCH_TAC THEN HO_MATCH_MP_TAC ind2 THEN
 POP_ASSUM (fn th => REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
 RULE_ASSUM_TAC (REWRITE_RULE [AND_IMP_INTRO]) THEN
 METIS_TAC [inner_lt,outer_lt,dom_eqns]);

(*---------------------------------------------------------------------------*)
(* Trivial examples                                                          *)
(*---------------------------------------------------------------------------*)

val closed_form = Q.prove
(`!n. dom n ==> (zero_0 n = 0)`,
 HO_MATCH_MP_TAC zero_0_ind THEN
   REPEAT STRIP_TAC THEN
   RW_TAC arith_ss [Once zero_0_eqns]);

(*---------------------------------------------------------------------------*)
(* Termination                                                               *)
(*---------------------------------------------------------------------------*)

val zero_total = Q.prove
(`!n. dom n`,
  Induct THEN
    RW_TAC arith_ss [Once dom_eqns] THEN
    METIS_TAC [closed_form,dom_eqns]);

(*---------------------------------------------------------------------------*)
(* Efficient executable version of zero                                      *)
(*---------------------------------------------------------------------------*)

val exec_def =
 Define
 `exec d n =
    if d=0 then (if dom n then zero_0 n else ARB) else
    if n=0 then 0
       else exec (d-1) (exec (d-1) (n-1))`;

val exec_equals_zero_0 = Q.prove
(`!d n. dom n ==> (exec d n = zero_0 n)`,
 Induct THEN RW_TAC std_ss [Once exec_def]
 THEN METIS_TAC [zero_0_eqns,dom_eqns]);

val BIG_def = Define `BIG = 1073741823`;

(*---------------------------------------------------------------------------*)
(* Final version                                                             *)
(*---------------------------------------------------------------------------*)

val zero_def =
 Define
   `zero n = if dom n then zero_0 n else exec BIG n`;

(*---------------------------------------------------------------------------*)
(* Theorem showing that exec BIG = zero in the domain of the function.       *)
(*---------------------------------------------------------------------------*)

val zero_exec = Q.prove
(`zero n = exec BIG n`,
 RW_TAC std_ss [zero_def,exec_equals_zero_0]);

val zero_dom_eqns = Q.prove
(`dom n <=> if n=0 then T else dom (n-1) /\ dom (zero(n-1))`,
 METIS_TAC [dom_eqns,zero_def]);

val zero_eqns = Q.prove
(`dom n ==>
   (zero n = if n=0 then 0 else zero (zero (n-1)))`,
 RW_TAC std_ss [zero_def] THEN METIS_TAC [zero_0_eqns,dom_eqns]);

val zero_ind = Q.prove
(`!P.
   (!n. dom n /\
          (n<>0 ==> P (n-1))  /\
          (n<>0 ==> P (zero (n-1)))
         ==> P n)
  ==> !n. dom n ==> P n`,
 GEN_TAC THEN STRIP_TAC THEN HO_MATCH_MP_TAC zero_0_ind THEN
 POP_ASSUM (fn th => REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
 RW_TAC std_ss [zero_def] THEN METIS_TAC [zero_dom_eqns]);
