open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["xprop_logicTheory", "prop_logicTheory", "infinite_pathTheory", "pred_setTheory", "listTheory", "pairTheory", "set_lemmataTheory",
   "containerTheory", "prim_recTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory", "arithmeticTheory", "numLib"];
*)

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
     containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
     tuerk_tacticsLib temporal_deep_mixedTheory arithmeticTheory numLib;
open Sanity;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val _ = new_theory "alternating_omega_automata";


(*****************************************************************************)
(* symbolic representation of alternating automata                 *)
(*****************************************************************************)
val alternating_acceptance_condition_def =
Hol_datatype
`alternating_acceptance_condition =
    TRUE |
    FALSE |
    INITIAL of 'state set |
    CO_INITIAL of 'state set |
    BUECHI of 'state set |
    CO_BUECHI of 'state set |
    PARITY of 'state->num |
    WEAK_PARITY of 'state->num |
    WEAK_BUECHI of 'state set |
    WEAK_CO_BUECHI of 'state set`;

val alternating_semi_automaton_def =
Hol_datatype
`alternating_semi_automaton =
    <| S:   'state set;                        (*set of all used statevariables *)
        I: 'input set;
        S0: 'state prop_logic;              (*initial condition*)
        R:   'state -> 'input -> 'state prop_logic (*transition function*)
    |>`;

val alternating_automaton_def =
Hol_datatype
`alternating_automaton =
    <| A: ('input, 'state) alternating_semi_automaton;
        AC: 'state alternating_acceptance_condition (*acceptance condition*)
    |>`;

val alternating_run_def =
Hol_datatype
`alternating_run =
    <| S0:   'state set;                          (*choosen initial states*)
         R:   'state -> num -> 'state set (*choosen transitions*)
    |>`;

Theorem alternating_automaton_REWRITES =
      LIST_CONJ (List.concat
                 [TypeBase.accessors_of “:(α,β)alternating_semi_automaton”,
                  TypeBase.accessors_of “:(α,β)alternating_automaton”,
                  TypeBase.accessors_of “:α alternating_run”])

val std_ss = std_ss ++
             rewrites (TypeBase.accessors_of “:α alternating_run” @
                       TypeBase.accessors_of “:(α,β)alternating_automaton” @
                       TypeBase.accessors_of “:(α,β)alternating_semi_automaton”)
(*============================================================
= Semantic
============================================================*)

val IS_REACHABLE_BY_RUN_def =
Define
`(IS_REACHABLE_BY_RUN (s, 0) r = (s IN r.S0)) /\
  (IS_REACHABLE_BY_RUN (s,  SUC n) r = (
    ?s'. IS_REACHABLE_BY_RUN (s', n) r /\ (s IN r.R s' n)))`;

val ALTERNATING_RUN_def =
Define
`ALTERNATING_RUN (A:('input, 'state) alternating_semi_automaton)
            (i:(num -> 'input))
            (r:'state alternating_run) = (
                (r.S0 SUBSET A.S) /\ (P_SEM (r.S0) A.S0) /\
                (!n s. (r.R s n SUBSET A.S)) /\
                (!n s.
                (IS_REACHABLE_BY_RUN (s, n) r) ==>
                (P_SEM (r.R s n) (A.R s (i n)))))`;

val IS_PATH_THROUGH_RUN_def =
Define
`IS_PATH_THROUGH_RUN w r = ((w 0 IN r.S0) /\ !n.
         ((w (SUC n)) IN r.R (w n) n))`;


val ALT_ACCEPT_COND_SEM_def =
Define
`(ALT_ACCEPT_COND_SEM TRUE i = T) /\
    (ALT_ACCEPT_COND_SEM FALSE i = F) /\
    (ALT_ACCEPT_COND_SEM (INITIAL S) i = (i 0 IN S)) /\
    (ALT_ACCEPT_COND_SEM (CO_INITIAL S) i = ~(i 0 IN S)) /\
    (ALT_ACCEPT_COND_SEM (BUECHI S) i =
        (~(((INF_ELEMENTS_OF_PATH i) INTER S) = EMPTY))) /\
    (ALT_ACCEPT_COND_SEM (PARITY f) i =
        (?n. EVEN n /\ (?s. (s IN (INF_ELEMENTS_OF_PATH i)) /\ (n = (f s))) /\
                              (!s. (s IN (INF_ELEMENTS_OF_PATH i)) ==> (n <= (f s))))) /\
    (ALT_ACCEPT_COND_SEM (WEAK_PARITY f) i =
        (?n. EVEN n /\ (?s. (s IN (ELEMENTS_OF_PATH i)) /\ (n = (f s))) /\
                              (!s. (s IN (ELEMENTS_OF_PATH i)) ==> (n <= (f s))))) /\
    (ALT_ACCEPT_COND_SEM (CO_BUECHI S) i =
        (((INF_ELEMENTS_OF_PATH i) INTER S) = EMPTY)) /\
    (ALT_ACCEPT_COND_SEM (WEAK_BUECHI S) i =
        (~(((ELEMENTS_OF_PATH i) INTER S) = EMPTY))) /\
    (ALT_ACCEPT_COND_SEM (WEAK_CO_BUECHI S) i =
        (((ELEMENTS_OF_PATH i) INTER S) = EMPTY))`;


val ALT_SEM_def =
Define
`ALT_SEM A i = ((!n. i n IN A.A.I) /\
        ?r. ALTERNATING_RUN A.A i r /\ (!w. IS_PATH_THROUGH_RUN w r ==> ALT_ACCEPT_COND_SEM A.AC w))`;


val ALT_AUTOMATON_EQUIV_def =
Define
`ALT_AUTOMATON_EQUIV A A' =
        (!i. ALT_SEM A i = ALT_SEM A' i)`;

(*============================================================
= Lemmata and Definitions about Acceptance Component
============================================================*)

val ALT_ACCEPT_COND_SEM_THM_1 =
    prove (
        ``!S i. ALT_ACCEPT_COND_SEM (BUECHI S) i = (?s. s IN S /\ (!n. ?m. m > n /\ (i m = s)))``,

    SIMP_TAC arith_ss [ALT_ACCEPT_COND_SEM_def, INF_ELEMENTS_OF_PATH_def,
        INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION] THEN
    PROVE_TAC[]);

val ALT_ACCEPT_COND_SEM_THM_2 =
    prove (``!S i. ALT_ACCEPT_COND_SEM (WEAK_BUECHI S) i = (?n. i n IN S)``,

    SIMP_TAC arith_ss [ALT_ACCEPT_COND_SEM_def, ELEMENTS_OF_PATH_def,
        INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION] THEN
    PROVE_TAC[]);

val ALT_ACCEPT_COND_SEM_THM_3 =
    prove (
        ``!S i. (ALT_ACCEPT_COND_SEM (CO_BUECHI S) i =
                 ~ALT_ACCEPT_COND_SEM (BUECHI S) i) /\
                (ALT_ACCEPT_COND_SEM (WEAK_CO_BUECHI S) i =
                 ~ALT_ACCEPT_COND_SEM (WEAK_BUECHI S) i) /\
                (ALT_ACCEPT_COND_SEM (CO_INITIAL S) i =
                 ~ALT_ACCEPT_COND_SEM (INITIAL S) i)``,

    SIMP_TAC arith_ss [ALT_ACCEPT_COND_SEM_def]);


val ALT_ACCEPT_COND_SEM_THM = LIST_CONJ [
                             ALT_ACCEPT_COND_SEM_THM_1,
                             ALT_ACCEPT_COND_SEM_THM_2,
                             ALT_ACCEPT_COND_SEM_THM_3];
val _ = save_thm("ALT_ACCEPT_COND_SEM_THM",ALT_ACCEPT_COND_SEM_THM);


val ALT_ACCEPT_COND_NEG_def =
Define
`(ALT_ACCEPT_COND_NEG TRUE = FALSE) /\
  (ALT_ACCEPT_COND_NEG FALSE = TRUE) /\
  (ALT_ACCEPT_COND_NEG (INITIAL S) = (CO_INITIAL S)) /\
  (ALT_ACCEPT_COND_NEG (CO_INITIAL S) = (INITIAL S)) /\
  (ALT_ACCEPT_COND_NEG (BUECHI S) = (CO_BUECHI S)) /\
  (ALT_ACCEPT_COND_NEG (CO_BUECHI S) = (BUECHI S)) /\
  (ALT_ACCEPT_COND_NEG (WEAK_BUECHI S) = (WEAK_CO_BUECHI S)) /\
  (ALT_ACCEPT_COND_NEG (WEAK_CO_BUECHI S) = (WEAK_BUECHI S)) /\
  (ALT_ACCEPT_COND_NEG (PARITY f) = (PARITY (\n. SUC(f n)))) /\
  (ALT_ACCEPT_COND_NEG (WEAK_PARITY f) = (WEAK_PARITY (\n. SUC(f n))))`;


val ALT_ACCEPT_COND_NEG_SEM =
 store_thm
  ("ALT_ACCEPT_COND_NEG_SEM",
    ``!a i. ((?f. a = PARITY f) ==> ~(INF_ELEMENTS_OF_PATH i = EMPTY)) ==> (ALT_ACCEPT_COND_SEM (ALT_ACCEPT_COND_NEG a) i = ~ALT_ACCEPT_COND_SEM a i)``,

    REPEAT STRIP_TAC THEN
    Cases_on `a` THEN
    REWRITE_TAC[ALT_ACCEPT_COND_NEG_def, ALT_ACCEPT_COND_SEM_def] THENL [
        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC arith_ss [] THEN
            `f s' <= f s` by PROVE_TAC[] THEN
            `SUC (f s) <= (SUC (f s'))` by PROVE_TAC[] THEN
            `f s' = f s` by DECIDE_TAC THEN
            PROVE_TAC[EVEN],


            FULL_SIMP_TAC arith_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
                EVEN, GSYM LEFT_FORALL_OR_THM, GSYM RIGHT_FORALL_OR_THM] THEN
            `?n. (?s. s IN INF_ELEMENTS_OF_PATH i /\ (f s = n)) /\
            !n'. n' < n ==> ~?s. s IN INF_ELEMENTS_OF_PATH i /\ (f s = n')` by (
                ASSUME_TAC (EXISTS_LEAST_CONV ``?n:num. (?s:'a. s IN (INF_ELEMENTS_OF_PATH i) /\ (f s = n))``) THEN
                METIS_TAC[MEMBER_NOT_EMPTY]
            ) THEN
            `!s'. s' IN INF_ELEMENTS_OF_PATH i ==> (n <= f s')` by (
                CCONTR_TAC THEN
                FULL_SIMP_TAC std_ss [] THEN
                `f s' < n` by DECIDE_TAC THEN
                PROVE_TAC[]
            ) THEN
            METIS_TAC[]
        ],


        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC arith_ss [] THEN
            `f s' <= f s` by PROVE_TAC[] THEN
            `SUC (f s) <= (SUC (f s'))` by PROVE_TAC[] THEN
            `f s' = f s` by DECIDE_TAC THEN
            PROVE_TAC[EVEN],

            FULL_SIMP_TAC arith_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
                EVEN, GSYM LEFT_FORALL_OR_THM, GSYM RIGHT_FORALL_OR_THM] THEN
            `?n. (?s. s IN ELEMENTS_OF_PATH i /\ (f s = n)) /\
            !n'. n' < n ==> ~?s. s IN ELEMENTS_OF_PATH i /\ (f s = n')` by (
                ASSUME_TAC (EXISTS_LEAST_CONV ``?n:num. (?s:'a. s IN (ELEMENTS_OF_PATH i) /\ (f s = n))``) THEN
                METIS_TAC[MEMBER_NOT_EMPTY, ELEMENTS_OF_PATH_NOT_EMPTY]
            ) THEN
            `!s'. s' IN ELEMENTS_OF_PATH i ==> (n <= f s')` by (
                CCONTR_TAC THEN
                FULL_SIMP_TAC std_ss [] THEN
                `f s' < n` by DECIDE_TAC THEN
                PROVE_TAC[]
            ) THEN
            METIS_TAC[]
        ]
    ]);



(*============================================================
= Min Semantic
============================================================*)

val ALTERNATING_MIN_RUN_def =
Define
`ALTERNATING_MIN_RUN (A:('input, 'state) alternating_semi_automaton)
            (i:(num -> 'input))
            (r:'state alternating_run) = (
                (r.S0 SUBSET A.S) /\ (P_SEM_MIN (r.S0) A.S0) /\
                (!n s. (r.R s n SUBSET A.S)) /\
                (!n s.
                (IS_REACHABLE_BY_RUN (s, n) r) ==>
                (P_SEM_MIN (r.R s n) (A.R s (i n)))))`;


val ALT_SEM_MIN_def =
Define
`ALT_SEM_MIN A i = ((!n. i n IN A.A.I) /\
        ?r. ALTERNATING_MIN_RUN A.A i r /\ (!w. IS_PATH_THROUGH_RUN w r ==> ALT_ACCEPT_COND_SEM A.AC w))`;


val IS_ALTERNATING_SUBRUN_def =
Define
`IS_ALTERNATING_SUBRUN r r' =
    (r.S0 SUBSET r'.S0 /\ !s n. (r.R s n SUBSET r'.R s n))`;


val IS_PATH_THROUGH_SUBRUN_THM =
 store_thm
  ("IS_PATH_THROUGH_SUBRUN_THM",
    ``!w r r'. (IS_ALTERNATING_SUBRUN r' r /\ IS_PATH_THROUGH_RUN w r') ==>
    IS_PATH_THROUGH_RUN w r``,

    SIMP_TAC std_ss [IS_ALTERNATING_SUBRUN_def, IS_PATH_THROUGH_RUN_def] THEN
    PROVE_TAC[SUBSET_DEF]);


val SUBRUN_REACHABLE_STATES =
 store_thm
  ("SUBRUN_REACHABLE_STATES",
    ``!r r'. (IS_ALTERNATING_SUBRUN r r') ==>
    (!s n. (IS_REACHABLE_BY_RUN (s, n) r ==>
    IS_REACHABLE_BY_RUN (s, n) r'))``,

    REWRITE_TAC[IS_ALTERNATING_SUBRUN_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    Induct_on `n` THENL [
        REWRITE_TAC[IS_REACHABLE_BY_RUN_def] THEN
        PROVE_TAC[SUBSET_DEF],

        REWRITE_TAC[IS_REACHABLE_BY_RUN_def] THEN
        PROVE_TAC[SUBSET_DEF]
    ]);


val ALTERNATING_RUN___ALTERNATING_MIN_RUN_EXISTS =
 store_thm
  ("ALTERNATING_RUN___ALTERNATING_MIN_RUN_EXISTS",
   ``!A i r. ALTERNATING_RUN A i r ==>
        (?r'. ALTERNATING_MIN_RUN A i r' /\ IS_ALTERNATING_SUBRUN r' r)``,

    FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def, ALTERNATING_MIN_RUN_def] THEN
    REPEAT STRIP_TAC THENL [
        `?r'. r' = (alternating_run (@S0'. S0' SUBSET r.S0 /\
            P_SEM_MIN S0' A.S0) (\s n. @S'. S' SUBSET r.R s n /\
               (IS_REACHABLE_BY_RUN (s, n) r ==>
                P_SEM_MIN S' (A.R s (i n)))))` by PROVE_TAC[] THEN
        EXISTS_TAC ``r':'b alternating_run`` THEN
        SUBGOAL_THEN ``IS_ALTERNATING_SUBRUN (r':'b alternating_run) r`` ASSUME_TAC THEN1 (
            ASM_SIMP_TAC (srw_ss()) [IS_ALTERNATING_SUBRUN_def] THEN
            REPEAT STRIP_TAC THENL [
                SELECT_ELIM_TAC THEN
                PROVE_TAC[P_SEM_MIN_MODEL_EXISTS],

                SELECT_ELIM_TAC THEN
                REPEAT STRIP_TAC THEN
                Cases_on `IS_REACHABLE_BY_RUN (s, n) r` THENL [
                        PROVE_TAC[P_SEM_MIN_MODEL_EXISTS],
                        PROVE_TAC[SUBSET_REFL]
                ]
            ]) THEN

        REPEAT STRIP_TAC THENL [
            PROVE_TAC[SUBSET_TRANS, IS_ALTERNATING_SUBRUN_def],

            simp[] THEN
            SELECT_ELIM_TAC THEN
            PROVE_TAC[P_SEM_MIN_MODEL_EXISTS],

            PROVE_TAC[SUBSET_TRANS, IS_ALTERNATING_SUBRUN_def],

            `IS_REACHABLE_BY_RUN (s, n) r` by PROVE_TAC[SUBRUN_REACHABLE_STATES] THEN
            RES_TAC THEN
            simp[] THEN SELECT_ELIM_TAC THEN
            REPEAT STRIP_TAC THEN
            PROVE_TAC[P_SEM_MIN_MODEL_EXISTS],

            ASM_REWRITE_TAC[]
        ]
    ]);


val ALT_SEM___ALT_SEM_MIN___EQUIV =
 store_thm
  ("ALT_SEM___ALT_SEM_MIN___EQUIV",
    ``!A i. ALT_SEM A i = ALT_SEM_MIN A i``,

    REWRITE_TAC [ALT_SEM_def, ALT_SEM_MIN_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [
        PROVE_TAC[ALTERNATING_RUN___ALTERNATING_MIN_RUN_EXISTS, IS_PATH_THROUGH_SUBRUN_THM],

        FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def, ALTERNATING_MIN_RUN_def, P_SEM_MIN_def] THEN
        METIS_TAC[]
    ]);


(*============================================================
= Negation of alternating automata
============================================================*)

val ALT_SEMI_AUTOMATON_NEG_def =
Define
    `ALT_SEMI_AUTOMATON_NEG A = alternating_semi_automaton A.S A.I (P_DUAL A.S0)
     (\s i. P_DUAL (A.R s i))`;


val ALT_AUTOMATON_NEG_def =
Define
    `ALT_AUTOMATON_NEG A = (alternating_automaton (ALT_SEMI_AUTOMATON_NEG A.A) (ALT_ACCEPT_COND_NEG A.AC))`;



val ALT_AUTOMATON_NEG_NEG_SEM =
 store_thm
  ("ALT_AUTOMATON_NEG_NEG_SEM",

    ``!A. (FINITE A.A.S) ==> (ALT_AUTOMATON_EQUIV (ALT_AUTOMATON_NEG (ALT_AUTOMATON_NEG A)) A)``,

    SIMP_TAC std_ss [ALT_AUTOMATON_EQUIV_def, ALT_SEM_def, ALT_AUTOMATON_NEG_def,
        P_DUAL_def,
        ALT_ACCEPT_COND_NEG_SEM, ALT_SEMI_AUTOMATON_NEG_def,
        alternating_automaton_REWRITES,
        ALTERNATING_RUN_def, P_SEM_MIN_def, P_SEM_THM,
        P_NEGATE_VARS_SEM, DIFF_DIFF_INTER, INTER_UNIV] THEN
    REPEAT STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    EXISTS_EQ_STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    Cases_on `IS_PATH_THROUGH_RUN w r` THEN ASM_REWRITE_TAC[] THEN
    `!n:num. (w n) IN A.A.S` by (Cases_on `n` THEN
        PROVE_TAC[SUBSET_DEF, IS_PATH_THROUGH_RUN_def]) THEN
    PROVE_TAC[INF_ELEMENTS_OF_PATH_NOT_EMPTY, ALT_ACCEPT_COND_NEG_SEM]);


val ALTERNATING_PRERUN_def =
Define
`ALTERNATING_PRERUN (A:('input, 'state) alternating_semi_automaton)
            (i:(num -> 'input))
            (r:'state alternating_run) = (
                (r.S0 SUBSET A.S) /\ ((P_SEM (r.S0) A.S0) \/ ((r.S0 = EMPTY) /\ P_IS_CONTRADICTION A.S0)) /\
                (!n s. (r.R s n SUBSET A.S)) /\
                (!n s.
                (IS_REACHABLE_BY_RUN (s, n) r) ==>
                (P_SEM (r.R s n) (A.R s (i n)) \/ ((r.R s n = EMPTY) /\ P_IS_CONTRADICTION (A.R s (i n))))))`;


val ALTERNATING_RUN_IS_PRERUN =
 store_thm
  ("ALTERNATING_RUN_IS_PRERUN",

    ``!A i r. ALTERNATING_RUN A i r ==> ALTERNATING_PRERUN A i r``,

    SIMP_TAC std_ss [ALTERNATING_RUN_def, ALTERNATING_PRERUN_def]);

(*****************************************************************************)
(* Some Classes of alternating automata                                                                                   *)
(*****************************************************************************)

val IS_NONDETERMINISTIC_SEMI_AUTOMATON_def =
Define
`IS_NONDETERMINISTIC_SEMI_AUTOMATON A =
        ((IS_PROP_DISJUNCTION A.S0) /\
        (!s i. IS_PROP_DISJUNCTION (A.R s i)))`;

val IS_UNIVERSAL_SEMI_AUTOMATON_def =
Define
`IS_UNIVERSAL_SEMI_AUTOMATON A =
        ((IS_PROP_CONJUNCTION A.S0) /\
        (!s i. IS_PROP_CONJUNCTION (A.R s i)))`;

val IS_DETERMINISTIC_SEMI_AUTOMATON_def =
Define
`IS_DETERMINISTIC_SEMI_AUTOMATON A =
        (IS_NONDETERMINISTIC_SEMI_AUTOMATON A /\
        IS_UNIVERSAL_SEMI_AUTOMATON A)`;


val IS_NONDETERMINISTIC_AUTOMATON_def =
Define
`IS_NONDETERMINISTIC_AUTOMATON A =
    IS_NONDETERMINISTIC_SEMI_AUTOMATON A.A`;

val IS_UNIVERSAL_AUTOMATON_def =
Define
`IS_UNIVERSAL_AUTOMATON A = IS_UNIVERSAL_SEMI_AUTOMATON A.A`;

val IS_DETERMINISTIC_AUTOMATON_def =
Define
`IS_DETERMINISTIC_AUTOMATON A =  IS_DETERMINISTIC_SEMI_AUTOMATON A.A`;


val IS_VALID_ALTERNATING_SEMI_AUTOMATON_def = Define
  `IS_VALID_ALTERNATING_SEMI_AUTOMATON A =
    (FINITE A.S /\ FINITE A.I /\ (P_USED_VARS A.S0 SUBSET A.S) /\
     (!s i. (P_USED_VARS (A.R s i) SUBSET A.S)) /\
     IS_POSITIVE_PROP_FORMULA A.S0 /\ (!s i. IS_POSITIVE_PROP_FORMULA (A.R s i)))`;

val IS_VALID_ACCEPTANCE_COMPONENT_def = Define
  `(IS_VALID_ACCEPTANCE_COMPONENT TRUE A = T) /\
    (IS_VALID_ACCEPTANCE_COMPONENT FALSE A = T) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (INITIAL s) A = (s SUBSET A.S)) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (CO_INITIAL s) A = (s SUBSET A.S)) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (BUECHI s) A = (s SUBSET A.S)) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (CO_BUECHI s) A = (s SUBSET A.S)) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (PARITY f) A = T) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (WEAK_PARITY f) A = T) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (WEAK_BUECHI s) A = (s SUBSET A.S)) /\
    (IS_VALID_ACCEPTANCE_COMPONENT (WEAK_CO_BUECHI s) A = (s SUBSET A.S))`;


val IS_VALID_ALTERNATING_AUTOMATON_def = Define
  `IS_VALID_ALTERNATING_AUTOMATON A =
        ((IS_VALID_ALTERNATING_SEMI_AUTOMATON A.A) /\
        (IS_VALID_ACCEPTANCE_COMPONENT A.AC A.A))`;

val IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def = Define
  `IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A =
        ((?p. P_SEM p A.S0)  /\ (!s i. ?p. P_SEM p (A.R s i)))`;


val IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def = Define
  `IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A =
        ((?p. ~P_SEM p A.S0)  /\ (!s i. ?p. ~P_SEM p (A.R s i)))`;


val IS_TOTAL_ALTERNATING_SEMI_AUTOMATON_def = Define
  `IS_TOTAL_ALTERNATING_SEMI_AUTOMATON A =
        (IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A /\
         IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A)`;

val UNIVERSAL_IS_EXISTENTIALLY_TOTAL =
 store_thm
  ("UNIVERSAL_IS_EXISTENTIALLY_TOTAL",

    ``!A. IS_UNIVERSAL_SEMI_AUTOMATON A ==> IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A``,

    REWRITE_TAC[IS_UNIVERSAL_SEMI_AUTOMATON_def,
        IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
        IS_PROP_CONJUNCTION_def] THEN
    REPEAT STRIP_TAC THENL [
        ALL_TAC,
        `?S'. A.R s i = P_PROP_CONJUNCTION S'` by PROVE_TAC[]
    ] THEN
    EXISTS_TAC ``UNIV:'b set`` THEN
    ASM_SIMP_TAC list_ss [P_PROP_CONJUNCTION_SEM, IN_UNIV]);


val NONDETERMINISTIC_IS_UNIVERSALLY_TOTAL =
 store_thm
  ("NONDETERMINISTIC_IS_UNIVERSALLY_TOTAL",

    ``!A. IS_NONDETERMINISTIC_SEMI_AUTOMATON A ==> IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A``,

    REWRITE_TAC[IS_NONDETERMINISTIC_SEMI_AUTOMATON_def,
        IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
        IS_PROP_DISJUNCTION_def] THEN
    REPEAT STRIP_TAC THENL [
        ALL_TAC,
        `?S'. A.R s i = P_PROP_DISJUNCTION S'` by PROVE_TAC[]
    ] THEN
    EXISTS_TAC ``EMPTY:'b set`` THEN
    ASM_SIMP_TAC list_ss [P_PROP_DISJUNCTION_SEM, NOT_IN_EMPTY]);


val UNIVERSAL_EXISTENTIALLY_TOTAL_DUAL =
 store_thm
  ("UNIVERSAL_EXISTENTIALLY_TOTAL_DUAL",
    ``(!A:('a, 'b) alternating_semi_automaton. IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON (ALT_SEMI_AUTOMATON_NEG A) = IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A) /\
(!A:('a, 'b) alternating_semi_automaton. IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON (ALT_SEMI_AUTOMATON_NEG A) = IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A)``,

    SIMP_TAC (srw_ss()) [IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
        IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
        ALT_SEMI_AUTOMATON_NEG_def,
        ALT_SEMI_AUTOMATON_NEG_def,
        P_DUAL_MODELS_THM, P_DUAL_def, P_NEGATE_VARS_SEM, P_SEM_THM] THEN

    `!p. (UNIV:'b set) DIFF (UNIV DIFF p) = p` by
      SIMP_TAC std_ss [EXTENSION, IN_DIFF, IN_UNIV] THEN
    METIS_TAC[]
    );



val IS_WEAK_ALTERNATING_SEMI_AUTOMATON_def =
Define
`IS_WEAK_ALTERNATING_SEMI_AUTOMATON A f =
    (!s n S s'. (P_SEM_MIN S (A.R s n) /\ (s' IN S)) ==> (f s' <= f s))`;


val NO_EMPTY_SET_IN_RUN_def =
Define
    `NO_EMPTY_SET_IN_RUN r = ((!s n. IS_REACHABLE_BY_RUN (s, n) r ==>
        ~(r.R s n = EMPTY)) /\ ~(r.S0 = EMPTY))`;


val UNIVERSALLY_TOTAL_NO_EMPTY_SET_IN_RUN =
 store_thm
  ("UNIVERSALLY_TOTAL_NO_EMPTY_SET_IN_RUN",
    ``!A i r. (ALTERNATING_RUN A i r /\ IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\ IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A) ==> NO_EMPTY_SET_IN_RUN r``,

FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def, IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
NO_EMPTY_SET_IN_RUN_def, IS_PROP_DISJUNCTION_def] THEN
PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM, EMPTY_SUBSET]);


val EXISTENTIALLY_TOTAL_PRERUN_IS_RUN =
 store_thm
  ("EXISTENTIALLY_TOTAL_PRERUN_IS_RUN",
    ``!A i r. IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A ==>
        (ALTERNATING_PRERUN A i r = ALTERNATING_RUN A i r)``,

    FULL_SIMP_TAC std_ss [IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON_def,
        ALTERNATING_PRERUN_def, ALTERNATING_RUN_def, P_IS_CONTRADICTION_def] THEN
    PROVE_TAC[]);



val ALTERNATING_PRERUN_EXISTS =
 store_thm
  ("ALTERNATING_PRERUN_EXISTS",
    ``!A i. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A) ==> (?r. ALTERNATING_PRERUN A i r)``,

    FULL_SIMP_TAC std_ss [ALTERNATING_PRERUN_def,
        IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
        P_IS_CONTRADICTION_def] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC ``alternating_run (if (P_IS_CONTRADICTION A.S0) then EMPTY else A.S:'b set)
       (\s n. if (P_IS_CONTRADICTION (A.R s (i n))) then EMPTY else A.S)`` THEN
    REWRITE_TAC(P_IS_CONTRADICTION_def ::
                TypeBase.accessors_of “:α alternating_run”) THEN
    REPEAT STRIP_TAC THENL [
        Cases_on `!P. ~P_SEM P A.S0` THEN ASM_REWRITE_TAC[SUBSET_REFL, EMPTY_SUBSET],

        Cases_on `!P. ~P_SEM P A.S0` THEN ASM_REWRITE_TAC[] THEN
        FULL_SIMP_TAC std_ss [] THEN
        `P_SEM (P INTER A.S) A.S0` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
        `P INTER A.S SUBSET A.S` by PROVE_TAC[INTER_SUBSET] THEN
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM],

        Cases_on `!P. ~P_SEM P (A.R s (i n))` THEN ASM_SIMP_TAC std_ss [SUBSET_REFL, EMPTY_SUBSET],


        Cases_on `!P. ~P_SEM P (A.R s (i n))` THEN ASM_SIMP_TAC std_ss [] THEN
        FULL_SIMP_TAC std_ss [] THEN
        `P_SEM (P INTER A.S) (A.R s (i n))` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
        `P INTER A.S SUBSET A.S` by PROVE_TAC[INTER_SUBSET] THEN
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM]
    ]);


val EXISTENTIALLY_TOTAL_RUN_EXISTS =
 store_thm
  ("EXISTENTIALLY_TOTAL_RUN_EXISTS",
    ``!A i. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\ IS_EXISTENTIALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A) ==> (?r. ALTERNATING_RUN A i r)``,

    PROVE_TAC[EXISTENTIALLY_TOTAL_PRERUN_IS_RUN, ALTERNATING_PRERUN_EXISTS]);


val IS_PATH_TO_def =
Define
    `IS_PATH_TO w r s n = ((w 0 IN r.S0) /\ (w n = s) /\
         (!m. m < n ==> (((w (SUC m)) IN r.R (w m) m))))`;


val IS_PATH_THROUGH_RUN___PATH_TO =
 store_thm
  ("IS_PATH_THROUGH_RUN___PATH_TO",
    ``!w r. IS_PATH_THROUGH_RUN w r ==> (!n. IS_PATH_TO w r (w n) n)``,

    REWRITE_TAC [IS_PATH_THROUGH_RUN_def, IS_PATH_TO_def] THEN
    PROVE_TAC[]);


val REACHABLE_STATES_IN_STATES_SET =
 store_thm
  ("REACHABLE_STATES_IN_STATES_SET",

    ``!A i r. ALTERNATING_PRERUN A i r ==> (!s n. IS_REACHABLE_BY_RUN (s, n) r ==> s IN A.S)``,

    REWRITE_TAC[ALTERNATING_PRERUN_def] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `n:num` THEN
    FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def] THEN
    PROVE_TAC[SUBSET_DEF]);


val PATH_TO_REACHABLE_STATES_EXISTS =
 store_thm
  ("PATH_TO_REACHABLE_STATES_EXISTS",

``!r s n. (IS_REACHABLE_BY_RUN (s, n) r) = (?w. IS_PATH_TO w r s n)``,

REWRITE_TAC [IS_PATH_TO_def] THEN
Induct_on `n` THENL [
    SIMP_TAC arith_ss [IS_REACHABLE_BY_RUN_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        EXISTS_TAC ``(\n. s):num -> 'a`` THEN
        BETA_TAC THEN
        ASM_REWRITE_TAC[],

        PROVE_TAC[]
    ],

    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def] THEN
        RES_TAC THEN
        EXISTS_TAC ``(\n'. if (n' = SUC n) then s else w n'):num->'a`` THEN
        ASM_SIMP_TAC arith_ss [] THEN
        REPEAT STRIP_TAC THEN
        Cases_on `m < n` THENL [
            ASM_SIMP_TAC arith_ss [],

            `m = n` by DECIDE_TAC THEN
            ASM_SIMP_TAC arith_ss []
        ],


        REWRITE_TAC[IS_REACHABLE_BY_RUN_def] THEN
        `!m. m < n ==> m < SUC n` by DECIDE_TAC THEN
        `IS_REACHABLE_BY_RUN (w n, n) r` by PROVE_TAC[] THEN
        EXISTS_TAC ``(w:num -> 'a) n`` THEN
        ASM_REWRITE_TAC[] THEN
        `n < SUC n` by DECIDE_TAC THEN
        PROVE_TAC[]
    ]
]);


val IS_PATH_THROUGH_RUN___IS_REACHABLE_BY_RUN =
 store_thm
  ("IS_PATH_THROUGH_RUN___IS_REACHABLE_BY_RUN",
    ``!w r. IS_PATH_THROUGH_RUN w r ==> (!n. IS_REACHABLE_BY_RUN (w n, n) r)``,

    PROVE_TAC[IS_PATH_THROUGH_RUN___PATH_TO,
                      PATH_TO_REACHABLE_STATES_EXISTS]);


Theorem NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_AND_REACHABLE_STATE_EXISTS:
  !r s n. IS_REACHABLE_BY_RUN (s, n) r /\ NO_EMPTY_SET_IN_RUN r ==>
          ?w. IS_PATH_THROUGH_RUN w r /\ w n = s
Proof
  REWRITE_TAC [IS_PATH_THROUGH_RUN_def] THEN
  REPEAT STRIP_TAC THEN
  ‘?w. w = \n'. if n' <= n then (@w1. IS_PATH_TO w1 r s n) n'
                else (CHOOSEN_PATH {s} (\S n''. r.R S (PRE n'' + n))) (n' - n)’
    by simp[] THEN
  SUBGOAL_THEN “!n'. IS_REACHABLE_BY_RUN (w n', n') r” ASSUME_TAC
  >- (Induct_on ‘n'’ THENL [
        ASM_SIMP_TAC arith_ss [IS_REACHABLE_BY_RUN_def] THEN
        SELECT_ELIM_TAC THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
            PROVE_TAC[IS_PATH_TO_def]
        ],

        ASM_SIMP_TAC arith_ss [IS_REACHABLE_BY_RUN_def] THEN
        EXISTS_TAC “(w:num->'a) n'” THEN
        ASM_REWRITE_TAC[] THEN
        Cases_on ‘SUC n' <= n’ THENL [
            ASM_SIMP_TAC arith_ss [] THEN
            SELECT_ELIM_TAC THEN
            REPEAT STRIP_TAC THENL [
                PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
                FULL_SIMP_TAC arith_ss [IS_PATH_TO_def]
            ],

            Cases_on ‘n' <= n’ THENL [
                ‘n' = n’ by DECIDE_TAC THEN
                FULL_SIMP_TAC arith_ss [] THEN
                ASM_REWRITE_TAC [CHOOSEN_PATH_def, IN_SING] THEN
                SIMP_TAC arith_ss [] THEN
                SELECT_ELIM_TAC THEN
                REPEAT STRIP_TAC THENL [
                    PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
                    REWRITE_TAC[ONE, CHOOSEN_PATH_def] THEN
                    SELECT_ELIM_TAC THEN SELECT_ELIM_TAC THEN simp[] THEN
                    METIS_TAC[NO_EMPTY_SET_IN_RUN_def, MEMBER_NOT_EMPTY,
                              IS_PATH_TO_def]
                ],

                FULL_SIMP_TAC arith_ss [] THEN
                ‘SUC n' - n = SUC (n' - n)’ by DECIDE_TAC THEN
                ASM_SIMP_TAC arith_ss [CHOOSEN_PATH_def] THEN
                SELECT_ELIM_TAC THEN
                REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
                UNDISCH_TAC “IS_REACHABLE_BY_RUN (w n', n') r” THEN
                FULL_SIMP_TAC arith_ss [] THEN
                PROVE_TAC[NO_EMPTY_SET_IN_RUN_def]
            ]
        ]
    ]
) THEN
EXISTS_TAC “w:num -> 'a” THEN
REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC arith_ss [] THEN
    SELECT_ELIM_TAC THEN
    REPEAT STRIP_TAC THENL [
        PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
        PROVE_TAC[IS_PATH_TO_def]
    ],

    ‘(SUC n' <= n) \/ (n' = n) \/ (n < n')’ by DECIDE_TAC THENL [
        ASM_SIMP_TAC arith_ss [] THEN
        SELECT_ELIM_TAC THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
            FULL_SIMP_TAC arith_ss [IS_PATH_TO_def]
        ],

        ASM_SIMP_TAC arith_ss [] THEN
        SELECT_ELIM_TAC THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],

            ‘x n = s’ by PROVE_TAC[IS_PATH_TO_def] THEN
            ASM_REWRITE_TAC [CHOOSEN_PATH_def, ADD_CLAUSES, IN_SING, ONE] THEN
            SIMP_TAC arith_ss [] THEN
            SELECT_ELIM_TAC THEN
            ASM_REWRITE_TAC [MEMBER_NOT_EMPTY] THEN
            PROVE_TAC [NO_EMPTY_SET_IN_RUN_def]
        ],


        ASM_SIMP_TAC arith_ss [] THEN
        ‘SUC n' - n = SUC (n' - n)’ by DECIDE_TAC THEN
        ASM_SIMP_TAC arith_ss [CHOOSEN_PATH_def] THEN
        SELECT_ELIM_TAC THEN
        ASM_REWRITE_TAC [MEMBER_NOT_EMPTY] THEN
        FULL_SIMP_TAC arith_ss [NO_EMPTY_SET_IN_RUN_def] THEN
        ‘?m. n' - n = m’ by PROVE_TAC[] THEN
        ‘n' = n + m’ by DECIDE_TAC THEN
        ASM_REWRITE_TAC[] THEN
        ‘IS_REACHABLE_BY_RUN (w n', n') r’ by PROVE_TAC[] THEN
        ‘(CHOOSEN_PATH {s} (\S n'''. r.R S (n + PRE n''')) m) = w n'’ by
            (ASM_REWRITE_TAC [] THEN
            SIMP_TAC std_ss [] THEN
            ‘~(n + m <= n) /\ (n + m - n = m)’ by DECIDE_TAC THEN
            ASM_REWRITE_TAC[]) THEN
        PROVE_TAC[NO_EMPTY_SET_IN_RUN_def]
     ],

    ASM_SIMP_TAC arith_ss [] THEN
    SELECT_ELIM_TAC THEN
    REPEAT STRIP_TAC THENL [
        PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS],
        PROVE_TAC[IS_PATH_TO_def]
    ]
  ]
QED



val NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_EXISTS =
 store_thm
  ("NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_EXISTS",
    ``!r. (NO_EMPTY_SET_IN_RUN r) ==> ((?w. IS_PATH_THROUGH_RUN w r))``,

    REPEAT STRIP_TAC THEN
    `?x. x IN r.S0` by PROVE_TAC[NO_EMPTY_SET_IN_RUN_def, MEMBER_NOT_EMPTY] THEN
    `IS_REACHABLE_BY_RUN (x, 0) r` by PROVE_TAC[IS_REACHABLE_BY_RUN_def] THEN
    PROVE_TAC[NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_AND_REACHABLE_STATE_EXISTS]);



val NDET_MIN_RUN_SING =
 store_thm
  ("NDET_MIN_RUN_SING",

    ``!A i r. (ALTERNATING_MIN_RUN A i r /\ IS_NONDETERMINISTIC_SEMI_AUTOMATON A) ==>
                ((SING r.S0) /\ (!n s. IS_REACHABLE_BY_RUN (s,n) r ==> SING (r.R s n)))``,

        SIMP_TAC std_ss [ALTERNATING_MIN_RUN_def, IS_NONDETERMINISTIC_SEMI_AUTOMATON_def, IS_PROP_DISJUNCTION_def] THEN
        REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [P_PROP_DISJUNCTION_MIN_SEM, EXISTS_MEM, SING_DEF] THEN
            PROVE_TAC[],

            RES_TAC THEN
            `?S. A.R s (i n) = P_PROP_DISJUNCTION S` by PROVE_TAC[] THEN
            FULL_SIMP_TAC std_ss [P_PROP_DISJUNCTION_MIN_SEM, EXISTS_MEM, SING_DEF] THEN
            PROVE_TAC[]
        ]);


val NDET_MIN_RUN_REACHABLE =
 store_thm
  ("NDET_MIN_RUN_REACHABLE",

    ``!A i r. (ALTERNATING_MIN_RUN A i r /\ IS_NONDETERMINISTIC_SEMI_AUTOMATON A) ==>
                (!n. ?!s. IS_REACHABLE_BY_RUN (s,n) r)``,

        SIMP_TAC std_ss [EXISTS_UNIQUE_DEF] THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        Induct_on `n` THENL [
            `SING r.S0` by PROVE_TAC[NDET_MIN_RUN_SING] THEN
            FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, SING_DEF, IN_SING],

            FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def] THEN
            `SING (r.R s n)` by PROVE_TAC[NDET_MIN_RUN_SING] THEN
            FULL_SIMP_TAC std_ss [SING_DEF] THEN
            METIS_TAC[IN_SING]
        ]);




val ALT_SEM_S0_TRUE =
 store_thm
  ("ALT_SEM_S0_TRUE",
    ``!A i. ((A.A.S0 = P_TRUE) /\ (!n. i n IN A.A.I)) ==> ALT_SEM A i``,

    SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC ``alternating_run (EMPTY:'b set) (\s n. EMPTY)`` THEN
    SIMP_TAC (srw_ss()) [IS_PATH_THROUGH_RUN_def] THEN
    Cases_on `n` THEN
    SIMP_TAC (srw_ss()) [IS_REACHABLE_BY_RUN_def]);


val ALT_SEM_S0_FALSE =
 store_thm
  ("ALT_SEM_S0_FALSE",
    ``!A i. ((A.A.S0 = P_FALSE)) ==> ~ALT_SEM A i``,
    SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM]);


val ALT_SEM_S0_OR_SPLIT =
 store_thm
  ("ALT_SEM_S0_OR_SPLIT",
    ``!A i p1 p2. ((A.A.S0 = P_OR(p1, p2))) ==>
        (ALT_SEM A i = (ALT_SEM (alternating_automaton (alternating_semi_automaton A.A.S A.A.I
            p1 A.A.R) A.AC) i \/ ALT_SEM (alternating_automaton (alternating_semi_automaton A.A.S A.A.I p2 A.A.R) A.AC) i))``,

    SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM,
        alternating_automaton_REWRITES] THEN
    METIS_TAC[]);



val ALT_SEM_INITIAL_S0_P_PROP =
 store_thm
  ("ALT_SEM_INITIAL_S0_P_PROP",
    ``!A s0 f i. (A.S0 = P_PROP s0) ==>
        (ALT_SEM (alternating_automaton A (INITIAL f)) i =
        ALT_SEM (alternating_automaton A (if (s0 IN f) then TRUE else FALSE)) i)``,


    SIMP_TAC std_ss [ALT_SEM___ALT_SEM_MIN___EQUIV,
            ALT_SEM_MIN_def, alternating_automaton_REWRITES,
            ALT_ACCEPT_COND_SEM_def] THEN
    REPEAT STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    EXISTS_EQ_STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    REWRITE_TAC[IMP_DISJ_THM] THEN
    BOOL_EQ_STRIP_TAC THEN
    `P_SEM_MIN r.S0 (P_PROP s0)` by
            PROVE_TAC(ALTERNATING_MIN_RUN_def ::
                      TypeBase.accessors_of
                      “:(α,β) alternating_semi_automaton”) THEN
    FULL_SIMP_TAC std_ss [P_PROP_MIN_SEM] THEN
    `w 0 = s0` by PROVE_TAC[IS_PATH_THROUGH_RUN_def, IN_SING] THEN
    Cases_on `s0 IN f` THEN
    ASM_REWRITE_TAC [ALT_ACCEPT_COND_SEM_def]);





Theorem ALT_SEM_S0_AND_SPLIT___INITIAL:
  !A f i p1 p2.
    IS_VALID_ALTERNATING_AUTOMATON A /\ (A.A.S0 = P_AND(p1, p2)) /\
    (A.AC = INITIAL f) ==>
    (ALT_SEM A i =
     (ALT_SEM (alternating_automaton (alternating_semi_automaton A.A.S A.A.I
                                      p1 A.A.R) A.AC) i /\
      ALT_SEM (alternating_automaton (alternating_semi_automaton A.A.S A.A.I
                                      p2 A.A.R) A.AC) i))
Proof

  SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM,
                   alternating_automaton_REWRITES] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [ (* 6 *)
    ASM_REWRITE_TAC[],
    METIS_TAC[],
    ASM_REWRITE_TAC[],
    METIS_TAC[],
    ASM_REWRITE_TAC[],

    Q.ABBREV_TAC `P = (\s n. (?w. (IS_PATH_TO w r s n) /\ ~(w 0 IN f)))` THEN
    Q.ABBREV_TAC `P' = (\s n. (?w. (IS_PATH_TO w r' s n) /\ ~(w 0 IN f)))` THEN
    `!s:'b n:num. P s n ==> IS_REACHABLE_BY_RUN (s, n) r` by
              PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS] THEN
    `!s:'b n:num. P' s n ==> IS_REACHABLE_BY_RUN (s, n) r'` by
              PROVE_TAC[PATH_TO_REACHABLE_STATES_EXISTS] THEN
    `?ru. ru = (alternating_run (r.S0 UNION r'.S0)
                (\s n. if (P s n) then r.R s n
                       else if (P' s n) then r'.R s n
                       else if ~(IS_REACHABLE_BY_RUN (s, n) r) then
                         r'.R s n
                       else if ~(IS_REACHABLE_BY_RUN (s, n) r') then
                         r.R s n
                       else
                         r.R s n UNION r'.R s n))` by METIS_TAC[] THEN
    SUBGOAL_TAC
    ‘!s n. IS_REACHABLE_BY_RUN (s, n) (ru:'b alternating_run) ==>
           (IS_REACHABLE_BY_RUN (s, n) r \/ IS_REACHABLE_BY_RUN (s, n) r')’
    THEN1 (Induct_on `n` THENL [
              ASM_SIMP_TAC (srw_ss()) [IS_REACHABLE_BY_RUN_def],

              ASM_SIMP_TAC (srw_ss()) [IS_REACHABLE_BY_RUN_def] THEN
              METIS_TAC[IN_UNION]
            ]) THEN

    EXISTS_TAC ``ru:'b alternating_run`` THEN
    FULL_SIMP_TAC (srw_ss()) [
        IS_VALID_ALTERNATING_AUTOMATON_def, IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
        IS_POSITIVE_PROP_FORMULA_def, IS_POSITIVE_PROP_FORMULA_SUBSET_def,
        UNION_SUBSET]
    THEN REPEAT STRIP_TAC THENL [ (* 5 *)
        METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM, SUBSET_UNIV],
        METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM, SUBSET_UNIV,
                  UNION_COMM],
        METIS_TAC[UNION_SUBSET],
        METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM, SUBSET_UNIV],

        CCONTR_TAC THEN
        FULL_SIMP_TAC std_ss [ALT_ACCEPT_COND_SEM_def] THEN

        Cases_on `?n. P (w n) n` THENL [
            CLEAN_ASSUMPTIONS_TAC THEN
            UNDISCH_HD_TAC THEN
            GSYM_NO_TAC 7 THEN
            ASM_SIMP_TAC std_ss [] THEN
            GSYM_NO_TAC 0 THEN
            CCONTR_TAC THEN
            FULL_SIMP_TAC std_ss [] THEN
            `?v. v = \m. if (m <= n) then w' m else w m` by METIS_TAC[] THEN

            Tactical.REVERSE (SUBGOAL_THEN ``(!n:num. P ((v n):'b) n) /\ IS_PATH_THROUGH_RUN v r`` ASSUME_TAC) THEN1 (
            `v 0 = w' 0` by ASM_SIMP_TAC arith_ss [] THEN
            PROVE_TAC[]
            ) THEN
            FULL_SIMP_TAC std_ss (IS_PATH_THROUGH_RUN_def ::
                                  GSYM FORALL_AND_THM ::
                                  IS_PATH_TO_def ::
                                  TypeBase.accessors_of “:α alternating_run”)THEN
            Tactical.REVERSE (SUBGOAL_THEN ``(!m:num n:num. (n <= m) ==> (P (v n) n /\ v (SUC n) IN (r:'b alternating_run).R (v n) n))`` ASSUME_TAC) THEN1 (
            UNDISCH_HD_TAC THEN
            ASM_SIMP_TAC arith_ss [] THEN
            METIS_TAC[LESS_EQ_REFL]
            ) THEN

            Induct_on `m` THENL [
              SIMP_TAC arith_ss [] THEN
              LEFT_CONJ_TAC THENL [
                GSYM_NO_TAC 5 THEN
                ASM_SIMP_TAC arith_ss [] THEN
                METIS_TAC[],

                ASM_SIMP_TAC arith_ss [] THEN
                `1 = SUC 0` by DECIDE_TAC THEN
                Cases_on `1 <= n` THENL [
                    ASM_REWRITE_TAC[] THEN
                    `0 < n` by DECIDE_TAC THEN
                    PROVE_TAC[],

                    ASM_REWRITE_TAC[] THEN
                    `n = 0` by DECIDE_TAC THEN
                    METIS_TAC[]
                  ]
              ],

              REPEAT GEN_TAC THEN
              STRIP_TAC THEN
              LEFT_CONJ_TAC THENL [
                  GSYM_NO_TAC 7 THEN
                  ASM_SIMP_TAC arith_ss [] THEN
                  EXISTS_TAC ``v:num->'b `` THEN
                  ASM_SIMP_TAC arith_ss [],

                  ASM_SIMP_TAC arith_ss [] THEN
                  Cases_on `SUC n' <= n` THENL [
                      `n' <= n /\ n' < n` by DECIDE_TAC THEN
                      ASM_REWRITE_TAC[] THEN
                      METIS_TAC[],

                      ASM_REWRITE_TAC[] THEN
                      Cases_on `n' <= n` THENL [
                          `n' = n` by DECIDE_TAC THEN
                          METIS_TAC[],

                          METIS_TAC[]
                        ]
                    ]
                ]
            ],





            FULL_SIMP_TAC std_ss [] THEN
            `w 0 IN r'.S0` by (
              FULL_SIMP_TAC (srw_ss()) [IS_PATH_THROUGH_RUN_def] THEN
              UNDISCH_HD_TAC THEN
              GSYM_NO_TAC 8 THEN
              `P (w 0) 0` by (ASM_SIMP_TAC arith_ss [IS_PATH_TO_def] THEN
                              PROVE_TAC[]) THEN
              PROVE_TAC[]
              ) THEN

            Tactical.REVERSE (SUBGOAL_THEN ``(!n:num. P' ((w n):'b) n) /\ IS_PATH_THROUGH_RUN w r'`` ASSUME_TAC) THEN1 (
              PROVE_TAC[]
              ) THEN
            FULL_SIMP_TAC std_ss (IS_PATH_THROUGH_RUN_def ::
                                  GSYM FORALL_AND_THM ::
                                  IS_PATH_TO_def ::
                                  TypeBase.accessors_of “:α alternating_run”)THEN
            Tactical.REVERSE (SUBGOAL_THEN ``(!m:num n:num. (n <= m) ==> (P' (w n) n /\ w (SUC n) IN (r':'b alternating_run).R (w n) n))`` ASSUME_TAC) THEN1 (
              PROVE_TAC[LESS_EQ_REFL]
              ) THEN

            Induct_on `m` THENL [
                SIMP_TAC arith_ss [] THEN
                LEFT_CONJ_TAC THENL [
                  GSYM_NO_TAC 9 THEN
                  ASM_SIMP_TAC arith_ss [] THEN
                  METIS_TAC[],

                  `1 = SUC 0` by DECIDE_TAC THEN
                  PROVE_TAC[]
                ],

                REPEAT GEN_TAC THEN
                STRIP_TAC THEN
                LEFT_CONJ_TAC THENL [
                    GSYM_NO_TAC 11 THEN
                    ASM_SIMP_TAC arith_ss [] THEN
                    EXISTS_TAC ``w:num->'b `` THEN
                    ASM_SIMP_TAC arith_ss [],

                    PROVE_TAC[]
                  ]
              ]
          ]
      ]
  ]
QED

val ALTERNATING_AUTOMATA_CONJUNCTION =
 store_thm
  ("ALTERNATING_AUTOMATA_CONJUNCTION",
    ``!A A1 A2 i. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A1.A /\
                IS_VALID_ALTERNATING_SEMI_AUTOMATON A2.A /\
                (DISJOINT A1.A.S A2.A.S) /\ (A.A = (alternating_semi_automaton (A1.A.S UNION A2.A.S)
            (A1.A.I INTER A2.A.I) (P_AND (A1.A.S0, A2.A.S0)) (\s n. if (s IN A1.A.S) then A1.A.R s n else
                A2.A.R s n))) /\ (!w. (!n:num. (w n) IN A1.A.S) ==> (ALT_ACCEPT_COND_SEM A.AC = ALT_ACCEPT_COND_SEM A1.AC))
            /\ (!w. (!n:num. (w n) IN A2.A.S) ==> (ALT_ACCEPT_COND_SEM A.AC = ALT_ACCEPT_COND_SEM A2.AC))) ==>
        (IS_VALID_ALTERNATING_SEMI_AUTOMATON A.A /\ ((ALT_SEM A1 i /\ ALT_SEM A2 i) = ALT_SEM A i))``,

    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    SUBGOAL_TAC `IS_VALID_ALTERNATING_SEMI_AUTOMATON A.A` THEN1 (
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
            alternating_automaton_REWRITES, IS_POSITIVE_PROP_FORMULA_SUBSET_def,
            FINITE_UNION, P_USED_VARS_def, UNION_SUBSET,
            IS_POSITIVE_PROP_FORMULA_def, INTER_FINITE] THEN
        METIS_TAC[SUBSET_TRANS, SUBSET_UNION]
    ) THEN
    ASM_SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM,
        alternating_automaton_REWRITES, IN_INTER, FORALL_AND_THM] THEN
    REPEAT CONJ_EQ_STRIP_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        `?ru. ru = alternating_run ((r:'b alternating_run).S0 UNION r'.S0) (\s n.
            (if s IN A1.A.S then r.R s n else r'.R s n))` by PROVE_TAC[] THEN
        SUBGOAL_TAC `!w. (IS_PATH_THROUGH_RUN w (ru:'b alternating_run)) =
            (IS_PATH_THROUGH_RUN w r \/ IS_PATH_THROUGH_RUN w r')` THEN1 (

            ASM_SIMP_TAC (srw_ss()) [IS_PATH_THROUGH_RUN_def] THEN
            REPEAT STRIP_TAC THEN EQ_TAC THENL [
                REPEAT STRIP_TAC THENL [
                    `~(w 0 IN r'.S0)` by METIS_TAC[IN_DISJOINT, SUBSET_DEF] THEN
                    ASM_REWRITE_TAC[] THEN
                    Induct_on `n` THEN
                    METIS_TAC[IN_DISJOINT, SUBSET_DEF],

                    `~(w 0 IN r.S0)` by METIS_TAC[IN_DISJOINT, SUBSET_DEF] THEN
                    ASM_REWRITE_TAC[] THEN
                    Induct_on `n` THEN
                    METIS_TAC[IN_DISJOINT, SUBSET_DEF]
                ],

                REPEAT STRIP_TAC THENL [
                    ASM_REWRITE_TAC[],
                    Cases_on `n` THEN METIS_TAC[SUBSET_DEF],
                    ASM_REWRITE_TAC[],
                    Cases_on `n` THEN METIS_TAC[SUBSET_DEF, IN_DISJOINT]
                ]
            ]
        ) THEN

        SUBGOAL_TAC `!s n. (IS_REACHABLE_BY_RUN (s, n) (ru:'b alternating_run)) =
            (IS_REACHABLE_BY_RUN (s,n) r \/ IS_REACHABLE_BY_RUN (s,n) r')` THEN1 (

            Induct_on `n` THENL [
                ASM_SIMP_TAC (srw_ss()) [IS_REACHABLE_BY_RUN_def],

                ASM_SIMP_TAC (srw_ss()) [IS_REACHABLE_BY_RUN_def] THEN
                REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
                    METIS_TAC[REACHABLE_STATES_IN_STATES_SET,
                        ALTERNATING_PRERUN_def],
                    METIS_TAC[REACHABLE_STATES_IN_STATES_SET, IN_DISJOINT,
                        ALTERNATING_PRERUN_def],
                    METIS_TAC[REACHABLE_STATES_IN_STATES_SET,
                        ALTERNATING_PRERUN_def],
                    METIS_TAC[REACHABLE_STATES_IN_STATES_SET,
                        ALTERNATING_PRERUN_def, IN_DISJOINT]
                ]
            ]
        ) THEN

        EXISTS_TAC ``ru : 'b alternating_run`` THEN
        FULL_SIMP_TAC (srw_ss()) [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                                  UNION_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
            METIS_TAC[SUBSET_TRANS, SUBSET_UNION],
            METIS_TAC[SUBSET_TRANS, SUBSET_UNION],
            METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM, SUBSET_UNION],
            METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM, SUBSET_UNION],
            METIS_TAC[SUBSET_TRANS, SUBSET_UNION],
            METIS_TAC[REACHABLE_STATES_IN_STATES_SET,
                ALTERNATING_PRERUN_def],
            METIS_TAC[REACHABLE_STATES_IN_STATES_SET, IN_DISJOINT,
                ALTERNATING_PRERUN_def],

            SUBGOAL_TAC `!n. w n IN A1.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def] THEN
                Cases_on `n` THEN
                PROVE_TAC[SUBSET_DEF]
            ) THEN
            METIS_TAC[],

            SUBGOAL_TAC `!n. w n IN A2.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def] THEN
                Cases_on `n` THEN
                PROVE_TAC[SUBSET_DEF]
            ) THEN
            METIS_TAC[]
        ],



        `?r1. r1 = alternating_run ((r:'b alternating_run).S0 INTER A1.A.S) (\s n. (r.R s n) INTER A1.A.S)` by PROVE_TAC[] THEN
        `IS_ALTERNATING_SUBRUN r1 r`
          by FULL_SIMP_TAC std_ss [IS_ALTERNATING_SUBRUN_def,
                                   INTER_SUBSET] THEN

        EXISTS_TAC ``r1:'b alternating_run`` THEN
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                              INTER_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `s IN A1.A.S` THEN1 (
                Cases_on `n` THEN
                FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER]
            ) THEN
            METIS_TAC[SUBRUN_REACHABLE_STATES, P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `!n. w n IN A1.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def, IN_INTER] THEN
                Cases_on `n` THEN
                ASM_REWRITE_TAC[]
            ) THEN
            PROVE_TAC[IS_PATH_THROUGH_SUBRUN_THM]
        ],



        `?r2. r2 = alternating_run ((r:'b alternating_run).S0 INTER A2.A.S) (\s n. (r.R s n) INTER A2.A.S)` by PROVE_TAC[] THEN
        `IS_ALTERNATING_SUBRUN r2 r`
          by FULL_SIMP_TAC std_ss [IS_ALTERNATING_SUBRUN_def,
                                   INTER_SUBSET] THEN

        EXISTS_TAC ``r2:'b alternating_run`` THEN
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                              INTER_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `s IN A2.A.S` THEN1 (
                Cases_on `n` THEN
                FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER]
            ) THEN
            `~(s IN A1.A.S)` by PROVE_TAC[IN_DISJOINT] THEN
            METIS_TAC[SUBRUN_REACHABLE_STATES, P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `!n. w n IN A2.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def, IN_INTER] THEN
                Cases_on `n` THEN
                ASM_REWRITE_TAC[]
            ) THEN
            PROVE_TAC[IS_PATH_THROUGH_SUBRUN_THM]
        ]
    ]);



val ALTERNATING_AUTOMATA_DISJUNCTION =
 store_thm
  ("ALTERNATING_AUTOMATA_DISJUNCTION",
    ``!A A1 A2 i. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A1.A /\
                IS_VALID_ALTERNATING_SEMI_AUTOMATON A2.A /\
                (A2.A.I = A1.A.I) /\
                (DISJOINT A1.A.S A2.A.S) /\ (A.A = (alternating_semi_automaton (A1.A.S UNION A2.A.S)
            (A1.A.I) (P_OR (A1.A.S0, A2.A.S0)) (\s n. if (s IN A1.A.S) then A1.A.R s n else
                A2.A.R s n))) /\ (!w. (!n:num. (w n) IN A1.A.S) ==> (ALT_ACCEPT_COND_SEM A.AC = ALT_ACCEPT_COND_SEM A1.AC))
            /\ (!w. (!n:num. (w n) IN A2.A.S) ==> (ALT_ACCEPT_COND_SEM A.AC = ALT_ACCEPT_COND_SEM A2.AC))) ==>
        (IS_VALID_ALTERNATING_SEMI_AUTOMATON A.A /\ ((ALT_SEM A1 i \/ ALT_SEM A2 i) = ALT_SEM A i))``,

    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    SUBGOAL_TAC `IS_VALID_ALTERNATING_SEMI_AUTOMATON A.A` THEN1 (
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
            alternating_automaton_REWRITES, IS_POSITIVE_PROP_FORMULA_SUBSET_def,
            FINITE_UNION, P_USED_VARS_def, P_OR_def, UNION_SUBSET,
            IS_POSITIVE_PROP_FORMULA_def, INTER_FINITE] THEN
        METIS_TAC[SUBSET_TRANS, SUBSET_UNION]
    ) THEN
    ASM_SIMP_TAC std_ss [ALT_SEM_def, ALTERNATING_RUN_def, P_SEM_THM,
        alternating_automaton_REWRITES, IN_INTER, FORALL_AND_THM] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        ASM_REWRITE_TAC[],

        EXISTS_TAC ``r:'b alternating_run`` THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[SUBSET_TRANS, SUBSET_UNION],
            PROVE_TAC[SUBSET_TRANS, SUBSET_UNION],
            METIS_TAC[REACHABLE_STATES_IN_STATES_SET, ALTERNATING_PRERUN_def],

            SUBGOAL_TAC `!n. w n IN A1.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def] THEN
                Cases_on `n` THEN
                PROVE_TAC[SUBSET_DEF]
            ) THEN
            METIS_TAC[]
        ],

        ASM_REWRITE_TAC[],

        EXISTS_TAC ``r:'b alternating_run`` THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[SUBSET_TRANS, SUBSET_UNION],
            PROVE_TAC[SUBSET_TRANS, SUBSET_UNION],
            METIS_TAC[REACHABLE_STATES_IN_STATES_SET, ALTERNATING_PRERUN_def,
                IN_DISJOINT],

            SUBGOAL_TAC `!n. w n IN A2.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def] THEN
                Cases_on `n` THEN
                PROVE_TAC[SUBSET_DEF]
            ) THEN
            METIS_TAC[]
        ],


        DISJ1_TAC THEN
        ASM_REWRITE_TAC[] THEN
        `?r1. r1 = alternating_run ((r:'b alternating_run).S0 INTER A1.A.S) (\s n. (r.R s n) INTER A1.A.S)` by PROVE_TAC[] THEN
        `IS_ALTERNATING_SUBRUN r1 r`
          by FULL_SIMP_TAC std_ss [IS_ALTERNATING_SUBRUN_def,
                                   INTER_SUBSET] THEN

        EXISTS_TAC ``r1:'b alternating_run`` THEN
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                              INTER_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],

            `s IN A1.A.S` by (Cases_on `n` THEN
                FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER]) THEN
            METIS_TAC[SUBRUN_REACHABLE_STATES, P_USED_VARS_INTER_SUBSET_THM],

            `!n. w n IN A1.A.S` by (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def, IN_INTER] THEN
                Cases_on `n` THEN
                ASM_REWRITE_TAC[]
             ) THEN
            PROVE_TAC[IS_PATH_THROUGH_SUBRUN_THM]
        ],

        DISJ2_TAC THEN
        ASM_REWRITE_TAC[] THEN
        `?r2. r2 = alternating_run ((r:'b alternating_run).S0 INTER A2.A.S) (\s n. (r.R s n) INTER A2.A.S)` by PROVE_TAC[] THEN
        `IS_ALTERNATING_SUBRUN r2 r`
          by FULL_SIMP_TAC std_ss [IS_ALTERNATING_SUBRUN_def,INTER_SUBSET] THEN

        EXISTS_TAC ``r2:'b alternating_run`` THEN
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                              INTER_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `s IN A2.A.S` THEN1 (
                Cases_on `n` THEN
                FULL_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER]
            ) THEN
            `~(s IN A1.A.S)` by PROVE_TAC[IN_DISJOINT] THEN
            METIS_TAC[SUBRUN_REACHABLE_STATES, P_USED_VARS_INTER_SUBSET_THM],

            SUBGOAL_TAC `!n. w n IN A2.A.S` THEN1 (
                FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def, IN_INTER] THEN
                Cases_on `n` THEN
                ASM_REWRITE_TAC[]
            ) THEN
            PROVE_TAC[IS_PATH_THROUGH_SUBRUN_THM]
         ]
    ]);



val ALT_AUTOMATON_NEG_COMMON_PATH_THROUGH_RUNS_EXISTS =
 prove (
    ``!A i r r'. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\
               ALTERNATING_RUN A i r /\ ALTERNATING_RUN (ALT_SEMI_AUTOMATON_NEG A) i r') ==> (?w. IS_PATH_THROUGH_RUN w r /\ IS_PATH_THROUGH_RUN w r')``,



    SIMP_TAC std_ss [ALT_AUTOMATON_NEG_def,
        ALT_SEMI_AUTOMATON_NEG_def, ALTERNATING_RUN_def,
        alternating_automaton_REWRITES, P_SEM_MIN_def, P_SEM_THM, P_NEGATE_VARS_SEM, P_DUAL_def,
        IS_VALID_ALTERNATING_SEMI_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [] THEN
    `?r''. r'' = alternating_run (r.S0 INTER r'.S0)  (\s n. (r.R s n INTER r'.R s n))` by METIS_TAC[] THEN

    REMAINS_TAC `?w. IS_PATH_THROUGH_RUN w (r'':'b alternating_run)` THEN1 (
        EXISTS_TAC ``w:num->'b`` THEN
        UNDISCH_HD_TAC THEN
        FULL_SIMP_TAC std_ss [IS_PATH_THROUGH_RUN_def, IN_INTER]
    ) THEN

    REMAINS_TAC `NO_EMPTY_SET_IN_RUN (r'':'b alternating_run)` THEN1 (
        PROVE_TAC[NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_EXISTS]
    ) THEN

    REWRITE_TAC[NO_EMPTY_SET_IN_RUN_def] THEN
    Tactical.REVERSE STRIP_TAC THENL [
        ASM_SIMP_TAC std_ss [] THEN
        REPEAT STRIP_TAC THEN
        `r.S0 SUBSET (UNIV DIFF r'.S0)` by PROVE_TAC[SUBSET_COMPL_DISJOINT, DISJOINT_DEF, COMPL_DEF] THEN
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM],


        SUBGOAL_TAC `!n (s:'b). (IS_REACHABLE_BY_RUN (s, n) r'') ==> (IS_REACHABLE_BY_RUN (s, n) r /\
                IS_REACHABLE_BY_RUN (s, n) r')` THEN1 (
            Induct_on `n` THENL [
                ASM_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER],

                ASM_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, IN_INTER] THEN
                PROVE_TAC[]
            ]
        ) THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        RES_TAC THEN
        ASM_SIMP_TAC std_ss [] THEN
        REPEAT STRIP_TAC THEN
        `r.R s n SUBSET (UNIV DIFF r'.R s n)` by PROVE_TAC[SUBSET_COMPL_DISJOINT, DISJOINT_DEF, COMPL_DEF] THEN
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM]
    ]);



val A_TRUE___A_UNIVERSALLY_TOTAL_WEAK_CO_BUECHI =
 store_thm
  ("A_TRUE___A_UNIVERSALLY_TOTAL_WEAK_CO_BUECHI",

    ``!A:('input, 'states) alternating_automaton S. (IS_VALID_ALTERNATING_AUTOMATON A /\ IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A.A /\ (A.AC = WEAK_CO_BUECHI S)) ==>
        (?B:('input, 'states) alternating_automaton. (B=(alternating_automaton (alternating_semi_automaton A.A.S A.A.I A.A.S0 (\s i. if (s IN S) then P_FALSE else A.A.R s i)) TRUE)) /\ (IS_VALID_ALTERNATING_AUTOMATON B) /\ (ALT_AUTOMATON_EQUIV A B))``,

    SIMP_TAC std_ss [] THEN
    REPEAT STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_AUTOMATON_def,
            IS_VALID_ALTERNATING_SEMI_AUTOMATON_def, IS_VALID_ACCEPTANCE_COMPONENT_def,
            alternating_automaton_REWRITES] THEN
        REPEAT STRIP_TAC THENL [
            Cases_on `s IN S` THEN
            ASM_SIMP_TAC std_ss [P_USED_VARS_def, P_FALSE_def, EMPTY_SUBSET],

            Cases_on `s IN S` THEN
            FULL_SIMP_TAC std_ss [IS_POSITIVE_PROP_FORMULA_def,
                IS_POSITIVE_PROP_FORMULA_SUBSET_def, P_FALSE_def]
        ],

        FULL_SIMP_TAC std_ss [ALT_AUTOMATON_EQUIV_def, ALT_SEM_def,
            IS_NONDETERMINISTIC_AUTOMATON_def,
            ALT_ACCEPT_COND_SEM_THM, ALT_ACCEPT_COND_SEM_def,
            alternating_automaton_REWRITES,
            IS_VALID_ALTERNATING_AUTOMATON_def] THEN
        REPEAT STRIP_TAC THEN
        CONJ_EQ_STRIP_TAC THEN
        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            EXISTS_TAC ``r:'states alternating_run`` THEN
            `NO_EMPTY_SET_IN_RUN r` by PROVE_TAC[UNIVERSALLY_TOTAL_NO_EMPTY_SET_IN_RUN] THEN
            FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def,
                alternating_automaton_REWRITES] THEN
            REPEAT STRIP_TAC THEN
            `?w. IS_PATH_THROUGH_RUN w r /\ (w n = s)` by PROVE_TAC[NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_AND_REACHABLE_STATE_EXISTS] THEN
            `~(s IN S)` by PROVE_TAC[] THEN
            PROVE_TAC[],

            EXISTS_TAC ``r:'states alternating_run`` THEN
            FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def,
                alternating_automaton_REWRITES] THEN
            REPEAT STRIP_TAC THENL [
                RES_TAC THEN
                Cases_on `s IN S` THEN
                FULL_SIMP_TAC std_ss [P_SEM_THM],

                `IS_REACHABLE_BY_RUN (w n, n) r` by PROVE_TAC[
                    IS_PATH_THROUGH_RUN___IS_REACHABLE_BY_RUN] THEN
                RES_TAC THEN
                PROVE_TAC[P_SEM_THM]
            ]
        ]
    ]);




val NDET_TRUE___NDET_WEAK_CO_BUECHI =
 store_thm
  ("NDET_TRUE___NDET_WEAK_CO_BUECHI",

    ``!A:('input, 'states) alternating_automaton. (IS_VALID_ALTERNATING_AUTOMATON A /\ IS_NONDETERMINISTIC_AUTOMATON A /\ (?S. A.AC = WEAK_CO_BUECHI S)) ==>
        (?B:('input, 'states) alternating_automaton. (IS_VALID_ALTERNATING_AUTOMATON B /\ IS_NONDETERMINISTIC_AUTOMATON B) /\ (B.AC = TRUE) /\ (ALT_AUTOMATON_EQUIV A B))``,

    REPEAT STRIP_TAC THEN
    `IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A.A` by PROVE_TAC[
        NONDETERMINISTIC_IS_UNIVERSALLY_TOTAL, IS_NONDETERMINISTIC_AUTOMATON_def] THEN
    `?B. (B = alternating_automaton (alternating_semi_automaton A.A.S A.A.I A.A.S0
                    (\s i. (if s IN S then P_FALSE else A.A.R s i)))
                 TRUE) /\ IS_VALID_ALTERNATING_AUTOMATON B /\
              ALT_AUTOMATON_EQUIV A B` by METIS_TAC[A_TRUE___A_UNIVERSALLY_TOTAL_WEAK_CO_BUECHI] THEN
    EXISTS_TAC ``B:('input, 'states) alternating_automaton`` THEN
    ASM_REWRITE_TAC (TypeBase.accessors_of “:(α,β)alternating_automaton”) THEN
    FULL_SIMP_TAC std_ss [IS_NONDETERMINISTIC_AUTOMATON_def,
        IS_NONDETERMINISTIC_SEMI_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `s IN S` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IS_PROP_DISJUNCTION_def] THEN
    PROVE_TAC[P_PROP_DISJUNCTION_def]);




val _ = export_theory();
