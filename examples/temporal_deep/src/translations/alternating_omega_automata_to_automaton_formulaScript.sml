open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["xprop_logicTheory", "prop_logicTheory", "infinite_pathTheory", "pred_setTheory", "listTheory", "pairTheory", "set_lemmataTheory",
   "containerTheory", "prim_recTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory", "arithmeticTheory", "numLib",
   "alternating_omega_automataTheory", "symbolic_semi_automatonTheory", "automaton_formulaTheory"];
*)

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
   containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
   tuerk_tacticsLib temporal_deep_mixedTheory arithmeticTheory numLib
   automaton_formulaTheory alternating_omega_automataTheory
   symbolic_semi_automatonTheory;
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


val _ = new_theory "alternating_omega_automata_to_automaton_formula";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]

(*This file contains some definitions and lemmata about a translation of
  alternating omega-automata to automaton formulas, i.e. symbolic
  nondeterminisation algorithms for alternating automata.

  However, it is far away from beeing complete. The main interest has been
  in proving some very simple cases. Alternating and symbolically represented
  nondeterministic automata are strongly connected for finite words. In fact,
  alternating automata on finite words can be considered as a special normal
  form of nonderministic automata, i.e. there is a very very simple nondetermisation
  algorithm for finite words.

  The same idea also works for simple classes of alternating omega automata.
  Here it is proved for alternating automata representing savety properties.

  For more details you can have a look at the internal report
  "Relationship between Alternating omega-Automata and Symbolically Represented Nondeterministic omega-Automata" by Thomas Tuerk and Klaus Schneider,
  University of Kaiserslautern, November 2005.
  It can be found at http://rsg.informatik.uni-kl.de/publications/.
  *)




val std_ss = std_ss ++
             rewrites (TypeBase.accessors_of “:α alternating_run” @
                       TypeBase.accessors_of “:(α,β)alternating_automaton” @
                       TypeBase.accessors_of “:(α,β)alternating_semi_automaton”)

val IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def = Define
  `IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON (A:('a, 'a) alternating_semi_automaton) (fi:'a->'a set) =
     (symbolic_semi_automaton (A:('a, 'a) alternating_semi_automaton).S
        A.S0
        (XP_BIGAND (SET_TO_LIST (IMAGE (\s. XP_IMPL (XP_PROP s,
                XP_BIGOR (SET_TO_LIST (IMAGE (\i. XP_AND(XP_CURRENT (P_PROP_SET_MODEL (fi i) (BIGUNION(IMAGE fi A.I))), XP_NEXT (A.R s i))) A.I)))) A.S))))`;


val EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def = Define
  `EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON (A:('a, 'a) alternating_semi_automaton) (fi:'a->'a set) =
     (symbolic_semi_automaton (A:('a, 'a) alternating_semi_automaton).S
        A.S0
        (XP_BIGAND (SET_TO_LIST (IMAGE (\s. XP_EQUIV(XP_PROP s,
                XP_BIGOR (SET_TO_LIST (IMAGE (\i. XP_AND(XP_CURRENT (P_PROP_SET_MODEL (fi i) (BIGUNION(IMAGE fi A.I))), XP_NEXT (A.R s i))) A.I)))) A.S))))`;



val COLLAPSED_ALTERNATING_RUN_def =
Define
    `COLLAPSED_ALTERNATING_RUN (r:'a alternating_run) = \n:num.
        {s | IS_REACHABLE_BY_RUN (s, n) r}`;


val DECOLLAPSED_RUN_def =
Define
    `DECOLLAPSED_RUN (r:num->'a set) = alternating_run (r 0) (\s n:num. r (SUC n))`;

val EMPTY_ABORT_RUN_def =
Define
    `EMPTY_ABORT_RUN (r:num->'a set) = (\n. if (?n'. (n' < n) /\ (r n' = EMPTY)) then EMPTY else r n)`;

val IS_VALID_INPUT_ENCODING_def =
Define
    `IS_VALID_INPUT_ENCODING (A:('a,'b) alternating_semi_automaton) (f:'a->'b set) =
        ((INJ f A.I UNIV) /\ (!i. (i IN A.I ==> (FINITE (f i) /\ DISJOINT A.S (f i)))))`;

val IS_VALID_ENCODED_INPUT_def =
Define
    `IS_VALID_ENCODED_INPUT (A:('a,'b) alternating_semi_automaton) (f:'a->'b set) i i' =
        (!n. (i n IN A.I) /\ (i' n = f (i n)))`;







val EQ_COLLAPSED_RUN___IMPLIES___IMPL_COLLAPSED_RUN =
 store_thm
  ("EQ_COLLAPSED_RUN___IMPLIES___IMPL_COLLAPSED_RUN",
    ``!A fi r i. (FINITE A.S /\ IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i r) ==>
             IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i r``,

    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
        IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def, XP_BIGAND_SEM,
        symbolic_semi_automaton_REWRITES] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_HD_TAC THEN UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [IMAGE_FINITE, MEM_SET_TO_LIST, IN_IMAGE] THEN
    SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_IMP_THM,
        GSYM RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC std_ss [XP_SEM_THM] THEN
    METIS_TAC[]);




val IMPL_COLLAPSED_RUN_SEM =
 store_thm
  ("IMPL_COLLAPSED_RUN_SEM",

    ``!A f i' i w.
    (IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\
    IS_VALID_INPUT_ENCODING A f /\
    IS_VALID_ENCODED_INPUT A f i i') ==> (

    IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A f) i' w =
    (PATH_SUBSET w A.S /\ P_SEM (w 0) A.S0 /\
    !n s. (s IN w n) ==> P_SEM (w (SUC n)) (A.R s (i n))))``,

    FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def, XP_BIGAND_SEM, MEM_SET_TO_LIST,
        IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
        EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
        IS_VALID_ALTERNATING_SEMI_AUTOMATON_def, GSYM LEFT_FORALL_IMP_THM, XP_BIGOR_SEM,
        GSYM LEFT_EXISTS_AND_THM, IS_VALID_INPUT_ENCODING_def,
        IS_VALID_ENCODED_INPUT_def, symbolic_semi_automaton_REWRITES, IMAGE_FINITE,
        IN_IMAGE, XP_SEM_THM, XP_SEM___XP_CURRENT,
        XP_SEM___XP_NEXT, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `FINITE (BIGUNION (IMAGE f A.I))` THEN1 (
        ASM_SIMP_TAC std_ss [FINITE_BIGUNION_EQ, IMAGE_FINITE, IN_IMAGE] THEN
        PROVE_TAC[]) THEN
    ASM_SIMP_TAC std_ss [P_PROP_SET_MODEL_SEM] THEN

    SUBGOAL_TAC `!n. ((w n UNION (f (i n) DIFF A.S)) INTER A.S) = (w n INTER A.S)` THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INTER, IN_DIFF] THEN
      REPEAT STRIP_TAC  THEN
      REPEAT BOOL_EQ_STRIP_TAC
    ) THEN
    `P_SEM (w 0 UNION (f (i 0) DIFF A.S)) A.S0 =
      P_SEM (w 0) A.S0` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
    `!i' n s. i' IN A.I ==> (P_SEM (w n UNION (f (i n) DIFF A.S)) (A.R s i') =
                                   P_SEM (w n) (A.R s i'))` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    REPEAT FORALL_EQ_STRIP_TAC THEN
    rename1 `s IN A.S` THEN
    Cases_on `~(s IN w n)` THENL [
        ASM_REWRITE_TAC[],

        `s IN A.S` by PROVE_TAC[PATH_SUBSET_def, SUBSET_DEF] THEN
        FULL_SIMP_TAC std_ss [] THEN
        SUBGOAL_TAC `((w n UNION (f (i n) DIFF A.S)) INTER BIGUNION (IMAGE f A.I)) = f (i n)` THEN1 (
          SIMP_TAC std_ss [EXTENSION] THEN
          SIMP_ALL_TAC std_ss [IN_INTER, IN_UNION, IN_DIFF, IN_BIGUNION,
          IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, GSYM SUBSET_COMPL_DISJOINT,
            PATH_SUBSET_def, SUBSET_DEF, COMPL_DEF, IN_UNIV] THEN
          METIS_TAC[]
        ) THEN
        SUBGOAL_TAC `!i'. (i' IN A.I) ==> (f i' INTER BIGUNION (IMAGE f A.I) = f i')` THEN1 (
          SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION,
            IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
          METIS_TAC[]
        ) THEN
        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            PROVE_TAC[INJ_DEF],

            EXISTS_TAC ``i:num->'a n`` THEN
            ASM_REWRITE_TAC[] THEN
            PROVE_TAC[]
        ]
    ]);



val EQ_COLLAPSED_RUN_SEM =
 store_thm
  ("EQ_COLLAPSED_RUN_SEM",

    ``!A f i' i w.
    (IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\
    IS_VALID_INPUT_ENCODING A f /\
    IS_VALID_ENCODED_INPUT A f i i') ==> (

    IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A f) i' w =
    (PATH_SUBSET w A.S /\ P_SEM (w 0) A.S0 /\
    !n s. (s IN w n) = ((s IN A.S) /\ P_SEM (w (SUC n)) (A.R s (i n)))))``,

    FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def, XP_BIGAND_SEM, MEM_SET_TO_LIST,
        IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
        EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
        IS_VALID_ALTERNATING_SEMI_AUTOMATON_def, GSYM LEFT_FORALL_IMP_THM, XP_BIGOR_SEM,
        GSYM LEFT_EXISTS_AND_THM, IS_VALID_INPUT_ENCODING_def,
        IS_VALID_ENCODED_INPUT_def, symbolic_semi_automaton_REWRITES, IMAGE_FINITE,
        IN_IMAGE, XP_SEM_THM, XP_SEM___XP_CURRENT,
        XP_SEM___XP_NEXT, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `FINITE (BIGUNION (IMAGE f A.I))` THEN1 (
        ASM_SIMP_TAC std_ss [FINITE_BIGUNION_EQ, IMAGE_FINITE, IN_IMAGE] THEN
        PROVE_TAC[]
    ) THEN
    ASM_SIMP_TAC std_ss [P_PROP_SET_MODEL_SEM] THEN

    SUBGOAL_TAC `!n. ((w n UNION (f (i n) DIFF A.S)) INTER A.S) = (w n INTER A.S)` THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INTER, IN_DIFF] THEN
      REPEAT STRIP_TAC  THEN
      REPEAT BOOL_EQ_STRIP_TAC
    ) THEN
    `P_SEM (w 0 UNION (f (i 0) DIFF A.S)) A.S0 =
      P_SEM (w 0) A.S0` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
    `!i' n s. i' IN A.I ==> (P_SEM (w n UNION (f (i n) DIFF A.S)) (A.R s i') =
                                   P_SEM (w n) (A.R s i'))` by PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    REPEAT FORALL_EQ_STRIP_TAC THEN
    rename1 `s IN A.S` THEN
    Cases_on `~(s IN A.S)` THENL [
        ASM_REWRITE_TAC[] THEN
        PROVE_TAC[PATH_SUBSET_def, SUBSET_DEF],

        FULL_SIMP_TAC std_ss [] THEN
        ASM_SIMP_TAC std_ss [prove(``!a:bool b:bool c:bool. ((a = b) = (a = c)) = (b = c)``, METIS_TAC[])] THEN

        SUBGOAL_TAC `((w n UNION (f (i n) DIFF A.S)) INTER BIGUNION (IMAGE f A.I)) = f (i n)` THEN1 (
          SIMP_TAC std_ss [EXTENSION] THEN
          SIMP_ALL_TAC std_ss [IN_INTER, IN_UNION, IN_DIFF, IN_BIGUNION,
          IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, GSYM SUBSET_COMPL_DISJOINT,
            PATH_SUBSET_def, SUBSET_DEF, COMPL_DEF, IN_UNIV] THEN
          METIS_TAC[]
        ) THEN
        SUBGOAL_TAC `!i'. (i' IN A.I) ==> (f i' INTER BIGUNION (IMAGE f A.I) = f i')` THEN1 (
          SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION,
            IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
          METIS_TAC[]
        ) THEN

        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            PROVE_TAC[INJ_DEF],

            EXISTS_TAC ``i:num->'a n`` THEN
            ASM_REWRITE_TAC[] THEN
            PROVE_TAC[]
        ]
    ]);


val EMPTY_ABORT_RUN_ELIM =
 store_thm
  ("EMPTY_ABORT_RUN_ELIM",
    ``!r. (!n. ~(r n = EMPTY)) ==> (EMPTY_ABORT_RUN r = r)``,
    SIMP_TAC std_ss [EMPTY_ABORT_RUN_def] THEN
    SIMP_TAC std_ss [FUN_EQ_THM]);


val EMPTY_ABORT_RUN_EMPTY_SUC =
 store_thm
  ("EMPTY_ABORT_RUN_EMPTY_SUC",
    ``!r n. (EMPTY_ABORT_RUN r n = EMPTY) ==> (EMPTY_ABORT_RUN r (SUC n) = EMPTY)``,
    SIMP_TAC std_ss [EMPTY_ABORT_RUN_def] THEN
    REPEAT STRIP_TAC THEN
    Tactical.REVERSE (SUBGOAL_THEN ``?n'. n' < SUC n /\ (r n' = EMPTY)`` ASSUME_TAC) THEN1 (
        PROVE_TAC[]
    ) THEN
    Cases_on `?n'. n' < n /\ (r n' = EMPTY)` THENL [
        CLEAN_ASSUMPTIONS_TAC THEN
        `n' < SUC n` by DECIDE_TAC THEN
        PROVE_TAC[],

        `r n = EMPTY` by PROVE_TAC[] THEN
        `n < SUC n` by DECIDE_TAC THEN
        PROVE_TAC[]
    ]);


val COLLAPSED_DECOLLAPSED_ELIM =
 store_thm
  ("COLLAPSED_DECOLLAPSED_ELIM",
    ``!r. ((COLLAPSED_ALTERNATING_RUN (DECOLLAPSED_RUN (EMPTY_ABORT_RUN r))) = (EMPTY_ABORT_RUN r))``,

    SIMP_TAC std_ss [COLLAPSED_ALTERNATING_RUN_def, DECOLLAPSED_RUN_def] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    Induct_on `x` THENL [
        simp[IS_REACHABLE_BY_RUN_def],

        simp [IS_REACHABLE_BY_RUN_def] THEN
        Cases_on `EMPTY_ABORT_RUN r x = EMPTY` THENL [
            PROVE_TAC[MEMBER_NOT_EMPTY, EMPTY_ABORT_RUN_EMPTY_SUC],
            PROVE_TAC[MEMBER_NOT_EMPTY]
        ]
    ]);



val IS_REACHABLE_BY_DECOLLAPSED_EMPTY_ABORT_RUN_ELIM =
 store_thm
  ("IS_REACHABLE_BY_DECOLLAPSED_EMPTY_ABORT_RUN_ELIM",
    ``!s n r. (IS_REACHABLE_BY_RUN (s, n) (DECOLLAPSED_RUN (EMPTY_ABORT_RUN r))) = (s IN (EMPTY_ABORT_RUN r) n)``,

    Induct_on `n` THENL [
        SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, DECOLLAPSED_RUN_def],

        ASM_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, DECOLLAPSED_RUN_def] THEN
        REPEAT GEN_TAC THEN
        Cases_on `EMPTY_ABORT_RUN r n = EMPTY` THENL [
            PROVE_TAC[MEMBER_NOT_EMPTY, EMPTY_ABORT_RUN_EMPTY_SUC],
            PROVE_TAC[MEMBER_NOT_EMPTY]
        ]
    ]);


val IS_REACHABLE_BY_DECOLLAPSED_RUN =
 store_thm
  ("IS_REACHABLE_BY_DECOLLAPSED_RUN",
    ``!s n r. (IS_REACHABLE_BY_RUN (s, n) (DECOLLAPSED_RUN r)) ==> (s IN r n)``,

    Induct_on `n` THENL [
        SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, DECOLLAPSED_RUN_def],

        ASM_SIMP_TAC std_ss [IS_REACHABLE_BY_RUN_def, DECOLLAPSED_RUN_def] THEN
        PROVE_TAC[]
    ]);



val IMPL_COLLAPSED_SEMI_AUTOMATON___EMPTY_ABORT_RUN =
 store_thm
  ("IMPL_COLLAPSED_SEMI_AUTOMATON___EMPTY_ABORT_RUN",
    ``!A fi r i. FINITE A.S /\ IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i r ==>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i (EMPTY_ABORT_RUN r)``,

REPEAT STRIP_TAC THEN
Cases_on `~?n. ((r n = EMPTY) /\ (!m. m < n ==> ~(r m = EMPTY)))` THENL [
    FULL_SIMP_TAC std_ss [] THEN
    SUBGOAL_TAC `!n:num. ~(r n = EMPTY)` THEN1 (
      REMAINS_TAC `!n:num. (!m. m < n ==> ~(r m = EMPTY))` THEN1 (
        REPEAT STRIP_TAC THEN
        `n < SUC n` by DECIDE_TAC THEN
        PROVE_TAC[]
      ) THEN
      Induct_on `n` THENL [
        SIMP_TAC arith_ss [],

        REPEAT STRIP_TAC THEN
        `~(m < n)` by PROVE_TAC[] THEN
        `m = n` by DECIDE_TAC THEN
        PROVE_TAC[]
      ]
    ) THEN
    PROVE_TAC[EMPTY_ABORT_RUN_ELIM],


    FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
            symbolic_semi_automaton_REWRITES, PATH_SUBSET_def, EMPTY_ABORT_RUN_def] THEN
        PROVE_TAC[EMPTY_SUBSET],

        FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def] THEN
        `EMPTY_ABORT_RUN r 0 = r 0` by SIMP_TAC arith_ss [EMPTY_ABORT_RUN_def] THEN
        ASM_REWRITE_TAC[],

        Cases_on `~(EMPTY_ABORT_RUN r n' = EMPTY)` THENL [
            SUBGOAL_TAC `EMPTY_ABORT_RUN r n' = r n'` THEN1 (
                FULL_SIMP_TAC arith_ss [EMPTY_ABORT_RUN_def] THEN
                PROVE_TAC[]
            ) THEN
            SUBGOAL_TAC `EMPTY_ABORT_RUN r (SUC n') = r (SUC n')` THEN1 (
                FULL_SIMP_TAC arith_ss [EMPTY_ABORT_RUN_def] THEN
                REMAINS_TAC `~?n''. n'' < SUC n' /\ (r n'' = {})` THEN1 (
                    ASM_REWRITE_TAC[]
                ) THEN
                SIMP_TAC std_ss [] THEN
                REPEAT STRIP_TAC THEN
                Cases_on `n'' < n'` THEN1 PROVE_TAC[] THEN
                Cases_on `n'' < SUC n'` THEN ASM_REWRITE_TAC[] THEN
                `n'' = n'` by DECIDE_TAC THEN
                ASM_REWRITE_TAC[]
            ) THEN
            ASM_REWRITE_TAC[],

            CLEAN_ASSUMPTIONS_TAC THEN
            ASM_SIMP_TAC std_ss [IS_TRANSITION_def, IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def,
                INPUT_RUN_STATE_UNION_def, XP_BIGAND_SEM, IMAGE_FINITE, MEM_SET_TO_LIST, IN_IMAGE,
                GSYM LEFT_FORALL_IMP_THM, symbolic_semi_automaton_REWRITES,
                IN_DIFF, XP_SEM_THM, UNION_EMPTY]
        ]
    ]
]);


val COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM =
 store_thm
  ("COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM",

``!A fi i i' r.
   ((IS_VALID_ALTERNATING_SEMI_AUTOMATON A) /\
     IS_VALID_INPUT_ENCODING A fi /\
     IS_VALID_ENCODED_INPUT A fi i i') ==>

    (ALTERNATING_RUN A i r ==>
     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i' (COLLAPSED_ALTERNATING_RUN r))``,

    REPEAT STRIP_TAC THEN
    ASSUME_TAC ((SPECL [``A:('a,'a) alternating_semi_automaton``, ``fi:'a->'a->bool``,
        ``i':num->'a->bool``, ``i:num->'a``] IMPL_COLLAPSED_RUN_SEM)) THEN
    ASM_SIMP_TAC std_ss [] THEN
    WEAKEN_HD_TAC THEN
    FULL_SIMP_TAC std_ss [
        COLLAPSED_ALTERNATING_RUN_def, IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
        IS_REACHABLE_BY_RUN_def, IS_VALID_INPUT_ENCODING_def, IS_VALID_ENCODED_INPUT_def,
        GSPECIFICATION, PATH_SUBSET_def, SUBSET_DEF, GSPEC_ID] THEN

    REPEAT STRIP_TAC THENL [
        PROVE_TAC[REACHABLE_STATES_IN_STATES_SET,
            ALTERNATING_RUN_IS_PRERUN],

        FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def],

        FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def] THEN
        SUBGOAL_TAC `r.R s n SUBSET ({s | ?s'. IS_REACHABLE_BY_RUN (s',n) r /\ s IN r.R s' n})` THEN1 (
            ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
            PROVE_TAC[]) THEN
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM]
    ]);


val  DECOLLAPSED_RUN___IMPL_COLLAPSED___THM =
 store_thm
  ("DECOLLAPSED_RUN___IMPL_COLLAPSED___THM",

    ``!A fi i i' r.
    ((IS_VALID_ALTERNATING_SEMI_AUTOMATON A) /\
      IS_VALID_INPUT_ENCODING A fi /\
      IS_VALID_ENCODED_INPUT A fi i i') ==>

        (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i' r ==>
         ALTERNATING_RUN A i (DECOLLAPSED_RUN r))``,

    REPEAT STRIP_TAC THEN
    `PATH_SUBSET r A.S /\ P_SEM (r 0) A.S0 /\
          !n s. s IN r n ==> P_SEM (r (SUC n)) (A.R s (i n))` by PROVE_TAC[IMPL_COLLAPSED_RUN_SEM] THEN

    FULL_SIMP_TAC std_ss [ALTERNATING_RUN_def, DECOLLAPSED_RUN_def,
                          IS_VALID_ENCODED_INPUT_def,
                          PATH_SUBSET_def] THEN
    METIS_TAC[IS_REACHABLE_BY_DECOLLAPSED_RUN, DECOLLAPSED_RUN_def]);




val IMPL_COLLAPSED_RUN___EQ_COLLAPSED_RUN___ENRICHMENT =
 store_thm
  ("IMPL_COLLAPSED_RUN___EQ_COLLAPSED_RUN___ENRICHMENT",

    ``!A f i i' w. (IS_VALID_ALTERNATING_SEMI_AUTOMATON A /\
        IS_VALID_INPUT_ENCODING A f /\ IS_VALID_ENCODED_INPUT A f i i' /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A f) i' w) ==>
        (?w'. (!n. w n SUBSET w' n) /\
                IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A f) i' w')``,

    REPEAT STRIP_TAC THEN
    UNDISCH_HD_TAC THEN
    ASSUME_TAC ((SPECL [``A:('a,'a) alternating_semi_automaton``, ``f:'a->'a->bool``,
        ``i':num->'a->bool``, ``i:num->'a``] EQ_COLLAPSED_RUN_SEM)) THEN
    ASSUME_TAC ((SPECL [``A:('a,'a) alternating_semi_automaton``, ``f:'a->'a->bool``,
        ``i':num->'a->bool``, ``i:num->'a``] IMPL_COLLAPSED_RUN_SEM)) THEN
    ASM_SIMP_TAC std_ss [] THEN
    WEAKEN_HD_TAC THEN WEAKEN_HD_TAC THEN
    REPEAT STRIP_TAC THEN

    FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def, PATH_SUBSET_def] THEN
    `?fw. fw = (\w n. (w n) UNION ({s | s IN A.S /\ P_SEM (w (SUC n)) (A.R s (i n))}))` by METIS_TAC[] THEN
    `?w'. w' = (\n:num. BIGUNION {FUNPOW fw m w n | m IN UNIV})` by
        METIS_TAC[] THEN


    SUBGOAL_TAC `(!m n:num. (w n SUBSET (FUNPOW fw m w n)) /\ ((FUNPOW fw m w n) SUBSET (A:('a,'a) alternating_semi_automaton).S))` THEN1 (
        Induct_on `m` THENL [
            ASM_SIMP_TAC std_ss [FUNPOW_0, SUBSET_REFL],

            `?x. FUNPOW fw m w = x` by PROVE_TAC[] THEN
            ASM_SIMP_TAC std_ss [FUNPOW_SUC, UNION_SUBSET] THEN
            REPEAT STRIP_TAC THENL [
                PROVE_TAC[SUBSET_UNION, SUBSET_REFL, SUBSET_TRANS],
                PROVE_TAC[],
                SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
            ]
        ]
    ) THEN


    SUBGOAL_TAC `!m m':num n:num. m' >= m ==> ((FUNPOW fw m w n) SUBSET (FUNPOW fw m' w n))` THEN1 (
        Induct_on `m'-m` THENL [

            REPEAT STRIP_TAC THEN
            `m' = m` by DECIDE_TAC THEN
            ASM_REWRITE_TAC[SUBSET_REFL],

            REPEAT STRIP_TAC THEN
            `(v = m' - SUC m) /\ (m' >= SUC m)` by DECIDE_TAC THEN
            `(FUNPOW fw m w n) SUBSET (FUNPOW fw (SUC m) w n)` by (
                REWRITE_TAC [FUNPOW_SUC] THEN
                `?x. FUNPOW fw m w = x` by PROVE_TAC[] THEN
                ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION]
            ) THEN
            PROVE_TAC[SUBSET_TRANS]
        ]
    ) THEN


    SUBGOAL_TAC `!n:num. (w n SUBSET w' n)` THEN1 (
        ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION,
            GSYM RIGHT_EXISTS_AND_THM, GSPECIFICATION, IN_UNIV] THEN
        REPEAT STRIP_TAC THEN
        EXISTS_TAC ``0:num`` THEN
        ASM_REWRITE_TAC[FUNPOW_0]
    ) THEN


    SUBGOAL_TAC `!n:num. w' n SUBSET (A:('a,'a) alternating_semi_automaton).S` THEN1 (
        GSYM_NO_TAC 4 (*Def fw*) THEN
        ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION,
            GSYM RIGHT_EXISTS_AND_THM, GSPECIFICATION, IN_UNIV] THEN
        PROVE_TAC[SUBSET_DEF]
    ) THEN

    SUBGOAL_TAC `!n. ?m0. !m. m >= m0 ==> (FUNPOW fw m w n = FUNPOW fw m0 w n)` THEN1 (
        CCONTR_TAC THEN
        FULL_SIMP_TAC std_ss [] THEN

        `?z. (!m. CARD (FUNPOW fw m w n) <= z) /\ !z'. z' < z ==> ~!m. CARD (FUNPOW fw m w n) <= z'` by
            METIS_TAC[CARD_SUBSET,
            EXISTS_LEAST_CONV ``?z. !m. CARD (FUNPOW fw m (w:num->'a set) n) <= z``] THEN
        SUBGOAL_TAC `?m0. CARD (FUNPOW fw m0 w n) = z` THEN1 (
            CCONTR_TAC THEN
            FULL_SIMP_TAC std_ss [] THEN
            `!x z. (x <= z /\ (~(x = z))) ==> (x <= PRE z /\ PRE z < z)` by DECIDE_TAC THEN
            `!m:num. CARD (FUNPOW fw m w n) <= (PRE z) /\ PRE z < z` by METIS_TAC[] THEN
            METIS_TAC[]
        ) THEN

        `?m1. m1 >= m0 /\ ~(FUNPOW fw m1 w n = FUNPOW fw m0 w n)` by METIS_TAC[] THEN
        `FUNPOW fw m0 w n PSUBSET FUNPOW fw m1 w n` by PROVE_TAC[PSUBSET_DEF] THEN
        `z < CARD (FUNPOW fw m1 w n)` by PROVE_TAC[CARD_PSUBSET, SUBSET_FINITE] THEN
        `!x y. ~(x <= y /\ y < x)` by DECIDE_TAC THEN
        PROVE_TAC[]
    ) THEN

    SUBGOAL_TAC `!n. ?m0. (w' n = (FUNPOW fw m0 w n)) /\
        (!m. m >= m0 ==> (FUNPOW fw m w n = FUNPOW fw m0 w n))` THEN1 (
        GSYM_NO_TAC 6 THEN
        ASM_SIMP_TAC std_ss [] THEN
        REPEAT STRIP_TAC THEN
        `?m0. !m. m >= m0 ==> (FUNPOW fw m w n = FUNPOW fw m0 w n)` by PROVE_TAC[] THEN
        EXISTS_TAC ``m0:num`` THEN
        ASM_REWRITE_TAC[EXTENSION] THEN
        SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION,
          GSPECIFICATION, IN_UNIV] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            Cases_on `m >= m0` THENL [
                PROVE_TAC[],

                `m0 >= m` by DECIDE_TAC THEN
                PROVE_TAC[SUBSET_DEF]
            ],

            PROVE_TAC[]
        ]
    ) THEN


    SUBGOAL_TAC `!n s m. (s IN (FUNPOW fw m w n)) ==>
        (P_SEM (FUNPOW fw m w (SUC n))  ((A:('a, 'a) alternating_semi_automaton).R s (i n)))` THEN1 (
        Induct_on `m` THENL [
            ASM_SIMP_TAC std_ss [FUNPOW_0],

            `?x. FUNPOW fw m w = x` by PROVE_TAC[] THEN
            ONCE_REWRITE_TAC [FUNPOW_SUC] THEN
            FULL_SIMP_TAC std_ss [IN_UNION, GSPECIFICATION] THEN
            PROVE_TAC[SUBSET_UNION, IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM]
        ]
    ) THEN

    EXISTS_TAC ``w':num->'a set`` THEN
    REPEAT STRIP_TAC THENL [
        ASM_REWRITE_TAC[],
        ASM_REWRITE_TAC[],
        PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM],

        SUBGOAL_TAC `?l. (w' n = FUNPOW fw l w n) /\
                                         (!m. m >= l ==> (FUNPOW fw m w n = FUNPOW fw l w n)) /\
                                         (w' (SUC n) = FUNPOW fw l w (SUC n)) /\
                                         (!m. m >= l ==> (FUNPOW fw m w (SUC n) = FUNPOW fw l w (SUC n)))` THEN1 (
            `?m0. (w' n = FUNPOW fw m0 w n) /\ !m. m >= m0 ==> (FUNPOW fw m w n = FUNPOW fw m0 w n)`
                by METIS_TAC[] THEN
            `?m1. (w' (SUC n) = FUNPOW fw m1 w (SUC n)) /\ !m. m >= m1 ==> (FUNPOW fw m w (SUC n) = FUNPOW fw m1 w (SUC n))` by METIS_TAC[] THEN
            SUBGOAL_TAC `?l. l >= m0 /\ l >= m1` THEN1 (
                Cases_on `m0 >= m1` THENL [
                    EXISTS_TAC ``m0:num``,
                    EXISTS_TAC ``m1:num``
                ] THEN
                ASM_SIMP_TAC arith_ss []) THEN
            EXISTS_TAC ``l:num`` THEN
            `!m:num.  m >= l  ==> (m >= m0 /\ m >= m1)` by DECIDE_TAC THEN
            PROVE_TAC[]
        ) THEN
        EQ_TAC THENL [
            PROVE_TAC[SUBSET_DEF],

            `?x. FUNPOW fw l w = x` by PROVE_TAC[] THEN
            `w' (SUC n) = x (SUC n)` by PROVE_TAC[] THEN
            `SUC l >= l` by DECIDE_TAC THEN
            `w' n = (fw x) n` by METIS_TAC[FUNPOW_SUC, FUNPOW_0] THEN
            ASM_SIMP_TAC std_ss [IN_UNION, GSPECIFICATION]
        ]
    ]
);



val COLLAPSED_ALTERNATING_RUN___EQ_COLLAPSED___THM =
 store_thm
  ("COLLAPSED_ALTERNATING_RUN___EQ_COLLAPSED___THM",

``!A fi i i' r.
   ((IS_VALID_ALTERNATING_SEMI_AUTOMATON A) /\
     IS_VALID_INPUT_ENCODING A fi /\
     IS_VALID_ENCODED_INPUT A fi i i') ==>

    (ALTERNATING_RUN A i r ==> (?w.
        (!n. (COLLAPSED_ALTERNATING_RUN r) n SUBSET w n) /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i' w))``,


    PROVE_TAC[COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM,
                       IMPL_COLLAPSED_RUN___EQ_COLLAPSED_RUN___ENRICHMENT]);


val  DECOLLAPSED_RUN___EQ_COLLAPSED___THM =
 store_thm
  ("DECOLLAPSED_RUN___EQ_COLLAPSED___THM",

    ``!A fi i i' r.
    ((IS_VALID_ALTERNATING_SEMI_AUTOMATON A) /\
      IS_VALID_INPUT_ENCODING A fi /\
      IS_VALID_ENCODED_INPUT A fi i i') ==>

        (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A fi) i' r ==>
         ALTERNATING_RUN A i (DECOLLAPSED_RUN r))``,

    PROVE_TAC[IS_VALID_ALTERNATING_SEMI_AUTOMATON_def,
                      EQ_COLLAPSED_RUN___IMPLIES___IMPL_COLLAPSED_RUN,
                      DECOLLAPSED_RUN___IMPL_COLLAPSED___THM]);


val NDET_TRUE___A_TRUE___IMPL =
 store_thm
  ("NDET_TRUE___A_TRUE___IMPL",

    ``!A fi i i'. (IS_VALID_ALTERNATING_AUTOMATON A /\ (A.AC = TRUE) /\
             IS_VALID_INPUT_ENCODING A.A fi /\
             IS_VALID_ENCODED_INPUT A.A fi i i') ==>
        ((A_SEM i' (A_NDET (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A.A fi, A_TRUE))) = ALT_SEM A i)``,

    REWRITE_TAC[IS_VALID_ALTERNATING_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[A_SEM_def, ALT_SEM_def, ALT_ACCEPT_COND_SEM_def] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        PROVE_TAC[IS_VALID_ENCODED_INPUT_def],
        PROVE_TAC[DECOLLAPSED_RUN___IMPL_COLLAPSED___THM],
        PROVE_TAC[COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM]
    ]);



val NDET_TRUE___A_TRUE___EQ =
 store_thm
  ("NDET_TRUE___A_TRUE___EQ",

    ``!A fi i i'. (IS_VALID_ALTERNATING_AUTOMATON A /\ (A.AC = TRUE) /\
             IS_VALID_INPUT_ENCODING A.A fi /\
             IS_VALID_ENCODED_INPUT A.A fi i i') ==>
        ((A_SEM i' (A_NDET (EQ_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A.A fi, A_TRUE))) = ALT_SEM A i)``,

    REWRITE_TAC[IS_VALID_ALTERNATING_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[A_SEM_def, ALT_SEM_def, ALT_ACCEPT_COND_SEM_def] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        PROVE_TAC[IS_VALID_ENCODED_INPUT_def],
        `FINITE A.A.S` by FULL_SIMP_TAC std_ss [IS_VALID_ALTERNATING_SEMI_AUTOMATON_def] THEN
        `IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A.A fi) i' w` by
            PROVE_TAC[EQ_COLLAPSED_RUN___IMPLIES___IMPL_COLLAPSED_RUN] THEN
        PROVE_TAC[DECOLLAPSED_RUN___IMPL_COLLAPSED___THM],

        PROVE_TAC[COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM,
            IMPL_COLLAPSED_RUN___EQ_COLLAPSED_RUN___ENRICHMENT]
    ]);




val NDET_G___A_UNIVERSALLY_TOTAL_WEAK_CO_BUECHI___IMPL =
 store_thm
  ("NDET_G___A_UNIVERSALLY_TOTAL_WEAK_CO_BUECHI___IMPL",

    ``!A fi i i' ac. (IS_VALID_ALTERNATING_AUTOMATON A /\
            IS_UNIVERSALLY_TOTAL_ALTERNATING_SEMI_AUTOMATON A.A /\
            (A.AC = WEAK_CO_BUECHI ac) /\
             IS_VALID_INPUT_ENCODING A.A fi /\
             IS_VALID_ENCODED_INPUT A.A fi i i') ==>
        ((A_SEM i' (A_NDET (IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON A.A fi,
            ACCEPT_COND_G (P_NOT(P_PROP_DISJUNCTION (SET_TO_LIST ac)))))) = ALT_SEM A i)``,

    REWRITE_TAC[IS_VALID_ALTERNATING_AUTOMATON_def] THEN
    REPEAT STRIP_TAC THEN
    `ac SUBSET A.A.S` by PROVE_TAC[IS_VALID_ACCEPTANCE_COMPONENT_def] THEN
    `FINITE ac` by PROVE_TAC[SUBSET_FINITE,
       IS_VALID_ALTERNATING_SEMI_AUTOMATON_def] THEN
    ASM_SIMP_TAC std_ss [ALT_SEM_def, ALT_ACCEPT_COND_SEM_THM,
        ACCEPT_COND_G_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
        IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def, P_PROP_DISJUNCTION_SEM,
        MEM_SET_TO_LIST, symbolic_semi_automaton_REWRITES, A_SEM_def,
        ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, P_SEM_THM,
        EXISTS_MEM, IN_UNION, IN_DIFF] THEN
    SIMP_TAC std_ss [GSYM IMPL_COLLAPSED_ALTERNATING_SEMI_AUTOMATON_def] THEN

    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        PROVE_TAC[IS_VALID_ENCODED_INPUT_def],

        EXISTS_TAC ``DECOLLAPSED_RUN w`` THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[DECOLLAPSED_RUN___IMPL_COLLAPSED___THM],

            `~(w' n IN w n)` by PROVE_TAC[]  THEN
            `IS_REACHABLE_BY_RUN (w' n, n) (DECOLLAPSED_RUN w)` by
                PROVE_TAC[IS_PATH_THROUGH_RUN___IS_REACHABLE_BY_RUN] THEN
            PROVE_TAC[IS_REACHABLE_BY_DECOLLAPSED_RUN]
        ],

        EXISTS_TAC ``COLLAPSED_ALTERNATING_RUN r`` THEN
        REPEAT STRIP_TAC THENL [
            PROVE_TAC[COLLAPSED_ALTERNATING_RUN___IMPL_COLLAPSED___THM],

            SIMP_TAC std_ss [COLLAPSED_ALTERNATING_RUN_def, GSPECIFICATION] THEN
            Cases_on `s IN ac` THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THENL [
                `NO_EMPTY_SET_IN_RUN r` by
                    PROVE_TAC[UNIVERSALLY_TOTAL_NO_EMPTY_SET_IN_RUN] THEN
                PROVE_TAC[NO_EMPTY_SET_IN_RUN___PATH_THROUGH_RUN_AND_REACHABLE_STATE_EXISTS],

                PROVE_TAC[SUBSET_DEF]
            ]
        ]
    ]);








val _ = export_theory();
