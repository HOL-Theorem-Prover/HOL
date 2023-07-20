(******************************************************************************)
(*                                                                            *)
(*    Translations between explicit-state and symbolic (semi-)automata.       *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     pred_setTheory rich_listTheory set_lemmataTheory temporal_deep_mixedTheory pairTheory
     symbolic_kripke_structureTheory
     numLib semi_automatonTheory omega_automatonTheory kripke_structureTheory
     containerTheory relationTheory;

open Sanity;

val _ = hide "K";
val _ = hide "S";
val _ = hide "I";

val _ = new_theory "omega_automaton_translations";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = ParseExtras.temp_loose_equality()

val DETERMINISED_SEMI_AUTOMATON_def = Define
   `DETERMINISED_SEMI_AUTOMATON A =
     (semi_automaton (POW A.S) A.I
                     (\(s, i). i SUBSET A.I /\ !x. x IN s <=> (x, i) IN A.S0)
                     (\(s1, i, s2, i'). s1 SUBSET A.S /\ i SUBSET A.I /\
                        !x. x IN s2 = ?s1'. s1' IN s1 /\ (s1', i, x, i') IN A.R))`;

Theorem DETERMINISED_SEMI_AUTOMATON___IS_DET_TOTAL :
    !A. IS_DET_TOTAL_SEMI_AUTOMATON (DETERMINISED_SEMI_AUTOMATON A)
Proof
    SIMP_TAC std_ss [IS_DET_TOTAL_SEMI_AUTOMATON_def,
                    DETERMINISED_SEMI_AUTOMATON_def,
                    semi_automaton_REWRITES, SING,
                    IN_POW,
                    EXISTS_UNIQUE_THM,
                    INTER_SUBSET,
    prove(``!P s i i' s'. ((s, i, s', i') IN \(s, i, s', i'). P s i s' i') = P s i s' i'``,
          SIMP_TAC std_ss [IN_DEF]),
    prove(``!P s i. ((s, i) IN \(s, i). P s i) = P s i``,
          SIMP_TAC std_ss [IN_DEF])
    ] THEN
    rpt STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `\x. (x, i INTER A.I) IN A.S0` THEN
      SIMP_TAC std_ss [IN_DEF],

      ASM_SIMP_TAC std_ss [EXTENSION],

      Q_TAC EXISTS_TAC `\x. (?s1'. s1' IN s /\ (s1',i,x, i') IN A.R)` THEN
      SIMP_TAC std_ss [IN_DEF],

      METIS_TAC[EXTENSION]
    ]
QED

val SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE_def = Define
   `SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE (A:('a, 'a) semi_automaton) =
     (kripke_structure (A.S CROSS (POW A.I)) A.S0
                       (\((s1, i1),(s2, i2)). (s1, i1, s2, i2) IN A.R /\ i1 SUBSET A.I /\ i2 SUBSET A.I)
                       (A.S UNION A.I) (\(s,i). s INSERT i))`;

val SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE___IS_WELL_FORMED =
  store_thm (
    "SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE___IS_WELL_FORMED",
    ``!A. IS_WELL_FORMED_SEMI_AUTOMATON A ==>
          IS_WELL_FORMED_KRIPKE_STRUCTURE (SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE A)``,

    SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                    SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE_def,
                    kripke_structure_REWRITES, SUBSET_DEF,
                    IN_CROSS, IN_POW,
                    IS_WELL_FORMED_SEMI_AUTOMATON_def] THEN
    GEN_TAC THEN STRIP_TAC THEN
    STRIP_TAC THEN1 (
      PROVE_TAC[FINITE_CROSS, FINITE_POW_IFF]
    ) THEN
    STRIP_TAC THEN1 (
      ASM_SIMP_TAC std_ss [FINITE_UNION]
    ) THEN
    STRIP_TAC THEN1 (
      PROVE_TAC[]
    ) THEN
    STRIP_TAC THENL [
      GEN_TAC THEN
      Cases_on `x` THEN Cases_on `r` THEN Cases_on `q` THEN
      SIMP_ALL_TAC std_ss [IN_DEF] THEN
      METIS_TAC[FST, SND],

      Cases_on `s` THEN
      SIMP_TAC std_ss [IN_UNION, IN_INSERT] THEN
      PROVE_TAC[]
    ]);

val SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE___LANGUAGE_EQ =
  store_thm (
    "SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE___LANGUAGE_EQ",

    ``!A i p.
    IS_WELL_FORMED_SEMI_AUTOMATON A ==>
    (IS_RUN_THROUGH_SEMI_AUTOMATON A i p =
    IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE (SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE A)
      (\n. (p n, i n INTER A.I)))``,

    SIMP_TAC std_ss [SEMI_AUTOMATON_TO_KRIPKE_STRUCTURE_def,
                    kripke_structure_REWRITES,
                    IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                    IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                    IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                    IN_CROSS, IN_POW,
                    SUBSET_DEF, IS_WELL_FORMED_SEMI_AUTOMATON_def,
                    FORALL_AND_THM,
                    prove(``!x1 x2 x3 x4 P1 P2.
                            (((x1,x2),x3,x4) IN (\((x1,x2),x3,x4). P1 (x1,x2,x3,x4) /\ P2 x2 x4)) =
                            (P1 (x1,x2,x3,x4) /\ P2 x2 x4)``, SIMP_TAC std_ss [IN_DEF])] THEN
    rpt STRIP_TAC THEN
    rpt BOOL_EQ_STRIP_TAC THEN
    METIS_TAC[FST, SND]);

val SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def = Define
   `SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON (A:'a symbolic_semi_automaton) I =
     (semi_automaton (POW A.S) I
                     (\(s, i). s SUBSET A.S /\ i SUBSET I /\
                               P_SEM (s UNION (i DIFF A.S)) A.S0)
                     (\(s1, i, s2, i'). s1 SUBSET A.S /\ s2 SUBSET A.S /\ i SUBSET I /\ i' SUBSET I /\
                                        XP_SEM A.R ((s1 UNION (i DIFF A.S)), s2 UNION (i' DIFF A.S))))`;

val SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___IS_WELL_FORMED =
  store_thm (
    "SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___IS_WELL_FORMED",

    ``!A I. (FINITE A.S /\ FINITE I) ==>
          IS_WELL_FORMED_SEMI_AUTOMATON (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A I)``,


    SIMP_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def,
                    SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def,
                    semi_automaton_REWRITES,
                    FINITE_POW_IFF, SUBSET_DEF, IN_POW,
                    IN_CROSS, FORALL_PROD] THEN
    SIMP_TAC std_ss [IN_DEF]);

val SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___LANGUAGE_EQ =
  store_thm (
    "SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___LANGUAGE_EQ",

    ``!A I i w. (!n. (i n INTER (SEMI_AUTOMATON_USED_INPUT_VARS A)) SUBSET I) ==>

    (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
    IS_RUN_THROUGH_SEMI_AUTOMATON (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A I) i w)``,

    rpt STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [ IS_TRANSITION_def,
                          IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                          IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                          SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def,
                          semi_automaton_REWRITES,
                          PATH_SUBSET_def,
                          IN_POW, INTER_SUBSET,
                          IN_ABS,
                          INPUT_RUN_STATE_UNION_def,
                          INPUT_RUN_PATH_UNION_def,
                          prove (``!f x1 x2 x3 x4. (x1,x2,x3,x4) IN (\(s1,s2,s3,s4). f s1 s2 s3 s4) = f x1 x2 x3 x4``, SIMP_TAC std_ss [IN_DEF]),
                          prove (``!f x1 x2. (x1,x2) IN (\(s1,s2). f s1 s2) = f x1 x2 ``, SIMP_TAC std_ss [IN_DEF])] THEN
    rpt BOOL_EQ_STRIP_TAC THEN
    REMAINS_TAC `!n. (((w n UNION (i n DIFF A.S)) INTER (XP_USED_VARS A.R)) =
                ((w n UNION ((i n INTER I) DIFF A.S)) INTER (XP_USED_VARS A.R))) /\
                (((w n UNION (i n DIFF A.S)) INTER (P_USED_VARS A.S0)) =
                ((w n UNION ((i n INTER I) DIFF A.S)) INTER (P_USED_VARS A.S0)))` THEN1 (
      BINOP_TAC THENL [
        METIS_TAC[P_USED_VARS_INTER_THM], METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_REFL]
      ]
    ) THEN
    SIMP_ALL_TAC std_ss [EXTENSION, SUBSET_DEF, IN_INTER,
                        IN_UNION, IN_DIFF,
                        SEMI_AUTOMATON_USED_INPUT_VARS_def,
                        XP_USED_VARS_def] THEN
    rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN
    METIS_TAC[]);

(*=============================================================================
= Connection to kripke_structures
=============================================================================*)

val SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE_def = Define
   `SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE (A:'a symbolic_semi_automaton) =
    symbolic_kripke_structure A.S0 A.R`;

val SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE___RUN =
 store_thm
  ("SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE___RUN",
    ``!A i w.
        ((IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) =
        ((PATH_SUBSET w A.S) /\
        IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE (SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE A) (INPUT_RUN_PATH_UNION A i w)))``,

      SIMP_TAC std_ss [PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE_def,
        symbolic_kripke_structure_REWRITES,
        IS_TRANSITION_def,
        INPUT_RUN_PATH_UNION_def] THEN
      PROVE_TAC[]);

val SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE___INITIAL_PATH =
 store_thm
  ("SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE___INITIAL_PATH",
    ``!A i.
        IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE (SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE A) i =
        (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i (PATH_RESTRICT i A.S))``,

      SUBGOAL_TAC `!a b. ((a INTER b) UNION (a DIFF b)) = a` THEN1 (
        SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN
        PROVE_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE_def,
        symbolic_kripke_structure_REWRITES,
        IS_TRANSITION_def,
        INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def,
        PATH_RESTRICT_def, PATH_MAP_def,
        PATH_SUBSET_def, INTER_SUBSET] THEN
      PROVE_TAC[]);

val SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT_def =
 Define
  `SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT K A =
    SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT K (SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE A)`;


val SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT =
 store_thm
  ("SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT",
  ``!K A. SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT K A =
          symbolic_kripke_structure (P_AND(K.S0, A.S0)) (XP_AND(K.R, A.R))``,

    SIMP_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE___WITH___SEMI_AUTOMATON___PRODUCT_def,
                     SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT_def,
                     SYMBOLIC_SEMI_AUTOMATON___TO___KRIPKE_STRUCTURE_def,
                     symbolic_kripke_structure_REWRITES]);

(* Rabin-Scott subset construction from NDET A to DET A',

   Set of states of A is determinized by f into a state of A' (of the same type)
 *)
val IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def = Define
   `IS_RABIN_SCOTT_SUBSET_CONSTRUCTION (A  :'a symbolic_semi_automaton)
                                       (A' :'a symbolic_semi_automaton)
                                       (IV :'a set)
                                       (f  :'a set -> 'a)
                                       (g  :'a -> 'a set)
    = ((INJ f (POW A.S) UNIV /\ DISJOINT (IMAGE f (POW A.S)) IV) /\
       (!(z:'a set). z SUBSET A.S ==> (g(f(z)) = z)) /\
       (A'.S = IMAGE f (POW A.S)) /\
       (!i Z. Z SUBSET A'.S ==>
             (P_SEM (INPUT_RUN_STATE_UNION A' i Z) A'.S0 <=>
              (Z = {z | z IN A'.S /\ P_SEM (INPUT_RUN_STATE_UNION A i (g z)) A.S0}))) /\
       !(S1 :'a set) (S2 :'a set) (i1 :'a set) (i2 :'a set).
         S1 SUBSET A'.S /\ S2 SUBSET A'.S ==>
        (IS_TRANSITION A' S1 i1 S2 i2 <=>
         (S2 = {s2 | s2 IN A'.S /\ ?s1. s1 IN S1 /\ IS_TRANSITION A (g s1) i1 (g s2) i2})))`;

(* Rabin-Scott subset construction algorithm, by Sven Lamberti *)
val RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_def = Define
   `RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON A f =
      symbolic_semi_automaton
        (IMAGE f (POW A.S))
        (P_FORALL (SET_TO_LIST A.S) (P_EQUIV(A.S0, VAR_RENAMING_HASHTABLE A.S f)))
        (XP_NEXT_FORALL (SET_TO_LIST A.S)
          (XP_EQUIV (XP_NEXT (VAR_RENAMING_HASHTABLE A.S f),
                     XP_CURRENT_EXISTS (SET_TO_LIST A.S)
                        (XP_AND(A.R, XP_CURRENT (VAR_RENAMING_HASHTABLE A.S f))))))`;

(* Rabin-Scott subset construction: main theorem, by Sven Lamberti *)
Theorem RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_THM :
    !A A' IV f g.
      (FINITE A.S /\ (A' = RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON A f) /\
       (INJ f (POW A.S) UNIV /\ DISJOINT (IMAGE f (POW A.S)) IV /\
        DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A)) /\
       (!(z:'a set). z SUBSET A.S ==> (g(f(z)) = z))) ==>
      IS_RABIN_SCOTT_SUBSET_CONSTRUCTION (A  :'a symbolic_semi_automaton)
                                         (A' :'a symbolic_semi_automaton)
                                         (IV:'a set) (f:'a set->'a) (g:'a -> 'a set)
Proof
    rpt GEN_TAC
 >> ONCE_ASM_REWRITE_TAC [GSYM SYMBOLIC_SEMI_AUTOMATON___REWRITE]
 >> REWRITE_TAC [symbolic_semi_automaton_11, SYMBOLIC_SEMI_AUTOMATON___REWRITE]
 >> rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def,
                          RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_def,
                          SEMI_AUTOMATON_USED_VARS_def,
                          SEMI_AUTOMATON_USED_INPUT_VARS_def, symbolic_semi_automaton_REWRITES]
 >> FULL_SIMP_TAC std_ss [DISJOINT_UNION_BOTH]
 >> FULL_SIMP_TAC std_ss [DISJOINT_DIFF_ELIM, DISJOINT_UNION_BOTH]
 >> SUBGOAL_TAC `!s. ~(f (s INTER A.S) IN A.S)`
 >- (FULL_SIMP_TAC std_ss [DISJOINT_DEF, IMAGE_DEF, EXTENSION, IN_POW,
                           IN_INTER, NOT_IN_EMPTY, GSPECIFICATION] \\
     PROVE_TAC [INTER_SUBSET])
 >> `!s s'. s' SUBSET A.S ==> ~(f (s INTER A.S) IN s')` by PROVE_TAC [SUBSET_DEF]
 >> SUBGOAL_TAC
       `!l'' i s. ((f:'a set->'a) (l'' INTER A.S) IN (INPUT_RUN_STATE_UNION A' i s)) =
                  (f (l'' INTER A.S) IN s)`
 >- (ASM_SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF, IN_IMAGE, IN_POW] \\
     PROVE_TAC [INTER_SUBSET])
 >> SUBGOAL_TAC `!l. l SUBSET A.S ==> ((l INTER A.S) = l)`
 >- (SIMP_TAC std_ss [SUBSET_DEF, EXTENSION, IN_INTER] >> PROVE_TAC [])
 >> SUBGOAL_TAC `!s s' s''. (s DIFF s'' UNION s') INTER s'' = s' INTER s''`
 >- (SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] >> PROVE_TAC [])
 >> SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_POW]
 >> rpt STRIP_TAC
 >| [ ASM_SIMP_TAC std_ss [P_FORALL_SEM, SET_TO_LIST_INV, VAR_RENAMING_HASHTABLE_SEM,
                           P_SEM_THM, IN_DIFF, EXTENSION, GSPECIFICATION, IN_UNION] \\
      SUBGOAL_TAC `!l'. P_SEM (INPUT_RUN_STATE_UNION A' i Z DIFF A.S UNION l') A.S0 =
                        P_SEM (INPUT_RUN_STATE_UNION A i l') A.S0` THEN1 (
        ONCE_REWRITE_TAC [P_USED_VARS_INTER_THM] THEN
        rpt GEN_TAC THEN
        REMAINS_TAC `(INPUT_RUN_STATE_UNION A' i Z DIFF A.S UNION l') INTER P_USED_VARS A.S0 =
                     (INPUT_RUN_STATE_UNION A i l') INTER P_USED_VARS A.S0` THEN1 (
          ASM_SIMP_TAC std_ss []
        ) THEN
        UNDISCH_HD_TAC THEN
        SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF,
          IN_IMAGE, IN_POW, SUBSET_DEF, GSYM SUBSET_COMPL_DISJOINT, IN_COMPL] THEN
        rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
    ) THEN

    ASM_REWRITE_TAC[] THEN
    EQ_TAC THEN rpt STRIP_TAC THENL [
        EQ_TAC THEN rpt STRIP_TAC THENL [
            METIS_TAC[],

            `?l':'a set. l' SUBSET A.S /\ ((x:'a) = f l')` by PROVE_TAC [SUBSET_DEF, IN_IMAGE,
                IN_POW] THEN
            METIS_TAC[],

            METIS_TAC[SUBSET_DEF]
        ],

        METIS_TAC[SUBSET_DEF]
    ],


    ASM_SIMP_TAC std_ss [IS_TRANSITION_def, XP_CURRENT_FORALL_SEM,
        XP_NEXT_FORALL_SEM, XP_CURRENT_EXISTS_SEM, VAR_RENAMING_HASHTABLE_SEM,
        MEM_SET_TO_LIST, SET_TO_LIST_INV, XP_SEM___XP_NEXT, XP_SEM___XP_CURRENT, IN_UNION,
        IN_DIFF, EXTENSION, GSPECIFICATION, XP_SEM_THM] THEN
    SUBGOAL_TAC `!l' l''. XP_SEM A.R
                (INPUT_RUN_STATE_UNION A' i1 S1 DIFF A.S UNION l',
                INPUT_RUN_STATE_UNION A' i2 S2 DIFF A.S UNION l'') =
                XP_SEM A.R (INPUT_RUN_STATE_UNION A i1 l', INPUT_RUN_STATE_UNION A i2 l'')` THEN1 (
        ONCE_REWRITE_TAC [XP_USED_VARS_INTER_THM] THEN

        rpt GEN_TAC THEN
        REMAINS_TAC `((INPUT_RUN_STATE_UNION A' i1 S1 DIFF A.S UNION l') INTER XP_USED_CURRENT_VARS A.R =
                      (INPUT_RUN_STATE_UNION A i1 l') INTER XP_USED_CURRENT_VARS A.R) /\
                     ((INPUT_RUN_STATE_UNION A' i2 S2 DIFF A.S UNION l'') INTER XP_USED_X_VARS A.R =
                      (INPUT_RUN_STATE_UNION A i2 l'') INTER XP_USED_X_VARS A.R)` THEN1 (
          ASM_REWRITE_TAC[]
        ) THEN
        FULL_SIMP_TAC std_ss [EXTENSION, IN_INTER, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF,
          IN_IMAGE, IN_POW, SUBSET_DEF, GSYM SUBSET_COMPL_DISJOINT, IN_COMPL,
          XP_USED_VARS_def] THEN
        METIS_TAC[]
    ) THEN
    ASM_SIMP_TAC std_ss [] THEN
    EQ_TAC THEN rpt STRIP_TAC THENL [
        EQ_TAC THEN rpt STRIP_TAC THENL [
            METIS_TAC[],

            `?l':'a set. l' SUBSET A.S /\ ((x:'a) = f l')` by PROVE_TAC [SUBSET_DEF, IN_IMAGE,
                IN_POW] THEN
            METIS_TAC[],


            `?l':'a set. l' SUBSET A.S /\ ((s1:'a) = f l')` by PROVE_TAC [SUBSET_DEF, IN_IMAGE] THEN
            `x' SUBSET A.S` by PROVE_TAC[SUBSET_DEF] THEN
            METIS_TAC[]
        ],


        ASM_REWRITE_TAC[] THEN
        SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
        SUBGOAL_TAC `!x. ((f l' = f x) /\ x SUBSET A.S) = (x = l')` THEN1 (
          METIS_TAC [INJ_DEF, IN_POW, IN_UNIV]
        ) THEN
        ASM_SIMP_TAC std_ss [] THEN
        METIS_TAC[SUBSET_DEF]
    ]
]
QED

val RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON___USED_INPUT_VARS =
  store_thm (
    "RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON___USED_INPUT_VARS",
    ``!A f. (FINITE A.S /\
             DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A))    ==>
    (SEMI_AUTOMATON_USED_INPUT_VARS
      (RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON A f) =
    SEMI_AUTOMATON_USED_INPUT_VARS A)``,

    rpt GEN_TAC THEN
    ASM_SIMP_TAC std_ss [RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_def,
      SEMI_AUTOMATON_USED_INPUT_VARS_def,
      symbolic_semi_automaton_REWRITES,
      P_USED_VARS_EVAL, XP_USED_VARS_EVAL,
      XP_COND_def, P_BIGOR___P_USED_VARS,
      P_FORALL___P_USED_VARS, VAR_RENAMING_HASHTABLE_def,
      XP_FORALL___XP_USED_VARS,
      XP_EXISTS___XP_USED_VARS,
      XP_USED_VARS_def,
      XP_USED_VARS_EVAL,
      XP_BIGOR___XP_USED_VARS,
      SET_TO_LIST_INV, UNION_EMPTY,
      P_PROP_SET_MODEL___P_USED_VARS] THEN

    ONCE_REWRITE_TAC[EXTENSION] THEN
    rpt STRIP_TAC THEN

    ASM_SIMP_TAC std_ss [IN_UNION, IN_DIFF,
      IN_LIST_BIGUNION, MEM_MAP, GSYM LEFT_EXISTS_AND_THM,
      MEM_SET_TO_LIST, FINITE_POW_IFF, IMAGE_FINITE,
      IN_IMAGE, P_USED_VARS_EVAL, IN_SING,
      XP_USED_VARS_EVAL,
      IN_POW,
      P_PROP_SET_MODEL___P_USED_VARS, NOT_IN_EMPTY] THEN

    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_POW,
      IN_IMAGE, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION,
      XP_USED_VARS_def] THEN

    EQ_TAC THEN rpt STRIP_TAC THEN
    METIS_TAC[SUBSET_DEF, IN_UNION]);

val RABIN_SCOTT_SUBSET_CONSTRUCTION___EXISTS =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___EXISTS",
   ``!A IV. (INFINITE (UNIV:'a set) /\ FINITE A.S /\ FINITE (IV:'a set)) ==> (?f g A'. IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g)``,

   rpt STRIP_TAC THEN

   `?f. INJ f (POW A.S) UNIV /\ (DISJOINT (IMAGE f (POW A.S)) (IV UNION (SEMI_AUTOMATON_USED_INPUT_VARS A) UNION A.S))`
      by METIS_TAC[POW_VARRENAMING_EXISTS,
                   FINITE___SEMI_AUTOMATON_USED_INPUT_VARS, FINITE_UNION] THEN
   SUBGOAL_THEN ``?g:('a -> 'a set). (!(z:'a set). ((z SUBSET (A:'a symbolic_semi_automaton).S) ==> (g(f(z)) = z)))`` STRIP_ASSUME_TAC THEN1 (
      EXISTS_TAC ``\z:'a. @x:'a set. ((x SUBSET (A:'a symbolic_semi_automaton).S) /\ (f x = z))`` THEN
      rpt STRIP_TAC THEN
      SIMP_TAC std_ss [] THEN
      SELECT_ELIM_TAC THEN
      rpt STRIP_TAC THENL [
         METIS_TAC[],

         `x IN (POW A.S)` by METIS_TAC[IN_POW] THEN
         `z IN (POW A.S)` by METIS_TAC[IN_POW] THEN
         METIS_TAC[INJ_DEF]
      ]
   ) THEN

   EXISTS_TAC ``f:'a set->'a`` THEN
   EXISTS_TAC ``g:'a -> 'a set`` THEN

   SUBGOAL_TAC `(DISJOINT (IMAGE f (POW A.S)) IV) /\
     (DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A))` THEN1 (

        FULL_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, DISJOINT_UNION_BOTH, DISJOINT_SYM]
   ) THEN

   PROVE_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_THM]);

val RABIN_SCOTT_SUBSET_CONSTRUCTION___IS_TOTAL_DET =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___IS_TOTAL_DET",
   ``!A A' IV f g. IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g ==>
    IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A'``,

SIMP_TAC std_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def,
    IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_THM] THEN
rpt STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [EXISTS_UNIQUE_DEF] THEN
    rpt STRIP_TAC THENL [

        `?Z. Z = {z | z IN A'.S /\ P_SEM (INPUT_RUN_STATE_UNION A i (g z)) A.S0}` by PROVE_TAC[] THEN
        SUBGOAL_TAC `Z SUBSET A'.S` THEN1 (
          ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
        ) THEN
        EXISTS_TAC ``Z:'a set`` THEN
        rpt STRIP_TAC THEN1 PROVE_TAC[] THEN
        ASM_SIMP_TAC std_ss [],

        METIS_TAC[]
    ],

    FULL_SIMP_TAC std_ss [EXISTS_UNIQUE_DEF] THEN
    rpt STRIP_TAC THENL [

        ONCE_REWRITE_TAC[TRANSITION_CURRENT_STATE_CLEANING] THEN
        `?S1. s1 INTER A'.S = S1` by PROVE_TAC[] THEN
        `?i1'. i1 UNION s1 = i1'` by PROVE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN

        `?S2. S2 = {s2 | s2 IN A'.S /\ ?s1'. s1' IN S1 /\
           IS_TRANSITION A (g s1') i1' (g s2) i2}` by PROVE_TAC[] THEN
        SUBGOAL_TAC `S1 SUBSET A'.S /\ S2 SUBSET A'.S` THEN1 (
          GSYM_NO_TAC 2 THEN
          ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_INTER]
        ) THEN
        EXISTS_TAC ``S2:'a set`` THEN

        rpt STRIP_TAC THEN1 PROVE_TAC[] THEN
        ASM_SIMP_TAC std_ss [],

        METIS_TAC[TRANSITION_CURRENT_STATE_CLEANING, INTER_SUBSET]
    ]
]);

val RABIN_SCOTT_SUBSET_CONSTRUCTION___UNIQUE_RUN =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___UNIQUE_RUN",
   ``!A A' IV f g. (IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g) ==>
                   (!i. ?!w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w)``,

   rpt STRIP_TAC THEN
   `IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A'` by PROVE_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION___IS_TOTAL_DET] THEN
   PROVE_TAC[TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]);

val RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN",
   ``!A A' IV f g i w'. (IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g) ==> (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w' =
            ((w' 0 = {z |
            z IN A'.S /\ P_SEM (INPUT_RUN_STATE_UNION A (i 0) (g z)) A.S0}) /\
            (!n. w' (SUC n) = {s2 |
               s2 IN A'.S /\
               ?s1. s1 IN (w' n) /\ IS_TRANSITION A (g s1) (i n) (g s2) (i (SUC n))})))``,

    REWRITE_TAC [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        PATH_SUBSET_def, INPUT_RUN_PATH_UNION_def] THEN
    rpt STRIP_TAC THEN EQ_TAC THENL [
        METIS_TAC[],

        STRIP_TAC THEN
        SUBGOAL_TAC `(!n. w' n SUBSET A'.S)` THEN1 (
            Cases_on `n` THEN
            ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
        ) THEN
        METIS_TAC[]
    ]);

val RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_SUBSET =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_SUBSET",
   ``!A A' IV f g i w w'. ((IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g) /\
                           IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w /\ IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w') ==>
     (!n. (f (w n)) IN w' n)``,

   rpt STRIP_TAC THEN
    `(w' 0 = {z | z IN A'.S /\
                   P_SEM (INPUT_RUN_STATE_UNION A (i 0) (g z)) A.S0}) /\
      (!n. w' (SUC n) = {s2 | s2 IN A'.S /\
               ?s1. s1 IN (w' n) /\ IS_TRANSITION A (g s1) (i n) (g s2) (i (SUC n))})` by
       METIS_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN] THEN
   Induct_on `n` THEN (
       FULL_SIMP_TAC std_ss [IN_POW,
            IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def, GSPECIFICATION, IN_IMAGE,
            IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def, PATH_SUBSET_def] THEN
       METIS_TAC[]
    ));

val RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_REACHABLE =
 store_thm
  ("RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_REACHABLE",
   ``!A A' IV f g i w'. ((IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g) /\  IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w') ==>
     (!n s. (f s IN w' n /\ s SUBSET A.S) = (?w. (PATH_SUBSET w A.S) /\ P_SEM (INPUT_RUN_PATH_UNION A i w 0) A.S0 /\ (w n = s) /\ !m. m < n ==> (IS_TRANSITION A (w m) (i m) (w (SUC m)) (i (SUC m)))))``,

    rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def,
            IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def] THEN
        UNDISCH_HD_TAC THEN UNDISCH_HD_TAC THEN
        SPEC_TAC (``s:'a set``, ``s:'a set``) THEN
        Induct_on `n` THEN
        rpt STRIP_TAC THENL [
            EXISTS_TAC ``\n:num. (s:'a set)`` THEN
            FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def] THEN
            `w' 0 = {z |
               z IN A'.S /\ P_SEM (INPUT_RUN_STATE_UNION A (i 0) (g z)) A.S0}` by
                METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
            PROVE_TAC[EXTENSION],


            rpt STRIP_TAC THEN
            `(!n. w' (SUC n) = {s2 | s2 IN A'.S /\
               ?s1. s1 IN (w' n) /\ IS_TRANSITION A (g s1) (i n) (g s2) (i (SUC n))})` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
            `s1 IN (IMAGE f (POW A.S))` by PROVE_TAC[SUBSET_DEF] THEN
            SUBGOAL_TAC `?s1':'a set. (s1' SUBSET A.S) /\ (s1 = f (s1'))` THEN1 (
                REWRITE_ASSUMPTIONS_TAC [IN_IMAGE, IN_POW] THEN
                PROVE_TAC[]
            ) THEN
            FULL_SIMP_TAC std_ss [] THEN

            `?w. (!n. w n SUBSET A.S) /\
               P_SEM (INPUT_RUN_PATH_UNION A i w 0) A.S0 /\ (w n = s1') /\
               !m.
                 m < n ==>
                 IS_TRANSITION A (w m) (i m) (w (SUC m)) (i (SUC m))` by METIS_TAC[EXTENSION] THEN
            EXISTS_TAC ``\m:num. if (m = SUC n) then (s:'a set) else (w m)`` THEN
            rpt STRIP_TAC THENL [
                METIS_TAC[],

                FULL_SIMP_TAC arith_ss [INPUT_RUN_PATH_UNION_def],
                SIMP_TAC std_ss [],

                Cases_on `m < n` THENL [
                    FULL_SIMP_TAC arith_ss [],

                    `m = n` by DECIDE_TAC THEN
                    METIS_TAC[EXTENSION]
                ]
            ]
        ],

        UNDISCH_HD_TAC THEN UNDISCH_HD_TAC THEN
        SPEC_TAC (``s:'a set``, ``s:'a set``) THEN
        SIMP_TAC std_ss [] THEN
        `(w' 0 = {z | z IN A'.S /\
                   P_SEM (INPUT_RUN_STATE_UNION A (i 0) (g z)) A.S0}) /\
        (!n. w' (SUC n) = {s2 | s2 IN A'.S /\
                ?s1. s1 IN (w' n) /\ IS_TRANSITION A (g s1) (i n) (g s2) (i (SUC n))})` by
        METIS_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN] THEN

        Induct_on `n` THENL [
            FULL_SIMP_TAC arith_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def,
             INPUT_RUN_PATH_UNION_def, IN_POW, GSPECIFICATION, IN_IMAGE, PATH_SUBSET_def] THEN
            PROVE_TAC[],

            rpt STRIP_TAC THEN
            FULL_SIMP_TAC arith_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def, IN_IMAGE, PATH_SUBSET_def,
             INPUT_RUN_PATH_UNION_def, IN_POW, GSPECIFICATION] THEN

            `n < SUC n /\ (!m. m < n ==> m < SUC n)` by DECIDE_TAC THEN
            METIS_TAC[]
        ],

        PROVE_TAC[PATH_SUBSET_def]
   ]);

val SYMBOLIC___TOTAL_UNIV_G___TO___DET_G___THM =
  store_thm ("SYMBOLIC___TOTAL_UNIV_G___TO___DET_G___THM",

``!A A' IV f g p p'.
(IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A /\
IS_RABIN_SCOTT_SUBSET_CONSTRUCTION A A' IV f g /\
(!i s. s SUBSET A'.S ==>
  ((P_SEM (INPUT_RUN_STATE_UNION A' i s) p') =
     !s'. s' IN IMAGE g (s INTER (IMAGE f (POW A.S))) ==>
         P_SEM (INPUT_RUN_STATE_UNION A i s') p))
) ==>
!i.
(A_SEM i (A_UNIV (A, ACCEPT_COND_G p)) =
A_SEM i (A_UNIV (A', ACCEPT_COND_G p')))``,


rpt STRIP_TAC THEN
SIMP_TAC std_ss [A_SEM_THM, ACCEPT_COND_G_def, ACCEPT_COND_SEM_def,
  ACCEPT_COND_SEM_TIME_def] THEN
EQ_TAC THEN rpt STRIP_TAC THEN rename1 `INPUT_RUN_PATH_UNION _ i w t` THENL [
  ASSUME_TAC RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_REACHABLE THEN
  Q_SPECL_NO_ASSUM 0 [`A`, `A'`, `IV`, `f`, `g`, `i`, `w`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN
  ASM_REWRITE_TAC[] THEN

  `IMAGE f (POW A.S) = A'.S` by
    FULL_SIMP_TAC std_ss [IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def] THEN
  `PATH_SUBSET w A'.S` by PROVE_TAC[IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
  SUBGOAL_TAC `INPUT_RUN_PATH_UNION A' i w t' INTER IMAGE f (POW A.S) =
               w t'` THEN1 (
    ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
    FULL_SIMP_TAC std_ss [PATH_SUBSET_def, INPUT_RUN_PATH_UNION_def,
      INPUT_RUN_STATE_UNION_def, SUBSET_DEF, IN_INTER, IN_UNION, IN_DIFF] THEN
    METIS_TAC[]
  ) THEN
  `w t SUBSET A'.S` by PROVE_TAC[PATH_SUBSET_def] THEN
  ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def] THEN
  NTAC 2 WEAKEN_HD_TAC THEN

  SIMP_TAC std_ss [IN_IMAGE, IN_INTER] THEN
  rpt STRIP_TAC THEN
  `x IN IMAGE f (POW A.S)` by METIS_TAC[] THEN
  FULL_SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
  `g (f x') = x'` by METIS_TAC[IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def] THEN
  ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

  REMAINS_TAC `?v. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i v /\ (v t = x')` THEN1 (
    METIS_TAC[INPUT_RUN_PATH_UNION_def]
  ) THEN

  Q_SPECL_NO_ASSUM 7 [`t`, `x'`] THEN
  UNDISCH_HD_TAC THEN FULL_SIMP_TAC std_ss [] THEN STRIP_TAC THEN
  ASSUME_TAC TOTAL_SYMBOLIC_SEMI_AUTOMATON_TRANS_FUNC THEN
  Q_SPEC_NO_ASSUM 0 `A` THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN

  SIMP_ALL_TAC std_ss [] THEN

  `?v'. v' = CHOOSEN_PATH {x'} (\s1 n. {R_FUNC s1 (i (PRE n + t)) (i (n + t))})` by METIS_TAC[] THEN

  Q_TAC EXISTS_TAC `\t2. if (t2 <= t) then w' t2 else v' (t2-t)` THEN

  FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def,
   INPUT_RUN_PATH_UNION_def] THEN
  rpt STRIP_TAC THENL [
    Cases_on `t2 <= t` THEN ASM_REWRITE_TAC[] THEN
    Q.ABBREV_TAC `t3 = t2 - t` THEN
    WEAKEN_HD_TAC THEN
    Induct_on `t3` THEN (
       ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING]
    ),

    Cases_on `SUC t2 <= t` THEN ASM_SIMP_TAC arith_ss [] THEN
    Cases_on `t2 = t` THENL [
      `SUC t - t = SUC 0` by DECIDE_TAC THEN
      `1 + t = SUC t` by DECIDE_TAC THEN
      ASM_REWRITE_TAC [CHOOSEN_PATH_def] THEN
      ASM_SIMP_TAC std_ss [IN_SING],

      ASM_SIMP_TAC arith_ss [] THEN
      `(SUC t2 - t = SUC (t2 - t)) /\
       (t + (t2 - t) = t2) /\
       ((SUC (t2 - t) + t) = SUC t2)` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING]
    ]
  ],

  `?w'. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w'` by
    METIS_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION___UNIQUE_RUN,
              EXISTS_UNIQUE_THM] THEN
  `P_SEM (INPUT_RUN_PATH_UNION A' i w' t) p'` by PROVE_TAC[] THEN
  WEAKEN_NO_TAC 3 THEN
  UNDISCH_HD_TAC THEN
  ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def] THEN
  rpt STRIP_TAC THEN

  `w' t SUBSET A'.S` by
    METIS_TAC[IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
              PATH_SUBSET_def] THEN
  REMAINS_TAC `w t IN IMAGE g (w' t INTER IMAGE f (POW A.S))` THEN1 METIS_TAC[] THEN
  WEAKEN_HD_TAC THEN

  `f (w t) IN w' t` by METIS_TAC[
    RABIN_SCOTT_SUBSET_CONSTRUCTION___RUN_SUBSET] THEN

  SIMP_TAC std_ss [IN_IMAGE, IN_INTER, IN_POW] THEN
  Q_TAC EXISTS_TAC `f (w t)` THEN

  FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def,
   IS_RABIN_SCOTT_SUBSET_CONSTRUCTION_def] THEN
  METIS_TAC[]
]);

val SYMBOLIC___TOTAL_UNIV_G___TO___DET_G___CONCRETE_THM =
  store_simp_thm ("SYMBOLIC___TOTAL_UNIV_G___TO___DET_G___CONCRETE_THM",
``!A p f A' p'.
  (FINITE A.S /\
   IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A /\
  (A' = RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON A f) /\
  (p' = (P_FORALL (SET_TO_LIST A.S) (P_IMPL( VAR_RENAMING_HASHTABLE A.S f, p)))) /\
  INJ f (POW A.S) UNIV /\
  DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A UNION P_USED_VARS p)) ==>

((!i.
(A_SEM i (A_UNIV (A, ACCEPT_COND_G p)) =
A_SEM i (A_UNIV (A', ACCEPT_COND_G p')))) /\
IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A')``,


rpt GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_TAC `?g. !x. (x SUBSET A.S) ==> (g (f x) = x)` THEN1 (
  PROVE_TAC[INJ_INVERSE, IN_POW]
) THEN

ASSUME_TAC RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_THM THEN
Q_SPECL_NO_ASSUM 0 [`A`, `A'`, `EMPTY`, `f`, `g`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
  METIS_TAC[DISJOINT_UNION_BOTH]
) THEN

STRIP_TAC THENL [
  ALL_TAC,
  PROVE_TAC[RABIN_SCOTT_SUBSET_CONSTRUCTION___IS_TOTAL_DET]
] THEN
MATCH_MP_TAC SYMBOLIC___TOTAL_UNIV_G___TO___DET_G___THM THEN

EXISTS_TAC ``EMPTY`` THEN
Q_TAC EXISTS_TAC `f` THEN
Q_TAC EXISTS_TAC `g` THEN
ASM_REWRITE_TAC[] THEN

ASM_SIMP_TAC std_ss [P_FORALL_SEM,
  SET_TO_LIST_INV, P_SEM_THM,
  VAR_RENAMING_HASHTABLE_SEM,
  RABIN_SCOTT_SUBSET_CONSTRUCTION_AUTOMATON_def,
  symbolic_semi_automaton_REWRITES,
  INPUT_RUN_STATE_UNION_def] THEN
rpt STRIP_TAC THEN

SUBGOAL_TAC `!l'. (l' SUBSET A.S) ==>
  ((s UNION (i DIFF IMAGE f (POW A.S)) DIFF A.S UNION l') INTER A.S = l')` THEN1 (
  SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, SUBSET_DEF] THEN
  METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

SUBGOAL_TAC `!l'. (l' SUBSET A.S) ==>
((f l' IN s UNION (i DIFF IMAGE f (POW A.S)) DIFF A.S UNION l') = (f l' IN s))` THEN1 (
  SIMP_ALL_TAC std_ss [EXTENSION, SUBSET_DEF, IN_UNION, IN_DIFF,
    IN_IMAGE, IN_POW, DISJOINT_DISJ_THM,
    SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
  METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

FORALL_EQ_STRIP_TAC THEN

SIMP_TAC std_ss [IN_IMAGE, IN_INTER, IN_POW,
  GSYM RIGHT_EXISTS_AND_THM] THEN

`(?x'. (l' = g (f x')) /\ f x' IN s /\ x' SUBSET A.S) =
 (l' SUBSET A.S /\ f l' IN s)` by METIS_TAC[] THEN
ASM_REWRITE_TAC[AND_IMP_INTRO] THEN WEAKEN_HD_TAC THEN
rpt BOOL_EQ_STRIP_TAC THEN

ONCE_REWRITE_TAC [P_USED_VARS_INTER_THM] THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
  IN_IMAGE, IN_POW] THEN
rpt STRIP_TAC THEN
rpt BOOL_EQ_STRIP_TAC THEN

SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_UNION, SUBSET_DEF,
  IN_IMAGE, IN_POW] THEN
METIS_TAC[]);

val NDET_F___TO___NDET_FG___THM =
 store_simp_thm
  ("NDET_F___TO___NDET_FG___THM",

    ``!A A' p i.
            (IS_EXPLICIT_PROP_ACCEPT_COND p /\
              EXPLICIT_ACCEPT_COND_USED_INPUT_VARS p SUBSET A.I /\
            (A' = (semi_automaton (A.S CROSS UNIV:bool set) A.I
                  (\((s, a),i). ((a = F) /\ ((s, i) IN A.S0)))
                  (\((s1, b1), i, (s2, b2), i'). (s1, i, s2, i') IN A.R /\
                    (b2 = (b1 \/ EXPLICIT_PROP_ACCEPT_COND_SEM i s1 p)))))) ==>

            ((EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, EXPLICIT_ACCEPT_F p) i) =
              (EXISTENTIAL_OMEGA_AUTOMATON_SEM (A', EXPLICIT_ACCEPT_FG (EXPLICIT_ACCEPT_STATE
                (\(s,b). b))) i))``,


SIMP_TAC std_ss [EXISTENTIAL_OMEGA_AUTOMATON_SEM_def,
                 EXPLICIT_ACCEPT_COND_SEM_def,
                 EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                 EXPLICIT_ACCEPT_F_def,
                 EXPLICIT_ACCEPT_FG_def,
                 IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                 semi_automaton_REWRITES,
                 EXPLICIT_PROP_ACCEPT_COND_SEM_THM,
                 IN_CROSS, IN_UNIV, IN_SING,
prove (``!P. (?w:num->('a # 'b). P w) = (?w1 w2. P (\n. (w1 n, w2 n)))``,
  rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
    Q_TAC EXISTS_TAC `\n. FST (w n)` THEN
    Q_TAC EXISTS_TAC `\n. SND (w n)` THEN
    SIMP_TAC std_ss [] THEN
    METIS_TAC[],

    METIS_TAC[]
  ]),
prove (``!P x1 x2 x3 x4 x5. (((x1, x2), x3, (x4, x5), x6) IN \((x1, x2), x3, (x4, x5), x6). P x1 x2 x3 x4 x5 x6) = P x1 x2 x3 x4 x5 x6``, SIMP_TAC std_ss [IN_DEF]),
prove (``!P x1 x2. ((x1, x2) IN \(x1, x2). P x1 x2) = P x1 x2``, SIMP_TAC std_ss [IN_DEF]),
prove (``!P x1 x2 x3. (((x1, x2), x3) IN \((x1, x2), x3). P x1 x2 x3) = P x1 x2 x3``, SIMP_TAC std_ss [IN_DEF])
] THEN
rpt STRIP_TAC THEN
SUBGOAL_TAC `!w. (?t'. EXPLICIT_PROP_ACCEPT_COND_SEM (i t') (w t') p) =
                 (?t'. EXPLICIT_PROP_ACCEPT_COND_SEM (i t' INTER A.I) (w t') p)` THEN1 (
  GEN_TAC THEN EXISTS_EQ_STRIP_TAC THEN
  SIMP_TAC std_ss [EXPLICIT_PROP_ACCEPT_COND_SEM_def] THEN
  SUBGOAL_TAC `(\n. i t' INTER A.I) = PATH_RESTRICT (\n. i t') A.I` THEN1 (
    SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN
  PROVE_TAC[EXPLICIT_ACCEPT_COND_USED_INPUT_VARS_INTER_SUBSET_THM]
) THEN
ASM_REWRITE_TAC[] THEN
WEAKEN_HD_TAC THEN
EQ_TAC THEN rpt STRIP_TAC THENL [
  rename1 `w t` THEN
  SUBGOAL_TAC `?t'. EXPLICIT_PROP_ACCEPT_COND_SEM (i t' INTER A.I) (w t') p /\
               !t''. t'' < t' ==> ~EXPLICIT_PROP_ACCEPT_COND_SEM (i t'' INTER A.I) (w t'') p` THEN1 (
    Q_TAC (fn t => (ASSUME_TAC (EXISTS_LEAST_CONV t))) `?t'. EXPLICIT_PROP_ACCEPT_COND_SEM (i t' INTER A.I) (w t') p` THEN
    METIS_TAC[]
  ) THEN
  Q_TAC EXISTS_TAC `w` THEN
  Q_TAC EXISTS_TAC `\n. t' < n` THEN
  ASM_SIMP_TAC std_ss [] THEN
  rpt STRIP_TAC THENL [
    EQ_TAC THEN rpt STRIP_TAC THENL [
      RIGHT_DISJ_TAC THEN
      `n = t'` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[],

      DECIDE_TAC,

      `~(n < t')` by PROVE_TAC[] THEN
      DECIDE_TAC
    ],

    EXISTS_TAC ``SUC t'`` THEN
    DECIDE_TAC
  ],

  rename1 `~(_ >= t') \/ _` THEN
  Q_TAC EXISTS_TAC `w1` THEN
  ASM_SIMP_TAC std_ss [] THEN
  SUBGOAL_TAC `?t. w2 t /\ !t'. t' < t ==> ~(w2 t')` THEN1 (
    Q_TAC (fn t => (ASSUME_TAC (EXISTS_LEAST_CONV t))) `?t. w2 t` THEN
    `t' >= t'` by DECIDE_TAC THEN
    METIS_TAC[]
  ) THEN
  `~(t = 0)` by PROVE_TAC[] THEN
  `(SUC (PRE t) = t) /\ ((PRE t) < t)` by DECIDE_TAC THEN
  METIS_TAC[]
]);

val BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def = Define
   `BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON A S =
    semi_automaton (POW A.S CROSS POW A.S) A.I
      (\(s,i). i SUBSET A.I /\ (SND s = EMPTY) /\ !x. x IN (FST s) <=> (x, i) IN A.S0)
      (\((s11, s12), i, (s21, s22), i').
         i SUBSET A.I /\ i' SUBSET A.I /\ s11 SUBSET A.S /\ s12 SUBSET A.S /\
         (!x. x IN s21 <=> x IN A.S /\ ?s1'. s1' IN s11 /\ (s1', i, x, i') IN A.R) /\
         (((s12 = {}) /\ (s22 = s21 INTER S)) \/
          (s12 <> {} /\
           !x. x IN s22 <=> x IN S /\ x IN A.S /\
                            ?s1'. s1' IN s12 /\ (s1', i, x, i') IN A.R)))`;

Theorem BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_DET_TOTAL :
    !A S. IS_DET_TOTAL_SEMI_AUTOMATON (BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON A S)
Proof
    SIMP_TAC std_ss [IS_DET_TOTAL_SEMI_AUTOMATON_def,
                    BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                    semi_automaton_REWRITES, SING, IN_CROSS,
                    IN_POW,
                    EXISTS_UNIQUE_THM,
    prove(``!P s i s'. ((s, i, s', i') IN \((s11, s12), i, (s21, s22), i'). P s11 s12 i s21 s22 i') = P (FST s) (SND s) i (FST s') (SND s') i'``,
          Cases_on `s` THEN Cases_on `s'` THEN
          SIMP_TAC std_ss [IN_DEF]),
    prove(``(x, y) IN (\(x, y). P x y) = P x y``, SIMP_TAC std_ss [IN_DEF])] THEN
    rpt STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `((\x'. (x',i INTER A.I) IN A.S0), EMPTY:'b set)` THEN
      SIMP_TAC std_ss [IN_ABS, INTER_SUBSET],

      Cases_on `x` THEN Cases_on `x'` THEN
      FULL_SIMP_TAC std_ss [EXTENSION],

      Cases_on `s` THEN
      FULL_SIMP_TAC std_ss [] THEN
      Cases_on `r = {}` THENL [
        ASM_SIMP_TAC std_ss [EMPTY_SUBSET] THEN
        `?q'. q' = \x. (x IN A.S) /\ (?s1'. s1' IN q /\ (s1',i,x, i') IN A.R)` by METIS_TAC[] THEN
        Q_TAC EXISTS_TAC `(q', q' INTER S)` THEN
        ASM_SIMP_TAC std_ss [IN_DEF, SUBSET_DEF],

        ASM_SIMP_TAC std_ss [] THEN
        `?q'. q' = (\x. x IN A.S /\ (?s1'. s1' IN q /\ (s1',i,x, i') IN A.R))` by METIS_TAC[] THEN
        `?r'. r' = \x. (x IN S /\ x IN A.S /\ (?s1'. s1' IN r /\ (s1',i,x, i') IN A.R))` by METIS_TAC[] THEN
        Q_TAC EXISTS_TAC `(q', r')` THEN
        ASM_SIMP_TAC std_ss [IN_DEF]
      ],

      Cases_on `s'` THEN Cases_on `s''` THEN
      FULL_SIMP_TAC std_ss [] THEN
      LEFT_CONJ_TAC THENL [
        METIS_TAC[EXTENSION],
        ASM_REWRITE_TAC[]
      ],

      Cases_on `s'` THEN Cases_on `s''` THEN
      FULL_SIMP_TAC std_ss [] THEN
      METIS_TAC[EXTENSION]
    ]
QED

val BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_WELL_FORMED =
  store_thm (
    "BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_WELL_FORMED",
    ``!A S. IS_WELL_FORMED_SEMI_AUTOMATON A ==>
            IS_WELL_FORMED_SEMI_AUTOMATON (BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON A S)``,

    SIMP_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def,
                     BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                     semi_automaton_REWRITES, SUBSET_DEF,
                     IN_SING, IN_CROSS, IN_POW,
                     NOT_IN_EMPTY, FINITE_CROSS, FINITE_POW_IFF,
                     FORALL_PROD, FORALL_AND_THM] THEN
    SIMP_TAC std_ss [IN_DEF, FORALL_AND_THM, EMPTY_applied] THEN
    rpt STRIP_TAC THENL [
      PROVE_TAC[],
      METIS_TAC[IN_INTER, IN_DEF],
      PROVE_TAC[]
    ]);


val NDET_FG___TO___DET_FG___THM =
 store_thm
  ("NDET_FG___TO___DET_FG___THM",

    ``!A S i. IS_WELL_FORMED_SEMI_AUTOMATON A ==>
            ((EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, EXPLICIT_ACCEPT_FG (EXPLICIT_ACCEPT_STATE S)) i) =
            (EXISTENTIAL_OMEGA_AUTOMATON_SEM (BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON A S, EXPLICIT_ACCEPT_FG (EXPLICIT_ACCEPT_STATE (\(s1, s2). (s1 SUBSET A.S) /\ (s2 SUBSET A.S) /\ ~(s2 = EMPTY)))) i))``,


    rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
      ASM_SIMP_TAC std_ss [BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_DET_TOTAL,
                           BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_WELL_FORMED,
                           IS_DET_TOTAL_SEMI_AUTOMATON___EXISTENTIAL_UNIVERSAL_SEM],
      ALL_TAC
    ] THEN
    UNDISCH_ALL_TAC THEN
    SIMP_ALL_TAC std_ss [EXISTENTIAL_OMEGA_AUTOMATON_SEM_def,
                     UNIVERSAL_OMEGA_AUTOMATON_SEM_def,
                     IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                     BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                     semi_automaton_REWRITES, IN_SING, IN_CROSS,
                     EXPLICIT_ACCEPT_F_def,
                     EXPLICIT_ACCEPT_FG_def,
                     EXPLICIT_ACCEPT_COND_SEM_def,
                     EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                     IN_POW,
                     INTER_SUBSET, FORALL_AND_THM,
prove (``!P. (!w:num->('a # 'b). P w) = (!w1 w2. P (\n. (w1 n, w2 n)))``,
  rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
    PROVE_TAC[],


    Q_SPECL_NO_ASSUM 0 [`\n. FST (w n)`, `\n. SND (w n)`] THEN
    SIMP_ALL_TAC std_ss [] THEN
    METIS_TAC[]
  ]),
prove (``!P. (?w:num->('a # 'b). P w) = (?w1 w2. P (\n. (w1 n, w2 n)))``,
  rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
    Q_TAC EXISTS_TAC `\n. FST (w n)` THEN
    Q_TAC EXISTS_TAC `\n. SND (w n)` THEN
    SIMP_TAC std_ss [] THEN
    METIS_TAC[],

    METIS_TAC[]
  ]),
prove(``!P x11 x12 i x21 x22 i'. (((x11,x12),i,(x21,x22),i') IN \((x11,x12),i,(x21,x22),i'). P x11 x12 i x21 x22 i') = P x11 x12 i x21 x22 i'``, SIMP_TAC std_ss [IN_DEF]),
prove (``!P x1 x2. ((x1, x2) IN \(x1, x2). P x1 x2) = P x1 x2``, SIMP_TAC std_ss [IN_DEF])] THEN
  rpt STRIP_TAC THENL [

    rename1 `~(_ >= t1) \/ _` THEN
    SUBGOAL_TAC `!n. w n IN w1 n` THEN1 (
      Induct_on `n` THEN (
        METIS_TAC[]
      )
    ) THEN
    CCONTR_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN
    `?u. (u >= t1) /\ (w2 u = {})` by METIS_TAC[] THEN
    SUBGOAL_TAC `!n. w ((SUC u) + n) IN w2 ((SUC u) + n)` THEN1 (
      Induct_on `n` THENL [
        ASM_SIMP_TAC std_ss [] THEN
        Q_SPEC_NO_ASSUM 4 `u` THEN
        UNDISCH_HD_TAC THEN
        ASM_SIMP_TAC std_ss [IN_INTER] THEN
        `SUC u >= t1` by DECIDE_TAC THEN
        PROVE_TAC[],

        Q_SPEC_NO_ASSUM 5 `SUC u + n` THEN
        `(SUC u + SUC n) = SUC((SUC u + n))` by DECIDE_TAC THEN
        `~(w2 (SUC u + n) = EMPTY)` by PROVE_TAC[MEMBER_NOT_EMPTY] THEN
        FULL_SIMP_TAC std_ss [] THEN
        `SUC (SUC u + n) >= t1` by DECIDE_TAC THEN
        PROVE_TAC[]
      ]
    ) THEN
    Q_SPEC_NO_ASSUM 3 `SUC u` THEN
    SIMP_ALL_TAC std_ss [] THEN
    rename1 `w2 t2 = EMPTY` THEN
    Q_SPEC_NO_ASSUM 2 `t2 - SUC u` THEN
    `SUC u + (t2 - SUC u) = t2` by DECIDE_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN
    PROVE_TAC[MEMBER_NOT_EMPTY],

    rename1 `~(_ >= t1) \/ _` THEN
    Q.ABBREV_TAC `R = (\(s1, n1) (s2, n2). (n2 = SUC n1) /\
                                   (s1, i n1 INTER A.I, s2, i n2 INTER A.I) IN A.R /\
                                   (n1 >= t1 ==> s2 IN S))` THEN
    REMAINS_TAC `(!x. FINITE {y | R x y}) /\
                 (?s0. ((s0, i 0 INTER A.I) IN A.S0) /\ (~FINITE {y | RTC R (s0,0) y}))` THEN1 (
      `?f. (f 0 = (s0, 0)) /\ !n. R (f n) (f (SUC n))` by METIS_TAC[KoenigsLemma] THEN
      Q_TAC EXISTS_TAC `\n. FST (f n)` THEN
      NTAC 2 UNDISCH_HD_TAC THEN
      GSYM_NO_TAC 3 (*Def R*) THEN
      ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [FORALL_AND_THM] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_TAC `!n. SND (f n) = n` THEN1 (
        Induct_on `n` THEN ASM_REWRITE_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def, SUBSET_DEF, IN_CROSS,
        IN_POW] THEN
      rpt STRIP_TAC THENL [
        METIS_TAC[FST, SND],

        EXISTS_TAC ``SUC t1`` THEN
        GEN_TAC THEN RIGHT_DISJ_TAC THEN
        rename1 `FST (f t2) IN S` THEN
        `(PRE t2 >= t1) /\ (SUC (PRE t2) = t2)` by DECIDE_TAC THEN
        PROVE_TAC[]
      ]
    ) THEN
    rpt STRIP_TAC THENL [
      GSYM_NO_TAC 0 (*Def R*) THEN
      SIMP_ALL_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def,
        SUBSET_DEF, IN_CROSS] THEN
      REMAINS_TAC `{y | R x y} SUBSET A.S CROSS {SUC (SND x)}` THEN1 (
        PROVE_TAC[SUBSET_FINITE, FINITE_CROSS, FINITE_SING]
      ) THEN
      ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [SUBSET_DEF, GSPECIFICATION, IN_CROSS, IN_SING] THEN
      METIS_TAC[FST, SND],

      Q.ABBREV_TAC `P = (\s0 y. (?w. IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w (FST y) (SND y) /\ (w 0 = s0) /\ (!n. ((n > t1) /\ (SND y >= n)) ==> w n IN S)))` THEN
      SUBGOAL_TAC `!s0. ((s0, i 0 INTER A.I) IN A.S0 /\ ~FINITE {y | RTC R (s0,0) y}) =
                        ((s0, i 0 INTER A.I) IN A.S0 /\ ~FINITE {y | P s0 y})` THEN1 (
        GSYM_NO_TAC 0 (*Def P*) THEN
        ASM_REWRITE_TAC[] THEN
        rpt STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        rpt AP_TERM_TAC THEN
        ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        SIMP_TAC std_ss [] THEN
        GEN_TAC THEN

        ASM_SIMP_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE_def] THEN
        Induct_on `SND x` THENL [
          GSYM_NO_TAC 2 (*Def R*) THEN
          Cases_on `x` THEN
          ONCE_REWRITE_TAC[RTC_CASES2] THEN
          ASM_SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) [] THEN
          rpt STRIP_TAC THEN
          GSYM_NO_TAC 0 THEN
          ASM_SIMP_TAC arith_ss [] THEN
          EQ_TAC THEN rpt STRIP_TAC THENL [
            Q_TAC EXISTS_TAC `\n:num. s0` THEN
            FULL_SIMP_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def, SUBSET_DEF, IN_CROSS] THEN
            PROVE_TAC[FST],

            NTAC 2 (GSYM_NO_TAC 1) THEN
            ASM_REWRITE_TAC[]
          ],

          Cases_on `x` THEN
          ONCE_REWRITE_TAC[RTC_CASES2] THEN
          SIMP_TAC arith_ss [] THEN
          rpt STRIP_TAC THEN
          SUBGOAL_TAC `!y. (RTC R (s0,0) y /\ R y (q,r)) =
                           ((?w.
                     ((!n. n <= SND y ==> w n IN A.S) /\ (w 0, i 0 INTER A.I) IN A.S0 /\
                      (w (SND y) = FST y) /\
                      !n.
                        n < SND y ==>
                        (w n,i n INTER A.I,w (SUC n), i (SUC n) INTER A.I) IN A.R) /\
                     (w 0 = s0) /\ (!n. ((n > t1) /\ (SND y >= n)) ==> w n IN S)) /\ (R y (q,r)))` THEN1 (

            SUBGOAL_TAC `!y. R y (q,r) ==> (v = SND y)`  THEN1 (
              GSYM_NO_TAC 4 (*Def R*) THEN
              ASM_SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) []
            ) THEN

            rpt STRIP_TAC THEN EQ_TAC THENL [
              STRIP_TAC THEN
              RES_TAC THEN
              Q_SPEC_NO_ASSUM 6 `y` THEN
              UNDISCH_HD_TAC THEN
              ASM_SIMP_TAC std_ss [],

              METIS_TAC[]
            ]
          ) THEN
          ASM_REWRITE_TAC[] THEN
          WEAKEN_HD_TAC THEN
          GSYM_NO_TAC 0 (*Def r*) THEN
          GSYM_NO_TAC 4 (*Def R*) THEN
          ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [] THEN
          EQ_TAC THEN rpt STRIP_TAC THENL [
            GSYM_NO_TAC 2 (*Def v*) THEN
            FULL_SIMP_TAC std_ss [] THEN
            Q_TAC EXISTS_TAC `\m. if (m = SUC v) then q else (w m)` THEN
            ASM_SIMP_TAC arith_ss [] THEN
            rpt STRIP_TAC THENL [
              Cases_on `n = SUC v` THENL [
                SIMP_ALL_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def,
                                      SUBSET_DEF, IN_CROSS] THEN
                ASM_SIMP_TAC std_ss [] THEN
                METIS_TAC[FST, SND],

                `n <= v` by DECIDE_TAC THEN
                ASM_SIMP_TAC std_ss []
              ],

              Cases_on `n < v` THENL [
                ASM_SIMP_TAC arith_ss [],

                `n = v` by DECIDE_TAC THEN
                ASM_SIMP_TAC std_ss []
              ],

              Cases_on `v >= n` THEN
              ASM_SIMP_TAC arith_ss []
            ],

            Q_TAC EXISTS_TAC `(w v, v)` THEN
            ASM_SIMP_TAC std_ss [] THEN
            rpt STRIP_TAC THENL [
              Q_TAC EXISTS_TAC `w` THEN
              ASM_SIMP_TAC arith_ss [],

              `v < SUC v` by DECIDE_TAC THEN
              METIS_TAC[],

              `(SUC v > t1) /\ (SUC v >= SUC v)` by DECIDE_TAC THEN
              METIS_TAC[]
            ]
          ]
        ]
      ) THEN
      ASM_SIMP_TAC std_ss [] THEN
      WEAKEN_HD_TAC THEN
      WEAKEN_NO_TAC 1 (*Def R*) THEN
      CCONTR_TAC THEN
      SIMP_ALL_TAC std_ss [IS_WELL_FORMED_SEMI_AUTOMATON_def] THEN

      SUBGOAL_TAC `!n x. x IN w1 n ==> (?w. IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w x n)` THEN1 (
        SIMP_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE_def] THEN
        Induct_on `n` THENL [
          rpt STRIP_TAC THEN
          Q_TAC EXISTS_TAC `\n:num. x` THEN
          ASM_SIMP_TAC std_ss [] THEN
          METIS_TAC[SUBSET_DEF],


          ASM_SIMP_TAC std_ss [] THEN
          rpt STRIP_TAC THEN
          Q_SPEC_NO_ASSUM 3 `s1'` THEN
          UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          Q_TAC EXISTS_TAC `\m. if (m = SUC n) then x else (w m)` THEN
          ASM_SIMP_TAC arith_ss [] THEN
          rpt STRIP_TAC THENL [
            Cases_on `n' = SUC n` THEN
            ASM_SIMP_TAC arith_ss [],

            Cases_on `n' < n` THENL [
              ASM_SIMP_TAC arith_ss [],

              `n' = n` by DECIDE_TAC THEN
              ASM_SIMP_TAC std_ss []
            ]
          ]
        ]
      ) THEN

      SUBGOAL_TAC `!n x. (x IN w2 n) ==>
                         (?w. IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w x n /\
                            (!m. ((m > t1) /\ (n >= m)) ==> (w m IN S)))` THEN1 (
        Induct_on `n` THENL [
          ASM_SIMP_TAC std_ss [NOT_IN_EMPTY],


          Q_SPEC_NO_ASSUM 5 `n` THEN
          Cases_on `w2 n = EMPTY` THENL [
            WEAKEN_NO_TAC 7 (*x IN w1 (SUC n)*) THEN
            `~(n >= t1)` by PROVE_TAC[] THEN
            FULL_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_INTER] THEN
            rpt STRIP_TAC THEN
            `?w. IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w x (SUC n)` by METIS_TAC[] THEN
            Q_TAC EXISTS_TAC `w` THEN
            ASM_SIMP_TAC std_ss [] THEN
            rpt STRIP_TAC THEN
            `n >= t1` by DECIDE_TAC,


            FULL_SIMP_TAC std_ss [] THEN
            rpt STRIP_TAC THEN
            `?w. IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w s1' n /\
                 (!m. ((m > t1) /\ (n >= m)) ==> (w m IN S))` by METIS_TAC[] THEN
            Q_TAC EXISTS_TAC `\m:num. if (m = SUC n) then x else w m` THEN
            rpt STRIP_TAC THENL [
              SIMP_ALL_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE_def] THEN
              rpt STRIP_TAC THENL [
                rename1 `m <= SUC n` THEN
                Cases_on `m = SUC n` THEN ASM_REWRITE_TAC[] THEN
                `m <= n` by DECIDE_TAC THEN
                RES_TAC,

                ASM_SIMP_TAC arith_ss [],

                rename1 `m < SUC n` THEN
                ASM_SIMP_TAC arith_ss [] THEN
                Cases_on `m = n` THENL [
                  ASM_SIMP_TAC std_ss [],

                  `m < n` by DECIDE_TAC THEN
                  ASM_SIMP_TAC std_ss []
                ]
              ],

              rename1 `SUC n >= m` THEN
              Cases_on `m = SUC n` THENL [
                ASM_SIMP_TAC std_ss [],

                `n >= m` by DECIDE_TAC THEN
                ASM_SIMP_TAC std_ss []
              ]
            ]
          ]
        ]
      ) THEN

      `?A_S0'. A_S0' = \s0. (s0, i 0 INTER A.I) IN A.S0` by METIS_TAC[] THEN
      SUBGOAL_TAC `FINITE A_S0'` THEN1 (
        `FINITE A.S0` by METIS_TAC[SUBSET_FINITE, FINITE_CROSS, FINITE_POW_IFF] THEN
        `?A_S0. A_S0 = A.S0 INTER (\(x, i'). (i' = (i 0 INTER A.I)))` by METIS_TAC[] THEN
        `FINITE A_S0` by PROVE_TAC[INTER_FINITE] THEN
        SUBGOAL_TAC `A_S0' = IMAGE FST A_S0` THEN1 (
          ASM_SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_INTER] THEN
          rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
            Q_TAC EXISTS_TAC `(x, i 0 INTER A.I)` THEN
            ASM_SIMP_TAC std_ss [IN_INTER,
              prove (``!P x y. (((x, y) IN \(x,y). P x y) = P x y)``, SIMP_TAC std_ss [IN_DEF])
            ],

            Cases_on `x'` THEN
            REMAINS_TAC `(x = q) /\ ((i 0 INTER A.I) = r)` THEN1 ASM_REWRITE_TAC[] THEN
            NTAC 3 UNDISCH_HD_TAC THEN
            SIMP_TAC std_ss [IN_INTER, EXTENSION,
              prove (``!P x y. (((x, y) IN \(x,y). P x y) = P x y)``, SIMP_TAC std_ss [IN_DEF])
            ]
          ]
        ) THEN
        METIS_TAC[IMAGE_FINITE]
      ) THEN
      SUBGOAL_TAC `FINITE (BIGUNION (IMAGE (\s0. {y | P s0 y}) A_S0'))` THEN1 (
        MATCH_MP_TAC FINITE_BIGUNION THEN
        ASM_SIMP_TAC std_ss [IMAGE_FINITE, IN_IMAGE, GSYM LEFT_FORALL_IMP_THM, IN_ABS] THEN
        METIS_TAC[]
      ) THEN

      `?f. f = \n. ((@s. s IN (w2 (t1+n))), t1+n)` by METIS_TAC[] THEN
      SUBGOAL_TAC `IMAGE f UNIV SUBSET (BIGUNION (IMAGE (\s0. {y | P s0 y}) A_S0'))` THEN1 (
        GSYM_NO_TAC 7 (*Def P*) THEN
        ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_BIGUNION, IN_UNIV,
          GSYM RIGHT_EXISTS_AND_THM, GSPECIFICATION,
          GSYM LEFT_EXISTS_AND_THM] THEN
        rpt STRIP_TAC THEN
        Cases_on `x` THEN
        SIMP_ALL_TAC std_ss [] THEN
        ASM_SIMP_TAC std_ss [IN_ABS] THEN
        SELECT_ELIM_TAC THEN
        rpt STRIP_TAC THENL [
          `t1 + x' >= t1` by DECIDE_TAC THEN
          METIS_TAC[MEMBER_NOT_EMPTY],

          Q_SPECL_NO_ASSUM 8 [`t1 + x'`, `x`] THEN
          UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN
          rpt STRIP_TAC THEN
          Q_TAC EXISTS_TAC `w` THEN
          ASM_SIMP_TAC std_ss [] THEN
          FULL_SIMP_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE_def]
        ]
      ) THEN
      REMAINS_TAC `INFINITE (IMAGE f UNIV)` THEN1 (
        METIS_TAC[SUBSET_FINITE]
      ) THEN
      MATCH_MP_TAC (SIMP_RULE std_ss [prove (``!P Q R. ((P ==> Q ==> R) = ((P /\ Q) ==> R))``, METIS_TAC[]), GSYM RIGHT_FORALL_IMP_THM] IMAGE_11_INFINITE) THEN
      STRIP_TAC THENL [
        ASM_SIMP_TAC std_ss [],

        REWRITE_TAC[INFINITE_UNIV] THEN
        EXISTS_TAC ``\n:num. SUC n`` THEN
        SIMP_TAC arith_ss [] THEN
        EXISTS_TAC ``0`` THEN
        SIMP_TAC arith_ss []
      ]
    ]
  ]);

val A_SEM___NDET_F___TO___NDET_FG =
  store_thm (
    "A_SEM___NDET_F___TO___NDET_FG",
    ``!A p x. (~(x IN (SEMI_AUTOMATON_USED_VARS A UNION P_USED_VARS p))) ==>
    (AUTOMATON_EQUIV (A_NDET (A, ACCEPT_COND_F p))
                    (A_NDET (symbolic_semi_automaton (x INSERT A.S)
                                                         (P_AND (P_EQUIV(P_PROP x, p), A.S0))
                                                         (XP_AND (XP_EQUIV(XP_NEXT_PROP x, XP_OR(XP_PROP x, XP_NEXT p)), A.R)),
                                (ACCEPT_COND_FG (P_PROP x)))))``,

  SIMP_TAC std_ss [IN_UNION, SEMI_AUTOMATON_USED_VARS_def,
    SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_DIFF, AUTOMATON_EQUIV_def,
    A_SEM_THM, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
    IS_TRANSITION_def, symbolic_semi_automaton_REWRITES,
    ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
    INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
    ACCEPT_COND_F_def, ACCEPT_COND_FG_def, ACCEPT_F_def] THEN
  rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
    rename1 `P_SEM (w t UNION _) p` THEN
    Q_EXISTS_LEAST_TAC `?t'. P_SEM (w t' UNION (v t' DIFF A.S)) p` THEN
    FULL_SIMP_TAC std_ss [] THEN
    Q_TAC EXISTS_TAC `\n. if n < t' then (w n) else (x INSERT (w n))` THEN
    SUBGOAL_TAC `(!n. (w n UNION (v n DIFF (x INSERT A.S))) INTER (COMPL {x}) =
                     (w n UNION (v n DIFF A.S)) INTER (COMPL {x})) /\
                 (!n. ((x INSERT w n) UNION (v n DIFF (x INSERT A.S))) INTER (COMPL {x}) =
                     (w n UNION (v n DIFF A.S)) INTER (COMPL {x}))` THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_SING, IN_UNION, IN_DIFF,
        IN_INSERT] THEN
      METIS_TAC[]
    ) THEN
    `(P_USED_VARS p SUBSET COMPL {x}) /\ (P_USED_VARS A.S0 SUBSET COMPL {x}) /\
     (XP_USED_VARS A.R SUBSET COMPL {x})` by ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_COMPL, IN_SING] THEN
    `!n. ~(x IN w n)` by PROVE_TAC[PATH_SUBSET_def, SUBSET_DEF] THEN
    rpt STRIP_TAC THENL [
      SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_INSERT, COND_RAND,
        COND_RATOR] THEN
      PROVE_TAC[],

      Cases_on `0 < t'` THENL [
        ASM_SIMP_TAC std_ss [P_SEM_THM, IN_UNION, IN_DIFF, IN_INSERT] THEN
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],

        `t' = 0` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [P_SEM_THM, IN_UNION, IN_INSERT] THEN
        METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
      ],

      Cases_on `SUC n < t'` THENL [
        `n < t'` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [XP_SEM_THM, IN_UNION, IN_DIFF, IN_INSERT,
                             XP_SEM___XP_NEXT] THEN
        rpt STRIP_TAC THENL [
          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM]
        ],

        Cases_on `SUC n = t'` THENL [
          `n < t'` by DECIDE_TAC THEN
          ASM_SIMP_TAC std_ss [XP_SEM_THM, IN_UNION, IN_DIFF, IN_INSERT,
                              XP_SEM___XP_NEXT] THEN
          rpt STRIP_TAC THENL [
            METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],
            METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM]
          ],

          `~(n < t')` by DECIDE_TAC THEN
          ASM_SIMP_TAC std_ss [XP_SEM_THM, IN_UNION, IN_DIFF, IN_INSERT,
                              XP_SEM___XP_NEXT] THEN
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM]
        ]
      ],

      EXISTS_TAC ``SUC t'`` THEN
      rpt STRIP_TAC THEN
      RIGHT_DISJ_TAC THEN
      rename1 `~~(t'' >= SUC t')` THEN
      `~(t'' < t')` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [P_SEM_THM, IN_UNION, IN_DIFF, COND_RAND, COND_RATOR,
        IN_INSERT]
    ],

    rename1 `~(_ >= t)` THEN
    Q_TAC EXISTS_TAC `PATH_RESTRICT w A.S` THEN
    SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, PATH_SUBSET_def, INTER_SUBSET] THEN
    SUBGOAL_TAC `!n. (w n UNION (v n DIFF (x INSERT A.S))) INTER (COMPL {x}) =
                    ((w n INTER A.S) UNION (v n DIFF A.S)) INTER (COMPL {x})` THEN1 (
      SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_SING, IN_UNION, IN_DIFF,
        IN_INSERT, PATH_SUBSET_def, SUBSET_DEF, IN_INSERT] THEN
      METIS_TAC[]
    ) THEN
    rpt STRIP_TAC THENL [
      `P_USED_VARS A.S0 SUBSET COMPL {x}` by ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_COMPL, IN_SING] THEN
      SIMP_ALL_TAC std_ss [P_SEM_THM] THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],

      `XP_USED_VARS A.R SUBSET COMPL {x}`
         by ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_COMPL, IN_SING] THEN
      SIMP_ALL_TAC std_ss [XP_SEM_THM] THEN
      METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM],


      `P_USED_VARS p SUBSET COMPL {x}` by ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_COMPL, IN_SING] THEN
      SIMP_ALL_TAC std_ss [XP_SEM_THM, P_SEM_THM, XP_SEM___XP_NEXT, IN_UNION, IN_DIFF, IN_INSERT] THEN
      `t >= t` by DECIDE_TAC THEN
      Q_EXISTS_LEAST_TAC `?u. x IN w u` THEN
      SIMP_ALL_TAC std_ss [] THEN
      REMAINS_TAC `P_SEM (w u UNION (v u DIFF (x INSERT A.S))) p` THEN1 (
        METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
      ) THEN
      Cases_on `u` THENL [
        PROVE_TAC[],

        `n < SUC n` by DECIDE_TAC THEN
        `~(x IN w n)` by PROVE_TAC[] THEN
        PROVE_TAC[]
      ]
    ]
  ]);

val A_SEM___UNIV_G___TO___UNIV_GF =
  store_thm (
    "A_SEM___UNIV_G___TO___UNIV_GF",
    ``!A p x. (~(x IN (SEMI_AUTOMATON_USED_VARS A UNION P_USED_VARS p))) ==>
    (AUTOMATON_EQUIV (A_UNIV (A, ACCEPT_COND_G p))
                    (A_UNIV (symbolic_semi_automaton (x INSERT A.S)
                                                         (P_AND (P_EQUIV(P_PROP x, P_NOT p), A.S0))
                                                         (XP_AND (XP_EQUIV(XP_NEXT_PROP x, XP_OR(XP_PROP x, XP_NEXT (P_NOT p))), A.R)),
                                (ACCEPT_COND_GF (P_NOT (P_PROP x))))))``,

    SIMP_TAC std_ss [AUTOMATON_EQUIV_def] THEN
    rpt STRIP_TAC THEN

    SUBGOAL_TAC `!A p. (A_SEM v (A_UNIV (A,ACCEPT_COND_G p)) =
                       ~A_SEM v (A_NDET (A,ACCEPT_COND_F (P_NOT p)))) /\
                       (A_SEM v (A_UNIV (A,ACCEPT_COND_GF p)) =
                       ~A_SEM v (A_NDET (A,ACCEPT_COND_FG (P_NOT p))))` THEN1 (
      SIMP_TAC std_ss [A_SEM_THM, ACCEPT_COND_GF_def, ACCEPT_COND_G_def,
        ACCEPT_COND_F_def, ACCEPT_F_def, P_SEM_def,
        ACCEPT_COND_FG_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def] THEN
      METIS_TAC[]
    ) THEN
    ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

    ASSUME_TAC A_SEM___NDET_F___TO___NDET_FG THEN
    Q_SPECL_NO_ASSUM 0 [`A`, `P_NOT p`, `x`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[P_USED_VARS_def] THEN
    FULL_SIMP_TAC std_ss [AUTOMATON_EQUIV_def] THEN WEAKEN_HD_TAC THEN

    SIMP_TAC std_ss [A_SEM_THM, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
      P_SEM_THM, ACCEPT_COND_FG_def, ACCEPT_F_def, ACCEPT_COND_SEM_def,
      ACCEPT_COND_SEM_TIME_def]);

val ACCEPT_COND_TO_LTL_def = Define
  `(ACCEPT_COND_TO_LTL (ACCEPT_PROP b) = (LTL_PROP b)) /\
   (ACCEPT_COND_TO_LTL ACCEPT_TRUE = LTL_TRUE) /\
   (ACCEPT_COND_TO_LTL (ACCEPT_NOT f) = (LTL_NOT (ACCEPT_COND_TO_LTL f))) /\
   (ACCEPT_COND_TO_LTL (ACCEPT_AND (f1, f2)) =
      (LTL_AND (ACCEPT_COND_TO_LTL f1, ACCEPT_COND_TO_LTL f2))) /\
   (ACCEPT_COND_TO_LTL (ACCEPT_G f) = (LTL_ALWAYS (ACCEPT_COND_TO_LTL f)))`;

Theorem ACCEPT_COND_TO_LTL_THM :
    (!ac:'a acceptance_condition v t.
       ACCEPT_COND_SEM_TIME t v ac = LTL_SEM_TIME t v (ACCEPT_COND_TO_LTL ac)) /\
    (!ac:'a acceptance_condition v.
       ACCEPT_COND_SEM v ac = LTL_SEM v (ACCEPT_COND_TO_LTL ac))
Proof
    LEFT_CONJ_TAC THENL [
      INDUCT_THEN acceptance_condition_induct ASSUME_TAC THEN
      ASM_SIMP_TAC std_ss  [ACCEPT_COND_TO_LTL_def, ACCEPT_COND_SEM_TIME_def, LTL_SEM_THM],

      ASM_REWRITE_TAC[ACCEPT_COND_SEM_def, LTL_SEM_def]
    ]
QED

val LTL_USED_VARS___ACCEPT_COND_TO_LTL =
  store_thm ("LTL_USED_VARS___ACCEPT_COND_TO_LTL",
    ``!ac. LTL_USED_VARS (ACCEPT_COND_TO_LTL ac) =
           ACCEPT_COND_USED_VARS ac``,

    INDUCT_THEN acceptance_condition_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss  [ACCEPT_COND_TO_LTL_def,
        ACCEPT_COND_USED_VARS_def, LTL_USED_VARS_EVAL]
    ));

val A_NDET_FG___SYM__TO__CONRETE =
  store_thm (
    "A_NDET_FG___SYM__TO__CONRETE",
    ``!A I p.
    (P_USED_VARS p SUBSET A.S /\
    SEMI_AUTOMATON_USED_INPUT_VARS A SUBSET I) ==>

    (!i. A_SEM i (A_NDET (A,ACCEPT_COND_FG p)) =
        EXISTENTIAL_OMEGA_AUTOMATON_SEM (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A I,
                                        EXPLICIT_ACCEPT_FG (EXPLICIT_ACCEPT_STATE (\s. P_SEM s p))) i)``,

    rpt STRIP_TAC THEN
    SUBGOAL_TAC `!n. (i n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A SUBSET I` THEN1 (
      PROVE_TAC[SUBSET_TRANS, INTER_SUBSET]
    ) THEN
    ASM_SIMP_TAC std_ss [A_SEM_THM, EXISTENTIAL_OMEGA_AUTOMATON_SEM_def,
      GSYM SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___LANGUAGE_EQ
    ] THEN
    EXISTS_EQ_STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_def,
                    EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                    EXPLICIT_ACCEPT_FG_def,
                    EXPLICIT_ACCEPT_F_def,
                    IN_ABS,
                    ACCEPT_COND_FG_def,
                    ACCEPT_F_def,
                    A_SEM_THM,
                    ACCEPT_COND_SEM_def,
                    ACCEPT_COND_SEM_TIME_def] THEN
    EXISTS_EQ_STRIP_TAC THEN FORALL_EQ_STRIP_TAC THEN BOOL_EQ_STRIP_TAC THEN
    rename1 `t2 >= t1` THEN
    REMAINS_TAC `INPUT_RUN_PATH_UNION A i w t2 INTER A.S = w t2 INTER A.S` THEN1 (
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
    ) THEN
    SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, EXTENSION,
      IN_INTER, IN_UNION, IN_DIFF] THEN
    rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC);

val A_SEM___PRUNE_ACCEPTANCE_CONDITION =
  store_thm (
    "A_SEM___PRUNE_ACCEPTANCE_CONDITION",
    ``!A f ac I A' ac'. ((I = ACCEPT_COND_USED_VARS ac DIFF A.S) /\
                       (INJ f I UNIV) /\
                       (DISJOINT (IMAGE f I) (SEMI_AUTOMATON_USED_VARS A UNION I)) /\
                       (A' = symbolic_semi_automaton (A.S UNION (IMAGE f I)) A.S0
                               (XP_AND(A.R, XP_BIGAND (MAP (\i. XP_EQUIV(XP_PROP(f i), XP_PROP i)) (SET_TO_LIST I))))) /\
                       (ac' = ACCEPT_VAR_RENAMING (\x. if (x IN I) then f x else x) ac)) ==>

    ((ACCEPT_COND_USED_VARS ac' SUBSET A'.S) /\
    (!i. A_SEM i (A_UNIV (A, ACCEPT_COND ac)) =
         A_SEM i (A_UNIV (A',ACCEPT_COND ac'))))``,

    rpt GEN_TAC THEN STRIP_TAC THEN
    LEFT_CONJ_TAC THENL [
      ASM_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES,
      ACCEPT_VAR_RENAMING___USED_VARS, SUBSET_DEF, IN_IMAGE, IN_DIFF, IN_UNION] THEN
      GEN_TAC THEN STRIP_TAC THEN
      Cases_on `~(x' IN A.S)` THEN FULL_SIMP_TAC std_ss [] THEN
      PROVE_TAC[],

      SUBGOAL_TAC `FINITE (ACCEPT_COND_USED_VARS p DIFF A.S)` THEN1 (
        ASM_SIMP_TAC std_ss [FINITE_DIFF, FINITE___ACCEPT_COND_USED_VARS]
      ) THEN
      ASM_SIMP_TAC std_ss [A_SEM_THM, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        symbolic_semi_automaton_REWRITES,
        INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def,
        XP_SEM_THM, FORALL_AND_THM, XP_BIGAND_SEM, MEM_MAP,
        GSYM LEFT_FORALL_IMP_THM, containerTheory.MEM_SET_TO_LIST,
        IN_DIFF, IN_UNION, IN_IMAGE,
        FINITE___ACCEPT_COND_USED_VARS,
        FINITE_DIFF] THEN
      rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
        `?w'. w' = PATH_RESTRICT w A.S` by METIS_TAC[] THEN
        SUBGOAL_TAC `!n. (((w n UNION (i n DIFF (A.S UNION IMAGE f (ACCEPT_COND_USED_VARS ac DIFF A.S)))) INTER (COMPL (IMAGE f I))) =
                    ((w' n UNION (i n DIFF A.S)) INTER (COMPL (IMAGE f I))))` THEN1 (
          UNDISCH_NO_TAC 4 (*PATH_SUBSET w*) THEN
          ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_UNION, IN_DIFF,
            PATH_RESTRICT_def, PATH_MAP_def, PATH_SUBSET_def, SUBSET_DEF] THEN
          rpt WEAKEN_HD_TAC THEN
          rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN
          PROVE_TAC[]
        ) THEN

        Q_SPEC_NO_ASSUM 6 `w'` THEN
        PROVE_CONDITION_NO_ASSUM 0 THEN1 (
          rpt STRIP_TAC THENL [
            ASM_SIMP_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def,
              INTER_SUBSET],

            REMAINS_TAC `(P_USED_VARS A.S0 SUBSET COMPL (IMAGE f I))` THEN1 (
              METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
            ) THEN
            UNDISCH_NO_TAC 10 (*DISJOINT IMAGE*) THEN
            rpt WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
              IN_UNION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[],

            REMAINS_TAC `(XP_USED_VARS A.R SUBSET COMPL (IMAGE f I))` THEN1 (
              METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM]
            ) THEN
            UNDISCH_NO_TAC 10 (*DISJOINT IMAGE*) THEN
            rpt WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
              IN_UNION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[]
          ]
        ) THEN
        FULL_SIMP_TAC std_ss [ACCEPT_COND_SEM_def, ACCEPT_COND___VAR_RENAMING___NOT_INJ] THEN
        UNDISCH_HD_TAC THEN IMP_TO_EQ_TAC THEN
        ONCE_REWRITE_TAC [ACCEPT_COND_USED_VARS_INTER_THM] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_NO_TAC 10 (*DISJOINT*) THEN
        UNDISCH_NO_TAC 5 (*PATH_SUBSET w*) THEN
        UNDISCH_NO_TAC 2 (*i f i ON w*) THEN
        UNDISCH_NO_TAC 8 (*INJ f*) THEN
        ASM_SIMP_TAC std_ss [EXTENSION, IN_ABS,
          IN_INTER, COND_RAND, COND_RATOR] THEN
        rpt WEAKEN_HD_TAC THEN
        rpt DISCH_TAC THEN
        ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        SIMP_ALL_TAC std_ss [IN_UNION, IN_DIFF, PATH_RESTRICT_def,
          PATH_MAP_def, IN_INTER, COND_EXPAND_IMP,
          GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
          PATH_SUBSET_def, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, INJ_DEF,
          IN_UNIV, IN_IMAGE, IN_DIFF, EXTENSION, IN_ABS] THEN
        METIS_TAC[],

        `?w'. w' = \n. (w n) UNION (IMAGE f (i n INTER I))` by METIS_TAC[] THEN
        SUBGOAL_TAC `!n. (((w' n UNION (i n DIFF (A.S UNION IMAGE f (ACCEPT_COND_USED_VARS ac DIFF A.S)))) INTER (COMPL (IMAGE f I))) =
                    ((w n UNION (i n DIFF A.S)) INTER (COMPL (IMAGE f I))))` THEN1 (
          UNDISCH_NO_TAC 3 (*PATH_SUBSET w*) THEN
          ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_UNION, IN_DIFF,
            PATH_RESTRICT_def, PATH_MAP_def, PATH_SUBSET_def, SUBSET_DEF, IN_IMAGE] THEN
          rpt WEAKEN_HD_TAC THEN
          rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN
          METIS_TAC[]
        ) THEN
        Q_SPEC_NO_ASSUM 5 `w'` THEN
        PROVE_CONDITION_NO_ASSUM 0 THEN1 (
          rpt STRIP_TAC THENL [
            UNDISCH_NO_TAC 4 THEN (*PATH_SUBSET w*)
            ASM_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_IMAGE, IN_INTER, IN_DIFF] THEN
            rpt WEAKEN_HD_TAC THEN
            METIS_TAC[],

            REMAINS_TAC `(P_USED_VARS A.S0 SUBSET COMPL (IMAGE f I))` THEN1 (
              METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
            ) THEN
            UNDISCH_NO_TAC 9 (*DISJOINT IMAGE*) THEN
            rpt WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
              IN_UNION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[],

            REMAINS_TAC `(XP_USED_VARS A.R SUBSET COMPL (IMAGE f I))` THEN1 (
              METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM]
            ) THEN
            UNDISCH_NO_TAC 9 (*DISJOINT IMAGE*) THEN
            rpt WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
              IN_UNION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[],

            NTAC 2 UNDISCH_HD_TAC THEN
            UNDISCH_NO_TAC 10 THEN (*INJ I*)
            UNDISCH_NO_TAC 9 THEN (*DISJOINT IMAGE f I*)
            UNDISCH_NO_TAC 4 THEN (*PATH_SUBSET w*)
            ASM_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, IN_INTER, IN_DIFF] THEN
            rpt WEAKEN_HD_TAC THEN rpt STRIP_TAC THEN
            SIMP_ALL_TAC std_ss [INJ_DEF, IN_DIFF, IN_UNIV,
              GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, IN_IMAGE,
              SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, PATH_SUBSET_def] THEN
            METIS_TAC[]
          ]
        ) THEN
        FULL_SIMP_TAC std_ss [ACCEPT_COND_SEM_def, ACCEPT_COND___VAR_RENAMING___NOT_INJ] THEN
        UNDISCH_HD_TAC THEN IMP_TO_EQ_TAC THEN
        ONCE_REWRITE_TAC [ACCEPT_COND_USED_VARS_INTER_THM] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_NO_TAC 9 (*DISJOINT*) THEN
        UNDISCH_NO_TAC 4 (*PATH_SUBSET w*) THEN
        UNDISCH_NO_TAC 8 (*INJ f*) THEN
        ASM_SIMP_TAC std_ss [EXTENSION, IN_ABS,
          IN_INTER, COND_RAND, COND_RATOR] THEN
        rpt WEAKEN_HD_TAC THEN
        rpt DISCH_TAC THEN
        ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        SIMP_ALL_TAC std_ss [IN_UNION, IN_DIFF, PATH_RESTRICT_def,
          PATH_MAP_def, IN_INTER, COND_EXPAND_IMP,
          GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
          PATH_SUBSET_def, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, INJ_DEF,
          IN_UNIV, IN_IMAGE, IN_DIFF, EXTENSION, IN_ABS] THEN
        METIS_TAC[]
      ]
    ]);

Theorem A_NDET_FG___SYM__TO__CONRETE___MIN_I =
  GEN ``A:'a symbolic_semi_automaton``
    (REWRITE_RULE [SUBSET_REFL]
                  (SPECL [``A:'a symbolic_semi_automaton``, ``SEMI_AUTOMATON_USED_INPUT_VARS A``]
                         A_NDET_FG___SYM__TO__CONRETE));

val IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def = Define
   `IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION (A  :'a symbolic_semi_automaton)
                                        (A' :'a symbolic_semi_automaton)
                                        (IV :'a set)
                                        (f  :'a set -> 'a)
                                        (g  :'a -> 'a set)
                                        (f' :'a set -> 'a) S =
     ((S SUBSET (POW A.S)) /\
      (INJ f (POW A.S) UNIV) /\
      (INJ f' (POW A.S) UNIV) /\
      (DISJOINT (IMAGE f (POW A.S)) IV) /\
      (DISJOINT (IMAGE f' (POW A.S)) IV) /\
      (DISJOINT (IMAGE f (POW A.S)) (IMAGE f' (POW A.S))) /\
      (!z. z SUBSET A.S ==> (g (f z) = z)) /\
      (!z. z SUBSET A.S ==> (g (f' z) = z)) /\
      (A'.S = IMAGE f (POW A.S) UNION IMAGE f' (POW A.S)) /\
      (!i Z. Z SUBSET A'.S ==>
            (P_SEM (INPUT_RUN_STATE_UNION A' i Z) A'.S0 <=>
             (Z = {z | z IN (IMAGE f (POW A.S)) /\
                       P_SEM (INPUT_RUN_STATE_UNION A i (g z)) A.S0}))) /\
      (!S1 S2 i1 i2.
           S1 SUBSET A'.S /\ S2 SUBSET A'.S ==>
          (IS_TRANSITION A' S1 i1 S2 i2 <=>
           (S2 = {s2 | s2 IN (IMAGE f (POW A.S)) /\
                      ?s1. s1 IN S1 /\ s1 IN (IMAGE f (POW A.S)) /\
                           IS_TRANSITION A (g s1) i1 (g s2) i2} UNION
                 {s2 | s2 IN (IMAGE f' (POW A.S)) /\
                      ?s1. s1 IN S1 /\
                          (COND (S1 INTER (IMAGE f' (POW A.S)) = EMPTY)
                                (s1 IN (IMAGE f (POW A.S))) (s1 IN (IMAGE f' (POW A.S)))) /\
                           IS_TRANSITION A (g s1) i1 (g s2) i2 /\ (g s2) IN S}))))`;

Theorem SYMBOLIC___NDET_FG___TO___DET_FG___THM :
    !A A' IV f f' g S p p'.
       FINITE A.S /\
       (P_USED_VARS p) SUBSET A.S /\
       (P_USED_VARS p') SUBSET A'.S /\
       (SEMI_AUTOMATON_USED_INPUT_VARS A' = SEMI_AUTOMATON_USED_INPUT_VARS A) /\
       (S = (\s. s SUBSET A.S /\ P_SEM s p)) /\
       IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION A A' IV f g f' S /\
       (!s. P_SEM s p' <=> s INTER (IMAGE f' (POW A.S)) <> EMPTY) ==>
       !i. A_SEM i (A_NDET (A, ACCEPT_COND_FG p)) <=>
           A_SEM i (A_NDET (A', ACCEPT_COND_FG p'))
Proof
    rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss [A_NDET_FG___SYM__TO__CONRETE___MIN_I]
 >> ASSUME_TAC (INST_TYPE [beta |-> (alpha --> ``:bool``)] NDET_FG___TO___DET_FG___THM)
 >> Q_SPECL_NO_ASSUM 0 [`SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A
          (SEMI_AUTOMATON_USED_INPUT_VARS A)`, `\s. P_SEM s p`, `i`] THEN
SUBGOAL_TAC `IS_WELL_FORMED_SEMI_AUTOMATON
                (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A
                    (SEMI_AUTOMATON_USED_INPUT_VARS A))` THEN1 (
  MATCH_MP_TAC SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___IS_WELL_FORMED THEN
  ASM_REWRITE_TAC[FINITE___SEMI_AUTOMATON_USED_INPUT_VARS]
) THEN
FULL_SIMP_TAC std_ss [] THEN NTAC 2 WEAKEN_HD_TAC

THEN

`?h. h = \(S1, S2). (IMAGE f S1) UNION (IMAGE f' S2)` by METIS_TAC[] THEN
`?h'. h' = \S:'a set. (IMAGE g (S INTER (IMAGE f (POW A.S))), IMAGE g (S INTER (IMAGE f' (POW A.S))))` by METIS_TAC[] THEN
SUBGOAL_TAC `INJ h (POW (POW A.S) CROSS POW (POW A.S)) UNIV` THEN1 (
  ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [INJ_DEF, IN_CROSS, IN_POW, IN_UNIV] THEN
  Cases_on `x` THEN Cases_on `y` THEN
  SIMP_ALL_TAC std_ss [IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def] THEN
  NTAC 2 (UNDISCH_NO_TAC 4) THEN (*INJ f, f'*)
  UNDISCH_NO_TAC 6 (*DISJOINT IMAGE*) THEN
  rpt WEAKEN_HD_TAC THEN
  rpt DISCH_TAC THEN
  CLEAN_ASSUMPTIONS_TAC THEN
  SUBGOAL_TAC `(IMAGE f q = IMAGE f q') /\
                (IMAGE f' r = IMAGE f' r')` THEN1 (
    UNDISCH_HD_TAC THEN
    SIMP_ALL_TAC std_ss [EXTENSION, IN_UNION, GSYM SUBSET_COMPL_DISJOINT,
      SUBSET_DEF, IN_COMPL] THEN
    METIS_TAC[IMAGE_SUBSET, SUBSET_DEF]
  ) THEN
  WEAKEN_NO_TAC 2 THEN

  SIMP_ALL_TAC std_ss [INJ_DEF, IN_UNIV, SUBSET_DEF] THEN
  rpt STRIP_TAC THENL [
    UNDISCH_NO_TAC 1 THEN
    IMP_TO_EQ_TAC THEN
    MATCH_MP_TAC INJECTIVE_IMAGE_EQ THEN
    SIMP_TAC std_ss [IN_UNION] THEN
    METIS_TAC[],

    UNDISCH_NO_TAC 0 THEN
    IMP_TO_EQ_TAC THEN
    MATCH_MP_TAC INJECTIVE_IMAGE_EQ THEN
    SIMP_TAC std_ss [IN_UNION] THEN
    METIS_TAC[]
  ]
) THEN

SUBGOAL_TAC `!s. s IN (POW (POW A.S) CROSS POW (POW A.S)) ==> (h' (h s) = s)` THEN1 (
  Cases_on `s` THEN
  ASM_SIMP_TAC std_ss [IN_CROSS, IN_POW] THEN
  SIMP_ALL_TAC std_ss [IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def] THEN
  STRIP_TAC THEN
  SUBGOAL_TAC `((IMAGE f q UNION IMAGE f' r) INTER IMAGE f (POW A.S) =
                IMAGE f q) /\
                ((IMAGE f q UNION IMAGE f' r) INTER IMAGE f' (POW A.S) =
                IMAGE f' r)` THEN1 (
    NTAC 2 UNDISCH_HD_TAC (*r, q SUBSET POWERSET A.S*) THEN
    UNDISCH_NO_TAC 9 (*DISJOINT IMAGE IMAGE*) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, EXTENSION, IN_INTER, IN_UNION] THEN
    METIS_TAC[IMAGE_SUBSET, SUBSET_DEF]
  ) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_COMPOSE] THEN
  rpt STRIP_TAC THEN
  MATCH_MP_TAC IMAGE_ID_SUBSET THEN
  SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_POW] THEN
  METIS_TAC[]
) THEN

ASSUME_TAC (INST_TYPE [beta |-> (pairLib.mk_prod ((alpha --> bool) --> bool, (alpha --> bool) --> bool)), gamma |-> alpha --> bool] OMEGA_AUTOMATON___STATE_VAR_RENAMING) THEN
Q_SPECL_NO_ASSUM 0 [`BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON
            (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A
               (SEMI_AUTOMATON_USED_INPUT_VARS A)) (\s. P_SEM s p)`,
             ` EXPLICIT_ACCEPT_FG (EXPLICIT_ACCEPT_STATE
               (\(s1,s2).
                  s1 SUBSET
                  (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A
                     (SEMI_AUTOMATON_USED_INPUT_VARS A)).S /\
                  s2 SUBSET
                  (SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON A
                     (SEMI_AUTOMATON_USED_INPUT_VARS A)).S /\
                  ~(s2 = {}))):('a, (('a -> bool) -> bool) # (('a -> bool) -> bool))
                explicit_acceptance_condition`,
            `h`, `h'`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  rpt STRIP_TAC THENL [
    MATCH_MP_TAC BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON___IS_WELL_FORMED THEN
    MATCH_MP_TAC SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON___IS_WELL_FORMED THEN
    ASM_SIMP_TAC std_ss [FINITE___SEMI_AUTOMATON_USED_INPUT_VARS],

    SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def,
                     BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                     semi_automaton_REWRITES, SUBSET_DEF,
                     EXPLICIT_ACCEPT_FG_def, EXPLICIT_ACCEPT_F_def] THEN
    Cases_on `x` THEN
    SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS,
      prove (``!P x1 x2. ((x1, x2) IN \(x1,x2). P x1 x2) = P x1 x2``, SIMP_TAC std_ss [IN_DEF])],

    SIMP_TAC std_ss [BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                     semi_automaton_REWRITES, SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def] THEN
    ASM_REWRITE_TAC[],

    UNDISCH_HD_TAC THEN
    SIMP_TAC std_ss [BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                     semi_automaton_REWRITES, SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def] THEN
    ASM_REWRITE_TAC[]
  ]
) THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

FULL_SIMP_TAC std_ss [EXISTENTIAL_OMEGA_AUTOMATON_SEM_def,
                    BREAKPOINT_CONSTRUCTION_SEMI_AUTOMATON_def,
                    SYMBOLIC_SEMI_AUTOMATON_TO_SEMI_AUTOMATON_def,
                    semi_automaton_REWRITES, IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                    IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def,
                    INTER_SUBSET, SEMI_AUTOMATON_STATE_VAR_RENAMING_def,
  prove (``!P x1 x2 x3 x4. ((x1, x2,x3,x4) IN \(x1, x2,x3, x4). P x1 x2 x3 x4) =
                          P x1 x2 x3 x4``, SIMP_TAC std_ss [IN_DEF]),
  prove (``!P x1 x2 x3 x4. ((x1, x2,x3,x4) IN \((x1, x2), x3, (x4,x5), x6). P x1 x2 x3 x4 x5 x6) = P (FST x1) (SND x1) x2 (FST x3) (SND x3) x4``,
  Cases_on `x1` THEN Cases_on `x3` THEN SIMP_TAC std_ss [IN_DEF]),
  prove (``!P x1 x2. ((x1, x2) IN \(x1, x2). P x1 x2) =
                          P x1 x2``, SIMP_TAC std_ss [IN_DEF])] THEN

EXISTS_EQ_STRIP_TAC THEN
SUBGOAL_TAC `IMAGE (\(S1,S2). IMAGE f S1 UNION IMAGE f' S2)
        (POW (POW A.S) CROSS POW (POW A.S)) =
          POW
        (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))` THEN1 (

  SIMP_TAC std_ss [EXTENSION] THEN
  rpt STRIP_TAC THEN EQ_TAC THENL [
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [IN_IMAGE, EXTENSION, IN_UNION, IN_CROSS,
      IN_POW, SUBSET_DEF] THEN
    METIS_TAC[],

    ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [IN_POW, IN_IMAGE] THEN
    rpt STRIP_TAC THEN
    Q_TAC EXISTS_TAC `(IMAGE g (x INTER (IMAGE f (POW A.S))), IMAGE g (x INTER (IMAGE f' (POW A.S))))` THEN
    SIMP_TAC std_ss [GSYM IMAGE_COMPOSE, IN_CROSS, IN_POW] THEN
    rpt STRIP_TAC THENL [
      SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_IMAGE, IN_UNION,
        IN_POW, GSYM SUBSET_COMPL_DISJOINT, IN_COMPL,
        GSYM RIGHT_EXISTS_AND_THM] THEN
      rpt STRIP_TAC THEN EQ_TAC THENL [
        rpt STRIP_TAC THEN
        `x' IN IMAGE f (POW A.S) UNION IMAGE f' (POW A.S)` by
          PROVE_TAC[SUBSET_DEF] THEN
        SIMP_ALL_TAC std_ss [IN_UNION] THENL [
          DISJ1_TAC THEN
          Q_TAC EXISTS_TAC `x'` THEN
          ASM_REWRITE_TAC[IN_INTER] THEN
          UNDISCH_HD_TAC THEN
          SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
          METIS_TAC[],

          DISJ2_TAC THEN
          Q_TAC EXISTS_TAC `x'` THEN
          ASM_REWRITE_TAC[IN_INTER] THEN
          UNDISCH_HD_TAC THEN
          SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
          METIS_TAC[]
        ],

        SIMP_TAC std_ss [IN_IMAGE, IN_POW, IN_INTER,
          GSYM RIGHT_EXISTS_AND_THM] THEN
        METIS_TAC[]
      ],

      SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_IMAGE, IN_UNION, IN_INTER,
        IN_POW] THEN
      METIS_TAC[SUBSET_DEF],

      SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_IMAGE, IN_UNION, IN_INTER,
        IN_POW] THEN
      METIS_TAC[SUBSET_DEF]
    ]
  ]
) THEN

ASM_SIMP_TAC std_ss [IN_POW] THEN
rpt BOOL_EQ_STRIP_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
BINOP_TAC THENL [
  BINOP_TAC,
  ALL_TAC
] THENL [

  Q_SPECL_NO_ASSUM 8 [`i 0 INTER SEMI_AUTOMATON_USED_INPUT_VARS A' `, `w 0`] THEN
  UNDISCH_HD_TAC THEN
  ASM_SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, IMAGE_EQ_EMPTY] THEN
  DISCH_TAC THEN WEAKEN_HD_TAC THEN
  EQ_TAC THENL [
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION, IN_SING, NOT_IN_EMPTY, IN_INTER] THEN
    rpt STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      `(x IN (IMAGE f (POW A.S)))` by PROVE_TAC[SUBSET_DEF, IN_UNION] THEN
      ASM_REWRITE_TAC[] THEN
      Q_SPEC_NO_ASSUM 2 `g x` THEN
      SUBGOAL_TAC `g x IN IMAGE g (w 0 INTER IMAGE f (POW A.S))` THEN1 (
        SIMP_TAC std_ss [IN_IMAGE] THEN
        PROVE_TAC[IN_INTER]
      ) THEN
      FULL_SIMP_TAC std_ss [],

      SUBGOAL_TAC `g x SUBSET A.S` THEN1 (
        SIMP_ALL_TAC std_ss [IN_IMAGE, IN_POW] THEN
        METIS_TAC[]
      ) THEN
      `g x IN IMAGE g (w 0 INTER IMAGE f (POW A.S))` by METIS_TAC[] THEN
      UNDISCH_HD_TAC THEN
      UNDISCH_NO_TAC 2 (*x IN IMAGE f*) THEN
      SIMP_TAC std_ss [IN_IMAGE, IN_INTER, GSYM RIGHT_EXISTS_AND_THM, IN_POW] THEN
      SIMP_ALL_TAC std_ss [IN_IMAGE, IN_POW] THEN
      METIS_TAC[]
    ],

    SIMP_TAC std_ss [] THEN
    rpt STRIP_TAC THENL [
      UNDISCH_NO_TAC 12 (*DISJOINT IMAGE IMAGE*) THEN
      rpt WEAKEN_HD_TAC THEN
      SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, EXTENSION, GSPECIFICATION, IN_INTER, NOT_IN_EMPTY] THEN
      METIS_TAC[],

      SIMP_TAC std_ss [IN_IMAGE, IN_INTER, GSPECIFICATION, IN_POW, GSYM RIGHT_EXISTS_AND_THM] THEN
      METIS_TAC[]
    ]
  ],

  SUBGOAL_TAC `(!n. IMAGE g (w n INTER IMAGE f (POW A.S)) SUBSET POW A.S) /\  !n.
    IMAGE g (w n INTER IMAGE f' (POW A.S)) SUBSET POW A.S` THEN1 (
    ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_IMAGE, IN_INTER,
      GSYM RIGHT_EXISTS_AND_THM] THEN
    METIS_TAC[SUBSET_DEF]
  ) THEN
  ASM_REWRITE_TAC[] THEN
  FORALL_EQ_STRIP_TAC THEN
  Q_SPECL_NO_ASSUM 9 [`w n`, `w (SUC n)`, `i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A'`,
                      `i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A'`] THEN
  UNDISCH_HD_TAC THEN
  ASM_SIMP_TAC std_ss [IS_TRANSITION_def, INPUT_RUN_STATE_UNION_def,
    IMAGE_EQ_EMPTY] THEN
  DISCH_TAC THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `(w (SUC n) =
    {s2 |
      s2 IN IMAGE f (POW A.S) /\
      ?s1.
        s1 IN w n /\ s1 IN IMAGE f (POW A.S) /\
        XP_SEM A.R
          (g s1 UNION (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF A.S),
          g s2 UNION
          (i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF
            A.S))} UNION
    {s2 |
      s2 IN IMAGE f' (POW A.S) /\
      ?s1.
        s1 IN w n /\
        (if w n INTER IMAGE f' (POW A.S) = {} then
          s1 IN IMAGE f (POW A.S)
        else
          s1 IN IMAGE f' (POW A.S)) /\
        XP_SEM A.R
          (g s1 UNION (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF A.S),
          g s2 UNION
          (i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF A.S)) /\
        g s2 IN (\s. s SUBSET A.S /\ P_SEM s p)}) = (
(w (SUC n) INTER (IMAGE f (POW A.S)) =
                {s2 |
          s2 IN IMAGE f (POW A.S) /\
          ?s1.
            s1 IN w n /\ s1 IN IMAGE f (POW A.S) /\
            XP_SEM A.R
              (g s1 UNION
                (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF A.S),
                g s2 UNION
                (i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF
                A.S))}) /\
              (w (SUC n) INTER (IMAGE f' (POW A.S)) =
                {s2 |
          s2 IN IMAGE f' (POW A.S) /\
          ?s1.
            s1 IN w n /\
            (if w n INTER IMAGE f' (POW A.S) = {} then
                s1 IN IMAGE f (POW A.S)
              else
                s1 IN IMAGE f' (POW A.S)) /\
            XP_SEM A.R
              (g s1 UNION
                (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF A.S),
                g s2 UNION
                (i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A DIFF
                A.S)) /\ g s2 IN (\s. s SUBSET A.S /\ P_SEM s p)}))` THEN1 (
    UNDISCH_NO_TAC 13 THEN (*DISJOINT IMAGE IMAGE*)
    UNDISCH_NO_TAC 2 THEN (*w n SUBSET*)
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INTER, GSPECIFICATION,
      GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, GSYM FORALL_AND_THM] THEN
    rpt STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    METIS_TAC[]
  ) THEN
  ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN
  MATCH_MP_TAC (prove (``((A = C) /\ (A ==> (B = D))) ==> (A /\ B = C /\ D)``, PROVE_TAC[])) THEN
  rpt STRIP_TAC THENL [
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_IMAGE, IN_INTER,
      IN_POW, GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM] THEN

    `!s1' x' n. ((!x. x IN s1' = x IN g (f x')) /\ f x' IN w n /\ x' SUBSET A.S) = ((s1' = x') /\ f x' IN w n /\ x' SUBSET A.S)` by METIS_TAC[EXTENSION] THEN
    ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC[],

    Cases_on `w n INTER IMAGE f' (POW A.S) = {}` THEN (
      ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER] THEN
      WEAKEN_NO_TAC 1 THEN
      SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_INTER,
        IN_POW, GSYM LEFT_EXISTS_AND_THM,
        GSYM RIGHT_EXISTS_AND_THM, IN_ABS] THEN
      METIS_TAC[]
    )
  ],

  SIMP_TAC std_ss [
    EXPLICIT_ACCEPT_FG_def,
    EXPLICIT_ACCEPT_F_def,
    EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def,
    EXPLICIT_ACCEPT_COND_SEM_def,
    EXPLICIT_ACCEPT_COND_SEM_TIME_def,
    IN_ABS] THEN
  EXISTS_EQ_STRIP_TAC THEN
  FORALL_EQ_STRIP_TAC THEN
  BOOL_EQ_STRIP_TAC THEN
  rename1 `t2 >= t1` THEN
  SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [IN_IMAGE,
    prove (``!P x. (x IN \(x1, x2). P x1 x2) = (P (FST x) (SND x))``,
             Cases_on `x` THEN SIMP_TAC std_ss [IN_DEF])] THEN
  EQ_TAC THEN rpt STRIP_TAC THENL [
    NTAC 5 UNDISCH_HD_TAC THEN
    UNDISCH_NO_TAC 13 (*DISJOINT IMAGE IMAGE*) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL] THEN
    rpt STRIP_TAC THEN
    SUBGOAL_TAC `IMAGE f' (SND x) = EMPTY` THEN1 (
      FULL_SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_IMAGE, IN_POW, IN_INTER, NOT_IN_EMPTY, IN_UNION] THEN
      METIS_TAC[]
    ) THEN
    SIMP_ALL_TAC std_ss [IMAGE_EQ_EMPTY],

    `?w1. w1 = (w t2 INTER (IMAGE f (POW A.S)))` by PROVE_TAC[] THEN
    `?w2. w2 = (w t2 INTER (IMAGE f' (POW A.S)))` by PROVE_TAC[] THEN
    SUBGOAL_TAC `w t2 = w1 UNION w2` THEN1 (
      NTAC 2 UNDISCH_HD_TAC THEN
      UNDISCH_NO_TAC 2 (*w n SUBSET*) THEN
      rpt WEAKEN_HD_TAC THEN
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, SUBSET_DEF] THEN
      METIS_TAC[]
    ) THEN
    SUBGOAL_TAC `?gw1 gw2. (gw1 SUBSET (POW A.S)) /\
                           (gw2 SUBSET (POW A.S)) /\
                           (w1 = IMAGE f gw1) /\
                           (w2 = IMAGE f' gw2)` THEN1 (
      NTAC 2 (UNDISCH_NO_TAC 1) THEN
      rpt WEAKEN_HD_TAC THEN
      rpt STRIP_TAC THEN

      ASSUME_TAC (INST_TYPE [alpha |-> alpha --> bool, beta |-> alpha] SUBSET_IMAGE___ORGINAL_EXISTS) THEN
      Q_SPECL_NO_ASSUM 0 [`f`, `POW A.S`, `w1`] THEN

      ASSUME_TAC (INST_TYPE [alpha |-> alpha --> bool, beta |-> alpha] SUBSET_IMAGE___ORGINAL_EXISTS) THEN
      Q_SPECL_NO_ASSUM 0 [`f'`, `POW A.S`, `w2`] THEN

      METIS_TAC[INTER_SUBSET, SUBSET_IMAGE___ORGINAL_EXISTS]
    ) THEN

    Q_TAC EXISTS_TAC `(gw1, gw2)` THEN
    ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC[IMAGE_EQ_EMPTY]
  ]
]
QED

val SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_TOTAL =
  store_thm (
    "SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_TOTAL",
    ``!A A' IV f f' g S.
    IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION A A' IV f g f' S ==> IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A'``,

    SIMP_TAC std_ss [IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def, IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON_def] THEN
    rpt STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `{z |
               z IN IMAGE f (POW A.S) /\
               P_SEM (INPUT_RUN_STATE_UNION A i (g z)) A.S0}` THEN
      LEFT_CONJ_TAC THENL [
        ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNION],
        METIS_TAC[]
      ],

      ONCE_REWRITE_TAC[TRANSITION_CURRENT_STATE_CLEANING] THEN
      `?s2. s2 = {s2 |
              s2 IN IMAGE f (POW A.S) /\
              ?s1'.
                s1' IN s1 INTER A'.S /\ s1' IN IMAGE f (POW A.S) /\
                IS_TRANSITION A (g s1') (i1 UNION s1) (g s2) i2} UNION
             {s2 |
              s2 IN IMAGE f' (POW A.S) /\
              ?s1'.
                s1' IN s1 INTER A'.S /\
                (if s1 INTER A'.S INTER IMAGE f' (POW A.S) = {} then
                   s1' IN IMAGE f (POW A.S)
                 else
                   s1' IN IMAGE f' (POW A.S)) /\
                IS_TRANSITION A (g s1') (i1 UNION s1) (g s2) i2 /\
                g s2 IN S}` by METIS_TAC[] THEN
      Q_TAC EXISTS_TAC `s2` THEN
      LEFT_CONJ_TAC THENL [
        ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNION] THEN
        METIS_TAC[],

        METIS_TAC[INTER_SUBSET]
      ]
    ]);

val SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET =
  store_thm (
    "SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET",
    ``!A A' IV f f' g S.
    IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION A A' IV f g f' S ==>
    IS_DET_SYMBOLIC_SEMI_AUTOMATON A'``,

    SIMP_TAC std_ss [IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def, IS_DET_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_AT_MOST_ONE_def] THEN
    rpt STRIP_TAC THENL [
      METIS_TAC[],
      METIS_TAC[TRANSITION_CURRENT_STATE_CLEANING, INTER_SUBSET]
    ]);

val SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET_TOTAL =
  store_thm (
    "SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET_TOTAL",
    ``!A A' IV f f' g S.
    IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION A A' IV f g f' S ==>
    IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A'``,

    PROVE_TAC [IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_def,
      SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET, SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_TOTAL]);

val SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def=
(* Idea by Sven Lamberti *)
 Define
   `SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON A f f' pS =
        symbolic_semi_automaton
            (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))
            (P_AND (P_FORALL (SET_TO_LIST A.S) (P_EQUIV(A.S0, VAR_RENAMING_HASHTABLE A.S f)),
              P_NOT (P_BIGOR (SET_TO_LIST (IMAGE (\s. P_PROP (f' s)) (POW A.S))))))
            (XP_AND(
  (XP_NEXT_FORALL (SET_TO_LIST A.S) (XP_EQUIV(
                      XP_NEXT (VAR_RENAMING_HASHTABLE A.S f),
                      XP_CURRENT_EXISTS (SET_TO_LIST A.S) (
                          XP_AND(A.R, XP_CURRENT (VAR_RENAMING_HASHTABLE A.S f)))))),
  (XP_COND ((XP_NOT (XP_BIGOR (SET_TO_LIST (IMAGE (\s. XP_PROP (f' s)) (POW A.S))))),
    (XP_NEXT_FORALL (SET_TO_LIST A.S) (XP_EQUIV(
                          XP_NEXT (VAR_RENAMING_HASHTABLE A.S f'),
                          XP_CURRENT_EXISTS (SET_TO_LIST A.S) (
                              XP_AND(XP_AND(A.R, XP_NEXT pS), XP_CURRENT (VAR_RENAMING_HASHTABLE A.S f)))))),
    (XP_NEXT_FORALL (SET_TO_LIST A.S) (XP_EQUIV(
                      XP_NEXT (VAR_RENAMING_HASHTABLE A.S f'),
                      XP_CURRENT_EXISTS (SET_TO_LIST A.S) (
                          XP_AND(XP_AND(A.R, XP_NEXT pS), XP_CURRENT (VAR_RENAMING_HASHTABLE A.S f'))))))))))`;

val SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_THM =
 store_thm
  ("SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_THM",
    ``!A A' IV f g f' pS.

      ((A' = SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON A f f' pS) /\
        FINITE A.S /\
        SEMI_AUTOMATON_USED_VARS A SUBSET IV /\
        P_USED_VARS pS SUBSET A.S /\
        INJ f (POW A.S) UNIV /\
        INJ f' (POW A.S) UNIV /\
        DISJOINT (IMAGE f (POW A.S)) IV /\
        DISJOINT (IMAGE f' (POW A.S)) IV /\
        DISJOINT (IMAGE f (POW A.S)) (IMAGE f' (POW A.S)) /\
        (!z. z SUBSET A.S ==> (g (f z) = z)) /\
        (!z. z SUBSET A.S ==> (g (f' z) = z))) ==>

    (IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION A A' IV f g f' (\s. s SUBSET A.S /\ P_SEM s pS))``,

SIMP_TAC std_ss [IS_SYMBOLIC_BREAKPOINT_CONSTRUCTION_def,
  SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def, symbolic_semi_automaton_REWRITES] THEN
rpt STRIP_TAC THENL [

  SIMP_TAC std_ss [SUBSET_DEF, IN_ABS, IN_POW],


  ASM_SIMP_TAC std_ss [P_FORALL_SEM, SET_TO_LIST_INV,
    P_SEM_THM, VAR_RENAMING_HASHTABLE_SEM,
    INPUT_RUN_STATE_UNION_def, symbolic_semi_automaton_REWRITES,
    P_BIGOR_SEM, MEM_SET_TO_LIST, FINITE_POW_IFF, IMAGE_FINITE] THEN

  SUBGOAL_TAC `!l'. (l' SUBSET A.S) ==> ((Z UNION
            (i DIFF
             (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
            A.S UNION l') INTER A.S = l')` THEN1 (
    UNDISCH_HD_TAC (*Z SUBSET IMAGE*) THEN
    UNDISCH_NO_TAC 2 (*DISJOINT IMAGE IMAGE*) THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, SUBSET_DEF,
      GSYM SUBSET_COMPL_DISJOINT, IN_COMPL] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!l'. (l' SUBSET A.S) ==> (
      (f l' IN
        Z UNION
        (i DIFF
         (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
        A.S UNION l') = (f l' IN Z))` THEN1 (

    SIMP_ALL_TAC std_ss [SEMI_AUTOMATON_USED_VARS___DIRECT_DEF,
      UNION_SUBSET] THEN
    UNDISCH_NO_TAC 5 (*DISJOINT IMAGE f IV*) THEN
    UNDISCH_NO_TAC 10 (*A.S SUBSET IV*) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, SUBSET_DEF,
      GSYM SUBSET_COMPL_DISJOINT, IN_COMPL, IN_IMAGE, IN_POW] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!l'. (P_SEM
          (Z UNION
           (i DIFF
            (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
           A.S UNION l') A.S0) = (P_SEM (l' UNION (i DIFF A.S)) A.S0)` THEN1 (
    GEN_TAC THEN
    ONCE_REWRITE_TAC[P_USED_VARS_INTER_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
      EXTENSION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, IN_INTER, IN_DIFF] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `(!e.
       ~(e IN IMAGE (\s. P_PROP (f' s)) (POW A.S)) \/
       ~P_SEM
          (Z UNION
           (i DIFF
            (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S)))) e) =
          (Z INTER IMAGE f' (POW A.S) = EMPTY)` THEN1 (
    SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_FORALL_OR_THM, P_SEM_THM, IN_POW, IN_UNION, EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY, IN_DIFF] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  EQ_TAC THENL [
    rpt STRIP_TAC THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
    GEN_TAC THEN
    SUBGOAL_TAC `Z = Z INTER (IMAGE f (POW A.S))` THEN1 (
      SIMP_ALL_TAC std_ss [EXTENSION, SUBSET_DEF, IN_INTER, NOT_IN_EMPTY, IN_UNION] THEN
      METIS_TAC[]
    ) THEN
    ONCE_ASM_REWRITE_TAC [] THEN WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [IN_INTER] THEN
    BOOL_EQ_STRIP_TAC THEN
    SIMP_ALL_TAC std_ss [IN_IMAGE, IN_POW] THEN
    METIS_TAC[],

    SIMP_TAC std_ss [] THEN
    DISCH_TAC THEN WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, NOT_IN_EMPTY] THEN
    rpt STRIP_TAC THENL [
      ASM_SIMP_TAC std_ss [] THEN
      BOOL_EQ_STRIP_TAC THEN
      SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
      PROVE_TAC[],

      SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM] THEN
      METIS_TAC[]
    ]
  ],

  ASM_SIMP_TAC std_ss [IS_TRANSITION_def, symbolic_semi_automaton_REWRITES,
    XP_SEM_THM, INPUT_RUN_STATE_UNION_def, XP_NEXT_FORALL_SEM,
    SET_TO_LIST_INV, XP_SEM___XP_NEXT, VAR_RENAMING_HASHTABLE_SEM,
    XP_CURRENT_EXISTS_SEM, XP_SEM___XP_CURRENT, XP_BIGOR_SEM,
    MEM_SET_TO_LIST, FINITE_POW_IFF, IMAGE_FINITE] THEN

  SUBGOAL_TAC `!l' Z i.
            (Z SUBSET IMAGE f (POW A.S) UNION IMAGE f' (POW A.S)) ==> ((Z UNION
            (i DIFF
             (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
            A.S UNION l') INTER A.S = (l' INTER A.S))` THEN1 (
    UNDISCH_NO_TAC 4 (*DISJOINT IMAGE IMAGE*) THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, SUBSET_DEF,
      GSYM SUBSET_COMPL_DISJOINT, IN_COMPL] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!l' Z i. (Z SUBSET IMAGE f (POW A.S) UNION IMAGE f' (POW A.S)) ==> ((
      (f (l' INTER A.S) IN
        Z UNION
        (i DIFF
         (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
        A.S UNION l') = (f (l' INTER A.S) IN (Z UNION (l' DIFF A.S)))) /\

      ((f' (l' INTER A.S) IN
        Z UNION
        (i DIFF
         (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))) DIFF
        A.S UNION l') = (f' (l' INTER A.S) IN (Z UNION (l' DIFF A.S)))))` THEN1 (

    SIMP_ALL_TAC std_ss [SEMI_AUTOMATON_USED_VARS___DIRECT_DEF,
      UNION_SUBSET] THEN
    UNDISCH_NO_TAC 5 (*DISJOINT IMAGE f' IV*) THEN
    UNDISCH_NO_TAC 5 (*DISJOINT IMAGE f IV*) THEN
    UNDISCH_NO_TAC 10 (*A.S SUBSET IV*) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, SUBSET_DEF,
      GSYM SUBSET_COMPL_DISJOINT, IN_COMPL, IN_IMAGE, IN_POW] THEN
    METIS_TAC[INTER_SUBSET, SUBSET_DEF]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `(!e.
        ~(e IN IMAGE (\s. XP_PROP (f' s)) (POW A.S)) \/
        ~XP_SEM e
           (S1 UNION
            (i1 DIFF
             (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))),
            S2 UNION
            (i2 DIFF
             (IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))))) =
          (S1 INTER IMAGE f' (POW A.S) = EMPTY)` THEN1 (
    SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_FORALL_OR_THM, XP_SEM_THM, IN_POW, IN_UNION, EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY, IN_DIFF] THEN
    METIS_TAC[]
  ) THEN
  POP_NO_ASSUM 0 (fn thm =>
                    let
                      val thm2 = ONCE_REWRITE_RULE [prove (``(A = B) = (~A = ~B)``, PROVE_TAC[])] thm
                      val thm2 = CONV_RULE (LHS_CONV (SIMP_CONV std_ss [])) thm2
                    in
                      ASSUME_TAC thm THEN ASSUME_TAC thm2
                    end) THEN
  ASM_SIMP_TAC std_ss [] THEN NTAC 2 WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!i1 i2 l' l''. XP_SEM A.R
             (S1 UNION
              (i1 DIFF
               (IMAGE f (POW A.S) UNION
                IMAGE f' (POW A.S))) DIFF A.S UNION l'',
              S2 UNION
              (i2 DIFF
               (IMAGE f (POW A.S) UNION
                IMAGE f' (POW A.S))) DIFF A.S UNION l') =

            (XP_SEM A.R (l'' UNION (i1 DIFF A.S), l' UNION (i2 DIFF A.S)))` THEN1 (
    rpt GEN_TAC THEN
    ONCE_REWRITE_TAC[XP_USED_VARS_INTER_THM] THEN
    MATCH_MP_TAC (prove (``(s1 = s1') /\ (s2 = s2') ==> (XP_SEM xp (s1, s2) = XP_SEM xp (s1', s2'))``, PROVE_TAC[])) THEN
    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, SUBSET_DEF,
      EXTENSION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, IN_INTER, IN_DIFF, XP_USED_VARS_def] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!i2 l'. (P_SEM
             (S2 UNION
              (i2 DIFF
               (IMAGE f (POW A.S) UNION
                IMAGE f' (POW A.S))) DIFF A.S UNION l') pS) =

            (P_SEM l' pS)` THEN1 (
    rpt GEN_TAC THEN
    ONCE_REWRITE_TAC[P_USED_VARS_INTER_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, SUBSET_DEF,
      EXTENSION, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, IN_INTER, IN_DIFF, XP_USED_VARS_def] THEN
    METIS_TAC[]
  ) THEN
  ASM_SIMP_TAC std_ss [IN_ABS] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `!l'. l' SUBSET A.S ==>
                      (((l' INTER A.S = l') /\ (l' DIFF A.S = EMPTY)) /\
                       (((f l' IN IMAGE f (POW A.S)) /\                 (f' l' IN IMAGE f' (POW A.S))) /\
                       (~(f' l' IN IMAGE f (POW A.S)) /\               ~(f l' IN IMAGE f' (POW A.S)))))` THEN1 (
    GEN_TAC THEN NTAC 2 STRIP_TAC THENL [
      METIS_TAC [SUBSET_INTER_ABSORPTION, DIFF_SUBSET_EMPTY],


      LEFT_CONJ_TAC THENL [
        SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
        PROVE_TAC[],

        PROVE_TAC[DISJOINT_DISJ_THM]
      ]
    ]
  ) THEN

  EQ_TAC THENL [
    ASM_SIMP_TAC std_ss [EXTENSION, IN_UNION, GSPECIFICATION] THEN
    DISCH_TAC THEN GEN_TAC THEN
    Cases_on `~(x IN IMAGE f (POW A.S) UNION IMAGE f' (POW A.S))` THEN1 (
      SIMP_ALL_TAC std_ss [IN_UNION, SUBSET_DEF] THEN
      ASM_REWRITE_TAC[] THEN
      METIS_TAC[]
    ) THEN
    UNDISCH_HD_TAC THEN
    SIMP_TAC std_ss [IN_UNION] THEN
    STRIP_TAC THENL [
      `~(x IN IMAGE f' (POW A.S))` by PROVE_TAC[DISJOINT_DISJ_THM] THEN
      FULL_SIMP_TAC std_ss [] THEN
      SIMP_ALL_TAC std_ss [IN_IMAGE, IN_POW] THEN
      Q_SPEC_NO_ASSUM 5 `x'` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
      DISCH_TAC THEN WEAKEN_HD_TAC THEN
      METIS_TAC[NOT_IN_EMPTY],

      `~(x IN IMAGE f (POW A.S))` by PROVE_TAC[DISJOINT_DISJ_THM] THEN
      FULL_SIMP_TAC std_ss [] THEN
      SIMP_ALL_TAC std_ss [IN_IMAGE, IN_POW] THEN
      Q_SPEC_NO_ASSUM 3 `x'` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
      DISCH_TAC THEN WEAKEN_HD_TAC THEN
      METIS_TAC[NOT_IN_EMPTY]
    ],

    ASM_SIMP_TAC std_ss [UNION_EMPTY, GSPECIFICATION, IN_UNION, NOT_IN_EMPTY] THEN
    rpt STRIP_TAC THENL [
      SUBGOAL_TAC `f l' IN IMAGE f (POW A.S)` THEN1 (
        SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
        PROVE_TAC[]
      ) THEN
      `~(f l' IN IMAGE f' (POW A.S))` by PROVE_TAC [DISJOINT_DISJ_THM] THEN
      ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
        GSYM LEFT_EXISTS_AND_THM, IN_POW] THEN
      EQ_TAC THEN rpt STRIP_TAC THENL [
        Q_TAC EXISTS_TAC `x` THEN
        ASM_SIMP_TAC std_ss [] THEN
        METIS_TAC[],

        Q_TAC EXISTS_TAC `l''` THEN
        ASM_SIMP_TAC std_ss [] THEN
        PROVE_TAC[SUBSET_INTER_ABSORPTION],

        PROVE_TAC[DIFF_SUBSET_EMPTY, NOT_IN_EMPTY]
      ],

      Cases_on `(S1 INTER IMAGE f' (POW A.S) = {})` THENL [
        ASM_SIMP_TAC std_ss [IN_IMAGE, IN_POW, UNION_EMPTY, IN_UNION, GSPECIFICATION] THEN
        rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
          Q_TAC EXISTS_TAC `x` THEN
          ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
          METIS_TAC[],

          Q_TAC EXISTS_TAC `f l''` THEN
          ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
          METIS_TAC[],

          PROVE_TAC[NOT_IN_EMPTY]
        ],

        ASM_REWRITE_TAC[IN_IMAGE, IN_POW] THEN
        rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
          Q_TAC EXISTS_TAC `x` THEN
          ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
          METIS_TAC[],

          Q_TAC EXISTS_TAC `f' l''` THEN
          ASM_SIMP_TAC std_ss [NOT_IN_EMPTY] THEN
          METIS_TAC[],

          PROVE_TAC[NOT_IN_EMPTY]
        ]
      ]
    ]
  ]
]);

val SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON___USED_INPUT_VARS =
  store_thm (
    "SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON___USED_INPUT_VARS",
    ``!A f f' p. (FINITE A.S /\ (P_USED_VARS p SUBSET
      SEMI_AUTOMATON_USED_VARS A) /\
      DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A) /\
      DISJOINT (IMAGE f' (POW A.S)) (SEMI_AUTOMATON_USED_VARS A))    ==>
    (SEMI_AUTOMATON_USED_INPUT_VARS
      (SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON A f f' p) =
    SEMI_AUTOMATON_USED_INPUT_VARS A)``,

    rpt GEN_TAC THEN
    ASM_SIMP_TAC std_ss [SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def,
      SEMI_AUTOMATON_USED_INPUT_VARS_def,
      symbolic_semi_automaton_REWRITES,
      P_USED_VARS_EVAL, XP_USED_VARS_EVAL,
      XP_COND_def, P_BIGOR___P_USED_VARS,
      P_FORALL___P_USED_VARS, VAR_RENAMING_HASHTABLE_def,
      XP_FORALL___XP_USED_VARS,
      XP_EXISTS___XP_USED_VARS,
      XP_USED_VARS_def,
      XP_USED_VARS_EVAL,
      XP_BIGOR___XP_USED_VARS,
      SET_TO_LIST_INV, UNION_EMPTY,
      P_PROP_SET_MODEL___P_USED_VARS] THEN

    ONCE_REWRITE_TAC[EXTENSION] THEN
    rpt STRIP_TAC THEN

    ASM_SIMP_TAC std_ss [IN_UNION, IN_DIFF,
      IN_LIST_BIGUNION, MEM_MAP, GSYM LEFT_EXISTS_AND_THM,
      MEM_SET_TO_LIST, FINITE_POW_IFF, IMAGE_FINITE,
      IN_IMAGE, P_USED_VARS_EVAL, IN_SING,
      XP_USED_VARS_EVAL,
      IN_POW,
      P_PROP_SET_MODEL___P_USED_VARS, NOT_IN_EMPTY] THEN

    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_POW,
      IN_IMAGE, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION,
      XP_USED_VARS_def] THEN

    EQ_TAC THEN rpt STRIP_TAC THEN
    METIS_TAC[SUBSET_DEF, IN_UNION]);

val SYMBOLIC___NDET_FG___TO___DET_FG___CONCRETE_THM =
  store_simp_thm ("SYMBOLIC___NDET_FG___TO___DET_FG___CONCRETE_THM",

``!A p f f' A' p'.
  (FINITE A.S /\
  (P_USED_VARS p SUBSET A.S) /\
  (A' = SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON A f f' p) /\
  (p' =  (P_BIGOR (SET_TO_LIST
                       (IMAGE (\s. P_PROP (f' s)) (POW A.S))))) /\
  INJ f (POW A.S) UNIV /\
  INJ f' (POW A.S) UNIV /\
  DISJOINT (IMAGE f (POW A.S)) (SEMI_AUTOMATON_USED_VARS A) /\
  DISJOINT (IMAGE f' (POW A.S)) (SEMI_AUTOMATON_USED_VARS A) /\
  DISJOINT (IMAGE f (POW A.S)) (IMAGE f' (POW A.S))) ==>

((!i.
(A_SEM i (A_NDET (A, ACCEPT_COND_FG p)) =
A_SEM i (A_NDET (A', ACCEPT_COND_FG p')))) /\
IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A')``,

rpt GEN_TAC THEN STRIP_TAC THEN

SUBGOAL_TAC `?inv_f. !x. (x IN POW A.S) ==> (inv_f (f x) = x)` THEN1 (
  PROVE_TAC[INJ_INVERSE]
) THEN
SUBGOAL_TAC `?inv_f'. !x. (x IN POW A.S) ==> (inv_f' (f' x) = x)` THEN1 (
  PROVE_TAC[INJ_INVERSE]
) THEN
`?g. g = \x. if (x IN IMAGE f (POW A.S)) then inv_f x else inv_f' x` by METIS_TAC[] THEN

rpt STRIP_TAC THENL [

  MATCH_MP_TAC SYMBOLIC___NDET_FG___TO___DET_FG___THM THEN

  Q_TAC EXISTS_TAC `SEMI_AUTOMATON_USED_VARS A` THEN
  Q_TAC EXISTS_TAC `f` THEN
  Q_TAC EXISTS_TAC `f'` THEN
  Q_TAC EXISTS_TAC `g` THEN
  Q_TAC EXISTS_TAC `\s. s SUBSET A.S /\ P_SEM s p` THEN

  ASM_REWRITE_TAC[] THEN
  rpt STRIP_TAC THENL [
    ASM_SIMP_TAC std_ss [P_USED_VARS_EVAL, P_BIGOR___P_USED_VARS,
      SUBSET_DEF, SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def,
      symbolic_semi_automaton_REWRITES, IN_LIST_BIGUNION, MEM_MAP,
      GSYM LEFT_EXISTS_AND_THM,
      MEM_SET_TO_LIST, IMAGE_FINITE, FINITE_POW_IFF,
      IN_IMAGE, IN_SING, IN_UNION] THEN
    PROVE_TAC[],

    MATCH_MP_TAC SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON___USED_INPUT_VARS THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEMI_AUTOMATON_USED_VARS_def] THEN
    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],

    MATCH_MP_TAC SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_THM THEN
    ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN
    SIMP_ALL_TAC std_ss [IN_POW, GSYM FORALL_AND_THM,
      GSYM IMP_CONJ_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN

    SUBGOAL_TAC `f z IN IMAGE f (POW A.S) /\
                f' z IN IMAGE f' (POW A.S)` THEN1 (
      ASM_SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
      PROVE_TAC[]
    ) THEN
    SUBGOAL_TAC `~(f' z IN IMAGE f (POW A.S))` THEN1 (
      PROVE_TAC[DISJOINT_DISJ_THM]
    ) THEN
    ASM_SIMP_TAC std_ss [],

    ASM_SIMP_TAC std_ss [P_SEM_THM, P_BIGOR_SEM, MEM_SET_TO_LIST,
      IMAGE_FINITE, FINITE_POW_IFF, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM] THEN
    SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE] THEN
    PROVE_TAC[]
  ],

  MATCH_MP_TAC SYMBOLIC_BREAKPOINT_CONSTRUCTION___IS_DET_TOTAL THEN
  Q_TAC EXISTS_TAC `A` THEN
  Q_TAC EXISTS_TAC `SEMI_AUTOMATON_USED_VARS A` THEN
  Q_TAC EXISTS_TAC `f` THEN
  Q_TAC EXISTS_TAC `f'` THEN
  Q_TAC EXISTS_TAC `g` THEN
  Q_TAC EXISTS_TAC `\s. s SUBSET A.S /\ P_SEM s p` THEN

  MATCH_MP_TAC SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_THM THEN
  ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN
  SIMP_ALL_TAC std_ss [IN_POW, GSYM FORALL_AND_THM,
    GSYM IMP_CONJ_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN

  SUBGOAL_TAC `f z IN IMAGE f (POW A.S) /\
              f' z IN IMAGE f' (POW A.S)` THEN1 (
    ASM_SIMP_TAC std_ss [IN_IMAGE, IN_POW] THEN
    PROVE_TAC[]
  ) THEN
  SUBGOAL_TAC `~(f' z IN IMAGE f (POW A.S))` THEN1 (
    PROVE_TAC[DISJOINT_DISJ_THM]
  ) THEN
  ASM_SIMP_TAC std_ss []
]);

val KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_def =
  Define `KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE (ks:('a, 'b) kripke_structure) f =
          symbolic_kripke_structure
            (P_BIGOR (SET_TO_LIST ((IMAGE (\s. P_PROP_SET_MODEL (f s) (BIGUNION (IMAGE f ks.S))) ks.S0))))

            (XP_AND(
              XP_CURRENT(P_BIGAND (SET_TO_LIST (IMAGE
                (\s. P_IMPL(P_PROP_SET_MODEL (f s) (BIGUNION (IMAGE f ks.S)), P_PROP_SET_MODEL (ks.L s) (ks.P) )) ks.S))),

              XP_BIGOR (SET_TO_LIST ((IMAGE (\(s1, s2). XP_AND(XP_CURRENT (P_PROP_SET_MODEL (f s1) (BIGUNION (IMAGE f ks.S))), XP_NEXT (P_PROP_SET_MODEL (f s2) (BIGUNION (IMAGE f ks.S))))) ks.R)))))`;


val KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_THM =
  store_thm (
    "KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_THM",

    ``!K S f.

    IS_WELL_FORMED_KRIPKE_STRUCTURE K /\
    (S = (BIGUNION (IMAGE f K.S))) /\
    INJ f K.S UNIV /\
    (!s. s IN K.S ==> FINITE (f s)) /\
    DISJOINT S K.P ==>

    !p. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p =
        ((!n. p n IN K.S) /\ IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE
        (KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE K f)
        (\n. f (p n) UNION K.L (p n)))``,

REWRITE_TAC [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
rpt STRIP_TAC THEN
`FINITE K.S0` by PROVE_TAC[SUBSET_FINITE] THEN
`FINITE K.R` by PROVE_TAC[SUBSET_FINITE, FINITE_CROSS] THEN
SUBGOAL_TAC `FINITE (BIGUNION (IMAGE f K.S))` THEN1 (
  MATCH_MP_TAC FINITE_BIGUNION THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE, IN_IMAGE] THEN
  PROVE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
    IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
    PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
    KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_def,
    symbolic_kripke_structure_REWRITES,
    XP_SEM_THM, XP_SEM___XP_CURRENT,
    P_BIGAND_SEM, MEM_SET_TO_LIST,
    IMAGE_FINITE, IN_IMAGE,
    GSYM LEFT_FORALL_IMP_THM,
    P_SEM_THM,
    P_PROP_SET_MODEL_SEM,
    P_BIGOR_SEM, GSYM LEFT_EXISTS_AND_THM,
    XP_BIGOR_SEM,
    prove (``(?x:('b # 'b). P x) = ?s1 s2. P (s1, s2)``,
      METIS_TAC[PAIR]),
    XP_SEM___XP_NEXT] THEN

SUBGOAL_TAC `!n s. (s IN K.S /\ (p n) IN K.S) ==> (((f (p n) UNION (K.L (p n))) INTER BIGUNION (IMAGE f K.S) =
       f s INTER BIGUNION (IMAGE f K.S)) = (s = p n))` THEN1 (
  rpt STRIP_TAC THEN
  SUBGOAL_TAC `(f s INTER BIGUNION (IMAGE f K.S)) = f s` THEN1 (
    ONCE_REWRITE_TAC[EXTENSION] THEN
    SIMP_TAC std_ss [IN_UNION, IN_INTER, IN_BIGUNION, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM] THEN
    METIS_TAC[]
  ) THEN
  SUBGOAL_TAC `(f (p n) UNION K.L (p n)) INTER BIGUNION (IMAGE f K.S) = f (p n)` THEN1 (
    UNDISCH_NO_TAC 6 (*DISJOING S IMAGE g*) THEN
    ONCE_REWRITE_TAC[EXTENSION] THEN
    ASM_SIMP_TAC std_ss [IN_UNION, IN_INTER, DISJOINT_DISJ_THM,
      GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION,
      IN_IMAGE] THEN
    METIS_TAC[SUBSET_DEF]
  ) THEN
  ASM_REWRITE_TAC[] THEN

  METIS_TAC[INJ_DEF]
) THEN

EQ_TAC THENL [
  STRIP_TAC THEN
  `!n. p n IN K.S` by
    METIS_TAC[SUBSET_DEF, IN_CROSS, FST, SND] THEN
  rpt STRIP_TAC THENL [
    ASM_REWRITE_TAC[],

    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [] THEN
    STRIP_TAC THEN

    ONCE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN
    SIMP_TAC std_ss [IN_INTER, IN_UNION] THEN
    rpt BOOL_EQ_STRIP_TAC THEN
    CCONTR_TAC THEN
    REMAINS_TAC `x IN S` THEN1 METIS_TAC[DISJOINT_DISJ_THM] THEN
    ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
    PROVE_TAC[],

    Q_TAC EXISTS_TAC `p n` THEN
    Q_TAC EXISTS_TAC `p (SUC n)` THEN
    ASM_SIMP_TAC std_ss [],

    Q_TAC EXISTS_TAC `p 0` THEN
    ASM_SIMP_TAC std_ss []
  ],

  SIMP_TAC std_ss [FORALL_AND_THM] THEN
  rpt STRIP_TAC THENL [
    Q_SPEC_NO_ASSUM 2 `n` THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    `s1 IN K.S /\ s2 IN K.S` by METIS_TAC[IN_CROSS, SUBSET_DEF, FST, SND] THEN
    METIS_TAC[],

    METIS_TAC[SUBSET_DEF]
  ]
]);

val KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE___TRACE_OF_INITIAL_PATH =
  store_thm (
    "KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE___TRACE_OF_INITIAL_PATH",

    ``!K S f.

    IS_WELL_FORMED_KRIPKE_STRUCTURE K /\
    (S = (BIGUNION (IMAGE f K.S))) /\
    INJ f K.S UNIV /\
    (!s. s IN K.S ==> FINITE (f s)) /\
    DISJOINT S K.P ==>

    !p. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE
        (KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE K f) p ==>

        IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K
        (PATH_RESTRICT p K.P)``,

rpt GEN_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN

ASSUME_TAC (SIMP_RULE std_ss [] KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_THM) THEN
Q_SPECL_NO_ASSUM 0 [`K`, `f`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 PROVE_TAC[] THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

SIMP_ALL_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
`FINITE K.S0` by PROVE_TAC[SUBSET_FINITE] THEN
`FINITE K.R` by PROVE_TAC[SUBSET_FINITE, FINITE_CROSS] THEN
SUBGOAL_TAC `FINITE (BIGUNION (IMAGE f K.S))` THEN1 (
  MATCH_MP_TAC FINITE_BIGUNION THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE, IN_IMAGE] THEN
  PROVE_TAC[]
) THEN

ASM_SIMP_TAC std_ss [TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
  KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_def,
  PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
  symbolic_kripke_structure_REWRITES,
  XP_SEM_THM, P_SEM_THM, P_BIGOR_SEM,
  MEM_SET_TO_LIST, IMAGE_FINITE,
  IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
  XP_SEM___XP_CURRENT, XP_BIGOR_SEM,
  prove (``(?x:('b # 'b). P x) = ?s1 s2. P (s1, s2)``,
    METIS_TAC[PAIR]),
  P_BIGAND_SEM,
  GSYM LEFT_FORALL_IMP_THM, XP_SEM___XP_NEXT,
  P_PROP_SET_MODEL_SEM
  ] THEN

REWRITE_TAC [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
rpt STRIP_TAC THEN
rename1 `s IN K.S0` THEN
`FINITE K.S0` by PROVE_TAC[SUBSET_FINITE] THEN
`FINITE K.R` by PROVE_TAC[SUBSET_FINITE, FINITE_CROSS] THEN
SUBGOAL_TAC `FINITE (BIGUNION (IMAGE f K.S))` THEN1 (
  MATCH_MP_TAC FINITE_BIGUNION THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE, IN_IMAGE] THEN
  PROVE_TAC[]
) THEN

SUBGOAL_TAC `!s. s IN K.S ==> ((f s INTER BIGUNION (IMAGE f K.S)) = f s)` THEN1 (
  ONCE_REWRITE_TAC[EXTENSION] THEN
  SIMP_TAC std_ss [IN_UNION, IN_INTER, IN_BIGUNION, IN_IMAGE,
    GSYM RIGHT_EXISTS_AND_THM] THEN
  METIS_TAC[]
) THEN

SUBGOAL_TAC `!s'. s' IN K.S ==> ((f s' UNION (K.L s')) INTER BIGUNION (IMAGE f K.S) = f s')` THEN1 (
  rpt STRIP_TAC THEN
  UNDISCH_NO_TAC 8 (*DISJOING S K.P*) THEN
  ONCE_REWRITE_TAC[EXTENSION] THEN
  ASM_SIMP_TAC std_ss [IN_UNION, IN_INTER, DISJOINT_DISJ_THM,
    GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION,
    IN_IMAGE] THEN
  METIS_TAC[SUBSET_DEF]
) THEN

SUBGOAL_TAC `!s s'. (s IN K.S /\ s' IN K.S) ==> (((f s' UNION (K.L s')) INTER BIGUNION (IMAGE f K.S) =
       f s INTER BIGUNION (IMAGE f K.S)) = (s = s'))` THEN1 (
  rpt STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  METIS_TAC[INJ_DEF]
) THEN

SIMP_ALL_TAC std_ss [FORALL_AND_THM] THEN
rpt STRIP_TAC THEN
`?w'. w' = (CHOOSEN_PATH {s} (\s1 sn x. x IN K.S /\ (((f x) INTER BIGUNION (IMAGE f K.S)) = ((p sn) INTER BIGUNION (IMAGE f K.S)))))` by METIS_TAC[] THEN

Q_TAC EXISTS_TAC `w'` THEN

SUBGOAL_TAC `(!n. w' n IN K.S /\
                  (((p n) INTER BIGUNION (IMAGE f K.S)) = (f (w' n))))` THEN1 (
  ASM_REWRITE_TAC[] THEN
  Cases_on `n` THENL [
    SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING] THEN
    METIS_TAC[SUBSET_DEF],

    SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_ABS] THEN
    SELECT_ELIM_TAC THEN
    rpt STRIP_TAC THENL [
      Q_SPEC_NO_ASSUM 7 `n'` (*K.R def*) THEN
      CLEAN_ASSUMPTIONS_TAC THEN
      Q_TAC EXISTS_TAC `s2` THEN
      ASM_REWRITE_TAC[] THEN
      METIS_TAC[SUBSET_DEF, IN_CROSS, SND],

      ASM_REWRITE_TAC[],

      METIS_TAC[]
    ]
  ]
) THEN

GSYM_NO_TAC 1 (*Def w'*) THEN
ASM_SIMP_TAC std_ss [] THEN
rpt STRIP_TAC THENL [
  UNDISCH_NO_TAC 12 (*DISJOINT S K.P*) THEN
  ASM_REWRITE_TAC[] THEN
  `w' n IN K.S` by PROVE_TAC[] THEN
  UNDISCH_HD_TAC THEN
  rpt WEAKEN_HD_TAC THEN

  SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_BIGUNION, IN_IMAGE,
    EXTENSION, IN_INTER, IN_UNION] THEN
  METIS_TAC[],

  Q_TAC EXISTS_TAC `w' n` THEN
  Q_TAC EXISTS_TAC `w' (SUC n)` THEN
  ASM_SIMP_TAC std_ss [] THEN

  Q_SPEC_NO_ASSUM 8 `n` THEN
  CLEAN_ASSUMPTIONS_TAC THEN
  `s1 IN K.S /\ s2 IN K.S` by METIS_TAC[SUBSET_DEF, IN_CROSS, FST, SND] THEN
  NTAC 3 (UNDISCH_NO_TAC 2) THEN
  ASM_SIMP_TAC std_ss [] THEN
  METIS_TAC[INJ_DEF],

  Q_TAC EXISTS_TAC `w' 0` THEN
  GSYM_NO_TAC 0 (*Def w'*) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  GSYM_NO_TAC 0 (*Def w'*) THEN
  ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING] THEN
  METIS_TAC[SUBSET_DEF],

  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
  Q_SPECL_NO_ASSUM 7 [`x`, `w' x`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_SIMP_TAC std_ss [] THEN
  ASM_REWRITE_TAC[GSYM SUBSET_INTER_ABSORPTION] THEN
  METIS_TAC[]
]);

val UNIQUE_PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURES_ARE_ULTIMATIVELY_PERIODIC =
  store_thm (
    "UNIQUE_PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURES_ARE_ULTIMATIVELY_PERIODIC",

    ``!i S M. ((FINITE S /\ IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i) /\
              (!i'. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i' ==> (PATH_RESTRICT i' S = PATH_RESTRICT i S))) ==>
              (IS_ULTIMATIVELY_PERIODIC_PATH (PATH_RESTRICT i S))``,

SIMP_TAC std_ss [PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES] THEN
rpt STRIP_TAC THEN
ASSUME_TAC (INST_TYPE [alpha |-> alpha-->bool] INF_ELEMENTS_OF_PATH_NOT_EMPTY) THEN
Q_SPEC_NO_ASSUM 0 `POW (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)` THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  SIMP_TAC std_ss [FINITE_POW_IFF, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
    FINITE_UNION, FINITE___P_USED_VARS, FINITE___XP_USED_VARS]
) THEN
Q_SPEC_NO_ASSUM 0 `PATH_RESTRICT i (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)` THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, IN_POW, INTER_SUBSET]
) THEN

SIMP_ALL_TAC std_ss [GSYM MEMBER_NOT_EMPTY,
  INF_ELEMENTS_OF_PATH_def, GSPECIFICATION] THEN

SUBGOAL_TAC `?m0. (PATH_RESTRICT i (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M) m0 = x)` THEN1 (
  Q_SPEC_NO_ASSUM 0 `0:num` THEN
  PROVE_TAC[]
) THEN

SUBGOAL_TAC `?m1. (m1 > m0) /\
                  (PATH_RESTRICT i (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M) m1 = x)` THEN1 (
  METIS_TAC[]
) THEN

`?i'. i' = CUT_PATH_PERIODICALLY (PATH_RESTRICT i (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)) m0 (m1 - m0)` by METIS_TAC[] THEN

Q_SPEC_NO_ASSUM 5 `i'` THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  ASM_SIMP_TAC std_ss [] THEN
  rpt STRIP_TAC THENL [
    SIMP_TAC std_ss [CUT_PATH_PERIODICALLY_def, PATH_RESTRICT_def, PATH_MAP_def, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def] THEN
    Cases_on `SUC n < m0` THENL [
      ASM_SIMP_TAC arith_ss [] THEN
      PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_UNION],

      Cases_on `SUC n = m0` THENL [
        ASM_SIMP_TAC arith_ss [] THEN
        METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_UNION],

        `~(n < m0)` by DECIDE_TAC THEN
        NTAC 2 (WEAKEN_NO_TAC 1) THEN
        ASM_SIMP_TAC arith_ss [] THEN

        Cases_on `~(1 < m1 - m0)` THEN1 (
          `m1 - m0 = 1` by DECIDE_TAC THEN
          ASM_SIMP_TAC std_ss [MOD_1] THEN
          SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def,
            SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def] THEN
          `m1 = SUC m0` by DECIDE_TAC THEN
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_UNION]
        ) THEN

        Q.ABBREV_TAC `m' = m1 - m0` THEN
        SUBGOAL_TAC `(SUC n - m0) MOD m' = (1 + (n - m0) MOD m') MOD m'` THEN1 (
          SUBGOAL_TAC `1 MOD m' = 1` THEN1 (
            MATCH_RIGHT_EQ_MP_TAC X_MOD_Y_EQ_X THEN
            DECIDE_TAC
          ) THEN
          GSYM_NO_TAC 0 THEN ONCE_ASM_REWRITE_TAC [] THEN WEAKEN_HD_TAC THEN

          ASM_SIMP_TAC arith_ss [MOD_PLUS] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN
          DECIDE_TAC
        ) THEN
        ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN
        Q.ABBREV_TAC `r = (n - m0) MOD m'` THEN
        Cases_on `1 + r < m'` THENL [
          ASM_SIMP_TAC arith_ss [] THEN
          `m0 + (r + 1) = SUC (m0 + r)` by DECIDE_TAC THEN
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_UNION],

          SUBGOAL_TAC `1 + r = m'` THEN1 (
            `0 < m'` by DECIDE_TAC THEN
            `r < m'` by METIS_TAC [DIVISION] THEN
            DECIDE_TAC
          ) THEN
          ASM_SIMP_TAC arith_ss [] THEN

          SUBGOAL_TAC `m0 + r = PRE m1` THEN1 (
            `r = PRE m'` by DECIDE_TAC THEN
            Q.UNABBREV_TAC `m'` THEN
            DECIDE_TAC
          ) THEN
          `SUC (PRE m1) = m1` by DECIDE_TAC THEN
          SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def,
            SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def] THEN
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, SUBSET_UNION]
        ]
      ]
    ],

    `0 < (m1 - m0) + m0` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss [CUT_PATH_PERIODICALLY___BEGINNING] THEN
    SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def,
      SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def] THEN
    PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM, SUBSET_UNION]
  ]
) THEN

GSYM_NO_TAC 0 THEN
ASM_REWRITE_TAC[PATH_RESTRICT___CUT_PATH_PERIODICALLY,
                IS_ULTIMATIVELY_PERIODIC_PATH_def] THEN
Q_TAC EXISTS_TAC `m0` THEN
Q_TAC EXISTS_TAC `(m1 - m0)` THEN
ASM_SIMP_TAC arith_ss [CUT_PATH_PERIODICALLY___IS_ULTIMATIVELY_PERIODIC]
);

val ULTIMALTIVELY_PERIODIC_PATH_CORRESPONDING_TO_UNIQUE_PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURES =
  store_thm (
    "ULTIMALTIVELY_PERIODIC_PATH_CORRESPONDING_TO_UNIQUE_PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURES",

``!i S. (FINITE (S:'a set) /\ INFINITE (UNIV:'a set) /\
    (IS_ULTIMATIVELY_PERIODIC_PATH i)) ==>
      (?M.
          (?i'. (IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i')) /\
          (!i'. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i' ==> (PATH_RESTRICT i' S = PATH_RESTRICT i S)))``,

rpt STRIP_TAC THEN
ASSUME_TAC (INST_TYPE [beta |-> alpha] DET_TOTAL_KRIPKE_STRUCTURES_THM) THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
Q_SPECL_NO_ASSUM 0 [`S`, `PATH_RESTRICT i S`] THEN
POP_NO_ASSUM 0 (fn thm => ASSUME_TAC (fst (EQ_IMP_RULE thm))) THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  rpt STRIP_TAC THENL [
    SIMP_ALL_TAC std_ss [IS_ULTIMATIVELY_PERIODIC_PATH_def,
                         IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE_def] THEN
    Q_TAC EXISTS_TAC `n0` THEN
    Q_TAC EXISTS_TAC `n` THEN
    ASM_REWRITE_TAC[] THEN
    rpt STRIP_TAC THEN
    RES_TAC THEN
    ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def],

    ASM_REWRITE_TAC[],

    ASM_SIMP_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def,
      INTER_SUBSET]
  ]
) THEN
CLEAN_ASSUMPTIONS_TAC THEN
GSYM_NO_TAC 1 (*M.P = S*) THEN
FULL_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

SUBGOAL_TAC `?f. INJ f M.S UNIV /\ DISJOINT (IMAGE f M.S) M.P` THEN1 (
  MATCH_MP_TAC (SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,
                              AND_IMP_INTRO] FINITE_INJ_EXISTS) THEN
  SIMP_ALL_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
  ASM_REWRITE_TAC[]
) THEN

ASSUME_TAC (SIMP_RULE std_ss [] ((INST_TYPE [beta |-> alpha, gamma |-> alpha] KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE_THM))) THEN
Q_SPECL_NO_ASSUM 0 [`M`, `\x. {f x}`] THEN

PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  ASM_SIMP_TAC std_ss [FINITE_SING, INJ_DEF, IN_UNIV, EQUAL_SING] THEN
  UNDISCH_HD_TAC (*DISJ IMAGE f M.P*) THEN
  UNDISCH_HD_TAC (*INJ f*) THEN
  SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_BIGUNION, IN_IMAGE,
    GSYM RIGHT_FORALL_OR_THM, IN_SING, INJ_DEF]
) THEN

SIMP_ALL_TAC std_ss [IMAGE_ID, UNION_SING] THEN
Q_TAC EXISTS_TAC `KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE M
                   (\x. {f x})` THEN
rpt STRIP_TAC THENL [
  UNDISCH_NO_TAC 4 (*IS_TRACE_OF_INITIAL_PATH*)   THEN
  ASM_SIMP_TAC std_ss [IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
  METIS_TAC[],

  ASSUME_TAC (SIMP_RULE std_ss [] (INST_TYPE [beta |-> alpha]
  KRIPKE_STRUCTURE___TO___SYMBOLIC_KRIPKE_STRUCTURE___TRACE_OF_INITIAL_PATH)) THEN
  Q_SPECL_NO_ASSUM 0 [`M`, `(\x. {f x})`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    ASM_SIMP_TAC std_ss [FINITE_SING, INJ_DEF, IN_UNIV, EQUAL_SING] THEN
    UNDISCH_NO_TAC 2 (*DISJ IMAGE f M.P*) THEN
    UNDISCH_NO_TAC 2 (*INJ f*) THEN
    SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_BIGUNION, IN_IMAGE,
      GSYM RIGHT_FORALL_OR_THM, IN_SING, INJ_DEF]
  ) THEN
  METIS_TAC[]
]);

val SYMBOLIC___UNIV_G___TO___DET_GF___EXISTS_THM =
  store_thm (
    "SYMBOLIC___UNIV_G___TO___DET_GF___EXISTS_THM",

    ``!S A (p:'a prop_logic). (INFINITE (UNIV:'a set)  /\ FINITE S /\ FINITE A.S) ==>

?A' p'. ((IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A') /\
        (DISJOINT A'.S S) /\ FINITE A'.S /\
        (P_USED_VARS p' SUBSET A'.S) /\
        (!i. A_SEM i (A_UNIV (A,ACCEPT_COND_G p)) =
             A_SEM i (A_UNIV (A',ACCEPT_COND_GF p'))))``,

rpt STRIP_TAC THEN
SUBGOAL_TAC `!A p i. (A_SEM i (A_UNIV (A,ACCEPT_COND_G p)) =
                  ~A_SEM i (A_NDET (A,ACCEPT_COND_F (P_NOT p)))) /\
                     (A_SEM i (A_UNIV (A,ACCEPT_COND_GF p)) =
                  ~A_SEM i (A_NDET (A,ACCEPT_COND_FG (P_NOT p))))` THEN1 (
  SIMP_TAC std_ss [A_SEM_THM, ACCEPT_COND_FG_def, ACCEPT_COND_GF_def,
    ACCEPT_COND_F_def, ACCEPT_COND_G_def, ACCEPT_COND_SEM_def,
    ACCEPT_COND_SEM_TIME_def, ACCEPT_F_def, P_SEM_THM] THEN
  METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

SUBGOAL_TAC `?x. ~(x IN SEMI_AUTOMATON_USED_VARS A UNION P_USED_VARS p)` THEN1 (
  REMAINS_TAC `FINITE (SEMI_AUTOMATON_USED_VARS A UNION P_USED_VARS p)` THEN1 (
    METIS_TAC[IN_INFINITE_NOT_FINITE, IN_UNIV]
  ) THEN
  ASM_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, FINITE_UNION,
    FINITE___P_USED_VARS, FINITE___SEMI_AUTOMATON_USED_INPUT_VARS]
) THEN

ASSUME_TAC (REWRITE_RULE [AUTOMATON_EQUIV_def] A_SEM___NDET_F___TO___NDET_FG) THEN
Q_SPECL_NO_ASSUM 0 [`A`, `P_NOT p`, `x`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[P_USED_VARS_def] THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

Q.ABBREV_TAC `B = (symbolic_semi_automaton (x INSERT A.S)
                     (P_AND (P_EQUIV (P_PROP x,P_NOT p),A.S0))
                     (XP_AND
                        (XP_EQUIV
                           (XP_NEXT_PROP x,
                            XP_OR (XP_PROP x,XP_NEXT (P_NOT p))),A.R)))` THEN
SUBGOAL_TAC `?f. INJ f (POW B.S) UNIV /\ DISJOINT (IMAGE f (POW B.S)) (SEMI_AUTOMATON_USED_VARS B UNION S)` THEN1 (
  MATCH_MP_TAC (SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,
    AND_IMP_INTRO] FINITE_INJ_EXISTS) THEN
  Q.UNABBREV_TAC `B` THEN
  ASM_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES,
    FINITE_POW_IFF, FINITE_INSERT, SEMI_AUTOMATON_USED_VARS_def,
    FINITE_UNION, FINITE___SEMI_AUTOMATON_USED_INPUT_VARS]
) THEN

SUBGOAL_TAC `?f'. INJ f' (POW B.S) UNIV /\ DISJOINT (IMAGE f' (POW B.S)) (SEMI_AUTOMATON_USED_VARS B UNION (IMAGE f (POW B.S)) UNION S)` THEN1 (
  MATCH_MP_TAC (SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,
    AND_IMP_INTRO] FINITE_INJ_EXISTS) THEN
  Q.UNABBREV_TAC `B` THEN
  ASM_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES,
    FINITE_POW_IFF, FINITE_INSERT, SEMI_AUTOMATON_USED_VARS_def,
    FINITE_UNION, FINITE___SEMI_AUTOMATON_USED_INPUT_VARS,
    IMAGE_FINITE]
) THEN

ASSUME_TAC SYMBOLIC___NDET_FG___TO___DET_FG___CONCRETE_THM THEN
Q_SPECL_NO_ASSUM 0 [`B`, `P_PROP x`, `f`, `f'`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  FULL_SIMP_TAC std_ss [DISJOINT_UNION_BOTH, DISJOINT_SYM] THEN
  Q.UNABBREV_TAC `B` THEN
  ASM_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES, FINITE_INSERT,
    P_USED_VARS_def, SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY]
) THEN
CLEAN_ASSUMPTIONS_TAC THEN

Q_TAC EXISTS_TAC `SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON B f f' (P_PROP x)` THEN
Q_TAC EXISTS_TAC `P_NOT (P_BIGOR (SET_TO_LIST (IMAGE (\s. P_PROP (f' s)) (POW B.S))))` THEN

ASM_SIMP_TAC std_ss [] THEN
rpt STRIP_TAC THENL [
  FULL_SIMP_TAC std_ss [SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def,
    symbolic_semi_automaton_REWRITES, DISJOINT_UNION_BOTH, DISJOINT_SYM],

  Q.UNABBREV_TAC `B` THEN
  FULL_SIMP_TAC std_ss [SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def,
    symbolic_semi_automaton_REWRITES, IMAGE_FINITE, FINITE_UNION, FINITE_POW_IFF, FINITE_INSERT],

  Q.UNABBREV_TAC `B` THEN
  ASM_SIMP_TAC std_ss [SYMBOLIC_BREAKPOINT_CONSTRUCTION_AUTOMATON_def,
    symbolic_semi_automaton_REWRITES,
    P_BIGOR___P_USED_VARS, SUBSET_DEF, IN_LIST_BIGUNION, IN_UNION,
    MEM_MAP, MEM_SET_TO_LIST, FINITE_POW_IFF, FINITE_INSERT,
    IMAGE_FINITE, GSYM LEFT_EXISTS_AND_THM, IN_IMAGE, P_USED_VARS_def,
    IN_SING] THEN
  METIS_TAC[],

  ASM_SIMP_TAC std_ss [A_SEM_THM, ACCEPT_COND_FG_def, ACCEPT_COND_SEM_def,
    ACCEPT_COND_SEM_TIME_def, ACCEPT_F_def, P_SEM_def]
]);

val TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_PRODUCT_THM =
 store_thm
  ("TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_PRODUCT_THM",

``!A B i w ac . (IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A /\
      (DISJOINT B.S (SEMI_AUTOMATON_USED_VARS A)) /\
      IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) ==>

      (A_SEM i (A_UNIV (PRODUCT_SEMI_AUTOMATON A B, ac)) =
       A_SEM (INPUT_RUN_PATH_UNION A i w) (A_UNIV (B, ac)))``,

rpt STRIP_TAC THEN
SIMP_TAC std_ss [A_SEM_THM] THEN
SUBGOAL_TAC `
  !w'. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (PRODUCT_SEMI_AUTOMATON A B) i w' =
       (PATH_SUBSET w' (A.S UNION B.S) /\ (PATH_RESTRICT w' A.S = w) /\
        (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON B (INPUT_RUN_PATH_UNION A i w) (PATH_RESTRICT w' B.S)))` THEN1 (

  SUBGOAL_TAC `!x. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i x ==> (x = w)` THEN1 (
    METIS_TAC[TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]
  ) THEN
  GEN_TAC THEN
  NTAC 2 UNDISCH_HD_TAC THEN
  REWRITE_TAC [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def, PRODUCT_SEMI_AUTOMATON_REWRITES, P_SEM_THM, IS_TRANSITION_def,
  INPUT_RUN_STATE_UNION_def, INPUT_RUN_PATH_UNION_def] THEN
  rpt STRIP_TAC THEN
  SIMP_ALL_TAC std_ss [XP_SEM_THM, P_SEM_THM, FORALL_AND_THM] THEN
  rpt BOOL_EQ_STRIP_TAC THEN
  SUBGOAL_TAC `P_SEM (w' 0 UNION (i 0 DIFF (A.S UNION B.S))) A.S0 =
               P_SEM ((PATH_RESTRICT w' A.S) 0 UNION (i 0 DIFF A.S)) A.S0` THEN1 (
    ONCE_REWRITE_TAC[P_USED_VARS_INTER_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_NO_TAC 5 (*DISJOINT B.S *)THEN
    UNDISCH_HD_TAC (*w' n SUBSET *) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [DISJOINT_DISJ_THM, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, EXTENSION, PATH_RESTRICT_def, IN_INTER, PATH_MAP_def, IN_DIFF, SUBSET_DEF] THEN
    METIS_TAC[]
  ) THEN

  SUBGOAL_TAC `!n. XP_SEM A.R (w' n UNION (i n DIFF (A.S UNION B.S)),
                               w' (SUC n) UNION (i (SUC n) DIFF (A.S UNION B.S))) =
                   XP_SEM A.R ((PATH_RESTRICT w' A.S) n UNION (i n DIFF A.S), (PATH_RESTRICT w' A.S) (SUC n) UNION (i (SUC n) DIFF A.S)) ` THEN1 (
    GEN_TAC THEN
    ONCE_REWRITE_TAC[XP_USED_VARS_INTER_THM] THEN
    AP_TERM_TAC THEN
    UNDISCH_NO_TAC 6 (*DISJOINT B.S *)THEN
    UNDISCH_NO_TAC 1 (*w' n SUBSET *) THEN
    rpt WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [DISJOINT_DISJ_THM, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION, EXTENSION, PATH_RESTRICT_def, IN_INTER, PATH_MAP_def, IN_DIFF, SUBSET_DEF,
      XP_USED_VARS_def] THEN
    METIS_TAC[]
  ) THEN
  ASM_REWRITE_TAC[] THEN NTAC 2 WEAKEN_HD_TAC THEN

  EQ_TAC THENL [
    STRIP_TAC THEN
    Q_SPEC_NO_ASSUM 5 `PATH_RESTRICT w' A.S` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1  (
      ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET]
    ) THEN
    ASM_REWRITE_TAC[] THEN

    SUBGOAL_TAC `!n. (PATH_RESTRICT w' B.S n UNION (w n UNION (i n DIFF A.S) DIFF B.S)) = (w' n UNION (i n DIFF (A.S UNION B.S)))` THEN1 (
      GSYM_NO_TAC 0 THEN
      UNDISCH_NO_TAC 5 (*PATH_SUBSET w' n*) THEN
      UNDISCH_NO_TAC 8 (*DISJOINT B.S*) THEN
      ASM_REWRITE_TAC[] THEN
      rpt WEAKEN_HD_TAC THEN

      SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, DISJOINT_DISJ_THM,
        SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, SUBSET_DEF, IN_UNION,
        EXTENSION, IN_INTER, IN_DIFF] THEN
      METIS_TAC[]
    ) THEN
    ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET],

    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN

    SUBGOAL_TAC `!n. (PATH_RESTRICT w' B.S n UNION (w n UNION (i n DIFF A.S) DIFF B.S)) = (w' n UNION (i n DIFF (A.S UNION B.S)))` THEN1 (
      GSYM_NO_TAC 3  (*w = PATH_RESTRICT*) THEN
      UNDISCH_NO_TAC 4 (*PATH_SUBSET w' n*) THEN
      UNDISCH_NO_TAC 8 (*DISJOINT B.S*) THEN
      ASM_REWRITE_TAC[] THEN
      rpt WEAKEN_HD_TAC THEN

      SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, DISJOINT_DISJ_THM,
        SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, SUBSET_DEF, IN_UNION,
        EXTENSION, IN_INTER, IN_DIFF] THEN
      METIS_TAC[]
    ) THEN
    METIS_TAC[]
  ]
) THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

EQ_TAC THENL [
  rpt STRIP_TAC THEN
  `PATH_SUBSET w A.S /\ PATH_SUBSET w' B.S` by METIS_TAC[IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
  SUBGOAL_TAC `!x. ~(x IN A.S) \/ ~(x IN B.S)` THEN1 (
    FULL_SIMP_TAC std_ss [DISJOINT_DISJ_THM, SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, IN_UNION] THEN
    METIS_TAC[]
  ) THEN

  Q_SPEC_NO_ASSUM 4 `PATH_UNION w w'` THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    rpt STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, PATH_SUBSET_def, PATH_UNION_def, IN_UNION] THEN
      METIS_TAC[],

      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, PATH_RESTRICT_def, PATH_UNION_def, IN_UNION, PATH_MAP_def, EXTENSION, IN_INTER] THEN
      METIS_TAC[],

      REMAINS_TAC `(PATH_RESTRICT (PATH_UNION w w') B.S) = w'` THEN1 (
        ASM_REWRITE_TAC[]
      ) THEN
      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, PATH_RESTRICT_def, PATH_UNION_def, IN_UNION, PATH_MAP_def, EXTENSION, IN_INTER] THEN
      METIS_TAC[]
    ]
  ) THEN

  UNDISCH_HD_TAC THEN
  IMP_TO_EQ_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF,
    INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
    PRODUCT_SEMI_AUTOMATON_REWRITES, PATH_UNION_def, EXTENSION,
    IN_UNION, IN_DIFF] THEN
  METIS_TAC[],

  rpt STRIP_TAC THEN
  Q_SPEC_NO_ASSUM 3 `PATH_RESTRICT w' B.S` THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
  UNDISCH_HD_TAC THEN
  IMP_TO_EQ_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN

  GSYM_NO_TAC 1 (*Def w*) THEN
  UNDISCH_NO_TAC 2 (*PATH_SUBSET w'*) THEN
  ASM_REWRITE_TAC[] THEN
  FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF,
    INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
    PRODUCT_SEMI_AUTOMATON_REWRITES, PATH_UNION_def, EXTENSION,
    IN_UNION, IN_DIFF, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
  METIS_TAC[]
]);

val _ = export_theory ();
