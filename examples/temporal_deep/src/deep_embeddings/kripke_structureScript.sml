open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (Globals.HOLDIR ^ "/examples/temporal_deep/");
loadPath := (home_dir ^ "src/deep_embeddings") ::
            (home_dir ^ "src/tools") :: !loadPath;

map load
 ["xprop_logicTheory", "prop_logicTheory", "infinite_pathTheory", "pred_setTheory", "listTheory", "pairTheory", "set_lemmataTheory",
   "containerTheory", "prim_recTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory", "arithmeticTheory"];
*)

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
     tuerk_tacticsLib temporal_deep_mixedTheory arithmeticTheory;
open Sanity;

val _ = hide "S";
val _ = hide "I";
val _ = hide "K";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val _ = new_theory "kripke_structure";
val _ = ParseExtras.temp_loose_equality()


val kripke_structure_def =
 Hol_datatype
  `kripke_structure =
    <| S:  'state set;                     (*set of states *)
       S0: 'state set;                     (*initial states*)
       R:  ('state # 'state) set;          (*transition relation*)
       P:  'label set;                     (*set of used labels *)
       L:  'state -> ('label set)          (*label function*) |>`;

Theorem kripke_structure_REWRITES =
        LIST_CONJ (TypeBase.one_one_of “:(α,β)kripke_structure” ::
                   TypeBase.accessors_of “:(α,β)kripke_structure”)


val IS_WELL_FORMED_KRIPKE_STRUCTURE_def =
 Define
  `IS_WELL_FORMED_KRIPKE_STRUCTURE K =
    (FINITE K.S /\ FINITE K.P /\ K.S0 SUBSET K.S /\
     K.R SUBSET (K.S CROSS K.S) /\
     (!s. (s IN K.S) ==> (K.L s) SUBSET K.P))`


val simple_kripke_structure_def =
 Define
  `simple_kripke_structure S B R =
   kripke_structure S B R (POW S) (\s. {p | p SUBSET S /\ s IN p})`;



val universal_kripke_structure_def =
 Define
  `universal_kripke_structure S P L =
   kripke_structure S S (S CROSS S) P L`;


val IS_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_PATH_THROUGH_KRIPKE_STRUCTURE K p =
     (!n. (p n, p (SUC n)) IN K.R)`;

val IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE K FC p =
     (IS_PATH_THROUGH_KRIPKE_STRUCTURE K p /\
      (!b. MEM b FC ==> (!t0. ?t. t > t0 /\ (P_SEM (K.L (p t)) b))))`;


val IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p =
     (IS_PATH_THROUGH_KRIPKE_STRUCTURE K p /\ p 0 IN K.S0)`;

val IS_FAIR_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_FAIR_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K FC p =
     (IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE K FC p /\
      p 0 IN K.S0)`;


val IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE___EMPTY_FAIRNESS =
  store_thm (
    "IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE___EMPTY_FAIRNESS",
    ``!K p. (IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE K [] p =
             IS_PATH_THROUGH_KRIPKE_STRUCTURE K p) /\
            (IS_FAIR_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K [] p =
             IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p)``,

      SIMP_TAC list_ss [IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE_def,
        IS_FAIR_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
        IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def]);


val TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p =
     (\n:num. K.L (p n))`;

val IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p =
    (?p'. IS_PATH_THROUGH_KRIPKE_STRUCTURE K p' /\
          (p = TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p'))`;


val IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def =
 Define
  `IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p =
    (?p'. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p' /\
          (p = TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p'))`;


val PATH_THROUGH_KRIPKE_STRUCTURE___RESTN =
  store_thm (
    "PATH_THROUGH_KRIPKE_STRUCTURE___RESTN",
    ``!n K FC p. (IS_PATH_THROUGH_KRIPKE_STRUCTURE K p ==> IS_PATH_THROUGH_KRIPKE_STRUCTURE K (PATH_RESTN p n)) /\
                 (IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE K FC p ==> IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE K FC (PATH_RESTN p n)) /\
                 (IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p ==> IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K (PATH_RESTN p n))``,

  SIMP_TAC arith_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def, PATH_RESTN_def,
    IS_FAIR_PATH_THROUGH_KRIPKE_STRUCTURE_def,
    IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
    TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC[arithmeticTheory.ADD_SUC],
    PROVE_TAC[arithmeticTheory.ADD_SUC],

    RES_TAC THEN
    SPECL_NO_ASSUM 0 [``n + t0``] THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    EXISTS_TAC ``t - n`` THEN
    REPEAT STRIP_TAC THENL [
      DECIDE_TAC,

      `n + (t - n) = t` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[]
    ],

    EXISTS_TAC ``\m:num. (p' (n + m)):'a set`` THEN
    REPEAT STRIP_TAC THENL [
      METIS_TAC[arithmeticTheory.ADD_SUC],

      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_SIMP_TAC std_ss []
    ]
  ]);


val IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE_def =
 Define
  `IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s =
    (?p n. (p 0 IN K.S0) /\ ((p n) = s) /\
         (!m. m < n ==> (p m, p (SUC m)) IN K.R))`;

val IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE___RECURSIVE_DEF =
  store_thm ("IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE___RECURSIVE_DEF",
  ``!K s. IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s =
    ((s IN K.S0) \/ (?s'. IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s' /\
                         (s', s) IN K.R))``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE_def] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      GSYM_NO_TAC 1 THEN ASM_REWRITE_TAC [] THEN WEAKEN_HD_TAC THEN
      Induct_on `n` THENL [
        ASM_REWRITE_TAC[],

        REPEAT STRIP_TAC THEN
        DISJ2_TAC THEN
        `!P. (!m. ((m < SUC n) ==> P m)) =
                         ((!m. ((m < n) ==> P m)) /\ P n)` by (
          REPEAT WEAKEN_HD_TAC THEN
          REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            `m < SUC n` by DECIDE_TAC THEN RES_TAC,
            `n < SUC n` by DECIDE_TAC THEN RES_TAC,

            Cases_on `m < n` THENL [
              RES_TAC,
              `m = n` by DECIDE_TAC THEN ASM_REWRITE_TAC[]
            ]
          ]
        ) THEN
        FULL_SIMP_TAC std_ss [] THEN
        WEAKEN_HD_TAC THEN
        EXISTS_TAC ``(p:num->'b) (n:num)`` THEN
        ASM_REWRITE_TAC[] THEN
        EXISTS_TAC ``p:num->'b`` THEN
        EXISTS_TAC ``n:num`` THEN
        ASM_REWRITE_TAC[]
      ],


      EXISTS_TAC ``\n:num. s:'b`` THEN
      EXISTS_TAC ``0:num`` THEN
      ASM_SIMP_TAC arith_ss [],


      EXISTS_TAC ``\n':num. if (n' <= n) then (p n') else (s:'b)`` THEN
      EXISTS_TAC ``SUC n`` THEN
      ASM_SIMP_TAC arith_ss [] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `SUC m <= n` THENL [
        `m < n` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [],

        `m = n` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss []
      ]
    ]);


val IS_TOTAL_KRIPKE_STRUCTURE_def =
 Define
  `IS_TOTAL_KRIPKE_STRUCTURE K =
    (~(K.S0 = EMPTY) /\
    (!s. (IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s) ==>
        (?s'. (s, s') IN K.R)))`;


val IS_TOTAL_KRIPKE_STRUCTURE___PATH_EXISTS =
 store_thm ("IS_TOTAL_KRIPKE_STRUCTURE___PATH_EXISTS",
  ``!K s. (IS_TOTAL_KRIPKE_STRUCTURE K /\
          IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s) ==>
          (?p. (((p 0) = s) /\ IS_PATH_THROUGH_KRIPKE_STRUCTURE K p))``,


  SIMP_TAC std_ss [IS_TOTAL_KRIPKE_STRUCTURE_def] THEN
  REPEAT STRIP_TAC THEN
  `?p. p = CHOOSEN_PATH {s} (\s n. {s' | (s, s') IN K.R})` by METIS_TAC[] THEN
  `p 0 = s` by (
    ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING]
  ) THEN
  `!n. IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K (p n)` by (
    Induct_on `n` THENL [
      ASM_REWRITE_TAC[],

      ONCE_REWRITE_TAC[IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE___RECURSIVE_DEF] THEN
      DISJ2_TAC THEN
      EXISTS_TAC ``(p:num->'b) n`` THEN
      ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, GSPECIFICATION] THEN
      SELECT_ELIM_TAC THEN
      METIS_TAC[]
    ]
  ) THEN
  `!n. (p n, p (SUC n)) IN K.R` by (
    ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, GSPECIFICATION] THEN
    METIS_TAC[]
  ) THEN
  WEAKEN_NO_TAC 3 (*Def p*) THEN
  EXISTS_TAC ``p:num->'b`` THEN
  ASM_REWRITE_TAC[IS_PATH_THROUGH_KRIPKE_STRUCTURE_def]);



val IS_TOTAL_KRIPKE_STRUCTURE___INITIAL_PATH_EXISTS =
 store_thm ("IS_TOTAL_KRIPKE_STRUCTURE___INITIAL_PATH_EXISTS",
  ``!K s. (IS_TOTAL_KRIPKE_STRUCTURE K /\
          IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s) ==>
          (?p n. (((p n) = s) /\ IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p))``,




  REPEAT STRIP_TAC THEN
  `?p'. ((p' 0) = s) /\ IS_PATH_THROUGH_KRIPKE_STRUCTURE K p'` by METIS_TAC[
    IS_TOTAL_KRIPKE_STRUCTURE___PATH_EXISTS] THEN
  SIMP_ALL_TAC std_ss [IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE_def] THEN

  `?q. q = (\m. if m <= n then p m else p' (m-n))` by METIS_TAC[] THEN
  EXISTS_TAC ``q:num->'b`` THEN
  EXISTS_TAC ``n:num`` THEN
  FULL_SIMP_TAC arith_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        IS_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
  GEN_TAC THEN
  Cases_on `SUC n' <= n` THENL [
    ASM_SIMP_TAC arith_ss [],

    Cases_on `~(n' <= n)` THENL [
      ASM_SIMP_TAC arith_ss [] THEN
      `(SUC n' - n) = SUC (n' - n)` by DECIDE_TAC THEN
      PROVE_TAC[],

      `(n' = n) /\ ((SUC n') - n = (SUC 0))` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      PROVE_TAC[]
    ]
  ]);


val IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE_def =
 Define
  `IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE K =
    (IS_TOTAL_KRIPKE_STRUCTURE K /\
     (!s. s IN K.S ==> IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE K s))`;


val IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE___ALTERNATIVE_DEF =
 store_thm ("IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE___ALTERNATIVE_DEF",

  ``!K. (IS_WELL_FORMED_KRIPKE_STRUCTURE K) ==>
      (IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE K =
        (~(K.S = EMPTY) /\ (!s. s IN K.S ==>
          (?p n. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p /\
                ((p n) = s)))))``,

  SIMP_TAC std_ss [IS_TOTAL_COMPLETELY_REACHABLE_KRIPKE_STRUCTURE_def] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [IS_TOTAL_KRIPKE_STRUCTURE_def,
      IS_WELL_FORMED_KRIPKE_STRUCTURE_def, SUBSET_EMPTY],

    METIS_TAC[IS_TOTAL_KRIPKE_STRUCTURE___INITIAL_PATH_EXISTS],

    SIMP_TAC std_ss [IS_TOTAL_KRIPKE_STRUCTURE_def] THEN
    REPEAT STRIP_TAC THENL [
      `?s. s IN K.S` by PROVE_TAC[MEMBER_NOT_EMPTY] THEN
      RES_TAC THEN
      SIMP_ALL_TAC std_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
      PROVE_TAC[MEMBER_NOT_EMPTY],

      SIMP_ALL_TAC std_ss [IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE_def,
                           IS_WELL_FORMED_KRIPKE_STRUCTURE_def, SUBSET_DEF,
                           IN_CROSS] THEN
      `s IN K.S` by (
        Cases_on `n` THENL [
          PROVE_TAC[],

          `n' < SUC n'` by DECIDE_TAC THEN
          PROVE_TAC[SND]
        ]
      ) THEN
      RES_TAC THEN
      SIMP_ALL_TAC std_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                           IS_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
      METIS_TAC[SND]
    ],


    RES_TAC THEN
    SIMP_ALL_TAC std_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                         IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                         IS_REACHABLE_STATE_OF_KRIPKE_STRUCTURE_def] THEN
    METIS_TAC[]
  ]);




val IS_WELL_FORMED_KRIPKE_STRUCTURE_def =
 Define
  `IS_WELL_FORMED_KRIPKE_STRUCTURE K =
    (FINITE K.S /\ FINITE K.P /\ K.S0 SUBSET K.S /\
     K.R SUBSET (K.S CROSS K.S) /\
     (!s. (s IN K.S) ==> (K.L s) SUBSET K.P))`



val LANGUAGE_OF_KRIPKE_STRUCTURE_def =
 Define
  `LANGUAGE_OF_KRIPKE_STRUCTURE K  =
    {p | IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p}`;


val KRIPKE_STRUCTURE___PATHS_AND_TRACES_PATH_SUBSET =
  store_thm (
    "KRIPKE_STRUCTURE___PATHS_AND_TRACES_PATH_SUBSET",
    ``!K p p'.  (IS_WELL_FORMED_KRIPKE_STRUCTURE K) ==>
           (((IS_PATH_THROUGH_KRIPKE_STRUCTURE K p) ==> (!n. p n IN K.S)) /\
            (IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p ==>
             IS_PATH_THROUGH_KRIPKE_STRUCTURE K p) /\
            (IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p' ==> (PATH_SUBSET p' K.P)) /\
            ((IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p') ==>
             (IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p')))``,

      SIMP_TAC std_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       IS_WELL_FORMED_KRIPKE_STRUCTURE_def, SUBSET_DEF,
                       IN_CROSS,
                       IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       PATH_SUBSET_def] THEN
      METIS_TAC[FST]);



Theorem DET_TOTAL_KRIPKE_STRUCTURES_THM:
  INFINITE (UNIV:'b set) ==>
  (!S i. ((IS_ULTIMATIVELY_PERIODIC_PATH i /\ FINITE S /\ PATH_SUBSET i S)=
          (?M:('a, 'b) kripke_structure.
             IS_WELL_FORMED_KRIPKE_STRUCTURE M /\
             (M.P = S) /\
             IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE M i /\
             (!j. IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE M j ==>
                  (j = i)))))
Proof

REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  FULL_SIMP_TAC std_ss [IS_ULTIMATIVELY_PERIODIC_PATH_def,
                       IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE___ALTERNATIVE_DEF] THEN
  `?el. IS_ELEMENT_ITERATOR el (n+n0) ({}:'b set)` by
    PROVE_TAC[IS_ELEMENT_ITERATOR_EXISTS, FINITE_EMPTY] THEN
  `?el'. !m. m < (n+n0) ==> ((el' (el m)) = m)` by
    PROVE_TAC[IS_ELEMENT_ITERATOR___INVERSE] THEN

  `?M. M = kripke_structure (IMAGE el (count (n+n0)))
                            {(el 0)}
                            (\(s1,s2). ((s2 = el n0) /\ (s1 = el (PRE (n+n0)))) \/
                                        (?m. (SUC m < (n+n0)) /\ (el m = s1) /\
                                             (el (SUC m) = s2)))
                            S
                            (\x. i (el' x))` by METIS_TAC[] THEN
  Q_TAC EXISTS_TAC `M` THEN
  LEFT_CONJ_TAC THENL [
    ALL_TAC,

    STRIP_TAC THEN1 (
      ASM_SIMP_TAC std_ss [kripke_structure_REWRITES]
    ) THEN
    LEFT_CONJ_TAC
  ] THENL [
    ASM_SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                        kripke_structure_REWRITES,
                        IN_SING, IMAGE_FINITE, FINITE_COUNT,
                        SUBSET_DEF, IN_IMAGE, IN_COUNT, IN_CROSS,
    prove(``!P x. x IN (\(x1,x2). P x1 x2) = P (FST x) (SND x)``, Cases_on `x` THEN SIMP_TAC std_ss [IN_DEF])
    ] THEN
    `0 < n /\ 0 < (n+n0) /\ n0 < (n+n0) /\ (PRE (n+n0) < (n+n0))` by DECIDE_TAC THEN
    REPEAT STRIP_TAC THENL [
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      `m < (n+n0)` by DECIDE_TAC THEN PROVE_TAC[],
      PROVE_TAC[],
      SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF] THEN PROVE_TAC[]
    ],


    ASM_SIMP_TAC std_ss [IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        kripke_structure_REWRITES,
                        IN_SING,
    prove(``!P x1 x2. ((x1, x2) IN \(x1,x2). P x1 x2) = P x1 x2``, SIMP_TAC std_ss [IN_DEF])] THEN

    Q_TAC EXISTS_TAC `CUT_PATH_PERIODICALLY (\m. el m) n0 n` THEN
    SIMP_TAC arith_ss [CUT_PATH_PERIODICALLY_def] THEN
    REPEAT STRIP_TAC THENL [
      Cases_on `SUC n' <= n0` THENL [
        DISJ2_TAC THEN
        EXISTS_TAC ``n':num`` THEN
        ASM_SIMP_TAC arith_ss [],

        Cases_on `(SUC n' - n0) MOD n = 0` THENL [
          DISJ1_TAC THEN
          ASM_SIMP_TAC arith_ss [] THEN
          `(n' - n0) MOD n = PRE n` suffices_by (
            `n0 + PRE n = PRE (n + n0)` by DECIDE_TAC THEN
            ASM_SIMP_TAC arith_ss []
          ) THEN
          `(PRE n) < n /\ (SUC (PRE n) = n) /\
          ((SUC (n' - n0)) = (SUC n' - n0))` by DECIDE_TAC THEN
          `PRE n = PRE n MOD n` by PROVE_TAC[LESS_MOD] THEN
          `n MOD n = 0` by PROVE_TAC[DIVMOD_ID] THEN
          METIS_TAC[SUC_MOD],

          DISJ2_TAC THEN
          Q_TAC EXISTS_TAC `n0 + ((n' - n0) MOD n)` THEN
          ASM_SIMP_TAC arith_ss [] THEN
          `(SUC (n0 + (n' - n0) MOD n)) = n0 + (SUC n' - n0) MOD n` suffices_by (
            ASM_SIMP_TAC arith_ss [] THEN
            PROVE_TAC[DIVISION]
          ) THEN
          SIMP_TAC arith_ss [ADD_SUC] THEN
          `(SUC n' - n0) = (SUC (n' - n0))` by DECIDE_TAC THEN
          METIS_TAC[SUC_MOD_CASES]
        ]
      ],

      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      SIMP_TAC std_ss [] THEN
      GEN_TAC THEN
      Cases_on `x < n0` THENL [
        `x < n + n0` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [],

        ASM_SIMP_TAC std_ss [] THEN
        `?y. x - n0 = y` by METIS_TAC[]  THEN
        `x = n0 + y` by DECIDE_TAC THEN
        ONCE_ASM_REWRITE_TAC[] THEN
        NTAC 2 WEAKEN_HD_TAC THEN
        `n0 + y MOD n < n + n0` by ASM_SIMP_TAC arith_ss [DIVISION] THEN
        METIS_TAC[IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE___ALTERNATIVE_DEF]
      ]
    ],


    UNDISCH_HD_TAC THEN
    `!i j. (IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE M i /\
                        IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE M j) ==>
                       (i = j)` suffices_by (
      METIS_TAC[]
    ) THEN
    ASM_SIMP_TAC std_ss [IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                        kripke_structure_REWRITES,
                        IN_SING,
    prove(``!P x1 x2. ((x1, x2) IN \(x1,x2). P x1 x2) = P x1 x2``, SIMP_TAC std_ss [IN_DEF])] THEN
    REPEAT STRIP_TAC THEN
    `p' = p''` suffices_by METIS_TAC[] THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    Induct_on `x` THENL [
      ASM_REWRITE_TAC[],

      SIMP_ALL_TAC std_ss [IS_ELEMENT_ITERATOR_def, NOT_IN_EMPTY] THEN
      Q_SPEC_NO_ASSUM 3 `x` THEN
      Q_SPEC_NO_ASSUM 6 `x` THEN
      FULL_SIMP_TAC std_ss [] THENL [
        `(PRE (n + n0) < n + n0) /\
         ~(SUC (PRE (n + n0)) < n + n0) /\
         m < n + n0` by DECIDE_TAC THEN
        `m = PRE (n + n0)` by METIS_TAC[] THEN
        METIS_TAC[],

        `(PRE (n + n0) < n + n0) /\
         ~(SUC (PRE (n + n0)) < n + n0) /\
         m < n + n0` by DECIDE_TAC THEN
        `m = PRE (n + n0)` by METIS_TAC[] THEN
        METIS_TAC[],


        `m < n + n0 /\ m' < n + n0` by DECIDE_TAC THEN
        `m' = m` by METIS_TAC[] THEN
        METIS_TAC[]
      ]
    ]
  ],



  SIMP_ALL_TAC std_ss [IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                       IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
  `?n m. (n < m) /\ (p' n = p' m)` by (
    `!n. p' n IN M.S` by METIS_TAC[KRIPKE_STRUCTURE___PATHS_AND_TRACES_PATH_SUBSET] THEN
    SIMP_ALL_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
    CCONTR_TAC THEN
    `!n. ({p' m | m < n} SUBSET M.S) /\ (CARD {p' m | m < n} = n)` suffices_by (
      `!n. ~(SUC n <= n)` by DECIDE_TAC THEN
      METIS_TAC[CARD_SUBSET]
    ) THEN
    SIMP_TAC std_ss [FORALL_AND_THM] THEN
    LEFT_CONJ_TAC THENL [
      SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
      METIS_TAC[],

      Induct_on `n` THENL [
        `{p' m | m < 0} = {}` suffices_by (
          METIS_TAC[CARD_DEF]
        ) THEN
        SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, GSPECIFICATION],

        `{p' m | m < (SUC n)} = p' n INSERT {p' m | m < n}` by (
          SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT] THEN
          `!m. (m < SUC n) = ((m = n) \/ (m < n))` by DECIDE_TAC THEN
          METIS_TAC[]
        ) THEN
        `FINITE ({p' m | m < n})` by METIS_TAC[SUBSET_FINITE] THEN
        ASM_SIMP_TAC std_ss [CARD_DEF] THEN
        SIMP_TAC std_ss [GSPECIFICATION] THEN
        METIS_TAC[]
      ]
    ]
  ) THEN

  `?q. q = CUT_PATH_PERIODICALLY p' n (m-n)` by METIS_TAC[] THEN
  `i = TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE M q` by (
    `q 0 IN M.S0 /\ IS_PATH_THROUGH_KRIPKE_STRUCTURE M q` suffices_by (
      METIS_TAC[]
    ) THEN
    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC arith_ss [CUT_PATH_PERIODICALLY_def] THEN
      Cases_on `0 < n` THEN ASM_REWRITE_TAC[] THEN
      `n = 0` by DECIDE_TAC THEN
      PROVE_TAC[],

      FULL_SIMP_TAC arith_ss [CUT_PATH_PERIODICALLY_def,
                             IS_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
      REPEAT STRIP_TAC THEN
      ASSUME_TAC arithmeticTheory.LESS_LESS_CASES THEN
      Q_SPECL_NO_ASSUM 0 [`SUC n'`, `n`] THEN
      CLEAN_ASSUMPTIONS_TAC THENL [
        ASM_SIMP_TAC arith_ss [] THEN
        PROVE_TAC[],

        ASM_SIMP_TAC arith_ss [],

        ASM_SIMP_TAC arith_ss [] THEN
        `?k. (n' - n) MOD (m - n) = k` by METIS_TAC[] THEN
        `0 < m - n` by DECIDE_TAC THEN
        `k < (m - n)` by PROVE_TAC[DIVISION] THEN
        `(SUC n' - n) MOD (m - n) = (SUC k) MOD (m - n)` by (
          `(SUC n' - n) = SUC (n' - n)` by DECIDE_TAC THEN
          ASM_SIMP_TAC std_ss [SUC_MOD]
        ) THEN

        ASM_REWRITE_TAC[] THEN
        Cases_on `SUC k < (m - n)` THENL [
          `SUC k MOD (m - n) = SUC k` by PROVE_TAC[LESS_MOD] THEN
          `(n + SUC k) = SUC (n + k)` by DECIDE_TAC THEN
          ASM_REWRITE_TAC[],

          `SUC k = m - n` by DECIDE_TAC THEN
          ASM_SIMP_TAC arith_ss [] THEN
          `m = SUC (k + n)` by DECIDE_TAC THEN
          PROVE_TAC[]
        ]
      ]
    ]
  ) THEN


  `IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE
           q n (m - n)` by
    PROVE_TAC[CUT_PATH_PERIODICALLY___IS_ULTIMATIVELY_PERIODIC] THEN
  `0 < m - n` by DECIDE_TAC THEN
  NTAC 3 UNDISCH_HD_TAC THEN
  REPEAT WEAKEN_HD_TAC THEN
  SIMP_TAC std_ss [IS_ULTIMATIVELY_PERIODIC_PATH_def,
                   IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE_def,
                   TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
  METIS_TAC[],


  SIMP_ALL_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
  PROVE_TAC[],

  METIS_TAC [KRIPKE_STRUCTURE___PATHS_AND_TRACES_PATH_SUBSET]
]
QED



val PRODUCT_KRIPKE_STRUCTURE_def =
 Define
  `PRODUCT_KRIPKE_STRUCTURE K1 K2  =
      kripke_structure {(s1, s2) | s1 IN K1.S /\ s2 IN K2.S /\
                                   (K1.L s1 INTER K1.P INTER K2.P =
                                    K2.L s2 INTER K1.P INTER K2.P)}
                       {(s1, s2) | s1 IN K1.S0 /\ s2 IN K2.S0 /\
                                   (K1.L s1 INTER K1.P INTER K2.P =
                                    K2.L s2 INTER K1.P INTER K2.P)}
                       {((s1, s2),(s1',s2')) |
                                   (s1,s1') IN K1.R /\ (s2,s2') IN K2.R/\
                                   (K1.L s1 INTER K1.P INTER K2.P =
                                    K2.L s2 INTER K1.P INTER K2.P) /\
                                   (K1.L s1' INTER K1.P INTER K2.P =
                                    K2.L s2' INTER K1.P INTER K2.P)}
                       (K1.P UNION K2.P)
                       (\(s1,s2). K1.L s1 UNION K2.L s2)`;


val PRODUCT_KRIPKE_STRUCTURE___REWRITES =
  store_simp_thm (
    "PRODUCT_KRIPKE_STRUCTURE___REWRITES",

    ``!K1 K2 K'. (IS_WELL_FORMED_KRIPKE_STRUCTURE K1 /\
                IS_WELL_FORMED_KRIPKE_STRUCTURE K2 /\
                (K' = (PRODUCT_KRIPKE_STRUCTURE K1 K2))) ==>
              ((K'.S = {(s1, s2) | s1 IN K1.S /\ s2 IN K2.S /\
                                      (K1.L s1 INTER K1.P INTER K2.P =
                                        K2.L s2 INTER K1.P INTER K2.P)}) /\
              (K'.S0 = (K1.S0 CROSS K2.S0) INTER K'.S) /\
              (K'.R = {((s1,s2),(s1',s2')) | (s1,s1') IN K1.R /\ (s2,s2') IN K2.R} INTER (K'.S CROSS K'.S)) /\
              (K'.P = (K1.P UNION K2.P)) /\
              (K'.L = (\(s1,s2). K1.L s1 UNION K2.L s2)))``,


    SIMP_TAC (std_ss++ boolSimps.EQUIV_EXTRACT_ss) [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                    PRODUCT_KRIPKE_STRUCTURE_def, EXISTS_PROD, FORALL_PROD,
                    kripke_structure_REWRITES, EXTENSION,
                    GSPECIFICATION, IN_INTER, IN_CROSS, SUBSET_DEF] THEN
    METIS_TAC[]);





val PRODUCT_KRIPKE_STRUCTURE___IS_WELL_FORMED =
  store_thm (
    "PRODUCT_KRIPKE_STRUCTURE___IS_WELL_FORMED",

    ``!K1 K2. (IS_WELL_FORMED_KRIPKE_STRUCTURE K1 /\
            IS_WELL_FORMED_KRIPKE_STRUCTURE K2) ==>
            IS_WELL_FORMED_KRIPKE_STRUCTURE (PRODUCT_KRIPKE_STRUCTURE K1 K2)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                     PRODUCT_KRIPKE_STRUCTURE___REWRITES,
                     INTER_SUBSET, GSPECIFICATION, FORALL_PROD, EXISTS_PROD] THEN
FULL_SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
REPEAT STRIP_TAC THENL [
  Q.MATCH_ABBREV_TAC `FINITE S` THEN
  `S SUBSET (K1.S CROSS K2.S)` suffices_by (
    METIS_TAC[FINITE_CROSS, SUBSET_FINITE]
  ) THEN
  UNABBREV_ALL_TAC THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_CROSS,
     PRODUCT_KRIPKE_STRUCTURE___REWRITES, FORALL_PROD, EXISTS_PROD],

  PROVE_TAC[FINITE_UNION],

  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
  PROVE_TAC[]
]);



val PRODUCT_KRIPKE_STRUCTURES___PATH_IS_PRODUCT_OF_ORIGINAL_PATHS =
  store_thm (
    "PRODUCT_KRIPKE_STRUCTURES___PATH_IS_PRODUCT_OF_ORIGINAL_PATHS",

   ``!K1 K2 p. IS_PATH_THROUGH_KRIPKE_STRUCTURE (PRODUCT_KRIPKE_STRUCTURE K1 K2) p ==>
               (IS_PATH_THROUGH_KRIPKE_STRUCTURE K1 (\n. FST (p n)) /\
                IS_PATH_THROUGH_KRIPKE_STRUCTURE K2 (\n. SND (p n)))``,

    SIMP_TAC std_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      PRODUCT_KRIPKE_STRUCTURE_def, kripke_structure_REWRITES,
      GSPECIFICATION] THEN
    REPEAT STRIP_TAC THEN (
      SPECL_NO_ASSUM 0 [``n:num``] THEN
      SIMP_ALL_TAC std_ss [] THEN
      Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN
      FULL_SIMP_TAC std_ss []
    ));


val PRODUCT_KRIPKE_STRUCTURES___PATH_IS_PRODUCT_OF_ORIGINAL_PATHS =
  store_thm (
    "PRODUCT_KRIPKE_STRUCTURES___PATH_IS_PRODUCT_OF_ORIGINAL_PATHS",

   ``!K1 K2 p. IS_PATH_THROUGH_KRIPKE_STRUCTURE (PRODUCT_KRIPKE_STRUCTURE K1 K2) p =
               (IS_PATH_THROUGH_KRIPKE_STRUCTURE K1 (\n. FST (p n)) /\
                IS_PATH_THROUGH_KRIPKE_STRUCTURE K2 (\n. SND (p n)) /\
                (!n. (K1.L (FST (p n)) INTER K1.P INTER K2.P =
                      K2.L (SND (p n)) INTER K1.P INTER K2.P)))``,

    SIMP_TAC std_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      PRODUCT_KRIPKE_STRUCTURE_def, kripke_structure_REWRITES,
      GSPECIFICATION, FORALL_PROD, EXISTS_PROD] THEN
    SIMP_TAC std_ss [prove (``!x y1 y2. (x = (y1, y2)) = ((FST x = y1) /\ (SND x = y2))``, Cases_on `x` THEN SIMP_TAC std_ss []), FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC);


(*open model*)
val UNIVERSAL_KRIPKE_STRUCTURE_def =
 Define
  `UNIVERSAL_KRIPKE_STRUCTURE P =
    kripke_structure (POW P) (POW P)
      (POW P CROSS POW P) P (\s. s)`


val UNIVERSAL_KRIPKE_STRUCTURE___IS_WELL_FORMED =
  store_thm (
    "UNIVERSAL_KRIPKE_STRUCTURE___IS_WELL_FORMED",
    ``!P. FINITE P ==> IS_WELL_FORMED_KRIPKE_STRUCTURE (UNIVERSAL_KRIPKE_STRUCTURE P)``,

    SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                    UNIVERSAL_KRIPKE_STRUCTURE_def,
                    kripke_structure_REWRITES,
                    SUBSET_REFL, IN_POW,
                    FINITE_POW_IFF]);



val UNIVERSAL_KRIPKE_STRUCTURE___PATHS_AND_TRACES =
  store_simp_thm (
    "UNIVERSAL_KRIPKE_STRUCTURE___PATHS_AND_TRACES",
    ``!P K p. (K = UNIVERSAL_KRIPKE_STRUCTURE P) ==> (
              (IS_PATH_THROUGH_KRIPKE_STRUCTURE K p = (PATH_SUBSET p P)) /\
              (IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p = (PATH_SUBSET p P)) /\
              (TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p = p) /\
              (IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE K p = (PATH_SUBSET p P)) /\
              (IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p = (PATH_SUBSET p P)))``,


      SIMP_TAC std_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                      UNIVERSAL_KRIPKE_STRUCTURE_def,
                      kripke_structure_REWRITES, IN_CROSS,
                      IN_POW,
                      TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                      IS_TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                      IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                      IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                      PATH_SUBSET_def] THEN
      METIS_TAC[]);



val IS_SIMULATION_RELATION_def =
 Define
  `IS_SIMULATION_RELATION K1 K2 P =
    (K1.P SUBSET K2.P /\
     (!s1 s2. P s1 s2 ==> (s1 IN K1.S /\ s2 IN K2.S)) /\
     (!s1 s2. P s1 s2 ==> (K1.L s1 = (K2.L s2 INTER K1.P))) /\
     (!s1 s1' s2. (P s1 s2 /\ (s1, s1') IN K1.R) ==>
            ?s2'. (P s1' s2' /\ (s2, s2') IN K2.R)) /\
     (!s1. s1 IN K1.S0 ==> ?s2. s2 IN K2.S0 /\ P s1 s2))`;



val IS_SIMULATION_RELATION___REFL =
  store_thm (
    "IS_SIMULATION_RELATION___REFL",
    ``!K. (IS_WELL_FORMED_KRIPKE_STRUCTURE K) ==>
          IS_SIMULATION_RELATION K K (\x y. (x = y) /\ (x IN K.S))``,

    SIMP_TAC std_ss [IS_SIMULATION_RELATION_def,
                     SUBSET_REFL, IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
                     SUBSET_DEF, IN_CROSS,
                     EXTENSION, IN_INTER] THEN
    METIS_TAC[FST, SND]);


val IS_SIMULATION_RELATION___TRANS =
  store_thm (
    "IS_SIMULATION_RELATION___TRANS",
    ``!K1 K2 K3 P1 P2. (IS_SIMULATION_RELATION K1 K2 P1 /\
                        IS_SIMULATION_RELATION K2 K3 P2) ==>
                        IS_SIMULATION_RELATION K1 K3 (\x1 x3. ?x2. P1 x1 x2 /\ P2 x2 x3)``,

    SIMP_TAC std_ss [IS_SIMULATION_RELATION_def,
                     SUBSET_DEF, IN_CROSS,
                     EXTENSION, IN_INTER] THEN
    METIS_TAC[FST, SND]);



val IS_BISIMULATION_RELATION_def =
 Define
  `IS_BISIMULATION_RELATION K1 K2 P =
    (IS_SIMULATION_RELATION K1 K2 P /\
     IS_SIMULATION_RELATION K2 K1
      (\s1 s2. P s2 s1))`;


Theorem IS_BISIMULATION_RELATION___DIRECT_DEF:
    !K1 K2 P.
        (IS_WELL_FORMED_KRIPKE_STRUCTURE K1 /\
         IS_WELL_FORMED_KRIPKE_STRUCTURE K2) ==>

        (IS_BISIMULATION_RELATION K1 K2 P =
          ((K1.P = K2.P) /\
          (!s1 s2. P s1 s2 ==> (s1 IN K1.S /\ s2 IN K2.S)) /\
          (!s1 s2. P s1 s2 ==> (K1.L s1 = K2.L s2)) /\
          (!s1 s1' s2. (P s1 s2 /\ (s1, s1') IN K1.R) ==>
                  ?s2'. (P s1' s2' /\ (s2, s2') IN K2.R)) /\
          (!s2 s2' s1. (P s1 s2 /\ (s2, s2') IN K2.R) ==>
                  ?s1'. (P s1' s2'/\ (s1, s1') IN K1.R)) /\
          (!s1. s1 IN K1.S0 ==> ?s2. s2 IN K2.S0 /\ P s1 s2) /\
          (!s2. s2 IN K2.S0 ==> ?s1. s1 IN K1.S0 /\ P s1 s2)))
Proof
    SIMP_TAC std_ss [IS_BISIMULATION_RELATION_def,
                     IS_SIMULATION_RELATION_def,
                     IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
    REPEAT STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC[SET_EQ_SUBSET],
      SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN  METIS_TAC[],
      PROVE_TAC[SET_EQ_SUBSET],
      SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN  METIS_TAC[],
      PROVE_TAC[SET_EQ_SUBSET],
      SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN  METIS_TAC[],
      PROVE_TAC[],
      SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN  METIS_TAC[]
    ]
QED

val IS_BISIMULATION_RELATION___SYM =
  store_thm (
    "IS_BISIMULATION_RELATION___SYM",
    ``!K1 K2 P. IS_BISIMULATION_RELATION K1 K2 P =
                IS_BISIMULATION_RELATION K2 K1 (\s1 s2. P s2 s1)``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [IS_BISIMULATION_RELATION_def] THEN
    `(\s1 s2. P s1 s2) = P` by SIMP_TAC std_ss [FUN_EQ_THM] THEN
    ASM_SIMP_TAC std_ss [] THEN
    PROVE_TAC[]);


val IS_BISIMULATION_RELATION___REFL =
  store_thm (
    "IS_BISIMULATION_RELATION___REFL",
    ``!K. (IS_WELL_FORMED_KRIPKE_STRUCTURE K) ==>
          IS_BISIMULATION_RELATION K K (\x y. (x = y) /\ x IN K.S)``,

    SIMP_TAC std_ss [IS_BISIMULATION_RELATION_def,
                     IS_SIMULATION_RELATION_def, IN_CROSS,
                     SUBSET_DEF, EXTENSION, IN_INTER,
                     IS_WELL_FORMED_KRIPKE_STRUCTURE_def] THEN
    METIS_TAC[FST, SND]);


val IS_BISIMULATION_RELATION___TRANS =
  store_thm (
    "IS_BISIMULATION_RELATION___TRANS",
    ``!K1 K2 K3 P1 P2. (IS_BISIMULATION_RELATION K1 K2 P1 /\
                        IS_BISIMULATION_RELATION K2 K3 P2) ==>
                        IS_BISIMULATION_RELATION K1 K3 (\x1 x3. ?x2. P1 x1 x2 /\ P2 x2 x3)``,

    SIMP_TAC std_ss [IS_BISIMULATION_RELATION_def] THEN
    REPEAT STRIP_TAC THENL [
      METIS_TAC[IS_SIMULATION_RELATION___TRANS],

      WEAKEN_NO_TAC 1 THEN WEAKEN_NO_TAC 2 THEN
      FULL_SIMP_TAC std_ss [IS_SIMULATION_RELATION_def,
                     SUBSET_DEF, IN_CROSS,
                     EXTENSION, IN_INTER] THEN
      METIS_TAC[FST, SND]
    ]);


val IS_BISIMULATION_RELATION___LABEL_EQ =
  store_thm (
    "IS_BISIMULATION_RELATION___LABEL_EQ",
    ``!K1 K2 P s1 s2. (IS_BISIMULATION_RELATION K1 K2 P /\
                       (P s1 s2)) ==>
                      (K1.L s1 = K2.L s2)``,

    SIMP_TAC std_ss [IS_BISIMULATION_RELATION_def, IS_SIMULATION_RELATION_def,
      SUBSET_DEF, EXTENSION, IN_INTER] THEN
    REPEAT STRIP_TAC THEN
    METIS_TAC[]);



val SIMULATION_RELATION___PATH_THROUGH_KRIPKE_STRUCTURE =
  store_thm (
    "SIMULATION_RELATION___PATH_THROUGH_KRIPKE_STRUCTURE",
    ``!K1 K2 P p s0. (IS_SIMULATION_RELATION K1 K2 P /\
                   IS_PATH_THROUGH_KRIPKE_STRUCTURE K1 p /\
                   (P (p 0) s0)) ==>

                (?p'. IS_PATH_THROUGH_KRIPKE_STRUCTURE K2 p' /\
                      ((p' 0) = s0) /\
                      !n. (P (p n) (p' n)))``,

    SIMP_TAC std_ss [IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      IS_SIMULATION_RELATION_def] THEN
    REPEAT STRIP_TAC THEN
    `?w. w = CHOOSEN_PATH {s0}
          (\s2 n. {s2' | P (p n) s2' /\ (s2, s2') IN K2.R})` by METIS_TAC[] THEN
    EXISTS_TAC ``w:num->'c`` THEN
    `!n. P (p n) (w n)` by (
      Induct_on `n` THENL [
        ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, GSPECIFICATION, IN_SING],

        ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, GSPECIFICATION] THEN
        SELECT_ELIM_TAC THEN
        METIS_TAC[]
      ]
    ) THEN
    REPEAT STRIP_TAC THENL [
      Induct_on `n` THENL [
        ASM_REWRITE_TAC [CHOOSEN_PATH_def, IN_SING] THEN
        SIMP_TAC std_ss [GSPECIFICATION] THEN
        SELECT_ELIM_TAC THEN
        `1 = SUC 0` by DECIDE_TAC THEN
        METIS_TAC[],

        ASM_REWRITE_TAC [CHOOSEN_PATH_def] THEN
        SIMP_TAC std_ss [GSPECIFICATION] THEN
        SELECT_ELIM_TAC THEN
        METIS_TAC[]
      ],


      ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING],

      PROVE_TAC[]
    ]);


val SIMULATION_RELATION___INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE =
  store_thm (
    "SIMULATION_RELATION___INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE",
    ``!K1 K2 P p. (IS_SIMULATION_RELATION K1 K2 P /\
                   IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K1 p) ==>

                (?p'. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K2 p' /\
                      !n. (P (p n) (p' n)))``,

    SIMP_TAC std_ss [IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def] THEN
    REPEAT STRIP_TAC THEN
    `?s0. P (p 0) s0 /\ s0 IN K2.S0` suffices_by (
      METIS_TAC[SIMULATION_RELATION___PATH_THROUGH_KRIPKE_STRUCTURE]
    ) THEN

    SIMP_ALL_TAC std_ss [IS_SIMULATION_RELATION_def] THEN
    METIS_TAC[]);



val LABEL_RESTRICTED_KRIPKE_STRUCTURE_def =
 Define
  `LABEL_RESTRICTED_KRIPKE_STRUCTURE K L =
    (kripke_structure K.S K.S0 K.R (K.P INTER L) (\s. K.L s INTER L))`;


val LABEL_RESTRICTED_KRIPKE_STRUCTURE___PATHS =
  store_simp_thm (
    "LABEL_RESTRICTED_KRIPKE_STRUCTURE___PATHS",
    ``!K L K'. (K' = LABEL_RESTRICTED_KRIPKE_STRUCTURE K L) ==>
               ((!p. IS_PATH_THROUGH_KRIPKE_STRUCTURE K' p = IS_PATH_THROUGH_KRIPKE_STRUCTURE K p) /\
                (!p. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K' p = IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K p))``,

    SIMP_TAC std_ss [LABEL_RESTRICTED_KRIPKE_STRUCTURE_def,
                     kripke_structure_REWRITES,
                     IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
                     IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def]);



val LABEL_RESTRICTED_KRIPKE_STRUCTURE___LANGUAGE =
  store_thm (
    "LABEL_RESTRICTED_KRIPKE_STRUCTURE___LANGUAGE",
    ``!K L. LANGUAGE_OF_KRIPKE_STRUCTURE (LABEL_RESTRICTED_KRIPKE_STRUCTURE K L) =
            IMAGE (\p. PATH_RESTRICT p L) (LANGUAGE_OF_KRIPKE_STRUCTURE K)``,

    SIMP_TAC std_ss [LANGUAGE_OF_KRIPKE_STRUCTURE_def, IMAGE_DEF,
      EXTENSION, GSPECIFICATION, IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def, LABEL_RESTRICTED_KRIPKE_STRUCTURE_def,
      kripke_structure_REWRITES, IS_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def, PATH_RESTRICT_def, PATH_MAP_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``\n:num. K.L (p' n)`` THEN
      METIS_TAC[],

      METIS_TAC[]
    ]);



val SIMULATION_RELATION___IMPLIES___SUBLANGUAGE =
  store_thm (
    "SIMULATION_RELATION___IMPLIES___SUBLANGUAGE",
    ``!K1 K2. (?P. IS_SIMULATION_RELATION K1 K2 P)  ==>

              ((LANGUAGE_OF_KRIPKE_STRUCTURE K1) SUBSET
                LANGUAGE_OF_KRIPKE_STRUCTURE (LABEL_RESTRICTED_KRIPKE_STRUCTURE K2 K1.P))``,

    SIMP_TAC std_ss [LABEL_RESTRICTED_KRIPKE_STRUCTURE___LANGUAGE,
      LANGUAGE_OF_KRIPKE_STRUCTURE_def, SUBSET_DEF,
      IMAGE_DEF, TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      GSPECIFICATION, GSYM LEFT_FORALL_IMP_THM, IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def, PATH_RESTRICT_def,
      PATH_MAP_def] THEN
    REPEAT STRIP_TAC THEN
    `?w. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K2 w /\ !n. (P (p' n) (w n))` by
      METIS_TAC[SIMULATION_RELATION___INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE] THEN
    EXISTS_TAC ``\n:num. (K2.L ((w:num->'c) n))`` THEN
    REPEAT STRIP_TAC THENL [
      ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
      SIMP_ALL_TAC std_ss [IS_SIMULATION_RELATION_def] THEN
      PROVE_TAC[],

      EXISTS_TAC ``w:num->'c`` THEN
      ASM_SIMP_TAC std_ss []
    ]);


val BISIMULATION_RELATION___IMPLIES___SUBLANGUAGE =
  store_thm (
    "BISIMULATION_RELATION___IMPLIES___SUBLANGUAGE",
    ``!K1 K2. (?P. IS_BISIMULATION_RELATION K1 K2 P)  ==>
              (LANGUAGE_OF_KRIPKE_STRUCTURE K1 SUBSET LANGUAGE_OF_KRIPKE_STRUCTURE K2)``,

    SIMP_TAC std_ss [LABEL_RESTRICTED_KRIPKE_STRUCTURE___LANGUAGE,
      LANGUAGE_OF_KRIPKE_STRUCTURE_def, SUBSET_DEF,
      IMAGE_DEF, TRACE_OF_PATH_THROUGH_KRIPKE_STRUCTURE_def,
      GSPECIFICATION, GSYM LEFT_FORALL_IMP_THM, IS_TRACE_OF_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE_def, PATH_RESTRICT_def,
      PATH_MAP_def, IS_BISIMULATION_RELATION_def] THEN
    REPEAT STRIP_TAC THEN
    `?w. IS_INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE K2 w /\ !n. (P (p' n) (w n))` by
      METIS_TAC[SIMULATION_RELATION___INITIAL_PATH_THROUGH_KRIPKE_STRUCTURE] THEN
    EXISTS_TAC ``w:num->'c`` THEN
    ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC[IS_BISIMULATION_RELATION___LABEL_EQ,
              IS_BISIMULATION_RELATION_def]);


val BISIMULATION_RELATION___IMPLIES___EQ_LANGUAGE =
  store_thm (
    "BISIMULATION_RELATION___IMPLIES___EQ_LANGUAGE",
    ``!K1 K2. (?P. IS_BISIMULATION_RELATION K1 K2 P)  ==>
              (LANGUAGE_OF_KRIPKE_STRUCTURE K1 = LANGUAGE_OF_KRIPKE_STRUCTURE K2)``,

      METIS_TAC [IS_BISIMULATION_RELATION___SYM, SET_EQ_SUBSET,
        BISIMULATION_RELATION___IMPLIES___SUBLANGUAGE]);



val UNIVERSAL_KRIPKE_STRUCTURE___IS_MOST_GENERAL =
  store_thm (
    "UNIVERSAL_KRIPKE_STRUCTURE___IS_MOST_GENERAL",
    ``!K. IS_WELL_FORMED_KRIPKE_STRUCTURE K ==>
        ?P. IS_SIMULATION_RELATION K (UNIVERSAL_KRIPKE_STRUCTURE K.P) P``,

    REPEAT STRIP_TAC THEN
    `?P. P = \s1 s2. ((s1 IN K.S) /\ (s2 = K.L s1))` by METIS_TAC[] THEN
    EXISTS_TAC ``P:'b -> 'a set -> bool`` THEN
    FULL_SIMP_TAC std_ss [IS_WELL_FORMED_KRIPKE_STRUCTURE_def,
      IS_SIMULATION_RELATION_def, UNIVERSAL_KRIPKE_STRUCTURE_def,
      kripke_structure_REWRITES, SUBSET_REFL, IN_CROSS,
      IN_POW, SUBSET_DEF, EXTENSION, IN_INTER] THEN
    METIS_TAC[FST, SND]);


val _ = export_theory();
