(* -*- Mode: holscript; -*- ***************************************************)
(*                                                                            *)
(*   Symbolic Kripke Structure (with external fair conditions)                *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
     containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
     tuerk_tacticsLib temporal_deep_mixedTheory arithmeticTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";
val _ = hide "K";

val _ = new_theory "symbolic_kripke_structure";

(* NOTE: `symbolic_semi_automaton` has concepts of input vars, used as the translation
   results of LTL, etc., while `symbolic_kripke_structure` has only state variables,
   thus only suitable for representing system models (no fairness constraints).
 *)
Datatype : symbolic_kripke_structure =
    <| S0: 'state prop_logic; (* initial states *)
       R:  'state xprop_logic (* transition function *)
     |>
End

Theorem symbolic_kripke_structure_REWRITES =
        LIST_CONJ (TypeBase.one_one_of “:α symbolic_kripke_structure” ::
                   TypeBase.accessors_of “:α symbolic_kripke_structure”)


val IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p = !n. XP_SEM K.R (p n, p (SUC n))`;

(* key concept: p is a fair path of K w.r.t fair condition FC *)
val IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K FC p =
     (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p /\
      !b. MEM b FC ==> !t0. ?t. t >= t0 /\ P_SEM (p t) b)`;

(* added toplevel quantifiers *)
Theorem IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___ALTERNATIVE_DEF :
    !K FC p.
       IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K FC p =
        (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p /\
         !b. MEM b FC ==> !t0. ?t. P_SEM (p (t0 + t + 1)) b)
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def]
 >> BOOL_EQ_STRIP_TAC
 >> FORALL_EQ_STRIP_TAC
 >> BOOL_EQ_STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q_SPEC_NO_ASSUM 0 `SUC t0` \\
      CLEAN_ASSUMPTIONS_TAC \\
      Q_TAC EXISTS_TAC `PRE (t - t0)` \\
     `t0 + PRE (t - t0) + 1 = t` by DECIDE_TAC \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q_SPEC_NO_ASSUM 0 `t0` \\
      CLEAN_ASSUMPTIONS_TAC \\
      Q_TAC EXISTS_TAC `t0 + t + 1` \\
      ASM_SIMP_TAC arith_ss [] ]
QED

val IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p =
     (IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p /\ P_SEM (p 0) K.S0)`;

val IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K FC p =
     (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K FC p /\ P_SEM (p 0) K.S0)`;

Theorem PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES =
   LIST_CONJ [IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
              IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
              IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
              IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def];

Theorem IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___EMPTY_FAIRNESS :
    !K p. (IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K [] p =
           IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p) /\
          (IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K [] p =
           IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p)
Proof
    SIMP_TAC list_ss [IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
                      IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
                      IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def]
QED

val IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE K FC =
    !p. ~(IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K FC p)`;

val IS_EMPTY_SYMBOLIC_KRIPKE_STRUCTURE_def = Define
   `IS_EMPTY_SYMBOLIC_KRIPKE_STRUCTURE K =
    !p. ~(IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE K p)`;

val SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT_def = Define
   `SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT (K1:'a symbolic_kripke_structure)
                                      (K2:'a symbolic_kripke_structure) =
    symbolic_kripke_structure (P_AND(K1.S0, K2.S0)) (XP_AND(K1.R, K2.R))`;

val SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def = Define
   `SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS (K:'a symbolic_kripke_structure) =
    (P_USED_VARS K.S0) UNION (XP_USED_VARS K.R)`;

val SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def = Define
   `SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING f (K:'a symbolic_kripke_structure) =
    symbolic_kripke_structure (P_VAR_RENAMING f K.S0) (XP_VAR_RENAMING f K.R)`;

Theorem IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___IDENTIFY_VARIABLES :
    !f K fc.
       IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE K fc ==>
       IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
        (SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING f K) (MAP (P_VAR_RENAMING f) fc)
Proof
    SIMP_TAC std_ss [IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
                     PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
                     SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def,
                     symbolic_kripke_structure_REWRITES,
                     MEM_MAP, GSYM LEFT_EXISTS_AND_THM,
                     P_SEM___VAR_RENAMING___NOT_INJ,
                     XP_SEM___VAR_RENAMING___NOT_INJ]
QED

Theorem IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___VAR_RENAMING :
    !f K fc. INJ f
      (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS K UNION
       LIST_BIGUNION (MAP P_USED_VARS fc)) UNIV ==>
      (IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE K fc =
       IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
         (SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING f K) (MAP (P_VAR_RENAMING f) fc))
Proof
    rpt STRIP_TAC
 >> EQ_TAC
 >- REWRITE_TAC [IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___IDENTIFY_VARIABLES]
 >> SIMP_TAC std_ss [IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
                       PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
                       SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def,
                       symbolic_kripke_structure_REWRITES,
                       MEM_MAP, GSYM LEFT_EXISTS_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      `?w. w = PATH_RESTRICT p (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS K UNION
             LIST_BIGUNION (MAP P_USED_VARS fc))` by PROVE_TAC[] THEN
      SUBGOAL_TAC `(((?n. ~XP_SEM K.R (p n,p (SUC n))) \/
                    ?b. MEM b fc /\ ?t0. !t. ~(t >= t0) \/ ~P_SEM (p t) b) \/
                    ~P_SEM (p 0) K.S0) =
                   (((?n. ~XP_SEM K.R (w n,w (SUC n))) \/
                    ?b. MEM b fc /\ ?t0. !t. ~(t >= t0) \/ ~P_SEM (w t) b) \/
                    ~P_SEM (w 0) K.S0)` THEN1 (
        ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
        BINOP_TAC THENL [
          BINOP_TAC,
          ALL_TAC
        ] THENL [
          EXISTS_EQ_STRIP_TAC THEN
          SIMP_TAC std_ss [] THEN
          MATCH_MP_TAC XP_USED_VARS_INTER_SUBSET_BOTH_THM THEN
          SIMP_TAC std_ss [SUBSET_DEF, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, IN_UNION],

          EXISTS_EQ_STRIP_TAC THEN
          BOOL_EQ_STRIP_TAC THEN
          EXISTS_EQ_STRIP_TAC THEN
          FORALL_EQ_STRIP_TAC THEN
          BOOL_EQ_STRIP_TAC THEN
          SIMP_TAC std_ss [] THEN
          MATCH_MP_TAC P_USED_VARS_INTER_SUBSET_THM THEN
          SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_LIST_BIGUNION, MEM_MAP] THEN
          PROVE_TAC[],

          SIMP_TAC std_ss [] THEN
          MATCH_MP_TAC P_USED_VARS_INTER_SUBSET_THM THEN
          SIMP_TAC std_ss [SUBSET_DEF, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, IN_UNION]
        ]
      ) THEN
      ONCE_ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

      `!n. w n SUBSET (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS K UNION
             LIST_BIGUNION (MAP P_USED_VARS fc))` by PROVE_TAC[PATH_RESTRICT_SUBSET] THEN
      GSYM_NO_TAC 1 THEN

      Q_SPEC_NO_ASSUM 2 `PATH_VAR_RENAMING f w` THEN
      UNDISCH_HD_TAC THEN
      SIMP_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def] THEN
      IMP_TO_EQ_TAC THEN
      BINOP_TAC THENL [
        BINOP_TAC,
        ALL_TAC
      ] THENL [
        EXISTS_EQ_STRIP_TAC THEN
        SIMP_TAC std_ss [] THEN
        MATCH_MP_TAC (GSYM XP_SEM___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 2 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_UNION, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def] THEN
        PROVE_TAC[],

        EXISTS_EQ_STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        EXISTS_EQ_STRIP_TAC THEN
        FORALL_EQ_STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        SIMP_TAC std_ss [] THEN
        MATCH_MP_TAC (GSYM P_SEM___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 4 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_UNION, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
          IN_LIST_BIGUNION, MEM_MAP] THEN
        METIS_TAC[],

        SIMP_TAC std_ss [] THEN
        MATCH_MP_TAC (GSYM P_SEM___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 2 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SUBSET_DEF, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, IN_UNION] THEN
        PROVE_TAC[]
      ]
QED

val _ = export_theory();
