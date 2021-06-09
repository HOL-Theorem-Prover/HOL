open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (Globals.HOLDIR ^ "/examples/temporal_deep/");
loadPath := (home_dir ^ "src/deep_embeddings") ::
            (home_dir ^ "src/tools") :: !loadPath;

map load
 ["xprop_logicTheory", "prop_logicTheory", "infinite_pathTheory", "pred_setTheory", "listTheory", "pairTheory", "set_lemmataTheory",
   "containerTheory", "prim_recTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory"];
*)

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
     containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
     tuerk_tacticsLib temporal_deep_mixedTheory;
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


val _ = new_theory "semi_automaton";
val _ = ParseExtras.temp_loose_equality()



(*****************************************************************************)
(* representation of non deterministic semi automata, that use               *)
(* the powerset of a set of propositional varibales as inputs                *)
(*****************************************************************************)
val semi_automaton_def =
 Hol_datatype
  `semi_automaton =
    <| S:  'state set;                         (*set of states *)
       I:  'input set;                         (*set of inputs *)
       S0: ('state # 'input set) set;          (*initial states*)
       R:  ('state # 'input set # 'state # 'input set) set  (*transition relation*) |>`;

Theorem semi_automaton_REWRITES =
        LIST_CONJ (TypeBase.one_one_of “:(α,β) semi_automaton” ::
                   TypeBase.accessors_of “:(α,β)semi_automaton”)


val IS_WELL_FORMED_SEMI_AUTOMATON_def =
 Define
  `IS_WELL_FORMED_SEMI_AUTOMATON A =
    (FINITE A.S /\ FINITE A.I /\ A.S0 SUBSET (A.S CROSS (POW A.I)) /\
     A.R SUBSET (A.S CROSS ((POW A.I) CROSS (A.S CROSS (POW A.I)))))`

(*****************************************************************************)
(* RUN A i w is true iff p is a run of i through A                             *)
(*****************************************************************************)
val IS_RUN_THROUGH_SEMI_AUTOMATON_def =
 Define
  `IS_RUN_THROUGH_SEMI_AUTOMATON A i w =
    ((!n. w n IN A.S) /\
     ((w 0, (i 0) INTER A.I) IN A.S0) /\
    (!n. (w n, (i n) INTER A.I, w (SUC n), (i (SUC n)) INTER A.I) IN A.R))`;


val IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE_def =
 Define
  `IS_RUN_THROUGH_SEMI_AUTOMATON_TO_STATE A i w s m =
    ((!n. n <= m ==> (w n IN A.S)) /\
     ((w 0, (i 0) INTER A.I) IN A.S0) /\ (w m = s) /\
    (!n. n < m ==> ((w n, (i n) INTER A.I, w (SUC n), (i (SUC n)) INTER A.I) IN A.R)))`;


val IS_DET_TOTAL_SEMI_AUTOMATON_def =
 Define
  `IS_DET_TOTAL_SEMI_AUTOMATON A =
    ((!i. ?!x. (x, i INTER A.I) IN A.S0) /\
     !s i i'. (s IN A.S /\ i SUBSET A.I /\ i' SUBSET A.I) ==>
           (?!s'. (s, i, s', i') IN A.R))`;


val IS_DET_TOTAL_SEMI_AUTOMATON___UNIQUE_RUN_EXISTS =
  store_thm (
    "IS_DET_TOTAL_SEMI_AUTOMATON___UNIQUE_RUN_EXISTS",

    ``!A. (IS_DET_TOTAL_SEMI_AUTOMATON A /\
    IS_WELL_FORMED_SEMI_AUTOMATON A) ==>
    (!i. ?!w. IS_RUN_THROUGH_SEMI_AUTOMATON A i w)``,


    SIMP_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                    EXISTS_UNIQUE_DEF,
                    IS_DET_TOTAL_SEMI_AUTOMATON_def,
                    IS_WELL_FORMED_SEMI_AUTOMATON_def,
                    SUBSET_DEF, IN_CROSS, IN_POW,
    prove (``!P. (!x. P x) = (!x1 x2 x3 x4. P (x1,x2,x3, x4))``,
            METIS_TAC[FST, SND, PAIR])
    ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    GEN_TAC THEN
    Q_SPEC_NO_ASSUM 5 `i 0` THEN
    SIMP_ALL_TAC std_ss [] THEN
    REPEAT STRIP_TAC THENL [
      `?w. w = CHOOSEN_PATH {x} (\s n. ({s' | (s, i (PRE n) INTER A.I, s', (i n) INTER A.I) IN A.R}))` by METIS_TAC[] THEN
      `!n. w n IN A.S` by (
        Induct_on `n` THENL [
          ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def, IN_SING] THEN
          PROVE_TAC[FST],

          ASM_SIMP_TAC std_ss [CHOOSEN_PATH_def] THEN
          GSYM_NO_TAC 1 THEN
          ASM_REWRITE_TAC[] THEN
          SIMP_TAC std_ss [GSPECIFICATION] THEN
          SELECT_ELIM_TAC THEN
          REPEAT STRIP_TAC THENL [
            Q_SPECL_NO_ASSUM 8 [`w n`, `i n INTER A.I`, `(i (SUC n)) INTER A.I`] THEN
            UNDISCH_HD_TAC THEN
            ASM_SIMP_TAC std_ss [IN_INTER],

            METIS_TAC[]
          ]
        ]
      ) THEN

      Q_TAC EXISTS_TAC `w` THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],

        `w 0 = x` suffices_by METIS_TAC[] THEN
        ASM_REWRITE_TAC [CHOOSEN_PATH_def, IN_SING] THEN
        SIMP_TAC std_ss [],

        ASM_REWRITE_TAC [CHOOSEN_PATH_def] THEN
        GSYM_NO_TAC 1 THEN
        ASM_REWRITE_TAC [CHOOSEN_PATH_def] THEN
        SELECT_ELIM_TAC THEN
        SIMP_TAC std_ss [GSPECIFICATION] THEN
        Q_SPECL_NO_ASSUM 8 [`w n`, `i n INTER A.I`, `(i (SUC n)) INTER A.I`] THEN
        UNDISCH_HD_TAC THEN
        ASM_SIMP_TAC std_ss [IN_INTER]
      ],



      ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
      GEN_TAC THEN
      Induct_on `x''` THENL [
        PROVE_TAC[],

        Q_SPECL_NO_ASSUM 13 [`y x''`, `i x'' INTER A.I`, `i (SUC x'') INTER A.I`] THEN
        UNDISCH_HD_TAC THEN
        ASM_SIMP_TAC std_ss [IN_INTER] THEN
        REPEAT STRIP_TAC THEN
        PROVE_TAC[]
      ]
    ]);






val SEMI_AUTOMATON_STATE_VAR_RENAMING_def =
 Define
  `SEMI_AUTOMATON_STATE_VAR_RENAMING A f g =
    (semi_automaton (IMAGE f A.S) A.I (\(s,i). (g s, i) IN A.S0)
                     (\(s1, i, s2, i'). (g s1, i, g s2, i') IN A.R))`;

val SEMI_AUTOMATON_STATE_VAR_RENAMING___RUN =
  store_thm (
    "SEMI_AUTOMATON_STATE_VAR_RENAMING___RUN",
    ``(!A f g i w.
          IS_WELL_FORMED_SEMI_AUTOMATON A /\ INJ f A.S UNIV /\
          (!s. s IN A.S ==> (g (f s) = s)) /\ (!n. w n IN A.S) ==>
          (IS_RUN_THROUGH_SEMI_AUTOMATON
             (SEMI_AUTOMATON_STATE_VAR_RENAMING A f g) i
             (PATH_MAP (\n. f) w) =
           IS_RUN_THROUGH_SEMI_AUTOMATON A i w)) /\
       (!A:('a, 'b) semi_automaton (f:'b -> 'c) g i w.
         IS_WELL_FORMED_SEMI_AUTOMATON A /\ INJ f A.S UNIV /\
         (!s. s IN A.S ==> (g (f s) = s)) /\
         (!n. w n IN IMAGE f A.S) ==>
         (IS_RUN_THROUGH_SEMI_AUTOMATON
            (SEMI_AUTOMATON_STATE_VAR_RENAMING A f g) i w =
          IS_RUN_THROUGH_SEMI_AUTOMATON A i (PATH_MAP (\n. g) w)))``,


SIMP_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                 SEMI_AUTOMATON_STATE_VAR_RENAMING_def,
                 semi_automaton_REWRITES, IN_IMAGE,
                 PATH_MAP_def,
                 IS_WELL_FORMED_SEMI_AUTOMATON_def,
                 INJ_DEF, SUBSET_DEF, IN_CROSS,
  prove(``!P x1 x2 x3 x4. (x1, x2, x3, x4) IN (\(x1,x2,x3,x4). P x1 x2 x3 x4) = (P x1 x2 x3 x4)``,
          SIMP_TAC std_ss [IN_DEF]),
  prove(``!P x1 x2. (x1, x2) IN (\(x1,x2). P x1 x2) = (P x1 x2)``,
          SIMP_TAC std_ss [IN_DEF])] THEN
REPEAT STRIP_TAC THEN
REPEAT BOOL_EQ_STRIP_TAC THEN
METIS_TAC[FST, SND]);





val _ = export_theory();
