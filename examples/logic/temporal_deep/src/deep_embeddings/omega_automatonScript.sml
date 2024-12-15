open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["xprop_logicTheory", "prop_logicTheory", "infinite_pathTheory", "pred_setTheory", "listTheory", "pairTheory", "set_lemmataTheory",
   "containerTheory", "prim_recTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory", "semi_automatonTheory", "numLib",
  "relationTheory", "symbolic_kripke_structureTheory"];
*)

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
     containerTheory prop_logicTheory set_lemmataTheory prim_recTheory
     tuerk_tacticsLib temporal_deep_mixedTheory
     semi_automatonTheory numLib relationTheory;
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


val _ = new_theory "omega_automaton";


val explicit_acceptance_condition =
 Hol_datatype
  `explicit_acceptance_condition =
          EXPLICIT_ACCEPT_INPUT of 'input prop_logic
        | EXPLICIT_ACCEPT_STATE of 'state set
        | EXPLICIT_ACCEPT_TRUE
        | EXPLICIT_ACCEPT_NOT  of explicit_acceptance_condition
        | EXPLICIT_ACCEPT_AND  of explicit_acceptance_condition # explicit_acceptance_condition
        | EXPLICIT_ACCEPT_G    of explicit_acceptance_condition`;




val explicit_acceptance_condition_induct =
 save_thm
  ("explicit_acceptance_condition_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:('a, 'b) explicit_acceptance_condition``)))));



val EXPLICIT_ACCEPT_COND_SEM_TIME_def=
 Define
   `(EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_INPUT p) = P_SEM (i t) p) /\
    (EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_STATE q) = ((w t) IN q)) /\
    (EXPLICIT_ACCEPT_COND_SEM_TIME t i w EXPLICIT_ACCEPT_TRUE = T) /\
    (EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_NOT a) = ~(EXPLICIT_ACCEPT_COND_SEM_TIME t i w a)) /\
    (EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_G a) = (!t':num. (t' >= t) ==> (EXPLICIT_ACCEPT_COND_SEM_TIME t' i w a))) /\
    (EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_AND(a, b)) = ((EXPLICIT_ACCEPT_COND_SEM_TIME t i w a) /\ EXPLICIT_ACCEPT_COND_SEM_TIME t i w b))`;


val EXPLICIT_ACCEPT_COND_SEM_def=
 Define
   `(EXPLICIT_ACCEPT_COND_SEM i w f = EXPLICIT_ACCEPT_COND_SEM_TIME 0 i w f)`;



(*=============================================================================
= Syntactic Sugar and elementary lemmata
=============================================================================*)

(*****************************************************************************
 * Acceptance conditions
*****************************************************************************)
val EXPLICIT_ACCEPT_FALSE_def = Define `EXPLICIT_ACCEPT_FALSE = EXPLICIT_ACCEPT_NOT(EXPLICIT_ACCEPT_TRUE)`;
val EXPLICIT_ACCEPT_F_def     = Define `EXPLICIT_ACCEPT_F b = EXPLICIT_ACCEPT_NOT(EXPLICIT_ACCEPT_G (EXPLICIT_ACCEPT_NOT b))`;
val EXPLICIT_ACCEPT_OR_def    = Define `EXPLICIT_ACCEPT_OR(b1, b2) = EXPLICIT_ACCEPT_NOT(EXPLICIT_ACCEPT_AND(EXPLICIT_ACCEPT_NOT b1, EXPLICIT_ACCEPT_NOT b2))`;
val EXPLICIT_ACCEPT_IMPL_def  = Define `EXPLICIT_ACCEPT_IMPL(b1, b2) = EXPLICIT_ACCEPT_OR(EXPLICIT_ACCEPT_NOT b1, b2)`;
val EXPLICIT_ACCEPT_EQUIV_def = Define `EXPLICIT_ACCEPT_EQUIV(b1, b2) = EXPLICIT_ACCEPT_AND(EXPLICIT_ACCEPT_IMPL(b1, b2),EXPLICIT_ACCEPT_IMPL(b2, b1))`;
val EXPLICIT_ACCEPT_GF_def     = Define `EXPLICIT_ACCEPT_GF b = EXPLICIT_ACCEPT_G(EXPLICIT_ACCEPT_F b)`;
val EXPLICIT_ACCEPT_FG_def     = Define `EXPLICIT_ACCEPT_FG b = EXPLICIT_ACCEPT_F(EXPLICIT_ACCEPT_G b)`;


val EXPLICIT_ACCEPT_COND_USED_INPUT_VARS_def=
 Define
   `(EXPLICIT_ACCEPT_COND_USED_INPUT_VARS (EXPLICIT_ACCEPT_INPUT p) = (P_USED_VARS p)) /\
    (EXPLICIT_ACCEPT_COND_USED_INPUT_VARS (EXPLICIT_ACCEPT_STATE q) = {}) /\
    (EXPLICIT_ACCEPT_COND_USED_INPUT_VARS EXPLICIT_ACCEPT_TRUE = {}) /\
    (EXPLICIT_ACCEPT_COND_USED_INPUT_VARS (EXPLICIT_ACCEPT_NOT a) = EXPLICIT_ACCEPT_COND_USED_INPUT_VARS a) /\
    (EXPLICIT_ACCEPT_COND_USED_INPUT_VARS (EXPLICIT_ACCEPT_G a) = EXPLICIT_ACCEPT_COND_USED_INPUT_VARS a) /\
    (EXPLICIT_ACCEPT_COND_USED_INPUT_VARS (EXPLICIT_ACCEPT_AND(a, b)) = ((EXPLICIT_ACCEPT_COND_USED_INPUT_VARS a) UNION EXPLICIT_ACCEPT_COND_USED_INPUT_VARS b))`;


val EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def=
 Define
   `(EXPLICIT_ACCEPT_COND_USED_STATE_VARS (EXPLICIT_ACCEPT_INPUT p) = {}) /\
    (EXPLICIT_ACCEPT_COND_USED_STATE_VARS (EXPLICIT_ACCEPT_STATE q) = q) /\
    (EXPLICIT_ACCEPT_COND_USED_STATE_VARS EXPLICIT_ACCEPT_TRUE = {}) /\
    (EXPLICIT_ACCEPT_COND_USED_STATE_VARS (EXPLICIT_ACCEPT_NOT a) = EXPLICIT_ACCEPT_COND_USED_STATE_VARS a) /\
    (EXPLICIT_ACCEPT_COND_USED_STATE_VARS (EXPLICIT_ACCEPT_G a) = EXPLICIT_ACCEPT_COND_USED_STATE_VARS a) /\
    (EXPLICIT_ACCEPT_COND_USED_STATE_VARS (EXPLICIT_ACCEPT_AND(a, b)) = ((EXPLICIT_ACCEPT_COND_USED_STATE_VARS a) UNION EXPLICIT_ACCEPT_COND_USED_STATE_VARS b))`;


val EXPLICIT_ACCEPT_COND_USED_INPUT_VARS_INTER_SUBSET_THM =
 store_thm
  ("EXPLICIT_ACCEPT_COND_USED_INPUT_VARS_INTER_SUBSET_THM",
  ``!f t i w S. EXPLICIT_ACCEPT_COND_USED_INPUT_VARS f SUBSET S ==>
              (EXPLICIT_ACCEPT_COND_SEM_TIME t i w f =
              EXPLICIT_ACCEPT_COND_SEM_TIME t (PATH_RESTRICT i S) w f)``,

  INDUCT_THEN explicit_acceptance_condition_induct ASSUME_TAC THEN (
    FULL_SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                          EXPLICIT_ACCEPT_COND_USED_INPUT_VARS_def,
                          PATH_RESTRICT_def, PATH_MAP_def,
                          UNION_SUBSET] THEN
    METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
  ));




val IS_EXPLICIT_PROP_ACCEPT_COND_def=
 Define
   `(IS_EXPLICIT_PROP_ACCEPT_COND (EXPLICIT_ACCEPT_INPUT p) = T) /\
    (IS_EXPLICIT_PROP_ACCEPT_COND (EXPLICIT_ACCEPT_STATE q) = T) /\
    (IS_EXPLICIT_PROP_ACCEPT_COND EXPLICIT_ACCEPT_TRUE = T) /\
    (IS_EXPLICIT_PROP_ACCEPT_COND (EXPLICIT_ACCEPT_NOT a) = IS_EXPLICIT_PROP_ACCEPT_COND a) /\
    (IS_EXPLICIT_PROP_ACCEPT_COND (EXPLICIT_ACCEPT_G a) = F) /\
    (IS_EXPLICIT_PROP_ACCEPT_COND (EXPLICIT_ACCEPT_AND(a, b)) = ((IS_EXPLICIT_PROP_ACCEPT_COND a) /\ IS_EXPLICIT_PROP_ACCEPT_COND b))`;


val EXPLICIT_PROP_ACCEPT_COND_SEM_def=
 Define
   `EXPLICIT_PROP_ACCEPT_COND_SEM i0 w0 f =
    EXPLICIT_ACCEPT_COND_SEM_TIME 0 (\n. i0) (\n. w0) f`;


val EXPLICIT_PROP_ACCEPT_COND_SEM_THM =
 store_thm
  ("EXPLICIT_PROP_ACCEPT_COND_SEM_THM",

    ``!f. IS_EXPLICIT_PROP_ACCEPT_COND f ==>
        (!t i w. (EXPLICIT_ACCEPT_COND_SEM_TIME t i w f =
                EXPLICIT_PROP_ACCEPT_COND_SEM (i t) (w t) f))``,


    INDUCT_THEN explicit_acceptance_condition_induct ASSUME_TAC THEN (
      FULL_SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                            EXPLICIT_PROP_ACCEPT_COND_SEM_def,
                            IS_EXPLICIT_PROP_ACCEPT_COND_def]
    ));




val EXISTENTIAL_OMEGA_AUTOMATON_SEM_def =
 Define
  `EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, ac) i =
    (?w. IS_RUN_THROUGH_SEMI_AUTOMATON A i w /\
         EXPLICIT_ACCEPT_COND_SEM i w ac)`;

val UNIVERSAL_OMEGA_AUTOMATON_SEM_def =
 Define
  `UNIVERSAL_OMEGA_AUTOMATON_SEM (A, ac) i =
    (!w. IS_RUN_THROUGH_SEMI_AUTOMATON A i w ==>
         (EXPLICIT_ACCEPT_COND_SEM i w ac))`;


val EXISTENTIAL_UNIVERSAL_OMEGA_AUTOMATON_SEM_THM =
 store_thm
  ("EXISTENTIAL_UNIVERSAL_OMEGA_AUTOMATON_SEM_THM",

    ``!A ac i.
    ((EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, ac) i =
    ~(UNIVERSAL_OMEGA_AUTOMATON_SEM (A, EXPLICIT_ACCEPT_NOT ac) i)) /\
    ((UNIVERSAL_OMEGA_AUTOMATON_SEM (A, ac) i) =
    ~EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, EXPLICIT_ACCEPT_NOT ac) i))``,


    SIMP_TAC std_ss [EXISTENTIAL_OMEGA_AUTOMATON_SEM_def,
                    UNIVERSAL_OMEGA_AUTOMATON_SEM_def,
                    EXPLICIT_ACCEPT_COND_SEM_def,
                    EXPLICIT_ACCEPT_COND_SEM_TIME_def,
                    IMP_DISJ_THM]);


val IS_DET_TOTAL_SEMI_AUTOMATON___EXISTENTIAL_UNIVERSAL_SEM =
  store_thm (
    "IS_DET_TOTAL_SEMI_AUTOMATON___EXISTENTIAL_UNIVERSAL_SEM",

    ``!A. (IS_DET_TOTAL_SEMI_AUTOMATON A /\ IS_WELL_FORMED_SEMI_AUTOMATON A) ==>
    !ac i. (EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, ac) i =
    UNIVERSAL_OMEGA_AUTOMATON_SEM (A, ac) i)``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC [UNIVERSAL_OMEGA_AUTOMATON_SEM_def,
                EXISTENTIAL_OMEGA_AUTOMATON_SEM_def] THEN
    PROVE_TAC[IS_DET_TOTAL_SEMI_AUTOMATON___UNIQUE_RUN_EXISTS]);








val EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def=
 Define
   `(EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f (EXPLICIT_ACCEPT_INPUT p) = (EXPLICIT_ACCEPT_INPUT p)) /\
    (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f (EXPLICIT_ACCEPT_STATE q) = (EXPLICIT_ACCEPT_STATE (IMAGE f q))) /\
    (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f EXPLICIT_ACCEPT_TRUE = EXPLICIT_ACCEPT_TRUE) /\
    (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f(EXPLICIT_ACCEPT_NOT a) = EXPLICIT_ACCEPT_NOT (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f a)) /\
    (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f (EXPLICIT_ACCEPT_G a) =
     EXPLICIT_ACCEPT_G (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f a)) /\
    (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f (EXPLICIT_ACCEPT_AND(a, b)) = (EXPLICIT_ACCEPT_AND(EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f a,
                         EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f b)))`;


val EXPLICIT_ACCEPT_COND_SEM___STATE_VAR_RENAMING___NOT_INJ =
  store_thm (
    "EXPLICIT_ACCEPT_COND_SEM___STATE_VAR_RENAMING___NOT_INJ",
    ``!ac f g S w.
        (EXPLICIT_ACCEPT_COND_USED_STATE_VARS ac SUBSET S /\
        (!x. (x IN S ==> (g (f x) = x))) /\
        (!n. w n IN IMAGE f S)) ==>
       (!t i. (EXPLICIT_ACCEPT_COND_SEM_TIME t i w (EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f ac) =
    EXPLICIT_ACCEPT_COND_SEM_TIME t i (PATH_MAP (\n. g) w) ac))``,

    INDUCT_THEN explicit_acceptance_condition_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def],

      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def, PATH_MAP_def, IN_IMAGE,
      EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def, SUBSET_DEF] THEN
      METIS_TAC[],

      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def],

      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def, EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def] THEN
      ASM_REWRITE_TAC[],

      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def, EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def, UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      Q_SPECL_NO_ASSUM 5 [`f`, `g`, `S`, `w`] THEN
      Q_SPECL_NO_ASSUM 5 [`f`, `g`, `S`, `w`] THEN
      NTAC 2 UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [],

      SIMP_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_TIME_def, EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING_def, EXPLICIT_ACCEPT_COND_USED_STATE_VARS_def, UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      Q_SPECL_NO_ASSUM 3 [`f`, `g`, `S`, `w`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss []
    ]);





val OMEGA_AUTOMATON___STATE_VAR_RENAMING =
 store_thm
  ("OMEGA_AUTOMATON___STATE_VAR_RENAMING",
   ``!A ac f g.
    (IS_WELL_FORMED_SEMI_AUTOMATON A /\
     EXPLICIT_ACCEPT_COND_USED_STATE_VARS ac SUBSET A.S /\
    INJ f A.S UNIV /\
    (!s. s IN A.S ==> (g (f s) = s))) ==>
    ((!i. EXISTENTIAL_OMEGA_AUTOMATON_SEM (A, ac) i =
          EXISTENTIAL_OMEGA_AUTOMATON_SEM ((SEMI_AUTOMATON_STATE_VAR_RENAMING A f g), EXPLICIT_ACCEPT_COND___STATE_VAR_RENAMING f ac) i))``,


    SIMP_TAC std_ss [EXISTENTIAL_OMEGA_AUTOMATON_SEM_def] THEN
    REPEAT STRIP_TAC THEN

    ASSUME_TAC EXPLICIT_ACCEPT_COND_SEM___STATE_VAR_RENAMING___NOT_INJ THEN
    Q_SPECL_NO_ASSUM 0 [`ac`, `f`, `g`, `A.S`] THEN
    UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    REPEAT STRIP_TAC THEN


    ASSUME_TAC (CONJUNCT2 SEMI_AUTOMATON_STATE_VAR_RENAMING___RUN) THEN
    Q_SPECL_NO_ASSUM 0 [`A`, `f`, `g`, `i`] THEN
    UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    REPEAT STRIP_TAC THEN


    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `PATH_MAP (\n. f) w` THEN
      Q_SPEC_NO_ASSUM 2 `PATH_MAP (\n. f) w` THEN
      Q_SPEC_NO_ASSUM 3 `PATH_MAP (\n. f) w` THEN
      NTAC 2 UNDISCH_HD_TAC THEN
      SIMP_ALL_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_def,
        EXPLICIT_ACCEPT_COND_SEM_def] THEN
      ASM_SIMP_TAC std_ss [PATH_MAP_def, IN_IMAGE, ETA_THM] THEN
      METIS_TAC[],


      Q_TAC EXISTS_TAC `PATH_MAP (\n. g) w` THEN
      Q_SPEC_NO_ASSUM 2 `w` THEN
      Q_SPEC_NO_ASSUM 3 `w` THEN
      NTAC 2 UNDISCH_HD_TAC THEN
      `!n. w n IN IMAGE f A.S` by (
        SIMP_ALL_TAC std_ss [IS_RUN_THROUGH_SEMI_AUTOMATON_def,
                             SEMI_AUTOMATON_STATE_VAR_RENAMING_def,
                             semi_automaton_REWRITES]
      ) THEN
      SIMP_ALL_TAC std_ss [EXPLICIT_ACCEPT_COND_SEM_def] THEN
      ASM_SIMP_TAC std_ss [PATH_MAP_def, IN_IMAGE, ETA_THM] THEN
      METIS_TAC[]
    ]);



val _ = export_theory();

