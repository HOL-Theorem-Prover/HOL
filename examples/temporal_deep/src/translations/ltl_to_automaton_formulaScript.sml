open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val base_dir = concat Globals.HOLDIR "/examples/temporal_deep/";
loadPath := (concat base_dir "src/tools") :: (concat base_dir "src/deep_embeddings") :: !loadPath;
map load
 ["ltlTheory", "arithmeticTheory", "automaton_formulaTheory", "xprop_logicTheory", "prop_logicTheory",
  "infinite_pathTheory", "tuerk_tacticsLib", "symbolic_semi_automatonTheory", "listTheory", "pred_setTheory",
  "pred_setTheory", "rich_listTheory", "set_lemmataTheory", "temporal_deep_mixedTheory",
  "pairTheory", "symbolic_kripke_structureTheory",
  "numLib"];
*)

open ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory
     prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     pred_setTheory rich_listTheory set_lemmataTheory temporal_deep_mixedTheory pairTheory symbolic_kripke_structureTheory
     numLib;
val _ = hide "S";
val _ = hide "I";


(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val _ = new_theory "ltl_to_automaton_formula";


(****************************************************************
 * A datastructure for the translation. For the idea behind this
 * datastructure look at LTL_TO_GEN_BUECHI_DS_SEM
 *
 * It contains the necessary informations to construct a GENERALISED
 * Buechi-Automaton. However, state variables have to be distinct to
 * input variables. To avoid varrenamings, the set of input variables
 * is explicitely modelled and all parameters get
 * a function enumeration state var distinct from this
 * set of input variables
 ****************************************************************)
val LTL_TO_GEN_BUECHI_DS_def =
 Hol_datatype
  `ltl_to_gen_buechi_ds =
    <| SN:  num;                                     (*number of needed state variables*)
       S0:  (num # bool) list;                       (*initial states, state variables can be true or false or unspecified*)
       IV:  ('var->bool);                            (*the set of input variables*)
       R:   ((num->'var) -> 'var xprop_logic) list;  (*transition relation*)
       FC:  ((num->'var) -> 'var prop_logic) list;   (*fairness conditions*)
       B:   ('var ltl # bool # bool # ((num->'var) -> 'var prop_logic)) set (*Bindings*)
     |>`;

val ltl_to_gen_buechi_ds_SN = DB.fetch "-" "ltl_to_gen_buechi_ds_SN";
val ltl_to_gen_buechi_ds_S0 = DB.fetch "-" "ltl_to_gen_buechi_ds_S0";
val ltl_to_gen_buechi_ds_IV = DB.fetch "-" "ltl_to_gen_buechi_ds_IV";
val ltl_to_gen_buechi_ds_R = DB.fetch "-" "ltl_to_gen_buechi_ds_R";
val ltl_to_gen_buechi_ds_FC = DB.fetch "-" "ltl_to_gen_buechi_ds_FC";
val ltl_to_gen_buechi_ds_B = DB.fetch "-" "ltl_to_gen_buechi_ds_B";
val ltl_to_gen_buechi_ds_11 = DB.fetch "-" "ltl_to_gen_buechi_ds_11";

val ltl_to_gen_buechi_ds_REWRITES = save_thm("ltl_to_gen_buechi_ds_REWRITES",
   LIST_CONJ [ltl_to_gen_buechi_ds_SN,
              ltl_to_gen_buechi_ds_S0,
              ltl_to_gen_buechi_ds_IV,
              ltl_to_gen_buechi_ds_R,
              ltl_to_gen_buechi_ds_FC,
              ltl_to_gen_buechi_ds_B,
              ltl_to_gen_buechi_ds_11])


(*Some definitions to get meaning to this datastructure*)
val LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___INITIAL_STATES (DS:'a ltl_to_gen_buechi_ds) = (\sv:num->'a.
      P_BIGAND (MAP (\(n, b). if b then P_PROP (sv n) else P_NOT(P_PROP (sv n))) DS.S0))`;

val LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS DS = (\sv.
     (A_BIGAND (MAP (\p. ACCEPT_COND_GF (p sv)) DS.FC)))`;


val LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS =
      (\sv s. (?n. (n < DS.SN) /\ (s = sv n)))`;


val LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS",

   ``!DS s sv. s IN LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv =
        (?n. (n < DS.SN) /\ (s = sv n))``,

    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, IN_DEF]);


val LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS___COUNT =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS___COUNT",

   ``!DS sv. LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv =
        IMAGE sv (count DS.SN)``,

    SIMP_TAC std_ss [EXTENSION,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, IN_IMAGE,
      IN_COUNT] THEN
    METIS_TAC[]);


val LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS___FINITE =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS___FINITE",

   ``!DS sv. FINITE (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)``,

    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS___COUNT,
      IMAGE_FINITE, FINITE_COUNT]);



val LTL_TO_GEN_BUECHI_DS___USED_VARS_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___USED_VARS DS =
    (\sv. (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) UNION
          (LIST_BIGUNION (MAP (\xpf. XP_USED_VARS (xpf sv)) DS.R)) UNION
          (LIST_BIGUNION (MAP (\pf. P_USED_VARS (pf sv)) DS.FC)) UNION
          (BIGUNION (IMAGE (\(l, b1, b2, pf). (P_USED_VARS (pf sv) UNION LTL_USED_VARS l)) DS.B)))`;



val LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS =
    (\sv. symbolic_semi_automaton
      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)
      (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv)
      (XP_BIGAND (MAP (\xp. xp sv) DS.R)))`;



(*a suitable function creating new state variables*)
val LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def =
 Define `
   LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv = (IS_ELEMENT_ITERATOR sv DS.SN DS.IV)`;


val LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv =
     (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w /\ A_SEM (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w)             (LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS DS sv))`;


val LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET",

  ``!DS sv i w. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv ==>
                PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)``,

  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
                   IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                   symbolic_semi_automaton_REWRITES]);



(*a fair run, that is minimal according to
  some special propositional formula *)
val LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN DS i w p sv  =
      !w'. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w' sv ==>
           (!t. P_SEM ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w) t) p ==>
                P_SEM ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w') t) p)`;


(*a fair run, that is maximal according to
  some special propositional formula *)
val LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN DS i w p sv  =
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN DS i w (P_NOT p) sv`;

(*a fair run, such that the propositinal part of
  the binding behaves as the ltl part
  and such that the run is according to the binding minimal or maximal according to the propositional part *)
val LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def =
 Define
    `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l, b1, b2, pf) i sv =
         (((!t. LTL_SEM_TIME t i l = P_SEM (w t UNION (i t DIFF (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))) (pf sv))) /\
         (b1 ==> LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN DS i w (pf sv) sv) /\
         (b2 ==> LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN DS i w (pf sv) sv)
          )`;


val LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE",

  ``!DS sv i w l pf b1 b2. LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l, b1, b2, pf) i sv =
                (!wi. (wi = INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w) ==>

                ((!t. (LTL_SEM_TIME t i l = P_SEM (wi t) (pf sv))) /\
                 !w' wi'. (LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w' sv /\
                           (wi' = INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w')) ==>
                           ((!t. (b1 /\ P_SEM (wi' t) (pf sv) ==> P_SEM (wi t) (pf sv))) /\
                            (!t. (b2 /\ P_SEM (wi t) (pf sv) ==> P_SEM (wi' t) (pf sv))))
                            ))``,

  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, P_SEM_def,
    LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def, LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def] THEN
  REPEAT GEN_TAC THEN
  REMAINS_TAC `!t. (w t UNION (i t DIFF LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) =
                   (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w t)` THEN1 (
    METIS_TAC[]
  ) THEN
  SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                   LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                   symbolic_semi_automaton_REWRITES]
  );



(*The meaning "semantics" of the datastructure*)
val LTL_TO_GEN_BUECHI_DS___SEM_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___SEM DS =
      !sv.
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>

        ((!n b. (MEM (n, b) DS.S0 ==> (n < DS.SN))) /\
         (LTL_TO_GEN_BUECHI_DS___USED_VARS DS sv SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) /\
         (!i. ?w. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv /\
                 (!l b1 b2 pf. ((l,b1,b2,pf) IN DS.B) ==>
                           LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l, b1, b2, pf) i sv
                 )))`;


val LTL_TO_GEN_BUECHI_DS___EQUIVALENT_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___EQUIVALENT DS DS' =
    (LTL_TO_GEN_BUECHI_DS___SEM DS = LTL_TO_GEN_BUECHI_DS___SEM DS')`;



(*This meaning implies that all bindings in it, we
  can easily construct equivalent generalised buechi
  automata*)

val LTL_TO_GEN_BUECHI_DS___A_NDET_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___A_NDET DS pf =
    (\sv. A_NDET (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv,
      A_AND(LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS DS sv, ACCEPT_COND_PROP (pf sv))))`;


val LTL_TO_GEN_BUECHI_DS___A_UNIV_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf =
    (\sv. A_UNIV (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv,
      A_IMPL(LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS DS sv, ACCEPT_COND_PROP (pf sv))))`;


val LTL_TO_GEN_BUECHI_DS___KRIPKE_STRUCTURE_def =
 Define
   `LTL_TO_GEN_BUECHI_DS___KRIPKE_STRUCTURE DS pf =
    (\sv. symbolic_kripke_structure (P_AND(pf sv, (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv)))
      (XP_BIGAND (MAP (\xp. xp sv) DS.R)))`;


val LTL_TO_GEN_BUECHI_DS___SEM___MAX =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___MAX",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, T, a, pf) IN DS.B) ==>

      (!i. LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))``,

    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def, LTL_SEM_def, LTL_TO_GEN_BUECHI_DS___A_NDET_def,
      A_SEM_def, ACCEPT_COND_PROP_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def, LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def,
      INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
      symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def] THEN
    REPEAT STRIP_TAC THEN
    SPECL_NO_ASSUM 1 [``sv:num->'a``] THEN
    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SPECL_NO_ASSUM 0 [``i:num->'a set``] THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    SPECL_NO_ASSUM 2 [``l:'a ltl``, ``T``, ``a:bool``, ``pf:(num->'a)->'a prop_logic``] THEN
    UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
    METIS_TAC[P_SEM_def]
  );



val LTL_TO_GEN_BUECHI_DS___SEM___MIN =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___MIN",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, a, T, pf) IN DS.B) ==>

      (!i. LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))``,

    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def, LTL_SEM_THM, LTL_TO_GEN_BUECHI_DS___A_UNIV_def,
      A_SEM_THM, ACCEPT_COND_PROP_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def, LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def,
      INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
      symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def] THEN
    REPEAT STRIP_TAC THEN
    SPECL_NO_ASSUM 1 [``sv:num->'a``] THEN
    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SPECL_NO_ASSUM 0 [``i:num->'a set``] THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    SPECL_NO_ASSUM 2 [``l:'a ltl``, ``a:bool``, ``T``, ``pf:(num->'a)->'a prop_logic``] THEN
    UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
    METIS_TAC[P_SEM_def]
  );


val LTL_TO_GEN_BUECHI_DS___KS_SEM___MIN =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___KS_SEM___MIN",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, a, T, pf) IN DS.B) ==>

      (!M. LTL_KS_SEM M l = A_KS_SEM M (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))``,

    SIMP_TAC std_ss [LTL_KS_SEM_def, A_KS_SEM_def] THEN
    PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___MIN]
  );


val LTL_TO_GEN_BUECHI_DS___KS_SEM___MAX =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___KS_SEM___MAX",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, T, a, pf) IN DS.B) ==>

      (!M. LTL_KS_SEM M l = A_KS_SEM M (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))``,

    SIMP_TAC std_ss [LTL_KS_SEM_def, A_KS_SEM_def] THEN
    PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___MAX]
  );



val LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___MAX =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___MAX",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, T, a, pf) IN DS.B) ==>

      (LTL_IS_CONTRADICTION l = A_IS_EMPTY (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))``,

    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [A_IS_EMPTY_def, LTL_IS_CONTRADICTION_def] THEN
    PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___MAX]
  );



val LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___MIN =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___MIN",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, a, T, pf) IN DS.B) ==>

      (LTL_IS_CONTRADICTION l = A_IS_EMPTY (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))``,

    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [A_IS_EMPTY_def, LTL_IS_CONTRADICTION_def] THEN
    PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___MIN]
  );



val LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___MIN =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___MIN",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (LTL_EVENTUAL l, a, T, pf) IN DS.B) ==>

      (LTL_EQUIVALENT l LTL_FALSE = A_IS_EMPTY (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))``,

    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [A_IS_EMPTY_def, LTL_IS_CONTRADICTION_def, LTL_EQUIVALENT_def] THEN
    ASSUME_TAC (GSYM LTL_TO_GEN_BUECHI_DS___SEM___MIN) THEN
    Q_SPECL_NO_ASSUM 0 [`DS`, `LTL_EVENTUAL l`, `pf`, `sv`, `a`] THEN
    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC std_ss [LTL_SEM_THM] THEN
    PROVE_TAC[]
  );


val LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___MAX =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___MAX",

  ``!DS l pf sv a.
    (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (LTL_EVENTUAL l, T, a, pf) IN DS.B) ==>

      (LTL_EQUIVALENT l LTL_FALSE = A_IS_EMPTY (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))``,

    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [A_IS_EMPTY_def, LTL_IS_CONTRADICTION_def, LTL_EQUIVALENT_def] THEN
    ASSUME_TAC (GSYM LTL_TO_GEN_BUECHI_DS___SEM___MAX) THEN
    Q_SPECL_NO_ASSUM 0 [`DS`, `LTL_EVENTUAL l`, `pf`, `sv`, `a`] THEN
    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC std_ss [LTL_SEM_THM] THEN
    PROVE_TAC[]
  );




val GEN_BUECHI_IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY =
 store_thm
  ("GEN_BUECHI_IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY",
   ``!A fc.
    A_IS_EMPTY (A_NDET(A, A_BIGAND (MAP (\p. ACCEPT_COND_GF p) fc))) =
    IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE (symbolic_kripke_structure A.S0 A.R) fc``,


SIMP_TAC std_ss [A_IS_EMPTY_def,
  A_SEM_THM, IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  symbolic_kripke_structure_REWRITES,
  IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
  IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_TRANSITION_def,
  A_BIGAND_SEM,
  ACCEPT_COND_GF_def, ACCEPT_F_def,
  ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
  MEM_MAP, GSYM LEFT_EXISTS_AND_THM
  ] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  Q_SPECL_NO_ASSUM 0 [`p`, `PATH_RESTRICT p A.S`] THEN
  CLEAN_ASSUMPTIONS_TAC THENL [
    SIMP_ASSUMPTIONS_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def,
      INTER_SUBSET],

    FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION___SPLIT],

    SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INPUT_RUN_STATE_UNION___SPLIT] THEN
    PROVE_TAC[],

    FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION___SPLIT] THEN
    PROVE_TAC[]
  ],


  Q_SPEC_NO_ASSUM 0 `INPUT_RUN_PATH_UNION A i w` THEN
  FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def] THEN
  PROVE_TAC[]
]);


val LTL_TO_GEN_BUECHO_DS___A_NDET___IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY =
 store_thm
  ("LTL_TO_GEN_BUECHO_DS___A_NDET___IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY",
   ``!DS sv pf.
    A_IS_EMPTY (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv) =
    IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE (symbolic_kripke_structure
          (P_AND
             (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,pf sv))
          (XP_BIGAND (MAP (\xp. xp sv) DS.R))) (MAP (\x. x sv) DS.FC)``,

    REPEAT STRIP_TAC THEN
    ASSUME_TAC (GSYM GEN_BUECHI_IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY) THEN
    Q_SPEC_NO_ASSUM 0 `symbolic_semi_automaton (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)
    (P_AND (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,pf sv))
    (XP_BIGAND (MAP (\xp. xp sv) DS.R))` THEN
    FULL_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES] THEN
    WEAKEN_HD_TAC THEN

    SIMP_TAC std_ss [A_IS_EMPTY_def, LTL_TO_GEN_BUECHI_DS___A_NDET_def,
                     A_SEM_THM, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                     INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                     IS_TRANSITION_def, symbolic_semi_automaton_REWRITES,
                     P_SEM_THM, ACCEPT_COND_PROP_def, ACCEPT_COND_SEM_def,
                     ACCEPT_COND_SEM_TIME_def, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                     MAP_MAP_o, combinTheory.o_DEF] THEN
    METIS_TAC[]);


val GEN_BUECHI_KS_SEM___TO___KRIPKE_STRUCTURE_EMPTY =
 store_thm
  ("GEN_BUECHI_KS_SEM___TO___KRIPKE_STRUCTURE_EMPTY",
   ``!A fc. DISJOINT A.S (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M) ==> (
    A_KS_SEM M (A_UNIV(A, A_NOT (A_BIGAND (MAP (\p. ACCEPT_COND_GF p) fc)))) =
    IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE (
      (SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT M
      (symbolic_kripke_structure A.S0 A.R))) fc)``,


SIMP_TAC std_ss [A_IS_EMPTY_def, A_KS_SEM_def,
  A_SEM_THM, IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  symbolic_kripke_structure_REWRITES,
  IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
  IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  IS_TRANSITION_def,
  A_BIGAND_SEM,
  ACCEPT_COND_GF_def, ACCEPT_F_def,
  ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
  MEM_MAP, GSYM LEFT_EXISTS_AND_THM,
  SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT_def,
  IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
  XP_SEM_THM, P_SEM_THM
  ] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  Q_SPEC_NO_ASSUM 0 `p` THEN
  Cases_on `(!n. XP_SEM M.R (p n,p (SUC n))) /\ P_SEM (p 0) M.S0` THENL [
    FULL_SIMP_TAC std_ss [IMP_DISJ_THM],
    METIS_TAC[]
  ] THEN
  Q_SPEC_NO_ASSUM 2 `PATH_RESTRICT p A.S` THEN
  CLEAN_ASSUMPTIONS_TAC THENL [
    SIMP_ASSUMPTIONS_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def,
      INTER_SUBSET],

    FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION___SPLIT],

    SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INPUT_RUN_STATE_UNION___SPLIT] THEN
    PROVE_TAC[],

    FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION___SPLIT] THEN
    PROVE_TAC[]
  ],

  SUBGOAL_TAC `P_SEM (INPUT_RUN_PATH_UNION A i w 0) M.S0` THEN1 (
    SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def] THEN
    UNDISCH_NO_TAC 3 THEN
    ONCE_REWRITE_TAC[P_USED_VARS_INTER_THM] THEN
    IMP_TO_EQ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
      GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
      SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, PATH_SUBSET_def] THEN
    METIS_TAC[]
  ) THEN
  SUBGOAL_TAC `!n.
            XP_SEM M.R
              (INPUT_RUN_STATE_UNION A (i n) (w n),
               INPUT_RUN_STATE_UNION A (i (SUC n)) (w (SUC n)))` THEN1 (
    SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def] THEN
    UNDISCH_NO_TAC 5 THEN
    ONCE_REWRITE_TAC[XP_USED_VARS_INTER_THM] THEN
    IMP_TO_EQ_TAC THEN FORALL_EQ_STRIP_TAC THEN BINOP_TAC THEN SIMP_TAC std_ss [] THEN
    SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
      GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
      SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, PATH_SUBSET_def, XP_USED_VARS_def] THEN
    METIS_TAC[]
  ) THEN
  Q_SPEC_NO_ASSUM 7 `INPUT_RUN_PATH_UNION A i w` THEN
  METIS_TAC[INPUT_RUN_PATH_UNION_def]
]);



val LTL_TO_GEN_BUECHI_DS___KS_SEM___KRIPKE_STRUCTURE =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___KS_SEM___KRIPKE_STRUCTURE",

  ``!DS l pf sv M a.
    (IS_ELEMENT_ITERATOR sv DS.SN (DS.IV UNION (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)) /\
     LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, a, T, pf) IN DS.B) ==>

      (LTL_KS_SEM M l = IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
        (SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT M (symbolic_kripke_structure  (P_AND
               (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,P_NOT (pf sv)))
            (XP_BIGAND (MAP (\xp. xp sv) DS.R))))  (MAP (\x. x sv) DS.FC))``,

    REPEAT STRIP_TAC THEN
    ASSUME_TAC LTL_TO_GEN_BUECHI_DS___KS_SEM___MIN THEN
    Q_SPECL_NO_ASSUM 0 [`DS`, `l`, `pf`, `sv`, `a`] THEN
    UNDISCH_HD_TAC THEN
    SUBGOAL_TAC `LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv` THEN1 (
      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def] THEN
      PROVE_TAC[IS_ELEMENT_ITERATOR_SUBSET, SUBSET_UNION]
    ) THEN
    ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN DISCH_TAC THEN WEAKEN_HD_TAC THEN

    SUBGOAL_TAC `A_KS_SEM M (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv) =
      A_KS_SEM M (A_UNIV(symbolic_semi_automaton
                  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)
                  (P_AND(LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv, (P_NOT (pf sv))))
                  (XP_BIGAND (MAP (\xp. xp sv) DS.R)),
                  A_NOT (A_BIGAND ((MAP (\p. ACCEPT_COND_GF p)) ((MAP (\x. x sv) DS.FC))))))` THEN1 (
      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___A_UNIV_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, A_SEM_THM,
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        symbolic_semi_automaton_REWRITES, INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def, P_SEM_THM, ACCEPT_COND_PROP_def,
        ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, IMP_DISJ_THM,
        IS_TRANSITION_def, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def, MAP_MAP_o, combinTheory.o_DEF, A_KS_SEM_def] THEN
      FORALL_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      FORALL_EQ_STRIP_TAC THEN
      REPEAT BOOL_EQ_STRIP_TAC
    ) THEN
    ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

    REMAINS_TAC `DISJOINT (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)
                 (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)` THEN1 (
        PROVE_TAC[GEN_BUECHI_KS_SEM___TO___KRIPKE_STRUCTURE_EMPTY,
                  symbolic_semi_automaton_REWRITES]
    ) THEN
    SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, IS_ELEMENT_ITERATOR_def,
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, SUBSET_DEF, IN_BETA_THM,
      IN_COMPL, IN_UNION] THEN
    PROVE_TAC[]
  );




val LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE =
 save_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE",

    SIMP_RULE std_ss [LTL_TO_GEN_BUECHO_DS___A_NDET___IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY]
    LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___MAX);


val LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___KRIPKE_STRUCTURE =
 save_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___KRIPKE_STRUCTURE",

    SIMP_RULE std_ss [LTL_TO_GEN_BUECHO_DS___A_NDET___IS_EMPTY___TO___KRIPKE_STRUCTURE_EMPTY]
    LTL_TO_GEN_BUECHI_DS___SEM___GEN_CONTRADICTION___MAX);







val LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS",

   ``!DS sv l b1 b2 pf.
      (LTL_TO_GEN_BUECHI_DS___SEM DS /\ LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\ (l, b1, b2, pf) IN DS.B) ==>
      (P_USED_VARS (pf sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
       LTL_USED_VARS l SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))``,

    REWRITE_TAC [GSYM UNION_SUBSET] THEN
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN

    REMAINS_TAC `(P_USED_VARS (pf sv) UNION LTL_USED_VARS l) SUBSET LTL_TO_GEN_BUECHI_DS___USED_VARS DS sv` THEN1 (
      SIMP_ASSUMPTIONS_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def] THEN
      PROVE_TAC[SUBSET_TRANS]
    ) THEN

    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def] THEN
    REMAINS_TAC `P_USED_VARS (pf sv) UNION LTL_USED_VARS l SUBSET
                BIGUNION (IMAGE (\(l,b1,b2,pf). P_USED_VARS (pf sv) UNION LTL_USED_VARS l) DS.B)` THEN1 (
      PROVE_TAC[SUBSET_UNION, UNION_ASSOC, SUBSET_TRANS]
    ) THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM] THEN
    REPEAT STRIP_TAC THEN
    Q_TAC EXISTS_TAC `(l, b1, b2, pf)` THEN
    ASM_SIMP_TAC std_ss []
  );



val LTL_TO_GEN_BUECHI_DS___SEM___S0 =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___S0",

   ``!DS sv A.
      (LTL_TO_GEN_BUECHI_DS___SEM DS /\ LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\ (A = LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv)) ==>
      (P_USED_VARS A.S0 SUBSET A.S)``,


      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___SEM_def,
        symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def] THEN
      REPEAT GEN_TAC THEN
      `?S0. DS.S0 = S0` by PROVE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      `(!n b. MEM (n,b) S0 ==> n < DS.SN)` by PROVE_TAC[] THEN
      UNDISCH_HD_TAC THEN
      REPEAT WEAKEN_HD_TAC THEN
      Induct_on `S0` THENL [
        SIMP_TAC list_ss [P_BIGAND_def, P_USED_VARS_def, EMPTY_SUBSET],

        SIMP_TAC list_ss [P_BIGAND_def, P_USED_VARS_def, UNION_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
          ALL_TAC,
          METIS_TAC[]
        ] THEN
        Cases_on `h` THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_S,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def] THEN
        Cases_on `r` THEN
        SIMP_ALL_TAC arith_ss [SUBSET_DEF, P_USED_VARS_def, IN_SING] THEN
        SIMP_TAC std_ss [IN_DEF] THEN
        METIS_TAC[IN_DEF]
      ]);



val LTL_TO_GEN_BUECHI_DS___SEM___R =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___SEM___R",

   ``!DS sv A.
      (LTL_TO_GEN_BUECHI_DS___SEM DS /\ LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv /\ (A = LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv)) ==>
      (XP_USED_VARS A.R SUBSET (A.S UNION DS.IV))``,


      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___SEM_def,
        symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
        UNION_SUBSET] THEN
      REPEAT GEN_TAC THEN
      `?R. DS.R = R` by PROVE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      `LIST_BIGUNION (MAP (\xpf. XP_USED_VARS (xpf sv)) R) SUBSET
       LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by METIS_TAC[] THEN
      UNDISCH_HD_TAC THEN
      REPEAT WEAKEN_HD_TAC THEN
      Induct_on `R` THENL [
        SIMP_TAC list_ss [LIST_BIGUNION_def, XP_USED_VARS___DIRECT_DEF, XP_BIGAND_def,
          EMPTY_SUBSET, UNION_EMPTY],


        SIMP_TAC list_ss [LIST_BIGUNION_def, XP_USED_VARS___DIRECT_DEF, XP_BIGAND_def,
          UNION_SUBSET] THEN
        REPEAT STRIP_TAC THEN
        METIS_TAC[]
      ]);



(*This are the basic definitions, now we can start to
  construct such valid datastructures*)

(*The basic one is the empty datastructure*)
val EMPTY_LTL_TO_GEN_BUECHI_DS_def =
 Define `
  EMPTY_LTL_TO_GEN_BUECHI_DS = ltl_to_gen_buechi_ds 0 [] {} [] [] {}`;


val EMPTY_LTL_TO_GEN_BUECHI_DS___SEM =
  store_thm
    ("EMPTY_LTL_TO_GEN_BUECHI_DS___SEM",
     ``LTL_TO_GEN_BUECHI_DS___SEM EMPTY_LTL_TO_GEN_BUECHI_DS``,

     SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___SEM_def, EMPTY_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES,
       IS_ELEMENT_ITERATOR_0, LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def, A_BIGAND_def,
       A_SEM_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, IS_TRANSITION_def, XP_BIGAND_def, XP_SEM_def,
       symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def, P_BIGAND_def, P_SEM_def,
       PATH_SUBSET_def, SUBSET_DEF, LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
       LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, LTL_TO_GEN_BUECHI_DS___USED_VARS_def, LIST_BIGUNION_def, NOT_IN_EMPTY,
       IMAGE_EMPTY, BIGUNION_EMPTY] THEN
    EXISTS_TAC ``\n:num. EMPTY`` THEN
    SIMP_TAC std_ss [NOT_IN_EMPTY]);


(*Then we can extend an existing datastructure*)
val EXTEND_LTL_TO_GEN_BUECHI_DS_def =
 Define `
  EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B' =
     (ltl_to_gen_buechi_ds (DS.SN + n') (S0' ++ DS.S0) (IV' UNION DS.IV) (R' ++ DS.R) (FC' ++ DS.FC) (B' UNION DS.B))`;


val EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES =
  store_thm
    ("EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES",
    ``!DS n' S0' IV' R' FC' B'.

      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').SN = DS.SN + n') /\
      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').S0 = S0'++DS.S0) /\
      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').IV = IV' UNION DS.IV) /\
      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').R =  R'++DS.R) /\
      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').FC = FC'++DS.FC) /\
      ((EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B').B = B' UNION DS.B)``,

    SIMP_TAC std_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES]);



val EXTEND_LTL_TO_GEN_BUECHI_DS___EXTEND_LTL_TO_GEN_BUECHI_DS =
  store_thm
    ("EXTEND_LTL_TO_GEN_BUECHI_DS___EXTEND_LTL_TO_GEN_BUECHI_DS",
    ``!DS n' S0' IV' R' FC' B' n'' S0'' IV'' R'' FC'' B''.

      (EXTEND_LTL_TO_GEN_BUECHI_DS (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') n'' S0'' IV'' R'' FC'' B'') =
      (EXTEND_LTL_TO_GEN_BUECHI_DS DS (n''+n') (S0''++S0') (IV'' UNION IV') (R''++R') (FC''++FC') (B'' UNION B'))``,

    SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES,
      UNION_ASSOC]);


val EXTEND_LTL_TO_GEN_BUECHI_DS___USED_VARS =
  store_thm
    ("EXTEND_LTL_TO_GEN_BUECHI_DS___USED_VARS",
    ``!DS sv n' S0' IV' R' FC' B'.
      LTL_TO_GEN_BUECHI_DS___USED_VARS DS sv SUBSET
      LTL_TO_GEN_BUECHI_DS___USED_VARS (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv``,

  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def, SUBSET_DEF, IN_UNION,
    EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES, LIST_BIGUNION_APPEND,
    LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
    IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [
    NTAC 3 DISJ1_TAC THEN
    EXISTS_TAC ``n:num`` THEN
    DECIDE_TAC,

    PROVE_TAC[]
  ]);




val EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR =
  store_thm
    ("EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR",

    ``!DS sv n' S0' IV' R' FC' B'.
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv ==>
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES] THEN
    `DS.SN <= DS.SN + n'` by DECIDE_TAC THEN
    `DS.IV SUBSET IV' UNION DS.IV` by PROVE_TAC[SUBSET_UNION] THEN
    PROVE_TAC[IS_ELEMENT_ITERATOR_GE, IS_ELEMENT_ITERATOR_SUBSET]);



val EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN =
  store_thm
    ("EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN",

``!DS sv w i DS' w' n' S0' IV' R' FC' B'.

(LTL_TO_GEN_BUECHI_DS___SEM DS /\
 LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS' sv /\
(!n b. (MEM (n, b) S0' ==> (n < n' + DS.SN))) /\
(DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') /\
(w' = INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w)) ==>

(LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS' i w sv =

PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS' sv) /\
P_SEM (w 0) (P_BIGAND (MAP (\(n, b). if b then P_PROP (sv n) else P_NOT(P_PROP (sv n))) S0')) /\
(!n xp. MEM xp R' ==> XP_SEM (xp sv) (w' n, w' (SUC n))) /\
(!p. MEM p FC' ==> A_SEM w' (ACCEPT_COND_GF (p sv))) /\
LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i (PATH_RESTRICT w
  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv)``,


SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def,
  LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
  INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
  IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, IS_TRANSITION_def,
  LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
  symbolic_semi_automaton_REWRITES, PATH_SUBSET_def,
  (SIMP_RULE std_ss [] PATH_RESTRICT_SUBSET),
  PATH_RESTRICT_def, PATH_MAP_def] THEN
REPEAT STRIP_TAC THEN
CONJ_EQ_STRIP_TAC THEN

SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def,
  ltl_to_gen_buechi_ds_REWRITES,
  LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
  LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
  XP_BIGAND_SEM, P_BIGAND_SEM, A_BIGAND_SEM,
  MEM_MAP, GSYM LEFT_FORALL_IMP_THM, GSYM EXISTS_OR_THM,
  GSYM LEFT_AND_OVER_OR,
  LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def] THEN

SPECL_NO_ASSUM 3 [``sv:num->'a``] THEN
`LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv` by
  METIS_TAC[EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN
FULL_SIMP_TAC std_ss [] THEN
WEAKEN_NO_TAC 1 THEN


SUBGOAL_TAC `(!y. MEM y S0' \/ MEM y DS.S0 ==>
  P_SEM (w 0 UNION (i 0 DIFF (\s. ?n. n < n' + DS.SN /\ (s = sv n))))
  ((\(n,b). (if b then P_PROP (sv n) else P_NOT (P_PROP (sv n)))) y)) =

  ((!y. MEM y DS.S0 ==> P_SEM
    (w 0 INTER (\s. ?n. n < DS.SN /\ (s = sv n)) UNION
      (i 0 DIFF (\s. ?n. n < DS.SN /\ (s = sv n))))
    ((\(n,b). (if b then P_PROP (sv n) else P_NOT (P_PROP (sv n)))) y)) /\
  (!y. MEM y S0' ==> P_SEM (w 0)
    ((\(n,b). (if b then P_PROP (sv n) else P_NOT (P_PROP (sv n)))) y)))` THEN1 (

  SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
  FORALL_EQ_STRIP_TAC THEN
  Cases_on `y` THEN
  SIMP_TAC std_ss [P_SEM_def, IN_UNION, IN_DIFF, IN_INTER,
    prove (``!s b p1 p2. P_SEM s (if b then p1 else p2) =
          if b then P_SEM s p1 else P_SEM s p2``, METIS_TAC[]),
    prove (``!x f. x IN (\x. f x) = f x``,
           SIMP_TAC std_ss [IN_DEF])] THEN
  SIMP_ALL_TAC arith_ss [LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
    EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IS_ELEMENT_ITERATOR_def,
    IN_UNION, SUBSET_DEF, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
  `!n. n < DS.SN ==> n < n' + DS.SN` by DECIDE_TAC THEN
  Cases_on `r` THEN
  METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [INTER_SUBSET] THEN
REPEAT CONJ_EQ_STRIP_TAC THEN
NTAC 3 WEAKEN_HD_TAC THEN


SIMP_TAC std_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
REPEAT CONJ_EQ_STRIP_TAC THEN
NTAC 2 WEAKEN_HD_TAC THEN

SUBGOAL_TAC `(!xp. MEM xp DS.R ==>
    XP_USED_VARS (xp sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) UNION DS.IV) /\
             (!p. MEM p DS.FC ==>
    P_USED_VARS (p sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) UNION DS.IV)` THEN1 (

  UNDISCH_NO_TAC 1 THEN
  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def, UNION_SUBSET] THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_BIGUNION, MEM_MAP, GSYM LEFT_FORALL_IMP_THM, IN_UNION,
    prove (``!B1 B2 B3. (B1 /\ B2) ==> B3 = (B1 ==> B2 ==> B3)``, METIS_TAC[])] THEN
  METIS_TAC[]
) THEN

REMAINS_TAC `!n. (w n INTER (\s. ?n. n < DS.SN /\ (s = sv n)) UNION
                  (i n DIFF (\s. ?n. n < DS.SN /\ (s = sv n)))) INTER
                  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) =

                  (w n UNION (i n DIFF (\s. ?n. n < n' + DS.SN /\ (s = sv n)))) INTER
                  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)` THEN1 (

  SIMP_TAC std_ss [ACCEPT_COND_GF_def, A_SEM_def,
    ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, ACCEPT_F_def] THEN
  METIS_TAC[P_USED_VARS_INTER_SUBSET_THM, XP_USED_VARS_INTER_SUBSET_BOTH_THM]
) THEN


SIMP_ALL_TAC arith_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
  LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, SUBSET_DEF,
  EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
  LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
  IS_ELEMENT_ITERATOR_def,
  prove (``!x f. x IN (\x. f x) = f x``, METIS_TAC[IN_DEF])] THEN

`!n. n < DS.SN ==> n < n' + DS.SN` by DECIDE_TAC THEN
METIS_TAC []);





(*Usually it is only extended in special ways. So
  the following lemmata is helpful*)
val EXTEND_LTL_TO_GEN_BUECHI_DS___SEM =
 store_thm
  ("EXTEND_LTL_TO_GEN_BUECHI_DS___SEM",

    ``!DS DS' n' S0' IV' R' FC' B'.
        (LTL_TO_GEN_BUECHI_DS___SEM DS /\
         (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') /\

         (*The extension does not conflict with old
         binding runs. Every old binding run can be extended
         to a new binding run. Obviously new binding runs can
         be restricted to old ones. So its really
         an extension.*)
         (!sv w i. (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS' sv /\
                    LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv /\
                    (!l b1 b2 pf. ((l,b1,b2,pf) IN DS.B ==>
                      LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l,b1,b2,pf) i sv))) ==>
                   ((?w'. (w = (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))) /\
                          LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS' i w' sv /\
                          (!l b1 b2 pf. (((l,b1,b2,pf) IN B' /\ LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS' i w' sv) ==>
                              LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS' w' (l,b1,b2,pf) i sv))))) /\


         (*The set of state variables is extended
         large enough*)
         (!n b. (MEM (n, b) S0') ==> (n < n' + DS.SN)) /\

         (*The set of input variables IV is extended
         large enough*)
         (!sv.
           (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS' sv /\
            (!l' b1' b2' pf'. ((l',b1',b2',pf') IN DS.B ==>
              P_USED_VARS (pf' sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
              LTL_USED_VARS l' SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) ==>

            ((LIST_BIGUNION (MAP (\xpf. XP_USED_VARS (xpf sv)) R') UNION
             LIST_BIGUNION (MAP (\pf. P_USED_VARS (pf sv)) FC') UNION
             BIGUNION
              (IMAGE (\(l,b1,b2,pf). P_USED_VARS (pf sv) UNION LTL_USED_VARS l) B')) SUBSET
             (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS' sv UNION IV' UNION DS.IV))))) ==>

        LTL_TO_GEN_BUECHI_DS___SEM DS'``,

SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
UNDISCH_KEEP_NO_TAC 3 THEN
SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___SEM_def] THEN
NTAC 3 STRIP_TAC THEN

SPECL_NO_ASSUM 1 [``sv:num->'a``] THEN
SPECL_NO_ASSUM 3 [``sv:num->'a``] THEN
SPECL_NO_ASSUM 5 [``sv:num->'a``] THEN

`LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv` by
  PROVE_TAC[EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN

`LIST_BIGUNION (MAP (\xpf. XP_USED_VARS (xpf sv)) R') UNION
 LIST_BIGUNION (MAP (\pf. P_USED_VARS (pf sv)) FC') UNION
 BIGUNION (IMAGE (\(l,b1,b2,pf). P_USED_VARS (pf sv) UNION LTL_USED_VARS l) B') SUBSET
   LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv UNION IV' UNION DS.IV` by METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS] THEN
WEAKEN_NO_TAC 3 THEN
GSYM_NO_TAC 6 THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [
  UNDISCH_HD_TAC THEN
  SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  `!n. n < DS.SN ==> n < n' + DS.SN` by DECIDE_TAC THEN
  METIS_TAC[],



  UNDISCH_NO_TAC 5 THEN UNDISCH_NO_TAC 1 THEN
  REPEAT WEAKEN_HD_TAC THEN
  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
    EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF,
    IN_UNION, IMAGE_UNION, BIGUNION_UNION,
    LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, LIST_BIGUNION_APPEND] THEN
  SUBGOAL_TAC `!x. (?n. n < DS.SN /\ (x = sv n)) ==> (?n. n < n' + DS.SN /\ (x = sv n))` THEN1 (
    REPEAT STRIP_TAC THEN
    EXISTS_TAC ``n:num`` THEN
    ASM_SIMP_TAC arith_ss []
  ) THEN
  METIS_TAC[],


  SPECL_NO_ASSUM 4 [``i:num->'a set``] THEN
  CLEAN_ASSUMPTIONS_TAC THEN
  SPECL_NO_ASSUM 5 [``w:num->'a set``, ``i:num->'a set``] THEN
  UNDISCH_HD_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC ``w':num->'a set`` THEN
  ASM_SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IN_UNION] THEN
  REPEAT STRIP_TAC THEN1 PROVE_TAC[] THEN
  RES_TAC THEN
  UNDISCH_HD_TAC THEN
  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, P_SEM_def,
    LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def, LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def] THEN

  ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN

  SUBGOAL_TAC `P_USED_VARS (pf sv) SUBSET
    (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)` THEN1 (
    METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS]
  ) THEN

  SUBGOAL_TAC `!w' t.
              (LTL_TO_GEN_BUECHI_DS___FAIR_RUN
                (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') i w' sv) ==>

              ((w' t INTER LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION
                  (i t DIFF LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) INTER
                (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) =

                (w' t UNION (i t DIFF LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS
                (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv)) INTER
                (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))` THEN1 (

    UNDISCH_NO_TAC 13 THEN (*Element Iterator DS'*)
    REPEAT WEAKEN_HD_TAC THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
    SUBGOAL_TAC `PATH_SUBSET w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS
      (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv)` THEN1 (
      FULL_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES]
    ) THEN
    SUBGOAL_TAC `(LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) SUBSET
      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS
      (EXTEND_LTL_TO_GEN_BUECHI_DS DS n' S0' IV' R' FC' B') sv)` THEN1 (

      SIMP_TAC arith_ss [SUBSET_DEF, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC ``n:num`` THEN
      ASM_SIMP_TAC arith_ss []
    ) THEN

    SIMP_ALL_TAC arith_ss [PATH_SUBSET_def, SUBSET_DEF,
      LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
      IS_ELEMENT_ITERATOR_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, IN_UNION] THEN
    `!n. n < DS.SN ==> n < n' + DS.SN` by DECIDE_TAC THEN
    METIS_TAC[]
  ) THEN

  SIMP_TAC std_ss [prove (``(~A ==> ~B) = (B ==> A)``, PROVE_TAC[])] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
    METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],

    `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` by
     METIS_TAC[EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
    FULL_SIMP_TAC std_ss [] THEN
    SPECL_NO_ASSUM 5 [``(PATH_RESTRICT (w'':num->'a set) (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (DS:'a ltl_to_gen_buechi_ds) sv))``] THEN
    UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 1 THEN
    ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
      INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, symbolic_semi_automaton_REWRITES] THEN
    METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],


    `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` by
     METIS_TAC[EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
    FULL_SIMP_TAC std_ss [] THEN
    SPECL_NO_ASSUM 4 [``(PATH_RESTRICT (w'':num->'a set) (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (DS:'a ltl_to_gen_buechi_ds) sv))``] THEN
    UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 1 THEN
    ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
      INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, symbolic_semi_automaton_REWRITES] THEN
    METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
  ]
]);



(*often we can restrict to just extending the
  bindings and the set of input vars, this
  simplifies a lot*)
val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def =
 Define `
   EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV=
     EXTEND_LTL_TO_GEN_BUECHI_DS DS 0 [] IV [] [] B`;


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS``,

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, ltl_to_gen_buechi_ds_REWRITES,
      LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS DS``,

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS_def, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
      ltl_to_gen_buechi_ds_REWRITES]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIR_RUN =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___FAIR_RUN (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS``,

    SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, FUN_EQ_THM,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN DS``,

    SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, FUN_EQ_THM,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIR_RUN]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN DS``,

    SIMP_TAC std_ss [FUN_EQ_THM,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def, EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN]);

val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS``,

    SIMP_TAC std_ss [FUN_EQ_THM, EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___BINDING_RUN =
  prove (
    ``!DS B IV.
        LTL_TO_GEN_BUECHI_DS___BINDING_RUN (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) =
        LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS``,

    SIMP_TAC std_ss [FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN
    Cases_on `x'` THEN Cases_on `r` THEN Cases_on `r'` THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN]);



val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___ELEMENT_FUNCTIONS =
  prove (
    ``!DS B IV.
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).SN = DS.SN) /\
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).S0 = DS.S0) /\
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).IV = (IV UNION DS.IV)) /\
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).R =  DS.R) /\
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).FC =  DS.FC) /\
        ((EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV).B =  (B UNION DS.B))``,

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES]);



val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES =
  save_thm ("EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES",
    LIST_CONJ [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIR_RUN,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___BINDING_RUN,
              EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___ELEMENT_FUNCTIONS]);




(*Some simple lemmata about how to extend and remove bindings*)
val LTL_TO_GEN_BUECHI_DS___PRODUCT_def =
 Define
  `LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 =
   ltl_to_gen_buechi_ds
     (DS1.SN+DS2.SN)
     (DS1.S0++(MAP (\(n, b). (n+DS1.SN, b)) DS2.S0))
     (DS1.IV UNION DS2.IV)
     (DS1.R++(MAP (\pf sv. (pf (\n. (sv (n+DS1.SN))))) DS2.R))
     (DS1.FC++(MAP (\fc sv. (fc (\n. (sv (n+DS1.SN))))) DS2.FC))
     (DS1.B UNION (IMAGE (\(l, b1, b2, pf). (l, b1, b2, (\sv. pf (\n. (sv (n+DS1.SN)))))) DS2.B))`;


val LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def =
 Define
  `LTL_TO_GEN_BUECHI_DS___SET_BINDINGS DS B =
   ltl_to_gen_buechi_ds
     DS.SN DS.S0 DS.IV DS.R DS.FC B`;




val LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS =
  store_thm
    ("LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS",
    ``!DS DS'.
      ((DS.SN = DS'.SN) /\ (DS.S0 = DS'.S0) /\ (DS.IV = DS'.IV) /\
       (DS.R = DS'.R) /\ (DS.FC = DS'.FC) /\ (DS'.B SUBSET DS.B)) ==>
      (LTL_TO_GEN_BUECHI_DS___SEM DS ==> LTL_TO_GEN_BUECHI_DS___SEM DS')``,


    REPEAT STRIP_TAC THEN
    `!sv. LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>
        (!l b1 b2 pf. (l, b1, b2, pf) IN DS.B ==>
     ((P_USED_VARS (pf sv) SUBSET
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
     (LTL_USED_VARS l SUBSET
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` by METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS] THEN

    UNDISCH_NO_TAC 1 THEN
    ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def] THEN
    DISCH_TAC THEN GEN_TAC THEN
    NTAC 2 (SPECL_NO_ASSUM 1 [``sv:num->'a``]) THEN
    NTAC 2 UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
      ltl_to_gen_buechi_ds_REWRITES] THEN
    REPEAT STRIP_TAC THENL [
      PROVE_TAC[],

      UNDISCH_NO_TAC 1 THEN UNDISCH_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, UNION_SUBSET,
        ltl_to_gen_buechi_ds_REWRITES] THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_NO_TAC 1 THEN
      SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
        GSYM RIGHT_EXISTS_AND_THM] THEN
      METIS_TAC[],

      FULL_SIMP_TAC std_ss [] THEN
      SPECL_NO_ASSUM 1 [``i:num->'a set``] THEN
      CLEAN_ASSUMPTIONS_TAC THEN
      EXISTS_TAC ``w:num->'a set`` THEN
      REPEAT STRIP_TAC THENL [
        UNDISCH_HD_TAC THEN
        ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
          LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
          ltl_to_gen_buechi_ds_REWRITES],

        `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l,b1,b2,pf) i sv` by PROVE_TAC[SUBSET_DEF] THEN
        UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
          LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
          LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
          ltl_to_gen_buechi_ds_REWRITES] THEN
        ASM_SIMP_TAC std_ss [] THEN
        METIS_TAC[]
      ]
    ]);




val LTL_TO_GEN_BUECHI_DS___SEM___SET_BINDINGS =
  store_thm
    ("LTL_TO_GEN_BUECHI_DS___SEM___SET_BINDINGS",
    ``!DS B.
      ((B SUBSET DS.B) /\ (LTL_TO_GEN_BUECHI_DS___SEM DS) ==>
       LTL_TO_GEN_BUECHI_DS___SEM (LTL_TO_GEN_BUECHI_DS___SET_BINDINGS DS B))``,

    REPEAT STRIP_TAC THEN
    UNDISCH_HD_TAC THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def,
      ltl_to_gen_buechi_ds_REWRITES]);



val LTL_TO_GEN_BUECHI_DS___SEM___EQ =
  store_thm
    ("LTL_TO_GEN_BUECHI_DS___SEM___EQ",
    ``!DS DS'.
      ((DS.SN = DS'.SN) /\ (DS.S0 = DS'.S0) /\ (DS.IV = DS'.IV) /\
        (EVERY (\r. (?r'. (MEM r' DS'.R) /\ !sv.
          XPROP_LOGIC_EQUIVALENT (r sv) (r' sv))) DS.R) /\
        (EVERY (\r'. (?r. (MEM r DS.R) /\ !sv.
          XPROP_LOGIC_EQUIVALENT (r sv) (r' sv))) DS'.R) /\

        (EVERY (\fc. (?fc'. (MEM fc' DS'.FC) /\ !sv.
          PROP_LOGIC_EQUIVALENT (fc sv) (fc' sv))) DS.FC) /\
        (EVERY (\fc'. (?fc. (MEM fc DS.FC) /\ !sv.
          PROP_LOGIC_EQUIVALENT (fc sv) (fc' sv))) DS'.FC) /\

        (!l b1 b2 pf. ((l, b1, b2, pf) IN DS.B) ==> (?l' pf' b1' b2'. (b1 ==> b1') /\ (b2 ==> b2') /\ ((l', b1', b2', pf') IN DS'.B) /\
          LTL_EQUIVALENT l l' /\ !sv.
          PROP_LOGIC_EQUIVALENT (pf sv) (pf' sv))) /\
        (!l b1 b2 pf. ((l, b1, b2, pf) IN DS'.B) ==> (?l' pf' b1' b2'. (b1 ==> b1') /\ (b2 ==> b2') /\ ((l', b1', b2', pf') IN DS.B) /\
          LTL_EQUIVALENT l l' /\ !sv.
          PROP_LOGIC_EQUIVALENT (pf sv) (pf' sv))) /\
        (!sv. (LTL_TO_GEN_BUECHI_DS___USED_VARS DS sv = LTL_TO_GEN_BUECHI_DS___USED_VARS DS' sv))) ==>
      (LTL_TO_GEN_BUECHI_DS___SEM DS = LTL_TO_GEN_BUECHI_DS___SEM DS')``,


    Cases_on `DS` THEN Cases_on `DS'` THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES] THEN
    STRIP_TAC THEN
    NTAC 7 UNDISCH_HD_TAC (*everything except eq*) THEN
    ASM_SIMP_TAC std_ss [] THEN
    REPEAT WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def,
      LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
      ltl_to_gen_buechi_ds_REWRITES,
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
      EVERY_MEM,
      XPROP_LOGIC_EQUIVALENT_def,
      PROP_LOGIC_EQUIVALENT_def,
      LTL_EQUIVALENT_def] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [IMP_DISJ_THM] THEN
    FORALL_EQ_STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    EXISTS_EQ_STRIP_TAC THEN
    MATCH_MP_TAC (prove (``!A A' B B' w i sv. ((!i w sv. (A i w sv = A' i w sv)) /\ (B = B')) ==> (((A i w sv) /\ B) = ((A' i w sv) /\ B'))``,
           METIS_TAC[])) THEN
    LEFT_CONJ_TAC THENL [
      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
                      IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                      LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                      ltl_to_gen_buechi_ds_REWRITES,
                      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                      LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
                      symbolic_semi_automaton_REWRITES,
                      LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                      IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
                      INPUT_RUN_STATE_UNION_def, XP_BIGAND_SEM,
                      A_BIGAND_SEM,
                      MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      REPEAT BOOL_EQ_STRIP_TAC THEN
      BINOP_TAC THENL [
        METIS_TAC[],

        SIMP_TAC std_ss [ACCEPT_COND_GF_def, A_SEM_THM,
                        ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
                        ACCEPT_F_def] THEN
        METIS_TAC[]
      ],




      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def,
        INPUT_RUN_STATE_UNION_def, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        ltl_to_gen_buechi_ds_REWRITES, symbolic_semi_automaton_REWRITES
        ] THEN
      EQ_TAC THENL [
        STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 7 [`l`, `b1`, `b2`, `pf`] THEN
        PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC [] THEN
        CLEAN_ASSUMPTIONS_TAC THEN
        Q_SPECL_NO_ASSUM 6 [`l''`, `b1'`, `b2'`, `pf'`] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC [] THEN
        METIS_TAC[],


        STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 8 [`l`, `b1`, `b2`, `pf`] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 6 [`l'''`, `b1'`, `b2'`, `pf'`] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC [] THEN
        METIS_TAC[]
      ]
    ]);



val LTL_TO_GEN_BUECHI_DS___SEM___EXTEND_EQUIV_BINDING =
  store_thm
    ("LTL_TO_GEN_BUECHI_DS___SEM___EXTEND_EQUIV_BINDING",
    ``!DS l l' b1 b2 b1' b2' pf pf'.
      ((l, b1, b2, pf) IN DS.B /\
      LTL_EQUIVALENT l l' /\ (LTL_USED_VARS l' SUBSET LTL_USED_VARS l) /\ !sv. (PROP_LOGIC_EQUIVALENT (pf sv) (pf' sv) /\ (P_USED_VARS (pf' sv) SUBSET P_USED_VARS (pf sv))) /\ (b1' ==> b1) /\ (b2' ==> b2)) ==>

      (LTL_TO_GEN_BUECHI_DS___SEM DS = LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(l', b1', b2', pf')} {}))``,

    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___EQ THEN
    SIMP_ALL_TAC std_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES,
                     UNION_EMPTY, IN_SING, IN_UNION, LTL_EQUIVALENT_def,
                     XPROP_LOGIC_EQUIVALENT_def, PROP_LOGIC_EQUIVALENT_def,
                     EVERY_MEM] THEN
    REPEAT STRIP_TAC THENL [
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      METIS_TAC[],

      Q_TAC EXISTS_TAC `l` THEN
      Q_TAC EXISTS_TAC `pf` THEN
      Q_TAC EXISTS_TAC `b1` THEN
      Q_TAC EXISTS_TAC `b2` THEN
      ASM_SIMP_TAC std_ss [],

      METIS_TAC[],

      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
                       EXTENSION, IN_UNION,
                       EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
      REPEAT STRIP_TAC THEN
      REPEAT BOOL_EQ_STRIP_TAC THEN
      SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
            GSYM RIGHT_EXISTS_AND_THM, IN_UNION, IN_SING] THEN
      EQ_TAC THEN STRIP_TAC THENL [
        METIS_TAC[],

        Q_TAC EXISTS_TAC `(l, b1, b2, pf)` THEN
        FULL_SIMP_TAC std_ss [IN_UNION, SUBSET_DEF],

        METIS_TAC[]
      ]
    ]);


val LTL_TO_GEN_BUECHI_DS___SEM___WEAKEN_BINDING =
  store_thm
    ("LTL_TO_GEN_BUECHI_DS___SEM___WEAKEN_BINDING",
    ``!DS l b1 b2 b1' b2' pf IV.
      (LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(l, b1, b2, pf)} IV) /\
      (b1' ==> b1) /\ (b2' ==> b2)) ==>

      LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(l, b1', b2', pf)} IV)``,

REPEAT STRIP_TAC THEN
ASSUME_TAC LTL_TO_GEN_BUECHI_DS___SEM___EXTEND_EQUIV_BINDING THEN
Q_SPECL_NO_ASSUM 0 [`EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(l,b1,b2,pf)} IV`, `l`, `l`, `b1`, `b2`, `b1'`, `b2'`, `pf`, `pf`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  ASM_SIMP_TAC std_ss [LTL_EQUIVALENT_def, SUBSET_REFL, PROP_LOGIC_EQUIVALENT_def,
    EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES, IN_UNION, IN_SING]
) THEN
FULL_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN
UNDISCH_NO_TAC 2 THEN
MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN

SIMP_TAC std_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_SING,
  SUBSET_DEF, IN_INSERT, UNION_EMPTY] THEN
METIS_TAC[]);


val EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM =
 store_thm
  ("EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM",

    ``!DS B IV.
        (LTL_TO_GEN_BUECHI_DS___SEM DS /\
        (!sv l b1 b2 pf.
           ((l, b1, b2, pf) IN B /\
            LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) sv /\
            (!l' b1' b2' pf'. ((l',b1',b2',pf') IN DS.B ==>
              P_USED_VARS (pf' sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
              LTL_USED_VARS l' SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))) ==>

             P_USED_VARS (pf sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION IV UNION DS.IV) /\
             LTL_USED_VARS l SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION IV UNION DS.IV)) /\

        (!sv l b1 b2 pf w i.
           ((l, b1, b2, pf) IN B /\ LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv /\
            LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV) sv /\
            (!l' b1' b2' pf'. ((l',b1',b2',pf') IN DS.B ==>
              P_USED_VARS (pf' sv) SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
              LTL_USED_VARS l' SUBSET (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV) /\
              LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l',b1',b2',pf') i sv))) ==>

            LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l,b1,b2,pf) i sv)) ==>

        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS B IV)``,

REWRITE_TAC[EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___SEM) THEN
ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY] THEN
REPEAT STRIP_TAC THENL [
  EXISTS_TAC ``w:num->'a set`` THEN
  ASM_REWRITE_TAC[GSYM EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
    EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    METIS_TAC[PATH_RESTRICT_PATH_SUBSET, LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET],

    METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR]
  ],


  REMAINS_TAC `!l b1 b2 pf. (l, b1, b2, pf) IN B ==>
                        P_USED_VARS (pf sv) UNION LTL_USED_VARS l SUBSET
                        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION IV UNION DS.IV` THEN1 (
    UNDISCH_HD_TAC THEN
    REPEAT WEAKEN_HD_TAC THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `x'` THEN Cases_on `r` THEN Cases_on `r'` THEN
    FULL_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
      EXTEND_LTL_TO_GEN_BUECHI_DS_def, IN_UNION,
      ltl_to_gen_buechi_ds_REWRITES] THEN
    METIS_TAC[IN_UNION]
  ) THEN

  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  ASM_REWRITE_TAC[UNION_SUBSET]
]);


(*Combining two complete datastructures*)
val LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM",

  ``!DS1 DS2. LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (LTL_TO_GEN_BUECHI_DS___SEM (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2))``,

SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEM_def, LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
                 ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def] THEN
REPEAT GEN_TAC THEN NTAC 4 STRIP_TAC THEN
SUBGOAL_TAC `IS_ELEMENT_ITERATOR sv DS1.SN DS1.IV /\
             IS_ELEMENT_ITERATOR (\n. sv (n + DS1.SN)) DS2.SN DS2.IV` THEN1 (
  UNDISCH_HD_TAC THEN
  REPEAT WEAKEN_HD_TAC THEN
  SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def, IN_UNION]
) THEN
Q_SPEC_NO_ASSUM 4 `sv` THEN
Q_SPEC_NO_ASSUM 4 `(\n. sv (n + DS1.SN))` THEN
NTAC 2 UNDISCH_HD_TAC THEN
ASM_SIMP_TAC list_ss [MEM_MAP] THEN
NTAC 2 WEAKEN_HD_TAC THEN
REPEAT STRIP_TAC THENL [
  `n < DS1.SN` by PROVE_TAC[] THEN
  DECIDE_TAC,

  Cases_on `y` THEN
  SIMP_ALL_TAC std_ss [] THEN
  `q < DS2.SN` by PROVE_TAC[] THEN
  ASM_SIMP_TAC arith_ss [],

  UNDISCH_NO_TAC 1 THEN
  UNDISCH_NO_TAC 3 THEN
  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
                   LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                   ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF,
                   IN_UNION, IN_LIST_BIGUNION, IMAGE_UNION,
                   BIGUNION_UNION, MEM_MAP, IN_BIGUNION,
                   IN_IMAGE,
                   GSYM RIGHT_EXISTS_AND_THM,
                   IN_BETA_THM,
                   PAIR_BETA_THM_4] THEN
  `!n. n < DS1.SN ==> n < DS1.SN + DS2.SN` by DECIDE_TAC THEN
  `!n. n < DS2.SN ==> n + DS1.SN < DS1.SN + DS2.SN` by DECIDE_TAC THEN
  METIS_TAC[],


  REWRITE_TAC [GSYM LTL_TO_GEN_BUECHI_DS___PRODUCT_def] THEN
  `!n. n < DS1.SN ==> n < DS1.SN + DS2.SN` by DECIDE_TAC THEN
  `!n. n < DS2.SN ==> n + DS1.SN < DS1.SN + DS2.SN` by DECIDE_TAC THEN
  `!n. ~((n + DS1.SN) < DS1.SN)` by DECIDE_TAC THEN

  `(?S1. (COMPL (\x. ?n. n < DS2.SN /\ (x = sv (n + DS1.SN)))) = S1) /\
   (?S2. (COMPL (\x. ?n. n < DS1.SN /\ (x = sv n))) = S2)`
     by SIMP_TAC std_ss [] THEN
  SUBGOAL_TAC `(!fc. MEM fc DS1.FC ==> P_USED_VARS (fc sv) SUBSET S1) /\
    (!fc. MEM fc DS2.FC ==> P_USED_VARS (fc (\n. sv (n + DS1.SN))) SUBSET S2) /\
    (!xp. MEM xp DS1.R ==> XP_USED_VARS (xp sv) SUBSET S1) /\
    (!xp. MEM xp DS2.R ==> XP_USED_VARS (xp (\n. sv (n + DS1.SN))) SUBSET S2) /\
    (!l b1 b2 pf. (l, b1, b2, pf) IN DS1.B ==> P_USED_VARS (pf sv) SUBSET S1) /\
    (!l b1 b2 pf. (l, b1, b2, pf) IN DS2.B ==> P_USED_VARS (pf (\n. sv (n + DS1.SN))) SUBSET S2)` THEN1 (
      UNDISCH_NO_TAC 9 (*USED VARS DS1*) THEN
      UNDISCH_NO_TAC 6 (*USED VARS DS2*) THEN
      GSYM_NO_TAC 1 THEN
      GSYM_NO_TAC 1 THEN
      UNDISCH_NO_TAC 9 THEN (*ELEMENT_ITERATOR*)
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___USED_VARS_def,
        SUBSET_DEF, IN_COMPL,
        IN_BETA_THM, IN_UNION, IN_LIST_BIGUNION, MEM_MAP,
        GSYM LEFT_EXISTS_AND_THM, DISJ_IMP_THM, FORALL_AND_THM,
        GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        IS_ELEMENT_ITERATOR_def,
        IN_BIGUNION, IN_IMAGE,
        prove (``!P. (!x. P x) = (!x1 x2 x3 x4. P (x1,x2,x3,x4))``, METIS_TAC[PAIR])] THEN
      METIS_TAC[]
  ) THEN

  SUBGOAL_TAC `(?P. !w w' n. (w n UNION w' n UNION
                  (i n DIFF (\s. ?n. n < DS1.SN + DS2.SN /\ (s = sv n)))) = P w w' n) /\
               (?P1. !w n. (w n UNION (i n DIFF (\s. ?n. n < DS1.SN /\ (s = sv n)))) = P1 w n) /\
               (?P2. !w' n. (w' n UNION (i n DIFF (\s. ?n. n < DS2.SN /\ (s = sv (n+ DS1.SN))))) = P2 w' n) /\
               (?P3. !w n. (w n UNION
                  (i n DIFF (\s. ?n. n < DS1.SN + DS2.SN /\ (s = sv n)))) = P3 w n)` THEN1 (
    SIMP_TAC std_ss [GSYM FUN_EQ_THM,
      prove (``(\x y. f x y) = f``, METIS_TAC[]),
      prove (``(\x y z. f x y z) = f``, METIS_TAC[])]
  ) THEN
  SUBGOAL_TAC `(!w w'. (PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv) /\
                       PATH_SUBSET w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2 (\n. sv (n + DS1.SN)))) ==>
                        ((!n. ((P w w' n) INTER S1) = (P1 w n) INTER S1) /\
                        (!n. ((P w w' n) INTER S2) = (P2 w' n) INTER S2))) /\

               (!w. (PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2) sv)) ==>
                    ((!n. ((P3 w n) INTER S1) = ((P1 (PATH_RESTRICT w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv)) n) INTER S1)) /\
                     (!n. ((P3 w n) INTER S2) = ((P2 (PATH_RESTRICT w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2 (\n. sv (n + DS1.SN)))) n) INTER S2))))` THEN1 (
    NTAC 2 (GSYM_NO_TAC 11) THEN
    NTAC 4 (GSYM_NO_TAC 5) THEN
    UNDISCH_NO_TAC 21 (*Element iterator*) THEN
    ASM_SIMP_TAC arith_ss [EXTENSION, IN_UNION, IN_INTER, IN_COMPL,
      IN_DIFF, IN_BETA_THM, IS_ELEMENT_ITERATOR_def,
      PATH_SUBSET_def, LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
      ltl_to_gen_buechi_ds_REWRITES, PATH_RESTRICT_def,
      PATH_MAP_def,
      LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, SUBSET_DEF] THEN
    NTAC 12 WEAKEN_HD_TAC THEN
    NTAC 3 UNDISCH_HD_TAC THEN
    REPEAT WEAKEN_HD_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_TAC `!x. ((!n. ~(n < DS1.SN) \/ ~(x = sv n)) ==>
                     ((!n. ~(n < DS1.SN + DS2.SN) \/ ~(x = sv n)) =
                      (!n. ~(n < DS2.SN) \/ ~(x = sv (n + DS1.SN))))) /\
                   ((!n. ~(n < DS2.SN) \/ ~(x = sv (n+DS1.SN))) ==>
                     ((!n. ~(n < DS1.SN + DS2.SN) \/ ~(x = sv n)) =
                      (!n. ~(n < DS1.SN) \/ ~(x = sv n))))` THEN1 (
      REPEAT STRIP_TAC THEN
        (EQ_TAC THENL [
          METIS_TAC[],

          REPEAT STRIP_TAC THEN
          RIGHT_DISJ_TAC THEN
          Cases_on `n < DS1.SN` THENL [
            METIS_TAC[],

            `(n - DS1.SN < DS2.SN) /\
            (((n - DS1.SN) + DS1.SN) = n)` by DECIDE_TAC THEN
            METIS_TAC[]
          ]
        ])
    ) THEN
    METIS_TAC[]
  ) THEN

  SUBGOAL_TAC `!w w'. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS1 i w sv /\
                      LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS2 i w'
                        (\n. sv (n + DS1.SN)) =
                      (PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv) /\
                       PATH_SUBSET w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2 (\n. sv (n + DS1.SN))) /\
                      LTL_TO_GEN_BUECHI_DS___FAIR_RUN (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2) i (\n. (w n UNION w' n)) sv)` THEN1 (
    REPEAT GEN_TAC THEN
    Q_SPECL_NO_ASSUM 1 [`w`, `w'`] THEN
    UNDISCH_HD_TAC THEN
    SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                     IS_TRANSITION_def,
                     INPUT_RUN_STATE_UNION_def,
                     INPUT_RUN_PATH_UNION_def,
                     LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                     LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
                     symbolic_semi_automaton_REWRITES,
                     ltl_to_gen_buechi_ds_REWRITES,
                     A_BIGAND___A_SEM,
                     MAP_MAP_o,
                     combinTheory.o_DEF,
                     LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                     LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
                     P_BIGAND_SEM,
                     XP_BIGAND_SEM,
                     A_BIGAND_SEM, MEM_MAP,
                     GSYM LEFT_FORALL_IMP_THM,
                     ACCEPT_COND_GF_def,
                     ACCEPT_F_def,
                     A_SEM_def, ACCEPT_COND_SEM_def,
                     ACCEPT_COND_SEM_TIME_def,
                     PATH_SUBSET_def, SUBSET_DEF, IN_UNION,
                     IN_BETA_THM
    ] THEN
    STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MATCH_MP_TAC (prove (``((X30 /\ ((X11 /\ X21) = X31)) /\
                           (((X12 /\ X22) = X32) /\ ((X13 /\ X23) = X33))) ==>
             ((((X11 /\ X12) /\ X13) /\ ((X21 /\ X22) /\ X23)) =
             ((X30 /\ (X31 /\ X32)) /\ X33))``, METIS_TAC[])) THEN
    STRIP_TAC THENL [
      REPEAT STRIP_TAC THENL [
        METIS_TAC[],
        METIS_TAC[],

        SIMP_TAC std_ss [
          prove (``!P. (!y. P y) = (!y1 y2. P (y1, y2))``, METIS_TAC[PAIR]),
          prove (``!P. (?y. P y) = (?y1 y2. P (y1, y2))``, METIS_TAC[PAIR]),
          DISJ_IMP_THM, FORALL_AND_THM,
          GSYM LEFT_FORALL_IMP_THM
        ] THEN
        UNDISCH_NO_TAC 26 (*Element Iterator*) THEN
        NTAC 4 (GSYM_NO_TAC 8) THEN (*P1, P2, P*)
        ASM_SIMP_TAC std_ss [
          P_SEM_THM, IN_UNION,
          IN_DIFF, IN_BETA_THM,
          COND_RAND,
          IS_ELEMENT_ITERATOR_def
        ] THEN
        NTAC 2 (UNDISCH_NO_TAC 6) THEN (*PATH_SUBSET w w'*)
        NTAC 3 (UNDISCH_NO_TAC 15) THEN (*< helpers*)
        UNDISCH_NO_TAC 20 THEN (*DS1.S0*)
        UNDISCH_NO_TAC 17 THEN (*DS1.S0*)
        REPEAT WEAKEN_HD_TAC THEN
        REPEAT STRIP_TAC THEN

        SIMP_TAC std_ss [GSYM FORALL_AND_THM, IMP_DISJ_THM] THEN
        NTAC 2 FORALL_EQ_STRIP_TAC THEN
        Cases_on `y2` THEN SIMP_TAC std_ss [] THEN
        BINOP_TAC THEN
        REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
      ],

      SIMP_TAC std_ss [DISJ_IMP_THM, FORALL_AND_THM,
        GSYM LEFT_FORALL_IMP_THM] THEN
      NTAC 2 UNDISCH_HD_TAC (*P_INTER*) THEN
      NTAC 4 (UNDISCH_NO_TAC 9) (*DS1.R DS.R DS.FC*) THEN
      REPEAT WEAKEN_HD_TAC THEN
      REPEAT DISCH_TAC THEN
      METIS_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM,
          P_USED_VARS_INTER_SUBSET_THM]
    ]
  ) THEN


  Q_SPEC_NO_ASSUM 18 `i` THEN
  Q_SPEC_NO_ASSUM 21 `i` THEN
  CLEAN_ASSUMPTIONS_TAC THEN
  Q_TAC EXISTS_TAC `(\n. w n UNION w' n)` THEN
  REPEAT STRIP_TAC THEN1 METIS_TAC[] THEN
  UNDISCH_HD_TAC THEN
  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
    IMP_CONJ_THM] THEN
  `PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv) /\
  PATH_SUBSET w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2 (\n. sv (n + DS1.SN)))` by METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
  Q_SPECL_NO_ASSUM 8 [`w`, `w'`] THEN
  UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_IMAGE,
      prove (``(?x. P x) = (?l b1 b2 pf. P (l,b1,b2,pf))``, METIS_TAC[PAIR])] THEN
    REPEAT STRIP_TAC THENL [
      Q_SPECL_NO_ASSUM 6 [`l`, `b1`, `b2`, `pf`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES,
        symbolic_semi_automaton_REWRITES] THEN
      STRIP_TAC THEN NTAC 2 WEAKEN_HD_TAC THEN
      `P_USED_VARS (pf sv) SUBSET S1` by METIS_TAC[] THEN
      NTAC 4 UNDISCH_HD_TAC THEN
      REPEAT WEAKEN_HD_TAC THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],


      Q_SPECL_NO_ASSUM 9 [`l`, `b1`, `b2`, `pf'`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES,
        symbolic_semi_automaton_REWRITES] THEN
      STRIP_TAC THEN NTAC 2 WEAKEN_HD_TAC THEN
      `P_USED_VARS (pf' (\n. sv (n + DS1.SN))) SUBSET S2` by METIS_TAC[] THEN
      NTAC 5 UNDISCH_HD_TAC THEN
      REPEAT WEAKEN_HD_TAC THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
    ],


    SIMP_TAC std_ss [prove (``((X ==> Y1) /\ (X ==> Y2)) = (X ==> (Y1 /\ Y2))``, METIS_TAC[]), GSYM FORALL_AND_THM] THEN
    NTAC 4 STRIP_TAC THEN
    `?v1. v1 = PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv)` by METIS_TAC[] THEN
    `?v2. v2 = PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2
                  (\n. sv (n + DS1.SN)))` by METIS_TAC[] THEN
    SUBGOAL_TAC `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS1 i v1 sv /\
                  LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS2 i v2 (\n. sv (n + DS1.SN))` THEN1 (
      Q_SPECL_NO_ASSUM 12 [`v1`, `v2`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [PATH_SUBSET_def, SIMP_RULE std_ss [] PATH_RESTRICT_SUBSET] THEN
      REMAINS_TAC `(\n.
          PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv)
            n UNION
          PATH_RESTRICT w''
            (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2
              (\n. sv (n + DS1.SN))) n) = w''` THEN1 (
        ASM_REWRITE_TAC[]
      ) THEN
      `PATH_SUBSET w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2) sv)` by
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
      UNDISCH_HD_TAC THEN
      ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
      SIMP_TAC std_ss [EXTENSION, PATH_RESTRICT_def, PATH_MAP_def,
        PATH_SUBSET_def, IN_UNION, IN_INTER,
        LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF,
        IN_BETA_THM] THEN
      REPEAT WEAKEN_HD_TAC THEN
      REPEAT STRIP_TAC THEN
      Cases_on `x' IN w'' x` THEN ASM_REWRITE_TAC[] THEN
      RES_TAC THEN
      Cases_on `n' < DS1.SN` THENL [
        PROVE_TAC[],

        DISJ2_TAC THEN
        EXISTS_TAC ``n' - DS1.SN`` THEN
        ASM_SIMP_TAC arith_ss []
      ]
    ) THEN

    `PATH_SUBSET w''
       (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS
          (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2) sv) /\
     PATH_SUBSET v1 (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS1 sv) /\
     PATH_SUBSET v2 (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS2 (\n. sv (n + DS1.SN)))` by METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
    UNDISCH_NO_TAC 8 THEN (*l, b1, b2, pf IN DS.B*)
    SIMP_TAC std_ss [IN_UNION, IN_IMAGE,
      prove (``(?x. P x) = (?l b1 b2 pf. P (l,b1,b2,pf))``, METIS_TAC[PAIR])] THEN
    STRIP_TAC THENL [
      Q_SPECL_NO_ASSUM 14 [`l`, `b1`, `b2`, `pf`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES,
        IN_UNION,
        symbolic_semi_automaton_REWRITES] THEN
      STRIP_TAC THEN
      Q_SPEC_NO_ASSUM 0 `v1` THEN
      UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN
      `P_USED_VARS (pf sv) SUBSET S1` by METIS_TAC[] THEN
      UNDISCH_HD_TAC THEN
      Q_SPEC_NO_ASSUM 18 `w''` THEN
      UNDISCH_HD_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_NO_TAC 11 (*INTER S1*) THEN
      REPEAT WEAKEN_HD_TAC THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],


      Q_SPECL_NO_ASSUM 17 [`l`, `b1`, `b2`, `pf'`] THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
        LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES,
        symbolic_semi_automaton_REWRITES] THEN
      STRIP_TAC THEN
      Q_SPEC_NO_ASSUM 0 `v2` THEN
      UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN
      `P_USED_VARS (pf' (\n. sv (n + DS1.SN))) SUBSET S2` by METIS_TAC[] THEN
      UNDISCH_HD_TAC THEN
      Q_SPEC_NO_ASSUM 19 `w''` THEN
      UNDISCH_HD_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_NO_TAC 11 (*INTER S2*) THEN
      REPEAT WEAKEN_HD_TAC THEN
      METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
    ]
  ]
]);








(* Now we have the necessary basics to start
   proving the translation *)

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP",

   ``!DS p.
        LTL_TO_GEN_BUECHI_DS___SEM DS ==>
        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_PROP p, T, T, \sv. p)} (P_USED_VARS p))``,

  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM THEN
  ASM_SIMP_TAC list_ss [LTL_USED_VARS_def, SUBSET_DEF, IN_UNION, IN_SING] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_TIME_def, LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
      LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES, P_SEM_def] THEN

  UNDISCH_NO_TAC 1 THEN UNDISCH_NO_TAC 1 THEN
  REPEAT WEAKEN_HD_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_TAC `DISJOINT (P_USED_VARS p) (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` THEN1 (
    FULL_SIMP_TAC list_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
      LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      IS_ELEMENT_ITERATOR_def, IN_UNION,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
    PROVE_TAC[]
  ) THEN

  SUBGOAL_TAC `!w t. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv ==>
                      (((w t UNION (i t DIFF  LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) INTER (P_USED_VARS p)) =
                      ((i t) INTER (P_USED_VARS p)))` THEN1 (
    UNDISCH_HD_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
      symbolic_semi_automaton_REWRITES, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, PATH_SUBSET_def, SUBSET_DEF,
      GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
    PROVE_TAC[]
  ) THEN
  METIS_TAC[P_USED_VARS_INTER_THM]
);



val LTL_TO_GEN_BUECHI_DS___BINDING_RUN_NOT =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___BINDING_RUN_NOT",

   ``!DS i w l b1 b2 pf sv.
        LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (LTL_NOT l, b1, b2, (\sv. P_NOT (pf sv))) i sv  =
        LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l, b2, b1, pf) i sv``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_THM,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_def] THEN
    METIS_TAC[]);



val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT",

   ``!b1 b2 DS l pf.
        LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, b1, b2, pf) IN DS.B ==>
        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_NOT l, b2, b1, \sv. P_NOT (pf sv))} {})``,


  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM THEN
  ASM_SIMP_TAC list_ss [UNION_EMPTY, P_USED_VARS_def, LTL_USED_VARS_def,
    LTL_TO_GEN_BUECHI_DS___BINDING_RUN_NOT, IN_SING] THEN
  PROVE_TAC[]);




val LTL_TO_GEN_BUECHI_DS___BINDING_RUN_AND =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___BINDING_RUN_AND",

   ``!DS i w b11 b12 l1 pf1 b12 b22 l2 pf2 sv.
        (LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l1, b11, b12, pf1) i sv  /\
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l2, b21, b22, pf2) i sv) ==>
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (LTL_AND(l1, l2), b11 /\ b21, b12 /\ b22, (\sv. P_AND(pf1 sv, pf2 sv))) i sv``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_THM,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_THM] THEN
    METIS_TAC[]);




val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND",

   ``!DS b11 b12 b21 b22 l1 l2 pf1 pf2.
        LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B ==>
        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_AND(l1,l2), b11 /\ b21, b12 /\ b22, \sv. P_AND (pf1 sv, pf2 sv))} {})``,

  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM THEN
  ASM_SIMP_TAC list_ss [UNION_EMPTY, P_USED_VARS_def, LTL_USED_VARS_def,
    UNION_SUBSET, IN_SING] THEN
  METIS_TAC[LTL_TO_GEN_BUECHI_DS___BINDING_RUN_AND]);


val LTL_TO_GEN_BUECHI_DS___BINDING_RUN_OR =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___BINDING_RUN_OR",

   ``!DS i w b11 b12 b21 b22 l1 pf1 l2 pf2 sv.
        (LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l1, b11, b12, pf1) i sv  /\
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l2, b21, b22, pf2) i sv) ==>
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (LTL_OR(l1, l2), b11 /\ b21, b12 /\ b22, (\sv. P_OR(pf1 sv, pf2 sv))) i sv``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_THM,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_THM] THEN
    METIS_TAC[]);


val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR",

   ``!DS b11 b12 b21 b22 l1 l2 pf1 pf2.
        LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B==>
        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_OR(l1,l2), b11 /\ b21, b12 /\ b22, \sv. P_OR (pf1 sv, pf2 sv))} {})``,

  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM THEN
  ASM_SIMP_TAC list_ss [UNION_EMPTY, P_USED_VARS_def, LTL_USED_VARS_def,
    UNION_SUBSET, P_OR_def, LTL_OR_def, IN_SING] THEN
  ASM_SIMP_TAC list_ss [GSYM P_OR_def, GSYM LTL_OR_def] THEN
  METIS_TAC[LTL_TO_GEN_BUECHI_DS___BINDING_RUN_OR]);


val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT",

   ``!b1 b2 DS DS' l pf.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [] {} [\sv. XP_EQUIV(XP_PROP (sv DS.SN), XP_NEXT (pf sv))] []
          {(LTL_NEXT l, b1, b2, \sv. P_PROP(sv DS.SN))}) ==>
        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, b1, b2, pf) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___SEM) THEN
  ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY, IMAGE_SING, BIGUNION_SING, IN_SING] THEN
  REPEAT STRIP_TAC THENL [


    `?P. (\n. LTL_SEM_TIME (SUC n) i l) = P` by METIS_TAC[] THEN
    `?w'. PATH_EXTENSION w (sv DS.SN) P = w'` by PROVE_TAC[] THEN
    `PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
    SUBGOAL_TAC `~((sv DS.SN) IN (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))` THEN1 (
      CCONTR_TAC THEN
      SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IS_ELEMENT_ITERATOR_def] THEN
      `DS.SN < DS.SN + 1 /\ n < DS.SN + 1 /\ ~(DS.SN < DS.SN)` by DECIDE_TAC THEN
      PROVE_TAC[]
    ) THEN
    EXISTS_TAC ``(w':num->'a set)`` THEN
    LEFT_CONJ_TAC THEN1 (
      PROVE_TAC [PATH_EXTENSION_EQUIV_THM]
    ) THEN


    SUBGOAL_TAC `!n w. (sv DS.SN IN INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w n =
             sv DS.SN IN w n)` THEN1 (

        SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF] THEN
        REPEAT GEN_TAC THEN
        DISJ_EQ_STRIP_TAC THEN
        SIMP_TAC std_ss [] THEN
        DISJ2_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
        EXISTS_TAC ``DS.SN`` THEN
        SIMP_TAC arith_ss []
    ) THEN


    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC list_ss [SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [P_BIGAND_def, P_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        UNDISCH_HD_TAC THEN
        SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_INSERT,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
        PROVE_TAC[],

        UNDISCH_NO_TAC 1 (*sv DS.SN IN ...*) THEN GSYM_NO_TAC 4 (*Definition P*) THEN
        `sv DS.SN IN w' n = P n` by PROVE_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        ASM_SIMP_TAC std_ss [XP_SEM_THM, XP_SEM___XP_NEXT] THEN
        DISCH_TAC THEN WEAKEN_HD_TAC THEN
        RES_TAC THEN UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def,
          INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def] THEN
        DISCH_TAC THEN WEAKEN_HD_TAC THEN

        `P_USED_VARS (pf sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
          PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN

        REMAINS_TAC `(((w (SUC n) UNION (i (SUC n) DIFF (\s. ?n. n < DS.SN /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                    (((w' (SUC n) UNION (i (SUC n) DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (
          PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN


        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        `!x n. x IN (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) n) =
          x IN (w n)` by METIS_TAC[FUN_EQ_THM, EXTENSION] THEN
        SIMP_ALL_TAC arith_ss [EXTENSION, PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
          prove (``!x f. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF]),
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY, IS_ELEMENT_ITERATOR_def, IN_INSERT] THEN
        `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
      ],


      GSYM_NO_TAC 12 (*Def. DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE, LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
        LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_def, LTL_SEM_TIME_def] THEN
      CONJ_TAC THEN1 (
        `!n. sv DS.SN IN w' n = P n` by METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        METIS_TAC[]
      ) THEN
      GEN_TAC THEN STRIP_TAC THEN

      REMAINS_TAC `!w. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS' i w sv ==>
                       (!t. (sv DS.SN IN w t) = P_SEM (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv)
                              i (PATH_RESTRICT w  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) (SUC t)) (pf sv))` THEN1 (
        `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l,b1,b2,pf) i sv` by RES_TAC THEN
        `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i (PATH_RESTRICT w''
               (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` by
         METIS_TAC[EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN, MEM] THEN
        UNDISCH_HD_TAC THEN
        FULL_SIMP_TAC std_ss [] THEN
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE]
      ) THEN


      REPEAT GEN_TAC THEN
      GSYM_NO_TAC 1 (*DS' def*) THEN
      UNDISCH_NO_TAC 3 (*sv DS.SN IN INPUT ...*) THEN
      ASM_SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        IS_TRANSITION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS_def,
        ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        XP_BIGAND_def, XP_SEM_THM, XP_SEM___XP_NEXT,
        INPUT_RUN_PATH_UNION_def] THEN

      (*Keep only PATH_SUBSET w''' STATE_VARS*)
      DISCH_TAC THEN WEAKEN_HD_TAC THEN
      STRIP_TAC THEN NTAC 3 WEAKEN_HD_TAC THEN

      SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, symbolic_semi_automaton_REWRITES,
                       PATH_RESTRICT_def, PATH_MAP_def] THEN

      REMAINS_TAC `!n. (((w''' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                    (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                   ((((w''' n INTER (\s. ?n. n < DS.SN /\ (s = sv n))) UNION (i n DIFF (\s. ?n. n < DS.SN  /\ (s = sv n)))) INTER
                    (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (
         `P_USED_VARS (pf sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
           PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN
         METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
      ) THEN

      UNDISCH_HD_TAC (*PathSUBSET*) THEN
      UNDISCH_NO_TAC 10 (*ELEMENT_ITERATOR*) THEN
      REPEAT WEAKEN_HD_TAC THEN
      SIMP_TAC arith_ss [PATH_SUBSET_def, EXTENSION, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
        LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY,
        IS_ELEMENT_ITERATOR_def,
        prove(``!f x. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF])] THEN
      `!n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
      METIS_TAC[]
    ],


    FULL_SIMP_TAC std_ss [XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
      XP_EQUIV_def, XP_IMPL_def, XP_OR_def, XP_USED_X_VARS_def,
      XP_NEXT___XP_USED_VARS, UNION_EMPTY, SUBSET_DEF, IN_UNION,
      IN_SING, P_USED_VARS_def, LTL_USED_VARS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
    `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by
        DECIDE_TAC THEN
    METIS_TAC[]
  ]);






val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT",

   ``!b1 b2 DS DS' l pf.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [(DS.SN, F)] {} [\sv. XP_EQUIV(XP_NEXT_PROP (sv DS.SN), XP_CURRENT (pf sv))] [] {
          (LTL_PSNEXT l, b1, b2, \sv. P_PROP(sv DS.SN))}) ==>
        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, b1, b2, pf) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___SEM) THEN
  ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY, IMAGE_SING, BIGUNION_SING,
    IN_SING] THEN
  REPEAT STRIP_TAC THENL [


    `?P. (\n. (n > 0) /\ LTL_SEM_TIME (PRE n) i l) = P` by METIS_TAC[] THEN
    `?w'. PATH_EXTENSION w (sv DS.SN) P = w'` by PROVE_TAC[] THEN
    `PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
    SUBGOAL_TAC `~((sv DS.SN) IN (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))` THEN1 (
      CCONTR_TAC THEN
      SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IS_ELEMENT_ITERATOR_def] THEN
      `DS.SN < DS.SN + 1 /\ n < DS.SN + 1 /\ ~(DS.SN < DS.SN)` by DECIDE_TAC THEN
      PROVE_TAC[]
    ) THEN
    EXISTS_TAC ``(w':num->'a set)`` THEN
    LEFT_CONJ_TAC THEN1 (
      PROVE_TAC [PATH_EXTENSION_EQUIV_THM]
    ) THEN


    SUBGOAL_TAC `!n w. (sv DS.SN IN INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w n =
             sv DS.SN IN w n)` THEN1 (

        SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF] THEN
        REPEAT GEN_TAC THEN
        DISJ_EQ_STRIP_TAC THEN
        SIMP_TAC std_ss [] THEN
        DISJ2_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
        EXISTS_TAC ``DS.SN`` THEN
        SIMP_TAC arith_ss []
    ) THEN


    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC list_ss [SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [P_BIGAND_def, P_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        UNDISCH_HD_TAC THEN
        SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_INSERT,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
        PROVE_TAC[],


        UNDISCH_HD_TAC THEN
        `sv DS.SN IN w' 0 = P 0` by PROVE_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        GSYM_NO_TAC 6 (*Definition P*) THEN
        ASM_SIMP_TAC arith_ss [],



        UNDISCH_NO_TAC 1 (*sv DS.SN IN ...*) THEN GSYM_NO_TAC 4 (*Definition P*) THEN
        `sv DS.SN IN w' (SUC n) = P (SUC n)` by PROVE_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        ASM_SIMP_TAC std_ss [XP_SEM_THM, XP_SEM___XP_CURRENT] THEN
        DISCH_TAC THEN WEAKEN_HD_TAC THEN
        RES_TAC THEN UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def,
          INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def] THEN
        DISCH_TAC THEN WEAKEN_HD_TAC THEN

        `P_USED_VARS (pf sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
          PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN

        REMAINS_TAC `(((w n UNION (i n DIFF (\s. ?n. n < DS.SN /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                    (((w' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (
          PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN


        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        `!x n. x IN (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) n) =
          x IN (w n)` by METIS_TAC[FUN_EQ_THM, EXTENSION] THEN
        SIMP_ALL_TAC arith_ss [EXTENSION, PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
          prove (``!x f. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF]),
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY, IS_ELEMENT_ITERATOR_def, IN_INSERT] THEN
        `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
      ],


      GSYM_NO_TAC 12 (*Def. DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE, LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
        LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_def, LTL_SEM_TIME_def] THEN
      CONJ_TAC THEN1 (
        `!n. sv DS.SN IN w' n = P n` by METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        METIS_TAC[]
      ) THEN
      GEN_TAC THEN STRIP_TAC THEN

      REMAINS_TAC `!w. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS' i w sv ==>
                       (!t. (sv DS.SN IN w t) = ((t > 0)  /\ P_SEM (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv)
                              i (PATH_RESTRICT w  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) (PRE t)) (pf sv)))` THEN1 (
        `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l,b1,b2,pf) i sv` by RES_TAC THEN

        SUBGOAL_TAC `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i (PATH_RESTRICT w''
               (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` THEN1 (
          ASSUME_TAC (SPECL [``DS:'a ltl_to_gen_buechi_ds``, ``sv:num -> 'a``, ``w'':num -> 'a set``, ``i:num -> 'a set``,
            ``DS':'a ltl_to_gen_buechi_ds``] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN) THEN
          SIMP_ALL_TAC std_ss [] THEN
          SPECL_NO_ASSUM 0 [``1:num``, ``[((DS:'a ltl_to_gen_buechi_ds).SN,F)]``] THEN
          SIMP_ALL_TAC list_ss [] THEN
          METIS_TAC[]
        ) THEN
        UNDISCH_HD_TAC THEN
        FULL_SIMP_TAC std_ss [] THEN
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE]
      ) THEN


      REPEAT GEN_TAC THEN
      GSYM_NO_TAC 1 (*DS' def*) THEN
      UNDISCH_NO_TAC 3 (*sv DS.SN IN INPUT ...*) THEN
      ASM_SIMP_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
        IS_TRANSITION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
        symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS_def,
        ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
        XP_BIGAND_def, XP_SEM_THM, XP_SEM___XP_CURRENT,
        INPUT_RUN_PATH_UNION_def, LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
        P_BIGAND_def, P_SEM_THM, FORALL_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `t` THEN (
        ASM_SIMP_TAC arith_ss []
      ) THEN

      (*Keep only PATH_SUBSET w''' STATE_VARS*)
      NTAC 5 WEAKEN_HD_TAC THEN

      SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, symbolic_semi_automaton_REWRITES,
                       PATH_RESTRICT_def, PATH_MAP_def] THEN

      REMAINS_TAC `!n. (((w''' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                    (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                   ((((w''' n INTER (\s. ?n. n < DS.SN /\ (s = sv n))) UNION (i n DIFF (\s. ?n. n < DS.SN  /\ (s = sv n)))) INTER
                    (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (
         `P_USED_VARS (pf sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
           PROVE_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN
         METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
      ) THEN

      UNDISCH_HD_TAC (*PathSUBSET*) THEN
      UNDISCH_NO_TAC 11 (*ELEMENT_ITERATOR*) THEN
      REPEAT WEAKEN_HD_TAC THEN
      SIMP_TAC arith_ss [PATH_SUBSET_def, EXTENSION, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
        LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY,
        IS_ELEMENT_ITERATOR_def,
        prove(``!f x. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF])] THEN
      `!n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
      METIS_TAC[]
    ],


    FULL_SIMP_TAC std_ss [XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
      XP_EQUIV_def, XP_IMPL_def, XP_OR_def, XP_USED_X_VARS_def,
      XP_CURRENT___XP_USED_VARS, UNION_EMPTY, SUBSET_DEF, IN_UNION,
      IN_SING, P_USED_VARS_def, LTL_USED_VARS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, NOT_IN_EMPTY,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
    `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by
        DECIDE_TAC THEN
    METIS_TAC[]
  ]);




(*before we can prove the cases of SUNTIL and PSUNTIL, we need some lemmata about
  the semantics of these operators. These are quite specialised lemmata, which are probably not
  of general interest. Therefore, they are profed here and not in ltlTheory. Moreover,
  they are not exported, because they are just of insterest to proof the cases of
  SUNTIL and PSUNTIL. The names of these lemmata go back to their number
  in the book "Verification of Reactive Systems" by Klaus Schneider,
  Springer Verlag 2004*)

val LEMMA_5_35___2 =
 prove (
   ``!w p1 p2 q. (LTL_SEM w (LTL_ALWAYS(
      LTL_EQUIV(q, LTL_OR(p2, LTL_AND(p1, LTL_NEXT q)))))) ==>

    ((LTL_SEM w (LTL_ALWAYS(LTL_IMPL(LTL_EVENTUAL(LTL_IMPL(p1, p2)), LTL_EQUIV(q, LTL_SUNTIL(p1, p2)))))))``,

   REWRITE_TAC [LTL_SEM_THM] THEN
   ASM_REWRITE_TAC[prove (``!k:num. k >= 0``, DECIDE_TAC)] THEN
   REPEAT STRIP_TAC THEN

   SUBGOAL_THEN ``?l. (l >= k /\ (LTL_SEM_TIME l w p1 ==> LTL_SEM_TIME l w p2)) /\
         !l'. (k <= l' /\ l' < l) ==> (LTL_SEM_TIME l' w p1 /\ ~LTL_SEM_TIME l' w p2)`` STRIP_ASSUME_TAC THEN1(
     ASSUME_TAC (EXISTS_LEAST_CONV ``?l. (l >= k) /\ (LTL_SEM_TIME l w p1 ==> LTL_SEM_TIME l w p2)``) THEN
     RES_TAC THEN
     EXISTS_TAC ``l:num`` THEN
     ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     `l'' >= k` by DECIDE_TAC THEN
     METIS_TAC[]
   ) THEN


   `!l'. (k <= l' /\ l' < l) ==> (LTL_SEM_TIME l' w q = LTL_SEM_TIME (SUC l') w q)` by METIS_TAC[] THEN

   SUBGOAL_THEN ``!l'. (k <= l' /\ l' <= l) ==> (LTL_SEM_TIME l' w q = LTL_SEM_TIME l w q)`` STRIP_ASSUME_TAC THEN1 (
      Induct_on `(l:num)-(l':num)` THENL [
         SIMP_TAC arith_ss [] THEN
         REPEAT STRIP_TAC THEN
         `l = l'` by DECIDE_TAC THEN
         METIS_TAC[],

         SIMP_TAC arith_ss [] THEN
         REPEAT STRIP_TAC THEN
         `v = l - SUC l'` by DECIDE_TAC THEN
         `SUC l' <= l` by DECIDE_TAC THEN
         `k <= SUC l'` by DECIDE_TAC THEN
         RES_TAC
      ]
   ) THEN

   `LTL_SEM_TIME k w q = LTL_SEM_TIME l w q` by METIS_TAC[LESS_EQ_REFL, GREATER_EQ] THEN

   Cases_on `LTL_SEM_TIME l w p2` THENL [
      METIS_TAC[],

      `~LTL_SEM_TIME l w p1` by METIS_TAC[] THEN
      `~LTL_SEM_TIME l w q` by METIS_TAC[] THEN
      `~LTL_SEM_TIME k w q` by METIS_TAC[] THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `(k'' >= k) /\ LTL_SEM_TIME k'' w p2` THENL [
         ASM_REWRITE_TAC[] THEN
         `~(k'' <= l)` by METIS_TAC[GREATER_EQ] THEN
         `l < k''` by DECIDE_TAC THEN
         METIS_TAC[GREATER_EQ],

         METIS_TAC[]
      ]
   ]);


val LEMMA_5_35___3 =
  prove(
   ``!w p1 p2 q. (LTL_SEM w (LTL_ALWAYS(
      LTL_EQUIV(q, LTL_OR(p2, LTL_AND(p1, LTL_NEXT q)))))) ==>

    ((LTL_SEM w (LTL_ALWAYS(LTL_COND(LTL_EVENTUAL(LTL_IMPL(p1, p2)),
                          LTL_PALWAYS(LTL_EQUIV(q, LTL_SUNTIL(p1, p2))),
                          LTL_OR(LTL_ALWAYS q, LTL_ALWAYS (LTL_NOT q)))))))``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [LTL_SEM_def, LTL_ALWAYS_SEM, LTL_COND_def] THEN
ONCE_REWRITE_TAC [LTL_SEM_TIME_def] THEN
REWRITE_TAC[prove (``!k:num. k >= 0``, DECIDE_TAC)] THEN
REWRITE_TAC [LTL_IMPL_SEM, LTL_PALWAYS_SEM] THEN
REPEAT STRIP_TAC THENL [
   `!l. l <= k ==> LTL_SEM_TIME l w (LTL_EVENTUAL (LTL_IMPL (p1,p2)))` by METIS_TAC[LTL_EVENTUAL___PALWAYS] THEN
   ASSUME_TAC (REWRITE_RULE [LTL_SEM_def, LTL_IMPL_SEM, LTL_ALWAYS_SEM, prove (``!k:num. k >= 0``, DECIDE_TAC)] LEMMA_5_35___2) THEN
   FULL_SIMP_TAC arith_ss [LTL_ALWAYS_SEM, LTL_SEM_def],


   SIMP_TAC std_ss [LTL_SEM_THM] THEN
   SIMP_ASSUMPTIONS_TAC std_ss [LTL_SEM_THM] THEN
   REWRITE_ASSUMPTIONS_TAC [prove (``!k:num. k >= 0``, DECIDE_TAC)] THEN
   `!k'. (k' >= k) ==> ((LTL_SEM_TIME k' w q) = (LTL_SEM_TIME (SUC k') w q))` by METIS_TAC[] THEN

   SUBGOAL_THEN ``!k'. (k' >= k) ==> ((LTL_SEM_TIME k' w q) = (LTL_SEM_TIME k w q))`` ASSUME_TAC THEN1(
      Induct_on `k' - k` THENL [
         REPEAT STRIP_TAC THEN
         `k = k'` by DECIDE_TAC THEN
         METIS_TAC[],

         REPEAT STRIP_TAC THEN
         `v = k' - SUC k` by DECIDE_TAC THEN
         `k' >= SUC k` by DECIDE_TAC THEN
         `!j l. (j >= SUC l) ==> (j >= l)` by DECIDE_TAC THEN
         `!k'. ~(k' >= SUC k) \/ LTL_SEM_TIME k' w p1 /\ ~LTL_SEM_TIME k' w p2` by METIS_TAC[] THEN
         `!k'. (k' >= SUC k) ==> (LTL_SEM_TIME k' w q = LTL_SEM_TIME (SUC k') w q)` by METIS_TAC[] THEN
         RES_TAC THEN
         `LTL_SEM_TIME k w q = LTL_SEM_TIME (SUC k) w q` by METIS_TAC[LESS_EQ_REFL, GREATER_EQ] THEN
         METIS_TAC[]
      ]
   ) THEN

   Cases_on `LTL_SEM_TIME k w q` THEN
   METIS_TAC[]
]);



val LEMMA_5_35___4 =
  prove (
    ``!w p1 p2 q. (LTL_SEM w (LTL_ALWAYS(
      LTL_EQUIV(q, LTL_OR(p2, LTL_AND(p1, LTL_NEXT q)))))) ==>

    ((LTL_SEM w (LTL_OR(LTL_ALWAYS(LTL_EQUIV(q, LTL_SUNTIL(p1, p2))),
                        LTL_ALWAYS(LTL_EQUIV(q, LTL_UNTIL(p1, p2)))))))``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [LTL_SEM_def, LTL_ALWAYS_SEM, LTL_COND_def] THEN
ONCE_REWRITE_TAC [LTL_SEM_TIME_def] THEN
REWRITE_TAC [LTL_IMPL_SEM, LTL_OR_SEM, LTL_ALWAYS_SEM] THEN
REWRITE_TAC[prove (``!k:num. k >= 0``, DECIDE_TAC)] THEN
Cases_on `!k. LTL_SEM_TIME k w (LTL_EVENTUAL(LTL_IMPL(p1, p2)))` THENL [
   ASSUME_TAC (REWRITE_RULE [LTL_SEM_def, LTL_IMPL_SEM, LTL_ALWAYS_SEM, prove (``!k:num. k >= 0``, DECIDE_TAC)] LEMMA_5_35___2) THEN
   FULL_SIMP_TAC arith_ss [LTL_ALWAYS_SEM, LTL_SEM_def],


   REPEAT STRIP_TAC THEN
   REWRITE_ALL_TAC [LTL_SEM_TIME_def, LTL_ALWAYS_SEM, prove (``!k:num. k >= 0``, DECIDE_TAC)] THEN
   FULL_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN

   SUBGOAL_THEN ``?l. ~LTL_SEM_TIME l w (LTL_EVENTUAL (LTL_IMPL (p1,p2))) /\
         !l'. l' < l ==> LTL_SEM_TIME l' w (LTL_EVENTUAL (LTL_IMPL (p1,p2)))`` STRIP_ASSUME_TAC THEN1(

      ASSUME_TAC (EXISTS_LEAST_CONV ``?k. ~LTL_SEM_TIME k w (LTL_EVENTUAL (LTL_IMPL (p1,p2)))``) THEN
      RES_TAC THEN
      EXISTS_TAC ``k':num`` THEN
      FULL_SIMP_TAC std_ss []
   ) THEN

   REWRITE_TAC[LTL_EQUIV_SEM, LTL_UNTIL_def, LTL_OR_SEM] THEN
   Cases_on `!k. LTL_SEM_TIME k w q = LTL_SEM_TIME k w (LTL_SUNTIL (p1,p2))` THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `k' < l` THENL [
      `LTL_SEM_TIME k' w (LTL_EVENTUAL (LTL_IMPL (p1,p2)))` by METIS_TAC[] THEN

      SUBGOAL_THEN ``LTL_SEM_TIME k' w (LTL_EQUIV (q,LTL_SUNTIL (p1,p2)))`` ASSUME_TAC THEN1(
         ASSUME_TAC (REWRITE_RULE [LTL_SEM_def, LTL_IMPL_SEM, LTL_ALWAYS_SEM, prove (``!k:num. k >= 0``, DECIDE_TAC)] LEMMA_5_35___2) THEN
         FULL_SIMP_TAC arith_ss [LTL_ALWAYS_SEM, LTL_SEM_def]
      ) THEN

      FULL_SIMP_TAC std_ss [LTL_EQUIV_SEM, LTL_OR_SEM, LTL_UNTIL_def] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LTL_SEM_THM] THEN
      FULL_SIMP_TAC std_ss [LTL_ALWAYS_SEM, LTL_EVENTUAL_SEM, LTL_IMPL_SEM] THEN
      EXISTS_TAC ``k''':num`` THEN
      METIS_TAC[GREATER_EQ],



      SUBGOAL_THEN ``(!l':num. l' >= l ==> LTL_SEM_TIME l' w q) \/ (!l':num. l' >= l ==> ~LTL_SEM_TIME l' w q)`` STRIP_ASSUME_TAC THEN1(
         ASSUME_TAC LEMMA_5_35___3 THEN
         REWRITE_ASSUMPTIONS_TAC [prove (``!k:num. k >= 0``, DECIDE_TAC), LTL_SEM_THM, LTL_COND_def] THEN
         SIMP_TAC std_ss [LTL_SEM_THM] THEN
         RES_TAC THENL [
            REWRITE_TAC [(ASSUME ``!k. k >= l ==> LTL_SEM_TIME k w q``)],
            REWRITE_TAC [(ASSUME ``!k. k >= l ==> LTL_SEM_TIME k w q``)],
            REWRITE_TAC [(ASSUME ``!k. k >= l ==> ~LTL_SEM_TIME k w q``)],
            REWRITE_TAC [(ASSUME ``!k. k >= l ==> ~LTL_SEM_TIME k w q``)]
         ]
      ) THENL [
         `k' >= l` by DECIDE_TAC THEN
         FULL_SIMP_TAC std_ss [LTL_SEM_THM, LTL_UNTIL_def] THEN
         DISJ2_TAC THEN
         REPEAT STRIP_TAC THEN
         `k''' >= l` by DECIDE_TAC THEN
         METIS_TAC[],

         `k' >= l` by DECIDE_TAC THEN
         ASM_SIMP_TAC std_ss [] THEN
         STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [LTL_SEM_THM, LTL_UNTIL_def] THEN
            REPEAT STRIP_TAC THEN
            Cases_on `(k''' >= k') /\ LTL_SEM_TIME k''' w p2` THENL [
               CLEAN_ASSUMPTIONS_TAC THEN
               ASM_REWRITE_TAC[] THEN
               `k''' >= 0` by DECIDE_TAC THEN
               `k''' >= l` by DECIDE_TAC THEN
               METIS_TAC[],

               METIS_TAC[]
            ],


            FULL_SIMP_TAC arith_ss [] THEN
            Cases_on `k'' >= l` THENL [
               FULL_SIMP_TAC std_ss [LTL_SEM_THM] THEN
               `k''' >= l` by DECIDE_TAC THEN
               METIS_TAC[],



               `k'' < l` by DECIDE_TAC THEN
               `LTL_SEM_TIME k'' w (LTL_EVENTUAL (LTL_IMPL (p1,p2)))` by METIS_TAC[] THEN

               SUBGOAL_THEN ``LTL_SEM_TIME k'' w (LTL_EQUIV (q,LTL_SUNTIL (p1,p2)))`` ASSUME_TAC THEN1(
                  ASSUME_TAC (REWRITE_RULE [LTL_SEM_def, LTL_IMPL_SEM, LTL_ALWAYS_SEM, prove (``!k:num. k >= 0``, DECIDE_TAC)] LEMMA_5_35___2) THEN
                  FULL_SIMP_TAC arith_ss [LTL_ALWAYS_SEM, LTL_SEM_def]
               ) THEN

               FULL_SIMP_TAC std_ss [LTL_EQUIV_SEM]
           ]
        ]
     ]
   ]
]);


val LTL_UNTIL_SUNTIL_CONDITION =
  prove (
    ``!w p1 p2 q.

    ((LTL_SEM w (LTL_ALWAYS(LTL_EQUIV(q, LTL_UNTIL(p1, p2))))) /\
     (LTL_SEM w (LTL_ALWAYS(LTL_EVENTUAL(LTL_IMPL(q, p2)))))) ==>

     (LTL_SEM w (LTL_ALWAYS(LTL_EQUIV(q, LTL_SUNTIL(p1, p2)))))``,


   FULL_SIMP_TAC std_ss [LTL_UNTIL_def, LTL_SEM_THM] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[],

      ASM_SIMP_TAC std_ss [GREATER_EQ] THEN
      `!l l' l''. l >= l' /\ l' >= l'' ==> l >= l''` by DECIDE_TAC THEN
      `!k'. k' >= k ==> LTL_SEM_TIME k' w q` by METIS_TAC[] THEN
      `?l. l >= k /\ (LTL_SEM_TIME l w q ==> LTL_SEM_TIME l w p2)` by METIS_TAC[] THEN
      EXISTS_TAC ``l:num`` THEN
      METIS_TAC [GREATER_EQ],

      METIS_TAC[]
   ]);



val LEMMA_5_36___PSUNTIL =
  prove (
    ``!w p1 p2 q.

     (LTL_SEM w (LTL_ALWAYS(LTL_EQUIV(q, LTL_OR(p2, LTL_AND(p1, LTL_PSNEXT q)))))) =
     (LTL_SEM w (LTL_ALWAYS(LTL_EQUIV(q, LTL_PSUNTIL(p1, p2)))))``,


   SIMP_TAC std_ss [LTL_SEM_THM] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL [
      REPEAT DISCH_TAC THEN
      Induct_on `k` THENL [
         ONCE_ASM_REWRITE_TAC [] THEN
         SIMP_TAC arith_ss [],

         ONCE_ASM_REWRITE_TAC [] THEN
         SIMP_TAC arith_ss [] THEN
         ONCE_ASM_REWRITE_TAC[] THEN
         EQ_TAC THEN REPEAT STRIP_TAC THENL [
            EXISTS_TAC ``SUC k`` THEN
            ASM_SIMP_TAC arith_ss [],

            EXISTS_TAC ``k':num`` THEN
            ASM_SIMP_TAC arith_ss [] THEN
            REPEAT STRIP_TAC THEN
            Cases_on `j <= k` THENL [
               METIS_TAC[],

               `j = SUC k` by DECIDE_TAC THEN
               METIS_TAC[]
            ],

            Cases_on `k' = SUC k` THENL [
               METIS_TAC[],

               DISJ2_TAC THEN
               REPEAT STRIP_TAC THENL [
                  `k' < SUC k /\ SUC k <= SUC k` by DECIDE_TAC THEN
                  METIS_TAC[],

                  EXISTS_TAC ``k':num`` THEN
                  `k' <= k /\ !j. j <= k ==> j <= SUC k` by DECIDE_TAC THEN
                  METIS_TAC[]
               ]
            ]
         ]
      ],

      REPEAT STRIP_TAC THEN
      Cases_on `k` THENL [
         ASM_SIMP_TAC arith_ss [],

         ASM_SIMP_TAC arith_ss [] THEN
         EQ_TAC THEN REPEAT STRIP_TAC THENL [
            Cases_on `k = SUC n` THENL [
               METIS_TAC[],

               DISJ2_TAC THEN
               REPEAT STRIP_TAC THENL [
                  `k < SUC n /\ SUC n <= SUC n` by DECIDE_TAC THEN
                  METIS_TAC[],

                  EXISTS_TAC ``k:num`` THEN
                  `k <= n /\ !j. j <= n ==> j <= SUC n` by DECIDE_TAC THEN
                  METIS_TAC[]
               ]
            ],

            EXISTS_TAC ``SUC n`` THEN
            ASM_SIMP_TAC arith_ss [],


            EXISTS_TAC ``k:num`` THEN
            ASM_SIMP_TAC arith_ss [] THEN
            REPEAT STRIP_TAC THEN
            Cases_on `j <= n` THENL [
               METIS_TAC[],

               `j = SUC n` by DECIDE_TAC THEN
               METIS_TAC[]
            ]
         ]
      ]
   ]);


(*now we can prove the lemma for SUNTIL*)
val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL",

   ``!b11 b12 b21 b22 a DS DS' l1 l2 pf1 pf2.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [] {}
               [\sv. XP_EQUIV(XP_PROP (sv DS.SN), XP_OR(XP_CURRENT (pf2 sv),
                                                        XP_AND(
                                                          XP_CURRENT (pf1 sv),
                                                          XP_NEXT_PROP (sv DS.SN))))]
               (if (b11 /\ b21 /\ a) then [\sv. P_IMPL(P_PROP(sv DS.SN), pf2 sv)] else [])
               {(LTL_SUNTIL(l1, l2), b11 /\ b21 /\ a, b12 /\ b22, \sv. P_PROP(sv DS.SN))}) ==>

        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___SEM) THEN
  ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY,
    IN_SING, IMAGE_SING, BIGUNION_SING] THEN
  REPEAT STRIP_TAC THENL [


    `?P. (\n. LTL_SEM_TIME n (INPUT_RUN_PATH_UNION
         (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w)
                   (LTL_SUNTIL(LTL_PROP (pf1 sv), LTL_PROP (pf2 sv)))) = P` by METIS_TAC [] THEN
    `?w'. PATH_EXTENSION w (sv DS.SN) P = w'` by PROVE_TAC[] THEN


    `PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN

    SUBGOAL_TAC `~((sv DS.SN) IN (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))` THEN1 (
      CCONTR_TAC THEN
      SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IS_ELEMENT_ITERATOR_def] THEN
      `DS.SN < DS.SN + 1 /\ n < DS.SN + 1 /\ ~(DS.SN < DS.SN)` by DECIDE_TAC THEN
      PROVE_TAC[]
    ) THEN
    EXISTS_TAC ``(w':num->'a set)`` THEN
    LEFT_CONJ_TAC THEN1 (
      METIS_TAC [PATH_EXTENSION_EQUIV_THM]
    ) THEN


    (*some usefull lemmata*)
    `P_USED_VARS (pf1 sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV /\
      P_USED_VARS (pf2 sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN
    SUBGOAL_TAC `!n. ((((w n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                  (((w' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))))` THEN1 (
        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        `!x n. x IN (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) n) =
          x IN (w n)` by METIS_TAC[FUN_EQ_THM, EXTENSION] THEN
        SIMP_ALL_TAC arith_ss [EXTENSION, PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
          prove (``!x f. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF]),
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY, IS_ELEMENT_ITERATOR_def, IN_INSERT] THEN
        `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT GEN_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
    ) THEN

    `!n. sv DS.SN IN w' n = P n` by METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
    SUBGOAL_TAC `!n w'. sv DS.SN IN INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w' n =
                  sv DS.SN IN w' n` THEN1 (
      REPEAT GEN_TAC THEN
      SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF] THEN
      DISJ_EQ_STRIP_TAC THEN
      SIMP_TAC std_ss [] THEN
      DISJ2_TAC THEN
      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
        symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
      EXISTS_TAC ``DS.SN`` THEN
      SIMP_TAC arith_ss []
    ) THEN


    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC list_ss [SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
      GSYM_NO_TAC 5 (*w = PATH_RESTRICT w'*) THEN
      ASM_SIMP_TAC std_ss [P_BIGAND_def, P_SEM_def] THEN
      REPEAT STRIP_TAC THENL [

        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        UNDISCH_HD_TAC THEN
        REPEAT WEAKEN_HD_TAC THEN
        SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_INSERT,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
        PROVE_TAC[],




        UNDISCH_NO_TAC 1 (*sv DS.SN IN_INPUT_RUN_...*) THEN
        ASM_SIMP_TAC std_ss [XP_SEM_THM, INPUT_RUN_PATH_UNION_def, XP_SEM___XP_CURRENT, INPUT_RUN_STATE_UNION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def] THEN
        GSYM_NO_TAC 8 (*Definition P*) THEN
        ASM_SIMP_TAC std_ss [] THEN
        SUBGOAL_TAC `!w. (LTL_SEM_TIME n w
                          (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))) =
                    P_SEM (w n) (pf2 sv) \/
                    (P_SEM (w n) (pf1 sv) /\
                      (LTL_SEM_TIME (SUC n) w
                      (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))))` THEN1 (
          REPEAT WEAKEN_HD_TAC THEN
          GEN_TAC THEN
          ASSUME_TAC (SPECL [``LTL_PROP ((pf1:(num->'a)->'a prop_logic) sv)``,
                            ``LTL_PROP ((pf2:(num->'a)->'a prop_logic) sv)``]
                                LTL_RECURSION_LAWS___LTL_SUNTIL) THEN
          SIMP_ALL_TAC std_ss [LTL_SEM_THM, LTL_EQUIVALENT_def] THEN
          SPECL_NO_ASSUM 0 [``n:num``] THEN
          ASM_REWRITE_TAC[]
        ) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          ltl_to_gen_buechi_ds_REWRITES, symbolic_semi_automaton_REWRITES,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        METIS_TAC[P_USED_VARS_INTER_SUBSET_THM],


        Cases_on `b11 /\ b21 /\ a` THEN (
          CLEAN_ASSUMPTIONS_TAC THEN
          FULL_SIMP_TAC list_ss []
        ) THEN
        UNDISCH_NO_TAC 5 (*sv DS.SN IN ...*) THEN
        ASM_SIMP_TAC std_ss [A_SEM_def, ACCEPT_COND_GF_def,
          ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
          ACCEPT_F_def, P_SEM_THM] THEN
        REPEAT STRIP_TAC THEN
        GSYM_NO_TAC 13 (*Definition of P*) THEN
        ASM_SIMP_TAC std_ss [LTL_SEM_TIME_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          ltl_to_gen_buechi_ds_REWRITES, symbolic_semi_automaton_REWRITES,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        Cases_on `?t''. t'' >= t' /\ P_SEM
            (w' t'' UNION (i t'' DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) (pf2 sv)` THENL [
            METIS_TAC[],

            SIMP_ASSUMPTIONS_TAC std_ss [] THEN
            EXISTS_TAC ``t':num`` THEN
            ASM_SIMP_TAC arith_ss [] THEN
            METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ]
      ],


      GSYM_NO_TAC 17 (*Def. DS'*) THEN
      GSYM_NO_TAC 11 (*Definition of P*) THEN
      GSYM_NO_TAC 8 (*w = PATH_RESTRICT ...*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        P_SEM_def] THEN

      (*Usefull lemmata*)
      `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l1,b11,b12,pf1) i sv /\
       LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l2,b21,b22,pf2) i sv` by
        (RES_TAC THEN ASM_REWRITE_TAC[]) THEN

      CONJ_TAC THENL [
        GEN_TAC THEN
        ASM_SIMP_TAC std_ss [P_SEM_def, LTL_SEM_TIME_def] THEN
        NTAC 2 UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE] THEN
        REPEAT (DISCH_TAC THEN WEAKEN_HD_TAC) THEN
        EXISTS_EQ_STRIP_TAC THEN
        REMAINS_TAC `!n. ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w n)
                          INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                          ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w n)
                          INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))` THEN1 (
          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN
        GSYM_NO_TAC 2 (*Definition DS'*) THEN
        UNDISCH_NO_TAC 14 (*Iterator*) THEN
        UNDISCH_NO_TAC 10 (*Path Subset*) THEN
        ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
          EXTENSION, IN_UNION, IN_INTER, IN_DIFF, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, PATH_SUBSET_def, SUBSET_DEF,
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
          IS_ELEMENT_ITERATOR_def] THEN
        REPEAT WEAKEN_HD_TAC THEN
        `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[],

        GEN_TAC THEN STRIP_TAC THEN
        SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
        GEN_TAC THEN
        REMAINS_TAC ` ((b11 /\ b21 /\ a) /\ sv DS.SN IN w'' t ==>
          LTL_SEM_TIME t
            (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv)
                i (PATH_RESTRICT w''  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))) (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))) /\
          ((b12 /\ b22) /\
          LTL_SEM_TIME t
            (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv)
                i (PATH_RESTRICT w''  (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))) (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv))) ==>
          sv DS.SN IN w'' t)` THEN1 (

          NTAC 2 UNDISCH_HD_TAC THEN
          ASM_SIMP_TAC std_ss [P_SEM_def, LTL_SEM_THM, LTL_UNTIL_def] THEN
          SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE] THEN
          SUBGOAL_TAC `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i  (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` THEN1 (
            UNDISCH_NO_TAC 0 THEN UNDISCH_NO_TAC 18 THEN
            UNDISCH_NO_TAC 6 THEN UNDISCH_NO_TAC 19 THEN
            REPEAT WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [] THEN
            REPEAT STRIP_TAC THEN
            ASSUME_TAC (SPECL [``DS:'a ltl_to_gen_buechi_ds``, ``sv:num -> 'a``, ``w'':num -> 'a set``, ``i:num -> 'a set``,
              ``DS':'a ltl_to_gen_buechi_ds``] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN) THEN
            SIMP_ALL_TAC std_ss [] THEN
            SPECL_NO_ASSUM 0 [``1:num``, ``[]:(num # bool) list``] THEN
            SIMP_ALL_TAC list_ss [] THEN
            METIS_TAC[]
          ) THEN


          REMAINS_TAC `!n w. LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i w sv ==>
                          (((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w n)
                          INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                          ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w n)
                          INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (


            (*Cleaning up*)
            NTAC 2 UNDISCH_HD_TAC (*current FairRun Stuff*) THEN
            UNDISCH_NO_TAC 18 (*w Fair run*) THEN
            UNDISCH_NO_TAC 4 (*Binding-Run pf2*) THEN
            UNDISCH_NO_TAC 2 (*Binding-Run pf1*) THEN
            NTAC 2 (UNDISCH_NO_TAC 10) (*P_USED_VARS pf1 pf2*) THEN
            SIMP_TAC std_ss [] THEN
            REPEAT WEAKEN_HD_TAC THEN
            METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
          ) THEN
          UNDISCH_NO_TAC 20 (*Iterator*) THEN
          GSYM_NO_TAC 8 (*DEF DS'*) THEN
          ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
            LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
            EXTENSION, IN_UNION, IN_INTER, IN_DIFF, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
            LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, PATH_SUBSET_def, SUBSET_DEF,
            LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
            IS_ELEMENT_ITERATOR_def, LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
            IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
          REPEAT WEAKEN_HD_TAC THEN
          REPEAT STRIP_TAC THEN
          `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
          REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
          METIS_TAC[]
        ) THEN

        `?q. q = LTL_PROP (P_PROP (sv DS.SN))` by METIS_TAC[] THEN
        `?v. v = (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w'')` by METIS_TAC[] THEN

        SUBGOAL_TAC `(sv DS.SN IN w'' t = LTL_SEM_TIME t v q) /\
                      (LTL_SEM v (LTL_ALWAYS(LTL_EQUIV(q, LTL_OR(LTL_PROP (pf2 sv), LTL_AND(LTL_PROP (pf1 sv), LTL_NEXT q)))))) /\
                      (b11 /\ b21 /\ a ==> (LTL_SEM v (LTL_ALWAYS(LTL_EVENTUAL(LTL_IMPL(q, LTL_PROP (pf2 sv)))))))` THEN1 (
            (*Cleaning up*)
            NTAC 3 UNDISCH_HD_TAC THEN
            UNDISCH_NO_TAC 6 (*sv DS.SN IN ...*) THEN
            GSYM_NO_TAC 4 (*Definition D'*) THEN
            ASM_REWRITE_TAC[] THEN
            REPEAT WEAKEN_HD_TAC THEN
            REPEAT DISCH_TAC THEN
            ASM_REWRITE_TAC[] THEN

            SIMP_ALL_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
              IS_TRANSITION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
              symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
              XP_BIGAND_def, XP_SEM_THM, LTL_SEM_THM, P_SEM_THM,
              INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
              LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, XP_SEM___XP_CURRENT,
              FORALL_AND_THM, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def] THEN
            UNDISCH_NO_TAC 4 THEN
            ONCE_ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THENL [
              REWRITE_TAC[],
              METIS_TAC[],

              WEAKEN_NO_TAC 3 THEN
              FULL_SIMP_TAC list_ss [A_BIGAND_def, A_SEM_THM,
                ACCEPT_COND_GF_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def,
                ACCEPT_F_def, P_SEM_THM] THEN
              METIS_TAC[]
            ]
        ) THEN

        SUBGOAL_TAC `(LTL_SEM_TIME t (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv)
                i (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)))
                (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv))) =
                LTL_SEM_TIME t v (LTL_SUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))) /\
                (LTL_SEM_TIME t (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv)
                i (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)))
                (LTL_UNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv))) =
                LTL_SEM_TIME t v (LTL_UNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv))))` THEN1 (
          SUBGOAL_TAC `!n. ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w'' n)
                            INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                            ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i
                              (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) n)
                            INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))` THEN1 (
            GSYM_NO_TAC 10 (*Definition DS'*) THEN
            UNDISCH_NO_TAC 22 (*Iterator*) THEN
            `PATH_SUBSET w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS' sv)` by
              METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
            UNDISCH_HD_TAC THEN
            ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
              LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
              EXTENSION, IN_UNION, IN_INTER, IN_DIFF, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
              LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, PATH_SUBSET_def, SUBSET_DEF,
              LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
              IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def] THEN
            REPEAT WEAKEN_HD_TAC THEN
            `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
            REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
            METIS_TAC[]
          ) THEN
          ASM_SIMP_TAC std_ss [LTL_SEM_THM, LTL_UNTIL_def] THEN
          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN


        (*Cleaning up*)
        GSYM_NO_TAC 6 (*Definition q*) THEN
        GSYM_NO_TAC 6 (*Definition v*) THEN
        ASM_REWRITE_TAC[] THEN
        NTAC 2 UNDISCH_HD_TAC THEN
        NTAC 2 WEAKEN_HD_TAC THEN
        NTAC 3 UNDISCH_HD_TAC THEN
        REPEAT WEAKEN_HD_TAC THEN
        REPEAT DISCH_TAC THEN
        (*continuing proof*)
        `LTL_SEM v (LTL_OR(LTL_ALWAYS(LTL_EQUIV(q, LTL_SUNTIL(LTL_PROP (pf1 sv), LTL_PROP (pf2 sv)))),
                                LTL_ALWAYS(LTL_EQUIV(q, LTL_UNTIL(LTL_PROP (pf1 sv), LTL_PROP (pf2 sv))))))` by
          METIS_TAC[LEMMA_5_35___4] THEN UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [LTL_SEM_def, LTL_OR_SEM, LTL_ALWAYS_SEM, LTL_EQUIV_SEM] THEN
        REPEAT STRIP_TAC THENL [
          METIS_TAC[],
          METIS_TAC[],

          ASSUME_TAC LTL_UNTIL_SUNTIL_CONDITION THEN
          FULL_SIMP_TAC std_ss [LTL_SEM_def, LTL_ALWAYS_SEM, LTL_EQUIV_SEM] THEN
          SPECL_NO_ASSUM 0 [``v:num->'a set``, ``LTL_PROP ((pf1:(num->'a)->'a prop_logic) sv)``,
            ``LTL_PROP ((pf2:(num->'a)->'a prop_logic) sv)``, ``q:'a ltl``] THEN
          METIS_TAC[],

          ASM_SIMP_TAC std_ss [LTL_UNTIL_def, LTL_OR_SEM]
        ]
      ]
    ],

    Q.ABBREV_TAC `a' = b11 /\ b21 /\ a` THEN
    Cases_on `a'` THEN
    FULL_SIMP_TAC list_ss [XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
      XP_EQUIV_def, XP_IMPL_def, XP_OR_def, XP_USED_X_VARS_def,
      XP_CURRENT___XP_USED_VARS, UNION_EMPTY, SUBSET_DEF, IN_UNION,
      IN_SING, P_USED_VARS_def, LTL_USED_VARS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, NOT_IN_EMPTY,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, LIST_BIGUNION_def,
      P_USED_VARS_def, P_IMPL_def, P_OR_def] THEN
    `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by
        DECIDE_TAC THEN
    METIS_TAC[]
  ]);





val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL",

   ``!b11 b12 b21 b22 DS DS' l1 l2 pf1 pf2.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [(DS.SN, F)] {}
               [\sv. XP_EQUIV(XP_NEXT_PROP (sv DS.SN), XP_OR(XP_CURRENT (pf2 sv),
                                                        XP_AND(
                                                          XP_CURRENT (pf1 sv),
                                                          XP_PROP (sv DS.SN))))]
               []
               {(LTL_PSUNTIL(l1, l2), b11 /\ b21, b12 /\ b22, \sv. (P_OR(pf2 sv, P_AND(pf1 sv, P_PROP(sv DS.SN)))))}) ==>

        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___SEM) THEN
  ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY, IN_SING, IMAGE_SING, BIGUNION_SING] THEN
  REPEAT STRIP_TAC THENL [


    `?P. (\n. n > 0 /\ LTL_SEM_TIME (PRE n) (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w)
                   (LTL_PSUNTIL(LTL_PROP (pf1 sv), LTL_PROP (pf2 sv)))) = P` by METIS_TAC [] THEN
    `?w'. PATH_EXTENSION w (sv DS.SN) P = w'` by PROVE_TAC[] THEN


    `PATH_SUBSET w (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
        METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN

    SUBGOAL_TAC `~((sv DS.SN) IN (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv))` THEN1 (
      CCONTR_TAC THEN
      SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
        LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
        EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IS_ELEMENT_ITERATOR_def] THEN
      `DS.SN < DS.SN + 1 /\ n < DS.SN + 1 /\ ~(DS.SN < DS.SN)` by DECIDE_TAC THEN
      PROVE_TAC[]
    ) THEN
    EXISTS_TAC ``(w':num->'a set)`` THEN
    LEFT_CONJ_TAC THEN1 (
      METIS_TAC [PATH_EXTENSION_EQUIV_THM]
    ) THEN


    (*some usefull lemmata*)
    `P_USED_VARS (pf1 sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV /\
      P_USED_VARS (pf2 sv) SUBSET LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___USED_BINDING_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR] THEN

    `!n. sv DS.SN IN w' n = P n` by METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
    SUBGOAL_TAC `!n w'. sv DS.SN IN INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w' n =
                  sv DS.SN IN w' n` THEN1 (
      REPEAT GEN_TAC THEN
      SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IN_UNION, IN_DIFF] THEN
      DISJ_EQ_STRIP_TAC THEN
      SIMP_TAC std_ss [] THEN
      DISJ2_TAC THEN
      SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
        symbolic_semi_automaton_REWRITES, LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS] THEN
      EXISTS_TAC ``DS.SN`` THEN
      SIMP_TAC arith_ss []
    ) THEN


    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC list_ss [SIMP_RULE std_ss [] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN] THEN
      GSYM_NO_TAC 4 (*w = PATH_RESTRICT w'*) THEN
      ASM_SIMP_TAC std_ss [P_BIGAND_def, P_SEM_def] THEN
      REPEAT STRIP_TAC THENL [

        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        UNDISCH_HD_TAC THEN
        REPEAT WEAKEN_HD_TAC THEN
        SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_INSERT,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
        `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
        PROVE_TAC[],


        UNDISCH_HD_TAC THEN
        GSYM_NO_TAC 8 (*Definition P*) THEN
        ASM_SIMP_TAC arith_ss [],




        UNDISCH_NO_TAC 1 (*sv DS.SN IN_INPUT_RUN_...*) THEN
        ASM_SIMP_TAC std_ss [XP_SEM_THM, INPUT_RUN_PATH_UNION_def, XP_SEM___XP_CURRENT, INPUT_RUN_STATE_UNION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def] THEN
        GSYM_NO_TAC 7 (*Definition P*) THEN
        ASM_SIMP_TAC std_ss [] THEN
        SUBGOAL_TAC `!w. (LTL_SEM_TIME n w
                          (LTL_PSUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))) =
                    P_SEM (w n) (pf2 sv) \/
                    (P_SEM (w n) (pf1 sv) /\
                      n > 0 /\
                      (LTL_SEM_TIME (PRE n) w
                      (LTL_PSUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv)))))` THEN1 (
          REPEAT WEAKEN_HD_TAC THEN
          GEN_TAC THEN
          ASSUME_TAC (SPECL [``LTL_PROP ((pf1:(num->'a)->'a prop_logic) sv)``,
                            ``LTL_PROP ((pf2:(num->'a)->'a prop_logic) sv)``]
                                LTL_RECURSION_LAWS___LTL_PSUNTIL) THEN
          SIMP_ALL_TAC std_ss [LTL_SEM_THM, LTL_EQUIVALENT_def] THEN
          SPECL_NO_ASSUM 0 [``n:num``] THEN
          ASM_REWRITE_TAC[]
        ) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          ltl_to_gen_buechi_ds_REWRITES, symbolic_semi_automaton_REWRITES,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN

        REMAINS_TAC `!n. ((((w n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                      (((w' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))))` THEN1 (

          (*Keep only the new proposition and P_USED_VARS pf1, pf2 SUBSET ....*)
          REPEAT (DISCH_TAC THEN WEAKEN_HD_TAC) THEN
          UNDISCH_HD_TAC THEN
          NTAC 4 WEAKEN_HD_TAC THEN
          NTAC 2 UNDISCH_HD_TAC THEN
          REPEAT WEAKEN_HD_TAC THEN
          REPEAT STRIP_TAC THEN

          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN
        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        `!x n. x IN (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) n) =
          x IN (w n)` by METIS_TAC[FUN_EQ_THM, EXTENSION] THEN
        SIMP_ALL_TAC arith_ss [EXTENSION, PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
          prove (``!x f. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF]),
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY, IS_ELEMENT_ITERATOR_def, IN_INSERT] THEN
        `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT GEN_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
      ],


      GSYM_NO_TAC 16 (*Def. DS'*) THEN
      GSYM_NO_TAC 10 (*Definition of P*) THEN
      GSYM_NO_TAC 7 (*w = PATH_RESTRICT ...*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE,
        P_SEM_THM] THEN

      (*Usefull lemmata*)
      `LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l1,b11,b12,pf1) i sv /\
        LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l2,b21,b22,pf2) i sv` by
        (RES_TAC THEN ASM_REWRITE_TAC[]) THEN

      CONJ_TAC THENL [
        GEN_TAC THEN
        ASSUME_TAC (SPECL [``l1:'a ltl``, ``l2:'a ltl``, ``t:num``]
          (REWRITE_RULE [LTL_EQUIVALENT_def] LTL_RECURSION_LAWS___LTL_PSUNTIL)) THEN
        ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN
        NTAC 2 UNDISCH_HD_TAC THEN
        GSYM_NO_TAC 2 (*Definition DS'*) THEN
        SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_THM] THEN
        REPEAT (DISCH_TAC THEN WEAKEN_HD_TAC) THEN
        ASM_SIMP_TAC std_ss [
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
          INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          symbolic_semi_automaton_REWRITES] THEN

        REMAINS_TAC `!n. ((((w n UNION (i n DIFF (\s. ?n. n < DS.SN /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                      (((w' n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))) /\

                      ((((w n UNION (i n DIFF (\s. ?n. n < DS.SN /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) =
                      (((w n UNION (i n DIFF (\s. ?n. n < DS.SN + 1 /\ (s = sv n)))) INTER
                      (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))))` THEN1 (

          (*Keep only the new proposition and P_USED_VARS pf1, pf2 SUBSET ....*)
          UNDISCH_HD_TAC THEN
          NTAC 6 WEAKEN_HD_TAC THEN
          NTAC 2 UNDISCH_HD_TAC THEN
          REPEAT WEAKEN_HD_TAC THEN
          REPEAT STRIP_TAC THEN

          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN

        `PATH_SUBSET w' ((sv DS.SN) INSERT LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)` by
          METIS_TAC[PATH_EXTENSION_EQUIV_THM] THEN
        `!x n. x IN (PATH_RESTRICT w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv) n) =
          x IN (w n)` by METIS_TAC[FUN_EQ_THM, EXTENSION] THEN
        SIMP_ALL_TAC arith_ss [EXTENSION, PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_INTER, IN_DIFF,
          LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS,
          prove (``!x f. x IN (\x. f x) = f x``, SIMP_TAC std_ss [IN_DEF]),
          LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, PATH_RESTRICT_def, PATH_MAP_def,
          EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_EMPTY, IS_ELEMENT_ITERATOR_def, IN_INSERT] THEN
        `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by DECIDE_TAC THEN
        REPEAT GEN_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[],




        GEN_TAC THEN DISCH_TAC THEN
        SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN GEN_TAC THEN
        REMAINS_TAC `!t. ((sv DS.SN IN w'' t) = (t > 0) /\ LTL_SEM_TIME (PRE t)
                          (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv)
                              i w'')
                          (LTL_PSUNTIL (LTL_PROP (pf1 sv),LTL_PROP (pf2 sv))))` THEN1 (


          UNDISCH_HD_TAC THEN
          ASM_SIMP_TAC std_ss [P_SEM_def, LTL_SEM_THM] THEN
          SIMP_ALL_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN___REWRITE] THEN
          SUBGOAL_TAC `LTL_TO_GEN_BUECHI_DS___FAIR_RUN DS i  (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) sv` THEN1 (
            UNDISCH_NO_TAC 0 THEN UNDISCH_NO_TAC 17 THEN
            UNDISCH_NO_TAC 6 THEN UNDISCH_NO_TAC 18 THEN
            REPEAT WEAKEN_HD_TAC THEN
            SIMP_TAC std_ss [] THEN
            REPEAT STRIP_TAC THEN
            ASSUME_TAC (SPECL [``DS:'a ltl_to_gen_buechi_ds``, ``sv:num -> 'a``, ``w'':num -> 'a set``, ``i:num -> 'a set``,
              ``DS':'a ltl_to_gen_buechi_ds``] EXTEND_LTL_TO_GEN_BUECHI_DS___FAIR_RUN) THEN
            SIMP_ALL_TAC std_ss [] THEN
            SPECL_NO_ASSUM 0 [``1:num``, ``[((DS:'a ltl_to_gen_buechi_ds).SN, F)]``] THEN
            SIMP_ALL_TAC list_ss [] THEN
            METIS_TAC[]
          ) THEN


          DISCH_TAC THEN WEAKEN_HD_TAC THEN
          SUBGOAL_TAC `!n. (((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w' n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                           ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) /\

                           (((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                           ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i w n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV))) /\

                           (((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS sv) i
                              (PATH_RESTRICT w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv)) n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)) =
                           ((INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w'' n)
                           INTER (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS sv UNION DS.IV)))` THEN1 (

            UNDISCH_NO_TAC 19 (*Iterator*) THEN
            UNDISCH_NO_TAC 15 (*PATH_SUBSET w*) THEN
            GSYM_NO_TAC 8 (*DEF DS'*) THEN
            UNDISCH_NO_TAC 7 (*PATH_RESTRICT w' = w*) THEN
            `PATH_SUBSET w' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS' sv)`
              by METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
            `PATH_SUBSET w'' (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS DS' sv)`
              by METIS_TAC[LTL_TO_GEN_BUECHI_DS___FAIR_RUN___PATH_SUBSET] THEN
            NTAC 2 UNDISCH_HD_TAC THEN

            SIMP_TAC std_ss [EXTENSION] THEN
            ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
            ASM_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
              LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
              EXTENSION, IN_UNION, IN_INTER, IN_DIFF, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
              LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, PATH_SUBSET_def, SUBSET_DEF,
              LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def, UNION_EMPTY,
              IS_ELEMENT_ITERATOR_def, LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def,
              PATH_RESTRICT_def, PATH_MAP_def, PATH_SUBSET_def] THEN
            REPEAT WEAKEN_HD_TAC THEN
            REPEAT STRIP_TAC THEN
            `DS.SN < DS.SN + 1 /\ !n. n < DS.SN ==> n < DS.SN + 1` by DECIDE_TAC THEN
            REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
            METIS_TAC[]
          ) THEN


          (*Cleaning up*)
          SPECL_NO_ASSUM 4 [``PATH_RESTRICT (w'':num->'a set) (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (DS:'a ltl_to_gen_buechi_ds) sv)``] THEN
          SPECL_NO_ASSUM 6 [``PATH_RESTRICT (w'':num->'a set) (LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS (DS:'a ltl_to_gen_buechi_ds) sv)``] THEN
          NTAC 4 UNDISCH_HD_TAC (*path constraints*) THEN
          NTAC 2 (UNDISCH_NO_TAC 9) (*P_USED_VARS pf1 pf2*) THEN
          REPEAT WEAKEN_HD_TAC THEN
          REPEAT STRIP_TAC THEN
          METIS_TAC[P_USED_VARS_INTER_SUBSET_THM]
        ) THEN


        `?q. q = LTL_NEXT(LTL_PROP (P_PROP (sv DS.SN)))` by METIS_TAC[] THEN
        `?v. v = (INPUT_RUN_PATH_UNION (LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON DS' sv) i w'')` by METIS_TAC[] THEN


        REMAINS_TAC `(!t. (sv DS.SN IN w'' t = (t > 0 /\ LTL_SEM_TIME (PRE t) v q))) /\
                     (LTL_SEM v (LTL_ALWAYS(LTL_EQUIV(q, LTL_OR(LTL_PROP (pf2 sv), LTL_AND(LTL_PROP (pf1 sv), LTL_PSNEXT q))))))` THEN1 (

            SIMP_ALL_TAC std_ss [LEMMA_5_36___PSUNTIL] THEN
            UNDISCH_HD_TAC THEN
            ASM_SIMP_TAC arith_ss [LTL_SEM_THM]
        ) THEN

        (*Cleaning up*)
        NTAC 3 UNDISCH_HD_TAC THEN
        UNDISCH_NO_TAC 6 (*sv DS.SN IN ...*) THEN
        GSYM_NO_TAC 4 (*Definition D'*) THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT WEAKEN_HD_TAC THEN
        REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC[] THEN

        SIMP_ALL_TAC list_ss [LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
          IS_TRANSITION_def, LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
          symbolic_semi_automaton_REWRITES, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
          XP_BIGAND_def, XP_SEM_THM, LTL_SEM_THM, P_SEM_THM,
          INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
          LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def, XP_SEM___XP_CURRENT,
          FORALL_AND_THM, LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
          LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def, P_BIGAND_def] THEN
        UNDISCH_NO_TAC 3 THEN
        UNDISCH_NO_TAC 4 THEN
        ONCE_ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THENL [
          Cases_on `t` THEN
          ASM_SIMP_TAC arith_ss [],

          Cases_on `k` THENL [
            ASM_REWRITE_TAC[] THEN
            SIMP_TAC arith_ss [],

            SIMP_TAC arith_ss [] THEN
            METIS_TAC[]
          ]
        ]
      ]
    ],


    FULL_SIMP_TAC list_ss [XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
      XP_EQUIV_def, XP_IMPL_def, XP_OR_def, XP_USED_X_VARS_def,
      XP_CURRENT___XP_USED_VARS, UNION_EMPTY, SUBSET_DEF, IN_UNION,
      IN_SING, P_USED_VARS_def, LTL_USED_VARS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, NOT_IN_EMPTY,
      LTL_TO_GEN_BUECHI_DS___IN_USED_STATE_VARS, LIST_BIGUNION_def,
      P_USED_VARS_def, P_IMPL_def, P_OR_def] THEN
    `(!n. n < DS.SN ==> n < DS.SN + 1) /\ DS.SN < DS.SN + 1` by
        DECIDE_TAC THEN
    METIS_TAC[]
  ]);




val LTL_TO_GEN_BUECHI___EXTEND_def =
 Define
  `(LTL_TO_GEN_BUECHI___EXTEND (LTL_PROP p) b1 b2 DS = ((\sv:num->'a. p:'a prop_logic),
    (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_PROP p, b1, b2, \sv. p)} (P_USED_VARS p)))) /\

   (LTL_TO_GEN_BUECHI___EXTEND (LTL_NOT l) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l b2 b1 DS))
    in
    ((\sv. P_NOT (pf1' sv)),
     EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS1' {(LTL_NOT l, b1, b2, \sv. P_NOT (pf1' sv))} {}))) /\

   (LTL_TO_GEN_BUECHI___EXTEND (LTL_AND (l1, l2)) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l1 b1 b2 DS))
    in
    (let
     ((pf2', DS2') = (LTL_TO_GEN_BUECHI___EXTEND l2 b1 b2 DS1'))
     in
    ((\sv. P_AND (pf1' sv, pf2' sv)),
     EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS2' {(LTL_AND(l1,l2), b1, b2, \sv. P_AND (pf1' sv, pf2' sv))} {})))) /\


   (LTL_TO_GEN_BUECHI___EXTEND (LTL_NEXT l) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l b1 b2 DS))
    in
    ((\sv. P_PROP (sv DS1'.SN)),
      EXTEND_LTL_TO_GEN_BUECHI_DS DS1' 1 [] {} [\sv. XP_EQUIV(XP_PROP (sv DS1'.SN), XP_NEXT (pf1' sv))] [] {
          (LTL_NEXT l, b1, b2, \sv. P_PROP(sv DS1'.SN))}))) /\

   (LTL_TO_GEN_BUECHI___EXTEND (LTL_PSNEXT l) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l b1 b2 DS))
    in
    ((\sv. P_PROP (sv DS1'.SN)),
      EXTEND_LTL_TO_GEN_BUECHI_DS DS1' 1 [(DS1'.SN, F)] {} [\sv. XP_EQUIV(XP_NEXT_PROP (sv DS1'.SN), XP_CURRENT (pf1' sv))] [] {
          (LTL_PSNEXT l, b1, b2, \sv. P_PROP(sv DS1'.SN))}))) /\


   (LTL_TO_GEN_BUECHI___EXTEND (LTL_SUNTIL (l1, l2)) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l1 b1 b2 DS))
    in
    (let
     ((pf2', DS2') = (LTL_TO_GEN_BUECHI___EXTEND l2 b1 b2 DS1'))
     in
    ((\sv:num->'a. P_PROP (sv DS2'.SN)),
      EXTEND_LTL_TO_GEN_BUECHI_DS (DS2':'a ltl_to_gen_buechi_ds) 1 [] {}
               [\sv:num->'a. XP_EQUIV(XP_PROP (sv DS2'.SN), XP_OR(XP_CURRENT (pf2' sv),
                                                        XP_AND(
                                                          XP_CURRENT (pf1' sv),
                                                          XP_NEXT_PROP (sv DS2'.SN))))]
               (if b1 then [\sv. P_IMPL(P_PROP(sv DS2'.SN), pf2' sv)] else [])
               {(LTL_SUNTIL(l1, l2), b1, b2, \sv. P_PROP(sv DS2'.SN))})))) /\


   (LTL_TO_GEN_BUECHI___EXTEND (LTL_PSUNTIL (l1, l2)) b1 b2 DS = (let
     ((pf1', DS1') = (LTL_TO_GEN_BUECHI___EXTEND l1 b1 b2 DS))
    in
    (let
     ((pf2', DS2') = (LTL_TO_GEN_BUECHI___EXTEND l2 b1 b2 DS1'))
     in
    ((\sv. (P_OR(pf2' sv, P_AND(pf1' sv, P_PROP(sv DS2'.SN))))),
    EXTEND_LTL_TO_GEN_BUECHI_DS DS2' 1 [(DS2'.SN, F)] {}
               [\sv. XP_EQUIV(XP_NEXT_PROP (sv DS2'.SN), XP_OR(XP_CURRENT (pf2' sv),
                                                        XP_AND(
                                                          XP_CURRENT (pf1' sv),
                                                          XP_PROP (sv DS2'.SN))))]
               []
               {(LTL_PSUNTIL(l1, l2), b1, b2, \sv. (P_OR(pf2' sv, P_AND(pf1' sv, P_PROP(sv DS2'.SN)))))}))))`;



val LTL_TO_GEN_BUECHI_def =
 Define
  `LTL_TO_GEN_BUECHI l b1 b2 = LTL_TO_GEN_BUECHI___EXTEND l b1 b2 (EMPTY_LTL_TO_GEN_BUECHI_DS)`;




val LTL_TO_GEN_BUECHI___EXTEND___THM =
 store_thm
  ("LTL_TO_GEN_BUECHI___EXTEND___THM",

``!l b1 b2 DS DS' pf. ((pf, DS') = LTL_TO_GEN_BUECHI___EXTEND l b1 b2 DS) ==> (
  ((l, b1, b2, pf) IN DS'.B /\ (DS.B SUBSET DS'.B) /\
  (LTL_TO_GEN_BUECHI_DS___SEM DS ==> LTL_TO_GEN_BUECHI_DS___SEM DS')))``,



ONCE_REWRITE_TAC[GSYM PAIR] THEN
REWRITE_TAC[PAIR_EQ] THEN
INDUCT_THEN ltl_induct ASSUME_TAC THENL [
  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def,
    EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, IN_UNION, IN_SING,
    SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN
  METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___WEAKEN_BINDING, CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP,
  EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def],


  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],

    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],

    REWRITE_TAC [GSYM EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def] THEN
    `?y. (x = (~y)) /\ ((~x) = y)` by METIS_TAC[] THEN
    ASM_SIMP_TAC std_ss [] THEN
    METIS_TAC[CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT]
  ],


  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],

    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],

    SIMP_ALL_TAC std_ss [GSYM EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND THEN
    Q_SPECL_NO_ASSUM 0 [`SND (LTL_TO_GEN_BUECHI___EXTEND l' b1 b2
               (SND (LTL_TO_GEN_BUECHI___EXTEND l b1 b2 DS)))`, `b1`, `b2`, `b1`, `b2`] THEN
    METIS_TAC[SUBSET_DEF]
  ],



  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],
    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],
    METIS_TAC[CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT]
  ],


  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],
    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],

    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `b1`, `b2`, `b1`] THEN

    Cases_on `b1` THEN (
      SIMP_ALL_TAC std_ss [SUBSET_DEF] THEN
      METIS_TAC[]
    )
  ],


  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],
    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],
    METIS_TAC[CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT, SUBSET_DEF]
  ],


  SIMP_TAC list_ss [LTL_TO_GEN_BUECHI___EXTEND_def, LET_THM, PAIR_BETA_THM,
    EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [IN_UNION, IN_SING],
    PROVE_TAC[SUBSET_UNION, SUBSET_TRANS],

    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `b1`, `b2`] THEN
    METIS_TAC[SUBSET_DEF]
  ]
]);




val LTL_TO_GEN_BUECHI_THM =
 store_thm
  ("LTL_TO_GEN_BUECHI_THM",

``!l b1 b2. LTL_TO_GEN_BUECHI_DS___SEM (SND (LTL_TO_GEN_BUECHI l b1 b2)) /\
        (l, b1, b2, FST (LTL_TO_GEN_BUECHI l b1 b2)) IN (SND (LTL_TO_GEN_BUECHI l b1 b2)).B``,

  REPEAT GEN_TAC THEN
  REWRITE_TAC[LTL_TO_GEN_BUECHI_def] THEN
  ASSUME_TAC (SPECL [``l:'a ltl``, ``b1:bool``, ``b2:bool``, ``EMPTY_LTL_TO_GEN_BUECHI_DS:'a ltl_to_gen_buechi_ds``] LTL_TO_GEN_BUECHI___EXTEND___THM) THEN
  UNDISCH_HD_TAC THEN
  ONCE_REWRITE_TAC[GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  SIMP_TAC std_ss [] THEN
  METIS_TAC[EMPTY_LTL_TO_GEN_BUECHI_DS___SEM]);



val LTL_TO_GEN_BUECHI___EXTEND___IS_LTL_G_F =
 store_thm
  ("LTL_TO_GEN_BUECHI___EXTEND___IS_LTL_G_F",

``!l DS. (IS_LTL_G l ==> ((SND (LTL_TO_GEN_BUECHI___EXTEND l T F DS)).FC = DS.FC)) /\
         (IS_LTL_F l ==> ((SND (LTL_TO_GEN_BUECHI___EXTEND l F T DS)).FC = DS.FC))``,

  INDUCT_THEN ltl_induct ASSUME_TAC THEN (
    ASM_SIMP_TAC list_ss [IS_LTL_G_def, LTL_TO_GEN_BUECHI___EXTEND_def,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def, LET_THM, PAIR_BETA_THM,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, ltl_to_gen_buechi_ds_REWRITES]
  ));


val LTL_TO_GEN_BUECHI___IS_LTL_G_F =
 store_thm
  ("LTL_TO_GEN_BUECHI___IS_LTL_G_F",

``!l. (IS_LTL_G l ==> ((SND (LTL_TO_GEN_BUECHI l T F)).FC = [])) /\
      (IS_LTL_F l ==> ((SND (LTL_TO_GEN_BUECHI l F T)).FC = []))``,

  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_def, LTL_TO_GEN_BUECHI___EXTEND___IS_LTL_G_F,
    EMPTY_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES]);



val LTL_TO_GEN_BUECHI___EXTEND___USED_INPUT_VARS =
 store_thm
  ("LTL_TO_GEN_BUECHI___EXTEND___USED_INPUT_VARS",

``!l b1 b2 DS. (SND (LTL_TO_GEN_BUECHI___EXTEND l b1 b2 DS)).IV = (LTL_USED_VARS l) UNION DS.IV``,

  INDUCT_THEN ltl_induct ASSUME_TAC THEN (
    ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI___EXTEND_def,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def, LET_THM, PAIR_BETA_THM,
      EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, ltl_to_gen_buechi_ds_REWRITES,
      LTL_USED_VARS_def, NOT_IN_EMPTY, EXTENSION, IN_UNION] THEN
    REPEAT GEN_TAC THEN REPEAT BOOL_EQ_STRIP_TAC
  ));


val LTL_TO_GEN_BUECHI___USED_INPUT_VARS =
 store_thm
  ("LTL_TO_GEN_BUECHI___USED_INPUT_VARS",

``!l b1 b2. (SND (LTL_TO_GEN_BUECHI l b1 b2)).IV = (LTL_USED_VARS l)``,

  SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_def, LTL_TO_GEN_BUECHI___EXTEND___USED_INPUT_VARS,
    EMPTY_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES, UNION_EMPTY]);




(*Derived construction rules for operators defined as
  syntactic sugar*)


val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE",

   ``!b11 b12 b21 b22 a DS DS' l1 l2 pf1 pf2.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [] {}
               [\sv. XP_EQUIV(XP_PROP (sv DS.SN), XP_OR(XP_CURRENT (pf2 sv),
                                                        XP_AND(
                                                          XP_CURRENT (P_NOT (pf1 sv)),
                                                          XP_NEXT_PROP (sv DS.SN))))]
               (if ~(b12 /\ b21 /\ a) then [] else [\sv. P_IMPL(P_PROP(sv DS.SN), pf2 sv)])
               {(LTL_BEFORE(l1, l2), b11 /\ b22, b12 /\ b21 /\ a, \sv. P_NOT (P_PROP(sv DS.SN)))}) ==>

        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

    REWRITE_TAC [LTL_BEFORE_def] THEN
    REPEAT STRIP_TAC THEN

    (*Negation of l1*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b11`, `b12`, `DS`, `l1`, `pf1`] THEN
    UNDISCH_HD_TAC THEN
    `?DS1. (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS
         {(LTL_NOT l1,b12, b11,(\sv. P_NOT (pf1 sv)))} {}) = DS1` by METIS_TAC[] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_NOT l1, b12, b11, (\sv. P_NOT (pf1 sv))) IN DS1.B /\
                 (l2,b21,b22,pf2) IN DS1.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN


    (*SUNTIL*)
    ASSUME_TAC (SIMP_RULE std_ss [] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL) THEN
    Q_SPECL_NO_ASSUM 0 [`b12`,`b11`,`b21`, `b22`, `a`, `DS1`, `LTL_NOT l1`, `l2`, `(\sv. P_NOT (pf1 sv))`, `pf2`] THEN
    UNDISCH_HD_TAC THEN
    `?DS2. (EXTEND_LTL_TO_GEN_BUECHI_DS DS1 1 [] {}
          [(\sv.
              XP_EQUIV
                (XP_PROP (sv DS1.SN),
                 XP_OR
                   (XP_CURRENT (pf2 sv),
                    XP_AND
                      (XP_CURRENT ((\sv. P_NOT (pf1 sv)) sv),
                       XP_NEXT_PROP (sv DS1.SN)))))]
          (if b12 /\ b21 /\ a then [(\sv. P_IMPL (P_PROP (sv DS1.SN),pf2 sv))] else [])
          {(LTL_SUNTIL (LTL_NOT l1,l2),b12 /\ b21 /\ a, b11 /\ b22,(\sv. P_PROP (sv DS1.SN)))}) = DS2` by METIS_TAC[] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_SUNTIL (LTL_NOT l1,l2), b12 /\ b21 /\ a, b11 /\ b22, (\sv. P_PROP (sv DS1.SN))) IN DS2.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN
    `?pf. pf = (\(sv :num -> 'a).
               P_PROP (sv (DS1 :'a ltl_to_gen_buechi_ds).SN))` by METIS_TAC[] THEN

    (*NOT*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b12 /\ b21 /\ a`, `b11 /\ b22`, `DS2`, `LTL_SUNTIL (LTL_NOT l1,l2)`, `pf`] THEN
    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN
    GSYM_NO_TAC 3 (*Def DS2*) THEN
    GSYM_NO_TAC 7 (*Def DS1*) THEN
    FULL_SIMP_TAC std_ss [] THEN
    REPEAT WEAKEN_HD_TAC THEN

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___EXTEND_LTL_TO_GEN_BUECHI_DS,
      UNION_EMPTY, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_SING] THEN

    (*REMOVE UNNECESSARY BINDINGS*)
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, SUBSET_DEF, IN_UNION,
      IN_SING, IN_INSERT, DISJ_IMP_THM] THEN
    METIS_TAC[]);




val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE",

   ``!b11 b12 b21 b22 DS DS' l1 l2 pf1 pf2.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [(DS.SN,F)] {}
               [\sv. XP_EQUIV(XP_NEXT_PROP (sv DS.SN), XP_OR(XP_CURRENT (pf2 sv),
                                                        XP_AND(
                                                          XP_CURRENT (P_NOT (pf1 sv)),
                                                          XP_PROP (sv DS.SN))))]
               []
               {(LTL_PBEFORE(l1, l2), b11 /\ b22, b12 /\ b21, (\sv.
              P_NOT
                (P_OR (pf2 sv,P_AND (P_NOT (pf1 sv),P_PROP (sv DS.SN))))))}) ==>

        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, b11, b12, pf1) IN DS.B /\ (l2, b21, b22, pf2) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

    REWRITE_TAC [LTL_PBEFORE_def] THEN
    REPEAT STRIP_TAC THEN

    (*Negation of l1*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b11`, `b12`, `DS`, `l1`, `pf1`] THEN
    UNDISCH_HD_TAC THEN
    `?DS1. (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS
         {(LTL_NOT l1,b12, b11,(\sv. P_NOT (pf1 sv)))} {}) = DS1` by METIS_TAC[] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_NOT l1, b12, b11, (\sv. P_NOT (pf1 sv))) IN DS1.B /\
                 (l2,b21,b22,pf2) IN DS1.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN


    (*PSUNTIL*)
    ASSUME_TAC (SIMP_RULE std_ss [] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL) THEN
    Q_SPECL_NO_ASSUM 0 [`b12`, `b11`, `b21`, `b22`, `DS1`, `LTL_NOT l1`, `l2`, `(\sv. P_NOT (pf1 sv))`, `pf2`] THEN
    UNDISCH_HD_TAC THEN
    `?DS2. (EXTEND_LTL_TO_GEN_BUECHI_DS DS1 1 [(DS1.SN,F)] {}
          [(\sv.
              XP_EQUIV
                (XP_NEXT_PROP (sv DS1.SN),
                 XP_OR
                   (XP_CURRENT (pf2 sv),
                    XP_AND
                      (XP_CURRENT ((\sv. P_NOT (pf1 sv)) sv),
                       XP_PROP (sv DS1.SN)))))]
          []
          {(LTL_PSUNTIL (LTL_NOT l1,l2),b12 /\ b21,b11 /\ b22,(\sv. P_OR(pf2 sv, P_AND(P_NOT (pf1 sv), P_PROP (sv DS1.SN)))))}) = DS2` by METIS_TAC[] THEN
    FULL_SIMP_TAC std_ss [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_PSUNTIL (LTL_NOT l1,l2),b12 /\ b21, b11 /\ b22, (\sv.
                 P_OR
                   (pf2 sv,P_AND (P_NOT (pf1 sv),P_PROP (sv DS1.SN))))) IN DS2.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN
    `?pf. pf = (\(sv:num -> 'a).
                 P_OR
                   (pf2 sv,P_AND (P_NOT (pf1 sv),P_PROP (sv (DS1:'a ltl_to_gen_buechi_ds).SN))))` by METIS_TAC[] THEN

    (*NOT*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b12 /\ b21`, `b11 /\ b22`, `DS2`, `LTL_PSUNTIL (LTL_NOT l1,l2)`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    GSYM_NO_TAC 3 (*Def DS2*) THEN
    GSYM_NO_TAC 7 (*Def DS1*) THEN
    FULL_SIMP_TAC std_ss [] THEN
    REPEAT WEAKEN_HD_TAC THEN

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___EXTEND_LTL_TO_GEN_BUECHI_DS,
      UNION_EMPTY, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_SING] THEN

    (*REMOVE UNNECESSARY BINDINGS*)
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, SUBSET_DEF, IN_UNION,
      IN_SING, IN_INSERT, DISJ_IMP_THM]);




val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT",

   ``!b1 b2 DS DS' l pf.
        (DS' = EXTEND_LTL_TO_GEN_BUECHI_DS DS 1 [(DS.SN,F)] {}
               [(\sv. XP_EQUIV
                  (XP_NEXT_PROP (sv DS.SN),XP_CURRENT (P_NOT (pf sv))))] []
               {(LTL_PNEXT l, b1, b2, (\sv. P_NOT (P_PROP (sv DS.SN))))}) ==>

        ((LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l, b1, b2, pf) IN DS.B) ==>
        LTL_TO_GEN_BUECHI_DS___SEM DS')``,

    REWRITE_TAC [LTL_PNEXT_def] THEN
    REPEAT STRIP_TAC THEN

    (*Negation of l*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `DS`, `l`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    `?DS1. (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS
         {(LTL_NOT l,b2,b1,(\sv. P_NOT (pf sv)))} {}) = DS1` by METIS_TAC[] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_NOT l, b2,b1, (\sv. P_NOT (pf sv))) IN DS1.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN


    (*PSNEXT*)
    ASSUME_TAC (SIMP_RULE std_ss [] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT) THEN
    Q_SPECL_NO_ASSUM 0 [`b2`,`b1`, `DS1`, `LTL_NOT l`, `(\sv. P_NOT (pf sv))`] THEN
    UNDISCH_HD_TAC THEN
    `?DS2. (EXTEND_LTL_TO_GEN_BUECHI_DS DS1 1 [(DS1.SN,F)] {}
          [(\sv.
              XP_EQUIV
                (XP_NEXT_PROP (sv DS1.SN),
                XP_CURRENT ((\sv. P_NOT (pf sv)) sv)))]
          []
          {(LTL_PSNEXT (LTL_NOT l),b2,b1,(\sv. P_PROP (sv DS1.SN)))}) = DS2` by METIS_TAC[] THEN
    FULL_SIMP_TAC std_ss [] THEN STRIP_TAC THEN
    SUBGOAL_TAC `(LTL_PSNEXT (LTL_NOT l),b2,b1, (\sv.
                   P_PROP (sv DS1.SN))) IN DS2.B` THEN1 (
      GSYM_NO_TAC 1 THEN
      ASM_SIMP_TAC std_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES,
        IN_UNION, IN_SING]
    ) THEN
    `?pf2. pf2 = (\(sv:num -> 'a).
                 P_PROP (sv (DS1:'a ltl_to_gen_buechi_ds).SN))` by METIS_TAC[] THEN

    (*NOT*)
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT THEN
    Q_SPECL_NO_ASSUM 0 [`b2`,`b1`, `DS2`, `LTL_PSNEXT (LTL_NOT l)`, `pf2`] THEN
    UNDISCH_HD_TAC THEN
    GSYM_NO_TAC 3 (*Def DS2*) THEN
    GSYM_NO_TAC 6 (*Def DS1*) THEN
    FULL_SIMP_TAC std_ss [] THEN
    REPEAT WEAKEN_HD_TAC THEN

    SIMP_TAC list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS___EXTEND_LTL_TO_GEN_BUECHI_DS,
      UNION_EMPTY, EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, UNION_SING] THEN

    (*REMOVE UNNECESSARY BINDINGS*)
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS___REWRITES, SUBSET_DEF, IN_UNION,
      IN_SING, IN_INSERT, DISJ_IMP_THM]);





val LTL_TO_GEN_BUECHI_DS___BINDING_RUN_EQUIV =
 store_thm
  ("LTL_TO_GEN_BUECHI_DS___BINDING_RUN_EQUIV",

   ``!DS i w l1 pf1 l2 pf2 sv.
        (LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l1, T, T, pf1) i sv  /\
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (l2, T, T, pf2) i sv) ==>
         LTL_TO_GEN_BUECHI_DS___BINDING_RUN DS w (LTL_EQUIV(l1, l2), T, T, (\sv. P_EQUIV(pf1 sv, pf2 sv))) i sv``,

    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def, LTL_SEM_THM,
      LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def,
      LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def, P_SEM_THM] THEN
    METIS_TAC[]);


val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV =
 store_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV",

   ``!DS l1 l2 pf1 pf2.
        LTL_TO_GEN_BUECHI_DS___SEM DS /\ (l1, T, T, pf1) IN DS.B /\ (l2, T, T, pf2) IN DS.B==>
        LTL_TO_GEN_BUECHI_DS___SEM (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS {(LTL_EQUIV(l1,l2), T, T, \sv. P_EQUIV (pf1 sv, pf2 sv))} {})``,

  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS___SEM THEN
  ASM_SIMP_TAC list_ss [UNION_EMPTY, P_USED_VARS_EVAL, LTL_USED_VARS_EVAL,
    UNION_SUBSET, IN_SING] THEN
  METIS_TAC[LTL_TO_GEN_BUECHI_DS___BINDING_RUN_EQUIV]);


val _ = export_theory();

