(* ACL2 model (/examples/acl2/acl2-new-partial/tests/gold) *)

quietdec := true;
load "sexpTheory";
open sexpTheory;

load "LTLTheory";
open LTLTheory;

open pred_setTheory;

load "load_book";
open load_book;

load "imported_acl2Theory";
open imported_acl2Theory;
quietdec := false;

(*****************************************************************************)
(* Start new theory "main"                                                   *)
(*****************************************************************************)

val _ = new_theory "main";

val HOL_MODEL_def =
 Define
  `HOL_MODEL sexp_model =
    <| S  := \s.     |= memberp s (g (ksym "STATES") sexp_model);
       S0 := \s.     |= memberp s (g (ksym "INITIAL-STATES") sexp_model);
       R  := \(p,q). |= (next_statep p q sexp_model);
       L  := \s a.   |= memberp a (label_of s sexp_model)
    |> : (sexp,sexp)model`;

val CIRC_TO_MODEL_def =
 Define
  `CIRC_TO_MODEL C = HOL_MODEL (create_kripke C)`;

val initial_state_is_state_thm = get_acl2_thm "initial_state_is_state";
val range_transition_relation_thm = get_acl2_thm "range_transition_relation";

val ModelSanity =
 store_thm
  ("ModelSanity",
   ``!m. (|= circuit_modelp m) ==> MODEL(HOL_MODEL m)``,
   RW_TAC std_ss 
    [MODEL_def,HOL_MODEL_def,SPECIFICATION,SUBSET_DEF,
     initial_state_is_state_thm,range_transition_relation_thm]
    THEN METIS_TAC[range_transition_relation_thm]);

val cone_of_influence_reduction_is_circuit_p_thm = 
 get_acl2_thm "cone_of_influence_reduction_is_circuit_p";

val create_kripke_produces_circuit_model_thm =
 get_acl2_thm "create_kripke_produces_circuit_model";

val CircuitModels =
 store_thm
  ("CircuitModels",
   ``!C Vars. (|= circuitp C)
              ==>
              (|= (circuit_modelp (create_kripke C))) /\
              (|= (circuit_modelp
                   (create_kripke (cone_of_influence_reduction C vars)))) /\
              MODEL (CIRC_TO_MODEL C) /\
              MODEL (CIRC_TO_MODEL (cone_of_influence_reduction C vars))``,
   METIS_TAC
     [MODEL_def,HOL_MODEL_def,SPECIFICATION,SUBSET_DEF,CIRC_TO_MODEL_def,
      ModelSanity,
      cone_of_influence_reduction_is_circuit_p_thm,
      create_kripke_produces_circuit_model_thm]);

(* Convert sexp list to set *)
val SexpToSet_def =
 Define
  `SexpToSet lst =
    \x. |= memberp x lst`;

val cone_of_influence_is_c_bisimi_equiv_thm =
 get_acl2_thm "cone_of_influence_is_c_bisimi_equiv";

val c_bisimilar_equiv_implies_init_greater_init_m_greater_n_thm =
 get_acl2_thm "c_bisimilar_equiv_implies_init_greater_init_m_greater_n";

val c_bisimilar_equiv_implies_init_greater_init_n_greater_m_thm =
 get_acl2_thm "c_bisimilar_equiv_implies_init_greater_init_n_greater_m";

val c_bisimilar_equiv_implies_bisimilar_initial_states_m_greater_n_thm =
 get_acl2_thm "c_bisimilar_equiv_implies_bisimilar_initial_states_m_greater_n";

val c_bisimilar_equiv_implies_bisimilar_initial_states_n_greater_m_thm =
 get_acl2_thm "c_bisimilar_equiv_implies_bisimilar_initial_states_n_greater_m";

val bisim_lemma_1_thm =
 get_acl2_thm "bisim_lemma_1";

val c_bisimilar_witness_member_of_states_m_greater_n_thm =
 get_acl2_thm "c_bisimilar_witness_member_of_states_m_greater_n";

val c_bisimilar_witness_matches_transition_m_greater_n_thm =
 get_acl2_thm "c_bisimilar_witness_matches_transition_m_greater_n";

val c_bisimilar_witness_produces_bisimilar_states_m_greater_n_thm =
 get_acl2_thm "c_bisimilar_witness_produces_bisimilar_states_m_greater_n";

val c_bisimilar_witness_member_of_states_n_greater_m_thm =
 get_acl2_thm "c_bisimilar_witness_member_of_states_n_greater_m";

val c_bisimilar_witness_matches_transition_n_greater_m_thm =
 get_acl2_thm "c_bisimilar_witness_matches_transition_n_greater_m";

val c_bisimilar_witness_produces_bisimilar_states_n_greater_m_thm =
 get_acl2_thm "c_bisimilar_witness_produces_bisimilar_states_n_greater_m";

(* Bisimulation Lemma *)
val BisimLemma =
 time store_thm
  ("BisimLemma",
   ``!m1 m2 Vars. (|= circuit_modelp m1) /\
                  (|= circuit_modelp m2) /\
                  (|= (c_bisim_equiv m1 m2 Vars))
                  ==>
                  BISIM_EQ (HOL_MODEL m1) (HOL_MODEL m2) (SexpToSet Vars)``,
   RW_TAC std_ss [BISIM_EQ_def, SPECIFICATION]
    THEN Q.EXISTS_TAC `\(s,s'). (|= circuit_bisim s m1 s' m2 Vars)`
    THEN RW_TAC std_ss [] (* beta reduce *)
    THENL
     [RW_TAC (srw_ss())
             [HOL_MODEL_def, BISIM_def, SPECIFICATION, SexpToSet_def]
       THENL
        [METIS_TAC
          [bisim_lemma_1_thm,SPECIFICATION,equal_imp],
         METIS_TAC
          [c_bisimilar_witness_member_of_states_m_greater_n_thm,
           c_bisimilar_witness_matches_transition_m_greater_n_thm,
           c_bisimilar_witness_produces_bisimilar_states_m_greater_n_thm],
         METIS_TAC
          [c_bisimilar_witness_member_of_states_n_greater_m_thm,
           c_bisimilar_witness_matches_transition_n_greater_m_thm,
           c_bisimilar_witness_produces_bisimilar_states_n_greater_m_thm]],
      Q.EXISTS_TAC
       `c_bisimilar_initial_state_witness_m_greater_n s0 m1 m2 Vars`
       THEN FULL_SIMP_TAC (srw_ss()) [HOL_MODEL_def]
       THEN METIS_TAC
             [c_bisimilar_equiv_implies_init_greater_init_m_greater_n_thm,
	      c_bisimilar_equiv_implies_bisimilar_initial_states_m_greater_n_thm],
      Q.EXISTS_TAC
       `c_bisimilar_initial_state_witness_n_greater_m m1 s0' m2 Vars`
       THEN FULL_SIMP_TAC (srw_ss()) [HOL_MODEL_def]
       THEN METIS_TAC
             [c_bisimilar_equiv_implies_init_greater_init_n_greater_m_thm,
	      c_bisimilar_equiv_implies_bisimilar_initial_states_n_greater_m_thm]]);

(* Key Lemma *)
val Key =
 time store_thm
  ("Key",
   ``!C Vars. (|= circuitp C)
              ==>
              BISIM_EQ (CIRC_TO_MODEL C)
                       (CIRC_TO_MODEL (cone_of_influence_reduction C Vars))
                       (SexpToSet (cone_variables Vars C))``,
   METIS_TAC
     [cone_of_influence_is_c_bisimi_equiv_thm,
      CircuitModels,
      CIRC_TO_MODEL_def,
      BisimLemma]);

val subset_implies_memberp_thm =
  get_acl2_thm "subset_implies_memberp";

val subset_implies_SUBSET =
 time store_thm
  ("subset_implies_SUBSET",
   ``!x y. (|= subset x y) ==> ((SexpToSet x) SUBSET (SexpToSet y))``,
   METIS_TAC
    [SUBSET_DEF, SexpToSet_def, SPECIFICATION, subset_implies_memberp_thm]);

val Main =
 time store_thm
  ("Main",
   ``!C Vars.
      (|= circuitp C)
      ==>
      !f. (Atoms f) SUBSET (SexpToSet (cone_variables Vars C))
          ==>
          (SAT (CIRC_TO_MODEL C) f =
           SAT (CIRC_TO_MODEL (cone_of_influence_reduction C Vars)) f)``,
   METIS_TAC [Key, Theorem1, CircuitModels]);

show_tags := true;

val MainCorollary =
 time store_thm
  ("MainCorollary",
   ``!C Vars FVars.
      (|= circuitp C) /\
      (|= subset FVars (cone_variables Vars C))
      ==>
      !f. (Atoms f) SUBSET (SexpToSet FVars)
          ==>
          (SAT (CIRC_TO_MODEL C) f =
           SAT (CIRC_TO_MODEL (cone_of_influence_reduction C Vars)) f)``,
   METIS_TAC [Main, SUBSET_TRANS, subset_implies_SUBSET]);

show_tags := false;

export_theory();

compile_theory();
