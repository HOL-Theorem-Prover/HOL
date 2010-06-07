signature holfootLib =
sig
  include Abbrev

   structure holfoot_param : sig
    include Abbrev;

    val combinator_thmL              : thm list
    val predicate_ssfrag             : int -> simpLib.ssfrag
    val final_decision_procedure     : thm list -> term -> thm;
    val combinator_terms             : term * term * term;
    val resource_proccall_free_thmL  : thm list
    val inital_prop_rewrite_thmL     : thm list
    val abstrL                       : separationLogicLib.fasl_program_abstraction list
    val comments_step_convL          : (conv->conv) list
    val quantifier_heuristicsL       : quantHeuristicsLib.quant_param list
    val var_res_prop_implies___GENERATE :
       (term list -> int -> (bool * simpLib.ssfrag) -> thm list -> term * term * term * term -> thm list) list

    val hoare_triple_case_splitL     : (term -> term) list
    val frame_split_case_splitL      : (term -> term) list

    structure var_res_base : sig
       include Abbrev;

       val var_res_prove              : Abbrev.term -> Abbrev.thm
       val var_res_prove___no_expn    : Abbrev.term -> Abbrev.thm
       val var_res_assumptions_prove  : Abbrev.thm -> Abbrev.thm
       val var_res_precondition_prove : Abbrev.thm -> Abbrev.thm
       val var_res_precondition_assumption_prove :
                                        Abbrev.term option -> Abbrev.thm -> Abbrev.thm
       val raise_var_res_prove_expn   : exn -> 'a

       val COND_REWR_CONV             : Abbrev.thm -> Abbrev.conv
       val COND_REWRITE_CONV          : bool -> Abbrev.thm list -> Abbrev.conv
       val GUARDED_COND_REWRITE_CONV  : bool -> (Abbrev.term -> bool) -> Abbrev.thm list -> Abbrev.conv

       val VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV : conv -> conv
       val VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV : conv -> conv
       val VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV : (term -> bool) -> conv

       val var_res_prop___VAR_EQ_PROPAGATE : conv
       val VAR_RES_COND_INFERENCE___CONST_INTRO___CONV : term -> string option -> term -> (bool * term * thm)
       val VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV : (term * string option) list -> term -> thm
       val VAR_RES_FRAME_SPLIT_INFERENCE___CONST_INTRO___CONV : term -> string option -> term -> thm
       val VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV : (term * string option) list -> term -> thm

       val var_res_prop_equal_unequal___NORMALISE_CONV : conv
       val VAR_RES_PROP_REWRITE_CONV : (bool * simpLib.ssfrag) -> thm list -> term -> thm
       val get_const_name_for_exp    : string -> term -> string

       val VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV : int list -> conv
       val var_res_prop___COND_RESORT_CONV : int list -> conv

       val cond_rewrite___varlist_update : thm list -> conv
       val GENERATE___var_res_exp_varlist_update___REWRITES : term -> term -> term -> (term * thm list)
       val var_res_prop___var_res_prop_varlist_update___EVAL : term -> conv;
       val VAR_RES_COND_INFERENCE___PRECOND_var_res_prop_varlist_update___EVAL : term -> conv

       val BAG_NORMALISE_CONV : conv;
       val VAR_RES_FRAME_SPLIT___imp_CONV               : conv -> conv
       val VAR_RES_FRAME_SPLIT___split_CONV             : conv -> conv
       val VAR_RES_FRAME_SPLIT___context_CONV           : conv -> conv
       val VAR_RES_FRAME_SPLIT___context_split_imp_CONV : conv -> conv
       val VAR_RES_FRAME_SPLIT___PROP_CONV              : conv -> conv

       type var_res_inference_param =
         {fast           : bool,
          do_prop_simps  : bool,
          prop_simp_ss   : simpLib.ssfrag,
          expands_level  : int};

       type var_res_inference = var_res_inference_param -> thm list -> ConseqConv.directed_conseq_conv

       val no_context_conseq_conv                    : ConseqConv.directed_conseq_conv -> var_res_inference;
       val no_context_strengthen_conseq_conv         : conv -> var_res_inference;
       val context_strengthen_conseq_conv            : (thm list -> conv) -> var_res_inference;
       val simpset_strengthen_conseq_conv            : ((bool * simpLib.ssfrag) -> thm list -> conv) -> var_res_inference;
       val simpset_no_context_strengthen_conseq_conv : ((bool * simpLib.ssfrag) -> conv) -> var_res_inference;
       val expands_strengthen_conseq_conv            : (int -> (bool * simpLib.ssfrag) -> thm list -> conv) -> var_res_inference;
    end

    val INFERENCES_LIST___simulate_command          : (string * var_res_base.var_res_inference) list
    val INFERENCES_LIST___simulate_minor_command    : (string * var_res_base.var_res_inference) list
    val INFERENCES_LIST___expensive_simplifications : (string * var_res_base.var_res_inference) list
    val INFERENCES_LIST___entailment_steps          : (string * var_res_base.var_res_inference) list

    val VAR_RES_IS_PURE_PROPOSITION___provers : (term -> term -> thm) list
  end

  structure holfoot_tactics : sig
   type var_res_inference_group =
     (* group name (used for debug) *) 
     string * 
     (* group guard, inferences are just applied to
        terms that satisfy this guard *)
     (Abbrev.term -> bool) * 
     (* apply before working on subterms *) 
     bool * 
     (* use this inference group to clean up after a "bigger" step *)
     bool * 
     (* the members of the group, each with a name for debugging *)
     (string * holfoot_param.var_res_base.var_res_inference) list;

   type user_rewrite_param = (Abbrev.thm list * Abbrev.conv list * simpLib.ssfrag list);
   type gen_step_param = {use_asms       : bool,
                          do_case_splits : bool,
                          expands_level  : int,
                          generate_vcs   : bool,
                          fast           : bool,
                          stop_evals     : (Abbrev.term -> bool) list,
                          prop_simp_level: int,
                          inferences     : (int * var_res_inference_group) list *
                                           (int * var_res_inference_group) list *
                                           (int * var_res_inference_group) list};

   datatype gen_step_tac_opt =
       case_splits_flag of bool
     | expands_level of int
     | fast_flag of bool
     | prop_simp_level of int
     | use_asms_flag of bool
     | generate_vcs_flag of bool
     | add_rewrites of Abbrev.thm list
     | add_convs of Abbrev.conv list
     | add_ssfrags of simpLib.ssfrag list
     | stop_evals of (Abbrev.term -> bool) list
     | combined_gen_step_tac_opt of gen_step_tac_opt list
     | add_inference_groups of (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list;

   val no_case_splits        : gen_step_tac_opt;
   val do_case_splits        : gen_step_tac_opt;
   val no_expands            : gen_step_tac_opt;
   val do_expands            : gen_step_tac_opt;
   val full_expands          : gen_step_tac_opt;
   val no_case_split_expands : gen_step_tac_opt;
   val generate_vcs          : gen_step_tac_opt;
   val dont_generate_vcs     : gen_step_tac_opt;
   val no_asms               : gen_step_tac_opt;
   val use_asms              : gen_step_tac_opt;
   val no_prop_simps         : gen_step_tac_opt;
   val simple_prop_simps     : gen_step_tac_opt;
   val conservative          : gen_step_tac_opt; (* not fast *)
   val careful               : gen_step_tac_opt; (* no asms. no case splits, no expands *)
   val stop_at_cond          : gen_step_tac_opt;
   val stop_at_while         : gen_step_tac_opt;
   val stop_at_abstraction   : gen_step_tac_opt;
   val stop_at_frame_calc    : gen_step_tac_opt;
   val stop_at_hoare_triple  : gen_step_tac_opt;
   val stop_at_block_spec    : gen_step_tac_opt;

   val gen_step_param___update_use_asms   : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_cs         : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_vcs        : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_expands    : gen_step_param -> int  -> gen_step_param
   val gen_step_param___update_fast       : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_prop_simps : gen_step_param -> int  -> gen_step_param
   val gen_step_param___update_stop_evals : gen_step_param -> (Abbrev.term -> bool) list -> gen_step_param
   val gen_step_param___update_inferences : gen_step_param -> (
                               (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list) -> gen_step_param

   val gen_step_param___add_inferences    : gen_step_param -> (
                               (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list *
                               (int * var_res_inference_group) list) -> gen_step_param

   val VAR_RES_GEN_STEP_CONSEQ_CONV : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.thm list -> Abbrev.conv
   val VAR_RES_GEN_STEP_TAC         : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.tactic
   val xVAR_RES_GEN_STEP_CONSEQ_CONV: gen_step_tac_opt list -> int option -> int -> Abbrev.conv
   val xVAR_RES_GEN_STEP_TAC        : gen_step_tac_opt list -> int option -> int -> Abbrev.tactic

   val VAR_RES_PURE_VC_TAC          : Abbrev.tactic;
   val VAR_RES_ELIM_COMMENTS_TAC    : Abbrev.tactic
   val VAR_RES_VC_TAC               : Abbrev.tactic;
   val VAR_RES_SPECIFICATION___CONSEQ_CONV : ConseqConv.conseq_conv
   val VAR_RES_SPECIFICATION_TAC    : Abbrev.tactic
   val VAR_RES_ENTAILMENT_INIT___CONSEQ_CONV : ConseqConv.conseq_conv
   val VAR_RES_ENTAILMENT_INIT_TAC   : Abbrev.tactic
end


   val add_rewrites : Abbrev.thm list -> holfoot_tactics.gen_step_tac_opt;
   val add_convs : Abbrev.conv list -> holfoot_tactics.gen_step_tac_opt;
   val add_ssfrags : simpLib.ssfrag list -> holfoot_tactics.gen_step_tac_opt;
   val combined_gen_step_tac_opt : holfoot_tactics.gen_step_tac_opt list -> holfoot_tactics.gen_step_tac_opt;
   val add_inference_groups  : (int * holfoot_tactics.var_res_inference_group) list *
                               (int * holfoot_tactics.var_res_inference_group) list *
                               (int * holfoot_tactics.var_res_inference_group) list -> holfoot_tactics.gen_step_tac_opt
   val no_case_splits        : holfoot_tactics.gen_step_tac_opt;
   val do_case_splits        : holfoot_tactics.gen_step_tac_opt;
   val no_expands            : holfoot_tactics.gen_step_tac_opt;
   val do_expands            : holfoot_tactics.gen_step_tac_opt;
   val full_expands          : holfoot_tactics.gen_step_tac_opt;
   val no_case_split_expands : holfoot_tactics.gen_step_tac_opt;
   val generate_vcs          : holfoot_tactics.gen_step_tac_opt;
   val dont_generate_vcs     : holfoot_tactics.gen_step_tac_opt;
   val no_asms               : holfoot_tactics.gen_step_tac_opt;
   val use_asms              : holfoot_tactics.gen_step_tac_opt;
   val no_prop_simps         : holfoot_tactics.gen_step_tac_opt;
   val simple_prop_simps     : holfoot_tactics.gen_step_tac_opt;
   val conservative          : holfoot_tactics.gen_step_tac_opt; (* not fast *)
   val careful               : holfoot_tactics.gen_step_tac_opt; (* no asms. no case splits, no expands *)
   val stop_at_cond          : holfoot_tactics.gen_step_tac_opt;
   val stop_at_while         : holfoot_tactics.gen_step_tac_opt;
   val stop_at_abstraction   : holfoot_tactics.gen_step_tac_opt;
   val stop_at_frame_calc    : holfoot_tactics.gen_step_tac_opt;
   val stop_at_hoare_triple  : holfoot_tactics.gen_step_tac_opt;
   val stop_at_block_spec    : holfoot_tactics.gen_step_tac_opt;

   val default_holfoot_gst_optL : holfoot_tactics.gen_step_tac_opt list ref;

   val HF_GEN_STEP_CONSEQ_CONV : holfoot_tactics.gen_step_param -> holfoot_tactics.user_rewrite_param -> int option -> int -> Abbrev.thm list -> Abbrev.conv
   val HF_GEN_STEP_TAC         : holfoot_tactics.gen_step_param -> holfoot_tactics.user_rewrite_param -> int option -> int -> Abbrev.tactic
   val xHF_GEN_STEP_CONSEQ_CONV: holfoot_tactics.gen_step_tac_opt list -> int option -> int -> Abbrev.conv
   val xHF_GEN_STEP_TAC        : holfoot_tactics.gen_step_tac_opt list -> int option -> int -> Abbrev.tactic

   val xHF_STEP_TAC            : holfoot_tactics.gen_step_tac_opt list -> int -> Abbrev.tactic;
   val xHF_STEP_TAC_n          : holfoot_tactics.gen_step_tac_opt list -> int -> int option -> Abbrev.tactic;
   val xHF_SOLVE_TAC           : holfoot_tactics.gen_step_tac_opt list -> Abbrev.tactic;
   val xHF_CONTINUE_TAC        : holfoot_tactics.gen_step_tac_opt list -> Abbrev.tactic;
   val xHF_SIMPLIFY_TAC        : holfoot_tactics.gen_step_tac_opt list -> Abbrev.tactic;

   val HF_STEP_TAC             : int -> Abbrev.tactic;
   val HF_STEP_TAC_n           : int -> int option -> Abbrev.tactic;
   val HF_SOLVE_TAC            : Abbrev.tactic;
   val HF_CONTINUE_TAC         : Abbrev.tactic;
   val HF_SIMPLIFY_TAC         : Abbrev.tactic;
   val HF_VC_SOLVE_TAC         : Abbrev.tactic;

   val HF_PURE_VC_TAC          : Abbrev.tactic;
   val HF_ELIM_COMMENTS_TAC    : Abbrev.tactic
   val HF_VC_TAC               : Abbrev.tactic;
   val HF_SPECIFICATION_TAC    : Abbrev.tactic
   val HF_INIT_TAC             : Abbrev.tactic
   val HF_SPECIFICATION_CONSEQ_CONV : ConseqConv.conseq_conv


   val holfoot_set_goal                : string -> proofManagerLib.proofs
   val holfoot_set_goal_preprocess     : string -> proofManagerLib.proofs
   val holfoot_set_goal_specs          : string -> string list -> proofManagerLib.proofs
   val holfoot_set_goal_procedures     : string -> string list -> proofManagerLib.proofs
   val holfoot_auto_verify_spec        : string -> thm
   val holfoot_verify_spec             : string -> holfoot_tactics.gen_step_tac_opt list -> thm
   val holfoot_tac_verify_spec         : string -> (holfoot_tactics.gen_step_tac_opt list) option -> (string * tactic) list -> thm
   val holfoot_interactive_verify_spec : bool -> bool -> string -> (holfoot_tactics.gen_step_tac_opt list) option -> (string * tactic) list -> thm
   val holfoot_prove_remaining         : (thm * tactic) -> thm
   val holfoot_set_remaining_goal      : thm -> proofManagerLib.proofs

end
