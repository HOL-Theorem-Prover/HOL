signature holfootLib =
sig
  include Abbrev

   type user_rewrite_param = (Abbrev.thm list * Abbrev.conv list * simpLib.ssfrag list);
   type gen_step_param = {use_asms       : bool,
                          do_case_splits : bool,
                          do_expands     : bool,
                          generate_vcs   : bool,
                          fast           : bool,
                          stop_evals     : (term -> bool) list,
                          prop_simp_level: int};

   datatype gen_step_tac_opt =
       case_splits_flag of bool
     | expands_flag of bool
     | fast_flag of bool
     | prop_simp_level of int
     | use_asms_flag of bool
     | generate_vcs_flag of bool
     | add_rewrites of thm list
     | add_convs of conv list
     | add_ssfrags of simpLib.ssfrag list
     | stop_evals of (term -> bool) list
     | combined_gen_step_tac_opt of gen_step_tac_opt list

   val no_case_splits        : gen_step_tac_opt;
   val do_case_splits        : gen_step_tac_opt;
   val no_expands            : gen_step_tac_opt;
   val do_expands            : gen_step_tac_opt;
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
   val gen_step_param___update_expands    : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_fast       : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_prop_simps : gen_step_param -> int  -> gen_step_param
   val gen_step_param___update_stop_evals : gen_step_param -> (term -> bool) list -> gen_step_param

   val HF_GEN_STEP_CONSEQ_CONV : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.thm list -> Abbrev.conv
   val HF_GEN_STEP_TAC         : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.tactic
   val xHF_GEN_STEP_CONSEQ_CONV: gen_step_tac_opt list -> int option -> int -> Abbrev.conv
   val xHF_GEN_STEP_TAC        : gen_step_tac_opt list -> int option -> int -> Abbrev.tactic

   val xHF_STEP_TAC            : gen_step_tac_opt list -> int -> Abbrev.tactic;
   val xHF_STEP_TAC_n          : gen_step_tac_opt list -> int -> int option -> Abbrev.tactic;
   val xHF_SOLVE_TAC           : gen_step_tac_opt list -> Abbrev.tactic;
   val xHF_CONTINUE_TAC        : gen_step_tac_opt list -> Abbrev.tactic;
   val xHF_SIMPLIFY_TAC        : gen_step_tac_opt list -> Abbrev.tactic;

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
   val holfoot_verify_spec             : string -> gen_step_tac_opt list -> thm
   val holfoot_tac_verify_spec         : string -> (gen_step_tac_opt list) option -> (string * tactic) list -> thm
   val holfoot_interactive_verify_spec : bool -> bool -> string -> (gen_step_tac_opt list) option -> (string * tactic) list -> thm
   val holfoot_prove_remaining         : (thm * tactic) -> thm
   val holfoot_set_remaining_goal      : thm -> proofManagerLib.proofs
end
