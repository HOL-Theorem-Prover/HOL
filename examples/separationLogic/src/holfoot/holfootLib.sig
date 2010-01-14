signature holfootLib =
sig
  include Abbrev

  type user_rewrite_param = (Abbrev.thm list * Abbrev.conv list * simpLib.ssfrag list);
  type gen_step_param = {use_asms       : bool,
                         do_case_splits : bool,
                         do_expands     : bool,
                         generate_vcs   : bool,
                         fast           : bool,
                         do_prop_simps  : bool};


   val GEN_STEP_CONSEQ_CONV : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.thm list -> Abbrev.conv
   val GEN_STEP_TAC         : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.tactic

   val xSTEP_TAC            : user_rewrite_param -> int -> Abbrev.tactic;
   val xSTEP_TAC_n          : user_rewrite_param -> int -> int option -> Abbrev.tactic;
   val xSOLVE_TAC           : user_rewrite_param -> Abbrev.tactic;
   val xCONTINUE_TAC        : (bool * bool * bool * bool) -> user_rewrite_param -> Abbrev.tactic;
   val xVC_STEP_TAC_n       : user_rewrite_param -> int -> int option -> Abbrev.tactic;
   val xVC_STEP_TAC         : user_rewrite_param -> int -> Abbrev.tactic;
   val xVC_SOLVE_TAC        : user_rewrite_param -> Abbrev.tactic;

   val STEP_TAC             : int -> Abbrev.tactic;
   val STEP_TAC_n           : int -> int option -> Abbrev.tactic;
   val SOLVE_TAC            : Abbrev.tactic;
   val CONTINUE_TAC         : (bool * bool * bool * bool) -> Abbrev.tactic;
   val VC_STEP_TAC_n        : int -> int option -> Abbrev.tactic;
   val VC_STEP_TAC          : int -> Abbrev.tactic;
   val VC_SOLVE_TAC         : Abbrev.tactic;

   val PURE_VC_TAC          : Abbrev.tactic;
   val ELIM_COMMENTS_TAC    : Abbrev.tactic
   val HOLFOOT_SPECIFICATION_TAC : Abbrev.tactic

   val holfoot_set_goal                : string -> proofManagerLib.proofs
   val holfoot_auto_verify_spec        : bool -> string -> thm
   val holfoot_interactive_verify_spec : bool -> gen_step_param -> user_rewrite_param -> string -> thm
   val holfoot_prove_remaining         : (thm * tactic) -> thm
   val holfoot_set_remaining_goal      : thm -> proofManagerLib.proof
end
