signature smallfootLib =
sig
  include Abbrev

  (*Conversion to handle the original parsed term and
    do some preprocessing*)
  val SMALLFOOT_SPECIFICATION___CONSEQ_CONV : conv;

  (*Reasoning for the different statements*)
  val SMALLFOOT_COND_INFERENCE_CONV___assign : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___new : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___cond : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___field_lookup : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___field_assign : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___dispose : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___skip : conv;
  val SMALLFOOT_COND_INFERENCE_CONV___cond_choose_const : conv;

  (*A combination for all statements*)
  val SMALLFOOT_COND_INFERENCE_CONV___prog_step : conv;


  (*Varies conversions to handle SMALLFOOT_PROP_IMPLIES,
    i.e. to prove entailments and deduce frames*)
  val SMALLFOOT_PROP_IMPLIES___EQ_PROPAGATE___CONSEQ_CONV : conv;
  val SMALLFOOT_PROP_IMPLIES___SIMP_EQ___CONV : conv
  val SMALLFOOT_PROP_IMPLIES___ELIM_stack_true___CONV : conv
  val SMALLFOOT_PROP_IMPLIES___ELIM_FRAME___CONV : conv
  val SMALLFOOT_PROP_IMPLIES___ELIM_POINTS_TO___CONSEQ_CONV : conv
  val SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___TO_CONTEXT___CONV : bool -> conv
  val SMALLFOOT_PROP_IMPLIES___LIST_REMOVE_START___CONSEQ_CONV : conv
  val SMALLFOOT_PROP_IMPLIES___SOLVE___CONSEQ_CONV : conv


  (*A tactic to do the initial processing*)
  val SMALLFOOT_SPECIFICATION_TAC : tactic

  (*Performs one step*)
  val SMALLFOOT_STEP_TAC : tactic
  val SMALLFOOT_MINI_STEP_TAC : tactic

  (*Tries as many steps as possible. This
    should solve the goal*)
  val SMALLFOOT_SOLVE_TAC : tactic

  (*Parses a file and sets the goal, that the
    specification is correct. It calls
    SMALLFOOT_SPECIFICATION_TAC for the preprocessing*)
  val smallfoot_set_goal : string -> proofManagerLib.proof


  (*Parses a file and tries to prove it correct.
    Same as smallfoot_set_goal followed by
    SMALLFOOT_SOLVE_TAC. The verbose version gives some
    status reports on the way and measures the needed time.*)
  val smallfoot_prove : string -> thm;
  val smallfoot_verbose_prove : string -> thm;



  (*General stuff*)
  val smallfoot_prop___SIMPLIFY_CONV : conv;
  val smallfoot_prop___EQ_PROPAGATE_CONV : bool -> bool -> conv;

  val MAKE___SMALLFOOT_COND_PROP___IMP___RULE : thm -> thm
  val MAKE___SMALLFOOT_COND_PROP___EQUIV___RULE : thm -> thm
  val SMALLFOOT_COND_PROP___IMP___TRANS_RULE : thm -> thm -> thm
  val SMALLFOOT_COND_PROP___EQUIV___TRANS_RULE : thm -> thm -> thm
  val SMALLFOOT_COND_PROP___EQ_OR_IMP_OR_EQUIV___TRANS_RULE : thm -> thm -> thm








end
