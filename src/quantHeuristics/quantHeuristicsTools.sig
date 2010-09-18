signature quantHeuristicsTools =
sig
  include Abbrev


  val TOP_ONCE_REWRITE_CONV        : thm list -> conv;
  val NEG_NEG_INTRO_CONV           : conv;
  val NEG_NEG_ELIM_CONV            : conv;
  val NOT_FORALL_LIST_CONV         : conv;
  val NOT_EXISTS_LIST_CONV         : conv;
  val STRIP_NUM_QUANT_CONV         : int -> conv -> conv;
  val BOUNDED_NOT_EXISTS_LIST_CONV : int -> conv;
  val BOUNDED_REPEATC              : int -> conv -> conv;

  val EXISTS_NOT_LIST_CONV         : conv;
  val FORALL_NOT_LIST_CONV         : conv;
  val QUANT_SIMP_CONV              : conv;

  val NOT_OR_CONV                  : conv;
  val NOT_AND_CONV                 : conv;
  val AND_NOT_CONV                 : conv;
  val OR_NOT_CONV                  : conv;

  val VARIANT_TAC                  : term list -> tactic
  val VARIANT_CONV                 : term list -> conv

  val min_var_occur_CONV           : term -> conv
  val match_term_var               : term -> term -> term -> term
  val list_variant                 : term list -> term list -> (term list * (term,term) Lib.subst);

  val EQ_EXISTS_INTRO              : (term * thm) -> thm;
  val EQ_FORALL_INTRO              : (term * thm) -> thm;
  val AND_IMP_INTRO_CONV           : term -> thm
  val AND_IMP_ELIM_CONV            : term -> thm
  val LIST_AND_IMP_ELIM_CONV       : term -> thm
  val IMP_EXISTS_INTRO             : term * thm -> thm
  val IMP_FORALL_INTRO             : term * thm -> thm
  val LEFT_IMP_AND_INTRO_RULE      : term -> thm -> thm
  val RIGHT_IMP_AND_INTRO_RULE     : term -> thm -> thm
  val LEFT_IMP_OR_INTRO_RULE       : term -> thm -> thm
  val RIGHT_IMP_OR_INTRO_RULE      : term -> thm -> thm

end
