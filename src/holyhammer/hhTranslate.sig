signature hhTranslate =
sig

include Abbrev

  val must_pred       : term -> bool
  val contains_lambda : term -> bool
  val contains_exall  : term -> bool
  val has_fofarity    : term -> bool
  val classify        : thm -> (bool * bool * bool)

  val ATOM_CONV        : conv -> conv
  val BOOL_LIFT_CONV   : conv
  val LAMBDA_LIFT_CONV : conv

end
