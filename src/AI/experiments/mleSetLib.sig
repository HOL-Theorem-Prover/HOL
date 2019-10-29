signature mleSetLib =
sig

  include Abbrev

  val eval_term : term -> int
  val eval_subst : (term * term) -> int -> bool
  val start_form : term
  val xvar : term
  val xvarl : term list
  val is_cont : term -> bool
  val cont_form : term
  val cont_term : term
  val yvarl : term list
  val movel : term list
  val random_step : term -> term
  val apply_move : term -> term -> term
  val is_applicable : term -> term -> bool

end
