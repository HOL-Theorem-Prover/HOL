signature isqrtLib =
sig
  include Abbrev

  val iSQRT_COMPUTE_CONV : conv

  val sqrt_tm        : term
  val is_sqrt        : term -> bool
  val dest_sqrt      : term -> term
  val mk_sqrt        : term -> term
end
