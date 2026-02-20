signature Elim_Lambda =
sig
  include Abbrev

  val lift_lambdas : term -> (thm * thm list) option

end
