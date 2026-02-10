signature Elim_Lambda =
sig
  include Abbrev

  val firstify : thm -> (thm * thm list) option

end
