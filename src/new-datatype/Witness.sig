signature Witness =
sig
  include Abbrev

  val find_inductive_witnesses
      : thm list -> thm option list -> thm list -> thm list

end
