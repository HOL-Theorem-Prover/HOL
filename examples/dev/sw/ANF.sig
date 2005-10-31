signature ANF =
sig
  include Abbrev

  type env = (term * (bool * thm * thm * thm)) list

  val toComb : thm -> bool * term * thm
  val toANF : env -> thm -> env

end
