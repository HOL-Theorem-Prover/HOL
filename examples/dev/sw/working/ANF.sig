signature ANF =
sig
  include Abbrev

  type env = (term * (bool * thm * thm * thm)) list

  val toComb : thm -> bool * term * term * thm
  val toANF : env -> thm -> env

  val std_bvars : string -> term -> term
  val STD_BVARS : string -> thm -> thm
  val STD_BVARS_CONV : string -> conv
  val STD_BVARS_TAC : string -> tactic
end
