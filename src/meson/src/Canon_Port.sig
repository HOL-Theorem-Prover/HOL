signature Canon_Port = 
sig
  type term = Term.term
  type thm  = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

  val freesl: term list -> term list
  val get_thm_heads : thm -> (term*int)list * (term*int) list 
                          -> (term*int)list * (term*int) list

  val GEN_FOL_CONV : (term*int)list * (term*int) list -> conv

  val NNFC_CONV     : conv
  val DELAMB_CONV   : conv
  val PROP_CNF_CONV : conv
  val PRESIMP_CONV  : conv
  val SKOLEM_CONV   : conv
  val PRENEX_CONV   : conv
  val REFUTE_THEN   : (thm -> tactic) -> tactic
end;

