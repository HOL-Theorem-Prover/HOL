signature Canon_Port = 
sig
  include Abbrev

  val is_eqc        : term -> bool
  val freesl        : term list -> term list
  val get_thm_heads : thm -> (term*int)list * (term*int) list 
                          -> (term*int)list * (term*int) list
  val NNFC_CONV     : conv
  val DELAMB_CONV   : conv
  val PROP_CNF_CONV : conv
  val PRESIMP_CONV  : conv
  val SKOLEM_CONV   : conv
  val PRENEX_CONV   : conv
  val REFUTE_THEN   : (thm -> tactic) -> tactic
  val GEN_FOL_CONV  : (term*int)list * (term*int) list -> conv
end;

