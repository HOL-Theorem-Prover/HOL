signature Defn =
sig
  include Abbrev

  type thry   = TypeBasePure.typeBase
  type proofs = Manager.proofs
  type absyn  = Absyn.absyn
  type pattern = Functional.pattern

  val monitoring : bool ref

  val ind_suffix : string ref
  val def_suffix : string ref
  val const_eq_ref : conv ref

  val wfrec_eqns : thry -> term -> 
                    {SV : term list, 
                     WFR : term, 
                     extracta : (thm * term list * bool) list,
                     pats : pattern list, 
                     proto_def : term}

  val mk_defn    : string -> term -> defn
  val mk_Rdefn   : string -> term -> term -> defn
  val Hol_defn   : string -> term quotation -> defn
  val Hol_Rdefn  : string -> term quotation -> term quotation -> defn
  val mk_defns   : string list -> term list -> defn list
  val Hol_defns  : string list -> term quotation -> defn list

  val name_of    : defn -> string
  val eqns_of    : defn -> thm list
  val ind_of     : defn -> thm option
  val tcs_of     : defn -> term list
  val reln_of    : defn -> term option
  val params_of  : defn -> term list

  val aux_defn   : defn -> defn option
  val union_defn : defn -> defn option

  val inst_defn  : defn -> (term,term)subst * (hol_type,hol_type)subst -> defn
  val set_reln   : defn -> term -> defn

  val elim_tcs   : defn -> thm list -> defn
  val simp_tcs   : defn -> conv -> defn
  val prove_tcs  : defn -> tactic -> defn
  
  val triv_defn  : defn -> bool
  val fetch_eqns : defn -> thm

  val been_stored: string * thm -> unit
  val store      : string * thm * thm -> unit
  val save_defn  : defn -> unit

  val parse_absyn : absyn -> term * string list
  val parse_quote : term quotation -> term list

  val tgoal      : defn -> proofs
  val tprove0    : defn * tactic -> thm * thm
  val tprove     : defn * tactic -> thm * thm
  val tstore_defn : defn * tactic -> thm * thm

  val SUC_TO_NUMERAL_DEFN_CONV_hook : (term -> thm) ref

end
