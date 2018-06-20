signature term_pp_utils =
sig

  type term = Term.term
  val dflt_pinfo : term_pp_types.printing_info

  val setbvs : term HOLset.set -> (term_pp_types.printing_info,unit) smpp.t
  val getbvs : (term_pp_types.printing_info,term HOLset.set) smpp.t
  val addbvs : term list -> (term_pp_types.printing_info,unit)smpp.t
  val record_bvars : term list -> (term_pp_types.printing_info,'a) smpp.t ->
                     (term_pp_types.printing_info,'a) smpp.t

  val getfvs : (term_pp_types.printing_info,term HOLset.set) smpp.t
  val spotfv : term -> (term_pp_types.printing_info,unit) smpp.t

  val set_gspec : (term_pp_types.printing_info,'a) smpp.t ->
                  (term_pp_types.printing_info,'a) smpp.t
  val get_gspec : (term_pp_types.printing_info,bool) smpp.t

  val decdepth : int -> int
  val pp_dest_abs : term_grammar.grammar -> term -> term * term
  val pp_is_abs : term_grammar.grammar -> term -> bool

  datatype bvar = datatype term_pp_utils_dtype.bvar
  val bv2term : bvar -> term

  val dest_vstruct :
      term_grammar.grammar ->
      {binder : string option, restrictor : string option} ->
      term -> bvar * term
  val strip_vstructs :
      term_grammar.grammar ->
      {binder : string option, restrictor : string option} ->
      term -> bvar list * term

end
