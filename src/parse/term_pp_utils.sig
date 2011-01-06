signature term_pp_utils =
sig

  type term = Term.term
  val setbvs : term HOLset.set -> (term_pp_types.printing_info,unit) smpp.t
  val getbvs : (term_pp_types.printing_info,term HOLset.set) smpp.t
  val addbvs : term list -> (term_pp_types.printing_info,unit)smpp.t
  val record_bvars : term list -> (term_pp_types.printing_info,'a) smpp.t ->
                     (term_pp_types.printing_info,'a) smpp.t

  val getfvs : (term_pp_types.printing_info,term HOLset.set) smpp.t
  val spotfv : term -> (term_pp_types.printing_info,unit) smpp.t

end


