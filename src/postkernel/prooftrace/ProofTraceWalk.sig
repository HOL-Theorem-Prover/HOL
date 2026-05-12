signature ProofTraceWalk = sig

  type 'a ptr = 'a ProofTraceParser.ptr
  val walk :
    { heap : ProofTraceParser.heap,
      thyname : string,
      named_thms : (string * Thm.thm * 'thminfo) list ptr,
      anon_thms : Thm.thm list ptr,
      incr : unit ptr -> unit,
      on_def_thm : Thm.thm ptr -> unit } ->
    { tm_defs : (string, Thm.thm ptr list) Redblackmap.dict,
      ty_defs : (string, Thm.thm ptr list) Redblackmap.dict,
      is_closed : Term.term ptr -> bool,
      get_const_id : Term.term ptr -> string * string,
      get_type_id : Type.hol_type ptr -> string * string }

end
