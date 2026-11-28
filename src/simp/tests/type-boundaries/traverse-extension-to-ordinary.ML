(* Deliberately ill-typed: no implicit reverse adapter is provided. *)
val bad : Traverse.reducer = TraverseExt.lift (Traverse.REDUCER
  {name=NONE,initial=Fail "ordinary",addcontext=fn (ctxt,_) => ctxt,
   apply=fn _ => Conv.NO_CONV});
