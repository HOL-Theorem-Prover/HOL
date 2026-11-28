(* Deliberately ill-typed: explicit lift is required. *)
val bad : TraverseExt.reducer = Traverse.REDUCER
  {name=NONE,initial=Fail "ordinary",addcontext=fn (ctxt,_) => ctxt,
   apply=fn _ => Conv.NO_CONV};
