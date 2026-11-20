(* Deliberately ill-typed: extension reducers cannot be installed ordinarily. *)
val bad = simpLib.dproc_ss (TraverseExt.lift (Traverse.REDUCER
  {name=NONE,initial=Fail "lifted",addcontext=fn (ctxt,_) => ctxt,
   apply=fn _ => Conv.NO_CONV}));
