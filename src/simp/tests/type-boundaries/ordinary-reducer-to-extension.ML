(* Deliberately ill-typed: opaque ordinary reducers require explicit lift. *)
val bad = simpExtLib.dproc_ss (Traverse.REDUCER
  {name=NONE,initial=Fail "ordinary",addcontext=fn (ctxt,_) => ctxt,
   apply=fn _ => Conv.NO_CONV});
