(* congLibFn over TraverseExt reducers and simpExtLib simpsets *)
signature congExtLib =
sig
  include congLibFn where type reducer = TraverseExt.reducer
                      and type simpset = simpExtLib.simpset

  val lift_fragment : congLib.congsetfrag -> congsetfrag
end
