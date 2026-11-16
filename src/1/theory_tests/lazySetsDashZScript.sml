Theory lazySetsDashZ[bare]
Ancestors
  lazySetsDashC
Libs
  HolKernel lazyAncestryLib

(* lazySetsDash's ancestry and so lazySetsDashC's lead to "-", so their
   values are computed when they are loaded.  The fringe here includes
   both, so neither merge finds a theory with a value. *)
fun db thy = #DB anc {thyname = thy}
val _ = db "lazySetsDash" = NONE orelse raise Fail "lazySets: lazySetsDash"
val _ = db "lazySetsDashC" = NONE orelse raise Fail "lazySets: lazySetsDashC"
