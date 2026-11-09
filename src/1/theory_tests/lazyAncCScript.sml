Theory lazyAncC[bare]
Ancestors
  lazyAncB1 lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* Loading the theories applied no delta; reading their values applies
   each theory's deltas once, and reading them again applies none *)
val _ = !applied = 0 orelse raise Fail "lazyAnc: values not lazy"

fun db thy = #DB anc {thyname = thy}
val _ = case (db "lazyAncA", db "lazyAncB1", db "lazyAncB2") of
            (SOME ["a2", "a1"], SOME ["b1", "a2", "a1"],
             SOME ["b2", "a2", "a1"]) => ()
          | _ => raise Fail "lazyAnc: unexpected stored values"
val _ = !applied = 4 orelse raise Fail "lazyAnc: deltas applied twice"
val _ = (db "lazyAncA", db "lazyAncB2")
val _ = !applied = 4 orelse raise Fail "lazyAnc: value computed twice"

val _ = check "merge" ["a1", "a2", "b1", "b2"]
              (#merge anc ["lazyAncA", "lazyAncB1", "lazyAncB2"])
val _ = check "global" ["a1", "a2", "b1", "b2"]
              (SOME (#get_global_value anc ()))
