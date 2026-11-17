Theory lazySetsZ[bare]
Ancestors
  lazySetsR2 lazySetsCT lazySetsSelf
Libs
  HolKernel lazyAncestryLib

(* Loading applied no delta.  Reading each value applies every delta in
   its ancestry once: lazySetsR lists a redundant parent, lazySetsCT's
   ancestry is the last one its script set, and lazySetsSelf's names
   itself *)
val _ = !applied = 0 orelse raise Fail "lazySets: values not lazy"

fun db thy = #DB anc {thyname = thy}
val _ = check "lazySetsR2" ["a1", "a2", "b1", "b2", "o", "r", "r2"]
              (db "lazySetsR2")
val _ = !applied = 7 orelse raise Fail "lazySets: lazySetsR2 deltas"
val _ = check "lazySetsCT" ["a1", "a2", "b1", "b2", "ct"] (db "lazySetsCT")
val _ = check "lazySetsSelf" ["a1", "a2", "b2", "self"] (db "lazySetsSelf")
val _ = check "merge" ["a1", "a2", "b1", "b2", "ct", "o", "r", "r2", "self"]
              (#merge anc ["lazySetsR2", "lazySetsCT", "lazySetsSelf"])
