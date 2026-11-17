Theory lazySetsCT[bare]
Ancestors
  lazyAncB1 lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* The current theory's ancestry is computed afresh each time its parents
   are set *)
val _ = check "lazySetsCT first" ["a1", "a2", "b1"]
              (#set_parents anc ["lazyAncB1"])
val _ = check "lazySetsCT second" ["a1", "a2", "b1", "b2"]
              (#set_parents anc ["lazyAncB1", "lazyAncB2"])
val _ = record "ct"
