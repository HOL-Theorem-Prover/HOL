Theory lazyAncO[bare]
Ancestors
  lazyAncB1 lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* records an ancestry that leaves out lazyAncB2 *)
val _ = #set_parents anc ["lazyAncB1"]
val _ = record "o"
