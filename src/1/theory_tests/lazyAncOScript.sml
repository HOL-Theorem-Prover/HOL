Theory lazyAncO[bare]
Ancestors
  lazyAncB1 lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* records an ancestry that leaves out lazyAncB2 *)
val _ = #set_parents eager ["lazyAncB1"]
val _ = #set_parents lazy ["lazyAncB1"]
val _ = record "o"
