Theory lazySetsR[bare]
Ancestors
  lazyAncD
Libs
  HolKernel lazyAncestryLib

(* records an ancestry listing lazyAncA, an ancestor of lazyAncD, first *)
val _ = #set_parents anc ["lazyAncA", "lazyAncD"]
val _ = record "r"
