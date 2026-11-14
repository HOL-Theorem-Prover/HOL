Theory lazySetsSelf[bare]
Ancestors
  lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* records an ancestry naming this theory itself *)
val _ = #set_parents anc [current_theory(), "lazyAncB2"]
val _ = record "self"
