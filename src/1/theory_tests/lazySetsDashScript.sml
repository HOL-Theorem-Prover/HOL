Theory lazySetsDash[bare]
Ancestors
  lazyAncA
Libs
  HolKernel lazyAncestryLib

(* records "-", the fringe of the theory graph, as this theory's ancestry *)
val _ = #set_parents anc ["-"]
val _ = record "dash"
