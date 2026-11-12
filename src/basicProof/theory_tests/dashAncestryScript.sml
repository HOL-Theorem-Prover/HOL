Theory dashAncestry[bare]
Libs
  HolKernel Parse boolLib BasicProvers

(* Stores "-", the fringe of the theory graph, as this theory's simpset
   parent.  When dashAncestry2 loads this theory, the fringe includes it,
   so its simpset ancestry leads back to itself. *)
val _ = set_simpset_ancestry ["-"]

Theorem boring = TRUTH
