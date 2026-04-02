Theory staleSimp[bare]
Libs
  HolKernel Parse boolLib BasicProvers

val def = new_definition("def", “c : bool -> bool = λb. ¬b”);

val _ = export_rewrites ["def"]

val _ = new_constant("c", “:bool -> bool”);

(* give the theory at least one valid theorem *)
Theorem boring = TRUTH
