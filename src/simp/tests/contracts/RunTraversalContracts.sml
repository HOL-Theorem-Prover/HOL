(* Normal Holmake launcher for the same module as the paired legacy probe. *)
open HolKernel testutils
val _ = new_theory "traversallifetimes"
val _ = TraversalContracts.run ()
val _ = OS.Process.exit OS.Process.success
