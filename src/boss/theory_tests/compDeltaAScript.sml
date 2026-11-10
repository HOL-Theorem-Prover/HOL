Theory compDeltaA
Ancestors
  compDeltaBase

(* A persistently removes cdrf from the compset; this takes effect in
   theories that load A *)
val _ = computeLib.del_persistent_consts [“cdrf”]
