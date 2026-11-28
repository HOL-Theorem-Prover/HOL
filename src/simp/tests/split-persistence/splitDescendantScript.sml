Theory splitDescendant[bare]
Ancestors
  splitChild
Libs
  HolKernel Parse boolLib splitLib testutils

(* No script-time opt-in here: the ancestor's exported ML dependency must
   run before the first split-bearing .dat file and TheoryLoaded event. *)
val _ = testutils.tprint "fresh descendant preserves qualified REMOVE keys"
val _ = if map #1 (splitLib.named_split_thms ()) =
             ["splitChild$drop", "splitParent$keep"]
        then testutils.OK () else testutils.die "descendant split names"
