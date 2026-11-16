Theory splitChild[bare]
Ancestors
  splitParent
Libs
  HolKernel Parse boolLib splitLib testutils

val _ = testutils.tprint "child sees fresh parent addition/removal replay"
val _ = if map #1 (splitLib.named_split_thms ()) =
             ["splitParent$drop", "splitParent$keep"]
        then testutils.OK () else testutils.die "parent import replay"

(* The child's identically named theorem must survive the ancestor REMOVE. *)
val _ = splitLib.exclude_split "splitParent.drop"
Theorem drop[split] = splitLib.type_split_of “:bool”;
Theorem ephemeral[split] = splitLib.type_split_of “:bool”;
val _ = splitLib.exclude_split "ephemeral"

val _ = testutils.tprint "child persistent named retraction and addition"
val _ = if map #1 (splitLib.named_split_thms ()) =
             ["splitChild$drop", "splitParent$keep"]
        then testutils.OK () else testutils.die "child split names"
