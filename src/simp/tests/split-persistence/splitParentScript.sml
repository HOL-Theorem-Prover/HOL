Theory splitParent[bare]
Libs
  HolKernel Parse boolLib splitLib splitPersistLib markerLib testutils

(* Libs initializes this script; the ML dependency initializes fresh imports.
   It belongs on this earliest split-bearing theory, not just its child. *)
val _ = Theory.add_ML_dependency "splitPersistLib"

Theorem keep[split] = splitLib.type_split_of “:bool”;
Theorem drop[split] = splitLib.type_split_of “:bool”;
Theorem transient[split] = splitLib.type_split_of “:bool”;

val _ = splitLib.exclude_split "transient"
val _ = splitLib.exclude_split "missing"
val _ = testutils.tprint "parent persistent addition and same-theory removal"
val _ = if map #1 (splitLib.named_split_thms ()) =
             ["splitParent$drop", "splitParent$keep"]
        then testutils.OK () else testutils.die "parent split names"

(* Exported marker theorems must keep their marker$ constants. *)
Theorem split_marker = markerLib.Split boolTheory.TRUTH;
Theorem exclusion_marker = markerLib.ExclX "case:bool";
