Theory compDeltaE
Ancestors
  compDeltaD1 compDeltaD2

(* Loading D1 and D2 merges their parents C and B (one of the two parent
   orders starts the merge from C, which doesn't descend from A).  B's
   computeLib.delta value is then reached through A, but A's
   del_persistent_consts was already applied to the global compset when A
   loaded, before B's add_persistent_funs.  Replaying it during the merge
   would undo B's addition. *)
val th = EVAL “cdrf 1”
val _ = rhs (concl th) ~~ “2n” orelse
        raise Fail "cdrf no longer evaluates: A's delete was replayed"
