(* Stub implementation of LSPExtension.goalStateAtPos, replaced by
   the goalFrag-based walker in later slices.  Loaded AFTER HOL is
   initialized so the proof-manager modules are in scope. *)

val () = LSPExtension.goalStateAtPos :=
  (fn (_: LSPExtension.hover_context, _: int) => NONE)
