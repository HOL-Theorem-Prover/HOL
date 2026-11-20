(* There is no retrospective inventory of an arbitrary ordinary simpset. *)
val _ = simpExtLib.rewrite_source_handles
  (simpLib.++ (simpLib.empty_ss,simpLib.rewrites [boolTheory.TRUTH]));
