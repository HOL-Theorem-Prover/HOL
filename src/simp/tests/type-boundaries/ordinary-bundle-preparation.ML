(* Bundle preparation cannot silently replay an ordinary simpset. *)
val _ = simpExtLib.prepare_rewrite_bundle simpLib.empty_ss [];
