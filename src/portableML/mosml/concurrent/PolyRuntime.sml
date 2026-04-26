(* Moscow ML stub for PolyRuntime.
   No-op implementations — all Poly/ML-specific features (heap save,
   thread-based timeout, PolyML.compiler) are unavailable on mosml.
   These functions are never called at runtime on mosml because the
   Globals refs that gate them (dumpheap, g_flag) are always false. *)
structure PolyRuntime :> PolyRuntime =
struct

exception TacticTimeout of real

fun tactic_timeout _ f x = f x  (* no timeout on mosml *)

fun save_heap _ = ()  (* no heap save on mosml *)

fun eval_sml_string _ = raise Fail "eval_sml_string not available on mosml"

end (* struct *)
