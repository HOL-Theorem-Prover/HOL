open HolKernel Parse boolLib

open baseLib

val _ = new_theory "next";

val _ = save_thm("B" ^ Int.toString (do_base_thing 3), TRUTH);

val _ = export_theory();
