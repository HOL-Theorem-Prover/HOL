open HolKernel boolLib

val _ = new_theory"gh1370";

val _ = new_definition ("def", “c = T”);

val _ =
 adjoin_to_theory
 {sig_ps = SOME (fn _ => PP.add_string "val ctm : Term.term"),
  struct_ps = NONE};

val _ = adjoin_after_completion
    (fn _ => PP.add_string ("val ctm = Parse.Term ‘c’;\n\n"))

val _ = export_theory();
