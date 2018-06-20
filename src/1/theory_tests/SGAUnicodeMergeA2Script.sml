open HolKernel Parse boolLib

val _ = new_theory "SGAUnicodeMergeA2";

val INTER_def = new_definition(
  "INTER_def",
  ``INTER P Q x = P x /\ Q x``);

val _ = Unicode.unicode_version { u = "∩", tmnm = "INTER"};  (* UOK *)

val FUNION_def = new_definition(
  "FUNION_def",
  ``FUNION f1 f2 x <=> f1 x \/ f2 x``);

val funion_symbol = UTF8.chr 0x228C
val _ = set_fixity funion_symbol (Infixl 500)
val _ = overload_on (funion_symbol, ``FUNION``)

val _ = export_theory();
