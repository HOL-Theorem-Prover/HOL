open HolKernel Parse boolLib ;

val _ = new_theory "attr1";

val _ = ThmSetData.new_storage_attribute "test"

val PP = store_thm(
  "PP[test]",
  ``P ==> P``,
  STRIP_TAC THEN ASM_REWRITE_TAC []);

val _ = export_theory();
