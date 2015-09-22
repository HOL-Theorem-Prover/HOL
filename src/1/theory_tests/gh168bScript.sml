open HolKernel Parse boolLib

open gh294aTheory gh294bTheory testutils

val _ = new_theory "gh168b";

val _ = remove_type_abbrev "foo"

val tyg = type_grammar()

val _ = tprint "foo abbrev no longer parses"
val _ = (``:foo``; die "FAILED!") handle HOL_ERR _ => OK()

fun typrinttest s =
  let
    val ty = Parse.Type [QUOTE s]
  in
    tprint (standard_tpp_message s);
    if s = type_to_string ty then OK() else die "FAILED!"
  end

val _ = typrinttest ":bool -> bool"
val _ = typrinttest ":bool -> bool -> bool"
val _ = tprint "type_grammar abbrevs map is empty"
val _ = if Binarymap.numItems (type_grammar.abbreviations tyg) = 0 then OK()
        else die "FAILED!"

val _ = export_theory();
