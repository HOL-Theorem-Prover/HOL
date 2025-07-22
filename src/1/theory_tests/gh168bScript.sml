Theory gh168b[bare]
Ancestors
  gh294a gh294b
Libs
  HolKernel Parse boolLib testutils

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
val _ = if Binarymap.numItems (type_grammar.parse_map tyg) = 4 then OK()
        else die "FAILED!"

