open HolKernel Parse boolLib

open gh294aTheory gh294bTheory testutils

val _ = new_theory "gh168c";

val tyg0 = type_grammar()
val privthy = Binarymap.find(type_grammar.privileged_abbrevs tyg0, "foo")
val unprivthy = if privthy = "gh294a" then "gh294b" else "gh294a"

val _ = remove_type_abbrev (privthy ^ "$foo")

val _ = tprint "foo abbrev no longer parses"
val _ = (``:foo``; die "FAILED!") handle HOL_ERR _ => OK()

fun typrinttest s expected =
  let
    val ty = Parse.Type [QUOTE s]
  in
    tprint (standard_tpp_message s);
    if type_to_string ty = expected then OK() else die "FAILED!"
  end

val _ = typrinttest ":bool -> bool"
                    (if unprivthy = "gh294a" then ":gh294a$foo"
                     else ":bool -> bool -> bool")
val _ = typrinttest ":bool -> bool -> bool"
                    (if unprivthy = "gh294a" then ":bool -> gh294a$foo"
                     else ":gh294b$foo")


val _ = export_theory();
