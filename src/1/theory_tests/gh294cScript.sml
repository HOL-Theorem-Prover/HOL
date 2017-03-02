open HolKernel Parse boolLib

open gh294aTheory gh294bTheory

val _ = new_theory "gh294c";

val _ = disable_tyabbrev_printing "foo"

val s = type_to_string ``:bool -> bool -> bool`` = ":bool -> bool -> bool"
        orelse
        raise Fail "Test fails"


val _ = export_theory();
