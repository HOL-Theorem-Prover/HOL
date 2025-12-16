Theory gh294c[bare]
Ancestors
  gh294a gh294b
Libs
  HolKernel Parse boolLib

val _ = disable_tyabbrev_printing "foo"

val s = type_to_string ``:bool -> bool -> bool`` = ":bool -> bool -> bool"
        orelse
        raise Fail "Test fails"


