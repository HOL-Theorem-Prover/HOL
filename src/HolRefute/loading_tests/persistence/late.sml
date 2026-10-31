val _ = load "refutePersistTheory"
val _ = if Option.isSome (#lookupStruct PolyML.globalNameSpace "Refute")
        then raise Fail "producer incidentally loaded Refute" else ()
val _ = load "Refute"
val _ = load "testutils"
val _ = use "checks.sml"
