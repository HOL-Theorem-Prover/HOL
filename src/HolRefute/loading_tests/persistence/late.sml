val _ = load (String.concat ["refute", "PersistTheory"])
val _ = if Option.isSome (#lookupStruct PolyML.globalNameSpace "Refute")
        then raise Fail "producer incidentally loaded Refute" else ()
val _ = load (String.concat ["Re", "fute"])
val _ = load "testutils"
val _ = use "checks.sml"
