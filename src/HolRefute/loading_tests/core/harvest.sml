(* The fixture theories load before Refute, so the theory-load hook never
   reports them; harvesting must still scan them to find the bijection of
   [refute_harvest_early] outside the type's home theory.  The checks are
   used, not compiled in, so that this file has no static Refute
   dependency. *)
val _ = load "refuteHarvestEarlyAbsTheory"
val _ = if Option.isSome (#lookupStruct PolyML.globalNameSpace "Refute")
        then raise Fail "the fixture incidentally loaded Refute" else ()
val _ = load "Refute"
val _ = load "testutils"
(* [bin/hol run] starts with no current theory, which harvesting needs *)
val _ = Thm.setCT "scratch"
val _ = use "harvest-checks.sml"
