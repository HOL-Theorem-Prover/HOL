val early = Type.mk_thy_type
  {Thy = "refuteHarvestEarlyType", Tyop = "refute_harvest_early", Args = []}

val _ = testutils.tprint "a theory loaded before Refute is harvested"
val _ =
  if List.exists (fn ty => Type.compare (ty, early) = EQUAL)
       (#typedefs (Refute.harvest_registrations ()))
  then testutils.OK ()
  else testutils.die "refute_harvest_early was not harvested"
