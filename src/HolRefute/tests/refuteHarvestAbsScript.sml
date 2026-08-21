Theory refuteHarvestAbs
Ancestors
  refuteHarvestType

(* [refute_harvest_deep]'s home theory ([refuteHarvestType]) has neither
   abs/rep constants nor any bijection theorem for it; both are introduced
   here instead, in a theory the type's own home does not own.  This is
   the theorem the lazy harvest scan must reach beyond home to find. *)
val _ = define_new_type_bijections
  {name = "refute_harvest_deep_absrep",
   ABS = "refute_harvest_deep_abs", REP = "refute_harvest_deep_rep",
   tyax = DB.fetch "refuteHarvestType" "refute_harvest_deep_TY_DEF"};
