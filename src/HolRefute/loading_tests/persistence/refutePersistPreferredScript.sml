Theory refutePersistPreferred
Ancestors
  refutePersistOld
Libs
  Refute

val persist_preferred_bij = define_new_type_bijections
  {name = "persist_preferred_bij", ABS = "persist_preferred_abs",
   REP = "persist_preferred_rep", tyax = persist_cross_TY_DEF};
val _ = Refute.export_typedef
  {ty = ``:persist_cross``, abs = ``persist_preferred_abs``,
   rep = ``persist_preferred_rep``, absrep_thms = [persist_preferred_bij]};
val _ = Theory.delete_binding "persist_preferred_bij";
