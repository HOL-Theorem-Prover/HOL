Theory refutePersistCrossAType
Ancestors
  refutePersistOld
Libs
  Refute

val _ = Refute.export_typedef
  {ty = ``:persist_cross``, abs = ``persist_cross_abs``,
   rep = ``persist_cross_rep``, absrep_thms = [persist_cross_bij]};
