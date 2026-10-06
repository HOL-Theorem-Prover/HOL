Theory refutePersistCrossBCodata
Ancestors
  refutePersistOld
Libs
  Refute

val _ = Refute.export_codatatype
  {tyop = {Thy = "refutePersistOld", Tyop = "persist_cross"},
   case_const = ``persist_cross_case``,
   constructors = [``persist_cross_cons``], witness = NONE};
