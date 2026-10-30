Theory refuteExportRetired
Ancestors
  refutePersistentType
Libs
  Refute

val _ = new_constant ("retired_case",
  ``:api_missing -> (api_missing -> 'a) -> 'a``);
val _ = Refute.register_codatatype
  {tyop = {Thy = "refutePersistentType", Tyop = "api_missing"},
   case_const = ``retired_case``, constructors = [``api_missing_cons``],
   witness = NONE};
val _ = Refute.register_codatatype
  {tyop = {Thy = "refutePersistentType", Tyop = "api_small"},
   case_const = ``api_small_case``, constructors = [``api_small_cons``],
   witness = NONE};
val _ = Refute.export_registrations [``:api_missing``, ``:api_small``];
val _ = Theory.delete_const "retired_case";
