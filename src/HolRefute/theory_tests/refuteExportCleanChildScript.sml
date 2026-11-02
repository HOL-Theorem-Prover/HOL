Theory refuteExportCleanChild
Ancestors
  refuteExportClean
Libs
  Refute

(* The successful export belongs to the wrapper, although its operator
   lives in the ancestor fixture. *)
val _ = Refute.export_registrations [``:api_local``];

(* A leaked first entry from the rejected batch would be a typedef and
   would make this explicit codata description incompatible. *)
val _ = Refute.register_codatatype
  {tyop = {Thy = "refutePersistentType", Tyop = "api_small"},
   case_const = ``api_small_case``, constructors = [``api_small_cons``],
   witness = NONE};
val missing =
  (Refute.export_registrations [``:api_missing``]; false)
  handle HOL_ERR _ => true;
val _ = if missing then ()
        else raise Fail "the rejected backend export reached a descendant";
