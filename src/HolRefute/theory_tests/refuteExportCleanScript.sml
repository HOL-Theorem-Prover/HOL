Theory refuteExportClean
Ancestors
  refutePersistentType
Libs
  Refute

fun symbols () =
  (Theory.types "-",
   map (#Name o Term.dest_thy_const) (Theory.constants "-"),
   map #1 (DB.thms "-"));
val original_symbols = symbols ();
val _ = Refute.export_codatatype
  {tyop = {Thy = "refutePersistentType", Tyop = "api_local"},
   case_const = ``api_local_case``, constructors = [``api_local_cons``],
   witness = NONE};
val _ = if symbols () = original_symbols then ()
        else raise Fail "export created named theory content";
val batch_failed =
  (Refute.export_registrations [``:api_small``, ``:api_missing``]; false)
  handle HOL_ERR _ => true;
val _ = if batch_failed andalso symbols () = original_symbols then ()
        else raise Fail "rejected batch changed named theory content";

val backend_failed = ref false;
fun backend_run _ _ =
  (backend_failed :=
    ((Refute.export_codatatype
       {tyop = {Thy = "refutePersistentType", Tyop = "api_missing"},
        case_const = ``api_missing_case``,
        constructors = [``api_missing_cons``], witness = NONE}; false)
      handle HOL_ERR _ => true);
   Refute.Unknown []);
val _ = Refute.register_backend
  {name = "export-hygiene", family = Refute.OtherFamily, weight = 0,
   configured = fn () => true, requires = Refute.AnyGoal,
   input = Refute.MonoInstances,
   certainty_ceiling = fn _ => fn _ => Refute.Genuine,
   run = backend_run, render = NONE};
val _ = Refute.refute
  (Refute.default_config |> Refute.upd_search
     (Refute.Only [Refute.RegisteredBackend "export-hygiene"])
   |> Refute.upd_quiet true) ``T``;
val _ = if !backend_failed andalso symbols () = original_symbols then ()
        else raise Fail "export inside a backend left theory residue";
