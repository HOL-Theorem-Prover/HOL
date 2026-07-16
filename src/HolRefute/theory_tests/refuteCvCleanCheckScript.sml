Theory refuteCvCleanCheck
Ancestors
  refuteCvClean

fun residue_name name =
  String.isSubstring "refute_cv_" name orelse
  String.isSubstring "from_" name orelse
  String.isSubstring "to_" name

val type_names = List.map #1 (Theory.types "refuteCvClean")

val constant_names = List.map
  (fn tm => #Name (Term.dest_thy_const tm))
  (Theory.constants "refuteCvClean")

val binding_names = List.map
  (fn ((_, name), _) => name)
  (DB.thy "refuteCvClean")

val bad_types = List.filter residue_name type_names
val bad_constants = List.filter residue_name constant_names
val bad_bindings = List.filter residue_name binding_names
val residue = bad_types @ bad_constants @ bad_bindings

val _ =
  if null residue then ()
  else
    raise Fail
      ("Refute cv export residue: " ^ String.concatWith ", " residue)
