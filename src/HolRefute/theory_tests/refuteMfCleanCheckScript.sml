Theory refuteMfCleanCheck
Ancestors
  refuteMfClean

val type_names = List.map #1 (Theory.types "refuteMfClean")

val constant_names = List.map
  (fn tm => #Name (Term.dest_thy_const tm))
  (Theory.constants "refuteMfClean")

val binding_names = List.map
  (fn ((_, name), _) => name)
  (DB.thy "refuteMfClean")

val residue = type_names @ constant_names @ binding_names

val _ =
  if null residue then ()
  else
    raise Fail
      ("Refute MF export residue: " ^ String.concatWith ", " residue)
