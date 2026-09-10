Theory refuteRegistrationCleanCheck
Ancestors
  refuteRegistrationClean

val type_names = List.map #1
  (Theory.types "refuteRegistrationClean")

val constant_names = List.map
  (fn tm => #Name (Term.dest_thy_const tm))
  (Theory.constants "refuteRegistrationClean")

val binding_names = List.map
  (fn ((_, name), _) => name)
  (DB.thy "refuteRegistrationClean")

val residue = type_names @ constant_names @ binding_names

val _ =
  if null residue then ()
  else
    raise Fail
      ("Refute registration export residue: " ^
       String.concatWith ", " residue)
