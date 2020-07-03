signature smlParser =
sig

  datatype smlexp =
    SmlExp of string option * (smlexp list)
  | SmlUnit of string option

  datatype tacexp =
    SmlInfix of string * (tacexp * tacexp)
  | SmlTactical of string
  | SmlTactic of string

  (* parse tree *)
  val sml_propl_all_of : string -> PolyML.ptProperties list list

  (* information *)
  val declaration_path : string -> string
  val reprint : string -> string option

  (* sub expression *)
  val extract_smlexp : string -> smlexp list
  val extract_tacexp : string -> tacexp
  val size_of_tacexp : tacexp -> int
  val string_of_tacexp : tacexp -> string

end
