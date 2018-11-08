signature smlParser =
sig

  datatype smlexpr =
    SmlExpr of string option * (smlexpr list)
  | SmlUnit of string option

  (* parse tree *)
  val sml_propl_all_of : string -> PolyML.ptProperties list list
  
  (* information *)
  val sml_path_of : string -> string
  val reprint : string -> string option

  (* sub expression *)
  val extract_subexpr : string -> smlexpr list
  val extract_tacticl : string -> string list list

end
