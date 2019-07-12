signature smlParser =
sig

  datatype smlexpr =
    SmlExpr of string option * (smlexpr list)
  | SmlUnit of string option

  datatype proptree =
    PropNode of PolyML.ptProperties list * (proptree list)
  | PropLeaf of PolyML.ptProperties list

  (* parse tree *)
  val sml_propl_all_of : string -> PolyML.ptProperties list list

  (* information *)
  val declaration_path : string -> string
  val reprint : string -> string option

  (* sub expression *)
  val extract_proptree : string -> proptree list
  val extract_subexpr : string -> smlexpr list
  val extract_tacticl : string -> string list list


end
