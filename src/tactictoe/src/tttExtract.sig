signature tttExtract =
sig

  datatype ttt_subtac =
    HHSTACL of string option * (ttt_subtac list)
  | HHSLEAF of string option

  val ttt_extract : string -> string list list
  val ttt_propl_all_of : string -> PolyML.ptProperties list list
  val ttt_path_of : string -> string
  val extract_subterms : string -> ttt_subtac list
  val reprint : string -> string option

end
