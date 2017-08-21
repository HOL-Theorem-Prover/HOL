signature hhsExtract =
sig

  datatype hhs_subtac =
    HHSTACL of string option * (hhs_subtac list)
  | HHSLEAF of string option

  val hhs_extract : string -> string list list
  val hhs_propl_all_of : string -> PolyML.ptProperties list list
  val hhs_path_of : string -> string
  val pointer_cache_glob : (string, bool) Redblackmap.dict ref
  val extract_subterms : string -> hhs_subtac list
  val reprint : string -> string option
  
end
