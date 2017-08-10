signature hhsExtract =
sig

  val hhs_extract : string -> string list list
  val hhs_propl_all_of : string -> PolyML.ptProperties list list
  val hhs_path_of : string -> string
  val pointer_cache_glob : (string, bool) Redblackmap.dict ref
  
end
