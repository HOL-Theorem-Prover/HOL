signature smlExecScripts =
sig

  val find_heapname : string -> string
  val find_genscriptdep : string -> string list

  val buildheap_options : string ref (* see buildheap --help *)
  val buildheap_dir : string ref (* output directory for
    the standard out of exec_script and exec_tttscript *)
  val exec_script : string -> unit
  val exec_tttscript : string -> unit (* for tactictoe *)

end
