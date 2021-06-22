signature smlExecScripts =
sig

  val use_state0 : bool ref
  val find_heapname : string -> string
  val find_genscriptdep : string -> string list

  val buildheap_options : string ref (* see buildheap --help *)
  val buildheap_dir : string ref (* output directory for
    the standard out of exec_script and exec_tttscript *)
  val exec_script : string -> unit

  (* for tactictoe *)
  val exec_tttrecord : string -> unit
  val exec_ttteval : string -> string -> unit

end
