signature smlExecScripts =
sig

  (* scratch output lands under aiLib.scratch_dir *)
  val use_state0 : bool ref
  val script_includes : string list ref
  val find_heapname : string -> string
  val find_genscriptdep : string -> string list

  val buildheap_options : string ref (* see buildheap --help *)
  val exec_script_in_dir : string -> string -> unit
  val exec_script : string -> unit

  (* for tactictoe *)
  val exec_tttrecord_in_dir : string -> string -> unit
  val exec_tttrecord : string -> unit
  val exec_ttteval : string -> string -> unit

end
