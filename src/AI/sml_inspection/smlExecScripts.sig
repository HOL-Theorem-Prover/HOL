signature smlExecScripts =
sig

  (* scratch output lands under aiLib.scratch_dir *)
  val use_state0 : bool ref
  val script_includes : string list ref
  val find_heapname : string -> string
  val find_genscriptdep : string -> string list

  val buildheap_options : string ref (* see buildheap --help *)
  (* Hard wall-clock limit, in seconds, for one rewritten TacticToe theory.  The
     recording itself uses in-process tactic timeouts, but those cannot
     always stop a Poly/ML worker; this process-level guard keeps such a
     worker from wedging the whole recording run. *)
  val tttrecord_time_limit : int ref
  val exec_script_with_pid :
    (Posix.Process.pid -> unit) ->
    (Posix.Process.pid -> unit) -> string -> unit
  val exec_script_in_dir : string -> string -> unit
  val exec_script : string -> unit

  (* for tactictoe *)
  val exec_tttrecord_in_dir : string -> string -> unit
  val exec_tttrecord : string -> unit
  val exec_ttteval : string -> string -> unit

end
