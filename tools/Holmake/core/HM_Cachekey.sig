signature HM_Cachekey =
sig

  datatype rebuild_strategy = datatype HM_Cachekey_dtype.rebuild_strategy

  (* Result of computing a cachekey for a theory-target node.
       Key k      : the cachekey is k.
       Missing ds : at least one dependency file does not exist or is
                    unreadable; ds lists them (each as {name, path}).
     Callers should treat Missing as a reason to rebuild. *)
  datatype compute_result =
           Key of string
         | Missing of {name : string, path : string} list

  val compute_for_node :
      'a HM_DepGraph.t -> HM_DepGraph.node -> compute_result

  (* Filesystem helpers for cachekey stamp files.  Each theory-target
     .dat file has a sibling .cachekey file recording the cachekey of
     the inputs that produced it, written after a successful build.
     All paths here are real FS paths, not HOL paths. *)
  val stamp_path_for_datfile : string -> string
  val read_stamp  : string -> string option
  val write_stamp : string -> string -> unit
  val remove_stamp : string -> unit

end
