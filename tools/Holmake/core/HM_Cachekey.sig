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

  (* Both [compute_for_node] and [compute_for_deps] return the
     updated graph alongside the cachekey: per-dep file hashes
     they compute get memoised onto the graph so that subsequent
     calls reusing any of the same dep files (very common when
     many targets share parent theories) avoid re-reading and
     re-hashing them. *)
  val compute_for_node :
      'a HM_DepGraph.t -> HM_DepGraph.node ->
      compute_result * 'a HM_DepGraph.t

  (* Lower-level variant: compute the cachekey for a theory target
     given its direct dependency list directly (without needing a
     node already recorded in a depgraph).  Used from the rebuild-
     decision path, where the node is about to be created, and from
     BuildCommand after a successful script run. *)
  val compute_for_deps :
      'a HM_DepGraph.t -> Holmake_tools.dep list ->
      compute_result * 'a HM_DepGraph.t

  (* Filesystem helpers for cachekey stamp files.  Each theory-target
     .dat file has a sibling .cachekey file recording the cachekey of
     the inputs that produced it, written after a successful build.
     All paths here are real FS paths, not HOL paths. *)
  val stamp_path_for_datfile : string -> string
  val read_stamp  : string -> string option
  val write_stamp : string -> string -> unit
  val remove_stamp : string -> unit

end
