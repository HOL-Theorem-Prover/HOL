signature HM_DepGraph =
sig

  type 'a t
  type dep = Holmake_tools.dep
  type dir = Holmake_tools.hmdir.t
  exception NoSuchNode
  exception DuplicateTarget
  datatype target_status =
           Pending of {needed:bool}
         | Succeeded
         | Failed of {needed:bool}
         | Running
  val is_pending : target_status -> bool
  val is_failed : target_status -> bool
  eqtype node
  datatype builtincmd = BIC_BuildScript of string | BIC_Compile
  val bic_toString : builtincmd -> string

  datatype command =
           NoCmd
         | SomeCmd of string
         | BuiltInCmd of builtincmd * Holmake_tools.include_info
  type 'a nodeInfo = { target : dep, status : target_status,
                       phony : bool, dir : dir,
                       command : command, seqnum : int, extra : 'a,
                       dependencies : (node * dep) list,
                       mtime : Time.time option,
                       local_parallelism_limit : int option }
    (* mtime is the target file's modTime at the moment the node was
       added to the graph, or NONE if the file didn't exist or the
       target is phony.  Snapshot, not live: build jobs that run
       later won't update it.  Diagnostic only -- not consulted by
       any rebuild-decision code.

       local_parallelism_limit is SOME n when the node's directory's
       Holmakefile sets `LOCAL_PARALLELISM_LIMIT = n' (n > 0).  The
       parallel scheduler refuses to dispatch this node unless the
       total number of jobs running after dispatch would be <= n. *)
  val nodeInfo_toString : 'a nodeInfo -> string
  val node_toString : node -> string
  val setStatus : target_status -> 'a nodeInfo -> 'a nodeInfo
  val node_compare : node * node -> order

  val empty : unit -> 'a t
  val add_node : 'a nodeInfo -> 'a t -> 'a t * node
  val updnode : node * target_status -> 'a t -> 'a t

  (* File-hash memo (used by HM_Cachekey to avoid re-hashing shared
     dependencies during a single Holmake invocation). *)
  val peek_file_hash : 'a t -> dep -> string option
  val set_file_hash  : 'a t -> dep -> string -> 'a t
  val nodeStatus : 'a t -> node -> target_status
  val peeknode : 'a t -> node -> 'a nodeInfo option
  val target_node : 'a t -> dep -> node option
  val size : 'a t -> int
  val listNodes : 'a t -> (node * 'a nodeInfo) list
  val find_nodes_by_command : 'a t -> dir * command -> node list
  val mkneeded : dep list -> 'a t -> 'a t
  val mk_dirneeded : Holmake_tools.hmdir.t -> 'a t -> 'a t
  val fold : (node * 'a nodeInfo -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val topo_sort : 'a t -> node list

  val find_runnable : 'a t -> (node * 'a nodeInfo) option
  val find_runnable_pred :
      ('a nodeInfo -> bool) -> 'a t -> (node * 'a nodeInfo) option
    (* Scans nodes in id order; returns the first runnable node (i.e.
       Pending{needed=true} with all deps Succeeded) for which the
       predicate also holds.  Predicate is expected to be cheap and
       free of observable side effects -- it may be invoked many
       times across successive scheduler turns and on each
       candidate. *)

  val toString : 'a t -> string
  val toJSONString : 'a t -> string

  (* first function is passed true iff build has been deemed successful *)
  val postmortem : (bool -> unit) ->
                   Holmake_tools.output_functions -> OS.Process.status * 'a t ->
                   OS.Process.status



end
