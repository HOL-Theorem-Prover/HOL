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
         | Undecided of {forced:bool}
    (* Undecided is the status a node carries while the graph is being
       built.  Whether a target needs rebuilding depends on whether its
       dependencies do, and that is not known until the walk over the
       directories has finished: see `assign_statuses'.  `forced' is
       the part of the decision that does not depend on the graph --
       the target is missing, or phony, or older than one of its
       dependencies -- recorded by whoever created the node.  No node
       is still Undecided once `assign_statuses' has run. *)
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

  val assign_statuses :
      ('a t -> (node * 'a nodeInfo) list -> {deps_unbuilt : bool} ->
       'a t * target_status)
      -> 'a t -> 'a t
    (* Replace every Undecided status with a real one, visiting nodes in
       an order that settles a node's dependencies before the node
       itself.  That is what makes the result independent of the order
       the directories were scanned in: a decision is never taken
       against a dependency whose own status is still to change.

       The argument supplies the policy.  It is handed the graph (so it
       can thread the file-hash memo), a group of nodes to be decided
       together, and whether any dependency of any of them will be
       rebuilt; it returns the status the whole group takes.  The graph
       it returns must differ only in that memo: adding or rewriting
       nodes would invalidate the traversal in progress.  Nodes
       sharing a BIC_BuildScript command form one group, because a
       single script run writes all of its theory's products: deciding
       them separately allows a .sig to be called stale while the .dat
       written beside it is called fresh.

       Statuses already decided -- placeholders for targets no
       directory in this build claims -- are left alone.  The
       theories_built count is reset, since nothing has been built at
       the point this runs. *)
  val updnode_tgtstatus : node * target_status -> 'a t -> 'a t
  val updnode_fully : node * 'a nodeInfo -> 'a t -> 'a t

  val add_dependency : node -> (node * dep) -> 'a t -> 'a t
    (* Append (dep_node, dep_target) to `node`'s `#dependencies` list.
       No-op if the edge already exists.  Used by `multibuild` to
       record deps discovered during dispatch (see the post-BIC_BuildScript
       rescan of generated `*Theory.sml`). *)

  (* File-hash memo (used by HM_Cachekey to avoid re-hashing shared
     dependencies during a single Holmake invocation). *)
  val peek_file_hash : 'a t -> dep -> string option
  val set_file_hash  : 'a t -> dep -> string -> 'a t

  val theories_built : 'a t -> int
    (* Running count of dat-product nodes whose status has transitioned
       to Succeeded during this Holmake invocation.  Maintained
       incrementally by updnode_tgtstatus / updnode_fully. *)

  val is_theory_dat_node : 'a nodeInfo -> bool
    (* True iff the node builds the dat product of a theory script. *)
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

  val find_best_runnable_pred :
      (node -> real) -> ('a nodeInfo -> bool) -> 'a t ->
      (node * 'a nodeInfo) option
    (* Ties on the smallest node id: with score ≡ 0 the result is
       identical to `find_runnable_pred`. *)

  val successor_map : 'a t -> (node, node list) Binarymap.dict
    (* Inverse of `#dependencies`. *)

  val compute_cp_weights :
      ('a nodeInfo -> real) -> 'a t -> (node -> real)
    (* Critical-path weight lookup: `cp n = cost n + max cp m` over
       successors `m`.  Unknown nodes score 0.0. *)

  val toString : 'a t -> string
  val toJSONString : 'a t -> string

  (* first function is passed true iff build has been deemed successful *)
  val postmortem : (bool -> unit) ->
                   Holmake_tools.output_functions -> OS.Process.status * 'a t ->
                   OS.Process.status



end
