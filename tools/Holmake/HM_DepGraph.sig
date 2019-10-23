signature HM_DepGraph =
sig

  type 'a t
  type dep = Holmake_tools.dep
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
                       phony : bool, dir : Holmake_tools.hmdir.t,
                       command : command, seqnum : int, extra : 'a,
                       dependencies : (node * dep) list }
  val nodeInfo_toString : 'a nodeInfo -> string
  val node_toString : node -> string
  val setStatus : target_status -> 'a nodeInfo -> 'a nodeInfo
  val node_compare : node * node -> order

  val empty : unit -> 'a t
  val add_node : 'a nodeInfo -> 'a t -> 'a t * node
  val updnode : node * target_status -> 'a t -> 'a t
  val nodeStatus : 'a t -> node -> target_status
  val addDeps : node * (node * dep) list -> 'a t -> 'a t
  val peeknode : 'a t -> node -> 'a nodeInfo option
  val target_node : 'a t -> dep -> node option
  val size : 'a t -> int
  val listNodes : 'a t -> (node * 'a nodeInfo) list
  val find_nodes_by_command : 'a t -> command -> node list
  val make_all_needed : 'a t -> 'a t
  val mkneeded : dep list -> 'a t -> 'a t
  val mk_dirneeded : Holmake_tools.hmdir.t -> 'a t -> 'a t

  val find_runnable : 'a t -> (node * 'a nodeInfo) option

  val toString : 'a t -> string

  val postmortem : Holmake_tools.output_functions -> OS.Process.status * 'a t ->
                   OS.Process.status



end
