signature HM_DepGraph =
sig

  type t
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
  type 'a nodeInfo = { target : 'a, status : target_status,
                       phony : bool, dir : Holmake_tools.hmdir.t,
                       command : command, seqnum : int,
                       dependencies : (node * dep) list }
  val nodeInfo_toString : ('a -> string) -> 'a nodeInfo -> string
  val node_toString : node -> string
  val setStatus : target_status -> 'a nodeInfo -> 'a nodeInfo
  val node_compare : node * node -> order

  val empty : t
  val add_node : dep nodeInfo -> t -> t * node
  val updnode : node * target_status -> t -> t
  val nodeStatus : t -> node -> target_status
  val addDeps : node * (node * dep) list -> t -> t
  val peeknode : t -> node -> dep nodeInfo option
  val target_node : t -> dep -> node option
  val size : t -> int
  val listNodes : t -> (node * dep nodeInfo) list
  val find_nodes_by_command : t -> command -> node list
  val make_all_needed : t -> t
  val mkneeded : dep list -> t -> t
  val mk_dirneeded : Holmake_tools.hmdir.t -> t -> t

  val find_runnable : t -> (node * dep nodeInfo) option

  val toString : t -> string

  val postmortem : Holmake_tools.output_functions -> OS.Process.status * t ->
                   OS.Process.status



end
