signature HM_DepGraph =
sig

  type t
  exception NoSuchNode
  exception DuplicateTarget
  datatype target_status = Pending | Succeeded | Failed | Running
  eqtype node
  datatype builtincmd = BIC_BuildScript of string | BIC_Compile
  val bic_toString : builtincmd -> string

  datatype command = NoCmd | SomeCmd of string | BuiltInCmd of builtincmd
  type 'a nodeInfo = { target : 'a, status : target_status,
                       phony : bool, dir : Holmake_tools.hmdir.t,
                       command : command, seqnum : int,
                       dependencies : (node * string) list }
  val nodeInfo_toString : ('a -> string) -> 'a nodeInfo -> string
  val node_toString : node -> string
  val setStatus : target_status -> 'a nodeInfo -> 'a nodeInfo
  val node_compare : node * node -> order

  val pending_dflt: target_status * target_status -> target_status

  val empty : t
  val add_node : string nodeInfo -> t -> t * node
  val updnode : node * target_status -> t -> t
  val nodeStatus : t -> node -> target_status
  val addDeps : node * (node * string) list -> t -> t
  val peeknode : t -> node -> string nodeInfo option
  val target_node : t -> string -> node option
  val size : t -> int
  val listNodes : t -> (node * string nodeInfo) list
  val find_nodes_by_command : t -> command -> node list

  val find_runnable : t -> (node * string nodeInfo) option

end
