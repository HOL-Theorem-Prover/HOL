signature HM_DepGraph =
sig

  type t
  exception NoSuchNode
  exception DuplicateTarget
  datatype target_status = Pending | Succeeded | Failed | Running
  eqtype node
  type 'a nodeInfo = { target : 'a, status : target_status,
                       command : string list option,
                       dependencies : (node * string) list }
  val nodeInfo_toString : ('a -> string) -> 'a nodeInfo -> string
  val setStatus : target_status -> 'a nodeInfo -> 'a nodeInfo
  val node_compare : node * node -> order

  val empty : t
  val add_node : string nodeInfo -> t -> t * node
  val updnode : node * target_status -> t -> t
  val peeknode : t -> node -> string list nodeInfo option
  val target_node : t -> string -> node option
  val size : t -> int
  val listNodes : t -> string list nodeInfo list

  val find_runnable : t -> (node * string list nodeInfo) option

end
