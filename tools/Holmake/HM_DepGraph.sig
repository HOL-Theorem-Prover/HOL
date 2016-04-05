signature HM_DepGraph =
sig

  type t
  exception NoSuchNode
  exception DuplicateTarget
  datatype target_status = Pending | Succeeded | Failed | Running
  eqtype node
  type nodeInfo = { target : string, status : target_status,
                    command : string option,
                    dependencies : node list }
  val nodeInfo_toString : nodeInfo -> string
  val setStatus : target_status -> nodeInfo -> nodeInfo
  val node_compare : node * node -> order

  val empty : t
  val add_node : nodeInfo -> t -> t * node
  val updnode : node * target_status -> t -> t
  val peeknode : t -> node -> nodeInfo option
  val target_node : t -> string -> node option
  val size : t -> int
  val listNodes : t -> nodeInfo list

  val find_runnable : t -> (node * nodeInfo) option

end
