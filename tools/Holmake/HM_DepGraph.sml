structure HM_DepGraph :> HM_DepGraph =
struct

datatype target_status = Pending | Succeeded | Failed | Running
exception NoSuchNode
exception DuplicateTarget
type node = int
type nodeInfo = { target : string, status : target_status,
                  command : string,
                  dependencies : node list  }

fun setStatus s {target,command,status,dependencies} =
  {target = target, status = s, command = command,
   dependencies = dependencies}

val node_compare = Int.compare

type t = (node, nodeInfo) Binarymap.dict * string Binaryset.set

val empty = (Binarymap.mkDict node_compare, Binaryset.empty String.compare)

fun size ((g,_) : t) = Binarymap.numItems g

fun add_node nI (g as (m,s):t) =
  if Binaryset.member(s, #target nI) then raise DuplicateTarget
  else
    let
      val n = size g
    in
      ((Binarymap.insert(m,n,nI), Binaryset.add(s,#target nI)), n)
    end

fun updnode (n, st) ((g,s): t) =
  case Binarymap.peek (g, n) of
      NONE => raise NoSuchNode
    | SOME nI => (Binarymap.insert(g, n, setStatus st nI), s)

fun peeknode ((g,_):t) n = Binarymap.peek(g, n)

fun find_runnable (g : t) =
  let
    val sz = size g
    fun hasSucceeded i = #status (valOf (peeknode g i)) = Succeeded
    (* relying on invariant that all nodes up to size are in map *)
    fun search i =
      case peeknode g i of
          NONE => NONE
        | SOME nI =>
          if #status nI <> Pending then search (i + 1)
          else if List.all hasSucceeded (#dependencies nI) then SOME (i,nI)
          else search (i + 1)
  in
    search 0
  end


end
