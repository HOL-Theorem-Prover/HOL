structure HM_DepGraph :> HM_DepGraph =
struct

structure Map = Binarymap

datatype target_status = Pending | Succeeded | Failed | Running
exception NoSuchNode
exception DuplicateTarget
type node = int
type nodeInfo = { target : string, status : target_status,
                  command : string option,
                  dependencies : node list  }

fun setStatus s {target,command,status,dependencies} =
  {target = target, status = s, command = command,
   dependencies = dependencies}

val node_compare = Int.compare

type t = (node, nodeInfo) Map.dict * (string,node) Map.dict

val empty = (Map.mkDict node_compare, Map.mkDict String.compare)

fun size ((g,_) : t) = Map.numItems g

fun add_node nI (g as (m,s):t) =
  if isSome (Map.peek(s, #target nI)) then raise DuplicateTarget
  else
    let
      val n = size g
    in
      ((Map.insert(m,n,nI), Map.insert(s,#target nI,n)), n)
    end

fun updnode (n, st) ((g,s): t) =
  case Map.peek (g, n) of
      NONE => raise NoSuchNode
    | SOME nI => (Map.insert(g, n, setStatus st nI), s)

fun peeknode ((g,_):t) n = Map.peek(g, n)

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

fun target_node ((m,s):t) t = Map.peek(s,t)
fun listNodes (g:t) = Map.foldr (fn (k,v,acc) => v::acc) [] (#1 g)

fun status_toString s =
  case s of
      Succeeded => "[Succeeded]"
    | Failed => "[Failed]"
    | Running => "[Running]"
    | Pending => "[Pending]"


fun nodeInfo_toString {target,status,command,dependencies} =
  target ^ " " ^ status_toString status ^ " : " ^
  (case command of
       SOME s => s
     | NONE => "handled by Holmake")

end
