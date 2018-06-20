structure HM_DepGraph :> HM_DepGraph =
struct

infix |>
fun x |> f = f x

structure Map = Binarymap

datatype target_status = Pending | Succeeded | Failed | Running
fun status_toString s =
  case s of
      Succeeded => "[Succeeded]"
    | Failed => "[Failed]"
    | Running => "[Running]"
    | Pending => "[Pending]"

fun pending_dflt (s1, s2) = if s1 = s2 then s1 else Pending

exception NoSuchNode
exception DuplicateTarget
type node = int
datatype builtincmd = BIC_BuildScript of string | BIC_Compile

fun bic_toString BIC_Compile = "BIC_Compile"
  | bic_toString (BIC_BuildScript s) = "BIC_Build " ^ s

datatype command = NoCmd | SomeCmd of string | BuiltInCmd of builtincmd
type 'a nodeInfo = { target : 'a, status : target_status,
                     command : command, phony : bool,
                     seqnum : int, dir : Holmake_tools.hmdir.t,
                     dependencies : (node * string) list  }

fun setStatus s (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum,phony,dir} = nI
  in
    {target = target, status = s, command = command, seqnum = seqnum,
     dependencies = dependencies, phony = phony, dir = dir}
  end

fun addDeps0 dps {target,command,status,dependencies,seqnum,phony,dir} =
  {target = target, status = status, command = command, phony = phony,
   dependencies = dps @ dependencies, seqnum = seqnum, dir = dir}


val node_compare = Int.compare
fun bic_compare (BIC_Compile, BIC_Compile) = EQUAL
  | bic_compare (BIC_Compile, _) = LESS
  | bic_compare (BIC_BuildScript _, BIC_Compile) = GREATER
  | bic_compare (BIC_BuildScript s1, BIC_BuildScript s2) = String.compare(s1,s2)

fun command_compare (NoCmd, NoCmd) = EQUAL
  | command_compare (NoCmd, _) = LESS
  | command_compare (_, NoCmd) = GREATER
  | command_compare (SomeCmd s1, SomeCmd s2) = String.compare(s1,s2)
  | command_compare (SomeCmd _, BuiltInCmd _) = LESS
  | command_compare (BuiltInCmd _, SomeCmd _) = GREATER
  | command_compare (BuiltInCmd b1, BuiltInCmd b2) = bic_compare(b1,b2)

type t = { nodes : (node, string nodeInfo) Map.dict,
           target_map : (string,node) Map.dict,
           command_map : (command,node list) Map.dict }

fun lex_compare c (l1, l2) =
  case (l1,l2) of
      ([],[]) => EQUAL
    | ([], _) => LESS
    | (_, []) => GREATER
    | (h1::t1, h2::t2) => case c(h1,h2) of EQUAL => lex_compare c (t1,t2)
                                         | x => x

val empty = { nodes = Map.mkDict node_compare,
              target_map = Map.mkDict String.compare,
              command_map = Map.mkDict command_compare }
fun fupd_nodes f {nodes, target_map, command_map} =
  {nodes = f nodes, target_map = target_map, command_map = command_map}

fun find_nodes_by_command (g : t) c =
  case Map.peek (#command_map g, c) of
      NONE => []
    | SOME ns => ns

fun size (g : t) = Map.numItems (#nodes g)
fun peeknode (g:t) n = Map.peek(#nodes g, n)
fun pair_compare (c1,c2) ((a1,b1), (a2,b2)) =
  case c1(a1,a2) of
      EQUAL => c2(b1,b2)
    | x => x
val empty_nodeset = Binaryset.empty (pair_compare(node_compare, String.compare))

fun addDeps (n,dps) g =
  case peeknode g n of
      NONE => raise NoSuchNode
    | SOME nI =>
      fupd_nodes (fn nm => Binarymap.insert(nm,n,addDeps0 dps nI)) g

fun nodeStatus g n =
  case peeknode g n of
      NONE => raise NoSuchNode
    | SOME nI => #status nI

fun nodeset_eq (nl1, nl2) =
  let
    val ns1 = Binaryset.addList(empty_nodeset, nl1)
    val ns2 = Binaryset.addList(empty_nodeset, nl2)
  in
    Binaryset.isSubset(ns1, ns2) andalso Binaryset.isSubset(ns2, ns1)
  end

fun extend_map_list m k v =
  case Map.peek (m, k) of
      NONE => Map.insert(m, k, [v])
    | SOME vs => Map.insert(m, k, v::vs)

fun add_node (nI : string nodeInfo) (g :t) =
  let
    fun newNode (copt : command) =
      let
        val n = size g
      in
        ({ nodes = Map.insert(#nodes g,n,nI),
           target_map = Map.insert(#target_map g, #target nI, n),
           command_map = extend_map_list (#command_map g) copt n },
         n)
      end
    val tgt = #target nI
    val tmap = #target_map g
    val _ =
        case Map.peek (tmap, tgt) of
            SOME n => if #seqnum (valOf (peeknode g n)) <> #seqnum nI then ()
                      else raise DuplicateTarget
          | NONE => ()
  in
    newNode (#command nI)
  end

fun updnode (n, st) (g : t) : t =
  case peeknode g n of
      NONE => raise NoSuchNode
    | SOME nI => fupd_nodes (fn m => Map.insert(m, n, setStatus st nI)) g

fun find_runnable (g : t) =
  let
    val sz = size g
    fun hasSucceeded (i,_) = #status (valOf (peeknode g i)) = Succeeded
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

fun target_node (g:t) t = Map.peek(#target_map g,t)
fun listNodes (g:t) = Map.foldr (fn (k,v,acc) => (k,v)::acc) [] (#nodes g)

val node_toString = Int.toString

fun nodeInfo_toString tstr (nI : 'a nodeInfo) =
  let
    open Holmake_tools
    val {target,status,command,dependencies,seqnum,phony,dir} = nI
  in
    OS.Path.concat(hmdir.toString dir, tstr target) ^
    (if phony then "[PHONY]" else "") ^
    "(" ^ Int.toString seqnum ^ ") " ^
    status_toString status ^ " : " ^
    (case command of
         SomeCmd s => s
       | BuiltInCmd bic => "<Holmake: " ^ bic_toString bic ^ ">"
       | NoCmd => "<no command>")
  end

end
