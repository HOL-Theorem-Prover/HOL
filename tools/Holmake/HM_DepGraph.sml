structure HM_DepGraph :> HM_DepGraph =
struct

structure Map = Binarymap

datatype target_status = Pending | Succeeded | Failed | Running
exception NoSuchNode
exception DuplicateTarget
type node = int
datatype command = NoCmd | SomeCmd of string | BuiltInCmd
type 'a nodeInfo = { target : 'a, status : target_status,
                     command : command,
                     seqnum : int,
                     dependencies : (node * string) list  }

fun lift {target,status,command,dependencies,seqnum} =
  {target = [target], status = status, command = command,
   dependencies = dependencies, seqnum = seqnum}

fun setStatus s (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum} = nI
  in
    {target = target, status = s, command = command, seqnum = seqnum,
     dependencies = dependencies}
  end

fun addTarget tgt {target,command,status,dependencies,seqnum} =
  {target = tgt :: target, status = status, command = command,
   dependencies = dependencies, seqnum = seqnum}

val node_compare = Int.compare

type t = { nodes : (node, string list nodeInfo) Map.dict,
           target_map : (string,node) Map.dict,
           command_map : (string, node) Map.dict }

fun lex_compare c (l1, l2) =
  case (l1,l2) of
      ([],[]) => EQUAL
    | ([], _) => LESS
    | (_, []) => GREATER
    | (h1::t1, h2::t2) => case c(h1,h2) of EQUAL => lex_compare c (t1,t2)
                                         | x => x

val empty = { nodes = Map.mkDict node_compare,
              target_map = Map.mkDict String.compare,
              command_map = Map.mkDict String.compare }
fun fupd_nodes f {nodes, target_map, command_map} =
  {nodes = f nodes, target_map = target_map, command_map = command_map}

fun size (g : t) = Map.numItems (#nodes g)
fun peeknode (g:t) n = Map.peek(#nodes g, n)
fun pair_compare (c1,c2) ((a1,b1), (a2,b2)) =
  case c1(a1,a2) of
      EQUAL => c2(b1,b2)
    | x => x
val empty_nodeset = Binaryset.empty (pair_compare(node_compare, String.compare))

fun nodeset_eq (nl1, nl2) =
  let
    val ns1 = Binaryset.addList(empty_nodeset, nl1)
    val ns2 = Binaryset.addList(empty_nodeset, nl2)
  in
    Binaryset.isSubset(ns1, ns2) andalso Binaryset.isSubset(ns2, ns1)
  end

fun replace_last2 sfx s =
  let
    val root = String.substring (s, 0, String.size s - 2)
  in
    root ^ sfx
  end
fun file_pair s =
  if String.isSuffix "Theory.sml" s then SOME (replace_last2 "ig" s)
  else if String.isSuffix "Theory.sig" s then SOME (replace_last2 "ml" s)
  else NONE

fun add_node (nI : string nodeInfo) (g :t) =
  let
    fun newNode (copt : command) =
      let
        val n = size g
      in
        ({ nodes = Map.insert(#nodes g,n,lift nI),
           target_map = Map.insert(#target_map g, #target nI, n),
           command_map = case copt of
                             SomeCmd c => Map.insert(#command_map g, c, n)
                           | _ => #command_map g },
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
    case #command nI of
        copt as SomeCmd c =>
        (case Map.peek(#command_map g, c) of
             NONE => newNode copt
           | SOME n =>
             let val nI' = valOf (peeknode g n)
             in
               if nodeset_eq(#dependencies nI, #dependencies nI') then
                 let
                   val nI'' = addTarget tgt nI'
                 in
                   ({ nodes = Map.insert(#nodes g, n, nI''),
                      target_map = Map.insert(tmap, tgt, n),
                      command_map = #command_map g }, n)
                 end
               else newNode copt
             end)
        | BuiltInCmd =>
          (case file_pair tgt of
               SOME tgt' =>
               (case Map.peek(tmap, tgt') of
                    NONE =>
                    let
                      val n = size g
                      val nI' = addTarget tgt' (lift nI)
                    in
                      ({ nodes = Map.insert(#nodes g, n, nI'),
                         target_map = Map.insert(Map.insert(tmap, tgt, n),
                                                 tgt', n),
                         command_map = #command_map g },
                       n)
                    end
                  | SOME n =>
                    let
                      val nI' = valOf (peeknode g n)
                    in
                      ({ nodes = Map.insert(#nodes g, n, addTarget tgt nI'),
                         target_map = Map.insert(tmap, tgt, n),
                         command_map = #command_map g }, n)
                    end)
             | NONE => newNode (#command nI))
          | NoCmd => newNode NoCmd
  end

fun updnode (n, st) (g : t) =
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
fun listNodes (g:t) = Map.foldr (fn (k,v,acc) => v::acc) [] (#nodes g)

fun status_toString s =
  case s of
      Succeeded => "[Succeeded]"
    | Failed => "[Failed]"
    | Running => "[Running]"
    | Pending => "[Pending]"


fun nodeInfo_toString tstr (nI : 'a nodeInfo) =
  let
    val {target,status,command,dependencies,seqnum} = nI
  in
    tstr target ^ "(" ^ Int.toString seqnum ^ ") " ^ status_toString status ^ " : " ^
    (case command of
         SomeCmd s => s
       | BuiltInCmd => "<handled by Holmake>"
       | NoCmd => "<no command>")
  end

end
