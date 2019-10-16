structure HM_DepGraph :> HM_DepGraph =
struct


open Holmake_tools
infix |>
fun x |> f = f x

structure Map = Binarymap

datatype target_status =
         Pending of {needed:bool}
       | Succeeded
       | Failed of {needed:bool}
       | Running
fun is_pending (Pending _) = true | is_pending _ = false
fun is_failed (Failed _) = true | is_failed _ = false
fun needed_string {needed} = "{needed="^Bool.toString needed^"}]"
fun status_toString s =
  case s of
      Succeeded => "[Succeeded]"
    | Failed n => "[Failed" ^ needed_string n ^ "]"
    | Running => "[Running]"
    | Pending n => "[Pending" ^ needed_string n ^ "]"

exception NoSuchNode
exception DuplicateTarget
type node = int
datatype builtincmd = BIC_BuildScript of string | BIC_Compile

fun bic_toString BIC_Compile = "BIC_Compile"
  | bic_toString (BIC_BuildScript s) = "BIC_Build " ^ s

datatype command =
         NoCmd
       | SomeCmd of string
       | BuiltInCmd of builtincmd * Holmake_tools.include_info
type 'a nodeInfo = { target : 'a, status : target_status,
                     command : command, phony : bool,
                     seqnum : int, dir : Holmake_tools.hmdir.t,
                     dependencies : (node * string) list  }

fun fupdStatus f (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum,phony,dir} = nI
  in
    {target = target, status = f status, command = command, seqnum = seqnum,
     dependencies = dependencies, phony = phony, dir = dir}
  end

fun setStatus s = fupdStatus (fn _ => s)

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
  | command_compare (BuiltInCmd (b1,_), BuiltInCmd (b2,_)) = bic_compare(b1,b2)

type t = { nodes : (node, string nodeInfo) Map.dict,
           target_map : (hmdir.t * string,node) Map.dict,
           command_map : (command,node list) Map.dict }

fun pair_compare (c1,c2) ((a1,b1), (a2,b2)) =
  case c1(a1,a2) of
      EQUAL => c2(b1,b2)
    | x => x
fun lex_compare c (l1, l2) =
  case (l1,l2) of
      ([],[]) => EQUAL
    | ([], _) => LESS
    | (_, []) => GREATER
    | (h1::t1, h2::t2) => case c(h1,h2) of EQUAL => lex_compare c (t1,t2)
                                         | x => x

val tgt_compare = pair_compare(hmdir.compare, String.compare)


val empty = { nodes = Map.mkDict node_compare,
              target_map = Map.mkDict tgt_compare,
              command_map = Map.mkDict command_compare }
fun fupd_nodes f {nodes, target_map, command_map} =
  {nodes = f nodes, target_map = target_map, command_map = command_map}

fun find_nodes_by_command (g : t) c =
  case Map.peek (#command_map g, c) of
      NONE => []
    | SOME ns => ns

fun size (g : t) = Map.numItems (#nodes g)
fun peeknode (g:t) n = Map.peek(#nodes g, n)
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
           target_map = Map.insert(#target_map g, (#dir nI, #target nI), n),
           command_map = extend_map_list (#command_map g) copt n },
         n)
      end
    val {target=tgt,dir,...} = nI
    val tmap = #target_map g
    val _ =
        case Map.peek (tmap, (dir,tgt)) of
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
          if not (is_pending (#status nI)) then search (i + 1)
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
    hmdir.toString (hmdir.extendp {base = dir, extension = tstr target}) ^
    (if phony then "[PHONY]" else "") ^
    "(" ^ Int.toString seqnum ^ ") " ^
    status_toString status ^ " : " ^
    (case command of
         SomeCmd s => s
       | BuiltInCmd (bic,{preincludes,includes}) =>
         "<Holmake: " ^ bic_toString bic ^
         ",{pres=[" ^ String.concatWith "," preincludes ^ "],incs=[" ^
         String.concatWith "," includes ^ "]}>"
       | NoCmd => "<no command>")
  end

fun make_all_needed g =
    let
      fun mkneeded (Pending _) = Pending {needed = true}
        | mkneeded s = s
    in
      fupd_nodes (Map.map (fn (_,n) => fupdStatus mkneeded n)) g
    end

fun mkneeded tgts g =
    let
      fun setneeded n g = updnode(n,Pending{needed=true}) g
      fun work visited wlist g =
          case wlist of
              [] => g
            | [] :: rest => work visited rest g
            | (n :: ns) :: rest =>
              if Binaryset.member(visited, n) then work visited (ns::rest) g
              else
                case peeknode g n of
                    NONE => raise NoSuchNode
                  | SOME nI =>
                    work (Binaryset.add(visited, n))
                         (map #1 (#dependencies nI) :: ns :: rest)
                         (case #status nI of
                              Pending {needed=false} => setneeded n g
                            | _ => g)
      val initial_tgts = List.mapPartial (target_node g) tgts
    in
      work (Binaryset.empty node_compare) [initial_tgts] g
    end

fun mk_dirneeded d g =
    let
      fun upd_nI nI = if hmdir.compare(#dir nI, d) = EQUAL andalso
                         #status nI = Pending{needed=false}
                      then
                        setStatus (Pending{needed=true}) nI
                      else nI
    in
      fupd_nodes (Map.map (fn (_,nI) => upd_nI nI)) g
    end

fun toString g =
    let
      fun prNode(n,nI) =
          "[" ^ node_toString n ^ "], " ^
          nodeInfo_toString (fn s => s) nI
    in
      "{\n  " ^
      String.concatWith ",\n  " (map prNode (listNodes g)) ^ "\n}"
    end

fun postmortem (outs : Holmake_tools.output_functions) tgts g =
  let
    fun pr s = s
    val {diag,tgtfatal,...} = outs
    val diagK = diag o (fn x => fn _ => x)
  in
    case List.filter (fn (_,nI) => #status nI <> Succeeded) (listNodes g) of
        [] => OS.Process.success
      | ns =>
        let
          fun str (n,nI) = node_toString n ^ ": " ^ nodeInfo_toString pr nI
          fun failed_nocmd (_, nI) =
            #status nI = Failed{needed=true} andalso #command nI = NoCmd
          val ns' = List.filter failed_nocmd ns
          fun nI_target (_, nI) = #target nI
        in
          diagK ("Failed nodes: \n" ^ String.concatWith "\n" (map str ns));
          if not (null ns') then
            tgtfatal ("Don't know how to build necessary target(s): " ^
                      String.concatWith ", " (map nI_target ns'))
          else ();
          OS.Process.failure
        end
  end




end
