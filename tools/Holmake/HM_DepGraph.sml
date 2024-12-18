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

fun command_toString NoCmd = ""
  | command_toString (SomeCmd s) = s
  | command_toString (BuiltInCmd(bic,_)) = bic_toString bic

type dir = Holmake_tools.hmdir.t
type 'a nodeInfo = { target : dep, status : target_status, extra : 'a,
                     command : command, phony : bool,
                     seqnum : int, dir : dir,
                     dependencies : (node * Holmake_tools.dep) list  }

fun fupdStatus f (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum,phony,dir,extra} = nI
  in
    {target = target, status = f status, command = command, seqnum = seqnum,
     dependencies = dependencies, phony = phony, dir = dir, extra = extra}
  end

fun setStatus s = fupdStatus (fn _ => s)

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

type 'a t = { nodes : (node, 'a nodeInfo) Map.dict,
              target_map : (dep,node) Map.dict,
              command_map : (dir * command,node list) Map.dict }


fun fold f (g:'a t) A =
    Map.foldl (fn (n,ni,acc) => f (n,ni) acc) A (#nodes g)

fun empty() : 'a t =
    { nodes = Map.mkDict node_compare,
      target_map = Map.mkDict hm_target.compare,
      command_map = Map.mkDict (pair_compare(hmdir.compare, command_compare)) }
fun fupd_nodes f ({nodes, target_map, command_map}: 'a t) : 'a t =
  {nodes = f nodes, target_map = target_map, command_map = command_map}

fun find_nodes_by_command (g : 'a t) dc =
  case Map.peek (#command_map g, dc) of
      NONE => []
    | SOME ns => ns

fun size (g : 'a t) = Map.numItems (#nodes g)
fun peeknode (g:'a t) n = Map.peek(#nodes g, n)
val empty_nodeset = Binaryset.empty (pair_compare(node_compare, String.compare))

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

fun add_node (nI : 'a nodeInfo) (g :'a t) =
  let
    fun newNode (copt : command) =
      let
        val n = size g
      in
        ({ nodes = Map.insert(#nodes g,n,nI),
           target_map = Map.insert(#target_map g, #target nI, n),
           command_map = extend_map_list (#command_map g) (#dir nI,copt) n },
         n)
      end
    val {target=tgt,dir,...} = nI
    val tmap = #target_map g
    val _ =
        case Map.peek (tmap, tgt) of
            SOME n => if #seqnum (valOf (peeknode g n)) <> #seqnum nI then ()
                      else raise DuplicateTarget
          | NONE => ()
  in
    newNode (#command nI)
  end

fun updnode (n, st) (g : 'a t) : 'a t =
  case peeknode g n of
      NONE => raise NoSuchNode
    | SOME nI => fupd_nodes (fn m => Map.insert(m, n, setStatus st nI)) g

fun find_runnable (g : 'a t) =
  let
    val sz = size g
    fun hasSucceeded (i,_) = #status (valOf (peeknode g i)) = Succeeded
    (* relying on invariant that all nodes up to size are in map *)
    fun search i =
      case peeknode g i of
          NONE => NONE
        | SOME nI =>
          if #status nI = Pending{needed=true} andalso
             List.all hasSucceeded (#dependencies nI)
          then SOME (i,nI)
          else search (i + 1)
  in
    search 0
  end

fun target_node (g:'a t) t = Map.peek(#target_map g,t)
fun listNodes (g:'a t) = Map.foldr (fn (k,v,acc) => (k,v)::acc) [] (#nodes g)

val node_toString = Int.toString

fun nodeInfo_toString (nI : 'a nodeInfo) =
  let
    open Holmake_tools
    val {target,status,command,dependencies,seqnum,phony,dir,...} = nI
  in
    tgt_toString target ^ (if phony then "[PHONY]" else "") ^
    "(" ^ Int.toString seqnum ^ ") " ^
    "deps{" ^String.concatWith "," (map (Int.toString o #1) dependencies) ^ "}"^
    status_toString status ^ " : " ^
    (case command of
         SomeCmd s => s
       | BuiltInCmd (bic,{preincludes,includes}) => "<" ^ bic_toString bic ^ ">"
       | NoCmd => "<no command>")
  end

datatype 'a applist = apNIL | apSING of 'a | ++ of ('a applist * 'a applist)
infix ++
fun ap2list apNIL A = A
  | ap2list (apSING x) A = x::A
  | ap2list (a ++ b) A = ap2list a (ap2list b A)


fun pr_list s [] = apNIL
  | pr_list s [x] = x
  | pr_list s (x::xs) = x ++ apSING s ++ pr_list s xs

fun nodeInfo_toJSON (n, nI : 'a nodeInfo) =
    let
      open Holmake_tools
      val {target,status,command,dependencies,seqnum,phony,dir,...} = nI
      fun field fnm f v = apSING ("  \"" ^ fnm ^ "\" : " ^ f v)
      fun quote f x = "\"" ^ f x ^ "\""
    in
      apSING "{\n" ++
      pr_list ",\n" [
        field "node_id" Int.toString n,
        field "target" (quote hm_target.toString) target,
        field "seqnum" Int.toString seqnum,
        field "phony" Bool.toString phony,
        field "dependencies"
              (fn ds =>
                  "[" ^
                  String.concatWith ", " (map (Int.toString o #1) ds) ^ "]")
              dependencies,
        field "command" (fn c => "\"" ^ command_toString c ^ "\"") command,
        field "dir" (quote hmdir.toString) dir,
        field "needs_rebuild" (fn s => Bool.toString (s <> Succeeded)) status
      ] ++
      apSING "\n}"
    end

fun mkneeded tgts g =
    let
      fun setneeded f n g = updnode(n,f{needed=true}) g
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
                              Pending {needed=false} => setneeded Pending n g
                            | Failed  {needed=false} => setneeded Failed  n g
                            | _ => g)
      val initial_tgts = List.mapPartial (target_node g) tgts
    in
      work (Binaryset.empty node_compare) [initial_tgts] g
    end

fun mk_dirneeded d g =
    let
      fun upd_nI nI =
          if hmdir.compare(#dir nI, d) <> EQUAL then
            case (hm_target.tgtexists_readable (#target nI), #status nI) of
                (true, Pending _) => setStatus Succeeded nI
              | (false, Pending {needed}) => setStatus(Failed{needed=needed})nI
              | _ => nI
          else nI
    in
      fupd_nodes (Map.map (fn (_,nI) => upd_nI nI)) g
    end

fun indentedlist f l =
    let
      fun recurse c A l =
          case l of
              [] => ""
            | [x] => let val s = f x
                     in
                       if c + String.size s > 80 then
                         String.concat (List.rev ("\n }\n" :: s :: "\n  " :: A))
                       else String.concat (List.rev ("\n }\n" :: s :: A))
                     end
            | x::xs => let val s = f x
                           val sz = String.size s
                       in
                         if c + sz > 78 then
                           recurse (sz + 4) (", " :: s :: "\n  " :: A) xs
                         else
                           recurse (sz + c + 2) (", " :: s :: A) xs
                       end
    in
      case l of
          [] => "{}\n"
        | _ => "{\n  " ^ recurse 2 [] l
    end

fun toString g =
    let
      open hm_target
      val (successes, others) =
          List.partition (fn (_,nI) => #status nI = Succeeded) (listNodes g)
      fun prSuccess (n,{dir,target,...}) =
          Int.toString n ^ ":" ^
          tgt_toString target ^
          (if hmdir.compare(dir,dirpart target) <> EQUAL then
             "[ run in " ^ hmdir.pretty_dir dir ^ "]"
           else "")
      fun prNode(n,nI) = "[" ^ node_toString n ^ "], " ^ nodeInfo_toString nI
    in
      "{Already built " ^
      indentedlist prSuccess successes ^ " Others:\n  " ^
      String.concatWith ",\n  " (map prNode others) ^ "\n}"
    end

fun toJSONString g =
    let
      val ns = listNodes g
      val ap = apSING "[\n" ++
               pr_list ",\n" (map nodeInfo_toJSON ns) ++
               apSING "\n]"
      val ss = ap2list ap []
    in
      String.concat ss
    end

fun postmortem (outs : Holmake_tools.output_functions) (status,g) =
  let
    val pr = tgt_toString
    val {diag,tgtfatal,...} = outs
    val diagK = diag "postmortem" o (fn x => fn _ => x)
    fun pending_or_failed ps fs ns =
        case ns of
            [] => (ps,fs)
          | (x as (n,nI))::rest => if #status nI = Failed{needed=true} then
                                     pending_or_failed ps (x::fs) rest
                                   else if #status nI = Pending{needed=true}then
                                     pending_or_failed (x::ps) fs rest
                                   else pending_or_failed ps fs rest
  in
    case pending_or_failed [] [] (listNodes g) of
        ([],[]) => OS.Process.success
      | (ps, fs) =>
        let
          fun str (n,nI) = node_toString n ^ ": " ^ nodeInfo_toString nI
          fun nocmd (_, nI) = #command nI = NoCmd
          val fs' = List.filter nocmd fs
          fun nI_target (_, nI) = #target nI
        in
          diagK ("Failed nodes: \n" ^ concatWithf str "\n" fs);
          diagK ("True pending: \n" ^ concatWithf str "\n" ps);
          if not (null fs') then
            tgtfatal ("Don't know how to build necessary target(s): " ^
                      concatWithf (tgt_toString o nI_target) ", " fs')
          else ();
          OS.Process.failure
        end

  end

structure Set = Binaryset

fun topo_sort g =
    let
      val unmarked = fold (fn (n, _) => fn A => Set.add(A,n))
                          g (Set.empty node_compare)
      fun visit (n, (tempmarked, unmarked, L)) =
          let
            val _ = not (Set.member(tempmarked, n)) orelse
                    raise Fail "Cyclic graph"
          in
            if Set.member(unmarked, n) then
              case peeknode g n of
                  NONE => raise Fail ("No node for " ^ node_toString n)
                | SOME nI =>
                  let val (temp', marked', L') =
                          List.foldl (fn ((m,nI), A) => visit(m,A))
                                     (Set.add (tempmarked, n),
                                      Set.delete(unmarked, n),
                                      L)
                                     (#dependencies nI)
                  in
                    (Set.delete(temp',n), marked', n::L')
                  end
            else (tempmarked, unmarked, L)
          end
      fun recurse (A as (tempmarked, unmarked, L)) =
          case Set.find (fn _ => true) unmarked of
              NONE => L
            | SOME n => recurse (visit(n,A))
    in
      recurse (Set.empty node_compare, unmarked, [])
    end

end
