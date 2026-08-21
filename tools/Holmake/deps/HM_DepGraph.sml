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
       | Undecided of {forced:bool}
fun is_pending (Pending _) = true | is_pending _ = false
fun is_failed (Failed _) = true | is_failed _ = false
fun needed_string {needed} = "{needed="^Bool.toString needed^"}]"
fun status_toString s =
  case s of
      Succeeded => "[Succeeded]"
    | Failed n => "[Failed" ^ needed_string n ^ "]"
    | Running => "[Running]"
    | Pending n => "[Pending" ^ needed_string n ^ "]"
    | Undecided {forced} => "[Undecided{forced=" ^ Bool.toString forced ^ "}]"

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
                     dependencies : (node * Holmake_tools.dep) list,
                     mtime : Time.time option,
                     local_parallelism_limit : int option }

fun fupdStatus f (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum,phony,dir,extra,mtime,
         local_parallelism_limit} = nI
  in
    {target = target, status = f status, command = command, seqnum = seqnum,
     dependencies = dependencies, phony = phony, dir = dir, extra = extra,
     mtime = mtime, local_parallelism_limit = local_parallelism_limit}
  end

fun fupdDependencies f (nI: 'a nodeInfo) : 'a nodeInfo =
  let
    val {target,command,status,dependencies,seqnum,phony,dir,extra,mtime,
         local_parallelism_limit} = nI
  in
    {target = target, status = status, command = command, seqnum = seqnum,
     dependencies = f dependencies, phony = phony, dir = dir, extra = extra,
     mtime = mtime, local_parallelism_limit = local_parallelism_limit}
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

(* file_hashes memoises SHA1.sha1_file results during a Holmake
   invocation.  Lives on the dep graph because the graph already
   threads through every place that needs to ask "what's this dep
   file's hash?", and because (in shape) it's keyed by the same
   [dep] identifier the graph uses for target_map.  Plain dict, no
   ref: updates return a new graph in the existing functional
   style. *)
type 'a t = { nodes : (node, 'a nodeInfo) Map.dict,
              target_map : (dep,node) Map.dict,
              command_map : (dir * command,node list) Map.dict,
              file_hashes : (dep, string) Map.dict,
              theories_built : int }


fun fold f (g:'a t) A =
    Map.foldl (fn (n,ni,acc) => f (n,ni) acc) A (#nodes g)

fun empty() : 'a t =
    { nodes = Map.mkDict node_compare,
      target_map = Map.mkDict hm_target.compare,
      command_map = Map.mkDict (pair_compare(hmdir.compare, command_compare)),
      file_hashes = Map.mkDict hm_target.compare,
      theories_built = 0 }
fun fupd_nodes f ({nodes, target_map, command_map, file_hashes,
                   theories_built}: 'a t) : 'a t =
  {nodes = f nodes, target_map = target_map,
   command_map = command_map, file_hashes = file_hashes,
   theories_built = theories_built}

fun theories_built (g : 'a t) = #theories_built g

fun is_theory_dat_node (nI : 'a nodeInfo) =
    case (#command nI, hm_target.filepart (#target nI)) of
        (BuiltInCmd (BIC_BuildScript _, _), DAT _) => true
      | _ => false

fun peek_file_hash (g : 'a t) d = Map.peek (#file_hashes g, d)
fun set_file_hash (g : 'a t) d h : 'a t =
    {nodes = #nodes g, target_map = #target_map g,
     command_map = #command_map g,
     file_hashes = Map.insert (#file_hashes g, d, h),
     theories_built = #theories_built g}

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
           command_map = extend_map_list (#command_map g) (#dir nI,copt) n,
           file_hashes = #file_hashes g,
           theories_built = #theories_built g },
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

fun bump_built_count (old_nI, new_st) g =
    if #status old_nI <> Succeeded andalso new_st = Succeeded andalso
       is_theory_dat_node old_nI
    then {nodes = #nodes g, target_map = #target_map g,
          command_map = #command_map g, file_hashes = #file_hashes g,
          theories_built = #theories_built g + 1}
    else g

fun updnode_tgtstatus (n, st) (g : 'a t) : 'a t =
  case peeknode g n of
      NONE => raise NoSuchNode
    | SOME nI => bump_built_count (nI, st)
                   (fupd_nodes (fn m => Map.insert(m, n, setStatus st nI)) g)

fun updnode_fully (n, nInfo) (g : 'a t) : 'a t =
    case peeknode g n of
        NONE => raise NoSuchNode
      | SOME old_nI =>
        bump_built_count (old_nI, #status nInfo)
          (fupd_nodes (fn m => Map.insert(m, n, nInfo)) g)

fun add_dependency n (dn, dt) (g : 'a t) : 'a t =
    case peeknode g n of
        NONE => raise NoSuchNode
      | SOME nI =>
        if List.exists (fn (m,_) => m = dn) (#dependencies nI) then g
        else
          let
            (* Edges attached mid-build must not leave a node claiming to
               be up to date over something that is not: the same
               invariant `assign_statuses' establishes.  A node already
               marked Succeeded that acquires an unbuilt dependency goes
               back to being needed. *)
            val dep_unbuilt =
                case peeknode g dn of
                    NONE => raise NoSuchNode
                  | SOME dnI => #status dnI <> Succeeded
            val nI = if dep_unbuilt andalso #status nI = Succeeded then
                       setStatus (Pending{needed=true}) nI
                     else nI
          in
            fupd_nodes
              (fn m =>
                  Map.insert(m, n,
                             fupdDependencies (fn ds => (dn, dt) :: ds) nI))
              g
          end

(* Three-way probe so `find_runnable_pred`'s scan can terminate on the
   first NoNode without a second peeknode. *)
datatype 'a probe = NoNode | NotRunnable | Runnable of 'a nodeInfo
fun probe g P i =
    case peeknode g i of
        NONE => NoNode
      | SOME nI =>
        if #status nI = Pending{needed=true} andalso
           List.all (fn (j,_) => #status (valOf (peeknode g j)) = Succeeded)
                    (#dependencies nI) andalso
           P nI
        then Runnable nI
        else NotRunnable

fun find_runnable_pred P (g : 'a t) =
  let
    (* relying on invariant that all nodes up to size are in map *)
    fun search i =
      case probe g P i of
          NoNode => NONE
        | Runnable nI => SOME (i, nI)
        | NotRunnable => search (i + 1)
  in
    search 0
  end

fun find_runnable g = find_runnable_pred (fn _ => true) g

fun find_best_runnable_pred (score : node -> real) P (g : 'a t) =
  let
    val n = size g
    fun better (s, i, nI) NONE = SOME (s, i, nI)
      | better (s, i, nI) (b as SOME (sb, _, _)) =
          if Real.> (s, sb) then SOME (s, i, nI) else b
    fun step (i, best) =
        if i >= n then best
        else case probe g P i of
                 Runnable nI => step (i + 1, better (score i, i, nI) best)
               | _ => step (i + 1, best)
  in
    case step (0, NONE) of
        NONE => NONE
      | SOME (_, i, nI) => SOME (i, nI)
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

fun JSONstring s =
    let fun ctrans c =
            case c of
                #"\n" => "\\n"
              | #"\t" => "\\t"
              | #"\\" => "\\\\"
              | #"\"" => "\\\""
              | _ => if Char.ord c < 32 then
                       "\\u" ^
                       StringCvt.padLeft #"0" 4
                                         (Int.fmt StringCvt.HEX (Char.ord c))
                     else str c
    in
      "\"" ^ String.translate ctrans s ^ "\""
      (* behaves incorrectly if there are non-UTF8 high bytes in the string *)
    end

fun nodeInfo_toJSON (n, nI : 'a nodeInfo) =
    let
      open Holmake_tools
      val {target,status,command,dependencies,seqnum,phony,dir,mtime,...} = nI
      fun field fnm f v = apSING ("  \"" ^ fnm ^ "\" : " ^ f v)
      fun quote f x = JSONstring (f x)
      fun mtimeJSON NONE = "null"
        | mtimeJSON (SOME t) = Time.toString t
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
        field "command" (quote command_toString) command,
        field "dir" (quote hmdir.toString) dir,
        field "mtime" mtimeJSON mtime,
        field "needs_rebuild" (fn s => Bool.toString (s <> Succeeded)) status
      ] ++
      apSING "\n}"
    end

fun mkneeded tgts g =
    let
      fun setneeded f n g = updnode_tgtstatus(n,f{needed=true}) g
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

fun postmortem logfinished (outs : Holmake_tools.output_functions) (status,g) =
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
        ([],[]) => (logfinished true; OS.Process.success)
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
          (logfinished false; OS.Process.failure)
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

(* ----------------------------------------------------------------------
    assign_statuses

    Nodes are created Undecided because the walk that creates them
    cannot tell whether they need rebuilding: that depends on their
    dependencies, and a cross-directory target no local rule claims is
    entered as a placeholder judged on file existence alone, only
    becoming a real node when its own directory is scanned.  A decision
    taken against such a placeholder can be wrong by the time the walk
    ends, and nothing revisits it.

    So decide here instead, over the finished graph, in an order that
    settles a node's dependencies before the node.  `topo_sort' lists
    dependents ahead of what they depend on, so its reverse is the
    order wanted.

    A group is decided as a unit and at the position of its *last*
    member: every member's dependencies precede that member in the
    order, hence precede the last member too, so all of them are
    settled by then.  Earlier members are passed over -- `ready' is
    what recognises that -- rather than decided against dependencies
    that have yet to be looked at.
   ---------------------------------------------------------------------- *)
fun assign_statuses decide (g0 : 'a t) =
    let
      fun info g n = case peeknode g n of
                         NONE => raise NoSuchNode
                       | SOME nI => nI
      fun undecidedp g n =
          case #status (info g n) of Undecided _ => true | _ => false
      (* One script run writes every product of its theory, so those
         products stand or fall together. *)
      fun group_of g n =
          let val nI = info g n
          in
            case #command nI of
                BuiltInCmd (BIC_BuildScript _, _) =>
                  List.filter (undecidedp g)
                              (find_nodes_by_command g (#dir nI, #command nI))
              | _ => [n]
          end
      (* The dependencies of a group that lie outside it.  One inside
         the group is settled by this very decision, so it neither
         blocks the group nor counts against it: a starred-dep rule can
         name a product of the script it shares its command with. *)
      fun outside_deps g ns =
          let fun inside m = List.exists (fn k => k = m) ns
          in
            List.concat
              (map (fn n => List.filter (fn (m, _) => not (inside m))
                                        (#dependencies (info g n)))
                   ns)
          end
      fun settled g (m, _) = not (undecidedp g m)
      (* Undecided counts as unbuilt, which is why the straggler pass
         below is safe: it errs towards rebuilding, never towards
         reading a stale file. *)
      fun unbuilt g (m, _) = #status (info g m) <> Succeeded
      fun decide_group g ns ods =
          let
            val nIs = map (fn n => (n, info g n)) ns
            val (g', st) =
                decide g nIs {deps_unbuilt = List.exists (unbuilt g) ods}
          in
            (* `decide' only threads the file-hash memo, so the records
               read above are still current. *)
            List.foldl
              (fn ((n, nI), g) =>
                  fupd_nodes (fn m => Map.insert(m, n, setStatus st nI)) g)
              g' nIs
          end
      fun step (n, g) =
          if not (undecidedp g n) then g
          else
            let
              val ns = group_of g n
              val ods = outside_deps g ns
            in
              if List.all (settled g) ods then decide_group g ns ods else g
            end
      val order = List.rev (topo_sort g0)
      val g = List.foldl step g0 order
      (* Every group is reachable at its last member, so nothing should
         be left.  Deciding a straggler on its own anyway is the only
         one of the three outcomes that is harmless: leaving a node
         Undecided would make it unrunnable and invisible to
         `postmortem', which is the silent stale build this whole pass
         exists to prevent, and raising would fail a build over a
         graph shape that is merely unexpected. *)
      val g = List.foldl (fn (n, g) =>
                             if undecidedp g n then
                               decide_group g [n] (outside_deps g [n])
                             else g)
                         g order
    in
      (* Nothing has been built at this point, whatever the walk's
         placeholder upgrades may have counted along the way. *)
      {nodes = #nodes g, target_map = #target_map g,
       command_map = #command_map g, file_hashes = #file_hashes g,
       theories_built = 0}
    end

fun successor_map g =
    fold (fn (n, nI) => fn A =>
            List.foldl (fn ((m, _), acc) => extend_map_list acc m n)
                       A (#dependencies nI))
         g (Map.mkDict node_compare)

fun successors_of succs n =
    case Map.peek (succs, n) of NONE => [] | SOME l => l

fun compute_cp_weights (cost : 'a nodeInfo -> real) (g : 'a t) =
  let
    val succs = successor_map g
    fun succs_of n = successors_of succs n
    (* `topo_sort` returns sinks-first (head = nodes nothing else
       depends on within the reachable set), so iterating head-to-
       tail makes each node's successors' cp values already
       available when we compute the node's own. *)
    val order = topo_sort g
    val cp_map =
        List.foldl
          (fn (n, m) =>
              case peeknode g n of
                  NONE => m
                | SOME nI =>
                  let
                    val self = cost nI
                    val ss = succs_of n
                    val maxsucc =
                      List.foldl
                        (fn (j, best) =>
                            case Map.peek(m, j) of
                                NONE => best
                              | SOME v => if v > best then v else best)
                        0.0 ss
                  in
                    Map.insert(m, n, self + maxsucc)
                  end)
          (Map.mkDict node_compare)
          order
  in
    fn n => case Map.peek(cp_map, n) of NONE => 0.0 | SOME v => v
  end

end
