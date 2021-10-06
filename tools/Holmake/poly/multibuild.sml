structure multibuild =
struct

open ProcessMultiplexor HM_DepGraph Holmake_tools

type 'a mosml_build_command = 'a HM_GraphBuildJ1.mosml_build_command
datatype buildresult =
         BR_OK
       | BR_ClineK of { cline : string * string list,
                        job_kont : (string -> unit) -> OS.Process.status ->
                                   bool,
                        other_nodes : HM_DepGraph.node list }
       | BR_Failed

val RealFail = Failed{needed=true}
structure Map = Binarymap

fun fupdkey m f k dflt =
    case Map.peek (m,k) of
        NONE => Map.insert(m,k,dflt)
      | SOME v => Map.insert(m,k,f v)

fun lmap_insert k v m =
    fupdkey m (fn l => v::l) k [v]

infix ++
fun p1 ++ p2 = OS.Path.concat(p1, p2)
val loggingdir = ".hollogs"

fun graph_dirinfo g =
    let
      fun foldthis (_, nI) A =
          case #status nI of
              Pending {needed=true} => fupdkey A (fn n => n + 1) (#dir nI) 1
            | _ => A
    in
      HM_DepGraph.fold foldthis g (Map.mkDict Holmake_tools.hmdir.compare)
    end

fun is_multidir gdi =
    Map.numItems gdi > 1 orelse
    (Map.numItems gdi = 1 andalso
     Binarymap.peek(gdi, hmdir.curdir()) = NONE)

fun build_predmap g =
    let
      fun foldthis (n, nI) A =
          List.foldl (fn ((sn,_), A) => lmap_insert sn n A) A (#dependencies nI)
    in
      HM_DepGraph.fold foldthis g (Binarymap.mkDict node_compare)
    end




fun graphbuild optinfo g =
  let
    val { build_command,
          mosml_build_command : GraphExtra.t mosml_build_command,
          warn, tgtfatal, diag,
          keep_going, quiet, hmenv, jobs, info, time_limit,
          relocbuild } = optinfo
    val _ = diag "Starting graphbuild"
    val dirmap = graph_dirinfo g
    fun dropthySuffix s =
        if List.exists
             (fn sfx => String.isSuffix ("Theory." ^ sfx) s)
             ["dat", "sml", "sig"]
        then String.substring(s,0,String.size s - 4)
        else s
    fun safetag d t =
        String.map (fn #"/" => #"-" | c => c) (dropthySuffix t)
    fun genLF {tag, dir} =
        let
          val ldir = dir ++ loggingdir
          val _ = OS.FileSys.mkDir ldir handle _ => ()
        in
          ldir ++ safetag dir tag
        end

    val (monitor, {bold,green,red,coloured_info = info}) =
        MB_Monitor.new {info = info, warn = warn, genLogFile = genLF,
                        time_limit = time_limit,
                        multidir = is_multidir dirmap}

    fun dircomplete dir (good, bad) t =
        let
          val pfx0 = bold ("Finished " ^ hmdir.pretty_dir dir)
          val timetaken = "(" ^ Time.toString t ^ "s)"
          val pfx = if good > 0 orelse bad > 0 then
                      pfx0 ^ " [" ^
                      (if good > 0 then
                         "#theories: " ^ green (Int.toString good) ^
                         (if bad > 0 then "; " else "")
                       else "") ^
                      (if bad > 0 then
                         "#fails: " ^ red (Int.toString bad)
                       else "") ^ "]"
                    else pfx0
        in
          info (pfx,timetaken)
        end

    fun tgtcompletion_cb dirmap =
        if not (is_multidir dirmap) then fn _ => ()
        else
          let
            fun foldthis (d,n,A) =
                (diag (hmdir.pretty_dir d ^ " has " ^ Int.toString n ^
                       " targets to build");
                 Map.insert(A, d, {good = ref 0, bad = ref 0, tgt = n,
                                   goodthys = ref 0,
                                   elapsed = ref Time.zeroTime}))
            val dirprogress_map =
                Map.foldl foldthis (Map.mkDict hmdir.compare) dirmap
          in
            fn (dir, n, nthys, goodp, t) =>
               let
                 val {tgt,good,bad,goodthys,elapsed} =
                     Map.find(dirprogress_map, dir)
                 val _ = if goodp then (good := !good + n;
                                        goodthys := !goodthys + nthys)
                         else bad := !bad + n
                 val _ = elapsed := Time.+(!elapsed, t)
               in
                 if !good + !bad >= tgt then
                   dircomplete dir (!goodthys,!bad) (!elapsed)
                 else ()
               end
          end



    val env =
        (if relocbuild then [Systeml.build_after_reloc_envvar^"=1"] else []) @
        Posix.ProcEnv.environ()
    fun cline_to_command (s, args) = {executable = s, nm_args = args, env = env}
    fun shell_command s =
      {executable = "/bin/sh", nm_args = ["/bin/sh", "-c", s], env = env}

    val tgtcomplete = tgtcompletion_cb dirmap
    fun really_needed nI = #status nI = Pending{needed=true}
    fun b2n true = 1 | b2n false = 0
    fun count_theories_needed0 (A as (thys,nd)) ns =
        case ns of
            [] => A
          | n::rest =>
            (case peeknode g n of
                 NONE => count_theories_needed0 A rest
               | SOME nI =>
                 count_theories_needed0
                   (thys +
                    b2n (String.isSuffix "Theory.dat"
                                         (hm_target.toString (#target nI))),
                    nd + b2n (really_needed nI))
                   rest)
    val count_theories_needed = count_theories_needed0 (0,0)

    fun genjob (g,ok) =
      case (ok,find_runnable g) of
          (false, _) => GiveUpAndDie (g, false)
       |  (true, NONE) => NoMoreJobs (g, ok)
       |  (true, SOME (n,nI : GraphExtra.t nodeInfo)) =>
          let
            val _ = diag ("Found runnable node "^node_toString n)
            val extra = #extra nI
            val needed = #status nI = Pending{needed=true}
            fun eCompile ds = Compile(ds, extra)
            fun eBuildScript (s,deps) = BuildScript(s,deps,extra)
            fun eBuildArticle (s,deps) = BuildArticle(s,deps,extra)
            fun eProcessArticle s = ProcessArticle(s,extra)
            val dir = Holmake_tools.hmdir.toAbsPath (#dir nI)
            fun k b g =
                (if needed then tgtcomplete (#dir nI, 1, 0, b, Time.zeroTime)
                 else ();
                 if b orelse keep_going then
                   genjob (updnode(n, if b then Succeeded else RealFail) g,
                           true)
                 else GiveUpAndDie (g, ok))
            val deps = map #2 (#dependencies nI)
            val _ = is_pending (#status nI) orelse
                    raise Fail "runnable not pending"
            val target_s = tgt_toString (#target nI)
            val tag = if OS.Path.dir target_s = dir then OS.Path.file target_s
                      else target_s
            fun stdprocess() =
              case #command nI of
                  NoCmd => genjob (updnode (n,Succeeded) g, true)
                | cmd as SomeCmd c =>
                  let
                    val hypargs as {noecho,ignore_error,command=c} =
                        process_hypat_options c
                    val hypargs =
                        {noecho=true,ignore_error=ignore_error,command=c}
                    fun error b =
                      if b then Succeeded
                      else if ignore_error then
                        (warn ("Ignoring error executing: " ^ c);
                         Succeeded)
                      else RealFail
                  in
                    case pushdir dir
                                 (mosml_build_command hmenv extra hypargs) deps
                     of
                        SOME r =>
                          k (error (OS.Process.isSuccess r) = Succeeded) g
                      | NONE =>
                        let
                          val others = find_nodes_by_command g (#dir nI, cmd)
                          val _ = diag ("Found nodes " ^
                                        String.concatWith ", "
                                           (map node_toString others) ^
                                        " with duplicate commands")
                          fun updall (g, st) =
                            List.foldl (fn (n, g) => updnode (n, st) g)
                                       g
                                       others
                          val (thycount,neededi) = count_theories_needed others
                          fun update ((g,ok), b, t) =
                              let
                                val status = error b
                                val g' = updall (g, status)
                                val ok' = status = Succeeded orelse keep_going
                                val _ =
                                    tgtcomplete(#dir nI, neededi, thycount,
                                                ok, t)
                              in
                                (g',ok')
                              end
                        in
                          NewJob ({tag = tag, command = shell_command c,
                                   update = update, dir = dir},
                                  (updall(g, Running), true))
                        end
                  end
                | BuiltInCmd (bic,incinfo) =>
                  let
                    val _ = diag ("Setting up for target >" ^ target_s ^
                                  "< with bic " ^ bic_toString bic)
                    fun bresk bres g =
                      case bres of
                          BR_OK => k true g
                        | BR_Failed => k false g
                        | BR_ClineK{cline, job_kont, other_nodes} =>
                          let
                            val (thyc,ndi) = count_theories_needed other_nodes
                            fun b2res b = if b then OS.Process.success
                                          else OS.Process.failure
                            fun updall s g =
                              List.foldl (fn (n,g) => updnode(n,s) g)
                                         g
                                         other_nodes
                            fun update ((g,ok), b, t) =
                              if job_kont (fn s => ()) (b2res b) then
                                (tgtcomplete(#dir nI, ndi, thyc, true, t);
                                 (updall Succeeded g, true))
                              else
                                (tgtcomplete(#dir nI, ndi, thyc, false, t);
                                 (updall RealFail g, keep_going))
                            fun cline_str (c,l) = "["^c^"] " ^
                                                  String.concatWith " " l
                          in
                            diag ("New graph job for "^target_s^
                                  " with c/line: " ^ cline_str cline);
                            diag ("All nodes are: "^
                                  String.concatWith ", "
                                        (map node_toString other_nodes));
                            NewJob({tag = tag, dir = dir,
                                    command = cline_to_command cline,
                                    update = update},
                                   (updall Running g, true))
                          end
                    fun bc c f = pushdir dir (build_command g incinfo c) f
                    val _ = diag ("Handling builtin command " ^
                                  bic_toString bic ^ " for "^target_s)
                  in
                    case bic of
                        BIC_Compile =>
                        (case toFile target_s of
                             UI c => bresk (bc (eCompile deps) (SIG c)) g
                           | UO c => bresk (bc (eCompile deps) (SML c)) g
                           | ART (RawArticle s) =>
                               bresk (bc (eBuildArticle(s,deps))
                                         (SML (Script s)))
                                     g
                           | ART (ProcessedArticle s) =>
                               bresk (bc (eProcessArticle s)
                                         (ART (RawArticle s)))
                                     g
                           | _ => raise Fail ("bg tgt = " ^ target_s))
                      | BIC_BuildScript thyname =>
                          bresk (bc (eBuildScript(thyname, deps))
                                    (SML (Script thyname)))
                                g
                  end
          in
            if not (#phony nI) andalso
               hm_target.tgtexists_readable (#target nI) andalso
               #seqnum nI = 0
               (* necessary to avoid dropping out of a multi-command execution
                  part way through *)
            then
              let
                val _ = diag ("May not need to rebuild "^target_s)
              in
                case List.find
                       (fn (_, d) => depforces_update_of(d,#target nI))
                       (#dependencies nI)
                 of
                    NONE => (diag ("Can skip work on "^target_s);
                             genjob (updnode (n, Succeeded) g, true))
                  | SOME (_,d) =>
                    (diag ("Dependency " ^ tgt_toString d ^
                           " forces rebuild of "^ target_s);
                     stdprocess())
              end
            else
              stdprocess()
          end
    val worklist =
        new_worklist {worklimit = jobs,
                      provider = { initial = (g,true), genjob = genjob }}
  in
    do_work(worklist, monitor)
  end

end
