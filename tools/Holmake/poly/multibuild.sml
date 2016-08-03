structure multibuild =
struct

open ProcessMultiplexor HM_DepGraph Holmake_tools
type wp = HM_DepGraph.t workprovider

datatype buildresult =
         BR_OK
       | BR_ClineK of ((string * string list) *
                       ((string -> unit) -> OS.Process.status -> bool))
       | BR_Failed

fun extract_thypart s = (* <....>Theory.sml *)
  String.substring(s, 0, String.size s - 10)

infix ++
fun p1 ++ p2 = OS.Path.concat(p1, p2)
val loggingdir = ".hollogs"


local
  fun split p = let val {base, ext} = OS.Path.splitBaseExt p in (base, ext) end
in
  fun target_string l =
    let
      val (names, e) = ListPair.unzip (List.map split l)
      val exts = List.mapPartial (fn x => x) e
      val n = List.length exts
    in
      case names of
         [] => ""
       | [_] => List.hd l
       | h :: t => if List.all (fn x => x = h) t andalso List.length e = n
                     then if n = 2 andalso String.isSuffix "Theory" h
                            then h
                          else h ^ ".{" ^ String.concatWith "," exts ^ "}"
                   else String.concatWith " " l
    end
end

fun graphbuild optinfo incinfo g =
  let
    val _ = OS.FileSys.mkDir loggingdir handle _ => ()
    val { build_command, mosml_build_command, warn, tgtfatal, diag,
          keep_going, quiet, hmenv, jobs, info, time_limit } = optinfo
    val safetag = String.map (fn #"/" => #"-" | c => c)
    val monitor =
        MB_Monitor.new {info = info,
                        warn = warn,
                        genLogFile = (fn {tag} => loggingdir ++ safetag tag),
                        keep_going = keep_going,
                        time_limit = time_limit}
    fun genjob g =
      case find_runnable g of
          NONE => NoMoreJobs g
        | SOME (n,nI) =>
          let
            val _ = diag ("Found runnable node "^node_toString n)
            fun k b g =
              if b orelse keep_going then
                genjob (updnode(n, if b then Succeeded else Failed) g)
              else GiveUpAndDie g
            val depfs = map (toFile o #2) (#dependencies nI)
            val _ = #status nI = Pending orelse
                    raise Fail "runnable not pending"
            val target_s = target_string (#target nI)
          in
            case #command nI of
                NoCmd => genjob (updnode (n,Succeeded) g)
              | SomeCmd c =>
                let
                  val hypargs as {noecho,ignore_error,command=c} =
                      process_hypat_options c
                  val hypargs = {noecho=true,ignore_error=ignore_error,command=c}
                  fun error b =
                    if b then Succeeded
                    else if ignore_error then
                      (warn ("Ignoring error building " ^ target_s);
                       Succeeded)
                    else Failed
                in
                  case mosml_build_command hmenv hypargs depfs of
                      SOME r => k (error (OS.Process.isSuccess r) = Succeeded) g
                    | NONE =>
                      let
                        fun update (g, b) = updnode (n, error b) g
                      in
                        NewJob ({tag = target_s,
                                 command = mk_shell_command c,
                                 update = update}, updnode(n, Running) g)
                      end
                end
              | BuiltInCmd =>
                let
                  fun bresk bres g =
                    case bres of
                        BR_OK => k true g
                      | BR_Failed => k false g
                      | BR_ClineK(cline, jobk) =>
                        let
                          fun b2res b = if b then OS.Process.success
                                        else OS.Process.failure
                          fun update (g, b) =
                            if jobk (fn s => ()) (b2res b) then
                              updnode(n, Succeeded) g
                            else
                              updnode(n, Failed) g
                          fun cline_str (c,l) = "["^c^"] " ^
                                                String.concatWith " " l
                        in
                          diag ("New graph job for "^target_s^
                                " with c/line: " ^ cline_str cline);
                          NewJob({tag = target_s,
                                  command = cline,
                                  update = update}, updnode(n, Running) g)
                        end
                  val bc = build_command incinfo
                  val _ = diag ("Handling builtin command for "^target_s)
                in
                  case #target nI of
                      [f] => (case toFile f of
                                  UI c => bresk (bc (Compile depfs) (SIG c)) g
                                | UO c => bresk (bc (Compile depfs) (SML c)) g
                                | ART (RawArticle s) =>
                                    bresk (bc (BuildArticle(s,depfs))
                                              (SML (Script s)))
                                          g
                                | ART (ProcessedArticle s) =>
                                    bresk (bc (ProcessArticle s)
                                              (ART (RawArticle s)))
                                          g
                                | _ => raise Fail ("bg tgt = " ^ f))
                    | [thyfile, _] =>
                      let
                        val thyname = extract_thypart thyfile
                      in
                        bresk (bc (BuildScript(thyname, depfs))
                                  (SML (Script thyname)))
                              g
                      end
                    | ts =>
                      raise Fail ("implicit bg targets: " ^
                                  String.concatWith ", " ts)
                end
          end
    val worklist =
        new_worklist {worklimit = jobs,
                      provider = { initial = g, genjob = genjob }}
  in
    do_work(worklist, monitor)
  end

end
