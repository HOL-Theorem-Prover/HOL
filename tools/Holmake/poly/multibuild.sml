structure multibuild =
struct

open ProcessMultiplexor HM_DepGraph Holmake_tools
type wp = HM_DepGraph.t workprovider

datatype buildresult =
         BR_OK
       | BR_ClineK of ((string * string list) * (OS.Process.status -> bool))
       | BR_Failed

fun extract_thypart s = (* <....>Theory.sml *)
  String.substring(s, 0, String.size s - 10)

fun graphbuild info incinfo g =
  let
    val { build_command, mosml_build_command, warn, tgtfatal, diag,
          keep_going, quiet, hmenv, jobs } = info
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
          in
            case #command nI of
                NoCmd => genjob (updnode (n,Succeeded) g)
              | SomeCmd s =>
                let
                  val hypargs as {noecho,ignore_error,command=c} =
                      process_hypat_options s
                in
                  case mosml_build_command hmenv hypargs depfs of
                      SOME r =>
                      let
                        val status =
                            if OS.Process.isSuccess r then Succeeded
                            else
                              (tgtfatal (String.concatWith " " (#target nI));
                               Failed)
                      in
                        k (status = Succeeded) g
                      end
                    | NONE =>
                      let
                        fun update (g, b) =
                          updnode (n, if b then Succeeded else Failed) g
                      in
                        NewJob ({tag = String.concatWith " " (#target nI),
                                 command = mk_shell_command s,
                                 update = update}, updnode(n, Running) g)
                      end
                end
              | BuiltInCmd =>
                let
                  val target_s = String.concatWith " " (#target nI)
                  fun bresk bres g =
                    case bres of
                        BR_OK => k true g
                      | BR_Failed => k false g
                      | BR_ClineK(cline, jobk) =>
                        let
                          fun b2res b = if b then OS.Process.success
                                        else OS.Process.failure
                          fun update (g, b) =
                            if jobk (b2res b) then
                              updnode(n, Succeeded) g
                            else
                              updnode(n, Failed) g
                        in
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
    do_work(worklist, text_monitor)
  end

end
