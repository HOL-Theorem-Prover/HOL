structure multibuild =
struct

open ProcessMultiplexor HM_DepGraph Holmake_tools
type wp = HM_DepGraph.t workprovider

fun extract_thypart s = (* <....>Theory.sml *)
  String.substring(s, 0, String.size s - 10)

fun graphbuild info incinfo g : wp =
  let
    val { build_command, mosml_build_command, warn, tgtfatal, diag,
          keep_going, quiet, hmenv, jobs } = info
    fun genjob g =
      case find_runnable g of
          NONE => NoMoreJobs
        | SOME (n,nI) =>
          let
            fun k b g =
              if b orelse keep_going then
                genjob (updnode(n, if b then Succeeded else Failed) g)
              else GiveUpAndDie
            val depfs = map (toFile o #2) (#dependencies nI)
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
                  val bc = build_command incinfo
                in
                  case #target nI of
                      [f] => (case toFile f of
                                  UI c => k (bc (Compile depfs) (SIG c)) g
                                | UO c => k (bc (Compile depfs) (SML c)) g
                                | _ => raise Fail ("bg tgt = " ^ f))
                    | [thyfile, _] =>
                      let
                        val thyname = extract_thypart thyfile
                      in
                        k (bc (BuildScript(thyname, depfs))
                              (SML (Script thyname)))
                          g
                      end
                    | ts =>
                      raise Fail ("implicit bg targets: " ^
                                  String.concatWith ", " ts)
                end
          end
  in
    { initial = g, genjob = genjob }
  end

end
