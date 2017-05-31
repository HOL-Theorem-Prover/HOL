structure HM_GraphBuildJ1 :> HM_GraphBuildJ1 =
struct

open Holmake_tools

type build_command = include_info -> buildcmds -> File -> bool
type mosml_build_command =
     Holmake_types.env ->
     {noecho : bool, ignore_error : bool, command : string} ->
     File list ->
     OS.Process.status option
type 'optv buildinfo_t = {
  optv : 'optv, hmake_options : string list,
  actual_overlay : string option,
  envlist : string -> string list,
  hmenv : Holmake_types.env,
  quit_on_failure : bool,
  outs : Holmake_tools.output_functions,
  SIGOBJ : string
}

fun extract_thypart s = (* <....>Theory.sml *)
  String.substring(s, 0, String.size s - 10)

fun fail (outs : Holmake_tools.output_functions) g =
  let
    open HM_DepGraph
    val pr_sl = String.concatWith " "
    val {diag,tgtfatal,...} = outs
  in
    case List.filter (fn (_,nI) => #status nI <> Succeeded) (listNodes g) of
        [] => raise Fail "No failing nodes in supposedly failed graph"
      | ns =>
        let
          fun str (n,nI) = node_toString n ^ ": " ^ nodeInfo_toString pr_sl nI
          fun failed_nocmd (_, nI) =
            #status nI = Failed andalso #command nI = NoCmd
          val ns' = List.filter failed_nocmd ns
          fun nI_target (_, nI) = String.concatWith " " (#target nI)
        in
          diag ("Failed nodes: \n" ^ String.concatWith "\n" (map str ns));
          if not (null ns') then
            tgtfatal ("Don't know how to build necessary target(s): " ^
                      String.concatWith ", " (map nI_target ns'))
          else ();
          OS.Process.failure
        end
  end

fun is_heap_only() =
  case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      SOME "1" => true
    | _ => false

fun graphbuildj1 static_info =
  let
    val {build_command, mosml_build_command, outs, keep_going,
         quiet, hmenv, system} = static_info
    val {warn,diag,tgtfatal,info,...} = (outs : Holmake_tools.output_functions)
    fun build_graph incinfo g =
      let
        open HM_DepGraph
        val _ = diag "Entering HMGBJ1.build_graph"
        val bc = build_command incinfo
        fun recurse retval g =
          case find_runnable g of
              NONE => (case List.find (fn (_,ni) => #status ni = Failed)
                                      (listNodes g)
                        of
                           NONE => retval
                         | SOME _ => fail outs g)
            | SOME (n, nI) =>
              let
                val deps = map #2 (#dependencies nI)
                val depfs = map toFile deps
                val target_s = target_string (#target nI)
                fun k res =
                  let
                    val g = updnode(n, if res then Succeeded else Failed) g
                  in
                    if res then recurse retval g
                    else if keep_going then recurse OS.Process.failure g
                    else fail outs g
                  end
                fun stdprocess () =
                  case #command nI of
                      BuiltInCmd =>
                      (diag("J1Build: Running built-in command on " ^
                            String.concatWith " " (#target nI));
                       case #target nI of
                           [f] =>
                           (case toFile f of
                                UI c => k (bc (Compile depfs) (SIG c))
                              | UO c => k (bc (Compile depfs) (SML c))
                              | ART (RawArticle s) =>
                                  k (bc (BuildArticle(s,depfs))
                                        (SML (Script s)))
                              | ART (ProcessedArticle s) =>
                                  k (bc (ProcessArticle s) (ART (RawArticle s)))
                              | _ => raise Fail ("bg tgt = " ^ f))
                         | [thyfile, _] =>
                           let
                             val thyname = extract_thypart thyfile
                           in
                             k (bc (BuildScript(thyname, depfs))
                                   (SML (Script thyname)))
                           end
                         | ts =>
                           raise Fail ("implicit bg targets: " ^
                                       String.concatWith ", " ts))
                    | SomeCmd c =>
                      let
                        val hypargs as {noecho,ignore_error,command=c} =
                            process_hypat_options c
                      in
                        case mosml_build_command hmenv hypargs depfs of
                            SOME r => k (OS.Process.isSuccess r)
                          | NONE =>
                            let
                              val () =
                                  if not noecho andalso not quiet then
                                    (TextIO.output(TextIO.stdOut, c ^ "\n");
                                     TextIO.flushOut TextIO.stdOut)
                                  else ()
                              val result = system c
                              val res_b = OS.Process.isSuccess result
                            in
                              if not res_b andalso ignore_error
                              then
                                (warn ("[" ^ hd (#target nI) ^
                                       "] Error (ignored)");
                                 k true)
                              else k res_b
                            end
                      end
                    | NoCmd => k true
              in
                if is_heap_only() andalso not (#phony nI) andalso
                   List.all exists_readable (#target nI)
                then
                  let
                    val _ = diag ("May not need to rebuild "^target_s)
                  in
                    case List.find
                           (fn (_, d) =>
                               List.exists (fn tgt => forces_update_of(d,tgt))
                                           (#target nI))
                           (#dependencies nI)
                     of
                        NONE => (diag ("Can skip work on "^target_s); k true)
                      | SOME (_,d) =>
                        (diag ("Dependency "^d^" forces rebuild of "^ target_s);
                         stdprocess())
                  end
                else
                  stdprocess()
              end
      in
        recurse OS.Process.success g
      end
  in
    build_graph
  end

end
