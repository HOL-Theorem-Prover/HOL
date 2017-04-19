structure BuildCommand :> BuildCommand =
struct

open Systeml Holmake_tools Holmake_types
structure FileSys = OS.FileSys
structure Path = OS.Path
structure Process = OS.Process

infix |>
fun x |> f = f x

val default_holstate = Systeml.DEFAULT_STATE

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

open HM_GraphBuildJ1

datatype cmd_line = Mosml_compile of File list * string
                  | Mosml_link of string * File list
                  | Mosml_error

datatype buildresult = datatype multibuild.buildresult

fun process_mosml_args (outs:Holmake_tools.output_functions) c = let
  val {diag,...} = outs
  fun isSource t = OS.Path.ext t = SOME "sig" orelse OS.Path.ext t = SOME "sml"
  fun isObj t = OS.Path.ext t = SOME "uo" orelse OS.Path.ext t = SOME "ui"
  val toks = String.tokens (fn c => c = #" ") c
  val c = ref false
  val q = ref false
  val toplevel = ref false
  val obj = ref NONE
  val I = ref []
  val obj_files = ref []
  val src_file = ref NONE
  fun process_args [] = ()
    | process_args ("-c"::rest) = (c := true; process_args rest)
    | process_args ("-q"::rest) = (q := true; process_args rest)
    | process_args ("-toplevel"::rest) = (toplevel := true; process_args rest)
    | process_args ("-o"::arg::rest) = (obj := SOME arg; process_args rest)
    | process_args ("-I"::arg::rest) = (I := arg::(!I); process_args rest)
    | process_args (file::rest) = let
      in
        if file = HM_BaseEnv.mosml_indicator then ()
        else if isSource file then
          src_file := SOME file
        else if isObj file then
          obj_files := toFile file::(!obj_files)
        else ();
        process_args rest
      end
in
  process_args toks;
  ((case (!c, !src_file, !obj_files, !obj) of
         (true, SOME f, ofs, NONE) => Mosml_compile (List.rev ofs, f)
       | (false, NONE, ofs, SOME f) => Mosml_link (f, List.rev ofs)
       | _ => let
           fun ostring NONE = "NONE"
             | ostring (SOME s) = "SOME "^s
         in
           diag ("mosml error: c = "^Bool.toString (!c)^", src_file = "^
                 ostring (!src_file) ^ ", obj = "^ostring (!obj));
           Mosml_error
         end),
   List.rev (!I))
end;




fun posix_diagnostic stat = let
  open Posix.Process
in
  case fromStatus stat of
    W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
  | W_EXITED => "exited normally"
  | W_SIGNALED sg => "with signal " ^
                     SysWord.toString (Posix.Signal.toWord sg)
  | W_STOPPED sg => "stopped with signal " ^
                    SysWord.toString (Posix.Signal.toWord sg)
end

fun addPath I file =
  if OS.Path.isAbsolute file then
    file
  else let
      val p = List.find (fn p =>
                            FileSys.access (Path.concat (p, file ^ ".ui"), []))
                        (FileSys.getDir() :: I)
    in
      case p of
           NONE => OS.Path.concat (OS.FileSys.getDir(), file)
         | SOME p => OS.Path.concat (p, file)
    end;

fun time_max(t1,t2) = if Time.<(t1,t2) then t2 else t1

fun finish_compilation warn depMods0 filename tgt =
  case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      NONE => OS.Process.success
    | SOME "1" =>
      let
        val filename_base = OS.Path.base filename
        val depMods = List.filter (fn s => s <> filename_base) depMods0
        fun getFTime fname =
          SOME (OS.FileSys.modTime fname) handle OS.SysErr _ => NONE
        fun combine fname t =
          case getFTime fname of NONE => t | SOME t0 => time_max(t0,t)
        fun foldthis (modn, t) =
          t |> combine (modn ^ ".uo") |> combine (modn ^ ".ui")
        val startTime =
            case getFTime filename of
                NONE => (warn("Can't see base file " ^ filename ^
                              " though I just compiled it??");
                         Time.zeroTime)
              | SOME t => t
      in
        OS.FileSys.setTime (tgt, SOME (List.foldl foldthis startTime depMods));
        OS.Process.success
      end
    | SOME s =>
      (warn ("Ignoring strange value (" ^ s ^ ") in " ^
             Systeml.build_after_reloc_envvar ^ " environment variable");
       OS.Process.success)

fun poly_compile warn diag quietp file I deps = let
  val modName = fromFileNoSuf file
  val deps = let
    open Binaryset
    val dep_set0 = addList (empty String.compare, map fromFile deps)
    val {deps = extra_deps, ...} =
        Holdep.main {assumes = [], includes = I, diag = diag,
                     fname = fromFile file}
    val dep_set = addList (dep_set0, extra_deps)
  in
    foldr (fn (s,acc) => toFile s :: acc) [] dep_set
  end
  val _ = diag ("Writing "^fromFile file^" with dependencies: " ^
                String.concatWith ", " (map fromFile deps))
  fun mapthis (Unhandled _) = NONE
    | mapthis f = SOME (fromFileNoSuf f)
  val depMods = List.map (addPath I) (List.mapPartial mapthis deps)
  fun usePathVars p = holpathdb.reverse_lookup {path = p}
  val depMods = List.map usePathVars depMods
  val say = if quietp then (fn s => ())
            else (fn s => TextIO.output(TextIO.stdOut, s ^ "\n"))
  val _ = say ("HOLMOSMLC -c " ^ fromFile file)
  val filename = addPath [] (fromFile file)
in
case file of
  SIG _ =>
    (let
      val tgt = modName ^ ".ui"
      val outUi = TextIO.openOut tgt
     in
       TextIO.output (outUi, String.concatWith "\n" depMods);
       TextIO.output (outUi, "\n");
       TextIO.output (outUi, usePathVars filename ^ "\n");
       TextIO.closeOut outUi;
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| SML _ =>
    (let
      val tgt = modName ^ ".uo"
      val outUo = TextIO.openOut tgt
     in
       TextIO.output (outUo, String.concatWith "\n" depMods);
       TextIO.output (outUo, "\n");
       TextIO.output (outUo, usePathVars (addPath [] (fromFile file)) ^ "\n");
       TextIO.closeOut outUo;
       (if OS.FileSys.access (modName ^ ".sig", []) then
          ()
        else
          let val outUi = TextIO.openOut (modName ^ ".ui")
          in
            TextIO.closeOut outUi;
            ignore (finish_compilation warn depMods filename (modName ^ ".ui"))
          end);
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| _ => raise Match
end

fun list_delete x [] = []
  | list_delete x (y::ys) = if x = y then ys else y :: list_delete x ys

type build_command = {preincludes : string list, includes : string list} ->
                     Holmake_tools.buildcmds ->
                     File -> bool

fun make_build_command (buildinfo : HM_Cline.t buildinfo_t) = let
  val {optv,hmake_options,actual_overlay,envlist,quit_on_failure,outs,...} =
      buildinfo
  val hmenv = #hmenv buildinfo
  val {warn,diag,tgtfatal,...} = outs
  val keep_going = #keep_going (#core optv)
  val debug = #debug (#core optv)
  val opentheory = #opentheory (#core optv)
  val allfast = #fast (#core optv)
  val polynothol = #poly_not_hol optv
  val relocbuild = #relocbuild optv orelse
                   (case OS.Process.getEnv Systeml.build_after_reloc_envvar of
                        SOME "1" => true
                      | _ => false)
  val interactive_flag = #interactive (#core optv)
  val quiet_flag = #quiet (#core optv)
  val cmdl_HOLSTATE = #holstate optv
  val jobs = #jobs (#core optv)
  val time_limit = #time_limit optv
  val chatty = if jobs = 1 then #chatty outs else (fn _ => ())
  val info = if jobs = 1 then #info outs else (fn _ => ())

  val HOLSTATE = let
    val default =
        case cmdl_HOLSTATE of
            NONE => if polynothol then POLY else default_holstate
          | SOME s => s
  in
    case envlist "HOLHEAP" of
        [] => default
      | [x] => x
      | xs => (warn ("Can't interpret "^String.concatWith " " xs ^
                     " as a HOL HEAP spec; using default hol.builder.");
               default)
  end



  fun poly_link quietp result files =
  let
    val _ = if not quietp then
              TextIO.output(TextIO.stdOut,
                            "HOLMOSMLC -o " ^ result ^ " " ^
                            String.concatWith " "
                                              (map (fn s => s ^ ".uo") files) ^
                            "\n")
            else ()
    val out = TextIO.openOut result
    fun p s =
        (TextIO.output (out, s); TextIO.output (out, "\n"))
  in
    p "#!/bin/sh";
    p (protect(POLY) ^ " -q --gcthreads=1 " ^
       String.concatWith " " (envlist "POLY_CLINE_OPTIONS") ^
       " <<'__end-of-file__'");
    (if polynothol then
       (p "local";
        p "val dir = OS.FileSys.getDir();";
        p ("val _ = OS.FileSys.chDir (OS.Path.concat (\"" ^
                    String.toString Systeml.HOLDIR ^ "\", \"tools-poly\"));");
        p "val _ = use \"poly/poly-init2.ML\";";
        p "val _ = OS.FileSys.chDir dir;";
        p "in end;")
     else
       (p ("val _ = PolyML.SaveState.loadState \"" ^
           String.toString HOLSTATE ^ "\";\n");
        p ("val _ = List.app holpathdb.extend_db" ^
           "(holpathdb.search_for_extensions ReadHMF.find_includes " ^
           "[OS.FileSys.getDir()])\n")));
    p ("val _ = List.map load [" ^
       String.concatWith "," (List.map (fn f => "\"" ^ f ^ "\"") files) ^
       "] handle x => ((case x of Fail s => print (s^\"\\n\") | _ => ()); \
       \OS.Process.exit OS.Process.failure);");
    p "__end-of-file__";
    TextIO.closeOut out;
    Systeml.mk_xable result;
    OS.Process.success
  end handle IO.Io _ => OS.Process.failure

  fun build_command (ii as {preincludes,includes}) c arg = let
    val include_flags = preincludes @ includes
    val overlay_stringl = case actual_overlay of NONE => [] | SOME s => [s]
    exception CompileFailed
    exception FileNotFound
    val isSuccess = OS.Process.isSuccess
    fun setup_script s deps extras = let
      val scriptsml_file = SML (Script s)
      val scriptsml = fromFile scriptsml_file
      val script   = s^"Script"
      val scriptuo = script^".uo"
      val scriptui = script^".ui"
      (* first thing to do is to create the Script.uo file *)
      val b =
          case build_command ii (Compile deps) scriptsml_file of
              BR_OK => true
            | BR_Failed => false
            | BR_ClineK _ => raise Fail "Compilation resulted in commandline"
      val _ = b orelse raise CompileFailed
      val _ = info ("Linking "^scriptuo^" to produce theory-builder executable")
      val objectfiles0 =
          if allfast then ["fastbuild.uo", scriptuo]
          else if quit_on_failure then [scriptuo]
          else ["holmakebuild.uo", scriptuo]
      val objectfiles0 = extras @ objectfiles0
      val objectfiles =
        if polynothol then
          objectfiles0
        else if interactive_flag then "holmake_interactive.uo" :: objectfiles0
        else "holmake_not_interactive.uo" :: objectfiles0
    in
        ((script,[scriptuo,scriptui,script]), objectfiles)
    end
    fun run_script (script, intermediates) objectfiles expected_results =
      if isSuccess (poly_link true script (List.map OS.Path.base objectfiles))
      then let
        fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
        val _ = app safedelete expected_results
        val cline = [fullPath [OS.FileSys.getDir(), script]]
        fun cont wn res =
          let
            val _ =
                if not (isSuccess res) then
                  wn ("Failed script build for "^script^" - "^
                      posix_diagnostic res)
                else ()
            val _ = if isSuccess res orelse not debug then
                      app safedelete (script :: intermediates)
                    else ()
          in
            isSuccess res andalso
            List.all (fn file =>
                         exists_readable file orelse
                         (wn ("Script file "^script^" didn't produce "^file^
                              "; \n\
                              \  maybe need export_theory() at end of "^
                              script ^ ".sml");
                          false))
                     expected_results
          end
      in
        BR_ClineK ((script, cline), cont)
      end
      else
        (warn ("Failed to build script file, "^script^"\n"); BR_Failed)
  in
    let
    in
      case c of
          Compile deps =>
          let
            val file = fromFile arg
            val _ = exists_readable file orelse
                    (warn ("Wanted to compile "^file^
                            ", but it wasn't there\n");
                     raise FileNotFound)
            val res = poly_compile warn diag true arg include_flags deps
          in
            if OS.Process.isSuccess res then BR_OK else BR_Failed
          end
        | BuildScript (s, deps) =>
          let
            val (scriptetc,objectfiles) = setup_script s deps []
          in
            run_script scriptetc objectfiles [s^"Theory.sml", s^"Theory.sig"]
          end
        | BuildArticle (s0, deps) =>
          let
            val s = s0 ^ ".art"
            val oldscript_f = SML (Script s0)
            val fakescript_f = SML (Script s)
            val _ = Posix.FileSys.link {old = fromFile oldscript_f,
                                        new = fromFile fakescript_f }
            val loggingextras =
                case opentheory of SOME uo => [uo]
                                 | NONE => ["loggingHolKernel.uo"]
            val deps = list_delete oldscript_f deps @ [fakescript_f]
            val ((script,inters),objectfiles) =
                setup_script s deps loggingextras
          in
            run_script (script,fromFile fakescript_f :: inters) objectfiles [s]
          end
        | ProcessArticle s =>
          let
            val raw_art_file = ART (RawArticle s)
            val art_file = ART (ProcessedArticle s)
            val raw_art = fromFile raw_art_file
            val art = fromFile art_file
            val cline =
                ("/bin/sh",
                 ["/bin/sh", "-c",
                  "opentheory info --article -o " ^ art ^ " " ^ raw_art])
          in
            BR_ClineK (cline, (fn _ => OS.Process.isSuccess))
          end
    end handle CompileFailed => BR_Failed
             | FileNotFound  => BR_Failed
  end
  fun mosml_build_command hm_env {noecho, ignore_error, command = c} deps =
    let
      open Holmake_types
      val isHolmosmlcc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC-C"]) c
      val isHolmosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC"]) c
      val isMosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "MOSMLC"]) c
      val {diag,...} = outs
    in
      if isHolmosmlcc orelse isHolmosmlc orelse isMosmlc then let
        val _ = diag ("Processing mosml build command: "^c)
      in
        case process_mosml_args outs (if isHolmosmlcc then " -c " ^ c else c) of
            (Mosml_compile (objs, src), I) =>
            SOME (poly_compile warn diag (noecho orelse quiet_flag)
                               (toFile src)
                               I
                               (deps @ objs))
          | (Mosml_link (result, objs), I) =>
            let
            in
              diag ("Moscow ML command is link -o "^result^" ["^
                    String.concatWith ", " (map fromFile objs) ^ "]");
              SOME (poly_link (noecho orelse quiet_flag) result
                              (map fromFileNoSuf objs))
            end
          | (Mosml_error, _) =>
            (warn ("*** Couldn't interpret Moscow ML command: "^c);
             SOME (OS.Process.failure))
      end
      else NONE
    end
  val jobs = #jobs (#core optv)
  open HM_DepGraph
  val pr_sl = String.concatWith " "
  fun interpret_graph g =
    case List.filter (fn (_,nI) => #status nI <> Succeeded) (listNodes g) of
        [] => OS.Process.success
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
  fun interpret_bres bres =
    case bres of
        BR_OK => true
      | BR_ClineK((_,cline), k) => k warn (Systeml.systeml cline)
      | BR_Failed => false


  fun system s =
    Systeml.system_ps
      (if relocbuild then Systeml.build_after_reloc_envvar ^ "=1 " ^ s
       else s)

  val build_graph =
      if jobs = 1 then
        graphbuildj1 {
          build_command = (fn ii => fn cmds => fn f =>
                              build_command ii cmds f |> interpret_bres),
          mosml_build_command = mosml_build_command,
          outs = outs,
          keep_going = keep_going,
          quiet = quiet_flag,
          hmenv = hmenv,
          system = system }
      else
        (fn ii => fn g =>
            multibuild.graphbuild { build_command = build_command,
                                    relocbuild = relocbuild,
                                    mosml_build_command = mosml_build_command,
                                    warn = warn, tgtfatal = tgtfatal,
                                    keep_going = keep_going, diag = diag,
                                    info = #info outs,
                                    time_limit = time_limit,
                                    quiet = quiet_flag, hmenv = hmenv,
                                    jobs = jobs } ii g |> interpret_graph)
  fun extend_holpaths () =
    List.app holpathdb.extend_db
             (holpathdb.search_for_extensions
                (fn s => [])
                [OS.FileSys.getDir()])

in
  {extra_impl_deps = [Unhandled HOLSTATE],
   build_graph = (fn arg => (extend_holpaths(); build_graph arg))}
end

end (* struct *)
