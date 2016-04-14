structure BuildCommand :> BuildCommand =
struct

open Systeml Holmake_tools Holmake_types
structure FileSys = OS.FileSys
structure Path = OS.Path
structure Process = OS.Process

val default_holstate = Systeml.DEFAULT_STATE
val failed_script_cache = ref (Binaryset.empty String.compare)

datatype cmd_line = Mosml_compile of File list * string
                  | Mosml_link of string * File list
                  | Mosml_error

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

fun poly_compile quietp file I deps = let
  val modName = fromFileNoSuf file
  fun mapthis (Unhandled _) = NONE
    | mapthis f = SOME (fromFileNoSuf f)
  val depMods = List.map (addPath I) (List.mapPartial mapthis deps)
  val say = if quietp then (fn s => ())
            else (fn s => TextIO.output(TextIO.stdOut, s ^ "\n"))
  val _ = say ("HOLMOSMLC -c " ^ fromFile file)
in
case file of
  SIG _ =>
    (let val outUi = TextIO.openOut (modName ^ ".ui")
     in
       TextIO.output (outUi, String.concatWith "\n" depMods);
       TextIO.output (outUi, "\n");
       TextIO.output (outUi, addPath [] (fromFile file) ^ "\n");
       TextIO.closeOut outUi;
       OS.Process.success
     end
     handle IO.Io _ => OS.Process.failure)
| SML _ =>
    (let val outUo = TextIO.openOut (modName ^ ".uo")
     in
       TextIO.output (outUo, String.concatWith "\n" depMods);
       TextIO.output (outUo, "\n");
       TextIO.output (outUo, addPath [] (fromFile file) ^ "\n");
       TextIO.closeOut outUo;
       (if OS.FileSys.access (modName ^ ".sig", []) then
          ()
        else
          let val outUi = TextIO.openOut (modName ^ ".ui")
          in
            TextIO.closeOut outUi
          end);
       OS.Process.success
     end
     handle IO.Io _ => OS.Process.failure)
| _ => raise Match
end

type build_command = {preincludes : string list, includes : string list} ->
                     Holmake_tools.buildcmds ->
                     File -> bool

fun make_build_command (buildinfo : HM_Cline.t buildinfo_t) = let
  val {optv,hmake_options,actual_overlay,envlist,quit_on_failure,outs,...} =
      buildinfo
  val {warn,diag,...} = outs
  val debug = #debug (#core optv)
  val opentheory = #opentheory (#core optv)
  val allfast = #fast (#core optv)
  val polynothol = #poly_not_hol optv
  val interactive_flag = #interactive (#core optv)
  val quiet_flag = #quiet (#core optv)
  val cmdl_HOLSTATE = #holstate optv

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
           String.toString HOLSTATE ^ "\";\n")));
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
      val _ = not (Binaryset.member(!failed_script_cache, s)) orelse
              (print ("Not re-running "^s^"Script; believe it will fail\n");
               raise CompileFailed)
      val scriptsml_file = SML (Script s)
      val scriptsml = fromFile scriptsml_file
      val script   = s^"Script"
      val scriptuo = script^".uo"
      val scriptui = script^".ui"
      (* first thing to do is to create the Script.uo file *)
      val b = build_command ii (Compile deps) scriptsml_file
      val _ = b orelse raise CompileFailed
      val _ = print ("Linking "^scriptuo^
                     " to produce theory-builder executable\n")
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
      in ((script,scriptuo,scriptui,scriptsml,s), objectfiles) end
    fun run_script (script,scriptuo,scriptui,scriptsml,s) objectfiles
                   expected_results =
      if isSuccess (poly_link true script (List.map OS.Path.base objectfiles))
      then let
        fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
        val _ = app safedelete expected_results
        val res2 = systeml [fullPath [OS.FileSys.getDir(), script]];
        val () =
            if not (isSuccess res2) then
              (failed_script_cache := Binaryset.add(!failed_script_cache, s);
               warn ("Failed script build for "^script^" - "^
                     posix_diagnostic res2))
            else ()
        val _ = if isSuccess res2 orelse not debug then
                  app safedelete [script, scriptuo, scriptui]
                else ()
      in
        (isSuccess res2) andalso
        List.all (fn file =>
          exists_readable file orelse
          (print ("Script file "^script^" didn't produce "^file^"; \n\
                  \  maybe need export_theory() at end of "^scriptsml^"\n");
           false)) expected_results
      end
      else (print ("Failed to build script file, "^script^"\n"); false)
  in
    let
    in
      case c of
          Compile deps =>
          let
            val file = fromFile arg
            val _ = exists_readable file orelse
                    (print ("Wanted to compile "^file^
                            ", but it wasn't there\n");
                     raise FileNotFound)
            val res = poly_compile true arg include_flags deps
          in
            OS.Process.isSuccess res
          end
        | BuildScript (s, deps) =>
          let
            val (scriptetc,objectfiles) = setup_script s deps []
          in
            run_script scriptetc objectfiles [s^"Theory.sml", s^"Theory.sig"]
          end
        | BuildArticle (s, deps) =>
          let
            val loggingextras =
                case opentheory of SOME uo => [uo]
                                 | NONE => ["loggingHolKernel.uo"]
            val (scriptetc,objectfiles) = setup_script s deps loggingextras
          in
            run_script scriptetc objectfiles [s^".art"]
          end
        | ProcessArticle s => let
          val raw_art_file = ART (RawArticle s)
          val art_file = ART (ProcessedArticle s)
          val raw_art = fromFile raw_art_file
          val art = fromFile art_file
          val res = OS.Process.system
                      ("opentheory info --article -o "^art^" "^raw_art)
        in
          OS.Process.isSuccess res
        end
    end handle CompileFailed => false
             | FileNotFound  => false
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
            SOME (poly_compile (noecho orelse quiet_flag)
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
  fun build_graph g = raise Fail "Can't build from dependency graphs yet"
in
  {build_command = build_command, mosml_build_command = mosml_build_command,
   extra_impl_deps = [Unhandled HOLSTATE],
   build_graph = build_graph}
end

end (* struct *)
