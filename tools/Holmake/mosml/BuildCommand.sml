structure BuildCommand :> BuildCommand =
struct

open Systeml Holmake_tools Holmake_types
structure FileSys = OS.FileSys
structure Path = OS.Path
structure Process = OS.Process

open HM_GraphBuildJ1

val MOSMLDIR0 = Systeml.MOSMLDIR;

fun variant str =  (* get an unused file name in the current directory *)
 if FileSys.access(str,[])
 then let fun vary i =
           let val s = str^Int.toString i
           in if FileSys.access(s,[])  then vary (i+1) else s
           end
      in vary 0
      end
 else str;

fun includify [] = []
  | includify (h::t) = "-I" :: h :: includify t

val SYSTEML = Systeml.systeml
val UNQUOTER  = xable_string(fullPath [HOLDIR, "bin/unquote"])
fun has_unquoter() = FileSys.access(UNQUOTER, [FileSys.A_EXEC])
fun unquote_to intp file1 file2 =
    SYSTEML (UNQUOTER :: (if intp then ["-i"] else []) @ [file1, file2])


val failed_script_cache = ref (Binaryset.empty String.compare)

fun make_build_command (buildinfo : HM_Cline.t buildinfo_t) = let
  val {optv,actual_overlay,SIGOBJ,outs,hmenv,...} = buildinfo
  val {warn,tgtfatal,info,chatty,diag,...} = outs
  val debug = #debug (#core optv)
  val allfast = #fast (#core optv)
  val keep_going = #keep_going (#core optv)
  val quit_on_failure = #quit_on_failure (#core optv)
  val quiet_flag = #quiet (#core optv)
  val interactive_flag = #interactive (#core optv)
  val no_overlay = #no_overlay (#core optv)
  val overlay_stringl = case actual_overlay of NONE => [] | SOME s => [s]
  val MOSMLDIR =  case #mosmldir optv of NONE => MOSMLDIR0 | SOME s => s
  val MOSMLCOMP = fullPath [MOSMLDIR, "mosmlc"]
  fun compile debug args = let
    val _ = if isSome debug then
              print ("  with command "^ spacify(MOSMLCOMP::args)^"\n")
            else ()
  in
    SYSTEML (MOSMLCOMP::args)
  end
  fun build_command g (ii as {preincludes,includes}) c arg = let
    val include_flags = includify (preincludes @ includes)
    exception CompileFailed
    exception FileNotFound
  in
    case c of
        Compile _ (* deps *) =>
        let
          val file = fromFile arg
          val intp = case arg of SML (Script _) => true | _ => false
          val _ = exists_readable file orelse
                  (print ("Wanted to compile "^file^", but it wasn't there\n");
                   raise FileNotFound)
          val _ = info ("Compiling "^file)
          open Process
          val res =
              if has_unquoter() then let
                (* force to always use unquoter if present, so as to generate
                   location pragmas. Must test for existence, for bootstrapping.
                 *)
                val clone = variant file
                val _ = FileSys.rename {old=file, new=clone}
                fun revert() =
                  if FileSys.access (clone, [FileSys.A_READ]) then
                    ((if isSome debug then
                        FileSys.rename{old=file, new=file ^ ".quoted"}
                      else
                        FileSys.remove file) handle _ => ();
                     FileSys.rename{old=clone, new=file})
                  else ()
              in
                (if Process.isSuccess (unquote_to intp clone file)
                    handle e => (revert();
                                 print ("Unquoting "^file^
                                        " raised exception\n");
                                 raise CompileFailed)
                 then
                   compile debug ("-q"::(include_flags @ ["-c"] @
                                         overlay_stringl @ [file])) before
                   revert()
                 else (print ("Unquoting "^file^" ran and failed\n");
                       revert();
                       raise CompileFailed))
                handle CompileFailed => raise CompileFailed
                     | e => (revert();
                             print("Unable to compile: "^file^
                                   " - raised exception "^exnName e^"\n");
                             raise CompileFailed)
              end
              else
                compile debug ("-q"::(include_flags@ ("-c"::(overlay_stringl @
                                                             [file]))))
        in
          Process.isSuccess res
        end
      | BuildArticle _ => (print "Can't handle article building yet";
                           false)
      | ProcessArticle _ => (print "Can't handle article processing yet";
                             false)
      | BuildScript (s, deps, ex) =>
        let
          val _ = not (Binaryset.member(!failed_script_cache, s)) orelse
                  (print ("Not re-running "^s^"Script; believe it will fail\n");
                   raise CompileFailed)
          val scriptsml_file = SML (Script s)
          val scriptsml = fromFile scriptsml_file
          val script   = s^"Script"
          val scriptuo = script^".uo"
          val scriptui = script^".ui"
          open Process
          (* first thing to do is to create the Script.uo file *)
          val b = build_command g ii (Compile (deps, ex)) scriptsml_file
          val _ = b orelse raise CompileFailed
          val _ = print ("Linking "^scriptuo^
                         " to produce theory-builder executable\n")
          val objectfiles0 =
              if allfast then ["fastbuild.uo", scriptuo]
              else if quit_on_failure then [scriptuo]
              else ["holmakebuild.uo", scriptuo]
          val objectfiles =
              if interactive_flag then "holmake_interactive.uo" :: objectfiles0
              else objectfiles0
        in
          if
            isSuccess (
              compile debug (
                include_flags @ ["-o", script, "holmake_holpathdb.uo"] @
                objectfiles
              )
            )
          then
            let
              val status = Systeml.mk_xable script
              val _ = OS.Process.isSuccess status orelse
                      die_with ("Couldn't make script "^script^" executable")
              val script' = xable_string script
              val thysmlfile = s^"Theory.sml"
              val thysigfile = s^"Theory.sig"
              fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
              val _ = app safedelete [thysmlfile, thysigfile]
              val res2 = Systeml.systeml [fullPath [FileSys.getDir(), script']]
              val _ = app safedelete [script', scriptuo, scriptui]
              val () = if not (isSuccess res2) then
                         failed_script_cache :=
                           Binaryset.add(!failed_script_cache, s)
                       else ()
            in
              isSuccess res2 andalso
              (exists_readable thysmlfile orelse
               (print ("Couldn't find required output file: "^thysmlfile^ "\n");
                print ("Script file "^script'^
                       " didn't produce "^thysmlfile^"; \n\
                       \  maybe need export_theory() at end of "^
                       scriptsml^"\n");
                false)) andalso
              (exists_readable thysigfile orelse
               (print ("Script file "^script'^" didn't produce "^
                       thysigfile^"; \n\
                       \  maybe need export_theory() at end of "^
                       scriptsml^"\n");
                false))
            end
          else (print ("Failed to build script file, "^script^"\n"); false)
        end handle CompileFailed => false
                 | FileNotFound => false
  end (* fun's let *)
  fun mosml_build_command _ _ _ _ = NONE
  val build_graph = graphbuildj1 { build_command = build_command,
                                   mosml_build_command = mosml_build_command,
                                   outs = outs,
                                   keep_going = keep_going,
                                   quiet = quiet_flag,
                                   system = Systeml.system_ps,
                                   hmenv = hmenv}
in
  {extra_impl_deps = [], build_graph = build_graph}
end (* make_build_command's let *)

end (* struct *)
