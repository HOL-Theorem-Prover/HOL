(*---------------------------------------------------------------------------
                An ML script for building HOL
 ---------------------------------------------------------------------------*)

structure build =
struct

open buildutils
datatype phase = Initial | Bare | Full

(* utilities *)

  fun main () = let

    val _ = startup_check()
    val phase = ref Initial


    open buildutils

(* ----------------------------------------------------------------------
    Analysing the command-line
   ---------------------------------------------------------------------- *)

val {cmdline,build_theory_graph,do_selftests,SRCDIRS,jobcount,relocbuild} =
    process_cline ()

open Systeml;

fun phase_extras () =
  case !phase of
    Initial => ["--poly_not_hol"]
  | Bare => ["--holstate", fullPath [HOLDIR, "bin", "hol.state0"]]
  | Full => []

fun aug_systeml proc args = let
  open Posix.Process
  val env' =
      "SELFTESTLEVEL="^Int.toString do_selftests :: Posix.ProcEnv.environ()
in
  case fork() of
    NONE => (exece(proc,proc::args,env')
             handle _ => die ("Exece of "^proc^" failed"))
  | SOME cpid => let
      val (_, result) = waitpid(W_CHILD cpid, [])
    in
      result
    end
end


val Holmake = let
  fun isSuccess Posix.Process.W_EXITED = true
    | isSuccess _ = false
  fun analysis hmstatus = let
    open Posix.Process
  in
    case hmstatus of
      W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
    | W_EXITED => "exited normally???"
    | W_SIGNALED sg => "with signal " ^
                       SysWord.toString (Posix.Signal.toWord sg)
    | W_STOPPED sg => "stopped with signal " ^
                      SysWord.toString (Posix.Signal.toWord sg)
  end
in
  buildutils.Holmake aug_systeml isSuccess
                     (fn () => ("-j"^Int.toString jobcount) ::
                               ((if relocbuild then ["--relocbuild"] else []) @
                                phase_extras()))
                     analysis do_selftests
end

(* create a symbolic link - Unix only *)
fun link b s1 s2 =
    Posix.FileSys.symlink {new = s2, old = s1}
    handle OS.SysErr (s, _) =>
           die ("Unable to link old file "^quote s1^" to new file "
                ^quote s2^": "^s)

fun symlink_check() =
    if OS = "winNT" then
      die "Sorry; symbolic linking isn't available under Windows NT"
    else link
val default_link = if OS = "winNT" then cp else link

(*---------------------------------------------------------------------------
        Transport a compiled directory to another location. The
        symlink argument says whether this is via a symbolic link,
        or by copying. The ".uo", ".ui", ".so", ".xable" and ".sig"
        files are transported.
 ---------------------------------------------------------------------------*)

fun upload ((src, regulardir), target, symlink) =
    if regulardir = 0 then
      (print ("Uploading files to "^target^"\n");
       map_dir (transfer_file symlink target) src)
      handle OS.SysErr(s, erropt) =>
             die ("OS error: "^s^" - "^
                  (case erropt of SOME s' => OS.errorMsg s'
                                | _ => ""))
    else if do_selftests >= regulardir then
      print ("Self-test directory "^src^" built successfully.\n")
    else ()

(*---------------------------------------------------------------------------
    For each element in SRCDIRS, build it, then upload it to SIGOBJ.
    This allows us to have the build process only occur w.r.t. SIGOBJ
    (thus requiring only a single place to look for things).
 ---------------------------------------------------------------------------*)

fun buildDir symlink s =
  if #1 s = fullPath [HOLDIR, "bin/hol.bare"] then phase := Bare
  else if #1 s = fullPath [HOLDIR, "bin/hol"] then phase := Full
  else
    (build_dir Holmake do_selftests s; upload(s,SIGOBJ,symlink))

fun build_src symlink = List.app (buildDir symlink) SRCDIRS

fun build_hol symlink = let
in
  clean_sigobj();
  setup_logfile();
  build_src symlink
    handle SML90.Interrupt => (finish_logging false; die "Interrupted");
  finish_logging true;
  make_buildstamp();
  build_help build_theory_graph;
  print "\nHol built successfully.\n"
end


(*---------------------------------------------------------------------------
       Get rid of compiled code and dependency information.
 ---------------------------------------------------------------------------*)

val check_againstB = check_against EXECUTABLE
val _ = check_againstB "tools-poly/smart-configure.sml"
val _ = check_againstB "tools-poly/configure.sml"
val _ = check_againstB "tools-poly/build.sml"
val _ = check_againstB "tools/Holmake/Systeml.sig"

val _ = let
  val fP = fullPath
  open OS.FileSys
  val hmake = fP [HOLDIR,"bin",xable_string "Holmake"]
in
  if access(hmake, [A_READ, A_EXEC]) then
    (app_sml_files (check_against hmake)
                   {dirname = fP [HOLDIR, "tools-poly", "Holmake"]};
     app_sml_files (check_against hmake)
                   {dirname = fP [HOLDIR, "tools", "Holmake"]})
  else
    die ("No Holmake executable in " ^ fP [HOLDIR, "bin"])
end





in
    case cmdline of
      []            => build_hol default_link
    | _ => die "Multi-dir build not implemented yet"

  end
end (* struct *)
