(*---------------------------------------------------------------------------
                An ML script for building HOL
 ---------------------------------------------------------------------------*)

structure build =
struct

structure Process = OS.Process

(* utilities *)

(* ----------------------------------------------------------------------
    Magic to ensure that interruptions (SIGINTs) are actually seen by the
    linked executable as Interrupt exceptions
   ---------------------------------------------------------------------- *)

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

open buildutils
val _ = startup_check()

(* ----------------------------------------------------------------------
    Analysing the command-line
   ---------------------------------------------------------------------- *)

val cline_record = process_cline ()
val {cmdline,build_theory_graph,selftest_level,...} = cline_record
val {extra={SRCDIRS},jobcount,relocbuild,debug,...} = cline_record


open Systeml;

val Holmake = let
  fun sysl p args = Systeml.systeml (p::args)
  val isSuccess = OS.Process.isSuccess
in
  buildutils.Holmake sysl isSuccess
                     (fn () => (case jobcount of
                                    NONE => []
                                  | SOME j => ["-j"^Int.toString j]) @
                               (if debug then ["--dbg"] else []))
                     (fn _ => "")
                     selftest_level
end

(* ----------------------------------------------------------------------
   Some useful file-system utility functions
   ---------------------------------------------------------------------- *)

(* create a symbolic link - Unix only *)
fun link b s1 s2 =
  let open Process
  in if SYSTEML ["ln", "-s", s1, s2] then ()
     else die ("Unable to link file "^quote s1^" to file "^quote s2^".")
  end

fun symlink_check() =
    if OS = "winNT" then
      die "Sorry; symbolic linking isn't available under Windows NT"
    else link
val default_link = if OS = "winNT" then cp else link

fun mem x [] = false
  | mem x (y::ys) = x = y orelse mem x ys

fun exns_link exns b s1 s2 =
  if mem (OS.Path.file s1) exns then () else default_link b s1 s2

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
    else if selftest_level >= regulardir then
      print ("Self-test directory "^src^" built successfully.\n")
    else ()

(*---------------------------------------------------------------------------
    For each element in SRCDIRS, build it, then upload it to SIGOBJ.
    This allows us to have the build process only occur w.r.t. SIGOBJ
    (thus requiring only a single place to look for things).
 ---------------------------------------------------------------------------*)

fun buildDir symlink s =
    (build_dir Holmake selftest_level s; upload(s,SIGOBJ,symlink));

fun build_src symlink = List.app (buildDir symlink) SRCDIRS

fun upload_holmake_files symlink =
  upload ((fullPath[HOLDIR, "tools", "Holmake"], 0), SIGOBJ, symlink)

val holmake_exns = [
  "Systeml.sig", "Systeml.ui", "Systeml.uo"
]

fun remove_holmkdir (dirname,_) =
    let
      open OS.FileSys
      val holmkdir = OS.Path.concat (dirname, ".HOLMK")
    in
      if access (holmkdir, [A_READ, A_EXEC]) andalso isDir holmkdir then
        (map_dir (fn (d,f) => rem_file (OS.Path.concat(d,f))) holmkdir;
         OS.FileSys.rmDir holmkdir)
      else ()
    end

fun build_hol symlink = let
in
  List.app remove_holmkdir SRCDIRS;
  clean_sigobj();
  setup_logfile();
  upload_holmake_files (exns_link holmake_exns);
  build_src symlink
    handle Interrupt => (finish_logging false; die "Interrupted");
  finish_logging true;
  make_buildstamp();
  build_help build_theory_graph;
  print "\nHol built successfully.\n"
end


(*---------------------------------------------------------------------------
       Get rid of compiled code and dependency information.
 ---------------------------------------------------------------------------*)

val check_againstB = check_against EXECUTABLE
val _ = check_againstB "tools/smart-configure.sml"
val _ = check_againstB "tools/configure.sml"
val _ = check_againstB "tools/build.sml"
val _ = check_againstB "tools/Holmake/Systeml.sig"
val _ = check_againstB "tools/configure-mosml.sml"

val _ = let
  val fP = fullPath
  open OS.FileSys
  val hmake = fP [HOLDIR,"bin",xable_string "Holmake"]
in
  if access(hmake, [A_READ, A_EXEC]) then
    app_sml_files (check_against hmake)
                  {dirname = fP [HOLDIR, "tools", "Holmake"]}
  else
    die ("No Holmake executable in " ^ fP [HOLDIR, "bin"])
end


val _ =
    case cmdline of
      []            => build_hol default_link
     | _ => die "Not implemented yet"

end (* struct *)
