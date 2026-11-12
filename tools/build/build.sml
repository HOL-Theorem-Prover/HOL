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
val {cmdline,build_theory_graph,selftest_level,keepgoing,...} = cline_record
val {extra={SRCDIRS},jobcount,relocbuild,debug,thmsrc,...} = cline_record

(* Forward only the cache options the user actually wrote -- see comment
   in tools-poly/build.sml for the same code there. *)
val cache_args = extract_cache_args (CommandLine.arguments())


open Systeml;

val Holmake = let
  fun sysl p args = Systeml.systeml (p::args)
  val isSuccess = OS.Process.isSuccess
in
  buildutils.Holmake sysl isSuccess
                     (fn () => (case jobcount of
                                    NONE => []
                                  | SOME j => ["-j"^Int.toString j]) @
                               (if debug then ["--dbg"] else []) @
                               (if keepgoing then ["-k"] else []) @
                               (case thmsrc of
                                    NONE => []
                                  | SOME s => ["--thmsrc="^s]) @
                               cache_args)
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
  (upload ((fullPath[HOLDIR, "tools", "Holmake"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "Holmake", "core"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "Holmake", "deps"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "Holmake", "hfs"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "Holmake", "hmf"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "parsing"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "Holmake", "util"], 0), SIGOBJ, symlink);
   upload ((fullPath[HOLDIR, "tools", "util"], 0), SIGOBJ, symlink);
   transfer_file symlink SIGOBJ
       (fullPath[HOLDIR, "tools", "Holmake", "mosml"], "HFS_NameMunge.uo"));

val holmake_exns = [
  "Systeml.sig", "Systeml.ui", "Systeml.uo"
]

(* tools/parsing is compiled by configure and has no Holmakefile, so
   nothing here can rebuild it; upload_holmake_files would just ship an
   empty directory to sigobj and the first sign of trouble would be a
   missing HOLSource.uo when mosml links src/parse/selftest.exe, many
   directories later.  Say it now instead.  Poly/ML doesn't care: it
   gets these modules from bin/hol, not from sigobj. *)
fun check_configure_built () =
    let
      val f = fullPath [HOLDIR, "tools", "parsing", "HOLSource.uo"]
    in
      if Systeml.ML_SYSNAME = "poly" orelse
         OS.FileSys.access (f, [OS.FileSys.A_READ])
      then ()
      else die ("Missing " ^ f ^ "\n" ^
                "tools/parsing is compiled by configure, not by the " ^
                "build sequence.\nRe-run\n\n    " ^
                Systeml.ML_SYSNAME ^ " < tools/smart-configure.sml\n\n" ^
                "before building.")
    end

fun build_hol symlink = let
in
  check_configure_built();
  remove_all_holmkdirs();
  clean_sigobj();
  setup_logfile();
  upload_holmake_files (exns_link holmake_exns);
  build_src symlink
    handle Interrupt =>
      (finish_logging {buildok = false, selftest_level = selftest_level};
       die "Interrupted");
  finish_logging {buildok = true, selftest_level = selftest_level};
  make_buildstamp();
  build_help {graph = build_theory_graph,
              no_mdbook = #no_mdbook cline_record,
              no_helpdocs = #no_helpdocs cline_record};
  print "\nHol built successfully.\n"
end


(*---------------------------------------------------------------------------
       Get rid of compiled code and dependency information.
 ---------------------------------------------------------------------------*)

val check_againstB = check_against EXECUTABLE
val _ = check_againstB "tools/smart-configure.sml"
val _ = check_againstB "tools/configure.sml"
val _ = check_againstB "tools/build/build.sml"
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

(* The quote filter's lexer is generated from tools/parsing/HolLex by
   configure, and by no Holmakefile rule, so pulling in a grammar change
   leaves a stale bin/unquote that silently mis-lexes the new syntax.
   The app_sml_files sweep above cannot catch it: HolLex has no .sml
   extension and does not live under tools/Holmake. *)
val _ = let
  val fP = fullPath
  open OS.FileSys
  val unquote = fP [HOLDIR,"bin",xable_string "unquote"]
in
  if access(unquote, [A_READ, A_EXEC]) then
    check_against unquote "tools/parsing/HolLex"
  else ()
end


val _ =
    case cmdline of
      []            => build_hol default_link
     | _ => die "Not implemented yet"

end (* struct *)
