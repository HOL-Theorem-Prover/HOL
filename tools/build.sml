(*---------------------------------------------------------------------------
                An ML script for building HOL
 ---------------------------------------------------------------------------*)

structure build =
struct

structure Process = OS.Process

open buildutils

(* utilities *)

(* ----------------------------------------------------------------------
    Magic to ensure that interruptions (SIGINTs) are actually seen by the
    linked executable as Interrupt exceptions
   ---------------------------------------------------------------------- *)

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

(* values from the Systeml structure, which is created at HOL configuration
   time *)
val OS = Systeml.OS;
val HOLDIR = Systeml.HOLDIR
val EXECUTABLE = Systeml.xable_string (fullPath [HOLDIR, "bin", "build"])
val DEPDIR = Systeml.DEPDIR
val DYNLIB = Systeml.DYNLIB

(* ----------------------------------------------------------------------
    Analysing the command-line
   ---------------------------------------------------------------------- *)

val dfltbuildseq = fullPath [HOLDIR, "tools", "build-sequence"]

val {kernelspec,seqname = bseq_fname,rest = cmdline} =
    case get_cline {default_seq = dfltbuildseq} of
      Normal x => x
    | Clean s => {kernelspec = "", seqname = dfltbuildseq, rest = [s]}

(* do self-tests? and to what level *)
val (do_selftests, cmdline) = cline_selftest cmdline

(*---------------------------------------------------------------------------
     Source directories.
 ---------------------------------------------------------------------------*)

val kname =
    case kernelspec of
      "-expk" => "expk"
    | "-otknl" => "otknl"
    | _ => "stdknl"

val SRCDIRS =
    if cmdline = ["help"] then []
    else read_buildsequence {kernelname = kname} bseq_fname

val HOLMAKE = fullPath [HOLDIR, "bin/Holmake"]

open Systeml;

fun Holmake dir =
  if SYSTEML [HOLMAKE, "--qof"] then
    if do_selftests > 0 andalso
       FileSys.access("selftest.exe", [FileSys.A_EXEC])
    then
      (print "Performing self-test...\n";
       if SYSTEML [dir ^ "/selftest.exe", Int.toString do_selftests] then
         print "Self-test was successful\n"
       else
         die ("Selftest failed in directory "^dir))
    else
      ()
  else die ("Build failed in directory "^dir);

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
    (build_dir Holmake do_selftests s; upload(s,SIGOBJ,symlink));

fun build_src symlink = List.app (buildDir symlink) SRCDIRS

fun build_adoc_files () = let
  val docdirs = let
    val instr = TextIO.openIn(fullPath [HOLDIR, "tools",
                                        "documentation-directories"])
    val wholefile = TextIO.inputAll instr before TextIO.closeIn instr
  in
    map normPath (String.tokens Char.isSpace wholefile)
  end handle _ => (print "Couldn't read documentation directories file\n";
                   [])
  val doc2txt = fullPath [HOLDIR, "help", "src-sml", "Doc2Txt.exe"]
  fun make_adocs dir = let
    val fulldir = fullPath [HOLDIR, dir]
  in
    if SYSTEML [doc2txt, fulldir, fulldir] then true
    else
      (print ("Generation of ASCII doc files failed in directory "^dir^"\n");
       false)
  end
in
  List.all make_adocs docdirs
end

fun build_help () =
 let val dir = Path.concat(Path.concat (HOLDIR,"help"),"src-sml")
     val _ = FileSys.chDir dir

     (* builds the documentation tools called below *)
     val _ = SYSTEML [HOLMAKE, "all"]

     val doc2html = fullPath [dir,"Doc2Html.exe"]
     val docpath  = fullPath [HOLDIR, "help", "Docfiles"]
     val htmlpath = fullPath [docpath, "HTML"]
     val _        = if (FileSys.isDir htmlpath handle _ => false) then ()
                    else (print ("Creating directory "^htmlpath^"\n");
                          FileSys.mkDir htmlpath)
     val cmd1     = [doc2html, docpath, htmlpath]
     val cmd2     = [fullPath [dir,"makebase.exe"]]
     val _ = print "Generating ASCII versions of Docfiles...\n"
     val _ = if build_adoc_files () then print "...ASCII Docfiles done\n"
             else ()
 in
   print "Generating HTML versions of Docfiles...\n"
 ;
   if SYSTEML cmd1 then print "...HTML Docfiles done\n"
   else die "Couldn't make html versions of Docfiles"
 ;
   if (print "Building Help DB\n"; SYSTEML cmd2) then ()
   else die "Couldn't make help database"
 end;

fun make_buildstamp () =
 let open Path TextIO
     val stamp_filename = concat(HOLDIR, concat("tools","build-stamp"))
     val stamp_stream = openOut stamp_filename
     val date_string = Date.toString (Date.fromTimeLocal (Time.now()))
 in
    output(stamp_stream, "built "^date_string);
    closeOut stamp_stream
end

val logdir = Systeml.build_log_dir
val logfilename = Systeml.build_log_file
val hostname = if Systeml.isUnix then
                 case Mosml.run "hostname" [] "" of
                   Mosml.Success s => String.substring(s,0,size s - 1) ^ "-"
                                      (* substring to drop \n in output *)
                 | _ => ""
               else "" (* what to do under windows? *)

fun setup_logfile () = let
  open FileSys
  fun ensure_dir () =
      if access (logdir, []) then
        isDir logdir
      else (mkDir logdir; true)
in
  if ensure_dir() then
    if access (logfilename, []) then
      warn "Build log exists; new logging will concatenate onto this file"
    else let
        (* touch the file *)
        val outs = TextIO.openOut logfilename
      in
        TextIO.closeOut outs
      end
  else warn "Couldn't make or use build-logs directory"
end handle Io _ => warn "Couldn't set up build-logs"

fun finish_logging buildok = let
in
  if FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      FileSys.rename {old = logfilename, new = fullPath [logdir, newname]}
    end
  else ()
end handle Io _ => warn "Had problems making permanent record of build log"

val () = Process.atExit (fn () => finish_logging false)
        (* this will do nothing if finish_logging happened normally first;
           otherwise the log's bad version will be recorded *)

fun build_hol symlink = let
in
  clean_sigobj();
  setup_logfile();
  build_src symlink
    handle Interrupt => (finish_logging false; die "Interrupted");
  finish_logging true;
  make_buildstamp();
  build_help();
  print "\nHol built successfully.\n"
end


(*---------------------------------------------------------------------------
       Get rid of compiled code and dependency information.
 ---------------------------------------------------------------------------*)

fun clean_dirs f =
    clean_sigobj() before
    (* clean both kernel directories, regardless of which was actually built,
       the help src directory too, and all the src directories, including
       those with ! annotations  *)
    buildutils.clean_dirs {HOLDIR=HOLDIR, action = f}
                          (fullPath [HOLDIR, "help", "src-sml"] ::
                           fullPath [HOLDIR, "src", "0"] ::
                           fullPath [HOLDIR, "src", "experimental-kernel"] ::
                           fullPath [HOLDIR, "src", "logging-kernel"] ::
                           map #1 SRCDIRS)

val _ = check_against "tools/smart-configure.sml"
val _ = check_against "tools/configure.sml"
val _ = check_against "tools/build.sml"
val _ = check_against "tools/Holmake/Systeml.sig"
val _ = check_against "tools/configure-mosml.sml"


val _ =
    case cmdline of
      []            => build_hol default_link
    | ["-symlink"]  => build_hol (symlink_check()) (* w/ symbolic linking *)
    | ["-small"]    => build_hol mv                (* by renaming *)
    | ["-dir",path] => buildDir cp (path, 0)
    | ["-dir",path,
       "-symlink"]  => buildDir (symlink_check()) (path, 0)
    | ["-nosymlink"]=> build_hol cp
    | ["-clean"]    => clean_dirs buildutils.clean
    | ["-cleanAll"] => clean_dirs buildutils.cleanAll
    | ["clean"]     => clean_dirs buildutils.clean
    | ["cleanAll"]  => clean_dirs buildutils.cleanAll
    | ["symlink"]   => build_hol (symlink_check())
    | ["nosymlink"] => build_hol cp
    | ["small"]     => build_hol mv
    | ["help"]      => build_help()
    | otherwise     => warn help_mesg

end (* struct *)
