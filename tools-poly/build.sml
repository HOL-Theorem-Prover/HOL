(*---------------------------------------------------------------------------
                An ML script for building HOL
 ---------------------------------------------------------------------------*)

structure build =
struct

open buildutils
datatype phase = Initial | Bare | Full

(* utilities *)

  fun main () = let

    val phase = ref Initial


(* values from the Systeml structure, which is created at HOL configuration
   time *)
val OS = Systeml.OS;
val HOLDIR = Systeml.HOLDIR
val DEPDIR = Systeml.DEPDIR
val DYNLIB = Systeml.DYNLIB
val POLY_LDFLAGS = Systeml.POLY_LDFLAGS
val POLY_LDFLAGS_STATIC = Systeml.POLY_LDFLAGS_STATIC

val dfltbuildseq = fullPath [HOLDIR, "tools", "build-sequence"]

(* ----------------------------------------------------------------------
    Analysing the command-line
   ---------------------------------------------------------------------- *)

val {kernelspec,seqname = bseq_fname,rest = cmdline,build_theory_graph} =
    case get_cline {default_seq = dfltbuildseq} of
      Normal x => x
    | Clean s => {kernelspec = "", seqname = dfltbuildseq, rest = [s],
                  build_theory_graph = false}

(* use the experimental kernel? Depends on the command-line and the compiler
   version... *)
val use_expk = let
  val version_string_w1 =
      hd (String.tokens Char.isSpace PolyML.Compiler.compilerVersion)
      handle Empty => ""
  val compiler_number =
      Real.floor (100.0 * valOf (Real.fromString version_string_w1))
      handle Option => 0
  val expkp = kernelspec = "-expk"
in
  if not expkp andalso compiler_number < 530 then
    (warn "*** Using the experimental kernel (standard kernel requires \
          \Poly/ML 5.3 or\n*** higher)";
     true)
  else
    expkp
end

(* do self-tests? and to what level *)
val (do_selftests, cmdline) = cline_selftest cmdline
(*---------------------------------------------------------------------------
     Source directories.
 ---------------------------------------------------------------------------*)

val kname =
  if use_expk then "expk"
  else if kernelspec = "-otknl" then "otknl"
  else "stdknl"

val SRCDIRS =
    if cmdline = ["help"] then []
    else read_buildsequence {kernelname = kname} bseq_fname

val HOLMAKE = fullPath [HOLDIR, "bin/Holmake"]

open Systeml;

fun which_hol () =
  case !phase of
    Initial => (POLY, "--poly_not_hol")
  | Bare => (fullPath [HOLDIR, "bin", "hol.builder0"], "")
  | Full => (fullPath [HOLDIR, "bin", "hol.builder"], "");


fun Holmake dir = let
  val (wp, hol) = which_hol ()
  val hmstatus = Systeml.systeml [HOLMAKE, "--qof", "--poly", wp, hol]
in
  if OS.Process.isSuccess hmstatus then
    if do_selftests > 0 andalso
       OS.FileSys.access("selftest.exe", [OS.FileSys.A_EXEC])
    then
      (print "Performing self-test...\n";
       if SYSTEML [dir ^ "/selftest.exe", Int.toString do_selftests]
       then
         print "Self-test was successful\n"
       else
         die ("Selftest failed in directory "^dir))
    else
      ()
  else let
      open Posix.Process
      val info =
          case fromStatus hmstatus of
            W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
          | W_EXITED => "exited normally???"
          | W_SIGNALED sg => "with signal " ^
                              SysWord.toString (Posix.Signal.toWord sg)
          | W_STOPPED sg => "stopped with signal " ^
                            SysWord.toString (Posix.Signal.toWord sg)
    in
      die ("Build failed in directory "^dir^" ("^info^")")
    end
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
           Compile a HOL directory in place. Some libraries,
           e.g., the robdd libraries, need special treatment because
           they come with external tools or C libraries.
 ---------------------------------------------------------------------------*)


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

fun compile (systeml : string list -> OS.Process.status) exe obj : unit =
  (systeml ([Systeml.CC, "-o", exe, obj] @ POLY_LDFLAGS);
   OS.FileSys.remove obj);

fun make_exe (name:string) (POLY : string) (target:string) : unit = let
  val _ = print ("Building "^target^"\n")
  val dir = OS.FileSys.getDir()
 in
   OS.FileSys.chDir (fullPath [HOLDIR, "tools-poly"]);
   Systeml.system_ps (POLY ^ " < " ^ name);
   compile systeml (fullPath [Systeml.HOLDIR, "bin", target]) (target ^ ".o");
   OS.FileSys.chDir dir
 end

fun buildDir symlink s =
  if #1 s = fullPath [HOLDIR, "bin/hol.bare"] then phase := Bare
  else if #1 s = fullPath [HOLDIR, "bin/hol"] then phase := Full
  else
    (build_dir Holmake do_selftests s; upload(s,SIGOBJ,symlink))

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
 let val dir = OS.Path.concat(OS.Path.concat (HOLDIR,"help"),"src-sml")
     val _ = OS.FileSys.chDir dir

     (* builds the documentation tools called below *)
     val _ = Systeml.system_ps (fullPath [HOLDIR, "tools", "mllex", "mllex.exe"] ^ " Lexer.lex")
     val _ = Systeml.system_ps (fullPath [HOLDIR, "tools", "mlyacc", "src", "mlyacc.exe"] ^ " Parser.grm")
     val _ = Systeml.system_ps (POLY ^ " < poly-makebase.ML");
     val _ = compile systeml "makebase.exe" "makebase.o";
     val _ = Systeml.system_ps (POLY ^ " < poly-Doc2Html.ML");
     val _ = compile systeml "Doc2Html.exe" "Doc2Html.o";
     val _ = Systeml.system_ps (POLY ^ " < poly-Doc2Txt.ML");
     val _ = compile systeml "Doc2Txt.exe" "Doc2Txt.o";
     val _ = Systeml.system_ps (POLY ^ " < poly-Doc2Tex.ML");
     val _ = compile systeml "Doc2Tex.exe" "Doc2Tex.o";

     val doc2html = fullPath [dir,"Doc2Html.exe"]
     val docpath  = fullPath [HOLDIR, "help", "Docfiles"]
     val htmlpath = fullPath [docpath, "HTML"]
     val _        = if (OS.FileSys.isDir htmlpath handle _ => false) then ()
                    else (print ("Creating directory "^htmlpath^"\n");
                          OS.FileSys.mkDir htmlpath)
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
 let open OS.Path TextIO
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
  open OS.FileSys
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
end handle IO.Io _ => warn "Couldn't set up build-logs"

fun finish_logging buildok = let
in
  if OS.FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      OS.FileSys.rename {old = logfilename, new = fullPath [logdir, newname]}
    end
  else ()
end handle IO.Io _ => warn "Had problems making permanent record of build log"

val () = OS.Process.atExit (fn () => finish_logging false)
        (* this will do nothing if finish_logging happened normally first;
           otherwise the log's bad version will be recorded *)

fun build_hol symlink = let
in
  clean_sigobj();
  setup_logfile();
  build_src symlink
    handle SML90.Interrupt => (finish_logging false; die "Interrupted");
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
                           map #1 SRCDIRS)

val _ = check_against "tools-poly/smart-configure.sml"
val _ = check_against "tools-poly/configure.sml"
val _ = check_against "tools-poly/build.sml"
val _ = check_against "tools/Holmake/Systeml.sig"




in
    case cmdline of
      []            => build_hol default_link
    | ["-symlink"]  => build_hol (symlink_check()) (* w/ symbolic linking *)
    | ["-nosymlink"]=> build_hol cp
    | ["-small"]    => build_hol mv                (* by renaming *)
    | ["-dir",path] => buildDir cp (path, 0)
    | ["-dir",path,
       "-symlink"]  => buildDir (symlink_check()) (path, 0)
    | ["-clean"]    => clean_dirs buildutils.clean
    | ["-cleanAll"] => clean_dirs buildutils.cleanAll
    | ["clean"]     => clean_dirs buildutils.clean
    | ["cleanAll"]  => clean_dirs buildutils.cleanAll
    | ["symlink"]   => build_hol (symlink_check())
    | ["nosymlink"] => build_hol cp
    | ["small"]     => build_hol mv
    | ["help"]      => build_help()
    | otherwise     => warn help_mesg
  end
end (* struct *)
