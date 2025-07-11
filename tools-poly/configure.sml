(* ----------------------------------------------------------------------
              HOL configuration script


   DO NOT EDIT THIS FILE UNLESS YOU HAVE TRIED AND FAILED WITH

     smart-configure

   AND

     config-override.

   ---------------------------------------------------------------------- *)


(* Uncomment these lines and fill in correct values if smart-configure doesn't
   get the correct values itself.  Then run

      poly < tools/configure.sml

   If you are specifying directories under Windows, we recommend you
   use forward slashes (the "/" character) as a directory separator,
   rather than the 'traditional' backslash (the "\" character).

   The problem with the latter is that you have to double them up
   (i.e., write "\\") in order to 'escape' them and make the string
   valid for SML.  For example, write "c:/dir1/dir2/mosml", rather
   than "c:\\dir1\\dir2\\mosml", and certainly DON'T write
   "c:\dir1\dir2\mosml".
*)

(*
val poly : string         =
val polymllibdir : string =
val holdir :string        =
val OS :string            =
                           (* Operating system; choices are:
                                "linux", "solaris", "unix", "macosx",
                                "winNT"   *)
*)

val _ = PolyML.print_depth 0;

use "tools-poly/poly/Mosml.sml";
val pkgconfig_info =
    case Mosml.run "pkg-config" ["--libs", "polyml"] "" of
        Mosml.Success lstr => SOME (String.tokens Char.isSpace lstr)
      | _ => NONE


val CC:string       = "cc";       (* C compiler                       *)


fun echo s = (TextIO.output(TextIO.stdOut, s^"\n");
              TextIO.flushOut TextIO.stdOut);

val verbose = false

val echov = if verbose then echo else (fn _ => ())

fun liftstatus f x =
  if OS.Process.isSuccess (f x) then ()
  else raise Fail "Command failed"

(*---------------------------------------------------------------------------
          END user-settable parameters
 ---------------------------------------------------------------------------*)

val version_number = 1
val release_string = "Trindemossen"

(*
val _ = Meta.quietdec := true;
app load ["OS", "Substring", "BinIO", "Lexing", "Nonstdio"];
*)
structure FileSys = OS.FileSys
structure Process = OS.Process
structure Path = OS.Path

fun check_is_dir role dir =
    (FileSys.isDir dir handle e => false) orelse
    (print "\n*** Bogus directory ("; print dir; print ") given for ";
     print role; print "! ***\n";
     Process.exit Process.failure)

val _ = check_is_dir "polymllibdir" polymllibdir
val _ = check_is_dir "holdir" holdir
val _ =
    if List.exists (fn s => s = OS)
                   ["linux", "solaris", "unix", "winNT", "macosx"]
    then ()
    else (print ("\n*** Bad OS specified: "^OS^" ***\n");
          Process.exit Process.failure)

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

fun quote s = String.concat ["\"",String.toString s,"\""]

val holmakedir = fullPath [holdir, "tools-poly", "Holmake"];

(*---------------------------------------------------------------------------
      File handling. The following implements a very simple line
      replacement function: it searchs the source file for a line that
      contains "redex" and then replaces the whole line by "residue". As it
      searches, it copies lines to the target. Each replacement happens
      once; the replacements occur in order. After the last replacement
      is done, the rest of the source is copied to the target.
 ---------------------------------------------------------------------------*)

fun processLinesUntil (istrm,ostrm) (redex,residue) =
 let open TextIO
     fun loop () =
       case inputLine istrm
        of NONE => ()
          | SOME ""   => ()
         | SOME line =>
            let val ssline = Substring.full line
                val (pref, suff) = Substring.position redex ssline
            in
              if Substring.size suff > 0
              then output(ostrm, residue)
              else (output(ostrm, line); loop())
            end
 in
   loop()
 end;

fun fill_holes (src,target) repls =
 let open TextIO
     val istrm = openIn src
     val ostrm = openOut target
  in
     List.app (processLinesUntil (istrm, ostrm)) repls;
     output(ostrm, inputAll istrm);
     closeIn istrm; closeOut ostrm
  end;

infix -->
fun (x --> y) = (x,y);

fun text_copy src dest = fill_holes(src, dest) [];

fun bincopy src dest = let
  val instr = BinIO.openIn src
  val outstr = BinIO.openOut dest
  fun loop () = let
    val v = BinIO.inputN(instr, 1024)
  in
    if Word8Vector.length v = 0 then (BinIO.flushOut outstr;
                                      BinIO.closeOut outstr;
                                      BinIO.closeIn instr)
    else (BinIO.output(outstr, v); loop())
  end
in
  loop()
end;


(*---------------------------------------------------------------------------
     Generate "Systeml" file in tools-poly/Holmake and then load in that file,
     thus defining the Systeml structure for the rest of the configuration
     (with OS-specific stuff available).
 ---------------------------------------------------------------------------*)

(* default values ensure that later things fail if Systeml doesn't compile *)
fun systeml x = (print "Systeml not correctly loaded.\n";
                 Process.exit Process.failure);
val mk_xable = systeml;
val xable_string = systeml;

fun opt_to_string p NONE = "NONE"
  | opt_to_string p (SOME x) = "SOME " ^ p x
val optquote = opt_to_string quote

val OSkind = if OS="linux" orelse OS="solaris" orelse OS="macosx" then "unix"
             else OS
local
   fun assoc item =
      let
         fun assc ((key,ob)::rst) = if item=key then ob else assc rst
           | assc [] = raise Match
      in
         assc
      end
   val machine_env = Posix.ProcEnv.uname ()
   val sysname = assoc "sysname" machine_env
   val intOf = Option.valOf o Int.fromString
   val number = PolyML.Compiler.compilerVersionNumber
   val _ = number >= 570 orelse die "PolyML version must be at least 5.7.0"
   val ldruntimepath = "-Wl,-rpath,"^polymllibdir
   val default =
       ["-L" ^ polymllibdir,
        "-lpolymain", "-lpolyml", "-lpthread",
        "-lm", "-ldl", "-lstdc++", "-lgcc_s", "-lgcc", ldruntimepath]
in
   val machine_flags =
       if sysname = "Darwin" (* Mac OS X *) then
         let
           val stdsuffix = "-Wl,-no_pie"
         in
           (case pkgconfig_info of
                  SOME list => list @ [ldruntimepath, stdsuffix]
                | NONE => ["-L"^polymllibdir, "-lpolymain", "-lpolyml",
                           "-lstdc++"] @ [ldruntimepath, stdsuffix]) @
           (if PolyML.architecture() = "I386" then ["-arch", "i386"] else [])
         end
       else if sysname = "Linux" then
         case pkgconfig_info of
             SOME list => list @ [ldruntimepath]
           | _ => default
       else if String.isPrefix "CYGWIN_NT" sysname (* Cygwin! *) then
         default
       else
         default
end;


val _ = let
  (* copy system-specific implementation of Systeml into place *)
  val srcfile = fullPath [holmakedir, OSkind ^"-systeml.sml"]
  val destfile = fullPath [holmakedir, "Systeml.sml"]
  val sigfile = fullPath [holdir, "tools", "Holmake", "Systeml.sig"]
in
  print "\nLoading system specific functions\n";
  use sigfile;
  fill_holes (srcfile, destfile)
  ["val HOLDIR ="   --> ("val HOLDIR = "^quote holdir^"\n"),
   "val POLYMLLIBDIR =" --> ("val POLYMLLIBDIR = "^quote polymllibdir^"\n"),
   "val POLY =" --> ("val POLY = "^quote poly^"\n"),
   "val POLYC =" --> ("val POLYC = "^quote polyc^"\n"),
   "val POLY_LDFLAGS =" -->
      ("val POLY_LDFLAGS = [" ^
       String.concatWith ", "
                         (map quote
                              ((if null POLY_LDFLAGS then machine_flags
                                else POLY_LDFLAGS) @ EXTRA_POLY_LDFLAGS)) ^
       "]\n"),
   "val POLY_LDFLAGS_STATIC =" -->
      ("val POLY_LDFLAGS_STATIC = [" ^
       String.concatWith ", "
                         (map quote
                              ((if null POLY_LDFLAGS_STATIC then
                                  ("-static" :: machine_flags)
                                else
                                  POLY_LDFLAGS_STATIC) @ EXTRA_POLY_LDFLAGS)) ^
       "]\n"),
   "val CC =" --> ("val CC = "^quote CC^"\n"),
   "val OS ="       --> ("val OS = "^quote OS^"\n"),
   "val GNUMAKE ="  --> ("val GNUMAKE = "^quote GNUMAKE^"\n"),
   "val DYNLIB ="   --> ("val DYNLIB = "^Bool.toString dynlib_available^"\n"),
   "val version ="  --> ("val version = "^Int.toString version_number^"\n"),
   "val ML_SYSNAME =" --> "val ML_SYSNAME = \"poly\"\n",
   "val release ="  --> ("val release = "^quote release_string^"\n"),
   "val DOT_PATH =" --> ("val DOT_PATH = "^optquote DOT_PATH^"\n"),
   "val MV =" -->       ("val MV = "^quote MV^"\n"),
   "val CP =" -->       ("val CP = "^quote CP^"\n")
  ];
  use destfile
end;

open Systeml;

(*---------------------------------------------------------------------------
     Now compile Systeml.sml in tools-poly/Holmake/
 ---------------------------------------------------------------------------*)

fun canread s = OS.FileSys.access(s, [FileSys.A_READ])
val modTime = OS.FileSys.modTime;

val _ = print ("Note: Int.maxInt = " ^ opt_to_string Int.toString Int.maxInt ^
               "\n");

let
  val _ = print "Compiling system specific functions ("
  val sigfile = fullPath [holdir, "tools", "Holmake", "Systeml.sig"]
  val uifile = fullPath [holdir, "sigobj", "Systeml.ui"]
  fun to_sigobj s = bincopy s (fullPath [holdir, "sigobj", Path.file s])
  val uifile_content = "$(HOLDIR)/sigobj/Systeml.sig\n"
in
  if not (canread uifile) orelse
     Time.>(modTime sigfile, modTime uifile) orelse
     Position.toInt (OS.FileSys.fileSize uifile) > size uifile_content
     (* if the file is this large it's been generated by Moscow ML, or is
        otherwise wrong *)
  then
    let
      val oo = TextIO.openOut uifile
    in
      (* note how this is "compiling" straight into sigobj, rather than
         doing anything in the source directory, tools/Holmake *)
      TextIO.output (oo, uifile_content);
      TextIO.closeOut oo;
      print "sig "
    end
  else ();
  to_sigobj sigfile;
  let val oo = TextIO.openOut (fullPath [holdir, "sigobj", "Systeml.uo"])
  in
    TextIO.output (oo, fullPath [holdir, "sigobj", "Systeml.sml"] ^ "\n");
    TextIO.closeOut oo
  end;
  to_sigobj (fullPath [holmakedir, "Systeml.sml"]);
  print "sml)\n"
end;

val _ = echo "Beginning configuration.";

(* ----------------------------------------------------------------------
    remove the quotation filter from the bin directory, if it exists
  ---------------------------------------------------------------------- *)

val _ = let
  val unquote = fullPath [holdir, "bin", xable_string "unquote"]
in
  if FileSys.access(unquote, [FileSys.A_READ]) then
    (print "Removing old quotation filter from bin/\n";
     FileSys.remove unquote
     handle Thread.Thread.Interrupt => raise Thread.Thread.Interrupt
          | _ => print "*** Tried to remove quotation filter from bin/ but \
                       \couldn't!  Proceeding anyway.\n")
  else ()
end



fun die s = (print s; print "\n"; Process.exit Process.failure)

local
  val cdir = FileSys.getDir()
  val systeml = liftstatus systeml
  val system_ps = liftstatus system_ps
  val toolsdir = fullPath [holdir, "tools-poly"]
  val lexdir = fullPath [holdir, "tools", "mllex"]
  val yaccdir = fullPath [holdir, "tools", "mlyacc", "src"]
  val qfdir = fullPath [holdir, "tools", "quote-filter"]
  val hmakedir = fullPath [toolsdir, "Holmake"]
  val hmakebin = fullPath [holdir, "bin", "Holmake"]
  val buildbin = fullPath [holdir, "bin", "build"]
  val qfbin = fullPath [holdir, "bin", "unquote"]
  val lexer = fullPath [lexdir, "mllex.exe"]
  val yaccer = fullPath [yaccdir, "mlyacc.exe"]
  fun copyfile from to =
    let val instrm = BinIO.openIn from
        val ostrm = BinIO.openOut to
        val v = BinIO.inputAll instrm
    in
      BinIO.output(ostrm, v);
      BinIO.closeIn instrm;
      BinIO.closeOut ostrm
    end;
  fun remove f = (FileSys.remove f handle OS.SysErr _ => ())
in

(* Remove old files *)

val _ = remove hmakebin;
val _ = remove buildbin;
val _ = remove lexer;
val _ = remove yaccer;
val _ = remove qfbin;
val _ = remove (fullPath [hmakedir, "Lexer.lex.sml"]);
val _ = remove (fullPath [hmakedir, "Parser.grm.sig"]);
val _ = remove (fullPath [hmakedir, "Parser.grm.sml"]);


fun polyc_compile0 s tgt =
  let
    val cline = POLYC ^ " -o " ^ tgt ^ " " ^ s
  in
    echov cline;
    system_ps cline
  end

fun mlton_compile mltonp mlbfile_opt s tgt =
  case mlbfile_opt of
      NONE => polyc_compile0 s tgt
    | SOME mlbfile_d =>
      let
        val _ = print ("Using mlton to compile "^mlbfile_d^"\n")
        val _ = print "  (this can be overridden with 'val MLTON = NONE;'\
                      \ (without single-quotes)\n\
                      \   in tools-poly/poly-includes.ML)\n"
        val {dir=mlbdir,file=mlbfile} = OS.Path.splitDirFile mlbfile_d
        val {base=mlbbase, ...} = OS.Path.splitBaseExt mlbfile
        val tgt_f = OS.Path.file tgt
        val _ = tgt_f = mlbbase orelse
                die ("stem of mlb-file "^mlbfile_d^
                     " doesn't match file of target: "^ tgt)
        val cline = mltonp ^ " " ^ mlbfile_d
        val generated_file =
            OS.Path.joinDirFile {dir = mlbdir, file = mlbbase}
      in
        echov cline ;
        system_ps cline ;
        OS.FileSys.rename{old = generated_file, new = tgt}
      end

val polyc_compile =
    case MLTON of
        NONE => (fn _ => polyc_compile0)
      | SOME p => mlton_compile p

fun work_in_dir tgtname d f =
  (echo ("Making " ^ tgtname); FileSys.chDir d; f(); FileSys.chDir cdir)
    handle e => die ("Failed to make "^tgtname^" ("^General.exnMessage e^")")

(* mllex *)
val _ = work_in_dir "mllex"
          lexdir
          (fn () => polyc_compile NONE "poly-mllex.ML" "mllex.exe")

(* mlyacc *)
val _ = work_in_dir
          "mlyacc" yaccdir
          (fn () => (systeml [lexer, "yacc.lex"];
                     polyc_compile NONE "poly-mlyacc.ML" "mlyacc.exe"))

(* Holmake *)
val _ = work_in_dir
          "Holmake" (fullPath [HOLDIR, "tools", "Holmake", "poly"])
          (fn () => (OS.FileSys.chDir "..";
                     systeml [lexer, "HolLex"];
                     OS.FileSys.chDir "poly";
                     polyc_compile (SOME "../mlton/Holmake.mlb")
                                   "poly-Holmake.ML" hmakebin))

(* unquote - the quotation filter *)
val _ = work_in_dir "unquote" qfdir
                    (fn () => (polyc_compile NONE "poly-unquote.ML" qfbin))

(* holdeptool *)
val _ = work_in_dir "holdeptool" (fullPath [HOLDIR, "tools", "Holmake"])
                    (fn () =>
                        polyc_compile NONE
                          "poly-holdeptool.ML"
                          (fullPath [HOLDIR, "bin", "holdeptool.exe"]))

(* build *)
val _ = work_in_dir "build" toolsdir
                    (fn () => polyc_compile (SOME "../tools/build.mlb")
                                            "poly-build.ML" buildbin)

(* heapname *)
val _ = work_in_dir
          "heapname" toolsdir
          (fn () => polyc_compile NONE "heapname.ML"
                                        (fullPath [HOLDIR,"bin","heapname"]))

(* buildheap *)
val _ = work_in_dir
          "buildheap" toolsdir
          (fn () => polyc_compile NONE "buildheap.ML"
                                        (fullPath [HOLDIR, "bin", "buildheap"]))

(* genscriptdep *)
val _ = work_in_dir "genscriptdep"
                    (fullPath [HOLDIR, "tools", "Holmake", "poly"])
                    (fn () => polyc_compile NONE "poly-genscriptdep.ML"
                                 (fullPath [HOLDIR, "bin", "genscriptdep"]))

(* linkToSigobj *)
val _ = work_in_dir
          "linkToSigobj"
          (fullPath [HOLDIR, "tools", "Holmake", "poly"])
          (fn () => polyc_compile NONE "poly-linkToSigobj.ML"
                                  (fullPath [HOLDIR, "bin", "linkToSigobj"]))

end (* local *)

(*---------------------------------------------------------------------------
    Instantiate tools/editor-modes/emacs/hol-mode.src, and put it into
    hol-mode.el in the same directory.
 ---------------------------------------------------------------------------*)

val _ =
 let open TextIO
     val _ = echo "Making hol-mode.el (for Emacs)"
     val src = fullPath [holdir, "tools", "editor-modes", "emacs", "hol-mode.src"]
    val target = fullPath [holdir, "tools", "editor-modes", "emacs", "hol-mode.el"]
 in
    fill_holes (src, target)
      ["(defcustom hol-executable HOL-EXECUTABLE\n"
        -->
       ("(defcustom hol-executable \n  "^
        quote (fullPath [holdir, "bin", "hol"])^"\n"),
       "(defcustom holmake-executable HOLMAKE-EXECUTABLE\n"
        -->
       ("(defcustom holmake-executable \n  "^
        quote (fullPath [holdir, "bin/Holmake"])^"\n")]
 end;

(*---------------------------------------------------------------------------
    Instantiate tools/editor-modes/vim/*.src
 ---------------------------------------------------------------------------*)

val _ =
  let open TextIO
    val _ = echo "Making tools/editor-modes/vim/*"
    val pref = fullPath [holdir, "tools", "editor-modes", "vim"]
    val src1 = fullPath [pref, "hol.src"]
    val tar1 = fullPath [pref, "hol.vim"]
    val src2 = fullPath [pref, "vimhol.src"]
    val tar2 = fullPath [pref, "vimhol.sml"]
    val tar3 = openOut (fullPath [pref, "hol-config.sml"])
    val tar4 = openOut (fullPath [pref, "filetype.vim"])
    fun qstr s = (quote s)^"\n"
    val holpipe = qstr(fullPath [pref, "fifo"])
    val tmpprefix = qstr("/tmp/vimhol")
  in
    fill_holes (src1,tar1)
      ["let s:defaultholpipe =" -->
       "let s:defaultholpipe = "^holpipe,
       "let s:tmpprefix =" -->
       "let s:tmpprefix = "^tmpprefix];
    fill_holes (src2,tar2)
      ["val defaultFifoPath ="-->
       "val defaultFifoPath = "^holpipe];
    output(tar3, "use "^(qstr tar2));
    closeOut tar3;
    output(tar4,"augroup filetypedetect\n");
    output(tar4,"  au BufRead,BufNewFile *.sml let maplocalleader = \"h\" | source "^tar1^"\n");
    output(tar4,"  au BufRead,BufNewFile *?Script.sml setlocal filetype=hol4script\n");
    output(tar4,"  \" recognise pre-munger files as latex source\n");
    output(tar4,"  au BufRead,BufNewFile *.htex setlocal filetype=htex syntax=tex\n");
    output(tar4,"  \"Uncomment the line below to automatically load Unicode\n");
    output(tar4,"  \"au BufRead,BufNewFile *?Script.sml source "^fullPath [pref, "holabs.vim"]^"\n");
    output(tar4,"  \"Uncomment the line below to fold proofs\n");
    output(tar4,"  \"au BufRead,BufNewFile *?Script.sml setlocal foldmethod=syntax foldnestmax=1\n");
    output(tar4,"augroup END\n");
    closeOut tar4
  end;





(*---------------------------------------------------------------------------
      Generate shell scripts for running HOL.
 ---------------------------------------------------------------------------*)

val _ =
   let
      val _ = echo "Generating bin/hol."
      val target      = fullPath [holdir, "bin", "hol.bare"]
      val target_boss = fullPath [holdir, "bin", "hol"]
      val hol0_heap   = protect(fullPath[HOLDIR,"bin", "hol.state0"])
      val hol_heapcalc=
            "`" ^ protect(fullPath[HOLDIR,"bin","heapname"]) ^ "`"
      fun TP s = protect(fullPath[HOLDIR, "tools-poly", s])
      val prelude = ["Arbint", "Arbrat", TP "prelude.ML"]
      val prelude2 = prelude @ [TP "prelude2.ML"]
   in
      (* "unquote" scripts use the unquote executable to provide nice
         handling of double-backquote characters *)
      emit_hol_script target hol0_heap prelude;
      emit_hol_script target_boss hol_heapcalc prelude2
   end

val _ = print "\nFinished configuration!\n"
