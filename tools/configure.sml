(*---------------------------------------------------------------------------
              HOL98 configuration script

   First, edit the following user-settable parameters. Then execute this
   file by going

      mosml < configure.sml

 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
          BEGIN user-settable parameters
 ---------------------------------------------------------------------------*)

val mosmldir =
val holdir   =

val OS       = "linux";    (* Operating system; choices are:
                                "linux", "solaris", "unix", "winNT"        *)

val CC       = "gcc";      (* C compiler                                   *)
val GNUMAKE  = "make";     (* for bdd library and SMV                      *)

val DEPDIR   = ".HOLMK";   (* local dir. where Holmake dependencies kept   *)
val LN_S     = "ln -s";    (* only change if you are a HOL developer.      *)

(*---------------------------------------------------------------------------
          END user-settable parameters
 ---------------------------------------------------------------------------*)


app load ["FileSys", "Process", "Path",
          "Substring", "BinIO", "Lexing", "Nonstdio"];

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

(*---------------------------------------------------------------------------
     Load in OS-dependent stuff.
 ---------------------------------------------------------------------------*)


val holmakedir = fullPath [holdir, "tools", "Holmake"];
val compiler = fullPath [mosmldir, "bin", "mosmlc"];

(*---------------------------------------------------------------------------
         First load in systeml functions
 ---------------------------------------------------------------------------*)

val _ =
  if FileSys.access(fullPath [holmakedir, "Systeml.uo"],[FileSys.A_READ])
     andalso
     FileSys.access(fullPath [holmakedir, "Systeml.ui"], [FileSys.A_READ])
  then let val oldloadpath = !loadPath
           val _ = loadPath := !loadPath @ [holmakedir]
       in
         load (fullPath [holmakedir, "Systeml"]);
         loadPath := oldloadpath
       end
  else use (fullPath [holmakedir, "Systeml.sml"]);

open Systeml;

local val OSkind = if OS="linux" orelse OS="solaris" then "unix" else OS
in
val _ = use (fullPath [holdir,"tools/config-"^OSkind^".sml"])
end;

(*---------------------------------------------------------------------------
     Now compile Systeml.sml; if necessary
 ---------------------------------------------------------------------------*)

if not (FileSys.access("Holmake/Systeml.uo", [FileSys.A_READ]))
 then let val dir_0 = FileSys.getDir()
      in FileSys.chDir holmakedir;
         systeml [compiler, "-c", "Systeml.sml"];
         FileSys.chDir dir_0
      end
 else ();


(*---------------------------------------------------------------------------
     Source directories.
 ---------------------------------------------------------------------------*)

val SRCDIRS =
 ["src/portableML", "src/0", "src/parse", "src/bool", "src/marker",
  "src/goalstack",
  "src/taut", "src/compute/src", "src/q", "src/combin", "src/lite",
  "src/refute", "src/simp/src", "src/meson/src","src/basicProof",
  "src/relation", "src/pair/src", "src/sum", "src/one", "src/option",
  "src/num/theories", "src/num/reduce/src", "src/num/arith/src","src/num",
  "src/IndDef",
  "src/datatype/parse", "src/datatype/equiv",  "src/datatype/record",
  "src/datatype",  "src/list/src", "src/tfl/src", "src/unwind", "src/boss",
  "src/string", "src/llist",   "src/pred_set/src", "src/ring/src",
  "src/integer",
  "src/res_quan/src",
  "src/word/theories", "src/word/src",
  "src/finite_map", "src/hol88", "src/real", "src/bag",
  "src/temporal/src", "src/temporal/smv.2.4.3", "src/prob", "src/HolSat",
  "src/muddy/muddyC", "src/muddy", "src/HolBdd"];

(*---------------------------------------------------------------------------
          String and path operations.
 ---------------------------------------------------------------------------*)

fun echo s = (TextIO.output(TextIO.stdOut, s^"\n");
              TextIO.flushOut TextIO.stdOut);

local fun expChar #"\\" = "\\\\"
        | expChar #"\"" = "\\\""
        | expChar ch    = String.str ch
      val exp_bslash = String.translate expChar
in
fun quote s = String.concat["\"", exp_bslash s, "\""]
end;

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
        of ""   => ()
         | line =>
            let val ssline = Substring.all line
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

val _ = echo "\nBeginning configuration.";

(*---------------------------------------------------------------------------
    Install the given paths etc in Holmake/Holmake.src, then compile
    Holmake (bypassing the makefile in directory Holmake), then put it
    in bin/Holmake.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Making bin/Holmake."
     val cdir      = FileSys.getDir()
     val hmakedir  = normPath(Path.concat(holdir, "tools/Holmake"))
     val _         = FileSys.chDir hmakedir
     val src       = "Holmake.src"
     val target    = "Holmake.sml"
     val bin       = fullPath [holdir,   "bin/Holmake"]
     val lexer     = fullPath [mosmldir, "bin/mosmllex"]
     val yaccer    = fullPath [mosmldir, "bin/mosmlyac"]
  in
    fill_holes (src,target)
       ["val HOLDIR0 ="
          --> String.concat["val HOLDIR0 = ", quote holdir,";\n"],
        "val MOSMLDIR0 ="
          -->  String.concat["val MOSMLDIR0 = ", quote mosmldir, ";\n"],
        "fun MK_XABLE"
          -->  String.concat["fun MK_XABLE file = ", MK_XABLE_RHS, ";\n"],
        "val SYSTEML" --> String.concat["val SYSTEML = ", SYSTEML_NAME, ";\n"],
        "val DEFAULT_OVERLAY = _;\n"
          --> "val DEFAULT_OVERLAY = SOME \"Overlay.ui\"\n"];
    systeml [yaccer, "Parser.grm"];
    systeml [lexer, "Lexer.lex"];
    systeml [compiler, "-c", "Parser.sig"];
    systeml [compiler, "-c", "Parser.sml"];
    systeml [compiler, "-c", "Lexer.sml" ];
    systeml [compiler, "-c", "Holdep.sml"];
    systeml [yaccer, "Holmake_parse.grm"];
    systeml [lexer, "Holmake_tokens.lex"];
    systeml [compiler, "-c", "Holmake_types.sig"];
    systeml [compiler, "-c", "Holmake_types.sml"];
    systeml [compiler, "-c", "Holmake_parse.sig"];
    systeml [compiler, "-c", "Holmake_parse.sml"];
    systeml [compiler, "-c", "Holmake_tokens.sml"];
    systeml [compiler, "-c", "Holmake_rules.sig"];
    systeml [compiler, "-c", "Holmake_rules.sml"];
    if OS <> "winNT" then
      systeml [compiler, "-standalone", "-o", bin, target]
    else
      systeml [compiler, "-o", bin, target];
    mk_xable bin;
    FileSys.chDir cdir
  end
handle _ => (print "Couldn't build Holmake\n"; Process.exit Process.failure)

(*---------------------------------------------------------------------------
    Instantiate tools/build.src, compile it, and put it in bin/build.
 ---------------------------------------------------------------------------*)

val _ =
 let open TextIO
     val _ = echo "Making bin/build."
     val src    = fullPath [holdir, "tools/build.src"]
     val target = fullPath [holdir, "tools/build.sml"]
     val bin    = fullPath [holdir, "bin/build"]
     val full_paths =
      let fun ext s = fullPath [holdir,s]
          fun plist [] = raise Fail "plist: empty"
            | plist  [x] = [quote (ext x), "];\n"]
            | plist (h::t) = quote (ext h)::",\n     "::plist  t
      in String.concat o plist
      end
  in
   fill_holes (src,target)
    ["val OS =" --> String.concat["val OS = ", quote OS, ";\n"],
     "val HOLDIR = _;\n" --> String.concat["val HOLDIR = ",quote holdir,";\n"],
     "val DEPDIR = _;\n" --> String.concat["val DEPDIR = ",quote DEPDIR,";\n"],
     "val SRCDIRS = _;\n" --> String.concat["val SRCDIRS = \n","    [",
                                          full_paths SRCDIRS],
     "val GNUMAKE = _;\n" --> String.concat["val GNUMAKE = ",
                                              quote GNUMAKE,";\n"],
     "val EXECUTABLE = _;\n" --> String.concat["val EXECUTABLE = ",
                                          quote(xable_string bin),";\n"]];
   systeml [fullPath [mosmldir, "bin/mosmlc"], "-o", bin,
            "-I", holmakedir, target];
   FileSys.remove (fullPath [holdir,"tools/build.ui"]);
   FileSys.remove (fullPath [holdir,"tools/build.uo"]);
   mk_xable bin
  end;


(*---------------------------------------------------------------------------
    Instantiate tools/hol98-mode.src, and put it in tools/hol98-mode.el
 ---------------------------------------------------------------------------*)

val _ =
 let open TextIO
     val _ = echo "Making hol98-mode.el (for Emacs)"
     val src = fullPath [holdir, "tools/hol98-mode.src"]
    val target = fullPath [holdir, "tools/hol98-mode.el"]
 in
    fill_holes (src, target)
      ["(defvar hol98-executable HOL98-EXECUTABLE\n"
        -->
       ("(defvar hol98-executable \n  "^
        quote (fullPath [holdir, "bin/hol.unquote"])^"\n")]
 end;


(*---------------------------------------------------------------------------
    Fill in some slots in the Standard Prelude file, and write it to
    std.prelude in the top level of the distribution directory.
 ---------------------------------------------------------------------------*)

val _ =
 let open TextIO
     val _ = echo "Setting up the standard prelude."
     val src    = fullPath [holdir, "tools/std.prelude.src"]
     val target = fullPath [holdir, "std.prelude"]
 in
   fill_holes (src,target)
     ["val SIGOBJ = __"
        -->
      String.concat["      val SIGOBJ = toString(fromString(concat\n",
                     "                    (", quote holdir,
                     ",", quote"sigobj",")))\n"]
     ]
 end;

(*---------------------------------------------------------------------------
     Set the location of HOLDIR in Globals.src and write it to
     src/0/Globals.sml
 ---------------------------------------------------------------------------*)

val _ =
 let open TextIO
     val _ = echo "Setting up src/0/Globals.sml."
     val src    = fullPath [holdir, "tools/Globals.src"]
     val target = fullPath [holdir, "src/0/Globals.sml"]
  in
   fill_holes (src,target)
    ["val HOLDIR =" -->
     String.concat["val HOLDIR = ",quote holdir,";\n"]]
  end;

(*---------------------------------------------------------------------------
      Generate shell scripts for running HOL.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Generating bin/hol."
     val mosml       = fullPath [mosmldir, "bin/mosml"]
     val std_prelude = fullPath [holdir, "std.prelude"]
     val target      = fullPath [holdir, "bin/hol.bare"]
     val qend        = fullPath [holdir, "tools/end-init.sml"]
     val target_boss = fullPath [holdir, "bin/hol"]
     val qend_boss   = fullPath [holdir, "tools/end-init-boss.sml"]
 in
   emit_hol_script target mosml std_prelude qend;
   emit_hol_script target_boss mosml std_prelude qend_boss
 end;

val _ =
 let val _ = echo "Generating bin/hol.unquote."
     val qfilter     = fullPath [holdir,   "bin/unquote"]
     val target      = fullPath [holdir,   "bin/hol.bare.unquote"]
     val target_boss = fullPath [holdir,   "bin/hol.unquote"]
     val mosml       = fullPath [mosmldir, "bin/mosml"]
     val std_prelude = fullPath [holdir,   "std.prelude"]
     val qinit       = fullPath [holdir,   "tools/unquote-init.sml"]
     val qend        = fullPath [holdir,   "tools/end-init.sml"]
     val qend_boss   = fullPath [holdir,   "tools/end-init-boss.sml"]
 in
  emit_hol_unquote_script target qfilter mosml std_prelude qinit qend;
  emit_hol_unquote_script target_boss qfilter mosml std_prelude qinit qend_boss
 end;

(*---------------------------------------------------------------------------
    Compile the quotation preprocessor used by bin/hol.unquote and
    put it in bin/
 ---------------------------------------------------------------------------*)

val _ =
  if OS <> "winNT"
  then let val _ = print "Attempting to compile quote filter ... "
           open Process
           fun make_src () = let
             val qfdir = fullPath [holdir, "src/quote-filter"]
           in
             system ("cd "^qfdir^" ; make -s filter.c")
           end
           val src    = fullPath [holdir, "src/quote-filter/filter.c"]
           val target = fullPath [holdir, "bin/unquote"]
           fun check_src () =
               FileSys.access(src, [FileSys.A_READ]) orelse
               (print "(filter.c: ";
                if make_src() = success then
                  (print "OK) "; true)
                else (print "failed!) "; false))
       in
         if check_src() andalso
            systeml [CC,src,"-o",target] = success
         then (mk_xable target; print "successful.\n") handle _
                => print(String.concat["\n>>>>>Failed to move quote filter!",
                              "(continuing anyway)\n\n"])
         else print
             "\n>>>>>>Couldn't compile quote filter! (continuing anyway)\n\n"
       end
  else let
    val src = fullPath[holdir, "tools", "win-binaries", "hol_filt.exe"]
    val target = fullPath[holdir, "bin", "unquote.exe"]
    val instrm = BinIO.openIn src
    val ostrm = BinIO.openOut target
    val v = BinIO.inputAll instrm
    val _ = BinIO.output(ostrm,v)
  in
    BinIO.closeIn instrm;
    BinIO.closeOut ostrm
  end
handle e =>
  print"\n>>>>>>Couldn't install quote filter! (continuing anyway)\n\n";


(*---------------------------------------------------------------------------
    Configure the muddy library.
 ---------------------------------------------------------------------------*)

local val CFLAGS =
        case OS
         of "linux"   => SOME " -Dunix -O3 -fPIC $(CINCLUDE)"
          | "solaris" => SOME " -Dunix -O3 $(CINCLUDE)"
          |     _     => NONE
      val DLLIBCOMP =
        case OS
         of "linux"   => SOME "ld -shared -o $@ $(COBJS) $(LIBS)"
          | "solaris" => SOME "ld -G -B dynamic -o $@ $(COBJS) $(LIBS)"
          |    _      => NONE
      val ALL =
        if OS="linux" orelse OS="solaris"
        then SOME " muddy.so"
        else NONE
in
val _ =
 let open TextIO
     val _ = echo "Setting up the muddy library Makefile."
     val src    = fullPath [holdir, "tools/makefile.muddy.src"]
     val target = fullPath [holdir, "src/muddy/muddyC/Makefile"]
     val (cflags, dllibcomp, all) =
       case (CFLAGS, DLLIBCOMP, ALL) of
         (SOME s1, SOME s2, SOME s3) => (s1, s2, s3)
       | _ => let
         in
           print (String.concat
                  ["   Warning! (non-fatal):\n    The muddy package is not ",
                   "expected to build in OS flavour ", quote OS, ".\n",
                   "   On winNT, muddy will be installed from binaries.\n",
                   "   End Warning.\n"]);
           ("unknownOS", "unknownOS", "unknownOS")
         end
  in
     fill_holes (src,target)
       ["MOSMLHOME=\n"  -->  String.concat["MOSMLHOME=", mosmldir,"\n"],
        "CC=\n"         -->  String.concat["CC=", CC, "\n"],
        "CFLAGS="       -->  String.concat["CFLAGS=",cflags,"\n"],
        "all:\n"        -->  String.concat["all: ",all,"\n"],
        "DLLIBCOMP"     -->  String.concat["\t", dllibcomp, "\n"]
        ]
  end
end;

(*---------------------------------------------------------------------------
           Configure the help database
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Setting up the help source directory."
     val src     = fullPath [holdir, "tools", "makebase.src"]
     val target  = fullPath [holdir, "help", "src", "makebase.sml"]
     val src1    = fullPath [holdir, "tools", "Holmakefile.help.src"]
     val target1 = fullPath [holdir, "help", "src", "Holmakefile"]
 in
  fill_holes (src,target)
   ["val HOLpath = __;\n"
      --> String.concat["val HOLpath = ", quote holdir, ";\n"]];
  fill_holes (src1,target1)
   ["(1)\n" --> String.concat["\tMOSMLC -o ",
                              xable_string "makebase", " makebase.uo\n"],
    "(2)\n" --> String.concat["\tMOSMLC -o ",
                              xable_string "Doc2Html", " Doc2Html.uo\n"],
    "(3)\n" --> String.concat["\tMOSMLC -o ",
                              xable_string "Doc2Tex", " Doc2Tex.uo\n"]]
 end;

val _ = print "\nFinished configuration!\n";
