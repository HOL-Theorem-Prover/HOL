(*---------------------------------------------------------------------------
              HOL98 configuration script

   First, edit the following user-settable parameters. Then execute this
   file by going

      mosml < configure.sml

 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
          BEGIN user-settable parameters
 ---------------------------------------------------------------------------*)

val mosmldir = ;
val holdir   = ;
val OS       = "linux";          (* Operating system; choices are:
                                "linux", "solaris", "unix", "winNT" *)

val CC       = "gcc";     (* C compiler (for building quote filter)        *)
val GNUMAKE  = "gnumake"; (* for robdd library                             *)

val DEPDIR   = ".HOLMK";  (* local dir. where Holmake dependencies kept    *)
val LN_S     = "ln -s";   (* only change if you are a HOL developer.       *)

(*---------------------------------------------------------------------------
          END user-settable parameters
 ---------------------------------------------------------------------------*)


app load ["FileSys", "Process", "Path", "Substring"];

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

(*---------------------------------------------------------------------------
     Load in OS-dependent stuff.
 ---------------------------------------------------------------------------*)

local val OSkind = if OS="linux" orelse OS="solaris" then "unix" else OS
in
val _ = use (fullPath [holdir,"tools/config-"^OSkind^".sml"])
end;


(*---------------------------------------------------------------------------
     Source directories.
 ---------------------------------------------------------------------------*)

val SRCDIRS =
 ["src/portableML", "src/0", "src/parse",
  "src/bool", "src/basicHol90", "src/compute/src", "src/goalstack", "src/q",
  "src/combin", "src/refute", "src/simp/src", "src/meson/src","src/basicProof",
  "src/relation", "src/pair/src", "src/sum", "src/one", "src/option",
  "src/num/theories", "src/num/reduce/src", "src/num/arith/src","src/num",
  "src/hol88", "src/taut", "src/ind_def/src", "src/IndDef",
  "src/datatype/parse", "src/datatype/equiv",  "src/datatype/record",
  "src/datatype",  "src/list/src", "src/tree", "src/datatype/basicrec",
  "src/datatype/mutrec/utils", "src/datatype/mutrec",
  "src/datatype/nestrec", "src/datatype/mutual",
  "src/decision/src", "src/tfl/src", "src/unwind", "src/boss", "src/llist",
  "src/integer", "src/res_quan/src", "src/set/src", "src/pred_set/src",
  "src/string/theories", "src/string/src",
  "src/word/theories", "src/word/src", "src/BoyerMoore",
  "src/hol90", "src/finite_map", "src/real", "src/bag", "src/ring/src", 
  "src/temporal/src"] @
 (if OS = "linux" orelse OS = "solaris" then ["src/muddy", "src/HolBdd"]
  else []);


(*---------------------------------------------------------------------------
          String and path operations.
 ---------------------------------------------------------------------------*)

val space  = " ";
fun echo s = (TextIO.output(TextIO.stdOut, s^"\n");
              TextIO.flushOut TextIO.stdOut);

local val expand_backslash =
            String.translate
                (fn #"\\" => "\\\\"
                  | #"\"" => "\\\""
                  | ch => String.str ch)
in
fun quote s = String.concat["\"", expand_backslash s, "\""]
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

fun full_paths (ind,holdir) =
  let fun ext s = Path.concat(holdir,s)
      fun plist [] = raise Fail "plist: empty"
        | plist  [x] = [quote (ext x), "];\n"]
        | plist (h::t) = quote (ext h)::",\n"::ind::plist  t
  in
   String.concat o plist
  end;

val _ = echo "\nBeginning configuration.";

(*---------------------------------------------------------------------------
    Install the given paths etc in Holmake/Holmake.src, then compile
    Holmake (bypassing the makefile in directory Holmake), then put it
    in bin/Holmake.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Making bin/Holmake."
     val current_dir = FileSys.getDir()
     val hmakedir  = normPath(Path.concat(holdir, "tools/Holmake"))
     val _ = FileSys.chDir hmakedir
     val src       = "Holmake.src"
     val target    = "Holmake.sml"
     val bin       = fullPath [holdir, "bin/Holmake"]
     val compiler  = fullPath [mosmldir, "bin/mosmlc"]
     val lexer     = fullPath [mosmldir, "bin/mosmllex"]
     val yaccer    = fullPath [mosmldir, "bin/mosmlyac"]
     fun systeml l = let
       val command = String.concat l
     in
       if Process.system command = Process.success then
         ()
       else
         (print ("Executing\n  "^command^"\nfailed.\n");
          raise Fail "")
     end
  in
    fill_holes (src,target)
       ["val HOLDIR = _;\n"
          --> String.concat["val HOLDIR = ",    quote holdir,";\n"],
        "val MOSMLDIR = _;\n"
          -->  String.concat["val MOSMLDIR = ", quote mosmldir, ";\n"],
        "val DEPDIR = _;\n"
          -->  String.concat["val DEPDIR = ",   quote DEPDIR, ";\n"],
        "fun MK_XABLE file = _;\n"
          -->  String.concat["fun MK_XABLE file = ", MK_XABLE_RHS, ";\n"]];
    systeml [yaccer, space, "Parser.grm"];
    systeml [lexer, space, "Lexer.lex"];
    systeml [compiler, " -c ", "Parser.sig"];
    systeml [compiler, " -c ", "Parser.sml"];
    systeml [compiler, " -c ", "Lexer.sml" ];
    systeml [compiler, " -c ", "Holdep.sml"];
    if OS <> "winNT" then
      systeml [compiler, " -standalone -o ", bin, space, target]
    else
      systeml [compiler, " -o ", bin, space, target];
    mk_xable bin;
    FileSys.chDir current_dir
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
  in
   fill_holes (src,target)
    ["val LN_S = _;\n" --> String.concat["val LN_S = ",quote LN_S,";\n"],
     "val HOLDIR = _;\n" --> String.concat["val HOLDIR = ",quote holdir,";\n"],
     "val DEPDIR = _;\n" --> String.concat["val DEPDIR = ",quote DEPDIR,";\n"],
     "val SRCDIRS = _;\n" --> String.concat["val SRCDIRS = \n","    [",
                                          full_paths("     ",holdir) SRCDIRS],
     "val GNUMAKE = _;\n" --> String.concat["val GNUMAKE = ",
                                              quote GNUMAKE,";\n"]];
   Process.system (String.concat
       [fullPath [mosmldir, "bin/mosmlc"], " -o ", bin, space, target]);
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
     val docdirs =
        let val docfile = fullPath[holdir,"tools","documentation-directories"]
            val instr  = openIn docfile
            val wholefile = inputAll instr
            val _ = closeIn instr
        in
          map (fn s => Path.concat(holdir, s))
              (String.tokens Char.isSpace wholefile)
        end
     fun listtostring acc [] = String.concat ("["::List.rev ("]\n"::acc))
       | listtostring acc [x] = String.concat ("["::List.rev ("]\n"::x::acc))
       | listtostring acc (x::xs) = listtostring (", \n     "::x::acc) xs
     val docdirs_str = listtostring [] (map quote docdirs)
 in
   fill_holes (src,target)
     ["val SIGOBJ = __"
        -->
      String.concat["      val SIGOBJ = toString(fromString(concat\n",
                     "                    (", quote holdir,
                     ",", quote"sigobj",")))\n"],
      "val docdirs = __"
      -->
      ("  val docdirs = map (Path.toString o Path.fromString)\n    "^
           docdirs_str)]
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
    ["val HOLDIR = _;\n" --> String.concat["val HOLDIR = ",quote holdir,";\n"]]
  end;

(*---------------------------------------------------------------------------
      Generate a shell script for running HOL.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Generating bin/hol."
     val mosml       = fullPath [mosmldir, "bin/mosml"]
     val std_prelude = fullPath [holdir, "std.prelude"]
     val target      = fullPath [holdir, "bin/hol"]
     val qend        = fullPath [holdir, "tools/end-init.sml"]
 in
   emit_hol_script target mosml std_prelude qend
 end;

(*---------------------------------------------------------------------------
    Compile the quotation preprocessor used by bin/hol.unquote and
    put it in bin/
 ---------------------------------------------------------------------------*)

val _ =
  let val _ = print "Attempting to compile quote filter ... "
      val src    = fullPath [holdir, "src/quote-filter/filter.c"]
      val target = fullPath [holdir, "bin/unquote"]
      open Process
  in
    if OS <> "winNT" then
      if system (String.concat [CC," ", src," -o ", target]) = success then
        (mk_xable target; print "successful.\n")
        handle _ =>
          print(String.concat["\n>>>>>Failed to move quote filter!",
                              "(continuing anyway)\n\n"])
      else
        print "\n>>>>>>Couldn't compile quote filter! (continuing anyway)\n\n"
    else
      FileSys.rename {old = fullPath[holdir, "src/quote-filter/hol_filt.exe"],
                      new = fullPath[holdir, "bin/unquote.exe"]}
 end

(*---------------------------------------------------------------------------
    Generate a shell script for running HOL through a preprocessor.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Generating bin/hol.unquote."
     val qfilter     = fullPath [holdir,   "bin/unquote"]
     val target      = fullPath [holdir,   "bin/hol.unquote"]
     val mosml       = fullPath [mosmldir, "bin/mosml"]
     val std_prelude = fullPath [holdir,   "std.prelude"]
     val qinit       = fullPath [holdir,   "tools/unquote-init.sml"]
     val qend        = fullPath [holdir,   "tools/end-init.sml"]
 in
   emit_hol_unquote_script target qfilter mosml std_prelude qinit qend
 end;

(*
fun help mosmldir holdir =
 let open TextIO
     val _ = echo "Setting up the help database Makefile."
     val src    = Path.concat(holdir, "help/src/Makefile.dbase.src")
     val target = Path.concat(holdir, "help/src/Makefile")
  in
     fill_holes (src,target)
       ["MOSMLHOME=\n" -->  String.concat["MOSMLHOME=", mosmldir,"\n"]]
  end;
*)



(*---------------------------------------------------------------------------
    Configure the muddy library. This is only temporary, until I know
    more about how it should configure on other systems than linux.
 ---------------------------------------------------------------------------*)

val _ = use (fullPath [holdir, "tools", "config-muddy.sml"]);

val _ =
 let open TextIO
     val _ = echo "Setting up the muddy library Makefile."
     val src    = fullPath [holdir, "tools/makefile.muddy.src"]
     val target = fullPath [holdir, "src/muddy/Makefile"]
     val (cflags, dllibcomp, all) =
       case (CFLAGS, DLLIBCOMP, ALL) of
         (SOME s1, SOME s2, SOME s3) => (s1, s2, s3)
       | _ => let
         in
           print (String.concat
                  ["   Warning! (non-fatal):\n    The muddy package is not ",
                   "expected to build in OS flavour ", quote OS,
                   ".\n   Only linux and solaris are currently supported.\n",
                   "   End Warning.\n"]);
           ("unknownOS", "unknownOS", "unknownOS")
         end
  in
     fill_holes (src,target)
       ["MOSMLHOME=\n"  -->  String.concat["MOSMLHOME=", mosmldir,"\n"],
        "CC=\n"         -->  String.concat["CC=", CC,"\n"],
        "CFLAGS="       -->  String.concat["CFLAGS=",cflags,"\n"],
        "all:\n"        -->  String.concat["all: ",all,"\n"],
        "DLLIBCOMP"     -->  String.concat["\t", dllibcomp, "\n"]
        ]
  end;

val _ = print "\nFinished configuration!\n";
