(*---------------------------------------------------------------------------
              HOL98 configuration script

   First, edit the following user-settable parameters. Then execute this
   file by going

      mosml < configure.sml

 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
          BEGIN user-settable parameters
 ---------------------------------------------------------------------------*)

val mosmldir = "/homes/kl216/lang/ml/mosml"
val holdir   = "/local/scratch/mn200/Work/hol98"
val OS       = "unix";    (* Operating system; alternatives are: winNT      *)
val CC       = "gcc";     (* C compiler (for building quote filter)         *)

val DEPDIR   = ".HOLMK";  (* local dir. where Holmake dependencies kept     *)
val LN_S     = "ln -s";   (* only change if you are a HOL developer.        *)

(*---------------------------------------------------------------------------
          END user-settable parameters
 ---------------------------------------------------------------------------*)


app load ["FileSys", "Process", "Path"];

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

(*---------------------------------------------------------------------------
     Load in OS-dependent stuff.
 ---------------------------------------------------------------------------*)

use (fullPath [holdir,"tools/config-"^OS^".sml"]);


(*---------------------------------------------------------------------------
     Source directories.
 ---------------------------------------------------------------------------*)

val SRCDIRS =
 ["src/portableML", "src/0", "src/parse",
  "src/bool", "src/basicHol90", "src/goalstack", "src/q", "src/combin",
  "src/lite", "src/ho_match", "src/refute", "src/simp/src", "src/meson/src",
  "src/relation", "src/num",
  "src/pair/src", "src/list/src", "src/sum", "src/tree", "src/one",
  "src/option","src/reduce/src", "src/arith/src",
  "src/taut", "src/hol88", "src/ind_def/src", "src/IndDef",
  "src/datatype/parse", "src/datatype/equiv", "src/datatype/basicrec",
  "src/utils", "src/datatype/mutrec", "src/datatype/nestrec",
  "src/datatype/mutual", "src/datatype/record", "src/datatype",
  "src/decision/src", "src/tfl/src", "src/unwind",
  "src/res_quan/theories", "src/res_quan/src", "src/set/src",
  "src/pred_set/src", "src/string/theories", "src/string/src",
  "src/word/theories", "src/word/src", "src/integer", "src/BoyerMoore",
  "src/hol90", "src/boss", "src/finite_map", "src/real", "src/bag"];


(*---------------------------------------------------------------------------
          String and path operations.
 ---------------------------------------------------------------------------*)

val space = " ";
fun quote s = String.concat["\"", s, "\""];
fun echo s  = TextIO.output(TextIO.stdOut, s^"\n");

local val expand_backslash =
        String.translate (fn #"\\" => "\\\\" | ch => Char.toString ch)
in
fun quote s = String.concat["\"", expand_backslash s, "\""]
end;

(*---------------------------------------------------------------------------
      File handling. The following implements a very simple line
      replacement function: it searchs the source file for a line that
      is equal to "redex" and then replaces it by "residue". As it
      searches, it copies lines to the target. Each replacement happens
      once; the replacements occur in order. After the last replacement
      is done, the rest of the source is copied to the target.
 ---------------------------------------------------------------------------*)

fun processLinesUntil (istrm,ostrm) (redex,residue) =
   let open TextIO
       fun loop () =
         case inputLine istrm
          of ""   => ()
           | line =>  if line = redex
                       then output(ostrm, residue)
                       else (output(ostrm, line); loop())
   in loop() end;

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

(*---------------------------------------------------------------------------
  Give tools/Holmake/Holmake.src its paths and compile it and put it in bin.
 ---------------------------------------------------------------------------*)

fun full_paths (ind,holdir) =
  let fun ext s = Path.concat(holdir,s)
      fun plist [] = raise Fail "plist: empty"
        | plist  [x] = [quote (ext x), "];\n"]
        | plist (h::t) = quote (ext h)::",\n"::ind::plist  t
  in
   String.concat o plist
  end;

(*---------------------------------------------------------------------------
    Install the given paths etc in Holmake/Holmake.src, then compile
    Holmake (bypassing the makefile in directory Holmake), then put it
    in bin/Holmake.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Making bin/Holmake."
     val hmakedir  = normPath(Path.concat(holdir, "tools/Holmake"))
     val src       = fullPath [holdir, "tools/Holmake/Holmake.src"]
     val target    = fullPath [holdir, "tools/Holmake/Holmake.sml"]
     val bin       = fullPath [holdir, "bin/Holmake"]
     val compiler  = fullPath [mosmldir, "bin/mosmlc"]^" -I "^hmakedir
     fun atDir s   = fullPath [hmakedir,s]
     fun systeml l = Process.system (String.concat l)
  in
    fill_holes (src,target)
       ["val HOLDIR = _;\n"
          --> String.concat["val HOLDIR = ",    quote holdir,";\n"],
        "val MOSMLDIR = _;\n"
          -->  String.concat["val MOSMLDIR = ", quote mosmldir, ";\n"],
        "val DEPDIR = _;\n"
          -->  String.concat["val DEPDIR = ",   quote DEPDIR, ";\n"],
        "fun MK_XABLE file = _;\n"
          -->  String.concat["fun MK_XABLE file = ", MK_XABLE_RHS, ";\n"],
        "val SRCDIRS = _;\n"
          --> String.concat["val SRCDIRS = \n","    [",
                             full_paths("     ",holdir) SRCDIRS]];
    systeml [compiler, " -c ", atDir "Parser.sig"];
    systeml [compiler, " -c ", atDir "Parser.sml"];
    systeml [compiler, " -c ", atDir "Lexer.sml" ];
    systeml [compiler, " -c ", atDir "Holdep.sml"];
    systeml [compiler, " -o ", bin, space, target];
    mk_xable bin
  end;


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
                                          full_paths("     ",holdir) SRCDIRS]];
   Process.system (String.concat
       [fullPath [mosmldir, "bin/mosmlc"], " -o ", bin, space, target]);
   FileSys.remove (fullPath [holdir,"tools/build.ui"]);
   FileSys.remove (fullPath [holdir,"tools/build.uo"]);
   mk_xable bin
  end;


val _ =
 let open TextIO
     val _ = echo "Setting up the standard prelude."
     val src    = fullPath [holdir, "tools/std.prelude.src"]
     val target = fullPath [holdir, "std.prelude"]
  in
     fill_holes (src,target)
         ["      val SIGOBJ = __\n"
              -->
          String.concat["      val SIGOBJ = toString(fromString(concat\n",
         "                    (", quote holdir, ",", quote"sigobj",")))\n"]]
  end;

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
 in
   emit_hol_script target mosml std_prelude
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
    if system (String.concat [CC," ", src," -o ", target]) = success
    then (mk_xable target; print "successful.\n")
    else print "\n>>>>>>Couldn't compile quote filter! (continuing anyway)\n\n"
 end

(*---------------------------------------------------------------------------
    Generate a shell script for running HOL through a preprocessor.
 ---------------------------------------------------------------------------*)

val _ =
 let val _ = echo "Generating bin/hol.unquote."
     val qfilter = fullPath [holdir, "bin/unquote"]
     val hol     = fullPath [holdir, "bin/hol"]
     val quse    = fullPath [holdir, "tools/use.sml"]
     val target  = fullPath [holdir, "bin/hol.unquote"]
 in
   emit_hol_unquote_script target qfilter hol quse
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

val _ =
 let open TextIO
     val _ = echo "Setting up the robdd library Makefile."
     val src    = fullPath [holdir, "src/robdd/GNUmakefile.src"]
     val target = fullPath [holdir, "src/robdd/GNUmakefile"]
  in
     fill_holes (src,target)
       ["MOSMLHOME:=\n"  -->  String.concat["MOSMLHOME:=", mosmldir,"\n"],
        "HOLDIR:=\n"     -->  String.concat["HOLDIR:=", holdir,"\n"]]
  end;

val _ = print "Finished!\n";
