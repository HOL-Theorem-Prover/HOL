val cmdline_args = CommandLine.arguments()
fun warn s = (TextIO.output(TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

val holdir   = hd cmdline_args
  handle Empty => (warn "Must specify HOLDIR as first and only argument\n";
                   Process.exit Process.failure)

fun butlast0 _ [] = raise Fail "butlast - empty list"
  | butlast0 acc [x] = List.rev acc
  | butlast0 acc (h::t) = butlast0 (h::acc) t
fun butlast l = butlast0 [] l

val mosmldir =
  case Process.getEnv "MOSMLLIB" of
    (* note that if this code is running at all, the MOSMLLIB variable
       will be set because Moscow ML under Windows depends on it *)
    NONE => (warn "No MOSMLLIB environment variable!!\n";
             Process.exit Process.failure)
  | SOME s => let
      val {arcs,isAbs,vol} = Path.fromString s
      val newarcs = butlast arcs
    in
      Path.toString {arcs = newarcs, isAbs = isAbs, vol = vol}
    end



(*---------------------------------------------------------------------------
          String and path operations.
 ---------------------------------------------------------------------------*)

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

val compiler  = fullPath [mosmldir, "bin/mosmlc.exe"]
val sigobj = fullPath [holdir, "sigobj"]

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

open Systeml;
val systeml = winnt_systeml

val _ = echo "\nBeginning configuration.";

(*---------------------------------------------------------------------------
    Install the given paths etc in Holmake/Holmake.src, then compile
    Holmake (bypassing the makefile in directory Holmake), then put it
    in bin/Holmake.
 ---------------------------------------------------------------------------*)
fun mk_xable file =   (* returns the name of the executable *)
  let val exe = file^".exe"
      val _ = FileSys.remove exe handle _ => ()
  in
    FileSys.rename{old=file, new=exe};
    exe
  end


val MK_XABLE_RHS =
 "let val exe = file^\".exe\" \
\       val _ = FileSys.remove exe handle _ => () \
\  in \
\    FileSys.rename{old=file, new=exe}; \
\    exe \
\  end"

val _ =
 let val _ = echo "Making bin/Holmake."
     val cdir      = FileSys.getDir()
     val hmakedir  = normPath(Path.concat(holdir, "tools/Holmake"))
     val _         = print ("Changing dir into "^hmakedir^"\n")
     val _         = FileSys.chDir hmakedir
     val src       = "Holmake.src"
     val target    = "Holmake.sml"
     val bin       = fullPath [holdir,   "bin/Holmake"]
  in
    fill_holes (src,target)
       ["val HOLDIR0 ="
          --> String.concat["val HOLDIR0 = ", quote holdir,";\n"],
        "val MOSMLDIR0 ="
          -->  String.concat["val MOSMLDIR0 = ", quote mosmldir, ";\n"],
        "fun MK_XABLE"
          -->  String.concat["fun MK_XABLE file = ", MK_XABLE_RHS, ";\n"],
        "val SYSTEML" --> String.concat["val SYSTEML = winnt_systeml"]];
    systeml [compiler, "-o", bin, target];
    mk_xable bin;
    FileSys.chDir cdir
  end
handle _ => (print "Couldn't build Holmake\n"; Process.exit Process.failure)


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
     val src1    = fullPath [holdir, "tools/Globals.src"]
     val target1 = fullPath [holdir, "tools/Globals.sml"]
     val src2    = fullPath [holdir, "tools/Globals.uo"]
     val target2 = fullPath [sigobj, "Globals.uo"]
     val cd = FileSys.getDir()
  in
   fill_holes (src1,target1)
    ["val HOLDIR =" -->
     String.concat["val HOLDIR = ",quote holdir,";\n"]];
   FileSys.chDir (fullPath [holdir, "tools"]);
   systeml [compiler, "-I", sigobj, "-c", "Globals.sml"];
   Filesys.remove target2 handle _ => ();
   FileSys.rename {old = src2, new = target2};
   FileSys.chDir cd
  end;

(*---------------------------------------------------------------------------
      Generate a shell script for running HOL.
 ---------------------------------------------------------------------------*)

local
  fun fopen file = let
    val _ = FileSys.remove file handle _ => ()
  in
    TextIO.openOut file
  end
  fun munge s = String.translate (fn #"/" => "\\" | c => str c) s
  fun q s = "\""^munge s^"\""
in
  fun emit_hol_script target mosml std_prelude qend = let
    val ostrm = fopen(target^".bat")
    fun output s = TextIO.output(ostrm, s)
  in
    output "@echo off\n";
    output  "rem The bare hol98 script\n\n";
    output (String.concat["call ", q mosml, " -P full ", q std_prelude,
                          " %* ", q qend, "\n"]);
    TextIO.closeOut ostrm
  end;


  fun emit_hol_unquote_script target qfilter mosml std_prelude qinit qend = let
    val ostrm = fopen(target^".bat")
    fun output s = TextIO.output(ostrm, s)
  in
    output  "@echo off\n";
    output  "rem The hol98 script (with quote preprocessing)\n\n";
    output  (String.concat ["call ", q qfilter, " | ", q mosml,
                          " -P full ",
                            q std_prelude, " ", q qinit, " %* ",
                            q qend, "\n"]);
    TextIO.closeOut ostrm
  end
end;


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


val _ = print "\nFinished configuration!\n";
val _ = Process.exit Process.success;