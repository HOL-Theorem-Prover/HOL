val cmdline_args = CommandLine.arguments()
fun warn s = (TextIO.output(TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

val holdir   =
    case cmdline_args of
      [x] => x
    | _ => (warn "Must specify HOLDIR as first and only argument\n";
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

val config_src = fullPath [holdir, "tools", "configure.sml"]
val config_dest = fullPath [holdir, "tools", "newconfig.sml"]

val _ = fill_holes(config_src, config_dest)
        ["val mosmldir =" --> mosmldir,
         "val holdir =" --> holdir]



val _ - print "Configuring the system\n";
val _ = FileSys.mkDir (fullPath [holdir, "src", "0"]) handle _ => ()
val _ = Process.system ("mosml < \"" ^ config_dest ^ "\"")

val _ = print "Setting up Globals.sml file\n";
val _ = fill_holes(fullPath [holdir, "src", "0", "Globals.sml"],
                   fullPath [holdir, "sigobj", "Globals.sml"])

val _ = FileSys.chDir (fullPath [holdir, "sigobj"])
val _ = Systeml.systeml [fullPath [holdir, "tools", "Holmake", "Holmake"],
                         "Globals.uo"]

val _ = print "Building the help system \n";
val _ = Systeml.systeml [fullPath [holdir, "bin", "build"], "help"];


val _ = print "\nFinished configuration!\n";
val _ = Process.exit Process.success;