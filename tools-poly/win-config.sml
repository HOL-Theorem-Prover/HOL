val cmdline_args = CommandLine.arguments()
fun warn s = (TextIO.output(TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)

val holdir =
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
      val newarcs = butlast arcs @ ["bin"]
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

val ostrm = TextIO.openOut (fullPath [holdir, "config-override"])

val _ = FileSys.chDir holdir
val holdir = FileSys.getDir ()

fun pr s = TextIO.output(ostrm, s)
val _ = (pr ("val holdir = \""^holdir^"\"\n");
         pr ("val mosmldir = \""^mosmldir^"\"\n");
         pr ("val OS = \"winNT\"\n");
         pr ("val dynlib_available = true\n");
         TextIO.closeOut ostrm)

val _ = print "Configuring the system\n";
val _ = FileSys.mkDir (fullPath [holdir, "src", "0"]) handle _ => ()
val _ = Process.system ("mosml < tools\\smart-configure.sml")

val _ = let
  val _ = print "Adjusting sigobj/SRCFILES ... "
  val file = fullPath [holdir, "sigobj", "SRCFILES"]
  val instrm = TextIO.openIn file
  fun readlines acc =
      case TextIO.inputLine instrm of
        "" => List.rev acc
      | s => readlines (s::acc)
  val lines = readlines []
  val _ = TextIO.closeIn instrm
  fun adjustline s = fullPath [holdir, s]
  val outstrm = TextIO.openOut file
  val _ = app (fn s => TextIO.output(outstrm, adjustline s)) lines
  val _ = TextIO.closeOut outstrm
in
  print "done\n"
end


val _ = print "Building the help system \n";
val _ = Systeml.systeml [fullPath [holdir, "bin", "build"], "help"];

val _ = Process.exit Process.success;
