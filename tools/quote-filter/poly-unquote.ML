val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

use "../../src/portableML/DString.sig";
use "../../src/portableML/DString.sml";
use "../../src/portableML/DArray.sig";
use "../../src/portableML/DArray.sml";
use "../Holmake/Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "../parsing/AttributeSyntax.sig";
use "../parsing/AttributeSyntax.sml";
use "../parsing/HolLex.sml";
use "../util/SimpleBuffer.sig";
use "../util/SimpleBuffer.sml";
use "../Holmake/hfs/HOLFS_dtype.sml";
use "../Holmake/hfs/HFS_NameMunge.sig";
use "../Holmake/poly/HFS_NameMunge.sml";
use "../Holmake/hfs/HOLFS_dtype.sml";
use "../Holmake/hfs/HOLFileSys.sig";
use "../Holmake/hfs/HOLFileSys.sml";
use "../../tools-poly/poly/Binarymap.sig";
use "../../tools-poly/poly/Binarymap.sml";
use "../parsing/HOLAst.sig";
use "../parsing/HOLAst.sml";
use "../parsing/HOLParser.sig";
use "../parsing/HOLParser.sml";
use "../parsing/HOLToSML.sig";
use "../parsing/HOLToSML.sml";
use "../parsing/HOLPrinter.sig";
use "../parsing/HOLPrinter.sml";
use "../parsing/HolParser.sig";
use "../parsing/HolParser.sml";
use "quotefix.sig";
use "quotefix.sml";
use "qfilter_util.sig";
use "qfilter_util.sml";

open OS.Process

fun main() = let
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
     linked executable as Interrupt exceptions *)
  val _ = Signal.signal(2, Signal.SIG_HANDLE
                               (fn _ => Thread.Thread.broadcastInterrupt()))
  val {instrm, outstrm, interactive, quotefixp, quietOpen, closefn, infilename} =
      qfilter_util.processArgs(false,false,false,false) (CommandLine.arguments())

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  fun read _ = TextIO.input instrm
  fun write s = TextIO.output (outstrm, s)
  val _ = if quotefixp then
    quotefix.run read write
  else let
    open HolParser.ToSML
    val {read, ...} = mkPullTranslator {
      read = read,
      filename = infilename,
      parseError = HOLParser.simpleParseError,
      quietOpen = quietOpen, canBindStr = true }
    fun loop () = case read () of "" => () | s => (write s; loop ())
    in loop () end
in
  closefn ();
  exit success
end handle e => (
  TextIO.output (TextIO.stdErr, "Uncaught exception" ^
    (case PolyML.Exception.exceptionLocation e of
        NONE => ""
      | SOME {file, startLine, ...} => " at " ^ file ^ ":" ^ FixedInt.toString startLine) ^
    ": " ^ General.exnMessage e);
  PolyML.Exception.reraise e
);
