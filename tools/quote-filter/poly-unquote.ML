val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

use "../Holmake/Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "../Holmake/AttributeSyntax.sig";
use "../Holmake/AttributeSyntax.sml";
use "../Holmake/HolLex.sml";
use "../Holmake/HM_SimpleBuffer.sig";
use "../Holmake/HM_SimpleBuffer.sml";
use "../Holmake/HOLFS_dtype.sml";
use "../Holmake/HFS_NameMunge.sig";
use "../Holmake/poly/HFS_NameMunge.sml";
use "../Holmake/HOLFS_dtype.sml";
use "../Holmake/HOLFileSys.sig";
use "../Holmake/HOLFileSys.sml";
use "../Holmake/HolParser.sig";
use "../Holmake/HolParser.sml";
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
    val read = mkPushTranslator {
      read = read,
      filename = infilename,
      parseError = fn (start, stop) => fn s =>
        TextIO.output (TextIO.stdErr,
          "parse error at " ^ Int.toString start ^ "-" ^ Int.toString stop ^ ": " ^ s ^ "\n"),
      quietOpen = quietOpen
    } (mkStrcode write)

    fun loop () = if read () then () else loop ()
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
