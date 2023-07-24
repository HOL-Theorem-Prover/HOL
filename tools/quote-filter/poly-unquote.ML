val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

use "../Holmake/Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "../Holmake/AttributeSyntax.sig";
use "../Holmake/AttributeSyntax.sml";
use "../Holmake/QuoteFilter.sml";
open OS.Process

fun read_from_stream is n = TextIO.input is;

use "qfilter_util.sig";
use "qfilter_util.sml";

fun main() = let
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
     linked executable as Interrupt exceptions *)
  val _ = Signal.signal(2, Signal.SIG_HANDLE
                               (fn _ => Thread.Thread.broadcastInterrupt()))
  val (instream, outstream, intp, qfixp, cb) =
      qfilter_util.processArgs(false,false,false) (CommandLine.arguments())

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  open QuoteFilter.UserDeclarations
  val state as QFS args = newstate {inscriptp = intp, quotefixp = qfixp}

  fun loop() =
    let
      val lexer = #2 o QuoteFilter.makeLexer (read_from_stream instream) state
      fun coreloop () =
        case lexer() of
            "" => ()
          | s => (TextIO.output(outstream, s); coreloop())
    in
      coreloop() handle Interrupt => (resetstate state; loop())
    end
in
  loop();
  TextIO.closeOut outstream;
  cb();
  exit success
end;
