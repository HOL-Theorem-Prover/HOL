val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

use "../Holmake/Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "../Holmake/AttributeSyntax.sig";
use "../Holmake/AttributeSyntax.sml";
use "../Holmake/HolLex.sml";
use "../Holmake/QuoteFilter.sml";
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
open OS.Process

fun read_from_stream is n = TextIO.input is;

use "qfilter_util.sig";
use "qfilter_util.sml";

fun main() = let
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
     linked executable as Interrupt exceptions *)
  val _ = Signal.signal(2, Signal.SIG_HANDLE
                               (fn _ => Thread.Thread.broadcastInterrupt()))
  val (instream, outstream, intp, qfixp, oldp, cb) =
      qfilter_util.processArgs(false,false,false,false) (CommandLine.arguments())

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  val _ = PolyML.print_depth 100;
  val loop =
    if oldp orelse qfixp then let
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
      in loop end
    else let
      open HolParser.ToSML
      val read = mkPushTranslator {
        read = read_from_stream instream,
        parseError = fn (start, stop) => fn s =>
          TextIO.output (TextIO.stdErr,
            "parse error at " ^ Int.toString start ^ "-" ^ Int.toString stop ^ ": " ^ s ^ "\n")
      } (mkStrcode (fn s => TextIO.output(outstream, s)))

      fun loop () = if read () then () else loop ()
      in loop end
in
  loop();
  TextIO.closeOut outstream;
  cb();
  exit success
end handle e => (
  TextIO.output (TextIO.stdErr, "Uncaught exception" ^
    (case PolyML.Exception.exceptionLocation e of
        NONE => ""
      | SOME {file, startLine, ...} => " at " ^ file ^ ":" ^ FixedInt.toString startLine) ^
    ": " ^ General.exnMessage e);
  PolyML.Exception.reraise e
);
