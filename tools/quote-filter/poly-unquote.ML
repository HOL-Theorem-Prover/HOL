(* this is an -*- sml -*- file *)
PolyML.print_depth 0;
open OS.Process
structure Substring = struct
  open Substring
  val all = full
end;
use "filter.sml";

fun read_from_stream is n = TextIO.input is

fun main() = let
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
     linked executable as Interrupt exceptions *)
  val _ = Signal.signal(2, Signal.SIG_HANDLE
                               (fn _ => Thread.Thread.broadcastInterrupt()))
  val (instream, outstream) =
      case CommandLine.arguments() of
        [] => (TextIO.stdIn, TextIO.stdOut)
      | [ifile, ofile] => let
          open TextIO
          val is = TextIO.openIn ifile
              handle OS.SysErr _ =>
                     (output(stdErr, "Error opening "^ifile^"\n");
                      exit failure)
          val os = TextIO.openOut ofile
              handle IO.Io {cause = OS.SysErr (_, eo), ...} =>
                     (case eo of
                        SOME e => output(stdErr, OS.errorMsg e)
                      | NONE => ();
                      exit failure)
        in
          (is, os)
        end
      | _ => (TextIO.output(TextIO.stdErr,
                            "Usage:\n  " ^ CommandLine.name() ^
                            " [<inputfile> <outputfile>]\n");
              exit failure)

  val _ = filter.UserDeclarations.output_stream := outstream

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  fun loop() = let
    val lexer = filter.makeLexer (read_from_stream instream)
  in
    lexer()
    handle Thread.Thread.Interrupt => (let open filter.UserDeclarations
                         in
                           comdepth := 0;
                           pardepth := 0;
                           antiquote := false;
                           loop()
                         end)
  end
in
  loop();
  TextIO.closeOut outstream;
  exit success
end;

PolyML.export("unquote", main);
