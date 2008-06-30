(* this is an -*- sml -*- file *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
structure Substring = struct
  open Substring
  val all = full
end;

use "filter.sml";
open OS.Process

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

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  open filter.UserDeclarations
  val state as QFS args =
      QFS {output_stream=outstream, comdepth=ref 0, pardepth=ref 0,
           antiquote=ref false, row=ref 0, rowstart=ref 0};


  fun loop() = let
    val lexer = filter.makeLexer (read_from_stream instream) state
  in
    lexer()
    handle Interrupt => (let open filter.UserDeclarations
                         in
                           #comdepth args := 0;
                           #pardepth args := 0;
                           #antiquote args := false;
                           loop()
                         end)
  end
in
  loop();
  TextIO.closeOut outstream;
  exit success
end;

val _ = PolyML.shareCommonData main;
val _ = PolyML.export("unquote", main);
