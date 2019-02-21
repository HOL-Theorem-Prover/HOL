val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

use "../Holmake/QuoteFilter.sml";
open OS.Process

fun read_from_stream is n = TextIO.input is

fun open_files b infn outfn =
    let
      open TextIO
      val is = TextIO.openIn infn
               handle OS.SysErr _ =>
                      (output(stdErr, "Error opening "^infn^"\n");
                       exit failure)
      val os = TextIO.openOut outfn
               handle IO.Io {cause = OS.SysErr (_, eo), ...} =>
                      (case eo of
                           SOME e => output(stdErr, OS.errorMsg e)
                         | NONE => ();
                       exit failure)
      in
        (is, os, b)
    end

fun usage status =
    (TextIO.output(TextIO.stdErr,
                   "Usage:\n  " ^ CommandLine.name() ^
                   " [[-i] <inputfile> <outputfile>] | -h | -n\n");
     exit status)



fun main() = let
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
     linked executable as Interrupt exceptions *)
  val _ = Signal.signal(2, Signal.SIG_HANDLE
                               (fn _ => Thread.Thread.broadcastInterrupt()))
  val (instream, outstream, intp) =
    case CommandLine.arguments() of
        [] => (TextIO.stdIn, TextIO.stdOut, true)
      | ["-h"] => usage success
      | ["-n"] => (TextIO.stdIn, TextIO.stdOut, false)
      | [ifile, ofile] => open_files false ifile ofile
      | ["-i", ifile, ofile] => open_files true ifile ofile
      | _ => usage failure

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

  open QuoteFilter.UserDeclarations
  val state as QFS args = newstate intp

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
  exit success
end;
