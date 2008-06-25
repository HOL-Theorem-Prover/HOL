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

  val state = {output_stream=outstream, comdepth=ref 0, pardepth=ref 0, 
               antiquote=ref false, row=ref 0, rowstart=ref 0};


  fun loop() = let
    val lexer = filter.makeLexer (read_from_stream instream) state
  in
    lexer()
    handle Interrupt => (let open filter.UserDeclarations
                         in
                           #comdepth state := 0;
                           #pardepth state := 0;
                           #antiquote state := false;
                           loop()
                         end)
  end
in
  loop();
  TextIO.closeOut outstream;
  exit success
end;

