open OS.Process

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

fun read_from_stream is n = TextIO.input is

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
                 handle Io {cause = OS.SysErr (_, eo), ...} =>
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

open filter.UserDeclarations
  val state as QFS args =
      QFS {output_stream=outstream, comdepth=ref 0, pardepth=ref 0,
           antiquote=ref false, row=ref 0, rowstart=ref 0};

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

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

val _ = loop()
val _ = TextIO.closeOut outstream
val _ = exit success
