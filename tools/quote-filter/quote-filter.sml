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

open QuoteFilter.UserDeclarations
val state as QFS args = newstate ()


(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)
val lexer = QuoteFilter.makeLexer (read_from_stream instream) state
fun lexopt() =
  case lexer () of
      "" => NONE
    | s => SOME s

fun loop() =
  case (lexopt() handle Interrupt => (resetstate state; SOME "")) of
      NONE => ()
    | SOME s => (TextIO.output(outstream, s); TextIO.flushOut outstream; loop())

val _ = loop()
val _ = TextIO.closeOut outstream
val _ = exit success
