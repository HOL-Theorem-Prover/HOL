open OS.Process

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

val (instream, outstream) =
    case CommandLine.arguments() of
      [] => (BasicIO.std_in, TextIO.stdOut)
    | [ifile, ofile] => let
        open TextIO
        val is = BasicIO.open_in ifile
                 handle OS.SysErr _ =>
                        (output(stdErr, "Error opening "^ifile^"\n");
                         exit failure)
        val os = openOut ofile
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

val _ = filter.output_stream := outstream
val instr = createLexerStream instream

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)

fun loop() = filter.INITIAL instr
    handle Interrupt => (filter.comdepth := 0; filter.pardepth := 0;
                         filter.antiquote := false; loop())

val _ = loop()
val _ = exit success
