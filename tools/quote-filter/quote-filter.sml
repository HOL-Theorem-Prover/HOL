open OS.Process

fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

val argv = CommandLine.arguments()

val (instream, outstream) =
    case argv of
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
val _ = filter.INITIAL (createLexerStream instream)

val _ = exit success