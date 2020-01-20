open OS.Process

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

fun read_from_stream is n = TextIO.input is

fun open_files b infn outfn =
    let
      open TextIO
      val is = TextIO.openIn infn
               handle OS.SysErr _ =>
                      (output(stdErr, "Error opening "^infn^"\n");
                       exit failure)
      val os = TextIO.openOut outfn
               handle Io {cause = OS.SysErr (_, eo), ...} =>
                      (case eo of
                           SOME e => output(stdErr, OS.errorMsg e)
                         | NONE => ();
                       exit failure)
      in
        (is, os, b, false)
    end

fun usage status =
    (TextIO.output(TextIO.stdErr,
                   "Usage:\n  " ^ CommandLine.name() ^
                   " [[-i] <inputfile> <outputfile>] | -h | -n | --quotefix\n");
     exit status)

val (instream, outstream, intp, qfixp) =
    case CommandLine.arguments() of
        [] => (TextIO.stdIn, TextIO.stdOut, true, false)
      | ["-h"] => usage success
      | ["-n"] => (TextIO.stdIn, TextIO.stdOut, false, false)
      | [ifile, ofile] => open_files false ifile ofile
      | ["-i", ifile, ofile] => open_files true ifile ofile
      | ["--quotefix"] => (TextIO.stdIn, TextIO.stdOut, false, true)
      | _ => usage failure

open QuoteFilter.UserDeclarations
val state as QFS args = newstate intp


(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)
fun loop() =
  let
    val lexer = #2 o QuoteFilter.makeLexer (read_from_stream instream) state
    fun coreloop () =
      case lexer() of
          "" => ()
        | s => (TextIO.output(outstream, s); TextIO.flushOut outstream;
                coreloop())
  in
    coreloop() handle Interrupt => (resetstate state; loop())
  end

val _ = loop()
val _ = TextIO.closeOut outstream
val _ = exit success
