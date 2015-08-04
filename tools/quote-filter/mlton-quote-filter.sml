open OS.Process
open filter.UserDeclarations

fun slave (input, outstream) state = let
   val lexer = filter.makeLexer input state
in
   lexer();
   TextIO.closeOut outstream;
   exit success
end

fun noninteractive (is,os) = let
  fun input n = TextIO.input is
in
  (fn () => slave(input, os) (newstate os))
end

fun interactive () = let
  open MLton.Thread
  val out = TextIO.stdOut
  fun input _ = TextIO.input TextIO.stdIn
  fun go() = prepare (new (slave (input, out)), newstate out)
  fun interrupt_handler _ = go()

  val h = MLton.Signal.Handler.handler interrupt_handler
in
  MLton.Signal.setHandler(Posix.Signal.int, h);
  switch interrupt_handler
end

val go : unit -> unit =
    case CommandLine.arguments() of
        [] => interactive
      | [ifile, ofile] =>
        let
          open TextIO
          val is = openIn ifile
                   handle OS.SysErr _ =>
                          (output(stdErr, "Error opening "^ifile^"\n");
                           exit failure)
          val os = openOut ofile
                   handle IO.Io {cause = OS.SysErr (_, eo), ...} =>
                          (case eo of
                             SOME e => output(stdErr, OS.errorMsg e)
                            | NONE => ();
                           exit failure)
        in
          noninteractive (is,os)
        end
      | _ => (TextIO.output(TextIO.stdErr,
                            "Usage:\n  " ^ CommandLine.name() ^
                            " [<inputfile> <outputfile>]\n");
              exit failure)

val _ = go()
