local
open HolKernel Parse
in
fun munger () = let
  val () = Feedback.emit_MESG := false
  val () = Feedback.WARNING_outstream := TextIO.stdErr
  val () = set_trace "Unicode" 1
  val () = set_trace "pp_dollar_escapes" 0
  val () = set_trace "ambiguous grammar warning" 2
  open TextIO
  val lexer = mungeLex.makeLexer (fn n => TextIO.input stdIn)
  val _ = case CommandLine.arguments() of
            [] => ()
          | [fname] => (mungeTools.user_overrides :=
                        mungeTools.read_overrides fname)
          | _ => mungeTools.usage()
in
  lexer()
end
end

