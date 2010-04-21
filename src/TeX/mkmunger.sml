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
  fun parseWidth s =
      if String.isPrefix "-w" s then let
          val newwidth_s = String.extract(s,2,NONE)
        in
          case Int.fromString newwidth_s of
            NONE => mungeTools.usage()
          | SOME i => SOME i
        end
      else NONE
  fun setwidth i = mungeLex.UserDeclarations.width := i
  fun setoverrides s = mungeTools.user_overrides := mungeTools.read_overrides s
  val run_lexer = ref true
  val _ = case CommandLine.arguments() of
            [] => () 
          | ["-index", basename] => (
                holindex.holindex basename;
                run_lexer := false)
          | [s] => let
            in
              case parseWidth s of
                NONE => setoverrides s
              | SOME i => setwidth i
            end
          | [s1,s2] => let
            in
              case (parseWidth s1, parseWidth s2) of
                (NONE, SOME i) => (setoverrides s1; setwidth i)
              | (SOME i, NONE) => (setoverrides s2; setwidth i)
              | _ => mungeTools.usage()
            end
          | _ => mungeTools.usage()
in
  if (!run_lexer) then lexer() else ()
end
end

