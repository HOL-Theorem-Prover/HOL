local
open HolKernel Parse
structure UD = mungeLex.UserDeclarations
in
fun munger () = let
  val () = Feedback.emit_MESG := false
  val () = Feedback.WARNING_outstream := TextIO.stdErr
  val () = set_trace "Unicode" 1
  val () = set_trace "pp_dollar_escapes" 1
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
  fun setwidth i = UD.width := i
  fun setoverrides s = mungeTools.user_overrides := mungeTools.read_overrides s
  fun set_mathmode s = UD.mathmode := SOME (UD.tex_spacing s)
  val run_lexer = ref true
  fun proc_args args =
      case args of
        [] => ()
      | ["-index"] => mungeTools.usage()
      | ["-index", basename] => (holindex.holindex basename; run_lexer := false)
      | "--nomergeanalysis" :: rest => (set_trace "pp_avoids_symbol_merges" 0;
                                        proc_args rest)
      | s :: rest => let
        in
          case parseWidth s of
            SOME i => (setwidth i ; proc_args rest)
          | NONE => let
            in
              if String.isPrefix "-m" s then
                (set_mathmode (String.extract(s,2,NONE)); proc_args rest)
              else
                (setoverrides s ; proc_args rest)
            end
        end
  val _ = proc_args (CommandLine.arguments())
in
  if (!run_lexer) then lexer() else ()
end
end
