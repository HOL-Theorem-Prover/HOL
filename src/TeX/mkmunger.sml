local
open HolKernel Parse
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
  fun setwidth i = mungeLex.UserDeclarations.width := i
  fun setoverrides s = mungeTools.user_overrides := mungeTools.read_overrides s
  val run_lexer = ref true
  fun proc_args args =
      case args of
        [] => ()
      | ["-index"] => mungeTools.usage()
      | ["-index", basename] => (holindex.holindex basename; run_lexer := false)
      | s :: rest => let
        in
          case parseWidth s of
            SOME i => (setwidth i ; proc_args rest)
          | NONE => let
            in
              case s of
                "--nomergeanalysis" => (set_trace "pp_avoids_symbol_merges" 0;
                                        proc_args rest)
              | _ => (setoverrides s ; proc_args rest)
            end
        end
  val _ = proc_args (CommandLine.arguments())
in
  if (!run_lexer) then lexer() else ()
end
end

