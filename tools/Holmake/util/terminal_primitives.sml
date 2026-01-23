structure terminal_primitives :> terminal_primitives =
struct

(* this is bogus, but seems the best we can do *)
fun strmIsTTY s = true


fun TERM_isANSI () =
    case OS.Process.getEnv "TERM" of
        NONE => false
      | SOME t =>
          String.isPrefix "xterm" t orelse
          String.isPrefix "screen" t orelse
          String.isPrefix "tmux" t orelse
          t = "eterm-color"

end
