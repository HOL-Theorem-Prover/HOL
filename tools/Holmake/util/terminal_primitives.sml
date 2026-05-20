structure terminal_primitives :> terminal_primitives =
struct

(* this is bogus, but seems the best we can do *)
fun strmIsTTY s = true

(* Conservative: no way to portably ask whether stdin is a tty, and
   the consequence of saying "yes" wrongly would be a hung prompt
   waiting on input that will never arrive.  Better to always abort
   in the conflict path under non-Poly/ML systems. *)
fun stdin_is_tty () = false


fun TERM_isANSI () =
    case OS.Process.getEnv "TERM" of
        NONE => false
      | SOME t =>
          String.isPrefix "xterm" t orelse
          String.isPrefix "screen" t orelse
          String.isPrefix "tmux" t orelse
          t = "eterm-color"

end
