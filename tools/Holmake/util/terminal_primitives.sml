structure terminal_primitives :> terminal_primitives =
struct

(* this is bogus, but seems the best we can do *)
fun strmIsTTY s = true

(* Shell out to `test -t 0' as a portable-ish isatty without needing
   the Posix structure (which Moscow ML doesn't provide).  POSIX-style
   shells inherit stdin from the caller, so `test -t 0' in the
   spawned shell sees this process's stdin.  Anywhere /bin/sh or
   `test' aren't available the OS.Process.system call falls through
   to false -- a conservative default, since saying "yes" wrongly
   would mean a hung prompt waiting for input that never arrives. *)
fun stdin_is_tty () =
    OS.Process.isSuccess (OS.Process.system "test -t 0")
    handle _ => false


fun TERM_isANSI () =
    case OS.Process.getEnv "TERM" of
        NONE => false
      | SOME t =>
          String.isPrefix "xterm" t orelse
          String.isPrefix "screen" t orelse
          String.isPrefix "tmux" t orelse
          t = "eterm-color"

end
