signature terminal_primitives =
sig


  val strmIsTTY : TextIO.outstream -> bool
  val stdin_is_tty : unit -> bool
    (* True iff standard input is connected to a terminal.  Used to
       decide whether to prompt the user vs. abort silently; the
       conservative default for ML systems where we can't tell is
       false, so a non-interactive context never hangs waiting on
       input.  The Poly/ML implementation uses Posix.ProcEnv.isatty
       for an accurate answer; other systems return false. *)
  val TERM_isANSI : unit -> bool

end
