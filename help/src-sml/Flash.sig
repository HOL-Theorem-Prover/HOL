signature Flash =
sig

  (* `(prefix, total)` -> `(tick, finish)`.  Each `tick` redraws the
     in-place progress line; `finish` advances past it.  When `TERM`
     indicates a non-animating terminal (emacs, dumb, unset), both
     are no-ops. *)

  (* Percentage form: \r<prefix><nn>%, where nn = ticks/total. *)
  val initialise : (string * int) -> ((unit -> unit) * (unit -> unit))

  (* Spinner + decreasing-count form:
     \r<prefix>[<|/-\>] <total - ticks> remaining
     The spinner glyph rotates on each tick; the count counts down to
     zero.  `finish` blanks the line so subsequent output starts
     clean.  Each tick flushes stdout so progress is visible during
     slow per-tick work (the percentage variant relies on terminal
     line-buffering and may not show live). *)
  val initialise_spinner :
        (string * int) -> ((unit -> unit) * (unit -> unit))

end;
