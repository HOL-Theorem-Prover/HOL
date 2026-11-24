signature Refute_ThreadClock =
sig

  (* A clock of the CPU time one thread uses.  Linux reports a thread's
     CPU time in /proc/<pid>/task/<tid>/stat; where that file can't be
     read (macOS has no /proc), the clock reads the lesser of the wall time
     and the process's CPU time. *)
  type clock

  (* [start ()] starts a clock of the calling thread's CPU time. *)
  val start : unit -> clock

  (* [start_reading file] is [start ()] reading the stat file [file]; NONE,
     or a file that can't be read, gives the process clock. *)
  val start_reading : string option -> clock

  (* [seconds clock] is the CPU seconds the clock's thread has used since
     the clock started, to a tick; any thread may read it. *)
  val seconds : clock -> real

  (* the resolution of a thread's clock, in seconds *)
  val tick : real

end
