signature smlTimeout =
sig

  include Abbrev

  exception FunctionTimeout

  val interruptkill : Thread.thread -> unit
  val timeout : real -> ('a -> 'b) -> 'a -> 'b
  (* thread_timeout t f x is timeout t f x, with the CPU seconds the call
     used, but it stops f only once the thread running it has used t
     seconds of CPU, so that the call gets t seconds of computation
     whatever else the machine and the process do.  Without Linux's
     /proc/thread-self the clock is the lesser of the wall time and the
     process's CPU time.  A call that does not compute is stopped after
     20 t seconds of wall time. *)
  val thread_timeout : real -> ('a -> 'b) -> 'a -> 'b * real

end
