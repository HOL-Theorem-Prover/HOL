(*  Title:      Pure/Concurrent/timeout.ML
    Author:     Makarius

Execution with (relative) timeout.
*)

signature TIMEOUT =
sig
  exception TIMEOUT of Time.time
  val apply: Time.time -> ('a -> 'b) -> 'a -> 'b
end;

structure Timeout: TIMEOUT =
struct

exception TIMEOUT of Time.time;

fun apply timeout f x =
  Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
    let
      val self = Thread.self ();
      val start = Time.now ();

      val request =
        Event_Timer.request (start + timeout)
          (fn () => Standard_Thread.interrupt_unsynchronized self);
      val result =
        Exn.capture (fn () => Thread_Attributes.with_attributes orig_atts (fn _ => f x)) ();

      val stop = Time.now ();
      val was_timeout = not (Event_Timer.cancel request);
      val test = Exn.capture Thread_Attributes.expose_interrupt ();
    in
      if was_timeout andalso (Exn.is_interrupt_exn result orelse Exn.is_interrupt_exn test)
      then raise TIMEOUT (stop - start)
      else (Exn.release test; Exn.release result)
    end);

end;
