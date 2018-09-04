(*  Title:      Pure/Concurrent/thread_attributes.ML
    Author:     Makarius

Thread attributes for interrupt handling.
*)

signature THREAD_ATTRIBUTES =
sig
  type attributes
  val get_attributes: unit -> attributes
  val set_attributes: attributes -> unit
  val convert_attributes: attributes -> Thread.Thread.threadAttribute list
  val no_interrupts: attributes
  val test_interrupts: attributes
  val public_interrupts: attributes
  val private_interrupts: attributes
  val sync_interrupts: attributes -> attributes
  val safe_interrupts: attributes -> attributes
  val with_attributes: attributes -> (attributes -> 'a) -> 'a
  val uninterruptible: ((('c -> 'd) -> 'c -> 'd) -> 'a -> 'b) -> 'a -> 'b
  val expose_interrupt: unit -> unit  (*exception Interrupt*)
end;

structure Thread_Attributes: THREAD_ATTRIBUTES =
struct

abstype attributes = Attributes of Word.word
with

(* thread attributes *)

val thread_attributes = 0w7;

val broadcast = 0w1;

val interrupt_state = 0w6;
val interrupt_defer = 0w0;
val interrupt_synch = 0w2;
val interrupt_asynch = 0w4;
val interrupt_asynch_once = 0w6;


(* access thread flags *)

val thread_flags = 0w1;

fun load_word () : word =
  RunCall.loadWord (RunCall.unsafeCast (Thread.Thread.self ()), thread_flags);

fun get_attributes () = Attributes (Word.andb (load_word (), thread_attributes));

fun set_attributes (Attributes w) =
  let
    val w' = Word.orb (Word.andb (load_word (), Word.notb thread_attributes), w);
    val _ = RunCall.storeWord (RunCall.unsafeCast (Thread.Thread.self ()), thread_flags, w');
  in
    if Word.andb (w', interrupt_asynch) = interrupt_asynch
    then Thread.Thread.testInterrupt () else ()
  end;

fun convert_attributes (Attributes w) =
  [Thread.Thread.EnableBroadcastInterrupt (Word.andb (w, broadcast) = broadcast),
   Thread.Thread.InterruptState
      let val w' = Word.andb (w, interrupt_state) in
        if w' = interrupt_defer then Thread.Thread.InterruptDefer
        else if w' = interrupt_synch then Thread.Thread.InterruptSynch
        else if w' = interrupt_asynch then Thread.Thread.InterruptAsynch
        else Thread.Thread.InterruptAsynchOnce
      end];


(* common configurations *)

val no_interrupts = Attributes interrupt_defer;
val test_interrupts = Attributes interrupt_synch;
val public_interrupts = Attributes (Word.orb (broadcast, interrupt_asynch_once));
val private_interrupts = Attributes interrupt_asynch_once;

fun sync_interrupts (Attributes w) =
  let
    val w' = Word.andb (w, interrupt_state);
    val w'' = Word.andb (w, Word.notb interrupt_state);
  in Attributes (if w' = interrupt_defer then w else Word.orb (w'', interrupt_synch)) end;

fun safe_interrupts (Attributes w) =
  let
    val w' = Word.andb (w, interrupt_state);
    val w'' = Word.andb (w, Word.notb interrupt_state);
  in Attributes (if w' = interrupt_asynch then Word.orb (w'', interrupt_asynch_once) else w) end;

fun with_attributes new_atts e =
  let
    val atts1 = safe_interrupts (get_attributes ());
    val atts2 = safe_interrupts new_atts;
  in
    if atts1 = atts2 then e atts1
    else
      let
        val result = Exn.capture (fn () => (set_attributes atts2; e atts1)) ();
        val _ = set_attributes atts1;
      in Exn.release result end
  end;

end;

fun uninterruptible f x =
  with_attributes no_interrupts (fn atts =>
    f (fn g => fn y => with_attributes atts (fn _ => g y)) x);

fun expose_interrupt () =
  let
    val orig_atts = safe_interrupts (get_attributes ());
    val _ = set_attributes test_interrupts;
    val test = Exn.capture Thread.Thread.testInterrupt ();
    val _ = set_attributes orig_atts;
  in Exn.release test end;

end;
