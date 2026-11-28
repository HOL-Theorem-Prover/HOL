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
  val defer_interrupts: attributes -> attributes
  val with_attributes: attributes -> (attributes -> 'a) -> 'a
  val uninterruptible: ((('c -> 'd) -> 'c -> 'd) -> 'a -> 'b) -> 'a -> 'b
  val uninterruptible_defer: ((('c -> 'd) -> 'c -> 'd) -> 'a -> 'b) -> 'a -> 'b
  val uninterruptible_wait:
    ((('c -> 'd) -> 'c -> 'd option) -> 'a -> 'b) -> 'a -> 'b
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

(*deferred, but unlike no_interrupts keeping the broadcast flag, so that
  a broadcast interrupt is recorded rather than dropped*)
fun defer_interrupts (Attributes w) = Attributes (Word.andb (w, broadcast));

fun with_attributes new_atts e =
  let
    val atts1 = get_attributes ()
    val atts2 = safe_interrupts new_atts
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

(* Masking interrupts the plain way does not defer a Ctrl-C, it loses one.
   Poly/ML retains a directed [Thread.interrupt] and delivers it when the
   mask lifts, but HOL raises Ctrl-C as [Thread.broadcastInterrupt], and a
   broadcast simply skips a thread whose broadcast flag is clear, recording
   nothing; [no_interrupts] clears that flag along with
   the rest.  A wait that must run to completion therefore has to stay
   observant while it waits.

   [uninterruptible_defer f x] is [uninterruptible] with
   the broadcast flag left as the caller had it: interrupts are deferred
   rather than refused, so a broadcast arriving inside the masked region is
   held and delivered when the caller's attributes come back, at a [restore]
   step or on the way out.  Poly/ML has no attribute constant for that
   combination, hence the raw [Thread.Thread.setAttributes]; it writes the
   interrupt-state bits only. *)
fun uninterruptible_defer f x =
  let
    val saved = get_attributes ()
    val _ =
      Thread.Thread.setAttributes
        [Thread.Thread.InterruptState Thread.Thread.InterruptDefer]
    fun restore g y = with_attributes saved (fn _ => g y)
    val result = Exn.capture (f restore) x
    val _ = set_attributes saved
  in
    Exn.release result
  end;

(* [uninterruptible_wait f x] runs [f observe x] masked, as
   [uninterruptible] does, except that [observe g y] runs
   [g y] under the caller's own attributes, so a broadcast arriving during
   that step is delivered.  [observe] answers [SOME] with the result, or
   records the interrupt and answers [NONE]; once one is recorded, later
   steps run masked, one being all that is needed.  A recorded interrupt is
   raised after [f] has returned, so the wait still runs to completion.  An
   exception from [f] itself wins and the recorded interrupt is dropped: it
   is [f]'s own outcome the caller is waiting on, and control is leaving for
   the top level under either exception anyway. *)
fun uninterruptible_wait f =
  uninterruptible (fn restore => fn x =>
    let
      val pending = ref false
      fun observe g y =
        if !pending then SOME (g y)
        else
          (SOME (restore g y)
           handle Exn.Interrupt => (pending := true; NONE))
      val result = Exn.capture (f observe) x
    in
      case result of
          Exn.Res value => if !pending then raise Exn.Interrupt else value
        | Exn.Exn _ => Exn.release result
    end);

fun expose_interrupt () =
  let
    val orig_atts = safe_interrupts (get_attributes ());
    val _ = set_attributes test_interrupts;
    val test = Exn.capture Thread.Thread.testInterrupt ();
    val _ = set_attributes orig_atts;
  in Exn.release test end;

end;
