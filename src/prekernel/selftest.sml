fun tprint s = print (StringCvt.padRight #" " 75 s)
fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

val _ = tprint "nameStream in subscripting mode starts at 1";

val f = Lexis.nameStrm (SOME "") "foo"
val l = List.tabulate(10, fn i => f())
val expected = List.tabulate(10, fn i => "foo" ^ Int.toString (i + 1))

val _ = (l = expected before print "OK\n") orelse die "FAILED"

(* Context.with_context answers this thread's ambient reads from the
   pinned context rather than from the live cell, and takes that
   thread's writes there as well.

   Deterministic and single-threaded on purpose.  The property is about
   where a read is answered from, not about timing, so rewinding the
   live cell and reading once each way tests it exactly -- and the
   second read is the control that makes the first mean something.  A
   version that forked a thread and raced it against `restore` would
   only catch a broken pin in whichever windows the race happened to
   hit, and could not run under Moscow ML, which has no threads. *)

val _ = tprint "with_context answers ambient reads from the pin"

val slot = Context.Data.new {name = "selftest_pin", empty = 0,
                             pp = Int.toString}
val () = Context.Data.write slot 1
val pinnedCtx = Context.snapshot ()
val () = Context.Data.write slot 2

fun readSlot () = Context.Data.get slot (Context.snapshot ())

val pinned = Context.with_context pinnedCtx readSlot ()
val unpinned = readSlot ()

val _ =
    if pinned = 1 andalso unpinned = 2 then print "OK\n"
    else die ("FAILED: pinned read gave " ^ Int.toString pinned ^
              " (want 1), unpinned gave " ^ Int.toString unpinned ^
              " (want 2)")

val _ = tprint "is_pinned says which side of a pin a reader is on"

val _ =
    if not (Context.is_pinned ()) andalso
       Context.with_context pinnedCtx Context.is_pinned ()
    then print "OK\n"
    else die "FAILED: is_pinned does not follow with_context"

val _ = tprint "with_context releases the pin when its body raises"

exception Boom
val _ =
    (ignore (Context.with_context pinnedCtx
               (fn () => raise Boom) ()); die "FAILED: no exception")
    handle Boom =>
           if readSlot () = 2 then print "OK\n"
           else die "FAILED: pin outlived the exception"

(* The writes.  A pin that answered reads from one context and sent
   writes to another let a caller that declared a name and looked it up
   again see two different answers, which is how a theorem could be
   made to describe the type its own declaration had just replaced. *)

val _ = tprint "a pinned write answers the pinned thread's own reads"

val pinnedAfterWrite =
    Context.with_context pinnedCtx
      (fn () => (Context.Data.write slot 3; readSlot ())) ()

val _ =
    if pinnedAfterWrite = 3 then print "OK\n"
    else die ("FAILED: read back " ^ Int.toString pinnedAfterWrite ^
              " (want 3)")

val _ = tprint "a pinned write does not reach the live cell"

val _ =
    if readSlot () = 2 then print "OK\n"
    else die ("FAILED: live cell holds " ^ Int.toString (readSlot ()) ^
              " (want 2)")

val _ = tprint "a pinned write is discarded with the pin"

val _ =
    if Context.with_context pinnedCtx readSlot () = 1 then print "OK\n"
    else die "FAILED: a write outlived the pin that took it"

val _ = tprint "with_slot_value brackets a pinned write"

val (inWindow, afterWindow) =
    Context.with_context pinnedCtx
      (fn () =>
          let val inWindow = Context.Data.with_slot_value slot 7 readSlot ()
          in (inWindow, readSlot ()) end) ()

val _ =
    if inWindow = 7 andalso afterWindow = 1 then print "OK\n"
    else die ("FAILED: inside the window " ^ Int.toString inWindow ^
              " (want 7), after it " ^ Int.toString afterWindow ^
              " (want 1)")

val _ = tprint "with_slot_value in a pin leaves the live cell alone"

val _ =
    if readSlot () = 2 then print "OK\n"
    else die ("FAILED: live cell holds " ^ Int.toString (readSlot ()) ^
              " (want 2)")

val _ = tprint "restore inside a pin replaces the pin, not the cell"

val () = Context.Data.write slot 5
val fiveCtx = Context.snapshot ()
val () = Context.Data.write slot 2

val restoredInPin =
    Context.with_context pinnedCtx
      (fn () => (Context.restore fiveCtx; readSlot ())) ()

val _ =
    if restoredInPin = 5 andalso readSlot () = 2 then print "OK\n"
    else die ("FAILED: pinned read " ^ Int.toString restoredInPin ^
              " (want 5), live cell " ^ Int.toString (readSlot ()) ^
              " (want 2)")
