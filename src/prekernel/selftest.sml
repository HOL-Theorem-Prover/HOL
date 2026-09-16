fun tprint s = print (StringCvt.padRight #" " 75 s)
fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

val _ = tprint "nameStream in subscripting mode starts at 1";

val f = Lexis.nameStrm (SOME "") "foo"
val l = List.tabulate(10, fn i => f())
val expected = List.tabulate(10, fn i => "foo" ^ Int.toString (i + 1))

val _ = (l = expected before print "OK\n") orelse die "FAILED"

(* Context.with_context answers this thread's ambient reads from the
   pinned context rather than from the live cell.

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

val _ = tprint "with_context releases the pin when its body raises"

exception Boom
val _ =
    (ignore (Context.with_context pinnedCtx
               (fn () => raise Boom) ()); die "FAILED: no exception")
    handle Boom =>
           if readSlot () = 2 then print "OK\n"
           else die "FAILED: pin outlived the exception"
