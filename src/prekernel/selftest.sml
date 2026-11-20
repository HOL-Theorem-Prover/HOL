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

(* ----------------------------------------------------------------------
    HOLmessage, and Feedback's string-valued interfaces over it

    The whole point of putting a message where a string used to be is
    that it does not have to be rendered.  These check the two halves
    of that: text put in comes back out unchanged, so that every
    existing caller of the string interfaces still means what it meant;
    and a value put in is not touched until someone looks.
   ---------------------------------------------------------------------- *)

val _ = tprint "txt round-trips, newlines and all"

val multiline = "first line\nsecond line\n  indented"

val _ = if HOLmessage.toString (HOLmessage.txt multiline) = multiline
        then print "OK\n"
        else die ("FAILED: got " ^
                  String.toString
                    (HOLmessage.toString (HOLmessage.txt multiline)))

val _ = tprint "a plain error's message_of is the string it was built from"

(* This is the compatibility property the migration rests on: 2000-odd
   `raise ERR' sites and every selftest that matches on error text go
   through here.  Re-wrapping the text -- laying it out at the reader's
   width like a term -- would shift all of them at once. *)
val _ =
    let
      val e = Feedback.mk_hol_error "Struct" "fn" locn.Loc_Unknown multiline
    in
      if Feedback.message_of e = multiline then print "OK\n"
      else die ("FAILED: got " ^ String.toString (Feedback.message_of e))
    end

val _ = tprint "is_empty_hol_error agrees with the equality test it replaces"

val _ =
    let
      val nonempty = Feedback.mk_hol_error "S" "f" locn.Loc_Unknown "boom"
      val noMessage = Feedback.mk_hol_error "S" "f" locn.Loc_Unknown ""
    in
      if Feedback.is_empty_hol_error Feedback.empty_hol_error andalso
         not (Feedback.is_empty_hol_error nonempty) andalso
         not (Feedback.is_empty_hol_error noMessage)
      then print "OK\n"
      else die "FAILED"
    end

val _ = tprint "a value in a message is not printed until it is read"

(* The property that makes this type affordable.  `can', `Lib.total'
   and `handle HOL_ERR' raise and discard errors as a control
   structure, so building one must not cost a pretty-print.  The
   counter is the control: it says the suspension really was the thing
   that would have done the work. *)
val _ =
    let
      val forced = ref 0
      val m = HOLmessage.^^
                (HOLmessage.txt "a term: ",
                 HOLmessage.pp (fn () => (forced := !forced + 1;
                                          HOLPP.add_string "<the term>")))
      val e = Feedback.mk_HOL_ERRm "S" "f" m
      val afterRaise = !forced
      val shown = Feedback.exn_to_string e
      val afterShow = !forced
    in
      if afterRaise = 0 andalso afterShow = 1 andalso
         String.isSubstring "a term: <the term>" shown
      then print "OK\n"
      else die ("FAILED: forced " ^ Int.toString afterRaise ^ " before, " ^
                Int.toString afterShow ^ " after; message " ^
                String.toString shown)
    end

val _ = tprint "a value whose printer fails does not take the report down"

(* A message is read while something has already gone wrong.  A printer
   that raises -- a term naming a type the context no longer has --
   must not replace the error being reported with itself. *)
val _ =
    let
      val m = HOLmessage.^^ (HOLmessage.txt "before ",
                             HOLmessage.pp (fn () => raise Fail "printer"))
      val shown = HOLmessage.toString m
    in
      if String.isSubstring "before " shown andalso
         String.isSubstring "unprintable" shown
      then print "OK\n"
      else die ("FAILED: got " ^ String.toString shown)
    end
