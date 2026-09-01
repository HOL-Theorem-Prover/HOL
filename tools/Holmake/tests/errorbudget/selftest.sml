(* The closing "*** Holmake aborted" report quotes the tail of every
   failed target's log, so with -k its length is bounded only by the
   number of failures.  It should instead spend a fixed budget of log
   lines across the failures there are, and -- once the share per
   target is too small to hold an error message -- name the targets and
   their logs without quoting anything.

   testdir's targets each emit sixty numbered LOGLINEs before failing.
   Sixty exceeds what the monitor retains per job, so every failure
   arrives at the report wanting more space than the budget can give
   it: the counts below are the budget's doing, not the fixture's. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val testdir = OS.FileSys.getDir() ++ "testdir"

(* Mirrors of MB_Monitor.sml's retained_lines, report_budget and
   min_useful_extract; nothing links this test to that structure, so
   tuning them there means tuning them here. *)
val retained = 50
val budget = retained + 1
val min_useful = 10

(* The largest number of failures whose even share is still worth
   printing, and so the last one that quotes any log at all. *)
val last_quoting = budget div min_useful
val fixture_targets = 6
val _ = if last_quoting < fixture_targets then ()
        else die ("testdir needs more than " ^ Int.toString last_quoting ^
                  " targets to straddle the cutoff")

fun targets n = List.tabulate (n, fn i => "t" ^ Int.toString (i + 1))

fun read_file f =
    let val s = TextIO.openIn f
    in TextIO.inputAll s before TextIO.closeIn s end

fun run_holmake_in dir args =
    let
      val saved = OS.FileSys.getDir()
      val _ = OS.FileSys.chDir dir
      val cmd = String.concatWith " "
                  (Holmake :: args @ [">", "output", "2>&1"])
      val res = OS.Process.system cmd
    in
      OS.FileSys.chDir saved;
      (res, read_file (dir ++ "output"))
    end

(* Under -k each failure also echoes its whole tail inline as it
   happens; the report is everything from its banner onwards. *)
val banner = "*** Holmake aborted"
fun summary out =
    let
      fun from [] = []
        | from (l :: ls) = if String.isPrefix banner l then l :: ls
                           else from ls
    in
      from (String.fields (fn c => c = #"\n") out)
    end

fun count p l = length (List.filter p l)
fun containing s = count (String.isSubstring s)

fun expect (label, args, checks) =
    let
      val _ = tprint label
      val (res, output) = run_holmake_in testdir args
      val sm = summary output
      fun fail msg =
          (print "\n--- captured Holmake output ---\n"; print output;
           print "--- end captured output ---\n";
           die ("FAILED: " ^ msg))
    in
      if OS.Process.isSuccess res then
        fail "sub-Holmake unexpectedly succeeded"
      else
        case List.find (fn (_, p) => not (p sm)) checks of
            SOME (msg, _) => fail msg
          | NONE => OK()
    end

(* The targets never produce a file, so they cannot go out of date and
   no run needs cleaning up after; this is just insurance against an
   interrupted earlier run. *)
val _ = ignore (OS.Process.system
                  ("cd " ^ testdir ^ " && " ^ Holmake ^
                   " cleanAll > /dev/null 2>&1"))

(* One failure has the budget to itself, so it shows all it retained
   and the report says nothing about trimming. *)
val _ = expect (
  "One failure: whole retained tail, no trim notice",
  ["--no-cache", "-j", "4", "t1"],
  [("summary should quote " ^ Int.toString retained ^ " log lines",
    fn sm => containing "LOGLINE" sm = retained),
   ("summary should not claim to have trimmed",
    fn sm => containing " lines of output. Full log:" sm = 0),
   ("summary should point at the log",
    fn sm => containing "Full log:" sm = 1)])

(* Several failures share that same budget, and each says how much of
   its log it is showing. *)
val _ = expect (
  "Three failures: budget shared, trim reported",
  ["--no-cache", "-k", "-j", "4"] @ targets 3,
  [("summary should quote " ^ Int.toString budget ^ " log lines",
    fn sm => containing "LOGLINE" sm = budget),
   ("each target should report how much of its log was shown",
    fn sm => containing " lines of output. Full log:" sm = 3),
   ("all three targets should be named",
    fn sm => containing "*** t" sm = 3)])

(* Either side of the cutoff. *)
val _ = expect (
  "Cutoff: the last count that quotes logs",
  ["--no-cache", "-k", "-j", "4"] @ targets last_quoting,
  [("summary should quote " ^ Int.toString budget ^ " log lines",
    fn sm => containing "LOGLINE" sm = budget),
   ("each target should report how much of its log was shown",
    fn sm => containing " lines of output. Full log:" sm = last_quoting)])

val _ = expect (
  "Past the cutoff: targets named, no log quoted",
  ["--no-cache", "-k", "-j", "4"] @ targets (last_quoting + 1),
  [("summary should quote no log lines at all",
    fn sm => containing "LOGLINE" sm = 0),
   ("every failed target should still be named",
    fn sm => containing "*** t" sm = last_quoting + 1),
   ("every failed target should still point at its log",
    fn sm => containing "Full log:" sm = last_quoting + 1)])
