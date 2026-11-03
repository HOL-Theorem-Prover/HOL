open testutils

infix ++
val op++ = OS.Path.concat

val _ = OS.FileSys.chDir "testdir"

val holmake = "../../../../../bin/Holmake"
val hol = Systeml.HOLDIR ++ "bin" ++ "hol"
val state0 = Systeml.HOLDIR ++ "bin" ++ "hol.state0"
val heap = "markerheap"
val dumpfile = "resumeFail.lemma[a].dumpedheap"
val loadcheck = "loadcheck.sml"

fun hm_raw extra = OS.Process.system (holmake ^ " --no-cache " ^ extra)
fun hm extra = hm_raw ("--holstate=" ^ heap ^ " " ^ extra)

fun safedelete f = (OS.FileSys.remove f) handle OS.SysErr _ => ()

fun cleanAll () =
  if OS.Process.isSuccess (hm_raw ("--holstate=" ^ state0 ^ " cleanAll"))
  then ()
  else die "Holmake cleanAll failed"

val _ = cleanAll ()
val _ = safedelete dumpfile

(* The trigger needs markerLib to sit in a hierarchy level that the dump's
   saveChild would demote, so the heap must be a *child* of hol.state0 with
   markerLib loaded into it.  An empty child heap does not reproduce #2074:
   markerLib's residence is what matters, not the heap's size.  hol.state
   would do too, but it does not exist this early in the build. *)
val _ = tprint "building a markerLib heap on top of hol.state0"
val _ = if OS.Process.isSuccess
             (Systeml.systeml [hol, "buildheap", "-q", "-o", heap,
                               "-b", state0, "markerLib"]) andalso
           OS.FileSys.access (heap, [])
        then OK()
        else die "could not build the markerLib heap"

(* Before the fix this run dies with an uncaught Option rather than
   CHEATing, and Holmake exits non-zero. *)
val _ = tprint "noqof CHEATs a failing Resume under a deeper heap"
val _ = if OS.Process.isSuccess (hm "--noqof > noqof_output 2>&1") then ()
        else die "expected noqof Holmake to succeed via CHEAT"
val _ = if OS.FileSys.access (dumpfile, []) then OK()
        else die ("dumpedheap file " ^ dumpfile ^ " not produced")

(* A heap that saves without raising but cannot be loaded, or that comes up
   without the failing goal, is still a failure: seeding the goal is what
   dump_setup_hook exists for. *)
val _ = tprint "the dumped heap loads with the failing goal seeded"
val _ = let val out = TextIO.openOut loadcheck
        in
          TextIO.output (out,
            "val _ = (proofManagerLib.p(); \
            \OS.Process.exit OS.Process.success)\n\
            \        handle _ => OS.Process.exit OS.Process.failure;\n");
          TextIO.closeOut out
        end
(* `run' rather than the REPL: bin/hol's interactive prelude opens bossLib,
   which does not exist this early in the build.  systeml rather than
   OS.Process.system: no shell, so the brackets in the dumpedheap's name
   need no quoting. *)
val _ = if OS.Process.isSuccess
             (Systeml.systeml [hol, "run", "--holstate=" ^ dumpfile,
                               loadcheck])
        then OK()
        else die ("dumpedheap " ^ dumpfile ^ " did not load with a goal set")

val _ = safedelete dumpfile
val _ = cleanAll ()
