open testutils

val _ = OS.FileSys.chDir "testdir"

val holmake = "../../../../../bin/Holmake"
val dumpfile = "failing.bad_thm.dumpedheap"

fun hm extra =
  OS.Process.system (holmake ^ " --no-cache " ^ extra)

fun safedelete f = (OS.FileSys.remove f) handle OS.SysErr _ => ()

fun cleanAll () =
  if OS.Process.isSuccess (hm "cleanAll") then ()
  else die "Holmake cleanAll failed"

(* --- qof (default): build must fail AND leave a dumpedheap file. *)
val _ = tprint "qof build fails and writes <thy>.<thm>.dumpedheap"
val _ = cleanAll ()
val _ = safedelete dumpfile
val _ = if OS.Process.isSuccess (hm "") then
          die "expected qof Holmake to fail (theorem proof should not succeed)"
        else ()
val _ = if OS.FileSys.access (dumpfile, []) then OK()
        else die ("dumpedheap file " ^ dumpfile ^ " not produced")

(* --- noqof: build succeeds (CHEAT used) AND still leaves a dumpedheap. *)
val _ = tprint "noqof build CHEATs but still writes <thy>.<thm>.dumpedheap"
val _ = cleanAll ()
val _ = safedelete dumpfile
val _ = if OS.Process.isSuccess (hm "--noqof > noqof_output 2>&1") then ()
        else die "expected noqof Holmake to succeed via CHEAT"
val _ = if OS.FileSys.access (dumpfile, []) then OK()
        else die ("dumpedheap file " ^ dumpfile ^ " not produced under --noqof")

val _ = safedelete dumpfile
val _ = cleanAll ()

(* --- rebuild sweeps stale <theory>.*.dumpedheap files.  Seed a
   "stale" dump from a hypothetical previous run, then re-invoke
   Holmake: the prep_for_build pass must wipe it before re-running
   the script.  The live failing.bad_thm.dumpedheap is also wiped by
   the sweep but is then re-created by the new failing run, so it is
   the stale_thm sibling we check. *)
val stalefile = "failing.stale_thm.dumpedheap"
val _ = tprint "Holmake rebuild sweeps stale <thy>.*.dumpedheap"
val _ = cleanAll ()
val _ = safedelete dumpfile
val _ = safedelete stalefile
val _ = if OS.Process.isSuccess (hm "") then
          die "expected qof Holmake to fail on first run"
        else ()
val _ = if OS.FileSys.access (dumpfile, []) then ()
        else die ("dumpedheap file " ^ dumpfile ^ " not produced on first run")
val _ = let val out = TextIO.openOut stalefile
        in TextIO.output (out, "stale\n"); TextIO.closeOut out end
val _ = if OS.Process.isSuccess (hm "") then
          die "expected qof Holmake to fail on second run"
        else ()
val _ = if OS.FileSys.access (stalefile, []) then
          die ("stale dumpedheap " ^ stalefile ^ " not swept on rebuild")
        else OK()
val _ = safedelete dumpfile
val _ = safedelete stalefile
val _ = cleanAll ()
