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
