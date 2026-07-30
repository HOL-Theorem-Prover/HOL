open testutils
infix ++
val op++ = OS.Path.concat

(* ------------------------------------------------------------------
   target_times.load : empty result on NONE / missing file
   ------------------------------------------------------------------ *)
val _ = tprint "load {root=NONE} returns empty map"
val _ = require (check_result (fn m => Binarymap.numItems m = 0))
                target_times.load {root = NONE}

val _ = tprint "load on missing file returns empty map"
val fresh = OS.FileSys.getDir() ++ "tmp-root"
val _ = OS.Process.system ("rm -rf " ^ fresh) (* clean any leftover *)
val _ = OS.FileSys.mkDir fresh
val _ = require (check_result (fn m => Binarymap.numItems m = 0))
                target_times.load {root = SOME fresh}

(* ------------------------------------------------------------------
   target_times.merge_from_log : round-trip
   ------------------------------------------------------------------ *)
val _ = tprint "merge_from_log creates and populates target-times"
val logpath = OS.FileSys.getDir() ++ "tmp-log"
val outs = TextIO.openOut logpath
val _ = TextIO.output(outs, "src/foo/bar 1.5\n")
val _ = TextIO.output(outs, "src/foo/baz 2.75\n")
val _ = TextIO.output(outs, "malformed line without space\n")
val _ = TextIO.output(outs, "\n")
val _ = TextIO.closeOut outs

val _ = target_times.merge_from_log {root = fresh, log_path = logpath}
val m = target_times.load {root = SOME fresh}
val _ = if Binarymap.numItems m = 2 andalso
           Real.== (Binarymap.find(m, "src/foo/bar"), 1.5) andalso
           Real.== (Binarymap.find(m, "src/foo/baz"), 2.75)
        then OK()
        else die "unexpected contents"

(* ------------------------------------------------------------------
   Later runs update existing entries (last-observed wins) and preserve
   entries not touched by the later run.
   ------------------------------------------------------------------ *)
val _ = tprint "merge_from_log upserts and preserves"
val logpath2 = OS.FileSys.getDir() ++ "tmp-log"
val outs = TextIO.openOut logpath2
val _ = TextIO.output(outs, "src/foo/bar 9.0\n")   (* update *)
val _ = TextIO.output(outs, "src/foo/new 0.5\n")   (* new *)
val _ = TextIO.closeOut outs
val _ = target_times.merge_from_log {root = fresh, log_path = logpath2}
val m2 = target_times.load {root = SOME fresh}
val _ = if Binarymap.numItems m2 = 3 andalso
           Real.== (Binarymap.find(m2, "src/foo/bar"), 9.0) andalso
           Real.== (Binarymap.find(m2, "src/foo/baz"), 2.75) andalso
           Real.== (Binarymap.find(m2, "src/foo/new"), 0.5)
        then OK()
        else die "upsert or preservation failed"

(* ------------------------------------------------------------------
   Cleanup
   ------------------------------------------------------------------ *)
val _ = OS.Process.system ("rm -rf " ^ fresh)
val _ = OS.FileSys.remove logpath handle _ => ()
