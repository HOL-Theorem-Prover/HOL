open testutils

val hmstr = OS.Path.concat (Globals.HOLDIR, OS.Path.concat("bin", "Holmake"))
val _ = OS.FileSys.chDir "testdir";

fun hm testname tgts test =
  (tprint testname ;
   Systeml.systeml (hmstr :: "-q" :: "--no-cache" :: tgts);
   if test() then OK() else die "FAILED!")

fun present n = HOLFileSys.access(n, [OS.FileSys.A_READ])
fun delete n = HOLFileSys.remove n handle _ => ()
fun mtime n = HOLFileSys.modTime n

fun touch n =
    let val now = Time.now ()
    in HOLFileSys.setTime (n, SOME now) end

(* Phase 3 e2e: %.copy: %.txt rule should fire for foo.copy and
   bar.copy without an explicit per-target rule. *)

val _ = hm "Cleaning" ["-r", "cleanAll"]
           (fn () => List.all (not o present)
                              ["foo.copy", "bar.copy", "sub/baz.copy"])

val _ = hm "Default build produces foo.copy and bar.copy via pattern rule" []
           (fn () => present "foo.copy" andalso present "bar.copy")

(* Cross-directory pattern `sub/%.copy: sub/%.txt' fires for the
   subdirectory target without an explicit per-target rule. *)
val _ = hm "Cross-directory pattern produces sub/baz.copy" []
           (fn () => present "sub/baz.copy")

(* bar.copy has an explicit recipe-less rule adding extra.txt as a
   prereq.  Touch extra.txt and bar.copy should rebuild; foo.copy
   should not. *)
val foo_t0 = mtime "foo.copy"
val bar_t0 = mtime "bar.copy"
val _ = OS.Process.sleep (Time.fromSeconds 1)  (* mtime granularity *)
val _ = touch "extra.txt"

val _ = hm "Touching pattern's deps-composition prereq rebuilds bar, not foo" []
           (fn () =>
               Time.> (mtime "bar.copy", bar_t0) andalso
               mtime "foo.copy" = foo_t0)

val _ = hm "Final clean" ["cleanAll"]
           (fn () => List.all (not o present) ["foo.copy", "bar.copy"])
