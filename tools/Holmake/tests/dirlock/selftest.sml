open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val testdir = OS.FileSys.getDir()

fun run_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

fun clean dir = ignore (run_in dir ["cleanAll"])

fun build dir = run_in dir []

(* -----------------------------------------------------------------------
   Test 1: Lock file is created during build
   ----------------------------------------------------------------------- *)
val _ = tprint "Lock file created during build"
val _ = clean (testdir ++ "shared")
val _ = clean (testdir ++ "dirA")
val result = build (testdir ++ "dirA")
val lockfile = testdir ++ "shared" ++ ".hol" ++ "holmake.lock"
val _ = if OS.Process.isSuccess result andalso
           OS.FileSys.access(lockfile, [])
        then OK()
        else die "FAILED"

(* -----------------------------------------------------------------------
   Test 2: Two concurrent Holmake processes both succeed when building
   directories that share a dependency.

   We clean shared, then launch Holmake in dirA and dirB simultaneously.
   Both should succeed — one will acquire the lock on shared/ and build
   it, the other will wait and then skip (since targets are up-to-date).
   ----------------------------------------------------------------------- *)
val _ = tprint "Concurrent Holmakes on shared dep both succeed"
val _ = clean (testdir ++ "shared")
val _ = clean (testdir ++ "dirA")
val _ = clean (testdir ++ "dirB")

(* Launch both in background using shell *)
val tmpA = OS.FileSys.tmpName()
val tmpB = OS.FileSys.tmpName()
val cmd = String.concat [
    "(cd ", testdir ++ "dirA", " && ", Holmake, ") > ", tmpA, " 2>&1 & ",
    "(cd ", testdir ++ "dirB", " && ", Holmake, ") > ", tmpB, " 2>&1 & ",
    "wait"
  ]
val shell_result = OS.Process.isSuccess (Systeml.system_ps cmd)

(* Check that both theory files got built.
   With Poly/ML name munging, .dat files live under .hol/objs *)
fun dat_exists dir thy =
    let val p1 = dir ++ ".hol" ++ "objs" ++ (thy ^ "Theory.dat")
        val p2 = dir ++ (thy ^ "Theory.dat")
    in
      OS.FileSys.access(p1, []) orelse OS.FileSys.access(p2, [])
    end handle OS.SysErr _ => false

val dirA_ok = dat_exists (testdir ++ "dirA") "dirA"
val dirB_ok = dat_exists (testdir ++ "dirB") "dirB"
val shared_ok = dat_exists (testdir ++ "shared") "shared"

(* If something failed, show the logs *)
val _ = if not (shell_result andalso dirA_ok andalso dirB_ok andalso shared_ok)
        then
          let fun showlog f = (print ("\n--- " ^ f ^ " ---\n");
                               let val s = TextIO.openIn f
                               in print (TextIO.inputAll s);
                                  TextIO.closeIn s
                               end handle IO.Io _ => ())
          in showlog tmpA; showlog tmpB end
        else ()
val _ = OS.FileSys.remove tmpA handle OS.SysErr _ => ()
val _ = OS.FileSys.remove tmpB handle OS.SysErr _ => ()
val _ = if shell_result andalso dirA_ok andalso dirB_ok andalso shared_ok
        then OK()
        else die ("FAILED: shell=" ^ Bool.toString shell_result ^
                  " dirA=" ^ Bool.toString dirA_ok ^
                  " dirB=" ^ Bool.toString dirB_ok ^
                  " shared=" ^ Bool.toString shared_ok)

(* -----------------------------------------------------------------------
   Test 3: Repeated concurrent builds also succeed (idempotency).
   Everything is already built; two concurrent Holmakes should both
   just skip and succeed.
   ----------------------------------------------------------------------- *)
val _ = tprint "Concurrent Holmakes on already-built dirs succeed"
val cmd2 = String.concat [
    "(cd ", testdir ++ "dirA", " && ", Holmake, ") > /dev/null 2>&1 & ",
    "(cd ", testdir ++ "dirB", " && ", Holmake, ") > /dev/null 2>&1 & ",
    "wait"
  ]
val result2 = OS.Process.isSuccess (Systeml.system_ps cmd2)
val _ = if result2 then OK() else die "FAILED"

(* Clean up *)
val _ = clean (testdir ++ "shared")
val _ = clean (testdir ++ "dirA")
val _ = clean (testdir ++ "dirB")
