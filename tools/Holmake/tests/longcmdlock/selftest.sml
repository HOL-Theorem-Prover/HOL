open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

fun run_holmake dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

fun clean dir = ignore (run_holmake dir ["cleanAll"])
fun build dir = run_holmake dir []

(* Create a temporary test directory with a Holmakefile whose SomeCmd
   rule has a command string longer than 255 characters.
   Before the fix for issue #1920, the entire command string was used as
   the lock key, making the lock filename exceed NAME_MAX and causing
   "File name too long" errors.  After the fix, the lock key is derived
   from the short target name, so the lock file fits on disk. *)
fun mk_testdir dir =
    let
      val _ = OS.FileSys.mkDir dir handle OS.SysErr _ => ()
      val hmf = dir ++ "Holmakefile"
      val out = TextIO.openOut hmf
      val longcmd =
          "building output with a deliberately very long command that\
          \ exceeds two hundred and fifty five characters in total length\
          \ in order to reproduce the File name too long error from issue\
          \ one nine two zero where the entire command string was used as\
          \ the lock key and caused the build lock file path to exceed\
          \ filesystem NAME_MAX limits"
    in
      TextIO.output (out,
        "ifdef POLY\nHOLHEAP = $(HOLDIR)/bin/hol.state0\nendif\n\n\
        \output:\n\
        \\t@echo \"" ^ longcmd ^ "\" && echo \"x\" > output\n\n\
        \EXTRA_CLEANS = output\n");
      TextIO.closeOut out
    end

fun rm_rf d =
    let
      fun walk dir =
          let fun rm f =
                  let val p = d ++ f
                  in if OS.FileSys.isDir p
                     then rm_rf p
                     else OS.FileSys.remove p
                  end handle OS.SysErr _ => ()
              fun loop () =
                  case OS.FileSys.readDir dir of
                    NONE => ()
                  | SOME f => (rm f; loop ())
          in loop ();
             OS.FileSys.closeDir dir
          end
    in
      if OS.FileSys.isDir d then
        (walk (OS.FileSys.openDir d);
         OS.FileSys.rmDir d)
      else ()
    end handle OS.SysErr _ => ()

(* -----------------------------------------------------------------------
   Test: SomeCmd rule with a long command acquires a real build lock.
   ----------------------------------------------------------------------- *)
val _ = tprint "Long-command SomeCmd rule acquires build lock"
val tmpname = OS.FileSys.tmpName ()
val _ = OS.FileSys.remove tmpname handle OS.SysErr _ => ()
val tmpdir = tmpname
val _ = OS.FileSys.mkDir tmpdir
val _ = mk_testdir tmpdir
val result = build tmpdir

(* Check that the target was built *)
val target_exists = OS.FileSys.access(tmpdir ++ "output", [])
                    handle OS.SysErr _ => false

(* On Unix: check that a lock file was created with the target-based
   name.  If the old code (using the full command as key) were active,
   the lock filename would exceed NAME_MAX and acquire would fall back
   to DummyLock, leaving no .lock file on disk. *)
val lockdir = tmpdir ++ ".hol" ++ "locks"
val has_lock =
    if Systeml.isUnix then
      OS.FileSys.access(lockdir ++ "output.lock", [])
      handle OS.SysErr _ => false
    else true (* no real locks on Windows; skip this check *)

val _ = if OS.Process.isSuccess result andalso target_exists andalso has_lock
        then OK()
        else die ("FAILED: result=" ^ Bool.toString (OS.Process.isSuccess result) ^
                  " target=" ^ Bool.toString target_exists ^
                  " lock=" ^ Bool.toString has_lock)

(* Clean up *)
val _ = rm_rf tmpdir
