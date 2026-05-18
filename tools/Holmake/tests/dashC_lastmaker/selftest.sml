(* Regression test: -C / --directory must survive the lastmaker
   exec-switch.  When Holmake's lastmaker check (Holmake_tools.sml's
   do_lastmade_checks) decides to re-exec a different binary, the
   original argv has by then already been processed once -- including
   -C, which chdir'd the parent process.  Naively forwarding the
   (often relative) -C argument to the exec'd child would make the
   child re-resolve the path against its already-chdir'd cwd, which
   generally fails.  This test triggers the switch by invoking Holmake
   through a symlink whose absolute path differs from the canonical
   $HOLDIR/bin/Holmake, with -C pointing at a sibling subdirectory. *)

open testutils

infix ++
val op++ = OS.Path.concat

fun safedel p = OS.FileSys.remove p handle OS.SysErr _ => ()

fun read_file f =
    let val s = TextIO.openIn f
    in TextIO.inputAll s before TextIO.closeIn s end

val sym = "altHolmake"
val output = "dashC_lastmaker-output"

val real_holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val _ = safedel sym
val _ =
    let val cmd = "ln -s " ^ real_holmake ^ " " ^ sym
    in
      if OS.Process.isSuccess (OS.Process.system cmd) then ()
      else die ("Could not create symlink: " ^ cmd)
    end

val _ = OS.Process.atExit (fn () => (safedel sym; safedel output))

val _ = tprint "Holmake -C <reldir> survives the lastmaker exec-switch"

(* Without the fix, the exec'd child re-resolves "subdir" against its
   post-chdir cwd (which is already .../subdir) and dies with
     Holmake died: -C subdir: No such file or directory *)
val cmd = String.concatWith " "
            ["./" ^ sym, "--no-cache", "-C", "subdir", "-n",
             ">", output, "2>&1"]
val res = OS.Process.system cmd
val out = read_file output handle _ => ""

val _ =
    if not (OS.Process.isSuccess res) then
      (print "\n--- captured Holmake output ---\n"; print out;
       print "--- end captured output ---\n";
       die "Holmake exited non-zero")
    else if String.isSubstring "No such file or directory" out then
      (print "\n--- captured Holmake output ---\n"; print out;
       print "--- end captured output ---\n";
       die "Holmake reported a missing directory")
    else OK ()
