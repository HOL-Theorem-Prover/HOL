(* Issue #1979: case-mismatched load on case-insensitive filesystems
   should die with a clear "module is registered as ..." message rather
   than silently mis-loading.

   The .uo and .ui files Holmake produces are plain-text newline-
   separated lists of source paths.  The case check in poly-init2.ML
   peeks at each line's basename, so we can fabricate a minimal .ui
   directly under .hol/objs/ (where HFS resolves it) without invoking
   Holmake's full pipeline. *)

open testutils

val op++ = OS.Path.concat
val hol = Globals.HOLDIR ++ "bin" ++ "hol"

val testdir = OS.FileSys.tmpName ()
val _ = (OS.FileSys.remove testdir handle OS.SysErr _ => ())
val _ = OS.FileSys.mkDir testdir
val _ = OS.FileSys.mkDir (testdir ++ ".hol")
val _ = OS.FileSys.mkDir (testdir ++ ".hol" ++ "objs")

fun writeFile path s =
    let val out = TextIO.openOut path
    in TextIO.output (out, s); TextIO.closeOut out end

fun rm_rf d =
    let val ds = OS.FileSys.openDir d
        fun loop () =
            case OS.FileSys.readDir ds of
                NONE => ()
              | SOME f =>
                  let val p = d ++ f
                  in
                    (if OS.FileSys.isDir p then rm_rf p
                     else OS.FileSys.remove p)
                    handle OS.SysErr _ => ();
                    loop ()
                  end
    in
      loop ();
      OS.FileSys.closeDir ds;
      OS.FileSys.rmDir d
    end handle OS.SysErr _ => ()

(* Write fooBar.ui whose contents reference FooBar.sig — i.e., the
   build artifact says the module's real case is "FooBar", but the
   file is named "fooBar".  This is exactly what a case-insensitive
   FS produces when the user typed the wrong case. *)
val objs = testdir ++ ".hol" ++ "objs"
val _ = writeFile (objs ++ "fooBar.ui") (testdir ++ "FooBar.sig\n")
val _ = writeFile (objs ++ "fooBar.uo") (testdir ++ "FooBar.sml\n")

val saved = OS.FileSys.getDir ()
val _ = OS.FileSys.chDir testdir

val _ = writeFile "input.sml" "load \"fooBar\";\n"
val _ = OS.Process.system
            (String.concatWith " "
               [Systeml.protect hol, "--bare", "--zero", "--noconfig",
                "<", "input.sml", ">", "out", "2>&1"])
val output =
    let val s = TextIO.openIn "out"
    in TextIO.inputAll s before TextIO.closeIn s end

val _ = OS.FileSys.chDir saved

val _ = tprint "load reports case mismatch (#1979)"
val _ =
    if String.isSubstring "module is registered as \"FooBar\"" output
    then (rm_rf testdir; OK ())
    else (print "\n--- captured hol output ---\n";
          print output;
          print "--- end captured output ---\n";
          rm_rf testdir;
          die "FAILED: case-mismatch message not present")
