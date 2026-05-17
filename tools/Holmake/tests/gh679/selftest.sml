(* Issue #679: warn when directory contents differ only by case. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"

val testdir = OS.FileSys.tmpName ()
val _ = (OS.FileSys.remove testdir handle OS.SysErr _ => ())
val _ = OS.FileSys.mkDir testdir

fun write_empty f =
    let val s = TextIO.openOut (testdir ++ f)
    in TextIO.output (s, "(* empty *)\n"); TextIO.closeOut s end

val _ = write_empty "foo.sml"
val _ = write_empty "Foo.sml"

fun list_dir d =
    let val ds = OS.FileSys.openDir d
        fun loop acc =
            case OS.FileSys.readDir ds of
                NONE => (OS.FileSys.closeDir ds; acc)
              | SOME f => loop (f :: acc)
    in loop [] end

val entries = list_dir testdir
val both_present = List.exists (fn f => f = "foo.sml") entries andalso
                   List.exists (fn f => f = "Foo.sml") entries

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

val _ = tprint "Case-only filename collision emits warning (#679)"

val _ =
    if not both_present then
      (rm_rf testdir;
       print "(filesystem is case-insensitive; skipping) ";
       OK ())
    else
      let
        val saved = OS.FileSys.getDir ()
        val _ = OS.FileSys.chDir testdir
        val cmd = String.concatWith " "
                    [Systeml.protect Holmake, "-n",
                     ">", "out", "2>&1"]
        val _ = OS.Process.system cmd
        val s = TextIO.openIn "out"
        val output = TextIO.inputAll s before TextIO.closeIn s
        val _ = OS.FileSys.chDir saved
      in
        if String.isSubstring "case-only filename collision" output
        then (rm_rf testdir; OK ())
        else (print "\n--- captured Holmake output ---\n";
              print output;
              print "--- end captured output ---\n";
              rm_rf testdir;
              die "FAILED: warning not present in Holmake output")
      end
