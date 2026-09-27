open testutils

val _ = tprint "hol --min can perform basic kernel operations"
val res =
    OS.Process.system
      (String.concat
         ["echo 'val _ = Feedback.emit_MESG := false; ",
          "val v = Term.mk_var(\"x\", Type.bool); ",
          "val _ = OS.Process.exit OS.Process.success;' | ",
          Systeml.protect (Systeml.HOLDIR ^ "/bin/hol"),
          " --min --quiet"])
val _ = if OS.Process.isSuccess res then OK() else die "FAILED"

val _ = tprint "hol --min does not have boolTheory loaded"
(* The absence is a compile-time "has not been declared", so that is
   what to look for rather than the exit status. *)
val outfile = OS.FileSys.tmpName()
val _ =
    OS.Process.system
      (String.concat
         ["echo 'val _ = boolTheory.TRUTH;' | ",
          Systeml.protect (Systeml.HOLDIR ^ "/bin/hol"),
          " --min --quiet > ", Systeml.protect outfile, " 2>&1"])
val output =
    let val istrm = TextIO.openIn outfile
    in TextIO.inputAll istrm before TextIO.closeIn istrm
    end handle IO.Io _ => ""
val _ = OS.FileSys.remove outfile handle OS.SysErr _ => ()
val _ = if String.isSubstring "boolTheory" output andalso
           String.isSubstring "has not been declared" output
        then OK()
        else die ("FAILED\n" ^ output)
