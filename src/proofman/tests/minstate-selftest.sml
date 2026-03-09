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
val res =
    OS.Process.system
      (String.concat
         ["echo 'val _ = (boolTheory.TRUTH; ",
          "OS.Process.exit OS.Process.failure); ",
          "val _ = OS.Process.exit OS.Process.success;' | ",
          Systeml.protect (Systeml.HOLDIR ^ "/bin/hol"),
          " --min --quiet"])
val _ = if OS.Process.isSuccess res then OK() else die "FAILED"
