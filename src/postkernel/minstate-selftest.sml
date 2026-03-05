open testutils

val _ = tprint "hol --min starts with min theory as current"
val res =
    OS.Process.system
      ("echo 'if Theory.current_theory() = \"min\" then " ^
       "OS.Process.exit OS.Process.success " ^
       "else OS.Process.exit OS.Process.failure;' | " ^
       Systeml.protect (Systeml.HOLDIR ^ "/bin/hol") ^
       " --min --quiet")
val _ = if OS.Process.isSuccess res then OK() else die "FAILED"
