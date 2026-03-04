open testutils

fun inDir d f =
  let
    val cur = OS.FileSys.getDir()
    val _ = OS.FileSys.chDir d
    val res = f ()
    val _ = OS.FileSys.chDir cur
  in
    res
  end

val _ = tprint "Cleaning test directory"
val _ = inDir "test" (fn () =>
  OS.Process.isSuccess (Systeml.systeml [Systeml.HOLDIR ^ "/bin/Holmake",
                                          "cleanAll"]))
val _ = OK()

val _ = tprint "--heap-size=2 should fail (heap too small)"
val res = inDir "test" (fn () =>
  Systeml.systeml [Systeml.HOLDIR ^ "/bin/Holmake",
                   "--holstate", Systeml.HOLDIR ^ "/bin/hol.state0",
                   "--heap-size=2", "--no_overlay", "-r"])
val _ = if OS.Process.isSuccess res
        then die "FAILED: expected build to fail with 2MB heap"
        else OK()

val _ = tprint "Cleaning test directory"
val _ = inDir "test" (fn () =>
  OS.Process.isSuccess (Systeml.systeml [Systeml.HOLDIR ^ "/bin/Holmake",
                                          "cleanAll"]))
val _ = OK()

val _ = tprint "Without --heap-size should succeed"
val res = inDir "test" (fn () =>
  Systeml.systeml [Systeml.HOLDIR ^ "/bin/Holmake",
                   "--holstate", Systeml.HOLDIR ^ "/bin/hol.state0",
                   "--no_overlay", "-r"])
val _ = if OS.Process.isSuccess res
        then OK()
        else die "FAILED: expected build to succeed without heap limit"
