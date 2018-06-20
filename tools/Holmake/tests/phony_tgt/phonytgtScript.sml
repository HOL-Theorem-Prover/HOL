open HolKernel Parse boolLib testutils

val _ = new_theory "phonytgt";
val op++ = OS.Path.concat

val _ = let
  val _ = tprint "Building output though all file exists"
  val _ = OS.FileSys.chDir "test1"
  val _ = OS.FileSys.remove "output" handle _ => ()
  val _ = Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake"]
in
  if OS.FileSys.access("output",[]) then OK()
  else die "FAILED!"
end

val _ = OS.FileSys.chDir ".."

val _ = save_thm("test1", TRUTH)

val _ = let
  val _ = tprint "Not building output as all file exists"
  val _ = OS.FileSys.chDir "test2"
  val _ = OS.FileSys.remove "output" handle _ => ()
  val _ = Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake"]
in
  if OS.FileSys.access("output",[]) then die "FAILED!"
  else OK()
end

val _ = OS.FileSys.chDir ".."

val _ = save_thm("test2", TRUTH)

val _ = export_theory();
