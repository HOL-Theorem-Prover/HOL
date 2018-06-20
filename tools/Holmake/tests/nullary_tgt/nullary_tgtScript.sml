open HolKernel Parse boolLib testutils

val _ = new_theory "nullary_tgt";

val _ = let
  val _ = tprint "Testing creation of output file via Holmake"
  val op++ = OS.Path.concat
  val _ = OS.FileSys.chDir "test"
  val _ = OS.FileSys.remove "output" handle _ => ()
  val _ = Systeml.systeml [Systeml.HOLDIR ++ "bin" ++ "Holmake"]
in
  if OS.FileSys.access("output", []) then OK()
  else die "FAILED!"
end

val _ = OS.FileSys.chDir OS.Path.parentArc

val th = save_thm("th", TRUTH);


val _ = export_theory();
