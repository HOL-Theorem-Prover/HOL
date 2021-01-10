QUse.useScript "../euclid.sml" handle _ => OS.Process.exit OS.Process.failure;
val _ = let
  val os = TextIO.openOut "euclid-OK"
in
  TextIO.output(os, "OK\n");
  TextIO.closeOut os
end;
