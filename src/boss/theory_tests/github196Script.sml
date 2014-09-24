open HolKernel Parse boolLib bossLib;

val _ = new_theory "github196";

val _ = (
  Define ` (dummy2 c NONE = c) /\ (dummy2 d (SOME _) = c)` ;
  print "Malformed definition goes through - FAILURE\n";
  OS.Process.exit OS.Process.failure)
handle HOL_ERR _ => print "Test-case OK\n"

val _ = export_theory();
