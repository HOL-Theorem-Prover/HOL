

open HolKernel Parse boolLib bossLib;

val _ = new_theory "other";


open sampleTheory;

val _ = print "Successfully opened sampleTheory\n"


val _ = export_theory();

