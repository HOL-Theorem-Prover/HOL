open HolKernel Parse boolLib

open gh1370Theory

val _ = new_theory "gh1370child";

val _ = type_of gh1370Theory.ctm = bool andalso
        (print "ctm has correct type\n";true) orelse
        OS.Process.exit OS.Process.failure

val _ = export_theory();
