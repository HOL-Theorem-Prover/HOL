open HolKernel Parse boolLib

val _ = new_theory"bug";

Definition bug_def:
  bug = nothing to see here
Termination
  cheat
QED

val _ = export_theory();
