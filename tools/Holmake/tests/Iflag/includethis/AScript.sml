open HolKernel Parse boolLib bossLib;

val _ = new_theory "A";

val foo_def = Define`
  foo x = x * 10 + 1
`;

val _ = export_theory();
