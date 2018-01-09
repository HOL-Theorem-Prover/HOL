open HolKernel boolLib testutils

fun Va n = mk_var("va" ^ Int.toString n, bool)
fun Vb n = mk_var("vb" ^ Int.toString n, bool)

fun dnfgen n =
  list_mk_conj (List.tabulate(n, fn i => mk_disj(Va i, Vb i)))
fun cnfgen n =
  list_mk_disj (List.tabulate(n, fn i => mk_conj(Va i, Vb i)))

fun test gen c nm sz =
  (tprint (nm ^ StringCvt.padLeft #" " 3 (Int.toString sz));
   timed c (exncheck (fn _ => OK())) (gen sz));

val _ = List.app (test dnfgen Canon.DNF_CONV "DNF_CONV") [10,11,12,13,14];
val _ = List.app (test cnfgen Canon.CNF_CONV "CNF_CONV") [10,11,12,13,14];
