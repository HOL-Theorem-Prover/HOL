Theory compDeltaC
Ancestors
  compDeltaBase

(* C is independent of A: a merge that starts from C's value and then
   visits B has to walk back through A *)
Theorem cdrf_0 = EVAL “cdrf 0”
