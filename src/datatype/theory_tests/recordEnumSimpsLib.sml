structure recordEnumSimpsLib =
struct

  open simpLib BasicProvers

  val stupid_lemma = Q.prove(‘x < 10 ==> x < 11’,
                             SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []);

end
