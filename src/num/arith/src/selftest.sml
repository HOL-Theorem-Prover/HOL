(* check SUC_FILTER_ss is working correctly *)
open simpLib Parse boolLib HolKernel

val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.SUC_FILTER_ss

val th = QCONV (SIMP_CONV ss [arithmeticTheory.FUNPOW])
               ``FUNPOW (f:'a->'a) 2 x``

val _ = print "Testing SUC_FILTER_ss ... "
val _ = if rhs (concl th) <> ``(f:'a -> 'a) (f x)`` then
          (print "FAILED!\n" ; Process.exit Process.failure)
        else print "OK\n"

val _ = Process.exit Process.success
