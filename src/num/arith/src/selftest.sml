open simpLib Parse boolLib HolKernel

fun die s = (print s; Process.exit Process.failure)

val _ = print "Testing SUC_FILTER_ss ...                     "
val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.SUC_FILTER_ss
val th = QCONV (SIMP_CONV ss [arithmeticTheory.FUNPOW])
               ``FUNPOW (f:'a->'a) 2 x``
val _ = if not (aconv (rhs (concl th)) ``(f:'a -> 'a) (f x)``) then
          die "FAILED!\n"
        else print "OK\n"

val _ = print "Testing coefficient gathering in ARITH_ss ... "
val arith_ss = boolSimps.bool_ss ++ numSimps.ARITH_ss
val _ = if not (aconv (rhs (concl (SIMP_CONV arith_ss [] ``x + x + x``)))
                      ``3 * x``)
        then die "FAILED!\n"
        else print "OK\n"

val _ = Process.exit Process.success
