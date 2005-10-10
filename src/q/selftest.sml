open Parse boolLib HolKernel

val _ = print "Testing Q.EXISTS ... "

val th = Q.EXISTS (`?f. f T T = T`, `$/\`) (REWRITE_CONV [] ``T /\ T``)
         handle HOL_ERR _ => Process.exit Process.failure

val _ = print "done\n"

val _ = Process.exit Process.success;

