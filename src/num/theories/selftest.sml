open arithmeticTheory HolKernel boolLib

val _ = print "Testing that I can parse num$0"

val _ = (Parse.Term`num$0`; print "     OK\n")
        handle HOL_ERR _ => (print "     FAILED\n";
                             OS.Process.exit OS.Process.failure)

