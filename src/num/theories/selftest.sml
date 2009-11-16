open arithmeticTheory HolKernel boolLib

fun tprint s = print (StringCvt.padRight #" " 60 s)

fun fail() = (print "FAILED\n"; OS.Process.exit OS.Process.failure)

val _ = tprint "Testing that I can parse num$0"
val _ = (Parse.Term`num$0`; print "OK\n")
        handle HOL_ERR _ => fail()

val _ = tprint "Testing that I can't parse num$1"
val _ = (Parse.Term`num$1`; fail()) handle HOL_ERR _ => print "OK\n";


val _ = tprint "Testing that bool$0 fails"
val _ = (Parse.Term`bool$0`; fail()) handle HOL_ERR _ => print "OK\n"

val _ = tprint "Testing that num$01 fails"
val _ = (Parse.Term`num$01`; fail()) handle HOL_ERR _ => print "OK\n"
