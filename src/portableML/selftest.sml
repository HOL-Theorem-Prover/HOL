
val _ =print "\n"

fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

fun assert (s, b) =
    (print (StringCvt.padRight #" " 65 s);
     if b() then print "OK\n"
     else die "FAILED!")


open Redblackset
val es = empty Int.compare

val _ = List.app assert [
    ("Redblackset.isSubset({},{})", fn () => isSubset(es,es)),
    ("Redblackset.isSubset({}, {1})",
     (fn () => isSubset(es,addList(es,[1]))))
    ]

val _ = OS.Process.exit OS.Process.success
