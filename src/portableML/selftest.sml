
val _ =print "\n"

fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

fun assert (s, b) =
    (print (StringCvt.padRight #" " 65 s);
     if b() then print "OK\n"
     else die "FAILED!")


open Redblackset
val es = empty Int.compare

fun m10cmp (i1,i2) = Int.compare(i1 mod 10, i2 mod 10)
val em10 = empty m10cmp
val em3 = add(em10, 3)
val em13 = add(em3, 13)

val _ = List.app assert [
    ("Redblackset.isSubset({},{})", fn () => isSubset(es,es)),
    ("Redblackset.isSubset({}, {1})",
     (fn () => isSubset(es,addList(es,[1])))),
    ("Redblackset.add replaces EQUAL elements",
     (fn () => listItems em13 = [13]))
    ]

val _ = OS.Process.exit OS.Process.success
