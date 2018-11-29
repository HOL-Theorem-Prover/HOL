fun tprint s = print (StringCvt.padRight #" " 75 s)
fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

val _ = tprint "nameStream in subscripting mode starts at 1";

val f = Lexis.nameStrm (SOME "") "foo"
val l = List.tabulate(10, fn i => f())
val expected = List.tabulate(10, fn i => "foo" ^ Int.toString (i + 1))

val _ = (l = expected before print "OK\n") orelse die "FAILED"
