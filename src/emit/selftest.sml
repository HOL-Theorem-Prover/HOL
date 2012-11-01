local open basis_emitTheory in end

val (is_con, thy, name, ty) = ConstMapML.apply ``bool$IN``
fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

fun tprint s = print (StringCvt.padRight #" " 65 s)
val _ = tprint "Testing ConstMapML information for bool$IN"

val _ = if thy <> "set" then die "FAILED!" else print "OK\n"
