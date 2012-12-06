open testutils TotalDefn

val _ = tprint "Testing mutually recursive function definition"

val f_def = Define`
  (f x = if x = 0 then T else ~g(x - 1)) /\
  (g x = if x = 0 then F else ~f(x - 1))
` handle _ => die "FAILED!"

val _ = print "OK\n";
