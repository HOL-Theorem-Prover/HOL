val r = ref 5
val y =
  while !r >= 0 do
    r := List.filter (fn x => x mod 2 = 0) (List.tabulate (100, fn i => i))
fun foo bar =
  fizzbuzz
    (while foo bar > 100
     do (foo bar; foo baz; print "hello"))
