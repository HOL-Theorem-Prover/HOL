fun f (x, y) : int = x + y

fun ++ (a, b) = a + b
fun op++ (a, b) = a + b
infix ++
fun op++ (a, b) = a + b

fun foo _ "hello" (1, #"a", 2) () Option.NONE =
  let
    val bar = foo () "hello" (1, #"a", 2) () NONE
  in
    bar
  end
