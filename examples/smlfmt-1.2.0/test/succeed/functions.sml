fun 'a op fact 0 = 1
  | op fact n = n * fact (n-1)

fun ('a, 'b) bar 0 = 2
  | op bar n = n
and op baz (SOME true) = []
  | baz (SOME false) = [2, 3]
  | baz NONE = [3, 1, 4]
and bear [] = ()
and bees "hi" = "there"

fun ('a, 'b, 'c) op foo 0 (SOME x) (x, y, z) {bob, harper} [2] _ true () = 3
  | foo n NONE (a, b, c) {bob, harper = 3} (2::3::[]) "hi" _ () = 5

fun (x + y) = x * y
fun (x + y) : int = x * y
fun (x + y) a b c = x * y
fun x + y : int = x * y
fun x + y = x * y

fun op+ (x, y) = x * y
fun op+ - op* : int = 0

fun (Option.SOME x) + Option.NONE = "hello"
  | op+ (NONE, SOME x) = "goodbye"
