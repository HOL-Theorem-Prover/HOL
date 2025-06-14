val A x | B x | C x = foobar

fun foo (boo: ty as (A x | B x | C x | D x)) = ()

datatype t = A of int | B of int | C of int | D of int * int | E of int * int

fun f t =
  case t of
    A x | B x | C x => x + 1
  | D (x, _) | E (_, x) => x * 2