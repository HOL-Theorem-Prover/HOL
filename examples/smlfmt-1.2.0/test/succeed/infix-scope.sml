val << = fn (x, y) => x + y
fun foo x =
  let
    infix <<
  in
    x << 5
  end

val res = 2 << 3

val hello = fn (x, y) => x + y
fun foo x =
  let
    infix hello
  in
    x hello 5
  end

val res = 2 hello 3
