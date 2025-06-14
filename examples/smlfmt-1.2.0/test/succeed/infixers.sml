
val xs = 8 :: 9 :: 10 :: nil
val ys = 1+1+2+1 :: 6 :: 7 :: xs @ 11 :: nil

val (<<, >>, !!) =
  let
    nonfix +
  in
    ( +, +, + )
  end

val (a, b) =
  let
    infix 5 << !!
    infixr 5 >>
    infixr 6 !!
  in
    ( 100 + 0 << 1 << 2 !! 3 << 4 << 5
    , 100 + 0 >> 1 >> 2 !! 3 >> 4 >> 5
    )
  end

val c = << (10, 15)
val d = >> (20, 25)
val e = !! (30, 35)

infix 5 << !!
infixr 5 >>
infixr 6 !!

val op<< = op>>
val op!! = op!!
val op>> = op<<
