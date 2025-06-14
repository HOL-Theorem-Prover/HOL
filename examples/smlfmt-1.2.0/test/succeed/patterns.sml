val ((x)) = "hello"
val () = ()
val "hello" = "hello"
val ("hello") = "hello"
val (_, ("world")) = ("hello", "world")
val ( (a, b, c)
    , d
    , (e, f)
    , whyIsThisParameterNamedSoBig
    , (h, i, j, k, l, m, n, oo, p)
    ) =
  someLongFunctionName ()
val ([(x), (1,2,3), "hello", Option.NONE]) =
  [ 0, (1,2,3), "hello", NONE ]

infix 5 !!
val SOME op!! = SOME (fn (a, b) => a + b)
val SOME (Option.SOME (1 :: 2 :: [])) = SOME (SOME [1,2])

val xx =
  case SOME x of
    Option.NONE => "hello"
  | Option.SOME (SOME NONE) => "what"
  | SOME _ => "goodbye"

val x as SOME y : int option = SOME 5
val SOME (op!! : int * int -> int as f) = SOME op+

val 1 :: 2 :: (3:int) :: nil = [1,2,3]

(** this is strange, but legit... *)
type 'a :: = 'a list
type 'a nil = 'a
val 1 :: 2 :: []:int :: nil = [1,2]


val {x, y: int option as SOME (z: int), a = "hello", ...} =
  { x = 1
  , y = SOME 2
  , a = "hello"
  , b = ()
  }
