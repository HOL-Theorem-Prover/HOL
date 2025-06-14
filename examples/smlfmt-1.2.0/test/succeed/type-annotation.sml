val a = 5 : int
val b = Int.toString : int -> string
val c = List.nil : int list
val d = List.foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
val e = Array.update : 'a array * int * 'a -> unit

type ('a, 'b) folder = ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
val f = List.foldl : ('a, 'b) folder

type sb = Substring.substring
val g = Substring.splitl : (char -> bool) -> sb -> sb * sb

type ('a, 'b) thing = 'a * 'a * 'b
val h = (5, 6, "hello"): (int, string) thing

val x: {a: string, b: ('a, 'b) thing -> 'a} =
  { a = "hello": string
  , b = fn (foo, _, _) => foo
  } : {a: string, b: ('a, 'b) thing -> 'a}
