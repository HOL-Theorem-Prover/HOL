
datatype ('a, 'b) either = INL of 'a | INR of 'b
datatype foo = A

datatype even = Z | S1 of odd
and odd = S2 of even

datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree

datatype ('a, 'b, 'c) complicated =
    op Con1 of int * string
  | Con2 of int -> string
  | Con3
and complicate = op Cons1 | Cons2 of (int, string, bool) complicated
and 'a complex = Const
withtype bar = int
and 'a baz = string

datatype odd = even
datatype even = odd
