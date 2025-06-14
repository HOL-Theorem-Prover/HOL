
val x = 5;

fun foo (x, y) = "hello"
  | foo _ = "goodbye";

type int = string
and huh = string
and yah = string -> string

datatype X =
  XX of int (* AAA *) t
| YY of int list t
| ZZZ of sheesh
and sheesh = Sheeeesh of X
withtype 'a t = 'a list

datatype Y = Why of Y

datatype Z = datatype X

exception foobar (* X *) of string
and whatWhereWhy of int -> (unit -> int) -> string
and nope
and yep of string

exception hello
and goodbye;

val _ =
  let
    local
      datatype Ya = Boi
    in
    val x: Ya = Boi
    end
  in
    ()
  end

open X Y Foo.Z

abstype 'a (* XXX *) foo
  = Foo of 'a
  | Bar of 'a * 'a
  | Baz of baz
and baz
  = Bazz of baz * baz
  | Fooo of int foo t
withtype 'a t = 'a * 'a
with
  fun foo x = Foo x
  fun bar x = Bar (x,x)
end
