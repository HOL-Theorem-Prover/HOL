structure X = Y
structure Z = X.Y.Foo
and Bar = X.Y
and Baz = Z

structure X: Foo = Y

structure Y:
sig
  type t
  type u
  datatype 'a x = Foo | Bar
  val x: t
  val y: u -> t
end
where type t = int
  and type u = unit
= FooBar

and Z :> YO = Ya


structure Hello :>
sig
  val hello: string -> unit
end =
struct
  fun hello x = print (x ^ "\n")
end

signature X = sig type t end
signature Y = sig end

structure S :> Y =
  struct type t = int end : sig type t end : sig end
structure S =
  struct type t = int end : X : Y

and S = F(X)
and T :> Y = Fun (struct type t = int val x: int = 5 end) : X

and X =
  FooBun (type t = int
          val x: t = 5
          datatype P = L | R);

structure S = FunBar (structure X:Foo = X val hello: string = "hello")

structure Foobar =
  let
    structure Hello :>
    sig
      val hello: string -> unit
    end =
    struct
      fun hello x = print (x ^ "\n")
    end

    structure Goodbye = G (structure X:Foo = Hello val hello: string = "hello")
  in
    let in
      struct
        type t = string
        fun hello (x: t) : unit = Hello.hello
        val goodbye = Goodbye.hello
      end
    end
  end;

local
  structure X = Y;
  structure Z :> S = let structure A = B in B :> S end
in
structure Foo = F(structure X = X structure Y = Z)
end
