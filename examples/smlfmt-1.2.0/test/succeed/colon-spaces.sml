val y: int as (x: int) : int = 5
val ([1,2,3]:int list) = f()
type x = {! : int, 5: int}

signature X =
sig
  val x: int
  val y: int -> int
  val !! : string

  structure Y : sig end
end

structure XX:>X = struct end
structure YY:Y = struct end

functor F(X: X) :> sig end = struct end