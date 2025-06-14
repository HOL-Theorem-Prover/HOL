functor F(X:S) =
  G(structure X = X structure Y = X) :> T

functor F(X:S) : T =
  let structure Y = X in Y end

and F(type t val x: t) :> Foo =
struct
  type u = t
  fun f y = (x, y)
end

functor F(include T) =
struct
end
