signature STREAM =
sig
  datatype 'a u = Nil | Cons of 'a * 'a t
  withtype 'a t = unit -> 'a u
end
