signature UniversalType =
sig
  type t

  val embed: unit -> ('a -> t) * (t -> 'a option)
end
