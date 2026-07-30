signature Lock =
sig

  type t
  val new          : string -> t
  val synchronized : t -> (unit -> 'a) -> 'a

end
