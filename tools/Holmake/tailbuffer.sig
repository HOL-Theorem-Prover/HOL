signature tailbuffer =
sig

  type t
  val new : {numlines : int} -> t
  val append : string -> t -> t
  val output : t -> (string list * string)

end
