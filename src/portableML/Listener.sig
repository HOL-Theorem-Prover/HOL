signature Listener = sig

  type 'a t
  exception DUP of string
  val add_listener : 'a t -> (string * ('a -> unit)) -> unit
  val remove_listener : 'a t -> string -> ('a -> unit) option
  val listeners : 'a t -> (string * ('a -> unit)) list
  val new_listener : unit -> 'a t
  val call_listener : 'a t -> 'a -> (string * ('a -> unit) * exn) list
  val without_one : 'a t -> string -> ('b -> 'c) -> ('b -> 'c)
  val without_all : 'a t -> ('b -> 'c) -> ('b -> 'c)

end
