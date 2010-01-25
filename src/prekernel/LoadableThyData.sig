signature LoadableThyData =
sig

  type t
  val make : {merge : 'a * 'a -> 'a,
              read_update: string -> 'a,
              write_update : 'a -> string} ->
             {mk: 'a -> t, dest: t -> 'a option}

  val read_update : t -> string -> t
  val write_update : t -> string
  val merge : t * t -> t

end
