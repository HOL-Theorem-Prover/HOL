signature ThmSetData =
sig

  val mkData : string list -> LoadableThyData.t
  val destData : LoadableThyData.t -> (string * Thm.thm) list option
  val write : string list -> string

  val nullset : LoadableThyData.t

end
