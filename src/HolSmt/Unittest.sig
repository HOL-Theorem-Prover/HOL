signature Unittest =
sig

  val assert : bool * string -> unit
  val die : string -> 'a

  val run_unittests : unit -> unit

end
