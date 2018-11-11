signature Exn =
sig

  datatype 'a result = Res of 'a | Exn of exn

  val get_res: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a


end
