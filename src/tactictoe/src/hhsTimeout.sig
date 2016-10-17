signature hhsTimeout =
sig

  exception TacTimeOut
  val timeOut : real -> ('a -> 'b) -> 'a -> 'b

end
