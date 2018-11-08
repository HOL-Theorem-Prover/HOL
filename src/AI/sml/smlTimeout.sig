signature smlTimeout =
sig

  exception TimeOut
  val timeOut : real -> ('a -> 'b) -> 'a -> 'b

end
