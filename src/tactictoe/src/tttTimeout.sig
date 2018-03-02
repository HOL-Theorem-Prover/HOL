signature tttTimeout =
sig

  exception TacTimeOut
  val timeOut : real -> ('a -> 'b) -> 'a -> 'b

end
