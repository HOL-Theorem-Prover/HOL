signature readermonad =
sig

  type ('s,'b) t = 's -> 'b

  val return : 'a -> ('s,'a) t
  val >- : ('s,'a) t * ('a -> ('s,'b) t) -> ('s,'b) t
  val >> : ('s,'a) t * ('s,'b) t -> ('s,'b) t

end
