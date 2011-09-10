signature Nonce =
sig

  eqtype 'a t
  val mk : 'a -> 'a t
  val dest : 'a t -> 'a

end


