structure intML :> intML = 
struct
  open Arbint
  fun curry f x y = f (x,y);

  val op +    = curry Arbint.+
  val op -    = curry Arbint.-
  val op *    = curry Arbint.*
  val op div  = curry Arbint.div
  val op mod  = curry Arbint.mod
  val op quot = curry Arbint.quot
  val op rem  = curry Arbint.rem
  val divmod  = curry Arbint.divmod
  val quotrem = curry Arbint.quotrem

  val op <    = curry Arbint.<
  val op <=   = curry Arbint.<=
  val op >    = curry Arbint.>
  val op >=   = curry Arbint.>=

  val compare = curry Arbint.compare
  val min     = curry Arbint.min
  val max     = curry Arbint.max

end
