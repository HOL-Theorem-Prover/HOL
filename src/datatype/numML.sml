structure numML :> numML = 
struct
  open Arbnum
  fun curry f x y = f (x,y);

  val op + = curry Arbnum.+
  val op - = curry Arbnum.-
  val op * = curry Arbnum.*
  val op div = curry Arbnum.div
  val op mod = curry Arbnum.mod
  val divmod =  curry Arbnum.divmod

  val op <   = curry Arbnum.<
  val op <=  = curry Arbnum.<=
  val op >   = curry Arbnum.>
  val op >=  = curry Arbnum.>=

end
