signature hhsInfix =
sig
  
  datatype infixity_t = Inf_left of int | Inf_right of int
  val overlay_infixity : (string * infixity_t) list
  val infix_pair : infixity_t -> (string * string)
  
  val hhs_infixl0_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl0_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl1_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl1_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl2_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl2_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl3_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl3_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl4_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl4_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl5_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl5_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl6_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl6_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl7_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl7_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl8_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl8_close : ('a -> 'b) * 'a -> 'b
  val hhs_infixl9_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val hhs_infixl9_close : ('a -> 'b) * 'a -> 'b
  
  val hhs_infixr0_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr0_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr1_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr1_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr2_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr2_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr3_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr3_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr4_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr4_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr5_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr5_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr6_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr6_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr7_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr7_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr8_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr8_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val hhs_infixr9_open  : 'a * ('a -> 'b) -> 'b
  val hhs_infixr9_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c

end
