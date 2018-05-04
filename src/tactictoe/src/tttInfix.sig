signature tttInfix =
sig

  datatype infixity_t = Inf_left of int | Inf_right of int
  val overlay_infixity : (string * infixity_t) list
  val infix_pair : infixity_t -> (string * string)

  val ttt_infixl0_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl0_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl1_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl1_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl2_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl2_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl3_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl3_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl4_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl4_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl5_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl5_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl6_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl6_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl7_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl7_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl8_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl8_close : ('a -> 'b) * 'a -> 'b
  val ttt_infixl9_open  : 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val ttt_infixl9_close : ('a -> 'b) * 'a -> 'b

  val ttt_infixr0_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr0_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr1_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr1_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr2_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr2_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr3_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr3_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr4_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr4_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr5_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr5_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr6_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr6_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr7_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr7_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr8_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr8_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val ttt_infixr9_open  : 'a * ('a -> 'b) -> 'b
  val ttt_infixr9_close : ('a * 'b -> 'c) * 'b -> 'a -> 'c

end
