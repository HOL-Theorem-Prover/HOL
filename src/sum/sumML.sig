signature sumML =
sig
  datatype ('a,'b)sum = INL of 'a | INR of 'b

  val isl  : ('a,'b)sum -> bool
  val isr  : ('a,'b)sum -> bool
  val outl : ('a,'b)sum -> 'a
  val outr : ('a,'b)sum -> 'b
end
