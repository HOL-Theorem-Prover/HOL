signature numeralConvLib = sig
  include Abbrev

  val to_binary : conv
  (* to_binary [n] = |- n = n'
     for n made from ZERO, BIT1, and BIT2
     ensures n' is made from 0, BIT0, and BIT1
   *)

end
