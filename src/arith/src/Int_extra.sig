signature Int_extra =
sig
  local type int = arbint.int in

   val gcd : int * int -> int
   val lcm : int * int -> int
  end
end
