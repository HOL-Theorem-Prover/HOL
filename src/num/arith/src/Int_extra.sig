signature Int_extra =
sig
  type int = Arbint.int 

  val gcd : int * int -> int
  val lcm : int * int -> int
end
