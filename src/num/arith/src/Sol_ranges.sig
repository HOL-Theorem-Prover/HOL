signature Sol_ranges =
sig
  type int = Arbint.int

  val Shostak : (int * (string * int) list) list -> (string * int) list
end
