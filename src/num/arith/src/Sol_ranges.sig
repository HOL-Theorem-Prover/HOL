signature Sol_ranges =
sig
 local type int = Arbint.int
 in
    val Shostak : (int * (string * int) list) list -> (string * int) list
 end
end
