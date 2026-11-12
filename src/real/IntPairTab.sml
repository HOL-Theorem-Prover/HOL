(* Int-pair-keyed tables for SOSLib (matrix indices).                    *)
(* Separate file for the same reason as MonoTab.sml; see that file.      *)

structure IntPairTab = Table(
  type key = int * int

  fun intpair_compare ((i1,j1):key, (i2,j2):key) =
      case Int.compare(i1,i2) of EQUAL => Int.compare(j1,j2) | ord => ord

  val ord = intpair_compare
  fun pp (i,j) =
      HOLPP.add_string ("(" ^ Int.toString i ^ "," ^ Int.toString j ^ ")")
)
