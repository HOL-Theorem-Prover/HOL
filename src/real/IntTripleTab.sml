(* Int-triple-keyed tables for SOSLib (block, row, col).                 *)
(* Separate file for the same reason as MonoTab.sml; see that file.      *)

structure IntTripleTab = Table(
  type key = int * int * int

  fun eqvar3_compare ((a1,b1,c1):key, (a2,b2,c2):key) =
      case Int.compare(a1,a2) of
          EQUAL => (case Int.compare(b1,b2) of
                        EQUAL => Int.compare(c1,c2)
                      | ord => ord)
        | ord => ord

  val ord = eqvar3_compare
  fun pp (i,j,k) =
      HOLPP.add_string ("(" ^ Int.toString i ^ "," ^ Int.toString j ^ "," ^
                        Int.toString k ^ ")")
)
