(*---------------------------------------------------------------------------*)
(* A bridging theory between integers and reals                              *)
(*---------------------------------------------------------------------------*)

structure intrealScript =
struct

open HolKernel integerTheory realTheory

val _ = new_theory "intreal"

(*---------------------------------------------------------------------------*)
(* Define the inclusion homomorphism real_of_int :int->real.                 *)
(*---------------------------------------------------------------------------*)

val real_of_int = new_definition ("real_of_int", ``real_of_int i =
  if i < 0 then ~(real_of_num (Num (~i))) else real_of_num (Num i)``)

(*---------------------------------------------------------------------------*)
(* Floor and ceiling (ints)                                                  *)
(*---------------------------------------------------------------------------*)

val INT_FLOOR_def = bossLib.Define
  `INT_FLOOR (x:real) = LEAST_INT i. real_of_int (i+1) > x`

val INT_CEILING_def = bossLib.Define
  `INT_CEILING (x:real) = LEAST_INT i. x <= real_of_int i`

val _ = Parse.overload_on ("flr", ``INT_FLOOR``)
val _ = Parse.overload_on ("clg", ``INT_CEILING``)

(*---------------------------------------------------------------------------*)
(* is_int                                                                    *)
(*---------------------------------------------------------------------------*)

val is_int_def = bossLib.Define
  `is_int (x:real) = (x = real_of_int (INT_FLOOR x))`

val _ = export_theory ()

end
