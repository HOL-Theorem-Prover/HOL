(*==========================================================================*)
(* Build structure for the HOL type of natural numbers                      *)
(*==========================================================================*)

structure NumHOLType :> NumHOLType =
struct

open Exception Term;

fun failwith function = raise HOL_ERR{origin_structure = "NumHOLType",
                                      origin_function = function,
                                      message = ""};
open Lib Psyntax arithmeticTheory
type num = NumType.num

val num_ty = mk_type ("num",[]);

fun term_of_num n = mk_numeral (Arbint.toNat n)
  handle HOL_ERR _ => failwith "term_of_num";

fun num_of_term tm = Arbint.fromNat (dest_numeral tm)
  handle HOL_ERR _ => failwith "num_of_term";

val plus  = "+"
and minus = "-"
and mult  = "*"
and less  = "<"
and leq   = "<="
and great = ">"
and geq   = ">="
and suc   = "SUC"
and pre   = "PRE"
and zero  = "0"
and one   = "1";

end; (* NumHOLType *)
