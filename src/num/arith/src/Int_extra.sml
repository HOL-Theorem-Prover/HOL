(*****************************************************************************)
(* FILE          : int_extra.sml                                             *)
(* DESCRIPTION   : Additional functions for integer arithmetic in ML.        *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Int_extra :> Int_extra =
struct
  open Arbint Feedback;

(*---------------------------------------------------------------------------*)
(* Function to compute the Greatest Common Divisor of two integers.          *)
(*---------------------------------------------------------------------------*)

fun gcd (i,j) =
   let exception non_neg
       fun gcd' (i,j) =
          let val r = (i mod j)
          in  if (r = zero)
              then j
              else gcd' (j,r)
          end
   in  (if ((i < zero) orelse (j < zero))
        then raise non_neg
        else if (i < j) then gcd' (j,i) else gcd' (i,j)
       ) handle _ => raise HOL_ERR{origin_structure = "Arith",
                                   origin_function = "gcd",
                                   message = ""}
   end;

(*---------------------------------------------------------------------------*)
(* Function to compute the Lowest Common Multiple of two integers.           *)
(*---------------------------------------------------------------------------*)

fun lcm (i,j) = (i * j) div (gcd (i,j))
                handle _ => raise HOL_ERR{origin_structure = "Arith",
                                          origin_function = "lcm",
                                          message = ""};

end
