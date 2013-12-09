(*****************************************************************************)
(* FILE          : sol_ranges.sml                                            *)
(* DESCRIPTION   : Functions for determining the ranges of the solutions to  *)
(*                 linear programming problems, and whether there are        *)
(*                 natural number solutions.                                 *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 18th April 1991                                           *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Sol_ranges :> Sol_ranges =
struct
  open Arbint
  val op << = String.<


open Rationals;
open Sup_Inf;
open Streams;
open Lib; infix ##;
open Feedback;

fun failwith function = raise HOL_ERR{origin_structure = "Sol_ranges",
                                      origin_function = function,
                                      message = ""};


(*---------------------------------------------------------------------------*)
(* less_bound : bound -> bound -> bool                                       *)
(*---------------------------------------------------------------------------*)

fun less_bound Neg_inf Neg_inf = failwith "less_bound"
  | less_bound Neg_inf (Bound (_,[])) = true
  | less_bound Neg_inf Pos_inf = true
  | less_bound (Bound (_,[])) Neg_inf = false
  | less_bound (Bound (r1,[])) (Bound (r2,[])) =
       ((rat_less r1 r2) handle _ => failwith "less_bound")
  | less_bound (Bound (_,[])) Pos_inf = true
  | less_bound Pos_inf Neg_inf = false
  | less_bound Pos_inf (Bound (_,[])) = false
  | less_bound Pos_inf Pos_inf = failwith "less_bound"
  | less_bound _ _ = failwith "less_bound";

(*---------------------------------------------------------------------------*)
(* is_neg_bound : bound -> bool                                              *)
(*---------------------------------------------------------------------------*)

fun is_neg_bound (Bound (r,[])) =
       ((rat_less r rat_zero) handle _ => failwith "is_neg_bound")
  | is_neg_bound Pos_inf = false
  | is_neg_bound Neg_inf = true
  | is_neg_bound _ = failwith "is_neg_bound";

(*---------------------------------------------------------------------------*)
(* is_finite_bound : bound -> bool                                           *)
(*---------------------------------------------------------------------------*)

fun is_finite_bound (Bound (_,[])) = true
  | is_finite_bound Pos_inf = false
  | is_finite_bound Neg_inf = false
  | is_finite_bound _ = failwith "is_finite_bound";

(*---------------------------------------------------------------------------*)
(* rat_of_bound : bound -> rat                                               *)
(*---------------------------------------------------------------------------*)

fun rat_of_bound (Bound (r,[])) = r
  | rat_of_bound _ = failwith "rat_of_bound";

(*---------------------------------------------------------------------------*)
(* is_int_range : rat -> rat -> bool                                         *)
(*---------------------------------------------------------------------------*)

fun is_int_range r1 r2 =
   let val i1 = upper_int_of_rat r1
       and i2 = lower_int_of_rat r2
   in  not (i2 < i1)
   end;

(*---------------------------------------------------------------------------*)
(* non_neg_int_between : bound -> bound -> int                               *)
(*---------------------------------------------------------------------------*)

fun non_neg_int_between b1 b2 =
   (case (b1,b2)
    of (Neg_inf,Neg_inf) => failwith "fail"
     | (Neg_inf,Bound (r,[])) =>
          (if (rat_less r rat_zero) then failwith "fail" else zero)
     | (Neg_inf,Pos_inf) => zero
     | (Bound (_,[]),Neg_inf) => failwith "fail"
     | (Bound (r1,[]),Bound (r2,[])) =>
          (let val i1 = upper_int_of_rat r1
               and i2 = lower_int_of_rat r2
               val i1' = if (i1 < zero) then zero else i1
           in  if (i2 < i1') then failwith "fail" else i1'
           end)
     | (Bound (r,[]),Pos_inf) =>
          (if (rat_less r rat_zero) then zero else upper_int_of_rat r)
     | (Pos_inf,Neg_inf) => failwith "fail"
     | (Pos_inf,Bound (_,[])) => failwith "fail"
     | (Pos_inf,Pos_inf) => failwith "fail"
     | _ => failwith "fail"
   ) handle _ => failwith "non_neg_int_between";

(*---------------------------------------------------------------------------*)
(* inst_var_in_coeffs : (string * int) ->                                    *)
(*                      (int * (string * int) list) list ->                  *)
(*                      (int * (string * int) list) list                     *)
(*                                                                           *)
(* Substitute a constant for a variable in a set of coefficients.            *)
(*---------------------------------------------------------------------------*)

fun inst_var_in_coeffs (v:string,c) coeffsl =
   let fun remove p l =
          if (p (hd l))
          then (hd l,tl l)
          else (I ## (fn r => ((hd l)::r))) (remove p (tl l))
   in
   if (null coeffsl)
   then []
   else let val (const,bind) = hd coeffsl
            val ((_,coeff),bind') =
               (remove (fn (name,_) => name = v) bind handle _ => ((v,zero),bind))
        in  (const + (c * coeff),bind')::
               (inst_var_in_coeffs (v,c) (tl coeffsl))
        end
   end;

(*---------------------------------------------------------------------------*)
(* Shostak : (int * (string * int) list) list -> (string * int) list         *)
(*                                                                           *)
(* Uses SUP-INF in the way described by Shostak to find satisfying values    *)
(* (natural numbers) for the variables in a set of inequalities (represented *)
(* as bindings). The function fails if it can't find such values.            *)
(*                                                                           *)
(* The function tries permutations of the variables, because the ordering    *)
(* can affect whether or not satisfying values are found. Lazy evaluation is *)
(* used to avoid computing all the permutations before they are required.    *)
(* This should help to avoid problems due to enormously long lists, but even *)
(* so, for a large number of variables, the function could execute for a     *)
(* very long time.                                                           *)
(*---------------------------------------------------------------------------*)

fun Shostak coeffsl =
   let fun vars_of_coeffs coeffsl =
          Lib.mk_set (flatten (map ((map fst) o snd) coeffsl))
       fun Shostak' coeffsl vars =
          let val no_vars = filter (null o snd) coeffsl
              val falses = filter (fn (n,_) => n < zero) no_vars
          in  if (null falses)
              then if (null vars)
                   then []
                   else let val coeffsl' =
                               filter (fn (n,l) => not (null l)) coeffsl
                            val var = hd vars
                            val b = Bound (rat_zero,[(var,rat_one)])
                            val sup = eval_bound (SIMP (SUP coeffsl' (b,[])))
                            and inf = eval_bound (SIMP (INF coeffsl' (b,[])))
                            val value = non_neg_int_between inf sup
                            val new_coeffsl =
                               inst_var_in_coeffs (var,value) coeffsl'
                        in  (var,value)::(Shostak' new_coeffsl (tl vars))
                        end
              else failwith "fail"
          end
       fun try f s = case s () of (Stream (x,s')) => (f x handle _ => try f s')
       val vars = vars_of_coeffs coeffsl
   in  (if (null vars)
        then Shostak' coeffsl []
        else try (Shostak' coeffsl) (permutations vars)
       ) handle _ => failwith "Shostak"
   end;

end
