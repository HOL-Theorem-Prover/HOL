(*****************************************************************************)
(* FILE          : term_coeffs.sml                                           *)
(* DESCRIPTION   : Functions for converting between arithmetic terms and     *)
(*                 their representation as bindings of variable names to     *)
(*                 coefficients.                                             *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 15th February 1993                                        *)
(*****************************************************************************)

structure Term_coeffs :> Term_coeffs =
struct
  open Arbint HolKernel boolLib Arith_cons Rsyntax;

  val << = String.<
  infix << ##;

fun failwith function = raise (mk_HOL_ERR "Term_coeffs" function "");


(*===========================================================================*)
(* Manipulating coefficient representations of arithmetic expressions        *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* negate_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)        *)
(*                                                                           *)
(* Negates constant value and coefficients of variables in a binding.        *)
(*---------------------------------------------------------------------------*)

fun negate_coeffs x = ((fn n => zero - n) ##
                       (map (I ## (fn n => zero - n)))) x;

(*---------------------------------------------------------------------------*)
(* merge_coeffs : (int * (string * int) list) ->                             *)
(*                (int * (string * int) list) ->                             *)
(*                (int * (string * int) list)                                *)
(*                                                                           *)
(* Sums constant values and merges bindings by adding coefficients of any    *)
(* variable that appears in both bindings. If the sum of the coefficients is *)
(* zero, the variable concerned is not entered in the new binding.           *)
(*---------------------------------------------------------------------------*)

fun merge_coeffs coeffs1 coeffs2 =
   let fun merge bind1 bind2 =
          if (null bind1) then bind2
          else if (null bind2) then bind1
          else (let val (name1:string,coeff1) = hd bind1
                    and (name2,coeff2) = hd bind2
                in  if (name1 = name2)
                    then if ((coeff1 + coeff2) = zero)
                         then merge (tl bind1) (tl bind2)
                         else (name1,(coeff1 + coeff2))::
                                 (merge (tl bind1) (tl bind2))
                    else if (name1 << name2)
                         then (name1,coeff1)::(merge (tl bind1) bind2)
                         else (name2,coeff2)::(merge bind1 (tl bind2))
                end)
       val (const1,bind1) = coeffs1
       and (const2,bind2) = coeffs2
   in  ((const1 + const2:int),merge bind1 bind2)
   end;

(*---------------------------------------------------------------------------*)
(* lhs_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)           *)
(*                                                                           *)
(* Extract strictly negative coefficients and negate them.                   *)
(*---------------------------------------------------------------------------*)

fun lhs_coeffs x =
   let fun f n = if (n < zero) then (zero - n) else zero
       fun g (s,n) = if (n < zero) then (s,(zero - n))
                     else failwith "lhs_coeffs"
   in  (f ## (mapfilter g)) x
   end;

(*---------------------------------------------------------------------------*)
(* rhs_coeffs : (int * ('a * int) list) -> (int * ('a * int) list)           *)
(*                                                                           *)
(* Extract strictly positive coefficients.                                   *)
(*---------------------------------------------------------------------------*)

fun rhs_coeffs x =
   let fun f n = if (n > zero) then n else zero
   in  (f ## (filter (fn (_,n) => n > zero))) x
   end;

(*---------------------------------------------------------------------------*)
(* diff_of_coeffs :                                                          *)
(*    ((int * (string * int) list) * (int * (string * int) list)) ->         *)
(*    ((int * (string * int) list) * (int * (string * int) list))            *)
(*                                                                           *)
(* Given the coefficients representing two inequalities, this function       *)
(* computes the terms (as coefficients) that have to be added to each in     *)
(* order to make the right-hand side of the first equal to the left-hand side*)
(* of the second.                                                            *)
(*---------------------------------------------------------------------------*)

fun diff_of_coeffs (coeffs1,coeffs2) =
   let val coeffs1' = rhs_coeffs coeffs1
       and coeffs2' = lhs_coeffs coeffs2
       val coeffs = merge_coeffs (negate_coeffs coeffs1') coeffs2'
   in  (rhs_coeffs coeffs,lhs_coeffs coeffs)
   end;

(*---------------------------------------------------------------------------*)
(* vars_of_coeffs : ('a * (''b * 'c) list) list -> ''b list                  *)
(*                                                                           *)
(* Obtain a list of variable names from a set of coefficient lists.          *)
(*---------------------------------------------------------------------------*)

fun vars_of_coeffs coeffsl =
 Lib.mk_set(Lib.flatten (map ((map fst) o snd) coeffsl));

(*===========================================================================*)
(* Extracting coefficients and variable names from normalized terms          *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* var_of_prod : term -> string                                              *)
(*                                                                           *)
(* Returns variable name from terms of the form "var" and "const * var".     *)
(*---------------------------------------------------------------------------*)

fun var_of_prod tm =
 (#Name (dest_var tm)) handle HOL_ERR _ =>
 (#Name (dest_var (rand tm))) handle HOL_ERR _ =>
 failwith "var_of_prod";

(*---------------------------------------------------------------------------*)
(* coeffs_of_arith : term -> (int * (string * int) list)                     *)
(*                                                                           *)
(* Takes an arithmetic term that has been sorted and returns the constant    *)
(* value and a binding of variable names to their coefficients, e.g.         *)
(*                                                                           *)
(*    coeffs_of_arith `1 + (4 * x) + (10 * y)`  --->                         *)
(*    (1, [("x", 4); ("y", 10)])                                             *)
(*                                                                           *)
(* Assumes that there are no zero coefficients in the argument term. The     *)
(* function also assumes that when a variable has a coefficient of one, it   *)
(* appears in the term as (for example) `1 * x` rather than as `x`.          *)
(*---------------------------------------------------------------------------*)

fun coeffs_of_arith tm =
   let fun coeff tm = (int_of_term o rand o rator) tm
       fun coeffs tm =
          (let val (prod,rest) = dest_plus tm
           in  (var_of_prod prod,coeff prod)::(coeffs rest)
           end
          ) handle HOL_ERR _ => [(var_of_prod tm,coeff tm)]
   in  (let val (const,rest) = dest_plus tm
        in  (int_of_term const,coeffs rest)
        end)
       handle HOL_ERR _ => (int_of_term tm,[])
       handle HOL_ERR _ => (zero,coeffs tm)
       handle HOL_ERR _ => failwith "coeffs_of_arith"
   end;

(*---------------------------------------------------------------------------*)
(* coeffs_of_leq : term -> (int * (string * int) list)                       *)
(*                                                                           *)
(* Takes a less-than-or-equal-to inequality between two arithmetic terms     *)
(* that have been sorted and returns the constant value and a binding of     *)
(* variable names to their coefficients for the equivalent term with zero on *)
(* the LHS of the inequality, e.g.                                           *)
(*                                                                           *)
(*    coeffs_of_leq `((1 * x) + (1 * z)) <= (1 + (4 * x) + (10 * y))`  --->  *)
(*    (1, [("x", 3); ("y", 10); ("z", -1)])                                  *)
(*                                                                           *)
(* Assumes that there are no zero coefficients in the argument term. The     *)
(* function also assumes that when a variable has a coefficient of one, it   *)
(* appears in the term as (for example) `1 * x` rather than as `x`.          *)
(*---------------------------------------------------------------------------*)

fun coeffs_of_leq tm =
   (let val (tm1,tm2) = dest_leq tm
        val coeffs1 = negate_coeffs (coeffs_of_arith tm1)
        and coeffs2 = coeffs_of_arith tm2
    in  merge_coeffs coeffs1 coeffs2
    end
   ) handle HOL_ERR _ => failwith "coeffs_of_leq";

(*---------------------------------------------------------------------------*)
(* coeffs_of_leq_set : term -> (int * (string * int) list) list              *)
(*                                                                           *)
(* Obtains coefficients from a set of normalised inequalities.               *)
(* See comments for coeffs_of_leq.                                           *)
(*---------------------------------------------------------------------------*)

fun coeffs_of_leq_set tm =
 map coeffs_of_leq (strip_conj tm) 
     handle HOL_ERR _ => 
 failwith "coeffs_of_leq_set";

(*===========================================================================*)
(* Constructing terms from coefficients and variable names                   *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* build_arith : int * (string * int) list -> term                           *)
(*                                                                           *)
(* Takes an integer and a binding of variable names and coefficients, and    *)
(* returns a linear sum (as a term) with the constant at the head. Terms     *)
(* with a coefficient of zero are eliminated, as is a zero constant. Terms   *)
(* with a coefficient of one are not simplified.                             *)
(*                                                                           *)
(* Examples:                                                                 *)
(*                                                                           *)
(*    (3,[("x",2);("y",1)]) ---> `3 + (2 * x) + (1 * y)`                     *)
(*    (3,[("x",2);("y",0)]) ---> `3 + (2 * x)`                               *)
(*    (0,[("x",2);("y",1)]) ---> `(2 * x) + (1 * y)`                         *)
(*    (0,[("x",0);("y",0)]) ---> `0`                                         *)
(*---------------------------------------------------------------------------*)

val zero_tm = term_of_int zero
fun build_arith (const,bind) = let
  fun build bind =
    if (null bind) then zero_tm
    else let
      val (name,coeff) = Lib.trye hd bind
      and rest = build (Lib.trye tl bind)
    in
      if (coeff = zero) then rest
      else let
        val prod = mk_mult (term_of_int coeff,mk_num_var name)
      in
        if is_zero rest then prod else mk_plus (prod,rest)
      end
    end
in (let
  val c = term_of_int const
  and rest = build bind
in
  if is_zero rest then c
  else if (const = zero) then rest
       else mk_plus (c,rest)
end) handle HOL_ERR _ => failwith "build_arith"
end;

(*---------------------------------------------------------------------------*)
(* build_leq : (int * (string * int) list) -> term                           *)
(*                                                                           *)
(* Constructs a less-than-or-equal-to inequality from a constant and         *)
(* a binding of variable names to coefficients.                              *)
(* See comments for build_arith.                                             *)
(*---------------------------------------------------------------------------*)

fun build_leq coeffs =
   mk_leq (build_arith (lhs_coeffs coeffs),build_arith (rhs_coeffs coeffs));

end
