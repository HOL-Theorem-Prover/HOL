(****************************************************************************)
(* FILE          : ineq_coeffs.sml                                          *)
(* DESCRIPTION   : Functions for converting between arithmetic inequalities *)
(*                 and their representation as lists of variable names and  *)
(*                 coefficients.                                            *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 4th March 1991                                           *)
(*                                                                          *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 5th February 1993                                        *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 21st August 1996                                         *)
(****************************************************************************)

structure NumInequalityCoeffs :> NumInequalityCoeffs =
struct

open Exception Lib Term Dsyntax;
infix ##;

type term = Term.term;
type num = NumType.num;
val num0 = NumType.num0;

fun failwith function = raise
 HOL_ERR{origin_structure = "InequalityCoeffsFun",
         origin_function = function,
                 message = ""};


local

open Rsyntax NumType NumArithCons NumHOLType

in

val zero = term_of_num num0

(*--------------------------------------------------------------------------*)
(* Datatype for the different equality and inequality relations used in     *)
(* linear arithmetic.                                                       *)
(*--------------------------------------------------------------------------*)

datatype inequality_relation = Eq | Leq | Less;

(*--------------------------------------------------------------------------*)
(* dest_ineq : term -> inequality_relation * (term * term)                  *)
(*                                                                          *)
(* Breaks up a term that is an application of =, <= or < into the type of   *)
(* the relation and the two arguments.                                      *)
(*--------------------------------------------------------------------------*)

fun dest_ineq tm =
   (Eq,Psyntax.dest_eq tm) handle HOL_ERR _ =>
   (Leq,dest_leq tm) handle HOL_ERR _ =>
   (Less,dest_less tm) handle HOL_ERR _ =>
   failwith "dest_ineq";

(*--------------------------------------------------------------------------*)
(* mk_ineq : inequality_relation -> (term * term) -> term                   *)
(*                                                                          *)
(* Constructs an application of =, <= or < from two arguments.              *)
(*--------------------------------------------------------------------------*)

fun mk_ineq Eq = Psyntax.mk_eq
  | mk_ineq Leq = mk_leq
  | mk_ineq Less = mk_less;

(*==========================================================================*)
(* Manipulating coefficient representations of arithmetic expressions       *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* coeff_of_const : (num * (string * num) list) -> num                      *)
(*--------------------------------------------------------------------------*)

fun coeff_of_const (n,_) = n;

(*--------------------------------------------------------------------------*)
(* coeffs_of_vars : (num * (string * num) list) -> (string * num) list      *)
(*--------------------------------------------------------------------------*)

fun coeffs_of_vars (_,vcoeffs) = vcoeffs;

(*--------------------------------------------------------------------------*)
(* coeff_of_var : string -> (num * (string * num) list) -> num              *)
(*--------------------------------------------------------------------------*)

fun coeff_of_var var (_,vcoeffs) =
    assoc var vcoeffs handle HOL_ERR _ => (num0:num);

(*--------------------------------------------------------------------------*)
(* var_on_left     : string -> (num * (string * num) list) -> bool          *)
(* var_on_right    : string -> (num * (string * num) list) -> bool          *)
(* var_not_present : string -> (num * (string * num) list) -> bool          *)
(*--------------------------------------------------------------------------*)

fun var_on_left var coeffs = (coeff_of_var var coeffs < (num0:num))
fun var_on_right var coeffs = (num0:num) < (coeff_of_var var coeffs)
fun var_not_present var coeffs = (coeff_of_var var coeffs =  num0);

(*--------------------------------------------------------------------------*)
(* scale_coeffs : num ->                                                    *)
(*                (num * (string * num) list) ->                            *)
(*                (num * (string * num) list)                               *)
(*--------------------------------------------------------------------------*)

fun scale_coeffs n (const,vcoeffs) =
   (const * n,map (fn (name,coeff) => (name,coeff * n)) vcoeffs);

(*--------------------------------------------------------------------------*)
(* negate_coeffs : (num * (string * num) list) ->                           *)
(*                 (num * (string * num) list)                              *)
(*                                                                          *)
(* Negates constant value and coefficients of variables in a binding.       *)
(*--------------------------------------------------------------------------*)

fun negate_coeffs x = scale_coeffs (num0 - num1) x;

(*--------------------------------------------------------------------------*)
(* merge_coeffs : (num * (string * num) list) ->                            *)
(*                (num * (string * num) list) ->                            *)
(*                (num * (string * num) list)                               *)
(*                                                                          *)
(* Sums constant values and merges bindings by adding coefficients of any   *)
(* variable that appears in both bindings. If the sum of the coefficients   *)
(* is zero, the variable concerned is not entered in the new binding.       *)
(*--------------------------------------------------------------------------*)

fun merge_coeffs coeffs1 coeffs2 =
   let fun merge vcoeffs1 vcoeffs2 =
          if (null vcoeffs1) then vcoeffs2
          else if (null vcoeffs2) then vcoeffs1
          else (let val (name1:string,coeff1) = hd vcoeffs1
                    and (name2,coeff2) = hd vcoeffs2
                in  if (name1 = name2)
                    then if ((coeff1 + coeff2) = num0)
                         then merge (tl vcoeffs1) (tl vcoeffs2)
                         else (name1,(coeff1 + coeff2))::
                                 (merge (tl vcoeffs1) (tl vcoeffs2))
                    else if (Portable_String.< (name1,name2))
                         then (name1,coeff1)::(merge (tl vcoeffs1) vcoeffs2)
                         else (name2,coeff2)::(merge vcoeffs1 (tl vcoeffs2))
                end)
       val (const1,vcoeffs1) = coeffs1
       and (const2,vcoeffs2) = coeffs2
   in  ((const1 + const2:num),merge vcoeffs1 vcoeffs2)
   end;

(*--------------------------------------------------------------------------*)
(* lhs_coeffs : (num * (string * num) list) -> (num * (string * num) list)  *)
(*                                                                          *)
(* Extract strictly negative coefficients and negate them.                  *)
(*--------------------------------------------------------------------------*)

fun lhs_coeffs p =
   let fun f n = if (n < (num0:num)) then (num0 - n) else num0
       fun g (s,n) =
          if (n < num0) then (s,(num0 - n)) else failwith "lhs_coeffs"
   in  (f ## (mapfilter g)) p
   end;

(*--------------------------------------------------------------------------*)
(* rhs_coeffs : (num * (string * num) list) -> (num * (string * num) list)  *)
(*                                                                          *)
(* Extract strictly positive coefficients.                                  *)
(*--------------------------------------------------------------------------*)

fun rhs_coeffs p =
   let fun f n = if ((num0:num) < n) then n else num0
   in  (f ## (filter (fn (_,n) => num0 < n))) p
   end;

(*--------------------------------------------------------------------------*)
(* diff_of_coeffs :                                                         *)
(*    ((num * (string * num) list) * (num * (string * num) list)) ->        *)
(*    ((num * (string * num) list) * (num * (string * num) list))           *)
(*                                                                          *)
(* Given the coefficients representing two inequalities, this function      *)
(* computes the terms (as coefficients) that have to be added to each in    *)
(* order to make the right-hand side of the first equal to the left-hand    *)
(* side of the second.                                                      *)
(*--------------------------------------------------------------------------*)

fun diff_of_coeffs (coeffs1,coeffs2) =
   let val coeffs1' = rhs_coeffs coeffs1
       and coeffs2' = lhs_coeffs coeffs2
       val coeffs = merge_coeffs (negate_coeffs coeffs1') coeffs2'
   in  (rhs_coeffs coeffs,lhs_coeffs coeffs)
   end;

(*--------------------------------------------------------------------------*)
(* vars_of_coeffs : (num * (string * num) list) list -> string list         *)
(*                                                                          *)
(* Obtain a list of variable names from a set of coefficient lists.         *)
(*--------------------------------------------------------------------------*)

fun vars_of_coeffs coeffsl = mk_set (flatten (map ((map fst) o snd) coeffsl));

(*==========================================================================*)
(* Extracting coefficients and variable names from normalized terms         *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* var_of_prod : term -> string                                             *)
(*                                                                          *)
(* Returns variable name from terms of the form "var" and "const * var".    *)
(*--------------------------------------------------------------------------*)

fun var_of_prod tm =
   (#Name (dest_var tm)) handle HOL_ERR _ =>
   (#Name (dest_var (rand tm))) handle HOL_ERR _ =>
   failwith "var_of_prod";

(*--------------------------------------------------------------------------*)
(* coeffs_of_arith : term -> (num * (string * num) list)                    *)
(*                                                                          *)
(* Takes an arithmetic term that has been sorted and returns the constant   *)
(* value and a binding of variable names to their coefficients, e.g.        *)
(*                                                                          *)
(*    coeffs_of_arith `1 + (4 * x) + (10 * y)`  --->                        *)
(*    (1, [("x", 4); ("y", 10)])                                            *)
(*                                                                          *)
(* Assumes that there are no zero coefficients in the argument term.        *)
(*--------------------------------------------------------------------------*)

fun coeffs_of_arith tm =
   let fun coeff tm = (num_of_term o rand o rator) tm handle HOL_ERR _ => num1
       fun coeffs tm =
          (let val (prod,rest) = dest_plus tm
           in  (var_of_prod prod,coeff prod)::(coeffs rest)
           end
          ) handle HOL_ERR _ => [(var_of_prod tm,coeff tm)]
   in  (let val (const,rest) = dest_plus tm
        in  (num_of_term const,coeffs rest)
        end)
       handle HOL_ERR _ => (num_of_term tm,[])
       handle HOL_ERR _ => ((num0:num),coeffs tm)
       handle HOL_ERR _ => failwith "coeffs_of_arith"
   end;

(*--------------------------------------------------------------------------*)
(* coeffs_of_ineq :                                                         *)
(*    term -> inequality_relation * (num * (string * num) list)             *)
(*                                                                          *)
(* Takes an equality or inequality between two arithmetic terms that have   *)
(* been sorted and returns the relation, the constant value and a binding   *)
(* of variable names to their coefficients for the equivalent term with     *)
(* zero on the LHS, e.g.                                                    *)
(*                                                                          *)
(*    coeffs_of_ineq `(x + z) <= (1 + (4 * x) + (10 * y))`  --->            *)
(*    (Leq,(1, [("x", 3); ("y", 10); ("z", -1)]))                           *)
(*                                                                          *)
(* Assumes that there are no zero coefficients in the argument term.        *)
(*--------------------------------------------------------------------------*)

fun coeffs_of_ineq tm =
   (let val (R,(tm1,tm2)) = dest_ineq tm
        val coeffs1 = negate_coeffs (coeffs_of_arith tm1)
        and coeffs2 = coeffs_of_arith tm2
    in  (R,merge_coeffs coeffs1 coeffs2)
    end
   ) handle HOL_ERR _ => failwith "coeffs_of_ineq";

(*--------------------------------------------------------------------------*)
(* coeffs_of_ineq_set :                                                     *)
(*    term -> (inequality_relation * (num * (string * num) list)) list      *)
(*                                                                          *)
(* Obtains coefficients from a set of normalised inequalities.              *)
(* See comments for coeffs_of_ineq.                                         *)
(*--------------------------------------------------------------------------*)

fun coeffs_of_ineq_set tm =
   map coeffs_of_ineq (strip_conj tm)
   handle HOL_ERR _ => failwith "coeffs_of_ineq_set";

(*--------------------------------------------------------------------------*)
(* coeffs_of_goal : (term list * term) ->                                   *)
(*                  inequality_relation * (num * (string * num) list)       *)
(*--------------------------------------------------------------------------*)

fun coeffs_of_goal (_,tm) = coeffs_of_ineq tm;

(*==========================================================================*)
(* Constructing terms from coefficients and variable names                  *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* arith_of_coeffs : num * (string * num) list -> term                      *)
(*                                                                          *)
(* Takes an number and a binding of variable names and coefficients, and    *)
(* returns a linear sum (as a term) with the constant at the head. Terms    *)
(* with a coefficient of zero are eliminated, as is a zero constant. Terms  *)
(* with a coefficient of one are simplified.                                *)
(*                                                                          *)
(* Examples:                                                                *)
(*                                                                          *)
(*    (3,[("x",2);("y",1)]) ---> `3 + (2 * x) + y`                          *)
(*    (3,[("x",2);("y",0)]) ---> `3 + (2 * x)`                              *)
(*    (0,[("x",2);("y",1)]) ---> `(2 * x) + y`                              *)
(*    (0,[("x",0);("y",0)]) ---> `0`                                        *)
(*--------------------------------------------------------------------------*)

fun arith_of_coeffs (const,vcoeffs) =
   let fun build vcoeffs =
          if (null vcoeffs)
          then zero
          else let val (name,coeff) = hd vcoeffs
                   and rest = build (tl vcoeffs)
               in  if (coeff = (num0:num))
                   then rest
                   else let val prod =
                               if (coeff = num1)
                               then mk_num_var name
                               else mk_mult (term_of_num coeff,mk_num_var name)
                        in  if (rest = zero)
                            then prod
                            else mk_plus (prod,rest)
                        end
               end
   in (let val c = term_of_num const
           and rest = build vcoeffs
       in  if (rest = zero) then c
           else if (const = (num0:num)) then rest
           else mk_plus (c,rest)
       end
      ) handle HOL_ERR _ => failwith "arith_of_coeffs"
   end;

(*--------------------------------------------------------------------------*)
(* ineq_of_coeffs :                                                         *)
(*    inequality_relation * (num * (string * num) list) -> term             *)
(*                                                                          *)
(* Constructs an equality or inequality from a relation, a constant and a   *)
(* binding of variable names to coefficients.                               *)
(* See comments for arith_of_coeffs.                                        *)
(*--------------------------------------------------------------------------*)

fun ineq_of_coeffs (R,coeffs) =
   mk_ineq R (arith_of_coeffs (lhs_coeffs coeffs),
              arith_of_coeffs (rhs_coeffs coeffs));

end;

end; (* InequalityCoeffsFun *)
