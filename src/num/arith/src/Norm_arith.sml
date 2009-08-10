(*****************************************************************************)
(* FILE          : norm_arith.sml                                            *)
(* DESCRIPTION   : Functions for normalizing arithmetic terms.               *)
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
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Norm_arith :> Norm_arith =
struct
  open Arbint HolKernel boolLib Rsyntax
       Arith_cons Term_coeffs RJBConv Theorems Thm_convs reduceLib;


  val << = String.<
  infix << ## THENC;
  infixr -->

val num_CONV = Num_conv.num_CONV;

fun failwith function = raise (mk_HOL_ERR "Norm_arith" function "");

(*===========================================================================*)
(* Conversions for normalizing arithmetic                                    *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* COLLECT_NUM_CONSTS_CONV : conv                                            *)
(*                                                                           *)
(* Converts a term of the form `a + (b + (...))` into `c + (...)` where      *)
(* a and b are constants and c is their (constant) sum.                      *)
(*                                                                           *)
(* Also handles `a + b` --> `c`.                                             *)
(*---------------------------------------------------------------------------*)

fun COLLECT_NUM_CONSTS_CONV tm =
 (if ((is_plus tm) andalso (is_num_const (arg1 tm)))
  then if ((is_plus (arg2 tm)) andalso (is_num_const (arg1 (arg2 tm)))) then
          (ADD_ASSOC_CONV THENC (RATOR_CONV (RAND_CONV ADD_CONV))) tm
       else if (is_num_const (arg2 tm)) then ADD_CONV tm
       else failwith "fail"
  else failwith "fail"
 ) handle (Feedback.HOL_ERR _) => failwith "COLLECT_NUM_CONSTS_CONV";

(*---------------------------------------------------------------------------*)
(* NUM_RELN_NORM_CONV : conv -> conv -> conv                                 *)
(*                                                                           *)
(* Converts arithmetic relations and negations of arithmetic relations into  *)
(* conjuncts/disjuncts of less-than-or-equal-to. The arguments of the        *)
(* relation are processed using `arith_conv', and attempts are made to       *)
(* gather together numeric constants. The resulting less-than-or-equal-to    *)
(* inequalities are processed using `leq_conv'.                              *)
(*---------------------------------------------------------------------------*)

fun NUM_RELN_NORM_CONV arith_conv leq_conv tm =
 (if (is_neg tm)
  then (let val tm' = rand tm
        in  ((RAND_CONV (ARGS_CONV arith_conv)) THENC
             (if (is_eq tm') then
                 (NOT_NUM_EQ_NORM_CONV THENC
                  (ARGS_CONV
                    ((RATOR_CONV
                       (RAND_CONV
                         (TRY_CONV COLLECT_NUM_CONSTS_CONV))) THENC
                     leq_conv)))
              else if (is_leq tm') then
                 (NOT_LEQ_NORM_CONV THENC
                  (RATOR_CONV
                    (RAND_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV))) THENC
                  leq_conv)
              else if (is_less tm') then
                 (NOT_LESS_NORM_CONV THENC leq_conv)
              else if (is_great tm') then
                 (NOT_GREAT_NORM_CONV THENC leq_conv)
              else if (is_geq tm') then
                 (NOT_GEQ_NORM_CONV THENC
                  (RATOR_CONV
                    (RAND_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV))) THENC
                  leq_conv)
              else failwith "fail")) tm
        end)
  else ((ARGS_CONV arith_conv) THENC
        (if is_eq tm then (NUM_EQ_NORM_CONV THENC (ARGS_CONV leq_conv)) else
         if is_leq tm then leq_conv else
         if is_less tm then
            (LESS_NORM_CONV THENC
              (RATOR_CONV
                (RAND_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV))) THENC leq_conv)
         else if (is_great tm) then
            (GREAT_NORM_CONV THENC
             (RATOR_CONV
               (RAND_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV))) THENC
             leq_conv)
         else if (is_geq tm) then (GEQ_NORM_CONV THENC leq_conv)
         else failwith "fail")) tm
 ) handle Interrupt => raise Interrupt
       | e as HOL_ERR _ => raise (wrap_exn "Norm_arith" "NUM_RELN_NORM_CONV" e)


(*---------------------------------------------------------------------------*)
(* MULT_CONV : conv                                                          *)
(*                                                                           *)
(* Given a term of the form `a * b` where a and b are constants, returns the *)
(* theorem |- a * b = c where c is the product of a and b.                   *)
(*---------------------------------------------------------------------------*)

val MULT_CONV = reduceLib.MUL_CONV

(*---------------------------------------------------------------------------*)
(* mult_lookup : ((int * int) * thm) list -> (int * int) -> thm              *)
(*                                                                           *)
(* Takes an association list of pairs of integers, and theorems about the    *)
(* simplification of the products of the pairs of integers. The second       *)
(* argument is a pair of integers to be looked up. The integers in the       *)
(* association list should be greater than 1 and the first of each pair      *)
(* should not exceed the second. If the pair of integers specified (or the   *)
(* reverse of them) appear in the list, a theorem about the simplification   *)
(* of their product is returned.                                             *)
(*                                                                           *)
(* Given a list l of the form:                                               *)
(*                                                                           *)
(*    [((2, 3), |- 2 * 3 = 6); ((2, 2), |- 2 * 2 = 4)]                       *)
(*                                                                           *)
(* here are some examples:                                                   *)
(*                                                                           *)
(*    mult_lookup l (2,3)  --->  |- 2 * 3 = 6                                *)
(*    mult_lookup l (3,2)  --->  |- 3 * 2 = 6                                *)
(*    mult_lookup l (3,3)  fails                                             *)
(*---------------------------------------------------------------------------*)

fun mult_lookup ths (n,m) =
 (if (m < n)
  then let val th2 = assoc (m,n) ths
           val tm = mk_mult (term_of_int n,term_of_int m)
           val th1 = MULT_COMM_CONV tm
       in  TRANS th1 th2
       end
  else assoc (n,m) ths
 ) handle (Feedback.HOL_ERR _) => failwith "mult_lookup";

(*---------------------------------------------------------------------------*)
(* FAST_MULT_CONV : conv                                                     *)
(*                                                                           *)
(* Given a term of the form `a * b` where a and b are constants, returns the *)
(* theorem |- a * b = c where c is the product of a and b. A list of         *)
(* previously proved theorems is maintained to speed up the process. Any     *)
(* new theorems that have to be proved are added to the list.                *)
(*---------------------------------------------------------------------------*)

val multiplication_theorems = ref ([]:((int * int) * thm) list);

fun FAST_MULT_CONV tm =
 (let val (a,b) = dest_mult tm
      val aval = int_of_term a
      and bval = int_of_term b
  in  if (aval = zero) then SPEC b ZERO_MULT
      else if (aval = one) then SPEC b ONE_MULT
      else if (bval = zero) then SPEC a MULT_ZERO
      else if (bval = one) then SPEC a MULT_ONE
      else mult_lookup (!multiplication_theorems) (aval,bval) handle _ =>
           (let val th = MULT_CONV tm
            in  if (bval < aval)
                then let val th' = TRANS (MULT_COMM_CONV (mk_mult (b,a))) th
                         val _ =
                            multiplication_theorems :=
                               ((bval,aval),th')::(!multiplication_theorems)
                     in  th
                     end
                else let val _ =
                            multiplication_theorems :=
                               ((aval,bval),th)::(!multiplication_theorems)
                     in  th
                     end
            end)
  end
 ) handle (HOL_ERR _) => failwith "FAST_MULT_CONV";

fun reset_multiplication_theorems () =
   multiplication_theorems := ([]:((int * int) * thm) list);

val multiplication_theorems = fn () => !multiplication_theorems;

(*---------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_SUC_CONV : conv                                           *)
(*                                                                           *)
(* Given a term of the form `SUC x` where x is in sum-of-products form, this *)
(* function converts the whole term to sum-of-products form.                 *)
(*                                                                           *)
(*    SUC const         ---> const'                                          *)
(*    SUC var           ---> 1 + var                                         *)
(*    SUC (const * var) ---> 1 + (const * var)                               *)
(*    SUC (const + exp) ---> const' + exp                                    *)
(*    SUC (exp + const) ---> const' + exp                                    *)
(*    SUC (exp1 + exp2) ---> 1 + (exp1 + exp2)                               *)
(*                                                                           *)
(* where const' is the numeric constant one greater than const.              *)
(*---------------------------------------------------------------------------*)

val num_ty = Arith_cons.num_ty
val plus_tm = numSyntax.plus_tm;

fun SUM_OF_PRODUCTS_SUC_CONV tm =
 let val add1 = term_of_int o (curry (op +) one) o int_of_term
 in
 (if (is_suc tm)
  then let val tm' = rand tm
       in  if (is_num_const tm') then (SYM o num_CONV o add1) tm'
           else if (is_var tm') then SPEC tm' ONE_PLUS
           else if ((is_mult tm') andalso
                    (is_num_const (arg1 tm')) andalso
                    (is_var (arg2 tm')))
                then SPEC tm' ONE_PLUS
           else if (is_plus tm') then
              (let val (a,b) = dest_plus tm'
               in  if (is_num_const a) then
                      (let val th1 = SPEC b (SPEC a SUC_ADD1)
                           and th2 = AP_THM (AP_TERM plus_tm
                                                ((SYM o num_CONV o add1) a)) b
                       in  TRANS th1 th2
                       end)
                   else if (is_num_const b) then
                      (let val th1 = SPEC b (SPEC a SUC_ADD2)
                           and th2 = AP_THM (AP_TERM plus_tm
                                                ((SYM o num_CONV o add1) b)) a
                       in  TRANS th1 th2
                       end)
                   else SPEC tm' ONE_PLUS
               end)
           else failwith "fail"
       end
  else failwith "fail"
 ) handle (Feedback.HOL_ERR _) => failwith "SUM_OF_PRODUCTS_SUC_CONV"
 end;

(*---------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_MULT_CONV : conv                                          *)
(*                                                                           *)
(* Given a term of the form `x * y` where x and y are in sum-of-products     *)
(* form this function converts the whole term to sum-of-products form.       *)
(*                                                                           *)
(*    0 * exp                 ---> 0                                         *)
(*    exp * 0                 ---> 0                                         *)
(*    const1 * const2         ---> const3                                    *)
(*    exp * const             ---> SOPM (const * exp)                        *)
(*    const * var             ---> const * var              (i.e. no change) *)
(*    const1 * (const2 * var) ---> const3 * var                              *)
(*    const * (exp1 + exp2)   ---> SOPM (const * exp1) + SOPM (const * exp2) *)
(*                                                                           *)
(* where const3 is the numeric constant whose value is the product of const1 *)
(* and const2. SOPM denotes a recursive call of SUM_OF_PRODUCTS_MULT_CONV.   *)
(*---------------------------------------------------------------------------*)

fun SUM_OF_PRODUCTS_MULT_CONV tm =
 (if (is_mult tm)
  then (let val (tm1,tm2) = dest_mult tm
        in  if (is_zero tm1) then (SPEC tm2 ZERO_MULT)
            else if (is_zero tm2) then (SPEC tm1 MULT_ZERO)
            else if ((is_num_const tm1) andalso (is_num_const tm2)) then
               FAST_MULT_CONV tm
            else if (is_num_const tm2) then
               (let fun conv _ = SPEC tm2 (SPEC tm1 MULT_COMM)
                in  (conv THENC SUM_OF_PRODUCTS_MULT_CONV) tm
                end)
            else if (is_num_const tm1) then
               (if (is_var tm2) then ALL_CONV tm
                else if ((is_mult tm2) andalso
                         (is_num_const (arg1 tm2)) andalso
                         (is_var (arg2 tm2))) then
                   (MULT_ASSOC_CONV THENC
                    (RATOR_CONV (RAND_CONV FAST_MULT_CONV))) tm
                else if (is_plus tm2) then
                   (LEFT_ADD_DISTRIB_CONV THENC
                    (ARGS_CONV SUM_OF_PRODUCTS_MULT_CONV)) tm
                else failwith "fail")
            else failwith "fail"
        end)
  else failwith "fail"
 ) handle (Feedback.HOL_ERR _) => failwith "SUM_OF_PRODUCTS_MULT_CONV";

(*---------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_CONV : conv                                               *)
(*                                                                           *)
(* Puts an arithmetic expression involving constants, variables, SUC, + and  *)
(* * into sum-of-products form. That is, SUCs are eliminated, and the result *)
(* is an arbitrary tree of sums with products as the leaves. The only        *)
(* `products' allowed are constants, variables and products of a constant    *)
(* and a variable. The conversion fails if the term cannot be put in this    *)
(* form.                                                                     *)
(*---------------------------------------------------------------------------*)

fun SUM_OF_PRODUCTS_CONV tm =
 (if ((is_const tm) orelse (is_var tm) orelse (is_num_const tm)) then
    ALL_CONV tm
  else if (is_suc tm) then
     ((RAND_CONV SUM_OF_PRODUCTS_CONV) THENC SUM_OF_PRODUCTS_SUC_CONV) tm
  else if (is_plus tm) then
     ((ARGS_CONV SUM_OF_PRODUCTS_CONV) THENC
      (fn tm' =>
          let val (tm1,tm2) = dest_plus tm'
          in  if (is_zero tm1) then (SPEC tm2 ZERO_PLUS)
              else if (is_zero tm2) then (SPEC tm1 PLUS_ZERO)
              else if ((is_num_const tm1) andalso (is_num_const tm2)) then
                 (ADD_CONV tm')
              else ALL_CONV tm'
          end)) tm
  else if (is_mult tm) then
     ((ARGS_CONV SUM_OF_PRODUCTS_CONV) THENC SUM_OF_PRODUCTS_MULT_CONV) tm
  else failwith "fail"
 ) handle (Feedback.HOL_ERR _) => failwith "SUM_OF_PRODUCTS_CONV";

(*---------------------------------------------------------------------------*)
(* LINEAR_SUM_CONV : conv                                                    *)
(*                                                                           *)
(* Makes a tree of sums `linear', e.g.                                       *)
(*                                                                           *)
(*    (((a + b) + c) + d) + (e + f) ---> a + (b + (c + (d + (e + f))))       *)
(*---------------------------------------------------------------------------*)

val LINEAR_SUM_CONV =
 let fun FILTER_IN_CONV tm =
        (TRY_CONV (SYM_ADD_ASSOC_CONV THENC (RAND_CONV FILTER_IN_CONV))) tm
     fun LINEAR_SUM_CONV' tm =
        (if (is_plus tm)
         then ((ARGS_CONV LINEAR_SUM_CONV') THENC FILTER_IN_CONV) tm
         else ALL_CONV tm
        ) handle (Feedback.HOL_ERR _) => failwith "LINEAR_SUM_CONV"
 in  LINEAR_SUM_CONV'
 end;

(*---------------------------------------------------------------------------*)
(* GATHER_CONV : conv                                                        *)
(*                                                                           *)
(* Converts `(a * x) + (b * x)` to `(a + b) * x` and simplifies (a + b) if   *)
(* both a and b are constants. Also handles the cases when either or both of *)
(* a and b are missing, e.g. `(a * x) + x`.                                  *)
(*---------------------------------------------------------------------------*)

fun GATHER_CONV tm =
 (let val conv =
         case (is_mult ## is_mult) (dest_plus tm)
         of (true,true)   => GATHER_BOTH_CONV
          | (true,false)  => GATHER_LEFT_CONV
          | (false,true)  => GATHER_RIGHT_CONV
          | (false,false) => GATHER_NEITHER_CONV
  in  (conv THENC (RATOR_CONV (RAND_CONV (TRY_CONV ADD_CONV)))) tm
  end
 ) handle (Feedback.HOL_ERR _) => failwith "GATHER_CONV";

(*---------------------------------------------------------------------------*)
(* IN_LINE_SUM_CONV : conv -> conv                                           *)
(*                                                                           *)
(* Applies a conversion to the top two summands of a line of sums.           *)
(*                                                                           *)
(*    a + (b + ...)  --->  (a + b) + ...  --->  c + ...                      *)
(*                                                                           *)
(* where c is the result of applying `conv' to (a + b). If c is itself a     *)
(* sum, i.e. (c1 + c2) then the following conversion also takes place:       *)
(*                                                                           *)
(*    (c1 + c2) + ...  --->  c1 + (c2 + ...)                                 *)
(*---------------------------------------------------------------------------*)

fun IN_LINE_SUM_CONV conv tm =
 (ADD_ASSOC_CONV THENC
  (RATOR_CONV (RAND_CONV conv)) THENC
  (TRY_CONV SYM_ADD_ASSOC_CONV)) tm
 handle (Feedback.HOL_ERR _) => failwith "IN_LINE_SUM_CONV";

(*---------------------------------------------------------------------------*)
(* ONE_PASS_SORT_CONV : conv                                                 *)
(*                                                                           *)
(* Single pass of sort and gather for a linear sum of products.              *)
(*                                                                           *)
(* Operations on adjacent summands:                                          *)
(*                                                                           *)
(*    const1 + const2                   ---> const3                          *)
(*    const + exp                       ---> const + exp    (i.e. no change) *)
(*    exp + const                       ---> const + exp                     *)
(*                                                                           *)
(*    (const1 * var) + (const2 * var)   }                                    *)
(*    (const1 * var) + var              } GATHER                             *)
(*    var + (const2 * var)              }                                    *)
(*    var + var                         }                                    *)
(*                                                                           *)
(*    (const1 * var1) + (const2 * var2) }                                    *)
(*    (const1 * var1) + var2            } ADD_SYM if var2 lexicographically  *)
(*    var1 + (const2 * var2)            }         less than var1             *)
(*    var1 + var2                       }                                    *)
(*                                                                           *)
(* where const3 is the numeric constant whose value is the sum of const1 and *)
(* const2.                                                                   *)
(*---------------------------------------------------------------------------*)

fun ONE_PASS_SORT_CONV tm =
 (if (is_plus tm)
  then ((RAND_CONV ONE_PASS_SORT_CONV) THENC
        (fn tm' =>
          let val (tm1,tm2) = dest_plus tm'
          in  if (is_plus tm2) then
                 (let val tm2' = arg1 tm2
                  in  if ((is_num_const tm1) andalso (is_num_const tm2')) then
                         IN_LINE_SUM_CONV ADD_CONV tm'
                      else if (is_num_const tm1) then ALL_CONV tm'
                      else if (is_num_const tm2') then
                         IN_LINE_SUM_CONV ADD_SYM_CONV tm'
                      else let val name1 = var_of_prod tm1
                               and name2 = var_of_prod tm2'
                           in  if (name1 = name2) then
                                  IN_LINE_SUM_CONV GATHER_CONV tm'
                               else if (name2 << name1) then
                                  IN_LINE_SUM_CONV ADD_SYM_CONV tm'
                               else ALL_CONV tm'
                           end
                  end)
              else if ((is_num_const tm1) andalso (is_num_const tm2)) then ADD_CONV tm'
              else if (is_num_const tm1) then ALL_CONV tm'
              else if (is_num_const tm2) then ADD_SYM_CONV tm'
              else let val name1 = var_of_prod tm1
                       and name2 = var_of_prod tm2
                   in  if (name1 = name2) then GATHER_CONV tm'
                       else if (name2 << name1) then ADD_SYM_CONV tm'
                       else ALL_CONV tm'
                   end
          end)) tm
  else ALL_CONV tm
 ) handle (Feedback.HOL_ERR _) => failwith "ONE_PASS_SORT_CONV";

(*---------------------------------------------------------------------------*)
(* SORT_AND_GATHER_CONV : conv                                               *)
(*                                                                           *)
(* Sort and gather for a linear sum of products. Constants are moved to the  *)
(* front of the sum and variable terms are sorted lexicographically, e.g.    *)
(*                                                                           *)
(*    x + (y + (1 + ((9 * y) + (3 * x))))  --->  1 + ((4 * x) + (10 * y))    *)
(*---------------------------------------------------------------------------*)

fun SORT_AND_GATHER_CONV tm =
 REPEATC (CHANGED_CONV ONE_PASS_SORT_CONV) tm
 handle (Feedback.HOL_ERR _) => failwith "SORT_AND_GATHER_CONV";

(*---------------------------------------------------------------------------*)
(* SYM_ONE_MULT_VAR_CONV : conv                                              *)
(*                                                                           *)
(* If the argument term is a numeric variable, say `x`, then this conversion *)
(* returns the theorem |- x = 1 * x.                                         *)
(*---------------------------------------------------------------------------*)

fun SYM_ONE_MULT_VAR_CONV tm =
 (if (is_var tm)
  then SYM_ONE_MULT_CONV tm
  else failwith "fail"
 ) handle (Feedback.HOL_ERR _) => failwith "SYM_ONE_MULT_VAR_CONV";

(*---------------------------------------------------------------------------*)
(* NORM_ZERO_AND_ONE_CONV : conv                                             *)
(*                                                                           *)
(* Performs the following transformations on a linear sum of products:       *)
(*                                                                           *)
(*    ... (0 * x)          --->  ... 0                                       *)
(*    ... + (0 * x) + ...  --->  ... + ...                                   *)
(*                                                                           *)
(*    ... x                --->  ... (1 * x)                                 *)
(*    ... + x + ...        --->  ... + (1 * x) + ...                         *)
(*                                                                           *)
(*    ... + exp + 0        --->  ... + exp                                   *)
(*                                                                           *)
(* And at top-level only:                                                    *)
(*                                                                           *)
(*    0 + exp              --->  exp                                         *)
(*---------------------------------------------------------------------------*)

val NORM_ZERO_AND_ONE_CONV =
 let fun NORM_CONV tm =
        if (is_plus tm) then
           ((RAND_CONV NORM_CONV) THENC
            (RATOR_CONV (RAND_CONV (TRY_CONV SYM_ONE_MULT_VAR_CONV))) THENC
            (TRY_CONV ZERO_MULT_PLUS_CONV) THENC
            (TRY_CONV PLUS_ZERO_CONV)) tm
        else ((TRY_CONV ZERO_MULT_CONV) THENC
              (TRY_CONV SYM_ONE_MULT_VAR_CONV)) tm
 in  fn tm => ((NORM_CONV THENC (TRY_CONV ZERO_PLUS_CONV)) tm
             handle (Feedback.HOL_ERR _) => failwith "NORM_ZERO_AND_ONE_CONV")
 end;

end
