(****************************************************************************)
(* FILE          : NumArith.sml                                             *)
(* DESCRIPTION   : Functions for normalizing and solving linear arithmetic  *)
(*                 formulas.                                                *)
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

structure NumArith :> NumArith =
struct

open Exception;

val dense = false;

fun failwith function = raise
    HOL_ERR{origin_structure = "NumArith",
            origin_function = function, message = ""};

open HolKernel Parse boolTheory Drule Conv Num_conv;
open Psyntax DecisionConv DecisionSupport
open NumArithCons NumHOLType NumInequalityCoeffs NumType
open DecisionTheorems DecisionArithConvs DecisionNormConvs
infix THENC ##;

type term  = Term.term
type thm   = Thm.thm
type num   = NumType.num;
type coeffs = num * (string * num) list;


(*==========================================================================*)
(* Conversions for normalizing arithmetic                                   *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* ADD_CONV : conv                                                          *)
(*                                                                          *)
(* Given a term of the form `a + b` where a and b are constants, returns    *)
(* the theorem |- a + b = c where c is the sum of a and b.                  *)
(*                                                                          *)
(* NOTE: iterative version.                                                 *)
(*--------------------------------------------------------------------------*)

fun ADD_CONV tm = reduceLib.ADD_CONV tm
  handle (HOL_ERR _) => failwith "ADD_CONV"

(*--------------------------------------------------------------------------*)
(* COLLECT_NUM_CONSTS_CONV : conv                                           *)
(*                                                                          *)
(* Converts a term of the form `a + (b + (...))` into `c + (...)` where     *)
(* a and b are constants and c is their (constant) sum.                     *)
(*                                                                          *)
(* Also handles `a + b` --> `c`.                                            *)
(*--------------------------------------------------------------------------*)

fun COLLECT_NUM_CONSTS_CONV tm =
   (if ((is_plus tm) andalso (is_num_const (arg1 tm)))
    then if ((is_plus (arg2 tm)) andalso (is_num_const (arg1 (arg2 tm)))) then
            (ADD_ASSOC_CONV THENC LEFT_CONV ADD_CONV) tm
         else if (is_num_const (arg2 tm)) then ADD_CONV tm
         else failwith ""
    else failwith ""
   ) handle (HOL_ERR _) => failwith "COLLECT_NUM_CONSTS_CONV";

(*--------------------------------------------------------------------------*)
(* NUM_RELN_NORM_CONV : conv -> conv -> conv                                *)
(*                                                                          *)
(* Converts arithmetic relations and negations of arithmetic relations into *)
(* disjuncts of applications of the =, <= and < relations. The arguments of *)
(* the relation are processed using `arith_conv'. The resulting equalities  *)
(* and inequalities are processed using `ineq_conv'.                        *)
(*--------------------------------------------------------------------------*)

fun NUM_RELN_NORM_CONV arith_conv ineq_conv tm =
   (if (is_neg tm)
    then (let val tm' = rand tm
          in  ((RAND_CONV (BINOP_CONV arith_conv)) THENC
               (if (is_eq tm') then
                   NOT_NUM_EQ_NORM_CONV THENC
                   (BINOP_CONV
                      (if dense
                       then ineq_conv
                       else LEFT_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV) THENC
                            ineq_conv))
                else if (is_leq tm') then
                   NOT_LEQ_NORM_CONV THENC
                   (if dense
                    then ineq_conv
                    else LEFT_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV) THENC
                         ineq_conv)
                else if (is_less tm') then NOT_LESS_NORM_CONV THENC ineq_conv
                else if (is_great tm') then NOT_GREAT_NORM_CONV THENC ineq_conv
                else if (is_geq tm') then
                   NOT_GEQ_NORM_CONV THENC
                   (if dense
                    then ineq_conv
                    else LEFT_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV) THENC
                         ineq_conv)
                else failwith "")) tm
          end)
    else (BINOP_CONV arith_conv THENC
          (if not dense andalso (is_less tm) then
              LESS_NORM_CONV THENC LEFT_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV)
           else if (is_great tm) then
              if dense
              then GREAT_NORM_CONV
              else GREAT_NORM_CONV THENC
                   LEFT_CONV (TRY_CONV COLLECT_NUM_CONSTS_CONV)
           else if (is_geq tm) then GEQ_NORM_CONV
           else ALL_CONV) THENC
          ineq_conv) tm
   ) handle (HOL_ERR _) => failwith "NUM_RELN_NORM_CONV";

(*--------------------------------------------------------------------------*)
(* MULT_CONV : conv                                                         *)
(*                                                                          *)
(* Given a term of the form `a * b` where a and b are constants, returns    *)
(* the theorem |- a * b = c where c is the product of a and b.              *)
(*--------------------------------------------------------------------------*)

fun MULT_CONV tm = (reduceLib.MUL_CONV tm)
  handle (HOL_ERR _) => failwith "MULT_CONV";

(*--------------------------------------------------------------------------*)
(* mult_lookup : ((num * num) * thm) list -> (num * num) -> thm             *)
(*                                                                          *)
(* Takes an association list of pairs of numbers, and theorems about the    *)
(* simplification of the products of the pairs of numbers. The second       *)
(* argument is a pair of numbers to be looked up. The numbers in the        *)
(* association list should be greater than 1 and the first of each pair     *)
(* should not exceed the second. If the pair of numbers specified (or the   *)
(* reverse of them) appear in the list, a theorem about the simplification  *)
(* of their product is returned.                                            *)
(*                                                                          *)
(* Given a list l of the form:                                              *)
(*                                                                          *)
(*    [((2, 3), |- 2 * 3 = 6); ((2, 2), |- 2 * 2 = 4)]                      *)
(*                                                                          *)
(* here are some examples:                                                  *)
(*                                                                          *)
(*    mult_lookup l (2,3)  -->  |- 2 * 3 = 6                                *)
(*    mult_lookup l (3,2)  -->  |- 3 * 2 = 6                                *)
(*    mult_lookup l (3,3)  fails                                            *)
(*--------------------------------------------------------------------------*)

fun mult_lookup ths (n,m) =
   (if (m < n)
    then let val th2 = assoc (m,n) ths
             val tm = mk_mult (term_of_num n,term_of_num m)
             val th1 = MULT_COMM_CONV tm
         in  TRANS th1 th2
         end
    else assoc (n,m) ths
   ) handle (HOL_ERR _) => failwith "mult_lookup";

(*--------------------------------------------------------------------------*)
(* FAST_MULT_CONV : conv                                                    *)
(*                                                                          *)
(* Given a term of the form `a * b` where a and b are constants, returns    *)
(* the theorem |- a * b = c where c is the product of a and b. A list of    *)
(* previously proved theorems is maintained to speed up the process. Any    *)
(* new theorems that have to be proved are added to the list.               *)
(*--------------------------------------------------------------------------*)

val multiplication_theorems = ref ([]:((num * num) * thm) list);

fun FAST_MULT_CONV tm =
   (let val (a,b) = dest_mult tm
        val aval = num_of_term a
        and bval = num_of_term b
    in  if (aval = num0) then SPEC b ZERO_MULT
        else if (aval = num1) then SPEC b ONE_MULT
        else if (bval = num0) then SPEC a MULT_ZERO
        else if (bval = num1) then SPEC a MULT_ONE
        else mult_lookup (!multiplication_theorems) (aval,bval)
             handle HOL_ERR _ =>
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
   multiplication_theorems := ([]:((num * num) * thm) list);

val multiplication_theorems = fn () => !multiplication_theorems;

(*--------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_SUC_CONV : conv                                          *)
(*                                                                          *)
(* Given a term of the form `SUC x` where x is in sum-of-products form,     *)
(* this function converts the whole term to sum-of-products form.           *)
(*                                                                          *)
(*    SUC const         --> const'                                          *)
(*    SUC var           --> 1 + var                                         *)
(*    SUC (const * var) --> 1 + (const * var)                               *)
(*    SUC (const + exp) --> const' + exp                                    *)
(*    SUC (exp + const) --> const' + exp                                    *)
(*    SUC (exp1 + exp2) --> 1 + (exp1 + exp2)                               *)
(*                                                                          *)
(* where const' is the numeric constant one greater than const.             *)
(*--------------------------------------------------------------------------*)

fun SUM_OF_PRODUCTS_SUC_CONV tm =
 let val add1 = term_of_num o (curry (op +) num1) o num_of_term
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
                      (let val th1 = SPECL [a,b] SUC_ADD1
                           and th2 = AP_THM (AP_TERM (--`$+`--)
                                                ((SYM o num_CONV o add1) a)) b
                       in  TRANS th1 th2
                       end)
                   else if (is_num_const b) then
                      (let val th1 = SPECL [a,b] SUC_ADD2
                           and th2 = AP_THM (AP_TERM (--`$+`--)
                                                ((SYM o num_CONV o add1) b)) a
                       in  TRANS th1 th2
                       end)
                   else SPEC tm' ONE_PLUS
               end)
           else failwith ""
       end
  else failwith ""
 ) handle (HOL_ERR _) => failwith "SUM_OF_PRODUCTS_SUC_CONV"
 end;

(*--------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_MULT_CONV : conv                                         *)
(*                                                                          *)
(* Given a term of the form `x * y` where x and y are in sum-of-products    *)
(* form this function converts the whole term to sum-of-products form.      *)
(*                                                                          *)
(*    0 * exp                 --> 0                                         *)
(*    exp * 0                 --> 0                                         *)
(*    const1 * const2         --> const3                                    *)
(*    exp * const             --> SOPM (const * exp)                        *)
(*    const * var             --> const * var              (i.e. no change) *)
(*    const1 * (const2 * var) --> const3 * var                              *)
(*    const * (exp1 + exp2)   --> SOPM (const * exp1) + SOPM (const * exp2) *)
(*                                                                          *)
(* where const3 is the numeric constant whose value is the product of       *)
(* const1 and const2. SOPM denotes a recursive call of                      *)
(* SUM_OF_PRODUCTS_MULT_CONV.                                               *)
(*--------------------------------------------------------------------------*)

fun SUM_OF_PRODUCTS_MULT_CONV tm =
   (if (is_mult tm)
    then (let val (tm1,tm2) = dest_mult tm
          in  if (is_zero tm1) then (SPEC tm2 ZERO_MULT)
              else if (is_zero tm2) then (SPEC tm1 MULT_ZERO)
              else if ((is_num_const tm1) andalso (is_num_const tm2)) then
                 FAST_MULT_CONV tm
              else if (is_num_const tm2) then
                 (let fun conv _ = SPECL [tm1,tm2] MULT_COMM
                  in  (conv THENC SUM_OF_PRODUCTS_MULT_CONV) tm
                  end)
              else if (is_num_const tm1) then
                 (if (is_var tm2) then ALL_CONV tm
                  else if ((is_mult tm2) andalso
                           (is_num_const (arg1 tm2)) andalso
                           (is_var (arg2 tm2))) then
                     (MULT_ASSOC_CONV THENC LEFT_CONV FAST_MULT_CONV) tm
                  else if (is_plus tm2) then
                     (LEFT_ADD_DISTRIB_CONV THENC
                      (BINOP_CONV SUM_OF_PRODUCTS_MULT_CONV)) tm
                  else failwith "")
              else failwith ""
          end)
    else failwith ""
   ) handle (HOL_ERR _) => failwith "SUM_OF_PRODUCTS_MULT_CONV";

(*--------------------------------------------------------------------------*)
(* SUM_OF_PRODUCTS_CONV : conv                                              *)
(*                                                                          *)
(* Puts an arithmetic expression involving constants, variables, SUC, + and *)
(* * into sum-of-products form. That is, SUCs are eliminated, and the       *)
(* result is an arbitrary tree of sums with products as the leaves. The     *)
(* only `products' allowed are constants, variables and products of a       *)
(* constant and a variable. The conversion fails if the term cannot be put  *)
(* in this form.                                                            *)
(*--------------------------------------------------------------------------*)

fun SUM_OF_PRODUCTS_CONV tm =
   (if ((is_const tm) orelse (is_var tm) orelse (is_num_const tm)) then
      ALL_CONV tm
    else if (is_suc tm) then
       (RAND_CONV SUM_OF_PRODUCTS_CONV THENC SUM_OF_PRODUCTS_SUC_CONV) tm
    else if (is_plus tm) then
       (BINOP_CONV SUM_OF_PRODUCTS_CONV THENC
        (fn tm' =>
            let val (tm1,tm2) = dest_plus tm'
            in  if (is_zero tm1) then (SPEC tm2 ZERO_PLUS)
                else if (is_zero tm2) then (SPEC tm1 PLUS_ZERO)
                else if ((is_num_const tm1) andalso (is_num_const tm2)) then
                   (ADD_CONV tm')
                else ALL_CONV tm'
            end)) tm
    else if (is_mult tm) then
       ((BINOP_CONV SUM_OF_PRODUCTS_CONV) THENC SUM_OF_PRODUCTS_MULT_CONV) tm
    else failwith ""
   ) handle (HOL_ERR _) => failwith "SUM_OF_PRODUCTS_CONV";

(*--------------------------------------------------------------------------*)
(* LINEAR_SUM_CONV : conv                                                   *)
(*                                                                          *)
(* Makes a tree of sums `linear', e.g.                                      *)
(*                                                                          *)
(*    (((a + b) + c) + d) + (e + f) --> a + (b + (c + (d + (e + f))))       *)
(*--------------------------------------------------------------------------*)

val LINEAR_SUM_CONV =
   let fun FILTER_IN_CONV tm =
          (TRY_CONV (SYM_ADD_ASSOC_CONV THENC (RIGHT_CONV FILTER_IN_CONV))) tm
       fun LINEAR_SUM_CONV' tm =
          (if (is_plus tm)
           then ((BINOP_CONV LINEAR_SUM_CONV') THENC FILTER_IN_CONV) tm
           else ALL_CONV tm
          ) handle (HOL_ERR _) => failwith "LINEAR_SUM_CONV"
   in  LINEAR_SUM_CONV'
   end;

(*--------------------------------------------------------------------------*)
(* GATHER_CONV : conv                                                       *)
(*                                                                          *)
(* Converts `(a * x) + (b * x)` to `(a + b) * x` and simplifies (a + b) if  *)
(* both a and b are constants. Also handles the cases when either or both   *)
(* of a and b are missing, e.g. `(a * x) + x`.                              *)
(*--------------------------------------------------------------------------*)

fun GATHER_CONV tm =
   let val conv =
          case (is_mult ## is_mult) (dest_plus tm)
          of (true,true)   => GATHER_BOTH_CONV
           | (true,false)  => GATHER_LEFT_CONV
           | (false,true)  => GATHER_RIGHT_CONV
           | (false,false) => GATHER_NEITHER_CONV
   in  (conv THENC LEFT_CONV (TRY_CONV ADD_CONV)) tm
   end
   handle (HOL_ERR _) => failwith "GATHER_CONV";

(*--------------------------------------------------------------------------*)
(* IN_LINE_SUM_CONV : conv -> conv                                          *)
(*                                                                          *)
(* Applies a conversion to the top two summands of a line of sums.          *)
(*                                                                          *)
(*    a + (b + ...)  -->  (a + b) + ...  -->  c + ...                       *)
(*                                                                          *)
(* where c is the result of applying `conv' to (a + b). If c is itself a    *)
(* sum, i.e. (c1 + c2) then the following conversion also takes place:      *)
(*                                                                          *)
(*    (c1 + c2) + ...  -->  c1 + (c2 + ...)                                 *)
(*--------------------------------------------------------------------------*)

fun IN_LINE_SUM_CONV conv tm =
   (ADD_ASSOC_CONV THENC LEFT_CONV conv THENC TRY_CONV SYM_ADD_ASSOC_CONV) tm
   handle (HOL_ERR _) => failwith "IN_LINE_SUM_CONV";

(*--------------------------------------------------------------------------*)
(* ONE_PASS_SORT_CONV : conv                                                *)
(*                                                                          *)
(* Single pass of sort and gather for a linear sum of products.             *)
(*                                                                          *)
(* Operations on adjacent summands:                                         *)
(*                                                                          *)
(*    const1 + const2                   --> const3                          *)
(*    const + exp                       --> const + exp    (i.e. no change) *)
(*    exp + const                       --> const + exp                     *)
(*                                                                          *)
(*    (const1 * var) + (const2 * var)   }                                   *)
(*    (const1 * var) + var              } GATHER                            *)
(*    var + (const2 * var)              }                                   *)
(*    var + var                         }                                   *)
(*                                                                          *)
(*    (const1 * var1) + (const2 * var2) }                                   *)
(*    (const1 * var1) + var2            } ADD_SYM if var2 lexicographically *)
(*    var1 + (const2 * var2)            }         less than var1            *)
(*    var1 + var2                       }                                   *)
(*                                                                          *)
(* where const3 is the numeric constant whose value is the sum of const1    *)
(* and const2.                                                              *)
(*--------------------------------------------------------------------------*)

fun ONE_PASS_SORT_CONV tm =
   (if (is_plus tm)
    then (RIGHT_CONV ONE_PASS_SORT_CONV THENC
          (fn tm' =>
            let val (tm1,tm2) = dest_plus tm'
            in  if (is_plus tm2) then
                   (let val tm2' = arg1 tm2
                    in  if ((is_num_const tm1) andalso (is_num_const tm2')) then
                           IN_LINE_SUM_CONV ADD_CONV tm'
                        else if (is_const tm1 orelse is_num_const tm1) then
                          ALL_CONV tm'
                        else if (is_const tm2' orelse is_num_const tm2') then
                           IN_LINE_SUM_CONV ADD_SYM_CONV tm'
                        else let val name1 = var_of_prod tm1
                                 and name2 = var_of_prod tm2'
                             in  if (name1 = name2) then
                                    IN_LINE_SUM_CONV GATHER_CONV tm'
                                 else if (String.< (name2,name1)) then
                                    IN_LINE_SUM_CONV ADD_SYM_CONV tm'
                                 else ALL_CONV tm'
                             end
                    end)
                else if ((is_num_const tm1) andalso (is_num_const tm2)) then
                   ADD_CONV tm'
                else if (is_const tm1 orelse is_num_const tm1) then
                  ALL_CONV tm'
                else if (is_const tm2 orelse is_num_const tm2) then
                  ADD_SYM_CONV tm'
                else let val name1 = var_of_prod tm1
                         and name2 = var_of_prod tm2
                     in  if (name1 = name2) then GATHER_CONV tm'
                         else if (String.< (name2,name1)) then
                           ADD_SYM_CONV tm'
                         else ALL_CONV tm'
                     end
            end)) tm
    else ALL_CONV tm
   ) handle (HOL_ERR _) => failwith "ONE_PASS_SORT_CONV";

(*--------------------------------------------------------------------------*)
(* SORT_AND_GATHER_CONV : conv                                              *)
(*                                                                          *)
(* Sort and gather for a linear sum of products. Constants are moved to the *)
(* front of the sum and variable terms are sorted lexicographically, e.g.   *)
(*                                                                          *)
(*    x + (y + (1 + ((9 * y) + (3 * x))))  -->  1 + ((4 * x) + (10 * y))    *)
(*--------------------------------------------------------------------------*)

fun SORT_AND_GATHER_CONV tm =
   REPEATC (CHANGED_CONV ONE_PASS_SORT_CONV) tm
   handle (HOL_ERR _) => failwith "SORT_AND_GATHER_CONV";

(*--------------------------------------------------------------------------*)
(* NORM_ZERO_AND_ONE_CONV : conv                                            *)
(*                                                                          *)
(* Performs the following transformations on a linear sum of products:      *)
(*                                                                          *)
(*    ... (0 * x)          -->  ... 0                                       *)
(*    ... + (0 * x) + ...  -->  ... + ...                                   *)
(*                                                                          *)
(*    ... (1 * x)          -->  ... x                                       *)
(*    ... + (1 * x) + ...  -->  ... + x + ...                               *)
(*                                                                          *)
(*    ... + exp + 0        -->  ... + exp                                   *)
(*                                                                          *)
(* And at top-level only:                                                   *)
(*                                                                          *)
(*    0 + exp              -->  exp                                         *)
(*--------------------------------------------------------------------------*)

val NORM_ZERO_AND_ONE_CONV =
   let fun NORM_CONV tm =
          if (is_plus tm) then
             (RIGHT_CONV NORM_CONV THENC
              LEFT_CONV (TRY_CONV ONE_MULT_CONV) THENC
              TRY_CONV ZERO_MULT_PLUS_CONV THENC
              TRY_CONV PLUS_ZERO_CONV) tm
          else (TRY_CONV ZERO_MULT_CONV THENC
                TRY_CONV ONE_MULT_CONV) tm
   in  fn tm => ((NORM_CONV THENC TRY_CONV ZERO_PLUS_CONV) tm
                 handle (HOL_ERR _) => failwith "NORM_ZERO_AND_ONE_CONV")
   end;

(*==========================================================================*)
(* Adding terms to equalities and inequalities                              *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* ADD_TERM_TO_INEQ_CONV : term -> conv                                     *)
(*                                                                          *)
(* ADD_TERM_TO_INEQ_CONV `x` `a R b` returns the theorem:                   *)
(*                                                                          *)
(*    |- (a R b) = ((x + a) R (x + b))                                      *)
(*                                                                          *)
(* where R is one of the relations =, <= or <.                              *)
(*--------------------------------------------------------------------------*)

fun ADD_TERM_TO_INEQ_CONV addition tm =
   (let val (R,(tm1,tm2)) = dest_ineq tm
        val conv = case R of Eq => EQ_PLUS_CONV
                           | Leq => LEQ_PLUS_CONV
                           | Less => LESS_PLUS_CONV
        val tm' = mk_ineq R (mk_plus (addition,tm1),mk_plus (addition,tm2))
    in  SYM (conv tm')
    end
   ) handle (HOL_ERR _) => failwith "ADD_TERM_TO_INEQ_CONV";

(*--------------------------------------------------------------------------*)
(* ADD_COEFFS_TO_INEQ_CONV : coeffs -> conv                                 *)
(*                                                                          *)
(* Adds terms to both sides of an equality or inequality (=, <= or <). The  *)
(* conversion avoids adding a zero constant but does not concern itself     *)
(* with eliminating zero terms in any other way.                            *)
(*--------------------------------------------------------------------------*)

fun ADD_COEFFS_TO_INEQ_CONV (const,vcoeffs) =
   let fun add_terms_conv vcoeffs =
          if (null vcoeffs)
          then ALL_CONV
          else let val (name,coeff) = hd vcoeffs
                   val addition =
                      if (coeff = num1)
                      then mk_num_var name
                      else mk_mult (term_of_num coeff,mk_num_var name)
               in  (add_terms_conv (tl vcoeffs) THENC
                    ADD_TERM_TO_INEQ_CONV addition)
               end
   in fn tm =>
         ((add_terms_conv vcoeffs THENC
           (if (const = num0)
            then ALL_CONV
            else ADD_TERM_TO_INEQ_CONV (term_of_num const))) tm)
         handle (HOL_ERR _) => failwith "ADD_COEFFS_TO_INEQ_CONV"
   end;

(*==========================================================================*)
(* Normalizing inequalities                                                 *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* INEQ_GATHER_CONV : conv                                                  *)
(*                                                                          *)
(* Assumes that the argument term is an equality or inequality (=, <= or <) *)
(* of two fully normalized arithmetic expressions. The conversion           *)
(* transforms such a term to an equality or inequality in which each        *)
(* variable occurs on only one side of the relation, and a constant term    *)
(* appears on at most one side, unless the whole of one side is zero.       *)
(*                                                                          *)
(* Here is an example result:                                               *)
(*                                                                          *)
(*    |- (1 + ((3 * x) + z)) <= (2 + (x + (4 * y))) =                       *)
(*       ((2 * x) + z) <= (1 + (4 * y))                                     *)
(*--------------------------------------------------------------------------*)

val INEQ_GATHER_CONV =
   let fun subtract_common_terms vcoeffs1 vcoeffs2 =
          if (null vcoeffs1) then ([],[],vcoeffs2)
          else if (null vcoeffs2) then ([],vcoeffs1,[])
          else (let val (name1,coeff1) = hd vcoeffs1
                    and (name2,coeff2) = hd vcoeffs2
                in  if (name1 = name2) then
                       (let val (c,b1,b2) = subtract_common_terms
                                               (tl vcoeffs1) (tl vcoeffs2)
                        in  if (coeff1 = coeff2) then ((name1,coeff1)::c,b1,b2)
                            else if (coeff1 < coeff2) then
                               ((name1,coeff1)::c,b1,
                                (name1,coeff2 - coeff1)::b2)
                            else ((name1,coeff2)::c,
                                  (name1,coeff1 - coeff2)::b1,
                                  b2)
                        end)
                    else if (String.< (name1,name2)) then
                       (let val (c,b1,b2) =
                               subtract_common_terms (tl vcoeffs1) vcoeffs2
                        in  (c,(name1,coeff1)::b1,b2)
                        end)
                    else (let val (c,b1,b2) =
                                 subtract_common_terms vcoeffs1 (tl vcoeffs2)
                          in  (c,b1,(name2,coeff2)::b2)
                          end)
                end)
   in  fn tm =>
          let val (R,(tm1,tm2)) = dest_ineq tm
              val (const1,vcoeffs1) = coeffs_of_arith tm1
              and (const2,vcoeffs2) = coeffs_of_arith tm2
              val (vcoeffsc,vcoeffsl,vcoeffsr) =
                 subtract_common_terms vcoeffs1 vcoeffs2
              and (constc,constl,constr) =
                 if (const1 < const2)
                 then (const1,num0,const2 - const1)
                 else (const2,const1 - const2,num0)
              val tml = arith_of_coeffs (constl,vcoeffsl)
              and tmr = arith_of_coeffs (constr,vcoeffsr)
          in  SYM ((ADD_COEFFS_TO_INEQ_CONV (constc,vcoeffsc) THENC
                    BINOP_CONV
                       (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV))
                   (mk_ineq R (tml,tmr)))
          end
          handle (HOL_ERR _) => failwith "INEQ_GATHER_CONV"
   end;

(*--------------------------------------------------------------------------*)
(* ARITH_LITERAL_NORM_CONV : conv                                           *)
(*                                                                          *)
(* Converts an arithmetic literal into a disjunction of applications of the *)
(* =, <= and < relations. The arithmetic expressions are only allowed to    *)
(* contain variables, addition, the SUC function, and multiplication by     *)
(* constants. The literal may contain the natural number relations =, <=, < *)
(* >=, >.                                                                   *)
(*                                                                          *)
(* The equalities and inequalities in the result are normalized so that     *)
(* each variable appears on only one side of the relation, and each side is *)
(* a linear sum in which any constant appears first, followed by products   *)
(* of a constant and a variable. The variables are ordered                  *)
(* lexicographically, and if the coefficient of the variable is 1, the      *)
(* variable appears alone in the term, not as a product.                    *)
(*--------------------------------------------------------------------------*)

fun ARITH_LITERAL_NORM_CONV tm =
   NUM_RELN_NORM_CONV
      (SUM_OF_PRODUCTS_CONV THENC
       LINEAR_SUM_CONV THENC
       SORT_AND_GATHER_CONV THENC
       NORM_ZERO_AND_ONE_CONV)
      INEQ_GATHER_CONV
      tm
   handle (HOL_ERR _) => failwith "ARITH_LITERAL_NORM_CONV";

(*==========================================================================*)
(* Multiplying normalized arithmetic expressions by a constant              *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* CONST_TIMES_ARITH_CONV : conv                                            *)
(*                                                                          *)
(* Converts the product of a constant and a normalized arithmetic           *)
(* expression to a new normalized arithmetic expression.                    *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    CONST_TIMES_ARITH_CONV `3 * (1 + (3 * x) + (2 * y))`  -->             *)
(*    |- 3 * (1 + ((3 * x) + (2 * y))) = 3 + ((9 * x) + (6 * y))            *)
(*--------------------------------------------------------------------------*)

fun CONST_TIMES_ARITH_CONV tm =
   let fun CONST_TIMES_VAR_CONV tm =
          if (is_var (arg2 tm))
          then ALL_CONV tm
          else (MULT_ASSOC_CONV THENC LEFT_CONV FAST_MULT_CONV) tm
       fun CONST_TIMES_VARS_CONV tm =
          if (is_plus (arg2 tm))
          then (LEFT_ADD_DISTRIB_CONV THENC
                ARGS_CONV [CONST_TIMES_VAR_CONV,CONST_TIMES_VARS_CONV]) tm
          else CONST_TIMES_VAR_CONV tm
       val tm' = arg2 tm
   in  if (is_num_const tm') then FAST_MULT_CONV tm
       else if (is_var tm') orelse (is_mult tm') then CONST_TIMES_VAR_CONV tm
       else if (is_num_const (arg1 tm')) then
          (LEFT_ADD_DISTRIB_CONV THENC
           ARGS_CONV [FAST_MULT_CONV,CONST_TIMES_VARS_CONV]) tm
       else CONST_TIMES_VARS_CONV tm
   end
   handle (HOL_ERR _) => failwith "CONST_TIMES_ARITH_CONV";

(*--------------------------------------------------------------------------*)
(* MULT_INEQ_BY_CONST_CONV : term -> conv                                   *)
(*                                                                          *)
(* Multiplies both sides of a normalized equality or inequality by a        *)
(* non-zero constant.                                                       *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    MULT_INEQ_BY_CONST_CONV `3` `(1 + (3 * x) + (2 * y)) <= (3 * z)`  --> *)
(*    |- (1 + ((3 * x) + (2 * y))) <= (3 * z) =                             *)
(*       (3 + ((9 * x) + (6 * y))) <= (9 * z)                               *)
(*--------------------------------------------------------------------------*)

fun MULT_INEQ_BY_CONST_CONV constant tm =
   let val (R,(tm1,tm2)) = dest_ineq tm
       and n = num_of_term constant
   in  if (n = num0) then failwith ""
       else if (n = num1) then ALL_CONV tm
       else let val constant' = term_of_num (n - num1)
                val th = SYM (num_CONV constant)
                val conv = fn dummytm => th
                val thm = case R of Eq => MULT_EQ_SUC
                                  | Leq => MULT_LEQ_SUC
                                  | Less => MULT_LESS_SUC
            in  RIGHT_CONV_RULE
                   (BINOP_CONV (LEFT_CONV conv THENC CONST_TIMES_ARITH_CONV))
                   (SPECL [tm1,tm2,constant'] thm)
            end
   end
   handle (HOL_ERR _) => failwith "MULT_INEQ_BY_CONST_CONV";

(*==========================================================================*)
(* Solving equalities and inequalities between constants                    *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* EQ_CONV : conv                                                           *)
(*                                                                          *)
(* Given a term of the form `a = b` where a and b are constants, returns    *)
(* the theorem |- (a = b) = T or the theorem |- (a = b) = F depending on    *)
(* the values of a and b.                                                   *)
(*--------------------------------------------------------------------------*)

fun EQ_CONV tm =
   let val (tm1,tm2) = dest_eq tm
       val n1 = num_of_term tm1
       and n2 = num_of_term tm2
   in  if (n1 = n2) then ISPEC tm1 REFL_CLAUSE
       else if (n1 < n2) then
          let val diff1tm = term_of_num ((n2 - n1) - num1)
              and th = SYM (num_CONV tm2)
              val th1 = SPECL [tm1,diff1tm] EQ_SUC_ADD_F
              val conv = fn dummytm => th
          in  CONV_RULE
                 (LEFT_CONV (RIGHT_CONV (RAND_CONV ADD_CONV THENC conv))) th1
          end
       else
          let val diff1tm = term_of_num ((n1 - n2) - num1)
              and th = SYM (num_CONV tm1)
              val th1 = SPECL [tm2,diff1tm] SUC_ADD_EQ_F
              val conv = fn dummytm => th
          in  CONV_RULE
                 (LEFT_CONV (LEFT_CONV (RAND_CONV ADD_CONV THENC conv))) th1
          end
   end
   handle (HOL_ERR _) => failwith "EQ_CONV";

(*--------------------------------------------------------------------------*)
(* LEQ_CONV : conv                                                          *)
(*                                                                          *)
(* Given a term of the form `a <= b` where a and b are constants, returns   *)
(* the theorem |- (a <= b) = T or the theorem |- (a <= b) = F depending on  *)
(* the values of a and b.                                                   *)
(*                                                                          *)
(* Optimized for when one or both of the arguments is zero.                 *)
(*--------------------------------------------------------------------------*)

val LEQ_CONV = reduceLib.LE_CONV

(*--------------------------------------------------------------------------*)
(* LESS_CONV : conv                                                         *)
(*                                                                          *)
(* Given a term of the form `a < b` where a and b are constants, returns    *)
(* the theorem |- (a < b) = T or the theorem |- (a < b) = F depending on    *)
(* the values of a and b.                                                   *)
(*                                                                          *)
(* Optimized for when one or both of the arguments is zero.                 *)
(*--------------------------------------------------------------------------*)

val LESS_CONV = reduceLib.LT_CONV

(*==========================================================================*)
(* Eliminating variables from sets of inequalities                          *)
(*==========================================================================*)

local
   open LazyThm
in

(*--------------------------------------------------------------------------*)
(* INEQ_RULE : pre_thm -> pre_thm                                           *)
(*--------------------------------------------------------------------------*)

fun INEQ_RULE th =
   let val (hyps,conc) = dest_pre_thm th
       val (R,(tm1,tm2)) = dest_ineq conc
       val n1 = num_of_term tm1
       and n2 = num_of_term tm2
       val (tm,conv) =
          case R
          of Eq => (if (n1 = n2) then T else F,EQ_CONV)
           | Leq => (if (n2 < n1) then F else T,LEQ_CONV)
           | Less => (if (n1 < n2) then T else F,LESS_CONV)
   in  apply_rule1 (fn _ => (hyps,tm),CONV_RULE conv) th
   end
   handle (HOL_ERR _) => failwith "INEQ_RULE";

(*--------------------------------------------------------------------------*)
(* WEIGHTED_SUM :                                                           *)
(*    string ->                                                             *)
(*    ((inequality_relation * coeffs) lazy_thm *                            *)
(*     (inequality_relation * coeffs) lazy_thm) ->                          *)
(*    (inequality_relation * coeffs) lazy_thm                               *)
(*                                                                          *)
(* Function to eliminate a specified variable from two equalities or        *)
(* inequalities by forming their weighted sum. The equalities and           *)
(* inequalities must be given as lazy theorems with coefficients as the     *)
(* representation. The result is a lazy theorem for the combined formula.   *)
(*                                                                          *)
(* The variable to be eliminated should be on the right-hand side of the    *)
(* first inequality, and on the left-hand side of the second.               *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    WEIGHTED_SUM "y"                                                      *)
(*       ((. |- (3 * x) <= (1 + y)), (. |- ((3 * x) + y) <= 3))             *)
(*    -->                                                                   *)
(*    . |- (6 * x) <= 4                                                     *)
(*                                                                          *)
(* WARNING: This function assumes that `<' is not used as the relation when *)
(* the ordering is non-dense (e.g. natural numbers and integers). For       *)
(* non-dense orderings the transitivity theorem for two `<' inequalities    *)
(* needs to be different to the one used here. Also, multiplication of a    *)
(* `<' inequality by a factor requires special treatment.                   *)
(*--------------------------------------------------------------------------*)

fun WEIGHTED_SUM name (right_th,left_th) =
   let val (relr,coeffsr) = dest_lazy_thm right_th
       and (rell,coeffsl) = dest_lazy_thm left_th
       val (rel,transitivity) =
          case (relr,rell)
          of (Eq,Eq) => (Eq,EQ_EQ_TRANSIT)
           | (Eq,Leq) => (Leq,EQ_LEQ_TRANSIT)
           | (Eq,Less) => (Less,EQ_LESS_TRANSIT)
           | (Leq,Eq) => (Leq,LEQ_EQ_TRANSIT)
           | (Leq,Leq) => (Leq,LEQ_LEQ_TRANSIT)
           | (Leq,Less) => (Less,LEQ_LESS_TRANSIT)
           | (Less,Eq) => (Less,LESS_EQ_TRANSIT)
           | (Less,Leq) => (Less,LESS_LEQ_TRANSIT)
           | (Less,Less) => (Less,LESS_LESS_TRANSIT)
       val coeffr = coeff_of_var name coeffsr
       and coeffl = num0 - (coeff_of_var name coeffsl)
       val mult = lcm (coeffr,coeffl)
       val multr = mult div coeffr
       and multl = mult div coeffl
       val coeffsr' = scale_coeffs multr coeffsr
       and coeffsl' = scale_coeffs multl coeffsl
       val (addsr,addsl) = diff_of_coeffs (coeffsr',coeffsl')
       val coeffsr'' = merge_coeffs addsr (lhs_coeffs coeffsr')
       and coeffsl'' = merge_coeffs addsl (rhs_coeffs coeffsl')
       val new_coeffs = merge_coeffs (negate_coeffs coeffsr'') coeffsl''
       datatype side = Left | Right
       fun SIDE_CONV Left = LEFT_CONV
         | SIDE_CONV Right = RIGHT_CONV
       fun WEIGHT_CONV side mult adds =
          (if (mult = num1)
           then ALL_CONV
           else MULT_INEQ_BY_CONST_CONV (term_of_num mult)) THENC
          (if (adds = (num0,[]))
           then ALL_CONV
           else ADD_COEFFS_TO_INEQ_CONV adds THENC
                SIDE_CONV side
                   (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV))
       fun TIDY_CONV side adds =
          if (adds = (num0,[]))
          then ALL_CONV
          else SIDE_CONV side
                  (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV)
       fun rule right_th left_th =
          let val thr = CONV_RULE (WEIGHT_CONV Right multr addsr) right_th
              and thl = CONV_RULE (WEIGHT_CONV Left multl addsl) left_th
          in  CONV_RULE (TIDY_CONV Left addsr THENC
                         TIDY_CONV Right addsl THENC
                         INEQ_GATHER_CONV)
                 (MATCH_MP transitivity (CONJ thr thl))
          end
   in  apply_rule2 (fn _ => fn _ => (rel,new_coeffs),rule) right_th left_th
   end
   handle Portable.Div => failwith "WEIGHTED_SUM"
        | (HOL_ERR _) => failwith "WEIGHTED_SUM";

(*--------------------------------------------------------------------------*)
(* var_to_elim : (inequality_relation * coeffs) list -> string              *)
(*                                                                          *)
(* Given a list of (in)equalities (as relation and coefficients), this      *)
(* function determines which variable to eliminate. Such a variable must    *)
(* occur in two inequalities on different sides or in an equality and one   *)
(* of the other equalities or inequalities. The variable chosen is the one  *)
(* that gives rise to the smallest increase in the number of                *)
(* (in)equalities.                                                          *)
(*--------------------------------------------------------------------------*)

fun var_to_elim rel_and_coeffs_list =
   let fun var_to_elim' rel vcoeffs =
          if (null vcoeffs)
          then (([],[]),[])
          else let val (name,coeff) = hd vcoeffs
                   and ((occsl,occsr),occse) = var_to_elim' rel (tl vcoeffs)
               in  if (rel = Eq) andalso not (coeff = num0) then
                      ((occsl,occsr),name :: occse)
                   else if (coeff < num0) then ((name :: occsl,occsr),occse)
                   else if (num0 < coeff) then ((occsl,name :: occsr),occse)
                   else ((occsl,occsr),occse)
               end
       fun min_increase num_of_occs =
          let open Int
              exception Minimum
              fun minimum [] = raise Minimum
                | minimum ((name,((l,r),e))::rest) =
                 if ((l >= 1) andalso (r >= 1)) orelse
                    ((l >= 1) andalso (e >= 1)) orelse
                    ((r >= 1) andalso (e >= 1)) orelse
                    (e >= 2)
                 then let val increase = (l * r) + (l * e) + (r * e) +
                                         ((e * (e - 1)) div 2) - (l + r + e)
                      in  let val m as (_,min) = minimum rest
                          in  if (increase <= min) then (name,increase) else m
                          end
                          handle Minimum => (name,increase)
                      end
                 else minimum rest
          in  #1 (minimum num_of_occs) handle Minimum => failwith ""
          end
       fun count [] = []
         | count (name::names) =
          let fun count' partial [] = [partial]
                | count' (partial as (previous,n)) (s::ss) =
                 if (s = previous)
                 then count' (previous,Int.+ (n,1)) ss
                 else partial :: count' (s,1) ss
          in  count' (name,1) names
          end
       val acc = count o sort (curry String.<) o flatten
       fun merge (_,ydefault) (xs,[]) =
          map (fn (key,x) => (key,(x,ydefault))) xs
         | merge (xdefault,_) ([],ys) =
          map (fn (key,y) => (key,(xdefault,y))) ys
         | merge (d as (xd,yd)) (xs as (keyx,x) :: xs',ys as (keyy,y) :: ys') =
          if (keyx = keyy)
          then (keyx,(x,y)) :: merge d (xs',ys')
          else if (String.< (keyx,keyy))
               then (keyx,(x,yd)) :: merge d (xs',ys)
               else (keyy,(xd,y)) :: merge d (xs,ys')
       val occs = map (fn (rel,(_,vcoeffs)) => var_to_elim' rel vcoeffs)
                     rel_and_coeffs_list
       val num_of_occs =
          (merge ((0,0),0) o ((merge (0,0) o (acc ## acc) o split) ## acc))
             (split occs)
   in  min_increase num_of_occs
   end
   handle HOL_ERR _ => failwith "var_to_elim";

(*--------------------------------------------------------------------------*)
(* false_coeffs : inequality_relation * coeffs -> bool                      *)
(*                                                                          *)
(* Returns true if the inequality represented by the coefficients is        *)
(* manifestly false.                                                        *)
(*--------------------------------------------------------------------------*)

fun false_coeffs (rel,coeffs) =
   (null (coeffs_of_vars coeffs)) andalso
   (case rel of Eq => not (num0 = coeff_of_const coeffs)
              | Leq => coeff_of_const coeffs < num0
              | Less => not (num0 < coeff_of_const coeffs));

(*--------------------------------------------------------------------------*)
(* VAR_ELIM : (inequality_relation * coeffs) lazy_thm list ->               *)
(*            (inequality_relation * coeffs) lazy_thm                       *)
(*                                                                          *)
(* Given a list of (in)equalities represented by lazy theorems, this        *)
(* function returns a lazy theorem with false (actually an (in)equality     *)
(* between constants that can immediately be shown to be false) as its      *)
(* conclusion, and the original conjunction of (in)equalities as an         *)
(* assumption. The function fails if the set of (in)equalities is           *)
(* satisfiable.                                                             *)
(*                                                                          *)
(* The function assumes that none of the (in)equalities given are false,    *)
(* that is they either contain variables, or evaluate to true. Those that   *)
(* are true are filtered out. The function then determines which variable   *)
(* to eliminate and splits the remaining (in)equalities into five sets:     *)
(*                                                                          *)
(* 1. equations in which the variable occurs on the right-hand side,        *)
(* 2. equations in which the variable occurs on the left-hand side,         *)
(* 3. inequalities in which the variable occurs on the right-hand side,     *)
(* 4. inequalities in which the variable occurs on the left-hand side,      *)
(* 5. theorems in which the variable does not occur.                        *)
(*                                                                          *)
(* Pairings of the `right' and `left' inequalities are then made, along     *)
(* with pairings of all the equations with the `left' inequalities,         *)
(* pairings of the `right' inequalities with all the equations, and         *)
(* combinations of the equations. The equations have to be given special    *)
(* treatment because they are not oriented as the inequalities are: they    *)
(* can be reversed (using the symmetry of equality) so that the variable    *)
(* appears on the other side of the relation. Equations are combined in     *)
(* such a way as to avoid pairing any equation with itself.                 *)
(*                                                                          *)
(* When all the pairs of theorems have been formed the weighted sum of each *)
(* is determined, except that as soon as a pairing yields false the process *)
(* is terminated. It may well be the case that no pairing gives false. In   *)
(* this case the new theorems are added to the theorems that did not        *)
(* contain the variable, and a recursive call is made.                      *)
(*--------------------------------------------------------------------------*)

fun VAR_ELIM abs_ths =
   let fun weighted_sums var [] = (false,[])
         | weighted_sums var (pair::pairs) =
          let val result as (success,rest) = weighted_sums var pairs
          in  if success
              then result
              else let val new_th = WEIGHTED_SUM var pair
                   in  if (false_coeffs (dest_lazy_thm new_th))
                       then (true,[new_th])
                       else (false,new_th :: rest)
                   end
          end
       fun combinations [] = []
         | combinations ((x,_) :: rest) =
          map (fn (_,y) => (x,y)) rest @ combinations rest
       val sym =
          apply_rule1 (fn (rel,coeffs) => (rel,negate_coeffs coeffs),SYM)
       fun is (pr,pc) th =
          let val (rel,coeffs) = dest_lazy_thm th
          in  (pr rel) andalso (pc coeffs)
          end
       fun isc p = is (fn _ => true,p)
       fun an_eq Eq = true | an_eq _ = false
       val abs_ths' = filter (isc (not o null o coeffs_of_vars)) abs_ths
       val var = var_to_elim (map dest_lazy_thm abs_ths')
       val eqr_ths = filter (is (an_eq,var_on_right var)) abs_ths'
       and eql_ths = filter (is (an_eq,var_on_left var)) abs_ths'
       and right_ths = filter (is (not o an_eq,var_on_right var)) abs_ths'
       and left_ths = filter (is (not o an_eq,var_on_left var)) abs_ths'
       and no_var_ths = filter (isc (var_not_present var)) abs_ths'
       val eqr_ths2 = eqr_ths @ map sym eql_ths
       and eql_ths2 = map sym eqr_ths @ eql_ths
       val pairs = pairings I (right_ths,left_ths) @
                   pairings I (eqr_ths2,left_ths) @
                   pairings I (right_ths,eql_ths2) @
                   combinations (zip eqr_ths2 eql_ths2)
       val (success,new_ths) = weighted_sums var pairs
   in  if success
       then hd new_ths
       else VAR_ELIM (new_ths @ no_var_ths)
   end
   handle HOL_ERR _ => failwith "VAR_ELIM";

(*--------------------------------------------------------------------------*)
(* INEQS_FALSE_CONV : term -> pre_thm                                       *)
(*                                                                          *)
(* Proves a conjunction of normalized inequalities is false, provided they  *)
(* are unsatisfiable. Checks for any inequalities that can immediately be   *)
(* shown to be false before calling VAR_ELIM.                               *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    INEQS_FALSE_CONV                                                      *)
(*       `((2 + (2 * n)) <= m) /\                                           *)
(*        (m <= n) /\                                                       *)
(*        (0 <= n) /\                                                       *)
(*        (0 <= m)`                                                         *)
(*    -->                                                                   *)
(*    |- ((2 + (2 * n)) <= m) /\                                            *)
(*       (m <= n) /\                                                        *)
(*       (0 <= n) /\                                                        *)
(*       (0 <= m) =                                                         *)
(*       F                                                                  *)
(*--------------------------------------------------------------------------*)

local
   open LazyRules
   val ZERO_LESS_EQ = mk_proved_pre_thm ZERO_LESS_EQ
in

fun INEQS_FALSE_CONV tm =
   let val ths = CONJUNCTS (ASSUME tm)
       val abs_ths = map (restructure_lazy_thm coeffs_of_goal) ths
       val ineql = map dest_lazy_thm abs_ths
       val false_ths = filter (false_coeffs o #1) (zip ineql ths)
       val th =
          if (null false_ths)
          then let val var_names = vars_of_coeffs (map #2 ineql)
                   val axioms =
                      map (fn v => SPEC (mk_num_var v) ZERO_LESS_EQ) var_names
                   val abs_axioms =
                      map (restructure_lazy_thm coeffs_of_goal) axioms
               in  restructure_lazy_thm
                      (fn rel_and_coeffs =>
                          ([tm],ineq_of_coeffs rel_and_coeffs))
                      (VAR_ELIM (abs_axioms @ abs_ths))
               end
          else #2 (hd false_ths)
   in  IMP_F_EQ_F_RULE (DISCH tm (INEQ_RULE th))
   end
   handle (HOL_ERR _) => failwith "INEQS_FALSE_CONV";

end;

end;

end; (* NumArith *)
