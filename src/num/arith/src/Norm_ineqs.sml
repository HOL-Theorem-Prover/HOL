(*****************************************************************************)
(* FILE          : norm_ineqs.sml                                            *)
(* DESCRIPTION   : Functions for normalizing inequalities.                   *)
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
(* DATE          : 7th August 1996                                           *)
(*****************************************************************************)

structure Norm_ineqs :> Norm_ineqs =
struct


open Arbint HolKernel Arith_cons RJBConv 
     Term_coeffs Thm_convs Norm_bool Norm_arith;

infix THENC <<;

val op << = String.<

fun failwith f = raise (mk_HOL_ERR "Norm_ineqs" f "")


(*===========================================================================*)
(* Adding terms to inequalities                                              *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* ADD_TERM_TO_LEQ_CONV : term -> conv                                       *)
(*                                                                           *)
(* ADD_TERM_TO_LEQ_CONV `x` `a <= b` returns the theorem:                    *)
(*                                                                           *)
(*    |- (a <= b) = ((x + a) <= (x + b))                                     *)
(*---------------------------------------------------------------------------*)

fun ADD_TERM_TO_LEQ_CONV addition tm =
 (let val (tm1,tm2) = dest_leq tm
      val tm' = mk_leq (mk_plus (addition,tm1),mk_plus (addition,tm2))
  in  SYM (LEQ_PLUS_CONV tm')
  end
 ) handle (HOL_ERR _) => failwith "ADD_TERM_TO_LEQ_CONV";

(*---------------------------------------------------------------------------*)
(* ADD_COEFFS_TO_LEQ_CONV : (int * (string * int) list) -> conv              *)
(*                                                                           *)
(* Adds terms to both sides of a less-than-or-equal-to inequality. The       *)
(* conversion avoids adding a zero constant but does not concern itself with *)
(* eliminating zero terms in any other way.                                  *)
(*---------------------------------------------------------------------------*)

fun ADD_COEFFS_TO_LEQ_CONV (const,bind) =
 let fun add_terms_conv bind =
        if (null bind)
        then ALL_CONV
        else let val (name,coeff) = hd bind
                 val addition = mk_mult (term_of_int coeff,mk_num_var name)
             in  ((add_terms_conv (tl bind)) THENC
                  (ADD_TERM_TO_LEQ_CONV addition))
             end
 in fn tm =>
 (((add_terms_conv bind) THENC
   (if (const = zero)
    then ALL_CONV
    else ADD_TERM_TO_LEQ_CONV (term_of_int const))) tm)
 handle (HOL_ERR _) => failwith "ADD_COEFFS_TO_LEQ_CONV"
 end;

(*===========================================================================*)
(* Normalizing inequalities                                                  *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* LESS_OR_EQ_GATHER_CONV : conv                                             *)
(*                                                                           *)
(* Assumes that the argument term is a less-than-or-equal-to of two fully    *)
(* normalized arithmetic expressions. The conversion transforms such a term  *)
(* to a less-than-or-equal-to in which each variable occurs on only one side *)
(* of the inequality, and a constant term appears on at most one side,       *)
(* unless the whole of one side is zero.                                     *)
(*                                                                           *)
(* Here is an example result:                                                *)
(*                                                                           *)
(*    |- (1 + ((3 * x) + (1 * z))) <= (2 + ((1 * x) + (4 * y))) =            *)
(*       ((2 * x) + (1 * z)) <= (1 + (4 * y))                                *)
(*---------------------------------------------------------------------------*)

val LESS_OR_EQ_GATHER_CONV =
 let fun subtract_common_terms bind1 bind2 =
        if (null bind1) then ([],[],bind2)
        else if (null bind2) then ([],bind1,[])
        else let val (name1:string,coeff1:int) = hd bind1
                 and (name2,coeff2) = hd bind2
             in  if (name1 = name2) then
                     (let val (c,b1,b2) =
                             subtract_common_terms (tl bind1) (tl bind2)
                      in  if (coeff1 = coeff2) then ((name1,coeff1)::c,b1,b2)
                          else if (coeff1 < coeff2) then
                             ((name1,coeff1)::c,b1,(name1,coeff2 - coeff1)::b2)
                          else ((name1,coeff2)::c,
                                (name1,coeff1 - coeff2)::b1,
                                b2)
                      end)
                  else if (name1 << name2) then
                     (let val (c,b1,b2) =
                             subtract_common_terms (tl bind1) bind2
                      in  (c,(name1,coeff1)::b1,b2)
                      end)
                  else (let val (c,b1,b2) =
                               subtract_common_terms bind1 (tl bind2)
                        in  (c,b1,(name2,coeff2)::b2)
                        end)
             end
 in fn tm =>
 (let val (tm1,tm2) = dest_leq tm
      val (const1,bind1) = coeffs_of_arith tm1
      and (const2,bind2) = coeffs_of_arith tm2
      val (bindc,bindl,bindr) = subtract_common_terms bind1 bind2
      and (constc,constl,constr) =
         if (const1 < const2)
         then (const1, zero, const2 - const1)
         else (const2, const1 - const2, zero)
      val tml = build_arith (constl,bindl)
      and tmr = build_arith (constr,bindr)
  in  SYM
       (((ADD_COEFFS_TO_LEQ_CONV (constc,bindc)) THENC
         (ARGS_CONV (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV)))
        (mk_leq (tml,tmr)))
  end
 ) handle (HOL_ERR _) => failwith "LESS_OR_EQ_GATHER_CONV"
 end;

(*---------------------------------------------------------------------------*)
(* ARITH_FORM_NORM_CONV : conv                                               *)
(*                                                                           *)
(* Converts an arithmetic formula into a disjunction of conjunctions of      *)
(* less-than-or-equal-to inequalities. The arithmetic expressions are only   *)
(* allowed to contain variables, addition, the SUC function, and             *)
(* multiplication by constants. The formula is not allowed to contain        *)
(* quantifiers, but may have disjunction, conjunction, negation,             *)
(* implication, equality on Booleans, and the natural number relations       *)
(* =, <, <=, >, >=.                                                          *)
(*                                                                           *)
(* The inequalities in the result are normalized so that each variable       *)
(* appears on only one side of the inequality, and each side is a linear sum *)
(* in which any constant appears first, followed by products of a constant   *)
(* and a variable. The variables are ordered lexicographically, and if the   *)
(* coefficient of the variable is 1, the product of 1 and the variable       *)
(* appears in the term, not simply the variable.                             *)
(*---------------------------------------------------------------------------*)

fun ARITH_FORM_NORM_CONV tm =
 (EQ_IMP_ELIM_CONV is_num_reln
  THENC MOVE_NOT_DOWN_CONV is_num_reln
          (NUM_RELN_NORM_CONV
              (SUM_OF_PRODUCTS_CONV 
                 THENC LINEAR_SUM_CONV 
                 THENC SORT_AND_GATHER_CONV
                 THENC NORM_ZERO_AND_ONE_CONV)
              LESS_OR_EQ_GATHER_CONV)
  THENC DISJ_NORM_FORM_CONV)
 tm handle (HOL_ERR _) => failwith "ARITH_FORM_NORM_CONV";

end
