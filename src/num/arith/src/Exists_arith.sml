(*****************************************************************************)
(* FILE          : exists_arith.sml                                          *)
(* DESCRIPTION   : Procedure for proving purely existential prenex           *)
(*                 Presburger arithmetic formulae.                           *)
(*                                                                           *)
(* READS FILES   : The "reduce" library                                      *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 25th June 1992                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Exists_arith :> Exists_arith =
struct
  open Arbint
  val << = String.<


open HolKernel boolLib Rsyntax reduceLib Arith_cons;
open Term_coeffs;
open RJBConv; infix THENC;
open Norm_arith;
open Norm_ineqs;
open Sol_ranges;

fun failwith function = raise HOL_ERR{origin_structure = "Exists_arith",
                                      origin_function = function,
                                      message = ""};


(*---------------------------------------------------------------------------*)
(* NUM_REDUCE_CONV : conv                                                    *)
(*---------------------------------------------------------------------------*)

fun NUM_REDUCE_CONV tm =
   if (is_suc tm) then ((RAND_CONV NUM_REDUCE_CONV) THENC SUC_CONV) tm
   else if (is_plus tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC ADD_CONV) tm
   else if (is_mult tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC MUL_CONV) tm
   else ALL_CONV tm;

(*---------------------------------------------------------------------------*)
(* INEQ_REDUCE_CONV : conv                                                   *)
(*---------------------------------------------------------------------------*)

fun INEQ_REDUCE_CONV tm =
   if (is_eq tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC NEQ_CONV) tm
   else if (is_leq tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC LE_CONV) tm
   else if (is_less tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC LT_CONV) tm
   else if (is_geq tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC GE_CONV) tm
   else if (is_great tm) then ((ARGS_CONV NUM_REDUCE_CONV) THENC GT_CONV) tm
   else ALL_CONV tm;

(*---------------------------------------------------------------------------*)
(* BOOL_REDUCE_CONV : conv                                                   *)
(*---------------------------------------------------------------------------*)

fun BOOL_REDUCE_CONV tm =
   if (is_num_reln tm) then INEQ_REDUCE_CONV tm
   else if (is_neg tm) then ((RAND_CONV BOOL_REDUCE_CONV) THENC NOT_CONV) tm
   else if (is_conj tm) then ((ARGS_CONV BOOL_REDUCE_CONV) THENC AND_CONV) tm
   else if (is_disj tm) then ((ARGS_CONV BOOL_REDUCE_CONV) THENC OR_CONV) tm
   else if (is_imp tm) then ((ARGS_CONV BOOL_REDUCE_CONV) THENC IMP_CONV) tm
   else if (is_eq tm) then ((ARGS_CONV BOOL_REDUCE_CONV) THENC BEQ_CONV) tm
   else INEQ_REDUCE_CONV tm;

(*---------------------------------------------------------------------------*)
(* WITNESS : (string * int) list -> conv                                     *)
(*                                                                           *)
(* This function proves an existentially quantified arithmetic formula given *)
(* a witness for the formula in the form of a variable-name/value binding.   *)
(*---------------------------------------------------------------------------*)

fun WITNESS binding tm =
 (let val {Bvar,Body} = dest_exists tm
      val num = term_of_int (assoc (#Name (dest_var Bvar)) binding
                             handle _ => zero)
  in  EXISTS (tm,num)
         (WITNESS binding (subst [{residue = num,redex = Bvar}] Body))
  end
 ) handle _ => EQT_ELIM (RULE_OF_CONV BOOL_REDUCE_CONV tm);

(*---------------------------------------------------------------------------*)
(* witness : term list -> (string * int) list                                *)
(*                                                                           *)
(* Function to find a witness for a formula from the disjuncts of a          *)
(* normalised version.                                                       *)
(*---------------------------------------------------------------------------*)

fun witness tml =
   if (null tml)
   then failwith "witness"
   else Shostak (coeffs_of_leq_set (hd tml)) handle _ => (witness (tl tml));

(*---------------------------------------------------------------------------*)
(* EXISTS_ARITH_CONV : conv                                                  *)
(*                                                                           *)
(* Proof procedure for non-universal Presburger natural arithmetic           *)
(* (+, * by a constant, numeric constants, numeric variables, <, <=, =, >=,  *)
(* >, ~, /\, \/, ==>, = (iff), ? (when in prenex normal form).               *)
(* Expects formula in prenex normal form.                                    *)
(* Subtraction, PRE and conditionals must have been eliminated.              *)
(* SUC is allowed.                                                           *)
(* Boolean variables and constants are not allowed.                          *)
(*                                                                           *)
(* The procedure is not complete.                                            *)
(*---------------------------------------------------------------------------*)

fun EXISTS_ARITH_CONV tm =
 (reset_multiplication_theorems ();
  let val th = RULE_OF_CONV ARITH_FORM_NORM_CONV
                  (snd (strip_exists (assert (null o free_vars) tm)))
               handle (HOL_ERR _) =>
               raise HOL_ERR{origin_structure = "Exists_arith",
                             origin_function = "EXISTS_ARITH_CONV",
                             message = "formula not in the allowed subset"}
  in  (let val binding = witness (strip_disj (rhs (concl th)))
       in  EQT_INTRO (WITNESS binding tm)
       end
      ) handle (HOL_ERR _) =>
        raise HOL_ERR{origin_structure = "Exists_arith",
                      origin_function = "EXISTS_ARITH_CONV",
                      message = "cannot prove formula"}
  end
 );

end
