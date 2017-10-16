(* ----------------------------------------------------------------------
    FILE          : gen_arith.sml
    DESCRIPTION   : Generalised arithmetic proof procedure.

    AUTHOR        : R.J.Boulton, University of Cambridge
    DATE          : 30th January 1992
   ---------------------------------------------------------------------- *)

structure Gen_arith :> Gen_arith =
struct

open Arbint HolKernel boolLib Rsyntax
     Arith_cons Solve Exists_arith
     Sub_and_cond Prenex Instance RJBConv;

infix THENC;

val REWRITE_CONV = Rewrite.REWRITE_CONV;

fun failwith function = raise (mk_HOL_ERR "Gen_arith" function "");

val op << = String.<;


(*---------------------------------------------------------------------------*)
(* contains_var : term -> bool                                               *)
(*                                                                           *)
(* Returns true if an expression possibly involving SUC, +, *, numeric       *)
(* constants and variables does contain a variable. Also returns true if any *)
(* subterm does not conform to this specification of expressions.            *)
(*                                                                           *)
(* The internal function uses failure to denote that the expression          *)
(* evaluates to zero. This is used because, when normalised, zero multiplied *)
(* by an expression is zero and hence any variables in the expression can be *)
(* ignored.                                                                  *)
(*---------------------------------------------------------------------------*)

fun contains_var tm =
   let fun contains_var' tm =
          if (is_var tm) then true
          else if (is_const tm orelse is_num_const tm) then
             (if (is_zero tm) then failwith "fail" else not (is_num_const tm))
          else if (is_suc tm) then (contains_var' (rand tm) handle _ => false)
          else if (is_plus tm) then
             ((let val b = contains_var' (arg1 tm)
               in  b orelse (contains_var' (arg2 tm) handle _ => false)
               end)
             handle _ => contains_var' (arg2 tm)
             )
          else if (is_mult tm) then
             ((contains_var' (arg1 tm)) orelse (contains_var' (arg2 tm)))
          else true
   in  contains_var' tm handle _ => false
   end;

(*---------------------------------------------------------------------------*)
(* is_linear_mult : term -> bool                                             *)
(*                                                                           *)
(* Returns true if the term is a linear multiplication, i.e. at least one of *)
(* the arguments is a constant expression. Fails if the term is not a        *)
(* multiplication.                                                           *)
(*---------------------------------------------------------------------------*)

fun is_linear_mult tm =
 (let val (l,r) = dest_mult tm
  in  if (contains_var l) then (not (contains_var r)) else true
  end
 ) handle _ => failwith "is_linear_mult";

(*---------------------------------------------------------------------------*)
(* non_presburger_subterms : term -> term list                               *)
(*                                                                           *)
(* Computes the subterms of a term that are not in the Presburger subset of  *)
(* arithmetic. All variables are included.                                   *)
(*                                                                           *)
(* The function detects multiplications in which both of the arguments are   *)
(* non-constant expressions and returns the multiplication in the list of    *)
(* non-presburger terms. This allows a formula such as:                      *)
(*                                                                           *)
(*    m < (n * p) /\ (n * p) < q ==> m < q                                   *)
(*                                                                           *)
(* to be proved by the arithmetic procedure.                                 *)
(*---------------------------------------------------------------------------*)

fun non_presburger_subterms tm =
   (non_presburger_subterms (#Body (dest_forall tm))) handle _ =>
   (non_presburger_subterms (#Body (dest_exists tm))) handle _ =>
   (non_presburger_subterms (dest_neg tm)) handle _ =>
   (non_presburger_subterms (dest_suc tm)) handle _ =>
   (non_presburger_subterms (dest_pre tm)) handle _ =>
   (if (is_conj tm) orelse (is_disj tm) orelse (is_imp tm) orelse
       (is_eq tm) orelse
       (is_less tm) orelse (is_leq tm) orelse
       (is_great tm) orelse (is_geq tm) orelse
       (is_plus tm) orelse (is_minus tm) orelse
       (is_linear_mult tm handle _ => false)
    then Lib.op_union aconv
                      (non_presburger_subterms (arg1 tm))
                      (non_presburger_subterms (arg2 tm))
    else if (is_num_const tm) then []
    else [tm]);

(*---------------------------------------------------------------------------*)
(* is_presburger : term -> bool                                              *)
(*                                                                           *)
(* Returns true if the term is a formula in the Presburger subset of natural *)
(* number arithmetic.                                                        *)
(*---------------------------------------------------------------------------*)

val num_ty = Arith_cons.num_ty
fun is_num_var tm = is_var tm andalso type_of tm = num_ty
val is_presburger = (all is_num_var) o non_presburger_subterms;


(* ----------------------------------------------------------------------
    EXPAND_NORM_MULTS_CONV : term -> thm

    expands multiplications over additions (e.g., x * (y + z) becomes
    x * y + x * z), and then normalises multiplications so that
    non-numeral multiplicands always appear in the same order, and
    grouped together, possibly with an isolated numeral coefficient.
   ---------------------------------------------------------------------- *)

fun EXPAND_NORM_MULTS_CONV tm = let
  open arithmeticTheory numSyntax Psyntax
  fun norm_mult t = let
    val ms = strip_mult t
    val _ = Int.>(length ms, 1) orelse failwith "not a mult"
    val (nums, others) = partition is_numeral ms
    val sorted_others = Listsort.sort Term.compare others
    val AC = EQT_ELIM o AC_CONV(MULT_ASSOC, MULT_COMM)
  in
    if null others then reduceLib.REDUCE_CONV
    else if null nums then
      K (AC (mk_eq(t, list_mk_mult sorted_others)))
    else
      K (AC (mk_eq(t, mk_mult(list_mk_mult nums,
                              list_mk_mult sorted_others)))) THENC
      LAND_CONV reduceLib.REDUCE_CONV
  end t
in
  PURE_REWRITE_CONV [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THENC
  ONCE_DEPTH_CONV norm_mult
end tm


(*---------------------------------------------------------------------------*)
(* ARITH_CONV : conv                                                         *)
(*                                                                           *)
(* Proof procedure for purely universal and purely existential Presburger    *)
(* natural arithmetic (only one kind of quantifier allowed when in prenex    *)
(* normal form, i.e., only `forall' or only `exists', not a mixture).        *)
(*                                                                           *)
(* The subset consists of +, * by a constant, numeric constants, numeric     *)
(* variables, <, <=, =, >=, >, ~, /\, \/, ==>, = (iff).                      *)
(* Subtraction and conditionals are allowed.                                 *)
(* SUC and PRE are allowed.                                                  *)
(* Boolean variables are not allowed.                                        *)
(* Existential formulae must have all variables quantified because any free  *)
(* variables will be taken as universally quantified which violates the      *)
(* constraint that mixed quantifiers are not allowed.                        *)
(* Substitution instances of universal formulae are also allowed.            *)
(*                                                                           *)
(* The procedure will prove many formulae in the subset of arithmetic        *)
(* specified above, but there is some incompleteness.                        *)
(*---------------------------------------------------------------------------*)


val ARITH_CONV =
 let val BOOL_SIMP_CONV = REWRITE_CONV []
     fun GEN_ARITH_CONV tm =
       (if is_exists tm
       then EXISTS_ARITH_CONV tm
       else (EXPAND_NORM_MULTS_CONV THENC
             INSTANCE_T_CONV non_presburger_subterms FORALL_ARITH_CONV) tm)
       handle e => raise (wrap_exn "Gen_arith" "ARITH_CONV" e)
 in
   SUB_AND_COND_ELIM_CONV THENC BOOL_SIMP_CONV THENC
   (fn tm => if (is_T tm) orelse (is_F tm) then ALL_CONV tm
             else (PRENEX_CONV THENC GEN_ARITH_CONV) tm)
 end;

end
