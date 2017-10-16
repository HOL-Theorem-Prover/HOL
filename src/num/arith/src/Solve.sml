(*****************************************************************************)
(* FILE          : solve.sml                                                 *)
(* DESCRIPTION   : Functions for solving arithmetic formulae.                *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 19th April 1991                                           *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 15th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Solve :> Solve =
struct
  open Arbint HolKernel boolLib;
  open Arith_cons Term_coeffs RJBConv Theorems Thm_convs
       Norm_arith Norm_ineqs Solve_ineqs;

infix THENC;

fun failwith function = raise (mk_HOL_ERR "Solve" function  "")


(*---------------------------------------------------------------------------*)
(* INEQS_FALSE_CONV : conv                                                   *)
(*                                                                           *)
(* Proves a conjunction of normalized inequalities is false, provided they   *)
(* are unsatisfiable. Checks for any inequalities that can immediately be    *)
(* shown to be false before calling VAR_ELIM.                                *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    INEQS_FALSE_CONV                                                       *)
(*       `((2 + (2 * n)) <= (1 * m)) /\                                      *)
(*        ((1 * m) <= (1 * n)) /\                                            *)
(*        (0 <= (1 * n)) /\                                                  *)
(*        (0 <= (1 * m))`                                                    *)
(*    --->                                                                   *)
(*    |- (2 + (2 * n)) <= (1 * m) /\                                         *)
(*       (1 * m) <= (1 * n) /\                                               *)
(*       0 <= (1 * n) /\                                                     *)
(*       0 <= (1 * m) =                                                      *)
(*       F                                                                   *)
(*---------------------------------------------------------------------------*)

fun INEQS_FALSE_CONV tm =
 let val ineqs = strip_conj tm
     val rev_ineqs = rev ineqs
     val coeffsl = map coeffs_of_leq ineqs
     val falses =
         filter (fn (const,bind) => (null bind) andalso (const < zero)) coeffsl
     val th =
         if null falses
         then let val var_names = Lib.mk_set(map fst(flatten(map snd coeffsl)))
                  val coeffsl' =
                     (map (fn v => (zero, [(v,one)])) var_names) @ coeffsl
                  val (_,f) = VAR_ELIM coeffsl'
                  val axioms =
                     map (fn v => SPEC (mk_num_var v) ZERO_LESS_EQ_ONE_TIMES)
                                                                     var_names
              in  itlist PROVE_HYP axioms (f ())
              end
         else ASSUME (build_leq (hd falses))
     val th' = CONV_RULE LEQ_CONV th
     val th'' = DISCH (hd rev_ineqs) th'
     fun conj_disch tm th = CONV_RULE IMP_IMP_CONJ_IMP_CONV (DISCH tm th)
     val th''' = itlist conj_disch (rev (tl rev_ineqs)) th''
  in
      CONV_RULE IMP_F_EQ_F_CONV th'''
  end
  handle HOL_ERR _ => failwith "INEQS_FALSE_CONV";

(*---------------------------------------------------------------------------*)
(* DISJ_INEQS_FALSE_CONV : conv                                              *)
(*                                                                           *)
(* Proves a disjunction of conjunctions of normalized inequalities is false, *)
(* provided each conjunction is unsatisfiable.                               *)
(*---------------------------------------------------------------------------*)

fun DISJ_INEQS_FALSE_CONV tm =
 (if is_disj tm
  then ((RATOR_CONV (RAND_CONV INEQS_FALSE_CONV)) THENC
        OR_F_CONV THENC
        DISJ_INEQS_FALSE_CONV) tm
  else INEQS_FALSE_CONV tm
 ) handle (HOL_ERR _) => failwith "DISJ_INEQS_FALSE_CONV";

(*---------------------------------------------------------------------------*)
(* NOT_NOT_INTRO_CONV : conv                                                 *)
(*                                                                           *)
(* `b`  --->  |- b = ~~b  provided b is of type ":bool".                     *)
(*---------------------------------------------------------------------------*)

fun NOT_NOT_INTRO_CONV tm =
 (SYM ((NOT_NOT_NORM_CONV o mk_neg o mk_neg) tm)
 ) handle (HOL_ERR _) => failwith "NOT_NOT_INTRO_CONV";

(*---------------------------------------------------------------------------*)
(* Discriminator functions for T (true) and F (false)                        *)
(*---------------------------------------------------------------------------*)

val is_T = aconv T
and is_F = aconv F

(*---------------------------------------------------------------------------*)
(* NEGATE_CONV : conv -> conv                                                *)
(*                                                                           *)
(* Function for negating the operation of a conversion that proves a formula *)
(* to be either true or false. For example if `conv' proves `0 <= n` to be   *)
(* equal to `T` then `NEGATE_CONV conv' will prove `~(0 <= n)` to be `F`.    *)
(* The function fails if the application of `conv' to the negation of the    *)
(* formula does not yield either `T` or `F`.                                 *)
(*                                                                           *)
(* If use of this function succeeds then the input term will necessarily     *)
(* have been changed. Hence it does not need to be a CONV. It can however    *)
(* take a CONV as its argument.                                              *)
(*---------------------------------------------------------------------------*)

val neg_tm = boolSyntax.negation

fun NEGATE_CONV conv tm =
 let val neg = is_neg tm
     val th = RULE_OF_CONV conv (if neg then (dest_neg tm) else (mk_neg tm))
     val r = rhs (concl th)
     val truth_th =
        if is_T r then NOT_T_F else
        if is_F r then NOT_F_T else failwith "NEGATE_CONV"
     val neg_fn = if neg then I else TRANS (NOT_NOT_INTRO_CONV tm)
 in  neg_fn (TRANS (AP_TERM neg_tm th) truth_th)
 end;

(*---------------------------------------------------------------------------*)
(* DEPTH_FORALL_CONV : conv -> conv                                          *)
(*                                                                           *)
(* DEPTH_FORALL_CONV conv `!x1 ... xn. body` applies conv to `body` and      *)
(* returns a theorem of the form:                                            *)
(*                                                                           *)
(*    |- (!x1 ... xn. body) = (!x1 ... xn. body')                            *)
(*---------------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm =
   if is_forall tm
   then RAND_CONV (ABS_CONV (DEPTH_FORALL_CONV conv)) tm
   else conv tm;

(*---------------------------------------------------------------------------*)
(* FORALL_ARITH_CONV : conv                                                  *)
(*                                                                           *)
(* Proof procedure for non-existential Presburger natural arithmetic         *)
(* (+, * by a constant, numeric constants, numeric variables, <, <=, =, >=,  *)
(* >, ~, /\, \/, ==>, = (iff), ! (when in prenex normal form).               *)
(* Expects formula in prenex normal form.                                    *)
(* Subtraction, PRE and conditionals must have been eliminated.              *)
(* SUC is allowed.                                                           *)
(* Boolean variables and constants are not allowed.                          *)
(*                                                                           *)
(* The procedure will prove most formulae in the subset of arithmetic        *)
(* specified above, but there is some incompleteness. However, this rarely   *)
(* manifests itself in practice. It is therefore likely that if the          *)
(* procedure cannot prove a formula in the subset, the formula is not valid. *)
(*---------------------------------------------------------------------------*)

fun FORALL_ARITH_CONV tm =
 (reset_multiplication_theorems ();
  RULE_OF_CONV
  (DEPTH_FORALL_CONV
    (NEGATE_CONV
      ((fn tm => ARITH_FORM_NORM_CONV tm
                 handle HOL_ERR _ =>
                 raise HOL_ERR{origin_structure = "Solve",
                               origin_function = "FORALL_ARITH_CONV",
                               message = "formula not in the allowed subset"}
       ) THENC
       (fn tm => DISJ_INEQS_FALSE_CONV tm
                 handle HOL_ERR _ =>
                 raise HOL_ERR{origin_structure = "Solve",
                               origin_function = "FORALL_ARITH_CONV",
                               message = "cannot prove formula"}
       ))) THENC
   REPEATC FORALL_SIMP_CONV)
  tm
 );

end
