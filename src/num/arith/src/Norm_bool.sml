(*****************************************************************************)
(* FILE          : norm_bool.sml                                             *)
(* DESCRIPTION   : Functions for normalizing Boolean terms.                  *)
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

structure Norm_bool :> Norm_bool =
struct

open Arbint HolKernel boolSyntax Arith_cons Thm_convs RJBConv;

infix THENC;

fun failwith function = raise (mk_HOL_ERR "Norm_bool" function "");

(*===========================================================================*)
(* Conversions for normalizing Boolean terms                                 *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* EQ_IMP_ELIM_CONV : (term -> bool) -> conv                                 *)
(*                                                                           *)
(* Eliminates Boolean equalities and implications from terms consisting of   *)
(* =,==>,/\,\/,~ and atoms. The atoms are specified by the predicate that    *)
(* the conversion takes as its first argument.                               *)
(*---------------------------------------------------------------------------*)

fun EQ_IMP_ELIM_CONV is_atom tm =
 (if is_atom tm then ALL_CONV tm else 
  if is_neg tm then RAND_CONV (EQ_IMP_ELIM_CONV is_atom) tm else 
  if is_eq tm then (ARGS_CONV (EQ_IMP_ELIM_CONV is_atom) 
                    THENC EQ_EXPAND_CONV) tm else 
  if is_imp tm then (ARGS_CONV (EQ_IMP_ELIM_CONV is_atom) 
                     THENC IMP_EXPAND_CONV) tm
  else ARGS_CONV (EQ_IMP_ELIM_CONV is_atom) tm)
  handle HOL_ERR _ => failwith "EQ_IMP_ELIM_CONV";

(*---------------------------------------------------------------------------*)
(* MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv                       *)
(*                                                                           *)
(* Moves negations down through a term consisting of /\,\/,~ and atoms. The  *)
(* atoms are specified by a predicate (first argument). When a negation has  *)
(* reached an atom, the conversion `conv' (second argument) is applied to    *)
(* the negation of the atom. `conv' is also applied to any non-negated       *)
(* atoms encountered.                                                        *)
(*---------------------------------------------------------------------------*)

fun MOVE_NOT_DOWN_CONV is_atom conv tm =
 (if is_atom tm then conv tm else 
  if is_neg tm then
     (let val tm' = rand tm
      in if is_atom tm' then conv tm else 
         if is_neg tm'  then (NOT_NOT_NORM_CONV THENC
                               (MOVE_NOT_DOWN_CONV is_atom conv)) tm else 
         if is_conj tm' then (NOT_CONJ_NORM_CONV THENC
                      (ARGS_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) tm else 
         if is_disj tm' then
                 (NOT_DISJ_NORM_CONV THENC
                   ARGS_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) tm
         else failwith "fail"
      end)
  else if is_conj tm orelse is_disj tm then
     (ARGS_CONV (MOVE_NOT_DOWN_CONV is_atom conv) tm)
  else failwith "fail"
 ) handle (HOL_ERR _) => failwith "MOVE_NOT_DOWN_CONV";

(*---------------------------------------------------------------------------*)
(* DISJ_LINEAR_CONV : conv                                                   *)
(*                                                                           *)
(* Linearizes disjuncts using the following conversion applied recursively:  *)
(*                                                                           *)
(*    "(x \/ y) \/ z"                                                        *)
(*    ================================                                       *)
(*    |- (x \/ y) \/ z = x \/ (y \/ z)                                       *)
(*---------------------------------------------------------------------------*)

fun DISJ_LINEAR_CONV tm =
 (if ((is_disj tm) andalso (is_disj (arg1 tm)))
  then (DISJ_ASSOC_NORM_CONV THENC
        (RAND_CONV (TRY_CONV DISJ_LINEAR_CONV)) THENC
        (TRY_CONV DISJ_LINEAR_CONV)) tm
  else failwith "fail"
 ) handle (HOL_ERR _) => failwith "DISJ_LINEAR_CONV";

(*---------------------------------------------------------------------------*)
(* DISJ_NORM_FORM_CONV : conv                                                *)
(*                                                                           *)
(* Puts a term involving /\ and \/ into disjunctive normal form. Anything    *)
(* other than /\ and \/ is taken to be an atom and is not processed.         *)
(*                                                                           *)
(* The disjunction returned is linear, i.e. the disjunctions are associated  *)
(* to the right. Each disjunct is a linear conjunction.                      *)
(*---------------------------------------------------------------------------*)

fun DISJ_NORM_FORM_CONV tm =
 (if (is_conj tm) then
     (if (is_disj (arg1 tm)) then
         ((RATOR_CONV (RAND_CONV (ARGS_CONV DISJ_NORM_FORM_CONV))) THENC
          (RAND_CONV DISJ_NORM_FORM_CONV) THENC
          RIGHT_DIST_NORM_CONV THENC
          (ARGS_CONV DISJ_NORM_FORM_CONV) THENC
          (TRY_CONV DISJ_LINEAR_CONV)) tm
      else if (is_disj (arg2 tm)) then
         ((RATOR_CONV (RAND_CONV DISJ_NORM_FORM_CONV)) THENC
          (RAND_CONV (ARGS_CONV DISJ_NORM_FORM_CONV)) THENC
          LEFT_DIST_NORM_CONV THENC
          (ARGS_CONV DISJ_NORM_FORM_CONV) THENC
          (TRY_CONV DISJ_LINEAR_CONV)) tm
      else if (is_conj (arg1 tm)) then
         (CONJ_ASSOC_NORM_CONV THENC DISJ_NORM_FORM_CONV) tm
      else ((RAND_CONV DISJ_NORM_FORM_CONV) THENC
            (fn tm' => if (is_disj (arg2 tm'))
                       then DISJ_NORM_FORM_CONV tm'
                       else ALL_CONV tm')) tm)
  else if (is_disj tm) then
     ((ARGS_CONV DISJ_NORM_FORM_CONV) THENC
      (TRY_CONV DISJ_LINEAR_CONV)) tm
  else ALL_CONV tm
 ) handle (HOL_ERR _) => failwith "DISJ_NORM_FORM_CONV";

end
