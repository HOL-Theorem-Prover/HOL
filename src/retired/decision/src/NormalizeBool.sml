(****************************************************************************)
(* FILE          : norm_bool.sml                                            *)
(* DESCRIPTION   : Functions for normalizing boolean terms.                 *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 4th March 1991                                           *)
(*                                                                          *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 5th February 1993                                        *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 20th August 1996                                         *)
(****************************************************************************)

structure NormalizeBool =
struct

local

open HolKernel Parse boolTheory Drule Psyntax Conv 
     DecisionConv DecisionSupport DecisionNormConvs ;
infix THENC
infix ORELSEC
in

fun failwith function = raise HOL_ERR{origin_structure = "NormalizeBool",
                                      origin_function = function,
                                      message = ""};

(*==========================================================================*)
(* Conditional expressions                                                  *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* COND_ABS_CONV : conv                                                     *)
(*--------------------------------------------------------------------------*)

fun COND_ABS_CONV tm =
   let val (v,body) = dest_abs tm
       val (cond,x,y) = dest_cond body
       val b = assert (not o member v o free_vars) cond
       val xf = mk_abs (v,x)
       and yf = mk_abs (v,y)
       val th1 = Rsyntax.INST_TYPE
                    [{residue = type_of v,redex = (==`:'a`==)},
                     {residue = type_of x,redex = (==`:'b`==)}] COND_ABS
       val th2 = SPECL [b,xf,yf] th1
   in  CONV_RULE
          (LEFT_CONV
              (ABS_CONV (ARGS_CONV [BETA_CONV,BETA_CONV]) THENC ALPHA_CONV v))
          th2
   end
   handle (HOL_ERR _) => failwith "COND_ABS_CONV";

(*--------------------------------------------------------------------------*)
(* COND_OUT_CONV : conv                                                     *)
(*                                                                          *)
(* This function moves out all conditionals in a term that it can. Care has *)
(* to be taken with the conditional lifting theorems because they can loop  *)
(* if they try to move a conditional past another conditional, e.g.:        *)
(*                                                                          *)
(*    b1 => x | (b2 => y | z)                                               *)
(*--------------------------------------------------------------------------*)

val COND_OUT_CONV =
   let fun op_of_app tm = op_of_app (rator tm) handle HOL_ERR _ => tm
   in  fn tm =>
          TOP_DEPTH_CONV
             (COND_RATOR_CONV ORELSEC
              (fn tm => if ((#Name (Rsyntax.dest_const (op_of_app tm)) =
                             "COND")
                            handle HOL_ERR _ => false)
                        then failwith ""
                        else COND_RAND_CONV tm) ORELSEC
              COND_ABS_CONV) tm
   end;

(*==========================================================================*)
(* Prenex Normal Form                                                       *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* is_prenex : term -> bool                                                 *)
(*                                                                          *)
(* Yields true if the term is in prenex normal form.                        *)
(*--------------------------------------------------------------------------*)

fun is_prenex tm =
   let fun contains_quant tm =
          if (is_forall tm) orelse (is_exists tm)
          then true
          else let val (f,x) = dest_comb tm
               in  (contains_quant f) orelse (contains_quant x)
               end
               handle HOL_ERR _ => (contains_quant (body tm))
               handle HOL_ERR _ => false
   in  is_prenex (#Body (Rsyntax.dest_forall tm)) handle HOL_ERR _ =>
       is_prenex (#Body (Rsyntax.dest_exists tm)) handle HOL_ERR _ =>
       not (contains_quant tm)
   end;

(*--------------------------------------------------------------------------*)
(* QUANT_EQ_IMP_CONV : conv                                                 *)
(*--------------------------------------------------------------------------*)

fun QUANT_EQ_IMP_CONV tm =
   (let val (lhs,rhs) = dest_eq tm
    in  if (is_forall lhs) orelse (is_exists lhs) orelse
           (is_forall rhs) orelse (is_exists rhs)
        then SPECL [lhs,rhs] EQ_IMP_THM
        else failwith ""
    end
   ) handle (HOL_ERR _) => failwith "QUANT_EQ_IMP_CONV";

(*--------------------------------------------------------------------------*)
(* PRENEX_CONV : conv                                                       *)
(*                                                                          *)
(* Puts a boolean term consisting of =,==>,/\,\/,~ and atoms into prenex    *)
(* normal form. Note: it expands boolean equalities into two implications.  *)
(* Could be extended to handle boolean-valued conditional expressions.      *)
(*--------------------------------------------------------------------------*)

fun PRENEX_CONV tm =
   if (is_prenex tm)
   then ALL_CONV tm
   else
   TOP_DEPTH_CONV
      (fn tm =>
          if (is_neg tm) then (NOT_FORALL_CONV ORELSEC NOT_EXISTS_CONV) tm
          else if (is_conj tm) then
             (AND_FORALL_CONV ORELSEC
              LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV ORELSEC
              AND_EXISTS_CONV ORELSEC
              LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV) tm
          else if (is_disj tm) then
             (OR_FORALL_CONV ORELSEC
              LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV ORELSEC
              OR_EXISTS_CONV ORELSEC
              LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV) tm
          else if (is_imp tm) then
             (LEFT_IMP_FORALL_CONV ORELSEC RIGHT_IMP_FORALL_CONV ORELSEC
              LEFT_IMP_EXISTS_CONV ORELSEC RIGHT_IMP_EXISTS_CONV) tm
          else if (is_bool_eq tm) then QUANT_EQ_IMP_CONV tm
          else failwith "PRENEX_CONV")
      tm;

(*==========================================================================*)
(* Conjunctive and Disjunctive Normal Forms                                 *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* TOP_LINEAR_CONV : (term -> bool) * conv -> conv                          *)
(*                                                                          *)
(* Linearizes an application of an associative operator `#' to two linear   *)
(* nested applications of `#', i.e.:                                        *)
(*                                                                          *)
(*    (x1 # x2 # ... # xn) # (y1 # y2 # ... # ym) -->                       *)
(*    x1 # x2 # ... # xn # y1 # y2 # ... # ym                               *)
(*                                                                          *)
(* The function `is_op' should discriminate applications of `#' and the     *)
(* conversion `conv' should perform the following operation:                *)
(*                                                                          *)
(*    `(x # y) # z`                                                         *)
(*    ============================                                          *)
(*    |- (x # y) # z = x # (y # z)                                          *)
(*--------------------------------------------------------------------------*)

fun TOP_LINEAR_CONV (is_op,conv) tm =
   (if ((is_op tm) andalso (is_op (arg1 tm)))
    then (conv THENC RIGHT_CONV (TRY_CONV (TOP_LINEAR_CONV (is_op,conv)))) tm
    else NO_CONV tm
   ) handle (HOL_ERR _) => failwith "TOP_LINEAR_CONV";

(*--------------------------------------------------------------------------*)
(* LEFT_LINEAR_CONV : (term -> bool) * conv -> conv                         *)
(*                                                                          *)
(* Linearizes trees constructed with an associative operator `#' by         *)
(* recursively moving subterms in the left branch of the root into a linear *)
(* (i.e. right associated) application in the right branch. Assumes the     *)
(* right branch is linear at the start. The function `is_op' should         *)
(* discriminate applications of `#' and the conversion `conv' should        *)
(* perform the following operation:                                         *)
(*                                                                          *)
(*    `(x # y) # z`                                                         *)
(*    ============================                                          *)
(*    |- (x # y) # z = x # (y # z)                                          *)
(*--------------------------------------------------------------------------*)

fun LEFT_LINEAR_CONV (is_op,conv) tm =
   (if ((is_op tm) andalso (is_op (arg1 tm)))
    then (conv THENC
          (RIGHT_CONV (TRY_CONV (LEFT_LINEAR_CONV (is_op,conv)))) THENC
          (TRY_CONV (LEFT_LINEAR_CONV (is_op,conv)))) tm
    else NO_CONV tm
   ) handle (HOL_ERR _) => failwith "LEFT_LINEAR_CONV";

(*--------------------------------------------------------------------------*)
(* LINEAR_CONV : (term -> bool) * conv -> conv                              *)
(*                                                                          *)
(* Fully linearizes arbitrary trees constructed with an associative         *)
(* operator `#'. See comments for LEFT_LINEAR_CONV.                         *)
(*--------------------------------------------------------------------------*)

fun LINEAR_CONV (is_op,conv) tm =
   (if (is_op tm)
    then (RIGHT_CONV (LINEAR_CONV (is_op,conv)) THENC
          TRY_CONV (LEFT_LINEAR_CONV (is_op,conv))) tm
    else ALL_CONV tm
   ) handle (HOL_ERR _) => failwith "LINEAR_CONV";

(*--------------------------------------------------------------------------*)
(* DISTRIBUTE_CONV : (term -> bool) * conv -> (term -> bool) * conv ->      *)
(*                   conv * conv -> bool -> conv                            *)
(*                                                                          *)
(* Recursively distributes `under' over `over' to produce two layers. The   *)
(* top layer consists of applications of `over'. The arguments of these     *)
(* applications form the bottom layer. They may be applications of `under'. *)
(* For example:                                                             *)
(*                                                                          *)
(*    (... under ... under ... under ...) over                              *)
(*    (... under ... under ... under ...) over                              *)
(*    (... under ... under ... under ...)                                   *)
(*                                                                          *)
(* The conversion arguments should be based on the following theorems:      *)
(*                                                                          *)
(*    under_conv      |- (x under y) under z = x under (y under z)          *)
(*    over_conv       |- (x over y) over z = x over (y over z)              *)
(*    left_dist_conv  |- x under (y over z) = (x under y) over (x under z)  *)
(*    right_dist_conv |- (x over y) under z = (x under z) over (y under z)  *)
(*                                                                          *)
(* If the boolean argument is true then the layers will be linear, i.e.,    *)
(* the applications of the operators are associated to the right.           *)
(*--------------------------------------------------------------------------*)

fun DISTRIBUTE_CONV (is_under,under_conv) (is_over,over_conv)
                    (left_dist_conv,right_dist_conv) linear tm =
   let val OVER_LINEAR_CONV =
          if linear
          then TRY_CONV (TOP_LINEAR_CONV (is_over,over_conv))
          else ALL_CONV
       val UNDER_LINEAR_CONV =
          if linear
          then TRY_CONV (TOP_LINEAR_CONV (is_under,under_conv))
          else ALL_CONV
       fun UNDER_DOWN_CONV tm =
          if (is_under tm) then
             (if (is_over (arg1 tm)) then
                 (right_dist_conv THENC
                  ARGS_CONV [UNDER_DOWN_CONV,
                             UNDER_DOWN_CONV THENC OVER_LINEAR_CONV]) tm
              else if (is_over (arg2 tm)) then
                 (left_dist_conv THENC BINOP_CONV UNDER_DOWN_CONV) tm
              else UNDER_LINEAR_CONV tm)
          else ALL_CONV tm
       fun DIST_CONV tm =
          if (is_under tm) then
             (if (linear andalso is_under (arg1 tm)) (* aids efficiency *)
              then (under_conv THENC DIST_CONV) tm
              else (BINOP_CONV DIST_CONV THENC UNDER_DOWN_CONV THENC
                    OVER_LINEAR_CONV) tm)
          else if (is_over tm) then
             (BINOP_CONV DIST_CONV THENC OVER_LINEAR_CONV) tm
          else ALL_CONV tm
   in  DIST_CONV tm
   end
   handle (HOL_ERR _) => failwith "DISTRIBUTE_CONV";

(*--------------------------------------------------------------------------*)
(* DISJ_NORM_FORM_CONV : bool -> conv                                       *)
(*                                                                          *)
(* Puts a term involving /\ and \/ into disjunctive normal form. Anything   *)
(* other than /\ and \/ is taken to be an atom and is not processed.        *)
(*                                                                          *)
(* If the first argument is true, the disjunction returned is linear, i.e.  *)
(* the disjunctions are associated to the right, and each disjunct is a     *)
(* linear conjunction.                                                      *)
(*--------------------------------------------------------------------------*)

val DISJ_NORM_FORM_CONV =
   DISTRIBUTE_CONV
      (is_conj,CONJ_ASSOC_NORM_CONV)
      (is_disj,DISJ_ASSOC_NORM_CONV)
      (LEFT_DISJ_NORM_CONV,RIGHT_DISJ_NORM_CONV);

(*--------------------------------------------------------------------------*)
(* CONJ_NORM_FORM_CONV : bool -> conv                                       *)
(*                                                                          *)
(* Puts a term involving /\ and \/ into conjunctive normal form. Anything   *)
(* other than /\ and \/ is taken to be an atom and is not processed.        *)
(*                                                                          *)
(* If the first argument is true, the conjunction returned is linear, i.e.  *)
(* the conjunctions are associated to the right, and each conjunct is a     *)
(* linear disjunction.                                                      *)
(*--------------------------------------------------------------------------*)

val CONJ_NORM_FORM_CONV =
   DISTRIBUTE_CONV
      (is_disj,DISJ_ASSOC_NORM_CONV)
      (is_conj,CONJ_ASSOC_NORM_CONV)
      (LEFT_CONJ_NORM_CONV,RIGHT_CONJ_NORM_CONV);

(*==========================================================================*)
(* Boolean expansion and normalization                                      *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* Possible normal forms.                                                   *)
(*--------------------------------------------------------------------------*)

datatype normal_form = Disjunctive | Conjunctive;

(*--------------------------------------------------------------------------*)
(* EXPAND_BOOL_CONV : normal_form -> conv -> conv                           *)
(*                                                                          *)
(* Moves negations down through a boolean term consisting of =,==>,/\,\/,~, *)
(* conditional expressions, universal and existential quantifiers, and      *)
(* atoms, eliminating =,==>, and conditionals as it goes. When a negation   *)
(* has reached an atom, the conversion `conv' (second argument) is applied  *)
(* to the negation of the atom. `conv' is also applied to any non-negated   *)
(* atoms encountered. The expansions are optimised for the specified normal *)
(* form (first argument) so that term expansion is reduced in later stages. *)
(*--------------------------------------------------------------------------*)

fun EXPAND_BOOL_CONV form conv tm =
   (if (is_neg tm) then
       (let val tm' = rand tm
        in  if (is_neg tm') then
               (NOT_NOT_NORM_CONV THENC
                (EXPAND_BOOL_CONV form conv)) tm
            else if (is_conj tm') then
               (NOT_CONJ_NORM_CONV THENC
                (BINOP_CONV (EXPAND_BOOL_CONV form conv))) tm
            else if (is_disj tm') then
               (NOT_DISJ_NORM_CONV THENC
                (BINOP_CONV (EXPAND_BOOL_CONV form conv))) tm
            else if (is_imp tm') then
               (NOT_IMP_NORM_CONV THENC
                (BINOP_CONV (EXPAND_BOOL_CONV form conv))) tm
            else if (is_bool_eq tm') then
               ((case form
                 of Disjunctive => NOT_EQ_DISJ_NORM_CONV
                  | Conjunctive => NOT_EQ_CONJ_NORM_CONV) THENC
                (BINOP_CONV (BINOP_CONV (EXPAND_BOOL_CONV form conv))))
               tm
            else if (is_bool_cond tm') then
               ((case form
                 of Disjunctive => NOT_COND_DISJ_NORM_CONV
                  | Conjunctive => NOT_COND_CONJ_NORM_CONV) THENC
                (BINOP_CONV (BINOP_CONV (EXPAND_BOOL_CONV form conv))))
               tm
            else if (is_forall tm') then
               (NOT_FORALL_CONV THENC
                BINDER_CONV (EXPAND_BOOL_CONV form conv)) tm
            else if (is_exists tm') then
               (NOT_EXISTS_CONV THENC
                BINDER_CONV (EXPAND_BOOL_CONV form conv)) tm
            else conv tm
        end)
    else if ((is_conj tm) orelse (is_disj tm)) then
       BINOP_CONV (EXPAND_BOOL_CONV form conv) tm
    else if (is_imp tm) then
       (IMP_NORM_CONV THENC
        (BINOP_CONV (EXPAND_BOOL_CONV form conv))) tm
    else if (is_bool_eq tm) then
       ((case form
         of Disjunctive => EQ_DISJ_NORM_CONV
          | Conjunctive => EQ_CONJ_NORM_CONV) THENC
        (BINOP_CONV (BINOP_CONV (EXPAND_BOOL_CONV form conv)))) tm
    else if (is_bool_cond tm) then
       ((case form
         of Disjunctive => COND_DISJ_NORM_CONV
          | Conjunctive => COND_CONJ_NORM_CONV) THENC
        (BINOP_CONV (BINOP_CONV (EXPAND_BOOL_CONV form conv)))) tm
    else if (is_forall tm) orelse (is_exists tm) then
       BINDER_CONV (EXPAND_BOOL_CONV form conv) tm
    else conv tm
   ) handle (HOL_ERR _) => failwith "EXPAND_BOOL_CONV";

(*--------------------------------------------------------------------------*)
(* BINDERS_OUT_CONV : conv                                                  *)
(*                                                                          *)
(* Pulls universal and existential quantifiers out through conjunctions and *)
(* disjunctions.                                                            *)
(*--------------------------------------------------------------------------*)

fun BINDERS_OUT_CONV tm =
   let fun CONJ_DOWN_CONV tm =
          (((AND_FORALL_CONV ORELSEC
             LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV ORELSEC
             AND_EXISTS_CONV ORELSEC
             LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV) THENC
            BINDER_CONV CONJ_DOWN_CONV) ORELSEC
           ALL_CONV) tm
       fun DISJ_DOWN_CONV tm =
          (((OR_FORALL_CONV ORELSEC
             LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV ORELSEC
             OR_EXISTS_CONV ORELSEC
             LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV) THENC
            BINDER_CONV DISJ_DOWN_CONV) ORELSEC
           ALL_CONV) tm
       fun OUT_CONV tm =
          if (is_forall tm) orelse (is_exists tm) then
             BINDER_CONV BINDERS_OUT_CONV tm
          else if (is_conj tm) then
             (BINOP_CONV BINDERS_OUT_CONV THENC CONJ_DOWN_CONV) tm
          else if (is_disj tm) then
             (BINOP_CONV BINDERS_OUT_CONV THENC DISJ_DOWN_CONV) tm
          else ALL_CONV tm
   in  OUT_CONV tm
   end
   handle (HOL_ERR _) => failwith "BINDERS_OUT_CONV";

(*--------------------------------------------------------------------------*)
(* NORMALIZE_BOOL_CONV : bool -> normal_form -> bool -> conv -> conv        *)
(*                                                                          *)
(* Puts a boolean term consisting of =,==>,/\,\/,~, conditional expressions *)
(* and atoms (and universal and existential quantifiers if the first        *)
(* argument is true) into either disjunctive or conjunctive normal form as  *)
(* specified by the second argument. If the first argument is true, the     *)
(* result will also be in prenex normal form. If the third argument is      *)
(* true, the operator applications will be associated to the right. The     *)
(* atoms are processed by the conversion supplied as the fourth argument.   *)
(*--------------------------------------------------------------------------*)

fun NORMALIZE_BOOL_CONV prenex form linear conv tm =
   (EXPAND_BOOL_CONV form conv THENC
    (if prenex then BINDERS_OUT_CONV else ALL_CONV) THENC
    DEPTH_BINDER_CONV
       (case form
        of Disjunctive => DISJ_NORM_FORM_CONV linear
         | Conjunctive => CONJ_NORM_FORM_CONV linear))
   tm;

end;

end; (* NormalizeBool *)
