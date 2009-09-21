(* ===================================================================== *)
(* FILE          : hol88Lib.sml                                          *)
(* DESCRIPTION   : Routines that provide some compatibility with hol88.  *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)

structure hol88Lib :> hol88Lib =
struct

open Lib Abbrev

fun HOL88_ERR {function, message} =
 Feedback.HOL_ERR {origin_structure = "hol88Lib",
                   origin_function = function,
                   message = message}

infix ##

type ('a,'b)hol88subst = ('b * 'a) list

fun pair2recd (M,v) = {redex=v, residue=M}
fun recd2pair {redex, residue} = (residue, redex)

fun hol88subst_of s = map recd2pair s
fun subst_of s = map pair2recd s

fun match_type ty     = hol88subst_of o Type.match_type ty
val subst             = Term.subst o subst_of
val inst              = Term.inst o subst_of
fun match_term pat ob = (hol88subst_of ## hol88subst_of)
                          (Term.match_term pat ob)

fun SUBST s template th = Thm.SUBST (subst_of s) template th
val INST                = Thm.INST o subst_of
val INST_TYPE           = Thm.INST_TYPE o subst_of
val INST_TY_TERM        = Drule.INST_TY_TERM o (subst_of ## subst_of)

val match = match_term

fun assoc i alist =
   case Lib.assoc1 i alist
     of NONE => raise HOL88_ERR {function = "assoc", message = ""}
      | (SOME x) => x

fun rev_assoc i alist =
   case Lib.assoc2 i alist
     of NONE => raise HOL88_ERR {function = "rev_assoc", message = ""}
      | (SOME x) => x

val frees = rev o Term.free_vars
val freesl = rev o Term.free_varsl

fun GEN_ALL th =
  Lib.itlist Thm.GEN
    (Lib.set_diff (frees (Thm.concl th)) (freesl (Thm.hyp th))) th

fun GEN_REWRITE_RULE F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_RULE F
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2

fun GEN_REWRITE_TAC F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_TAC F
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2

fun variant L tm =
   if Term.is_var tm
   then Term.variant L tm
   else if Term.is_const tm
        then Term.variant L (Term.mk_var (Term.dest_const tm))
        else raise HOL88_ERR {function = "variant",
                               message = "not a variable or a constant"}

end
