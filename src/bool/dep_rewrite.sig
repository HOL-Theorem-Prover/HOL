(* ===================================================================== *)
(* FILE          : dep_rewrite.sig                                       *)
(* VERSION       : 1.1                                                   *)
(* DESCRIPTION   : Dependent Rewriting Tactics (general purpose)         *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : May 7, 2002                                           *)
(* COPYRIGHT     : Copyright (c) 2002 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

(* ================================================================== *)
(* ================================================================== *)
(*                     DEPENDENT REWRITING TACTICS                    *)
(* ================================================================== *)
(* ================================================================== *)
(*                                                                    *)
(* This file contains new tactics for dependent rewriting,            *)
(* a generalization of the rewriting tactics of standard HOL.         *)
(*                                                                    *)
(* The main tactics are named DEP_REWRITE_TAC[thm1,...], etc., with   *)
(* the standard variations (PURE,ONCE,ASM).  In addition, tactics     *)
(* with LIST instead of ONCE are provided, making 12 tactics in all.  *)
(*                                                                    *)
(* The argument theorems thm1,... are typically implications.         *)
(* These tactics identify the consequents of the argument theorems,   *)
(* and attempt to match these against the current goal.  If a match   *)
(* is found, the goal is rewritten according to the matched instance  *)
(* of the consequent, after which the corresponding hypotheses of     *)
(* the argument theorems are added to the goal as new conjuncts on    *)
(* the left.                                                          *)
(*                                                                    *)
(* Care needs to be taken that the implications will match the goal   *)
(* properly, that is, instances where the hypotheses in fact can be   *)
(* proven.  Also, even more commonly than with REWRITE_TAC,           *)
(* the rewriting process may diverge.                                 *)
(*                                                                    *)
(* Each implication theorem for rewriting may have a number of layers *)
(* of universal quantification and implications.  At the bottom of    *)
(* these layers is the base, which will either be an equality, a      *)
(* negation, or a general term.  The pattern for matching will be     *)
(* the left-hand-side of an equality, the term negated of a negation, *)
(* or the term itself in the third case.  The search is top-to-bottom,*)
(* left-to-right, depending on the quantifications of variables.      *)
(*                                                                    *)
(* To assist in focusing the matching to useful cases, the goal is    *)
(* searched for a subterm matching the pattern.  The matching of the  *)
(* pattern to subterms is performed by higher-order matching, so for  *)
(* example, ``!x. P x`` will match the term ``!n. (n+m) < 4*n``.      *)
(*                                                                    *)
(* The argument theorems may each be either an implication or not.    *)
(* For those which are implications, the hypotheses of the instance   *)
(* of each theorem which matched the goal are added to the goal as    *)
(* conjuncts on the left side.  For those argument theorems which     *)
(* are not implications, the goal is simply rewritten with them.      *)
(* This rewriting is also higher order.                               *)
(*                                                                    *)
(* Deep inner universal quantifications of consequents are supported. *)
(* Thus, an argument theorem like EQ_LIST:                            *)
(* |- !h1 h2. (h1 = h2) ==> (!l1 l2. (l1 = l2) ==>                    *)
(*                  (CONS h1 l1 = CONS h2 l2))                        *)
(* before it is used, is internally converted to appear as            *)
(* |- !h1 h2 l1 l2. (h1 = h2) /\ (l1 = l2) ==>                        *)
(*                  (CONS h1 l1 = CONS h2 l2)                         *)
(*                                                                    *)
(* As much as possible, the newly added hypotheses are analyzed to    *)
(* remove duplicates; thus, several theorems with the same            *)
(* hypothesis, or several uses of the same theorem, will generate     *)
(* a minimal additional proof burden.                                 *)
(*                                                                    *)
(* The new hypotheses are added as conjuncts rather than as a         *)
(* separate subgoal to reduce the user's burden of subgoal splits     *)
(* when creating tactics to prove theorems.  If a separate subgoal    *)
(* is desired, simply use CONJ_TAC after the dependent rewriting to   *)
(* split the goal into two, where the first contains the hypotheses   *)
(* and the second contains the rewritten version of the original      *)
(* goal.                                                              *)
(*                                                                    *)
(* The tactics including PURE in their name will only use the         *)
(* listed theorems for all rewriting; otherwise, the standard         *)
(* rewrites are used for normal rewriting, but they are not           *)
(* considered for dependent rewriting.                                *)
(*                                                                    *)
(* The tactics including ONCE in their name attempt to use each       *)
(* theorem in the list, only once, in order, left to right.           *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* not rewritten by the ONCE tactics.  This gives a more restrained   *)
(* version of dependent rewriting.                                    *)
(*                                                                    *)
(* The tactics with LIST take a list of lists of theorems, and        *)
(* uses each list of theorems once in order, left-to-right.  For      *)
(* each list of theorems, the goal is rewritten as much as possible,  *)
(* until no further changes can be achieved in the goal.  Hypotheses  *)
(* are collected from all rewriting and added to the goal, but they   *)
(* are not themselves rewritten.                                      *)
(*                                                                    *)
(* The tactics without ONCE or LIST attempt to reuse all theorems     *)
(* repeatedly, continuing to rewrite until no changes can be          *)
(* achieved in the goal.  Hypotheses are rewritten as well, and       *)
(* their hypotheses as well, ad infinitum.                            *)
(*                                                                    *)
(* The tactics with ASM in their name add the assumption list to      *)
(* the list of theorems used for dependent rewriting.                 *)
(*                                                                    *)
(* There are also three more general tactics provided,                *)
(* DEP_FIND_THEN, DEP_ONCE_FIND_THEN, and DEP_LIST_FIND_THEN,         *)
(* from which the others are constructed.                             *)
(*                                                                    *)
(* The differences among these is that DEP_ONCE_FIND_THEN uses        *)
(* each of its theorems only once, in order left-to-right as given,   *)
(* whereas DEP_FIND_THEN continues to reuse its theorems repeatedly   *)
(* as long as forward progress and change is possible.  In contrast   *)
(* to the others, DEP_LIST_FIND_THEN takes as its argument a list     *)
(* of lists of theorems, and processes these in order, left-to-right. *)
(* For each list of theorems, the goal is rewritten as many times     *)
(* as they apply.  The hypotheses for all these rewritings are        *)
(* collected into one set, added to the goal after all rewritings.    *)
(*                                                                    *)
(* DEP_ONCE_FIND_THEN and DEP_LIST_FIND_THEN will not attack the      *)
(* hypotheses generated as a byproduct of the dependent rewriting;    *)
(* in contrast, DEP_FIND_THEN will.  DEP_ONCE_FIND_THEN and           *)
(* DEP_LIST_FIND_THEN might be fruitfully applied again to their      *)
(* results; DEP_FIND_THEN will complete any possible rewriting,       *)
(* and need not be reapplied.                                         *)
(*                                                                    *)
(* These take as argument a thm_tactic, a function which takes a      *)
(* theorem and yields a tactic.  It is this which is used to apply    *)
(* the instantiated consequent of each successfully matched           *)
(* implication to the current goal.  Usually this is something like   *)
(* (fn th => REWRITE_TAC[th]), but the user is free to supply any     *)
(* thm_tactic he wishes.                                              *)
(*                                                                    *)
(* One significant note: because of the strategy of adding new        *)
(* hypotheses as conjuncts to the current goal, it is not fruitful    *)
(* to add *any* new assumptions to the current goal, as one might     *)
(* think would happen from using, say, ASSUME_TAC.                    *)
(*                                                                    *)
(* Rather, any such new assumptions introduced by thm_tactic are      *)
(* specifically removed.  Instead, one might wish to try MP_TAC,      *)
(* which will have the effect of ASSUME_TAC and then undischarging    *)
(* that assumption to become an antecedent of the goal.  Other        *)
(* thm_tactics may be used, and they may even convert the single      *)
(* current subgoal into multiple subgoals.  If this happens, it is    *)
(* fine, but note that the control strategy of DEP_FIND_THEN will     *)
(* continue to attack only the first of the multiple subgoals.        *)
(*                                                                    *)
(* ================================================================== *)
(* ================================================================== *)

signature dep_rewrite =
sig
type term = Term.term
type fixity = Parse.fixity
type thm = Thm.thm
type tactic  = Abbrev.tactic
type conv = Abbrev.conv
type thm_tactic = Abbrev.thm_tactic


(* ================================================================== *)
(*                                                                    *)
(* The show_rewrites global flag determines whether information is    *)
(* printed showing the details of the process of matching and         *)
(* applying implication theorems against the current goal.  The       *)
(* flag causes the following to be displayed:                         *)
(*                                                                    *)
(*   - Each implication theorem which is tried for matches against    *)
(*       the current goal,                                            *)
(*   - When a match is found, the matched version of the rewriting    *)
(*       rule (just the base, not the hypotheses),                    *)
(*   - The new burden of hypotheses justifying the matched rewrite,   *)
(*   - The revised goal after the rewrite.                            *)
(*                                                                    *)
(* ================================================================== *)

val show_rewrites : bool ref


(* ================================================================== *)
(*                                                                    *)
(* The tactics including ONCE in their name attempt to use each       *)
(* theorem in the list, only once, in order, left to right.           *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* not rewritten by the ONCE tactics.  This gives the most fine-grain *)
(* control of dependent rewriting.                                    *)
(*                                                                    *)
(* ================================================================== *)

val DEP_ONCE_FIND_THEN : thm_tactic -> thm list -> tactic

val DEP_PURE_ONCE_REWRITE_TAC : thm list -> tactic
val DEP_ONCE_REWRITE_TAC : thm list -> tactic
val DEP_PURE_ONCE_ASM_REWRITE_TAC : thm list -> tactic
val DEP_ONCE_ASM_REWRITE_TAC : thm list -> tactic

val DEP_PURE_ONCE_SUBST_TAC : thm list -> tactic
val DEP_ONCE_SUBST_TAC : thm list -> tactic
val DEP_PURE_ONCE_ASM_SUBST_TAC : thm list -> tactic
val DEP_ONCE_ASM_SUBST_TAC : thm list -> tactic


(* ================================================================== *)
(*                                                                    *)
(* The tactics including LIST in their name take a list of lists of   *)
(* implication theorems, and attempt to use each list of theorems     *)
(* once, in order, left to right.  Each list of theorems is applied   *)
(* by rewriting with each theorem in it as many times as they apply.  *)
(* The hypotheses added in the process of dependent rewriting are     *)
(* collected from all rewritings, but they are not rewritten by the   *)
(* LIST tactics.  This gives a moderate and more controlled degree    *)
(* of dependent rewriting than provided by DEP_REWRITE_TAC.           *)
(*                                                                    *)
(* ================================================================== *)

val DEP_LIST_FIND_THEN : thm_tactic -> thm list list -> tactic

val DEP_PURE_LIST_REWRITE_TAC : thm list list -> tactic
val DEP_LIST_REWRITE_TAC : thm list list -> tactic
val DEP_PURE_LIST_ASM_REWRITE_TAC : thm list list -> tactic
val DEP_LIST_ASM_REWRITE_TAC : thm list list -> tactic


(* ================================================================== *)
(*                                                                    *)
(* The tactics without ONCE attept to reuse all theorems until no     *)
(* changes can be achieved in the goal.  Hypotheses are rewritten     *)
(* and new ones generated from them, continuing until no further      *)
(* progress is possible.                                              *)
(*                                                                    *)
(* ================================================================== *)

val DEP_FIND_THEN : thm_tactic -> thm list ->  tactic

val DEP_PURE_REWRITE_TAC : thm list -> tactic
val DEP_REWRITE_TAC : thm list -> tactic
val DEP_PURE_ASM_REWRITE_TAC : thm list -> tactic
val DEP_ASM_REWRITE_TAC : thm list -> tactic


end;

(* ================================================================== *)
(* ================================================================== *)
(*                 END OF DEPENDENT REWRITING TACTICS                 *)
(* ================================================================== *)
(* ================================================================== *)

