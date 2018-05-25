(*
 * Formalized Lambek Calculus in Higher Order Logic (HOL4)
 *
 *  (based on https://github.com/coq-contribs/lambek)
 *
 * Copyright 2002-2003  Houda ANOUN and Pierre Casteran, LaBRI/INRIA.
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 *)

(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory listTheory arithmeticTheory integerTheory;
open relationTheory;

local
    val PAT_X_ASSUM = PAT_ASSUM;
    val qpat_x_assum = Q.PAT_ASSUM;
    open Tactical
in
    (* Backward compatibility with Kananaskis 11 *)
    val PAT_X_ASSUM = PAT_X_ASSUM;
    val qpat_x_assum = qpat_x_assum;

    (* Tacticals for better expressivity *)
    fun fix  ts = MAP_EVERY Q.X_GEN_TAC ts;	(* from HOL Light *)
    fun set  ts = MAP_EVERY Q.ABBREV_TAC ts;	(* from HOL mizar mode *)
    fun take ts = MAP_EVERY Q.EXISTS_TAC ts;	(* from HOL mizar mode *)
end;

val _ = new_theory "Lambek";

(******************************************************************************)
(*                                                                            *)
(*                              Module: Form                                  *)
(*                                                                            *)
(******************************************************************************)

val _ = Datatype `Form = At 'a | Slash Form Form | Backslash Form Form | Dot Form Form`;

val _ = overload_on ("*", ``Dot``); (* \HOLTokenProd *)
val _ = overload_on ("/", ``Slash``);
val _ = overload_on ("\\\\", ``Backslash``);
val _ = set_fixity "\\\\" (Infixr 1500);
val _ = TeX_notation { hol = "\\\\", TeX = ("\\HOLTokenBackslash", 1) };

val Form_induction = TypeBase.induction_of ``:'a Form``;
val Form_nchotomy  = TypeBase.nchotomy_of ``:'a Form``;
val Form_distinct  = TypeBase.distinct_of ``:'a Form``;
val Form_distinct' = save_thm ("Form_distinct'", GSYM Form_distinct);
val Form_11        = TypeBase.one_one_of ``:'a Form``;

val _ = type_abbrev ("arrow_extension", ``:'a Form -> 'a Form -> bool``);

(* Rules of Lambek's "Syntactic Calculus" (non-associative + extension) *)
val (arrow_rules, arrow_ind, arrow_cases) = Hol_reln `
    (!X A. arrow X A A) /\						(* one *)
    (!X A B C. arrow X (Dot A B) C ==> arrow X A (Slash C B)) /\	(* beta *)
    (!X A B C. arrow X A (Slash C B) ==> arrow X (Dot A B) C) /\	(* beta' *)
    (!X A B C. arrow X (Dot A B) C ==> arrow X B (Backslash A C)) /\	(* gamma *)
    (!X A B C. arrow X B (Backslash A C) ==> arrow X (Dot A B) C) /\	(* gamma' *)
    (!X A B C. arrow X A B /\ arrow X B C ==> arrow X A C) /\		(* comp *)
    (!(X :'a arrow_extension) A B. X A B ==> arrow X A B) `;		(* arrow_plus *)

val [one, beta, beta', gamma, gamma', comp, arrow_plus] =
    map save_thm
        (combine (["one", "beta", "beta'", "gamma", "gamma'", "comp", "arrow_plus"],
		  CONJUNCTS arrow_rules));

val beta_EQ = store_thm ("beta_EQ",
  ``!X A B C. arrow X A (Slash C B) = arrow X (Dot A B) C``,
    REPEAT STRIP_TAC
 >> EQ_TAC
 >| [ REWRITE_TAC [beta'],
      REWRITE_TAC [beta] ]);

val gamma_EQ = store_thm ("gamma_EQ",
  ``!X A B C. arrow X B (Backslash A C) = arrow X (Dot A B) C``,
    REPEAT STRIP_TAC
 >> EQ_TAC
 >| [ REWRITE_TAC [gamma'],
      REWRITE_TAC [gamma] ]);

val arrow_transitive = store_thm (
   "arrow_transitive", ``!X. transitive (arrow X)``,
   REWRITE_TAC [transitive_def, comp]);

val arrow_reflexive = store_thm (
   "arrow_reflexive", ``!X. reflexive (arrow X)``,
   REWRITE_TAC [reflexive_def, one]);

(** The arrow relationship and its extensions (like associativity, commutativity  etc.) **)

val _ = overload_on("add_extension", ``relation$RUNION``);
(* X extends (to) X', or X is extended to X' *)
val _ = overload_on("extends", ``relation$RSUBSET``);

val no_extend = store_thm ("no_extend", ``!X. extends X X``,
    RW_TAC bool_ss [RSUBSET]);

val add_extend_l = store_thm ("add_extend_l", ``!X X'. extends X (add_extension X X')``,
    RW_TAC bool_ss [RSUBSET, RUNION]);

val add_extend_r = store_thm ("add_extend_r", ``!X X'. extends X' (add_extension X X')``,
    RW_TAC bool_ss [RSUBSET, RUNION]);

val extends_trans = store_thm ("extends_trans",
  ``!X Y Z. extends X Y /\ extends Y Z ==> extends X Z``,
    RW_TAC bool_ss [RSUBSET]);

val extends_transitive = store_thm (
   "extends_transitive", ``transitive extends``,
    REWRITE_TAC [transitive_def, extends_trans]);

(** most popular extensions **)

val NL_def = Define `(NL :'a arrow_extension) = EMPTY_REL`;

(* L is defined by two rules, and it's reflexitive *)
val (L_rules, L_ind, L_cases) = Hol_reln `
    (!A B C. L (Dot A (Dot B C)) (Dot (Dot A B) C)) /\
    (!A B C. L (Dot (Dot A B) C) (Dot A (Dot B C)))`;

val [L_rule_rl, L_rule_lr] =
    map save_thm (combine (["L_rule_rl", "L_rule_lr"], CONJUNCTS L_rules));

(* NLP is defined by only one rule, it's reflexitive too. *)
val (NLP_rules, NLP_ind, NLP_cases) = Hol_reln `
    (!A B. NLP (Dot A B) (Dot B A))`;

val LP_def = Define `LP = add_extension NLP L`;

val NLextendsAll = store_thm (
   "NLextendsAll", ``!X. extends NL X``,
    RW_TAC bool_ss [NL_def, EMPTY_REL_DEF, RSUBSET]);

val NLPextendsLP = store_thm ("NLPextendsLP", ``extends NLP LP``,
    REWRITE_TAC [LP_def, add_extend_l]);

val LextendsLP = store_thm ("LextendsLP", ``extends L LP``,
    REWRITE_TAC [LP_def, add_extend_r]);

(* Some derived rules for arrow.
   Note: all theorems here can be simply proved by PROVE_TAC [arrow_rules]. *)

val Dot_mono_right = store_thm ("Dot_mono_right",
  ``!X A B B'. arrow X B' B ==> arrow X (Dot A B') (Dot A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `B`
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC gamma
 >> RW_TAC bool_ss [one]);

val Dot_mono_left = store_thm ("Dot_mono_left",
  ``!X A B A'. arrow X A' A ==> arrow X (Dot A' B) (Dot A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `A`
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC beta
 >> RW_TAC bool_ss [one]);

val Dot_mono = store_thm ("Dot_mono",
  ``!X A B C D. arrow X A C /\ arrow X B D ==> arrow X (Dot A B) (Dot C D)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC comp
 >> EXISTS_TAC ``(Dot C B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC Dot_mono_left >> RW_TAC bool_ss [],
      MATCH_MP_TAC Dot_mono_right >> RW_TAC bool_ss [] ]);

val Slash_mono_left = store_thm ("Slash_mono_left",
  ``!X C B C'. arrow X C' C ==> arrow X (Slash C' B) (Slash C B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `C'`
 >> CONJ_TAC
 >| [ MATCH_MP_TAC beta' >> RW_TAC bool_ss [one],
      RW_TAC bool_ss [] ]);

val Slash_antimono_right = store_thm ("Slash_antimono_right",
  ``!X C B B'. arrow X B' B ==> arrow X (Slash C B) (Slash C B')``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC beta
 >> MATCH_MP_TAC gamma'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `B`
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC gamma
 >> MATCH_MP_TAC beta'
 >> RW_TAC bool_ss [one]);

val Backslash_antimono_left = store_thm ("Backslash_antimono_left",
  ``!X A C A'. arrow X A A' ==> arrow X (Backslash A' C) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma
 >> MATCH_MP_TAC beta'
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `A'`
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC beta
 >> MATCH_MP_TAC gamma'
 >> RW_TAC bool_ss [one]);

val Backslash_mono_right = store_thm ("Backslash_mono_right",
  ``!X A C C'. arrow X C' C ==> arrow X (Backslash A C') (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gamma
 >> MATCH_MP_TAC comp
 >> Q.EXISTS_TAC `C'`
 >> CONJ_TAC
 >| [ MATCH_MP_TAC beta' \\
      MATCH_MP_TAC beta \\
      MATCH_MP_TAC gamma' \\
      RW_TAC bool_ss [one],
      ASM_REWRITE_TAC [] ]);

val mono_X = store_thm ("mono_X",
  ``!X' X A B. arrow X A B ==> extends X X' ==> arrow X' A B``,
    GEN_TAC
 >> Induct_on `arrow`
 >> REPEAT STRIP_TAC (* 7 sub-goals here *)
 >- REWRITE_TAC [one]
 >- RW_TAC bool_ss [beta]
 >- RW_TAC bool_ss [beta']
 >- RW_TAC bool_ss [gamma]
 >- RW_TAC bool_ss [gamma']
 >- PROVE_TAC [comp]
 >> PROVE_TAC [arrow_plus, RSUBSET]);

val pi = store_thm ("pi",
  ``!X. extends NLP X ==> !A B. arrow X (Dot A B) (Dot B A)``,
    REPEAT STRIP_TAC
 >> `NLP (Dot A B) (Dot B A)` by REWRITE_TAC [NLP_rules]
 >> `arrow NLP (Dot A B) (Dot B A)` by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val pi_NLP = store_thm ("pi_NLP", ``!A B. arrow NLP (Dot A B) (Dot B A)``,
    MATCH_MP_TAC pi
 >> REWRITE_TAC [no_extend]);

val pi_LP = store_thm ("pi_LP", ``!A B. arrow LP (Dot A B) (Dot B A)``,
    MATCH_MP_TAC pi
 >> REWRITE_TAC [NLPextendsLP]);

val alfa = store_thm ("alfa",
  ``!X. extends L X ==> !A B C. arrow X (Dot A (Dot B C)) (Dot (Dot A B) C)``,
    REPEAT STRIP_TAC
 >> `L (Dot A (Dot B C)) (Dot (Dot A B) C)`
	by REWRITE_TAC [L_rule_rl]
 >> `arrow L (Dot A (Dot B C)) (Dot (Dot A B) C)`
	by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val alfa_L = store_thm ("alfa_L",
  ``!A B C. arrow L (Dot A (Dot B C)) (Dot (Dot A B) C)``,
    MATCH_MP_TAC alfa
 >> REWRITE_TAC [no_extend]);

val alfa_LP = store_thm ("alfa_LP",
  ``!A B C. arrow LP (Dot A (Dot B C)) (Dot (Dot A B) C)``,
    MATCH_MP_TAC alfa
 >> REWRITE_TAC [LextendsLP]);

val alfa' = store_thm ("alfa'",
  ``!X. extends L X ==> !A B C. arrow X (Dot (Dot A B) C) (Dot A (Dot B C))``,
    REPEAT STRIP_TAC
 >> `L (Dot (Dot A B) C) (Dot A (Dot B C))` by REWRITE_TAC [L_rule_lr]
 >> `arrow L (Dot (Dot A B) C) (Dot A (Dot B C))` by RW_TAC bool_ss [arrow_plus]
 >> PROVE_TAC [mono_X]);

val alfa'_L = store_thm ("alfa'_L",
  ``!A B C. arrow L (Dot (Dot A B) C) (Dot A (Dot B C))``,
    MATCH_MP_TAC alfa'
 >> REWRITE_TAC [no_extend]);

val alfa'_LP = store_thm ("alfa'_LP",
  ``!A B C. arrow LP (Dot (Dot A B) C) (Dot A (Dot B C))``,
    MATCH_MP_TAC alfa'
 >> REWRITE_TAC [LextendsLP]);

(******************************************************************************)
(*                                                                            *)
(*                            L rules                                         *)
(*                                                                            *)
(******************************************************************************)

val L_a = store_thm ("L_a", ``!x. arrow L x x``, REWRITE_TAC [one]);
val L_b = store_thm ("L_b",  ``!x y z. arrow L (Dot (Dot x y) z) (Dot x (Dot y z))``,
    REWRITE_TAC [alfa'_L]);
val L_b' = store_thm ("L_b'", ``!x y z. arrow L (Dot x (Dot y z)) (Dot (Dot x y) z)``,
    REWRITE_TAC [alfa_L, alfa'_L]);
val L_c  = store_thm ("L_c",  ``!x y z. arrow L (Dot x y) z ==> arrow L x (Slash z y)``,
    REWRITE_TAC [beta]);
val L_c' = store_thm ("L_c'", ``!x y z. arrow L (Dot x y) z ==> arrow L y (Backslash x z)``,
    REWRITE_TAC [gamma]);
val L_d  = store_thm ("L_d",  ``!x y z. arrow L x (Slash z y) ==> arrow L (Dot x y) z``,
    REWRITE_TAC [beta']);
val L_d' = store_thm ("L_d'", ``!x y z. arrow L y (Backslash x z) ==> arrow L (Dot x y) z``,
    REWRITE_TAC [gamma']);
val L_e  = store_thm ("L_e",  ``!x y z. arrow L x y /\ arrow L y z ==> arrow L x z``,
    REWRITE_TAC [comp]);

val L_arrow_rules = save_thm (
   "L_arrow_rules", LIST_CONJ [L_a, L_b, L_b', L_c, L_c', L_d, L_d', L_e]);

local
  val t = PROVE_TAC [L_arrow_rules]
in
  val L_f  = store_thm ("L_f",  ``!x y. arrow L x (Slash (Dot x y) y)``, t)
  and L_g  = store_thm ("L_g",  ``!y z. arrow L (Dot (Slash z y) y) z``, t)
  and L_h  = store_thm ("L_h",  ``!y z. arrow L y (Backslash (Slash z y) z)``, t)
  and L_i  = store_thm ("L_i",  ``!x y z. arrow L (Dot (Slash z y) (Slash y x)) (Slash z x)``, t)
  and L_j  = store_thm ("L_j",  ``!x y z. arrow L (Slash z y) (Slash (Slash z x) (Slash y x))``, t)

  and L_k  = store_thm ("L_k",  ``!x y z. arrow L (Slash (Backslash x y) z)
						  (Backslash x (Slash y z))``, t)

  and L_k' = store_thm ("L_k'", ``!x y z. arrow L (Backslash x (Slash y z))
						  (Slash (Backslash x y) z)``, t)

  and L_l  = store_thm ("L_l",  ``!x y z. arrow L (Slash (Slash x y) z) (Slash x (Dot z y))``, t)
  and L_l' = store_thm ("L_l'", ``!x y z. arrow L (Slash x (Dot z y)) (Slash (Slash x y) z)``, t)
  and L_m  = store_thm ("L_m",  ``!x x' y y'. arrow L x x' /\ arrow L y y'
					  ==> arrow L (Dot x y) (Dot x' y')``, t)
  and L_n  = store_thm ("L_n",  ``!x x' y y'. arrow L x x' /\ arrow L y y'
					  ==> arrow L (Slash x y') (Slash x' y)``, t);

  val L_arrow_rules_ex = save_thm (
     "L_arrow_rules_ex", LIST_CONJ [L_f, L_g, L_h, L_i, L_j, L_k, L_k', L_l, L_l', L_m, L_n])
end;

local
  val t = PROVE_TAC [L_a, L_c, L_c', L_d, L_d', L_e] (* L_b and L_b' are not used *)
in
  val L_dot_mono_r = store_thm ("L_dot_mono_r",
    ``!A B B'. arrow L B B' ==> arrow L (Dot A B) (Dot A B')``, t)
  and L_dot_mono_l = store_thm ("L_dot_mono_l",
    ``!A B A'. arrow L A A' ==> arrow L (Dot A B) (Dot A' B)``, t)
  and L_slash_mono_l = store_thm ("L_slash_mono_l",
    ``!C B C'. arrow L C C' ==> arrow L (Slash C B) (Slash C' B)``, t)
  and L_slash_antimono_r = store_thm ("L_slash_antimono_r",
    ``!C B B'. arrow L B B' ==> arrow L (Slash C B') (Slash C B)``, t)
  and L_backslash_antimono_l = store_thm ("L_backslash_antimono_l",
    ``!A C A'. arrow L A A' ==> arrow L (Backslash A' C) (Backslash A C)``, t)
  and L_backslash_mono_r = store_thm ("L_backslash_mono_r",
    ``!A C'. arrow L C C' ==> arrow L (Backslash A C) (Backslash A C')``, t);

  val L_arrow_rules_mono = save_thm (
     "L_arrow_rules_mono",
      LIST_CONJ [L_dot_mono_r, L_dot_mono_l,
		 L_slash_mono_l, L_slash_antimono_r,
		 L_backslash_antimono_l, L_backslash_mono_r])
end;

(******************************************************************************)
(*                                                                            *)
(*                              Module: Terms                                 *)
(*                                                                            *)
(******************************************************************************)

val _ = Datatype `Term = OneForm ('a Form) | Comma Term Term`;

val Term_induction = TypeBase.induction_of ``:'a Term``;
val Term_nchotomy  = TypeBase.nchotomy_of ``:'a Term``;
val Term_distinct  = TypeBase.distinct_of ``:'a Term``;
val Term_distinct' = save_thm ("Term_distinct'", GSYM Term_distinct);
val Term_11        = TypeBase.one_one_of ``:'a Term``;

val _ = type_abbrev ("gentzen_extension", ``:'a Term -> 'a Term -> bool``);

(* Definition of the recursive function that translates Terms to Forms *)
val deltaTranslation_def = Define `
   (deltaTranslation (OneForm f) = f) /\
   (deltaTranslation (Comma t1 t2) = Dot (deltaTranslation t1) (deltaTranslation t2))`;

val deltaTranslationOneForm = store_thm (
   "deltaTranslationOneForm[simp]",
  ``deltaTranslation (OneForm f) = f``, RW_TAC std_ss [deltaTranslation_def]);

val deltaTranslationComma = store_thm (
   "deltaTranslationComma[simp]",
  ``deltaTranslation (Comma t1 t2) = Dot (deltaTranslation t1) (deltaTranslation t2)``,
    RW_TAC std_ss [deltaTranslation_def]);

(* Non-associative extension, an empty relation actually *)
val NL_Sequent_def = Define `
   (NL_Sequent :'a gentzen_extension) = EMPTY_REL`;

(* NLP Sequent extension *)
val (NLP_Sequent_rules, NLP_Sequent_ind, NLP_Sequent_cases) = Hol_reln `
    (!A B. NLP_Sequent (Comma A B) (Comma B A))`;

val NLP_Intro = save_thm ("NLP_Intro", NLP_Sequent_rules);

(* L Sequent extension, the Full Lambek Sequent Calculus extension *)
val (L_Sequent_rules, L_Sequent_ind, L_Sequent_cases) = Hol_reln `
    (!A B C. L_Sequent (Comma A (Comma B C)) (Comma (Comma A B) C)) /\
    (!A B C. L_Sequent (Comma (Comma A B) C) (Comma A (Comma B C)))`;

val [L_Intro_lr, L_Intro_rl] =
    map save_thm (combine (["L_Intro_lr", "L_Intro_rl"], CONJUNCTS L_Sequent_rules));

val LP_Sequent_def = Define `
    LP_Sequent = add_extension NLP_Sequent L_Sequent`;

val NLP_Sequent_LP_Sequent = store_thm (
   "NLP_Sequent_LP_Sequent", ``extends NLP_Sequent LP_Sequent``,
    REWRITE_TAC [LP_Sequent_def, add_extend_l]);

val L_Sequent_LP_Sequent = store_thm (
   "L_Sequent_LP_Sequent", ``extends L_Sequent LP_Sequent``,
    REWRITE_TAC [LP_Sequent_def, add_extend_r]);

val LPextendsL = store_thm ("LPextendsL",
  ``!E. extends LP_Sequent E ==> extends L_Sequent E``,
    RW_TAC bool_ss [LP_Sequent_def, RSUBSET, RUNION]);

val LPextendsNLP = store_thm ("LPextendsNLP",
  ``!E. extends LP_Sequent E ==> extends NLP_Sequent E``,
    RW_TAC bool_ss [LP_Sequent_def, RSUBSET, RUNION]);

(******************************************************************************)
(*                                                                            *)
(*                            Module: ReplaceProp                             *)
(*                                                                            *)
(******************************************************************************)

(* The `replace` operator has the type ('a ReplaceProp) *)
val _ = type_abbrev ("ReplaceProp", ``:'a Term -> 'a Term -> 'a Term -> 'a Term -> bool``);

(* Inductive definition of `replace` such that when ``replace Gamma Gamma' Delta Delta'``
   then Gamma' results from replacing a distinguished occurrence of the subterm Delta in
   the term Gamma by Delta' *)

val (replace_rules, replace_ind, replace_cases) = Hol_reln `
    (!F1 F2. replace F1 F2 F1 F2) /\					(* replaceRoot *)
    (!Gamma1 Gamma2 Delta F1 F2.
     replace Gamma1 Gamma2 F1 F2 ==>
     replace (Comma Gamma1 Delta) (Comma Gamma2 Delta) F1 F2) /\	(* replaceLeft *)
    (!Gamma1 Gamma2 Delta F1 F2.
     replace Gamma1 Gamma2 F1 F2 ==>
     replace (Comma Delta Gamma1) (Comma Delta Gamma2) F1 F2)`;		(* replaceRight *)

local
    val list = CONJUNCTS replace_rules
in
    val replaceRoot  = save_thm ("replaceRoot[simp]",  List.nth (list, 0))
    and replaceLeft  = save_thm ("replaceLeft",  List.nth (list, 1))
    and replaceRight = save_thm ("replaceRight", List.nth (list, 2))
end;

(* Definition of `replaceCommaDot` such that when ``replaceCommaDot Gamma Gamma'``
   then Gamma' is the result of replacing a number of commas in Gamma by the connector dot.

   Example: ``!A B. replaceCommaDot (A , (A , B)) (A , (A . B)))`` where in this case only
   one occurrence of comma is replaced by a dot. *)

val (replaceCommaDot1_rules, replaceCommaDot1_ind, replaceCommaDot1_cases) = Hol_reln `
    (!T1 T2 A B. replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B))
	     ==> replaceCommaDot1 T1 T2)`;

val replaceCommaDot_def = Define `replaceCommaDot = RTC replaceCommaDot1`;

val replaceCommaDot_rule = store_thm ("replaceCommaDot_rule",
  ``!T1 T2 A B. replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B))
	    ==> replaceCommaDot T1 T2``,
    PROVE_TAC [replaceCommaDot_def, replaceCommaDot1_rules, RTC_SINGLE]);

val replaceTransitive = store_thm ("replaceTransitive", ``transitive replaceCommaDot``,
    REWRITE_TAC [replaceCommaDot_def, RTC_TRANSITIVE]);

(* a more practical version *)
val replaceTransitive' = store_thm ("replaceTransitive'",
  ``!T1 T2 T3. replaceCommaDot T1 T2 /\ replaceCommaDot T2 T3 ==> replaceCommaDot T1 T3``,
    PROVE_TAC [replaceTransitive, transitive_def]);

val noReplace = store_thm ("noReplace[simp]", ``!T. replaceCommaDot T T``,
    PROVE_TAC [replaceCommaDot_def, RTC_REFLEXIVE, reflexive_def]);

local
  val t = PROVE_TAC [replaceCommaDot1_rules, replaceCommaDot_def, replaceTransitive,
		     transitive_def, RTC_SINGLE]
in
  val replaceOneComma = store_thm ("replaceOneComma",
    ``!T1 T2 T3 A B. replaceCommaDot T1 T2 /\
		     replace T2 T3 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B))
		 ==> replaceCommaDot T1 T3``, t)

  and replaceOneComma' = store_thm ("replaceOneComma'",
    ``!T1 T2 T3 A B. replace T1 T2 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\
		     replaceCommaDot T2 T3
		 ==> replaceCommaDot T1 T3``, t);

  val replaceCommaDot_rules = save_thm (
     "replaceCommaDot_rules", LIST_CONJ [noReplace, replaceCommaDot_rule,
					 replaceOneComma, replaceOneComma'])
end;

(* An induction theorem for RTC replaceCommaDot1, similar to those generated by Hol_reln *)
val replaceCommaDot_ind = store_thm ("replaceCommaDot_ind",
  ``!(P:'a gentzen_extension).
	(!x. P x x) /\
	(!x y z A B. replace x y (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\ P y z ==> P x z)
    ==> (!x y. replaceCommaDot x y ==> P x y)``,
 (* The idea is to use RTC_INDUCT thm to prove induct theorems for RTCs *)
    REWRITE_TAC [replaceCommaDot_def]
 >> GEN_TAC   (* remove outer !P *)
 >> STRIP_TAC (* prepare for higher order matching *)
 >> HO_MATCH_MP_TAC (ISPEC ``replaceCommaDot1:'a gentzen_extension`` RTC_INDUCT)
 >> PROVE_TAC [replaceCommaDot1_cases]);

local
  val t = GEN_TAC \\ (* prepare for higher order matching and induction *)
	  HO_MATCH_MP_TAC replaceCommaDot_ind \\
	  PROVE_TAC [replace_rules, replaceCommaDot_rules]
in
  val replaceMonoRight = store_thm ("replaceMonoRight",
    ``!T3 T1 T2. replaceCommaDot T1 T2
	     ==> replaceCommaDot (Comma T1 T3) (Comma T2 T3)``, t)
  and replaceMonoLeft = store_thm ("replaceMonoLeft",
    ``!T3 T1 T2. replaceCommaDot T1 T2
	     ==> replaceCommaDot (Comma T3 T1) (Comma T3 T2)``, t)
end;

val replaceMono = store_thm ("replaceMono",
  ``!T1 T2 T3 T4. replaceCommaDot T1 T2 /\ replaceCommaDot T3 T4
	      ==> replaceCommaDot (Comma T1 T3) (Comma T2 T4)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC replaceTransitive'
 >> EXISTS_TAC ``Comma T2 T3``
 >> PROVE_TAC [replaceMonoLeft, replaceMonoRight]);

val replaceTranslation = store_thm ("replaceTranslation",
  ``!T. replaceCommaDot T (OneForm (deltaTranslation T))``,
    Induct
 >- PROVE_TAC [deltaTranslation_def, noReplace] (* base case *)
 >> REWRITE_TAC [deltaTranslation_def]        (* induct case *)
 >> MATCH_MP_TAC replaceTransitive'
 >> EXISTS_TAC ``Comma (OneForm (deltaTranslation T')) (OneForm (deltaTranslation T''))``
 >> PROVE_TAC [replaceOneComma, noReplace, replaceRoot, replaceMono]);

val replace_inv1 = store_thm ("replace_inv1",
  ``!Gamma' Delta X C.
     replace (OneForm C) Gamma' (OneForm X) Delta ==> (Gamma' = Delta) /\ (X = C)``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [replace_cases] \\
 REPEAT STRIP_TAC
 >- ASM_REWRITE_TAC []
 >- PROVE_TAC [Term_11]
 >> PROVE_TAC [Term_distinct]);

val replace_inv2 = store_thm ("replace_inv2",
  ``!Gamma1 Gamma2 Gamma' Delta X.
     replace (Comma Gamma1 Gamma2) Gamma' (OneForm X) Delta ==>
     (?G. (Gamma' = Comma G Gamma2) /\ replace Gamma1 G (OneForm X) Delta) \/
     (?G. (Gamma' = Comma Gamma1 G) /\ replace Gamma2 G (OneForm X) Delta)``,
    REPEAT STRIP_TAC
 >> POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [replace_cases]))
 >> REPEAT STRIP_TAC
 >- PROVE_TAC [Term_distinct]
 >| [ `(Gamma1 = Gamma1') /\ (Gamma2 = Delta')` by PROVE_TAC [Term_11] \\
      ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC OR_INTRO_THM1 \\
      Q.EXISTS_TAC `Gamma2'` \\
      ASM_REWRITE_TAC [] ,
      `(Gamma1 = Delta') /\ (Gamma2 = Gamma1')` by PROVE_TAC [Term_11] \\
      ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC OR_INTRO_THM2 \\
      Q.EXISTS_TAC `Gamma2'` \\
      ASM_REWRITE_TAC [] ]);

val doubleReplace = store_thm ("doubleReplace",
  ``!Gamma Gamma' T1 T2.
     replace Gamma Gamma' T1 T2 ==>
     !Gamma2 A T3. replace Gamma' Gamma2 (OneForm A) T3 ==>
	      (?G. replace Gamma G (OneForm A) T3 /\ replace G Gamma2 T1 T2) \/
	      (?G. replace T2 G (OneForm A) T3 /\ replace Gamma Gamma2 T1 G)``,
    Induct_on `replace`
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      DISJ2_TAC \\
      Q.EXISTS_TAC `Gamma2` \\
      ASM_REWRITE_TAC [replaceRoot],
      (* goal 2 (of 3) *)
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2)) \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASM_REWRITE_TAC [] >> RES_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          DISJ1_TAC \\
          EXISTS_TAC ``(Comma G' Delta)`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [],
            (* goal 2.1.1.2 (of 2) *)
            MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 2) *)
          DISJ2_TAC \\
          Q.EXISTS_TAC `G'` \\
          CONJ_TAC >- ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 2) *)
        ASM_REWRITE_TAC [] \\
        DISJ1_TAC \\
        EXISTS_TAC ``(Comma Gamma G)`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [] ] ],
      (* goal 3 (of 3) *)
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2)) \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        ASM_REWRITE_TAC [] \\
        DISJ1_TAC \\
        EXISTS_TAC ``(Comma G Gamma)`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 3.1.1 (of 2) *)
          MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [],
          (* goal 3.1.2 (of 2) *)
          MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [] ],
        (* goal 3.2 (of 2) *)
        ASM_REWRITE_TAC [] >> RES_TAC >| (* 2 sub-goals here *)
        [ (* goal 3.2.1 (of 2) *)
          DISJ1_TAC \\
          EXISTS_TAC ``(Comma Delta G')`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 3.2.1.1 (of 2) *)
            MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [],
            (* goal 3.2.1.2 (of 2) *)
            MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [] ],
          (* goal 3.2.2 (of 2) *)
          DISJ2_TAC \\
          Q.EXISTS_TAC `G'` \\
          CONJ_TAC >- ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [] ] ] ]);

val replaceSameP = store_thm ("replaceSameP",
  ``!T1 T2 T3 T4. replace T1 T2 T3 T4 ==>
		  !G. ?G'. replace T1 G' T3 G /\ replace G' T2 G T4``,
    Induct_on `replace`
 >> REPEAT STRIP_TAC
 >| [ Q.EXISTS_TAC `G` >> REWRITE_TAC [replaceRoot],
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `G`))
   >> POP_ASSUM CHOOSE_TAC
   >> EXISTS_TAC ``(Comma G' Delta)``
   >> RW_TAC bool_ss [replaceLeft],
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `G`))
   >> POP_ASSUM CHOOSE_TAC
   >> EXISTS_TAC ``(Comma Delta G')``
   >> RW_TAC bool_ss [replaceRight] ]);

val replaceTrans = store_thm ("replaceTrans",
  ``!T5 T6 T1 T2 T3 T4.
     replace T1 T2 T3 T4 ==> replace T3 T4 T5 T6 ==> replace T1 T2 T5 T6``,
    NTAC 2 GEN_TAC
 >> Induct_on `replace`
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [replaceLeft],
      PROVE_TAC [replaceRight] ]);

(* easier for MATCH_MP_TAC *)
val replaceTrans' = store_thm ("replaceTrans'",
  ``!T5 T6 T1 T2 T3 T4.
     replace T1 T2 T3 T4 /\ replace T3 T4 T5 T6 ==> replace T1 T2 T5 T6``,
    PROVE_TAC [replaceTrans]);

(******************************************************************************)
(*                                                                            *)
(*                         Module: NaturalDeduction                           *)
(*                                                                            *)
(******************************************************************************)

val (natDed_rules, natDed_ind, natDed_cases) = Hol_reln `
    (!(E:'a gentzen_extension) A.				(* NatAxiom *)
      natDed E (OneForm A) A) /\
    (!E Gamma A B.						(* SlashIntro *)
      natDed E (Comma Gamma (OneForm B)) A ==>
      natDed E Gamma (Slash A B)) /\
    (!E Gamma A B.						(* BackslashIntro *)
      natDed E (Comma (OneForm B) Gamma) A ==>
      natDed E Gamma (Backslash B A)) /\
    (!E Gamma Delta A B.					(* DotIntro *)
      natDed E Gamma A /\ natDed E Delta B ==>
      natDed E (Comma Gamma Delta) (Dot A B)) /\
    (!E Gamma Delta A B.					(* SlashElim *)
      natDed E Gamma (Slash A B) /\ natDed E Delta B ==>
      natDed E (Comma Gamma Delta) A) /\
    (!E Gamma Delta A B.				 	(* BackslashElim *)
      natDed E Gamma B /\ natDed E Delta (Backslash B A) ==>
      natDed E (Comma Gamma Delta) A) /\
    (!E Gamma Gamma' Delta A B C.				(* DotElim *)
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) Delta /\
      natDed E Delta (Dot A B) /\ natDed E Gamma C ==>
      natDed E Gamma' C) /\
    (!(E:'a gentzen_extension) C Gamma Gamma' Delta Delta'.	(* NatExt *)
      replace Gamma Gamma' Delta Delta' /\ E Delta Delta' /\
      natDed E Gamma C ==> natDed E Gamma' C)`;

val [NatAxiom, SlashIntro, BackslashIntro, DotIntro, SlashElim, BackslashElim, DotElim, NatExt] =
    map save_thm
        (combine (["NatAxiom[simp]", "SlashIntro", "BackslashIntro", "DotIntro", "SlashElim",
		   "BackslashElim", "DotElim", "NatExt"], CONJUNCTS natDed_rules));

val NatAxiomGeneralized = store_thm ("NatAxiomGeneralized[simp]",
  ``!E Gamma. natDed E Gamma (deltaTranslation Gamma)``,
    Induct_on `Gamma:'a Term`
 >- PROVE_TAC [deltaTranslation_def, NatAxiom]
 >> REWRITE_TAC [deltaTranslation_def]
 >> PROVE_TAC [DotIntro]);

val DotElimGeneralized = store_thm ("DotElimGeneralized",
  ``!E C Gamma Gamma'. replaceCommaDot Gamma Gamma'
		   ==> natDed E Gamma C ==> natDed E Gamma' C``,
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC replaceCommaDot_ind
 >> REPEAT STRIP_TAC
 >> `natDed E (OneForm (Dot A B)) (Dot A B)` by PROVE_TAC [NatAxiomGeneralized, deltaTranslation_def]
 >> `natDed E Gamma' C` by PROVE_TAC [DotElim]
 >> RW_TAC bool_ss []);

val NatTermToForm = store_thm ("NatTermToForm",
  ``!E Gamma C. natDed E Gamma C ==> natDed E (OneForm (deltaTranslation Gamma)) C``,
    REPEAT STRIP_TAC
 >> PROVE_TAC [DotElimGeneralized, replaceTranslation]);

val NatExtSimpl = store_thm (
   "NatExtSimpl", ``!E Gamma Gamma' C. E Gamma Gamma' /\ natDed E Gamma C ==> natDed E Gamma' C``,
    REPEAT STRIP_TAC
 >> `replace Gamma Gamma' Gamma Gamma'` by REWRITE_TAC [replaceRoot]
 >> IMP_RES_TAC NatExt);

(******************************************************************************)
(*                                                                            *)
(*                        Module: Sequent Calculus                            *)
(*                                                                            *)
(******************************************************************************)

(* gentzen presentation using sequents. *)
val (gentzenSequent_rules, gentzenSequent_ind, gentzenSequent_cases) = Hol_reln `
    (!(E:'a gentzen_extension) A.				(* SeqAxiom = NatAxiom *)
      gentzenSequent E (OneForm A) A) /\
    (!E Gamma A B.						(* RightSlash = SlashIntro *)
      gentzenSequent E (Comma Gamma (OneForm B)) A ==>
      gentzenSequent E Gamma (Slash A B)) /\
    (!E Gamma A B.						(* RightBackslash = BackslashIntro *)
      gentzenSequent E (Comma (OneForm B) Gamma) A ==>
      gentzenSequent E Gamma (Backslash B A)) /\
    (!E Gamma Delta A B.					(* RightDot = DotIntro *)
      gentzenSequent E Gamma A /\ gentzenSequent E Delta B ==>
      gentzenSequent E (Comma Gamma Delta) (Dot A B)) /\

    (* Delta |- B /\ Gamma[A] |- C ==> Gamma[A / B, Delta] |- C  *)
    (!E Gamma Gamma' Delta A B C.				(* LeftSlash *)
      replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) /\
      gentzenSequent E Delta B /\ gentzenSequent E Gamma C ==>
      gentzenSequent E Gamma' C) /\

    (* Delta |- B /\ Gamma[A] |- C ==> Gamma[Delta, B \ A] |- C *)
    (!E Gamma Gamma' Delta A B C.				(* LeftBackslash *)
      replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A))) /\
      gentzenSequent E Delta B /\ gentzenSequent E Gamma C ==>
      gentzenSequent E Gamma' C) /\

    (* Gamma[A, B] |- C ==> Gamma[A * B] |- C *)
    (!E Gamma Gamma' A B C.					(* LeftDot *)
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) /\
      gentzenSequent E Gamma C ==>
      gentzenSequent E Gamma' C) /\

    (* Delta |- A /\ Gamma[A] |- C ==> Gamma[Delta] |- C *)
    (!E Delta Gamma Gamma' A C.					(* CutRule *)
      replace Gamma Gamma' (OneForm A) Delta /\
      gentzenSequent E Delta A /\ gentzenSequent E Gamma C ==>
      gentzenSequent E Gamma' C) /\

    (* E Delta Delta' /\ Gamma[Delta] |- C ==> Gamma[Delta'] |- C *)
    (!(E:'a gentzen_extension) Gamma Gamma' Delta Delta' C.	(* SeqExt = NatExt *)
      replace Gamma Gamma' Delta Delta' /\ E Delta Delta' /\
      gentzenSequent E Gamma C ==> gentzenSequent E Gamma' C)`;

val [SeqAxiom, RightSlash, RightBackslash, RightDot, LeftSlash, LeftBackslash, LeftDot,
     CutRule, SeqExt] =
    map save_thm
        (combine (["SeqAxiom[simp]", "RightSlash", "RightBackslash", "RightDot",
		   "LeftSlash", "LeftBackslash", "LeftDot", "CutRule", "SeqExt"],
		  CONJUNCTS gentzenSequent_rules));

(* old name: axiomeGeneralisation *)
val SeqAxiomGeneralized = store_thm ("SeqAxiomGeneralized[simp]",
  ``!E Gamma. gentzenSequent E Gamma (deltaTranslation Gamma)``,
    Induct_on `Gamma:'a Term`
 >| [ PROVE_TAC [deltaTranslation_def, SeqAxiom], (* base case *)
      REWRITE_TAC [deltaTranslation_def] \\     (* induct case *)
      PROVE_TAC [RightDot] ]);

(* Some derived properties concerning gentzenSequent *)

val LeftDotSimpl = store_thm ("LeftDotSimpl",
  ``!E A B C. gentzenSequent E (Comma (OneForm A) (OneForm B)) C ==>
	      gentzenSequent E (OneForm (Dot A B)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (OneForm A) (OneForm B))``
 >> Q.EXISTS_TAC `A`
 >> Q.EXISTS_TAC `B`
 >> PROVE_TAC [replaceRoot]);

val LeftDotGeneralized = store_thm ("LeftDotGeneralized",
  ``!E C T1 T2. replaceCommaDot T1 T2 ==> gentzenSequent E T1 C ==> gentzenSequent E T2 C``,
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC replaceCommaDot_ind
 >> REPEAT STRIP_TAC
 >> PROVE_TAC [LeftDot]);

val SeqTermToForm = store_thm ("SeqTermToForm",
  ``!E Gamma C. gentzenSequent E Gamma C
	    ==> gentzenSequent E (OneForm (deltaTranslation Gamma)) C``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC LeftDotGeneralized
 >> RW_TAC bool_ss [replaceTranslation]);

val LeftSlashSimpl = store_thm ("LeftSlashSimpl",
  ``!E Gamma A B C. gentzenSequent E Gamma B /\ gentzenSequent E (OneForm A) C
	        ==> gentzenSequent E (Comma (OneForm (Slash A B)) Gamma) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, LeftSlash]);

val LeftBackslashSimpl = store_thm ("LeftBackslashSimpl",
  ``!E Gamma A B C. gentzenSequent E Gamma B /\ gentzenSequent E (OneForm A) C
	        ==> gentzenSequent E (Comma Gamma (OneForm (Backslash B A))) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, LeftBackslash]);

val CutRuleSimpl = store_thm ("CutRuleSimpl",
  ``!E Gamma A C. gentzenSequent E Gamma A /\ gentzenSequent E (OneForm A) C
	      ==> gentzenSequent E Gamma C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, CutRule]);

val DotRightSlash' = store_thm ("DotRightSlash'",
  ``!E A B C. gentzenSequent E (OneForm A) (Slash C B)
	  ==> gentzenSequent E (OneForm (Dot A B)) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, gentzenSequent_rules]);

val DotRightBackslash' = store_thm ("DotRightBackslash'",
  ``!E A B C. gentzenSequent E (OneForm B) (Backslash A C)
	  ==> gentzenSequent E (OneForm (Dot A B)) C``,
    PROVE_TAC [replace_rules, replaceCommaDot_rules, gentzenSequent_rules]);

val SeqExtSimpl = store_thm (
   "SeqExtSimpl", ``!E Gamma Gamma' C. E Gamma Gamma' /\ gentzenSequent E Gamma C
				   ==> gentzenSequent E Gamma' C``,
    REPEAT STRIP_TAC
 >> `replace Gamma Gamma' Gamma Gamma'` by REWRITE_TAC [replaceRoot]
 >> IMP_RES_TAC SeqExt);

(* some definitions concerning extensions *)

val LextensionSimpl = store_thm ("LextensionSimpl",
  ``!E T1 T2 T3 C. extends L_Sequent E /\
		   gentzenSequent E (Comma T1 (Comma T2 T3)) C
	       ==> gentzenSequent E (Comma (Comma T1 T2) T3) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SeqExt
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``	(* Gamma *)
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``	(* Delta *)
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``	(* Delta' *)
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >- REWRITE_TAC [replaceRoot]
 >- PROVE_TAC [RSUBSET, L_Intro_lr]
 >> ASM_REWRITE_TAC []);

val LextensionSimpl' = store_thm ("LextensionSimpl'", (* dual theorem of above *)
  ``!E T1 T2 T3 C. extends L_Sequent E /\
		   gentzenSequent E (Comma (Comma T1 T2) T3) C
	       ==> gentzenSequent E (Comma T1 (Comma T2 T3)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SeqExt
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``	(* Gamma *)
 >> EXISTS_TAC ``(Comma (Comma T1 T2) T3)``	(* Delta *)
 >> EXISTS_TAC ``(Comma T1 (Comma T2 T3))``	(* Delta' *)
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >- REWRITE_TAC [replaceRoot]
 >- PROVE_TAC [RSUBSET, L_Intro_rl]
 >> ASM_REWRITE_TAC []);

val LextensionSimplDot = store_thm ("LextensionSimplDot",
  ``!E A B C D. extends L_Sequent E /\
		gentzenSequent E (OneForm (Dot A (Dot B C))) D
	    ==> gentzenSequent E (OneForm (Dot (Dot A B) C)) D``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (Comma (OneForm A) (OneForm B)) (OneForm C))``
 >> Q.EXISTS_TAC `A`
 >> Q.EXISTS_TAC `B`
 >> STRIP_TAC
 >- RW_TAC bool_ss [replaceLeft, replaceRoot]
 >> MATCH_MP_TAC LextensionSimpl
 >> STRIP_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (Comma (OneForm B) (OneForm C))))``
 >> RW_TAC bool_ss [SeqAxiomGeneralized, deltaTranslation_def]);

val LextensionSimplDot' = store_thm ("LextensionSimplDot'", (* dual theorem of above *)
  ``!E A B C D. extends L_Sequent E /\
		gentzenSequent E (OneForm (Dot (Dot A B) C)) D
	    ==> gentzenSequent E (OneForm (Dot A (Dot B C))) D``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftDot
 >> EXISTS_TAC ``(Comma (OneForm A) (Comma (OneForm B) (OneForm C)))``
 >> Q.EXISTS_TAC `B`
 >> Q.EXISTS_TAC `C`
 >> STRIP_TAC
 >- RW_TAC bool_ss [replaceRight, replaceRoot]
 >> MATCH_MP_TAC LextensionSimpl'
 >> STRIP_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (Comma (OneForm A) (OneForm B)) (OneForm C)))``
 >> RW_TAC bool_ss [SeqAxiomGeneralized, deltaTranslation_def]);

val NLPextensionSimpl = store_thm ("NLPextensionSimpl",
  ``!E T1 T2 C. extends NLP_Sequent E /\
		gentzenSequent E (Comma T1 T2) C
	    ==> gentzenSequent E (Comma T2 T1) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC SeqExt
 >> EXISTS_TAC ``(Comma T1 T2)``
 >> EXISTS_TAC ``(Comma T1 T2)``
 >> EXISTS_TAC ``(Comma T2 T1)``
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >- REWRITE_TAC [replaceRoot]
 >- PROVE_TAC [RSUBSET, NLP_Intro]
 >> ASM_REWRITE_TAC []);

val NLPextensionSimplDot = store_thm ("NLPextensionSimplDot",
  ``!E A B C. extends NLP_Sequent E /\
	      gentzenSequent E (OneForm (Dot A B)) C
	  ==> gentzenSequent E (OneForm (Dot B A)) C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC NLPextensionSimpl
 >> STRIP_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (OneForm B)))``
 >> RW_TAC bool_ss [SeqAxiomGeneralized, deltaTranslation_def]);

(* original name: gentzenExtends, see also mono_X *)
val mono_E = store_thm ("mono_E",
  ``!E' E Gamma A. gentzenSequent E Gamma A
	       ==> extends E E'
	       ==> gentzenSequent E' Gamma A``,
    GEN_TAC
 >> HO_MATCH_MP_TAC gentzenSequent_ind
 >> REPEAT STRIP_TAC (* 9 goals here *)
 >- REWRITE_TAC [SeqAxiom]
 >- RW_TAC bool_ss [RightSlash]
 >- RW_TAC bool_ss [RightBackslash]
 >- RW_TAC bool_ss [RightDot]
 >- PROVE_TAC [LeftSlash]
 >- PROVE_TAC [LeftBackslash]
 >- PROVE_TAC [LeftDot]
 >- PROVE_TAC [CutRule]
 >> `E' Delta Delta'` by PROVE_TAC [RSUBSET]
 >> `gentzenSequent E' Gamma A` by RW_TAC bool_ss []
 >> PROVE_TAC [SeqExt]);

(* Some theorems and derived properties
   These definitions can be applied for all gentzen extensions,
   we can see how CutRuleSimpl gets used in most of time. *)

val application = store_thm ("application",
  ``!E A B. gentzenSequent E (OneForm (Dot (Slash A B) B)) A``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftSlashSimpl
 >> REWRITE_TAC [SeqAxiom]);

val application' = store_thm ("application'",
  ``!E A B. gentzenSequent E (OneForm (Dot B (Backslash B A))) A``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC LeftDotSimpl
 >> MATCH_MP_TAC LeftBackslashSimpl
 >> REWRITE_TAC [SeqAxiom]);

val RightSlashDot = store_thm ("RightSlashDot",
  ``!E A B C. gentzenSequent E (OneForm (Dot A C)) B
	  ==> gentzenSequent E (OneForm A) (Slash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm A) (OneForm C)))``
 >> RW_TAC bool_ss [SeqAxiomGeneralized, deltaTranslation_def]);

val RightBackslashDot = store_thm ("RightBackslashDot",
  ``!E A B C. gentzenSequent E (OneForm (Dot B A)) C
	  ==> gentzenSequent E (OneForm A) (Backslash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation (Comma (OneForm B) (OneForm A)))``
 >> RW_TAC bool_ss [SeqAxiomGeneralized, deltaTranslation_def]);

val coApplication = store_thm ("coApplication",
  ``!E A B. gentzenSequent E (OneForm A) (Slash (Dot A B) B)``,
    PROVE_TAC [RightSlash, RightDot, SeqAxiom]);

val coApplication' = store_thm ("coApplication'",
  ``!E A B. gentzenSequent E (OneForm A) (Backslash B (Dot B A))``,
    PROVE_TAC [RightBackslash, RightDot, SeqAxiom]);

val monotonicity = store_thm ("monotonicity",
  ``!E A B C D. gentzenSequent E (OneForm A) B /\
		gentzenSequent E (OneForm C) D
	    ==> gentzenSequent E (OneForm (Dot A C)) (Dot B D)``,
    PROVE_TAC [LeftDotSimpl, RightDot]);

val isotonicity = store_thm ("isotonicity",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Slash A C)) (Slash B C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> Q.EXISTS_TAC `A`
 >> PROVE_TAC [LeftSlashSimpl, SeqAxiom]);

val isotonicity' = store_thm ("isotonicity'",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Backslash C A)) (Backslash C B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> Q.EXISTS_TAC `A`
 >> PROVE_TAC [LeftBackslashSimpl, SeqAxiom]);

val antitonicity = store_thm ("antitonicity",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Slash C B)) (Slash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash C B) B)``
 >> STRIP_TAC
 >- PROVE_TAC [RightDot, SeqAxiom]
 >> REWRITE_TAC [application]);

val antitonicity' = store_thm ("antitonicity'",
  ``!E A B C. gentzenSequent E (OneForm A) B
	  ==> gentzenSequent E (OneForm (Backslash B C)) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B C))``
 >> STRIP_TAC
 >- PROVE_TAC [RightDot, SeqAxiom]
 >> REWRITE_TAC [application']);

val lifting = store_thm ("lifting",
  ``!E A B C. gentzenSequent E (OneForm A) (Slash B (Backslash A B))``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A B))``
 >> STRIP_TAC
 >- PROVE_TAC [RightDot, SeqAxiom]
 >> REWRITE_TAC [application']);

val lifting' = store_thm ("lifting'",
  ``!E A B C. gentzenSequent E (OneForm A) (Backslash (Slash B A) B)``,
    REPEAT GEN_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash B A) A)``
 >> STRIP_TAC
 >- PROVE_TAC [RightDot, SeqAxiom]
 >> REWRITE_TAC [application]);

(* These definitions can be applied iff associativity is supported by our logical system *)

val mainGeach = store_thm ("mainGeach",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Slash A B))
			       (Slash (Slash A C) (Slash B C))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightSlash)
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A B) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      CONJ_TAC >|
      [ REWRITE_TAC [SeqAxiom],
	MATCH_MP_TAC LeftSlashSimpl \\
	STRIP_TAC \\
	REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val mainGeach' = store_thm ("mainGeach'",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Backslash B A))
			       (Backslash (Backslash C B) (Backslash C A))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightBackslash)
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      CONJ_TAC >|
      [ MATCH_MP_TAC LeftBackslashSimpl \\
	STRIP_TAC \\
	REWRITE_TAC [SeqAxiom],
	REWRITE_TAC [SeqAxiom] ] ,
      REWRITE_TAC [application'] ]);

val secondaryGeach = store_thm ("secondaryGeach",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Slash B C))
			       (Backslash (Slash A B) (Slash A C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC >- (POP_ASSUM ACCEPT_TAC)
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A B) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      CONJ_TAC >|
      [ REWRITE_TAC [SeqAxiom],
	MATCH_MP_TAC LeftSlashSimpl \\
	STRIP_TAC \\
	REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val secondaryGeach' = store_thm ("secondaryGeach'",
``!E A B C. extends L_Sequent E
	==> gentzenSequent E (OneForm (Backslash C B))
			     (Slash (Backslash C A) (Backslash B A))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      STRIP_TAC >|
      [ MATCH_MP_TAC LeftBackslashSimpl \\
	STRIP_TAC \\
	REWRITE_TAC [SeqAxiom],
	REWRITE_TAC [SeqAxiom] ] ,
      REWRITE_TAC [application'] ]);

val composition = store_thm ("composition",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Dot (Slash A B) (Slash B C)))
			       (Slash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash (Slash A C) (Slash B C)) (Slash B C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity \\
      CONJ_TAC >|
      [ RW_TAC bool_ss [mainGeach], REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val composition' = store_thm ("composition'",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Dot (Backslash C B) (Backslash B A)))
			       (Backslash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash (Backslash C A) (Backslash B A)) (Backslash B A))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity \\
      CONJ_TAC >|
      [ RW_TAC bool_ss [secondaryGeach'], REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val restructuring = store_thm ("restructuring",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Slash (Backslash A B) C))
			       (Backslash A (Slash B C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC LextensionSimpl
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A B))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      CONJ_TAC >| [ REWRITE_TAC [SeqAxiom],
		    MATCH_MP_TAC LeftSlashSimpl \\
		    REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application'] ]);

val restructuring' = store_thm ("restructuring'",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Backslash A (Slash B C)))
			       (Slash (Backslash A B) C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlash
 >> MATCH_MP_TAC RightBackslash
 >> MATCH_MP_TAC LextensionSimpl'
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash B C) C)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC RightDot \\
      CONJ_TAC >| [ MATCH_MP_TAC LeftBackslashSimpl \\
		    REWRITE_TAC [SeqAxiom],
		    REWRITE_TAC [SeqAxiom] ],
      REWRITE_TAC [application] ]);

val currying = store_thm ("currying",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Slash A (Dot B C)))
			       (Slash (Slash A C) B)``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightSlashDot)
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> REWRITE_TAC [application]);

val currying' = store_thm ("currying'",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Slash (Slash A C) B))
			       (Slash A (Dot B C))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Slash A C) C)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity
   >> CONJ_TAC
   >> REWRITE_TAC [application, SeqAxiom],
      REWRITE_TAC [application] ]);

val decurrying = store_thm ("decurrying",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Backslash (Dot A B) C))
			       (Backslash B (Backslash A C))``,
    REPEAT STRIP_TAC
 >> NTAC 2 (MATCH_MP_TAC RightBackslashDot)
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> REWRITE_TAC [application']);

val decurrying' = store_thm ("decurrying'",
  ``!E A B C. extends L_Sequent E
	  ==> gentzenSequent E (OneForm (Backslash B (Backslash A C)))
			       (Backslash (Dot A B) C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC
 >- POP_ASSUM ACCEPT_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot A (Backslash A C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity \\
      REWRITE_TAC [application', SeqAxiom],
      REWRITE_TAC [application'] ]);

(* Theorem for systems that support commutativity: if its extension extends NLP_Sequent *)

val permutation = store_thm ("permutation",
  ``!E A B C. extends NLP_Sequent E
	  ==> gentzenSequent E (OneForm A) (Backslash B C)
	  ==> gentzenSequent E (OneForm B) (Backslash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Backslash B C))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity >> ASM_REWRITE_TAC [SeqAxiom],
      REWRITE_TAC [application'] ]);

val exchange = store_thm ("exchange",
  ``!E A B. extends NLP_Sequent E
	==> gentzenSequent E (OneForm (Slash A B)) (Backslash B A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application]);

val exchange' = store_thm ("exchange'",
  ``!E A B. extends NLP_Sequent E
	==> gentzenSequent E (OneForm (Backslash B A)) (Slash A B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application']);

val preposing = store_thm ("preposing",
  ``!E A B. extends NLP_Sequent E
	==> gentzenSequent E (OneForm A) (Slash B (Slash B A))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application]);

val postposing = store_thm ("postposing",
  ``!E A B. extends NLP_Sequent E
	==> gentzenSequent E (OneForm A) (Backslash (Backslash A B) B)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> RW_TAC bool_ss [application']);

(* For systems that support both commutativity and associativity *)

val mixedComposition = store_thm ("mixedComposition",
  ``!E A B C. extends LP_Sequent E
	  ==> gentzenSequent E (OneForm (Dot (Slash A B) (Backslash C B))) (Backslash C A)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC
 >- RW_TAC bool_ss [LPextendsNLP]
 >> MATCH_MP_TAC RightBackslashDot
 >> MATCH_MP_TAC LextensionSimplDot'
 >> CONJ_TAC
 >- RW_TAC bool_ss [LPextendsL]
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot B (Slash A B))``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity \\
      RW_TAC bool_ss [application', SeqAxiom],
      MATCH_MP_TAC NLPextensionSimplDot \\
      RW_TAC bool_ss [application, LPextendsNLP] ]);

val mixedComposition' = store_thm ("mixedComposition'",
  ``!E A B C. extends LP_Sequent E
	 ==>  gentzenSequent E (OneForm (Dot (Slash B C) (Backslash B A))) (Slash A C)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> CONJ_TAC
 >- RW_TAC bool_ss [LPextendsNLP]
 >> MATCH_MP_TAC RightSlashDot
 >> MATCH_MP_TAC LextensionSimplDot
 >> CONJ_TAC
 >- RW_TAC bool_ss [LPextendsL]
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(Dot (Backslash B A) B)``
 >> CONJ_TAC
 >| [ MATCH_MP_TAC monotonicity \\
      RW_TAC bool_ss [application, SeqAxiom],
      MATCH_MP_TAC NLPextensionSimplDot \\
      RW_TAC bool_ss [application', LPextendsNLP] ]);

(******************************************************************************)
(*                                                                            *)
(*                          Module: ArrowGentzen                              *)
(*                                                                            *)
(******************************************************************************)

val replace_arrow = store_thm ("replace_arrow",
  ``!X Gamma Gamma' T1 T2.
     replace Gamma Gamma' T1 T2 ==>
     arrow X (deltaTranslation T2) (deltaTranslation T1) ==>
     arrow X (deltaTranslation Gamma') (deltaTranslation Gamma)``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ REWRITE_TAC [deltaTranslation_def] \\
      RES_TAC \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP Dot_mono_left)) \\
      ASM_REWRITE_TAC [],
      REWRITE_TAC [deltaTranslation_def] \\
      RES_TAC \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP Dot_mono_right)) \\
      ASM_REWRITE_TAC [] ]);

val replace_arrow' = store_thm ("replace_arrow'",
  ``!C X Gamma Gamma' T1 T2.
     replace Gamma Gamma' T1 T2 ==>
     arrow X (deltaTranslation T2) (deltaTranslation T1) ==>
     arrow X (deltaTranslation Gamma) C ==>
     arrow X (deltaTranslation Gamma') C``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC replace_arrow
 >> IMP_RES_TAC comp);

(* from axiomatic presentation to sequent calculus *)
val arrowToGentzenExt_def = Define `
    arrowToGentzenExt (X :'a arrow_extension) (E :'a gentzen_extension) =
	!A B. X A B ==> gentzenSequent E (OneForm A) B`;

val NLToNL_Sequent = store_thm (
   "NLToNL_Sequent", ``arrowToGentzenExt NL NL_Sequent``,
    REWRITE_TAC [arrowToGentzenExt_def]
 >> RW_TAC std_ss [NL_def, EMPTY_REL_DEF]);

val NLPToNLP_Sequent = store_thm (
   "NLPToNLP_Sequent", ``arrowToGentzenExt NLP NLP_Sequent``,
    REWRITE_TAC [arrowToGentzenExt_def]
 >> REWRITE_TAC [NLP_cases]
 >> REPEAT STRIP_TAC
 >> ASM_REWRITE_TAC []
 >> ASSUME_TAC (ISPEC ``NLP_Sequent`` no_extend)
 >> MATCH_MP_TAC NLPextensionSimplDot
 >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [SeqAxiom]);

val LToL_Sequent = store_thm (
   "LToL_Sequent", ``arrowToGentzenExt L L_Sequent``,
    REWRITE_TAC [arrowToGentzenExt_def]
 >> REWRITE_TAC [L_cases]
 >> ASSUME_TAC (ISPEC ``L_Sequent`` no_extend)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >> ASM_REWRITE_TAC []
 >| [ MATCH_MP_TAC LextensionSimplDot' >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [SeqAxiom],
      MATCH_MP_TAC LextensionSimplDot >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [SeqAxiom] ]);

val LPToLP_Sequent = store_thm (
   "LPToLP_Sequent", ``arrowToGentzenExt LP LP_Sequent``,
    REWRITE_TAC [arrowToGentzenExt_def, LP_def, RUNION]
 >> REPEAT STRIP_TAC (* two sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      MP_TAC NLP_Sequent_LP_Sequent \\
      POP_ASSUM (MP_TAC o (MATCH_MP (REWRITE_RULE [arrowToGentzenExt_def] NLPToNLP_Sequent))) \\
      REWRITE_TAC [mono_E],
      (* goal 2 (of 2) *)
      MP_TAC L_Sequent_LP_Sequent \\
      POP_ASSUM (MP_TAC o (MATCH_MP (REWRITE_RULE [arrowToGentzenExt_def] LToL_Sequent))) \\
      REWRITE_TAC [mono_E] ]);

val arrowToGentzen = store_thm (
   "arrowToGentzen",
  ``!E X A B. arrow X A B ==> arrowToGentzenExt X E ==> gentzenSequent E (OneForm A) B``,
    GEN_TAC
 >> HO_MATCH_MP_TAC arrow_ind
 >> REPEAT STRIP_TAC (* 7 goals here, first is easy *)
 >- REWRITE_TAC [SeqAxiom] (* rest 6 goals *)
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC RightSlashDot >> RES_TAC,
      (* goal 2 (of 6) *)
      MATCH_MP_TAC DotRightSlash' >> RES_TAC,
      (* goal 3 (of 6) *)
      MATCH_MP_TAC RightBackslashDot >> RES_TAC,
      (* goal 4 (of 6) *)
      MATCH_MP_TAC DotRightBackslash' >> RES_TAC,
      (* goal 5 (of 6) *)
      MATCH_MP_TAC CutRuleSimpl \\
      Q.EXISTS_TAC `A'` \\
      RES_TAC \\
      ASM_REWRITE_TAC [],
      (* goal 6 (of 6) *)
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [arrowToGentzenExt_def])) \\
      RES_TAC ]);

(* particular cases for NLP, L; LP and NL systems *)
val arrowToGentzenNL = store_thm (
   "arrowToGentzenNL",
  ``!A B. arrow NL A B ==> gentzenSequent NL_Sequent (OneForm A) B``,
    REPEAT STRIP_TAC
 >> irule arrowToGentzen
 >> Q.EXISTS_TAC `NL`
 >> ASM_REWRITE_TAC [NLToNL_Sequent]);

val arrowToGentzenNLP = store_thm (
   "arrowToGentzenNLP",
  ``!A B. arrow NLP A B ==> gentzenSequent NLP_Sequent (OneForm A) B``,
    REPEAT STRIP_TAC
 >> irule arrowToGentzen
 >> Q.EXISTS_TAC `NLP`
 >> ASM_REWRITE_TAC [NLPToNLP_Sequent]);

val arrowToGentzenL = store_thm (
   "arrowToGentzenL",
  ``!A B. arrow L A B ==> gentzenSequent L_Sequent (OneForm A) B``,
    REPEAT STRIP_TAC
 >> irule arrowToGentzen
 >> Q.EXISTS_TAC `L`
 >> ASM_REWRITE_TAC [LToL_Sequent]);

val arrowToGentzenLP = store_thm (
   "arrowToGentzenLP",
  ``!A B. arrow LP A B ==> gentzenSequent LP_Sequent (OneForm A) B``,
    REPEAT STRIP_TAC
 >> irule arrowToGentzen
 >> Q.EXISTS_TAC `LP`
 >> ASM_REWRITE_TAC [LPToLP_Sequent]);

(* from sequent calculus to axiomatic presentation.
   Notice the strange thing here: the order of T1 and T2 are changed from E to X. *)
val gentzenToArrowExt_def = Define
   `gentzenToArrowExt (E :'a gentzen_extension) (X :'a arrow_extension) =
	(!T1 T2. E T1 T2 ==> X (deltaTranslation T2) (deltaTranslation T1))`;

(* Build arrow_extensions directly from gentzen_extensions *)
val ToArrowExt_def = Define `
    ToArrowExt (E :'a gentzen_extension) =
	CURRY { (deltaTranslation y, deltaTranslation x) | (x,y) IN (UNCURRY E) }`;

val ToArrowExt_thm = store_thm (
   "ToArrowExt_thm",
  ``!E T1 T2. E T1 T2 ==> (ToArrowExt E) (deltaTranslation T2) (deltaTranslation T1)``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [ToArrowExt_def, CURRY_DEF]
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> ONCE_REWRITE_TAC [GSPECIFICATION]
 >> Q.EXISTS_TAC `(T2, T1)`
 >> `(T1, T2) IN (UNCURRY E)`
	by PROVE_TAC [UNCURRY_DEF, SPECIFICATION]
 >> FULL_SIMP_TAC std_ss []);

val gentzenToArrowExt_thm = store_thm (
   "gentzenToArrowExt_thm", ``!E. gentzenToArrowExt E (ToArrowExt E)``,
    REWRITE_TAC [gentzenToArrowExt_def, ToArrowExt_thm]);

val NL_SequentToNL = store_thm (
   "NL_SequentToNL", ``gentzenToArrowExt NL_Sequent NL``,
    REWRITE_TAC [gentzenToArrowExt_def]
 >> RW_TAC std_ss [NL_Sequent_def, EMPTY_REL_DEF]);

val NLP_SequentToNLP = store_thm (
   "NLP_SequentToNLP", ``gentzenToArrowExt NLP_Sequent NLP``,
    REWRITE_TAC [gentzenToArrowExt_def]
 >> REWRITE_TAC [NLP_Sequent_cases]
 >> REPEAT STRIP_TAC
 >> ASM_REWRITE_TAC [deltaTranslation_def]
 >> REWRITE_TAC [NLP_rules]);

val L_SequentToL = store_thm (
   "L_SequentToL", ``gentzenToArrowExt L_Sequent L``,
    REWRITE_TAC [gentzenToArrowExt_def]
 >> REWRITE_TAC [L_Sequent_cases]
 >> REPEAT STRIP_TAC
 >> ASM_REWRITE_TAC [deltaTranslation_def]
 >| [ REWRITE_TAC [L_rule_lr],
      REWRITE_TAC [L_rule_rl] ]);

val LP_SequentToLP = store_thm (
   "LP_SequentToLP", ``gentzenToArrowExt LP_Sequent LP``,
    REWRITE_TAC [gentzenToArrowExt_def, LP_Sequent_def, RUNION]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM (MP_TAC o (MATCH_MP (REWRITE_RULE [gentzenToArrowExt_def] NLP_SequentToNLP))) \\
      MP_TAC NLPextendsLP \\
      RW_TAC std_ss [RSUBSET],
      (* goal 2 (of 2) *)
      POP_ASSUM (MP_TAC o (MATCH_MP (REWRITE_RULE [gentzenToArrowExt_def] L_SequentToL))) \\
      MP_TAC LextendsLP \\
      RW_TAC std_ss [RSUBSET] ]);

val gentzenToArrow' = store_thm (
   "gentzenToArrow'",
  ``!X E Gamma A. gentzenSequent E Gamma A ==> gentzenToArrowExt E X ==>
		  arrow X (deltaTranslation Gamma) A``,
    GEN_TAC
 >> HO_MATCH_MP_TAC gentzenSequent_ind
 >> REPEAT STRIP_TAC (* 9 sub-goals here *)
 >| [ (* goal 1 *)
      REWRITE_TAC [deltaTranslation_def, one],
      (* goal 2 *)
      RES_TAC >> POP_ASSUM MP_TAC \\
      REWRITE_TAC [deltaTranslation_def, beta],
      (* goal 3 *)
      RES_TAC >> POP_ASSUM MP_TAC \\
      REWRITE_TAC [deltaTranslation_def, gamma],
      (* goal 4 *)
      RES_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC \\
      RW_TAC std_ss [deltaTranslation_def, Dot_mono],
      (* goal 5 *)
      RES_TAC \\
      SUFF_TAC ``arrow X (deltaTranslation (Comma (OneForm (Slash A A')) Gamma''))
			 (deltaTranslation (OneForm A))`` >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
	DISCH_TAC \\
	`arrow X (deltaTranslation Gamma') (deltaTranslation Gamma)`
		by PROVE_TAC [replace_arrow] \\
	IMP_RES_TAC comp,
	(* goal 5.2 (of 2) *)
	REWRITE_TAC [deltaTranslation_def] \\
	MATCH_MP_TAC beta' \\
	MATCH_MP_TAC Slash_antimono_right \\
	POP_ASSUM ACCEPT_TAC ],
      (* goal 6 *)
      RES_TAC \\
      SUFF_TAC ``arrow X (deltaTranslation (Comma Gamma'' (OneForm (Backslash A' A))))
			 (deltaTranslation (OneForm A))`` >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
	DISCH_TAC \\
	`arrow X (deltaTranslation Gamma') A''` by PROVE_TAC [replace_arrow'],
	(* goal 6.2 (of 2) *)
	REWRITE_TAC [deltaTranslation_def] \\
	MATCH_MP_TAC gamma' \\
	MATCH_MP_TAC Backslash_antimono_left \\
	POP_ASSUM ACCEPT_TAC ],
      (* goal 7 *)
      RES_TAC \\
      SUFF_TAC ``arrow X (deltaTranslation (OneForm (Dot A B)))
			 (deltaTranslation (Comma (OneForm A) (OneForm B)))`` >|
      (* 2 sub-goals here *)
      [ (* goal 7.1 *)
	DISCH_TAC \\
	`arrow X (deltaTranslation Gamma') A'` by PROVE_TAC [replace_arrow'],
	(* goal 7.2 *)
	REWRITE_TAC [deltaTranslation_def, one] ],
     (* goal 8 *)
     RES_TAC \\
     `arrow X (deltaTranslation Gamma) (deltaTranslation (OneForm A))`
	by ASM_REWRITE_TAC [deltaTranslation_def] \\
     `arrow X (deltaTranslation Gamma'') A'` by PROVE_TAC [replace_arrow'],
     (* goal 9 *)
     FULL_SIMP_TAC std_ss [gentzenToArrowExt_def] \\
     RES_TAC \\
     `arrow X (deltaTranslation Delta') (deltaTranslation Delta)`
	by PROVE_TAC [arrow_plus] \\
     `arrow X (deltaTranslation Gamma') A` by PROVE_TAC [replace_arrow'] ]);

val gentzenToArrow = store_thm (
   "gentzenToArrow",
  ``!E X Gamma A. gentzenToArrowExt E X /\ gentzenSequent E Gamma A
	      ==> arrow X (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``gentzenToArrowExt E X`` MP_TAC
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [gentzenToArrow']);

val gentzenToArrow_E = store_thm (
   "gentzenToArrow_E",
  ``!E Gamma A. gentzenSequent E Gamma A ==> arrow (ToArrowExt E) (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> ASSUME_TAC (Q.SPEC `E` gentzenToArrowExt_thm)
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> REWRITE_TAC [gentzenToArrow']);

val NLGentzenToArrow = store_thm (
   "NLGentzenToArrow",
  ``!Gamma A. gentzenSequent NL_Sequent Gamma A ==> arrow NL (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> MP_TAC NL_SequentToNL
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [gentzenToArrow']);

val NLPGentzenToArrow = store_thm (
   "NLPGentzenToArrow",
  ``!Gamma A. gentzenSequent NLP_Sequent Gamma A ==> arrow NLP (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> MP_TAC NLP_SequentToNLP
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [gentzenToArrow']);

val LGentzenToArrow = store_thm (
   "LGentzenToArrow",
  ``!Gamma A. gentzenSequent L_Sequent Gamma A ==> arrow L (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> MP_TAC L_SequentToL
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [gentzenToArrow']);

val LPGentzenToArrow = store_thm (
   "LPGentzenToArrow",
  ``!Gamma A. gentzenSequent LP_Sequent Gamma A ==> arrow LP (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> MP_TAC LP_SequentToLP
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [gentzenToArrow']);

(******************************************************************************)
(*                                                                            *)
(*          Module: Gentzen's Sequent Calculus and Natural Deduction          *)
(*                                                                            *)
(******************************************************************************)

val replaceGentzen = store_thm ("replaceGentzen",
  ``!E Gamma Gamma' Delta Delta'.
     replace Gamma Gamma' Delta Delta' ==>
     gentzenSequent E Delta' (deltaTranslation Delta) ==>
     gentzenSequent E Gamma' (deltaTranslation Gamma)``,
    X_GEN_TAC ``E :'a gentzen_extension``
 >> Induct_on `replace`
 >> REPEAT STRIP_TAC
 >> `gentzenSequent E Delta (deltaTranslation Delta)` by PROVE_TAC [SeqAxiomGeneralized]
 >> `gentzenSequent E Gamma' (deltaTranslation Gamma)` by PROVE_TAC []
 >> PROVE_TAC [RightDot, deltaTranslation_def]);

val replaceGentzen' = store_thm (
   "replaceGentzen'",
  ``!Gamma Gamma' Delta Delta' C E.
     replace Gamma Gamma' Delta Delta' /\
     gentzenSequent E Delta' (deltaTranslation Delta) /\
     gentzenSequent E Gamma C ==>
     gentzenSequent E Gamma' C``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC CutRuleSimpl
 >> EXISTS_TAC ``(deltaTranslation Gamma)``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC replaceGentzen,
      (* goal 2 (of 2) *)
      MATCH_MP_TAC SeqTermToForm \\
      ASM_REWRITE_TAC [] ]);

val replaceNatDed = store_thm ("replaceNatDed",
  ``!E Gamma Gamma' Delta Delta'.
    replace Gamma Gamma' Delta Delta' ==>
    natDed E Delta' (deltaTranslation Delta) ==>
    natDed E Gamma' (deltaTranslation Gamma)``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> CONJ_TAC
 >- RW_TAC bool_ss []
 >> REWRITE_TAC [deltaTranslation_def]
 >> CONJ_TAC
 >> REPEAT STRIP_TAC
 >> MATCH_MP_TAC DotIntro
 >> RW_TAC bool_ss [NatAxiomGeneralized]);

(* E T1[A] T2[A] ==> ?T1[Delta]. X T1[Delta] T2[Delta] *)
val condCutExt_def = Define `
    condCutExt (E :'a gentzen_extension) =
	!Gamma T1 T2 A Delta.
	 E T1 T2 ==> replace T2 Gamma (OneForm A) Delta
	         ==> ?Gamma'. E Gamma' Gamma /\ replace T1 Gamma' (OneForm A) Delta`;

val conditionOKNL = store_thm ("conditionOKNL", ``condCutExt NL_Sequent``,
    REWRITE_TAC [condCutExt_def]
 >> REPEAT GEN_TAC
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [NL_Sequent_def]
 >> RW_TAC std_ss [EMPTY_REL_DEF]);

val conditionOKNLP = store_thm ("conditionOKNLP", ``condCutExt NLP_Sequent``,
    REWRITE_TAC [condCutExt_def]
 >> REPEAT GEN_TAC
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [NLP_Sequent_cases]
 >> REPEAT STRIP_TAC
 >> `replace (Comma B A') Gamma (OneForm A) Delta` by PROVE_TAC []
 >> ASM_REWRITE_TAC []
 >> POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``(Comma A' G)`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ REWRITE_TAC [NLP_Sequent_rules],
        MATCH_MP_TAC replaceRight >> ASM_REWRITE_TAC [] ],
      ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``(Comma G B)`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ REWRITE_TAC [NLP_Sequent_rules],
        MATCH_MP_TAC replaceLeft >> ASM_REWRITE_TAC [] ] ]);

val conditionOKL = store_thm ("conditionOKL", ``condCutExt L_Sequent``,
    REWRITE_TAC [condCutExt_def]
 >> REPEAT GEN_TAC
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [L_Sequent_cases]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      ASM_REWRITE_TAC []						\\
      `replace (Comma (Comma A' B) C) Gamma (OneForm A) Delta`
	by PROVE_TAC []							\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
      REPEAT STRIP_TAC >| (* 2 sub sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
	REPEAT STRIP_TAC >| (* 2 sub-goals here *)
	[ (* goal 1.1.1 (of 2) *)
	  ASM_REWRITE_TAC []						\\
	  EXISTS_TAC ``(Comma G' (Comma B C))``				\\
	  CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	  MATCH_MP_TAC replaceLeft					\\
	  ASM_REWRITE_TAC [],
	  (* goal 1.1.2 (of 2) *)
	  ASM_REWRITE_TAC []						\\
	  EXISTS_TAC ``(Comma A' (Comma G' C))``			\\
	  CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	  MATCH_MP_TAC replaceRight					\\
	  MATCH_MP_TAC replaceLeft					\\
	  ASM_REWRITE_TAC [] ],
	(* goal 1.2 (of 2) *)
	ASM_REWRITE_TAC []						\\
	EXISTS_TAC ``(Comma A' (Comma B G))``				\\
	CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	NTAC 2 (MATCH_MP_TAC replaceRight)				\\
        ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      ASM_REWRITE_TAC []						\\
      `replace (Comma A' (Comma B C)) Gamma (OneForm A) Delta`
	by PROVE_TAC []							\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
	ASM_REWRITE_TAC []						\\
	EXISTS_TAC ``(Comma (Comma G B) C)``				\\
	CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	NTAC 2 (MATCH_MP_TAC replaceLeft)				\\
	ASM_REWRITE_TAC [],
	(* goal 2.2 (of 2) *)
	POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
	REPEAT STRIP_TAC >| (* 2 sub-goals here *)
	[ (* goal 2.2.1 (of 2) *)
	  ASM_REWRITE_TAC []						\\
	  EXISTS_TAC ``(Comma (Comma A' G') C)``			\\
	  CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	  MATCH_MP_TAC replaceLeft					\\
	  MATCH_MP_TAC replaceRight					\\
	  ASM_REWRITE_TAC [],
	  (* goal 2.2.2 (of 2) *)
	  ASM_REWRITE_TAC []						\\
	  EXISTS_TAC ``(Comma (Comma A' B) G')``			\\
	  CONJ_TAC >- REWRITE_TAC [L_Sequent_rules]			\\
	  MATCH_MP_TAC replaceRight					\\
	  ASM_REWRITE_TAC [] ] ] ]);

val condAddExt = store_thm (
   "condAddExt",
  ``!E E'. condCutExt E /\ condCutExt E' ==> condCutExt (add_extension E E')``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [condCutExt_def, RUNION]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      RES_TAC \\
      Q.EXISTS_TAC `Gamma'` \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      RES_TAC \\
      Q.EXISTS_TAC `Gamma'` \\
      ASM_REWRITE_TAC [] ]);

val CutNatDed = store_thm (
   "CutNatDed",
  ``!Delta A E Gamma C. natDed E Gamma C ==> condCutExt E ==> natDed E Delta A ==>
	!Gamma'. replace Gamma Gamma' (OneForm A) Delta ==> natDed E Gamma' C``,
    NTAC 2 GEN_TAC
 >> Induct_on `natDed`
 >> REPEAT CONJ_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      fix [`E`, `C`] >> rpt STRIP_TAC					\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv1))			\\
      RW_TAC std_ss []							\\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 8) *)
      fix [`E`, `Gamma`, `C`, `B`] >> rpt STRIP_TAC			\\
      MATCH_MP_TAC SlashIntro						\\
      IMP_RES_TAC replaceLeft						\\
      POP_ASSUM (ASSUME_TAC o (SPEC ``(OneForm B)``))			\\
      RES_TAC,
      (* goal 3 (of 8) *)
      fix [`E`, `Gamma`, `C`, `B`] >> rpt STRIP_TAC			\\
      MATCH_MP_TAC BackslashIntro					\\
      IMP_RES_TAC replaceRight						\\
      POP_ASSUM (ASSUME_TAC o (SPEC ``(OneForm B)``))			\\
      RES_TAC,
      (* goal 4 (of 8) *)
      fix [`E`, `Gamma`, `Gamma'`, `C`, `C'`] >> rpt STRIP_TAC		\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        ASM_REWRITE_TAC []						\\
        MATCH_MP_TAC DotIntro						\\
        CONJ_TAC >- RES_TAC						\\
        ASM_REWRITE_TAC [],
        (* goal 4.2 (of 2) *)
        ASM_REWRITE_TAC []						\\
        MATCH_MP_TAC DotIntro						\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        RES_TAC ],
      (* goal 5 (of 8) *)
      fix [`E`, `Gamma`, `Gamma'`, `C`, `C'`] >> rpt STRIP_TAC		\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
      REPEAT STRIP_TAC (* 2 sub-goals here, same tacticals *)		\\
      ASM_REWRITE_TAC []						\\
      MATCH_MP_TAC SlashElim						\\
      Q.EXISTS_TAC `C'`							\\
      ASM_REWRITE_TAC [] >> RES_TAC,
      (* goal 6 (of 8) *)
      fix [`E`, `Gamma`, `Gamma'`, `C`, `C'`] >> rpt STRIP_TAC		\\
      POP_ASSUM (MP_TAC o (MATCH_MP replace_inv2))			\\
      REPEAT STRIP_TAC (* 2 sub-goals here, same tacticals *)		\\
      ASM_REWRITE_TAC []						\\
      MATCH_MP_TAC BackslashElim					\\
      Q.EXISTS_TAC `C'`							\\
      ASM_REWRITE_TAC [] >> RES_TAC,
      (* goal 7 (of 8) *)
      fix [`E`, `Gamma`, `Gamma'`, `Gamma''`, `A'`, `B`, `C'`]		\\
      REPEAT STRIP_TAC							\\
      PAT_X_ASSUM ``replace Gamma Gamma' (Comma (OneForm A') (OneForm B)) Gamma''``
	(ASSUME_TAC o (MATCH_MP doubleReplace))				\\
      POP_ASSUM (ASSUME_TAC o (Q.SPECL [`Gamma'''`, `A`, `Delta`]))	\\
      RES_TAC (* 2 sub-goals here, same tactical *)			\\
      IMP_RES_TAC DotElim,
      (* goal 8 (of 8) *)
      fix [`E`, `C`, `Gamma`, `Gamma'`, `Delta'`, `Delta''`]		\\
      REPEAT STRIP_TAC							\\
      PAT_X_ASSUM ``condCutExt E ==> P``
	(ASSUME_TAC o
	  (fn thm => (MATCH_MP thm (ASSUME ``condCutExt E``))))		\\
      PAT_X_ASSUM ``natDed E Delta A ==> P``
	(ASSUME_TAC o
	  (fn thm => (MATCH_MP thm (ASSUME ``natDed E Delta A``))))	\\
      PAT_X_ASSUM ``condCutExt E``
	(ASSUME_TAC o (REWRITE_RULE [condCutExt_def]))			\\
      PAT_X_ASSUM ``replace Gamma Gamma' Delta' Delta''``
	(ASSUME_TAC o (MATCH_MP doubleReplace))				\\
      POP_ASSUM (ASSUME_TAC o (Q.SPECL [`Gamma''`, `A`, `Delta`]))	\\
      POP_ASSUM (MP_TAC o
	(fn thm => (MATCH_MP
		     thm (ASSUME ``replace Gamma' Gamma'' (OneForm A) Delta``)))) \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
	MATCH_MP_TAC NatExt						\\
	Q.EXISTS_TAC `G`						\\
	Q.EXISTS_TAC `Delta'`						\\
	Q.EXISTS_TAC `Delta''`						\\
	CONJ_TAC >- ASM_REWRITE_TAC []					\\
	CONJ_TAC >- ASM_REWRITE_TAC []					\\
	PAT_X_ASSUM ``!Gamma'. replace Gamma Gamma' (OneForm A) Delta ==> P``
	  (ASSUME_TAC o (Q.SPEC `G`))					\\
	RES_TAC,
        (* goal 8.2 (of 2) *)
        PAT_X_ASSUM ``!Gamma T1 T2 A Delta. E T1 T2 ==> P``
	  (ASSUME_TAC o
	    (Q.SPECL [`G`, `Delta'`, `Delta''`, `A`, `Delta`]))		\\
        POP_ASSUM (ASSUME_TAC o
	  (fn thm => (MP thm (ASSUME ``(E :'a gentzen_extension) Delta' Delta''``)))) \\
        POP_ASSUM (ASSUME_TAC o
	  (fn thm => (MP thm (ASSUME ``replace Delta'' G (OneForm A) Delta``)))) \\
        POP_ASSUM MP_TAC >> STRIP_TAC					\\
        PAT_X_ASSUM ``replace Gamma Gamma'' Delta' G``
	  (ASSUME_TAC o (MATCH_MP replaceSameP))			\\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Gamma'''`))			\\
        POP_ASSUM (Q.X_CHOOSE_TAC `G'`)					\\
        POP_ASSUM MP_TAC >> STRIP_TAC					\\
        MATCH_MP_TAC NatExt						\\
        Q.EXISTS_TAC `G'`						\\
        Q.EXISTS_TAC `Gamma'''`						\\
        Q.EXISTS_TAC `G`						\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        PAT_X_ASSUM ``!Gamma'. P`` MATCH_MP_TAC				\\
        MATCH_MP_TAC replaceTrans'					\\
        Q.EXISTS_TAC `Delta'`						\\
        Q.EXISTS_TAC `Gamma'''`						\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        ASM_REWRITE_TAC [] ] ] );

val natDedComposition = store_thm (
   "natDedComposition",
  ``!E Gamma F1 F2. condCutExt E /\ natDed E Gamma F1 /\ natDed E (OneForm F1) F2
		==> natDed E Gamma F2``,
    REPEAT STRIP_TAC
 >> irule CutNatDed
 >> ASM_REWRITE_TAC []
 >> take [`F1`, `Gamma`, `OneForm F1`]
 >> RW_TAC std_ss [replaceRoot]);

(* The easy direction, doesn't depend on new theorems in this section *)
val natDedToGentzen = store_thm (
   "natDedToGentzen",
  ``!E Gamma C. natDed E Gamma C ==> gentzenSequent E Gamma C``,
    HO_MATCH_MP_TAC natDed_ind (* or: Induct_on `natDed` *)
 >> REPEAT STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      REWRITE_TAC [SeqAxiom],
      (* goal 2 (of 8) *)
      MATCH_MP_TAC RightSlash						\\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 8) *)
      MATCH_MP_TAC RightBackslash					\\
      ASM_REWRITE_TAC [],
      (* goal 4 (of 8) *)
      MATCH_MP_TAC RightDot						\\
      ASM_REWRITE_TAC [],
      (* goal 5 (of 8) *)
      MATCH_MP_TAC CutRule						\\
      Q.EXISTS_TAC `Gamma` (* for Delta' *)				\\
      EXISTS_TAC ``(Comma (OneForm (Slash A B)) Delta)``		\\
      EXISTS_TAC ``(Slash A B)``					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        MATCH_MP_TAC replaceLeft					\\
        REWRITE_TAC [replaceRoot],
        (* goal 5.2 (of 2) *)
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        MATCH_MP_TAC LeftSlashSimpl					\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        REWRITE_TAC [SeqAxiom] ],
      (* goal 6 (of 8) *)
      MATCH_MP_TAC CutRule						\\
      Q.EXISTS_TAC `Delta`						\\
      EXISTS_TAC ``(Comma Gamma (OneForm (Backslash B A)))``		\\
      EXISTS_TAC ``(Backslash B A)``					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        MATCH_MP_TAC replaceRight					\\
        REWRITE_TAC [replaceRoot],
        (* goal 6.2 (of 2) *)
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        MATCH_MP_TAC LeftBackslashSimpl					\\
        CONJ_TAC >- ASM_REWRITE_TAC []					\\
        REWRITE_TAC [SeqAxiom] ],
      (* goal 7 (of 8) *)
      MATCH_MP_TAC replaceGentzen'					\\
      Q.EXISTS_TAC `Gamma`						\\
      EXISTS_TAC ``(Comma (OneForm A) (OneForm B))``			\\
      Q.EXISTS_TAC `Delta`						\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      REWRITE_TAC [deltaTranslation_def]				\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      ASM_REWRITE_TAC [],
      (* goal 8 (of 8) *)
      MP_TAC (SPEC_ALL SeqExt) >> REPEAT STRIP_TAC			\\
      RES_TAC ]);

(* The hard direction, heavily depends on theorems proved recently *)
val gentzenToNatDed = store_thm (
   "gentzenToNatDed",
  ``!E Gamma C. gentzenSequent E Gamma C ==> condCutExt E ==> natDed E Gamma C``,
    HO_MATCH_MP_TAC gentzenSequent_ind (* or: Induct_on `gentzenSequent` *)
 >> REPEAT CONJ_TAC (* 9 sub-goals here *)
 >| [ (* goal 1 (of 9) *)
      fix [`E`, `C`] >> rpt STRIP_TAC					\\
      REWRITE_TAC [NatAxiom],
      (* goal 2 (of 9) *)
      fix [`E`, `Gamma`, `C`, `B`] >> rpt STRIP_TAC			\\
      RES_TAC								\\
      MATCH_MP_TAC SlashIntro >> ASM_REWRITE_TAC [],
      (* goal 3 (of 9) *)
      fix [`E`, `Gamma`, `C`, `B`] >> rpt STRIP_TAC			\\
      RES_TAC								\\
      MATCH_MP_TAC BackslashIntro >> ASM_REWRITE_TAC [],
      (* goal 4 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `C`, `C'`] >> rpt STRIP_TAC		\\
      RES_TAC								\\
      MATCH_MP_TAC DotIntro >> ASM_REWRITE_TAC [],
      (* goal 5 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `Gamma''`, `A`, `C`, `C'`]		\\
      REPEAT STRIP_TAC							\\
      MATCH_MP_TAC natDedComposition					\\
      EXISTS_TAC ``(deltaTranslation Gamma)``				\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        irule replaceNatDed						\\
        EXISTS_TAC ``(OneForm A)``					\\
        EXISTS_TAC ``(Comma (OneForm (Slash A C)) Gamma'')``		\\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 5.1.1 (of 2) *)
          REWRITE_TAC [deltaTranslation_def]				\\
          MATCH_MP_TAC SlashElim					\\
          Q.EXISTS_TAC `C`						\\
          CONJ_TAC >- REWRITE_TAC [NatAxiom] >> RES_TAC,
          (* goal 5.1.2 (of 2) *)
          ASM_REWRITE_TAC [] ],
        (* goal 5.2 (of 2) *)
        MATCH_MP_TAC NatTermToForm >> RES_TAC ],
      (* goal 6 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `Gamma''`, `A`, `C`, `C'`]		\\
      REPEAT STRIP_TAC							\\
      MATCH_MP_TAC natDedComposition					\\
      EXISTS_TAC ``(deltaTranslation Gamma)``				\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        irule replaceNatDed						\\
        EXISTS_TAC ``(OneForm A)``					\\
        EXISTS_TAC ``(Comma Gamma'' (OneForm (Backslash C A)))``	\\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 6.1.1 (of 2) *)
          REWRITE_TAC [deltaTranslation_def]				\\
          MATCH_MP_TAC BackslashElim					\\
          Q.EXISTS_TAC `C`						\\
          CONJ_TAC >- RES_TAC						\\
          REWRITE_TAC [NatAxiom],
          (* goal 6.1.2 (of 2) *)
          ASM_REWRITE_TAC [] ],
        (* goal 6.2 (of 2) *)
        MATCH_MP_TAC NatTermToForm >> RES_TAC ],
      (* goal 7 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `A`, `B`, `C`] >> rpt STRIP_TAC	\\
      MATCH_MP_TAC natDedComposition					\\
      EXISTS_TAC ``(deltaTranslation Gamma)``				\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 7.1 (of 2) *)
        irule replaceNatDed						\\
        EXISTS_TAC ``(Comma (OneForm A) (OneForm B))``			\\
        EXISTS_TAC ``(OneForm (Dot A B))``				\\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 7.1.1 (of 2) *)
          REWRITE_TAC [deltaTranslation_def]				\\
          REWRITE_TAC [NatAxiom],
          (* goal 7.1.2 (of 2) *)
          ASM_REWRITE_TAC [] ],
        (* goal 7.2 (of 2) *)
        MATCH_MP_TAC NatTermToForm >> RES_TAC ],
      (* goal 8 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `Gamma''`, `C`, `C'`]		\\
      REPEAT STRIP_TAC							\\	
      MATCH_MP_TAC natDedComposition					\\
      EXISTS_TAC ``(deltaTranslation Gamma')``				\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
        irule replaceNatDed						\\
        EXISTS_TAC ``(OneForm C)``					\\
        Q.EXISTS_TAC `Gamma`						\\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 8.1.1 (of 2) *)
          REWRITE_TAC [deltaTranslation_def] >> RES_TAC,
          (* goal 8.1.2 (of 2) *)
          ASM_REWRITE_TAC [] ],
        (* goal 8.2 (of 2) *)
        MATCH_MP_TAC NatTermToForm >> RES_TAC ],
      (* goal 9 (of 9) *)
      fix [`E`, `Gamma`, `Gamma'`, `Delta`, `Delta'`, `C`]		\\
      REPEAT STRIP_TAC							\\
      MATCH_MP_TAC NatExt						\\
      Q.EXISTS_TAC `Gamma`						\\
      Q.EXISTS_TAC `Delta`						\\
      Q.EXISTS_TAC `Delta'`						\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      CONJ_TAC >- ASM_REWRITE_TAC []					\\
      RES_TAC ]);

val gentzenEqNatDed = store_thm (
   "gentzenEqNatDed",
  ``!E Gamma C. condCutExt E ==> (gentzenSequent E Gamma C = natDed E Gamma C)``,
    REPEAT STRIP_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      irule gentzenToNatDed \\ (* 2 sub-goals sharing the same tactical *)
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [natDedToGentzen] ]);

val NLgentzenEqNatDed = store_thm (
   "NLgentzenEqNatDed",
  ``!Gamma C. gentzenSequent NL_Sequent Gamma C = natDed NL_Sequent Gamma C``,
    REPEAT STRIP_TAC
 >> MP_TAC conditionOKNL
 >> REWRITE_TAC [gentzenEqNatDed]);

val LgentzenEqNatDed = store_thm (
   "LgentzenEqNatDed",
  ``!Gamma C. gentzenSequent L_Sequent Gamma C = natDed L_Sequent Gamma C``,
    REPEAT STRIP_TAC
 >> MP_TAC conditionOKL
 >> REWRITE_TAC [gentzenEqNatDed]);

val NLPgentzenEqNatDed = store_thm (
   "NLPgentzenEqNatDed",
 ``!Gamma C. gentzenSequent NLP_Sequent Gamma C = natDed NLP_Sequent Gamma C``,
    REPEAT STRIP_TAC
 >> MP_TAC conditionOKNLP
 >> REWRITE_TAC [gentzenEqNatDed]);

(******************************************************************************)
(*                                                                            *)
(*                    Module: Arrow and Natural Deduction                     *)
(*                                                                            *)
(******************************************************************************)

val natDedToArrow = store_thm (
   "natDedToArrow",
  ``!E X Gamma A. gentzenToArrowExt E X ==>
                  natDed E Gamma A ==> arrow X (deltaTranslation Gamma) A``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC gentzenToArrow
 >> Q.EXISTS_TAC `E`
 >> CONJ_TAC
 >- ASM_REWRITE_TAC []
 >> MATCH_MP_TAC natDedToGentzen
 >> ASM_REWRITE_TAC []);

val natDedToArrow_E = store_thm (
   "natDedToArrow_E",
  ``!E Gamma A. natDed E Gamma A ==> arrow (ToArrowExt E) (deltaTranslation Gamma) A``,
    REPEAT GEN_TAC
 >> MP_TAC (Q.SPEC `E` gentzenToArrowExt_thm)
 >> REWRITE_TAC [natDedToArrow]);

val arrowToNatDed = store_thm (
   "arrowToNatDed",
  ``!E X A B. condCutExt E /\ arrowToGentzenExt X E /\ arrow X A B
	  ==> natDed E (OneForm A) B``,
    REPEAT STRIP_TAC
 >> irule gentzenToNatDed
 >> ASM_REWRITE_TAC []
 >> irule arrowToGentzen
 >> Q.EXISTS_TAC `X`
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                          Grammar support in HOL                            *)
(*                                                                            *)
(******************************************************************************)

fun enable_grammar () = let
in
    add_rule { term_name = "arrow", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK ":-", BreakSpace(1,0), TM, BreakSpace(1,0), TOK "-->",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

    add_rule { term_name = "natDed", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK ":-", BreakSpace(1,0), TM, BreakSpace(1,0), TOK "|-n",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

    add_rule { term_name = "gentzenSequent", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK ":-", BreakSpace(1,0), TM, BreakSpace(1,0), TOK "|-g",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

    add_rule { term_name = "Sequent", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK ":-", BreakSpace(1,0), TM, BreakSpace(1,0), TOK "|-",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) }
end;

val _ = enable_grammar ();

val _ = export_theory ();
val _ = html_theory "Lambek";

(* last updated: April 10, 2017 *)
