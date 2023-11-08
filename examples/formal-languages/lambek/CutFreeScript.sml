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

open relationTheory prim_recTheory arithmeticTheory listTheory;
open LambekTheory;

local
    val PAT_X_ASSUM = PAT_ASSUM;
    val qpat_x_assum = Q.PAT_ASSUM;
    open Tactical
in
    (* Backward compatibility with Kananaskis 11 *)
    val PAT_X_ASSUM = PAT_X_ASSUM;
    val qpat_x_assum = qpat_x_assum;

    (* Tacticals for better expressivity *)
    fun fix  ts = MAP_EVERY Q.X_GEN_TAC ts;     (* from HOL Light *)
    fun set  ts = MAP_EVERY Q.ABBREV_TAC ts;    (* from HOL mizar mode *)
    fun take ts = MAP_EVERY Q.EXISTS_TAC ts;    (* from HOL mizar mode *)
end;

val _ = new_theory "CutFree";

val _ = hide "S";

(*** Module: CutSequent ***)

(* this theorem was not in HOL kananaskis-11 final release, it's new in K-12 *)
val MAX_EQ_0 = store_thm (
   "MAX_EQ_0",
  ``(MAX m n = 0) <=> (m = 0) /\ (n = 0)``,
    SRW_TAC [] [MAX_DEF, EQ_IMP_THM]
 >> FULL_SIMP_TAC (srw_ss()) [NOT_LESS_0, NOT_LESS]);

val maxNatL = store_thm ("maxNatL",
  ``(MAX n m = 0) ==> (n = 0)``, RW_TAC std_ss [MAX_EQ_0]);
val maxNatR = store_thm ("maxNatR",
  ``(MAX n m = 0) ==> (m = 0)``, RW_TAC std_ss [MAX_EQ_0]);

val degreeFormula_def = Define `
   (degreeFormula (At C) = 1) /\
   (degreeFormula (Slash F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2))) /\
   (degreeFormula (Backslash F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2))) /\
   (degreeFormula (Dot F1 F2) = SUC (MAX (degreeFormula F1) (degreeFormula F2)))`;

val degreeForm_0 = store_thm ("degreeForm_0", ``!F0. 1 <= (degreeFormula F0)``,
    Induct >> rw [degreeFormula_def]);

(* Deep Embeddings for Lambek's Sequent Calculus *)
val _ = Datatype `Sequent = Sequent ('a gentzen_extension) ('a Term) ('a Form)`;

val _ = Datatype `Rule = SeqAxiom
                       | RightSlash | RightBackslash | RightDot
                       | LeftSlash  | LeftBackslash  | LeftDot
                       | CutRule    | SeqExt`;

val all_rules_def = Define `
    all_rules =
        { SeqAxiom; RightSlash; RightBackslash; RightDot;
          LeftSlash; LeftBackslash; LeftDot; SeqExt; CutRule }`;

(* Note: (Dertree list) never has more than 2 elements in Lambek's Sequent Calculus *)
val _ = Datatype `Dertree = Der ('a Sequent) Rule (Dertree list)
                          | Unf ('a Sequent)`;

val Dertree_induction = TypeBase.induction_of ``:'a Dertree``;
val Dertree_nchotomy  = TypeBase.nchotomy_of ``:'a Dertree``;
val Dertree_distinct  = TypeBase.distinct_of ``:'a Dertree``;
val Dertree_distinct' = save_thm ("Dertree_distinct'", GSYM Dertree_distinct);
val Dertree_11        = TypeBase.one_one_of ``:'a Dertree``;

(* not used *)
val Is_Unfinished_def = Define `
   (Is_Unfinished (Der _ _ []) = F) /\
   (Is_Unfinished (Der _ _ [D]) = Is_Unfinished D) /\
   (Is_Unfinished (Der _ _ [D1; D2]) = (Is_Unfinished D1 /\ Is_Unfinished D2)) /\
   (Is_Unfinished (Unf _) = T)`;

(* not used *)
val Is_Finished_def = Define `
   (Is_Finished (Der _ _ []) = T) /\
   (Is_Finished (Der _ _ [D]) = Is_Finished D) /\
   (Is_Finished (Der _ _ [D1; D2]) = (Is_Finished D1 /\ Is_Finished D2)) /\
   (Is_Finished (Unf _) = F)`;

(* structure accessors *)
val head_def = Define `
   (head (Der seq _ _) = seq) /\
   (head (Unf seq) = seq)`;

val concl_def = Define `
   (concl (Unf (Sequent E Delta A))     = A) /\
   (concl (Der (Sequent E Delta A) _ _) = A)`;

val prems_def = Define `
   (prems (Unf (Sequent E Delta A))     = Delta) /\
   (prems (Der (Sequent E Delta A) _ _) = Delta)`;

val exten_def = Define `
   (exten (Unf (Sequent E Delta A))     = E) /\
   (exten (Der (Sequent E Delta A) _ _) = E)`;

val degreeRule_def = Define `
   (degreeRule (Der S SeqAxiom [])              = 0) /\
   (degreeRule (Der S RightSlash [H])           = 0) /\
   (degreeRule (Der S RightBackslash [H])       = 0) /\
   (degreeRule (Der S RightDot [H1; H2])        = 0) /\
   (degreeRule (Der S LeftSlash [H1; H2])       = 0) /\
   (degreeRule (Der S LeftBackslash [H1; H2])   = 0) /\
   (degreeRule (Der S LeftDot [H])              = 0) /\
   (degreeRule (Der S SeqExt [H])               = 0) /\
   (* The degree of a cut is the degree of the cut formula which disappears after
      application of the rule. *)
   (degreeRule (Der S CutRule [H1; H2])         = degreeFormula (concl H1))`;

(* degreeProof, one way to check if CutRule gets used *)
val degreeProof_def = Define `
   (degreeProof (Der S SeqAxiom [])             = 0) /\
   (degreeProof (Der S RightSlash [H])          = degreeProof H) /\
   (degreeProof (Der S RightBackslash [H])      = degreeProof H) /\
   (degreeProof (Der S RightDot [H1; H2])       = MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der S LeftSlash [H1; H2])      = MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der S LeftBackslash [H1; H2])  = MAX (degreeProof H1) (degreeProof H2)) /\
   (degreeProof (Der S LeftDot [H])             = degreeProof H) /\
   (degreeProof (Der S SeqExt [H])              = degreeProof H) /\
   (* CutRule is special *)
   (degreeProof (Der S CutRule [H1; H2])        =
        MAX (degreeFormula (concl H1))
            (MAX (degreeProof H1) (degreeProof H2)))`;

(* subFormula and their theorems *)
val (subFormula_rules, subFormula_ind, subFormula_cases) = Hol_reln `
    (!(A:'a Form).              subFormula A A) /\                      (* equalForm *)
    (!A B C. subFormula A B ==> subFormula A (Slash B C)) /\            (* slashL *)
    (!A B C. subFormula A B ==> subFormula A (Slash C B)) /\            (* slashR *)
    (!A B C. subFormula A B ==> subFormula A (Backslash B C)) /\        (* backslashL *)
    (!A B C. subFormula A B ==> subFormula A (Backslash C B)) /\        (* backslashR *)
    (!A B C. subFormula A B ==> subFormula A (Dot B C)) /\              (* dotL *)
    (!A B C. subFormula A B ==> subFormula A (Dot C B))`;               (* dotR *)

val [equalForm, slashL, slashR, backslashL, backslashR, dotL, dotR] =
    map save_thm
        (combine (["equalForm", "slashL", "slashR", "backslashL", "backslashR", "dotL", "dotR"],
                  CONJUNCTS subFormula_rules));

(* The simp set related to Form *)
val Form_ss = DatatypeSimps.type_rewrites_ss [``:'a Form``];

val subAt = store_thm ("subAt", ``!A a. subFormula A (At a) ==> (A = At a)``,
    ONCE_REWRITE_TAC [subFormula_cases]
 >> SIMP_TAC bool_ss [Form_distinct]); (* or: SIMP_TAC (bool_ss ++ Form_ss) [] *)

val subSlash = store_thm ("subSlash",
  ``!A B C. subFormula A (Slash B C) ==> (A = Slash B C) \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Slash B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ Form_ss) [EQ_SYM_EQ]);

val subBackslash = store_thm ("subBackslash",
  ``!A B C. subFormula A (Backslash B C) ==> (A = Backslash B C) \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Backslash B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ Form_ss) [EQ_SYM_EQ]);

val subDot = store_thm ("subDot",
  ``!A B C. subFormula A (Dot B C) ==> (A = Dot B C) \/ subFormula A B \/ subFormula A C``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [Q.SPECL [`A`, `(Dot B C)`] subFormula_cases]
 >> SIMP_TAC (bool_ss ++ Form_ss) [EQ_SYM_EQ]);

(* all previous theorems and rules were used in this proof ... *)
val subFormulaTrans = store_thm (
   "subFormulaTrans",
  ``!A B C. subFormula A B ==> subFormula B C ==> subFormula A C``,
    Induct_on `C`
 >| [ (* case 1 *)
      PROVE_TAC [subAt],
      (* case 2, can be proved by PROVE_TAC [subSlash, slashL, slashR] *)
      REPEAT STRIP_TAC \\
      POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP subSlash) >|
      [ PROVE_TAC [],
        PROVE_TAC [slashL],
        PROVE_TAC [slashR] ],
      (* case 3 *)
      PROVE_TAC [subBackslash, backslashL, backslashR],
      (* case 4 *)
      PROVE_TAC [subDot, dotL, dotR] ]);

val subFormulaTrans' = store_thm (
   "subFormulaTrans'", ``transitive subFormula``,
    PROVE_TAC [subFormulaTrans, transitive_def]);

(* subFormTerm *)
val (subFormTerm_rules, subFormTerm_ind, subFormTerm_cases) = Hol_reln `
    (!A B.     subFormula  A B  ==> subFormTerm A (OneForm B)) /\       (* eqFT *)
    (!A T1 T2. subFormTerm A T1 ==> subFormTerm A (Comma T1 T2)) /\     (* comL *)
    (!A T1 T2. subFormTerm A T1 ==> subFormTerm A (Comma T2 T1))`;      (* comR *)

val [eqFT, comL, comR] =
    map save_thm (combine (["eqFT", "comL", "comR"], CONJUNCTS subFormTerm_rules));

val Term_11 = TypeBase.one_one_of ``:'a Term``;
val Term_distinct = TypeBase.distinct_of ``:'a Term``;

val oneFormSub = store_thm (
   "oneFormSub", ``!A B. subFormTerm A (OneForm B) ==> subFormula A B``,
    ONCE_REWRITE_TAC [subFormTerm_cases]
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [Term_11],
      PROVE_TAC [Term_distinct],
      PROVE_TAC [Term_distinct] ]);

val oneFormSubEQ = store_thm (
   "oneFormSubEQ[simp]", ``!A B. subFormTerm A (OneForm B) = subFormula A B``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ REWRITE_TAC [oneFormSub],
      REWRITE_TAC [eqFT] ]);

val comSub = store_thm ("comSub",
  ``!f T1 T2. subFormTerm f (Comma T1 T2) ==> subFormTerm f T1 \/ subFormTerm f T2``,
    REPEAT GEN_TAC
 >> GEN_REWRITE_TAC LAND_CONV empty_rewrites [Once subFormTerm_cases]
 >> REPEAT STRIP_TAC
 >| [ PROVE_TAC [Term_distinct],
      PROVE_TAC [Term_11],
      PROVE_TAC [Term_11] ]);

val subReplace1 = store_thm ("subReplace1",
  ``!f T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm f T3 ==> subFormTerm f T1``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >- PROVE_TAC [comL]
 >> PROVE_TAC [comR]);

val subReplace2 = store_thm ("subReplace2",
  ``!f T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm f T4 ==> subFormTerm f T2``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >- PROVE_TAC [comL]
 >> PROVE_TAC [comR]);

val subReplace3 = store_thm ("subReplace3",
  ``!X T1 T2 T3 T4. replace T1 T2 T3 T4 ==> subFormTerm X T1
                ==> subFormTerm X T2 \/ subFormTerm X T3``,
    GEN_TAC
 >> HO_MATCH_MP_TAC replace_ind
 >> REPEAT STRIP_TAC
 >- ASM_REWRITE_TAC []
 >| [ (* case 2 *)
      `subFormTerm X T1 \/ subFormTerm X Delta` by PROVE_TAC [comSub] >|
      [ `subFormTerm X T2 \/ subFormTerm X T3` by PROVE_TAC [] \\
        PROVE_TAC [comL],
        PROVE_TAC [comR] ],
      (* case 3 *)
      `subFormTerm X Delta \/ subFormTerm X T1` by PROVE_TAC [comSub] >|
      [ PROVE_TAC [comL],
        `subFormTerm X T2 \/ subFormTerm X T3` by PROVE_TAC [] \\
        PROVE_TAC [comR] ] ]);

val CutFreeProof_def = Define `
    CutFreeProof p = (degreeProof p = 0)`;

val notCutFree = store_thm ("notCutFree",
  ``!E T1 T2 D A C p p1 p2.
     replace T1 T2 (OneForm A) D /\
     (p1 = Sequent E D A) /\ (p2 = Sequent E T1 C) ==>
     ~CutFreeProof (Der _ CutRule [Der p1 _ _; Der p2 _ _])``,
    REPEAT GEN_TAC
 >> STRIP_TAC
 >> REWRITE_TAC [CutFreeProof_def]
 >> RW_TAC std_ss [degreeProof_def, concl_def]
 >> STRIP_TAC
 >> `1 <= degreeFormula A` by REWRITE_TAC [degreeForm_0]
 >> `degreeFormula A = 0` by PROVE_TAC [MAX_EQ_0]
 >> RW_TAC arith_ss []);

val (subProofOne_rules, subProofOne_ind, subProofOne_cases) = Hol_reln `
    (!p0 p E Gamma A B R D.
                (p0 = Sequent E Gamma (Slash A B)) /\
                (p = Der (Sequent E (Comma Gamma (OneForm B)) A) R D)
            ==> subProofOne p  (Der p0 RightSlash [p]))                 /\ (* 1. rs *)

    (!p0 p E Gamma A B R D.
                (p0 = Sequent E Gamma (Backslash B A)) /\
                (p = Der (Sequent E (Comma (OneForm B) Gamma) A) R D)
            ==> subProofOne p  (Der p0 RightBackslash [p]))             /\ (* 2. rbs *)

    (!p0 p1 p2 E Gamma Delta A B R D.
                (p0 = Sequent E (Comma Gamma Delta) (Dot A B)) /\
                (p1 = Der (Sequent E Gamma A) R D) /\
                (p2 = Der (Sequent E Delta B) R D)
            ==> subProofOne p1 (Der p0 RightDot  [p1; p2]))             /\ (* 3. rd1 *)

    (!p0 p1 p2 E Gamma Delta A B R D.
                (p0 = Sequent E (Comma Gamma Delta) (Dot A B)) /\
                (p1 = Der (Sequent E Gamma A) R D) /\
                (p2 = Der (Sequent E Delta B) R D)
            ==> subProofOne p2 (Der p0 RightDot  [p1; p2]))             /\ (* 4. rd2 *)

    (!p0 p1 p2 E Gamma Gamma' Delta A B C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta B) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                (replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta))
            ==> subProofOne p1 (Der p0 LeftSlash [p1; p2]))             /\ (* 5. ls1 *)

    (!p0 p1 p2 E Gamma Gamma' Delta A B C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta B) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta)
            ==> subProofOne p2 (Der p0 LeftSlash [p1; p2]))             /\ (* 6. ls2 *)

    (!p0 p1 p2 E Gamma Gamma' Delta A B C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta B) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A)))
            ==> subProofOne p1 (Der p0 LeftBackslash [p1; p2]))         /\ (* 7. lbs1 *)

    (!p0 p1 p2 E Gamma Gamma' Delta A B C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta B) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A)))
            ==> subProofOne p2 (Der p0 LeftBackslash [p1; p2]))         /\ (* 8. lbs2 *)

    (!p0 p E Gamma Gamma' A B C R D.
                (p0 = Sequent E Gamma' C) /\
                (p = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B))
            ==> subProofOne p  (Der p0 LeftDot [p]))                    /\ (* 9. ld *)

    (!p0 p1 p2 E Gamma Gamma' Delta A C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta A) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (OneForm A) Delta
            ==> subProofOne p1 (Der p0 CutRule [p1; p2]))               /\ (* 10. cr1 *)

    (!p0 p1 p2 E Gamma Gamma' Delta A C R D.
                (p0 = Sequent E Gamma' C) /\
                (p1 = Der (Sequent E Delta A) R D) /\
                (p2 = Der (Sequent E Gamma C) R D) /\
                replace Gamma Gamma' (OneForm A) Delta
            ==> subProofOne p2 (Der p0 CutRule [p1; p2]))               /\ (* 11. cr2 *)

    (!p0 p E Gamma Gamma' T1 T2 C R D.
                (p0 = Sequent E Gamma' C) /\
                (p = Der (Sequent E Gamma C) R D) /\
                (E :'a gentzen_extension) T1 T2 /\
                replace Gamma Gamma' T1 T2
            ==> subProofOne p  (Der p0 SeqExt [p])) `;                     (* se *)

val [rs, rbs, rd1, rd2, ls1, ls2, lbs1, lbs2, ld, cr1, cr2, se] =
    map save_thm
        (combine (["rs", "rbs", "rd1", "rd2", "ls1", "ls2", "lbs1", "lbs2",
                   "ld", "cr1", "cr2", "se"],
                  CONJUNCTS subProofOne_rules));

(* (subProof :'a Dertree -> 'a Dertree -> bool) *)
val subProof_def = Define `subProof = RTC subProofOne`;

val sameProof = store_thm (
   "sameProof", ``!p. subProof p p``,
    REWRITE_TAC [subProof_def, RTC_REFL]);

val subProof1 = store_thm (
   "subProof1", ``!p1 p2 p3. subProofOne p1 p2 /\ subProof p2 p3 ==> subProof p1 p3``,
    REWRITE_TAC [subProof_def, RTC_RULES]);

val subProof_rules = save_thm (
   "subProof_rules", LIST_CONJ [sameProof, subProof1]);

(*
 |- ∀P.
     (∀x. P x x) ∧
     (∀x y z. subProofOne x y ∧ P y z ⇒ P x z) ⇒
     ∀x y. subProof x y ⇒ P x y
 *)
val subProof_ind = save_thm (
   "subProof_ind",
    REWRITE_RULE [GSYM subProof_def] (Q.ISPEC `subProofOne` RTC_INDUCT));

(*
 |- ∀P.
     (∀x. P x x) ∧
     (∀x y z. subProofOne x y ∧ subProof y z ∧ P y z ⇒ P x z) ⇒
     ∀x y. subProof x y ⇒ P x y:
 *)
val subProof_strongind = save_thm (
   "subProof_strongind",
    REWRITE_RULE [GSYM subProof_def] (Q.ISPEC `subProofOne` RTC_STRONG_INDUCT));

(*
 |- ∀x y. subProof x y ⇔ (x = y) ∨ ∃u. subProofOne x u ∧ subProof u y
 *)
val subProof_cases = save_thm (
   "subProof_cases",
    REWRITE_RULE [GSYM subProof_def] (Q.ISPEC `subProofOne` RTC_CASES1));

(*
 |- ∀x y. subProof x y ⇔ (x = y) ∨ ∃u. subProof x u ∧ subProofOne u y
 *)
val subProof_cases' = save_thm (
   "subProof_cases'",
    REWRITE_RULE [GSYM subProof_def] (Q.ISPEC `subProofOne` RTC_CASES2));

(* original code:
val (subProof'_rules, subProof'_ind, subProof'_cases) = Hol_reln `
    (!(p :'a Dertree). subProof' p p) /\
    (!p1 p2 p3. subProof' p2 p1 /\ subProofOne p3 p2 ==> subProof' p3 p1)`;
 *)

val CutFreeSubProofOne = store_thm ("CutFreeSubProofOne",
  ``!q p. subProofOne q p ==> CutFreeProof p ==> CutFreeProof q``,
    Induct_on `subProofOne`
 >> REWRITE_TAC [CutFreeProof_def, degreeProof_def]
 >> PROVE_TAC [MAX_EQ_0]);

val CutFreeSubProof = store_thm ("CutFreeSubProof",
  ``!q p. subProof q p ==> CutFreeProof p ==> CutFreeProof q``,
    REWRITE_TAC [subProof_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> PROVE_TAC [CutFreeSubProofOne]);

val extensionSub_def = Define `
    extensionSub E = !Form T1 T2. E T1 T2 ==> subFormTerm Form T1 ==> subFormTerm Form T2`;

val subProofOne_extension = store_thm (
   "subProofOne_extension",
  ``!q p. subProofOne q p ==>
          extensionSub (exten p) ==> extensionSub (exten q)``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [subProofOne_cases]
 >> REPEAT STRIP_TAC (* 12 subgoals, all sharing the same tacticals *)
 >> `extensionSub E` by METIS_TAC [exten_def]
 >> ASM_REWRITE_TAC [exten_def]);

val subProof_extension = store_thm (
   "subProof_extension",
  ``!q p. subProof q p ==>
          extensionSub (exten p) ==> extensionSub (exten q)``,
    HO_MATCH_MP_TAC subProof_strongind
 >> REPEAT STRIP_TAC
 >> RES_TAC
 >> IMP_RES_TAC subProofOne_extension);

(* one-step derivation (of proofs): Dertree -> Dertree -> bool *)
val (derivOne_rules, derivOne_ind, derivOne_cases) = Hol_reln `
    (!E A.
     derivOne (Unf (Sequent E (OneForm A) A))
        (Der (Sequent E (OneForm A) A) SeqAxiom [])) /\
    (!E Gamma A B.
     derivOne (Unf (Sequent E Gamma (Slash A B)))
        (Der (Sequent E Gamma (Slash A B)) RightSlash
             [ Unf (Sequent E (Comma Gamma (OneForm B)) A) ])) /\
    (!E Gamma A B.
     derivOne (Unf (Sequent E Gamma (Backslash B A)))
        (Der (Sequent E Gamma (Backslash B A)) RightBackslash
             [ Unf (Sequent E (Comma (OneForm B) Gamma) A) ])) /\
    (!E Gamma Delta A B.
     derivOne (Unf (Sequent E (Comma Gamma Delta) (Dot A B)))
        (Der (Sequent E (Comma Gamma Delta) (Dot A B)) RightDot
             [ Unf (Sequent E Gamma A); Unf (Sequent E Delta B) ])) /\
    (!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) ==>
     derivOne (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftSlash
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta B) ])) /\
    (!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A))) ==>
     derivOne (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftBackslash
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta B) ])) /\
    (!E Gamma Gamma' A B C.
     replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ==>
     derivOne (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftDot
             [ Unf (Sequent E Gamma C) ])) /\
    (!E Delta Gamma Gamma' A C.
     replace Gamma Gamma' (OneForm A) Delta ==>
     derivOne (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) CutRule
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta A) ])) /\
    (!E Gamma Gamma' Delta Delta' C.
     replace Gamma Gamma' Delta Delta' /\ E Delta Delta' ==>
     derivOne (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) SeqExt
             [ Unf (Sequent E Gamma C) ]))`;

val [derivSeqAxiom, derivRightSlash, derivRightBackslash, derivRightDot,
     derivLeftSlash, derivLeftBackslash, derivLeftDot, derivCutRule, derivSeqExt] =
    map save_thm
        (combine (["derivSeqAxiom", "derivRightSlash", "derivRightBackslash",
                   "derivRightDot", "derivLeftSlash", "derivLeftBackslash",
                   "derivLeftDot", "derivCutRule", "derivSeqExt"],
                  CONJUNCTS derivOne_rules));

(* structure rules *)
val (deriv_rules, deriv_ind, deriv_cases) = Hol_reln `
    (!D1 D2.          derivOne D1 D2  ==> deriv D1 D2)                                  /\
    (!S R D1 D1'.        deriv D1 D1' ==> deriv (Der S R [D1])    (Der S R [D1']))      /\
    (!S R D1 D1' D.      deriv D1 D1' ==> deriv (Der S R [D1; D]) (Der S R [D1'; D]))   /\
    (!S R D2 D2' D.      deriv D2 D2' ==> deriv (Der S R [D; D2]) (Der S R [D; D2']))   /\
    (!S R D1 D1' D2 D2'. deriv D1 D1' /\ deriv D2 D2'
                     ==> deriv (Der S R [D1; D2]) (Der S R [D1'; D2']))`;

val [derivDerivOne, derivOne, derivLeft, derivRight, derivBoth] =
    map save_thm
        (combine (["derivDerivOne", "derivOne", "derivLeft", "derivRight", "derivBoth"],
                  CONJUNCTS deriv_rules));

(* closure rules, in this way we can finish a proof *)
val Deriv_def = Define `Deriv = RTC deriv`;

(* |- ∀x. Deriv x x *)
val Deriv_refl  = save_thm (
   "Deriv_refl",
    REWRITE_RULE [SYM Deriv_def]
        (((Q.ISPEC `deriv`) o (Q.GEN `R`) o (Q.GEN `x`)) RTC_REFL));

(* |- ∀x y z. Deriv x y ∧ Deriv y z ⇒ Deriv x z *)
val Deriv_trans = save_thm (
   "Deriv_trans",
    REWRITE_RULE [SYM Deriv_def]
        (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)));

fun derivToDeriv thm =
    REWRITE_RULE [SYM Deriv_def] (MATCH_MP RTC_SINGLE thm);

fun derivOneToDeriv thm =
    REWRITE_RULE [GSYM Deriv_def]
      (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE)
        (MATCH_MP derivDerivOne (SPEC_ALL thm)));

(* derivation rules expressed in relation `Deriv`, for convinence *)

(* |- ∀E A.
     Deriv (Unf (E:- OneForm A |- A))
       (Der (E:- OneForm A |- A) SeqAxiom [])
 *)
val DerivSeqAxiom = save_thm (
   "DerivSeqAxiom",
  ((Q.GEN `E`) o (Q.GEN `A`) o derivOneToDeriv) derivSeqAxiom);

val DerivRightSlash = save_thm (
   "DerivRightSlash",
  ((Q.GEN `E`) o (Q.GEN `Gamma`) o (Q.GEN `A`) o (Q.GEN `B`) o
    derivOneToDeriv) derivRightSlash);

val DerivRightBackslash = save_thm (
   "DerivRightBackslash",
  ((Q.GEN `E`) o (Q.GEN `Gamma`) o (Q.GEN `A`) o (Q.GEN `B`) o
    derivOneToDeriv) derivRightBackslash);

val DerivRightDot = save_thm (
   "DerivRightDot",
  ((Q.GEN `E`) o (Q.GEN `Gamma`) o (Q.GEN `Delta`) o (Q.GEN `A`) o (Q.GEN `B`) o
    derivOneToDeriv) derivRightDot);

val DerivLeftSlash = store_thm (
   "DerivLeftSlash",
  ``!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) ==>
     Deriv (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftSlash
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta B) ])``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC (Q.ISPEC `deriv` RTC_SINGLE)
 >> MATCH_MP_TAC derivDerivOne
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [derivLeftSlash]);

val DerivLeftBackslash = store_thm (
   "DerivLeftBackslash",
  ``!E Gamma Gamma' Delta A B C.
     replace Gamma Gamma' (OneForm A) (Comma Delta (OneForm (Backslash B A))) ==>
     Deriv (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftBackslash
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta B) ])``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC (Q.ISPEC `deriv` RTC_SINGLE)
 >> MATCH_MP_TAC derivDerivOne
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [derivLeftBackslash]);

val DerivLeftDot = store_thm (
   "DerivLeftDot",
  ``!E Gamma Gamma' A B C.
     replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ==>
     Deriv (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) LeftDot
             [ Unf (Sequent E Gamma C) ])``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC (Q.ISPEC `deriv` RTC_SINGLE)
 >> MATCH_MP_TAC derivDerivOne
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [derivLeftDot]);

val DerivCutRule = store_thm (
   "DerivCutRule",
  ``!E Delta Gamma Gamma' A C.
     replace Gamma Gamma' (OneForm A) Delta ==>
     Deriv (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) CutRule
             [ Unf (Sequent E Gamma C); Unf (Sequent E Delta A) ])``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC (Q.ISPEC `deriv` RTC_SINGLE)
 >> MATCH_MP_TAC derivDerivOne
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [derivCutRule]);

val DerivSeqExt = store_thm (
   "DerivSeqExt",
  ``!E Gamma Gamma' Delta Delta' C.
     replace Gamma Gamma' Delta Delta' /\ E Delta Delta' ==>
     Deriv (Unf (Sequent E Gamma' C))
        (Der (Sequent E Gamma' C) SeqExt
             [ Unf (Sequent E Gamma C) ])``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC (Q.ISPEC `deriv` RTC_SINGLE)
 >> MATCH_MP_TAC derivDerivOne
 >> PROVE_TAC [derivSeqExt]);

val DerivOne = store_thm ("DerivOne",
  ``!S R D1 D1'. Deriv D1 D1' ==> Deriv (Der S R [D1]) (Der S R [D1'])``,
    NTAC 2 GEN_TAC
 >> REWRITE_TAC [Deriv_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> REPEAT STRIP_TAC (* 2 sub-goals here, first one is easy *)
 >- REWRITE_TAC [RTC_REFL]
 >> PAT_X_ASSUM ``deriv D1 D1'`` (ASSUME_TAC o (MATCH_MP derivOne))
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE))
                          o (SPECL [``S :'a Sequent``, ``R :Rule``]))
 >> IMP_RES_TAC (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)));

val DerivLeft = store_thm ("DerivLeft",
  ``!S R D D1 D1'. Deriv D1 D1' ==> Deriv (Der S R [D1; D]) (Der S R [D1'; D])``,
    NTAC 3 GEN_TAC
 >> REWRITE_TAC [Deriv_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> REPEAT STRIP_TAC (* 2 sub-goals here, first one is easy *)
 >- REWRITE_TAC [RTC_REFL]
 >> PAT_X_ASSUM ``deriv D1 D1'`` (ASSUME_TAC o (MATCH_MP derivLeft))
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE)) o (Q.SPECL [`S`, `R`, `D`]))
 >> IMP_RES_TAC (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)));

val DerivRight = store_thm ("DerivRight",
  ``!S R D D2 D2'. Deriv D2 D2' ==> Deriv (Der S R [D; D2]) (Der S R [D; D2'])``,
    NTAC 3 GEN_TAC
 >> REWRITE_TAC [Deriv_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> REPEAT STRIP_TAC (* 2 sub-goals here, first one is easy *)
 >- REWRITE_TAC [RTC_REFL]
 >> PAT_X_ASSUM ``deriv D1 D1'`` (ASSUME_TAC o (MATCH_MP derivRight))
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE)) o (Q.SPECL [`S`, `R`, `D`]))
 >> IMP_RES_TAC (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)));

val DerivBoth = store_thm ("DerivBoth",
  ``!S R D2 D2' D1 D1'. Deriv D1 D1' ==> Deriv D2 D2'
                    ==> Deriv (Der S R [D1; D2]) (Der S R [D1'; D2'])``,
    NTAC 4 GEN_TAC
 >> REWRITE_TAC [Deriv_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (`D2'`, `D2'`) \\
      Q.SPEC_TAC (`D2`, `D2`) \\
      HO_MATCH_MP_TAC RTC_INDUCT \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        REWRITE_TAC [RTC_REFL],
        (* goal 1.2 (of 2) *)
        PAT_X_ASSUM ``deriv D2 D2'`` (ASSUME_TAC o (MATCH_MP derivRight)) \\
        POP_ASSUM (ASSUME_TAC o (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE))
                              o (Q.SPECL [`S`, `R`, `D1`])) \\
        IMP_RES_TAC (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)) ],
      (* goal 2 (of 2) *)
      RES_TAC \\
      PAT_X_ASSUM ``deriv D1 D1'`` (ASSUME_TAC o (MATCH_MP derivLeft)) \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP (Q.ISPEC `deriv` RTC_SINGLE))
                            o (Q.SPECL [`S`, `R`, `D2`])) \\
      IMP_RES_TAC (Q.ISPEC `deriv` (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)) ]);

(* All Deriv rules *)
val Deriv_rules = save_thm ("Deriv_rules",
    LIST_CONJ [ DerivSeqAxiom, DerivRightSlash, DerivRightBackslash, DerivRightDot,
                DerivLeftSlash, DerivLeftBackslash, DerivLeftDot,
                DerivCutRule, DerivSeqExt,
                DerivOne, DerivLeft, DerivRight, DerivBoth,
                Deriv_refl, Deriv_trans ]);

(* Inductively define a "finished" proof *)
val (Proof_rules, Proof_ind, Proof_cases) = Hol_reln `
    (!S R.       Proof (Der S R [])) /\
    (!S R D.     Proof D ==> Proof (Der S R [D])) /\
    (!S R D1 D2. Proof D1 /\ Proof D2 ==> Proof (Der S R [D1; D2]))`;

val [ProofZero, ProofOne, ProofTwo] =
    map save_thm
        (combine (["ProofZero", "ProofOne", "ProofTwo"], CONJUNCTS Proof_rules));

(* Derivations starting from "Unf" are not finished! *)
val notProofUnf = store_thm (
   "notProofUnf",
  ``!S. ~Proof (Unf S)``,
    GEN_TAC
 >> ONCE_REWRITE_TAC [Proof_cases]
 >> rw []);

(* Now we make a connection between our derivation proofs and gentzenSequent relation *)

(* the easy direction (completeness) *)
val gentzenToDeriv = store_thm (
   "gentzenToDeriv",
  ``!E Gamma A. gentzenSequent E Gamma A
            ==> (?D. Deriv (Unf (Sequent E Gamma A)) D /\ Proof D)``,
    Induct_on `gentzenSequent`
 >> REPEAT STRIP_TAC (* 9 sub-goals here *)
 >| [ (* goal 1 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E (OneForm A) A) SeqAxiom [])`` \\
      REWRITE_TAC [DerivSeqAxiom, Proof_rules],
      (* goal 2 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma (Slash A B)) RightSlash [D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (SPEC_ALL DerivRightSlash) \\
        PAT_X_ASSUM ``Deriv (Unf (Sequent E (Comma Gamma (OneForm B)) A)) D``
          (ASSUME_TAC o (MATCH_MP DerivOne)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`Sequent E Gamma (Slash A B)`, `RightSlash`])) \\
        IMP_RES_TAC Deriv_trans,
        (* goal 2.2 (of 2) *)
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [ProofOne] ],
      (* goal 3 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma (Backslash B A)) RightBackslash [D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        ASSUME_TAC (SPEC_ALL DerivRightBackslash) \\
        PAT_X_ASSUM ``Deriv (Unf (Sequent E (Comma (OneForm B) Gamma) A)) D``
          (ASSUME_TAC o (MATCH_MP DerivOne)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`Sequent E Gamma (Backslash B A)`, `RightBackslash`])) \\
        IMP_RES_TAC Deriv_trans,
        (* goal 3.2 (of 2) *)
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [ProofOne] ],
      (* goal 4 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E (Comma Gamma Gamma') (Dot A A')) RightDot [D; D'])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        `Deriv (Der (Sequent E (Comma Gamma Gamma') (Dot A A')) RightDot
                  [ (Unf (Sequent E Gamma A)); (Unf (Sequent E Gamma' A')) ])
               (Der (Sequent E (Comma Gamma Gamma') (Dot A A')) RightDot [D; D'])`
            by PROVE_TAC [DerivBoth] \\
        ASSUME_TAC (Q.SPECL [`E`, `Gamma`, `Gamma'`, `A`, `A'`] DerivRightDot) \\
        IMP_RES_TAC Deriv_trans,
        (* goal 4.2 (of 2) *)
        MATCH_MP_TAC ProofTwo >> ASM_REWRITE_TAC [] ],
      (* goal 5 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma' A'') LeftSlash [D'; D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        `Deriv (Der (Sequent E Gamma' A'') LeftSlash
                 [ (Unf (Sequent E Gamma A'')); (Unf (Sequent E Gamma'' A')) ])
               (Der (Sequent E Gamma' A'') LeftSlash [D'; D])`
            by PROVE_TAC [DerivBoth] \\
        ASSUME_TAC (Q.SPECL [`E`, `Gamma`, `Gamma'`, `Gamma''`, `A`, `A'`, `A''`]
                            DerivLeftSlash) \\
        RES_TAC >> IMP_RES_TAC Deriv_trans,
        (* goal 5.2 (of 2) *)
        MATCH_MP_TAC ProofTwo >> ASM_REWRITE_TAC [] ],
      (* goal 6 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma' A'') LeftBackslash [D'; D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        `Deriv (Der (Sequent E Gamma' A'') LeftBackslash
                 [ (Unf (Sequent E Gamma A'')); (Unf (Sequent E Gamma'' A')) ])
               (Der (Sequent E Gamma' A'') LeftBackslash [D'; D])`
            by PROVE_TAC [DerivBoth] \\
        ASSUME_TAC (Q.SPECL [`E`, `Gamma`, `Gamma'`, `Gamma''`, `A`, `A'`, `A''`]
                            DerivLeftBackslash) \\
        RES_TAC >> IMP_RES_TAC Deriv_trans,
        (* goal 6.2 (of 2) *)
        MATCH_MP_TAC ProofTwo >> ASM_REWRITE_TAC [] ],
      (* goal 7 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma' A') LeftDot [D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 7.1 (of 2) *)
        IMP_RES_TAC DerivLeftDot \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`E`, `A'`])) \\
        PAT_X_ASSUM ``Deriv (Unf (Sequent E Gamma A')) D``
          (ASSUME_TAC o (MATCH_MP DerivOne)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`Sequent E Gamma' A'`, `LeftDot`])) \\
        IMP_RES_TAC Deriv_trans,
        (* goal 7.2 (of 2) *)
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [ProofOne] ],
      (* goal 8 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma'' A') CutRule [D'; D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
        IMP_RES_TAC DerivCutRule \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`E`, `A'`])) \\
        `Deriv (Der (Sequent E Gamma'' A') CutRule
                 [ (Unf (Sequent E Gamma' A')); (Unf (Sequent E Gamma A)) ])
               (Der (Sequent E Gamma'' A') CutRule [D'; D])`
            by PROVE_TAC [DerivBoth] \\
        IMP_RES_TAC Deriv_trans,
        (* goal 8.2 (of 2) *)
        MATCH_MP_TAC ProofTwo >> ASM_REWRITE_TAC [] ],
      (* goal 9 (of 9) *)
      EXISTS_TAC ``(Der (Sequent E Gamma' A) SeqExt [D])`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 9.1 (of 2) *)
        IMP_RES_TAC DerivOne \\
        POP_ASSUM (ASSUME_TAC o (Q.SPECL [`(Sequent E Gamma' A)`, `SeqExt`])) \\
        `Deriv (Unf (Sequent E Gamma' A))
               (Der (Sequent E Gamma' A) SeqExt [Unf (Sequent E Gamma A)])`
            by PROVE_TAC [DerivSeqExt] \\
        IMP_RES_TAC Deriv_trans,
        (* goal 9.2 (of 2) *)
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [ProofOne] ] ]);

(******************************************************************************)
(*                                                                            *)
(*               Sub-formula properties in cut-free proofs                    *)
(*                                                                            *)
(******************************************************************************)

val subFormulaPropertyOne = store_thm (
   "subFormulaPropertyOne",
  ``!q p. subProofOne q p ==>
          extensionSub (exten p) ==>
          CutFreeProof p ==>
      !x. (subFormTerm x (prems q) \/ subFormula x (concl q)) ==>
          (subFormTerm x (prems p) \/ subFormula x (concl p))``,
    REPEAT GEN_TAC
 >> NTAC 3 DISCH_TAC
 >> GEN_TAC
 >> DISCH_TAC
 >> PAT_X_ASSUM ``subProofOne q p`` MP_TAC
 >> ONCE_REWRITE_TAC [subProofOne_cases]
 >> STRIP_TAC (* 12 sub-goals here *)
 >| [ (* goal 1 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        POP_ASSUM (MP_TAC o (MATCH_MP comSub)) >> rw [] >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          DISJ1_TAC >> ASM_REWRITE_TAC [],
          (* goal 1.1.2 (of 2) *)
          (* Removed due to oneFormSubEQ[simp]:
             POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\ *)
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP slashR)) \\
          ASM_REWRITE_TAC [] ],
        (* goal 1.2 (of 2) *)
        DISJ2_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP slashL)) \\
        ASM_REWRITE_TAC [] ],
      (* goal 2 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        POP_ASSUM (MP_TAC o (MATCH_MP comSub)) >> rw [] >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          (* Removed due to oneFormSubEQ[simp]:
             POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\ *)
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP backslashL)) \\
          ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          DISJ1_TAC >> ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 2) *)
        DISJ2_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP backslashR)) \\
        ASM_REWRITE_TAC [] ],
      (* goal 3 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        DISJ1_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Delta`) o (MATCH_MP comL)) \\
        ASM_REWRITE_TAC [],
        (* goal 3.2 (of 2) *)
        DISJ2_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP dotL)) \\
        ASM_REWRITE_TAC [] ],
      (* goal 4 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        DISJ1_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Gamma`) o (MATCH_MP comR)) \\
        ASM_REWRITE_TAC [],
        (* goal 4.2 (of 2) *)
        DISJ2_TAC \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP dotR)) \\
        ASM_REWRITE_TAC [] ],
      (* goal 5 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        DISJ1_TAC \\
        IMP_RES_TAC subReplace2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
        POP_ASSUM (ASSUME_TAC o (SPEC ``(OneForm (Slash A B))``) o (MATCH_MP comR)) \\
        DISCH_TAC >> RES_TAC,
        (* goal 5.2 (of 2) *)
        DISJ1_TAC \\
        IMP_RES_TAC subReplace2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP slashR)) \\
        POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Delta`) o (MATCH_MP comL)) \\
        DISCH_TAC >> RES_TAC ],
      (* goal 6 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 6.1 (of 2) *)
        IMP_RES_TAC subReplace3 >| (* 2 sub-goals here *)
        [ (* goal 6.1.1 (of 2) *)
          ASM_REWRITE_TAC [],
          (* goal 6.1.2 (of 2) *)
          IMP_RES_TAC subReplace2 \\
          POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
          POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP slashL)) \\
          POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `Delta`) o (MATCH_MP comL)) \\
          DISCH_TAC >> RES_TAC >> ASM_REWRITE_TAC [] ],
        (* goal 6.2 (of 2) *)
        DISJ2_TAC >> ASM_REWRITE_TAC [] ],
      (* goal 7 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 7.1 (of 2) *)
        DISJ1_TAC \\
        IMP_RES_TAC subReplace2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
        POP_ASSUM (ASSUME_TAC o (SPEC ``(OneForm (Backslash B A))``) o (MATCH_MP comL)) \\
        DISCH_TAC >> RES_TAC,
        (* goal 7.2 (of 2) *)
        DISJ1_TAC \\
        IMP_RES_TAC subReplace2 \\
        POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP backslashL)) \\
        POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Delta`) o (MATCH_MP comR)) \\
        DISCH_TAC >> RES_TAC ],
      (* goal 8 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
        IMP_RES_TAC subReplace3 >| (* 2 sub-goals here *)
        [ (* goal 8.1.1 (of 2) *)
          ASM_REWRITE_TAC [],
          (* goal 8.1.2 (of 2) *)
          IMP_RES_TAC subReplace2 \\
          POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
          POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP backslashR)) \\
          POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
          POP_ASSUM (ASSUME_TAC o (Q.SPEC `Delta`) o (MATCH_MP comR)) \\
          DISCH_TAC >> RES_TAC >> ASM_REWRITE_TAC [] ],
        (* goal 8.2 (of 2) *)
        DISJ2_TAC >> ASM_REWRITE_TAC [] ],
      (* goal 9 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 9.1 (of 2) *)
        IMP_RES_TAC subReplace3 >| (* 2 sub-goals here *)
        [ (* goal 9.1.1 (of 2) *)
          ASM_REWRITE_TAC [],
          (* goal 9.1.2 (of 2) *)
          IMP_RES_TAC subReplace2 \\
          POP_ASSUM (MP_TAC o (Q.SPEC `x`)) \\
          POP_ASSUM (MP_TAC o (MATCH_MP comSub)) \\
          STRIP_TAC >| (* 2 sub-goals here *)
          [ (* goal 9.1.2.1 (of 2) *)
            POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\
            POP_ASSUM (ASSUME_TAC o (Q.SPEC `B`) o (MATCH_MP dotL)) \\
            POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
            DISCH_TAC >> RES_TAC >> ASM_REWRITE_TAC [],
            (* goal 9.1.2.2 (of 2) *)
            POP_ASSUM (ASSUME_TAC o (MATCH_MP oneFormSub)) \\
            POP_ASSUM (ASSUME_TAC o (Q.SPEC `A`) o (MATCH_MP dotR)) \\
            POP_ASSUM (ASSUME_TAC o (MATCH_MP eqFT)) \\
            DISCH_TAC >> RES_TAC \\
            ASM_REWRITE_TAC [] ] ],
        (* goal 9.2 (of 2) *)
        DISJ2_TAC >> ASM_REWRITE_TAC [] ],
      (* goal 10 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC \\ (* 2 sub-goals here, sharing the same tactical *)
      METIS_TAC [notCutFree],
      (* goal 11 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC \\ (* 2 sub-goals here, sharing the same tactical *)
      METIS_TAC [notCutFree],
      (* goal 12 (of 12) *)
      PAT_X_ASSUM ``subFormTerm x (prems q) \/ subFormula x (concl q)`` MP_TAC \\
      ASM_REWRITE_TAC [prems_def, concl_def] \\
      STRIP_TAC >| (* 2 sub-goals here, sharing the same tactical *)
      [ (* goal 12.1 (of 2) *)
        IMP_RES_TAC subReplace3 >- ASM_REWRITE_TAC [] \\
        DISJ1_TAC >> IMP_RES_TAC subReplace2 \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `x`)) \\
        `extensionSub E` by METIS_TAC [exten_def] \\
        IMP_RES_TAC extensionSub_def >> RES_TAC,
        (* goal 12.2 (of 2) *)
        DISJ2_TAC >> ASM_REWRITE_TAC [] ] ]);

(* original statements in the Coq version *)
val subFormulaPropertyOne' = store_thm (
   "subFormulaPropertyOne'",
  ``!Gamma1 Gamma2 B C x E p q.
     (p = Der (Sequent E Gamma1 B) _ _) ==>
     (q = Der (Sequent E Gamma2 C) _ _) ==>
     extensionSub E ==>
     subProofOne q p ==>
     CutFreeProof p ==>
     (subFormTerm x Gamma2 \/ subFormula x C) ==>
     (subFormTerm x Gamma1 \/ subFormula x B)``,
    REPEAT GEN_TAC
 >> NTAC 5 STRIP_TAC
 >> `Gamma1 = prems p` by PROVE_TAC [prems_def]
 >> `Gamma2 = prems q` by PROVE_TAC [prems_def]
 >> `B = concl p` by PROVE_TAC [concl_def]
 >> `C = concl q` by PROVE_TAC [concl_def]
 >> `E = exten p` by PROVE_TAC [exten_def]
 >> `extensionSub (exten p)` by PROVE_TAC []
 >> ONCE_ASM_REWRITE_TAC []
 >> METIS_TAC [subFormulaPropertyOne]);

val subFormulaProperty = store_thm (
   "subFormulaProperty",
  ``!q p. subProof q p ==>
          extensionSub (exten p) ==>
          CutFreeProof p ==>
      !x. (subFormTerm x (prems q) \/ subFormula x (concl q)) ==>
          (subFormTerm x (prems p) \/ subFormula x (concl p))``,
    HO_MATCH_MP_TAC subProof_strongind
 >> STRIP_TAC >- rw []
 >> fix [`p3`, `p2`, `p1`]
 >> set [`T1 = prems p1`, `T2 = prems p2`, `T3 = prems p3`,
         `A1 = concl p1`, `A2 = concl p2`, `A3 = concl p3`,
         `E  = exten p1`]
 >> PURE_ONCE_REWRITE_TAC []
 >> NTAC 4 STRIP_TAC >> DISCH_TAC
 >> `subFormTerm x T2 \/ subFormula x A2 ==>
     subFormTerm x T1 \/ subFormula x A1` by METIS_TAC []
 >> `CutFreeProof p2` by METIS_TAC [CutFreeSubProof]
 >> `extensionSub (exten p2)` by METIS_TAC [subProof_extension]
 >> `subFormTerm x T2 \/ subFormula x A2`
        by METIS_TAC [subFormulaPropertyOne]
 >> METIS_TAC []);

(* original statements in the Coq version *)
val subFormulaProperty' = store_thm (
   "subFormulaProperty'",
  ``!Gamma1 Gamma2 B C x E p q.
     (p = Der (Sequent E Gamma1 B) _ _) ==>
     (q = Der (Sequent E Gamma2 C) _ _) ==>
     extensionSub E ==>
     subProof q p ==>
     CutFreeProof p ==>
     (subFormTerm x Gamma2 \/ subFormula x C) ==>
     (subFormTerm x Gamma1 \/ subFormula x B)``,
    REPEAT GEN_TAC
 >> NTAC 5 STRIP_TAC
 >> `Gamma1 = prems p` by PROVE_TAC [prems_def]
 >> `Gamma2 = prems q` by PROVE_TAC [prems_def]
 >> `B = concl p` by PROVE_TAC [concl_def]
 >> `C = concl q` by PROVE_TAC [concl_def]
 >> `E = exten p` by PROVE_TAC [exten_def]
 >> `extensionSub (exten p)` by PROVE_TAC []
 >> ONCE_ASM_REWRITE_TAC []
 >> METIS_TAC [subFormulaProperty]);

val _ = export_theory ();
val _ = html_theory "CutFree";

(* last updated: April 25, 2017 *)
