(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory stringTheory;

open CCSLib CCSTheory CCSSyntax CCSConv;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory CoarsestCongrTheory;
open TraceTheory ExpansionTheory ContractionTheory;
open BisimulationUptoTheory UniqueSolutionsTheory;

open MultivariateTheory;

val _ = new_theory "Example";
val _ = temp_loose_equality ();

(* For paper generating purposes, some type abbreviations are disabled *)
val _ = disable_tyabbrev_printing "transition";
val _ = disable_tyabbrev_printing "context";
val _ = disable_tyabbrev_printing "simulation";

(******************************************************************************)
(*                                                                            *)
(*                     The coffee machine model [2]                           *)
(*                                                                            *)
(******************************************************************************)

val VM = “rec "VM" (In "coin"..
                      (In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
                       In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))”;

(* ex1 =
|- label (name "a")..label (name "b")..nil +
   label (name "b")..label (name "a")..nil
   -label (name "a")->
   label (name "b")..nil
 *)
local
    val t1 = ISPEC ``label (name "a")`` (ISPEC ``prefix (label (name "b")) nil`` PREFIX)
    and t2 = ISPECL [``prefix (label (name "a")) (prefix (label (name "b")) nil)``,
                    ``label (name "a")``,
                    ``prefix (label (name "b")) nil``,
                    ``prefix (label (name "b")) (prefix (label (name "a")) nil)``]
                   SUM1;
in
    val ex1 = save_thm ("ex1", MP t2 t1)
end;

(******************************************************************************)
(*                                                                            *)
(*       Example showing no difference between ind and coind definitions      *)
(*                                                                            *)
(******************************************************************************)

val (List_rules, List_ind, List_cases) = Hol_reln
   `(!l. (l = []) ==> List l) /\
    (!l h t. (l = h::t) /\ List t ==> List l)`;

val (coList_rules, coList_coind, coList_cases) = Hol_coreln
   `(!l. (l = []) ==> coList l) /\
    (!l h t. (l = h::t) /\ coList t ==> coList l)`;

val List_imp_coList = store_thm (
   "List_imp_coList", ``!l. List l ==> coList l``,
    HO_MATCH_MP_TAC List_ind
 >> RW_TAC bool_ss [coList_rules]);

val coList_imp_List = store_thm (
   "coList_imp_List", ``!l. coList l ==> List l``,
    Induct_on `l`
 >| [ RW_TAC bool_ss [List_rules, coList_rules],
      STRIP_TAC
   >> ONCE_REWRITE_TAC [coList_cases]
   >> ONCE_REWRITE_TAC [List_cases]
   >> REPEAT STRIP_TAC
   >| [ ASM_REWRITE_TAC [],
        SIMP_TAC list_ss []
     >> `t = l` by PROVE_TAC [CONS_11]
     >> PROVE_TAC [] ] ]);

val List_eq_coList = store_thm (
   "List_eq_coList", ``!l. coList l = List l``,
    PROVE_TAC [List_imp_coList, coList_imp_List]);

(******************************************************************************)
(*                                                                            *)
(*                        Example used in presentation                        *)
(*                                                                            *)
(******************************************************************************)

local
    val (temp_A, trans) =
        CCS_TRANS “label (name "a")..nil || label (coname "a")..nil”;
    val nodes = map (fn (l, s) => CCS_TRANS s) trans;
in
  val ex_A = save_thm ("ex_A", temp_A);
  val [ex_A1, ex_A2, ex_A3] = map (fn (n, (thm, _)) => save_thm (n, thm))
                                (combine (["ex_A1", "ex_A2", "ex_A3"], nodes))
end;

(* Examples used in Section 5 of I&C paper *)
Theorem WG_example1 :
    WG (\t. prefix a t + prefix b t + prefix c (var Y))
Proof
    HO_MATCH_MP_TAC WG4
 >> reverse CONJ_TAC >- REWRITE_TAC [WG2]
 >> HO_MATCH_MP_TAC WG4
 >> REWRITE_TAC [WG1]
QED

Theorem WG_example2 :
    WG (\t. prefix a (var X) + prefix b (var X) + prefix c t)
Proof
    HO_MATCH_MP_TAC WG4
 >> reverse CONJ_TAC >- REWRITE_TAC [WG1]
 >> REWRITE_TAC [WG2]
QED

val _ = export_theory ();
val _ = html_theory "Example";

open EmitTeX;

(* Emit theory books in TeX *)
val _ =
 if (OS.FileSys.isDir "../paper" handle e => false) then
    let in
        OS.FileSys.remove "../paper/references.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLCCS.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLStrongEQ.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLStrongLaws.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLWeakEQ.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLWeakLaws.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLObsCongr.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLObsCongrLaws.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLCongruence.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLTrace.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLCoarsestCongr.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLBisimulationUpto.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLExpansion.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLContraction.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLUniqueSolutions.tex" handle e => {};
        OS.FileSys.remove "../paper/HOLMultivariate.tex" handle e => {};

        EmitTeX.print_theories_as_tex_doc
            ["CCS",
             "StrongEQ",
             "StrongLaws",
             "WeakEQ",
             "WeakLaws",
             "ObsCongr",
             "ObsCongrLaws",
             "Congruence",
             "CoarsestCongr",
             "BisimulationUpto",
             "Trace",
             "Expansion",
             "Contraction",
             "UniqueSolutions",
             "Multivariate"]
            "../paper/references"
    end
 else
    {};

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).

 *)
