(* ========================================================================== *)
(* FILE          : ExampleScript.sml                                           *)
(* DESCRIPTION   : Example theorems and definitions used in the thesis         *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

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

val _ = new_theory "Example";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*          The proof of PROPERTY_STAR (old way as in Milner's book)          *)
(*                                                                            *)
(******************************************************************************)

(*
 In StrongEQScript.ml, currently we define STRONG_EQUIV (strong bisimilarity) by
 HOL's co-inductive package (Hol_coreln):

val (STRONG_EQUIV_rules, STRONG_EQUIV_coind, STRONG_EQUIV_cases) = Hol_coreln `
    (!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
       (!u.
	 (!E1. TRANS E u E1 ==>
	       (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
	 (!E2. TRANS E' u E2 ==>
	       (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2))) ==> STRONG_EQUIV E E')`;

  then the 3rd returned value (STRONG_EQUIV_cases) is just the PROPERTY_STAR:

(* Prop. 4, page 91: strong equivalence satisfies property [*] *)
val PROPERTY_STAR = save_thm ((* NEW *)
   "PROPERTY_STAR", STRONG_EQUIV_cases);

 However, if we started with the original definition of STRONG_EQUIV, which now
 becomes a theorem:

val STRONG_EQUIV = new_definition (
   "STRONG_EQUIV",
  ``STRONG_EQUIV E E' = ?Bsm. Bsm E E' /\ STRONG_BISIM Bsm``);

 It's not easy to prove PROPERTY_STAR, below is the proof of Robin Milner through
 a temporarily definition STRONG_EQUIV', originally formalized by Monica Nesi.

 *)

(* Definition 3, page 91 in Milner's book. *)
val STRONG_EQUIV' = new_definition (
   "STRONG_EQUIV'",
  ``STRONG_EQUIV' E E' =
        (!u.
         (!E1. TRANS E u E1 ==> 
               (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
         (!E2. TRANS E' u E2 ==> 
               (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))``); 

(* Strong equivalence implies the new relation. *)
val STRONG_EQUIV_IMP_STRONG_EQUIV' = store_thm (
   "STRONG_EQUIV_IMP_STRONG_EQUIV'",
      ``!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV' E E'``,
    rpt GEN_TAC
 >> REWRITE_TAC [STRONG_EQUIV', STRONG_EQUIV]
 >> rpt STRIP_TAC (* 2 sub-goals *)
 >> IMP_RES_TAC 
      (MATCH_MP (EQ_MP STRONG_BISIM (ASSUME ``STRONG_BISIM Bsm``))
		(ASSUME ``(Bsm: ('a, 'b) simulation) E E'``))
 >| [ Q.EXISTS_TAC `E2`,
      Q.EXISTS_TAC `E1` ]
 >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `Bsm`
 >> ASM_REWRITE_TAC [] );

val STRONG_EQUIV'_IS_STRONG_BISIM = store_thm (
   "STRONG_EQUIV'_IS_STRONG_BISIM",
  ``STRONG_BISIM STRONG_EQUIV'``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >> IMP_RES_TAC 
       (EQ_MP (Q.SPECL [`E`, `E'`] STRONG_EQUIV')
              (ASSUME ``STRONG_EQUIV' E E'``))
 >| [ Q.EXISTS_TAC `E2`,
      Q.EXISTS_TAC `E1` ]
 >> IMP_RES_TAC STRONG_EQUIV_IMP_STRONG_EQUIV'
 >> ASM_REWRITE_TAC []);

(* The new relation implies strong equivalence. *)
val STRONG_EQUIV'_IMP_STRONG_EQUIV = store_thm (
   "STRONG_EQUIV'_IMP_STRONG_EQUIV",
      ``!E E'. STRONG_EQUIV' E E' ==> STRONG_EQUIV E E'``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``STRONG_EQUIV'``
 >> ASM_REWRITE_TAC [STRONG_EQUIV'_IS_STRONG_BISIM]);

(* Prop. 4, page 91: strong equivalence satisfies property [*] *)
val PROPERTY_STAR' = store_thm (
   "PROPERTY_STAR'",
      ``!E E'. STRONG_EQUIV E E' =
         (!u.
           (!E1. TRANS E u E1 ==>
                 (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
           (!E2. TRANS E' u E2 ==>
                 (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ PURE_ONCE_REWRITE_TAC 
        [ONCE_REWRITE_RULE [STRONG_EQUIV'] STRONG_EQUIV_IMP_STRONG_EQUIV'],
      PURE_ONCE_REWRITE_TAC 
        [ONCE_REWRITE_RULE [STRONG_EQUIV'] STRONG_EQUIV'_IMP_STRONG_EQUIV] ]);

(******************************************************************************)
(*                                                                            *)
(*                     The coffee machine model                               *)
(*                                                                            *)
(******************************************************************************)

val VM = ``rec "VM" (In "coin"..(In "ask-esp"..rec "VM1" (Out "esp-coffee"..var "VM") +
				 In "ask-am"..rec "VM2" (Out "am-coffee"..var "VM")))``;

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
    val (temp_A, trans) = CCS_TRANS ``label (name "a")..nil || label (coname "a")..nil``;
    val nodes = map (fn (l, s) => CCS_TRANS s) trans;
in
  val ex_A = save_thm ("ex_A", temp_A);
  val [ex_A1, ex_A2, ex_A3] = map (fn (n, (thm, _)) => save_thm (n, thm))
				(combine (["ex_A1", "ex_A2", "ex_A3"], nodes))
end;

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
	     "UniqueSolutions"]
	    "../paper/references"
    end
 else
    {};

(* last updated: Oct 15, 2017 *)
