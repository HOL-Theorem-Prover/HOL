(*
 * Formalized Lambek Calculus in Higher Order Logic (HOL4)
 *
 *  (based on https://github.com/coq-contribs/lambek)
 *
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

open pred_setTheory relationTheory pairTheory listTheory prim_recTheory arithmeticTheory
open stringTheory integerTheory LambekTheory CutFreeTheory;

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

val _ = new_theory "Example";

(* check if a given sentence has category s *)
val sentence_def = Define `
    sentence words = arrow NL words (At "S")`;

(******************************************************************************)
(*                                                                            *)
(*              Example 1: check simple sentences in (arrow NL)               *)
(*                                                                            *)
(******************************************************************************)

(* in most simple cases, we have one-one mapping between words and their syntactic categories *)
val John = ``At "np"``;
val works = ``Backslash (At "np") (At "S")``;

val John_works = ``(Dot ^John ^works)``;

(* "John works" is a sentence, manual proof *)
val John_works_thm = store_thm (
   "John_works_thm", ``sentence ^John_works``,
    REWRITE_TAC [sentence_def]
 >> MATCH_MP_TAC gamma'
 >> REWRITE_TAC [one]);

(* same proof, done automatically *)
val John_works_thm2 = store_thm (
   "John_works_thm2", ``sentence ^John_works``,
    REWRITE_TAC [sentence_def]
 >> PROVE_TAC [arrow_rules]);

local
    val before_tac = REWRITE_TAC [sentence_def]
    and after_tac  = PROVE_TAC [arrow_rules]
in
    fun check_arrow tm =
	prove (tm, before_tac >> after_tac)
end;

val John_works_thm3 = save_thm (
   "John_works_thm3", check_arrow ``sentence ^John_works``);

(******************************************************************************)
(*                                                                            *)
(*           Example 2: check complex sentences in Natural Deduction          *)
(*                                                                            *)
(******************************************************************************)

val Ex1 = store_thm ("Ex1", (* sn/n . n |- sn *)
  ``natDed NL_Sequent (OneForm (Dot (Slash (At "sn") (At "n")) (At "n"))) (At "sn")``,
    MATCH_MP_TAC DotElim
 >> ONCE_REWRITE_TAC [replace_cases]
 >> RW_TAC std_ss [Term_11, Term_distinct]
 >> EXISTS_TAC ``Slash (At "sn") (At "n")``
 >> EXISTS_TAC ``At "n"``
 >> RW_TAC std_ss [NatAxiom]
 >> MATCH_MP_TAC SlashElim
 >> EXISTS_TAC ``At "n"``
 >> RW_TAC std_ss [NatAxiom]);

val Ex2 = store_thm ("Ex2", (* sn . (((sn \ n) / S) . S)) |- n *)
  ``natDed NL_Sequent
	(OneForm (Dot (At "sn") (Dot (Slash (Backslash (At "sn") (At "n")) (At "S")) (At "S"))))
	(At "n")``,
    MATCH_MP_TAC DotElim
 >> ONCE_REWRITE_TAC [replace_cases]
 >> RW_TAC std_ss [Term_11, Term_distinct]
 >> EXISTS_TAC ``At "sn"``
 >> EXISTS_TAC ``Dot (Slash (Backslash (At "sn") (At "n")) (At "S")) (At "S")``
 >> RW_TAC std_ss [NatAxiom]
 >> MATCH_MP_TAC BackslashElim
 >> EXISTS_TAC ``At "sn"``
 >> RW_TAC std_ss [NatAxiom]
 >> MATCH_MP_TAC DotElim
 >> ONCE_REWRITE_TAC [replace_cases]
 >> RW_TAC std_ss [Term_11, Term_distinct]
 >> EXISTS_TAC ``Slash (Backslash (At "sn") (At "n")) (At "S")``
 >> EXISTS_TAC ``At "S"``
 >> RW_TAC std_ss [NatAxiom]
 >> MATCH_MP_TAC SlashElim
 >> EXISTS_TAC ``At "S"``
 >> RW_TAC std_ss [NatAxiom]);

(******************************************************************************)
(*                                                                            *)
(*           Example 3: check complex sentences in Natural Deduction          *)
(*                                                                            *)
(******************************************************************************)

val Kevin = ``At "np"``;
val talks = ``Slash (Backslash (At "np") (At "S")) (At "pp")``; (* (np \ s) / pp *)

val to = ``Slash (At "pp") (At "np")``;

val himself = (* ((np \ s) / np) \ (np \ s) *)
  ``Backslash (Slash (Backslash (At "np") (At "S")) (At "np"))
	      (Backslash (At "np") (At "S"))``;

(* (Kevin, ((talks, to), himself)) *)
val Kevin_talks_to_himself = ``Dot ^Kevin (Dot (Dot ^talks ^to) ^himself)``;

(* this time automatic proof search by arrow doesn't work:

> check_arrow ``sentence ^Kevin_talks_to_himself``;
Meson search level: ................Exception- Interrupt raised
 *)

(*
val Kevin_talks_to_himself_thm = store_thm (
   "Kevin_talks_to_himself_thm", ``arrow NL ^Kevin_talks_to_himself (At "S")``,
 >> );
*)

(******************************************************************************)
(*                                                                            *)
(*     Example 4: "cosa guarda passare" in bot natDed and gentzenSequent      *)
(*                                                                            *)
(******************************************************************************)

(* a basic category type, but how to use it? *)
(* val _ = Datatype `Lexicon = <| word : string ; category : 'a Form |>`; *)

val cosa = ``(At "S") / ((At "S") / (At "np"))``;
val guarda = ``(At "S") / (At "inf")``;
val passare = ``(At "inf") / (At "np")``;
val il = ``(At "np") / (At "n")``;
val treno = ``At "n"``;

(*
S/(S/np) * (S/inf * inf/np) --> S
S/(S/np) --> S / (S/inf * inf/np)
1. S/inf * inf/np --> S/np
S/(S/np) * S/np --> S
S/(S/np) --> S/(S/np)
val cosa_guarda_passare_arrow = store_thm (
   "cosa_guarda_passare_arrow",
  ``arrow L (Dot ^cosa (Dot ^guarda ^passare)) (At "S")``,
);
 *)

(* Natural Deduction for Lambek Calculus:

                                   inf/np |- inf/np   np |- np
                                  ----------------------------- /e
                  S/inf |- S/inf    inf/np, np |- inf
                  ----------------------------------- /e
                       S/inf, (inf/np, np) |- S
                      -------------------------- L_Sequent
                       (S/inf, inf/np), np |- S
                      -------------------------- /i
 S/(S/np) |- S/(S/np)	 S/inf, inf/np |- S/np
------------------------------------------------ /e
    S/(S/np), (S/inf, inf/np) |- S
------------------------------------ Lex
("cosa", ("guarda", "passare")) |- S

 *)
val cosa_guarda_passare_natDed = store_thm (
   "cosa_guarda_passare_natDed",
  ``natDed L_Sequent (Comma (OneForm ^cosa) (Comma (OneForm ^guarda) (OneForm ^passare)))
		     (At "S")``,
    MATCH_MP_TAC SlashElim
 >> EXISTS_TAC ``(At "S") / (At "np")`` (* guess 1 *)
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      REWRITE_TAC [NatAxiom],
      (* goal 2 *)
      MATCH_MP_TAC SlashIntro \\
      MATCH_MP_TAC NatExtSimpl \\
      EXISTS_TAC ``(Comma (OneForm (At "S" / At "inf"))
			  (Comma (OneForm (At "inf" / At "np")) (OneForm (At "np"))))`` \\
      CONJ_TAC >- REWRITE_TAC [L_Sequent_rules] \\
      MATCH_MP_TAC SlashElim \\
      EXISTS_TAC ``At "inf"`` \\ (* guess 2 *)
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        REWRITE_TAC [NatAxiom],
        (* goal 2.2 *)
        MATCH_MP_TAC SlashElim \\
        EXISTS_TAC ``At "np"`` \\ (* guess 3 *)
        REWRITE_TAC [NatAxiom] ] ]);

(* Lambek's Sequent Calculus:

       S |- S   inf |- inf
      --------------------- /L
       S/inf, inf |- S       np |- np
      -------------------------------- /L
          S/inf, (inf/np, np) |- S
         -------------------------- L_Sequent
          (S/inf, inf/np), np |- S
         ----------------------------- /R
 S |- S		S/inf, inf/np |- S/np
-------------------------------------- /L
    S/(S/np), (S/inf, inf/np) |- S
------------------------------------ Lex
("cosa", ("guarda", "passare")) |- S

 *)
val cosa_guarda_passare_gentzenSequent = store_thm (
   "cosa_guarda_passare_gentzenSequent",
  ``gentzenSequent L_Sequent (Comma (OneForm ^cosa) (Comma (OneForm ^guarda) (OneForm ^passare)))
			     (At "S")``,
    MATCH_MP_TAC LeftSlashSimpl
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      MATCH_MP_TAC RightSlash \\
      MATCH_MP_TAC SeqExtSimpl \\
      EXISTS_TAC ``(Comma (OneForm (At "S" / At "inf"))
			  (Comma (OneForm (At "inf" / At "np")) (OneForm (At "np"))))`` \\
      CONJ_TAC >- REWRITE_TAC [L_Sequent_rules] \\
      MATCH_MP_TAC LeftSlashSimpl \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
        MATCH_MP_TAC LeftSlashSimpl \\
        REWRITE_TAC [SeqAxiom],
        (* goal 1.2 *)
        REWRITE_TAC [SeqAxiom] ],
      (* goal 2 *)
      REWRITE_TAC [SeqAxiom] ]);

val r0 =
  ``(Unf (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S")))``;

val r1 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Unf (Sequent L_Sequent (OneForm (At "S")) (At "S"))) ;
	(Unf (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))) ])``;

val r0_to_r1 = store_thm (
   "r0_to_r1", ``derivOne ^r0 ^r1``,
    MATCH_MP_TAC derivLeftSlash
 >> EXISTS_TAC ``At "S"``
 >> REWRITE_TAC [replaceRoot]);

val r0_to_r1' = store_thm (
   "r0_to_r1'", ``deriv ^r0 ^r1``,
    MATCH_MP_TAC derivDerivOne
 >> REWRITE_TAC [r0_to_r1]);

val r0_to_r1'' = store_thm (
   "r0_to_r1''", ``Deriv ^r0 ^r1``,
    REWRITE_TAC [Deriv_def]
 >> MATCH_MP_TAC RTC_SINGLE
 >> REWRITE_TAC [r0_to_r1']);

val r2 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Unf (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))) ])``;

val r1_to_r2 = store_thm (
   "r1_to_r2", ``deriv ^r1 ^r2``,
    MATCH_MP_TAC derivLeft
 >> MATCH_MP_TAC derivDerivOne
 >> REWRITE_TAC [derivSeqAxiom]);

val r3 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))
	     RightSlash
	  [ (Unf (Sequent L_Sequent (Comma (Comma (OneForm (At "S" / At "inf"))
						  (OneForm (At "inf" / At "np")))
					   (OneForm (At "np")))
				    (At "S"))) ]) ])``;

val r2_to_r3 = store_thm (
   "r2_to_r3", ``deriv ^r2 ^r3``,
    MATCH_MP_TAC derivRight
 >> MATCH_MP_TAC derivDerivOne
 >> REWRITE_TAC [derivRightSlash]);

val r4 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))
	     RightSlash
	  [ (Der (Sequent L_Sequent (Comma (Comma (OneForm (At "S" / At "inf"))
						  (OneForm (At "inf" / At "np")))
					   (OneForm (At "np")))
				    (At "S"))
			  SeqExt
		    [ (Unf (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
						     (Comma (OneForm (At "inf" / At "np"))
							    (OneForm (At "np"))))
					      (At "S"))) ]) ]) ])``;

val r3_to_r4 = store_thm (
   "r3_to_r4", ``deriv ^r3 ^r4``,
    MATCH_MP_TAC derivRight
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivDerivOne
 >> MATCH_MP_TAC derivSeqExt
 >> EXISTS_TAC ``(Comma (OneForm (At "S" / At "inf"))
			(Comma (OneForm (At "inf" / At "np")) (OneForm (At "np"))))``
 >> EXISTS_TAC ``(Comma (Comma (OneForm (At "S" / At "inf"))
			       (OneForm (At "inf" / At "np")))
			(OneForm (At "np")))``
 >> REWRITE_TAC [replaceRoot, L_Sequent_rules]);

val r5 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))
	     RightSlash
	  [ (Der (Sequent L_Sequent (Comma (Comma (OneForm (At "S" / At "inf"))
						  (OneForm (At "inf" / At "np")))
					   (OneForm (At "np")))
				    (At "S"))
			  SeqExt
		    [ (Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
						     (Comma (OneForm (At "inf" / At "np"))
							    (OneForm (At "np"))))
					      (At "S"))
			   LeftSlash
			[ (Unf (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
							 (OneForm (At "inf")))
						  (At "S"))) ;
			  (Unf (Sequent L_Sequent (OneForm (At "np")) (At "np"))) ]) ]) ]) ])``;

val r4_to_r5 = store_thm (
   "r4_to_r5", ``deriv ^r4 ^r5``,
    MATCH_MP_TAC derivRight
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivDerivOne
 >> MATCH_MP_TAC derivLeftSlash
 >> EXISTS_TAC ``At "inf"``
 >> MATCH_MP_TAC replaceRight
 >> REWRITE_TAC [replaceRoot]);

val r6 =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))
	     RightSlash
	  [ (Der (Sequent L_Sequent (Comma (Comma (OneForm (At "S" / At "inf"))
						  (OneForm (At "inf" / At "np")))
					   (OneForm (At "np")))
				    (At "S"))
			  SeqExt
		    [ (Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
						     (Comma (OneForm (At "inf" / At "np"))
							    (OneForm (At "np"))))
					      (At "S"))
			   LeftSlash
			[ (Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
							 (OneForm (At "inf")))
						  (At "S"))
					LeftSlash
			    [ (Unf (Sequent L_Sequent (OneForm (At "S")) (At "S"))) ;
			      (Unf (Sequent L_Sequent (OneForm (At "inf")) (At "inf"))) ]) ;
			  (Unf (Sequent L_Sequent (OneForm (At "np")) (At "np"))) ]) ]) ]) ])``;

val r5_to_r6 = store_thm (
   "r5_to_r6", ``deriv ^r5 ^r6``,
    MATCH_MP_TAC derivRight
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivLeft
 >> MATCH_MP_TAC derivDerivOne
 >> MATCH_MP_TAC derivLeftSlash
 >> EXISTS_TAC ``At "S"``
 >> REWRITE_TAC [replaceRoot]);

val r_final =
  ``(Der (Sequent L_Sequent (Comma (OneForm (At "S" / (At "S" / At "np")))
				   (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np"))))
			    (At "S"))
	 LeftSlash
      [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S"))
	     SeqAxiom []) ;
	(Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf")) (OneForm (At "inf" / At "np")))
				(At "S" / At "np"))
	     RightSlash
	  [ (Der (Sequent L_Sequent (Comma (Comma (OneForm (At "S" / At "inf"))
						  (OneForm (At "inf" / At "np")))
					   (OneForm (At "np")))
				    (At "S"))
			  SeqExt
		    [ (Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
						     (Comma (OneForm (At "inf" / At "np"))
							    (OneForm (At "np"))))
					      (At "S"))
			   LeftSlash
			[ (Der (Sequent L_Sequent (Comma (OneForm (At "S" / At "inf"))
							 (OneForm (At "inf")))
						  (At "S"))
					LeftSlash
			    [ (Der (Sequent L_Sequent (OneForm (At "S")) (At "S")) SeqAxiom []) ;
			      (Der (Sequent L_Sequent (OneForm (At "inf")) (At "inf")) SeqAxiom []) ]) ;
			  (Der (Sequent L_Sequent (OneForm (At "np")) (At "np")) SeqAxiom []) ]) ]) ]) ])``;

val r_finished = store_thm (
   "r_finished", ``Proof ^r_final``,
    PROVE_TAC [Proof_rules]);

val r_degree_zero = store_thm (
   "r_degree_zero", ``degreeProof ^r_final = 0``,
    REWRITE_TAC [degreeProof_def]
 >> rw [MAX_EQ_0]);

val r6_to_final = store_thm (
   "r6_to_final", ``deriv ^r6 ^r_final``,
    MATCH_MP_TAC derivRight
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivOne
 >> MATCH_MP_TAC derivBoth
 >> CONJ_TAC
 >| [ MATCH_MP_TAC derivBoth \\
      CONJ_TAC \\ (* 2 sub-goals, same tacticals *)
      MATCH_MP_TAC derivDerivOne >> REWRITE_TAC [derivSeqAxiom],
      MATCH_MP_TAC derivDerivOne >> REWRITE_TAC [derivSeqAxiom] ]);

fun derivToDeriv thm =
    REWRITE_RULE [SYM Deriv_def] (MATCH_MP RTC_SINGLE thm);

val r0_to_final = store_thm (
   "r0_to_final", ``Deriv ^r0 ^r_final``,
    ASSUME_TAC r0_to_r1''
 >> ASSUME_TAC (derivToDeriv r1_to_r2)
 >> ASSUME_TAC (derivToDeriv r2_to_r3)
 >> ASSUME_TAC (derivToDeriv r3_to_r4)
 >> ASSUME_TAC (derivToDeriv r4_to_r5)
 >> ASSUME_TAC (derivToDeriv r5_to_r6)
 >> ASSUME_TAC (derivToDeriv r6_to_final)
 >> REPEAT (IMP_RES_TAC Deriv_trans));

val _ = export_theory ();
val _ = html_theory "Example";

(* Emit theory books in TeX *)
(*
if (OS.FileSys.isDir "../papers" handle e => false) then
    let in
	OS.FileSys.remove "../papers/references.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLLambek.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLCutFree.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLExample.tex" handle e => {};

	EmitTeX.print_theories_as_tex_doc
	    ["Lambek", "CutFree", "Example"] "../papers/references"
    end
else
    {};
 *)

(* last updated: April 9, 2017 *)
