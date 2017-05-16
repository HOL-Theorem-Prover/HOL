(*
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open listTheory stringTheory pred_setTheory relationTheory;
open CCSLib CCSTheory CCSSyntax CCSSimps;
open StrongEQTheory StrongEQLib StrongLawsTheory WeakEQTheory;

val _ = new_theory "Example";

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
    val t1 = SPEC ``label (name "a")`` (SPEC ``prefix (label (name "b")) nil`` PREFIX)
    and t2 = SPECL [``prefix (label (name "a")) (prefix (label (name "b")) nil)``,
		    ``label (name "a")``,
		    ``prefix (label (name "b")) nil``,
		    ``prefix (label (name "b")) (prefix (label (name "a")) nil)``]
		   SUM1;
in
    val ex1 = save_thm ("ex1", MP t2 t1)
end;

local
    val t1 = SPECL [``prefix (label (name "b")) nil``, ``label (name "a")``] PREFIX;
    val t2 = MATCH_MP SUM1 t1
in
    val ex1' = save_thm ("ex1'", SPEC ``prefix (label (name "b")) (prefix (label (name "a")) nil)`` t2)
end;

(* (a.b.0 + b.a.0) --a-> (b.0) *)
val ex1'' = store_thm ("ex1''",
  ``TRANS (In "a"..In "b"..nil + In "b"..In "a"..nil)
	  (In "a")
	  (In "b"..nil)``,
    MATCH_MP_TAC SUM1
 >> rw [PREFIX]);

(* (a.b.0 + b.a.0) --b-> (a.0) *)
val ex2 = store_thm ("ex2",
  ``TRANS (sum (prefix (label (name "a")) (prefix (label (name "b")) nil))
               (prefix (label (name "b")) (prefix (label (name "a")) nil)))
	  (label (name "b"))
	  (prefix (label (name "a")) nil)``,
    MATCH_MP_TAC SUM2
 >> REWRITE_TAC [PREFIX]);

(* prove: (nu c)(a.c.0 | (`a.0 + c.0)) --tau-> (nu c)(c.0 | 0), using TRANS rules:
   PREFIX, SUM1, SUM2, PAR1, PAR2, PAR3, RESTR *)
val ex3 = store_thm ("ex3",
  ``TRANS (restr { name "c" }
		 (par (prefix (label (name "a"))
			      (prefix (label (name "c")) nil))
		      (sum (prefix (label (coname "a")) nil)
			   (prefix (label (name "c")) nil))))
	  tau
	  (restr { name "c" }
		 (par (prefix (label (name "c")) nil) nil))``,
    MATCH_MP_TAC RESTR
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC PAR3
 >> EXISTS_TAC ``name "a"``
 >> CONJ_TAC (* 2 sub-goals here *)
 >- REWRITE_TAC [PREFIX]
 >> MATCH_MP_TAC SUM1
 >> REWRITE_TAC [PREFIX, COMPL_LAB_def]);

(* prove: (nu c)(a.c.0 | (b.0+c.0)) --b-> (nu c)(a.c.0|0) *)
val ex4 = store_thm ("ex4",
  ``TRANS (restr { name "c" }
		 (par (prefix (label (name "a"))
			      (prefix (label (name "c")) nil))
		      (sum (prefix (label (name "b")) nil)
			   (prefix (label (name "c")) nil))))
	  (label (name "b"))
	  (restr { name "c" }
		 (par (prefix (label (name "a"))
			      (prefix (label (name "c")) nil))
		      nil))``,
    MATCH_MP_TAC RESTR
 >> RW_TAC std_ss [CHR_11, COMPL_LAB_def, IN_SING]
 >> MATCH_MP_TAC PAR2
 >> MATCH_MP_TAC SUM1
 >> REWRITE_TAC [PREFIX]);

(* prove: (a.0 | `a.0)|0 --tau-> (0|0)|0 *)
val ex5 = store_thm ("ex5",
  ``TRANS (par (par (prefix (label (name "a")) nil)
		    (prefix (label (coname "a")) nil))
	       nil)
	  tau
          (par (par nil nil) nil)``,
    MATCH_MP_TAC PAR1
 >> MATCH_MP_TAC PAR3
 >> EXISTS_TAC ``name "a"``
 >> RW_TAC std_ss [COMPL_LAB_def] (* two sub-goals *)
 >| [ REWRITE_TAC [PREFIX],
      REWRITE_TAC [PREFIX] ]);

(* prove: (nu c)(a.c.0 | b.0) --tau-> (nu c)(c.0 | 0) is not derivable *)
val ex6 = store_thm ("ex6",
  ``~TRANS (restr { name "c" }
		  (par (prefix (label (name "a"))
			       (prefix (label (name "c")) nil))
		       (prefix (label (name "b")) nil)))
	   tau
	   (restr { name "c" }
		  (par (prefix (label (name "c")) nil) nil))``,
    ONCE_REWRITE_TAC [TRANS_cases] (* step 1: remove outside restr *)
 >> RW_TAC std_ss [CCS_distinct]
 >> ONCE_REWRITE_TAC [TRANS_cases] (* step 2: remove par *)
 >> RW_TAC std_ss [CCS_distinct]
 >> Q.SPEC_TAC (`l`, `l`)
 >> Cases_on `l` (* 2 sub-goals divided by names and conames of `l` *)
 >| [ DISJ2_TAC \\
      ONCE_REWRITE_TAC [TRANS_cases] \\
      RW_TAC std_ss [CCS_distinct, COMPL_LAB_def, Label_distinct],
      REWRITE_TAC [COMPL_LAB_def] \\
      DISJ1_TAC \\
      ONCE_REWRITE_TAC [TRANS_cases] \\
      RW_TAC std_ss [CCS_distinct, COMPL_LAB_def, Label_distinct] ]);

(* prove: (nu a)(a.0 | `a.0) --a-> (nu a)(0 | `a.0) is not derivable *)
val ex7 = store_thm ("ex7",
  ``~TRANS (restr { name "a" }
		  (par (prefix (label (name "a")) nil)
		       (prefix (label (coname "a")) nil)))
	   (label (name "a"))
	   (restr { name "a" }
		  (par nil (prefix (label (coname "a")) nil)))``,
    ONCE_REWRITE_TAC [TRANS_cases] (* step 1: remove outside restr *)
 >> RW_TAC std_ss [CCS_distinct]
 >> RW_TAC std_ss [COMPL_LAB_def, IN_SING]);

(* A root of unknown LTS, (a.nil | `a.nil) *)
val r1 = ``par (prefix (label (name "a")) nil) (prefix (label (coname "a")) nil)``;

val r1_has_trans = store_thm ("r1_has_trans", ``?l G. TRANS ^r1 l G``,
    ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct]
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct, COMPL_LAB_def]
(* 3 possible cases here:
∃l G.
  (G = par nil (prefix (label (coname "a")) nil)) ∧ (label (name "a") = l) ∨
  (G = par (prefix (label (name "a")) nil) nil) ∧ (label (coname "a") = l) ∨
  (l = tau) ∧ (G = par nil nil)
*)
 >> EXISTS_TAC ``tau``
 >> EXISTS_TAC ``par nil nil``
 >> RW_TAC std_ss []);

(* above theorem indicates three possible transitions from r1 *)
val r1_s1 = ``par nil (prefix (label (coname "a")) nil)``; (* with label a *)
val r1_s2 = ``par (prefix (label (name "a")) nil) nil``;   (* with label co_a *)
val r1_s3 = ``par nil nil``;				   (* with label tau *)

(* two commonly used labels *)
val a    = ``label (name "a")``;
val co_a = ``label (coname "a")``;

(* proofs for three possible transitions *)
val r1_trans_1 = store_thm ("r1_trans_1", ``TRANS ^r1 ^a ^r1_s1``,
    MATCH_MP_TAC PAR1
 >> REWRITE_TAC [PREFIX]);

val r1_trans_2 = store_thm ("r1_trans_2", ``TRANS ^r1 ^co_a ^r1_s2``,
    MATCH_MP_TAC PAR2
 >> REWRITE_TAC [PREFIX]);

val r1_trans_3 = store_thm ("r1_trans_3", ``TRANS ^r1 tau ^r1_s3``,
    MATCH_MP_TAC PAR3
 >> EXISTS_TAC ``name "a"``
 >> REWRITE_TAC [PREFIX, COMPL_LAB_def]);

(* finally, there's a proof showing that no other transitions are possible *)
val r1_has_no_other_trans = store_thm (
   "r1_has_no_other_trans",
  ``~?l G. ~((G = ^r1_s1) /\ (l = ^a) \/
	     (G = ^r1_s2) /\ (l = ^co_a) \/
	     (G = ^r1_s3) /\ (l = tau)) /\ TRANS ^r1 l G``,
    ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct]
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct, COMPL_LAB_def]
 >> METIS_TAC []);

(* then we have to prove both s1 and s2 have single transition to this last status *)
local
    val t = ONCE_REWRITE_TAC [TRANS_cases] \\
	    RW_TAC std_ss [CCS_distinct] \\
	    ONCE_REWRITE_TAC [TRANS_cases] \\
	    RW_TAC std_ss [CCS_distinct] \\
	    METIS_TAC []
in
    val r1_s1_has_trans = store_thm ("r1_s1_has_trans", ``?l G. TRANS ^r1_s1 l G``, t)
    and r1_s2_has_trans = store_thm ("r1_s1_has_trans", ``?l G. TRANS ^r1_s2 l G``, t)
    and r1_s1_has_no_other_trans = store_thm (
       "r1_s1_has_no_other_trans",
      ``~?l G. ~((G = par nil nil) /\ (l = ^co_a)) /\ TRANS ^r1_s1 l G``, t)
    and r1_s2_has_no_other_trans = store_thm (
       "r1_s2_has_no_other_trans",
      ``~?l G. ~((G = par nil nil) /\ (l = ^a)) /\ TRANS ^r1_s2 l G``, t)
end;

val par_nils_no_trans = store_thm (
   "par_nils_no_trans", ``!l G. ~TRANS (par nil nil) l G``,
    ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct] (* 3 sub-goals sharing the same tacticals *)
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct, COMPL_LAB_def, Label_distinct]);

val r2 = ``restr { name "a" }
		 (par (prefix (label (name "a")) nil)
		      (prefix (label (coname "a")) nil))``;

val r2_has_trans = store_thm ("r2_has_trans", ``?l G. TRANS ^r2 l G``,
    ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct]	(* restr removed *)
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct]	(* par rewrited into 3 possible cases *)
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct, Label_distinct, COMPL_LAB_def]
(*
∃l E' l'.
  ((E' = par nil (prefix (label (coname "a")) nil)) ∧
   (label (name "a") = l) ∨
   (E' = par (prefix (label (name "a")) nil) nil) ∧
   (label (coname "a") = l) ∨ (l = tau) ∧ (E' = par nil nil)) ∧
  ((l = tau) ∨ (l = label l') ∧ l' ∉ {name "a"} ∧ COMPL l' ∉ {name "a"})
*)
 >> EXISTS_TAC ``tau``		(* for l *)
 >> EXISTS_TAC ``par nil nil``	(* for G *)
 >> RW_TAC std_ss [Label_distinct]);

(* above theorem indicates that (G = par nil nil) and (l = tau) are the only solution
   (with restrictions on G), now we prove that (G = restr (par nil nil) { name "a" })
   and (l = tau) are the actual transition. *)
val r2_trans = store_thm ("r2_trans",
  ``TRANS ^r2 tau (restr { name "a" } (par nil nil) )``,
    MATCH_MP_TAC RESTR
 >> RW_TAC std_ss [Label_distinct]
 >> MATCH_MP_TAC PAR3
 >> EXISTS_TAC ``name "a"``
 >> REWRITE_TAC [PREFIX, COMPL_LAB_def]);

(* above theorem indicates that (G = par nil nil) and (l = tau) are the only solution
   (after removing the restr), now we prove there's no others. It's incredibly hard! *)
val r2_has_no_other_trans = store_thm (
   "r2_has_no_other_trans",
  ``~?l G. ~((l = tau) /\ (G = restr { name "a" } (par nil nil))) /\ TRANS ^r2 l G``,
    CCONTR_TAC
 >> POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [DECIDE ``!t:bool. ~ ~t = t``]))
 >> PURE_ONCE_REWRITE_TAC [TRANS_cases]
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] (* 4 sub-goals here, first one is easy *)
 >- RW_TAC std_ss [] (* rest 3 sub-goals *)
 >| [ (* case 1 *)
      PAT_X_ASSUM ``TRANS E l E'`` (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
      FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] (* 3 sub-goals here, last one is easy *)
      >| [ (* case 1.1 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   `l' = name "a"` by PROVE_TAC [Action_11] \\
	   PROVE_TAC [IN_SING],
	   (* case 1.2 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   `l' = coname "a"` by PROVE_TAC [Action_11] \\
	   `COMPL l' = name "a"` by PROVE_TAC [COMPL_LAB_def] \\
	   PROVE_TAC [IN_SING],
	   (* case 1.3 *)
	   PROVE_TAC [Action_11] ],
      (* case 2 *)
      PAT_X_ASSUM ``TRANS E l E'`` (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
      FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] (* 3 sub-goals here *)
      >| [ (* case 2.1 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   PROVE_TAC [Action_distinct],
	   (* case 2.2 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   PROVE_TAC [Action_distinct],
	   (* case 2.3 *)
	   POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] ],
      (* case 3 *)
      PAT_X_ASSUM ``TRANS E l E'`` (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
      FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] (* 3 sub-goals here, last one is easy *)
      >| [ (* case 3.1 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   `l' = name "a"` by PROVE_TAC [Action_11] \\
	   PROVE_TAC [IN_SING],
	   (* case 3.2 *)
	   POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
	   FULL_SIMP_TAC std_ss [CCS_distinct, CCS_11] \\
	   `l' = coname "a"` by PROVE_TAC [Action_11] \\
	   `COMPL l' = name "a"` by PROVE_TAC [COMPL_LAB_def] \\
	   PROVE_TAC [IN_SING],
	   (* case 3.3 *)
	   PROVE_TAC [Action_distinct] ] ]);

(* (nu a)(0 | 0) *)
val r2_final = ``restr { name "a" } (par nil nil)``;

val r2_final_no_trans = store_thm (
   "r2_final_no_trans", ``!l G. ~TRANS ^r2_final l G``,
    ONCE_REWRITE_TAC [TRANS_cases]
 >> RW_TAC std_ss [CCS_distinct, CCS_11]
 >> SIMP_TAC std_ss [par_nils_no_trans]);

(* we define r3 on top of r2 *)
val r3 = ``par ^r2 (prefix (label (name "a")) nil)``;

(* for two transitions from r3, we construct the transitions in forward way, using previous results *)

(* r3_trans_1 =
   |- TRANS
     (par
        (restr {name "a"}
           (par (prefix (label (name "a")) nil)
              (prefix (label (coname "a")) nil)))
        (prefix (label (name "a")) nil))
     (label (name "a"))
     (par
        (restr {name "a"}
           (par (prefix (label (name "a")) nil)
              (prefix (label (coname "a")) nil))) nil):
 r3_trans_2' =
   |- TRANS
     (par (restr {name "a"} (par nil nil))
        (prefix (label (name "a")) nil))
     (label (name "a"))
     (par (restr {name "a"} (par nil nil)) nil)
 *)
local
    val t1 = SPECL [``nil``, ``label (name "a")``] PREFIX;
    val t2 = MATCH_MP PAR2 t1;
in
    val r3_trans_1 = SPEC r2 t2
    and r3_trans_2' = SPEC r2_final t2
end;

(* r3_trans_1' =
   |- TRANS
     (par
        (restr {name "a"}
           (par (prefix (label (name "a")) nil)
              (prefix (label (coname "a")) nil))) nil)
     tau
     (par (restr {name "a"} (par nil nil)) nil)

   r3_trans_2 =
   |- TRANS
     (par
        (restr {name "a"}
           (par (prefix (label (name "a")) nil)
              (prefix (label (coname "a")) nil)))
        (prefix (label (name "a")) nil))
     tau
     (par (restr {name "a"} (par nil nil))
        (prefix (label (name "a")) nil))
 *)
local
    val t1 = MATCH_MP PAR1 r2_trans;
in
    val r3_trans_1' = SPEC ``nil`` t1;
    val r3_trans_2 = SPEC ``prefix (label (name "a")) nil`` t1;
end;

(******************************************************************************)
(*                                                                            *)
(*           Re-worked exercises using the new CCS_TRANS function             *)
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

local
    val (temp_B, trans) = CCS_TRANS ``restr {name "a"} (label (name "a")..nil || label (coname "a")..nil)``;
    val nodes = map (fn (l, s) => CCS_TRANS s) trans;
in
  val ex_B = save_thm ("ex_B", temp_B);
  val [ex_B0] = map (fn (n, (thm, _)) => save_thm (n, thm))
		    (combine (["ex_B0"], nodes))
end;

local
    val (temp_C, trans) =
	CCS_TRANS ``(restr {name "a"} (label (name "a")..nil || label (coname "a")..nil)) ||
		    (label (name "a")..nil)``;
    val nodes = map (fn (l, s) => CCS_TRANS s) trans;
in
  val ex_C = save_thm ("ex_C", temp_C);
  val [ex_C1, ex_C2] = map (fn (n, (thm, _)) => save_thm (n, thm))
			   (combine (["ex_C1", "ex_C2"], nodes))
end;

val _ = export_theory ();
val _ = DB.html_theory "Example";

(* Emit theory books in TeX *)
if (OS.FileSys.isDir "../papers" handle e => false) then
    let in
	OS.FileSys.remove "../papers/references.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLCCS.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLStrongEQ.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLStrongLaws.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLWeakEQ.tex" handle e => {};
	OS.FileSys.remove "../papers/HOLExample.tex" handle e => {};

	EmitTeX.print_theories_as_tex_doc
	    ["CCS", "StrongEQ", "StrongLaws", "WeakEQ", "Example"] "../papers/references"
    end
else
    {};

(* last updated: May 14, 2017 *)
