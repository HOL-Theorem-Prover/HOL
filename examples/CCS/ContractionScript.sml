(* ========================================================================== *)
(* FILE          : ContractionScript.sml                                      *)
(* DESCRIPTION   : CONTRACTION and `contracts' relation                       *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory listTheory;
open CCSLib CCSTheory;
open StrongEQTheory StrongLawsTheory;
open WeakEQTheory WeakLawsTheory;
open CongruenceTheory TraceTheory ExpansionTheory;

val _ = new_theory "Contraction";

(******************************************************************************)
(*                                                                            *)
(*                  The bisimulation contraction relation                     *)
(*                                                                            *)
(******************************************************************************)

val CONTRACTION = new_definition ("CONTRACTION",
  ``CONTRACTION (Con: ('a, 'b) simulation) =
    !(E :('a, 'b) CCS) (E' :('a, 'b) CCS). Con E E' ==>
       (!l.
	 (!E1. TRANS E  (label l) E1 ==>
	       ?E2. TRANS E' (label l) E2 /\ Con E1 E2) /\
	 (!E2. TRANS E' (label l) E2 ==>
	       ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> Con E1 E' \/ ?E2. TRANS E' tau E2 /\ Con E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2)``);

(* The identity relation is a CONTRACTION. *)
val IDENTITY_CONTRACTION = store_thm (
   "IDENTITY_CONTRACTION", ``CONTRACTION (\x y. x = y)``,
    PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> BETA_TAC
 >> !! STRIP_TAC >> rfs [] (* 2 sub-goals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS,
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      IMP_RES_TAC ONE_TAU ]);

(* the proof is the same with EXPANSION_EPS *)
val CONTRACTION_EPS = store_thm (
   "CONTRACTION_EPS",
  ``!(Con: ('a, 'b) simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==> !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ Con E1 E2``,
    REPEAT STRIP_TAC
 >> Q.PAT_X_ASSUM `Con E E'` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E'` >> RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E1 E2``))
      >- ( Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

val CONTRACTION_WEAK_TRANS_label' = store_thm (
   "CONTRACTION_WEAK_TRANS_label'",
  ``!(Con: ('a, 'b) simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==>
	!l E2. WEAK_TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases2 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      IMP_RES_TAC
	(MATCH_MP WEAK_EQUIV_WEAK_TRANS_label' (ASSUME ``WEAK_EQUIV E1 E''``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC EPS_AND_WEAK_TRANS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      IMP_RES_TAC
	(MATCH_MP WEAK_EQUIV_EPS' (ASSUME ``WEAK_EQUIV E1 E''``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC WEAK_TRANS_AND_EPS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

val EXPANSION_IMP_CONTRACTION = store_thm (
   "EXPANSION_IMP_CONTRACTION",
  ``!Con. EXPANSION Con ==> CONTRACTION Con``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [CONTRACTION]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_EQUIV] \\
      Q.EXISTS_TAC `Con` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EXPANSION_IMP_WEAK_BISIM,
      (* goal 3 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      IMP_RES_TAC WEAK_TRANS_IMP_EPS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_EQUIV] \\
      Q.EXISTS_TAC `Con` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EXPANSION_IMP_WEAK_BISIM ]);

(* Bisimilarity contraction, written `P contracts (to) Q`, is the union of all
   bisimulation contractions. Here we define it as a co-inductive relation.

   "P contracts to Q" holds if "P is equivalent to Q" and, in addition,
   "Q has the possibility of being as efficient as P".  That is, Q is capable of
   simulating P by performing less internal work. It is sufficient that Q has
   one `efficient` path; Q could also have other paths, that are slower than
   any path in P.
 *)
val (contacts_rules, contracts_coind, contracts_cases) = Hol_coreln `
    (!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
       (!l.
	 (!E1. TRANS E  (label l) E1 ==>
		?E2. TRANS E' (label l) E2 /\ $contracts E1 E2) /\
	 (!E2. TRANS E' (label l) E2 ==>
		?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> $contracts E1 E' \/ ?E2. TRANS E' tau E2 /\ $contracts E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2)
      ==> $contracts E E')`;

val _ = set_fixity "contracts" (Infixl 500);

val _ = Unicode.unicode_version {u = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D47, tmnm = "contracts"}
val _ = TeX_notation {hol = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D47,
                      TeX = ("\\HOLTokenContracts{}", 1)}

val contracts_is_CONTRACTION = store_thm (
   "contracts_is_CONTRACTION", ``CONTRACTION $contracts``,
    PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> REPEAT GEN_TAC
 >> DISCH_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM contracts_cases]
 >> ASM_REWRITE_TAC []);

(* the original definition now becomes a theorem *)
val contracts_thm =  store_thm (
   "contracts_thm",
  ``!P Q. P contracts Q = ?Con. Con P Q /\ CONTRACTION Con``,
    NTAC 2 GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      EXISTS_TAC ``$contracts`` \\
      ASM_REWRITE_TAC [contracts_is_CONTRACTION],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`Q`, `Q`) \\
      Q.SPEC_TAC (`P`, `P`) \\
      HO_MATCH_MP_TAC contracts_coind \\ (* co-induction used here! *)
      METIS_TAC [CONTRACTION] ]);

val CONTRACTION_SUBSET_contracts = store_thm ((* NEW *)
   "CONTRACTION_SUBSET_contracts",
  ``!Con. CONTRACTION Con ==> Con RSUBSET $contracts``,
    PROVE_TAC [RSUBSET, contracts_thm]);

(* "Half" theorems for `contracts` relation *)
val contracts_TRANS_label = store_thm (
   "contracts_TRANS_label",
  ``!E E'. E contracts E' ==>
	   !l E1. TRANS E (label l) E1 ==> ?E2. TRANS E' (label l) E2 /\ E1 contracts E2``,
    PROVE_TAC [contracts_cases]);

val contracts_TRANS_label' = store_thm (
   "contracts_TRANS_label'",
  ``!E E'. E contracts E' ==>
	   !l E2. TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [contracts_cases]);

val contracts_TRANS_tau = store_thm (
   "contracts_TRANS_tau",
  ``!E E'. E contracts E' ==>
	   !E1. TRANS E tau E1 ==> E1 contracts E' \/ ?E2. TRANS E' tau E2 /\ E1 contracts E2``,
    PROVE_TAC [contracts_cases]);

val contracts_TRANS_tau' = store_thm (
   "contracts_TRANS_tau'",
  ``!E E'. E contracts E' ==>
	   !E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [contracts_cases]);

(* The `contracts` relation is reflexive *)
val contracts_reflexive = store_thm (
   "contracts_reflexive", ``reflexive $contracts``,
    REWRITE_TAC [reflexive_def]
 >> GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [contracts_thm]
 >> EXISTS_TAC ``\x y :('a, 'b) CCS. x = y``
 >> BETA_TAC
 >> REWRITE_TAC [IDENTITY_CONTRACTION]);

(* the version for easier use *)
val contracts_REFL = save_thm (
   "contracts_REFL", REWRITE_RULE [reflexive_def] contracts_reflexive);

(* `expands` implies `contracts` *)
val expands_IMP_contracts = store_thm (
   "expands_IMP_contracts", ``!P Q. P expands Q ==> P contracts Q``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [contracts_thm, expands_thm]
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `Exp`
 >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EXPANSION_IMP_CONTRACTION);

(* NOTE: unlike in the EXPANSION cases, CONTRACTION_IMP_WEAK_BISIM doesn't hold,
   To finish the proof, prof. Sangiorgi said "You do not prove Con itself is a weak
   bisimulation, but rather that Con "union" weak bisimilarity is a weak bisimulation."
   that is amazing ...
 *)
val contracts_IMP_WEAK_EQUIV = store_thm (
   "contracts_IMP_WEAK_EQUIV",
  ``!P Q. P contracts Q ==> WEAK_EQUIV P Q``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [WEAK_EQUIV, contracts_thm]
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `Con RUNION WEAK_EQUIV`
 >> REWRITE_TAC [RUNION]
 >> CONJ_TAC >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] )
 >> REWRITE_TAC [WEAK_BISIM, RUNION]
 >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` \\
      CONJ_TAC >- ( MATCH_MP_TAC TRANS_IMP_WEAK_TRANS >> ASM_REWRITE_TAC [] ) \\
      DISJ1_TAC >> ASM_REWRITE_TAC [],
      (* goal 2 (of 8) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 8) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [EPS_REFL] ) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU,
      (* goal 4 (of 8) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
		  (ASSUME ``(Con :('a, 'b) simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 5 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_label \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 6 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 7 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_tau \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 8 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_tau' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

(* This proof depends on `contracts_IMP_WEAK_EQUIV`, that's why it's here *)
val CONTRACTION_EPS' = store_thm (
   "CONTRACTION_EPS'",
  ``!(Con: ('a, 'b) simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==>
	!u E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> Q.PAT_X_ASSUM `Con E E'` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E2`, `E2`)
 >> Q.SPEC_TAC (`E'`, `E'`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E` >> REWRITE_TAC [EPS_REFL] \\
      MATCH_MP_TAC contracts_IMP_WEAK_EQUIV \\ (* IMPORTANT! *)
      REWRITE_TAC [contracts_thm] \\
      Q.EXISTS_TAC `Con` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC
	(MATCH_MP WEAK_EQUIV_TRANS_tau' (ASSUME ``WEAK_EQUIV E1 E2``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_TRANS ]);

(* The composition of two CONTRACTIONs is still an CONTRACTION. *)
val COMP_CONTRACTION = store_thm (
   "COMP_CONTRACTION",
  ``!Con1 Con2. CONTRACTION Con1 /\ CONTRACTION Con2 ==> CONTRACTION (Con2 O Con1)``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [CONTRACTION, O_DEF]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC 
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con1``))
		  (ASSUME ``(Con1 :('a, 'b) simulation) E y``)) \\
      IMP_RES_TAC 
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
		  (ASSUME ``(Con2 :('a, 'b) simulation) y E'``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
		  (ASSUME ``(Con2 :('a, 'b) simulation) y E'``)) \\
      IMP_RES_TAC
	(MATCH_MP (MATCH_MP CONTRACTION_WEAK_TRANS_label' (ASSUME ``CONTRACTION Con1``))
		  (ASSUME ``(Con1 :('a, 'b) simulation) E y``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS,
      (* goal 3 (of 4) *)
      IMP_RES_TAC 
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con1``))
		  (ASSUME ``(Con1 :('a, 'b) simulation) E y``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ) \\
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
		  (ASSUME ``(Con2 :('a, 'b) simulation) y E'``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC
	(MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
		  (ASSUME ``(Con2 :('a, 'b) simulation) y E'``)) \\
      IMP_RES_TAC
	(MATCH_MP (MATCH_MP CONTRACTION_EPS' (ASSUME ``CONTRACTION Con1``))
		  (ASSUME ``(Con1 :('a, 'b) simulation) E y``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS ]);

(* The `contracts` relation is transitive
   NOTE: it's not symmetric, because otherwise it becomes equivalence relation *)
val contracts_transitive = store_thm (
   "contracts_transitive", ``transitive $contracts``,
    REWRITE_TAC [transitive_def]
 >> REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [contracts_thm]
 >> STRIP_TAC
 >> Q.EXISTS_TAC `Con' O Con`
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC COMP_CONTRACTION ]);

(* the version for easier use *)
val contracts_TRANS = save_thm (
   "contracts_TRANS", REWRITE_RULE [transitive_def] contracts_transitive);

(* `contracts` is a pre-order *)
val contracts_PreOrder = store_thm (
   "contracts_PreOrder", ``PreOrder $contracts``,
    REWRITE_TAC [PreOrder, contracts_reflexive, contracts_transitive]);

val contracts_WEAK_TRANS_label' = store_thm (
   "contracts_WEAK_TRANS_label'",
  ``!E E'. E contracts E' ==>
	!l E2. WEAK_TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    REWRITE_TAC [contracts_thm]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC CONTRACTION_WEAK_TRANS_label'
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []);

val contracts_WEAK_TRANS_tau' = store_thm (
   "contracts_WEAK_TRANS_tau'",
  ``!E E'. E contracts E' ==>
	!l E2. WEAK_TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_TAU
 >> IMP_RES_TAC contracts_TRANS_tau'
 >> IMP_RES_TAC
	(MATCH_MP WEAK_EQUIV_EPS' (ASSUME ``WEAK_EQUIV E1 E''``))
 >> Q.EXISTS_TAC `E1'`
 >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EPS_TRANS);

val contracts_EPS = store_thm (
   "contracts_EPS",
  ``!E E'. E contracts E' ==> !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ E1 contracts E2``,
    REWRITE_TAC [contracts_thm]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC CONTRACTION_EPS
 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `Con` >> ASM_REWRITE_TAC []);

val contracts_EPS' = store_thm (
   "contracts_EPS'",
  ``!E E'. E contracts E' ==> !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    REWRITE_TAC [contracts_thm]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC CONTRACTION_EPS'
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []);

val contracts_WEAK_TRANS_label = store_thm (
   "contracts_WEAK_TRANS_label",
  ``!E E'. E contracts E' ==>
	!l E1. WEAK_TRANS E (label l) E1 ==> ?E2. WEAK_TRANS E' (label l) E2 /\ E1 contracts E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP contracts_EPS (ASSUME ``E contracts E'``))
 >> IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``E1' contracts E2'``))
 >> IMP_RES_TAC (MATCH_MP contracts_EPS (ASSUME ``E2 contracts E2''``))
 >> Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [WEAK_TRANS]
 >> take [`E2'`, `E2''`] >> ASM_REWRITE_TAC []);

val contracts_WEAK_TRANS_tau = store_thm (
   "contracts_WEAK_TRANS_tau",
  ``!E E'. E contracts E' ==>
	!E1. WEAK_TRANS E tau E1 ==> ?E2. EPS E' E2 /\ E1 contracts E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP contracts_EPS (ASSUME ``E contracts E'``))
 >> IMP_RES_TAC
	(MATCH_MP contracts_TRANS_tau (ASSUME ``E1' contracts E2'``)) (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (MATCH_MP contracts_EPS (ASSUME ``E2 contracts E2'``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_TRANS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC (MATCH_MP contracts_EPS (ASSUME ``E2 contracts E2''``)) \\
      Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

(******************************************************************************)
(*                                                                            *)
(*                     `contracts` is precongruence                           *)
(*                                                                            *)
(******************************************************************************)

val contracts_SUBST_PREFIX = store_thm (
   "contracts_SUBST_PREFIX",
  ``!E E'. E contracts E' ==> !u. (prefix u E) contracts (prefix u E')``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [Q.SPECL [`prefix u E`, `prefix u E'`] contracts_cases]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [PREFIX],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E` >> REWRITE_TAC [WEAK_PREFIX] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV,
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [PREFIX],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E` \\
      Q.PAT_X_ASSUM `tau = u` (REWRITE_TAC o wrap o SYM) \\
      CONJ_TAC >- ( MATCH_MP_TAC ONE_TAU >> REWRITE_TAC [PREFIX] ) \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV ]);

val contracts_PRESD_BY_GUARDED_SUM = store_thm (
   "contracts_PRESD_BY_GUARDED_SUM",
  ``!E1 E1' E2 E2' a1 a2.
	E1 contracts E1' /\ E2 contracts E2' ==>
	(sum (prefix a1 E1) (prefix a2 E2)) contracts
	(sum (prefix a1 E1') (prefix a2 E2'))``,
    REPEAT STRIP_TAC
 >> ONCE_REWRITE_TAC [contracts_cases]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1` \\
	CONJ_TAC >- ( MATCH_MP_TAC WEAK_SUM1 >> REWRITE_TAC [WEAK_PREFIX] ) \\
        IMP_RES_TAC contracts_IMP_WEAK_EQUIV,
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC WEAK_SUM2 >> REWRITE_TAC [WEAK_PREFIX] ) \\
        IMP_RES_TAC contracts_IMP_WEAK_EQUIV ],
      (* goal 3 (of 4) *)
      DISJ2_TAC >> IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.PAT_X_ASSUM `tau = a1` (fs o wrap o SYM) \\
        Q.EXISTS_TAC `E1` \\
        Rev CONJ_TAC >- IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.PAT_X_ASSUM `tau = a2` (fs o wrap o SYM) \\
        Q.EXISTS_TAC `E2` \\
        Rev CONJ_TAC >- IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ] ]);

val contracts_PRESD_BY_PAR = store_thm (
   "contracts_PRESD_BY_PAR",
  ``!E1 E1' E2 E2'.
	E1 contracts E1' /\ E2 contracts E2' ==> (par E1 E2) contracts (par E1' E2')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [contracts_thm]
 >> Q.EXISTS_TAC `\x y.
		   ?F1 F1' F2 F2'.
		    (x = par F1 F2) /\ (y = par F1' F2') /\
		    F1 contracts F1' /\ F2 contracts F2'`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E1`, `E1'`, `E2`, `E2'`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
			       (ASSUME ``TRANS E (label l) E1''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label
			      (ASSUME ``F1 contracts F1'``)) \\
	EXISTS_TAC ``par E2'' F2'`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 1.1.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
	  (* goal 1.1.2 (of 2) *)
	  take [`E1'''`, `E2''`, `F2`, `F2'`] >> ASM_REWRITE_TAC [] ],
	(* goal 1.2 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label
			      (ASSUME ``F2 contracts F2'``)) \\
	EXISTS_TAC ``par F1' E2''`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 1.2.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [],
	  (* goal 1.2.2 (of 2) *)
	  take [`F1`, `F1'`, `E1'''`, `E2''`] >> ASM_REWRITE_TAC [] ],
	(* goal 1.3 (of 3) *)
	IMP_RES_TAC Action_distinct_label ],
      (* goal 2 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par F1' F2'``]
			       (ASSUME ``TRANS E' (label l) E2''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 2.1 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label'
			      (ASSUME ``F1 contracts F1'``)) \\
	EXISTS_TAC ``par E1''' F2`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 2.1.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
	  (* goal 2.1.2 (of 2) *)
	  ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_PAR \\
          IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ],
	(* goal 2.2 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label'
			      (ASSUME ``F2 contracts F2'``)) \\
	EXISTS_TAC ``par F1 E1'''`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 2.2.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
	  (* goal 2.2.2 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_PAR \\
          IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ],
	(* goal 2.3 (of 3) *)
	IMP_RES_TAC Action_distinct_label ],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
			       (ASSUME ``TRANS E tau E1''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 3.1 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_tau
			      (ASSUME ``F1 contracts F1'``)) >| (* 2 sub-goals here *)
	[ (* goal 3.1.1 (of 2) *)
	  DISJ1_TAC >> take [`E1'''`, `F1'`, `F2`, `F2'`] >> ASM_REWRITE_TAC [],
	  (* goal 3.1.2 (of 2) *)
	  DISJ2_TAC \\
	  EXISTS_TAC ``par E2'' F2'`` \\
	  CONJ_TAC >| (* 2 sub-goals here *)
	  [ (* goal 3.1.2.1 (of 2) *)
	    ASM_REWRITE_TAC [] \\
	    MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
	    (* goal 3.1.2.2 (of 2) *)
	    take [`E1'''`, `E2''`, `F2`, `F2'`] >> ASM_REWRITE_TAC [] ] ],
	(* goal 3.2 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_tau
			      (ASSUME ``F2 contracts F2'``)) >| (* 2 sub-goals here *)
	[ (* goal 3.2.1 (of 2) *)
	  DISJ1_TAC >> take [`F1`, `F1'`, `E1'''`, `F2'`] >> ASM_REWRITE_TAC [],
	  (* goal 3.2.2 (of 2) *)
	  DISJ2_TAC \\
	  EXISTS_TAC ``par F1' E2''`` \\
	  CONJ_TAC >| (* 2 sub-goals here *)
	  [ (* goal 3.2.2.1 (of 2) *)
	    ASM_REWRITE_TAC [] \\
	    MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [],
	    (* goal 3.2.2.2 (of 2) *)
	    take [`F1`, `F1'`, `E1'''`, `E2''`] >> ASM_REWRITE_TAC [] ] ],
	(* goal 3.3 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``F1 contracts F1'``)) \\
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``F2 contracts F2'``)) \\
	DISJ2_TAC \\
	EXISTS_TAC ``par E2''' E2''''`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 3.3.1 (of 2) *)
	  ONCE_ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC PAR3 \\
	  Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [],
	  (* goal 3.3.2 (of 2) *)
	  take [`E1'''`, `E2'''`, `E2''`, `E2''''`] >> ASM_REWRITE_TAC [] ] ],
      (* goal 4 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par F1' F2'``]
			       (ASSUME ``TRANS E' tau E2''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``F1 contracts F1'``)) \\
	EXISTS_TAC ``par E1''' F2`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 4.1.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  IMP_RES_TAC EPS_PAR >> ASM_REWRITE_TAC [],
	  (* goal 4.1.2 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_PAR \\
          IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ],
	(* goal 4.2 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``F2 contracts F2'``)) \\
	EXISTS_TAC ``par F1 E1'''`` \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 4.2.1 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  IMP_RES_TAC EPS_PAR >> ASM_REWRITE_TAC [],
	  (* goal 4.2.2 (of 2) *)
	  ASM_REWRITE_TAC [] \\
	  MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_PAR \\
          IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ],
	(* goal 4.3 (of 3) *)
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label' (ASSUME ``F1 contracts F1'``)) \\
	IMP_RES_TAC (MATCH_MP contracts_TRANS_label' (ASSUME ``F2 contracts F2'``)) \\
	EXISTS_TAC ``par E1''' E1''''`` \\
	Rev CONJ_TAC
	>- ( ASM_REWRITE_TAC [] \\
	     MATCH_MP_TAC WEAK_EQUIV_PRESD_BY_PAR \\
             IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ) \\
	ONCE_ASM_REWRITE_TAC [] \\
	MATCH_MP_TAC WEAK_TRANS_IMP_EPS \\
	REWRITE_TAC [WEAK_TRANS] \\
	STRIP_ASSUME_TAC
	  (REWRITE_RULE [WEAK_TRANS] (ASSUME ``WEAK_TRANS F1 (label l) E1'''``)) \\
	STRIP_ASSUME_TAC
	  (REWRITE_RULE [WEAK_TRANS] (ASSUME ``WEAK_TRANS F2 (label (COMPL l)) E1''''``)) \\
	EXISTS_TAC ``par E1''''' E1''''''`` \\
	REWRITE_TAC [MATCH_MP EPS_PAR_PAR
			      (CONJ (ASSUME ``EPS F1 E1'''''``)
				    (ASSUME ``EPS F2 E1''''''``))] \\
	EXISTS_TAC ``par E2'''' E2'''''`` \\
	REWRITE_TAC [MATCH_MP EPS_PAR_PAR
			      (CONJ (ASSUME ``EPS E2'''' E1'''``)
				    (ASSUME ``EPS E2''''' E1''''``))] \\
	MATCH_MP_TAC PAR3 \\
	Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ] ]);

val contracts_SUBST_RESTR = store_thm (
   "contracts_SUBST_RESTR",
  ``!E E'. E contracts E' ==> !L. (restr L E) contracts (restr L E')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [contracts_thm]
 >> Q.EXISTS_TAC `\x y. ?E1 E2 L'. (x = restr L' E1) /\ (y = restr L' E2) /\ E1 contracts E2`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E`, `E'`, `L`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
			       (ASSUME ``TRANS E'' (label l) E1'``)) \\
      IMP_RES_TAC TRANS_RESTR >- IMP_RES_TAC Action_distinct_label \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``E1 contracts E2``)) \\
      Q.EXISTS_TAC `restr L' E2'` \\
      ASM_REWRITE_TAC
	[MATCH_MP WEAK_RESTR_label
		  (LIST_CONJ [ASSUME ``~((l': 'b Label) IN L')``,
			      ASSUME ``~((COMPL (l': 'b Label)) IN L')``,
			      REWRITE_RULE [ASSUME ``label (l :'b Label) = label l'``]
					   (ASSUME ``WEAK_TRANS E2 (label l) E2'``)])] \\
      CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l'` >> rfs [Action_11] ) \\
      take [`E''''`, `E2'`, `L'`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
			       (ASSUME ``TRANS E''' (label l) E2'``)) \\
      IMP_RES_TAC TRANS_RESTR >- IMP_RES_TAC Action_distinct_label \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label' (ASSUME ``E1 contracts E2``)) \\
      Q.EXISTS_TAC `restr L' E1'` \\
      ASM_REWRITE_TAC 
	[MATCH_MP WEAK_RESTR_label
		  (LIST_CONJ [ASSUME ``~((l': 'b Label) IN L')``,
			      ASSUME ``~((COMPL (l': 'b Label)) IN L')``,
			      REWRITE_RULE [ASSUME ``label (l :'b Label) = label l'``]
					   (ASSUME ``WEAK_TRANS E1 (label l) E1'``)])] \\
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
			       (ASSUME ``TRANS E'' tau E1'``)) \\
      Rev (IMP_RES_TAC TRANS_RESTR) >- IMP_RES_TAC Action_distinct \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau (ASSUME ``E1 contracts E2``))
      >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] \\
	   take [`E''''`, `E2`, `L'`] >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC \\
      ONCE_ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `restr L' E2'` \\
      CONJ_TAC >- ( MATCH_MP_TAC RESTR >> fs [] ) \\
      take [`E''''`, `E2'`, `L'`] >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
			       (ASSUME ``TRANS E''' tau E2'``)) \\
      Rev (IMP_RES_TAC TRANS_RESTR) >- IMP_RES_TAC Action_distinct \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``E1 contracts E2``)) \\
      Q.EXISTS_TAC `restr L' E1'` \\
      Rev CONJ_TAC
      >- ( ASM_REWRITE_TAC [] \\
	   MATCH_MP_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [] ) \\
      ONCE_ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_RESTR >> ASM_REWRITE_TAC [] ]);

val contracts_SUBST_RELAB = store_thm (
   "contracts_SUBST_RELAB",
  ``!E E'. E contracts E' ==> !rf. (relab E rf) contracts (relab E' rf)``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [contracts_thm]
 >> Q.EXISTS_TAC
	`\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\ E1 contracts E2`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E`, `E'`, `rf`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
			       (ASSUME ``TRANS E'' (label l) E1'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      Q.PAT_X_ASSUM `label l = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'b Action) = label l'``]
			       (ASSUME ``TRANS E1 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E2' rf'`` \\
      Rev CONJ_TAC
      >- ( take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `relabel rf' u' = label l` (REWRITE_TAC o wrap o SYM) \\
      MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
			       (ASSUME ``TRANS E''' (label l) E2'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      Q.PAT_X_ASSUM `label l = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'b Action) = label l'``]
			       (ASSUME ``TRANS E2 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label' (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      Rev CONJ_TAC
      >- ( ASM_REWRITE_TAC [] \\
	   MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_RELAB_rf >> PROVE_TAC [],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
			       (ASSUME ``TRANS E'' tau E1'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      Q.PAT_X_ASSUM `tau = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_tau \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'b Action) = tau``]
			       (ASSUME ``TRANS E1 u' E''''``)) \\ 
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau (ASSUME ``E1 contracts E2``))
      >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] \\
	   take [`E''''`, `E2`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC >> EXISTS_TAC ``relab E2' rf'`` \\
      Rev CONJ_TAC
      >- ( take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `relabel rf' u' = tau` (REWRITE_TAC o wrap o SYM) \\
      MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
			       (ASSUME ``TRANS E''' tau E2'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      Q.PAT_X_ASSUM `tau = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_tau \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'b Action) = tau``]
			       (ASSUME ``TRANS E2 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      Rev CONJ_TAC
      >- ( ASM_REWRITE_TAC [] \\
	   MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `relabel rf' u' = tau` (REWRITE_TAC o wrap o SYM) \\
      IMP_RES_TAC EPS_RELAB_rf >> ASM_REWRITE_TAC [] ]);

val contracts_SUBST_GCONTEXT = store_thm (
   "contracts_SUBST_GCONTEXT",
  ``!P Q. P contracts Q ==> !E. GCONTEXT E ==> (E P) contracts (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GCONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [contracts_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC contracts_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      MATCH_MP_TAC contracts_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 5) *)
      IMP_RES_TAC contracts_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC contracts_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC contracts_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

val contracts_precongruence = store_thm (
   "contracts_precongruence", ``precongruence1 $contracts``,
    PROVE_TAC [precongruence1_def, contracts_SUBST_GCONTEXT]);

val contracts_precongruence_applied = save_thm (
   "contracts_precongruence_applied",
    REWRITE_RULE [precongruence1_def] contracts_precongruence);

(******************************************************************************)
(*                                                                            *)
(*                  Trace, Weak transition and Contraction                    *)
(*                                                                            *)
(******************************************************************************)

val contracts_AND_TRACE1_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==>
	!E'. E contracts E' ==> ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [TRACE_REFL] )
 >> Cases_on `h` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC contracts_TRANS_tau >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	RES_TAC >> take [`xs'`, `E2`] >> ASM_REWRITE_TAC [],
	(* goal 1.2 (of 2) *)
	RES_TAC >> take [`tau :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
	MATCH_MP_TAC TRACE2 \\
	Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC contracts_TRANS_label \\
      RES_TAC \\
      take [`(label L) :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TRACE2 \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ]);

val contracts_AND_TRACE1 = store_thm (
   "contracts_AND_TRACE1",
  ``!E E'. E contracts E' ==>
	!xs E1. TRACE E xs E1 ==> ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2``,
    NTAC 2 (rpt GEN_TAC >> DISCH_TAC)
 >> irule contracts_AND_TRACE1_lemma
 >> take [`E`, `xs`] >> ASM_REWRITE_TAC []);

val contracts_AND_TRACE2_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==>
	!E'. E contracts E' ==>
	     ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\ (LENGTH xs' <= LENGTH xs)`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC
 >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [TRACE_REFL] \\
      REWRITE_TAC [LENGTH] >> RW_TAC arith_ss [] )
 >> Cases_on `h` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC contracts_TRANS_tau >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	RES_TAC >> take [`xs'`, `E2`] >> ASM_REWRITE_TAC [] \\
	REWRITE_TAC [LENGTH] >> RW_TAC arith_ss [],
	(* goal 1.2 (of 2) *)
	RES_TAC >> take [`tau :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
	CONJ_TAC >| (* 2 sub-goals here *)
	[ (* goal 1.2.1 (of 2) *)
	  MATCH_MP_TAC TRACE2 \\
	  Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
	  (* goal 1.2.2 (of 2) *)
	  REWRITE_TAC [LENGTH] >> RW_TAC arith_ss [] ] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC contracts_TRANS_label \\
      RES_TAC \\
      take [`(label L) :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
	MATCH_MP_TAC TRACE2 \\
	Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
	(* goal 2.2 (of 2) *)
	REWRITE_TAC [LENGTH] >> RW_TAC arith_ss [] ] ]);

val contracts_AND_TRACE2 = store_thm (
   "contracts_AND_TRACE2",
  ``!E E'. E contracts E' ==>
	!xs E1. TRACE E xs E1 ==>
	    ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\ (LENGTH xs' <= LENGTH xs)``,
    NTAC 2 (rpt GEN_TAC >> DISCH_TAC)
 >> irule contracts_AND_TRACE2_lemma
 >> Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC []);

val contracts_AND_TRACE_tau_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==> NO_LABEL xs ==>
	!E'. E contracts E' ==>
	     ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
		(LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC
 >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [TRACE_REFL, LENGTH] >> RW_TAC arith_ss [] )
 >> IMP_RES_TAC NO_LABEL_cases
 >> Q.PAT_X_ASSUM `NO_LABEL xs ==> X`
	(ASSUME_TAC o (fn thm => MATCH_MP thm (ASSUME ``NO_LABEL (xs :'b Action list)``)))
 >> Cases_on `h` >> FULL_SIMP_TAC std_ss [Action_distinct_label, LENGTH]
 >> IMP_RES_TAC contracts_TRANS_tau >> RES_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      take [`xs'`, `E2`] >> ASM_REWRITE_TAC [] \\
      FULL_SIMP_TAC arith_ss [],
      (* goal 2 (of 2) *)
      take [`tau :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      CONJ_TAC
      >- ( MATCH_MP_TAC TRACE2 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      Rev CONJ_TAC
      >- ( POP_ASSUM MP_TAC >> KILL_TAC \\
	   REWRITE_TAC [NO_LABEL_def, MEM, Action_distinct_label] ) \\
      REWRITE_TAC [LENGTH] \\
      FULL_SIMP_TAC arith_ss [] ]);

val contracts_AND_TRACE_tau = store_thm (
   "contracts_AND_TRACE_tau",
  ``!E E'. E contracts E' ==>
	!xs l E1. TRACE E xs E1 /\ NO_LABEL xs ==>
	    ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
		(LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'``,
    NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> irule contracts_AND_TRACE_tau_lemma
 >- ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC []);

val contracts_AND_TRACE_label_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==> !l. UNIQUE_LABEL (label l) xs ==>
	!E'. E contracts E' ==>
	     ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
		(LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC
 >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [TRACE_REFL, LENGTH] >> RW_TAC arith_ss [] )
 >> REWRITE_TAC [LENGTH]
 >> Cases_on `h` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC contracts_TRANS_tau >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	IMP_RES_TAC (EQ_IMP_LR UNIQUE_LABEL_cases1) \\
	RES_TAC \\
	take [`xs'`, `E2`] >> ASM_REWRITE_TAC [] \\
	FULL_SIMP_TAC arith_ss [],
	(* goal 1.2 (of 2) *)
	IMP_RES_TAC (EQ_IMP_LR UNIQUE_LABEL_cases1) \\
	RES_TAC \\
	take [`tau :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
	CONJ_TAC >- ( MATCH_MP_TAC TRACE2 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
	CONJ_TAC >- ( FULL_SIMP_TAC arith_ss [LENGTH] ) \\
	REWRITE_TAC [UNIQUE_LABEL_cases1] >> ASM_REWRITE_TAC [] ],
      (* goal 2 of 2 *)
      IMP_RES_TAC contracts_TRANS_label \\
      IMP_RES_TAC (EQ_IMP_LR UNIQUE_LABEL_cases2) \\
      IMP_RES_TAC (MATCH_MP contracts_AND_TRACE_tau (ASSUME ``E' contracts E2``)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      take [`label L :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC TRACE2 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      CONJ_TAC >- ( FULL_SIMP_TAC arith_ss [LENGTH] ) \\
      REWRITE_TAC [UNIQUE_LABEL_cases2] >> ASM_REWRITE_TAC [] ]);

val contracts_AND_TRACE_label = store_thm (
   "contracts_AND_TRACE_label",
  ``!E E'. E contracts E' ==>
	!xs l E1. TRACE E xs E1 /\ UNIQUE_LABEL (label l) xs ==>
	    ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
		(LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'``,
    NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> irule contracts_AND_TRACE_label_lemma
 >- ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                Bisimulation Upto `contracts` and context                   *)
(*                                                                            *)
(******************************************************************************)

val BISIM_UPTO_contracts_and_C = new_definition (
   "BISIM_UPTO_contracts_and_C",
  ``BISIM_UPTO_contracts_and_C (Wbsm: ('a, 'b) simulation) =
    !E E'.
	Wbsm E E' ==>
	(!l.
	  (!E1. TRANS E  (label l) E1 ==>
		?E2. WEAK_TRANS E' (label l) E2 /\
		    (WEAK_EQUIV O (gcontext_closure Wbsm) O $contracts) E1 E2) /\
	  (!E2. TRANS E' (label l) E2 ==>
		?E1. WEAK_TRANS E  (label l) E1 /\
		    ($contracts O (gcontext_closure Wbsm) O WEAK_EQUIV) E1 E2)) /\
	(!E1. TRANS E  tau E1 ==>
	      ?E2. EPS E' E2 /\ (WEAK_EQUIV O (gcontext_closure Wbsm) O $contracts) E1 E2) /\
	(!E2. TRANS E' tau E2 ==>
	      ?E1. EPS E  E1 /\ ($contracts O (gcontext_closure Wbsm) O WEAK_EQUIV) E1 E2)``);

(* Bibliography:
 *
 * [1] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 *)

val _ = export_theory ();
val _ = html_theory "Contraction";

(* last updated: Sep 19, 2017 *)
