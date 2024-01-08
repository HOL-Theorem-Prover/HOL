(* ========================================================================== *)
(* FILE          : ContractionScript.sml                                      *)
(* DESCRIPTION   : CONTRACTION and `contracts' relation                       *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) 2017 Chun Tian, University of Bologna, Italy           *)
(*                 (c) 2018 Chun Tian, Fondazione Bruno Kessler (FBK)         *)
(* DATE          : 2017-2018                                                  *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory combinTheory listTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory
     WeakEQTheory WeakEQLib WeakLawsTheory ObsCongrTheory ObsCongrLib
     ObsCongrLawsTheory ObsCongrConv TraceTheory CongruenceTheory
     CoarsestCongrTheory ExpansionTheory;

val _ = new_theory "Contraction";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*                  The bisimulation contraction relation                     *)
(*                                                                            *)
(******************************************************************************)

val CONTRACTION = new_definition ("CONTRACTION",
  ``CONTRACTION (Con :'a simulation) =
    !(E :'a CCS) (E' :'a CCS). Con E E' ==>
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               ?E2. TRANS E' (label l) E2 /\ Con E1 E2) /\
         (!E2. TRANS E' (label l) E2 ==>
               ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> Con E1 E' \/ ?E2. TRANS E' tau E2 /\ Con E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2)``);

(* The identity relation is a CONTRACTION. *)
val IDENTITY_CONTRACTION = store_thm (
   "IDENTITY_CONTRACTION", ``CONTRACTION Id``,
    PURE_ONCE_REWRITE_TAC [CONTRACTION]
 >> rpt STRIP_TAC >> rfs [] (* 2 sub-goals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS,
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [WEAK_EQUIV_REFL] \\
      IMP_RES_TAC ONE_TAU ]);

(* the proof is the same with EXPANSION_EPS *)
val CONTRACTION_EPS = store_thm (
   "CONTRACTION_EPS",
  ``!(Con :'a simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==> !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ Con E1 E2``,
    REPEAT STRIP_TAC
 >> qpat_x_assum `Con E E'` MP_TAC
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
                  (ASSUME ``(Con :'a simulation) E1 E2``))
      >- ( Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

val CONTRACTION_WEAK_TRANS_label' = store_thm (
   "CONTRACTION_WEAK_TRANS_label'",
  ``!(Con :'a simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==>
        !l E2. WEAK_TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases2 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
      IMP_RES_TAC
        (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label' (ASSUME ``WEAK_EQUIV E1 E''``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC EPS_AND_WEAK_TRANS \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
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
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_EQUIV] \\
      Q.EXISTS_TAC `Con` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EXPANSION_IMP_WEAK_BISIM,
      (* goal 3 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
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
CoInductive contracts :
    !(E :'a CCS) (E' :'a CCS).
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               ?E2. TRANS E' (label l) E2 /\ $contracts E1 E2) /\
         (!E2. TRANS E' (label l) E2 ==>
               ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> $contracts E1 E' \/ ?E2. TRANS E' tau E2 /\ $contracts E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2)
      ==> $contracts E E'
End

val _ = set_fixity "contracts" (Infix (NONASSOC, 450));

val _ = Unicode.unicode_version { u = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D47, tmnm = "contracts" };
val _ = TeX_notation { hol = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D47,
                       TeX = ("\\HOLTokenContracts{}", 1) };

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
 >> Q.EXISTS_TAC `Id`
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
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` \\
      CONJ_TAC >- ( MATCH_MP_TAC TRANS_IMP_WEAK_TRANS >> ASM_REWRITE_TAC [] ) \\
      DISJ1_TAC >> ASM_REWRITE_TAC [],
      (* goal 2 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [EPS_REFL] ) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU,
      (* goal 4 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E E'``)) \\
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
  ``!(Con :'a simulation). CONTRACTION Con ==>
     !E E'. Con E E' ==>
        !u E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> qpat_x_assum `Con E E'` MP_TAC
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
                  (ASSUME ``(Con1 :'a simulation) E y``)) \\
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
                  (ASSUME ``(Con2 :'a simulation) y E'``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
                  (ASSUME ``(Con2 :'a simulation) y E'``)) \\
      IMP_RES_TAC
        (MATCH_MP (MATCH_MP CONTRACTION_WEAK_TRANS_label' (ASSUME ``CONTRACTION Con1``))
                  (ASSUME ``(Con1 :'a simulation) E y``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS,
      (* goal 3 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con1``))
                  (ASSUME ``(Con1 :'a simulation) E y``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ) \\
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
                  (ASSUME ``(Con2 :'a simulation) y E'``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con2``))
                  (ASSUME ``(Con2 :'a simulation) y E'``)) \\
      IMP_RES_TAC
        (MATCH_MP (MATCH_MP CONTRACTION_EPS' (ASSUME ``CONTRACTION Con1``))
                  (ASSUME ``(Con1 :'a simulation) E y``)) \\
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
      qpat_x_assum `tau = u` (REWRITE_TAC o wrap o SYM) \\
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
        qpat_x_assum `tau = a1` (fs o wrap o SYM) \\
        Q.EXISTS_TAC `E1` \\
        reverse CONJ_TAC >- IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        qpat_x_assum `tau = a2` (fs o wrap o SYM) \\
        Q.EXISTS_TAC `E2` \\
        reverse CONJ_TAC >- IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
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
        reverse CONJ_TAC
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

(* |- ∀E E'. E contracts E' ⇒ ∀E''. (E || E'') contracts (E' || E'') *)
val contracts_SUBST_PAR_R = save_thm (
   "contracts_SUBST_PAR_R",
    Q.GENL [`E`, `E'`]
      (DISCH ``E contracts E'``
        (Q.GEN `E''`
           (MATCH_MP contracts_PRESD_BY_PAR
                     (CONJ (ASSUME ``E contracts E'``)
                           (Q.SPEC `E''` contracts_REFL))))));

(* |- ∀E E'. E contracts E' ⇒ ∀E''. (E'' || E) contracts (E'' || E') *)
val contracts_SUBST_PAR_L = save_thm (
   "contracts_SUBST_PAR_L",
    Q.GENL [`E`, `E'`]
      (DISCH ``E contracts E'``
        (Q.GEN `E''`
           (MATCH_MP contracts_PRESD_BY_PAR
                     (CONJ (Q.SPEC `E''` contracts_REFL)
                           (ASSUME ``E contracts E'``))))));

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
                  (LIST_CONJ [ASSUME ``~((l' :'a Label) IN L')``,
                              ASSUME ``~((COMPL (l' :'a Label)) IN L')``,
                              REWRITE_RULE [ASSUME ``label (l :'a Label) = label l'``]
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
                  (LIST_CONJ [ASSUME ``~((l' :'a Label) IN L')``,
                              ASSUME ``~((COMPL (l' :'a Label)) IN L')``,
                              REWRITE_RULE [ASSUME ``label (l :'a Label) = label l'``]
                                           (ASSUME ``WEAK_TRANS E1 (label l) E1'``)])] \\
      MATCH_MP_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                               (ASSUME ``TRANS E'' tau E1'``)) \\
      reverse (IMP_RES_TAC TRANS_RESTR) >- IMP_RES_TAC Action_distinct \\
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
      reverse (IMP_RES_TAC TRANS_RESTR) >- IMP_RES_TAC Action_distinct \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``E1 contracts E2``)) \\
      Q.EXISTS_TAC `restr L' E1'` \\
      reverse CONJ_TAC
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
      qpat_x_assum `label l = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = label l'``]
                               (ASSUME ``TRANS E1 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E2' rf'`` \\
      reverse CONJ_TAC
      >- ( take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      qpat_x_assum `relabel rf' u' = label l` (REWRITE_TAC o wrap o SYM) \\
      MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                               (ASSUME ``TRANS E''' (label l) E2'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      qpat_x_assum `label l = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = label l'``]
                               (ASSUME ``TRANS E2 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_label' (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      reverse CONJ_TAC
      >- ( ASM_REWRITE_TAC [] \\
           MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_RELAB_rf >> PROVE_TAC [],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                               (ASSUME ``TRANS E'' tau E1'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      qpat_x_assum `tau = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_tau \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = tau``]
                               (ASSUME ``TRANS E1 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau (ASSUME ``E1 contracts E2``))
      >- ( DISJ1_TAC >> ASM_REWRITE_TAC [] \\
           take [`E''''`, `E2`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC >> EXISTS_TAC ``relab E2' rf'`` \\
      reverse CONJ_TAC
      >- ( take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      qpat_x_assum `relabel rf' u' = tau` (REWRITE_TAC o wrap o SYM) \\
      MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                               (ASSUME ``TRANS E''' tau E2'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      qpat_x_assum `tau = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_tau \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = tau``]
                               (ASSUME ``TRANS E2 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP contracts_TRANS_tau' (ASSUME ``E1 contracts E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      reverse CONJ_TAC
      >- ( ASM_REWRITE_TAC [] \\
           MATCH_MP_TAC WEAK_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      qpat_x_assum `relabel rf' u' = tau` (REWRITE_TAC o wrap o SYM) \\
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
   "contracts_precongruence", ``precongruence' $contracts``,
    PROVE_TAC [precongruence', contracts_PreOrder, contracts_SUBST_GCONTEXT]);

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
      take [`label x :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TRACE2 \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ]);

val contracts_AND_TRACE1 = store_thm (
   "contracts_AND_TRACE1",
  ``!E E'. E contracts E' ==>
        !xs E1. TRACE E xs E1 ==> ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2``,
    NTAC 2 (rpt GEN_TAC >> DISCH_TAC)
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] contracts_AND_TRACE1_lemma)
 >> RW_TAC std_ss []);

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
      take [`label x :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
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
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] contracts_AND_TRACE2_lemma)
 >> RW_TAC std_ss []);

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
 >> qpat_x_assum `NO_LABEL xs ==> X`
        (ASSUME_TAC o (fn thm => MATCH_MP thm (ASSUME ``NO_LABEL (xs :'a Action list)``)))
 >> Cases_on `h` >> FULL_SIMP_TAC std_ss [Action_distinct_label, LENGTH]
 >> IMP_RES_TAC contracts_TRANS_tau >> RES_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      take [`xs'`, `E2`] >> ASM_REWRITE_TAC [] \\
      FULL_SIMP_TAC arith_ss [],
      (* goal 2 (of 2) *)
      take [`tau :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      CONJ_TAC
      >- ( MATCH_MP_TAC TRACE2 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      reverse CONJ_TAC
      >- ( POP_ASSUM MP_TAC >> KILL_TAC \\
           REWRITE_TAC [NO_LABEL_def, MEM, Action_distinct_label] ) \\
      REWRITE_TAC [LENGTH] \\
      FULL_SIMP_TAC arith_ss [] ]);

val contracts_AND_TRACE_tau = store_thm (
   "contracts_AND_TRACE_tau",
  ``!E E'. E contracts E' ==>
        !xs E1. TRACE E xs E1 /\ NO_LABEL xs ==>
            ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
                (LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'``,
    NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] contracts_AND_TRACE_tau_lemma)
 >> RW_TAC std_ss []);

(* the version shown in the paper using P and Q *)
val contracts_AND_TRACE_tau' = store_thm (
   "contracts_AND_TRACE_tau'",
  ``!P Q. P contracts Q ==>
        !xs P'. TRACE P xs P' /\ NO_LABEL xs ==>
            ?xs' Q'. TRACE Q xs' Q' /\ P' contracts Q' /\
                (LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'``,
    METIS_TAC [contracts_AND_TRACE_tau]);

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
      take [`label x :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
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
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] contracts_AND_TRACE_label_lemma)
 >> RW_TAC std_ss []);

(* the version shown in the paper using P and Q *)
val contracts_AND_TRACE_label' = store_thm (
   "contracts_AND_TRACE_label'",
  ``!P Q. P contracts Q ==>
        !xs l P'. TRACE P xs P' /\ UNIQUE_LABEL (label l) xs ==>
            ?xs' Q'. TRACE Q xs' Q' /\ P contracts Q /\
                (LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'``,
    METIS_TAC [contracts_AND_TRACE_label]);

(******************************************************************************)
(*                                                                            *)
(*                Bisimulation Upto `contracts` and context                   *)
(*                                                                            *)
(******************************************************************************)

(*
val BISIM_UPTO_contracts_and_C = new_definition (
   "BISIM_UPTO_contracts_and_C",
  ``BISIM_UPTO_contracts_and_C (Wbsm :'a simulation) =
    !E E'.
        Wbsm E E' ==>
        (!l.
          (!E1. TRANS E  (label l) E1 ==>
                ?E2. WEAK_TRANS E' (label l) E2 /\
                    (WEAK_EQUIV O (GCC Wbsm) O $contracts) E1 E2) /\
          (!E2. TRANS E' (label l) E2 ==>
                ?E1. WEAK_TRANS E  (label l) E1 /\
                    ($contracts O (GCC Wbsm) O WEAK_EQUIV) E1 E2)) /\
        (!E1. TRANS E  tau E1 ==>
              ?E2. EPS E' E2 /\ (WEAK_EQUIV O (GCC Wbsm) O $contracts) E1 E2) /\
        (!E2. TRANS E' tau E2 ==>
              ?E1. EPS E  E1 /\ ($contracts O (GCC Wbsm) O WEAK_EQUIV) E1 E2)``);
 *)

(******************************************************************************)
(*                                                                            *)
(*                Observational contraction (OBS_contracts)                   *)
(*                                                                            *)
(******************************************************************************)

val OBS_contracts = new_definition ("OBS_contracts",
  ``OBS_contracts (E :'a CCS) (E' :'a CCS) =
       (!(u :'a Action).
         (!E1. TRANS E  u E1 ==>
               ?E2. TRANS E' u E2 /\ E1 contracts E2) /\
         (!E2. TRANS E' u E2 ==>
               ?E1. WEAK_TRANS E u E1 /\ WEAK_EQUIV E1 E2))``);

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Infix (NONASSOC, 450),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK (UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D9C),
                                  BreakSpace (1,0)],
                   term_name = "OBS_contracts" };

val _ = TeX_notation { hol = (UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D9C),
                       TeX = ("\\HOLTokenObsContracts", 1) };

(* This one is difficult because `standard technique` doesn't work *)
val OBS_contracts_BY_CONTRACTION = store_thm (
   "OBS_contracts_BY_CONTRACTION",
  ``!Con. CONTRACTION Con ==>
      !E E'.
        (!u.
         (!E1. TRANS E u E1 ==>
               (?E2. TRANS E' u E2 /\ Con E1 E2)) /\
         (!E2. TRANS E' u E2 ==>
               (?E1. WEAK_TRANS E  u E1 /\ Con E1 E2))) ==> OBS_contracts E E'``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_contracts]
 >> REWRITE_TAC [contracts_thm]
 >> GEN_TAC
 >> CONJ_TAC (* 2 sub-goals here *)
 >- ( rpt STRIP_TAC >> RES_TAC \\
      Q.EXISTS_TAC `E2` >> art [] \\
      Q.EXISTS_TAC `Con` >> art [] )
 >> rpt STRIP_TAC >> RES_TAC
 >> Q.EXISTS_TAC `E1` >> art []
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `Con RUNION WEAK_EQUIV` (* here !!! *)
 >> REWRITE_TAC [RUNION]
 >> CONJ_TAC >- ( DISJ1_TAC >> art [] )
 >> REWRITE_TAC [WEAK_BISIM, RUNION] >> rpt STRIP_TAC (* 8 sub-goals here *)
 >| [ (* goal 1 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E'' E'''``)) \\
      Q.EXISTS_TAC `E2'` \\
      CONJ_TAC >- ( MATCH_MP_TAC TRANS_IMP_WEAK_TRANS >> art [] ) \\
      DISJ1_TAC >> art [],
      (* goal 2 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E'' E'''``)) \\
      Q.EXISTS_TAC `E1'` >> art [],
      (* goal 3 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E'' E'''``)) (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'''` >> art [EPS_REFL] ) \\
      Q.EXISTS_TAC `E2'` >> art [] \\
      IMP_RES_TAC ONE_TAU,
      (* goal 4 (of 8) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [CONTRACTION] (ASSUME ``CONTRACTION Con``))
                  (ASSUME ``(Con :'a simulation) E'' E'''``)) \\
      Q.EXISTS_TAC `E1'` >> art [],
      (* goal 5 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_label \\
      Q.EXISTS_TAC `E2'` >> art [],
      (* goal 6 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_label' \\
      Q.EXISTS_TAC `E1'` >> art [],
      (* goal 7 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_tau \\
      Q.EXISTS_TAC `E2'` >> art [],
      (* goal 8 (of 8) *)
      IMP_RES_TAC WEAK_EQUIV_TRANS_tau' \\
      Q.EXISTS_TAC `E1'` >> art [] ]);

val OBS_contracts_TRANS_LEFT = store_thm (
   "OBS_contracts_TRANS_LEFT",
  ``!E E'. OBS_contracts (E :'a CCS) (E' :'a CCS) ==>
           !u E1. TRANS E  u E1 ==> ?E2. TRANS E' u E2 /\ E1 contracts E2``,
    PROVE_TAC [OBS_contracts]);

val OBS_contracts_TRANS_RIGHT = store_thm (
   "OBS_contracts_TRANS_RIGHT",
  ``!E E'. OBS_contracts (E :'a CCS) (E' :'a CCS) ==>
           !u E2. TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [OBS_contracts]);

val OBS_contracts_IMP_contracts = store_thm (
   "OBS_contracts_IMP_contracts", ``!E E'. OBS_contracts E E' ==> E contracts E'``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [contracts_cases]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
      Q.EXISTS_TAC `E2` >> art [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 3 (of 4) *)
      IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
      DISJ2_TAC >> Q.EXISTS_TAC `E2` >> art [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      Q.EXISTS_TAC `E1` >> art [] \\
      MATCH_MP_TAC WEAK_TRANS_IMP_EPS >> art [] ]);

val OBS_contracts_IMP_WEAK_EQUIV = store_thm (
   "OBS_contracts_IMP_WEAK_EQUIV", ``!E E'. OBS_contracts E E' ==> WEAK_EQUIV E E'``,
    rpt STRIP_TAC
 >> IMP_RES_TAC OBS_contracts_IMP_contracts
 >> IMP_RES_TAC contracts_IMP_WEAK_EQUIV);

(* Know relations:
   1.       `expands` << `contracts`      << WEAK_EQUIV
   2. `OBS_contracts` << `contracts`
   3. `OBS_contracts`        << OBS_CONGR << WEAK_EQUIV *)
val OBS_contracts_IMP_OBS_CONGR = store_thm (
   "OBS_contracts_IMP_OBS_CONGR", ``!E E'. OBS_contracts E E' ==> OBS_CONGR E E'``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
      Q.EXISTS_TAC `E2` \\
      CONJ_TAC >- IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV,
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      Q.EXISTS_TAC `E1` >> art [] ]);

(* another way to prove this *)
val OBS_contracts_IMP_WEAK_EQUIV' = store_thm (
   "OBS_contracts_IMP_WEAK_EQUIV'", ``!E E'. OBS_contracts E E' ==> WEAK_EQUIV E E'``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC OBS_CONGR_IMP_WEAK_EQUIV
 >> IMP_RES_TAC OBS_contracts_IMP_OBS_CONGR);

val OBS_contracts_EPS' = store_thm (
   "OBS_contracts_EPS'",
  ``!E E'. OBS_contracts (E :'a CCS) (E' :'a CCS) ==>
           !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    rpt STRIP_TAC
 >> PAT_X_ASSUM ``OBS_contracts E E'`` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E2`, `E2`)
 >> Q.SPEC_TAC (`E'`, `E'`)
 >> HO_MATCH_MP_TAC EPS_strongind_right (* must use right induct here! *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E` >> REWRITE_TAC [EPS_REFL] \\
      IMP_RES_TAC OBS_contracts_IMP_WEAK_EQUIV,
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC WEAK_EQUIV_TRANS_tau' \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      IMP_RES_TAC EPS_TRANS ]);

val OBS_contracts_WEAK_TRANS' = store_thm (
   "OBS_contracts_WEAK_TRANS'",
  ``!E E'. OBS_contracts (E :'a CCS) (E' :'a CCS) ==>
           !u E2. WEAK_TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ WEAK_EQUIV E1 E2``,
    rpt STRIP_TAC
 >> Cases_on `u` (* 2 sub-goals here *)
 >| [ (* case 1 (of 2): u = tau *)
      IMP_RES_TAC WEAK_TRANS_TAU_IMP_TRANS_TAU \\
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      IMP_RES_TAC WEAK_EQUIV_EPS' \\
      Q.EXISTS_TAC `E1''` >> art [] \\
      MATCH_MP_TAC WEAK_TRANS_AND_EPS \\
      Q.EXISTS_TAC `E1'` >> art [],
      (* case 2 (of 2): ~(u = tau) *)
      IMP_RES_TAC WEAK_TRANS \\
      IMP_RES_TAC OBS_contracts_EPS' \\
      IMP_RES_TAC WEAK_EQUIV_TRANS_label' \\
      IMP_RES_TAC WEAK_EQUIV_EPS' \\
      Q.EXISTS_TAC `E1'''` >> art [] \\
      IMP_RES_TAC EPS_WEAK_EPS ]);

(******************************************************************************)
(*                                                                            *)
(*                       OBS_contracts is PreOrder                            *)
(*                                                                            *)
(******************************************************************************)

val OBS_contracts_TRANS = store_thm (
   "OBS_contracts_TRANS",
  ``!E E' E''. OBS_contracts E E' /\ OBS_contracts E' E'' ==> OBS_contracts E E''``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (REWRITE_RULE [OBS_contracts] (ASSUME ``OBS_contracts E E'``)) \\
      IMP_RES_TAC (REWRITE_RULE [OBS_contracts] (ASSUME ``OBS_contracts E' E''``)) \\
      Q.EXISTS_TAC `E2'` >> art [] \\
      IMP_RES_TAC contracts_TRANS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC (REWRITE_RULE [OBS_contracts] (ASSUME ``OBS_contracts E' E''``)) \\
      IMP_RES_TAC OBS_contracts_WEAK_TRANS' \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS ]);

val OBS_contracts_REFL = store_thm (
   "OBS_contracts_REFL", ``!E. OBS_contracts E E``,
    GEN_TAC
 >> REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC
 >- ( Q.EXISTS_TAC `E1` >> art [contracts_REFL] )
 >> Q.EXISTS_TAC `E2` >> REWRITE_TAC [WEAK_EQUIV_REFL]
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS);

val OBS_contracts_PreOrder = store_thm (
   "OBS_contracts_PreOrder", ``PreOrder OBS_contracts``,
    REWRITE_TAC [PreOrder, reflexive_def, transitive_def]
 >> CONJ_TAC >- REWRITE_TAC [OBS_contracts_REFL]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC OBS_contracts_TRANS
 >> Q.EXISTS_TAC `y` >> art []);

(******************************************************************************)
(*                                                                            *)
(*                      OBS_contracts is precongruence                        *)
(*                                                                            *)
(******************************************************************************)

(* Proposition 6 (Milner's book, page 154), the version for `contracts` *)
val contracts_PROP6 = store_thm (
   "contracts_PROP6",
  ``!E E'. E contracts E' ==> !u. OBS_contracts (prefix u E) (prefix u E')``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E'` >> art [] \\
      REWRITE_TAC [PREFIX],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E` >> art [] \\
      CONJ_TAC >- REWRITE_TAC [WEAK_PREFIX] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV ]);

val OBS_contracts_SUBST_PREFIX = store_thm (
   "OBS_contracts_SUBST_PREFIX",
  ``!E E'. OBS_contracts E E' ==> !u. OBS_contracts (prefix u E) (prefix u E')``,
    rpt STRIP_TAC
 >> IMP_RES_TAC OBS_contracts_IMP_contracts
 >> MATCH_MP_TAC contracts_PROP6 >> art []);

val OBS_contracts_PRESD_BY_SUM = store_thm (
   "OBS_contracts_PRESD_BY_SUM",
  ``!E1 E1' E2 E2'. OBS_contracts E1 E1' /\ OBS_contracts E2 E2' ==>
                    OBS_contracts (sum E1 E2) (sum E1' E2')``,
    rpt GEN_TAC
 >> REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E2''` >> art [] \\
        MATCH_MP_TAC SUM1 >> art [],
        (* goal 1.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E2''` >> art [] \\
        MATCH_MP_TAC SUM2 >> art [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E1''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM1 >> art [],
        (* goal 2.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E1''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM2 >> art [] ] ]);

(* |- !E E'. OBS_contracts E E' ==> !E''. OBS_contracts (sum E'' E) (sum E'' E') *)
val OBS_contracts_SUBST_SUM_L = save_thm (
   "OBS_contracts_SUBST_SUM_L",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_contracts E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_contracts_PRESD_BY_SUM
                   (CONJ (Q.SPEC `E''` OBS_contracts_REFL)
                         (ASSUME ``OBS_contracts E E'``))))));

(* |- !E E'. OBS_contracts E E' ==> !E''. OBS_contracts (sum E E'') (sum E' E'') *)
val OBS_contracts_SUBST_SUM_R = save_thm (
   "OBS_contracts_SUBST_SUM_R",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_contracts E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_contracts_PRESD_BY_SUM
                   (CONJ (ASSUME ``OBS_contracts E E'``)
                         (Q.SPEC `E''` OBS_contracts_REFL))))));

(* this belongs to ContractionLib.sml *)
fun C_TRANS thm1 thm2 =
    if (rhs_tm thm1 ~~ lhs_tm thm2) then
        MATCH_MP contracts_TRANS (CONJ thm1 thm2)
    else
        failwith "transitivity of contraction not applicable";

(* Observation contracts is preserved by parallel composition. *)
val OBS_contracts_PRESD_BY_PAR = store_thm (
   "OBS_contracts_PRESD_BY_PAR",
  ``!E1 E1' E2 E2'. OBS_contracts E1 E1' /\ OBS_contracts E2 E2' ==>
                    OBS_contracts (par E1 E2) (par E1' E2')``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
        ASSUME_TAC (Q.SPEC `E2'`
                        (MATCH_MP PAR1 (ASSUME ``TRANS E1' u E2''``))) \\
        EXISTS_TAC ``par E2'' E2'`` \\
        ASM_REWRITE_TAC
          [C_TRANS (Q.SPEC `E2`
                      (MATCH_MP contracts_SUBST_PAR_R
                                (ASSUME ``E1''' contracts E2''``)))
                   (Q.SPEC `E2''`
                      (MATCH_MP contracts_SUBST_PAR_L
                                (MATCH_MP OBS_contracts_IMP_contracts
                                          (ASSUME ``OBS_contracts E2 E2'``))))],
        (* goal 1.2 (of 3) *)
        IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
        ASSUME_TAC (Q.SPEC `E1'`
                        (MATCH_MP PAR2 (ASSUME ``TRANS E2' u E2''``))) \\
        EXISTS_TAC ``par E1' E2''`` \\
        ASM_REWRITE_TAC
          [C_TRANS (Q.SPEC `E1'''`
                      (MATCH_MP contracts_SUBST_PAR_R
                                (MATCH_MP OBS_contracts_IMP_contracts
                                          (ASSUME ``OBS_contracts E1 E1'``))))
                   (Q.SPEC `E1'`
                      (MATCH_MP contracts_SUBST_PAR_L
                                (ASSUME ``E1''' contracts E2''``)))],
        (* goal 1.3 (of 3) *)
        IMP_RES_TAC (MATCH_MP OBS_contracts_TRANS_LEFT (ASSUME ``OBS_contracts E1 E1'``)) \\
        IMP_RES_TAC (MATCH_MP OBS_contracts_TRANS_LEFT (ASSUME ``OBS_contracts E2 E2'``)) \\
        EXISTS_TAC ``par E2''' E2''''`` \\
        ASM_REWRITE_TAC
          [C_TRANS (Q.SPEC `E2''`
                       (MATCH_MP contracts_SUBST_PAR_R
                                 (ASSUME ``E1''' contracts E2'''``)))
                    (Q.SPEC `E2'''`
                       (MATCH_MP contracts_SUBST_PAR_L
                                 (ASSUME ``E2'' contracts E2''''``)))] \\
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 2.1 (of 3) *)
        IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
        ASSUME_TAC (CONJUNCT1
                     (Q.SPEC `E2`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E1 u E1'''``)))) \\
        EXISTS_TAC ``par E1''' E2`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E2`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))
                    (Q.SPEC `E1''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (MATCH_MP OBS_contracts_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_contracts E2 E2'``))))],
        (* goal 2.2 (of 3) *)
        IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
        ASSUME_TAC (CONJUNCT2
                     (Q.SPEC `E1`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E2 u E1'''``)))) \\
        EXISTS_TAC ``par E1 E1'''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E1'''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (MATCH_MP OBS_contracts_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_contracts E1 E1'``))))
                    (Q.SPEC `E1'`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))],
        (* goal 2.3 (of 3) *)
        IMP_RES_TAC (MATCH_MP OBS_contracts_TRANS_RIGHT (ASSUME ``OBS_contracts E1 E1'``)) \\
        IMP_RES_TAC (MATCH_MP OBS_contracts_TRANS_RIGHT (ASSUME ``OBS_contracts E2 E2'``)) \\
        EXISTS_TAC ``par E1''' E1''''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E1''''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))
                    (Q.SPEC `E1''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E1'''' E2'''``)))] \\
        PURE_ONCE_REWRITE_TAC [WEAK_TRANS] \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E1 (label l) E1'''``)) \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E2 (label (COMPL l)) E1''''``)) \\
        EXISTS_TAC ``par E1''''' E1''''''`` \\
        EXISTS_TAC ``par E2'''' E2'''''`` \\
        REWRITE_TAC
          [MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E1 E1'''''``)
                          (ASSUME ``EPS E2 E1''''''``)),
           MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E2'''' E1'''``)
                          (ASSUME ``EPS E2''''' E1''''``))] \\
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ] ]);

(* |- !E E'. OBS_contracts E E' ==> !E''. OBS_contracts (par E'' E) (par E'' E') *)
val OBS_contracts_SUBST_PAR_L = save_thm (
   "OBS_contracts_SUBST_PAR_L",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_contracts E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_contracts_PRESD_BY_PAR
                   (CONJ (Q.SPEC `E''` OBS_contracts_REFL)
                         (ASSUME ``OBS_contracts E E'``))))));

(* |- !E E'. OBS_contracts E E' ==> !E''. OBS_contracts (par E E'') (par E' E'') *)
val OBS_contracts_SUBST_PAR_R = save_thm (
   "OBS_contracts_SUBST_PAR_R",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_contracts E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_contracts_PRESD_BY_PAR
                   (CONJ (ASSUME ``OBS_contracts E E'``)
                         (Q.SPEC `E''` OBS_contracts_REFL))))));

val OBS_contracts_SUBST_RESTR = store_thm (
   "OBS_contracts_SUBST_RESTR",
  ``!E E'. OBS_contracts E E' ==> !L. OBS_contracts (restr L E) (restr L E')``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> art [] ) \\
        IMP_RES_TAC contracts_SUBST_RESTR >> art [],
        (* goal 1.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` >> art [] \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> rfs [] ) \\
        IMP_RES_TAC contracts_SUBST_RESTR >> art [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_tau
                    (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                                  (ASSUME ``WEAK_TRANS E u E1``))) \\
        Q.EXISTS_TAC `restr L E1` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> art [],
        (* goal 2.2 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_label
                    (LIST_CONJ [ASSUME ``~((l :'a Label) IN L)``,
                                ASSUME ``~((COMPL (l :'a Label)) IN L)``,
                                REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                                             (ASSUME ``WEAK_TRANS E u E1``)])) \\
        Q.EXISTS_TAC `restr L E1` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> art [] ] ]);

(* Observation congruence is substitutive under the relabelling operator. *)
val OBS_contracts_SUBST_RELAB = store_thm (
   "OBS_contracts_SUBST_RELAB",
  ``!E E'. OBS_contracts E E' ==> !rf. OBS_contracts (relab E rf) (relab E' rf)``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here, sharing start&end tacticals *)
 >> IMP_RES_TAC TRANS_RELAB
 >> RES_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `relab E2 rf` >> art [] \\
      CONJ_TAC >- ( MATCH_MP_TAC RELABELING >> art [] ) \\
      IMP_RES_TAC contracts_SUBST_RELAB >> art [],
      (* goal 2 (of 2) *)
      ASSUME_TAC (MATCH_MP WEAK_RELAB_rf
                           (ASSUME ``WEAK_TRANS E u' E1``)) \\
      Q.EXISTS_TAC `relab E1 rf` >> art [] \\
      IMP_RES_TAC WEAK_EQUIV_SUBST_RELAB >> art [] ]);

val OBS_contracts_SUBST_CONTEXT = store_thm (
   "OBS_contracts_SUBST_CONTEXT",
  ``!P Q. OBS_contracts P Q ==> !E. CONTEXT E ==> OBS_contracts (E P) (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `CONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [OBS_contracts_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC OBS_contracts_SUBST_PREFIX >> art [],
      (* goal 2 (of 5) *)
      MATCH_MP_TAC OBS_contracts_PRESD_BY_SUM >> art [],
      (* goal 3 (of 5) *)
      IMP_RES_TAC OBS_contracts_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC OBS_contracts_SUBST_RESTR >> art [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC OBS_contracts_SUBST_RELAB >> art [] ]);

val OBS_contracts_precongruence = store_thm (
   "OBS_contracts_precongruence", ``precongruence OBS_contracts``,
    PROVE_TAC [precongruence, OBS_contracts_PreOrder,
               OBS_contracts_SUBST_CONTEXT]);

(******************************************************************************)
(*                                                                            *)
(*                        OBS_contracts and trace                             *)
(*                                                                            *)
(******************************************************************************)

val OBS_contracts_AND_TRACE_tau = store_thm (
   "OBS_contracts_AND_TRACE_tau",
  ``!E E'. OBS_contracts E E' ==>
        !xs E1. TRACE E xs E1 /\ NO_LABEL xs ==>
            ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
                     (LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRACE_cases1
 >> Cases_on `xs` (* 2 sub-goals here *)
 >- ( take [`[]`, `E'`] >> REWRITE_TAC [TRACE_rule0] \\
      fs [NULL] >> IMP_RES_TAC OBS_contracts_IMP_contracts )
 >> fs [NULL]
 >> IMP_RES_TAC NO_LABEL_cases >> fs []
 >> IMP_RES_TAC OBS_contracts_TRANS_LEFT
 >> MP_TAC (Q.SPECL [`t`, `E1`]
                    (MATCH_MP (Q.SPECL [`u`, `E2`] contracts_AND_TRACE_tau)
                              (ASSUME ``u contracts E2``)))
 >> RW_TAC std_ss []
 >> take [`tau :: xs'`, `E2'`] >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC TRACE_rule1 >> Q.EXISTS_TAC `E2` >> art [])
 >> RW_TAC arith_ss [LENGTH]
 >> REWRITE_TAC [NO_LABEL_cases] >> art []);

val OBS_contracts_AND_TRACE_label = store_thm (
   "OBS_contracts_AND_TRACE_label",
  ``!E E'. OBS_contracts E E' ==>
        !xs l E1. TRACE E xs E1 /\ UNIQUE_LABEL (label l) xs ==>
            ?xs' E2. TRACE E' xs' E2 /\ E1 contracts E2 /\
                (LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRACE_cases1
 >> Cases_on `xs` (* 2 sub-goals here *)
 >- ( take [`[]`, `E'`] >> REWRITE_TAC [TRACE_rule0] \\
      fs [NULL] >> IMP_RES_TAC OBS_contracts_IMP_contracts )
 >> Cases_on `h` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      fs [UNIQUE_LABEL_cases1] \\
      IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
      MP_TAC (Q.SPECL [`t`, `l`, `E1`]
                      (MATCH_MP (Q.SPECL [`u`, `E2`] contracts_AND_TRACE_label)
                                (ASSUME ``u contracts E2``))) \\
      RW_TAC std_ss [] \\
      take [`tau :: xs'`, `E2'`] >> art [] \\
      CONJ_TAC >- ( MATCH_MP_TAC TRACE_rule1 >> Q.EXISTS_TAC `E2` >> art [] ) \\
      RW_TAC arith_ss [LENGTH] \\
      REWRITE_TAC [UNIQUE_LABEL_cases1] >> art [],
      (* goal 2 (of 2) *)
      fs [UNIQUE_LABEL_cases2] \\
      IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
      MP_TAC (Q.SPECL [`t`, `E1`]
                      (MATCH_MP (Q.SPECL [`u`, `E2`] contracts_AND_TRACE_tau)
                                (ASSUME ``u contracts E2``))) \\
      RW_TAC std_ss [] \\
      take [`label l :: xs'`, `E2'`] >> art [] \\
      CONJ_TAC >- ( MATCH_MP_TAC TRACE_rule1 >> Q.EXISTS_TAC `E2` >> art [] ) \\
      RW_TAC arith_ss [LENGTH] \\
      REWRITE_TAC [UNIQUE_LABEL_cases2] >> art [] ]);

val OBS_contracts_WEAK_TRANS_label' = store_thm (
   "OBS_contracts_WEAK_TRANS_label'",
  ``!E E'. OBS_contracts E E' ==>
        !l E2. WEAK_TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases1 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      IMP_RES_TAC WEAK_TRANS_IMP_EPS \\
      MATCH_MP_TAC EPS_AND_WEAK_TRANS \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
      IMP_RES_TAC WEAK_EQUIV_EPS' \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      MATCH_MP_TAC WEAK_TRANS_AND_EPS \\
      Q.EXISTS_TAC `E1` >> art [] ]);

(******************************************************************************)
(*                                                                            *)
(*      Is OBS_contracts coarsest precongruence contained in `contracts`?     *)
(*                                                                            *)
(******************************************************************************)

(* (pre)congruence closure of `contracts` relation *)
val C_contracts = new_definition (
   "C_contracts", ``C_contracts = CC $contracts``);

(* |- C_contracts = (λg h. ∀c. CONTEXT c ⇒ c g ⪰ᵇ c h) *)
val C_contracts_thm = save_thm (
   "C_contracts_thm", REWRITE_RULE [CC_def] C_contracts);

val C_contracts_precongruence = store_thm (
   "C_contracts_precongruence", ``precongruence $C_contracts``,
    PROVE_TAC [C_contracts, CC_precongruence, contracts_PreOrder]);

val OBS_contracts_IMP_C_contracts = store_thm (
   "OBS_contracts_IMP_C_contracts", ``!p q. OBS_contracts p q ==> C_contracts p q``,
    REWRITE_TAC [C_contracts, GSYM RSUBSET]
 >> ASSUME_TAC OBS_contracts_precongruence
 >> `OBS_contracts RSUBSET $contracts`
        by PROVE_TAC [OBS_contracts_IMP_contracts, GSYM RSUBSET]
 >> MATCH_MP_TAC PCC_is_coarsest >> art []);

Definition SUM_contracts :
    SUM_contracts = (\p q. !r. closed r ==> (sum p r) contracts (sum q r))
End

Theorem C_contracts_IMP_SUM_contracts :
    !p q. C_contracts p q ==> SUM_contracts p q
Proof
    rw [C_contracts, SUM_contracts, CC_def]
 >> Q.PAT_X_ASSUM ‘!c. CONTEXT c ==> _’ MP_TAC
 >> Know `CONTEXT (\(t :'a CCS). t) /\ CONTEXT (\t. r)`
 >- rw [CONTEXT1, CONTEXT2]
 >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP CONTEXT4))
 >> DISCH_TAC >> RES_TAC
 >> POP_ASSUM (MP_TAC o BETA_RULE) >> Rewr
QED

val OBS_contracts_IMP_SUM_contracts = store_thm (
   "OBS_contracts_IMP_SUM_contracts",
  ``!p q. OBS_contracts p q ==> SUM_contracts p q``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC C_contracts_IMP_SUM_contracts
 >> IMP_RES_TAC OBS_contracts_IMP_C_contracts);

(* OBS_contracts ==> C_contracts (coarsest) ==> SUM_contracts
        /\                                          ||
        ||                                          ||
        ++===================<<<====================++
 *)
Theorem SUM_contracts_IMP_OBS_contracts :
    !p q. free_action p /\ free_action q ==>
          (SUM_contracts p q ==> OBS_contracts p q)
Proof
    REWRITE_TAC [SUM_contracts, free_action_def, OBS_contracts]
 >> BETA_TAC
 >> reverse (rpt STRIP_TAC) (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2), same as goal 2 of COARSEST_CONGR_RL *)
      ASSUME_TAC (Q.SPEC `prefix (label a') nil`
                         (ASSUME ``!r. closed r ==> (sum p r) contracts (sum q r)``)) \\
      fs [] >> IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a') nil`)) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        STRIP_ASSUME_TAC (MATCH_MP contracts_TRANS_tau'
                             (ASSUME ``$contracts (sum p (prefix (label a') nil))
                                                  (sum q (prefix (label a') nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC EPS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          `TRANS E1 (label a') nil` by RW_TAC std_ss [SUM2, PREFIX] \\
          STRIP_ASSUME_TAC (MATCH_MP WEAK_EQUIV_TRANS_label
                                     (ASSUME ``WEAK_EQUIV E1 E2``)) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          RES_TAC,                              (* initial assumption of `q` is used here *)
          (* goal 1.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) tau u``
                      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.1.2.1 (of 4) *)
            Q.EXISTS_TAC `E1` >> art [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`p`, `u`] >> art [EPS_REFL],
            (* goal 1.1.2.2 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ] ],
        (* goal 1.2 (of 2) *)
        STRIP_ASSUME_TAC (MATCH_MP contracts_TRANS_label'
                             (ASSUME ``$contracts (sum p (prefix (label a') nil))
                                                  (sum q (prefix (label a') nil))``)) \\
        RES_TAC \\
        IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) tau E'``
                      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.2.1.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> art [] \\
            IMP_RES_TAC TRANS_TAU_AND_WEAK,
            (* goal 1.2.1.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ],
          (* goal 1.2.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a') nil)) (label L) E'``
                      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.2.2.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> art [] \\
            REWRITE_TAC [WEAK_TRANS] \\
            take [`p`, `E'`] >> art [EPS_REFL],
            (* goal 1.2.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            PAT_X_ASSUM ``label L = label a'`` (ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
            `TRANS q (label a') E2` by RW_TAC std_ss [] \\
            POP_ASSUM (ASSUME_TAC o (MATCH_MP TRANS_IMP_WEAK_TRANS)) \\
            RES_TAC ] ] ],                      (* initial assumption of `q` is used here *)
      (* goal 2 (of 2) *)
      ASSUME_TAC (Q.SPEC `prefix (label a) nil`
                         (ASSUME ``!r. closed r ==> (sum p r) contracts (sum q r)``)) \\
      fs [] >> IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) nil`)) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        STRIP_ASSUME_TAC (MATCH_MP contracts_TRANS_tau
                             (ASSUME ``$contracts (sum p (prefix (label a) nil))
                                                  (sum q (prefix (label a) nil))``)) \\
        RES_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          Q.ABBREV_TAC `E2 = q + label a..nil` \\
          `TRANS E2 (label a) nil` by PROVE_TAC [SUM2, PREFIX] \\
          STRIP_ASSUME_TAC (MATCH_MP contracts_TRANS_label'
                                     (ASSUME ``E1 contracts E2``)) \\
          RES_TAC \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          RES_TAC,
          (* goal 2.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) nil)) tau E2``
                      (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 4) *)
            Q.EXISTS_TAC `E2` >> art [],
            (* goal 2.1.2.2 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct] ] ],
        (* goal 2.2 (of 2) *)
        STRIP_ASSUME_TAC (MATCH_MP contracts_TRANS_label
                             (ASSUME ``$contracts (sum p (prefix (label a) nil))
                                                  (sum q (prefix (label a) nil))``)) \\
        RES_TAC \\
        PAT_X_ASSUM ``TRANS (sum q (prefix (label a) nil)) (label x) E2``
                    (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
        [ (* goal 2.2.2.1 (of 2) *)
          Q.EXISTS_TAC `E2` >> art [],
          (* goal 2.2.2.2 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          PAT_X_ASSUM ``label x = label a``
                      (ASSUME_TAC o (REWRITE_RULE [Action_11])) \\
          `TRANS p (label a) E1` by RW_TAC std_ss [] \\
          POP_ASSUM (ASSUME_TAC o (MATCH_MP TRANS_IMP_WEAK_TRANS)) \\
          RES_TAC ] ] ]
QED

val COARSEST_PRECONGR_RL = save_thm (
   "COARSEST_PRECONGR_RL",
    BETA_RULE (REWRITE_RULE [SUM_contracts] SUM_contracts_IMP_OBS_contracts));

(* Assuming p & q have free actions, OBS_contracts is the coarsest precongruence
   contained in `contracts`! *)
val COARSEST_PRECONGR_THM = store_thm (
   "COARSEST_PRECONGR_THM",
  ``!p q. free_action p /\ free_action q ==> (OBS_contracts p q = SUM_contracts p q)``,
    rpt STRIP_TAC
 >> EQ_TAC
 >- REWRITE_TAC [OBS_contracts_IMP_SUM_contracts]
 >> MATCH_MP_TAC SUM_contracts_IMP_OBS_contracts >> art []);

(* |- !p q.
        free_action p /\ free_action q ==>
        (OBS_contracts p q <=> !r. closed r ==> p + r contracts q + r)
 *)
val COARSEST_PRECONGR_THM' = save_thm (
   "COARSEST_PRECONGR_THM'",
    BETA_RULE (REWRITE_RULE [SUM_contracts] COARSEST_PRECONGR_THM));

(******************************************************************************)
(*                                                                            *)
(*  Coarsest precongruence contained in `contracts` (full, EXPRESS/SOS 2018)  *)
(*                                                                            *)
(******************************************************************************)

(* |- !p q. OBS_contracts p q ==> !r. closed r ==> p + r contracts q + r *)
val COARSEST_PRECONGR_LR = save_thm ((* NEW *)
   "COARSEST_PRECONGR_LR",
    BETA_RULE (REWRITE_RULE [SUM_contracts] OBS_contracts_IMP_SUM_contracts));
(*  or prove directly by:
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC OBS_contracts_IMP_contracts
 >> RW_TAC std_ss [OBS_contracts_SUBST_SUM_R] *)

(* This is the OBS_contracts version of PROP3_COMMON *)
Theorem COARSEST_PRECONGR_LEMMA :
    !p q. (?k. STABLE k /\ closed k /\
               (!p' u. WEAK_TRANS p u p' ==> ~(WEAK_EQUIV p' k)) /\
               (!q' u. WEAK_TRANS q u q' ==> ~(WEAK_EQUIV q' k))) ==>
          (!r. closed r ==> (sum p r) contracts (sum q r)) ==> OBS_contracts p q
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!r. closed r ==> (sum p r) contracts (sum q r)’
                  (ASSUME_TAC o (Q.SPEC `prefix (label a) k`))
 >> rfs []
 >> REWRITE_TAC [OBS_contracts]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) k`)) \\
      PAT_X_ASSUM ``$contracts (sum p (prefix (label a) k)) (sum q (prefix (label a) k))``
        (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [contracts_cases])) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          Q.ABBREV_TAC `E2 = sum q (prefix (label a) k)` \\
          `TRANS E2 (label a) k` by PROVE_TAC [PREFIX, SUM2] \\
          IMP_RES_TAC contracts_TRANS_label' \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          PROVE_TAC [],
          (* goal 1.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) k)) tau E2``
            (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 1.1.2.1 (of 2) *)
            Q.EXISTS_TAC `E2` >> art [],
            (* goal 1.1.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct_label] ] ],
        (* goal 1.2 (of 2) *)
        Cases_on `x = a` >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          FULL_SIMP_TAC std_ss [] >> RES_TAC \\
          Q.EXISTS_TAC `E2` >> art [] \\
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) k)) (label a) E2``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) \\
          IMP_RES_TAC TRANS_PREFIX \\
          `WEAK_EQUIV E1 k` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
          IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
          RES_TAC,
          (* goal 1.2.2 (of 2) *)
          RES_TAC \\
          Q.EXISTS_TAC `E2` >> art [] \\
          PAT_X_ASSUM ``TRANS (sum q (prefix (label a) k)) (label x) E2``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) \\
          IMP_RES_TAC TRANS_PREFIX \\
          RW_TAC std_ss [Action_11] ] ],
      (* goal 2 (of 2), almost symmetric with goal 1 *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `prefix (label a) k`)) \\
      PAT_X_ASSUM ``$contracts (sum p (prefix (label a) k)) (sum h (prefix (label a) k))``
        (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [contracts_cases])) \\
      Cases_on `u` >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC \\
        PAT_X_ASSUM ``EPS (sum p (prefix (label a) k)) E1``
          (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [EPS_cases1])) >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          `TRANS E1 (label a) k` by PROVE_TAC [PREFIX, SUM2] \\
          IMP_RES_TAC WEAK_EQUIV_TRANS_label \\
          IMP_RES_TAC TRANS_TAU_AND_WEAK \\
          `WEAK_EQUIV E2' k` by PROVE_TAC [WEAK_EQUIV_SYM] \\ (* one extra step *)
          PROVE_TAC [],
          (* goal 2.1.2 (of 2) *)
          PAT_X_ASSUM ``TRANS (sum p (prefix (label a) k)) tau u``
            (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            Q.EXISTS_TAC `E1` >> art [] \\
            IMP_RES_TAC TRANS_AND_EPS,
            (* goal 2.1.2.2 (of 2) *)
            IMP_RES_TAC TRANS_PREFIX \\
            RW_TAC std_ss [Action_distinct_label] ] ],
        (* goal 2.2 (of 2) *)
        Cases_on `x = a` >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          FULL_SIMP_TAC std_ss [] >> RES_TAC \\
          Q.EXISTS_TAC `E1` >> art [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 2.2.1.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum p (prefix (label a) k)) tau E'``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 2.2.1.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 2.2.1.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum p (prefix (label a) k)) (label a) E'``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 2.2.1.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              `WEAK_EQUIV E2 k` by PROVE_TAC [EPS_STABLE', WEAK_EQUIV_SYM] \\
              IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
              RES_TAC ] ],
          (* goal 2.2.2 (of 2) *)
          RES_TAC \\
          Q.EXISTS_TAC `E1` >> art [] \\
          IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
          [ (* goal 2.2.2.1 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum p (prefix (label a) k)) tau E'``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.2.1.1 (of 2) *)
              IMP_RES_TAC TRANS_TAU_AND_WEAK,
              (* goal 2.2.2.1.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_distinct] ],
            (* goal 2.2.2.2 (of 2) *)
            PAT_X_ASSUM ``TRANS (sum p (prefix (label a) k)) (label x) E'``
                (STRIP_ASSUME_TAC o (MATCH_MP TRANS_SUM)) >| (* 2 sub-goals here *)
            [ (* goal 2.2.2.2.1 (of 2) *)
              IMP_RES_TAC TRANS_AND_EPS,
              (* goal 2.2.2.2.2 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              RW_TAC std_ss [Action_11] ] ] ] ] ]
QED

(* The finite-state version of COARSEST_PRECONGR_THM; i. e.
   The contraction version of COARSEST_CONGR_FINITE (van Glabbeek scenario) *)
val COARSEST_PRECONGR_FINITE = store_thm ((* NEW *)
   "COARSEST_PRECONGR_FINITE",
  ``!p q. finite_state p /\ finite_state q ==>
          (OBS_contracts p q = !r. closed r ==> (sum p r) contracts (sum q r))``,
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [COARSEST_PRECONGR_LR]
 >> MP_TAC (Q.SPECL [`p`, `q`] KLOP_LEMMA_FINITE) (* in CoarsestCongrTheory *)
 >> RW_TAC std_ss [COARSEST_PRECONGR_LEMMA]);

(* Another version with SUM_contracts used *)
val COARSEST_PRECONGR_FINITE' = store_thm (
   "COARSEST_PRECONGR_FINITE'",
  ``!p q. finite_state p /\ finite_state q ==> (OBS_contracts p q = SUM_contracts p q)``,
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [OBS_contracts_IMP_SUM_contracts]
 >> REWRITE_TAC [SUM_contracts]
 >> BETA_TAC >> rpt STRIP_TAC
 >> MP_TAC COARSEST_PRECONGR_FINITE
 >> RW_TAC std_ss []);

(* Bibliography:
 *
 * [1] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 * [2] R.J. van Glabbeek, “A characterisation of weak bisimulation congruence”, in Processes,
 *     Terms and Cycles: Steps on the Road to Infinity, Essays dedicated to Jan Willem Klop, on the
 *     occasion of his 60th birthday, LNCS 3838, 26-39. Springer-Verlag, 2005.
 *)

val _ = export_theory ();
val _ = html_theory "Contraction";

(* last updated: Oct 14, 2017 *)
