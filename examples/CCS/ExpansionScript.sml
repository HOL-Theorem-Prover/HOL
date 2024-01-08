(* ========================================================================== *)
(* FILE          : ExpansionScript.sml                                        *)
(* DESCRIPTION   : EXPANSION and `expands' relation                           *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory listTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory;
open WeakEQTheory WeakLawsTheory CongruenceTheory TraceTheory;

val _ = new_theory "Expansion";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*                        The expansion relation                              *)
(*                                                                            *)
(******************************************************************************)

(* The definitin is confirmed with [1], [2] and [3] *)
val EXPANSION = new_definition ("EXPANSION",
  ``EXPANSION (Exp: 'a simulation) =
    !(E :'a CCS) (E' :'a CCS). Exp E E' ==>
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
                ?E2. TRANS E' (label l) E2 /\ Exp E1 E2) /\
         (!E2. TRANS E' (label l) E2 ==>
                ?E1. WEAK_TRANS E (label l) E1 /\ Exp E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> Exp E1 E' \/ ?E2. TRANS E' tau E2 /\ Exp E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. WEAK_TRANS E tau E1 /\ Exp E1 E2)``);

(* alternative definition *)
val EXPANSION_ALT = store_thm (
   "EXPANSION_ALT",
  ``EXPANSION (Exp: 'a simulation) =
    !(E :'a CCS) (E' :'a CCS). Exp E E' ==>
       (!l E1. TRANS E (label l) E1 ==> ?E2. TRANS E' (label l) E2 /\ Exp E1 E2) /\
       (!  E1. TRANS E    tau    E1 ==> Exp E1 E' \/ ?E2. TRANS E' tau E2 /\ Exp E1 E2) /\
       (!u E2. TRANS E'     u    E2 ==> ?E1. WEAK_TRANS E u E1 /\ Exp E1 E2)``,
    EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [EXPANSION] \\
      REPEAT STRIP_TAC >| (* 3 sub-goals here *)
      [ (* goal 1 (of 3) *)
        RES_TAC >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
        (* goal 2 (of 3) *)
        RES_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1 (of 2) *)
          DISJ1_TAC >> ASM_REWRITE_TAC [],
          (* goal 2.2 (of 2) *)
          DISJ2_TAC \\
          Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ],
        (* goal 3 (of 3) *)
        Cases_on `u` \\ (* 2 sub-goals sharing the same tacticals *)
        RES_TAC >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      REWRITE_TAC [EXPANSION] \\
      REPEAT STRIP_TAC >> RES_TAC >| (* 5 sub-goals here *)
      [ Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
        DISJ1_TAC >> ASM_REWRITE_TAC [],
        DISJ2_TAC >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ] ]);

(* The identity relation is a EXPANSION. *)
val IDENTITY_EXPANSION = store_thm (
   "IDENTITY_EXPANSION", ``EXPANSION Id``,
    PURE_ONCE_REWRITE_TAC [EXPANSION_ALT]
 >> rpt STRIP_TAC >> rfs []
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS);

val EXPANSION_EPS = store_thm (
   "EXPANSION_EPS",
  ``!(Exp: 'a simulation). EXPANSION Exp ==>
     !E E'. Exp E E' ==> !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ Exp E1 E2``,
    REPEAT STRIP_TAC
 >> qpat_x_assum `Exp E E'` MP_TAC
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
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E1 E2``))
      >- ( Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

val EXPANSION_EPS' = store_thm (
   "EXPANSION_EPS'",
  ``!(Exp: 'a simulation). EXPANSION Exp ==>
     !E E'. Exp E E' ==> !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ Exp E1 E2``,
    REPEAT STRIP_TAC
 >> qpat_x_assum `Exp E E'` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E2`, `E2`)
 >> Q.SPEC_TAC (`E'`, `E'`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E` >> RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E1 E2``)) \\
      `WEAK_TRANS E tau E1'` by PROVE_TAC [EPS_AND_WEAK_TRANS] \\
      `EPS E E1'` by PROVE_TAC [WEAK_TRANS_IMP_EPS] \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] ]);

(* NOTE: EXPANSION_WEAK_TRANS doens't hold *)
val EXPANSION_WEAK_TRANS' = store_thm (
   "EXPANSION_WEAK_TRANS'",
  ``!(Exp: 'a simulation). EXPANSION Exp ==>
     !E E'. Exp E E' ==>
        !u E2. WEAK_TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ Exp E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC
      (MATCH_MP (MATCH_MP EXPANSION_EPS' (ASSUME ``EXPANSION Exp``))
                (ASSUME ``(Exp :'a simulation) E E'``))
 >> IMP_RES_TAC
      (MATCH_MP (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp``))
                (ASSUME ``(Exp :'a simulation) E1' E1``))
 >> IMP_RES_TAC
      (MATCH_MP (MATCH_MP EXPANSION_EPS' (ASSUME ``EXPANSION Exp``))
                (ASSUME ``(Exp :'a simulation) E1'' E2'``))
 >> Q.EXISTS_TAC `E1'''`
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC EPS_WEAK_EPS
 >> take [`E1'`, `E1''`]
 >> ASM_REWRITE_TAC []);

(* The composition of two EXPANSIONs is an EXPANSION. *)
val COMP_EXPANSION = store_thm (
   "COMP_EXPANSION",
  ``!Exp1 Exp2. EXPANSION Exp1 /\ EXPANSION Exp2 ==> EXPANSION (Exp2 O Exp1)``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [EXPANSION_ALT, O_DEF]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      IMP_RES_TAC
        (MATCH_MP
          (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp1``))
          (ASSUME ``(Exp1 :'a simulation) E y``)) \\
      IMP_RES_TAC
        (MATCH_MP
          (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp2``))
          (ASSUME ``(Exp2 :'a simulation) y E'``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      IMP_RES_TAC
        (MATCH_MP
          (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp1``))
          (ASSUME ``(Exp1 :'a simulation) E y``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [] ) \\
      IMP_RES_TAC
        (MATCH_MP
          (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp2``))
          (ASSUME ``(Exp2 :'a simulation) y E'``)) (* 2 sub-goals here *)
      >- ( DISJ1_TAC >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      DISJ2_TAC >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION_ALT] (ASSUME ``EXPANSION Exp2``))
                  (ASSUME ``(Exp2 :'a simulation) y E'``)) \\
      IMP_RES_TAC
        (MATCH_MP (MATCH_MP EXPANSION_WEAK_TRANS' (ASSUME ``EXPANSION Exp1``))
                  (ASSUME ``(Exp1 :'a simulation) E y``)) \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

val STRONG_BISIM_IMP_EXPANSION = store_thm (
   "STRONG_BISIM_IMP_EXPANSION", ``!Exp. STRONG_BISIM Exp ==> EXPANSION Exp``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [EXPANSION]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [STRONG_BISIM] (ASSUME ``STRONG_BISIM Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [STRONG_BISIM] (ASSUME ``STRONG_BISIM Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS,
      (* goal 3 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [STRONG_BISIM] (ASSUME ``STRONG_BISIM Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [STRONG_BISIM] (ASSUME ``STRONG_BISIM Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS ]);

val EXPANSION_IMP_WEAK_BISIM = store_thm (
   "EXPANSION_IMP_WEAK_BISIM",
  ``!Exp. EXPANSION Exp ==> WEAK_BISIM Exp``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [WEAK_BISIM]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS,
      (* goal 2 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [EPS_REFL] ) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU,
      (* goal 4 (of 4) *)
      IMP_RES_TAC
        (MATCH_MP (REWRITE_RULE [EXPANSION] (ASSUME ``EXPANSION Exp``))
                  (ASSUME ``(Exp :'a simulation) E E'``)) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_TRANS_IMP_EPS ]);

(* `P expands Q` if P R Q for some expansion R, re-defined by co-induction
 * it means "P is at least as fast as Q", or more generally "Q uses at least as much
 * resources as P".
 *)
CoInductive expands :
    !(E :'a CCS) (E' :'a CCS).
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               ?E2. TRANS E' (label l) E2 /\ $expands E1 E2) /\
         (!E2. TRANS E' (label l) E2 ==>
               ?E1. WEAK_TRANS E (label l) E1 /\ $expands E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> $expands E1 E' \/ ?E2. TRANS E' tau E2 /\ $expands E1 E2) /\
       (!E2. TRANS E' tau E2 ==> ?E1. WEAK_TRANS E tau E1 /\ $expands E1 E2)
      ==> $expands E E'
End

val _ = set_fixity "expands" (Infixl 500);
val _ = Unicode.unicode_version { u = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D49, tmnm = "expands" };
val _ = TeX_notation { hol = UTF8.chr 0x2AB0 ^ UTF8.chr 0x1D49,
                       TeX = ("\\HOLTokenExpands{}", 1) };

(* a shorter version of `expands_cases` with only 3 branches *)
val expands_cases' = store_thm (
   "expands_cases'",
  ``!E E'. E expands E' =
        (!l E1. TRANS E (label l) E1 ==> ?E2. TRANS E' (label l) E2 /\ E1 expands E2) /\
        (!  E1. TRANS E tau E1 ==> E1 expands E' \/ (?E2. TRANS E' tau E2 /\ E1 expands E2)) /\
        (!u E2. TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ E1 expands E2)``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC >> POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [expands_cases])) \\
      fs [] >> rpt STRIP_TAC \\
      Cases_on `u` >> RES_TAC \\ (* 2 sub-goals here, same tacticals *)
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC expands_rules \\
      POP_ASSUM MP_TAC >> fs [] ]);

val expands_is_EXPANSION = store_thm (
   "expands_is_EXPANSION", ``EXPANSION $expands``,
    PURE_ONCE_REWRITE_TAC [EXPANSION]
 >> REPEAT GEN_TAC
 >> DISCH_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM expands_cases]
 >> ASM_REWRITE_TAC []);

(* the original definition now becomes a theorem *)
val expands_thm =  store_thm (
   "expands_thm",
  ``!P Q. P expands Q = ?Exp. Exp P Q /\ EXPANSION Exp``,
    NTAC 2 GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      EXISTS_TAC ``$expands`` \\
      ASM_REWRITE_TAC [expands_is_EXPANSION],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`Q`, `Q`) \\
      Q.SPEC_TAC (`P`, `P`) \\
      HO_MATCH_MP_TAC expands_coind \\ (* co-induction used here! *)
      METIS_TAC [EXPANSION] ]);

val EXPANSION_SUBSET_expands = store_thm ((* NEW *)
   "EXPANSION_SUBSET_expands",
  ``!Exp. EXPANSION Exp ==> Exp RSUBSET $expands``,
    PROVE_TAC [RSUBSET, expands_thm]);

(* "Half" theorems for `expands` relation *)
val expands_TRANS_label = store_thm (
   "expands_TRANS_label",
  ``!E E'. E expands E' ==>
     !l E1. TRANS E (label l) E1 ==> ?E2. TRANS E' (label l) E2 /\ E1 expands E2``,
    PROVE_TAC [expands_cases]);

val expands_TRANS_label' = store_thm (
   "expands_TRANS_label'",
  ``!E E'. E expands E' ==>
     !l E2. TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ E1 expands E2``,
    PROVE_TAC [expands_cases]);

val expands_TRANS_tau = store_thm (
   "expands_TRANS_tau",
  ``!E E'. E expands E' ==>
     !E1. TRANS E tau E1 ==> E1 expands E' \/ ?E2. TRANS E' tau E2 /\ E1 expands E2``,
    PROVE_TAC [expands_cases]);

val expands_TRANS_tau' = store_thm (
   "expands_TRANS_tau'",
  ``!E E'. E expands E' ==>
     !E2. TRANS E' tau E2 ==> ?E1. WEAK_TRANS E tau E1 /\ E1 expands E2``,
    PROVE_TAC [expands_cases]);

val expands_TRANS_action' = store_thm (
   "expands_TRANS_action'",
  ``!E E'. E expands E' ==>
     !u E2. TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ E1 expands E2``,
    rpt STRIP_TAC
 >> Cases_on `u`
 >- PROVE_TAC [expands_TRANS_tau']
 >> PROVE_TAC [expands_TRANS_label']);

(* The `expands` relation is reflexive *)
val expands_reflexive = store_thm (
   "expands_reflexive", ``reflexive $expands``,
    REWRITE_TAC [reflexive_def]
 >> GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [expands_thm]
 >> Q.EXISTS_TAC `Id`
 >> REWRITE_TAC [IDENTITY_EXPANSION]);

(* the version for easier use *)
val expands_REFL = save_thm (
   "expands_REFL", REWRITE_RULE [reflexive_def] expands_reflexive);

(* Syntactic equivalence implies expands. *)
val EQ_IMP_expands = store_thm (
   "EQ_IMP_expands", ``!E E'. (E = E') ==> E expands E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [expands_REFL]);

(* `expands` is a transitive relation. *)
val expands_transitive = store_thm (
   "expands_transitive", ``transitive $expands``,
    REWRITE_TAC [transitive_def]
 >> REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [expands_thm]
 >> STRIP_TAC
 >> Q.EXISTS_TAC `Exp' O Exp`
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC COMP_EXPANSION ]);

(* the version for easier use *)
val expands_TRANS = save_thm (
   "expands_TRANS", REWRITE_RULE [transitive_def] expands_transitive);

(* `expands` is a pre-order *)
val expands_PreOrder = store_thm (
   "expands_PreOrder", ``PreOrder $expands``,
    REWRITE_TAC [PreOrder, expands_reflexive, expands_transitive]);

val STRONG_EQUIV_IMP_expands = store_thm (
   "STRONG_EQUIV_IMP_expands", ``!P Q. STRONG_EQUIV P Q ==> P expands Q``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [expands_thm, STRONG_EQUIV]
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `Bsm` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC STRONG_BISIM_IMP_EXPANSION);

val expands_IMP_WEAK_EQUIV = store_thm (
   "expands_IMP_WEAK_EQUIV", ``!P Q. P expands Q ==> WEAK_EQUIV P Q``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [expands_thm, WEAK_EQUIV]
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `Exp` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EXPANSION_IMP_WEAK_BISIM);

val expands_EPS = store_thm (
   "expands_EPS",
  ``!E E'. E expands E' ==> !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ E1 expands E2``,
    REWRITE_TAC [expands_thm]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EXPANSION_EPS
 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `Exp` >> ASM_REWRITE_TAC []);

val expands_EPS' = store_thm (
   "expands_EPS'",
  ``!E E'. E expands E' ==> !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ E1 expands E2``,
    REWRITE_TAC [expands_thm]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EXPANSION_EPS'
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `Exp` >> ASM_REWRITE_TAC []);

val expands_WEAK_TRANS' = store_thm (
   "expands_WEAK_TRANS'",
  ``!E E'. E expands E' ==>
        !u E2. WEAK_TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ E1 expands E2``,
    REWRITE_TAC [expands_thm]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EXPANSION_WEAK_TRANS'
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `Exp` >> ASM_REWRITE_TAC []);

val expands_WEAK_TRANS_label = store_thm (
   "expands_WEAK_TRANS_label",
  ``!E E'. E expands E' ==>
        !l E1. WEAK_TRANS E (label l) E1 ==> ?E2. WEAK_TRANS E' (label l) E2 /\ E1 expands E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP expands_EPS (ASSUME ``E expands E'``))
 >> IMP_RES_TAC (MATCH_MP expands_TRANS_label (ASSUME ``E1' expands E2'``))
 >> IMP_RES_TAC (MATCH_MP expands_EPS (ASSUME ``E2 expands E2''``))
 >> Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [WEAK_TRANS]
 >> take [`E2'`, `E2''`] >> ASM_REWRITE_TAC []);

val expands_WEAK_TRANS_tau = store_thm (
   "expands_WEAK_TRANS_tau",
  ``!E E'. E expands E' ==>
        !E1. WEAK_TRANS E tau E1 ==> ?E2. EPS E' E2 /\ E1 expands E2``,
    rpt STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP expands_EPS (ASSUME ``E expands E'``))
 >> IMP_RES_TAC
        (MATCH_MP expands_TRANS_tau (ASSUME ``E1' expands E2'``)) (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (MATCH_MP expands_EPS (ASSUME ``E2 expands E2'``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_TRANS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC (MATCH_MP expands_EPS (ASSUME ``E2 expands E2''``)) \\
      Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

(******************************************************************************)
(*                                                                            *)
(*                       `expands` is precongruence                           *)
(*                                                                            *)
(******************************************************************************)

val expands_SUBST_PREFIX = store_thm (
   "expands_SUBST_PREFIX",
  ``!E E'. E expands E' ==> !u. (prefix u E) expands (prefix u E')``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [Q.SPECL [`prefix u E`, `prefix u E'`] expands_cases']
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [PREFIX],
      (* goal 2 (of 3) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [PREFIX],
      (* goal 3 (of 3) *)
      IMP_RES_TAC TRANS_PREFIX >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [WEAK_PREFIX] ]);

val expands_PRESD_BY_GUARDED_SUM = store_thm (
   "expands_PRESD_BY_GUARDED_SUM",
  ``!E1 E1' E2 E2' a1 a2. E1 expands E1' /\ E2 expands E2' ==>
        (sum (prefix a1 E1) (prefix a2 E2)) expands (sum (prefix a1 E1') (prefix a2 E2'))``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [expands_cases']
 >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 2 (of 3) *)
      DISJ2_TAC >> IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 3 (of 3) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM1 >> REWRITE_TAC [WEAK_PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX >> fs [] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM2 >> REWRITE_TAC [WEAK_PREFIX] ] ]);

val expands_PRESD_BY_PAR = store_thm (
   "expands_PRESD_BY_PAR",
  ``!E1 E1' E2 E2'.
        E1 expands E1' /\ E2 expands E2' ==> (par E1 E2) expands (par E1' E2')``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [expands_thm]
 >> Q.EXISTS_TAC `\x y.
                   ?F1 F1' F2 F2'.
                    (x = par F1 F2) /\ (y = par F1' F2') /\
                    F1 expands F1' /\ F2 expands F2'`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E1`, `E1'`, `E2`, `E2'`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [EXPANSION] (* cannot use EXPANSION_ALT here *)
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
                               (ASSUME ``TRANS E (label l) E1''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_label
                              (ASSUME ``F1 expands F1'``)) \\
        EXISTS_TAC ``par E2'' F2'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
          (* goal 1.1.2 (of 2) *)
          take [`E1'''`, `E2''`, `F2`, `F2'`] >> ASM_REWRITE_TAC [] ],
        (* goal 1.2 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_label
                              (ASSUME ``F2 expands F2'``)) \\
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
        IMP_RES_TAC (MATCH_MP expands_TRANS_label'
                              (ASSUME ``F1 expands F1'``)) \\
        EXISTS_TAC ``par E1''' F2`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          take [`E1'''`, `E1''`, `F2`, `F2'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_label'
                              (ASSUME ``F2 expands F2'``)) \\
        EXISTS_TAC ``par F1 E1'''`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          take [`F1`, `F1'`, `E1'''`, `E1''`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.3 (of 3) *)
        IMP_RES_TAC Action_distinct_label ],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
                               (ASSUME ``TRANS E tau E1''``)) \\
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 3.1 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_tau
                              (ASSUME ``F1 expands F1'``)) >| (* 2 sub-goals here *)
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
        IMP_RES_TAC (MATCH_MP expands_TRANS_tau
                              (ASSUME ``F2 expands F2'``)) >| (* 2 sub-goals here *)
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
        IMP_RES_TAC (MATCH_MP expands_TRANS_label (ASSUME ``F1 expands F1'``)) \\
        IMP_RES_TAC (MATCH_MP expands_TRANS_label (ASSUME ``F2 expands F2'``)) \\
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
        IMP_RES_TAC (MATCH_MP expands_TRANS_tau' (ASSUME ``F1 expands F1'``)) \\
        EXISTS_TAC ``par E1''' F2`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
          (* goal 4.1.2 (of 2) *)
          take [`E1'''`, `E1''`, `F2`, `F2'`] >> ASM_REWRITE_TAC [] ],
        (* goal 4.2 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_tau' (ASSUME ``F2 expands F2'``)) \\
        EXISTS_TAC ``par F1 E1'''`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
          (* goal 4.2.2 (of 2) *)
          take [`F1`, `F1'`, `E1'''`, `E1''`] >> ASM_REWRITE_TAC [] ],
        (* goal 4.3 (of 3) *)
        IMP_RES_TAC (MATCH_MP expands_TRANS_label' (ASSUME ``F1 expands F1'``)) \\
        IMP_RES_TAC (MATCH_MP expands_TRANS_label' (ASSUME ``F2 expands F2'``)) \\
        EXISTS_TAC ``par E1''' E1''''`` \\
        reverse CONJ_TAC
        >- ( take [`E1'''`, `E1''`, `E1''''`, `E2'''`] >> ASM_REWRITE_TAC [] ) \\
        ONCE_ASM_REWRITE_TAC [] \\
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

val expands_SUBST_RESTR = store_thm (
   "expands_SUBST_RESTR",
  ``!E E'. E expands E' ==> !L. (restr L E) expands (restr L E')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [expands_thm]
 >> Q.EXISTS_TAC `\x y. ?E1 E2 L'. (x = restr L' E1) /\ (y = restr L' E2) /\ E1 expands E2`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E`, `E'`, `L`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [EXPANSION]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                               (ASSUME ``TRANS E'' (label l) E1'``)) \\
      IMP_RES_TAC TRANS_RESTR >- IMP_RES_TAC Action_distinct_label \\
      IMP_RES_TAC (MATCH_MP expands_TRANS_label (ASSUME ``E1 expands E2``)) \\
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
      IMP_RES_TAC (MATCH_MP expands_TRANS_label' (ASSUME ``E1 expands E2``)) \\
      Q.EXISTS_TAC `restr L' E1'` \\
      ASM_REWRITE_TAC
        [MATCH_MP WEAK_RESTR_label
                  (LIST_CONJ [ASSUME ``~((l' :'a Label) IN L')``,
                              ASSUME ``~((COMPL (l' :'a Label)) IN L')``,
                              REWRITE_RULE [ASSUME ``label (l :'a Label) = label l'``]
                                           (ASSUME ``WEAK_TRANS E1 (label l) E1'``)])] \\
      take [`E1'`, `E''''`, `L'`] >> ASM_REWRITE_TAC [],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                               (ASSUME ``TRANS E'' tau E1'``)) \\
      reverse (IMP_RES_TAC TRANS_RESTR) >- IMP_RES_TAC Action_distinct \\
      IMP_RES_TAC (MATCH_MP expands_TRANS_tau (ASSUME ``E1 expands E2``))
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
      IMP_RES_TAC (MATCH_MP expands_TRANS_tau' (ASSUME ``E1 expands E2``)) \\
      Q.EXISTS_TAC `restr L' E1'` \\
      reverse CONJ_TAC
      >- ( take [`E1'`, `E''''`, `L'`] >> ASM_REWRITE_TAC [] ) \\
      ONCE_ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_TRANS] \\
      STRIP_ASSUME_TAC
        (REWRITE_RULE [WEAK_TRANS] (ASSUME ``WEAK_TRANS E1 tau E1'``)) \\
      take [`restr L' E1''`, `restr L' E2''`] \\
      IMP_RES_TAC EPS_RESTR >> fs [] \\
      MATCH_MP_TAC RESTR >> fs [] ]);

val expands_SUBST_RELAB = store_thm (
   "expands_SUBST_RELAB",
  ``!E E'. E expands E' ==> !rf. (relab E rf) expands (relab E' rf)``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [expands_thm]
 >> Q.EXISTS_TAC
        `\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\ E1 expands E2`
 >> BETA_TAC
 >> CONJ_TAC >- ( take [`E`, `E'`, `rf`] >> ASM_REWRITE_TAC [] )
 >> PURE_ONCE_REWRITE_TAC [EXPANSION]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                               (ASSUME ``TRANS E'' (label l) E1'``)) \\
      IMP_RES_TAC TRANS_RELAB \\
      qpat_x_assum `label l = relabel rf' u'` (ASSUME_TAC o SYM) \\
      IMP_RES_TAC Relab_label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = label l'``]
                               (ASSUME ``TRANS E1 u' E''''``)) \\
      IMP_RES_TAC (MATCH_MP expands_TRANS_label (ASSUME ``E1 expands E2``)) \\
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
      IMP_RES_TAC (MATCH_MP expands_TRANS_label' (ASSUME ``E1 expands E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      reverse CONJ_TAC
      >- ( take [`E1'`, `E''''`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
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
      IMP_RES_TAC (MATCH_MP expands_TRANS_tau (ASSUME ``E1 expands E2``))
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
      IMP_RES_TAC (MATCH_MP expands_TRANS_tau' (ASSUME ``E1 expands E2``)) \\
      EXISTS_TAC ``relab E1' rf'`` \\
      reverse CONJ_TAC
      >- ( take [`E1'`, `E''''`, `rf'`] >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      qpat_x_assum `relabel rf' u' = tau` (REWRITE_TAC o wrap o SYM) \\
      REWRITE_TAC [WEAK_TRANS] \\
      STRIP_ASSUME_TAC
        (REWRITE_RULE [WEAK_TRANS] (ASSUME ``WEAK_TRANS E1 tau E1'``)) \\
      take [`relab E1'' rf'`, `relab E2'' rf'`] \\
      IMP_RES_TAC EPS_RELAB_rf >> fs [] \\
      MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ]);

val expands_SUBST_GCONTEXT = store_thm (
   "expands_SUBST_GCONTEXT",
  ``!P Q. P expands Q ==> !E. GCONTEXT E ==> (E P) expands (E Q)``,
    rpt GEN_TAC >> DISCH_TAC
 >> Induct_on `GCONTEXT`
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >- ASM_REWRITE_TAC []
 >- REWRITE_TAC [expands_REFL]
 >| [ (* goal 1 (of 5) *)
      MATCH_MP_TAC expands_SUBST_PREFIX >> ASM_REWRITE_TAC [],
      (* goal 2 (of 5) *)
      MATCH_MP_TAC expands_PRESD_BY_GUARDED_SUM \\
      ASM_REWRITE_TAC [],
      (* goal 3 (of 5) *)
      IMP_RES_TAC expands_PRESD_BY_PAR,
      (* goal 4 (of 5) *)
      MATCH_MP_TAC expands_SUBST_RESTR >> ASM_REWRITE_TAC [],
      (* goal 5 (of 5) *)
      MATCH_MP_TAC expands_SUBST_RELAB >> ASM_REWRITE_TAC [] ]);

val expands_precongruence = store_thm (
   "expands_precongruence", ``precongruence' $expands``,
    PROVE_TAC [precongruence', expands_PreOrder, expands_SUBST_GCONTEXT]);

(******************************************************************************)
(*                                                                            *)
(*                   Trace, Weak transition and Expansion                     *)
(*                                                                            *)
(******************************************************************************)

val expands_AND_TRACE_tau_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==> NO_LABEL xs ==>
        !E'. E expands E' ==>
             ?xs' E2. TRACE E' xs' E2 /\ E1 expands E2 /\
                (LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC
 >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [TRACE_REFL, LENGTH] >> RW_TAC arith_ss [] )
 >> IMP_RES_TAC NO_LABEL_cases
 >> qpat_x_assum `NO_LABEL xs ==> X`
        (ASSUME_TAC o (fn thm => MATCH_MP thm (ASSUME ``NO_LABEL (xs :'a Action list)``)))
 >> Cases_on `h` >> FULL_SIMP_TAC std_ss [Action_distinct_label, LENGTH]
 >> IMP_RES_TAC expands_TRANS_tau >> RES_TAC (* 2 sub-goals here *)
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

val expands_AND_TRACE_tau = store_thm (
   "expands_AND_TRACE_tau",
  ``!E E'. E expands E' ==>
        !xs l E1. TRACE E xs E1 /\ NO_LABEL xs ==>
            ?xs' E2. TRACE E' xs' E2 /\ E1 expands E2 /\
                (LENGTH xs' <= LENGTH xs) /\ NO_LABEL xs'``,
    NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] expands_AND_TRACE_tau_lemma)
 >> RW_TAC std_ss []);

val expands_AND_TRACE_label_lemma = Q.prove (
   `!E xs E1. TRACE E xs E1 ==> !l. UNIQUE_LABEL (label l) xs ==>
        !E'. E expands E' ==>
             ?xs' E2. TRACE E' xs' E2 /\ E1 expands E2 /\
                (LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'`,
    HO_MATCH_MP_TAC TRACE_strongind
 >> rpt STRIP_TAC
 >- ( take [`[]`, `E'`] >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [TRACE_REFL, LENGTH] >> RW_TAC arith_ss [] )
 >> REWRITE_TAC [LENGTH]
 >> Cases_on `h` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC expands_TRANS_tau >| (* 2 sub-goals here *)
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
      IMP_RES_TAC expands_TRANS_label \\
      IMP_RES_TAC (EQ_IMP_LR UNIQUE_LABEL_cases2) \\
      IMP_RES_TAC (MATCH_MP expands_AND_TRACE_tau (ASSUME ``E' expands E2``)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      take [`label x :: xs'`, `E2'`] >> ASM_REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC TRACE2 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ) \\
      CONJ_TAC >- ( FULL_SIMP_TAC arith_ss [LENGTH] ) \\
      REWRITE_TAC [UNIQUE_LABEL_cases2] >> ASM_REWRITE_TAC [] ]);

val expands_AND_TRACE_label = store_thm (
   "expands_AND_TRACE_label",
  ``!E E'. E expands E' ==>
        !xs l E1. TRACE E xs E1 /\ UNIQUE_LABEL (label l) xs ==>
            ?xs' E2. TRACE E' xs' E2 /\ E1 expands E2 /\
                (LENGTH xs' <= LENGTH xs) /\ UNIQUE_LABEL (label l) xs'``,
    NTAC 2 (rpt GEN_TAC >> STRIP_TAC)
 >> MP_TAC (Q.SPECL [`E`, `xs`, `E1`] expands_AND_TRACE_label_lemma)
 >> RW_TAC std_ss []);

(******************************************************************************)
(*                                                                            *)
(*                Bisimulation Upto `expands` and context                     *)
(*                                                                            *)
(******************************************************************************)

(*
val BISIM_UPTO_expands_and_C = new_definition (
   "BISIM_UPTO_expands_and_C",
  ``BISIM_UPTO_expands_and_C (Wbsm: 'a simulation) =
    !E E'.
        Wbsm E E' ==>
        (!l.
          (!E1. TRANS E  (label l) E1 ==>
                ?E2. WEAK_TRANS E' (label l) E2 /\
                    (WEAK_EQUIV O (GCC Wbsm) O $expands) E1 E2) /\
          (!E2. TRANS E' (label l) E2 ==>
                ?E1. WEAK_TRANS E  (label l) E1 /\
                    ($expands O (GCC Wbsm) O WEAK_EQUIV) E1 E2)) /\
        (!E1. TRANS E  tau E1 ==>
              ?E2. EPS E' E2 /\ (WEAK_EQUIV O (GCC Wbsm) O $expands) E1 E2) /\
        (!E2. TRANS E' tau E2 ==>
              ?E1. EPS E  E1 /\ ($expands O (GCC Wbsm) O WEAK_EQUIV) E1 E2)``);
 *)

(* Bibliography:
 *
 * [1] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 * [2] Arun-Kumar, S., Hennessy, M.: An efficiency preorder for processes. Acta Informatica. 29, 737–760 (1992).
 * [3] Sangiorgi, D., Milner, R.: The problem of “Weak Bisimulation up to.” CONCUR'92. (1992).
 *)

val _ = export_theory ();
val _ = html_theory "Expansion";

(* last updated: Sep 28, 2017 *)
