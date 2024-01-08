(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory bisimulationTheory listTheory IndDefRules;

open CCSLib CCSTheory StrongEQTheory;

val _ = new_theory "WeakEQ";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*    Operational definition of obs. equiv. for CCS and related properties    *)
(*                                                                            *)
(******************************************************************************)

(* new definition for the epsilon transition relation. *)
val EPS_defn = ``\E E'. TRANS E tau E'``;
val EPS_def = Define `EPS = RTC ^EPS_defn`;

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
                            tok = ("=" ^ (UTF8.chr 0x03B5) ^ "=>"), term_name = "EPS" };
val _ = TeX_notation { hol = ("=" ^ (UTF8.chr 0x03B5) ^ "=>"),
                       TeX = ("\\HOLTokenEPS", 1) };

Theorem EPS_ETS :
    EPS = ETS TRANS tau
Proof
    REWRITE_TAC [ETS_def, EPS_def]
QED

Theorem ONE_TAU :
    !E E'. TRANS E tau E' ==> EPS E E'
Proof
    RW_TAC std_ss [EPS_ETS]
 >> MATCH_MP_TAC TS_IMP_ETS >> art []
QED

Theorem EPS_REFL :
    !E. EPS E E
Proof
    REWRITE_TAC [EPS_ETS, ETS_REFL]
QED

local
    val trans = (REWRITE_RULE [GSYM EPS_def]) o BETA_RULE o (ISPEC EPS_defn);
in

(* !x y z. EPS x y /\ EPS y z ==> EPS x z
 *)
val EPS_TRANS = save_thm ((* NEW *)
   "EPS_TRANS", trans (REWRITE_RULE [transitive_def] RTC_TRANSITIVE));

(* !P.
     (!x. P x x) /\ (!x y z. x --'t-> y /\ P y z ==> P x z) ==>
     !x y. EPS x y ==> P x y
 *)
val EPS_ind = save_thm ((* NEW *)
   "EPS_ind", trans RTC_INDUCT);

(* !P.
     (!x. P x x) /\ (!x y z. x --'t-> y /\ EPS y z /\ P y z ==> P x z) ==>
     !x y. EPS x y ==> P x y
 *)
val EPS_strongind = save_thm ((* NEW *)
   "EPS_strongind", trans RTC_STRONG_INDUCT);

(* !P.
     (!x. P x x) /\ (!x y z. P x y /\ y --'t-> z ==> P x z) ==>
     !x y. EPS x y ==> P x y
 *)
val EPS_ind_right = save_thm ((* NEW *)
   "EPS_ind_right", trans RTC_INDUCT_RIGHT1);

(* !P.
     (!x. P x x) /\ (!x y z. P x y /\ EPS x y /\ y --'t-> z ==> P x z) ==>
     !x y. EPS x y ==> P x y
 *)
val EPS_strongind_right = save_thm ((* NEW *)
   "EPS_strongind_right", trans RTC_STRONG_INDUCT_RIGHT1);

(* !x y. EPS x y <=> (x = y) \/ ?u. x --'t-> u /\ EPS u y
 *)
val EPS_cases1 = save_thm ((* NEW *)
   "EPS_cases1", trans RTC_CASES1);

(* !x y. EPS x y <=> (x = y) \/ ?u. EPS x u /\ u --'t-> y
 *)
val EPS_cases2 = save_thm ((* NEW *)
   "EPS_cases2", trans RTC_CASES2);

end; (* local *)

(* A slightly different version of EPS induction theorem *)
val EPS_INDUCT = store_thm ((* NEW *)
   "EPS_INDUCT", ``!P. (!E E'.    TRANS E tau E' ==> P E E') /\
                       (!E.       P E E) /\
                       (!E E1 E'. P E E1 /\ P E1 E' ==> P E E') ==>
                   !x y. EPS x y ==> P x y``,
    GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC EPS_ind
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      NTAC 2 RES_TAC]);

val EPS_INDUCT_TAC = RULE_INDUCT_THEN EPS_INDUCT ASSUME_TAC ASSUME_TAC;

(* This cases theorem is not the same with any theorem in relationTheory *)
val EPS_cases = store_thm ((* NEW *)
   "EPS_cases",
  ``!E E'. EPS E E' = TRANS E tau E' \/ (E = E') \/ ?E1. EPS E E1 /\ EPS E1 E'``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.SPEC_TAC (`E'`, `E'`) \\
      Q.SPEC_TAC (`E`, `E`) \\
      HO_MATCH_MP_TAC EPS_strongind (* must be strong *) \\
      REPEAT STRIP_TAC >- RW_TAC std_ss [] \\ (* 4 sub-goals here, first is easy *)
      NTAC 2 DISJ2_TAC \\ (* then the rest 3 goals share the same tacticals *)
      Q.EXISTS_TAC `E'` \\
      IMP_RES_TAC ONE_TAU \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      REPEAT STRIP_TAC >| (* 3 sub-goals here *)
      [ IMP_RES_TAC ONE_TAU,
        ASM_REWRITE_TAC [EPS_REFL],
        IMP_RES_TAC EPS_TRANS ] ]);

(******************************************************************************)
(*                                                                            *)
(*                             Weak transition                                *)
(*                                                                            *)
(******************************************************************************)

(* Define the weak transition relation (double arrow transition). *)
val WEAK_TRANS = new_definition ("WEAK_TRANS",
  ``WEAK_TRANS E u E' = ?E1 E2. EPS E E1 /\ TRANS E1 u E2 /\ EPS E2 E'``);

val _ =
    add_rule { term_name = "WEAK_TRANS", fixity = Infix (NONASSOC, 450),
        pp_elements = [ BreakSpace(1,0), TOK "==", HardSpace 0, TM, HardSpace 0,
                        TOK "=>", BreakSpace(1,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "==", TeX = ("\\HOLTokenWeakTransBegin", 1) };
val _ = TeX_notation { hol = "=>", TeX = ("\\HOLTokenWeakTransEnd", 1) };

Theorem WEAK_TRANS_WTS :
    WEAK_TRANS = WTS TRANS tau
Proof
    ASM_SIMP_TAC std_ss [WTS_def, WEAK_TRANS, FUN_EQ_THM, EPS_ETS]
QED

(* A transition is a particular weak transition. *)
Theorem TRANS_IMP_WEAK_TRANS :
    !E u E'. TRANS E u E' ==> WEAK_TRANS E u E'
Proof
    RW_TAC std_ss [WEAK_TRANS_WTS]
 >> MATCH_MP_TAC TS_IMP_WTS >> art []
QED

(* A weak transition on tau implies the epsilon relation. *)
val WEAK_TRANS_IMP_EPS = store_thm (
   "WEAK_TRANS_IMP_EPS", ``!E E'. WEAK_TRANS E tau E' ==> EPS E E'``,
    PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> MATCH_MP_TAC EPS_TRANS
 >> Q.EXISTS_TAC `E1`
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC EPS_TRANS
 >> Q.EXISTS_TAC `E2`
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC ONE_TAU
 >> ASM_REWRITE_TAC []);

val TRANS_TAU_IMP_EPS = store_thm ((* NEW *)
   "TRANS_TAU_IMP_EPS", ``!E E'. TRANS E tau E' ==> EPS E E'``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS
 >> IMP_RES_TAC WEAK_TRANS_IMP_EPS);

(* A weak transition on tau implies at least one transition on tau *)
val WEAK_TRANS_TAU_IMP_TRANS_TAU = store_thm ((* NEW *)
   "WEAK_TRANS_TAU_IMP_TRANS_TAU",
  ``!E E'. WEAK_TRANS E tau E' ==> ?E1. TRANS E tau E1 /\ EPS E1 E'``,
    REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> NTAC 3 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_strongind (* must be strong *)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

val TAU_PREFIX_EPS = store_thm ((* NEW *)
   "TAU_PREFIX_EPS", ``!E E'. EPS E E' ==> EPS (prefix tau E) E'``,
    REPEAT STRIP_TAC
 >> ONCE_REWRITE_TAC [EPS_cases1]
 >> DISJ2_TAC
 >> Q.EXISTS_TAC `E`
 >> ASM_REWRITE_TAC [PREFIX]);

val TAU_PREFIX_WEAK_TRANS = store_thm ((* NEW *)
   "TAU_PREFIX_WEAK_TRANS",
  ``!E u E'. WEAK_TRANS E u E' ==> WEAK_TRANS (prefix tau E) u E'``,
    REPEAT STRIP_TAC
 >> Cases_on `u` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_IMP_EPS \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`prefix tau E`, `E`] \\
      ASM_REWRITE_TAC [EPS_REFL, PREFIX],
      (* goal 2 (of 2) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E1`, `E2`] >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC TAU_PREFIX_EPS ]);

val EPS_WEAK_EPS = store_thm (
   "EPS_WEAK_EPS",
  ``!E E1 u E2 E'.
         EPS E E1 /\ WEAK_TRANS E1 u E2 /\ EPS E2 E' ==> WEAK_TRANS E u E'``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> Q.EXISTS_TAC `E1'`
 >> Q.EXISTS_TAC `E2'`
 >> ASM_REWRITE_TAC
       [MATCH_MP EPS_TRANS
                 (CONJ (ASSUME ``EPS E E1``) (ASSUME ``EPS E1 E1'``)),
        MATCH_MP EPS_TRANS
                 (CONJ (ASSUME ``EPS E2' E2``) (ASSUME ``EPS E2 E'``))]);

val EPS_AND_WEAK_TRANS = store_thm ((* NEW *)
   "EPS_AND_WEAK_TRANS",
  ``!E E1 u E2.
         EPS E E1 /\ WEAK_TRANS E1 u E2 ==> WEAK_TRANS E u E2``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> Q.EXISTS_TAC `E1'`
 >> Q.EXISTS_TAC `E2'`
 >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EPS_TRANS);

val WEAK_TRANS_AND_EPS = store_thm ((* NEW *)
   "WEAK_TRANS_AND_EPS",
  ``!E1 u E2 E'.
         WEAK_TRANS E1 u E2 /\ EPS E2 E' ==> WEAK_TRANS E1 u E'``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> Q.EXISTS_TAC `E1'`
 >> Q.EXISTS_TAC `E2'`
 >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EPS_TRANS);

val TRANS_TAU_AND_WEAK = store_thm ((* NEW *)
   "TRANS_TAU_AND_WEAK",
  ``!E E1 u E'. TRANS E tau E1 /\ WEAK_TRANS E1 u E' ==> WEAK_TRANS E u E'``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS
 >> IMP_RES_TAC WEAK_TRANS_IMP_EPS
 >> MATCH_MP_TAC EPS_WEAK_EPS
 >> take [`E1`, `E'`]
 >> ASM_REWRITE_TAC [EPS_REFL]);

val TRANS_AND_EPS = store_thm ((* NEW *)
   "TRANS_AND_EPS", ``!E u E1 E'. TRANS E u E1 /\ EPS E1 E' ==> WEAK_TRANS E u E'``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [WEAK_TRANS]
 >> take [`E`, `E1`]
 >> ASM_REWRITE_TAC [EPS_REFL]);

val EPS_IMP_WEAK_TRANS = store_thm (
   "EPS_IMP_WEAK_TRANS",
  ``!E E'. EPS E E' ==> (E = E') \/ WEAK_TRANS E tau E'``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [EPS_cases1]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      DISJ2_TAC \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E`, `u`] \\
      ASM_REWRITE_TAC [EPS_REFL] ]);

(* The two possible cases for the 1st step in WEAK_TRANS,
   NOTE: when (u = tau), after the first step it could be either EPS or WEAK_TRANS *)
val WEAK_TRANS_cases1 = store_thm ((* NEW *)
   "WEAK_TRANS_cases1",
  ``!E u E1. WEAK_TRANS E u E1 ==> (?E'. TRANS E tau E' /\ WEAK_TRANS E' u E1) \/
                                   (?E'. TRANS E u E' /\ EPS E' E1)``,
    REPEAT STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS]))
 >> PAT_X_ASSUM ``TRANS E1' u E2`` MP_TAC
 >> PAT_X_ASSUM ``EPS E E1'`` MP_TAC
 >> Q.SPEC_TAC (`E1'`, `E1'`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_strongind (* must be strong *)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISJ2_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      DISJ1_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E1'`, `E2`] >> ASM_REWRITE_TAC [] ]);

(* The two possible cases for the 1st step in ``WEAK_TRANS _ (label _) _`` *)
val WEAK_TRANS_cases2 = store_thm ((* NEW *)
   "WEAK_TRANS_cases2",
  ``!E l E1. WEAK_TRANS E (label l) E1 ==> (?E'. TRANS E tau E' /\ WEAK_TRANS E' (label l) E1) \/
                                           (?E'. TRANS E (label l) E' /\ EPS E' E1)``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases1
 >| [ DISJ1_TAC >> Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],
      DISJ2_TAC >> Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] ]);

val WEAK_TRANS_TAU = store_thm ((* NEW *)
   "WEAK_TRANS_TAU",
  ``!E E1. WEAK_TRANS E tau E1 = ?E'. TRANS E tau E' /\ EPS E' E1``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      STRIP_TAC \\
      IMP_RES_TAC WEAK_TRANS_cases1 >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_TRANS_IMP_EPS \\
        ASM_REWRITE_TAC [],
        (* goal 1.2 (of 2) *)
        Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      REPEAT STRIP_TAC \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E`, `E'`] >> ASM_REWRITE_TAC [EPS_REFL] ]);

(* The weak version of RREFIX *)
val WEAK_PREFIX = store_thm ((* NEW *)
   "WEAK_PREFIX", ``!E u. WEAK_TRANS (prefix u E) u E``,
    rpt GEN_TAC
 >> MATCH_MP_TAC TRANS_IMP_WEAK_TRANS
 >> REWRITE_TAC [PREFIX]);

(* The weak version of SUM1 *)
val WEAK_SUM1 = store_thm ((* NEW *)
   "WEAK_SUM1", ``!E u E1 E'. WEAK_TRANS E u E1 ==> WEAK_TRANS (sum E E') u E1``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases1 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `E'`)) \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP ONE_TAU)) \\
      ASSUME_TAC (Q.SPEC `E1` EPS_REFL) \\
      IMP_RES_TAC EPS_WEAK_EPS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC SUM1 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `E'`)) \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E + E'`, `E''`] \\
      ASM_REWRITE_TAC [EPS_REFL] ]);

(* The weak version of SUM2 *)
val WEAK_SUM2 = store_thm ((* NEW *)
   "WEAK_SUM2", ``!E u E1 E'. WEAK_TRANS E u E1 ==> WEAK_TRANS (sum E' E) u E1``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_cases1 (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC SUM2 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `E'`)) \\
      POP_ASSUM (ASSUME_TAC o (MATCH_MP ONE_TAU)) \\
      ASSUME_TAC (Q.SPEC `E1` EPS_REFL) \\
      IMP_RES_TAC EPS_WEAK_EPS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC SUM2 \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `E'`)) \\
      REWRITE_TAC [WEAK_TRANS] \\
      take [`E' + E`, `E''`] \\
      ASM_REWRITE_TAC [EPS_REFL] ]);

(******************************************************************************)
(*                                                                            *)
(*                       Weak bisimulation relation                           *)
(*                                                                            *)
(******************************************************************************)

val WEAK_BISIM_def = Define
   `WEAK_BISIM (R :'a simulation) = WBISIM TRANS tau R`;

Theorem WEAK_BISIM :
    WEAK_BISIM (Wbsm: 'a simulation) =
    !E E'. Wbsm E E' ==>
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
                (?E2. WEAK_TRANS E' (label l) E2 /\ Wbsm E1 E2)) /\
         (!E2. TRANS E' (label l) E2 ==>
                (?E1. WEAK_TRANS E  (label l) E1 /\ Wbsm E1 E2))) /\
       (!E1. TRANS E  tau E1 ==> (?E2. EPS E' E2 /\ Wbsm E1 E2)) /\
       (!E2. TRANS E' tau E2 ==> (?E1. EPS E  E1 /\ Wbsm E1 E2))
Proof
    RW_TAC bool_ss [WEAK_BISIM_def, WBISIM_def, SYM EPS_ETS, SYM WEAK_TRANS_WTS]
 >> EQ_TAC >> RW_TAC std_ss []
 >- METIS_TAC [Action_distinct_label]
 >- METIS_TAC [Action_distinct_label]
 >- METIS_TAC []
 >- METIS_TAC []
 >- (Cases_on `l` >> fs [] >> METIS_TAC [])
 >- (Cases_on `l` >> fs [] >> METIS_TAC [])
 >- METIS_TAC []
 >> METIS_TAC []
QED

Theorem IDENTITY_WEAK_BISIM :
    WEAK_BISIM Id
Proof
    REWRITE_TAC [WEAK_BISIM_def, WBISIM_ID]
QED

Theorem CONVERSE_WEAK_BISIM :
    !Wbsm. WEAK_BISIM Wbsm ==> WEAK_BISIM (inv Wbsm)
Proof
    REWRITE_TAC [WEAK_BISIM_def, WBISIM_INV]
QED

(******************************************************************************)
(*                                                                            *)
(*    Some auxiliary results for proving that the composition of two weak     *)
(*    bisimulations is a weak bisimulation.                                   *)
(*                                                                            *)
(******************************************************************************)

(* Different formulation of case 1 in Milner's proof. *)
val EPS_TRANS_AUX = store_thm (
   "EPS_TRANS_AUX",
  ``!E E1. EPS E E1 ==>
        !Wbsm E'. WEAK_BISIM Wbsm /\ Wbsm E E' ==> ?E2. EPS E' E2 /\ Wbsm E1 E2``,
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REPEAT STRIP_TAC \\
      IMP_RES_TAC
        (CONJUNCT2
           (MATCH_MP (EQ_MP (SPEC_ALL WEAK_BISIM) (ASSUME ``WEAK_BISIM Wbsm``))
                     (ASSUME ``(Wbsm: 'a simulation) E E''``))) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      REPEAT STRIP_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [EPS_REFL],
      (* goal 3 (of 3) *)
      REPEAT STRIP_TAC \\
      STRIP_ASSUME_TAC
        (MATCH_MP (ASSUME ``!Wbsm E'. WEAK_BISIM Wbsm /\ Wbsm E E' ==>
                                      (?E2. EPS E' E2 /\ Wbsm E1 E2)``)
                  (CONJ (ASSUME ``WEAK_BISIM Wbsm``)
                        (ASSUME ``(Wbsm: 'a simulation) E E''``))) \\
      STRIP_ASSUME_TAC
        (MATCH_MP (ASSUME ``!Wbsm E''. WEAK_BISIM Wbsm /\ Wbsm E1 E'' ==>
                                       (?E2. EPS E'' E2 /\ Wbsm E' E2)``)
                  (CONJ (ASSUME ``WEAK_BISIM Wbsm``)
                        (ASSUME ``(Wbsm: 'a simulation) E1 E2``))) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC EPS_TRANS \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] ]);

(* Symmetric auxiliary result for EPS. *)
val INVERSE_REL = store_thm (
   "INVERSE_REL", ``!(R: 'a -> 'a -> bool) x y. (inv R) x y = R y x``,
    rpt STRIP_TAC >> REWRITE_TAC [inv_DEF]);

val EPS_TRANS_AUX_SYM = store_thm (
   "EPS_TRANS_AUX_SYM",
  ``!E' E1.
        EPS E' E1 ==>
         !Wbsm E. WEAK_BISIM Wbsm /\ Wbsm E E' ==> (?E2. EPS E E2 /\ Wbsm E2 E1)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC (GSYM INVERSE_REL)
 >> IMP_RES_TAC CONVERSE_WEAK_BISIM
 >> IMP_RES_TAC
       (Q.SPEC `inv Wbsm` (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E' E1``)))
 >> ASSUME_TAC
      (REWRITE_RULE [INVERSE_REL]
                    (ASSUME ``(inv (Wbsm :'a simulation)) E1 E2'``))
 >> Q.EXISTS_TAC `E2'` >> art []);

(* Auxiliary result for WEAK_TRANS. *)
val WEAK_TRANS_AUX = store_thm (
   "WEAK_TRANS_AUX",
  ``!E l E1. WEAK_TRANS E (label l) E1 ==>
        !Wbsm E'. WEAK_BISIM Wbsm /\ Wbsm E E' ==>
         (?E2. WEAK_TRANS E' (label l) E2 /\ Wbsm E1 E2)``,
    REPEAT STRIP_TAC
 >> STRIP_ASSUME_TAC (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E (label l) E1``))
 >> STRIP_ASSUME_TAC
       (MATCH_MP (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E E1'``))
                 (CONJ (ASSUME ``WEAK_BISIM Wbsm``)
                       (ASSUME ``(Wbsm: 'a simulation) E E'``)))
 >> IMP_RES_TAC
       (MATCH_MP (EQ_MP (SPEC_ALL WEAK_BISIM) (ASSUME ``WEAK_BISIM Wbsm``))
                 (ASSUME ``(Wbsm: 'a simulation) E1' E2'``))
 >> STRIP_ASSUME_TAC
       (MATCH_MP (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E2 E1``))
                 (CONJ (ASSUME ``WEAK_BISIM Wbsm``)
                       (ASSUME ``(Wbsm: 'a simulation) E2 E2''``)))
 >> ASSUME_TAC
       (MATCH_MP EPS_WEAK_EPS
                 (LIST_CONJ [ASSUME ``EPS E' E2'``,
                             ASSUME ``WEAK_TRANS E2' (label l) E2''``,
                             ASSUME ``EPS E2'' E2'''``]))
 >> EXISTS_TAC ``E2''' :'a CCS``
 >> ASM_REWRITE_TAC []);

(* Symmetric auxiliary result for WEAK_TRANS. *)
val WEAK_TRANS_AUX_SYM = store_thm (
   "WEAK_TRANS_AUX_SYM",
  ``!E' l E1.
        WEAK_TRANS E' (label l) E1 ==>
         !Wbsm E. WEAK_BISIM Wbsm /\ Wbsm E E' ==>
          (?E2. WEAK_TRANS E (label l) E2 /\ Wbsm E2 E1)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC (GSYM INVERSE_REL)
 >> IMP_RES_TAC CONVERSE_WEAK_BISIM
 >> IMP_RES_TAC
      (Q.SPEC `inv Wbsm`
              (MATCH_MP WEAK_TRANS_AUX (ASSUME ``WEAK_TRANS E' (label l) E1``)))
 >> ASSUME_TAC
      (REWRITE_RULE [INVERSE_REL]
                    (ASSUME ``(inv (Wbsm: 'a simulation)) E1 E2'``))
 >> EXISTS_TAC ``E2' :'a CCS`` >> art []);

(* The composition of two weak bisimulations is a weak bisimulation. *)
Theorem COMP_WEAK_BISIM :
    !Wbsm1 Wbsm2. WEAK_BISIM Wbsm1 /\ WEAK_BISIM Wbsm2 ==> WEAK_BISIM (Wbsm2 O Wbsm1)
Proof
    REWRITE_TAC [WEAK_BISIM_def, WBISIM_O]
QED

(* The union of two weak bisimulations is a weak bisimulation. *)
Theorem UNION_WEAK_BISIM :
    !Wbsm1 Wbsm2. WEAK_BISIM Wbsm1 /\ WEAK_BISIM Wbsm2 ==>
                  WEAK_BISIM (Wbsm1 RUNION Wbsm2)
Proof
    REWRITE_TAC [WEAK_BISIM_def, WBISIM_RUNION]
QED

(* Define the weak equivalence relation for CCS processes.

  Obsevations on new definition:
   1. WEAK_EQUIV_cases ==> WEAK_EQUIV_rules (by EQ_IMP_LR)
   2. WEAK_EQUIV_cases is the same as WEAK_PROPERTY_STAR
   3. WEAK_EQUIV_coind is new (the co-inductive principle)
 *)
CoInductive WEAK_EQUIV :
    !(E :'a CCS) (E' :'a CCS).
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               ?E2. WEAK_TRANS E' (label l) E2 /\ WEAK_EQUIV E1 E2) /\
         (!E2. TRANS E' (label l) E2 ==>
               ?E1. WEAK_TRANS E  (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
       (!E1. TRANS E  tau E1 ==> (?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2)) /\
       (!E2. TRANS E' tau E2 ==> (?E1. EPS E  E1 /\ WEAK_EQUIV E1 E2))
      ==> WEAK_EQUIV E E'
End

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Infix (NONASSOC, 450),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK (UTF8.chr 0x2248), BreakSpace (1,0)],
                   term_name = "WEAK_EQUIV" };

val _ = TeX_notation { hol = UTF8.chr 0x2248,
                       TeX = ("\\HOLTokenWeakEQ", 1) };

(* "Weak bisimilarity is a weak bisimulation" *)
val WEAK_EQUIV_IS_WEAK_BISIM = store_thm (
   "WEAK_EQUIV_IS_WEAK_BISIM", ``WEAK_BISIM WEAK_EQUIV``,
    PURE_ONCE_REWRITE_TAC [WEAK_BISIM]
 >> REPEAT GEN_TAC
 >> DISCH_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM WEAK_EQUIV_cases]
 >> ASM_REWRITE_TAC []);

(* Alternative definition of WEAK_EQUIV, similar with STRONG_EQUIV. *)
val WEAK_EQUIV = store_thm ((* NEW *)
   "WEAK_EQUIV",
  ``!E E'. WEAK_EQUIV E E' = ?Wbsm. Wbsm E E' /\ WEAK_BISIM Wbsm``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      EXISTS_TAC ``WEAK_EQUIV`` \\
      ASM_REWRITE_TAC [WEAK_EQUIV_IS_WEAK_BISIM],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`E'`, `E'`) \\
      Q.SPEC_TAC (`E`, `E`) \\
      HO_MATCH_MP_TAC WEAK_EQUIV_coind \\ (* co-induction used here! *)
      PROVE_TAC [WEAK_BISIM] ]);

Theorem WEAK_EQUIV_IS_WBISIM_REL :
    WEAK_EQUIV = WBISIM_REL TRANS tau
Proof
    RW_TAC std_ss [FUN_EQ_THM, WBISIM_REL_def, WEAK_EQUIV, WEAK_BISIM_def]
 >> EQ_TAC >> RW_TAC std_ss []
 >| [ Q.EXISTS_TAC `Wbsm` >> art [],
      Q.EXISTS_TAC `R` >> art [] ]
QED

Theorem WEAK_EQUIV_equivalence :
    equivalence WEAK_EQUIV
Proof
    REWRITE_TAC [WEAK_EQUIV_IS_WBISIM_REL, WBISIM_REL_IS_EQUIV_REL]
QED

Theorem WEAK_EQUIV_REFL :
    !E. WEAK_EQUIV E E
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, reflexive_def]
                            WEAK_EQUIV_equivalence]
QED

Theorem WEAK_EQUIV_SYM :
    !E E'. WEAK_EQUIV E E' ==> WEAK_EQUIV E' E
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, symmetric_def]
                            WEAK_EQUIV_equivalence]
QED

Theorem WEAK_EQUIV_TRANS :
    !E E' E''. WEAK_EQUIV E E' /\ WEAK_EQUIV E' E'' ==> WEAK_EQUIV E E''
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, transitive_def]
                            WEAK_EQUIV_equivalence]
QED

val WEAK_BISIM_SUBSET_WEAK_EQUIV = store_thm ((* NEW *)
   "WEAK_BISIM_SUBSET_WEAK_EQUIV",
  ``!Wbsm. WEAK_BISIM Wbsm ==> Wbsm RSUBSET WEAK_EQUIV``,
    PROVE_TAC [RSUBSET, WEAK_EQUIV]);

val WEAK_EQUIV_SYM' = store_thm ((* NEW *)
   "WEAK_EQUIV_SYM'",
  ``!E E'. WEAK_EQUIV E E' <=> WEAK_EQUIV E' E``,
    REPEAT STRIP_TAC
 >> EQ_TAC
 >> REWRITE_TAC [WEAK_EQUIV_SYM]);

(* Syntactic equivalence implies observation equivalence. *)
val EQUAL_IMP_WEAK_EQUIV = store_thm (
   "EQUAL_IMP_WEAK_EQUIV", ``!E E'. (E = E') ==> WEAK_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [WEAK_EQUIV_REFL]);

(* Observation equivalence satisfies the property [*] *)
val WEAK_PROPERTY_STAR = save_thm ((* NEW *)
   "WEAK_PROPERTY_STAR", WEAK_EQUIV_cases);

(* Half versions of WEAK_PROPERTY_STAR *)
val WEAK_EQUIV_TRANS_label = store_thm (
   "WEAK_EQUIV_TRANS_label",
  ``!E E'. WEAK_EQUIV E E' ==>
        !l E1. TRANS E (label l) E1 ==> ?E2. WEAK_TRANS E' (label l) E2 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [WEAK_PROPERTY_STAR]);

val WEAK_EQUIV_TRANS_label' = store_thm (
   "WEAK_EQUIV_TRANS_label'",
  ``!E E'. WEAK_EQUIV E E' ==>
        !l E2. TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [WEAK_PROPERTY_STAR]);

val WEAK_EQUIV_TRANS_tau = store_thm (
   "WEAK_EQUIV_TRANS_tau",
  ``!E E'. WEAK_EQUIV E E' ==> !E1. TRANS E tau E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [WEAK_PROPERTY_STAR]);

val WEAK_EQUIV_TRANS_tau' = store_thm (
   "WEAK_EQUIV_TRANS_tau'",
  ``!E E'. WEAK_EQUIV E E' ==> !E2. TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [WEAK_PROPERTY_STAR]);

(* Observation equivalence is substitutive under prefix operator. *)
val WEAK_EQUIV_SUBST_PREFIX = store_thm (
   "WEAK_EQUIV_SUBST_PREFIX",
  ``!E E'. WEAK_EQUIV E E' ==> !u. WEAK_EQUIV (prefix u E) (prefix u E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [SPECL [``prefix (u :'a Action) E``,
                                  ``prefix (u :'a Action) E'``] WEAK_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [WEAK_TRANS] \\
      EXISTS_TAC ``prefix (u :'a Action) E'`` \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [WEAK_TRANS] \\
      EXISTS_TAC ``prefix (u :'a Action) E`` \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [EPS_REFL, PREFIX],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC ONE_TAU >> ASM_REWRITE_TAC [PREFIX],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC ONE_TAU >> ASM_REWRITE_TAC [PREFIX] ]);

(* Definition of stable agent (tau-derivative do not exist). *)
val _ = hide "STABLE"; (* conflicted with sortingTheory *)

val STABLE = new_definition ("STABLE",
  ``STABLE (E :'a CCS) = (!u E'. TRANS E u E' ==> ~(u = tau))``);

(* Alternative definition using P, Q, p, q as process variables *)
val STABLE' = store_thm (
   "STABLE'", ``STABLE p = (!u p'. TRANS p u p' ==> ~(u = tau))``,
    PROVE_TAC [STABLE]);

val STABLE_NO_TRANS_TAU = store_thm (
   "STABLE_NO_TRANS_TAU", ``!E. STABLE E ==> !E'. ~(TRANS E tau E')``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [STABLE]
 >> RW_TAC std_ss []);

(* Every process is either stable or not *)
val STABLE_cases = store_thm (
   "STABLE_cases", ``!E. STABLE E \/ ~(STABLE E)``,
    PROVE_TAC [STABLE]);

(* Properties of stable agents with respect to the epsilon and weak transition
   relations. *)
Theorem EPS_STABLE :
    !E E'. EPS E E' ==> (STABLE E ==> (E' = E))
Proof
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [STABLE] >> DISCH_TAC \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE []
         (MATCH_MP (ASSUME ``!(u :'a Action) E'. TRANS E u E' ==> ~(u = tau)``)
                   (ASSUME ``TRANS E tau E'``))),
      (* goal 2 (of 3) *)
      REWRITE_TAC [],
      (* goal 3 (of 3) *)
      DISCH_TAC >> RES_TAC \\
      REWRITE_TAC
        [MATCH_MP (REWRITE_RULE [ASSUME ``E1 = E: 'a CCS``]
                                (ASSUME ``STABLE E1 ==> (E' = E1)``))
                  (ASSUME ``STABLE E``)] ]
QED

val EPS_STABLE' = store_thm (
   "EPS_STABLE'", ``!E E'. EPS E E' /\ STABLE E ==> (E' = E)``,
    PROVE_TAC [EPS_STABLE]);

val WEAK_TRANS_STABLE = store_thm (
   "WEAK_TRANS_STABLE",
  ``!E l E'. WEAK_TRANS E (label l) E' /\ STABLE E ==>
            (?E''. TRANS E (label l) E'' /\ EPS E'' E')``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> ASSUME_TAC
       (MATCH_MP
        (MATCH_MP EPS_STABLE (ASSUME ``EPS E E1``))
        (ASSUME ``STABLE E``))
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E1 = E: 'a CCS``]
                             (ASSUME ``TRANS E1 (label l) E2``))
 >> Q.EXISTS_TAC `E2`
 >> ASM_REWRITE_TAC []);

val STABLE_NO_WEAK_TRANS_TAU = store_thm (
   "STABLE_NO_WEAK_TRANS_TAU",
  ``!E. STABLE E ==> !E'. ~(WEAK_TRANS E tau E')``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``STABLE E`` (ASSUME_TAC o (REWRITE_RULE [STABLE]))
 >> IMP_RES_TAC WEAK_TRANS_cases1 (* 2 sub-goals here *)
 >> PROVE_TAC []);

(* Observation equivalence of stable agents is preserved by binary summation. *)
val WEAK_EQUIV_PRESD_BY_SUM = store_thm (
   "WEAK_EQUIV_PRESD_BY_SUM",
  ``!E1 E1' E2 E2'.
         WEAK_EQUIV E1 E1' /\ STABLE E1 /\ STABLE E1' /\
         WEAK_EQUIV E2 E2' /\ STABLE E2 /\ STABLE E2' ==>
         WEAK_EQUIV (sum E1 E2) (sum E1' E2')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E2''` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E1' E2'`` \\
        REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC (MATCH_MP WEAK_TRANS_STABLE
                                   (CONJ (ASSUME ``WEAK_TRANS E1' (label l) E2''``)
                                         (ASSUME ``STABLE E1'``))) \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 2 (of 4) *)
        RES_TAC >> Q.EXISTS_TAC `E2''` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E1' E2'`` \\
        REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC (MATCH_MP WEAK_TRANS_STABLE
                                   (CONJ (ASSUME ``WEAK_TRANS E2' (label l) E2''``)
                                         (ASSUME ``STABLE E2'``))) \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E1''` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E1 E2`` >> REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC (MATCH_MP WEAK_TRANS_STABLE
                                   (CONJ (ASSUME ``WEAK_TRANS E1 (label l) E1''``)
                                         (ASSUME ``STABLE E1``))) \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E1''` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E1 E2`` >> REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC (MATCH_MP WEAK_TRANS_STABLE
                                   (CONJ (ASSUME ``WEAK_TRANS E2 (label l) E1''``)
                                         (ASSUME ``STABLE E2``))) \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E1` STABLE) (ASSUME ``STABLE E1``))
                    (ASSUME ``TRANS E1 tau E1''``))),
        (* goal 3.2 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E2` STABLE) (ASSUME ``STABLE E2``))
                    (ASSUME ``TRANS E2 tau E1''``))) ],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E1'` STABLE) (ASSUME ``STABLE E1'``))
                    (ASSUME ``TRANS E1' tau E2''``))),
        (* goal 4.2 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E2'` STABLE) (ASSUME ``STABLE E2'``))
                    (ASSUME ``TRANS E2' tau E2''``))) ] ]);

(* Observation equivalence of stable agents is substitutive under binary
   summation on the right. *)
val WEAK_EQUIV_SUBST_SUM_R = store_thm (
   "WEAK_EQUIV_SUBST_SUM_R",
  ``!E E'. WEAK_EQUIV E E' /\ STABLE E /\ STABLE E' ==>
        !E''. WEAK_EQUIV (sum E E'') (sum E' E'')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E2` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E' E''`` \\
        REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC
          (MATCH_MP WEAK_TRANS_STABLE
                    (CONJ (ASSUME ``WEAK_TRANS E' (label l) E2``)
                          (ASSUME ``STABLE E'``))) \\
        Q.EXISTS_TAC `E'''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 1.2 (of 2) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [WEAK_EQUIV_REFL, WEAK_TRANS] \\
        EXISTS_TAC ``sum E' E''`` \\
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [EPS_REFL] \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `E1` \\
        ASM_REWRITE_TAC [WEAK_TRANS] \\
        EXISTS_TAC ``sum E E''`` \\
        REWRITE_TAC [EPS_REFL] \\
        STRIP_ASSUME_TAC
          (MATCH_MP WEAK_TRANS_STABLE
                    (CONJ (ASSUME ``WEAK_TRANS E (label l) E1``)
                          (ASSUME ``STABLE E``))) \\
        Q.EXISTS_TAC `E'''` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Q.EXISTS_TAC `E2` \\
        REWRITE_TAC [WEAK_EQUIV_REFL, WEAK_TRANS] \\
        EXISTS_TAC ``sum E E''`` \\
        Q.EXISTS_TAC `E2` \\
        REWRITE_TAC [EPS_REFL] \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E` STABLE) (ASSUME ``STABLE E``))
                    (ASSUME ``TRANS E tau E1``))),
        (* goal 3.2 (of 2) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [WEAK_EQUIV_REFL] \\
        PURE_ONCE_REWRITE_TAC [EPS_cases] \\
        DISJ1_TAC \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >|
      [ (* goal 4.1 (of 2) *)
        CHECK_ASSUME_TAC
         (REWRITE_RULE []
          (MATCH_MP (EQ_MP (Q.SPEC `E'` STABLE) (ASSUME ``STABLE E'``))
                    (ASSUME ``TRANS E' tau E2``))),
        (* goal 4.2 (of 2) *)
        Q.EXISTS_TAC `E2` \\
        REWRITE_TAC [WEAK_EQUIV_REFL] \\
        PURE_ONCE_REWRITE_TAC [EPS_cases] \\
        DISJ1_TAC \\
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ] ]);

(* Observation equivalence is substitutive under guarded binary summation *)
val WEAK_EQUIV_PRESD_BY_GUARDED_SUM = store_thm (
   "WEAK_EQUIV_PRESD_BY_GUARDED_SUM",
  ``!E1 E1' E2 E2' a1 a2.
        WEAK_EQUIV E1 E1' /\ WEAK_EQUIV E2 E2' ==>
        WEAK_EQUIV (sum (prefix a1 E1) (prefix a2 E2))
                   (sum (prefix a1 E1') (prefix a2 E2'))``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [WEAK_PROPERTY_STAR]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM1 \\
        MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
        REWRITE_TAC [PREFIX],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM2 \\
        MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
        REWRITE_TAC [PREFIX] ],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM1 \\
        MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
        REWRITE_TAC [PREFIX],
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC WEAK_SUM2 \\
        MATCH_MP_TAC TRANS_IMP_WEAK_TRANS \\
        REWRITE_TAC [PREFIX] ],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        qpat_x_assum `tau = a1` (ASSUME_TAC o SYM) \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        qpat_x_assum `tau = a2` (ASSUME_TAC o SYM) \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        qpat_x_assum `tau = a1` (ASSUME_TAC o SYM) \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        qpat_x_assum `tau = a2` (ASSUME_TAC o SYM) \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ] ]);

(* The epsilon relation is preserved by the parallel operator. *)
val EPS_PAR = store_thm ("EPS_PAR",
  ``!E E'. EPS E E' ==>
        !E''. EPS (par E E'') (par E' E'') /\ EPS (par E'' E) (par E'' E')``,
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      GEN_TAC \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC PAR1 \\
        ASSUME_TAC
         (Q.SPEC `E''`
                 (ASSUME ``!E''. TRANS (par E E'') tau (par E' E'')``)) \\
        IMP_RES_TAC ONE_TAU,
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC PAR2 \\
        ASSUME_TAC
         (Q.SPEC `E''`
                 (ASSUME ``!E''. TRANS (par E'' E) tau (par E'' E')``)) \\
        IMP_RES_TAC ONE_TAU ],
      (* goal 2 (of 3) *)
      REWRITE_TAC [EPS_REFL],
      (* goal 3 (of 3) *)
      GEN_TAC \\
      CONJUNCTS_THEN ASSUME_TAC
        (Q.SPEC `E''`
                (ASSUME ``!E''. EPS (par E E'') (par E1 E'') /\
                                EPS (par E'' E) (par E'' E1)``)) \\
      CONJUNCTS_THEN ASSUME_TAC
        (Q.SPEC `E''`
                (ASSUME ``!E''. EPS (par E1 E'') (par E' E'') /\
                                EPS (par E'' E1) (par E'' E')``)) \\
      IMP_RES_TAC EPS_TRANS \\
      ASM_REWRITE_TAC [] ]);

val EPS_PAR_PAR = store_thm (
   "EPS_PAR_PAR",
  ``!E1 E2 F1 F2.
        EPS E1 E2 /\ EPS F1 F2 ==> EPS (par E1 F1) (par E2 F2)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC EPS_TRANS
 >> EXISTS_TAC ``par E2 F1``
 >> IMP_RES_TAC EPS_PAR
 >> ASM_REWRITE_TAC []);

(* The relation WEAK_TRANS is preserved by the parallel operator. *)
val WEAK_PAR = store_thm ("WEAK_PAR",
  ``!E u E'. WEAK_TRANS E u E' ==>
        !E''. WEAK_TRANS (par E E'') u (par E' E'') /\
              WEAK_TRANS (par E'' E) u (par E'' E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC EPS_PAR \\
      EXISTS_TAC ``par E1 E''`` \\
      EXISTS_TAC ``par E2 E''`` \\
      ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC EPS_PAR \\
      EXISTS_TAC ``par E'' E1`` \\
      EXISTS_TAC ``par E'' E2`` \\
      ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ]);

(* Observation equivalence is preserved by parallel operator. *)
val WEAK_EQUIV_PRESD_BY_PAR = store_thm (
   "WEAK_EQUIV_PRESD_BY_PAR",
  ``!E1 E1' E2 E2'.
        WEAK_EQUIV E1 E1' /\ WEAK_EQUIV E2 E2' ==>
        WEAK_EQUIV (par E1 E2) (par E1' E2')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_EQUIV]
 >> EXISTS_TAC ``\x y.
                   (?F1 F1' F2 F2'.
                    (x = par F1 F2) /\ (y = par F1' F2') /\
                    WEAK_EQUIV F1 F1' /\ WEAK_EQUIV F2 F2')``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E1`, `E1'`, `E2`, `E2'`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [WEAK_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
                                 (ASSUME ``TRANS E (label l) E1''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 1.1 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          EXISTS_TAC ``par E2'' F2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 1.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
            (* goal 1.1.2 (of 2) *)
            take [`E1'''`, `E2''`, `F2`, `F2'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 1.2 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par F1' E2''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 1.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
            (* goal 1.2.2 (of 2) *)
            take [`F1`, `F1'`, `E1'''`, `E2''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 1.3 (of 3) *)
          IMP_RES_TAC Action_distinct_label ],
        (* goal 2 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par F1' F2'``]
                                 (ASSUME ``TRANS E' (label l) E2''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 2.1 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          EXISTS_TAC ``par E1''' F2`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
            (* goal 2.1.2 (of 2) *)
            take [`E1'''`, `E1''`, `F2`, `F2'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.2 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par F1 E1'''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC WEAK_PAR >> ASM_REWRITE_TAC [],
            (* goal 2.2.2 (of 2) *)
            take [`F1`, `F1'`, `E1'''`, `E1''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.3 (of 3) *)
          IMP_RES_TAC Action_distinct_label ],
        (* goal 3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F2``]
                                 (ASSUME ``TRANS E tau E1''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 3.1 (of 3) *)
          IMP_RES_TAC
              (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          EXISTS_TAC ``par E2'' F2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 3.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC EPS_PAR \\ ASM_REWRITE_TAC [],
            (* goal 3.1.2 (of 2) *)
            take [`E1'''`, `E2''`, `F2`, `F2'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 3.2 (of 3) *)
          IMP_RES_TAC
              (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par F1' E2''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 3.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            IMP_RES_TAC EPS_PAR >> ASM_REWRITE_TAC [],
            (* goal 3.2.2 (of 2) *)
            take [`F1`, `F1'`, `E1'''`, `E2''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 3.3 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par E2''' E2''''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 3.3.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC EPS_TRANS \\
            STRIP_ASSUME_TAC
                (REWRITE_RULE [WEAK_TRANS]
                              (ASSUME ``WEAK_TRANS F1' (label l) E2'''``)) \\
            STRIP_ASSUME_TAC
                (REWRITE_RULE [WEAK_TRANS]
                              (ASSUME ``WEAK_TRANS F2' (label (COMPL l)) E2''''``)) \\
            EXISTS_TAC ``par E1'''' E1'''''`` \\
            REWRITE_TAC [MATCH_MP EPS_PAR_PAR
                                  (CONJ (ASSUME ``EPS F1' E1''''``)
                                        (ASSUME ``EPS F2' E1'''''``))] \\
            MATCH_MP_TAC EPS_TRANS \\
            EXISTS_TAC ``par E2''''' E2''''''`` \\
            REWRITE_TAC [MATCH_MP EPS_PAR_PAR
                                  (CONJ (ASSUME ``EPS E2''''' E2'''``)
                                        (ASSUME ``EPS E2'''''' E2''''``))] \\
            MATCH_MP_TAC ONE_TAU \\
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``l :'a Label`` \\
            ASM_REWRITE_TAC [],
            (* goal 3.3.2 (of 2) *)
            take [`E1'''`, `E2'''`, `E2''`, `E2''''`] \\
            ASM_REWRITE_TAC [] ] ],
        (* goal 4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par F1' F2'``]
                                 (ASSUME ``TRANS E' tau E2''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 4.1 (of 3) *)
          IMP_RES_TAC (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          EXISTS_TAC ``par E1''' F2`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 4.1.1 (of 2) *)
            IMP_RES_TAC EPS_PAR >> ASM_REWRITE_TAC [],
            (* goal 4.1.2 (of 2) *)
            take [`E1'''`, `E1''`, `F2`, `F2'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 4.2 (of 3) *)
          IMP_RES_TAC (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par F1 E1'''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 4.2.1 (of 2) *)
            IMP_RES_TAC EPS_PAR >> ASM_REWRITE_TAC [],
            (* goal 4.2.2 (of 2) *)
            take [`F1`, `F1'`, `E1'''`, `E1''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 4.3 (of 3) *)
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F1 F1'``))) \\
          IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                    (ASSUME ``WEAK_EQUIV F2 F2'``))) \\
          EXISTS_TAC ``par E1''' E1''''`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 4.3.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC EPS_TRANS \\
            STRIP_ASSUME_TAC
                (REWRITE_RULE [WEAK_TRANS]
                              (ASSUME ``WEAK_TRANS F1 (label l) E1'''``)) \\
            STRIP_ASSUME_TAC
                (REWRITE_RULE [WEAK_TRANS]
                              (ASSUME ``WEAK_TRANS F2 (label (COMPL l)) E1''''``)) \\
            EXISTS_TAC ``par E1''''' E1''''''`` \\
            REWRITE_TAC [MATCH_MP EPS_PAR_PAR
                                  (CONJ (ASSUME ``EPS F1 E1'''''``)
                                        (ASSUME ``EPS F2 E1''''''``))] \\
            MATCH_MP_TAC EPS_TRANS \\
            EXISTS_TAC ``par E2'''' E2'''''`` \\
            REWRITE_TAC [MATCH_MP EPS_PAR_PAR
                                  (CONJ (ASSUME ``EPS E2'''' E1'''``)
                                        (ASSUME ``EPS E2''''' E1''''``))] \\
            MATCH_MP_TAC ONE_TAU \\
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``l :'a Label`` \\
            ASM_REWRITE_TAC [],
            (* goal 4.3.2 (of 2) *)
            take [`E1'''`, `E1''`, `E1''''`, `E2'''`] \\
            ASM_REWRITE_TAC [] ] ] ] ]);

(* Observation equivalence is substitutive under parallel operator on the right:
   !E E'. WEAK_EQUIV E E' ==> !E''. WEAK_EQUIV (E || E'') (E' || E'')
 *)
val WEAK_EQUIV_SUBST_PAR_R = save_thm (
   "WEAK_EQUIV_SUBST_PAR_R",
    Q.GENL [`E`, `E'`]
      (DISCH ``WEAK_EQUIV E E'``
        (Q.GEN `E''`
           (MATCH_MP WEAK_EQUIV_PRESD_BY_PAR
                     (CONJ (ASSUME ``WEAK_EQUIV E E'``)
                           (Q.SPEC `E''` WEAK_EQUIV_REFL))))));

(* Observation equivalence is substitutive under parallel operator on the left:k
   !E E'. WEAK_EQUIV E E' ==> !E''. WEAK_EQUIV (E'' || E) (E'' || E')
 *)
val WEAK_EQUIV_SUBST_PAR_L = save_thm (
   "WEAK_EQUIV_SUBST_PAR_L",
    Q.GENL [`E`, `E'`]
      (DISCH ``WEAK_EQUIV E E'``
        (Q.GEN `E''`
           (MATCH_MP WEAK_EQUIV_PRESD_BY_PAR
                     (CONJ (Q.SPEC `E''` WEAK_EQUIV_REFL)
                           (ASSUME ``WEAK_EQUIV E E'``))))));

(* The epsilon relation is preserved by the restriction operator. *)
val EPS_RESTR = store_thm (
   "EPS_RESTR",
  ``!E E'. EPS E E' ==> !L. EPS (restr L E) (restr L E')``,
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      GEN_TAC \\
      IMP_RES_TAC
        (REWRITE_RULE [] (Q.SPECL [`E`, `tau`, `E'`] RESTR)) \\
      ASSUME_TAC
        (Q.SPEC `L` (ASSUME ``!L :'a Label set.
                                TRANS (restr L E) tau (restr L E')``)) \\
      IMP_RES_TAC ONE_TAU,
      (* goal 2 (of 3) *)
      REWRITE_TAC [EPS_REFL],
      (* goal 3 (of 3) *)
      GEN_TAC \\
      ASSUME_TAC
        (Q.SPEC `L` (ASSUME ``!L :'a Label set. EPS (restr L E) (restr L E1)``)) \\
      ASSUME_TAC
        (Q.SPEC `L` (ASSUME ``!L :'a Label set. EPS (restr L E1) (restr L E')``)) \\
      IMP_RES_TAC EPS_TRANS ]);

(* The relation WEAK_TRANS is preserved by the restriction operator. *)
val WEAK_RESTR_label = store_thm (
   "WEAK_RESTR_label",
      ``!(l :'a Label) L E E'.
         ~(l IN L) /\ ~((COMPL l) IN L) /\ WEAK_TRANS E (label l) E' ==>
          WEAK_TRANS (restr L E) (label l) (restr L E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> EXISTS_TAC ``restr (L :'a Label set) E1``
 >> EXISTS_TAC ``restr (L :'a Label set) E2``
 >> IMP_RES_TAC EPS_RESTR
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC RESTR
 >> EXISTS_TAC ``l :'a Label``
 >> ASM_REWRITE_TAC []);

val WEAK_RESTR_tau = store_thm (
   "WEAK_RESTR_tau",
 ``!E E'. WEAK_TRANS E tau E' ==>
         !L. WEAK_TRANS (restr L E) tau (restr L E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> STRIP_TAC
 >> GEN_TAC
 >> EXISTS_TAC ``restr (L :'a Label set) E1``
 >> EXISTS_TAC ``restr (L :'a Label set) E2``
 >> IMP_RES_TAC EPS_RESTR
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC RESTR
 >> ASM_REWRITE_TAC []);

(* Observation equivalence is substitutive under restriction operator. *)
val WEAK_EQUIV_SUBST_RESTR = store_thm (
   "WEAK_EQUIV_SUBST_RESTR",
  ``!E E'. WEAK_EQUIV E E' ==> !L. WEAK_EQUIV (restr L E) (restr L E')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 L'. (x = restr L' E1) /\ (y = restr L' E2) /\
                                  WEAK_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `L`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [WEAK_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                                 (ASSUME ``TRANS E'' (label l) E1'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          IMP_RES_TAC Action_distinct_label,
          (* goal 2.1.2 (of 2) *)
          IMP_RES_TAC
              (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV E1 E2``))) \\
          EXISTS_TAC ``restr (L' :'a Label set) E2'`` \\
          ASM_REWRITE_TAC
            [MATCH_MP WEAK_RESTR_label
                      (LIST_CONJ [ASSUME ``~((l' :'a Label) IN L')``,
                                  ASSUME ``~((COMPL (l' :'a Label)) IN L')``,
                                  REWRITE_RULE [ASSUME ``label (l :'a Label) = label l'``]
                                               (ASSUME ``WEAK_TRANS E2 (label l) E2'``)])] \\
          take [`E''''`, `E2'`, `L'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
                                 (ASSUME ``TRANS E''' (label l) E2'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          IMP_RES_TAC Action_distinct_label,
          (* goal 2.2.2 (of 2) *)
          IMP_RES_TAC
              (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV E1 E2``))) \\
          EXISTS_TAC ``restr (L' :'a Label set) E1'`` \\
          ASM_REWRITE_TAC
            [MATCH_MP WEAK_RESTR_label
                      (LIST_CONJ [ASSUME ``~((l' :'a Label) IN L')``,
                                  ASSUME ``~((COMPL (l' :'a Label)) IN L')``,
                                  REWRITE_RULE [ASSUME ``label (l :'a Label) = label l'``]
                                               (ASSUME ``WEAK_TRANS E1 (label l) E1'``)])] \\
          take [`E1'`, `E''''`, `L'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                                 (ASSUME ``TRANS E'' tau E1'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.3.1 (of 2) *)
          IMP_RES_TAC
              (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV E1 E2``))) \\
          EXISTS_TAC ``restr (L' :'a Label set) E2'`` \\
          IMP_RES_TAC EPS_RESTR >> ASM_REWRITE_TAC [] \\
          take [`E''''`, `E2'`, `L'`] >> ASM_REWRITE_TAC [],
          (* goal 2.3.2 (of 2) *)
          IMP_RES_TAC Action_distinct ],
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
                                 (ASSUME ``TRANS E''' tau E2'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.4.1 (of 2) *)
          IMP_RES_TAC
              (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                            (ASSUME ``WEAK_EQUIV E1 E2``))) \\
          EXISTS_TAC ``restr (L' :'a Label set) E1'`` \\
          IMP_RES_TAC EPS_RESTR >> ASM_REWRITE_TAC [] \\
          take [`E1'`, `E''''`, `L'`] >> ASM_REWRITE_TAC [],
          (* goal 2.4.2 (of 2) *)
          IMP_RES_TAC Action_distinct ] ] ]);

(* The epsilon relation is preserved by the relabelling operator. *)
val EPS_RELAB = store_thm ("EPS_RELAB",
  ``!E E'. EPS E E' ==>
           !labl. EPS (relab E (RELAB labl)) (relab E' (RELAB labl))``,
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      GEN_TAC \\
      IMP_RES_TAC
        (REWRITE_RULE [relabel_def]
                      (Q.SPECL [`E`, `tau`, `E'`] RELABELING)) \\
      ASSUME_TAC
        (SPEC ``RELAB (labl :('a Label # 'a Label) list)``
         (ASSUME ``!rf :'a Relabeling.
                   TRANS (relab E rf) tau (relab E' rf)``)) \\
      IMP_RES_TAC ONE_TAU,
      (* goal 2 (of 3) *)
      REWRITE_TAC [EPS_REFL],
      (* goal 3 (of 3) *)
      GEN_TAC \\
      PAT_X_ASSUM ``!labl :('a Label # 'a Label) list.
                     EPS (relab E (RELAB labl)) (relab E1 (RELAB labl))``
                  (ASSUME_TAC o (SPEC ``labl :('a Label # 'a Label) list``)) \\
      PAT_X_ASSUM ``!labl :('a Label # 'a Label) list.
                     EPS (relab E1 (RELAB labl)) (relab E' (RELAB labl))``
                  (ASSUME_TAC o (SPEC ``labl :('a Label # 'a Label) list``)) \\
      IMP_RES_TAC EPS_TRANS ]);

val EPS_RELAB_rf = store_thm (
   "EPS_RELAB_rf",
  ``!E E'. EPS E E' ==> !(rf :'a Relabeling). EPS (relab E rf) (relab E' rf)``,
    EPS_INDUCT_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      GEN_TAC \\
      IMP_RES_TAC
        (REWRITE_RULE [relabel_def]
                      (Q.SPECL [`E`, `tau`, `E'`] RELABELING)) \\
      ASSUME_TAC
        (Q.SPEC `rf`
         (ASSUME ``!rf :'a Relabeling.
                   TRANS (relab E rf) tau (relab E' rf)``)) \\
      IMP_RES_TAC ONE_TAU,
      (* goal 2 (of 3) *)
      REWRITE_TAC [EPS_REFL],
      (* goal 3 (of 3) *)
      GEN_TAC \\
      PAT_X_ASSUM ``!rf :'a Relabeling. EPS (relab E rf) (relab E1 rf)``
                  (ASSUME_TAC o (Q.SPEC `rf`)) \\
      PAT_X_ASSUM ``!rf :'a Relabeling. EPS (relab E1 rf) (relab E' rf)``
                  (ASSUME_TAC o (Q.SPEC `rf`)) \\
      IMP_RES_TAC EPS_TRANS ]);

(* The relation WEAK_TRANS is preserved by the relabelling operator. *)
val WEAK_RELAB = store_thm ("WEAK_RELAB",
  ``!E u E'.
       WEAK_TRANS E u E' ==>
        !(labl :('a Label # 'a Label) list).
          WEAK_TRANS (relab E (RELAB labl))
                     (relabel (RELAB labl) u)
                     (relab E' (RELAB labl))``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EPS_RELAB
 >> EXISTS_TAC ``relab E1 (RELAB labl)``
 >> EXISTS_TAC ``relab E2 (RELAB labl)``
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC RELABELING
 >> ASM_REWRITE_TAC []);

val WEAK_RELAB_rf = store_thm (
   "WEAK_RELAB_rf",
  ``!E u E'.
       WEAK_TRANS E u E' ==>
        !(rf :'a Relabeling). WEAK_TRANS (relab E rf) (relabel rf u) (relab E' rf)``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EPS_RELAB_rf
 >> EXISTS_TAC ``relab E1 rf``
 >> EXISTS_TAC ``relab E2 rf``
 >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC RELABELING
 >> ASM_REWRITE_TAC []);

(* Observation equivalence is substitutive under relabelling operator. *)
val WEAK_EQUIV_SUBST_RELAB = store_thm (
   "WEAK_EQUIV_SUBST_RELAB",
  ``!E E'. WEAK_EQUIV E E' ==> !rf. WEAK_EQUIV (relab E rf) (relab E' rf)``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\
                                   WEAK_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `rf`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [WEAK_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                                 (ASSUME ``TRANS E'' (label l) E1'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        PAT_X_ASSUM ``label (l :'a Label) = relabel rf' u'`` (ASSUME_TAC o SYM) \\
        IMP_RES_TAC Relab_label \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = label l'``]
                                 (ASSUME ``TRANS E1 u' E''''``)) \\
        IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                  (ASSUME ``WEAK_EQUIV E1 E2``))) \\
        EXISTS_TAC ``relab E2' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_RELAB_rf \\
          PROVE_TAC [],
          (* goal 2.1.2 (of 2) *)
          take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                                 (ASSUME ``TRANS E''' (label l) E2'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        PAT_X_ASSUM ``label (l :'a Label) = relabel rf' u'`` (ASSUME_TAC o SYM) \\
        IMP_RES_TAC Relab_label \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = label l'``]
                                 (ASSUME ``TRANS E2 u' E''''``)) \\
        IMP_RES_TAC (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                  (ASSUME ``WEAK_EQUIV E1 E2``))) \\
        EXISTS_TAC ``relab E1' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WEAK_RELAB_rf \\
          PROVE_TAC [],
          (* goal 2.2.2 (of 2) *)
          take [`E1'`, `E''''`, `rf'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                                 (ASSUME ``TRANS E'' tau E1'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        PAT_X_ASSUM ``(tau :'a Action) = relabel rf' u'`` (ASSUME_TAC o SYM) \\
        IMP_RES_TAC Relab_tau \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = tau``]
                                 (ASSUME ``TRANS E1 u' E''''``)) \\
        IMP_RES_TAC (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                  (ASSUME ``WEAK_EQUIV E1 E2``))) \\
        EXISTS_TAC ``relab E2' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.3.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC EPS_RELAB_rf \\
          ASM_REWRITE_TAC [],
          (* goal 2.3.2 (of 2) *)
          take [`E''''`, `E2'`, `rf'`] >> ASM_REWRITE_TAC [] ],
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                                 (ASSUME ``TRANS E''' tau E2'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        PAT_X_ASSUM ``(tau :'a Action) = relabel rf' u'`` (ASSUME_TAC o SYM) \\
        IMP_RES_TAC Relab_tau \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``(u' :'a Action) = tau``]
                                 (ASSUME ``TRANS E2 u' E''''``)) \\
        IMP_RES_TAC (CONJUNCT2 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                                  (ASSUME ``WEAK_EQUIV E1 E2``))) \\
        EXISTS_TAC ``relab E1' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.4.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          IMP_RES_TAC EPS_RELAB_rf \\
          ASM_REWRITE_TAC [],
          (* goal 2.4.2 (of 2) *)
          take [`E1'`, `E''''`, `rf'`] \\
          ASM_REWRITE_TAC [] ] ] ]);

(******************************************************************************)
(*                                                                            *)
(*        Relationship between strong bisimulation (strong equiv.)            *)
(*           and weak bisimulation (observation equivalence)                  *)
(*                                                                            *)
(******************************************************************************)

(* A strong bisimulation is a particular weak bisimulation. *)
Theorem STRONG_IMP_WEAK_BISIM :
    !Bsm. STRONG_BISIM Bsm ==> WEAK_BISIM Bsm
Proof
    REWRITE_TAC [STRONG_BISIM_def, WEAK_BISIM_def, BISIM_IMP_WBISIM]
QED

(* Strong equivalence implies weak/observation equivalence. *)
Theorem STRONG_IMP_WEAK_EQUIV :
    !E E'. STRONG_EQUIV E E' ==> WEAK_EQUIV E E'
Proof
    REWRITE_TAC [STRONG_EQUIV_def, WEAK_EQUIV_IS_WBISIM_REL,
                 BISIM_REL_IMP_WBISIM_REL]
QED

(******************************************************************************)
(*                                                                            *)
(*   Alternative half-definitions of WEAK_EQUIV using all WEAK_TRANS and EPS  *)
(*                                                                            *)
(******************************************************************************)

(* `EPS E E1` implies zero or more tau transitions, and this leads to
   zero or at least one tau transition on the other side, which implies
   `EPS E' E2` in any case.

    (Base case)    |     (Induct case)
 ==========================================
    !E  ~~ !E'     |    !E  ~~     !E'
     |       |     |    ||       ||   ||
     =       =     |    eps      eps  ||
     |       |     |    ||       ||   ||
     E  ~~  ?E'    |    \/       \/   ||
                   |    E1  ~~   ?E2  eps
                   |    |        ||   ||
                   |    tau      eps  ||
                   |    |        ||   ||
                   |    \/       \/   \/
                   |    E1'  ~~    ?E2'
 *)
val WEAK_EQUIV_EPS = store_thm ((* NEW *)
   "WEAK_EQUIV_EPS",
  ``!E E'. WEAK_EQUIV E E' ==>
           !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``WEAK_EQUIV E E'`` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E'` \\
      RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                     (ASSUME ``WEAK_EQUIV E1 E2``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_TRANS ]);

val WEAK_EQUIV_EPS' = store_thm ((* NEW *)
   "WEAK_EQUIV_EPS'",
  ``!E E'. WEAK_EQUIV E E' ==>
           !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP WEAK_EQUIV_SYM))
 >> IMP_RES_TAC WEAK_EQUIV_EPS
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC WEAK_EQUIV_SYM);

val WEAK_EQUIV_WEAK_TRANS_label = store_thm ((* NEW *)
   "WEAK_EQUIV_WEAK_TRANS_label",
  ``!E E'. WEAK_EQUIV E E' ==>
           !l E1. WEAK_TRANS E (label l) E1 ==> ?E2. WEAK_TRANS E' (label l) E2 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP WEAK_EQUIV_EPS (* lemma 1 used here *)
                          (ASSUME ``WEAK_EQUIV E E'``))
 >> IMP_RES_TAC (CONJUNCT1
                     (PURE_ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                             (ASSUME ``WEAK_EQUIV E1' E2'``)))
 >> IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
                              (Q.SPECL [`WEAK_EQUIV`, `E2''`]
                                       (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E2 E1``))))
 >> Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EPS_WEAK_EPS);

val WEAK_EQUIV_WEAK_TRANS_label' = store_thm ((* NEW *)
   "WEAK_EQUIV_WEAK_TRANS_label'",
  ``!E E'. WEAK_EQUIV E E' ==>
           !l E2. WEAK_TRANS E' (label l) E2 ==> ?E1. WEAK_TRANS E (label l) E1 /\ WEAK_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP WEAK_EQUIV_SYM))
 >> IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_label
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC WEAK_EQUIV_SYM);

val WEAK_EQUIV_WEAK_TRANS_tau = store_thm ((* NEW *)
   "WEAK_EQUIV_WEAK_TRANS_tau",
  ``!E E'. WEAK_EQUIV E E' ==>
           !E1. WEAK_TRANS E tau E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS_TAU_IMP_TRANS_TAU
 >> IMP_RES_TAC (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR] (ASSUME ``WEAK_EQUIV E E'``))
 >> IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
                              (Q.SPECL [`WEAK_EQUIV`, `E2`]
                                       (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E1' E1``))))
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC EPS_TRANS);

val WEAK_EQUIV_WEAK_TRANS_tau' = store_thm ((* NEW *)
   "WEAK_EQUIV_WEAK_TRANS_tau'",
  ``!E E'. WEAK_EQUIV E E' ==>
           !E2. WEAK_TRANS E' tau E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP WEAK_EQUIV_SYM))
 >> IMP_RES_TAC WEAK_EQUIV_WEAK_TRANS_tau
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC WEAK_EQUIV_SYM);

(* A similar results for STRONG_EQUIV, needed sometimes *)
val STRONG_EQUIV_EPS = store_thm ((* NEW *)
   "STRONG_EQUIV_EPS",
  ``!E E'. STRONG_EQUIV E E' ==>
           !E1. EPS E E1 ==> ?E2. EPS E' E2 /\ STRONG_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> PAT_X_ASSUM ``STRONG_EQUIV E E'`` MP_TAC
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`E1`, `E1`)
 >> Q.SPEC_TAC (`E`, `E`)
 >> HO_MATCH_MP_TAC EPS_ind_right (* must use right induct here! *)
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E'` \\
      RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LEFT
                            (ASSUME ``STRONG_EQUIV E1 E2``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC ONE_TAU \\
      IMP_RES_TAC EPS_TRANS ]);

val STRONG_EQUIV_EPS' = store_thm ((* NEW *)
   "STRONG_EQUIV_EPS'",
  ``!E E'. STRONG_EQUIV E E' ==>
           !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ STRONG_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP STRONG_EQUIV_SYM))
 >> IMP_RES_TAC STRONG_EQUIV_EPS
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC STRONG_EQUIV_SYM);

val STRONG_EQUIV_WEAK_TRANS = store_thm ((* NEW *)
   "STRONG_EQUIV_WEAK_TRANS",
  ``!E E'. STRONG_EQUIV E E' ==>
           !u E1. WEAK_TRANS E u E1 ==> ?E2. WEAK_TRANS E' u E2 /\ STRONG_EQUIV E1 E2``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC WEAK_TRANS
 >> IMP_RES_TAC (MATCH_MP STRONG_EQUIV_EPS (* lemma 1 used here *)
                          (ASSUME ``STRONG_EQUIV E E'``))
 >> IMP_RES_TAC PROPERTY_STAR_LEFT
 >> POP_ASSUM K_TAC
 >> IMP_RES_TAC (MATCH_MP STRONG_EQUIV_EPS (* lemma 1 used here *)
                          (ASSUME ``STRONG_EQUIV E2 E2''``))
 >> Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [WEAK_TRANS]
 >> take [`E2'`, `E2''`] >> ASM_REWRITE_TAC []);

val STRONG_EQUIV_WEAK_TRANS' = store_thm ((* NEW *)
   "STRONG_EQUIV_WEAK_TRANS'",
  ``!E E'. STRONG_EQUIV E E' ==>
           !u E2. WEAK_TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ STRONG_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP STRONG_EQUIV_SYM))
 >> IMP_RES_TAC STRONG_EQUIV_WEAK_TRANS
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC STRONG_EQUIV_SYM);

val _ = export_theory ();
val _ = html_theory "WeakEQ";
