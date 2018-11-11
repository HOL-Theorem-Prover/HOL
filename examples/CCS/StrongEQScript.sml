(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory relationTheory listTheory;
open CCSLib CCSTheory;

val _ = new_theory "StrongEQ";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*    Operational definition of strong equivalence for CCS (strong_sem.ml)    *)
(*                                                                            *)
(******************************************************************************)

(* Type abbreviations *)
val _ = type_abbrev_pp ("simulation", “:('a, 'b) CCS -> ('a, 'b) CCS -> bool”);

(* Use LIST_REL to build list_simulation from simulation, e.g. `LIST_REL STRONG_EQUIV` *)
val _ = type_abbrev ("list_simulation",
                    ``:('a, 'b) CCS list -> ('a, 'b) CCS list -> bool``);

val STRONG_SIM_def = Define
   `STRONG_SIM (R :('a, 'b) simulation) =
    !E E'. R E E' ==> !u E1. TRANS E u E1 ==> ?E2. TRANS E' u E2 /\ R E1 E2`;

val STRONG_BISIM_def = Define
   `STRONG_BISIM (R :('a, 'b) simulation) = STRONG_SIM R /\ STRONG_SIM (inv R)`;

val STRONG_BISIM = store_thm ("STRONG_BISIM",
  ``STRONG_BISIM (Bsm :('a, 'b) simulation) =
    !E E'. Bsm E E' ==>
        !u.
           (!E1. TRANS E u E1 ==>
                 ?E2. TRANS E' u E2 /\ Bsm E1 E2) /\
           (!E2. TRANS E' u E2 ==>
                 ?E1. TRANS E u E1 /\ Bsm E1 E2)``,
    Rev EQ_TAC
 >- ( REWRITE_TAC [STRONG_BISIM_def, STRONG_SIM_def, inv_DEF] >> METIS_TAC [] )
 >> REWRITE_TAC [STRONG_BISIM_def]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      qpat_x_assum `STRONG_SIM Bsm`
        (STRIP_ASSUME_TAC o (REWRITE_RULE [STRONG_SIM_def])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.ABBREV_TAC `Bsm' = inv Bsm` \\
      `Bsm' E' E` by PROVE_TAC [inv_DEF] \\
      qpat_x_assum `STRONG_SIM Bsm'`
        (STRIP_ASSUME_TAC o (REWRITE_RULE [STRONG_SIM_def])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `Bsm'` \\
      POP_ASSUM (MP_TAC o BETA_RULE o (REWRITE_RULE [inv_DEF])) \\
      REWRITE_TAC [] ]);

(* The identity relation is a strong bisimulation. *)
val IDENTITY_STRONG_BISIM = store_thm (
   "IDENTITY_STRONG_BISIM",
  ``STRONG_BISIM Id``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> REPEAT STRIP_TAC (* 2 sub-goals *)
 >| [ (* goal 1 *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E:('a, 'b) CCS = E'``]
                               (ASSUME ``TRANS E u E1``)) \\
      EXISTS_TAC ``E1:('a, 'b) CCS`` \\
      ASM_REWRITE_TAC [] ,
      (* goal 2 *)
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``E2:('a, 'b) CCS`` \\
      ASM_REWRITE_TAC [] ]);

(* The converse of a strong bisimulation is a strong bisimulation. *)
val CONVERSE_STRONG_BISIM = store_thm (
   "CONVERSE_STRONG_BISIM",
  ``!Bsm. STRONG_BISIM Bsm ==> STRONG_BISIM (inv Bsm)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> REWRITE_TAC [inv_DEF] >> BETA_TAC
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >> RES_TAC (* enrich assumptions *)
 >| [ EXISTS_TAC ``E1':('a, 'b) CCS``,
      EXISTS_TAC ``E2':('a, 'b) CCS`` ]
 >> art []);

(* The composition of two strong bisimulations is a strong bisimulation. *)
val COMP_STRONG_BISIM = store_thm (
   "COMP_STRONG_BISIM",
  ``!Bsm1 Bsm2. STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==> STRONG_BISIM (Bsm2 O Bsm1)``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> REWRITE_TAC [O_DEF] >> BETA_TAC
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC
        (MP (SPECL [``E :('a, 'b) CCS``, ``y :('a, 'b) CCS``]
            (ASSUME
             ``!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))``))
          (ASSUME ``(Bsm1 :('a, 'b) simulation) E y``)) \\
      IMP_RES_TAC
        (MP (SPECL [``y :('a, 'b) CCS``, ``E' :('a, 'b) CCS``]
            (ASSUME
             ``!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))``))
          (ASSUME ``(Bsm2 :('a, 'b) simulation) y E'``)) \\
      EXISTS_TAC ``E2' :('a, 'b) CCS`` >> art [] \\
      EXISTS_TAC ``E2 :('a, 'b) CCS`` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC
        (MP (SPECL [``y :('a, 'b) CCS``, ``E' :('a, 'b) CCS``]
            (ASSUME
             ``!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))``))
          (ASSUME ``(Bsm2 :('a, 'b) simulation) y E'``)) \\
      IMP_RES_TAC
        (MP (SPECL [``E :('a, 'b) CCS``, ``y :('a, 'b) CCS``]
            (ASSUME
             ``!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))``))
          (ASSUME ``(Bsm1 :('a, 'b) simulation) E y``)) \\
      EXISTS_TAC ``E1' :('a, 'b) CCS`` >> art [] \\
      EXISTS_TAC ``E1 :('a, 'b) CCS`` >> art [] ]);

(* The union of two strong bisimulations is a strong bisimulation. *)
val UNION_STRONG_BISIM = store_thm (
   "UNION_STRONG_BISIM",
  ``!Bsm1 Bsm2. STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>
                STRONG_BISIM (Bsm1 RUNION Bsm2)``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> REWRITE_TAC [RUNION] >> BETA_TAC
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >> RES_TAC
 >| [ EXISTS_TAC ``E2 :('a, 'b) CCS``,
      EXISTS_TAC ``E1 :('a, 'b) CCS``,
      EXISTS_TAC ``E2 :('a, 'b) CCS``,
      EXISTS_TAC ``E1 :('a, 'b) CCS``]
 >> art []);

(* Define the strong equivalence relation for CCS processes.

  Two states E and E' are bisimilar (or bisimulation equivalent, denoted E ~ E',
  if there exists a bisimulation R such that (E, E') IN R.

  Old definition:
val STRONG_EQUIV = new_definition ("STRONG_EQUIV",
  ``STRONG_EQUIV E E' = ?Bsm. Bsm E E' /\ STRONG_BISIM Bsm``);

  Obsevations on new definition:
   1. STRONG_EQUIV_cases ==> STRONG_EQUIV_rules (by EQ_IMP_LR)
   2. STRONG_EQUIV_cases is the same as PROPERTY_STAR
   3. STRONG_EQUIV_coind is new (the co-inductive principle)
 *) (* NEW *)
val (STRONG_EQUIV_rules, STRONG_EQUIV_coind, STRONG_EQUIV_cases) = Hol_coreln `
    (!(E :('a, 'b) CCS) (E' :('a, 'b) CCS).
       (!u.
         (!E1. TRANS E u E1 ==>
               (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
         (!E2. TRANS E' u E2 ==>
               (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2))) ==> STRONG_EQUIV E E')`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Infix (NONASSOC, 450),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK (UTF8.chr 0x223C), BreakSpace (1,0)],
                   term_name = "STRONG_EQUIV" }

val _ = TeX_notation { hol = UTF8.chr 0x223C,
                       TeX = ("\\HOLTokenStrongEQ", 1) };

val STRONG_EQUIV_IS_STRONG_BISIM = store_thm (
   "STRONG_EQUIV_IS_STRONG_BISIM",
  ``STRONG_BISIM STRONG_EQUIV``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> PURE_ONCE_REWRITE_TAC [GSYM STRONG_EQUIV_cases]
 >> RW_TAC bool_ss []);

(* Alternative definition of STRONG_EQUIV *)
val STRONG_EQUIV = store_thm ((* NEW *)
   "STRONG_EQUIV",
  ``!E E'. STRONG_EQUIV E E' = ?Bsm. Bsm E E' /\ STRONG_BISIM Bsm``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      EXISTS_TAC ``STRONG_EQUIV`` \\
      ASM_REWRITE_TAC [STRONG_EQUIV_IS_STRONG_BISIM],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`E'`, `E'`) \\
      Q.SPEC_TAC (`E`, `E`) \\
      HO_MATCH_MP_TAC STRONG_EQUIV_coind \\ (* co-induction used here! *)
      METIS_TAC [STRONG_BISIM] ]);

val STRONG_BISIM_SUBSET_STRONG_EQUIV = store_thm ((* NEW *)
   "STRONG_BISIM_SUBSET_STRONG_EQUIV",
  ``!Bsm. STRONG_BISIM Bsm ==> Bsm RSUBSET STRONG_EQUIV``,
    PROVE_TAC [RSUBSET, STRONG_EQUIV]);

(* Strong equivalence is a reflexive relation. *)
val STRONG_EQUIV_REFL = store_thm (
   "STRONG_EQUIV_REFL", ``!E. STRONG_EQUIV E E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> Q.EXISTS_TAC `Id`
 >> REWRITE_TAC [IDENTITY_STRONG_BISIM]);

(* Strong equivalence is a symmetric relation. *)
val STRONG_EQUIV_SYM = store_thm (
   "STRONG_EQUIV_SYM",
  ``!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV E' E``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> REPEAT STRIP_TAC
 >> Q.EXISTS_TAC `inv Bsm`
 >> CONJ_TAC >- ( REWRITE_TAC [inv_DEF] >> BETA_TAC >> art [] )
 >> IMP_RES_TAC CONVERSE_STRONG_BISIM);

(* Syntactic equivalence implies strong equivalence. *)
val EQUAL_IMP_STRONG_EQUIV = store_thm (
   "EQUAL_IMP_STRONG_EQUIV", ``!E E'. (E = E') ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [STRONG_EQUIV_REFL]);

(* Strong equivalence is a transitive relation. *)
val STRONG_EQUIV_TRANS = store_thm (
   "STRONG_EQUIV_TRANS",
  ``!E E' E''. STRONG_EQUIV E E' /\ STRONG_EQUIV E' E'' ==> STRONG_EQUIV E E''``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `Bsm' O Bsm`
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `E'` >> art [],
      IMP_RES_TAC COMP_STRONG_BISIM ]);

val STRONG_EQUIV_equivalence = store_thm ((* NEW *)
   "STRONG_EQUIV_equivalence", ``equivalence STRONG_EQUIV``,
    REWRITE_TAC [equivalence_def]
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [reflexive_def, STRONG_EQUIV_REFL],
      (* goal 2 (of 3) *)
      REWRITE_TAC [symmetric_def] \\
      REPEAT GEN_TAC \\
      EQ_TAC >> REWRITE_TAC [STRONG_EQUIV_SYM],
      (* goal 3 (of 3) *)
      REWRITE_TAC [transitive_def, STRONG_EQUIV_TRANS] ]);

(* Syntactic equivalence implies strong equivalence. *)
val EQUAL_IMP_STRONG_EQUIV = store_thm (
   "EQUAL_IMP_STRONG_EQUIV",
      ``!E E'. (E = E') ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [STRONG_EQUIV_REFL]);

(* Prop. 4, page 91: strong equivalence satisfies property [*] *)
val PROPERTY_STAR = save_thm ((* NEW *)
   "PROPERTY_STAR", STRONG_EQUIV_cases);

(* Half versions of PROPERTY_STAR *)
val PROPERTY_STAR_LEFT = store_thm (
   "PROPERTY_STAR_LEFT",
  ``!E E'. STRONG_EQUIV E E' ==>
        !u E1. TRANS E u E1 ==> ?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2``,
    PROVE_TAC [PROPERTY_STAR]);

val PROPERTY_STAR_RIGHT = store_thm (
   "PROPERTY_STAR_RIGHT",
  ``!E E'. STRONG_EQUIV E E' ==>
        !u E2. TRANS E' u E2 ==> ?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2``,
    PROVE_TAC [PROPERTY_STAR]);

(* Strong equivalence is substitutive under prefix operator. *)
val STRONG_EQUIV_SUBST_PREFIX = store_thm (
   "STRONG_EQUIV_SUBST_PREFIX",
      ``!E E'.
         STRONG_EQUIV E E' ==> !u. STRONG_EQUIV (prefix u E) (prefix u E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC
      [SPECL [``prefix (u :'b Action) E``, ``prefix (u :'b Action) E'``] PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ EXISTS_TAC ``E' :('a, 'b) CCS``,
      EXISTS_TAC ``E :('a, 'b) CCS``]
 >> IMP_RES_TAC TRANS_PREFIX
 >> ASM_REWRITE_TAC [PREFIX]);

(* Strong equivalence is preserved by binary summation. *)
val STRONG_EQUIV_PRESD_BY_SUM = store_thm (
   "STRONG_EQUIV_PRESD_BY_SUM",
      ``!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (sum E1 E2) (sum E1' E2')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here *)
      RES_TAC \\
      EXISTS_TAC ``E2'' :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2 ] \\
      ASM_REWRITE_TAC [],
      (* goal 2 *)
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here *)
      RES_TAC \\
      EXISTS_TAC ``E1'' :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2] \\
      ASM_REWRITE_TAC [] ]);

(* Strong equivalence is substitutive under summation operator on the right.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E E'') (sum E' E''))
 *)
val STRONG_EQUIV_SUBST_SUM_R = save_thm (
   "STRONG_EQUIV_SUBST_SUM_R",
   (GEN_ALL o
    DISCH_ALL o
    GEN_ALL o
    UNDISCH o
    (REWRITE_RULE [STRONG_EQUIV_REFL]) o
    DISCH_ALL)
       (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM
                 (CONJ (ASSUME ``STRONG_EQUIV E E'``)
                       (ASSUME ``STRONG_EQUIV E'' E''``))));

(* Strong equivalence is substitutive under summation operator on the left.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E'' E) (sum E'' E'))
 *)
val STRONG_EQUIV_SUBST_SUM_L = save_thm (
   "STRONG_EQUIV_SUBST_SUM_L",
   (GEN_ALL o
    DISCH_ALL o
    GEN_ALL o
    UNDISCH o
    (REWRITE_RULE [STRONG_EQUIV_REFL]) o
    DISCH_ALL)
       (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM
                 (CONJ (ASSUME ``STRONG_EQUIV E'' E''``)
                       (ASSUME ``STRONG_EQUIV E E'``))));

(* Strong equivalence is preserved by parallel composition. *)
val STRONG_EQUIV_PRESD_BY_PAR = store_thm (
   "STRONG_EQUIV_PRESD_BY_PAR",
      ``!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (par E1 E2) (par E1' E2')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y.
         (?F1 F2 F3 F4.
           (x = par F1 F3) /\ (y = par F2 F4) /\
           STRONG_EQUIV F1 F2 /\ STRONG_EQUIV F3 F4)``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E1`, `E1'`, `E2`, `E2'`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F3``]
                                 (ASSUME ``TRANS E u E1''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 2.1.1 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F1 F2``)) \\
          EXISTS_TAC ``par E2'' F4`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            MATCH_MP_TAC PAR1 \\
            PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.1.2 (of 2) *)
            take [`E1'''`, `E2''`, `F3`, `F4`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F3 F4``)) \\
          EXISTS_TAC ``par F2 E2''`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            MATCH_MP_TAC PAR2 >> PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.2.2 (of 2) *)
            take [`F1`, `F2`, `E1'''`, `E2''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.3 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F1 F2``)) \\
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F3 F4``)) \\
          EXISTS_TAC ``par E2''' E2''''`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.3.1 (of 2) *)
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``l: 'b Label`` \\
            ASM_REWRITE_TAC [],
            (* goal 2.1.3.2 (of 2) *)
            take [`E1'''`, `E2'''`, `E2''`, `E2''''`] \\
            ASM_REWRITE_TAC [] ] ],
         (* goal 2.2 (of 2) *)
         ASSUME_TAC
           (REWRITE_RULE [ASSUME ``E' = par F2 F4``]
                         (ASSUME ``TRANS E' u E2''``)) \\
         IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
         [ (* goal 2.2.1 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F1 F2``)) \\
           EXISTS_TAC ``par E1''' F3`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.1.1 (of 2) *)
             MATCH_MP_TAC PAR1 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.1.2 (of 2) *)
             take [`E1'''`, `E1''`, `F3`, `F4`] \\
             ASM_REWRITE_TAC [] ],
           (* goal 2.2.2 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F3 F4``)) \\
           EXISTS_TAC ``par F1 E1'''`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             MATCH_MP_TAC PAR2 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.2.2 (of 2) *)
             take [`F1`, `F2`, `E1'''`, `E1''`] \\
             ASM_REWRITE_TAC [] ],
           (* goal 2.2.3 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F1 F2``)) \\
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F3 F4``)) \\
           EXISTS_TAC ``par E1''' E1''''`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.3.1 (of 2) *)
             MATCH_MP_TAC PAR3 \\
             EXISTS_TAC ``l: 'b Label`` \\
             ASM_REWRITE_TAC [],
             (* goal 2.2.3.2 (of 2) *)
             take [`E1'''`, `E1''`, `E1''''`, `E2'''`] \\
             ASM_REWRITE_TAC [] ] ] ] ]);

(* Strong equivalence is substitutive under parallel operator on the right:
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (par E E'') (par E' E''))
 *)
val STRONG_EQUIV_SUBST_PAR_R = save_thm (
   "STRONG_EQUIV_SUBST_PAR_R",
    Q_GENL [`E`, `E'`]
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR
             (CONJ (ASSUME ``STRONG_EQUIV E E'``)
                   (ASSUME ``STRONG_EQUIV E'' E''``)))))))));

(* Strong equivalence is substitutive under parallel operator on the left:
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (par E'' E) (par E'' E'))
 *)
val STRONG_EQUIV_SUBST_PAR_L = save_thm (
   "STRONG_EQUIV_SUBST_PAR_L",
    Q_GENL [`E`, `E'`]
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR
             (CONJ (ASSUME ``STRONG_EQUIV E'' E''``)
                   (ASSUME ``STRONG_EQUIV E E'``)))))))));

(* Strong equivalence is substitutive under restriction operator. *)
val STRONG_EQUIV_SUBST_RESTR = store_thm (
   "STRONG_EQUIV_SUBST_RESTR",
      ``!E E'.
         STRONG_EQUIV E E' ==>
         (!L. STRONG_EQUIV (restr L E) (restr L E'))``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 L'. (x = restr L' E1) /\ (y = restr L' E2) /\
                                  STRONG_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `L`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                                 (ASSUME ``TRANS E'' u E1'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV E1 E2``)) \\
          EXISTS_TAC ``restr (L' :'b Label set) E2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = tau``]
                                      (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.1.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 2) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV E1 E2``)) \\
          EXISTS_TAC ``restr (L' :'b Label set) E2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            EXISTS_TAC ``l: 'b Label`` \\
            ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = label l``]
                                          (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.2.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ] ],
          (* goal 2.2 (of 2) *)
          ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
                                   (ASSUME ``TRANS E''' u E2'``)) \\
          IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
          [ (* goal 2.2.1 (of 2) *)
            IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                           (ASSUME ``STRONG_EQUIV E1 E2``)) \\
            EXISTS_TAC ``restr (L' :'b Label set) E1'`` \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1 (of 2) *)
              ASM_REWRITE_TAC [] \\
              MATCH_MP_TAC RESTR \\
              REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = tau``]
                                        (ASSUME ``TRANS E1 u E1'``)],
              (* goal 2.2.1.2 (of 2) *)
              take [`E1'`, `E''''`, `L'`] \\
              ASM_REWRITE_TAC [] ],
           (* goal 2.2.2 (of 2) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV E1 E2``)) \\
           EXISTS_TAC ``restr (L' :'b Label set) E1'`` \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             ASM_REWRITE_TAC [] \\
             MATCH_MP_TAC RESTR \\
             EXISTS_TAC ``l: 'b Label`` \\
             ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = label l``]
                                           (ASSUME ``TRANS E1 u E1'``)],
             (* goal 2.2.2.2 (of 2) *)
             take [`E1'`, `E''''`, `L'`] \\
             ASM_REWRITE_TAC [] ] ] ] ]);

(* Strong equivalence is substitutive under relabelling operator. *)
val STRONG_EQUIV_SUBST_RELAB = store_thm (
   "STRONG_EQUIV_SUBST_RELAB",
      ``!E E'.
         STRONG_EQUIV E E' ==>
         (!rf. STRONG_EQUIV (relab E rf) (relab E' rf))``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\
                                   STRONG_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `rf`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                                 (ASSUME ``TRANS E'' u E1'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E2' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELABELING \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          take [`E''''`, `E2'`, `rf'`] \\
          ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                                 (ASSUME ``TRANS E''' u E2'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E1' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELABELING \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          take [`E1'`, `E''''`, `rf'`] \\
          ASM_REWRITE_TAC [] ] ] ]);

val _ = export_theory ();
val _ = html_theory "StrongEQ";

(* last updated: Jun 20, 2017 *)
