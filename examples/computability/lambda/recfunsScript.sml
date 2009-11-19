open HolKernel Parse boolLib bossLib

open churchDBTheory
open churchnumTheory
open pred_setTheory
open chap3Theory
open normal_orderTheory
open reductionEval

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = set_trace "Unicode" 1

val _ = new_theory "recfuns"


(* Phi lifts all possible lambda-terms into the space of num->num option,
   indexing into the lambda-terms with the enumeration.  The NONE result
   corresponds to a divergence. *)
val Phi_def = Define`
  Phi n m = OPTION_MAP force_num (bnf_of (toTerm (numdB n) @@ church m))
`;

val UM_def = Define`
  UM =
  LAM "nm"
    (cbnf_ofk @@ cforce_num @@ (cdAPP @@ (cnumdB @@ (cnfst @@ VAR "nm"))
                                      @@ (cchurch @@ (cnsnd @@ VAR "nm"))))
`;

val FV_UM = Store_thm(
  "FV_UM",
  ``FV UM = {}``,
  SRW_TAC [][UM_def, EXTENSION]);

val PhiSOME_UM_I = store_thm(
  "PhiSOME_UM_I",
  ``(Phi n m = SOME p) ⇒ UM @@ church (n ⊗ m) -n->* church p``,
  SRW_TAC [][Phi_def, UM_def] THEN
  SIMP_TAC (bsrw_ss()) [cnfst_behaviour, cnumdB_behaviour, cnsnd_behaviour,
                        cchurch_behaviour, cdAPP_behaviour] THEN
  IMP_RES_TAC cbnf_of_works1 THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour]);

val PhiNONE_UM = store_thm(
  "PhiNONE_UM",
  ``(Phi n m = NONE) ⇔ ¬has_bnf (UM @@ church (n ⊗ m))``,
  EQ_TAC THENL [
    SRW_TAC [][Phi_def] THEN REPEAT STRIP_TAC THEN
    `∃M. UM @@ church (n ⊗ m) == M ∧ bnf M`
      by METIS_TAC [has_bnf_thm, betastar_lameq_bnf] THEN
    Q.PAT_ASSUM `X == Y` MP_TAC THEN
    SIMP_TAC (bsrw_ss()) [UM_def, cnfst_behaviour, cnsnd_behaviour,
                          cdAPP_behaviour, cnumdB_behaviour,
                          cchurch_behaviour] THEN
    STRIP_TAC THEN
    `cbnf_ofk @@ cforce_num @@ cDB (dAPP (numdB n) (fromTerm (church m)))
       -n->* M`
      by METIS_TAC [betastar_lameq_bnf, nstar_betastar_bnf] THEN
    IMP_RES_TAC cbnf_ofk_works2 THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Cases_on `Phi n m` THEN SRW_TAC [][] THEN
    IMP_RES_TAC PhiSOME_UM_I THEN
    METIS_TAC [nstar_betastar, bnf_church, has_bnf_thm]
  ]);

(* effectively the other case for PhiSOME_UM *)
val UM_bnf = store_thm(
  "UM_bnf",
  ``UM @@ church (n ⊗ m) == M ∧ bnf M ⇒
    ∃p. (Phi n m = SOME p) ∧ (M = church p)``,
  REPEAT STRIP_TAC THEN Cases_on `Phi n m` THEN SRW_TAC [][] THENL [
    METIS_TAC [PhiNONE_UM, has_bnf_thm, betastar_lameq_bnf],
    `UM @@ church (n ⊗ m) == church x`
      by METIS_TAC [PhiSOME_UM_I, nstar_lameq] THEN
    METIS_TAC [betastar_lameq_bnf,  bnf_reduction_to_self, bnf_triangle,
               bnf_church]
  ]);

val PhiSOME_UM = store_thm(
  "PhiSOME_UM",
  ``(Phi n m = SOME p) ⇔ UM @@ church (n ⊗ m) -n->* church p``,
  EQ_TAC THEN SRW_TAC [][PhiSOME_UM_I] THEN
  MATCH_MP_TAC
    (UM_bnf |> Q.INST [`M` |-> `church p`] |> SIMP_RULE (srw_ss()) []) THEN
  ASM_SIMP_TAC (bsrw_ss()) []);

(* Phi and its connection to cbnf_ofk *)
val cbnf_of_works1' =
    cbnf_of_works1 |> Q.INST [`M` |-> `toTerm dM`, `N` |-> `toTerm dN`]
                   |> SIMP_RULE (srw_ss()) []

val PhiSOME_cbnf_ofk = store_thm(
  "PhiSOME_cbnf_ofk",
  ``(Phi N e = SOME z) ⇒
    ∃v.
      (∀k. cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e))) ==
           k @@ cDB v) ∧
      (z = force_num (toTerm v))``,
  STRIP_TAC THEN
  `UM @@ church (N ⊗ e) -n->* church z`
    by FULL_SIMP_TAC (srw_ss()) [PhiSOME_UM] THEN
  FULL_SIMP_TAC (bsrw_ss()) [UM_def, cnfst_behaviour,
                             cchurch_behaviour, cnsnd_behaviour,
                             cnumdB_behaviour, cdAPP_behaviour] THEN
  `∃z'. (bnf_of (toTerm (dAPP (numdB N) (fromTerm (church e)))) =
         SOME (toTerm z')) ∧
        cforce_num @@ cDB z' -n->* church z`
      by METIS_TAC [cbnf_ofk_works2, bnf_church, nstar_betastar_bnf,
                    chap3Theory.betastar_lameq_bnf] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC (bsrw_ss()) [cforce_num_behaviour] THEN STRIP_TAC THEN
  IMP_RES_TAC cbnf_of_works1' THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  METIS_TAC [chap2Theory.lameq_refl]);

val optlemma = prove(
  ``(x ≠ NONE) ⇔ ∃z. x = SOME z``,
  Cases_on `x` THEN SRW_TAC [][]);

val PhiNONE_cbnf_ofk = store_thm(
  "PhiNONE_cbnf_ofk",
  ``(Phi N e = NONE) ⇒
    (bnf_of (cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e)))) =
     NONE)``,
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [optlemma] THEN
  `cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e))) -n->* z ∧
   bnf z`
     by METIS_TAC [bnf_of_SOME] THEN
  `∃v. (bnf_of (toTerm (dAPP (numdB N) (fromTerm (church e)))) =
        SOME (toTerm v)) ∧
       k @@ cDB v -n->* z`
     by METIS_TAC [cbnf_ofk_works2] THEN
  SRW_TAC [][Phi_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val bnf_of_UM = store_thm(
  "bnf_of_UM",
  ``bnf_of (UM @@ church n) =
    OPTION_MAP (church o force_num)
               (bnf_of (toTerm (numdB (nfst n)) @@ church (nsnd n)))``,
  SIMP_TAC (bsrw_ss()) [UM_def, cnsnd_behaviour, cchurch_behaviour,
                        cnumdB_behaviour, cnfst_behaviour, cdAPP_behaviour] THEN
  Cases_on `bnf_of (toTerm (numdB (nfst n)) @@ church (nsnd n))` THENL [
    IMP_RES_TAC bnfNONE_cbnf_ofk_fails THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [bnf_of_NONE],

    IMP_RES_TAC cbnf_of_works1 THEN
    FULL_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour, bnf_bnf_of]
  ]);

(* ----------------------------------------------------------------------
    computable functions compose
   ---------------------------------------------------------------------- *)

local open parmonadsyntax in
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
end

val OPTION_MAP_COMPOSE = optionTheory.OPTION_MAP_COMPOSE

val composition_computable = store_thm(
  "composition_computable",
  ``∀f g. ∃fg. ∀n. Phi fg n = do x <- Phi g n ; Phi f x od``,
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM "n" (
    cbnf_ofk
      @@ (LAM "r" (UM @@ (cnpair @@ church f @@ (cforce_num @@ VAR "r"))))
      @@ (cdAPP @@ (cnumdB @@ church g) @@ (cchurch @@ VAR "n")))))` THEN
  SRW_TAC [][Once Phi_def, SimpLHS] THEN
  SIMP_TAC (bsrw_ss()) [cchurch_behaviour, cnumdB_behaviour,
                        cdAPP_behaviour] THEN
  Cases_on `Phi g n` THEN1 (IMP_RES_TAC PhiNONE_cbnf_ofk THEN SRW_TAC [][]) THEN
  IMP_RES_TAC PhiSOME_cbnf_ofk THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnpair_behaviour, cforce_num_behaviour,
                            bnf_of_UM, OPTION_MAP_COMPOSE] THEN
  SIMP_TAC (srw_ss()) [Phi_def]);

val computable_composition_def = new_specification(
  "computable_composition_def", ["computable_composition"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] composition_computable);
val _ = overload_on ("o", ``computable_composition``);

(* ----------------------------------------------------------------------
    s-m-n theorem for case of m = 1, n = 1
   ---------------------------------------------------------------------- *)

val _ = temp_overload_on ("ei", (* encoded index *)
                          ``λt. church (dBnum (fromTerm t))``)



val s11_exists = prove(
  ``∃s11. ∀n. ∃fi. (Phi s11 n = SOME fi) ∧
                   ∀y. Phi fi y = Phi (nfst n) (nsnd n ⊗ y)``,
  Q.EXISTS_TAC `
   dBnum (fromTerm (LAM "fx" (
     cdBnum
       @@ (cdLAM
             @@ church (s2n "y")
             @@ (cdAPP
                   @@ (cnumdB @@ ei UM)
                   @@ (cdAPP
                         @@ (cdAPP
                               @@ (cnumdB @@ ei cnpair)
                               @@ (cchurch @@ (cnfst @@ VAR "fx")))
                         @@ (cdAPP
                               @@ (cdAPP
                                     @@ (cnumdB @@ ei cnpair)
                                     @@ (cchurch @@ (cnsnd @@ VAR "fx")))
                               @@ (cdV @@ church (s2n "y")))))))))` THEN
  SRW_TAC [][Phi_def] THEN
  SIMP_TAC (bsrw_ss()) [cdV_behaviour, cdAPP_behaviour, cnsnd_behaviour,
                        cnumdB_behaviour, cchurch_behaviour, cnfst_behaviour,
                        cdLAM_behaviour, cdBnum_behaviour, bnf_bnf_of,
                        cnpair_behaviour, bnf_of_UM, OPTION_MAP_COMPOSE]);

val s11_def = new_specification("s11_def", ["s11"], s11_exists)

val s11f_def = new_specification(
  "s11f_def", ["s11f"],
  s11_def |> Q.SPEC `g ⊗ x` |> Q.GEN `x` |> Q.GEN `g`
          |> SIMP_RULE (srw_ss()) [SKOLEM_THM]);

(* ----------------------------------------------------------------------
    Kleene's 2nd recursion theorem.

    Proof and statement of theorem from wikipedia page.
   ---------------------------------------------------------------------- *)



val recursion_thm = store_thm(
  "recursion_thm",
  ``(∀n. ∃r. Phi fi n = SOME r) ⇒ ∃e. Phi (THE (Phi fi e)) = Phi e``,
  (* if fi is the index of a total computable function f, then there
     exists an index e such that Phi e = Phi (f e). *)
  DISCH_THEN (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [SKOLEM_THM]) THEN
  Q.ABBREV_TAC
    `g =
     LAM "xy" (cbnf_ofk
                 @@ (LAM "t"
                         (cbnf_ofk
                            @@ cforce_num
                            @@ (cdAPP
                                  @@ (cnumdB @@ (cforce_num @@ VAR "t"))
                                  @@ (cchurch @@ (cnsnd @@ VAR "xy")))))
                 @@ (cdAPP
                       @@ (cnumdB @@ (cnfst @@ VAR "xy"))
                       @@ (cchurch @@ (cnfst @@ VAR "xy"))))` THEN
  Q.ABBREV_TAC `gi = dBnum (fromTerm g)` THEN
  `∀x y. Phi gi (x ⊗ y) = case Phi x x of NONE -> NONE || SOME e -> Phi e y`
     by (REPEAT GEN_TAC THEN SRW_TAC [][Phi_def] THEN
         SIMP_TAC (bsrw_ss()) [Abbr`gi`, Abbr`g`] THEN
         SIMP_TAC (bsrw_ss()) [cnfst_behaviour, cnsnd_behaviour,
                               cchurch_behaviour, cdAPP_behaviour,
                               cnumdB_behaviour] THEN
         Cases_on `bnf_of (toTerm (numdB x) @@ church x)` THENL [
           IMP_RES_TAC bnfNONE_cbnf_ofk_fails THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [bnf_of_NONE],
           IMP_RES_TAC cbnf_of_works1 THEN
           FULL_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour, bnf_bnf_of] THEN
           SIMP_TAC (bsrw_ss()) [cdAPP_behaviour, cnumdB_behaviour] THEN
           Cases_on `bnf_of (toTerm (numdB (force_num x')) @@ church y)` THENL [
             IMP_RES_TAC bnfNONE_cbnf_ofk_fails THEN
             FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [bnf_of_NONE],
             IMP_RES_TAC cbnf_of_works1 THEN
             FULL_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour, bnf_bnf_of]
           ]
         ]) THEN
  Q.ABBREV_TAC `hi = s11f s11 gi` THEN
  Q.ABBREV_TAC `h = λx. THE (Phi hi x)` THEN
  `∀x r. (Phi x x = SOME r) ⇒ (Phi (h x) = Phi r)`
     by ASM_SIMP_TAC (srw_ss()) [Abbr`h`, s11f_def, Abbr`hi`, FUN_EQ_THM] THEN
  Q.SPECL_THEN [`fi`, `hi`] (Q.X_CHOOSE_THEN `e` ASSUME_TAC)
               composition_computable THEN
  `Phi e e = SOME (f (s11f gi e))` by SRW_TAC [][s11f_def, Abbr`hi`] THEN
  Q.EXISTS_TAC `h e` THEN
  `Phi (h e) = Phi (THE (Phi e e))` by SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (srw_ss()) [Abbr`h`, Abbr`hi`, s11f_def]);


val _ = export_theory()
