(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory llistTheory
     ltreeTheory pathTheory posetTheory hurdUtils;

open binderLib termTheory appFOLDLTheory chap2Theory chap3Theory
     head_reductionTheory standardisationTheory solvableTheory pure_dBTheory;

val _ = new_theory "boehm_tree";

val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “hnf o toTerm”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

(* Translations from dLAMl to dABSi.

   Some samples for guessing out the statements of this theorem:

> SIMP_CONV arith_ss [dLAM_def, lift_def, sub_def, lift_sub]
                     “dLAM v1 (dLAM v0 t)”;
# val it =
   |- dLAM v1 (dLAM v0 t) =
      dABS (dABS ([dV 1/v1 + 2] ([dV 0/v0 + 2] (lift (lift t 0) 1)))): thm

> SIMP_CONV arith_ss [dLAM_def, lift_def, sub_def, lift_sub]
                     “dLAM v2 (dLAM v1 (dLAM v0 t))”;
# val it =
   |- dLAM v2 (dLAM v1 (dLAM v0 t)) =
      dABS
        (dABS
           (dABS ([dV 2/v2 + 3]
                    ([dV 1/v1 + 3]
                       ([dV 0/v0 + 3]
                          (lift (lift (lift t 0) 1) 2)))))): thm
 *)
Theorem dLAMl_to_dABSi :
    !vs. ALL_DISTINCT (vs :num list) ==>
         let n = LENGTH vs;
             body = FOLDL lift t (GENLIST I n);
             phi = ZIP (GENLIST dV n, MAP (\i. i + n) (REVERSE vs))
         in dLAMl vs t = dABSi n (body ISUB phi)
Proof
    Induct_on ‘vs’ >- rw [isub_def]
 >> rw [isub_def, GSYM SNOC_APPEND, MAP_SNOC, FUNPOW_SUC, GENLIST, FOLDL_SNOC,
        dLAM_def]
 >> fs []
 >> qabbrev_tac ‘n = LENGTH vs’
 >> rw [lift_dABSi]
 >> Q.PAT_X_ASSUM ‘dLAMl vs t = _’ K_TAC
 >> qabbrev_tac ‘N = FOLDL lift t (GENLIST I n)’
 >> qabbrev_tac ‘Ms = GENLIST dV n’
 >> qabbrev_tac ‘Vs = MAP (\i. i + n) (REVERSE vs)’
 >> Know ‘lift (N ISUB ZIP (Ms,Vs)) n =
          (lift N n) ISUB (ZIP (MAP (\e. lift e n) Ms,MAP SUC Vs))’
 >- (MATCH_MP_TAC lift_isub \\
     rw [Abbr ‘Ms’, Abbr ‘Vs’, EVERY_MEM, MEM_MAP] >> rw [])
 >> Rewr'
 >> ‘MAP SUC Vs = MAP (\i. i + SUC n) (REVERSE vs)’
       by (rw [LIST_EQ_REWRITE, EL_MAP, Abbr ‘Vs’]) >> POP_ORW
 >> qunabbrev_tac ‘Vs’ (* now useless *)
 >> rw [sub_def, GSYM ADD1]
 >> ‘MAP (\e. lift e n) Ms = Ms’
       by (rw [LIST_EQ_REWRITE, EL_MAP, Abbr ‘Ms’]) >> POP_ORW
 >> qabbrev_tac ‘Ns = MAP (\i. i + SUC n) (REVERSE vs)’
 >> qabbrev_tac ‘N' = lift N n’
 >> Suff ‘N' ISUB ZIP (SNOC (dV n) Ms,SNOC (h + SUC n) Ns) =
          [dV n/h + SUC n] (N' ISUB ZIP (Ms,Ns))’ >- rw []
 >> MATCH_MP_TAC isub_SNOC
 >> rw [Abbr ‘Ms’, Abbr ‘Ns’, MEM_EL, EL_MAP]
 >> rename1 ‘~(i < n)’
 >> ‘LENGTH (REVERSE vs) = n’ by rw [Abbr ‘n’]
 >> CCONTR_TAC >> gs [EL_MAP]
 >> ‘h = EL i (REVERSE vs)’ by rw []
 >> Suff ‘MEM h (REVERSE vs)’ >- rw [MEM_REVERSE]
 >> Q.PAT_X_ASSUM ‘~MEM h vs’ K_TAC
 >> ‘LENGTH (REVERSE vs) = n’ by rw [Abbr ‘n’]
 >> REWRITE_TAC [MEM_EL]
 >> Q.EXISTS_TAC ‘i’ >> art []
QED

(* |- !t vs.
        ALL_DISTINCT vs ==>
        dLAMl vs t =
        dABSi (LENGTH vs)
          (FOLDL lift t (GENLIST I (LENGTH vs)) ISUB
           ZIP (GENLIST dV (LENGTH vs),MAP (\i. i + LENGTH vs) (REVERSE vs)))
 *)
Theorem dLAMl_to_dABSi_applied[local] =
    GEN_ALL (SIMP_RULE std_ss [LET_DEF] dLAMl_to_dABSi)

(* dB version of hnf_cases (only the ==> direction) *)
Theorem dhnf_cases :
    !M. dhnf M ==> ?n y Ms. M = dABSi n (dV y @* Ms)
Proof
    RW_TAC std_ss [hnf_cases]
 >> qabbrev_tac ‘n = LENGTH vs’
 >> Q.EXISTS_TAC ‘n’
 >> Know ‘fromTerm (toTerm M) = fromTerm (LAMl vs (VAR y @* args))’
 >- (art [fromTerm_11])
 >> Q.PAT_X_ASSUM ‘toTerm M = LAMl vs (VAR y @* args)’ K_TAC
 >> rw [fromTerm_LAMl, fromTerm_appstar]
 >> qabbrev_tac ‘vs' = MAP s2n vs’
 >> qabbrev_tac ‘Ms = MAP fromTerm args’
 >> qabbrev_tac ‘y' = s2n y’
 >> Know ‘dLAMl vs' (dV y' @* Ms) =
          dABSi (LENGTH vs')
            (FOLDL lift (dV y' @* Ms) (GENLIST I (LENGTH vs')) ISUB
             ZIP (GENLIST dV (LENGTH vs'),
                  MAP (\i. i + LENGTH vs') (REVERSE vs')))’
 >- (MATCH_MP_TAC dLAMl_to_dABSi_applied \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> ‘LENGTH vs' = n’ by rw [Abbr ‘vs'’] >> POP_ORW
 >> Rewr'
 >> simp [FOLDL_lift_appstar, isub_appstar]
 >> Know ‘FOLDL lift (dV y') (GENLIST I n) = dV (y' + n)’
 >- (KILL_TAC \\
     Induct_on ‘n’ >> rw [GENLIST, FOLDL_SNOC])
 >> Rewr'
 >> qabbrev_tac ‘Ms' = MAP (\e. FOLDL lift e (GENLIST I n)) Ms’
 >> reverse (Cases_on ‘MEM y vs’)
 >- (‘~MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP]) \\
     ‘~MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE] \\
     Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,MAP (\i. i + n) (REVERSE vs')) =
           dV (y' + n)’ >- (Rewr' >> METIS_TAC []) \\
     MATCH_MP_TAC isub_dV_fresh \\
     qabbrev_tac ‘l1 = GENLIST dV n’ \\
     qabbrev_tac ‘l2 = MAP (\i. i + n) (REVERSE vs')’ \\
    ‘LENGTH l1 = n’ by rw [Abbr ‘l1’] \\
    ‘LENGTH l2 = n’ by rw [Abbr ‘l2’, Abbr ‘n’, Abbr ‘vs'’] \\
     simp [DOM_ALT_MAP_SND, MAP_ZIP] \\
     rw [Abbr ‘l2’, MEM_MAP])
 (* stage work *)
 >> ‘MEM y' vs'’ by (rw [Abbr ‘y'’, Abbr ‘vs'’, MEM_MAP])
 >> ‘MEM y' (REVERSE vs')’ by PROVE_TAC [MEM_REVERSE]
 >> ‘?j. j < LENGTH (REVERSE vs') /\ y' = EL j (REVERSE vs')’
        by METIS_TAC [MEM_EL]
 >> ‘LENGTH (REVERSE vs') = n’ by rw [Abbr ‘vs'’, Abbr ‘n’]
 >> qabbrev_tac ‘Ns = MAP (\i. i + n) (REVERSE vs')’
 >> ‘LENGTH Ns = n’ by rw [Abbr ‘Ns’]
 >> Know ‘ALL_DISTINCT Ns’
 >- (qunabbrev_tac ‘Ns’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [] \\
     qunabbrev_tac ‘vs'’ \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >> rw [])
 >> DISCH_TAC
 >> Suff ‘dV (y' + n) ISUB ZIP (GENLIST dV n,Ns) = EL j (GENLIST dV n)’
 >- (Rewr' \\
     simp [EL_GENLIST] >> METIS_TAC [])
 >> MATCH_MP_TAC isub_dV_once >> simp []
 >> CONJ_TAC >- (rw [Abbr ‘Ns’, EL_MAP])
 >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC
 >> ‘n <= EL i Ns’ by rw [Abbr ‘Ns’, EL_MAP]
 >> Suff ‘FVS (ZIP (GENLIST dV n,Ns)) = count n’ >- rw []
 >> Q.PAT_X_ASSUM ‘LENGTH Ns = n’ MP_TAC
 >> KILL_TAC >> Q.ID_SPEC_TAC ‘Ns’
 >> Induct_on ‘n’ >> rw [dFVS_def]
 >> ‘Ns <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘LENGTH (FRONT Ns) = n’ by rw [LENGTH_FRONT]
 >> ‘Ns = SNOC (LAST Ns) (FRONT Ns)’
      by (rw [APPEND_FRONT_LAST, SNOC_APPEND]) >> POP_ORW
 >> Q.PAT_X_ASSUM ‘!Ns. LENGTH Ns = n ==> P’ (MP_TAC o (Q.SPEC ‘FRONT Ns’))
 >> rw [GENLIST, COUNT_SUC, dFVS_SNOC, ZIP_SNOC, dFV_def]
 >> SET_TAC []
QED

val _ = export_theory ();
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
