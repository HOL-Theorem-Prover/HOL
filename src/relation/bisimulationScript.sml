(* ------------------------------------------------------------------------ *)
(*  Bisimulations defined on general labeled transition ('a->'b->'a->bool)  *)
(* ------------------------------------------------------------------------ *)

open HolKernel Parse boolLib simpLib metisLib BasicProvers;
open relationTheory;

val _ = new_theory "bisimulation";

(*---------------------------------------------------------------------------*)
(*  (Strong) bisimulation                                                    *)
(*---------------------------------------------------------------------------*)

val BISIM_def = new_definition ("BISIM_def",
  ``BISIM ts R = !p q.
                    R p q ==> !l.
                    (!p'. ts p l p' ==> ?q'. ts q l q' /\ R p' q') /\
                    (!q'. ts q l q' ==> ?p'. ts p l p' /\ R p' q')``);

(* (Strong) bisimilarity, see BISIM_REL_def for an alternative definition *)
CoInductive BISIM_REL :
    !p q. (!l.
            (!p'. ts p l p' ==> ?q'. ts q l q' /\ (BISIM_REL ts) p' q') /\
            (!q'. ts q l q' ==> ?p'. ts p l p' /\ (BISIM_REL ts) p' q'))
      ==> (BISIM_REL ts) p q
End

Theorem BISIM_ID :
    !ts. BISIM ts Id
Proof
    SRW_TAC[][BISIM_def]
QED

Theorem BISIM_INV :
    !ts R. BISIM ts R ==> BISIM ts (inv R)
Proof
    SRW_TAC[][BISIM_def, inv_DEF] >> METIS_TAC []
QED

Theorem BISIM_O :
    !ts R R'. BISIM ts R /\ BISIM ts R' ==> BISIM ts (R' O R)
Proof
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [BISIM_def]
 >> SRW_TAC[][O_DEF]
 >> METIS_TAC[BISIM_def]
QED

Theorem BISIM_RUNION :
    !ts R R'. BISIM ts R /\ BISIM ts R' ==> BISIM ts (R RUNION R')
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [BISIM_def]
 >> SRW_TAC[][RUNION]
 >> METIS_TAC[]
QED

Theorem BISIM_REL_IS_BISIM :
    !ts. BISIM ts (BISIM_REL ts)
Proof
    PURE_ONCE_REWRITE_TAC [BISIM_def]
 >> rpt GEN_TAC >> DISCH_TAC
 >> Q.SPEC_TAC (`l`, `l`)
 >> PURE_ONCE_REWRITE_TAC [GSYM BISIM_REL_cases]
 >> ASM_REWRITE_TAC []
QED

(* (Strong) bisimilarity, the original definition *)
Theorem BISIM_REL_def :
    !ts. BISIM_REL ts = \p q. ?R. BISIM ts R /\ R p q
Proof
    SRW_TAC[][FUN_EQ_THM]
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC >> Q.EXISTS_TAC `BISIM_REL ts` \\
      ASM_REWRITE_TAC [BISIM_REL_IS_BISIM],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`q`, `q`) \\
      Q.SPEC_TAC (`p`, `p`) \\
      HO_MATCH_MP_TAC BISIM_REL_coind \\ (* co-induction used here! *)
      PROVE_TAC [BISIM_def] ]
QED

Theorem BISIM_REL_IS_EQUIV_REL :
    !ts. equivalence (BISIM_REL ts)
Proof
    SRW_TAC[][equivalence_def]
 >- (SRW_TAC[][reflexive_def, BISIM_REL_def] \\
     Q.EXISTS_TAC `Id` \\
     REWRITE_TAC [BISIM_ID])
 >- (SRW_TAC[][symmetric_def, BISIM_REL_def] \\
     SRW_TAC[][EQ_IMP_THM] \\
     Q.EXISTS_TAC `SC R` \\
     FULL_SIMP_TAC (srw_ss ()) [BISIM_def, SC_DEF] \\
     METIS_TAC[])
 >- (SRW_TAC[][transitive_def, BISIM_REL_def] \\
     Q.EXISTS_TAC `R' O R` \\
     METIS_TAC [O_DEF, BISIM_O])
QED


(*---------------------------------------------------------------------------*)
(*  Weak bisimulation                                                        *)
(*---------------------------------------------------------------------------*)

(* Empty transition: zero or more invisible actions *)
val ETS_def = new_definition ("ETS_def", (* was: EPS *)
  ``ETS ts tau = RTC (\x y. ts x tau y)``);

(* Weak transition *)
val WTS_def = new_definition ("WTS_def",
  ``WTS ts tau =
     \p l q. ?p' q'. (ETS ts tau) p p' /\ ts p' l q' /\ (ETS ts tau) q' q``);

(* Weak bisimulation *)
val WBISIM_def = new_definition ("WBISIM_def",
  ``WBISIM ts tau R =
     !p q. R p q ==>
          (!l. l <> tau ==>
            (!p'. ts p l p' ==> ?q'. (WTS ts tau) q l q' /\ R p' q') /\
            (!q'. ts q l q' ==> ?p'. (WTS ts tau) p l p' /\ R p' q')) /\
          (!p'. ts p tau p' ==> ?q'. (ETS ts tau) q   q' /\ R p' q') /\
          (!q'. ts q tau q' ==> ?p'. (ETS ts tau) p   p' /\ R p' q')``);

(* Weak bisimilarity, see WBISIM_REL_def for an alternative definition *)
CoInductive WBISIM_REL :
  !p q.
    (!l. l <> tau ==>
      (!p'. ts p l p' ==> ?q'. WTS ts tau q l q' /\ WBISIM_REL ts tau p' q') /\
      (!q'. ts q l q' ==> ?p'. WTS ts tau p l p' /\ WBISIM_REL ts tau p' q')) /\
    (!p'. ts p tau p' ==> ?q'. ETS ts tau q   q' /\ WBISIM_REL ts tau p' q') /\
    (!q'. ts q tau q' ==> ?p'. ETS ts tau p   p' /\ WBISIM_REL ts tau p' q')
   ==>
    WBISIM_REL ts tau p q
End

Theorem TS_IMP_ETS :
    !ts tau p q. ts p tau q ==> (ETS ts tau) p q
Proof
    SRW_TAC[][ETS_def]
 >> MATCH_MP_TAC RTC_SINGLE
 >> BETA_TAC >> ASM_REWRITE_TAC []
QED

Theorem ETS_REFL :
    !ts tau p. (ETS ts tau) p p
Proof
    SRW_TAC[][ETS_def, RTC_REFL]
QED

Theorem TS_IMP_WTS :
    !ts tau p l q. ts p l q ==> WTS ts tau p l q
Proof
    SRW_TAC[][WTS_def]
 >> Q.EXISTS_TAC `p`
 >> Q.EXISTS_TAC `q`
 >> ASM_REWRITE_TAC [ETS_REFL]
QED

Theorem ETS_TRANS :
    !ts tau x y z. (ETS ts tau) x y /\ (ETS ts tau) y z
               ==> (ETS ts tau) x z
Proof
    SRW_TAC[][ETS_def]
 >> MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE)
 >> Q.EXISTS_TAC `y`
 >> ASM_REWRITE_TAC []
QED

val lemma1 = prove (
  ``!R. (!p q.   ts p tau q ==> R p q) /\
        (!p.     R p p) /\
        (!p q r. R p q /\ R q r ==> R p r)
    ==> !p q. (ETS ts tau) p q ==> R p q``,
    GEN_TAC >> STRIP_TAC
 >> REWRITE_TAC [ETS_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> METIS_TAC []);

Theorem ETS_WTS_ETS :
    !ts tau p p1 l p2 p'.
        (ETS ts tau) p p1 /\ (WTS ts tau) p1 l p2 /\ (ETS ts tau) p2 p'
    ==> (WTS ts tau) p l p'
Proof
    SRW_TAC[][WTS_def]
 >> Q.EXISTS_TAC `p''`
 >> Q.EXISTS_TAC `q'`
 >> ASM_REWRITE_TAC []
 >> METIS_TAC [ETS_TRANS]
QED

Theorem WBISIM_INV :
    !ts tau R. WBISIM ts tau R ==> WBISIM ts tau (inv R)
Proof
    SRW_TAC[][WBISIM_def, inv_DEF] >> METIS_TAC []
QED

Theorem lemma2[local]:
  !p p'. (ETS ts tau) p p' ==>
         !R q. WBISIM ts tau R /\ R p q ==> ?q'. (ETS ts tau) q q' /\ R p' q'
Proof
    HO_MATCH_MP_TAC lemma1
 >> SRW_TAC[][]
 >| [ (* goal 1 (of 3) *)
      FULL_SIMP_TAC (srw_ss()) [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      FULL_SIMP_TAC (srw_ss()) [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q` \\
      ASM_REWRITE_TAC [ETS_def, RTC_REFL],
      (* goal 3 (of 3) *)
     `?q'. ETS ts tau q q' /\ R p' q'` by PROVE_TAC [] \\
     `?q''. ETS ts tau q' q'' /\ R p'' q''` by PROVE_TAC [] \\
      Q.EXISTS_TAC `q''` >> ASM_REWRITE_TAC [] \\
      FULL_SIMP_TAC (srw_ss()) [ETS_def] \\
      MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) \\
      Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [] ]
QED

val lemma2' = prove (
  ``!q q'. (ETS ts tau) q q' ==>
           !R p. WBISIM ts tau R /\ R p q ==>
                 ?p'. (ETS ts tau) p p' /\ R p' q'``,
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`q`, `q'`] lemma2) >> SRW_TAC[][]
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [inv_DEF]) o (Q.SPECL [`inv R`, `p`]))
 >> IMP_RES_TAC WBISIM_INV
 >> SRW_TAC[][]);

(* p ==> p1 -l-> p2 ==> p'
   R     R       R      R
   q ==> q1 =l=> q2 ==> q'
 *)
val lemma3 = prove (
  ``!p l p'. (WTS ts tau) p l p' /\ l <> tau ==>
             !R q. WBISIM ts tau R /\ R p q ==>
                   ?q'. (WTS ts tau) q l q' /\ R p' q'``,
    rpt STRIP_TAC
 >> `?p1 p2. (ETS ts tau) p p1 /\ ts p1 l p2 /\ (ETS ts tau) p2 p'`
        by PROVE_TAC [WTS_def]
 >> `?q1. (ETS ts tau) q q1 /\ R p1 q1` by PROVE_TAC [lemma2]
 >> `?q2. (WTS ts tau) q1 l q2 /\ R p2 q2` by PROVE_TAC [WBISIM_def]
 >> `?q'. (ETS ts tau) q2 q' /\ R p' q'` by PROVE_TAC [lemma2]
 >> Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC ETS_WTS_ETS
 >> Q.EXISTS_TAC `q1`
 >> Q.EXISTS_TAC `q2`
 >> ASM_REWRITE_TAC []);

val lemma3' = prove (
  ``!q l q'. (WTS ts tau) q l q' /\ l <> tau ==>
             !R p. WBISIM ts tau R /\ R p q ==>
                   ?p'. (WTS ts tau) p l p' /\ R p' q'``,
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`q`, `l`, `q'`] lemma3) >> SRW_TAC[][]
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [inv_DEF]) o (Q.SPECL [`inv R`, `p`]))
 >> IMP_RES_TAC WBISIM_INV
 >> SRW_TAC[][]);

Theorem WBISIM_ID :
    !ts tau. WBISIM ts tau Id
Proof
    SRW_TAC[][WBISIM_def]
 >- (MATCH_MP_TAC TS_IMP_WTS >> ASM_REWRITE_TAC [])
 >> MATCH_MP_TAC TS_IMP_ETS >> ASM_REWRITE_TAC []
QED

Theorem WBISIM_O :
    !ts tau R R'. WBISIM ts tau R /\ WBISIM ts tau R' ==>
                  WBISIM ts tau (R' O R)
Proof
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [WBISIM_def]
 >> SRW_TAC[][O_DEF]
 >| [ METIS_TAC [WBISIM_def, lemma3],
      METIS_TAC [WBISIM_def, lemma3'],
      METIS_TAC [WBISIM_def, lemma2],
      METIS_TAC [WBISIM_def, lemma2'] ]
QED

Theorem WBISIM_RUNION :
    !ts tau R R'. WBISIM ts tau R /\ WBISIM ts tau R' ==>
                  WBISIM ts tau (R RUNION R')
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WBISIM_def]
 >> REWRITE_TAC [RUNION] >> BETA_TAC
 >> rpt STRIP_TAC
 >> RES_TAC (* 8 sub-goals here, the same last tactic *)
 >| [ Q.EXISTS_TAC `q'`, Q.EXISTS_TAC `p'`,
      Q.EXISTS_TAC `q'`, Q.EXISTS_TAC `p'`,
      Q.EXISTS_TAC `q'`, Q.EXISTS_TAC `p'`,
      Q.EXISTS_TAC `q'`, Q.EXISTS_TAC `p'` ]
 >> ASM_REWRITE_TAC []
QED

Theorem WBISIM_REL_IS_WBISIM :
    !ts tau. WBISIM ts tau (WBISIM_REL ts tau)
Proof
    PURE_ONCE_REWRITE_TAC [WBISIM_def]
 >> rpt GEN_TAC >> DISCH_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM WBISIM_REL_cases]
 >> ASM_REWRITE_TAC []
QED

(* Weak bisimilarity, the original definition *)
Theorem WBISIM_REL_def :
    !ts tau. WBISIM_REL ts tau = \p q. ?R. WBISIM ts tau R /\ R p q
Proof
    SRW_TAC[][FUN_EQ_THM]
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC >> Q.EXISTS_TAC `WBISIM_REL ts tau` \\
      ASM_REWRITE_TAC [WBISIM_REL_IS_WBISIM],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`q`, `q`) \\
      Q.SPEC_TAC (`p`, `p`) \\
      HO_MATCH_MP_TAC WBISIM_REL_coind \\ (* co-induction used here! *)
      PROVE_TAC [WBISIM_def] ]
QED

Theorem WBISIM_REL_IS_EQUIV_REL :
    !ts tau. equivalence (WBISIM_REL ts tau)
Proof
  SRW_TAC[][equivalence_def]
  >- (SRW_TAC[][reflexive_def, WBISIM_REL_def] \\
      Q.EXISTS_TAC `Id` \\
      SRW_TAC[][WBISIM_def, WBISIM_ID])
  >- (SRW_TAC[][symmetric_def, WBISIM_REL_def] \\
      SRW_TAC[][EQ_IMP_THM] \\
      Q.EXISTS_TAC `SC R` \\
      FULL_SIMP_TAC (srw_ss ()) [WBISIM_def, SC_DEF] \\
      METIS_TAC [])
  >- (SRW_TAC[][transitive_def, WBISIM_REL_def] >>
      Q.EXISTS_TAC `R' O R` \\
      METIS_TAC [WBISIM_O, O_DEF])
QED


(*---------------------------------------------------------------------------*)
(*  Relations between strong and weak bisimulations                          *)
(*---------------------------------------------------------------------------*)

Theorem BISIM_IMP_WBISIM :
    !ts tau R. BISIM ts R ==> WBISIM ts tau R
Proof
    SRW_TAC[][WBISIM_def] (* 4 goals *)
 >> IMP_RES_TAC BISIM_def
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TS_IMP_WTS,
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `p'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TS_IMP_WTS,
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TS_IMP_ETS,
      (* goal 4 (of 4) *)
      Q.EXISTS_TAC `p'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TS_IMP_ETS ]
 >> ASM_REWRITE_TAC []
QED

Theorem BISIM_REL_RSUBSET_WBISIM_REL :
    !ts tau. (BISIM_REL ts) RSUBSET (WBISIM_REL ts tau)
Proof
    SRW_TAC[][RSUBSET, BISIM_REL_def, WBISIM_REL_def]
 >> Q.EXISTS_TAC `R` >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC BISIM_IMP_WBISIM
 >> ASM_REWRITE_TAC []
QED

Theorem BISIM_REL_IMP_WBISIM_REL :
    !ts tau p q. (BISIM_REL ts) p q ==> (WBISIM_REL ts tau) p q
Proof
    REWRITE_TAC [GSYM RSUBSET, BISIM_REL_RSUBSET_WBISIM_REL]
QED

val _ = export_theory ();
