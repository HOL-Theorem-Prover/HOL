open HolKernel Parse boolLib bossLib;

val _ = new_theory "tailcalls";

Definition trec_def:
  trec c x = OUTR $ c (WHILE (ISL o c) (OUTL o c) x)
End

Definition tcall_def:
  tcall t cf x =
   case t x of
     INL cv => cf cv
   | INR tv => tv
End

Theorem trec_thm:
  !x. trec opts x = tcall opts (trec opts) x
Proof
  simp[tcall_def, trec_def] >> gen_tac >> Cases_on ‘opts x’ >> simp[] >>
  simp[SimpLHS, Once whileTheory.WHILE]
QED

Theorem guard_elimination:
  (!x y. P x /\ c x = INL y ==> P y) /\
  (!x. P x ==>
       ?R. WFP R x /\ !y z. P y /\ R^* y x /\ c y = INL z ==> R z y) /\
  (!x. P x ==> f x = tcall c f x) ==>
  (!x. P x ==> f x = trec c x)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘!x. P x ==> ?R. _’ (drule_then strip_assume_tac) >>
  qpat_x_assum ‘WFP R x’ (fn th => ntac 2 (pop_assum mp_tac) >> mp_tac th) >>
  qid_spec_tac ‘x’ >>
  ho_match_mp_tac relationTheory.WFP_STRONG_INDUCT >> rpt strip_tac >>
  simp[] >> simp[tcall_def] >>
  Cases_on ‘c x’ >> simp[]
  >- (simp[trec_thm] >> simp[tcall_def] >>
      first_x_assum irule >> simp[] >>
      rpt strip_tac >> first_assum irule >> simp[]
      >- metis_tac[] >>
      irule (cj 2 relationTheory.RTC_RULES_RIGHT1) >>
      first_assum $ irule_at (Pat ‘RTC _ _ _’) >> first_assum irule >>
      simp[]) >>
  simp[trec_thm] >> simp[tcall_def]
QED

Theorem guard_elimination_simpler:
  WF R /\
  (!x y. c x = INL y ==> R y x) /\
  (!x y. P x /\ c x = INL y ==> P y) /\
  (!x. P x ==> f x = tcall c f x) ==>
  (!x. P x ==> f x = trec c x)
Proof
  strip_tac >> MATCH_MP_TAC guard_elimination >> rw[]
  >- metis_tac[] >>
  qexists ‘R’ >> gs[relationTheory.WF_EQ_WFP]
QED

val _ = export_theory();
