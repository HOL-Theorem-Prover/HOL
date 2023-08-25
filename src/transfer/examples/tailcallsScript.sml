open HolKernel Parse boolLib bossLib;

val _ = new_theory "tailcalls";

Definition hascgd_def[simp]:
  (hascgd et [] x <=> F) /\
  (hascgd et ((pat,gd,rhs) :: rows) x <=>
   case PMATCH_ROW pat gd rhs x of
     SOME (INL cv) => T
   | SOME (INR tv) => F
   | _ => hascgd et rows x)
End

Definition execcgd_def[simp]:
  execcgd et [] x = x /\
  execcgd et ((pat,gd,rhs) :: rows) x =
  case PMATCH_ROW pat gd rhs x of
    SOME (INL cv) => cv
  | SOME (INR _) => x
  | NONE => execcgd et rows x
End

Definition exectmgd_def[simp]:
  exectmgd et [] x = et x /\
  exectmgd et ((pat,gd,rhs) :: rows) x =
  case PMATCH_ROW pat gd rhs x of
    SOME (INR tv) => tv
  | SOME (INL _) => et x
  | NONE => exectmgd et rows x
End

Definition trec_def:
  trec e f x = exectmgd e f (WHILE (hascgd e f) (execcgd e f) x)
End

Definition tcall_def[simp]:
  tcall et [] f x = et x /\
  (tcall et ((pat,gd,rhs) :: rest) f x =
   case PMATCH_ROW pat gd rhs x of
     SOME (INL cv) => f cv
   | SOME (INR tv) => tv
   | NONE => tcall et rest f x)
End

Theorem tcall_calls:
  !e opts x. hascgd e opts x ==>
             tcall e opts f x = f (execcgd e opts x)
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem tcall_terms:
  !e opts x. ~hascgd e opts x ==> tcall e opts f x = exectmgd e opts x
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem tcall_EQN:
  tcall e opts f x =
  if hascgd e opts x then f (execcgd e opts x)
  else exectmgd e opts x
Proof
  rw[]
  >- (drule tcall_calls >> simp[]) >>
  drule tcall_terms >> simp[]
QED

Theorem trec_thm0:
  trec e opts x = if hascgd e opts x then trec e opts (execcgd e opts x)
                  else exectmgd e opts x
Proof
  simp[trec_def] >> simp[SimpLHS, Once whileTheory.WHILE] >> rw[]
QED

Theorem trec_NIL[simp]:
  trec e [] x = e x
Proof
  simp[Once trec_thm0]
QED

Theorem trec_thm:
  !x. trec e opts x = tcall e opts (trec e opts) x
Proof
  strip_tac >>
  simp[Once trec_thm0] >> rw[]
  >- (drule tcall_calls >> simp[]) >>
  drule tcall_terms >> simp[]
QED

Theorem guard_elimination:
  (!x. P x /\ hascgd e opts x ==> P (execcgd e opts x)) /\
  (!x. P x ==>
       ?R. WFP R x /\
           !y. P y /\ R^* y x /\ hascgd e opts y ==>
               R (execcgd e opts y) y) /\
  (!x. P x ==> f x = tcall e opts f x) ==>
  (!x. P x ==> f x = trec e opts x)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘!x. P x ==> ?R. _’ (drule_then strip_assume_tac) >>
  qpat_x_assum ‘WFP R x’ (fn th => ntac 2 (pop_assum mp_tac) >> mp_tac th) >>
  qid_spec_tac ‘x’ >>
  ho_match_mp_tac relationTheory.WFP_STRONG_INDUCT >> rpt strip_tac >>
  simp[] >> simp[Once tcall_EQN]>> rw[]
  >- (simp[trec_thm] >> drule_then (simp o single) tcall_calls >>
      ‘P (execcgd e opts x)’ by metis_tac[] >>
      ‘tcall e opts f (execcgd e opts x) = f (execcgd e opts x)’ by simp[] >>
      pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
      rpt strip_tac >> first_assum irule >> simp[] >>
      irule (cj 2 relationTheory.RTC_RULES_RIGHT1) >>
      first_assum $ irule_at (Pat ‘RTC _ _ _’) >> first_assum irule >>
      simp[]) >>
  simp[trec_thm] >> drule tcall_terms >> simp[]
QED

Theorem guard_elimination_simpler:
  WF R /\
  (!x. hascgd e opts x ==> R (execcgd e opts x) x) /\
  (!x. P x /\ hascgd e opts x ==> P (execcgd e opts x)) /\
  (!x. P x ==> f x = tcall e opts f x) ==>
  (!x. P x ==> f x = trec e opts x)
Proof
  strip_tac >> MATCH_MP_TAC guard_elimination >> rw[] >>
  qexists ‘R’ >> gs[relationTheory.WF_EQ_WFP]
QED


Theorem COND_moveright:
  COND g1 (COND g2 t e1) e2 =
  COND (g1 /\ g2) t (COND g1 e1 e2)
Proof
  rw[] >> gs[]
QED

val _ = export_theory();
