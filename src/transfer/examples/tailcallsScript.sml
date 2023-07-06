open HolKernel Parse boolLib bossLib;

val _ = new_theory "tailcalls";


(* ----------------------------------------------------------------------
    tailcall experiments
   ---------------------------------------------------------------------- *)

(* has an enabled "call" guard *)
Definition hascgd_def[simp]:
  (hascgd et [] x <=> F) /\
  (hascgd et (gcsum :: rest) x <=>
   case gcsum of
     INL (g, c) => g x \/ hascgd et rest x
   | INR (g, _) => ~g x /\ hascgd et rest x)
End

(* execute an enabled call guard *)
Definition execcgd_def[simp]:
  (execcgd et [] x = x) /\
  (execcgd et (gcsum :: rest) x =
   case gcsum of
     INL (g, c) => if g x then c x else execcgd et rest x
   | INR _ => execcgd et rest x)
End

Definition exectmgd_def[simp]:
  (exectmgd et [] x = et x) /\
  (exectmgd e (gcsum :: rest) x =
   case gcsum of
   | INL _ => exectmgd e rest x
   | INR (g, tm) => if g x then tm x else exectmgd e rest x)
End

Definition trec_def:
  trec e f x = exectmgd e f (WHILE (hascgd e f) (execcgd e f) x)
End

Definition tcall_def[simp]:
  tcall et [] f x = et x /\
  (tcall et (INL (g, c) :: rest) f x =
   if g x then f (c x)
   else tcall et rest f x) /\
  (tcall et (INR (g, tm) :: rest) f x =
   if g x then tm x
   else tcall et rest f x)
End

Theorem tcall_calls:
  !e opts x. hascgd e opts x ==>
             tcall e opts f x = f (execcgd e opts x)
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rw[]
QED

Theorem tcall_terms:
  !e opts x. ¬hascgd e opts x ==> tcall e opts f x = exectmgd e opts x
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rw[]
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
  WF R /\ (!s. hascgd e opts s ==> R (execcgd e opts s) s) ==>
  !x. trec e opts x = tcall e opts (trec e opts) x
Proof
  strip_tac >>
  first_assum (ho_match_mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  rpt strip_tac >>
  simp[Once trec_thm0] >> rw[]
  >- (drule tcall_calls >> simp[]) >>
  drule tcall_terms >> simp[]
QED

Definition callsites_def[simp]:
  (callsites P [] <=> T) /\
  (callsites P (INR (g, tm) :: rest) <=>
   callsites (λx. P x /\ ~g x) rest) /\
  (callsites P (INL (g, c) :: rest) <=>
   (!x. P x /\ g x ==> P (c x)) /\
   callsites (λx. P x /\ ~g x) rest)
End

Theorem callsites_exec0:
  !P Q. callsites P opts /\ (!x. P x ==> Q x) ==>
        !x. P x /\ hascgd e opts x ==> Q (execcgd e opts x)
Proof
  Induct_on ‘opts’
  >- simp[] >>
  simp_tac (srw_ss())[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rpt strip_tac
  >- (COND_CASES_TAC >- metis_tac[] >> fs[])
  >- (COND_CASES_TAC >- metis_tac[] >> last_x_assum irule >> simp[] >>
      first_assum $ irule_at (Pat ‘callsites _ _’) >> simp[]) >>
  last_x_assum irule >> simp[] >>
  first_assum $ irule_at (Pat ‘callsites _ _’) >> simp[]
QED

Theorem callsites_exec = callsites_exec0 |> Q.SPECL[‘P’, ‘P’] |> SRULE[]

Theorem guard_elimination:
  WF R /\
  (!x. hascgd e opts x ==> R (execcgd e opts x) x) /\
  (!x. P x /\ hascgd e opts x ==> P (execcgd e opts x)) /\
  (!x. P x ==> f x = tcall e opts f x) ==>
  (!x. P x ==> f x = trec e opts x)
Proof
  strip_tac >>
  first_assum (ho_match_mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  rw[] >> rw[tcall_EQN]
  >- (drule_all trec_thm >> disch_then (fn th => simp[SimpRHS, th]) >>
      simp[tcall_EQN]) >>
  drule_all trec_thm >> disch_then (fn th => simp[SimpRHS, th]) >>
  simp[tcall_EQN]
QED

val _ = export_theory();
