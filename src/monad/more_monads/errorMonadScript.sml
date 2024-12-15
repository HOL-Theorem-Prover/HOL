open HolKernel Parse boolLib bossLib;

val _ = new_theory "errorMonad";

Datatype: error = return 'a | error 'e
End

Theorem EXISTS_ERROR:
  (?e:('a,'e)error. P e) <=> (?a. P (return a)) \/ (?e. P (error e))
Proof
  iff_tac >> strip_tac
  >- (Cases_on ‘e’ >> simp[] >> metis_tac[]) >>
  first_assum $ irule_at Any
QED

Theorem FORALL_ERROR:
  (!e:('a,'e)error. P e) <=> (!a. P (return a)) /\ !e. P (error e)
Proof
  simp[EQ_IMP_THM] >> strip_tac >> Cases >> simp[]
QED

Definition bind_def[simp]:
  bind (return v) f = f v /\
  bind (error e) f = error e
End

Definition choice_def:
  choice (return v) m = return v /\
  choice (error e) m = m
End

Definition guard_def:
  guard e b = if b then return () else error e
End

Theorem bind_return:
  bind m return = m
Proof
  Cases_on ‘m’ >> simp[]
QED

Theorem bind_EQ_return:
  bind m f = return v <=> ?u. m = return u /\ f u = return v
Proof
  Cases_on ‘m’ >> simp[]
QED

Theorem bind_EQ_error:
  bind m f = error e <=> m = error e \/ ?u. m = return u /\ f u = error e
Proof
  Cases_on ‘m’ >> simp[]
QED

val _ = monadsyntax.declare_monad("error",
  {bind = “bind”, choice = SOME “choice”, fail = SOME “error”,
   guard = SOME “guard”, ignorebind = NONE, unit = “return”})


val _ = export_theory();
