open HolKernel Parse boolLib bossLib;

open errorMonadTheory
val _ = new_theory "errorLogMonad";

Type M = “:('a,'e) error # 'w list”
  (* e for error, w for log or warning messages *)

Overload emret = “errorMonad$return”

Theorem M_CASES:
  !M. (?v ms. M = (emret v, ms)) \/ (?e ms. M = (error e, ms))
Proof
  metis_tac[TypeBase.nchotomy_of “:('a,'e)error”, pairTheory.pair_CASES]
QED

Definition return_def:
  return (v:'a) : ('a,'e,'w)M = (emret v, [])
End

Definition log_def:
  log (m : 'l) : (unit,'e,'l)M = (emret (), [m])
End

Definition error_def:
  error (e : 'e) : ('a,'e,'l) M = (errorMonad$error e, [])
End

Definition bind_def:
  bind (M:('a,'e,'l)M) (f:'a -> ('b,'e,'l)M) =
  case M of
  | (emret u, ms1) => (I ## APPEND ms1) (f u)
  | (error e, ms1) => (error e, ms1)
End

Theorem bind_IDL[simp]:
  bind (return (v:'a)) f : ('b,'e,'m) M = f v
Proof
  Cases_on ‘f v’ using M_CASES >>
  simp[bind_def, return_def]
QED

Theorem bind_IDR[simp]:
  bind (M:('a,'e,'l)M) return = M
Proof
  Cases_on ‘M’ using M_CASES >> simp[bind_def, return_def]
QED

Theorem bind_EQ_success:
  bind M f = (emret v, ms) <=> ?u ms0 ms1. M = (emret u, ms0) /\
                                           f u = (emret v, ms1) /\
                                           ms = ms0 ++ ms1
Proof
  Cases_on ‘M’ using M_CASES >> simp[bind_def, AllCaseEqs()] >>
  rename [‘(I ## _) (f v)’] >> Cases_on ‘f v’ using M_CASES >>
  simp[EQ_SYM_EQ]
QED

Definition silently_def:
  silently M = (I ## K []) M
End

Definition choice_def:
  choice M1 M2 =
  case M1 of
  | (emret v, ms1) => (emret v, ms1)
  | (error e, ms1) => (I ## APPEND ms1) M2
End

Theorem choice_return[simp]:
  choice (return v) M = return v
Proof
  simp[choice_def, return_def]
QED

val _ = monadsyntax.declare_monad ("errorLog", {
  unit = “errorLogMonad$return”,
  bind = “errorLogMonad$bind”,
  choice = SOME “errorLogMonad$choice”,
  guard = NONE,
  fail = SOME “errorLogMonad$error”,
  ignorebind = NONE
  });

val _ = export_theory();
