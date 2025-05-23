open HolKernel boolLib bossLib Parse stringTheory alistTheory pairTheory
     monadsyntax listTheory rich_listTheory

val () = new_theory "gh1431";

Definition return_def:
  return x s = (INL x, s)
End

Definition raise_def:
  raise e s = (INR e, s)
End

Definition bind_def:
  bind f g s =
  case f s of (INL x, s) => g x s | (INR e, s) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

Definition assert_def:
  assert b e s = ((if b then INL () else INR e), s)
End

val () = declare_monad ("mwe",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = SOME “assert”
  });
val () = enable_monad "mwe";
val () = enable_monadsyntax();

Datatype:
  dat = Dats (dat list) | Num num
End

Definition lift_opt_def:
  lift_opt x s = case x of NONE => raise s | SOME v => return v
End

Theorem bind_cong[defncong]:
  (s = s') ∧
  (f s' = f' s') ∧
  (∀x t. f' s' = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g s = bind f' g' s'
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem bind_cong_implicit:
  (!s. f s = f' s) ∧
  (∀s x t. f' s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

Theorem bind_cong_implicit_hyp[defncong]:
  (f = f') ∧
  (∀s x. FST $ f s = INL x ==> g x = g' x)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule
  \\ metis_tac[FST]
QED

Definition datcount_def[simp]:
  datcount (Dats ds) = 2 + SUM (MAP datcount ds)  ∧
  datcount _ = 1
End

Overload dcalist = “λas. LENGTH as + SUM (MAP (datcount o SND) as)”

Theorem LENGTH_FILTER_unchanged:
  LENGTH (FILTER P l) = LENGTH l ⇔ ∀x. MEM x l ⇒ P x
Proof
  Induct_on ‘l’ >> simp[] >> rw[] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  qspecl_then [‘P’, ‘l’] assume_tac LENGTH_FILTER_LEQ >>
  simp[]
QED

Theorem SUM_MAP_FILTER_LEQ:
  SUM (MAP f (FILTER P l)) ≤ SUM (MAP f l)
Proof
  Induct_on ‘l’ >> rw[]
QED

Definition mwe:
  mwe ns n = do
    x <- return n;
    d <- lift_opt (ALOOKUP ns n) "lookup";
    mwd (ADELKEY n ns) d
  od ∧
  mwd ns (Num n) = mwe ns n ∧
  mwd ns (Dats ds) = mwds ns ds ∧
  mwds ns [] = return T ∧
  mwds ns (d::ds) = do
    x <- mwd ns d;
    xs <- mwds ns ds;
    return (x ∧ xs)
  od
Termination
  (* There may also be a lexicographic ordering that shows
     termination where you privilege the length of the ns alist. Then you
     still need to know the d in the mwe clause has come from ns because
     this is what guarantees that ADELKEY has made ns smaller.
  *)
  WF_REL_TAC
  ‘measure
   (λs. case s of
        | INL (ns,n) => dcalist ns
        | INR (INL (ns,d)) => dcalist ns + datcount d
        | INR (INR (ns,ds)) => dcalist ns + SUM (MAP datcount ds) + 1)’ >>
  simp[SF ETA_ss] >> rpt strip_tac
  >- (Cases_on ‘d’ >> simp[]) >>
  (* now use fact that we know d in mwe clause has been pulled from ns *)
  irule (DECIDE “x < a ∧ y ≤ b ⇒ x + y < a + b”) >> conj_tac
  >- (simp[ADELKEY_def] >> qmatch_abbrev_tac ‘LENGTH (FILTER P _) < _’ >>
      rename [‘_ < LENGTH alist’] >>
      ‘LENGTH (FILTER P alist) ≤ LENGTH alist’
        by simp[LENGTH_FILTER_LEQ] >>
      gvs[DECIDE “(m:num) ≤ n ⇔ m = n ∨ m < n”, LENGTH_FILTER_unchanged] >>
      gvs[lift_opt_def] >> Cases_on ‘ALOOKUP alist n’ >>
      gvs[raise_def, return_def] >> drule_then assume_tac ALOOKUP_MEM >>
      gvs[Abbr‘P’] >> metis_tac[FST]) >>
  gvs[lift_opt_def] >> rename [‘ALOOKUP alist n’] >>
  Cases_on ‘ALOOKUP alist n’ >> gvs[raise_def, return_def] >>
  drule_then assume_tac ALOOKUP_MEM >>
  pop_assum (strip_assume_tac o
             ONCE_REWRITE_RULE[MEM_SPLIT_APPEND_first])>>
  gvs[ADELKEY_def, FILTER_APPEND_DISTRIB, SUM_APPEND] >>
  simp[DECIDE “x + (y + z) ≤ a + (b + z) ⇔ x + y ≤ a + b”] >>
  irule (DECIDE “x ≤ a ∧ y ≤ b ⇒ x + y ≤ a + b”) >>
  simp[SUM_MAP_FILTER_LEQ]
End


(*
  The termination conditions weren't strong enough here:

    (∀ns n s x d.
       FST (return n s) = INL x ⇒ R (INR (INL (ADELKEY n ns,d))) (INL (ns,n))) ∧

  we need to know where `d` came from.

  Then the proof would measure the total size of all the dats in ns
*)

val _ = export_theory()
