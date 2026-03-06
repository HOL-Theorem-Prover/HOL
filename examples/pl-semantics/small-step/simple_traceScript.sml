Theory simple_trace
Ancestors
  integer string alist list llist pred_set relation pair option
  finite_map arithmetic

Theorem hd_drop_last_take:
 !n l . 0 < n ∧ n ≤ LENGTH l ⇒ HD (DROP (n - 1) l) = LAST (TAKE n l)
Proof
 Induct >> rw[] >>
 Cases_on `l` >> fs[] >>
 Cases_on `n` >> fs[] >>
 Cases_on `t` >> fs[]
QED

Theorem some_no_choice:
 !f. (some x. f x) = NONE ⇔ ¬?x. f x
Proof
 rw [some_def]
QED

Theorem some_exists_determ:
 !f. (!x y. f x ∧ f y ⇒ x = y) ⇒ ((some x. f x) = SOME a ⇔ f a)
Proof
 rw [some_def] >>
 metis_tac []
QED

Definition monotone_def:
  monotone (f : num -> num) ⇔
    !x y. x ≤ y ⇒ f x ≤ f y
End

Definition unbounded_def:
  unbounded (f : num -> num) ⇔
    !x. ?y. x < f y
End



Definition check_trace_def:
  (check_trace step [] ⇔ T) ∧
  (check_trace step [s] ⇔ T) ∧
  (check_trace step (s1::s2::tr) ⇔
    step s1 = SOME s2 ∧
    check_trace step (s2::tr))
End

val check_trace_ind = fetch "-" "check_trace_ind";

Theorem check_trace_thm:
 !step s1 s2.
  (λs1 s2. step s1 = SOME s2)^* s1 s2 ⇔
  ?tr. tr ≠ [] ∧ HD tr = s1 ∧ LAST tr = s2 ∧ check_trace step tr
Proof
 rw [] >>
 eq_tac
 >- (
   qspec_tac (`s2`,`s2`) >>
   qspec_tac (`s1`,`s1`) >>
   ho_match_mp_tac RTC_INDUCT >>
   rw []
   >- (
     qexists_tac `[s1]` >>
     rw [check_trace_def])
   >- (
     qexists_tac `s1::tr` >>
     rw [LAST_DEF] >>
     Cases_on `tr` >>
     fs [check_trace_def])) >>
 rw [] >>
 Induct_on `tr` >>
 rw [LAST_DEF] >>
 fs [] >>
 Cases_on `tr` >>
 fs [check_trace_def] >>
 rw [Once RTC_CASES1]
QED

Theorem check_trace_append:
 !tr1 tr2.
  check_trace step (tr1 ++ tr2) ⇔
  if tr1 = [] then
    check_trace step tr2
  else if tr2 = [] then
    check_trace step tr1
  else
    check_trace step tr1 ∧ check_trace step tr2 ∧ step (LAST tr1) = SOME (HD tr2)
Proof
 Induct >>
 rw [] >>
 Cases_on `tr1` >>
 rw [check_trace_def]
 >- (
   Cases_on `tr2` >>
   fs [check_trace_def] >>
   metis_tac []) >>
 Cases_on `t` >>
 fs [check_trace_def] >>
 metis_tac []
QED

Theorem step_rel_determ:
 !s s1.
  (λs1 s2. step s1 = SOME s2)^* s s1 ⇒
  !s2. step s1 = NONE ∧ (λs1 s2. step s1 = SOME s2)^* s s2 ∧ step s2 = NONE
  ⇒
  s1 = s2
Proof
 ho_match_mp_tac RTC_INDUCT >>
 rw []
 >- (
   fs [Once RTC_CASES1] >>
   fs []) >>
 rw [] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 qpat_assum `r^* s s2` (assume_tac o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
 fs [] >>
 rw [] >>
 fs [] >>
 rw []
QED

Theorem trace_extends:
 !tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr < LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  step (LAST tr) ≠ NONE
Proof
 Induct_on `tr` >>
 rw [] >>
 Cases_on `tr'` >>
 fs [] >>
 Cases_on `tr` >>
 fs []
 >- (
   Cases_on `t` >>
   fs [check_trace_def])
 >- (
   Cases_on `t` >>
   fs [check_trace_def] >>
   rw [] >>
   first_x_assum (qspec_then `h'::t''` assume_tac) >>
   fs [])
QED

Theorem check_trace_append2:
 ∀f ls ls'.
 check_trace f ls ∧
 check_trace f ls' ∧
 f (LAST ls) = SOME (HD ls') ⇒
 check_trace f (ls++ls')
Proof
 ho_match_mp_tac check_trace_ind>>rw[]>>fs[check_trace_def]>>
 Cases_on`ls'`>>fs[check_trace_def]
QED

Theorem check_trace_drop:
 !tr n.
  check_trace step tr ∧
  n ≤ LENGTH tr
  ⇒
  check_trace step (DROP n tr)
Proof
 Induct_on `n` >>
 rw [] >>
 Cases_on `tr` >>
 fs [] >>
 first_x_assum (qspec_then `t` match_mp_tac) >>
 rw [] >>
 Cases_on `t` >>
 fs [check_trace_def]
QED

Theorem check_trace_twice_take:
 !tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr ≤ LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  TAKE (LENGTH tr) tr' = tr
Proof
 Induct_on `tr` >>
 simp [] >>
 gen_tac >>
 Cases_on `tr'` >>
 fs [] >>
 DISCH_TAC >>
 Cases_on `tr` >>
 Cases_on `t` >>
 fs [check_trace_def] >>
 fs [] >>
 rw [] >>
 first_x_assum (qspec_then `h'::t''` strip_assume_tac) >>
 rfs []
QED

Theorem check_trace_twice_suff:
 !tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr ≤ LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  HD (DROP (LENGTH tr - 1) tr') = (LAST tr)
Proof
 rw [] >>
 `TAKE (LENGTH tr) tr' = tr` by metis_tac [check_trace_twice_take] >>
 fs [] >>
 `0 < LENGTH tr ∧ LENGTH tr ≤ LENGTH tr'` by (rw [] >> Cases_on `tr` >> fs [] >> decide_tac) >>
 metis_tac [hd_drop_last_take]
QED

