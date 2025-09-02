open HolKernel boolLib bossLib Parse;
open integerTheory stringTheory alistTheory listTheory llistTheory pred_setTheory relationTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;

val _ = new_theory "simple_trace";

val hd_drop_last_take = Q.store_thm ("hd_drop_last_take",
`!n l . 0 < n ∧ n ≤ LENGTH l ⇒ HD (DROP (n - 1) l) = LAST (TAKE n l)`,
 Induct >> rw[] >>
 Cases_on `l` >> fs[] >>
 Cases_on `n` >> fs[] >>
 Cases_on `t` >> fs[]
);

val some_no_choice = Q.store_thm ("some_no_choice",
`!f. (some x. f x) = NONE ⇔ ¬?x. f x`,
 rw [some_def]);

val some_exists_determ = Q.store_thm ("some_exists_determ",
`!f. (!x y. f x ∧ f y ⇒ x = y) ⇒ ((some x. f x) = SOME a ⇔ f a)`,
 rw [some_def] >>
 metis_tac []);

val monotone_def = Define `
  monotone (f : num -> num) ⇔
    !x y. x ≤ y ⇒ f x ≤ f y`;

val unbounded_def = Define `
  unbounded (f : num -> num) ⇔
    !x. ?y. x < f y`;



val check_trace_def = Define `
  (check_trace step [] ⇔ T) ∧
  (check_trace step [s] ⇔ T) ∧
  (check_trace step (s1::s2::tr) ⇔
    step s1 = SOME s2 ∧
    check_trace step (s2::tr))`;

val check_trace_ind = fetch "-" "check_trace_ind";

val check_trace_thm = Q.store_thm ("check_trace_thm",
`!step s1 s2.
  (λs1 s2. step s1 = SOME s2)^* s1 s2 ⇔
  ?tr. tr ≠ [] ∧ HD tr = s1 ∧ LAST tr = s2 ∧ check_trace step tr`,
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
 rw [Once RTC_CASES1]);

val check_trace_append = Q.store_thm ("check_trace_append",
`!tr1 tr2.
  check_trace step (tr1 ++ tr2) ⇔
  if tr1 = [] then
    check_trace step tr2
  else if tr2 = [] then
    check_trace step tr1
  else
    check_trace step tr1 ∧ check_trace step tr2 ∧ step (LAST tr1) = SOME (HD tr2)`,
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
 metis_tac []);

val step_rel_determ = Q.store_thm ("step_rel_determ",
`!s s1.
  (λs1 s2. step s1 = SOME s2)^* s s1 ⇒
  !s2. step s1 = NONE ∧ (λs1 s2. step s1 = SOME s2)^* s s2 ∧ step s2 = NONE
  ⇒
  s1 = s2`,
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
 rw []);

val trace_extends = Q.store_thm ("trace_extends",
`!tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr < LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  step (LAST tr) ≠ NONE`,
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
   fs []));

val check_trace_append2 = Q.store_thm ("check_trace_append2",
`∀f ls ls'.
 check_trace f ls ∧
 check_trace f ls' ∧
 f (LAST ls) = SOME (HD ls') ⇒
 check_trace f (ls++ls')`,
 ho_match_mp_tac check_trace_ind>>rw[]>>fs[check_trace_def]>>
 Cases_on`ls'`>>fs[check_trace_def])

val check_trace_drop = Q.store_thm ("check_trace_drop",
`!tr n.
  check_trace step tr ∧
  n ≤ LENGTH tr
  ⇒
  check_trace step (DROP n tr)`,
 Induct_on `n` >>
 rw [] >>
 Cases_on `tr` >>
 fs [] >>
 first_x_assum (qspec_then `t` match_mp_tac) >>
 rw [] >>
 Cases_on `t` >>
 fs [check_trace_def]);

val check_trace_twice_take = Q.store_thm ("check_trace_twice_take",
`!tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr ≤ LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  TAKE (LENGTH tr) tr' = tr`,
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
 rfs []);

val check_trace_twice_suff = Q.store_thm ("check_trace_twice_suff",
`!tr tr'.
  tr ≠ [] ∧ tr' ≠ [] ∧
  HD tr = HD tr' ∧
  LENGTH tr ≤ LENGTH tr' ∧
  check_trace step tr ∧
  check_trace step tr'
  ⇒
  HD (DROP (LENGTH tr - 1) tr') = (LAST tr) `,
 rw [] >>
 `TAKE (LENGTH tr) tr' = tr` by metis_tac [check_trace_twice_take] >>
 fs [] >>
 `0 < LENGTH tr ∧ LENGTH tr ≤ LENGTH tr'` by (rw [] >> Cases_on `tr` >> fs [] >> decide_tac) >>
 metis_tac [hd_drop_last_take]);

val _ = export_theory ();
