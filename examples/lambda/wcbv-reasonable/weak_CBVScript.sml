(* See:
     Forster, Kunze and Roth,
     "The Weak Call-by-Value 𝜆-Calculus Is Reasonable for Both Time and Space", POPL 2020
   for inspiration
*)

(* Added assumptions for closed terms for some theorems (commented)
    due to the difference between
      how substitutions are defined
        in HOL library and in Forster etc.'s Coq proof *)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory combinTheory;

open PrelimsTheory;
open pure_dBTheory;

val _ = new_theory "weak_CBV";

(* ------------------
              CBV LC
   ------------------ *)

Definition size:
        size s =
                case s of
                        | dV x => 1 + x
                        | dABS s => 1 + (size s)
                        | dAPP s t => 1 + size s + size t
End

(* --------------------------------
          Substitution and Closedness
   -------------------------------- *)

Overload subst = “\s k u. sub u k s”

Theorem size_eqs:
  size (dV x) = 1 + x ∧
  size (dABS s) = 1 + size s ∧
  size (dAPP s t) = 1 + size s + size t
Proof
  rw[] >> rw[Once size]
QED

Inductive bound:
        (∀k n. n < k ⇒ bound k (dV n)) ∧
        (∀k s t. bound k s ∧ bound k t ⇒ bound k (dAPP s t)) ∧
        (∀k s. bound (SUC k) s ⇒ bound k (dABS s))
End

Definition closed:
        closed s = bound 0 s
End

Theorem lift_bound:
  ∀n s. bound n s ⇒ (lift s n = s)
Proof
  Induct_on `s` >>
  rw[lift_def]
  >- rw[Once bound_cases] >>
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[bound_cases]) >>
  gvs[] >> metis_tac[ADD1]
QED

Theorem lift_closed:
  closed s ⇒ (lift s 0 = s)
Proof
  strip_tac >> match_mp_tac lift_bound >> fs[closed]
QED

Definition lambda:
        lambda s = ∃t. s = dABS t
End

Theorem lambda_lam:
        lambda (dABS s)
Proof
        rw[lambda]
QED

Theorem bound_closed_k:
        ∀s k u. bound k s ⇒ subst s k u = s
Proof
        Induct_on `s` >> rw[]
  >- fs[Once bound_cases]
  >- (pop_assum mp_tac >> rw[Once bound_cases])
  >- (pop_assum mp_tac >> rw[Once bound_cases])
  >> pop_assum mp_tac >> rw[Once bound_cases] >>
  fs[ADD1]
QED

Theorem bound_ge:
        ∀k s. bound k s ⇒ ∀m. k ≤ m ⇒ bound m s
Proof
        Induct_on `s` >> rw[]
        >- fs[Once bound_cases]
        >- (qpat_x_assum (`bound _ _`) mp_tac >>
                rw[Once bound_cases] >>
                first_x_assum drule_all >> rw[] >>
                first_x_assum drule_all >> rw[] >>
                rw[Once bound_cases])
        >> qpat_x_assum (`bound _ _`) mp_tac >>
        rw[Once bound_cases] >>
        first_x_assum drule >> rw[] >>
        rw[Once bound_cases]
QED

Theorem bound_closed:
        ∀s k u. bound 0 s ⇒ subst s k u = s
Proof
  rw[] >> drule bound_ge >> rw[] >>
  metis_tac[bound_closed_k]
QED

(* Took ``Forall u`` out of the parenthesis and moved it up to the outter most level.
   Added ``closed u`` as an extra assumption *)
Theorem closed_k_bound:
        ∀k s u.
    closed u ⇒
    (∀n. k ≤ n ⇒ subst s n u = s) ⇒
    bound k s
Proof
        Induct_on `s` >> rw[]
  >- (Cases_on `k ≤ n` >> rw[]
      >- (first_x_assum drule  >> rw[] >>
          fs[closed, Once bound_cases])
      >> fs[NOT_LEQ] >> rw[Once bound_cases])
  >- (last_x_assum drule >> rw[] >>
      last_x_assum drule >> rw[] >>
      rw[Once bound_cases])
        >> rw[Once bound_cases, ADD1] >>
  first_x_assum irule >> rw[] >>
  qexists_tac `u` >> rw[] >>
  drule lift_closed >> rw[] >>
  fs[] >>
  first_x_assum (qspec_then `n - 1` mp_tac) >> rw[]
QED

(* Took ``Forall t`` out of the parenthesis and moved it up to the outter most level.
   Added ``closed t`` on both sides of the theorem *)
Theorem closed_subst_iff:
  ∀s t. closed s ∧ closed t ⇔ closed t ∧ (∀k. subst s k t = s)
Proof
  rw[EQ_IMP_THM, closed]
  >- metis_tac[bound_closed]
  >> metis_tac[closed_k_bound, closed]
QED

(* Took ``Forall t`` out of the parenthesis and moved it up to the outter most level.
   Added ``closed t`` on the LHS of the theorem *)
Theorem closed_subst:
  ∀s t. closed s ∧ closed t ⇒ (∀k. subst s k t = s)
Proof
  metis_tac[closed_subst_iff]
QED

Theorem closed_app:
  ∀s t. closed (dAPP s t) ⇒ closed s ∧ closed t
Proof
  rw[closed, Once bound_cases]
QED

Theorem app_closed:
  ∀s t. closed s ⇒ closed t ⇒ closed (dAPP s t)
Proof
  rw[closed] >> rw[Once bound_cases]
QED

(* Added ``closed t`` *)
Theorem bound_subst:
  ∀s t k.
    closed t ⇒
    bound (SUC k) s ⇒
    bound k t ⇒
    bound k (subst s k t)
Proof
  Induct_on `s` >> rw[]
  >- fs[Once bound_cases]
  >- (rw[Once bound_cases] >>
      qpat_x_assum `bound (SUC _) _` mp_tac >>
      rw[Once bound_cases])
  >> rw[Once bound_cases] >>
  qpat_x_assum `bound (SUC _) _` mp_tac >>
  rw[Once bound_cases] >>
  drule lift_closed >> rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  `bound (SUC k) t` by (irule bound_ge >> qexists_tac `k` >> rw[]) >>
  metis_tac[ADD1]
QED

Theorem closed_subst2:
  ∀s t. closed (dABS s) ⇒ closed t ⇒ closed (subst s 0 t)
Proof
  rw[closed] >>
  irule bound_subst >> rw[closed] >>
  qpat_x_assum `bound _ (dABS _)` mp_tac >> rw[Once bound_cases]
QED

(* ----------------------------
          Deterministic Reduction
   ---------------------------- *)

Inductive step:
[~App:]
        (∀s t. step (dAPP (dABS s) (dABS t)) (subst s 0 (dABS t)))
[~AppR:]
        (∀s t t'. step t t' ⇒ step (dAPP (dABS s) t) (dAPP (dABS s) t'))
[~AppL:]
        (∀s s' t. step s s' ⇒ step (dAPP s t) (dAPP s' t))
End

(* -----------------------
           Resource Measures
   ----------------------- *)

(* -- Small-Step Time Measure -- *)

Theorem NRC_step_congL:
  W (respectful (NRC step k) (respectful ($=) (NRC step k))) dAPP
Proof
  Induct_on `k` >> rw[]
  >- rw[respectful, NRC]
  >> fs[respectful, NRC] >> rw[] >>
  qexists_tac `dAPP z y'` >> rw[] >>
  rw[Once step_cases]
QED

Theorem NRC_step_congR:
  W (respectful ($=) (respectful (NRC step k) (NRC step k))) (λs t. dAPP (dABS s) t)
Proof
  Induct_on `k` >> rw[]
  >- rw[respectful]
  >> fs[respectful] >> rw[] >>
  fs[Once NRC] >>
  first_x_assum drule >> rw[] >>
  first_x_assum (qspecl_then [`y`] ASSUME_TAC) >>
  qexists_tac `(dAPP (dABS y) z)` >> rw[] >>
  rw[Once step_cases]
QED

(* -- Small-Step Space Measure -- *)

Definition redWithMaxSizeL:
        redWithMaxSizeL = redWithMaxSize size step
End

Theorem redWithMaxSizeL_congL:
  ∀m m' s s' t.
    redWithMaxSizeL m s s' ⇒
    m' = 1 + m + size t ⇒
    redWithMaxSizeL m' (dAPP s t) (dAPP s' t)
Proof
  simp[redWithMaxSizeL] >>
  Induct_on `redWithMaxSize` >> rw[]
  >- (irule redWithMaxSize_R >>
      `size (dAPP s t) = size s + (size t + 1)` suffices_by simp[] >>
      rw[Once size])
  >> irule redWithMaxSize_C >>
  qexistsl_tac [`(m' + (size t + 1))`, `dAPP s' t`] >> rw[]
  >- rw[Once step_cases]
  >> `MAX (size (dAPP s t)) (m' + (size t + 1))
      = size t + (MAX (size s) m' + 1)` suffices_by simp[] >>
  rw[Once size] >> rw[MAX_DEF]
QED

Theorem redWithMaxSizeL_redWithMaxSize_congL:
  ∀m m' s s' t.
    redWithMaxSize size step m s s' ⇒
    m' = 1 + m + size t ⇒
    redWithMaxSize size step m' (dAPP s t) (dAPP s' t)
Proof
  metis_tac[redWithMaxSizeL_congL, redWithMaxSizeL]
QED

Theorem redWithMaxSizeL_congR:
  ∀m m' s t t'.
    redWithMaxSizeL m t t' ⇒
    m' = (1 + m + size (dABS s)) ⇒
    redWithMaxSizeL m' (dAPP (dABS s) t) (dAPP (dABS s) t')
Proof
  simp[redWithMaxSizeL] >>
  Induct_on `redWithMaxSize` >> rw[]
  >- (irule redWithMaxSize_R >>
      `size (dAPP (dABS s) t) = size t + (size (dABS s) + 1)` suffices_by simp[] >>
      rw[Once size])
  >> irule redWithMaxSize_C >>
  qexistsl_tac [`(m' + (size (dABS s) + 1))`, `(dAPP (dABS s) t')`] >> rw[]
  >- rw[Once step_cases]
  >> `MAX (size (dAPP (dABS s) t)) (m' + (size (dABS s) + 1))
      = size (dABS s) + (MAX (size t) m' + 1)` suffices_by simp[] >>
  rw[Once size] >> rw[MAX_DEF]
QED

Theorem redWithMaxSizeL_redWithMaxSize_congR:
  ∀m m' s t t'.
    redWithMaxSize size step m t t' ⇒
    m' = (1 + m + size (dABS s)) ⇒
    redWithMaxSize size step m' (dAPP (dABS s) t) (dAPP (dABS s) t')
Proof
  metis_tac[redWithMaxSizeL_congR, redWithMaxSizeL]
QED

(* -- Big-Step Time Measure -- *)

Inductive timeBS:
[~Val:]
  (∀s. timeBS (0:num) (dABS s) (dABS s))
[~Beta:]
  (∀s s' t t' u i j k l.
    timeBS i s (dABS s') ∧
    timeBS j t (dABS t') ∧
    timeBS k (subst s' 0 (dABS t')) u ∧
    l = i+j+1+k ⇒
    timeBS l (dAPP s t) u)
End

Theorem closed_timeBS:
  ∀k s t.
    closed s ⇒
    timeBS k s t ⇒
    closed t
Proof
  Induct_on `timeBS` >> rw[] >>
  first_x_assum irule >>
  drule closed_app >> rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  metis_tac[closed_subst2]
QED

Theorem step_evaluatesIn:
  ∀s s' t k.
    step s s' ⇒
    timeBS k s' t ⇒
    timeBS (SUC k) s t
Proof
  Induct_on `step` >> rw[]
  >- (rw[Once timeBS_cases] >>
      irule_at (Pos hd) timeBS_Val >>
      irule_at (Pos hd) timeBS_Val >>
      rw[ADD1])
  >- (rw[Once timeBS_cases] >>
      pop_assum mp_tac >> rw[Once timeBS_cases] >>
      goal_assum drule >>
      first_x_assum drule >> rw[] >>
      goal_assum drule >>
      goal_assum drule >>
      rw[])
  >> rw[Once timeBS_cases] >>
  pop_assum mp_tac >> rw[Once timeBS_cases] >>
  first_x_assum drule >> rw[] >>
  goal_assum drule >>
  goal_assum drule >>
  goal_assum drule >>
  rw[]
QED

Theorem timeBS_correct:
  ∀s t k. timeBS k s t ⇔ NRC step k s t ∧ lambda t
Proof
  rw[lambda] >> EQ_TAC
  >- (Induct_on `timeBS` >> rw[] >>
      (* s s'' ---<k>---> (\s') s'' *)
      irule NRC_ADD_EQN_R >>
      qexists_tac `dAPP (dABS s') s''` >> rw[]
      >- (`W (respectful (NRC step k) (respectful ($=) (NRC step k))) dAPP`
            by metis_tac[NRC_step_congL] >> fs[respectful]) >>
      (* (\s') s'' ---<k'>---> (\s') (\t') *)
      irule NRC_ADD_EQN_R >>
      qexists_tac `(dAPP (dABS s') (dABS t'))` >> rw[]
      >- (`W (respectful ($=) (respectful (NRC step k') (NRC step k')))
           (λs t. dAPP (dABS s) t)`
            by metis_tac[NRC_step_congR] >>
          fs[respectful]) >>
      (* (\s') (\t') ---<1>---> subst ... *)
      `NRC step (SUC k'') (dAPP (dABS s') (dABS t')) (dABS t'')`
        suffices_by simp[ADD1] >>
      rw[NRC] >> qexists_tac `subst s' 0 (dABS t')` >>
      rw[] >> rw[Once step_cases])
  >> MAP_EVERY qid_spec_tac [`k`, `s`, `t`] >>
  Induct_on `k` >> rw[]
  >- fs[Once timeBS_cases, NRC, Once step_cases]
  >> irule step_evaluatesIn >>
  pop_assum mp_tac >> rw[Once NRC] >>
  qexists_tac `z` >> rw[]
QED

(* -- Big-Step Space Measure -- *)

Inductive spaceBS:
[~Val:]
  (∀s. spaceBS (size (dABS s)) (dABS s) (dABS s))
[~Beta:]
  (∀s s' t t' u m1 m2 m3 m.
    spaceBS m1 s (dABS s') ∧
    spaceBS m2 t (dABS t')  ∧
    spaceBS m3 (subst s' 0 (dABS t')) u ∧
    m = MAX (m1 + 1 + size t)
            (MAX (size (dABS s') + 1 + m2) m3) ⇒
    spaceBS m (dAPP s t) u)
End

Theorem closed_spaceBS:
  ∀k s t.
    closed s ⇒
    spaceBS k s t ⇒
    closed t
Proof
  Induct_on `spaceBS` >> rw[] >>
  first_x_assum irule >>
  drule closed_app >> rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  metis_tac[closed_subst2]
QED

Theorem spaceBS_ge:
  ∀s t m.
    spaceBS m s t ⇒ size s ≤ m ∧ size t ≤ m
Proof
  Induct_on `spaceBS` >> rw[] >>
  rw[Once size]
QED

Theorem step_evaluatesSpace:
  ∀s s' t m.
    step s s' ⇒
    spaceBS m s' t ⇒
    spaceBS (MAX (size s) m) s t
Proof
  Induct_on `step` >> rw[]
  >- (rw[Once spaceBS_cases] >>
      irule_at (Pos hd) spaceBS_Val >>
      irule_at (Pos hd) spaceBS_Val >>
      goal_assum drule >> rw[MAX_DEF]
      >- (fs[NOT_LESS] >> fs[Once size] >>
          qpat_x_assum `size _ + _ < _` mp_tac >>
          rw[Once size])
      >- (fs[NOT_LESS] >> fs[Once size] >>
          qpat_x_assum `m ≤ _` mp_tac >>
          rw[Once size])
      >> fs[NOT_LESS] >> fs[Once size])
  >- (rw[Once spaceBS_cases] >>
      pop_assum mp_tac >> rw[Once spaceBS_cases] >>
      goal_assum drule >>
      first_x_assum drule >> rw[] >>
      goal_assum drule >>
      goal_assum drule >>
      qpat_x_assum `spaceBS _ (dABS _) (dABS _)` mp_tac >>
      rw[Once spaceBS_cases] >>
      `size s'' ≤ m2 ∧ size (dABS t'') ≤ m2`
        by metis_tac[spaceBS_ge] >> rw[] >>
      `size (subst s 0 (dABS t'')) ≤ m3 ∧ size t ≤ m3`
        by metis_tac[spaceBS_ge] >> rw[] >>
      `size s' ≤ (MAX (size s') m2) ∧ size (dABS t'') ≤ (MAX (size s') m2)`
        by metis_tac[spaceBS_ge] >> rw[] >>
      `size (dABS s) = 1 + size s`
        by rw[Once size] >> rw[] >>
      `size (dAPP (dABS s) s') = 1 + (1 + size s) + size s'`
        by rw[Once size] >> rw[] >>
      `1 + size t'' ≤ MAX (size s') m2`
        by fs[Once size] >>
      pop_assum mp_tac >>
      rw[MAX_DEF])
  >> rw[Once spaceBS_cases] >>
  pop_assum mp_tac >> rw[Once spaceBS_cases] >>
  rename [`spaceBS m1 s' (dABS s'')`,
          `spaceBS m2 t (dABS t')`,
          `spaceBS m3 (subst s'' 0 (dABS t')) u`] >>
  first_x_assum drule >> rw[] >>
  goal_assum drule >>
  goal_assum drule >>
  goal_assum drule >>
  rw[Once size] >>
  `size (dABS s'') = 1 + size s''`
    by rw[Once size] >> rw[] >>
  first_x_assum (qspecl_then [] (K all_tac)) >>
  rw[MAX_ASSOC] >> rw[MAX_DEF]
QED

Theorem spaceBS_correctL:
  ∀s t m.
    spaceBS m s t ⇒
      redWithMaxSizeL m s t ∧ lambda t
Proof
  Induct_on `spaceBS` >> rw[]
  >- rw[redWithMaxSizeL, Once redWithMaxSize_cases]
  >- rw[lambda]
  >> fs[redWithMaxSizeL] >>
  irule redWithMaxSize_trans >>
  irule_at Any redWithMaxSizeL_redWithMaxSize_congL >> rw[] >>
  goal_assum drule >>
  (* irule_at (Pos hd) EQ_REFL >> *)
  irule_at Any redWithMaxSize_trans >>
  irule_at Any redWithMaxSizeL_redWithMaxSize_congR >> rw[] >>
  goal_assum drule >>
  (* irule_at (Pos hd) EQ_REFL >> *)
  rw[Once redWithMaxSize_cases] >>
  rw[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  DISJ2_TAC >> rw[PULL_EXISTS] >>
  goal_assum $ drule_at Any >> rw[]
  >- rw[Once step_cases] >>
  `size (dABS t') ≤ m'` by metis_tac[spaceBS_ge] >>
  fs[size_eqs] >> intLib.COOPER_TAC
QED

Theorem spaceBS_correctR:
  ∀s t m.
    redWithMaxSizeL m s t ∧ lambda t ⇒
      spaceBS m s t
Proof
  simp[redWithMaxSizeL] >>
  Induct_on `redWithMaxSize` >> rw[]
  >- fs[lambda, Once spaceBS_cases]
  >> irule step_evaluatesSpace >>
  first_x_assum drule >> metis_tac[]
QED

Theorem spaceBS_correct:
  ∀s t m.
    spaceBS m s t ⇔
      redWithMaxSizeL m s t ∧ lambda t
Proof
  metis_tac[spaceBS_correctL, spaceBS_correctR]
QED

val _ = export_theory ()
