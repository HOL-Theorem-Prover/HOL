Theory compilation
Ancestors
  arithmetic list rich_list finite_map CBPV_Mutual_Recursive weak_CBV
  pure_dB
Libs
  BasicProvers

(*dAPP s t: s is function body and t is the argument(value) *)
Definition compile_def:
  (compile (dV x) =  ret $ var x) ∧
  (compile (dAPP s t) =
   pseq (compile t) (compile s) (app (force $ var 0) (var 1))) ∧
  (compile (dABS s) =
   ret $ thunk $ lam $ compile s)
Termination
  WF_REL_TAC ‘measure $ dbsize o SND’ >>
  rw[]
End

Theorem compile_bound:
  ∀n s. bound n s  ⇒ boundComp n (compile s)
Proof
  Induct_on ‘bound’ >> rw[]
  >~ [‘dV’]
  >- (rw[compile_def] >>
      ntac 3 $ rw[Once boundVal_cases])
  >~ [‘dAPP’]
  >- (rw[compile_def] >>
      ntac 5 $ simp[Once boundVal_cases])
  >~ [‘dABS’]
  >- (rw[compile_def] >>
      ntac 3 $ simp[Once boundVal_cases])
QED

Theorem compile_closed:
  ∀env s. closed s ⇒ closedComp (compile s)
Proof
  rw[closed,closedComp_def] >>
  irule compile_bound >>
  rw[]
QED

Definition strip_ret_def:
  strip_ret (ret v) = SOME v ∧
  strip_ret _ = NONE
End

(*  compile(s[v':=λ. t]) = (compile s)[v:=t']
 *)
Theorem compile_subst:
  ∀s t t' k.
  closed(dABS t) ∧
  strip_ret(compile (dABS t)) = SOME t'
  ⇒
  compile (subst s k (dABS t)) =
  substComp (compile s) k t'
Proof
  Induct_on ‘s’ >> rpt strip_tac
  >~ [‘dV’]
  >- (rw[compile_def,substVal_def] >>
      gvs[strip_ret_def,compile_def] )
  >~ [‘dAPP’]
  >- (rw[compile_def,substVal_def] >>
      last_x_assum match_mp_tac >>
      simp[])
  >~ [‘dABS’]
  >- (rw[compile_def,substVal_def] >>
      first_x_assum drule_all >> rw[] >>
      subgoal ‘lift t 1 = t’
      >- gvs[closed,lift_bound,Once bound_cases] >>
      simp[GSYM ADD1])
QED

(* ====================
   =    TIME MODEL   =
   ====================
 *)

Theorem timeBS_makes_abs:
  ∀k s t. timeBS k s t ⇒ ∃t'. t = dABS t'
Proof
  Induct_on ‘timeBS’ >>
  rw[]
QED

Theorem spaceBS_makes_abs:
  ∀k s t. spaceBS k s t ⇒ ∃t'. t = dABS t'
Proof
  Induct_on ‘spaceBS’ >>
  rw[]
QED

Theorem correctTime:
  ∀k s t.
    closed s ∧
    timeBS k s t
    ⇒
    ∃k'. timeBS k' (compile s) (compile t) ∧ k' ≤ 5*k
Proof
  Induct_on ‘timeBS’ >>
  rw[compile_def]
  >- irule_at Any timeBS_Ret >>
  rw[Once CBPV_Mutual_RecursiveTheory.timeBS_cases,PULL_EXISTS] >>
  imp_res_tac closed_app >>
  gvs[lift_closed,substVal_def] >>
  first_x_assum $ irule_at $ Pos hd >>
  first_x_assum $ irule_at $ Pos hd >>
  irule_at (Pos hd) timeBS_App >>
  rw[substVal_def] >>
  irule_at (Pos hd) timeBS_Force >>
  irule_at (Pos hd) timeBS_Lam >>
  simp[PULL_EXISTS] >>
  drule timeBS_makes_abs >>
  strip_tac >>
  gvs[] >>
  drule_at (Pos last) closed_timeBS >>
  impl_tac
  >- (match_mp_tac $ MP_CANON closed_subst2 >>
      imp_res_tac closed_timeBS >>
      simp[]) >>
  strip_tac >>
  subgoal ‘closed(dABS s')’ >- imp_res_tac closed_timeBS >>
  first_assum $ mp_tac o REWRITE_RULE [closed] >>
  simp[Once bound_cases] >>
  strip_tac >>
  drule compile_bound >> rw[] >>
  subgoal ‘closed(dABS t')’ >- imp_res_tac closed_timeBS >>
  drule compile_subst >>
  simp[Once compile_def,strip_ret_def] >>
  disch_then $ qspecl_then [‘s'’,‘0’] mp_tac >> rw[] >>
  simp[compile_def] >>
  subgoal ‘closed (subst s' 0 (dABS t'))’
  >- (simp[closed] >>
      irule bound_subst >>
      imp_res_tac closed_timeBS >>
      gvs[closed] >>
      rename1 ‘bound _ ssss’ >>
      qpat_x_assum ‘bound _ $ dABS ssss’ mp_tac >>
      rw[Once bound_cases]) >>
  res_tac >> fs[] >>
  drule $ cj 2 CBPV_Mutual_RecursiveTheory.bound_ge >>
  disch_then $ qspec_then ‘2’ mp_tac >>
  rw[] >> drule $ cj 2 CBPV_Mutual_RecursiveTheory.bound_closed_k >>
  rw[] >> gvs[compile_def] >> first_x_assum $ irule_at $ Pos hd >> simp[]
QED

(* ====================
   =    SPACE MODEL   =
   ====================
 *)

Theorem compile_size:
  ∀s.
    sizeComp(compile s) ≤
    6 * size s
Proof
  Induct_on ‘s’ >>
  rw[sizeVal_def,compile_def,size_eqs,PULL_EXISTS]
QED

Theorem correctSpace:
  ∀k s t.
    closed s ∧
    spaceBS k s t
    ⇒
    ∃k'. spaceBS k' (compile s) (compile t) ∧ k' ≤ 6 * k
Proof
  Induct_on ‘spaceBS’ >>
  rw[compile_def]
  >- (irule_at Any spaceBS_Ret >>
      rw[sizeVal_def,size_eqs] >>
      match_mp_tac LESS_EQ_TRANS >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      irule_at (Pos hd) compile_size >>
      irule_at (Pos hd) LESS_EQ_REFL >> simp[]) >>
  rw[Once CBPV_Mutual_RecursiveTheory.spaceBS_cases,PULL_EXISTS] >>
  imp_res_tac closed_app >>
  gvs[lift_closed,substVal_def] >>
  first_x_assum $ irule_at $ Pos hd >>
  first_x_assum $ irule_at $ Pos hd >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [CBPV_Mutual_RecursiveTheory.bound_closed] >>
  conj_tac >- (imp_res_tac closed_spaceBS >> imp_res_tac compile_closed >>
               gvs[closedComp_def, compile_def] >>
               fs[Once boundVal_cases]) >>
  irule_at (Pos hd) spaceBS_App >>
  irule_at (Pos hd) spaceBS_Force >>
  irule_at (Pos hd) spaceBS_Lam >>
  simp[PULL_EXISTS] >>
  drule spaceBS_makes_abs >>
  strip_tac >>
  gvs[] >>
  drule_at (Pos last) closed_spaceBS >>
  impl_tac
  >- (match_mp_tac $ MP_CANON closed_subst2 >>
      imp_res_tac closed_spaceBS >>
      simp[]) >>
  strip_tac >>
  subgoal ‘closed(dABS s')’ >- imp_res_tac closed_spaceBS >>
  first_assum $ mp_tac o REWRITE_RULE [closed] >>
  simp[Once bound_cases] >>
  strip_tac >>
  drule compile_bound >>
  strip_tac >>
  subgoal ‘closed(dABS t')’ >- imp_res_tac closed_spaceBS >>
  drule compile_subst >>
  simp[Once compile_def,strip_ret_def] >>
  disch_then $ mp_tac o GSYM >>
  simp[compile_def] >>
  disch_then kall_tac >>
  gvs[compile_def] >>
  subgoal ‘closed (subst s' 0 (dABS t'))’
  >- (simp[closed] >>
      irule bound_subst >>
      imp_res_tac closed_spaceBS >>
      gvs[closed] >>
      rename1 ‘bound _ ssss’ >>
      qpat_x_assum ‘bound _ $ dABS ssss’ mp_tac >>
      rw[Once bound_cases]) >>
  res_tac >>
  first_x_assum $ irule_at Any >>
  gvs[] >>
  gvs[sizeVal_def,size_eqs] >>
  imp_res_tac spaceBS_ge >>
  gvs[size_eqs] >>
  rpt conj_tac
  >- (match_mp_tac LESS_EQ_TRANS >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      irule_at (Pos hd) compile_size >>
      irule_at (Any) LESS_EQ_REFL >>
      simp[] >>
      rw[MAX_DEF])
  >- (match_mp_tac LESS_EQ_TRANS >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      irule_at (Pos hd) compile_size >>
      irule_at (Any) LESS_EQ_REFL >>
      simp[] >>
      rw[MAX_DEF])
  >- (match_mp_tac LESS_EQ_TRANS >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      irule_at (Pos hd) compile_size >>
      rw[MAX_DEF] >>
      irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
      irule_at (Pos hd) compile_size >>
      irule_at (Any) LESS_EQ_REFL >>
      simp[])
  >> rw[MAX_DEF]
QED

(* Call by name *)

Inductive timeBSN:
[~Val:]
  (∀s. timeBSN (0:num) (dABS s) (dABS s))
[~Beta:]
  (∀s s' t u i j l.
    timeBSN i s (dABS s') ∧
    timeBSN j (subst s' 0 t) u ∧
    l = i+j+1 ⇒
    timeBSN l (dAPP s t) u)
End

Inductive spaceBSN:
[~Val:]
  (∀s. spaceBSN (size (dABS s)) (dABS s) (dABS s))
[~Beta:]
  (∀s s' t u m1 m2 m.
    spaceBSN m1 s (dABS s') ∧
    spaceBSN m2 (subst s' 0 t) u ∧
    m = MAX (m1 + 1 + size t) m2 ⇒
    spaceBSN m (dAPP s t) u)
End

Theorem closed_spaceBSN:
  ∀k s t.
    closed s ⇒
    spaceBSN k s t ⇒
    closed t
Proof
  Induct_on `spaceBSN` >> rw[] >>
  imp_res_tac closed_app >>
  res_tac >>
  first_x_assum irule >>
  irule closed_subst2 >>
  simp[]
QED

Theorem spaceBSN_ge:
  ∀s t m.
    spaceBSN m s t ⇒ size s ≤ m ∧ size t ≤ m
Proof
  Induct_on `spaceBSN` >> rw[] >>
  rw[Once size]
QED

Definition compileN_def:
  (compileN (dV x) =
   force $ var $ x) ∧
  (compileN (dAPP s t) =
   app (compileN s) (thunk $ compileN t)) ∧
  (compileN (dABS s) =
   lam $ compileN s)
Termination
  WF_REL_TAC ‘measure $ dbsize’ >>
  rw[]
End

Inductive ft_rel:
[~refl:] (∀t. ft_rel t t)
[~forcethunk:] (∀t t'. ft_rel t t' ⇒ ft_rel(force(thunk t)) t')
[~lam:] (∀t t'. ft_rel t t' ⇒ ft_rel (lam t) (lam t'))
[~app:] (∀s s' t t'. ft_rel s s' ∧ ft_relV t t' ⇒ ft_rel (app s t) (app s' t'))
[~seq:] (∀s s' t t'. ft_rel s s' ∧ ft_rel t t' ⇒ ft_rel (seq s t) (seq s' t'))
[~force:] (∀s s' t t'. ft_rel s s' ∧ ft_rel t t' ⇒ ft_rel (seq s t) (seq s' t'))
[~letin:] (∀s s' t t'. ft_relV s s' ∧ ft_rel t t' ⇒ ft_rel (letin s t) (letin s' t'))
[~reflV:] (∀v. ft_relV v v)
[~thunk:] (∀c. ft_rel c c' ⇒ ft_relV (thunk c) (thunk c'))
End

Theorem sizeComp_compileN_le:
  ∀s. sizeComp (compileN s) ≤ 2*size s
Proof
  Induct >>
  rw[sizeVal_def,compileN_def,size_eqs]
QED

Theorem ft_rel_trans:
  (∀t t' t''. ft_rel t t' ∧ ft_rel t' t'' ⇒ ft_rel t t'') ∧
  (∀v v' v''. ft_relV v v' ∧ ft_relV v' v'' ⇒ ft_relV v v'')
Proof
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_FORALL, GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac ft_rel_strongind >> rw[] >>
  res_tac >> rw[]
  >- rw[Once ft_rel_cases] >>
  pop_assum $ strip_assume_tac o PURE_ONCE_REWRITE_RULE [ft_rel_cases] >>
  gvs[] >>
  rw[Once ft_rel_cases]
QED

Triviality ft_rel_lam_spaceBSN_lemma:
  (∀t t'. ft_rel t t' ⇒ ∀t''. t' = lam t'' ⇒ ∃t'''. spaceBS (sizeComp t) t (lam t''') ∧ ft_rel t (lam t''') ∧ ft_rel t''' t'') ∧
  (∀v v'. ft_relV v v' ⇒ ft_relV v v')
Proof
  ho_match_mp_tac ft_rel_strongind >> rw[] >>
  rw[Once CBPV_Mutual_RecursiveTheory.spaceBS_cases,
     ft_rel_refl,sizeVal_def,PULL_EXISTS,ft_rel_reflV]
  >- (first_x_assum $ irule_at $ Pos hd >>
      rw[MAX_DEF] >>
      irule ft_rel_forcethunk >>
      simp[]) >>
  rw[ft_rel_thunk]
QED

Theorem ft_rel_lam_spaceBSN =
  ft_rel_lam_spaceBSN_lemma |> cj 1 |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]

Theorem spaceBS_normal_form:
  ∀k s t. spaceBS k s t ⇒ ((∃c. t = ret c) ∨ (∃c. t = lam c))
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.spaceBS_ind >>
  rw[]
QED

Theorem ft_rel_size:
  (∀t t'. ft_rel t t' ⇒ sizeComp t' ≤ sizeComp t) ∧
  (∀v v'. ft_relV v v' ⇒ sizeVal v' ≤ sizeVal v)
Proof
  ho_match_mp_tac ft_rel_ind >>
  rw[sizeVal_def]
QED

Theorem compileN_subst:
  ∀env s t v v' t'.
  closed t
  ⇒
  ft_rel (substComp (compileN s) v (thunk(compileN t)))
         (compileN (subst s v t))
Proof
  Induct_on ‘s’ >> rpt strip_tac
  >~ [‘dV’]
  >- (rw[compileN_def,substVal_def,ft_rel_refl,ft_rel_forcethunk])
  >- (rw[compileN_def,substVal_def] >>
      match_mp_tac ft_rel_app >>
      metis_tac[ft_rel_thunk]) >>
  rw[compileN_def,substVal_def] >>
  match_mp_tac ft_rel_lam >>
  simp[ADD1,lift_closed]
QED
