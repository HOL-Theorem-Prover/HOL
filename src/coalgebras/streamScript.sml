Theory stream
(* coalgebraic streams (infinite lists); bisimulation and BNF theorems proved *)

Ancestors hol arithmetic pair pred_set
Libs numLib

Type stream = “:num -> 'a”

Definition scons_def[simp]:
  scons a s 0 = a ∧
  scons a s (SUC n) = s n
End

Theorem scons_alt:
  scons a s = λn. case n of
                    0 => a
                  | SUC m => s m
Proof
  simp[FUN_EQ_THM] >> Induct>> simp[]
QED

Overload shd[inferior] = “λs. s 0”
Overload "" = “shd”

Definition stl_def: stl s = λn. s (n + 1)
End

Theorem stl_cons[simp]:
  stl (scons a s) = s
Proof
  simp[stl_def, scons_alt, GSYM ADD1, FUN_EQ_THM]
QED

Theorem shd_cons[simp]:
  shd (scons a s) = a
Proof
  simp[scons_alt]
QED

Theorem scons_11[simp]:
  scons a s = scons b t ⇔ a = b ∧ s = t
Proof
  simp[FUN_EQ_THM, scons_alt, AllCaseEqs(), SF CONJ_ss] >>
  Cases_on ‘a = b’ >> simp[]
  >- (rw[EQ_IMP_THM] >~
      [‘s i = t i (* g *)’]
      >- (first_x_assum $ qspec_then ‘SUC i’ mp_tac >> simp[]) >>
      metis_tac[TypeBase.nchotomy_of “:num”]) >>
  qexists ‘0’ >> simp[]
QED

Theorem scons_hdtl[simp]:
  scons (shd s) (stl s) = s
Proof
  simp[FUN_EQ_THM, scons_alt, AllCaseEqs(), SF CONJ_ss, stl_def, ADD1] >>
  metis_tac[TypeBase.nchotomy_of “:num”, ADD1]
QED

Theorem stream_cases:
  ∀s. ∃h t. s = scons h t
Proof
  metis_tac[scons_hdtl]
QED

Theorem sbisimulation:
  (s1 = s2) ⇔
  ∃R. R s1 s2 ∧
      ∀t1 t2.
        R t1 t2 ⇒ shd t1 = shd t2 ∧ (R (stl t1) (stl t2) ∨ stl t1 = stl t2)
Proof
  iff_tac
  >- (rw[] >> qexists ‘$=’ >> simp[]) >>
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘n’ >>
  qpat_x_assum ‘R s1 s2’ mp_tac >> map_every Q.ID_SPEC_TAC [‘s1’, ‘s2’] >>
  simp[PULL_FORALL] >> Induct_on ‘n’
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> last_x_assum $ drule_then strip_assume_tac
  >- (gvs[stl_def] >> first_x_assum drule >> simp[ADD1]) >>
  gvs[stl_def, ADD1, FUN_EQ_THM]
QED

Definition siterate_def:
  siterate f x = λn. FUNPOW f n x
End

Theorem shd_siterate[simp]:
  shd (siterate f sd) = sd
Proof
  simp[siterate_def]
QED

Theorem stl_siterate[simp]:
  stl (siterate f sd) = siterate f (f sd)
Proof
  simp[stl_def, siterate_def, FUN_EQ_THM, GSYM ADD1, FUNPOW]
QED

Theorem siterate_scons_eqn:
  siterate f sd = scons sd (siterate f (f sd))
Proof
  simp[Once sbisimulation] >>
  qexists
    ‘λs1 s2. ∃sd. s1 = siterate f sd ∧ s2 = scons sd (siterate f (f sd))’ >>
  rw[]>> simp[]
QED

Definition sunfold_def:
  sunfold hd tl sd = λn. hd (siterate tl sd n)
End

Theorem sunfold_thm:
  sunfold hd tl sd0 =
  let a = hd sd0;
      sd = tl sd0;
  in
    scons a (sunfold hd tl sd)
Proof
  simp[FUN_EQ_THM,sunfold_def,scons_alt] >> Cases >> simp[] >>
  simp[siterate_def, FUNPOW]
QED

Definition smap_def:
  smap f s = sunfold (f o shd) stl s
End

Theorem smap_thm[simp]:
  smap f (scons a s) = scons (f a) (smap f s)
Proof
  simp[smap_def, SimpLHS, Once sunfold_thm] >>
  simp[GSYM smap_def]
QED

Definition sset_def:
  sset s = { a | ∃i. s i = a }
End

Theorem smapO:
  smap f s = f o s
Proof
  simp[Once sbisimulation] >>
  qexists ‘λs1 s2. ∃s. s1 = smap f s ∧ s2 = f o s’ >>
  simp[] >> conj_tac >- metis_tac[] >>
  simp[PULL_EXISTS] >> rw[]
  >- (Cases_on ‘s’ using stream_cases >> simp[]) >>
  ‘stl (smap f s) = smap f (stl s)’
    by (Cases_on ‘s’ using stream_cases >> simp[]) >>
  simp[] >> disj1_tac >> irule_at Any EQ_REFL>>
  simp[stl_def, combinTheory.o_ABS_R]
QED

Theorem sset_map:
  sset (smap f s) = IMAGE f (sset s)
Proof
  simp[smapO, EXTENSION, PULL_EXISTS, sset_def] >> metis_tac[]
QED

Theorem smap_smap_o:
  smap f (smap g s) = smap (f o g) s
Proof
  simp[smapO]
QED

Theorem smap_ID:
  smap (λx. x) s = s
Proof
  simp[smapO, FUN_EQ_THM]
QED

Theorem smap_CONG:
  s1 = s2 ∧ (∀x. x ∈ sset s2 ⇒ f x = g x) ⇒ smap f s1 = smap g s2
Proof
  rw[] >> simp[smapO, FUN_EQ_THM] >> gvs[sset_def, PULL_EXISTS]
QED

Definition liftBin_def:
  liftBin f (s1:'a stream) (s2:'b stream) = λi. f (s1 i) (s2 i)
End

Theorem liftBin_comm:
  (∀x y. f x y = f y x) ⇒ liftBin f s1 s2 = liftBin f s2 s1
Proof
  strip_tac >> simp[Once sbisimulation] >>
  qexists ‘λt1 t2. ∃s1 s2. t1 = liftBin f s1 s2 ∧ t2 = liftBin f s2 s1’ >>
  simp[] >> conj_tac
  >- metis_tac[] >>
  simp[PULL_EXISTS] >> simp[liftBin_def, stl_def]
QED

Theorem shd_liftBin[simp]:
  shd (liftBin f s1 s2) = f (shd s1) (shd s2)
Proof
  simp[liftBin_def]
QED

Theorem stl_liftBin[simp]:
  stl (liftBin f s1 s2) = liftBin f (stl s1) (stl s2)
Proof
  simp[stl_def, liftBin_def]
QED

Definition szip_def: szip = liftBin (,)
End

Theorem szip_alt:
  szip s1 s2 = λi. (s1 i, s2 i)
Proof
  simp[szip_def, liftBin_def]
QED

Theorem szip_thm[simp]:
  szip (scons a s1) s2 = scons (a, shd s2) (szip s1 (stl s2)) ∧
  szip s1 (scons b s2) = scons (shd s1, b) (szip (stl s1) s2)
Proof
  simp[szip_alt, FUN_EQ_THM] >> conj_tac >> Cases >> simp[stl_def, ADD1]
QED

Definition sunzip_def:
  sunzip s = (smap FST s, smap SND s)
End

Theorem szip_unzip[simp]:
  UNCURRY szip (sunzip s) = s ∧ sunzip (szip s1 s2) = (s1,s2)
Proof
  simp[sunzip_def, szip_alt] >>
  simp[smapO, FUN_EQ_THM]
QED

Definition srel_def:
  srel R s1 s2 ⇔ ∀i. R (s1 i) (s2 i)
End

Theorem srelpair_characterisation:
  srel R s1 s2 ⇔ ∃sps. (∀a b. (a,b) ∈ sset sps ⇒ R a b) ∧
                       smap FST sps = s1 ∧ smap SND sps = s2
Proof
  simp[srel_def, smapO, sset_def, PULL_EXISTS] >>
  simp[EQ_IMP_THM, PULL_EXISTS] >> rw[] >> simp[]
  >- (qexists ‘szip s1 s2’ >>
      simp[combinTheory.o_ABS_R, FUN_EQ_THM, szip_alt])
  >- (Cases_on ‘sps i’ >> simp[] >> metis_tac[])
QED

Theorem cardinality_bound:
  countable (sset (s:'a stream))
Proof
  simp[countable_def] >> qexists ‘λa. LEAST i. s i = a’ >>
  simp[INJ_IFF] >> rw[] >> gvs[sset_def] >> simp[EQ_IMP_THM] >>
  LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >> simp[] >>
  LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >> rw[]
QED

Definition sconst_def:
  sconst x = λi. x
End

Theorem sconst_scons_eqn[simp]:
  sconst x = scons x (sconst x)
Proof
  simp[sconst_def, scons_alt, FUN_EQ_THM] >> Cases >> simp[]
QED

Definition sdrop_def:
  sdrop n s = FUNPOW stl n s
End

Theorem sdrop_thm[simp]:
  sdrop 0 s = s ∧
  sdrop (SUC n) s = stl (sdrop n s) ∧
  sdrop (NUMERAL (BIT2 n)) s = stl (sdrop (NUMERAL (BIT1 n)) s) ∧
  sdrop (NUMERAL (BIT1 n)) s = stl (sdrop (NUMERAL (BIT1 n) - 1) s)
Proof
  simp[sdrop_def, numeralTheory.numeral_funpow, PRE_SUB1] >>
  simp[GSYM FUNPOW_SUC] >> simp[FUNPOW]
QED

Theorem sdrop_eq_mono:
  ∀m n s t. sdrop m s = sdrop m t ∧ m ≤ n ⇒ sdrop n s = sdrop n t
Proof
  simp[sdrop_def, LESS_EQ_EXISTS, PULL_EXISTS] >> ONCE_REWRITE_TAC[ADD_COMM] >>
  simp[FUNPOW_ADD]
QED

Theorem stl_sdrop:
  stl (sdrop i s) = sdrop i (stl s)
Proof
  simp[sdrop_def, GSYM FUNPOW_SUC, FUNPOW]
QED

Definition sexists_def:
  sexists P s = ∃i. P (s i)
End

Theorem sexists_thm[simp]:
  sexists P (scons h t) ⇔ P h ∨ sexists P t
Proof
  simp[sexists_def, scons_alt] >>
  simp[SimpLHS, Once EXISTS_NUM]
QED

Theorem sexists_ind:
  ∀P.
    (∀h t. P h ⇒ Q (scons h t)) ∧
    (∀h t. Q t ∧ sexists P t ⇒ Q (scons h t)) ⇒
    ∀s. sexists P s ⇒ Q s
Proof
  simp[sexists_def, PULL_EXISTS] >> gen_tac >> strip_tac >>
  Induct_on ‘i’
  >- (rpt strip_tac >> first_x_assum drule >>
      disch_then $ qspec_then ‘stl s’ mp_tac >> simp[]) >>
  rw[] >>
  first_x_assum $ qspec_then ‘stl s’ mp_tac >>
  ‘P (stl s i)’ by simp[stl_def, GSYM ADD1] >>
  simp[] >> strip_tac >> first_x_assum drule_all >>
  disch_then $ qspec_then ‘shd s’ mp_tac >> simp[]
QED

(* eventually two sequences exactly coincide *)
Definition seventuallyeq_def:
  seventuallyeq s t ⇔ ∃i. sdrop i s = sdrop i t
End

Theorem seventuallyeq_REFL:
  seventuallyeq s s
Proof
  simp[seventuallyeq_def]
QED

Theorem seventuallyeq_SYM:
  seventuallyeq s t ⇔ seventuallyeq t s
Proof
  metis_tac[seventuallyeq_def]
QED

Theorem seventuallyeq_TRANS:
  seventuallyeq s t ∧ seventuallyeq t u ⇒ seventuallyeq s u
Proof
  simp[seventuallyeq_def, PULL_EXISTS] >> qx_genl_tac [‘i’, ‘j’] >>
  strip_tac >> qexists ‘MAX i j’ >>
  rpt (dxrule_then assume_tac sdrop_eq_mono) >>
  rpt (first_x_assum (resolve_then Any assume_tac (iffRL $ cj 1 MAX_LE))) >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem seventuallyeq_ind:
  ∀P.
    (∀s. P s s) ∧
    (∀h1 h2 s t. P s t ∧ seventuallyeq s t ⇒ P (scons h1 s) (scons h2 t)) ⇒
    ∀s t. seventuallyeq s t ⇒ P s t
Proof
  simp[seventuallyeq_def, PULL_EXISTS] >> gen_tac >> strip_tac >>
  Induct_on ‘i’ >> simp[] >> rw[] >>
  Cases_on ‘s’ using stream_cases >>
  Cases_on ‘t’ using stream_cases >>
  last_x_assum irule >> gvs[stl_sdrop] >> metis_tac[]
QED
