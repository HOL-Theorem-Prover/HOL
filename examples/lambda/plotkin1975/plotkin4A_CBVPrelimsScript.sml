Theory plotkin4A_CBVPrelims

(* A translation of “Call-by-name, Call-by-value and the λ-Calculus” by
   Gordon Plotkin, Theoretical Computer Science 1 (1975), pp125–159.
   North Holland

   First part of Section 4 on the CBV equational theory, and its CR and
   standardisation results.  Independent of §3.
*)

Ancestors
  cterm nomset pred_set plotkin2_TechPrelims
Libs
  NEWLib

(* p134, λᵥ |- M = N, parameterised by function "Constapply" *)
Inductive lv:
[~I2:] is_value N ⇒ lv capp (LAM x M @@ N) ([N/x] M)
[~I3:] capp a b = SOME t ⇒ lv capp (CONST a @@ CONST b) t
[~II1:] lv capp M M (* TYPO; original has M = N *)
[~II2:] lv capp M N ∧ lv capp N L ⇒ lv capp M L
[~II3:] lv capp M N ⇒ lv capp N M
[~III1a:] lv capp M N ⇒ lv capp (M @@ Z) (N @@ Z)
[~III1b:]  lv capp M N ⇒ lv capp (Z @@ M) (Z @@ N)
[~III2:] lv capp M N ⇒ lv capp (LAM x M) (LAM x N)
End

(* above without II3 (symmetry) *)
Inductive lge:
[~I2:] is_value N ⇒ lge capp (LAM x M @@ N) ([N/x] M)
[~I3:] capp a b = SOME t ⇒ lge capp (CONST a @@ CONST b) t
[~II1:] lge capp M M (* TYPO; original has M = N *)
[~II2:] lge capp M N ∧ lge capp N L ⇒ lge capp M L
[~II3:] lge capp M N ⇒ lge capp N M
[~III1a:] lge capp M N ⇒ lge capp (M @@ Z) (N @@ Z)
[~III1b:]  lge capp M N ⇒ lge capp (Z @@ M) (Z @@ N)
[~III2:] lge capp M N ⇒ lge capp (LAM x M) (LAM x N)
End

val _ = set_mapped_fixity{term_name = "lge", tok = "≥",
                          fixity = Infix(NONASSOC, 450)}

Theorem is_value_ctpm[simp]:
  is_value (ctpm pi N) = is_value N
Proof
  simp[is_value_def] >> Cases_on ‘N’ using cterm_CASES >> simp[]
QED

Theorem lv_perm:
  (∀a b M. capp a b = SOME M ⇒ closed M) ⇒
  ∀M N. lv capp M N ⇒ lv capp (ctpm pi M) (ctpm pi N)
Proof
  strip_tac >> Induct_on ‘lv’ >> rw[] >>
  simp[lv_II1, lv_III1a, lv_III1b, lv_III2] >~
  [‘lv _ (LAM (lswapstr _ _) (ctpm _ _) @@ _) (ctpm _ ([_/_] _))’]
  >- simp[ctpm_subst, lv_I2] >~
  [‘lv _ (CONST a @@ CONST b) _’]
  >- (first_x_assum drule >> simp[supp_pm_fresh, lv_I3]) >>
  metis_tac[lv_II2, lv_II3]
QED

Theorem lv_perm_EQN[simp]:
  (∀a b M. capp a b = SOME M ⇒ closed M) ⇒
  (lv capp (ctpm π M) (ctpm π N) ⇔ lv capp M N)
Proof
  metis_tac[lv_perm, pmact_inverse]
QED

Theorem lv_ind_genX:
  ∀capp P fv.
    (∀x. FINITE (fv x)) ∧
    (∀a b M. capp a b = SOME M ⇒ closed M) ∧
    (∀M N v x. v ∉ fv x ∧ v ∉ cFV N ∧ is_value N ⇒ P (LAM v M @@ N) ([N/v]M) x) ∧
    (∀a b t x. capp a b = SOME t ⇒ P (CONST a @@ CONST b) t x) ∧
    (∀M x. P M M x) ∧
    (∀M N x. lv capp M N ∧ (∀y. P M N y) ⇒ P N M x) ∧
    (∀M N Q x. lv capp M N ∧ lv capp N Q ∧ (∀y. P M N y) ∧
               (∀w. P N Q w) ⇒ P M Q x) ∧
    (∀M N Z x. lv capp M N ∧ (∀w. P M N w) ⇒ P (M @@ Z) (N @@ Z) x) ∧
    (∀M N Z x. lv capp M N ∧ (∀w. P M N w) ⇒ P (Z @@ M) (Z @@ N) x) ∧
    (∀M N v x. lv capp M N ∧ (∀w. P M N w) ∧ v ∉ fv x ⇒
               P (LAM v M) (LAM v N) x)
  ⇒
    ∀M N. lv capp M N ⇒ ∀x. P M N x
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀M N. lv capp M N ⇒ ∀π x. P (ctpm π M) (ctpm π N) x’
    suffices_by metis_tac[pmact_nil] >>
  Induct_on ‘lv’ >> simp[] >> rpt strip_tac >~
  [‘P (LAM (lswapstr π v) (ctpm π M) @@ ctpm π N) _ x (* g *)’]
  >- (simp[ctpm_subst] >>
      Q_TAC (NEW_TAC "z") ‘cFV (ctpm π M) ∪ cFV (ctpm π N) ∪ fv x ∪
                           {lswapstr π v}’ >>
      ‘LAM (lswapstr π v) (ctpm π M) =
       LAM z (ctpm [(z,lswapstr π v)] (ctpm π M))’ by simp[ctpm_ALPHA] >>
      simp[] >>
      ‘[ctpm π N / z] (ctpm [(z,lswapstr π v)] (ctpm π M)) =
       [ctpm π N / lswapstr π v] (ctpm π M)’
        suffices_by metis_tac[is_value_ctpm] >>
      simp[lemma15a, fresh_ctpm_subst]) >~
  [‘CONST a @@ CONST b’, ‘capp a b = SOME N’]
  >- metis_tac[supp_pm_fresh] >~
  [‘P (LAM (lswapstr π v) (ctpm π M)) (LAM _ (ctpm π N)) x (* g *)’]
  >- (Q_TAC (NEW_TAC "z") ‘cFV (ctpm π M) ∪ cFV (ctpm π N) ∪ fv x’ >>
      ‘LAM (lswapstr π v) (ctpm π M) =
       LAM z (ctpm [(z, lswapstr π v)] (ctpm π M)) ∧
       LAM (lswapstr π v) (ctpm π N) =
       LAM z (ctpm [(z, lswapstr π v)] (ctpm π N))’
        by simp[ctpm_ALPHA] >>
      simp[] >> first_x_assum irule >>
      simp[GSYM ctpm_CONS] >> irule (iffRL lv_perm_EQN) >>
      simp[SF SFY_ss]) >>
  metis_tac[lv_perm]
QED

Theorem substitution_lemma:
  u ≠ v ∧ v ∉ cFV P ⇒
  ∀M. [[P/u] N / v] ([P/u] M) = [P/u] ([N/v] M)
Proof
  strip_tac >> ho_match_mp_tac cterm_induction >>
  qexists ‘cFV N ∪ cFV P ∪ {u;v}’ >>
  rw[cSUB_THM, SUB_DEF] >> simp[lemma14b] >>
  rename [‘[_/_] (LAM w ([P/u] M)) = LAM w _’] >>
  ‘w ∉ cFV ([P/u]N)’ by (simp[cFV_SUB] >> rw[]) >>
  simp[cSUB_THM]
QED

Theorem is_value_SUB:
  ∀M. is_value M ∧ is_value N ⇒ is_value ([N/v]M)
Proof
  ho_match_mp_tac cterm_induction >> qexists ‘v INSERT cFV N’ >>
  rw[cSUB_THM, SUB_DEF]
QED

Theorem thm4_1_0[local]:
  (∀a b N. capp a b = SOME N ⇒ closed N) ⇒
  ∀M N. lv capp M N ⇒
        ∀Lx L x. Lx = (L,x) ∧ is_value L ⇒ lv capp ([L/x] M) ([L/x]N)
Proof
  strip_tac >>
  ho_match_mp_tac lv_ind_genX >>
  qexists_tac ‘λ(L,v). cFV L ∪ {v}’ >> simp[pairTheory.FORALL_PROD] >> rw[] >~
  [‘capp a b = SOME M’, ‘closed M (* g *)’]
  >- metis_tac[] >~
  [‘lv capp (LAM v ([P/u] M) @@ [P/u] N) ([P/u] ([N/v] M)) (* g *)’]
  >- (‘lv capp (LAM v ([P/u]M) @@ [P/u]N) ([[P/u]N/v] ([P/u]M))’
        by simp[lv_I2, is_value_SUB] >>
      gvs[substitution_lemma]) >~
  [‘capp M N = SOME P’]
  >- (‘closed P’ by metis_tac[] >> simp[lemma14b, lv_I3]) >>
  metis_tac[lv_II1, lv_II2, lv_II3, lv_III1a, lv_III1b, lv_III2]
QED

Theorem thm4_1 = SRULE[pairTheory.FORALL_PROD] thm4_1_0

val _ = set_mapped_fixity{fixity = Infix (NONASSOC, 450),
                          tok = "≥₁", term_name = "parredn"}

Theorem nv_exists[local] =
        parameter_tm_recursion
          |> INST_TYPE [“:ρ” |-> “:string”, “:ς” |-> “:num”]
          |> Q.INST [‘apm’ |-> ‘discrete_pmact’,
                     ‘ppm’ |-> ‘string_pmact’, ‘A’ |-> ‘∅’,
                     ‘vr’ |-> ‘λu v. if u = v then 1 else 0’,
                     ‘ap’ |-> ‘λm n t1 t2 u. m u + n u’,
                     ‘cn’ |-> ‘λa v. 0’,
                     ‘lm’ |-> ‘λbf v b u. bf u’]
          |> SRULE[fnpm_def]
          |> SRULE[Once reordering]

val nv_def = new_specification("nv_def", ["nv"], nv_exists)

Theorem absent_nv0:
  ∀t. nv v t = 0 ⇔ v ∉ cFV t
Proof
  ho_match_mp_tac cterm_induction >> qexists ‘{v}’ >>
  simp[nv_def, AllCaseEqs()] >> metis_tac[EQ_SYM_EQ]
QED

Theorem nv_LAM:
  nv v (LAM v M) = 0
Proof
  simp[absent_nv0]
QED

Theorem nv_thm[simp]:
  (nv v (VAR u) = if u = v then 1 else 0) ∧
  (nv v (M @@ N) = nv v M + nv v N) ∧
  (nv v (CONST a) = 0) ∧
  (nv v (LAM u M) = if u = v then 0 else nv v M)
Proof
  rw[nv_def, nv_LAM]
QED

Theorem nv_ctpm[simp]:
  nv v (ctpm [(x,y)] t) = nv (swapstr x y v) t
Proof
  CONV_TAC (RAND_CONV (REWR_CONV (CONJUNCT2 nv_def)))>>
  simp[]
QED

(* "we introduce a size measure on proofs [of ≥₁], correponding to the
    “implicit” number of β and δ reductions" *)
Inductive nparredn:
[~I1:]
  nparredn m M M' ∧ nparredn n N N' ∧ is_value N ⇒
  nparredn (m + nv x M' * n + 1) (LAM x M @@ N) ([N'/x]M)
[~I2:]
  capp a b = SOME M ⇒ nparredn 1 (CONST a @@ CONST b) M
[~II1:]
  nparredn 0 M M
[~II2:]
  nparredn m M M' ⇒ nparredn m (LAM x M) (LAM x M')
[~II3:]  (* TYPO: paper seems to omit at least first 1-subscript for ≥
            in premises *)
  nparredn m M M' ∧ nparredn n N N' ⇒
  nparredn (m + n) (M @@ N) (M' @@ N')
End

Theorem p137_note[simp]:
  nparredn 0 M N ⇔ M = N
Proof
  simp[EQ_IMP_THM, nparredn_II1] >> Induct_on ‘nparredn’ >> simp[]
QED
