Theory plotkin

(* A translation of “Call-by-name, Call-by-value and the λ-Calculus” by
   Gordon Plotkin, Theoretical Computer Science 1 (1975), pp125–159.
   North Holland
*)

Ancestors
  cterm fmaptree nomset finite_map nominalFmapTree
  pred_set
Libs NEWLib

val _ = hide "S"

(* p127: “A term is a *value* iff it is not a combination” *)
Definition is_value_def:
  is_value ct ⇔ ∀M N. ct ≠ M @@ N
End

Theorem is_value_thm[simp]:
  is_value (VAR s) ∧
  is_value (LAM v M) ∧
  is_value (CONST c) ∧
  ¬is_value (M @@ N)
Proof
  simp[is_value_def]
QED

Overload closed = “λct. cFV ct = {}”

(* §3 ISWIM, p128 *)
Datatype:
  iswim_const = ISN num | ISSUC | ISP | IS0
End

Type icterm[pp] = “:iswim_const cterm”

(* p129 *)
Definition constapply_def:
  constapply ISSUC (ISN n) = SOME $ CONST $ ISN $ n + 1 ∧
  (constapply ISP (ISN n) = if 0 < n then SOME $ CONST $ ISN $ n - 1
                            else NONE) ∧
  (constapply IS0 (ISN n) = if n = 0 then SOME $ LAM "x" (LAM "y" (VAR "x"))
                            else SOME $ LAM "x" (LAM "y" (VAR "y"))) ∧
  constapply _ _ = NONE
End

(* ----------------------------------------------------------------------
    Closures and environments

    Need Clos ≈ (term # (string |-> Clos)) with the second component
    being called the environment
   ---------------------------------------------------------------------- *)

Type Closure = “:(string,icterm)fmaptree”
Type Environment = “:string |-> Closure”

(* well-formedness is the translation of clause (2) on p129, where what it
   is to be a closure is specified *)
Definition wf_Closure_def:
  wf_Closure : Closure -> bool =
  fmtreerec (λct fmb fm. cFV ct ⊆ FDOM fm ∧
                         ∀s. s ∈ FDOM fmb ⇒ fmb ' s)
End

Overload mkClos = “FTNode : icterm -> (string |-> Closure) -> Closure”
Overload Clos_tm = “item : Closure -> icterm”
Overload Clos_E = “map : Closure -> (string |-> Closure)”

(* quail gets these characters with \langle \ratio \rangle *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟨", TM, HardSpace 1, TOK "∶",
                                 BreakSpace (1,1), TM, TOK "⟩"],
                  term_name = "mkClos"}



(*
   ⊢ wf_Closure (mkClos i fm) ⇔
     cFV i ⊆ FDOM fm ∧ ∀s. s ∈ FDOM fm ⇒ wf_Closure (fm ' s): thm
*)
Theorem wf_Closure_thm[simp] =
        PART_MATCH (rator o lhs) (GEN_ALL fmtreerec_thm)
                   (rhs $ concl wf_Closure_def)
          |> SRULE[]
          |> SRULE[GSYM wf_Closure_def]

val t_pmact_t = inst [alpha |-> “:iswim_const”] $ rand “cFV”


(* p129: “The function Real: Closures -> Terms is defined inductively by...” *)
Definition Real_def:
  Real : Closure -> icterm = fmtreerec (λct fmt fm. ssub fmt ct)
End

Theorem ssub_cong:
  M = N ∧ (∀v. v ∈ cFV N ⇒ FLOOKUP f v = FLOOKUP g v) ⇒ f ' M = g ' N
Proof
  simp[] >> Cases_on ‘M = N’ >> simp[] >> gvs[] >>
  qid_spec_tac ‘M’ >>
  ho_match_mp_tac cterm_induction >> simp[] >>
  qexists_tac ‘FDOM f ∪ FDOM g ∪ BIGUNION (IMAGE cFV $ FRANGE f) ∪
               BIGUNION (IMAGE cFV $ FRANGE g)’ >> simp[] >> rw[] >>
  simp[] >>~-
  ([‘VAR v’],
   gvs[GSYM finite_mapTheory.flookup_thm] >>
   gvs[finite_mapTheory.flookup_thm]) >~
  [‘FLOOKUP f v = FLOOKUP g v’]
  >- metis_tac[finite_mapTheory.flookup_thm, optionTheory.SOME_11] >>
  gvs[finite_mapTheory.FRANGE_DEF] >>
  ‘(∀fv. fv ∈ FDOM f ⇒ v ∉ cFV (f ' fv)) ∧
   ∀gv. gv ∈ FDOM g ⇒ v ∉ cFV (g ' gv)’ by metis_tac[] >>
  simp[ssub_thm] >> last_x_assum irule>> qx_gen_tac ‘u’ >>
  strip_tac >> Cases_on ‘u = v’ >> simp[] >>
  gvs[GSYM finite_mapTheory.flookup_thm]
QED

(* “Real (⟨M,E⟩) = [Real (E(x₁))/x₁] ... [Real (E(xₙ)/xₙ)] M” *)
Theorem Real_thm:
  wf_Closure (mkClos M E) ⇒
  Real (mkClos M E) = FUN_FMAP (λx. Real (E ' x)) (cFV M) ' M
Proof
  simp[Real_def, fmtreerec_thm, wf_Closure_thm] >> strip_tac >>
  irule ssub_cong >> simp[] >>
  simp[FLOOKUP_SIMP, FLOOKUP_o_f, AllCaseEqs()] >>
  metis_tac[flookup_thm, SUBSET_DEF]
QED

Datatype: controlstring = Ap | Tm icterm
End
Type Controlstrings = “:controlstring list”

Definition cstrsFV_def[simp]:
  cstrsFV [] = ∅ ∧
  cstrsFV (Ap :: rest) = cstrsFV rest ∧
  cstrsFV (Tm ct :: rest) = cFV ct ∪ cstrsFV rest
End

Type Stack = “:Closure list”

Definition isDump_def[simp]:
isDump [] = T ∧
isDump ((S,E,C)::D) = (
  isDump D ∧ (∀cl. MEM cl S ⇒ wf_Closure cl) ∧
  (∀(k:string) cl. FLOOKUP E k = SOME cl ⇒ wf_Closure cl) ∧
  cstrsFV C ⊆ FDOM E
)
End

Type Dump = “:(Stack # Environment # Controlstrings) list”

(* p130 *)
Inductive dumpTrans:
[~Cnil:]
  dumpTrans (((Cl::S,E,[])::(S',E',C')::D'):Dump)
            (((Cl::S',E',C')::D'):Dump)
[~Cvar:]
  x ∈ FDOM E ⇒
  dumpTrans ((S,E,Tm (VAR x)::C)::D)
            (((E ' x)::S,E,C)::D)
[~Cconst:]
  dumpTrans ((S,E,Tm (CONST a)::C)::D)
            ((mkClos (CONST a) FEMPTY::S,E,C)::D)
[~Clam:]
  dumpTrans ((S,E,Tm (LAM x M)::C)::D)
            ((mkClos (LAM x M) E::S,E,C)::D)
[~Caplam:]
  dumpTrans ((mkClos (LAM x M) E'::Cl::S,E,Ap::C)::D)
            (([],E' |+ (x,Cl),[Tm M])::(S,E,C)::D)
[~Capconst:]
  constapply a b = SOME t ⇒
  dumpTrans ((mkClos (CONST a) E' :: mkClos (CONST b) E'' :: S, E, Ap::C)::D)
            ((mkClos t FEMPTY::S,E,C)::D)
[~CAPP:]
  dumpTrans ((S,E,Tm (APP M N)::C)::D) ((S,E,Tm N::Tm M::Ap::C)::D)
End

Definition Load_def:
  Load (M:icterm) : Dump = [([],FEMPTY,[Tm M])]
End

Theorem Load_isDump:
  closed M ⇒ isDump (Load M)
Proof
  strip_tac >> simp[Load_def]
QED

Theorem dumpTrans_isDump:
  ∀D1 D2. dumpTrans D1 D2 ∧ isDump D1 ⇒ isDump D2
Proof
  Induct_on ‘dumpTrans’ >> simp[] >> rw[] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, flookup_thm] >~
  [‘wf_Closure _ (* g *)’]
  >- rw[FAPPLY_FUPDATE_THM] >~
  [‘_ ⊆ _ (* g *)’]
  >- ASM_SET_TAC[] >~
  [‘closed t’, ‘constapply _ _ = SOME t’]
  >- (Cases_on ‘a’ >> Cases_on ‘b’ >> gvs[constapply_def, AllCaseEqs()] >>
      simp[EXTENSION, EQ_IMP_THM])
QED

Definition Unload_def:
  Unload ([]:Dump) = NONE ∧
  (Unload [([Cl],E,[])] = if E = FEMPTY then SOME (Real Cl) else NONE) ∧
  Unload _ = NONE
End

Definition Eval_def:
  Eval M N ⇔ ∃D. RTC dumpTrans (Load M) D ∧ Unload D = SOME N
End

(* p130; relation is given as an equation and termed "informal" *)
Inductive eval:
[~const:]
  eval (CONST a) (CONST a)
[~abs:]
  eval (LAM x M) (LAM x M)
[~app_tm:]
  eval M (LAM x M') ∧ eval N N' ∧ eval ([N'/x]M') P ⇒
  eval (APP M N) P
[~app_const:]
  eval M (CONST a) ∧ eval N (CONST b) ∧ constapply a b = SOME t ⇒
  eval (APP M N) t
End

(* p130; “Formally, we define the predicate ‘M has value N at time t’ by
   induction on t, for closed terms M and N.” *)
Inductive timed_eval:
[~const:]
  timed_eval 1 (CONST a) (CONST a)
[~abs:]
  timed_eval 1 (LAM x M) (LAM x M)
[~app_tm:]
  timed_eval t M (LAM x M') ∧ timed_eval t' N N' ∧ timed_eval t'' ([N'/x]M') L ⇒
  timed_eval (t + t' + t'' + 1) (APP M N) L
[~app_const:]
  timed_eval t M (CONST a) ∧ timed_eval t' N (CONST b) ∧
  constapply a b = SOME P ⇒
  timed_eval (t + t' + 1) (APP M N) P
End

Theorem timed_eval_thm[simp]:
  (timed_eval t (CONST a) M ⇔ t = 1 ∧ M = CONST a) ∧
  (timed_eval t (LAM x M) N ⇔ t = 1 ∧ N = LAM x M)
Proof
  once_rewrite_tac [timed_eval_cases] >> simp[] >>
  rw[LAM_eq_thm, EQ_IMP_THM, EXISTS_OR_THM] >>
  simp[LAM_eq_thm] >> simp [GSYM pmact_append] >>
  rename [‘_ = ctpm [(a,b);(b,a)] M’] >>
  ‘[(a,b);(b,a)] == []’ suffices_by
    (strip_tac >>
     drule_then (assume_tac o INST_TYPE [alpha |-> “:icterm”]) pmact_permeq >>
     simp[]) >>
  simp[permeq_thm]
QED

Theorem timed_eval_det:
  ∀M N N' t t'. timed_eval t M N ∧ timed_eval t' M N' ⇒ N = N' ∧ t = t'
Proof
  Induct_on ‘timed_eval’ >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >~
  [‘constapply a b = SOME L’]
  >- (once_rewrite_tac[timed_eval_cases] >> simp[] >> strip_tac >~
      [‘timed_eval t1 M (CONST a)’, ‘timed_eval t2 M (LAM x N)’]
      >- (first_x_assum (qpat_x_assum ‘timed_eval _ _ (LAM _ _)’ o
                         mp_then Any mp_tac) >> simp[]) >>
      metis_tac[optionTheory.SOME_11, cterm_11]) >>
  once_rewrite_tac[timed_eval_cases] >> simp[] >> strip_tac >~
  [‘timed_eval t1 M (CONST a)’, ‘timed_eval t2 M (LAM x N)’]
  >- (first_x_assum (qpat_x_assum ‘timed_eval _ M (CONST a)’ o
                      mp_then Any mp_tac) >> simp[]) >>
  gvs[] >>
  rename [‘ta + _ = tx + _’,
          ‘timed_eval ta M (LAM x N)’, ‘timed_eval tx M (LAM y P)’] >>
  ‘ta = tx ∧ LAM y P = LAM x N’ by metis_tac[] >> gvs[] >>
  rename [‘tb + _ = ty + _’, ‘timed_eval tb M2 Na’, ‘timed_eval ty M2 Ny’] >>
  ‘tb = ty ∧ Na = Ny’ by metis_tac[] >> gvs[] >>
  rename [‘[Na/_] _’] >>
  ‘[Na/y] P = [Na/x] N’ suffices_by metis_tac[] >>
  pop_assum mp_tac >> simp[LAM_eq_thm] >> rw[] >>
  simp[fresh_ctpm_subst, lemma15a]
QED

Theorem eval_timed_eval:
  ∀M N. eval M N ⇔ ∃t. timed_eval t M N
Proof
  simp[PULL_EXISTS,EQ_IMP_THM,FORALL_AND_THM] >> conj_tac >~
  [‘eval _ _ ⇒ _’]
  >- (Induct_on ‘eval’ >> metis_tac[timed_eval_rules]) >>
  Induct_on ‘timed_eval’ >> metis_tac[eval_rules]
QED

Definition is_abs_def:
  is_abs M = ∃v M0. M = LAM v M0
End

Theorem is_abs_thm[simp]:
  is_abs (VAR v) = F ∧
  is_abs (APP M N) = F ∧
  is_abs (CONST c) = F ∧
  is_abs (LAM u M) = T
Proof
  simp[is_abs_def] >> metis_tac[]
QED

Definition is_const_def:
  is_const M = ∃c. M = CONST c
End

Theorem is_const_thm[simp]:
  is_const (VAR v) = F ∧
  is_const (CONST c) = T ∧
  is_const (APP M N) = F ∧
  is_const (LAM u M) = F
Proof
  simp[is_const_def]
QED

Inductive isVClosure:
[~clos:]
  wf_Closure (mkClos M E) ∧ (is_abs M ∨ is_const M) ∧ isVEnv E ⇒
  isVClosure (mkClos M E)
[~env:]
  (∀v. v ∈ FDOM E ⇒ isVClosure (E ' v)) ⇒
  isVEnv E
End

Theorem isVClosure_thm:
  (isVClosure (mkClos V e) ⇔
     wf_Closure (mkClos V e) ∧ (is_abs V ∨ is_const V) ∧ isVEnv e) ∧
  (isVEnv FEMPTY = T) ∧
  (isVEnv (fm |+ (v,c)) ⇔ isVClosure c ∧ isVEnv (fm \\ v))
Proof
  rpt strip_tac >> simp[Once isVClosure_cases, SimpLHS] >> simp[]
  >- metis_tac[] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[cj 2 isVClosure_cases] >>
  simp[FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM] >> metis_tac[]
QED

Theorem isVClosure_wf_Closure:
  isVClosure Cl ⇒ wf_Closure Cl
Proof
  simp[Once isVClosure_cases, PULL_EXISTS]
QED

Theorem FINITE_supp_string_pmact:
  FINITE (supp string_pmact s)
Proof
  simp[]
QED

Theorem Real_alt:
  wf_Closure Cl ⇒
  Real Cl =
  FUN_FMAP (λx. Real (fmt_map Cl ' x)) (cFV $ fmt_item Cl) ' (fmt_item Cl)
Proof
  Cases_on ‘Cl’ using fmaptree_nchotomy >> simp[Real_thm]
QED

Overload fmFV = “λapm bpm. supp (fm_pmact apm bpm)”
Overload clpmact = “fmt_pmact cterm_pmact string_pmact”
Overload clFV = “supp clpmact”
Overload clpm = “pmact clpmact”
Overload env_pmact = “fm_pmact string_pmact clpmact”
Overload eFV = “supp env_pmact”
Overload envpm = “pmact env_pmact”
Overload subpm = “fmpm string_pmact cterm_pmact”
Overload subFV = “supp (fm_pmact string_pmact cterm_pmact)”

Theorem FINITE_clFV[simp]:
  FINITE (clFV cl)
Proof
  irule FINITE_supp_fmtpm >> simp[]
QED

Theorem FINITE_eFV[simp]:
  FINITE (eFV E)
Proof
  simp[fmap_supp, supp_setpm, PULL_EXISTS]
QED

Theorem term_for_set_exists[local]:
  ∀A. FINITE A ⇒ ∃ct. cFV ct = A
Proof
  Induct_on ‘FINITE’ >> rw[]
  >- (qexists ‘CONST ARB’ >> simp[]) >>
  rename [‘v ∉ cFV t’] >>
  qexists ‘VAR v @@ t’ >> simp[] >> SET_TAC[]
QED

Theorem FORALL_cFV:
  (∀t. P (cFV t)) ⇔ (∀A. FINITE A ⇒ P A)
Proof
  metis_tac[term_for_set_exists, FINITE_cFV]
QED

Theorem FUN_FMAP_ssub_restrict:
  ∀(M:'a cterm) D.
    FINITE D ⇒
    FUN_FMAP f D ' M = FUN_FMAP f (D ∩ cFV M) ' M
Proof
  simp[GSYM FORALL_cFV] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  ho_match_mp_tac cterm_bvc_induction >>
  qexists ‘λt. cFV t ∪ supp (set_pmact cterm_pmact) (IMAGE f (cFV t))’ >>
  gvs[FORALL_cFV] >>
  rw[ssub_thm] >> simp[supp_setpm, PULL_EXISTS] >> rw[] >~
  [‘FUN_FMAP f _ ' (s:string) = FUN_FMAP f _ ' s’]
  >- simp[FUN_FMAP_DEF] >~
  [‘cFV M ∪ cFV N’, ‘_ ' M’]
  >- (‘A ∩ (cFV M ∪ cFV N) ∩ cFV M = A ∩ cFV M’ by SET_TAC[] >>
      ‘FINITE (A ∩ (cFV M ∪ cFV N))’ by simp[] >>
      metis_tac[]) >~
  [‘cFV M ∪ cFV N’, ‘_ ' N’]
  >- (‘A ∩ (cFV M ∪ cFV N) ∩ cFV N = A ∩ cFV N’ by SET_TAC[] >>
      ‘FINITE (A ∩ (cFV M ∪ cFV N))’ by simp[] >>
      metis_tac[]) >~
  [‘FUN_FMAP f (A ∩ _) ' (LAM v M0) = FUN_FMAP f A ' _’] >>
  ‘∀y. y ∈ A ⇒ v ∉ cFV (f y)’
    by (gvs[supp_setpm] >> metis_tac[]) >>
  ‘∀y. y ∈ A ∩ (cFV M0 DELETE v) ⇒ v ∉ cFV (f y)’ by ASM_SET_TAC[] >>
  simp[ssub_thm, FUN_FMAP_DEF] >>
  ‘A ∩ (cFV M0 DELETE v) ∩ cFV M0 = A ∩ cFV M0’ by ASM_SET_TAC[] >>
  ‘FINITE (A ∩ (cFV M0 DELETE v))’ by simp[] >>
  metis_tac[]
QED

Theorem FUN_FMAP_ssub_subset:
  ∀(M:'a cterm) D0 D.
    cFV M ⊆ D0 ∧ D0 ⊆ D ∧ FINITE D ⇒
    FUN_FMAP f D ' M = FUN_FMAP f D0 ' M
Proof
  rw[] >> simp[SimpLHS, Once FUN_FMAP_ssub_restrict] >>
  ‘FINITE D0’ by metis_tac[SUBSET_FINITE_I] >>
  simp[SimpRHS, Once FUN_FMAP_ssub_restrict] >>
  cong_tac (SOME 2) >>
  ASM_SET_TAC[]
QED

Theorem FUN_FMAP_ssub_cFV:
  cFV M ⊆ D ∧ FINITE D ⇒ FUN_FMAP f D ' M = FUN_FMAP f (cFV M) ' M
Proof
  strip_tac >> irule FUN_FMAP_ssub_subset >> simp[]
QED

Theorem wf_Closure_Real_ground_lemma:
  ∀t fm D.
    (∀k. k ∈ FDOM fm ⇒ wf_Closure (fm ' k) ∧ closed (Real (fm ' k))) ∧
    D ⊆ FDOM fm
    ⇒
    cFV (FUN_FMAP (λx. Real (fm ' x)) D ' t) = cFV t DIFF D
Proof
  ho_match_mp_tac cterm_bvc_induction >>
  qexists ‘supp (fm_pmact string_pmact (fmt_pmact cterm_pmact string_pmact))’ >>
  simp[fmap_supp, FINITE_supp_fmtpm, supp_setpm, PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >~
  [‘VAR v’]
  >- (‘FINITE D’ by metis_tac[FDOM_FINITE, SUBSET_FINITE_I] >>
      simp[FUN_FMAP_DEF, AllCaseEqs(), SF CONJ_ss] >>
      rename [‘v ∈ D ∧ _ ∨ v ∉ D’] >> Cases_on ‘v ∈ D’ >> simp[] >>
      first_x_assum (irule o cj 2) >> gvs[SUBSET_DEF]) >~
  [‘cFV M DIFF D ∪ (cFV N DIFF D)’]
  >- SET_TAC[] >>
  dep_rewrite.DEP_REWRITE_TAC[ssub_thm] >>
  ‘FINITE D’ by metis_tac[FDOM_FINITE, SUBSET_FINITE_I] >>
  simp[FUN_FMAP_DEF] >> rw[] >~
  [‘v ∉ D (* g *)’, ‘v ∉ FDOM fm’, ‘D ⊆ FDOM fm’]
  >- ASM_SET_TAC[] >~
  [‘v ∉ cFV (Real (fm ' k))’, ‘k ∈ D’] >- metis_tac[SUBSET_DEF, NOT_IN_EMPTY] >>
  ASM_SET_TAC[]
QED

Theorem wf_Closure_Real_ground:
  ∀Cl.
    wf_Closure Cl ⇒ cFV (Real Cl) = ∅
Proof
  Induct using ft_ind >> simp[] >> rpt strip_tac >> gvs[] >>
  rename [‘cFV t ⊆ FDOM E’] >>
  qspecl_then [‘t’, ‘E’, ‘cFV t’] mp_tac wf_Closure_Real_ground_lemma >>
  simp[] >> simp[GSYM Real_thm]
QED

Theorem Real_CONST[simp]:
  Real ⟨ CONST c ∶ E ⟩ = CONST c
Proof
  simp[Real_def, fmtreerec_thm]
QED

Theorem Real_APP[simp]:
  Real ⟨ M @@ N ∶ E ⟩ = Real ⟨ M ∶ E ⟩ @@ Real ⟨ N ∶ E ⟩
Proof
  simp[Real_def, fmtreerec_thm]
QED

Theorem Real_VAR:
  Real ⟨ VAR v ∶ E ⟩ = case FLOOKUP E v of
                         NONE => VAR v
                       | SOME cl => Real cl
Proof
  simp[Real_def, fmtreerec_thm] >> Cases_on ‘FLOOKUP E v’ >>
  gvs[flookup_thm]
QED

Theorem ssub_DRESTRICT_FV:
  ∀M fm. ssub (DRESTRICT fm $ cFV M) M = ssub fm M
Proof
  ho_match_mp_tac cterm_bvc_induction >>
  qexists ‘subFV’ >> simp[] >>
  simp[ssub_thm, DRESTRICT_DEF] >> rw[] >>~-
  ([‘DRESTRICT fm (_ ∪ _) ' M = fm ' M’],
   qpat_x_assum ‘∀fm. DRESTRICT fm _ ' M = fm ' M’
                (ONCE_REWRITE_TAC o single o GSYM) >>
   simp[DRESTRICT_DRESTRICT] >> cong_tac NONE >>
   SET_TAC[]) >~
  [‘DRESTRICT fm (_ DELETE _) ' M = fm ' M’] >>
  qpat_x_assum ‘∀fm. DRESTRICT fm _ ' M = fm ' M’
               (ONCE_REWRITE_TAC o single o GSYM) >>
  simp[DRESTRICT_DRESTRICT] >>
  cong_tac (SOME 1) >>
  simp[fmap_EXT, DRESTRICT_DEF] >>
  ASM_SET_TAC[]
QED

Theorem Real_LAM:
  wf_Closure ⟨ LAM v M ∶ E ⟩ ⇒
  Real  ⟨ LAM v M ∶ E ⟩ = LAM v (Real ⟨ M ∶ E \\ v ⟩)
Proof[exclude_simps = wf_Closure_thm]
  simp[Real_thm] >> strip_tac >>
  dep_rewrite.DEP_REWRITE_TAC[ssub_thm] >>
  simp[] >> rpt strip_tac
  >- (gvs[FUN_FMAP_DEF, wf_Closure_thm] >>
      rename [‘cFV (Real (E ' u))’] >>
      ‘u ∈ FDOM E’ by ASM_SET_TAC[] >>
      metis_tac[wf_Closure_Real_ground, NOT_IN_EMPTY]) >>
  simp[Real_def, fmtreerec_thm] >>
  ONCE_REWRITE_TAC [GSYM ssub_DRESTRICT_FV] >>
  cong_tac (SOME 1) >>
  simp[DRESTRICT_DEF, fmap_EXT] >> gvs[wf_Closure_thm] >> rpt strip_tac >~
  [‘_ ∩ _ = _ ∩ _ (* g *)’] >- ASM_SET_TAC[] >>
  gvs[SUBSET_DEF, DOMSUB_FAPPLY_THM, FUN_FMAP_DEF]
QED

Theorem ssub_update:
  ∀M.
    (∀k. k ∈ FDOM fm ∧ k ≠ v ⇒ cFV (fm ' k) = ∅) ⇒
    ssub (fm |+ (v,N)) M = [N/v] (ssub (fm \\ v) M)
Proof
  ho_match_mp_tac cterm_induction >>
  qexists ‘fmFV string_pmact cterm_pmact fm ∪ {v} ∪ cFV N’ >> simp[] >> rw[] >>
  simp[FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM, lemma14b] >> gvs[] >>
  rename [‘ssub (fm |+ (v,N)) (LAM u M) = _’] >>
  dep_rewrite.DEP_REWRITE_TAC[ssub_thm] >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[FAPPLY_FUPDATE_THM]
QED

Theorem RIGHT_FORALL_DISJ_THM[local] =
  METIS_PROVE[] “(∀x. P ∨ Q x) ⇔ P ∨ ∀x. Q x”

Theorem lemma1_0:
  ∀M E x NCl.
    wf_Closure NCl ∧ (∀k. k ∈ FDOM E ∧ k ≠ x ⇒ wf_Closure (E ' k)) ⇒
    Real ⟨ M ∶ E |+ (x, NCl) ⟩ = [Real NCl/x] (Real ⟨ M ∶ E \\ x ⟩)
Proof[exclude_simps = wf_Closure_thm]
  ‘∀M exn E x NCl.
     exn = (E,x,NCl) ∧
     wf_Closure NCl ∧ (∀k. k ∈ FDOM E ∧ k ≠ x ⇒ wf_Closure (E ' k)) ⇒
     Real ⟨ M ∶ E |+ (x, NCl) ⟩ = [Real NCl/x] (Real ⟨ M ∶ E \\ x ⟩)’
    suffices_by simp[] >>
  ho_match_mp_tac cterm_bvc_induction >>
  qexists ‘λ(E,x,NCl). eFV E ∪ {x} ∪ clFV NCl’>>
  simp[pairTheory.FORALL_PROD] >> rw[] >~
  [‘⟨ VAR v ∶ E |+ (u,NCl)⟩ (* sg *)’]
  >- (qabbrev_tac ‘rn = Real NCl’ >> simp[Real_def, fmtreerec_thm] >>
      Cases_on ‘u = v’ >> simp[FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM]
      >- simp[Abbr‘rn’, Real_def] >>
      rw[] >> simp[GSYM Real_def] >>
      simp[lemma14b, wf_Closure_Real_ground]) >~
  [‘⟨ LAM v M ∶ E |+ (u,NCl)⟩ (* sg *)’] >>
  qabbrev_tac ‘rn = Real NCl’ >> simp[Real_def, fmtreerec_thm] >>
  simp[GSYM Real_def] >> dep_rewrite.DEP_REWRITE_TAC[ssub_thm] >> simp[] >>
  gvs[fmap_supp, supp_setpm, GSYM RIGHT_FORALL_DISJ_THM] >>
  simp[FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM] >> rw[] >>
  simp[wf_Closure_Real_ground, Abbr‘rn’] >>
  dep_rewrite.DEP_REWRITE_TAC[ssub_update] >>
  simp[wf_Closure_Real_ground]
QED

Theorem sub_ssub_thm:
  ∀M.
    v ∉ FDOM fm ∧ (∀k. k ∈ FDOM fm ⇒ v ∉ cFV (fm ' k)) ∧
    FDOM fm ∩ cFV N = ∅ ⇒
    [N/v] (fm ' M) = fm ' ([N/v]M)
Proof
  ho_match_mp_tac cterm_induction >>
  qexists ‘{v} ∪ cFV N ∪ subFV fm’ >> simp[] >> rw[SUB_VAR] >>
  gvs[lemma14b] >> metis_tac[ssub_14b, INTER_COMM]
QED

Theorem ssub_domsub:
  ∀ct. v ∉ cFV ct ⇒ ssub (fm \\ v) ct = ssub fm ct
Proof
  ho_match_mp_tac cterm_induction >>
  qexists ‘subFV fm ∪ {v}’ >> simp[ssub_def, DOMSUB_FAPPLY_THM]
QED


(* p131 *)
(* Plotkin has isVClosure for both terms rather than wf_Closure, but
   the "value" nature of these don't contribute *)
Theorem lemma3_1:
  wf_Closure (mkClos (LAM y M) E) ∧ wf_Closure (mkClos N E') ∧
  Real (mkClos (LAM y M) E) = LAM x M' ∧ Real (mkClos N E') = N' ⇒
  Real (mkClos M (E |+ (y,mkClos N E'))) = [N'/x] M'
Proof
  rpt strip_tac >> dep_rewrite.DEP_REWRITE_TAC[lemma1_0] >>
  gvs[] >>
  qabbrev_tac ‘rn = Real ⟨N ∶ E'⟩’ >>
  ‘cFV rn = ∅’ by simp[Abbr‘rn’, wf_Closure_Real_ground] >>
  qpat_x_assum ‘Real (mkClos (LAM y M) E) = _’ mp_tac >>
  simp[Real_LAM, LAM_eq_thm] >> rw[] >>~-
  ([‘wf_Closure _ (* g *)’], gvs[wf_Closure_thm]) >>
  simp[ctpm_subst_out, ctpm_fresh] >>
  irule ctpm_fresh >> rw[cFV_SUB]
QED

Theorem Real_EQ_LAM:
  isVClosure cl ∧ Real cl = LAM v M ⇒
  ∃v0 M0 E. cl = ⟨ LAM v0 M0 ∶ E ⟩
Proof
  Cases_on ‘cl’ using fmaptree_nchotomy >>
  simp[Real_thm, isVClosure_thm, SF CONJ_ss] >>
  rename [‘ssub _ ct’] >> Cases_on ‘ct’ using cterm_CASES >>
  rw[ssub_thm] >> irule_at Any EQ_REFL
QED

Theorem Real_EQ_CONST:
  isVClosure cl ∧ Real cl = CONST c ⇒
  ∃E. cl = ⟨ CONST c ∶ E ⟩
Proof[exclude_simps = wf_Closure_thm]
  Cases_on ‘cl’ using fmaptree_nchotomy >>
  simp[isVClosure_thm, SF CONJ_ss] >>
  rename [‘is_abs ct ∨ is_const ct’] >>
  Cases_on ‘ct’ using cterm_CASES >> simp[] >>
  rename [‘wf_Closure ⟨ LAM u M ∶ E ⟩’] >>
  Cases_on ‘wf_Closure ⟨ LAM u M ∶ E ⟩’ >>
  simp[Real_LAM]
QED

Theorem isVEnv_Real:
  ∀E v. isVEnv E ∧ v ∈ FDOM E ⇒
        (∃c. Real (E ' (v:string)) = CONST c) ∨
        (∃u M. Real (E ' v) = LAM u M)
Proof
  ONCE_REWRITE_TAC [isVClosure_cases] >> rw[] >>
  first_x_assum $ drule_then assume_tac >>
  rename [‘isVClosure (E ' v)’] >>
  Cases_on ‘E ' v’ using fmaptree_nchotomy >>
  gvs[isVClosure_thm, is_abs_def, is_const_def, Real_LAM] >>
  irule_at Any EQ_REFL
QED

(* p131–2 *)
(* statement is
    “Suppose E is a value environment and ⟨M,E⟩ is a closure and M'' is the
     value of Real (⟨M,E⟩) at time t. Then for all S, E, C and D, with
     FV(C) ⊆ Dom(E) and some t' ≥ t, ⟨S,E,M:C,D⟩ ⇒^{t'} (⟨M',E'⟩:S,E,C,D⟩
     where ⟨M',E'⟩ is a value closure and Real (⟨M',E'⟩) = M''.”
   Assume that the shadowing of E in the universal quantification is
   unintended and that the qualified E and the outermost E are the same.
*)
Theorem lemma3_2:
  ∀t M M'' S E C D.
    isVEnv E ∧ wf_Closure ⟨M ∶ E⟩ ∧ timed_eval t (Real ⟨M ∶ E⟩) M'' ⇒
    isDump ((S,E,C)::D) ∧ cstrsFV C ⊆ FDOM E ⇒
    ∃t' M' E'.
      t ≤ t' ∧ NRC dumpTrans t' ((S,E,Tm M::C)::D) ((⟨M'∶E'⟩::S,E,C)::D) ∧
      isVClosure ⟨M'∶E'⟩ ∧ Real ⟨M'∶E'⟩ = M''
Proof
  gen_tac >> completeInduct_on ‘t’ >> Cases_on ‘M’ using cterm_CASES >~
  [‘CONST c’] (* Case 1 *)
  >- (simp[] >> rw[] >>
      qexists ‘1’ >> simp[Once dumpTrans_cases] >>
      simp[isVClosure_thm]) >~
  [‘LAM v M’] (* Case 2 *)
  >- (simp[Real_LAM, SF CONJ_ss] >> rw[] >>
      qexists ‘1’>>
      simp[Once dumpTrans_cases, PULL_EXISTS] >>
      irule_at Any EQ_REFL >>
      simp[isVClosure_thm, Excl "wf_Closure_thm", SF CONJ_ss, Real_LAM] >>
      simp[]) >~
  [‘VAR v’] (* Case 3, p132 *)
  >- (simp[Real_thm, SF CONJ_ss, FUN_FMAP_DEF] >> rw[] >>
      ‘M'' = Real (E ' v) ∧ t = 1’
        by (drule_then (drule_then strip_assume_tac) isVEnv_Real >>
            gvs[]) >> gvs[] >>
      qexists ‘1’ >> simp[] >>
      simp[Once dumpTrans_cases] >>
      Cases_on ‘E ' v’ using fmaptree_nchotomy >>
      irule_at Any EQ_REFL >> simp[] >>
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE[isVClosure_cases]) >> metis_tac[]) >~
  [‘M₁ @@ M₂’] (* Case 4, p132 *) >>
  simp[] >> rw[] >>
  qabbrev_tac ‘N₁ = Real ⟨M₁ ∶ E⟩’ >>
  qabbrev_tac ‘N₂ = Real ⟨M₂ ∶ E⟩’ >>
  qpat_x_assum ‘timed_eval t _ _’ mp_tac >>
  simp[Once timed_eval_cases] >> strip_tac >~
  (* Subcase 1, p132 *)
  [‘timed_eval t1 N₁ (LAM x N₃)’, ‘timed_eval t2 N₂ N₄’,
   ‘timed_eval t3 ([N₄/x]N₃) M''’, ‘t = t1 + (t2 + (t3 + 1))’]
  >- (irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
      simp[dumpTrans_cases] >>
      Q.UNABBREV_TAC ‘N₂’ >>
      first_assum (qpat_x_assum ‘timed_eval _ (Real _) _’ o
                   mp_then Any mp_tac) >> simp[] >>
      disch_then (qspecl_then [‘S’, ‘Tm M₁::Ap::C’, ‘D’] mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >>
      disch_then (qx_choosel_then [‘t2'’, ‘M₂'’, ‘E₂'’] strip_assume_tac) >>
      irule_at Any arithmeticTheory.NRC_ADD_I >>
      first_x_assum $ irule_at (Pat ‘NRC _ _ _ _’) >>
      Q.UNABBREV_TAC ‘N₁’ >>
      first_assum (qpat_x_assum ‘timed_eval _ (Real _) _’ o
                   mp_then Any mp_tac) >> simp[] >>
      disch_then (qspecl_then [‘⟨ M₂' ∶ E₂'⟩ :: S’, ‘Ap::C’, ‘D’] mp_tac) >>
      impl_tac
      >- (gvs[DISJ_IMP_THM, FORALL_AND_THM, isVClosure_thm] >> metis_tac[]) >>
      disch_then (qx_choosel_then [‘t1'’, ‘M₁'’, ‘E₁'’] strip_assume_tac) >>
      irule_at Any arithmeticTheory.NRC_ADD_I >>
      first_x_assum $ irule_at (Pat ‘NRC _ _ _ _’) >>
      irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
      drule_all Real_EQ_LAM >> simp[PULL_EXISTS] >>
      simp[dumpTrans_cases, PULL_EXISTS] >> rw[] >>
      irule_at Any EQ_REFL >>
      drule_at (Pat ‘Real _ = LAM _ _’) lemma3_1 >>
      simp[isVClosure_wf_Closure, Excl "wf_Closure_thm"] >>
      ‘wf_Closure ⟨ M₂' ∶ E₂'⟩’
        by simp[isVClosure_wf_Closure, Excl "wf_Closure_thm"] >>
      disch_then $ drule_then (assume_tac o SYM) >> gvs[] >>
      first_x_assum (qpat_assum ‘timed_eval _ _ _’ o mp_then Any mp_tac) >>
      simp[Excl "wf_Closure_thm"] >>
      disch_then (qspecl_then [‘[]’, ‘[]’, ‘(S,E,C)::D’] mp_tac)>> simp[] >>
      impl_tac
      >- (gvs[isVClosure_thm, DISJ_IMP_THM, FORALL_AND_THM, SF SFY_ss] >>
          rpt conj_tac >> rw[FAPPLY_FUPDATE_THM] >>~-
          ([‘isVEnv _ (* g *)’],
           gvs[cj 2 isVClosure_cases, DOMSUB_FAPPLY_THM]) >>~-
          ([‘_ ⊆ _ (* g *)’], ASM_SET_TAC[]) >>
          gvs[FLOOKUP_SIMP, AllCaseEqs()] >> gvs[flookup_thm]) >>
      disch_then (qx_choosel_then [‘t3'’, ‘M₃'’, ‘E'’] strip_assume_tac) >>
      irule_at Any arithmeticTheory.NRC_ADD_I >>
      first_assum $ irule_at (Pat ‘NRC _ _ _ _ ’) >>
      irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
      simp[dumpTrans_cases] >>
      irule_at Any (iffRL $ cj 1 arithmeticTheory.NRC) >>
      irule_at Any EQ_REFL >> simp[]) >>
  (* Subcase 2, p132 *)
  rename [‘timed_eval t1 N₁ (CONST a)’, ‘timed_eval t2 N₂ (CONST b)’,
          ‘t = t1 + (t2 + 1)’] >>
  irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
  simp[dumpTrans_cases] >>
  Q.UNABBREV_TAC ‘N₂’ >>
  first_assum (qpat_x_assum ‘timed_eval _ (Real _) _’ o
                            mp_then Any mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘S’, ‘Tm M₁::Ap::C’, ‘D’] mp_tac) >>
  simp[SF SFY_ss] >>
  disch_then (qx_choosel_then [‘t2'’, ‘M₂'’, ‘E₂'’] strip_assume_tac) >>
  irule_at Any arithmeticTheory.NRC_ADD_I >>
  first_x_assum $ irule_at (Pat ‘NRC _ _ _ _ ’) >> gvs[] >>
  drule_all_then strip_assume_tac Real_EQ_CONST >>
  gvs[Real_thm, isVClosure_wf_Closure, ssub_thm, Excl "wf_Closure_thm"] >>
  rename [‘isVClosure ⟨ CONST b ∶ E₂'⟩’] >>
  Q.UNABBREV_TAC ‘N₁’ >>
  first_assum (qpat_x_assum ‘timed_eval _ (Real _) _’ o
                            mp_then Any mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘⟨CONST b ∶ E₂'⟩::S’, ‘Ap::C’, ‘D’] mp_tac) >>
  simp[SF SFY_ss, DISJ_IMP_THM, FORALL_AND_THM, Excl "wf_Closure_thm",
       isVClosure_wf_Closure] >>
  disch_then (qx_choosel_then [‘t1'’, ‘M₁'’, ‘E₁'’] strip_assume_tac) >>
  drule_all_then strip_assume_tac Real_EQ_CONST >>
  gvs[Real_thm, isVClosure_wf_Closure, ssub_thm, Excl "wf_Closure_thm"] >>
  irule_at Any arithmeticTheory.NRC_ADD_I >>
  first_x_assum $ irule_at (Pat ‘NRC _ _ _ _ ’) >> gvs[] >>
  irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
  simp[dumpTrans_cases] >>
  irule_at Any (iffRL $ cj 1 arithmeticTheory.NRC) >> irule_at Any EQ_REFL >>
  simp[isVClosure_thm, Excl "wf_Closure_thm", SF CONJ_ss,
       Real_thm] >>
  simp[SF CONJ_ss] >>
  map_every Cases_on [‘a’, ‘b’] >> gvs[constapply_def, AllCaseEqs()] >>
  simp[EXTENSION, EQ_IMP_THM]
QED

Definition errorState_def:
  errorState D ⇔ (∀D'. ¬dumpTrans D D') ∧ Unload D = NONE
End

Theorem timed_eval0[simp]:
  timed_eval 0 M N ⇔ F
Proof
  simp[Once timed_eval_cases]
QED

Theorem NRC_dumpTrans_app[local]:
  NRC dumpTrans t ((S,E,Tm(M @@ N)::C)::D) D' ⇔
    t = 0 ∧ D' = ((S,E,Tm(M@@N)::C)::D) ∨
    ∃t0. t = SUC t0 ∧ NRC dumpTrans t0 ((S,E,Tm N :: Tm M :: Ap :: C)::D) D'
Proof
  Cases_on ‘t’ >> simp[EQ_SYM_EQ] >>
  simp[arithmeticTheory.NRC] >>
  simp[SimpLHS, dumpTrans_cases]
QED

Theorem errorState_appC[simp]:
  ¬errorState ((S,E,Tm(M @@ N)::C)::D)
Proof
  simp[errorState_def, Once dumpTrans_cases]
QED

fun pull P l =
  case total (pluck P) l of NONE => l | SOME (x,rest) => x::rest

Theorem shorter_NRC_paths_exist:
  ∀m n x y. NRC R n x y ∧ m ≤ n ⇒ ∃y0. NRC R m x y0
Proof
  Induct_on ‘n’ >> simp[arithmeticTheory.NRC] >> Cases_on ‘m’ >> simp[] >>
  simp[arithmeticTheory.NRC] >> metis_tac[]
QED

(* “Suppose E is a value environment and ⟨M∶E⟩ is a closure.
    If Real(⟨M∶E⟩) has no value at any t' ≤ t, then either for all
    S, E, C, D, with FV(C) ⊆ Dom(E), (S,E,M::C)::D hits an error state
    or else (S,E,M::C)::D ⇒^t D' for some D'” *)
(* Plotkin refers to "lemma 1" a couple of times in the course of the
   proof; he actually means lemma 2. *)
Theorem lemma3_3:
  ∀t E M.
    1 ≤ t ∧ isVEnv E ∧ wf_Closure ⟨M∶E⟩ ∧
    (∀t' N. t' ≤ t ⇒ ¬timed_eval t' (Real⟨M∶E⟩) N) ⇒
    ∀S C D.
      isDump ((S,E,C)::D) ⇒
      (∃t' D'. NRC dumpTrans t' ((S,E,Tm M::C)::D) D' ∧ errorState D') ∨
      (∃D'. NRC dumpTrans t ((S,E,Tm M::C)::D) D')
Proof
  gen_tac >> completeInduct_on ‘t’ >> rpt strip_tac >>
  ‘∀c. Real ⟨M∶E⟩ ≠ CONST c’ by (rpt strip_tac >> gvs[]) >>
  ‘∀v. Real ⟨M∶E⟩ ≠ VAR v’ by (rpt strip_tac >> drule wf_Closure_Real_ground >>
                               simp[]) >>
  ‘∀v M0. Real ⟨ M ∶ E ⟩ ≠ LAM v M0’ by (rpt strip_tac >> gvs[]) >>
  ‘∃M₁ M₂. M = M₁ @@ M₂’
    by (Cases_on ‘M’ using cterm_CASES >>
        gvs[Excl "wf_Closure_thm", Real_LAM] >>
        rename [‘Real ⟨ VAR v ∶ E⟩’] >>
        gvs[] >>
        ‘∃cl. FLOOKUP E v = SOME cl’ by simp[flookup_thm] >>
        gvs[Real_VAR] >> gvs[flookup_thm] >>
        drule_all isVEnv_Real >> simp[]) >>
  gvs[] >> dsimp[NRC_dumpTrans_app] >>
  Cases_on ‘t’ >> gvs[] >> rename [‘_ < SUC t0’] >>
  reverse $ Cases_on ‘1 ≤ t0’ >> gvs[arithmeticTheory.NOT_LE] >>
  reverse $ Cases_on ‘∃t2 N₂. t2 ≤ t0 ∧ timed_eval t2 (Real ⟨ M₂ ∶ E ⟩) N₂’
  >- (gvs[] >>
      CONV_TAC (
        LAND_CONV $ RESORT_EXISTS_CONV (
          pull (fn t => type_of t = numSyntax.num)
        )
      ) >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[] >>
  drule_at (Pat ‘timed_eval _ _ _’) lemma3_2 >> simp[SF CONJ_ss] >>
  ‘cstrsFV (Tm M₁::Ap::C) ⊆ FDOM E’ by simp[] >>
  disch_then (pop_assum o mp_then Any mp_tac) >>
  disch_then $ drule_all_then strip_assume_tac >>
  rename [‘NRC dumpTrans t2' ((S,E,Tm M₂ :: Tm M₁ :: Ap :: C)::D) (_::_)’] >>
  Cases_on ‘t0 ≤ t2'’
  >- metis_tac[shorter_NRC_paths_exist] >>
  gvs[arithmeticTheory.NOT_LE] >>
  reverse $ Cases_on
      ‘∃nt N₁. nt ≤ t0 - t2' ∧ timed_eval nt (Real ⟨ M₁ ∶ E ⟩) N₁’
  >- (gvs[DECIDE “¬p ∨ q ⇔ p ⇒ q”] >>
      first_x_assum (pop_assum o mp_then Any mp_tac) >> simp[] >>
      ‘cstrsFV (Ap::C) ⊆ FDOM E’ by simp[] >>
      disch_then (pop_assum o mp_then Any mp_tac) >>
      rename [‘isVClosure ⟨ M₂' ∶ E₂' ⟩’] >>
      ‘∀cl. MEM cl (⟨ M₂' ∶ E₂'⟩ :: S) ⇒ wf_Closure cl’
        by gvs[isVClosure_thm, DISJ_IMP_THM] >>
      disch_then (drule_all_then strip_assume_tac)
      >- metis_tac[arithmeticTheory.NRC_ADD_I] >>
      ‘t2' + (t0 - t2') = t0’ by simp[] >>
      metis_tac[arithmeticTheory.NRC_ADD_I]) >>
  pop_assum (qx_choosel_then [‘t1’, ‘N₁’] strip_assume_tac) >>
  first_assum (mp_then Any mp_tac lemma3_2) >> simp[] >>
  rename [‘isVClosure ⟨ M₂' ∶ E₂' ⟩’] >>
  ‘∀cl. MEM cl (⟨ M₂' ∶ E₂'⟩ :: S) ⇒ wf_Closure cl’
    by gvs[isVClosure_thm, DISJ_IMP_THM] >>
  disch_then (pop_assum o mp_then Any mp_tac) >> simp[SF SFY_ss] >>
  ‘cstrsFV (Ap::C) ⊆ FDOM E’ by simp[] >>
  disch_then (pop_assum o mp_then Any mp_tac) >>
  disch_then $ drule_all_then strip_assume_tac >> gvs[] >>
  rename [‘NRC _ t1' _ ((⟨ M₁' ∶ E₁' ⟩ :: ⟨ M₂' ∶ E₂' ⟩ :: _, _, _)::_)’] >>
  Cases_on ‘t0 - t2' ≤ t1'’
  >- (‘t2' + (t0 - t2') = t0’ by simp[] >>
      disj2_tac >> pop_assum (SUBST1_TAC o SYM) >>
      irule_at Any arithmeticTheory.NRC_ADD_I >>
      first_assum $ irule_at Any >>
      metis_tac[shorter_NRC_paths_exist]) >>
  gvs[arithmeticTheory.NOT_LE] >>
  Cases_on ‘∃x M₃. M₁' = LAM x M₃’
  >- (gvs[] >>
      ‘dumpTrans ((⟨ LAM x M₃ ∶ E₁' ⟩ :: ⟨ M₂' ∶ E₂' ⟩ :: S,
                   E, Ap::C)::D)
                 (([],E₁' |+ (x, ⟨ M₂' ∶ E₂' ⟩), [Tm M₃])::(S,E,C)::D)’
        by (simp[Once dumpTrans_cases] >> irule_at Any EQ_REFL >> simp[]) >>
      Cases_on ‘t0 = t2' + t1' + 1’
      >- (disj2_tac >> pop_assum SUBST_ALL_TAC >>
          irule_at Any arithmeticTheory.NRC_ADD_I >>
          irule_at Any arithmeticTheory.NRC_ADD_I >>
          simp[] >> rpt (first_assum $ irule_at Any)) >>
      qabbrev_tac ‘E₃' = E₁' |+ (x, ⟨ M₂' ∶ E₂' ⟩)’ >>
      reverse $ Cases_on ‘∃t3 N₃. t3 ≤ t0 - t1' - t2' - 1 ∧
                                  timed_eval t3 (Real ⟨ M₃ ∶ E₃' ⟩) N₃’
      >- (gvs[DECIDE “¬p ∨ q ⇔ p ⇒ q”] >>
          first_x_assum (pop_assum o mp_then Any mp_tac) >>
          simp[Abbr‘E₃'’, isVClosure_thm, DISJ_IMP_THM, FORALL_AND_THM,
               FAPPLY_FUPDATE_THM] >>
          ‘cFV M₃ ⊆ x INSERT FDOM E₁' ∧ cFV M₂' ⊆ FDOM E₂' ∧
           (∀s. s ∈ FDOM E₂' ⇒ wf_Closure (E₂' ' s))’
            by (gvs[isVClosure_thm] >> ASM_SET_TAC[]) >>
          simp[] >>
          ‘cstrsFV [] ⊆ x INSERT FDOM E₁'’ by simp[] >>
          disch_then (drule_at (Pat ‘cstrsFV _ ⊆ _’)) >>
          ‘isDump ((S,E,C)::D)’ by simp[flookup_thm] >>
          disch_then (pop_assum o mp_then Any mp_tac) >>
          disch_then (qspec_then ‘[]’ mp_tac) >> simp[] >>
          impl_tac
          >- (gvs[isVClosure_thm] >>
              gvs[cj 2 isVClosure_cases, DOMSUB_FAPPLY_THM] >>
              simp[flookup_thm, DISJ_IMP_THM, FAPPLY_FUPDATE_THM,
                   FORALL_AND_THM] >>
              rw[]) >>
          strip_tac
          >- (disj1_tac >> irule_at Any arithmeticTheory.NRC_ADD_I >>
              first_assum $ irule_at (Pat ‘NRC _ _ (_::_) _’) >>
              irule_at Any arithmeticTheory.NRC_ADD_I >>
              first_assum $ irule_at (Pat ‘NRC _ _ (_::_) _’) >>
              irule_at Any (iffRL $ cj 2 arithmeticTheory.NRC) >>
              first_assum $ irule_at (Pat ‘dumpTrans _ _’) >>
              metis_tac[]) >>
          disj2_tac >>
          ‘t0 = (t2' + t1' + 1) + (t0 - (t1' + t2' + 1))’ by simp[] >>
          pop_assum SUBST1_TAC >> irule_at Any arithmeticTheory.NRC_ADD_I >>
          irule_at Any arithmeticTheory.NRC_ADD_I >>
          irule_at Any arithmeticTheory.NRC_ADD_I >> simp[] >> metis_tac[]) >>
      gvs[] >>
      ‘t1 + t2 + t3 + 1 ≤ SUC t0’ by simp[] >>
      ‘F’ suffices_by simp[] >>
      first_x_assum (pop_assum o mp_then Any mp_tac) >>
      simp_tac bool_ss [] >>
      qexists ‘N₃’ >>
      irule timed_eval_app_tm >>
      first_assum $ irule_at Any >>
      ‘Real ⟨LAM x M₃ ∶ E₁'⟩ = LAM x (Real ⟨M₃ ∶ E₁' \\ x⟩)’
        by (irule Real_LAM >> gvs[isVClosure_thm]) >> gvs[] >>
      first_assum $ irule_at Any >>
      dep_rewrite.DEP_REWRITE_TAC[GSYM lemma1_0] >> conj_tac
      >- gvs[isVClosure_thm] >>
      simp[Abbr‘E₃'’]) >>
  Cases_on ‘∃a b N. M₁' = CONST a ∧ M₂' = CONST b ∧ constapply a b = SOME N’
  >- (gvs[] >>
      ‘t1 + t2 + 1 ≤ SUC t0’ by simp[] >>
      ‘F’ suffices_by simp[] >>
      first_x_assum (pop_assum o mp_then Any mp_tac) >>
      simp_tac bool_ss [] >> qexists ‘N’ >>
      irule timed_eval_app_const >> metis_tac[]) >>
  disj1_tac >>
  irule_at Any arithmeticTheory.NRC_ADD_I >>
  first_assum $ irule_at Any >>
  first_assum $ irule_at Any >>
  simp[errorState_def]>> conj_tac
  >- (simp[Once dumpTrans_cases] >> gvs[]) >>
  Cases_on ‘D’ >> simp[Unload_def]
QED

Theorem Unload_EQ_SOME:
  Unload D = SOME M ⇔
  ∃Cl. D = [([Cl], FEMPTY, [])] ∧ M = Real Cl
Proof
  Cases_on ‘D’>> simp[Unload_def] >> rename [‘Unload (sec::rest)’] >>
  Cases_on ‘rest’ >> simp[Unload_def] >> PairCases_on ‘sec’ >>
  Cases_on ‘sec0’ >> simp[Unload_def] >>
  Cases_on ‘sec2’ >> simp[Unload_def] >>
  rename [‘Unload [(s1::rests,_)]’] >>
  Cases_on ‘rests’ >> simp[Unload_def] >>
  metis_tac[]
QED

Theorem dumpTrans_nf:
  Unload D2 = SOME N ⇒ ∀D'. ¬dumpTrans D2 D'
Proof
  simp[Unload_EQ_SOME] >> rw[] >>
  simp[Once dumpTrans_cases]
QED

Theorem R_det_RTC_det:
  (∀x y z. R x y ∧ R x z ⇒ y = z) ⇒
  ∀a b c. R꙳ a b ∧ R꙳ a c ∧ (∀b'. ¬R b b') ∧ (∀c'. ¬R c c') ⇒
          b = c
Proof
  strip_tac >> Induct_on ‘RTC’ >> rw[]
  >- (qpat_x_assum ‘R꙳ _ _’ mp_tac >> simp[Once relationTheory.RTC_CASES1]) >>
  rename [‘b = c (* g *)’, ‘R꙳ a c’] >> qpat_x_assum ‘R꙳ a c’ mp_tac >>
  simp[Once relationTheory.RTC_CASES1] >> rw[] >- gvs[] >>
  metis_tac[]
QED

Definition raw_controlpm_def[simp]:
  raw_controlpm π Ap = Ap ∧
  raw_controlpm π (Tm t) = Tm (ctpm π t)
End

Definition control_pmact_def:
  control_pmact = mk_pmact raw_controlpm
End

Theorem controlpm_def:
  pmact control_pmact = raw_controlpm
Proof
  simp[GSYM pmact_bijections, control_pmact_def] >>
  simp[is_pmact_def] >> rw[]
  >- (Cases_on ‘x’ >> simp[])
  >- (Cases_on ‘x’ >> simp[pmact_append]) >>
  simp[FUN_EQ_THM] >> Cases >> simp[] >>
  metis_tac[pmact_permeq]
QED

Theorem controlpm_thm[simp] = REWRITE_RULE[SYM controlpm_def] raw_controlpm_def

Overload dump_pmact = “list_pmact (pair_pmact (list_pmact clpmact)
                   (pair_pmact env_pmact (list_pmact control_pmact)))”

(* mixture of invariant and alpha-equivalence like correspondence *)
Definition dumpEQ_def:
  dumpEQ d1 d2 ⇔
    LIST_REL (λ(s1,e1,cs1) (s2,e2,cs2).
                isVEnv e1 ∧ isVEnv e2 ∧
                cstrsFV cs1 ⊆ FDOM e1 ∧ cstrsFV cs2 ⊆ FDOM e2 ∧
                (∀cl. MEM cl s1 ⇒ isVClosure cl) ∧
                (∀cl. MEM cl s2 ⇒ isVClosure cl) ∧
                MAP Real s1 = MAP Real s2 ∧
                LIST_REL (λc1 c2. c1 = Ap ∧ c2 = Ap ∨
                                  ∃t1 t2. c1 = Tm t1 ∧ c2 = Tm t2 ∧
                                          Real ⟨ t1 ∶ e1 ⟩ = Real ⟨ t2 ∶ e2 ⟩)
                         cs1 cs2)
             d1 d2 ∧
    0 < LENGTH d1 ∧
    FST (SND (LAST d1)) = FEMPTY ∧
    FST (SND (LAST d2)) = FEMPTY
End

val _ = temp_set_mapped_fixity{
  fixity = Infix(NONASSOC, 450),
  term_name = "dumpEQ",
  tok = "≈"
  }

Theorem constapply_ground:
  constapply a b = SOME M ⇒ closed M
Proof
  map_every Cases_on [‘a’, ‘b’] >> simp[constapply_def] >> rw[] >> simp[] >>
  simp[EXTENSION] >> simp[EQ_IMP_THM]
QED

Theorem constapply_value:
  constapply a b = SOME M ⇒ is_abs M ∨ is_const M
Proof
  map_every Cases_on [‘a’, ‘b’] >> simp[constapply_def] >> rw[] >> simp[]
QED

Theorem clFV_SUBSET_eFV:
  k ∈ FDOM fm ∧ a ∈ clFV (fm ' k) ⇒ a ∈ eFV fm
Proof
  simp[fmap_supp, supp_setpm, DECIDE “¬p ∨ q ⇔ p ⇒ q”, PULL_EXISTS] >>
  strip_tac >>
  ‘fm ' k ∈ FRANGE fm’ by (simp[TO_FLOOKUP, NoAsms] >> simp[flookup_thm] >>
                           metis_tac[]) >>
  metis_tac[]
QED

Theorem cFV_Real_SUBSET_clFV:
  ∀Cl z. z ∈ cFV (Real Cl) ⇒ z ∈ clFV Cl
Proof
  simp[Real_def] >> Induct_on ‘Cl’ using ft_ind >>
  simp[fmtreerec_thm, supp_fmtpm] >> gen_tac >> strip_tac >>
  CCONTR_TAC >> qpat_x_assum ‘z ∈ cFV _’ mp_tac >> simp[] >>
  irule fresh_ssub >> gvs[] >> gen_tac >> rpt strip_tac >>
  first_x_assum drule_all >> metis_tac[clFV_SUBSET_eFV]
QED

Theorem Real_LAM_NEQ_APP[simp]:
  Real ⟨ LAM v M ∶ E⟩ ≠ N @@ P
Proof
  simp[Real_def, fmtreerec_thm] >>
  rename [‘LAM v M’, ‘_ o_f E’] >>
  Q_TAC (NEW_TAC "z") ‘{v} ∪ cFV M ∪ eFV E’ >>
  ‘LAM v M = LAM z (ctpm[(z,v)] M)’ by simp[ctpm_ALPHA] >>
  simp[] >> rpt gen_tac >>
  qmatch_abbrev_tac ‘FM ' _ ≠ _’ >>
  ‘z ∉ FDOM FM’ by (simp[Abbr‘FM’] >> gvs[fmap_supp]) >>
  ‘∀k. k ∈ FDOM FM ⇒ z ∉ cFV (FM ' k)’ suffices_by
    (strip_tac >> simp[ssub_thm]) >>
  rpt strip_tac >>
  gvs[Abbr‘FM’, GSYM Real_def] >>
  metis_tac[cFV_Real_SUBSET_clFV, clFV_SUBSET_eFV]
QED

Theorem Real_LAM_NEQ_CONST[simp]:
  Real ⟨ LAM v M ∶ E⟩ ≠ CONST c
Proof
  simp[Real_def, fmtreerec_thm] >>
  rename [‘LAM v M’, ‘_ o_f E’] >>
  Q_TAC (NEW_TAC "z") ‘{v} ∪ cFV M ∪ eFV E’ >>
  ‘LAM v M = LAM z (ctpm[(z,v)] M)’ by simp[ctpm_ALPHA] >>
  simp[] >> rpt gen_tac >>
  qmatch_abbrev_tac ‘FM ' _ ≠ _’ >>
  ‘z ∉ FDOM FM’ by (simp[Abbr‘FM’] >> gvs[fmap_supp]) >>
  ‘∀k. k ∈ FDOM FM ⇒ z ∉ cFV (FM ' k)’ suffices_by
    (strip_tac >> simp[ssub_thm]) >>
  rpt strip_tac >>
  gvs[Abbr‘FM’, GSYM Real_def] >>
  metis_tac[cFV_Real_SUBSET_clFV, clFV_SUBSET_eFV]
QED

Theorem dumpTrans_det:
  ∀a1 a2 b c. dumpEQ a1 a2 ∧ dumpTrans a1 b ∧ dumpTrans a2 c ⇒ dumpEQ b c
Proof
  Induct_on ‘dumpTrans’ >> rpt conj_tac >>
  simp[Once dumpTrans_cases] >> rw[] >>
  gvs[dumpEQ_def, fmtpm_thm, Real_VAR, AllCaseEqs(), flookup_thm,
      DISJ_IMP_THM, FORALL_AND_THM, cj 2 isVClosure_cases,
      isVClosure_wf_Closure] >> rpt strip_tac >>~-
  ([‘_ = FEMPTY (* g *)’, ‘LIST_REL _ (D1 : Dump) (D2 : Dump)’],
   Cases_on ‘D1’ >> Cases_on ‘D2’ >> gvs[]) >>~-
  ([‘isVClosure (_ ' k) (* g *)’],
   rw[FAPPLY_FUPDATE_THM] >> gvs[isVClosure_thm] >>
   gvs[cj 2 isVClosure_cases]) >>~-
  ([‘isVClosure _ (* g *)’],
   simp[isVClosure_thm] >> simp[cj 2 isVClosure_cases, isVClosure_wf_Closure] >>
   metis_tac [constapply_ground, constapply_value]) >>~-
  ([‘v ∈ FDOM E (* a *)’],
   drule_at (Pat ‘v ∈ FDOM E’) isVEnv_Real >>
   simp[cj 2 isVClosure_cases]) >>~-
  ([‘_ ⊆ _ (* g *)’], gvs[isVClosure_thm] >> ASM_SET_TAC[]) >~
  [‘Real ⟨LAM v1 M1 ∶ E1⟩ = Real ⟨LAM v2 M2 ∶ E2⟩’] >>
  ‘wf_Closure ⟨LAM v1 M1 ∶ E1⟩ ∧ wf_Closure ⟨LAM v2 M2 ∶ E2⟩’
    by simp[isVClosure_wf_Closure, Excl "wf_Closure_thm"] >>
  ‘Real ⟨LAM v1 M1 ∶ E1⟩ = LAM v1 (Real⟨M1 ∶ E1 \\ v1⟩) ∧
   Real ⟨LAM v2 M2 ∶ E2⟩ = LAM v2 (Real⟨M2 ∶ E2 \\ v2⟩)’
    by simp[Real_LAM, IgnAsm ‘Real _ = Real _’] >>
  ntac 2 (pop_assum $ mp_then Any mp_tac lemma3_1) >>
  simp[Excl "wf_Closure_thm"] >>
  rename [‘Real Cl1 = Real Cl2’, ‘E1 |+ (v1,Cl1)’, ‘E2 |+ (v2,Cl2)’] >>
  Cases_on ‘Cl1’ using fmaptree_nchotomy >>
  Cases_on ‘Cl2’ using fmaptree_nchotomy >>
  rename [‘Real ⟨N1 ∶ E1'⟩ = Real⟨N2∶E2'⟩’,
          ‘E1 |+ (v1,⟨N1 ∶ E1'⟩)’, ‘E2 |+ (v2,⟨N2∶E2'⟩)’] >>
  simp[isVClosure_wf_Closure, Excl "wf_Closure_thm"] >> rpt strip_tac >>
  qpat_x_assum ‘Real ⟨LAM _ _ ∶ _⟩ = Real _’ mp_tac >>
  simp[Real_LAM] >> rw[LAM_eq_thm] >> simp[] >>
  simp[ctpm_subst_out] >>
  simp[ctpm_fresh, Excl "wf_Closure_thm", wf_Closure_Real_ground,
       isVClosure_wf_Closure] >>
  irule ctpm_fresh >> simp[cFV_SUB] >> rw[] >>
  simp[Excl "wf_Closure_thm", wf_Closure_Real_ground,
       isVClosure_wf_Closure]
QED

Theorem dumpEQ_SYM:
  dumpEQ d1 d2 ⇔ dumpEQ d2 d1
Proof
  ‘∀d1 d2. dumpEQ d1 d2 ⇒ dumpEQ d2 d1’ suffices_by metis_tac[] >>
  simp[dumpEQ_def] >> rpt strip_tac
  >- (irule listTheory.EVERY2_sym >> first_assum $ irule_at Any >>
      simp[pairTheory.FORALL_PROD] >> rw[] >>
      irule listTheory.EVERY2_sym >> first_assum $ irule_at Any>>
      simp[PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM]) >>
  metis_tac[listTheory.LIST_REL_LENGTH]
QED

Theorem isVClosure_noncases[simp]:
  ¬isVClosure ⟨ VAR v ∶ E ⟩ ∧ ¬isVClosure ⟨ M @@ N ∶ E ⟩
Proof
  simp[isVClosure_thm]
QED

Theorem dumpEQ_preserves_nf:
  dumpEQ d1 d2 ⇒ (nf dumpTrans d1 ⇔ nf dumpTrans d2)
Proof
  ‘∀d1 d2. dumpEQ d1 d2 ∧ nf dumpTrans d1 ⇒ nf dumpTrans d2’
    suffices_by metis_tac[dumpEQ_SYM] >>
  simp[relationTheory.nf_def] >>
  ‘∀d1 d2 y. dumpEQ d1 d2 ∧ dumpTrans d2 y ⇒ ∃y. dumpTrans d1 y’
    suffices_by metis_tac[] >>
  Induct_on ‘dumpTrans’ >>
  simp[dumpEQ_def, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD,
       listTheory.MAP_EQ_CONS] >>
  rw[] >>~-
  ([‘Tm t1::_ (* sg *)’],
   simp[dumpTrans_cases] >> simp[EXISTS_OR_THM] >>
   rename [‘t = VAR _ ∧ _ ∈ _’] >> Cases_on ‘t’ using cterm_CASES >> gvs[] >>
   irule_at Any EQ_REFL) >~
  [‘((Shd::Stl,E,[])::_::_) (* sg *)’]
  >- simp[dumpTrans_cases] >~
  [‘Ap::_’, ‘Real ⟨ LAM v M ∶ E⟩ = Real Abs’]
  >- (simp[dumpTrans_cases] >> simp[EXISTS_OR_THM] >>
      Cases_on ‘Abs’ using fmaptree_nchotomy >>
      simp[] >> rename [‘tm = LAM _ _ (* sg *)’] >>
      Cases_on ‘tm’ using cterm_CASES >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      irule_at Any EQ_REFL) >~
  [‘Ap::_’, ‘CONST c1 = Real _’]
  >- (simp[dumpTrans_cases] >> simp[EXISTS_OR_THM] >>
      rename [‘cl1 = ⟨CONST _ ∶ _⟩ ∧ cl2 = ⟨CONST _ ∶ _⟩ ∧ _’] >>
      Cases_on ‘cl1’ using fmaptree_nchotomy >>
      Cases_on ‘cl2’ using fmaptree_nchotomy >> gvs[] >>
      rename [‘t1 = CONST _ ∧ t2 = CONST _ ∧ _’] >>
      Cases_on ‘t1’ using cterm_CASES >> Cases_on ‘t2’ using cterm_CASES >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM])
QED

Theorem RTC_dumpTrans_det:
  ∀d1 d2 e1 e2.
    dumpEQ d1 d2 ∧ dumpTrans꙳ d1 e1 ∧ dumpTrans꙳ d2 e2 ∧
    nf dumpTrans e1 ∧ nf dumpTrans e2 ⇒
    dumpEQ e1 e2
Proof
  Induct_on ‘RTC’ >> rw[] >> gvs[] >~
  [‘dumpTrans꙳ d2 e2’, ‘d1 ≈ d2’, ‘nf dumpTrans e2’, ‘nf dumpTrans d1’]
  >- (‘nf dumpTrans d2’ by metis_tac[dumpEQ_preserves_nf] >>
      ‘e2 = d2’ suffices_by simp[] >>
      qpat_x_assum ‘dumpTrans꙳ _ _’ mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >>
      gvs[relationTheory.nf_def]) >~
  [‘dumpTrans d1 dA’, ‘dumpTrans꙳ dA e1’, ‘d1 ≈ d2’, ‘dumpTrans꙳ d2 e2’,
   ‘nf dumpTrans e2’]
  >- (‘¬nf dumpTrans d1’ by simp[SF SFY_ss, relationTheory.nf_def] >>
      ‘¬nf dumpTrans d2’ by metis_tac[dumpEQ_preserves_nf] >>
      ‘d2 ≠ e2’ by (strip_tac >> gvs[]) >>
      qpat_x_assum ‘dumpTrans꙳ d2 e2’ mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >> strip_tac >>
      metis_tac[dumpTrans_det])
QED

Theorem dumpEQ_Load:
  closed M ⇒ dumpEQ (Load M) (Load M)
Proof
  simp[dumpEQ_def, Load_def] >> simp[cj 2 isVClosure_cases]
QED

Theorem Eval_det:
  closed M ∧ Eval M N1 ∧ Eval M N2 ⇒ N1 = N2
Proof
  simp[Eval_def] >> rpt strip_tac >>
  rename [‘N1 = N2 (* g *)’, ‘Unload D1 = SOME N1’, ‘Unload D2 = SOME N2’] >>
  gvs[Unload_EQ_SOME] >>
  ‘Load M ≈ Load M’ by simp[dumpEQ_Load] >>
  ‘∀Cl. nf dumpTrans [([Cl], FEMPTY, [])]’
    by simp[relationTheory.nf_def, dumpTrans_cases] >>
  dxrule_then (dxrule_then dxrule) RTC_dumpTrans_det >>
  simp[dumpEQ_def]
QED

Theorem dumpTrans_succeeds_noerrors:
  ∀n d1 d2 d N.
    d1 ≈ d2 ∧ NRC dumpTrans n d1 d ∧ Unload d = SOME N ⇒
    (∀t err. NRC dumpTrans t d2 err ⇒ ¬errorState err)
Proof
  simp[errorState_def] >> Induct_on ‘n’ >> simp[] >> rw[]
  >- (‘nf dumpTrans d1’
        by gvs[Unload_EQ_SOME,relationTheory.nf_def, dumpTrans_cases] >>
      ‘nf dumpTrans d2’ by metis_tac[dumpEQ_preserves_nf] >>
      Cases_on ‘t’ >> gvs[]
      >- (gvs[Unload_EQ_SOME, dumpEQ_def] >> rename [‘Unload [sec] = NONE’] >>
          PairCases_on ‘sec’ >> gvs[Unload_def]) >>
      gvs[arithmeticTheory.NRC, relationTheory.nf_def]) >>
  gvs[arithmeticTheory.NRC] >>
  rename [‘dumpTrans d1 dA’, ‘d1 ≈ d2’]>>
  ‘¬nf dumpTrans d1’ by simp[SF SFY_ss, relationTheory.nf_def] >>
  ‘¬nf dumpTrans d2’ by metis_tac[dumpEQ_preserves_nf] >>
  rename [‘Unload err = NONE’, ‘NRC _ m d2 err’] >>
  Cases_on ‘m’ >> gvs[arithmeticTheory.NRC]
  >- metis_tac[relationTheory.nf_def] >>
  drule_all dumpTrans_det >> metis_tac[]
QED

Theorem dumpTrans_succeeds_nolater_transitions:
  ∀n d1 d2 d N.
    d1 ≈ d2 ∧ NRC dumpTrans n d1 d ∧ Unload d = SOME N ⇒
    ∀m e. n < m ⇒ ¬NRC dumpTrans m d2 e
Proof
  Induct_on ‘n’ >> simp[] >> rw[]
  >- (‘nf dumpTrans d1’ by gvs[Unload_EQ_SOME, relationTheory.nf_def,
                               dumpTrans_cases] >>
      ‘nf dumpTrans d2’ by metis_tac[dumpEQ_preserves_nf] >>
      Cases_on ‘m’ >>
      gvs[arithmeticTheory.NRC, relationTheory.nf_def]) >>
  gvs[arithmeticTheory.NRC] >>
  Cases_on ‘m’ >> gvs[arithmeticTheory.NRC] >>
  metis_tac[dumpTrans_det]
QED

(* stated on p131: "For any program M, Eval_V(M) =_α eval_V(M)"
   (programs are closed terms, first paragraph of §3:
     "Its [ISWIM's] set of programs is just the set of closed terms")
*)
Theorem theorem3_1:
  closed M ⇒ (Eval M N ⇔ eval M N)
Proof
  strip_tac >>
  ‘wf_Closure ⟨ M ∶ FEMPTY ⟩’ by simp[] >>
  ‘Real ⟨ M ∶ FEMPTY ⟩ = M’ by simp[Real_thm] >>
  ‘(∀N. eval M N ⇒ Eval M N) ∧ ((∀N. ¬eval M N) ⇒ (∀N. ¬Eval M N))’
    suffices_by (strip_tac >> reverse iff_tac >> simp[] >>
                 Cases_on ‘∃N. eval M N’
                 >- (gvs[] >> first_x_assum drule >> metis_tac[Eval_det]) >>
                 metis_tac[]) >>
  conj_tac
  >- (simp[eval_timed_eval] >> rpt strip_tac >> rename [‘timed_eval t’] >>
      ‘timed_eval t (Real ⟨ M ∶ FEMPTY ⟩) N’ by simp[] >>
      dxrule_at (Pat ‘timed_eval _ _ _’) lemma3_2 >>
      simp[isVClosure_thm] >>
      disch_then $ qspecl_then [‘[]’, ‘[]’, ‘[]’] mp_tac >> simp[] >>
      strip_tac >> gvs[Eval_def, Load_def] >>
      irule_at Any arithmeticTheory.NRC_RTC >>
      first_assum $ irule_at Any >> simp[Unload_def]) >>
  CCONTR_TAC >> gvs[eval_timed_eval] >>
  qpat_x_assum ‘Eval M N’ mp_tac >>
  simp[Eval_def] >> rpt strip_tac >> gvs[Load_def] >>
  drule_then strip_assume_tac arithmeticTheory.RTC_NRC >>
  drule_then strip_assume_tac dumpTrans_nf >>
  ‘wf_Closure ⟨ M ∶ FEMPTY ⟩’ by simp[] >>
  drule_at_then (Pat ‘wf_Closure _’) assume_tac lemma3_3 >>
  ‘isDump [([],FEMPTY,[])]’ by simp[isDump_def] >>
  first_x_assum (dxrule_at Any) >> simp[isVClosure_thm] >>
  rename [‘NRC dumpTrans n _ _’] >>
  qexists ‘n + 1’ >> simp[] >> gvs[GSYM Load_def] >>
  metis_tac[dumpTrans_succeeds_noerrors, dumpEQ_Load,
            dumpTrans_succeeds_nolater_transitions, DECIDE “n < n + 1”]
QED
