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

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟨", TM, HardSpace 1, TOK "∶",
                                 BreakSpace (1,1), TM, TOK "⟩"],
                  term_name = "mkClos"}


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
Overload clFV = “supp (fmt_pmact cterm_pmact string_pmact)”
Overload eFV =
  “supp (fm_pmact string_pmact (fmt_pmact cterm_pmact string_pmact))”
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
Proof
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
  [‘⟨ CONST c ∶ E |+ (u,NCl)⟩ (* sg *)’]
  >- simp[Real_def, fmtreerec_thm] >~
  [‘⟨ M @@ N ∶ E |+ (u,NCl)⟩ (* sg *)’]
  >- (qabbrev_tac ‘rn = Real NCl’ >> simp[Real_def, fmtreerec_thm] >>
      simp[GSYM Real_def] >> dep_rewrite.DEP_REWRITE_TAC[ssub_update] >>
      simp[wf_Closure_Real_ground]) >~
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
  simp[Real_def, fmtreerec_thm] >>
  Q_TAC (NEW_TAC "z") ‘cFV M ∪ cFV M' ∪ {x;y} ∪ eFV E’ >>
  gvs[fmap_supp, GSYM RIGHT_FORALL_DISJ_THM, supp_setpm] >>
  simp[GSYM Real_def] >>
  ‘LAM y M = LAM z (ctpm [(z,y)] M)’ by simp[ctpm_ALPHA] >>
  simp[] >>
  dep_rewrite.DEP_REWRITE_TAC[ssub_thm] >> simp[wf_Closure_Real_ground] >>
  ‘LAM x M' = LAM z (ctpm [(z,x)] M')’ by simp[ctpm_ALPHA] >>
  simp[ctpm_eqr, ctpm_ssub] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  dep_rewrite.DEP_REWRITE_TAC[sub_ssub_thm] >> simp[] >> rw[] >>
  simp[wf_Closure_Real_ground, DOMSUB_FAPPLY_THM, fmpm_FDOM] >~
  [‘x ∉ cFV (subpm [(z,x)] (Real o_f E) ' k) (* g *)’]
  >- gvs[fmpm_applied, fmpm_FDOM, wf_Closure_Real_ground] >~
  [‘(Real o_f (E \\ y)) ' ([rn/y] M) = _’] >>
  simp[ctpm_subst_out, supp_fresh] >>
  simp[GSYM ssub_def] >>
  ‘ctpm [(z,y)] ([rn/y] M) = [rn/y]M’
    by (irule supp_fresh >> simp[cFV_SUB] >> rw[]) >>
  simp[] >> gvs[ssub_def] >>
  ‘ctpm [(z,x)] ((Real o_f E) ' ([rn/y]M)) = (Real o_f E) ' ([rn/y]M)’
    by (irule supp_fresh >> simp[cFV_ssub, wf_Closure_Real_ground] >>
        rw[cFV_SUB] >>
        qpat_x_assum ‘LAM x _ = LAM z _’ mp_tac >>
        simp[LAM_eq_thm, cFV_ssub, wf_Closure_Real_ground] >>
        Cases_on ‘x = y’ >> simp[]) >>
  simp[GSYM ssub_def] >>
  simp[GSYM o_f_DOMSUB, Excl "o_f_DOMSUB"] >>
  irule ssub_domsub >> rw[cFV_SUB]
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
Proof
  Cases_on ‘cl’ using fmaptree_nchotomy >>
  simp[Real_thm, isVClosure_thm, SF CONJ_ss] >>
  rename [‘ssub _ ct’] >> Cases_on ‘ct’ using cterm_CASES >>
  rw[ssub_thm] >> CCONTR_TAC >> gvs[] >> qpat_x_assum ‘ssub _ _ = _’ mp_tac >>
  rename [‘ssub _ (LAM v t)’, ‘Real (E ' _)’] >>
  Q_TAC (NEW_TAC "z") ‘{v} ∪ cFV t ∪ eFV E’ >>
  ‘LAM v t = LAM z (ctpm [(z,v)] t)’ by simp[ctpm_ALPHA] >>
  qmatch_abbrev_tac ‘Epm ' (LAM v t) = CONST c ⇒ _’ >>
  ‘z ∉ FDOM Epm’ by simp[Abbr‘Epm’] >>
  ‘∀y. y ∈ FDOM Epm ⇒ z ∉ cFV (Epm ' y)’
    by (simp[Abbr‘Epm’, FUN_FMAP_DEF] >> qx_gen_tac ‘y’ >> rw[] >>
        ‘closed (Real (E ' y))’ suffices_by simp[] >>
        irule wf_Closure_Real_ground >> metis_tac[SUBSET_DEF, IN_DELETE]) >>
  simp[ssub_thm]
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
  gvs[isVClosure_thm, is_abs_def, is_const_def] >>
  simp[Real_thm] >>
  qmatch_goalsub_abbrev_tac ‘Efm ' _ = LAM _ _’ >>
  rename [‘Efm ' (LAM u N) = LAM _ _’] >> disj2_tac >>
  Q_TAC (NEW_TAC "z") ‘eFV fm ∪ {u} ∪ cFV N’ >>
  ‘LAM u N = LAM z (ctpm [(z,u)] N)’ by simp[ctpm_ALPHA] >>
  ‘z ∉ FDOM Efm’ by simp[Abbr‘Efm’] >>
  ‘∀y. y ∈ FDOM Efm ⇒ z ∉ cFV (Efm ' y)’
    by (simp[Abbr‘Efm’, FUN_FMAP_DEF] >> qx_gen_tac ‘y’ >>
        strip_tac >> ‘y ∈ FDOM fm’ by ASM_SET_TAC[] >>
        ‘wf_Closure (fm ' y)’ by simp[] >>
        ‘cFV (Real (fm ' y)) = ∅’ suffices_by simp[] >>
        simp[wf_Closure_Real_ground]) >>
  simp[ssub_thm] >> irule_at Any EQ_REFL
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
  >- (simp[Real_thm, SF CONJ_ss, ssub_thm] >> rw[] >>
      qexists ‘1’ >> simp[Once dumpTrans_cases] >>
      simp[Real_thm, isVClosure_thm]) >~
  [‘LAM v M’] (* Case 2 *)
  >- (simp[Real_thm, SF CONJ_ss] >> rw[] >>
      Q_TAC (NEW_TAC "z") ‘cFV M ∪ {v} ∪ eFV E’ >>
      ‘LAM v M = LAM z (ctpm [(z,v)] M)’ by simp[ctpm_ALPHA] >>
      qabbrev_tac ‘Efm = FUN_FMAP (λx. Real (E ' x)) (cFV M DELETE v)’ >>
      ‘z ∉ FDOM Efm’ by simp[Abbr‘Efm’] >>
      ‘∀y. y ∈ FDOM Efm ⇒ z ∉ cFV (Efm ' y)’
        by (simp[Abbr‘Efm’, FUN_FMAP_DEF] >> qx_gen_tac ‘y’ >>
            strip_tac >> ‘y ∈ FDOM E’ by ASM_SET_TAC[] >>
            ‘wf_Closure (E ' y)’ by simp[] >>
            ‘cFV (Real (E ' y)) = ∅’ suffices_by simp[] >>
            simp[wf_Closure_Real_ground]) >>
      gvs[ssub_thm] >> qexists ‘1’>>
      simp[Once dumpTrans_cases, PULL_EXISTS] >>
      irule_at Any EQ_REFL >>
      ‘wf_Closure ⟨LAM z (ctpm [(z,v)] M) ∶ E⟩’
        by (simp[wf_Closure_thm, SUBSET_DEF] >>
            rw[basic_swapTheory.swapstr_def] >> ASM_SET_TAC[]) >>
      ‘cFV (ctpm [(z,v)] M) DELETE z = cFV M DELETE v’
        by (simp[EXTENSION] >> rw[basic_swapTheory.swapstr_def] >> simp[]) >>
      simp[Real_thm, ssub_thm] >>
      simp[isVClosure_thm]) >~
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
  simp[Real_thm, SF CONJ_ss, FUN_FMAP_ssub_cFV] >>
  rw[] >>
  ‘wf_Closure ⟨M₁ ∶ E⟩ ∧ wf_Closure ⟨M₂ ∶ E⟩’
    by simp[wf_Closure_thm] >>
  gvs[GSYM Real_thm] >>
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
      drule_at (Pat ‘Real _ = LAM _ _’) lemma1 >>
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
