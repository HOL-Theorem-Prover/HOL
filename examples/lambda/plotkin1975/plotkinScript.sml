Theory plotkin

(* A translation of “Call-by-name, Call-by-value and the λ-Calculus” by
   Gordon Plotkin, Theoretical Computer Science 1 (1975), pp125–159.
   North Holland
*)

Ancestors cterm fmaptree nomset finite_map

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
  metis_tac[flookup_thm, pred_setTheory.SUBSET_DEF]
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
  dumpTrans ((mkClos (CONST a) E' :: mkClos (CONST b) E' :: S, E, Ap::C)::D)
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
      simp[pred_setTheory.EXTENSION, EQ_IMP_THM])
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
