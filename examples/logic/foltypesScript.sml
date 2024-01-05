open HolKernel boolLib Parse bossLib

open binderLib nomdatatype nomsetTheory boolSimps
     pred_setTheory listTheory quotientLib

val _ = new_theory "foltypes"

val _ = Datatype‘foterm = V string | TFn string (foterm list)’;

Theorem foterm_induct:
  ∀P. (∀s. P (V s)) ∧ (∀f ts. (∀t. MEM t ts ⇒ P t) ⇒ P(TFn f ts)) ⇒
      ∀t. P t
Proof
  rpt strip_tac >>
  qspecl_then [‘P’, ‘λts. ∀t. MEM t ts ⇒ P t’]
    (assume_tac o SIMP_RULE bool_ss [])
    (TypeBase.induction_of “:foterm”) >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

val _ = TypeBase.update_induction foterm_induct

val foterm_size_def = DB.fetch "-" "foterm_size_def"
val _ = export_rewrites ["foterm_size_def"]


Theorem foterm_size_lemma[simp]:
  ∀x l a. MEM a l ⇒ foterm_size a < foterm1_size l + (x + 1)
Proof
  rpt gen_tac >> Induct_on ‘l’ >> simp[] >> rw[] >> simp[] >>
  res_tac >> simp[]
QED

Definition raw_tpm_def:
  (raw_tpm π (V s) = V (lswapstr π s)) ∧
  (raw_tpm π (TFn f ts) = TFn f (MAP (raw_tpm π) ts))
Termination
  WF_REL_TAC ‘measure (foterm_size o SND)’ >> simp[]
End

Theorem raw_tpm_def[allow_rebind] =
        SIMP_RULE (srw_ss() ++ ETA_ss) [] raw_tpm_def

Overload tpm = “pmact (mk_pmact raw_tpm)”
Overload tlpm = “listpm (mk_pmact raw_tpm)”
val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] listTheory.MAP_CONG

val tpm_raw = Q.prove(
  ‘(raw_tpm = tpm)’,
  simp[GSYM pmact_bijections] >> simp[is_pmact_def] >> rpt conj_tac
  >- (Induct >> simp[raw_tpm_def, Cong MAP_CONG'])
  >- (map_every qx_gen_tac [‘p1’, ‘p2’, ‘x’] >> Induct_on ‘x’ >>
      simp[raw_tpm_def, MAP_MAP_o, Cong MAP_CONG', pmact_decompose])
  >- (rpt strip_tac >> simp[FUN_EQ_THM] >> Induct >>
      simp[raw_tpm_def, Cong MAP_CONG', GSYM permeq_thm]));

Theorem tpm_thm[simp] =
  raw_tpm_def |> ONCE_REWRITE_RULE [tpm_raw]
              |> SIMP_RULE bool_ss [GSYM listpm_MAP]

Definition LIST_UNION_def[simp]:
  (LIST_UNION [] = ∅) ∧
  (LIST_UNION (s::rest) = s ∪ LIST_UNION rest)
End

Theorem IN_LIST_UNION[simp]:
  x ∈ LIST_UNION l ⇔ ∃s. MEM s l ∧ x ∈ s
Proof
  Induct_on ‘l’ >> simp[] >> metis_tac[]
QED

Theorem FINITE_LIST_UNION[simp]:
  FINITE (LIST_UNION l) ⇔ ∀s. MEM s l ⇒ FINITE s
Proof
  Induct_on ‘l’ >> simp[] >> metis_tac[]
QED

Theorem pmact_LIST_UNION:
  setpm pm p (LIST_UNION l) = LIST_UNION (listpm (set_pmact pm) p l)
Proof
  Induct_on ‘l’ >> simp[pmact_UNION]
QED

Definition tfv_def[simp]:
  (tfv (V s) = {s}) ∧
  (tfv (TFn f ts) = LIST_UNION (MAP tfv ts))
Termination
  WF_REL_TAC ‘measure foterm_size’ >> simp[]
End

Theorem FINITE_tfv[simp]:
  ∀t. FINITE (tfv t)
Proof
  Induct >> simp[MEM_MAP, PULL_EXISTS, DISJ_IMP_THM]
QED

val OR_LEFT_FORALL_THM = Q.prove(
  ‘(∀x. P x) ∨ Q ⇔ ∀x. P x ∨ Q’,
  metis_tac[])

Theorem tfv_support:
  support (mk_pmact raw_tpm) t (tfv t)
Proof
  simp[support_def] >> Induct_on ‘t’ >>
  simp[MEM_MAP, OR_LEFT_FORALL_THM] >> rw[] >> REWRITE_TAC [listpm_MAP] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[MEM_EL]
QED

Theorem tfv_apart:
  ∀t x y. x ∈ tfv t ∧ y ∉ tfv t ⇒ tpm [(x,y)] t ≠ t
Proof
  Induct >>
  simp[MEM_MAP, PULL_EXISTS, OR_LEFT_FORALL_THM, listpm_MAP] >> rw[] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[MEM_EL]
QED

Theorem supp_tpm[simp]:
  supp (mk_pmact raw_tpm) t = tfv t
Proof
  irule supp_unique >> simp[tfv_support] >>
  CCONTR_TAC >> fs[support_def, SUBSET_DEF] >>
  rename [‘FINITE s’] >>
  ‘∃y. y ∉ tfv t ∧ y ∉ s’
     by (Q.SPEC_THEN `tfv t UNION s` MP_TAC basic_swapTheory.NEW_def >>
         simp[] THEN METIS_TAC []) >>
  METIS_TAC [tfv_apart]
QED

Theorem ssetpm_LIST_UNION[simp]:
  ssetpm π (LIST_UNION l) = LIST_UNION (MAP (ssetpm π) l)
Proof
  Induct_on ‘l’ >> simp[pmact_UNION]
QED

Theorem tfv_tpm:
  ∀t. ssetpm π (tfv t) = tfv (tpm π t)
Proof
  Induct >>
  simp[pmact_INSERT, MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG',
       listpm_MAP]
QED

val _ = Datatype‘
  raw_fof = imp0 raw_fof raw_fof | raw_falsity | rawP string (foterm list)
          | rawALL string raw_fof
’;

Definition rawfpm_def[simp]:
  (rawfpm pi (imp0 rf1 rf2) = imp0 (rawfpm pi rf1) (rawfpm pi rf2)) ∧
  (rawfpm pi raw_falsity = raw_falsity) ∧
  (rawfpm pi (rawP p ts) = rawP p (tlpm pi ts)) ∧
  (rawfpm pi (rawALL bv f) = rawALL (lswapstr pi bv) (rawfpm pi f))
End

Theorem permeq_listpm:
  π₁ == π₂ ⇒ (listpm a π₁ l = listpm a π₂ l)
Proof
  strip_tac >>
  ‘is_pmact (listpm a)’ suffices_by metis_tac[is_pmact_def] >>
  simp[]
QED


val rawfpm_pmact = Q.prove(
  ‘rawfpm = pmact (mk_pmact rawfpm)’,
  simp[GSYM pmact_bijections] >>
  simp[is_pmact_def] >> rpt conj_tac
  >- (Induct >> simp[])
  >- (Induct_on ‘x’ >> simp[pmact_decompose])
  >- (rpt strip_tac >> simp[FUN_EQ_THM] >> Induct >> simp[] >>
      simp[GSYM permeq_thm] >> metis_tac[permeq_listpm]));

Definition raw_atoms_def:
  (raw_atoms raw_falsity = {}) ∧
  (raw_atoms (imp0 rf1 rf2) = raw_atoms rf1 ∪ raw_atoms rf2) ∧
  (raw_atoms (rawP p ts) = LIST_UNION (MAP tfv ts)) ∧
  (raw_atoms (rawALL bv f) = bv INSERT raw_atoms f)
End

Theorem raw_atoms_fresh:
  x ∉ raw_atoms rf ∧ y ∉ raw_atoms rf ⇒ (rawfpm [(x,y)] rf = rf)
Proof
  Induct_on ‘rf’ >> simp[raw_atoms_def, MEM_MAP, OR_LEFT_FORALL_THM] >>
  simp[LIST_EQ_REWRITE, listpm_MAP, EL_MAP] >>
  metis_tac[MEM_EL, support_def, tfv_support]
QED

Theorem raw_atoms_support:
  support (mk_pmact rawfpm) rf (raw_atoms rf)
Proof
  simp[support_def, GSYM rawfpm_pmact] >> Induct_on ‘rf’ >>
  simp[raw_atoms_def, MEM_MAP, OR_LEFT_FORALL_THM] >>
  REWRITE_TAC [listpm_MAP] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >>
  metis_tac[MEM_EL, support_def, tfv_support]
QED

Theorem FINITE_raw_atoms:
  FINITE (raw_atoms rf)
Proof
  Induct_on ‘rf’ >> dsimp[raw_atoms_def, MEM_MAP]
QED

val _ = augment_srw_ss [rewrites [FINITE_raw_atoms]]


Theorem raw_atoms_apart:
  ∀rf x y. x ∈ raw_atoms rf ∧ y ∉ raw_atoms rf ⇒ rawfpm [(x,y)] rf ≠ rf
Proof
  Induct >>
  simp[raw_atoms_def, MEM_MAP, PULL_EXISTS, OR_LEFT_FORALL_THM, listpm_MAP]
  >- metis_tac[]
  >- (rw[] >> simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[MEM_EL, tfv_apart])
  >- (rw[] >> simp[] >> fs[basic_swapTheory.swapstr_thm])
QED

Theorem raw_atoms_rawfpm:
  ssetpm π (raw_atoms rf) = raw_atoms (rawfpm π rf)
Proof
  Induct_on ‘rf’ >>
  simp[raw_atoms_def, rawfpm_def, pmact_UNION, pmact_INSERT] >>
  Induct >> simp[pmact_UNION, tfv_tpm]
QED

val (faeq_rules, faeq_ind, faeq_cases) = Hol_reln‘
  faeq raw_falsity raw_falsity ∧
  (∀p ts. faeq (rawP p ts) (rawP p ts)) ∧
  (∀rf11 rf12 rf21 rf22.
       faeq rf11 rf21 ∧ faeq rf12 rf22 ⇒
       faeq (imp0 rf11 rf12) (imp0 rf21 rf22)) ∧
  (∀bx by rf1 rf2 z.
     z ≠ bx ∧ z ≠ by ∧ z ∉ raw_atoms rf1 ∧ z ∉ raw_atoms rf2 ∧
     faeq (rawfpm [(bx,z)] rf1) (rawfpm [(by,z)] rf2) ⇒
     faeq (rawALL bx rf1) (rawALL by rf2))
’;

Theorem faeq_perm[simp]:
  ∀rf1 rf2 π. faeq (rawfpm π rf1) (rawfpm π rf2) ⇔ faeq rf1 rf2
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM] >> conj_asm2_tac
  >- metis_tac[pmact_inverse, rawfpm_pmact] >>
  ‘∀rf1 rf2. faeq rf1 rf2 ⇒ ∀π. faeq (rawfpm π rf1) (rawfpm π rf2)’
    suffices_by metis_tac[] >>
  Induct_on ‘faeq’ >> simp[rawfpm_def, faeq_rules] >> rw[] >>
  irule (last (CONJUNCTS faeq_rules)) >>
  qexists_tac ‘lswapstr π z’ >> ONCE_REWRITE_TAC [rawfpm_pmact] >>
  simp[pmact_sing_to_back] >> simp[GSYM rawfpm_pmact, GSYM raw_atoms_rawfpm]
QED

Theorem faeq_refl:
  ∀rf. faeq rf rf
Proof
  Induct >> simp[faeq_rules] >> qx_gen_tac ‘bv’ >>
  NEW_TAC "z" “bv INSERT raw_atoms rf” >>
  irule (last (CONJUNCTS faeq_rules)) >> qexists_tac ‘z’ >> simp[]
QED

Theorem faeq_sym:
  ∀rf1 rf2. faeq rf1 rf2 ⇒ faeq rf2 rf1
Proof
  Induct_on ‘faeq’ >> simp[faeq_rules] >> metis_tac[faeq_rules]
QED

Theorem faeq_imp0L_invert:
  faeq (imp0 rf1 rf2) rf ⇔
    ∃rf1' rf2'. (rf = imp0 rf1' rf2') ∧ faeq rf1 rf1' ∧ faeq rf2 rf2'
Proof
  simp[SimpLHS, Once faeq_cases]
QED

Theorem faeq_rawALLL_invert:
  faeq (rawALL bv1 rf1) rf ⇔
   ∃bv2 rf2 z. (rf = rawALL bv2 rf2) ∧ z ≠ bv1 ∧ z ≠ bv2 ∧
               z ∉ raw_atoms rf1 ∧ z ∉ raw_atoms rf2 ∧
               faeq (rawfpm [(bv1,z)] rf1) (rawfpm [(bv2,z)] rf2)
Proof
  simp[SimpLHS, Once faeq_cases]
QED

Theorem rawfpm_sing_to_front:
  rawfpm p (rawfpm [(u,v)] f) =
  rawfpm [(lswapstr p u, lswapstr p v)] (rawfpm p f)
Proof
  ONCE_REWRITE_TAC [rawfpm_pmact] >> simp[GSYM pmact_sing_to_back]
QED

Theorem faeq_trans:
  ∀rf1 rf2 rf3. faeq rf1 rf2 ∧ faeq rf2 rf3 ⇒ faeq rf1 rf3
Proof
  Induct_on ‘faeq rf1 rf2’ >> simp[faeq_rules] >> rw[]
  >- fs[faeq_imp0L_invert] >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [faeq_rawALLL_invert]) >>
  rename [‘faeq (rawfpm [(bx,z1)] rf1) (rawfpm [(by,z1)] rf2)’,
          ‘faeq (rawfpm [(by,z2)] rf2) (rawfpm [(bz,z2)] rf3)’] >>
  NEW_TAC "Z"
    “{bx; by; bz; z1; z2} ∪ raw_atoms rf1 ∪ raw_atoms rf2 ∪ raw_atoms rf3” >>
  ‘∀rf3.
     faeq (rawfpm [(z1,Z)] (rawfpm [(by,z1)] rf2)) (rawfpm [(z1,Z)] rf3) ⇒
     faeq (rawfpm [(z1,Z)] (rawfpm [(bx,z1)] rf1)) (rawfpm [(z1,Z)] rf3)’
   by simp[] >>
  pop_assum (qspec_then ‘rawfpm [(z1,Z)] rf3’ (mp_tac o Q.GEN ‘rf3’)) >>
  ONCE_REWRITE_TAC [rawfpm_pmact] >>
  simp[pmact_sing_inv] >> simp[GSYM rawfpm_pmact] >>
  disch_then (mp_tac o ONCE_REWRITE_RULE [rawfpm_sing_to_front]) >>
  simp[raw_atoms_fresh] >> strip_tac >>
  ‘faeq (rawfpm [(z2,Z)] (rawfpm [(by,z2)] rf2))
        (rawfpm [(z2,Z)] (rawfpm [(bz,z2)] rf3))’
    by simp[] >>
  pop_assum (mp_tac o ONCE_REWRITE_RULE [rawfpm_sing_to_front]) >>
  simp[raw_atoms_fresh] >>
  pop_assum (fn th => strip_tac >> drule th) >> metis_tac[faeq_rules]
QED

Theorem faeq_equiv:
  ∀rf1 rf2. faeq rf1 rf2 ⇔ (faeq rf1 = faeq rf2)
Proof   simp[FUN_EQ_THM] >> metis_tac[faeq_refl, faeq_sym, faeq_trans]
QED

Definition rawfv_def[simp]:
  (rawfv raw_falsity = ∅) ∧
  (rawfv (imp0 rf1 rf2) = rawfv rf1 ∪ rawfv rf2) ∧
  (rawfv (rawP _ ts) = LIST_UNION (MAP tfv ts)) ∧
  (rawfv (rawALL bv rf) = rawfv rf DELETE bv)
End

Theorem rawfv_rawfpm:
  rawfv (rawfpm pi rf) = ssetpm pi (rawfv rf)
Proof
  Induct_on‘rf’ >>
  simp[pmact_UNION, pmact_DELETE, pmact_LIST_UNION, listpm_MAP, MAP_MAP_o,
       Cong MAP_CONG', tfv_tpm]
QED

Theorem rawfv_SUBSET_raw_atoms:
  x ∈ rawfv rf ⇒ x ∈ raw_atoms rf
Proof
  Induct_on ‘rf’ >> simp[raw_atoms_def, MEM_MAP] >> metis_tac[]
QED

Theorem FINITE_rawfv:
  FINITE (rawfv rf)
Proof
  Induct_on ‘rf’ >> simp[MEM_MAP, PULL_EXISTS]
QED

Theorem faeq_rawfv:
  ∀rf1 rf2. faeq rf1 rf2 ⇒ (rawfv rf1 = rawfv rf2)
Proof
  Induct_on ‘faeq’ >> rw[rawfv_rawfpm, EXTENSION] >>
  rename [‘a ∈ rawfv rf1’, ‘faeq (rawfpm [(bx,z)] rf1) (rawfpm [(by,z)] rf2)’]>>
  Cases_on‘a = bx’ >> fs[]
  >- (Cases_on ‘bx = by’ >> simp[] >>
      first_x_assum (qspec_then ‘bx’ mp_tac) >> simp[] >>
      metis_tac[rawfv_SUBSET_raw_atoms]) >>
  Cases_on ‘a = z’ >> fs[] >- metis_tac [rawfv_SUBSET_raw_atoms] >>
  Cases_on ‘a = by’ >> fs[]
  >- (first_x_assum (qspec_then ‘by’ mp_tac) >> simp[] >>
      metis_tac [rawfv_SUBSET_raw_atoms]) >>
  first_x_assum (qspec_then ‘a’ mp_tac) >> simp[]
QED

Theorem faeq_imp0:
  faeq (imp0 rf1 rf2) (imp0 rfa rfb) ⇔ faeq rf1 rfa ∧ faeq rf2 rfb
Proof
  simp[Once faeq_cases, SimpLHS]
QED

Theorem faeq_rawP:
  faeq (rawP n1 ts1) (rawP n2 ts2) ⇔ (n1 = n2) ∧ (ts1 = ts2)
Proof
  simp[Once faeq_cases, EQ_SYM_EQ]
QED

Theorem faeq_ALL_respects:
  faeq b1 b2 ⇒ faeq (rawALL bv b1) (rawALL bv b2)
Proof
  rw[faeq_rawALLL_invert] >>
  Q_TAC (NEW_TAC "z") ‘bv INSERT (raw_atoms b1 ∪ raw_atoms b2)’ >>
  metis_tac[]
QED

Theorem rawfpm_xx_id[simp]:
  rawfpm [(x,x)] f = f
Proof
  Induct_on ‘f’ >> simp[]
QED
(*
Theorem raw_fresh:
  ∀x y. x ∉ rawfv rf ∧ y ∉ rawfv rf ⇒ faeq (rawfpm [(x,y)] rf) rf
Proof
  Induct_on ‘rf’ >> simp[faeq_rules, MEM_MAP, OR_LEFT_FORALL_THM] >> rw[] >>
  simp[] >> fs[]
  >- (‘tlpm [(x,y)] l = l’ suffices_by metis_tac[faeq_rules] >>
      simp[listpm_MAP, LIST_EQ_REWRITE, EL_MAP] >>
      metis_tac[supp_fresh, MEM_EL, supp_tpm])
  >- (Cases_on ‘s ∈ rawfv rf’
      >- (‘s ≠ x ∧ s ≠ y’ by (rpt strip_tac >> fs[]) >> simp[] >>
          irule (last (CONJUNCTS faeq_rules)) >> simp[] >>
          Q_TAC (NEW_TAC "z") ‘{x;y;s} ∪ raw_atoms rf’ >> qexists_tac ‘z’ >>
          simp[GSYM raw_atoms_rawfpm]) >>
      irule (last (CONJUNCTS faeq_rules)) >> simp[] >>
      Q_TAC (NEW_TAC "z") ‘{x;y;s;swapstr x y s} ∪ raw_atoms rf’ >>
      qexists_tac ‘z’ >> simp[GSYM raw_atoms_rawfpm] >>
      ‘(swapstr x y s, z) = (swapstr x y s, swapstr x y z)’ by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      REWRITE_TAC [rawfpm_sing_to_front
                     |> Q.INST [‘p’ |-> ‘[(x,y)]’]
                     |> SIMP_RULE (srw_ss()) []
                     |> SYM
                     |> GEN_ALL]




      >- (Cases_on ‘y = s’ >> fs[] >> simp[faeq_refl] >>
          simp[Once rawfpm_sing_to_front] >> csimp[] >>
          Q_TAC (NEW_TAC "z") ‘{s;y} ∪ raw_atoms rf’ >> qexists_tac ‘z’ >>
          simp[GSYM raw_atoms_rawfpm] >> first_x_assum irule >>
          metis_tac[rawfv_SUBSET_raw_atoms]) >>
*)


val fpm_respects = faeq_perm |> SPEC_ALL |> EQ_IMP_RULE |> #2 |> GEN_ALL

(* Theorem faeq_ALL :
  faeq (rawALL bv1 rf1) (rawALL bv2 rf2) ⇔
    (bv1 = bv2) ∧ faeq rf1 rf2 ∨
    bv1 ∉ rawfv rf2 ∧ faeq rf1 (rawfpm [(bv1,bv2)] rf2)
Proof
  rw[faeq_rawALLL_invert, EQ_IMP_THM]
  >- (‘z ∉ rawfv rf1’ by metis_tac[rawfv_SUBSET_raw_atoms] >>
      Cases_on ‘bv1 = bv2’ >> fs[] >>
      drule faeq_rawfv >> simp[rawfv_rawfpm] >>
      disch_then
        (fn th => Q_TAC (fn t => mp_tac (AP_TERM t th)) ‘$IN bv1’) >>
      simp[] >> strip_tac >>
      drule_then (qspec_then ‘[(bv1,z)]’ mp_tac) fpm_respects >>
      ONCE_REWRITE_TAC [rawfpm_pmact] >>
      simp_tac (srw_ss())[Excl "faeq_perm", pmact_sing_inv] >>
      simp[GSYM rawfpm_pmact] >>
*)

fun mkdef (n,tm) = {def_name = n ^ "_def", fixity = NONE, fname = n, func = tm};

val lifted_results = define_equivalence_type
  {defs = map mkdef [("fpm", “rawfpm”), ("FALL", “rawALL”), ("FIMP", “imp0”),
                     ("FFALSE", “raw_falsity”), ("FPRED", “rawP”),
                     ("FFV", “rawfv”)],
   equiv = faeq_equiv,
   name = "foform",
   old_thms = [faeq_rawP, faeq_imp0, rawfpm_def, rawfv_def, rawfv_rawfpm,
               FINITE_rawfv, faeq_perm],
   welldefs = [faeq_imp0 |> EQ_IMP_RULE |> #2 |> GSYM,
               fpm_respects,
               faeq_ALL_respects, faeq_rawfv]
  };






val _ = export_theory();
