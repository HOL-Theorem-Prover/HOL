(* A verified RUP checker for LRAT certificates, run with cv_compute.
   Literals are non-zero ints (literal 0 is never satisfied); a CNF is a list
   of clauses, clause i+1 being its i-th element.  An LRAT step (n, C, hs)
   with n <> 0 adds clause C as clause n, derived by unit propagation over the
   clauses hs; n = 0 deletes the clauses hs.  The certificate is checked
   straight from its cv encoding: dec_steps decodes any cv, and cv_dec_steps
   computes from_steps o dec_steps at the cv level. *)
Theory lratCheck
Ancestors
  pair list integer sptree cv_type cv_std
Libs
  cv_transLib

Definition sat_lit_def:
  sat_lit (a:num -> bool) (l:int) =
    if 0 < l then a (Num l) else if l < 0 then ¬a (Num (-l)) else F
End

Definition sat_clause_def:
  sat_clause a (c:int list) = EXISTS (sat_lit a) c
End

Theorem sat_lit_neg:
  sat_lit a l ⇒ ¬sat_lit a (-l)
Proof
  rw[sat_lit_def] >> ‘¬(0 < l ∧ l < 0)’ by intLib.ARITH_TAC >> gvs[]
QED

(* a set of literals is an sptree keyed by lit_key *)
Definition lit_key_def:
  lit_key (l:int) = if 0 ≤ l then 2 * Num l else 2 * Num (-l) + 1
End

Theorem lit_key_11:
  lit_key x = lit_key y ⇔ x = y
Proof
  rw[lit_key_def, EQ_IMP_THM] >> intLib.ARITH_TAC
QED

Definition delete_literals_def:
  delete_literals (c:int list) (d:unit num_map) =
    FILTER (λx. lookup (lit_key x) d = NONE) c
End

(* unit propagation: d holds the literals assumed false *)
Definition is_rup_def:
  (is_rup fml [] (d:unit num_map) = F) ∧
  (is_rup fml (i::is) d =
     case lookup i fml of
       NONE => F
     | SOME c =>
       case delete_literals c d of
         [] => T
       | [l] => is_rup fml is (insert (lit_key (-l)) () d)
       | _ => F)
End

Definition assume_lits_def:
  (assume_lits [] (d:unit num_map) = d) ∧
  (assume_lits (l::ls) d = assume_lits ls (insert (lit_key l) () d))
End

Definition check_steps_def:
  (check_steps [] fml = F) ∧
  (check_steps ((n:num, c:int list, hs:num list) :: rest) fml =
     if n = 0 then check_steps rest (FOLDL (λf i. delete i f) fml hs)
     else is_rup fml hs (assume_lits c LN) ∧
          (NULL c ∨ check_steps rest (insert n c fml)))
End

Definition build_fml_def:
  (build_fml (n:num) [] = LN) ∧
  (build_fml n (c::cs) = insert n (c:int list) (build_fml (n + 1) cs))
End

Definition check_unsat_def:
  check_unsat steps cnf = check_steps steps (build_fml 1 cnf)
End

Definition fml_sat_def:
  fml_sat a fml = ∀i c. lookup i fml = SOME c ⇒ sat_clause a c
End

Theorem is_rup_sound:
  ∀is fml d a. is_rup fml is d ∧ fml_sat a fml ⇒
               ∃l. lookup (lit_key l) d ≠ NONE ∧ sat_lit a l
Proof
  Induct >> simp[is_rup_def] >> rpt gen_tac >>
  rename1 ‘lookup i fml’ >> Cases_on ‘lookup i fml’ >> simp[] >>
  rename1 ‘lookup i fml = SOME c’ >>
  ‘fml_sat a fml ⇒ sat_clause a c’ by metis_tac[fml_sat_def] >>
  Cases_on ‘delete_literals c d’ >> simp[]
  >- (rpt strip_tac >> gvs[sat_clause_def, EXISTS_MEM, delete_literals_def] >>
      Cases_on ‘lookup (lit_key e) d = NONE’ >- gvs[FILTER_EQ_NIL, EVERY_MEM] >>
      metis_tac[]) >>
  rename1 ‘l::t’ >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘fml’, ‘insert (lit_key (-l)) () d’,
    ‘a’] mp_tac) >>
  simp[lookup_insert] >> strip_tac >>
  Cases_on ‘lit_key l' = lit_key (-l)’ >> gvs[lit_key_11] >- (
    gvs[sat_clause_def, EXISTS_MEM, delete_literals_def] >>
    Cases_on ‘lookup (lit_key e) d = NONE’ >- (
      ‘MEM e (FILTER (λx. lookup (lit_key x) d = NONE) c)’ by
        simp[MEM_FILTER] >>
      gvs[] >> metis_tac[sat_lit_neg, integerTheory.INT_NEGNEG]) >>
    metis_tac[]) >>
  metis_tac[]
QED

Theorem lookup_assume_lits:
  ∀c d l. lookup (lit_key l) (assume_lits c d) ≠ NONE ⇒
          MEM l c ∨ lookup (lit_key l) d ≠ NONE
Proof
  Induct >> rw[assume_lits_def] >> first_x_assum drule >>
  rw[lookup_insert] >> gvs[lit_key_11] >> metis_tac[]
QED

Theorem is_rup_sat:
  is_rup fml hs (assume_lits c LN) ∧ fml_sat a fml ⇒ sat_clause a c
Proof
  rw[sat_clause_def] >> drule_all is_rup_sound >> rw[] >>
  drule lookup_assume_lits >> rw[lookup_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem fml_sat_delete:
  ∀hs fml. fml_sat a fml ⇒ fml_sat a (FOLDL (λf i. delete i f) fml hs)
Proof
  Induct >> rw[] >> first_x_assum irule >>
  gvs[fml_sat_def, lookup_delete] >> metis_tac[]
QED

Theorem check_steps_sound:
  ∀steps fml a. check_steps steps fml ⇒ ¬fml_sat a fml
Proof
  Induct >> simp[check_steps_def, FORALL_PROD] >> rpt gen_tac >>
  rename1 ‘insert n c fml’ >> Cases_on ‘n = 0’ >> simp[]
  >- metis_tac[fml_sat_delete] >>
  rpt strip_tac >> ‘sat_clause a c’ by metis_tac[is_rup_sat]
  >- gvs[NULL_EQ, sat_clause_def] >>
  first_x_assum drule >> disch_then (qspec_then ‘a’ mp_tac) >>
  gvs[fml_sat_def, lookup_insert] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem lookup_build_fml:
  ∀cs n i c. lookup i (build_fml n cs) = SOME c ⇒ MEM c cs
Proof
  Induct >> rw[build_fml_def, lookup_insert] >> metis_tac[]
QED

Theorem check_unsat_sound:
  check_unsat steps cnf ⇒ ¬∃a. EVERY (sat_clause a) cnf
Proof
  rw[check_unsat_def, EVERY_MEM] >> drule check_steps_sound >>
  simp[fml_sat_def, EXISTS_MEM] >> metis_tac[lookup_build_fml]
QED

val _ = cv_auto_trans check_unsat_def;
val cv_check_unsat_thm = theorem "cv_check_unsat_thm";

(* Decoding a certificate from any cv, with no ARB: a missing field reads
   as Num 0. *)
Definition dec_step_def:
  dec_step (c:cv) =
    (cv$c2n (cv_fst c), to_list to_int (cv_fst (cv_snd c)),
     to_list cv$c2n (cv_snd (cv_snd c)))
End

Definition dec_steps_def:
  dec_steps (c:cv) = to_list dec_step c
End

(* from_steps o dec_steps, computed at the cv level *)
Definition cv_canon_int_def:
  cv_canon_int c =
    cv_if (cv_ispair c)
      (cv_if (cv_lt (cv$Num 0) (cv_add (cv_fst c) (cv$Num 0)))
         (cv$Pair (cv_add (cv_fst c) (cv$Num 0)) (cv$Num 0)) (cv$Num 0))
      c
End

Definition cv_canon_ints_def:
  cv_canon_ints c =
    cv_if (cv_ispair c)
      (cv$Pair (cv_canon_int (cv_fst c)) (cv_canon_ints (cv_snd c))) (cv$Num 0)
Termination
  WF_REL_TAC ‘measure cv_size’ >> Cases >> simp[]
End

Definition cv_canon_nums_def:
  cv_canon_nums c =
    cv_if (cv_ispair c)
      (cv$Pair (cv_add (cv_fst c) (cv$Num 0)) (cv_canon_nums (cv_snd c)))
        (cv$Num 0)
Termination
  WF_REL_TAC ‘measure cv_size’ >> Cases >> simp[]
End

Definition cv_canon_steps_def:
  cv_canon_steps c =
    cv_if (cv_ispair c)
      (cv$Pair (cv$Pair (cv_add (cv_fst (cv_fst c)) (cv$Num 0))
                  (cv$Pair (cv_canon_ints (cv_fst (cv_snd (cv_fst c))))
                        (cv_canon_nums (cv_snd (cv_snd (cv_fst c))))))
            (cv_canon_steps (cv_snd c)))
      (cv$Num 0)
Termination
  WF_REL_TAC ‘measure cv_size’ >> Cases >> simp[]
End

Theorem cv_add_0[local]:
  cv_add x (cv$Num 0) = cv$Num (cv$c2n x)
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem cv_canon_int_thm:
  ∀c. from_int (to_int c) = cv_canon_int c
Proof
  Cases >> simp[cv_canon_int_def, from_int_def, to_int_def, cv_add_0] >>
  rename1 ‘cv$c2n x’ >> Cases_on ‘cv$c2n x = 0’ >> simp[]
QED

Theorem cv_canon_ints_thm:
  ∀c. from_list from_int (to_list to_int c) = cv_canon_ints c
Proof
  recInduct cv_canon_ints_ind >> rw[] >> Cases_on ‘c’ >>
  simp[Once cv_canon_ints_def, to_list_def, from_list_def, cv_canon_int_thm] >>
  gvs[]
QED

Theorem cv_canon_nums_thm:
  ∀c. from_list cv$Num (to_list cv$c2n c) = cv_canon_nums c
Proof
  recInduct cv_canon_nums_ind >> rw[] >> Cases_on ‘c’ >>
  simp[Once cv_canon_nums_def, to_list_def, from_list_def, cv_add_0] >>
  gvs[]
QED

val from_steps = cv_typeLib.from_term_for “:(num # int list # num list) list”;

Theorem cv_canon_steps_thm:
  ∀c. ^from_steps (dec_steps c) = cv_canon_steps c
Proof
  recInduct cv_canon_steps_ind >> rw[] >> Cases_on ‘c’ >>
  simp[Once cv_canon_steps_def, dec_steps_def, dec_step_def, to_list_def,
       from_list_def, from_pair_def, cv_add_0, cv_canon_ints_thm,
       cv_canon_nums_thm] >>
  gvs[dec_steps_def]
QED

(* The certificate theorem the tactic instantiates: the certificate c is any
   cv value, checked after canonicalisation, so it never needs a HOL-level
   decoding of its own. *)
Theorem check_unsat_cv:
  from_list (from_list from_int) cnf = cnfc ∧
  cv_check_unsat (cv_canon_steps c) cnfc = cv$Num 1 ⇒
  ¬∃a. EVERY (sat_clause a) cnf
Proof
  strip_tac >> irule check_unsat_sound >> qexists_tac ‘dec_steps c’ >>
  ‘b2c (check_unsat (dec_steps c) cnf) = cv$Num 1’
    by (rewrite_tac[cv_check_unsat_thm, cv_canon_steps_thm] >> gvs[]) >>
  Cases_on ‘check_unsat (dec_steps c) cnf’ >> gvs[cvTheory.b2c_def]
QED
