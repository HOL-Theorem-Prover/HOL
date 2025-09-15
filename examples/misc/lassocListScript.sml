Theory lassocList

(* Demonstrates that the following rewrites on lists (using HOL notation):

   xs ++ [] = xs
   [] ++ xs = xs
   h::xs ++ ys = h::(xs ++ ys)
   xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
   (xs ++ h::ys) ++ zs = xs ++ h::(ys ++ zs)

   are confluent and strongly normalising
*)



Ancestors hol relation
Libs monadsyntax[qualified]

Datatype:
  term = APP term term | Nil | Cons 'a term | LAtom ('a list)
End

val _ = set_mapped_fixity {fixity = Infixl 500, term_name = "APP", tok = "+++"}

Inductive reduces:
[~appnilL:] reduces (Nil +++ xs) xs
[~appnilR:] reduces (xs +++ Nil) xs
[~appcons:] reduces (Cons h t +++ xs) (Cons h (t +++ xs))
[~app_nested:]
  reduces (xs +++ Cons h t +++ ys) (xs +++ Cons h (t +++ ys))
[~app_assoc:] reduces (xs +++ (ys +++ zs)) (xs +++ ys +++ zs)
[~cong_appl:] reduces xs ys ⇒ reduces (xs +++ zs) (ys +++ zs)
[~cong_appr:] reduces xs ys ⇒ reduces (zs +++ xs) (zs +++ ys)
[~cong_cons:] reduces xs ys ⇒ reduces (Cons h xs) (Cons h ys)
End

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition lmodel_def[simp]:
  lmodel (t1 +++ t2) = lmodel t1 ++ lmodel t2 ∧
  lmodel (Cons h t) = h :: lmodel t ∧
  lmodel Nil = [] ∧
  lmodel (LAtom as) = as
End

Theorem rules_sound:
  ∀t1 t2. reduces t1 t2 ⇒ lmodel t1 = lmodel t2
Proof
  Induct_on ‘reduces’ >> simp[]
QED

Definition app_count_def[simp]:
  app_count (APP t1 t2) = 1 + app_count t1 + app_count t2 ∧
  app_count (Cons h t) = 0 ∧
  app_count _ = 0
End

(* number of +++-applications directly to the right of a +++ *)
Definition rAPP_count_def[simp]:
  rAPP_count (LAtom a) = 0 ∧
  rAPP_count (l1 +++ l2) =
  rAPP_count l1 + rAPP_count l2 + app_count l2 ∧
  rAPP_count (Cons h t) = rAPP_count t ∧
  rAPP_count Nil = 0
End

Theorem app_count_decreases:
  ∀t1 t2. reduces t1 t2 ⇒ app_count t2 ≤ app_count t1
Proof
  Induct_on ‘reduces’ >> simp[]
QED

Theorem rAPP_decreases:
  ∀t1 t2. reduces t1 t2 ⇒ rAPP_count t2 ≤ rAPP_count t1
Proof
  Induct_on ‘reduces’ >> simp[] >> rpt strip_tac >>
  drule app_count_decreases >> simp[]
QED

Definition NILcount_def[simp]:
  NILCount (LAtom a) = 0 ∧
  NILCount (Cons h t) = NILCount t ∧
  NILCount (APP l1 l2) = NILCount l1 + NILCount l2 ∧
  NILCount Nil = 1
End

Theorem NILcount_decreases:
  ∀t1 t2. reduces t1 t2 ⇒ NILCount t2 ≤ NILCount t1
Proof
  Induct_on ‘reduces’ >> simp[]
QED

(* vector of heights of Cons applications within the term *)
Definition cheights_def[simp]:
  cheights (Cons h t) = 0 :: cheights t ∧
  cheights (APP l1 l2) = (MAP SUC $ cheights l1) ++ (MAP SUC $ cheights l2) ∧
  cheights _ = []
End

Theorem LENGTH_cheights_preserved:
  ∀t1 t2. reduces t1 t2 ⇒ ∀b. LENGTH (cheights t2) = LENGTH (cheights t1)
Proof
  Induct_on ‘reduces’ >> simp[]
QED

Theorem SHORTLEX_prefix:
  ∀p1 p2. SHORTLEX R p1 p2 ⇒ SHORTLEX R (p1 ++ sfx) (p2 ++ sfx)
Proof
  Induct >> simp[]
  >- (Cases >> simp[] >> Cases_on ‘sfx’ >> simp[]) >>
  qx_gen_tac ‘h’ >> Cases >> simp[DECIDE “x + y = y + z ⇔ x = z”] >>
  rw[] >> simp[]
QED

Theorem SHORTLEX_suffix:
  ∀s1 s2. SHORTLEX R s1 s2 ⇒ SHORTLEX R (p ++ s1) (p ++ s2)
Proof
  Induct_on ‘p’ >> simp[] >>
  metis_tac[listTheory.SHORTLEX_LENGTH_LE, arithmeticTheory.LE_LT]
QED

Theorem SHORTLEX_MAP_SUC[simp]:
  ∀l1 l2. SHORTLEX $< (MAP SUC l1) (MAP SUC l2) ⇔ SHORTLEX $< l1 l2
Proof
  Induct >> simp[] >- (Cases >> simp[]) >>
  qx_gen_tac ‘h’ >> Cases >> simp[]
QED

Theorem WF_reduces:
  ∀t1 t2. reduces t1 t2 ⇒
          inv_image
          ($< LEX $< LEX SHORTLEX $<)
          (λt. (NILCount t,rAPP_count t,cheights t))
          t2 t1
Proof
  Induct_on ‘reduces’ >> rpt conj_tac >> rpt gen_tac >~
  [‘inv_image _ _ t (Nil +++ t)’]
  >- simp[pairTheory.LEX_DEF] >~
  [‘inv_image _ _ t (t +++ Nil)’]
  >- simp[pairTheory.LEX_DEF] >~
  [‘inv_image _ _ (Cons h (xs +++ ys)) (Cons h xs +++ ys)’]
  >- simp[pairTheory.LEX_DEF] >~
  [‘inv_image _ _ (xs +++ Cons h (ys +++ zs)) (xs +++ Cons h ys +++ zs)’]
  >- (simp[pairTheory.LEX_DEF] >> Cases_on ‘cheights xs’ >> simp[]) >~
  [‘inv_image _ _ (xs +++ ys +++ zs) (xs +++ (ys +++ zs))’]
  >- simp[pairTheory.LEX_DEF] >~
  [‘inv_image _ _ (xs2 +++ ys) (xs1 +++ ys)’, ‘inv_image _ _ xs2 xs1’]
  >- (simp[pairTheory.LEX_DEF] >> rpt strip_tac >> simp[] >>
      irule SHORTLEX_prefix >> simp[]) >~
  [‘inv_image _ _ (xs +++ ys2) (xs +++ ys1)’, ‘inv_image _ _ ys2 ys1’]
  >- (simp[pairTheory.LEX_DEF] >> rpt strip_tac >>
      simp[DECIDE “x + (y + z) = a + (y + b) ⇔ x + z = a + b”,
           DECIDE “x + (y + z) < a + (y + b) ⇔ x + z < a + b”] >>
      drule_all app_count_decreases >> simp[arithmeticTheory.LE_LT] >>
      strip_tac >> simp[] >> irule SHORTLEX_suffix >> simp[]) >~
  [‘inv_image _ _ (Cons h xs) (Cons h ys)’, ‘inv_image _ _ xs ys’]
  >- (simp[pairTheory.LEX_DEF] >> rpt strip_tac >> simp[] >>
      drule listTheory.SHORTLEX_LENGTH_LE >> simp[])
QED

Theorem reduces_NIL[simp]:
  ~reduces Nil x
Proof
  simp[Once reduces_cases]
QED

Theorem RTC_reduces_NIL[simp]:
  reduces꙳ Nil x ⇔ x = Nil
Proof
  simp[Once RTC_CASES1]
QED

Theorem reduces_Cons[simp]:
  reduces (Cons h t0) t2 ⇔ ?t1. t2 = Cons h t1 /\ reduces t0 t1
Proof
  simp[Once reduces_cases, SimpLHS]
QED

Theorem RTC_reduces_Cons[simp]:
  ∀h t0 t2. reduces꙳ (Cons h t0) t2 ⇔ ∃t1. t2 = Cons h t1 ∧ reduces꙳ t0 t1
Proof
  simp[PULL_EXISTS, EQ_IMP_THM, FORALL_AND_THM] >> conj_tac >>
  Induct_on ‘RTC’ >> rw[] >> gvs[] >> metis_tac[RTC_RULES, reduces_rules]
QED

Theorem reduces_APP_cases:
  reduces (xs +++ ys) t ⇔
    xs = Nil ∧ t = ys ∨
    ys = Nil ∧ t = xs ∨
    (∃h xs0. xs = Cons h xs0 ∧ t = Cons h (xs0 +++ ys)) ∨
    (∃xs'. reduces xs xs' ∧ t = xs' +++ ys) ∨
    (∃ys'. reduces ys ys' ∧ t = xs +++ ys') ∨
    (∃ys1 ys2. ys = ys1 +++ ys2 ∧ t = xs +++ ys1 +++ ys2) ∨
    ∃xs1 h xs2. xs = xs1 +++ Cons h xs2 ∧ t = xs1 +++ Cons h (xs2 +++ ys)
Proof
  simp[Once reduces_cases, SimpLHS] >> iff_tac >> rw[]
QED

Theorem RTC_reduces_appl:
  ∀t1 t2 t3. reduces꙳ t1 t2 ⇒ reduces꙳ (t1 +++ t3) (t2 +++ t3)
Proof
  Induct_on ‘RTC’ >> rw[] >>
  irule (cj 2 RTC_RULES) >> metis_tac[reduces_rules]
QED

Theorem RTC_reduces_appr:
  ∀t1 t2 t3. reduces꙳ t1 t2 ⇒ reduces꙳ (t3 +++ t1) (t3 +++ t2)
Proof
  Induct_on ‘RTC’ >> rw[] >>
  irule (cj 2 RTC_RULES) >> metis_tac[reduces_rules]
QED

Theorem RTC_reduces_cons_I = iffLR RTC_reduces_Cons

fun step th = resolve_then Any (irule_at Any) th (cj 2 RTC_RULES)

fun step2 th1 th2 =
resolve_then Any (resolve_then Any (irule_at Any) th2) th1 (cj 2 RTC_RULES)

Theorem local_confluence:
  ∀t0 t1 t2. reduces t0 t1 ∧ reduces t0 t2 ⇒ ∃t. reduces꙳ t1 t ∧ reduces꙳ t2 t
Proof
  Induct_on ‘reduces’ >> rpt strip_tac >>
  qpat_x_assum ‘reduces _ _’ mp_tac >>
  simp[Once reduces_cases, SimpL “$==>”] >> rw[] >> gvs[PULL_EXISTS] >>~-
  ([‘?t. RTC _ x t’], irule_at Any RTC_REFL) >~
  [‘reduces (xs +++ (ys +++ zs)) ws’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      pop_assum mp_tac >> simp[Once reduces_APP_cases] >> rw[] >>
      simp[PULL_EXISTS] >>~-
      ([‘reduces꙳ (_ +++ (_ +++ _)) _’],
       step reduces_app_assoc >> metis_tac[reduces_rules,RTC_RULES]) >~
      [‘reduces (xs +++ ys) zs’]
      >- (gvs[reduces_APP_cases] >~
          [‘xs +++ (ys +++ Cons h2 (zs +++ ws))’]
          >- (step2 reduces_cong_appl reduces_app_assoc >>
              step reduces_app_nested >> step reduces_app_assoc >>
              irule_at Any RTC_REFL) >~
          [‘xs +++ Cons h2 ys +++ zs’]
          >- (step reduces_app_nested >> irule_at Any RTC_REFL) >>
          metis_tac[reduces_rules, RTC_RULES]) >~
      [‘xs +++ Cons h2 ys +++ zs +++ ws’]
      >- (step2 reduces_cong_appl reduces_app_nested >>
          step reduces_app_nested >>
          metis_tac[reduces_rules, RTC_RULES]) >>
      metis_tac[reduces_rules, RTC_RULES]) >~
  [‘reduces (xs +++ Cons h ys +++ zs) ws’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      gvs[reduces_APP_cases] >~
      [‘reduces꙳ (Cons h2 (xs +++ Cons h3 ys) +++ zs)’]
      >- (ntac 2 (step reduces_appcons) >> simp[PULL_EXISTS] >>
          step reduces_app_nested >> irule_at Any RTC_REFL) >~
      [‘reduces꙳ (xs +++ Cons h2 (ys +++ Cons h3 zs) +++ ws)’]
      >- (ntac 2 (step reduces_app_nested) >>
          ntac 2 (irule_at Any RTC_reduces_appr) >> simp[PULL_EXISTS] >>
          step reduces_app_nested >> irule_at Any RTC_REFL) >~
      [‘reduces꙳ (xs +++ Cons h2 ys +++ zs +++ ws)’]
      >- (step2 reduces_cong_appl reduces_app_nested >>
          step reduces_app_nested >>
          metis_tac[reduces_rules, RTC_RULES]) >>
      metis_tac[reduces_rules, RTC_RULES]) >~
  [‘reduces (xs +++ Nil) ws’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      gvs[reduces_APP_cases] >>
      metis_tac[RTC_RULES, reduces_rules]) >>~-
  ([‘_ +++ Nil’], metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces (Nil +++ xs) ws’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      gvs[reduces_APP_cases] >>
      metis_tac[RTC_RULES, reduces_rules]) >>~-
  ([‘Nil +++ _’], metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces꙳ (xs +++ (ys +++ zs))’,
   ‘reduces꙳ (Cons h xs +++ ys +++ zs)’]
  >- (step2 reduces_cong_appl reduces_appcons >>
      step reduces_appcons >> simp[PULL_EXISTS] >>
      metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces꙳ (xs +++ Cons h (as +++ (bs +++ cs)))’,
   ‘reduces꙳ (xs +++ Cons h as +++ bs +++ cs)’]
  >- (resolve_then Any (resolve_then Any (irule_at Any) reduces_cong_cons)
                   reduces_cong_appr
                   (cj 2 RTC_RULES) >>
      irule_at Any reduces_app_assoc >>
      resolve_then Any (resolve_then Any (irule_at Any) reduces_app_nested)
                   reduces_cong_appl
                   (cj 2 RTC_RULES) >>
      resolve_then Any (irule_at Any) reduces_app_nested
                   (cj 2 RTC_RULES) >>
      irule_at Any RTC_REFL) >~
  [‘reduces꙳ (xs +++ Cons h (ys +++ zs))’, ‘reduces (xs +++ Cons h ys) ws’]
  >- (gvs[reduces_APP_cases] >~
      [‘(Nil +++ _)’] >- metis_tac[RTC_RULES, reduces_rules] >~
      [‘Cons h1 _ +++ Cons h2 _’]
      >- (ntac 2 (resolve_then Any (irule_at Any)
                               reduces_appcons
                               (cj 2 RTC_RULES)) >>
          resolve_then Any (irule_at Any)
                       reduces_cong_cons
                       (cj 2 RTC_RULES) >>
          irule_at Any reduces_app_nested >>
          irule_at Any RTC_REFL) >~
      [‘reduces꙳ (xs1 +++ Cons h (ys +++ zs))’, ‘reduces꙳ (xs2 +++ _ +++ _)’]
      >- (step reduces_app_nested >>
          metis_tac[RTC_RULES, reduces_rules]) >~
      [‘reduces꙳ (xs +++ Cons h (ys +++ zs))’, ‘reduces ys ys'’]
      >- (step reduces_app_nested >>
          metis_tac[RTC_RULES, reduces_rules]) >>
      ntac 2 (step reduces_app_nested) >>
      step reduces_cong_appr >>
      irule_at Any reduces_cong_cons >>
      irule_at Any reduces_app_nested >>
      irule_at Any RTC_REFL) >~
  [‘reduces꙳ (Cons h xs +++ ys +++ zs)’, ‘reduces꙳ (xs +++ (ys +++ zs))’]
  >- (step reduces_cong_appl >> irule_at Any reduces_appcons >>
      step reduces_appcons >>
      metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces꙳ (xs1 +++ Cons h xs2 +++ ys +++ zs)’,
   ‘reduces꙳ (xs1 +++ Cons h (xs2 +++ (ys +++ zs)))’]
  >- (resolve_then Any (resolve_then Any (irule_at Any) reduces_app_nested)
                   reduces_cong_appl (cj 2 RTC_RULES) >>
      metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces (ys +++ zs) ws’, ‘reduces꙳ (xs +++ ws)’]
  >- (gvs[reduces_APP_cases] >~
      [‘xs0 +++ (xs1 +++ Cons h xs2) +++ ys’]
      >- (resolve_then Any (resolve_then Any (irule_at Any) reduces_app_assoc)
                       reduces_cong_appl (cj 2 RTC_RULES) >>
          step reduces_app_nested >> step reduces_app_assoc >>
          irule_at Any RTC_REFL) >>
      metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces (xs +++ Cons h ys) zs1’, ‘reduces꙳ (zs1 +++ zs2)’,
   ‘reduces꙳ (xs +++ Cons h (ys +++ zs2))’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      gvs[reduces_APP_cases] >~
      [‘reduces꙳ (Cons h1 (xs +++ Cons h2 ys) +++ zs)’]
      >- (ntac 2 (step reduces_appcons) >>
          metis_tac[RTC_RULES, reduces_rules]) >~
      [‘reduces꙳ (xs1 +++ Cons h1 (xs2 +++ Cons h ys) +++ zs)’]
      >- (ntac 2 (step reduces_app_nested) >>
          metis_tac[RTC_RULES, reduces_rules]) >>
      metis_tac[RTC_RULES, reduces_rules]) >>~-
  ([‘reduces꙳ (Cons _ _ +++ _) _’],
   step reduces_appcons >> simp[PULL_EXISTS] >>
   metis_tac[reduces_rules,RTC_RULES]) >~
  [‘reduces꙳ (xs +++ t1) _ ∧ reduces꙳ (xs +++ t2) _’]
  >- (‘∃t. reduces꙳ t1 t ∧ reduces꙳ t2 t’ by metis_tac[] >>
      metis_tac[RTC_reduces_appr]) >~
  [‘reduces꙳ (t1 +++ xs) _ ∧ reduces꙳ (t2 +++ xs) _’]
  >- (‘∃t. reduces꙳ t1 t ∧ reduces꙳ t2 t’ by metis_tac[] >>
      metis_tac[RTC_reduces_appl]) >~
  [‘reduces (as +++ bs) ys’, ‘reduces꙳ (xs +++ as +++ bs)’]
  >- (first_x_assum (qspec_then ‘ARB’ kall_tac) >>
      gvs[reduces_APP_cases] >~
      [‘reduces꙳ (xs +++ (ys +++ Cons h zs) +++ ws)’]
      >- (resolve_then Any (resolve_then Any (irule_at Any) reduces_app_assoc)
                       reduces_cong_appl (cj 2 RTC_RULES) >>
          metis_tac[RTC_RULES, reduces_rules]) >>
      metis_tac[RTC_RULES, reduces_rules]) >>~-
  ([‘reduces꙳ (xs +++ (ys +++ zs))’],
   step reduces_app_assoc >> metis_tac[RTC_RULES, reduces_rules]) >>~-
  ([‘reduces꙳ (_ +++ Cons _ _ +++ _)’],
   step reduces_app_nested >> metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces (Cons h xs +++ ys) ws’]
  >- (first_x_assum $ qspec_then ‘ARB’ kall_tac >> gvs[reduces_APP_cases] >>~-
      ([‘reduces꙳ (Cons _ _ +++ _)’],
       step reduces_appcons >> simp[PULL_EXISTS] >>
       metis_tac[RTC_RULES, reduces_rules]) >~
      [‘reduces꙳ (Cons h xs +++ ys +++ zs)’]
      >- (step2 reduces_cong_appl reduces_appcons >>
          step reduces_appcons >> simp[PULL_EXISTS] >>
          metis_tac[RTC_RULES, reduces_rules]) >>
      metis_tac[RTC_RULES, reduces_rules]) >~
  [‘reduces (xs +++ ys) ws’, ‘reduces ys zs’]
  >- (‘reduces (xs +++ ys) (xs +++ zs)’ by metis_tac[reduces_rules] >>
      first_x_assum (drule_then $ qx_choose_then ‘ws'’ strip_assume_tac) >>
      metis_tac[]) >~
  [‘reduces (xs +++ ys) ws’, ‘reduces xs zs’]
  >- (‘reduces (xs +++ ys) (zs +++ ys)’ by metis_tac[reduces_rules] >>
      first_x_assum (drule_then $ qx_choose_then ‘ws'’ strip_assume_tac) >>
      metis_tac[]) >>
  metis_tac[RTC_RULES, reduces_rules]
QED

Theorem reduces_SN:
  SN reduces
Proof
  simp[SN_def] >> irule relationTheory.WF_SUBSET >> simp[] >>
  qexists_tac ‘inv_image ($< LEX $< LEX SHORTLEX $<)
               (λt. (NILCount t, rAPP_count t, cheights t))’ >>
  simp[WF_reduces] >> irule WF_inv_image >> irule pairTheory.WF_LEX >>
  simp[pairTheory.WF_LEX, listTheory.WF_SHORTLEX]
QED

Theorem reduces_CR:
  CR reduces
Proof
  irule Newmans_lemma >> simp[reduces_SN, WCR_def] >>
  MATCH_ACCEPT_TAC local_confluence
QED
