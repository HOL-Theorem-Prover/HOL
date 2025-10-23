(*===========================================================================*)
(* Formal Language Theory                                                    *)
(*                                                                           *)
(* A formal language is a set of strings over an alphabet. The type 'a list  *)
(* is the representation of strings. The following language operations are   *)
(* introduced: concatenation, iterated concatenation, Kleene Star, and left  *)
(* quotient. We prove a collection of the standard algebraic laws, then      *)
(* Arden's lemma, and then develop the notion of finite state language.      *)
(*===========================================================================*)


Theory FormalLang
Ancestors
  pred_set arithmetic list
Libs
  pred_setLib Unicode[qualified]

(*---------------------------------------------------------------------------*)
(* Useful theorems and tactics                                               *)
(*---------------------------------------------------------------------------*)

val sym = SYM
val gsym = GSYM
val subst_all_tac = SUBST_ALL_TAC
val sym_subst_all_tac = subst_all_tac o sym
val pop_subst_tac = pop_assum subst_all_tac;
val pop_sym_subst_tac = pop_assum sym_subst_all_tac;
val pop_keep_tac = pop_assum mp_tac
val qpat_stage_tac = Lib.C qpat_x_assum mp_tac;
val pop_forget_tac = pop_assum kall_tac
val qpat_forget_tac = Lib.C qpat_x_assum kall_tac;
val forget_tac = WEAKEN_TAC

fun irule_with q = reverse $ subgoal q THENL [pop_assum irule,all_tac];

Triviality APPEND_EQNS[simp] = LIST_CONJ [APPEND,APPEND_NIL,APPEND_eq_NIL];

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)

Type lang = ``:'a list set``

(*---------------------------------------------------------------------------*)
(* Make "epsilon" (= UTF8.chr 0x03B5) stand for the empty string             *)
(*---------------------------------------------------------------------------*)

Overload "\206\181"[local] = listSyntax.nil_tm

Theorem LANG_CASES:
  A ⊆ {ε} ∨ ∃x. x ∈ A DIFF {ε}
Proof
  simp [SUBSET_SING] >>
  Cases_on ‘A = ∅’ >> gvs[] >>
  Cases_on ‘A = {ε}’ >> gvs[] >>
  Cases_on ‘A’ >> gvs [EXTENSION,EQ_IMP_THM] >>
  metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Alphabet of a set of strings                                              *)
(*---------------------------------------------------------------------------*)

Definition ALPHABET_OF_def:
  ALPHABET_OF L = BIGUNION{set w | w ∈ L}
End

Theorem FINITE_ALPHABET_OF:
  FINITE L ⇒ FINITE (ALPHABET_OF L)
Proof
  rw[ALPHABET_OF_def]
  >- (rw [GSPEC_IMAGE,combinTheory.o_DEF] >>
      irule IMAGE_FINITE >> rw[IN_DEF] >> metis_tac[])
  >- rw[]
QED

Theorem word_alphabet_of:
  w ∈ L ⇒ EVERY (λa. a ∈ ALPHABET_OF L) w
Proof
  rw [ALPHABET_OF_def,PULL_EXISTS,EVERY_MEM] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Binary language concatenation. Right infix                                *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "dot" (Infixr 675);

Definition dot_def :
  A dot B = {x ++ y | x ∈ A /\ y ∈ B}
End

val _ =  (* use \bullet for dot *)
 let val bullet = UTF8.chr 0x2022
 in Unicode.unicode_version {u = bullet, tmnm = "dot"} end

Theorem IN_dot:
  w ∈ A • B <=> ?u v. (w = u ++ v) /\ u ∈ A /\ v ∈ B
Proof
  rw [dot_def]
QED

Theorem EPSILON_IN_dot[simp]:
  ε ∈ A • B <=> ε ∈ A /\ ε ∈ B
Proof
 metis_tac [IN_dot,APPEND_EQNS]
QED

Theorem DOT_EMPTYSET[simp]:
  A • {} = {} ∧ {} • A = {}
Proof
  rw [dot_def,EXTENSION]
QED

Theorem DOT_EPSILONSET[simp]:
  A • {ε} = A ∧ {ε} • A = A
Proof
 rw [dot_def,EXTENSION]
QED

Theorem DOT_EQ_EMPTYSET[simp]:
  A • B = ∅ ⇔ A = ∅ ∨ B = ∅
Proof
  rw [EXTENSION,IN_dot] >> metis_tac[]
QED

Theorem DOT_EQ_EPSILONSET[simp]:
  A • B = {ε} ⇔ A = {ε} ∧ B = {ε}
Proof
  strip_assume_tac LANG_CASES >>
  strip_assume_tac (LANG_CASES |> Q.INST [‘A’ |-> ‘B’]) >>
  gvs [SUBSET_SING] >>
  ‘A ≠ {ε} ∧ B ≠ {ε}’ by
    (simp [EXTENSION] >> metis_tac[]) >> simp[] >>
  rw[EXTENSION,IN_dot,EQ_IMP_THM,PULL_EXISTS] >>
  metis_tac[]
QED

Theorem DOT_ASSOC:
  A • (B • C) = (A • B) • C
Proof
  rw [EXTENSION,IN_dot] >> metis_tac [APPEND_ASSOC]
QED

Theorem DOT_UNION_LDISTRIB:
  A • (B ∪ C) = (A • B) ∪ (A • C)
Proof
  rw [EXTENSION,IN_dot] >> metis_tac []
QED

Theorem DOT_UNION_RDISTRIB:
  (A ∪ B) • C = (A • C) ∪ (B • C)
Proof
  rw [EXTENSION,IN_dot] >> metis_tac []
QED

Theorem DOT_MONO:
  A ⊆ C /\ B ⊆ D ==> (A • B) ⊆ (C • D)
Proof
  rw [SUBSET_DEF,IN_dot] >> metis_tac []
QED

Theorem STRCAT_IN_DOT:
  a ∈ A /\ b ∈ B ==> (a ++ b) ∈ A • B
Proof
 metis_tac[IN_dot]
QED

(*
  ⊢ l1 ⧺ l2 = m1 ⧺ m2 ⇔
     (∃l. l1 = m1 ⧺ l ∧ m2 = l ⧺ l2) ∨
     (∃l. m1 = l1 ⧺ l ∧ l2 = l ⧺ m2)
*)
Theorem LEVY_LEMMA = listTheory.APPEND_EQ_APPEND;

Theorem STRCAT_IN_DOT_IFF:
  (w1 ++ w2 ∈ A • B)
  <=>
  ∃u v. u ∈ A ∧ v ∈ B /\
        ((∃l. w1 = u ⧺ l ∧ v = l ⧺ w2) ∨
          ∃l. u = w1 ⧺ l ∧ w2 = l ⧺ v)
Proof
  simp[IN_dot,LEVY_LEMMA] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Iterated language concatenation.                                          *)
(*---------------------------------------------------------------------------*)

Definition DOTn_def:
  DOTn A 0 = {ε} ∧
  DOTn A (SUC n) = A • DOTn A n
End

Theorem DOT_DOTn_COMM:
  ∀n. A • DOTn A n = DOTn A n • A
Proof
 Induct >> rw [DOTn_def] >> metis_tac [DOT_ASSOC]
QED

Theorem DOTn_EMPTYSET:
  !n. DOTn {} n = if n=0 then {ε} else {}
Proof
  Induct >> rw [DOTn_def]
QED

Theorem DOTn_EPSILONSET[simp]:
  !n. DOTn {ε} n = {ε}
Proof
  Induct
   >> rw [DOTn_def,dot_def,EXTENSION]
   >> metis_tac[APPEND_EQNS]
QED

Theorem EPSILON_IN_DOTn[simp]:
  !n. (ε ∈ DOTn A n) <=> (n=0) \/ (ε ∈ A)
Proof
  Induct >> rw [DOTn_def] >> metis_tac[]
QED

Theorem DOTn_UNION:
  !n x A B. x ∈ DOTn A n ==> x ∈ DOTn (A ∪ B) n
Proof
  Induct >> rw [DOTn_def,IN_dot] >> metis_tac[]
QED

Theorem DOTn_DIFF:
  !n x A B. x ∈ DOTn (A DIFF B) n ==> x ∈ DOTn A n
Proof
  Induct >> rw [DOTn_def,IN_dot] >> metis_tac[]
QED

Theorem STRCAT_IN_DOTn_SUC:
  (a ∈ A /\ b ∈ DOTn A n) \/
  (a ∈ DOTn A n /\ b ∈ A)
   ==> (a ++ b) ∈ DOTn A (SUC n)
Proof
 rw [DOTn_def] >> metis_tac [STRCAT_IN_DOT,DOT_DOTn_COMM]
QED

Theorem STRCAT_IN_DOTn_ADD:
  ∀m n a b A.
    a ∈ DOTn A m /\ b ∈ DOTn A n ==> (a ++ b) ∈ DOTn A (m + n)
Proof
 Induct >> rw [DOTn_def] >> gvs [IN_dot]
  >> `(v ++ b) IN DOTn A (m + n)` by metis_tac []
  >> metis_tac [STRCAT_IN_DOTn_SUC,APPEND_ASSOC,
                DECIDE``SUC(m+n) = n + SUC m``]
QED

Theorem IN_DOTn_ELIM:
  ∀n A w. w ∈ DOTn A n ==> (w = ε) \/ ?k. w ∈ DOTn (A DELETE ε) k
Proof
  Induct >> rw [DOTn_def,IN_dot] >>
  res_tac >> Cases_on `u` >> rw [] >>
  `h::t IN (A DELETE [])` by rw []
  >- (qexists_tac ‘SUC 0’ >> gvs [DOTn_def])
  >- metis_tac [STRCAT_IN_DOTn_SUC,APPEND_EQNS]
QED

(*---------------------------------------------------------------------------*)
(* Kleene star                                                               *)
(*---------------------------------------------------------------------------*)

Definition KSTAR_def:
  KSTAR(L:'a lang) = BIGUNION {DOTn L n | n IN UNIV}
End

Definition KPLUS_def:
  KPLUS(L:'a lang) = BIGUNION {DOTn L n | 0 < n}
End

val _ =
  List.app temp_overload_on [("RTC", ``KSTAR``), ("TC", ``KPLUS``)];

Theorem IN_KSTAR:
  x ∈ KSTAR(L) <=> ?n. x ∈ DOTn L n
Proof
  rw [KSTAR_def,BIGUNION] >>
  rw [SPECIFICATION] >>
  metis_tac[]
QED

Theorem KSTAR_EQN:
  KSTAR A = {ε} ∪ A • KSTAR A
Proof
  rw[EXTENSION,EQ_IMP_THM,IN_KSTAR]
  >- (Cases_on `n` >> gvs[DOTn_def] >>
      gvs[IN_dot,IN_KSTAR,PULL_EXISTS] >> metis_tac[])
  >- metis_tac[EPSILON_IN_DOTn]
  >- (gvs[IN_dot,IN_KSTAR] >> metis_tac [STRCAT_IN_DOTn_SUC])
QED

Theorem EPSILON_IN_KSTAR[simp]:
  ε ∈ KSTAR A
Proof
  simp [Once KSTAR_EQN,EXTENSION]
QED

Theorem KSTAR_EMPTYSET[simp]:
  KSTAR {} = {ε}
Proof
  simp [Once KSTAR_EQN]
QED

Theorem KSTAR_EPSILONSET[simp]:
  KSTAR {ε} = {ε}
Proof
  simp [EXTENSION, IN_KSTAR]
QED

Theorem SUBSET_KSTAR[simp]:
  A ⊆ KSTAR(A)
Proof
  simp [Ntimes KSTAR_EQN 2, DOT_UNION_LDISTRIB] >>
  simp [SUBSET_UNION, AC UNION_ASSOC UNION_COMM]
QED

Theorem IN_KSTAR_SING[simp]:
  x ∈ KSTAR {x}
Proof
  ACCEPT_TAC
     (SUBSET_KSTAR |> Q.INST [`A` |-> `{x}`] |> SRULE[SUBSET_DEF])
QED

(* TODO: move to pred_setLib simpset *)
Theorem IN_COND[simp,local]:
  x ∈ (if A then B else C) ⇔ if A then x ∈ B else x ∈ C
Proof
  rw[]
QED

Triviality sing_absorb:
  {x} ∪ t = {y} ⇔ x = y ∧ t ⊆ {x}
Proof
  rw[EXTENSION,SUBSET_DEF] >> metis_tac[]
QED

Theorem KSTAR_TRIVIAL[simp]:
  (KSTAR A = {x}) ⇔ x = ε ∧ A ⊆ {ε}
Proof
  rw [EQ_IMP_THM] >> rw[] >>
  gvs[Once KSTAR_EQN,sing_absorb] >>
  gvs[IN_dot,SUBSET_DEF,SUBSET_SING] >>
  metis_tac[EXTENSION,NOT_IN_EMPTY,EPSILON_IN_KSTAR]
QED

Theorem KSTAR_TRIVIAL_ALT:
  KSTAR A = {x} ⇔ x = ε ∧ ∀a. a ∈ A ⇒ a = ε
Proof
  rw [KSTAR_TRIVIAL,SUBSET_DEF] >> metis_tac[]
QED

Theorem KSTAR_DIFF_EPSILONSET:
  KSTAR A = KSTAR (A DIFF {ε})
Proof
  reverse $ rw [EXTENSION,IN_KSTAR,EQ_IMP_THM]
  >- metis_tac [DOTn_DIFF] >>
  dxrule IN_DOTn_ELIM >> rw[]
  >- metis_tac [EPSILON_IN_DOTn]
  >- (simp[DIFF_INSERT] >> metis_tac[])
QED

Theorem KSTAR_ADD_EPSILONSET:
  KSTAR A = KSTAR ({ε} ∪ A)
Proof
  rw [EXTENSION,EQ_IMP_THM]
  >- metis_tac [IN_KSTAR,DOTn_UNION,UNION_COMM] >>
  pop_keep_tac >> Cases_on ‘ε ∈ A’
  >- simp[INSERT_UNION] >>
  simp[SimpLHS, Once KSTAR_DIFF_EPSILONSET] >>
  dep_rewrite.DEP_PURE_REWRITE_TAC
      [SET_RULE “(s ∩ t = ∅) ⇒ (s ∪ t) DIFF s = t”] >>
  simp [EXTENSION]
QED

Theorem KSTAR_CASES:
  w ∈ KSTAR A
   ⇔
  w = ε ∨ ∃w1 w2. w = w1++w2 ∧ w1 ∈ (A DIFF {ε}) ∧ w2 ∈ KSTAR A
Proof
  pure_once_rewrite_tac [KSTAR_DIFF_EPSILONSET] >>
  rw[SimpLHS,Once KSTAR_EQN] >>
  rw[EQ_IMP_THM] >> disj2_tac
  >- (gvs [IN_dot] >> metis_tac[])
  >- (irule STRCAT_IN_DOT >> rw[])
QED

Theorem KSTAR_IND:
  ∀P. P ε ∧ (∀w1 w2. w1 ∈ (A DIFF {ε}) ∧ P w2 ⇒ P (w1 ++ w2)) ⇒ ∀w. w ∈ KSTAR A ⇒ P w
Proof
  pure_once_rewrite_tac [KSTAR_DIFF_EPSILONSET] >>
  rw [IN_KSTAR] >> pop_keep_tac >>
  qid_spec_tac ‘w’ >> Induct_on ‘n’ >>
  gvs[DOTn_def] >> rw [IN_dot] >>
  metis_tac[]
QED

Theorem IN_KSTAR_LIST:
  s ∈ KSTAR A <=> ∃wlist. EVERY (λw. w ∈ A ∧ w ≠ ε) wlist ∧ s = FLAT wlist
Proof
  eq_tac >> qid_spec_tac ‘s’
  >- (ho_match_mp_tac KSTAR_IND >> rw[]
      >- (qexists_tac ‘[]’ >> rw [])
      >- (qexists_tac ‘w1 :: wlist’ >> rw []))
  >- (simp[PULL_EXISTS] >>
      Induct_on ‘wlist’ >> rw[] >> gvs[] >>
      rw [Once KSTAR_EQN] >> metis_tac[STRCAT_IN_DOT])
QED

(*---------------------------------------------------------------------------*)
(* Weaker version is easier to apply right-to-left                           *)
(*---------------------------------------------------------------------------*)

Triviality flat_filter_not_null[simp]:
  FLAT (FILTER ($~ o NULL) lists) = FLAT lists
Proof
  Induct_on ‘lists’ >> rw[NULL_EQ]
QED

Theorem IN_KSTAR_LIST_ALT:
  s ∈ KSTAR A <=> ∃wlist. EVERY (λw. w ∈ A) wlist ∧ s = FLAT wlist
Proof
  rw [IN_KSTAR_LIST,EQ_IMP_THM]
  >- (irule_at Any EQ_REFL >>
      pop_keep_tac >>
      ho_match_mp_tac EVERY_MONOTONIC >> simp[])
  >- (irule_at Any $ GSYM flat_filter_not_null >>
      simp[EVERY_FILTER,NULL_EQ] >> irule EVERY_MONOTONIC >>
      first_x_assum $ irule_at Any >> metis_tac[])
QED

Theorem KSTAR_SUBSET_UNION:
  KSTAR A ⊆ KSTAR(A ∪ B)
Proof
  simp [SUBSET_DEF] >> ho_match_mp_tac KSTAR_IND >> rw[] >>
  simp [Once KSTAR_CASES] >> first_x_assum (irule_at Any) >>
  metis_tac[]
QED

Theorem SUBSET_KSTAR_DOT[simp]:
  B ⊆ KSTAR A • B
Proof
  simp [Once KSTAR_EQN, DOT_UNION_RDISTRIB]
QED

Theorem KSTAR_MONO:
  A ⊆ B ⇒ KSTAR A ⊆ KSTAR B
Proof
 rw [IN_KSTAR_LIST,SUBSET_DEF] >>
 irule_at Any EQ_REFL >> gvs [EVERY_MEM]
QED

Theorem KSTAR_EQ_INTRO:
  (!n. DOTn A n = DOTn B n) ==> (KSTAR A = KSTAR B)
Proof
  rw [EXTENSION,IN_KSTAR]
QED

Theorem KSTAR_DOT_KSTAR[simp]:
  KSTAR A • KSTAR A = KSTAR A
Proof
  rw [EXTENSION,IN_KSTAR_LIST,IN_dot,EQ_IMP_THM,PULL_EXISTS]
  >- (qexists_tac ‘wlist ++ wlist'’ >> rw[])
  >- (qexists_tac ‘wlist’ >> qexists_tac ‘[]’ >> rw[])
QED

Theorem KSTAR_KSTAR[simp]:
  KSTAR(KSTAR A) = KSTAR A
Proof
  rw [SET_EQ_SUBSET] >> simp [SUBSET_DEF] >>
  ho_match_mp_tac KSTAR_IND >> rw[] >>
  metis_tac [SRULE [EXTENSION,IN_dot] KSTAR_DOT_KSTAR]
QED

Theorem DOT_KSTAR_COMM:
  A • KSTAR A = KSTAR A • A
Proof
  rw [EXTENSION,IN_dot,IN_KSTAR,PULL_EXISTS,EQ_IMP_THM] >>
  metis_tac[SRULE [EXTENSION,IN_dot] DOT_DOTn_COMM]
QED

Theorem KSTAR_DOT_SHIFT:
  KSTAR (A • B) • A = A • KSTAR(B • A)
Proof
  reverse $ qsuff_tac
  ‘∀n. DOTn (A • B) n • A = A • DOTn (B • A) n’ >-
  (Induct >> rw [DOTn_def] >> metis_tac [DOT_ASSOC]) >>
  rw[IN_KSTAR,IN_dot,EXTENSION] >> metis_tac[]
QED

Theorem KSTAR_UNION_lemA[local]:
  KSTAR (A ∪ B) ⊆ KSTAR(KSTAR A • B) • KSTAR A
Proof
  simp [SUBSET_DEF] >> ho_match_mp_tac KSTAR_IND >> rw[]
  >- (pop_keep_tac >> simp [KSTAR_DOT_SHIFT] >>
      qspec_tac (‘KSTAR (B • KSTAR A)’,‘L’) >> gen_tac >>
      rw [IN_dot] >> first_assum (irule_at Any) >>
      rw [Once KSTAR_CASES] >> metis_tac[APPEND_ASSOC])
  >- (gvs [IN_dot] >> first_x_assum (irule_at Any) >>
      qexists_tac ‘w1 ++ u’ >> rw[Once KSTAR_CASES] >>
      rpt (first_assum (irule_at Any)) >> rw[IN_dot] >>
      last_x_assum (irule_at Any) >>
      metis_tac [APPEND_EQNS,EPSILON_IN_KSTAR])
QED

Triviality lemB_lem[local]:
  KSTAR A • B ⊆ KSTAR (A ∪ B)
Proof
  rw [IN_dot,SUBSET_DEF] >>
  pop_keep_tac >> qid_spec_tac ‘v’ >>
  pop_keep_tac >> qid_spec_tac ‘u’ >>
  ho_match_mp_tac KSTAR_IND >> rw[]
  >- (pop_keep_tac >> qid_spec_tac ‘v’ >> simp [GSYM SUBSET_DEF] >>
      irule SUBSET_TRANS >> metis_tac [SUBSET_UNION,SUBSET_KSTAR])
  >- (pure_once_rewrite_tac [GSYM APPEND_ASSOC] >>
      irule (iffRL KSTAR_CASES) >> disj2_tac >> simp[] >>
      res_tac >> first_x_assum (irule_at Any) >>
      metis_tac[APPEND_ASSOC])
QED


Theorem KSTAR_UNION_lemB[local]:
  KSTAR(KSTAR A • B) • KSTAR A ⊆ KSTAR (A ∪ B)
Proof
  rw [IN_dot,SUBSET_DEF] >>
  pop_keep_tac >> qid_spec_tac ‘v’ >>
  pop_keep_tac >> qid_spec_tac ‘u’ >>
  ho_match_mp_tac KSTAR_IND >> rw[]
  >- metis_tac [KSTAR_SUBSET_UNION,SUBSET_DEF] >>
  gvs [IN_dot] >> pure_once_rewrite_tac [GSYM APPEND_ASSOC] >>
  irule_with
  ‘∀A u v. u ∈ KSTAR A ∧ v ∈ KSTAR A ⇒ u ++ v ∈ KSTAR A’ >-
    (rw[] >>
     irule (lemB_lem |> SIMP_RULE std_ss [SUBSET_DEF,IN_dot]) >>
     metis_tac[]) >>
  rpt pop_forget_tac >> rw[] >>
  metis_tac [KSTAR_DOT_KSTAR |> SIMP_RULE std_ss [EXTENSION,IN_dot]]
QED

Theorem KSTAR_UNION:
  KSTAR (A ∪ B) = KSTAR(KSTAR A • B) • KSTAR A
Proof
  metis_tac[SET_EQ_SUBSET,KSTAR_UNION_lemA,KSTAR_UNION_lemB]
QED

Theorem DOT_SQUARED_SUBSET:
  A • A ⊆ A ==> A • KSTAR(A) ⊆ A
Proof
  rw [IN_dot, SUBSET_DEF,PULL_EXISTS] >>
  qpat_x_assum ‘u ∈ A’ mp_tac >> qid_spec_tac ‘u’ >>
  pop_keep_tac >> qid_spec_tac ‘v’ >>
  ho_match_mp_tac KSTAR_IND >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Theorems about KPLUS                                                      *)
(*---------------------------------------------------------------------------*)

Theorem IN_KPLUS:
  w ∈ KPLUS A <=> ∃n. 0 < n ∧ w ∈ DOTn A n
Proof
  rw [KPLUS_def,BIGUNION,EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
  metis_tac[]
QED

Theorem KPLUS_KSTAR:
  KPLUS A = A • KSTAR A
Proof
  rw [EXTENSION, IN_KPLUS, EQ_IMP_THM]
  >- (Cases_on ‘n’ >> gvs[DOTn_def,IN_dot,IN_KSTAR] >> metis_tac[])
  >- (gvs [IN_dot,IN_KSTAR] >>
      qexists_tac ‘SUC n’ >> rw [DOTn_def,IN_dot] >> metis_tac[])
QED

Theorem EPSILON_IN_KPLUS[simp]:
  ε ∈ KPLUS A ⇔ ε ∈ A
Proof
  rw [KPLUS_KSTAR]
QED

Theorem KPLUS_EQN:
  KPLUS A = A ∪ A • KPLUS A
Proof
  simp[SimpLHS,KPLUS_KSTAR] >>
  simp [Once KSTAR_EQN,DOT_UNION_LDISTRIB] >>
  simp[KPLUS_KSTAR]
QED

Theorem KPLUS_EMPTYSET[simp]:
  KPLUS ∅ = ∅
Proof
  rw [Once KPLUS_EQN,EXTENSION,IN_dot]
QED

Theorem KPLUS_EPSILONSET[simp]:
  KPLUS {ε} = {ε}
Proof
  rw [Once KPLUS_KSTAR,EXTENSION]
QED

Theorem KPLUS_EQ_KSTAR:
  ε ∈ A ⇔ (KPLUS A = KSTAR A)
Proof
  rw[KPLUS_KSTAR] >>
  simp[SimpRHS,Once KSTAR_EQN] >>
  rw [EXTENSION,EQ_IMP_THM]
  >- rw[]
  >- metis_tac [EPSILON_IN_dot]
QED

Theorem KPLUS_UNION_EPSILONSET:
  KPLUS A ∪ {ε} = KSTAR A
Proof
  rw[KPLUS_KSTAR] >>
  simp[SimpRHS,Once KSTAR_EQN] >>
  metis_tac [UNION_COMM]
QED

Theorem KPLUS_EQ_KSTAR_DIFF_EPSILONSET:
  ε ∉ A ⇒ KPLUS A = (KSTAR A) DIFF {ε}
Proof
  rw[Once $ GSYM KPLUS_UNION_EPSILONSET] >>
  rw[DIFF_SAME_UNION,DIFF_INSERT] >>
  metis_tac[DELETE_NON_ELEMENT,EPSILON_IN_KPLUS]
QED

(* NB: could be strengthened to disallow ϵ, as is done for KSTAR *)
Theorem KPLUS_IND:
  ∀P. (∀w. w ∈ A ⇒ P w) ∧
      (∀w1 w2. w1 ∈ A ∧ P w2 ⇒ P (w1 ++ w2))
      ⇒
      ∀w. w ∈ KPLUS A ⇒ P w
Proof
  rw [IN_KPLUS] >> pop_keep_tac >>
  qid_spec_tac ‘w’ >> Induct_on ‘n’ >>
  rw[] >> gvs[DOTn_def,IN_dot] >>
  Cases_on ‘n’ >> gvs[DOTn_def] >>
  metis_tac[]
QED

Theorem IN_KPLUS_LIST:
   w ∈ KPLUS A
   ⇔
   ∃wlist. wlist ≠ [] ∧ EVERY (λw. w ∈ A) wlist ∧ (w = FLAT wlist)
Proof
  eq_tac >> qid_spec_tac ‘w’
  >- (ho_match_mp_tac KPLUS_IND >> rw[]
      >- (qexists_tac ‘[w]’ >> rw [])
      >- (qexists_tac ‘w1 :: wlist’ >> rw[]))
  >- (rw[PULL_EXISTS] >> Induct_on ‘wlist’ >> rw[] >>
      simp [Once KPLUS_EQN] >> Cases_on ‘wlist’ >> gvs[] >>
      disj2_tac >> rw[IN_dot] >> metis_tac[APPEND_ASSOC])
QED

(*===========================================================================*)
(* Arden's Lemma.                                                            *)
(*===========================================================================*)

Theorem ARDEN_LEM1[local]:
  ε ∉ A ∧ (X = A • X ∪ B) ⇒ X ⊆ KSTAR A • B
Proof
  strip_tac >> simp[SUBSET_DEF] >> qx_gen_tac ‘w’ >>
  measureInduct_on ‘LENGTH w’ >>
  Cases_on ‘LENGTH w’ >> disch_tac
  >- (gvs[] >> metis_tac [EPSILON_IN_dot,IN_UNION]) >>
  ‘w ∈ B ∨ w ∈ A • X’ by
     metis_tac[EXTENSION,IN_UNION]
  >- metis_tac [SUBSET_DEF,SUBSET_KSTAR_DOT] >>
  pop_keep_tac >> rw[IN_dot] >> rename1 ‘w1 ++ w2 ∈ X’ >>
  ‘w2 ∈ KSTAR A • B’ by
    (first_x_assum irule >> simp[] >> Cases_on ‘w1’ >> gvs[]) >>
  pop_keep_tac >> rw[IN_dot] >> first_x_assum (irule_at Any) >>
  simp [Once KSTAR_CASES] >> disj2_tac >>
  (first_x_assum $ irule_at Any) >> (first_assum $ irule_at Any) >>
  gvs[] >> metis_tac[]
QED

Theorem ARDEN_LEM2[local]:
  X = A • X ∪ B ⇒ (KSTAR A • B) ⊆ X
Proof
  strip_tac >> rw[IN_dot,SUBSET_DEF,PULL_EXISTS] >>
  pop_keep_tac >> qid_spec_tac ‘v’ >>
  pop_keep_tac >> qid_spec_tac ‘u’ >>
  ho_match_mp_tac KSTAR_IND >> rw[]
  >- metis_tac [EXTENSION,IN_UNION]
  >- (first_x_assum drule >> strip_tac >>
      once_asm_rewrite_tac[] >>
      qpat_x_assum ‘_ = _’ (assume_tac o GSYM) >>
      simp [IN_dot] >> disj1_tac >>
      metis_tac [APPEND_ASSOC])
QED

Theorem ARDENS_LEMMA:
  ε ∉ A ∧ (X = (A • X) ∪ B) ==> X = KSTAR(A) • B
Proof
  metis_tac [ARDEN_LEM1,ARDEN_LEM2,SET_EQ_SUBSET]
QED

(*===========================================================================*)
(* Left quotient. Brzozowski derivatives (see regular/regexpScript.sml) are  *)
(* left quotient in the context of regexps.                                  *)
(*===========================================================================*)

Definition LEFT_QUOTIENT_def:
  LEFT_QUOTIENT x L = {y | (x ++ y) ∈ L}
End

Theorem IN_LEFT_QUOTIENT:
  y ∈ LEFT_QUOTIENT x L ⇔ (x ++ y) ∈ L
Proof
  simp [LEFT_QUOTIENT_def]
QED

Theorem LEFT_QUOTIENT_ELT:
  x ∈ L ⇔ ε ∈ LEFT_QUOTIENT x L
Proof
 simp [IN_LEFT_QUOTIENT]
QED

Theorem LEFT_QUOTIENT_EMPTYSET[simp]:
  LEFT_QUOTIENT x {} = {}
Proof
 rw[LEFT_QUOTIENT_def]
QED

Theorem LEFT_QUOTIENT_EPSILON[simp]:
  LEFT_QUOTIENT ε L = L
Proof
  rw[LEFT_QUOTIENT_def]
QED

Theorem LEFT_QUOTIENT_EPSILONSET[simp]:
  LEFT_QUOTIENT x {ε} = if x = ε then {ε} else {}
Proof
  rw[LEFT_QUOTIENT_def,EXTENSION,EQ_IMP_THM]
QED

(* Looping rewrite rule! Use LEFT_QUOTIENT_REC instead *)
Theorem LEFT_QUOTIENT_REC_ALT:
  LEFT_QUOTIENT x L =
   case x
    of ε => L
     | a::w => LEFT_QUOTIENT w (LEFT_QUOTIENT [a] L)
Proof
 Induct_on ‘x’ >> rw[LEFT_QUOTIENT_def]
QED

Theorem LEFT_QUOTIENT_REC:
  LEFT_QUOTIENT ε L = L ∧
  LEFT_QUOTIENT (a::w) L = LEFT_QUOTIENT w {y | ([a] ++ y ∈ L)}
Proof
  rw[Once LEFT_QUOTIENT_REC_ALT] >>
  metis_tac [LEFT_QUOTIENT_def,APPEND]
QED

Theorem LEFT_QUOTIENT_FOLDL:
  ∀x L.
  LEFT_QUOTIENT x L = FOLDL (λlang a. {y | [a] ++ y ∈ lang}) L x
Proof
 Induct >> rw[] >> gvs[] >>
 pop_assum (simp o single o GSYM) >>
 simp [Once LEFT_QUOTIENT_REC]
QED

Theorem LEFT_QUOTIENT_APPEND:
  LEFT_QUOTIENT (x ++ y) L = LEFT_QUOTIENT y (LEFT_QUOTIENT x L)
Proof
  rw [LEFT_QUOTIENT_def]
QED

Theorem LEFT_QUOTIENT_SYMBOL:
  x ≠ ε ⇒ LEFT_QUOTIENT x {[a]} = (if x = [a] then {ε} else {})
Proof
  rw[LEFT_QUOTIENT_def,EXTENSION,EQ_IMP_THM] >>
  Cases_on ‘x’ >> gvs[]
QED

Theorem LEFT_QUOTIENT_UNION[simp]:
  LEFT_QUOTIENT x (L1 ∪ L2) = LEFT_QUOTIENT x L1 ∪ LEFT_QUOTIENT x L2
Proof
  rw[LEFT_QUOTIENT_def,EXTENSION,EQ_IMP_THM]
QED

Theorem LEFT_QUOTIENT_INTER[simp]:
  LEFT_QUOTIENT x (L1 ∩ L2) = LEFT_QUOTIENT x L1 ∩ LEFT_QUOTIENT x L2
Proof
  rw[LEFT_QUOTIENT_def,EXTENSION,EQ_IMP_THM]
QED

Theorem LEFT_QUOTIENT_COMPL[simp]:
  LEFT_QUOTIENT x (COMPL L) = COMPL (LEFT_QUOTIENT x L)
Proof
  rw [LEFT_QUOTIENT_def,EXTENSION,EQ_IMP_THM]
QED

(*---------------------------------------------------------------------------*)
(* TODO: the "full string" versions of the following two theorems            *)
(*---------------------------------------------------------------------------*)

Theorem LEFT_QUOTIENT_SYMBOL_DOT:
  LEFT_QUOTIENT [a] (L1 • L2) =
    ((LEFT_QUOTIENT [a] L1 • L2)
    ∪
    (if ε ∈ L1 then LEFT_QUOTIENT [a] L2 else {}))
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  gvs [IN_LEFT_QUOTIENT,IN_dot]
  >- (Cases_on ‘u = ε’ >> gvs[] >> disj1_tac >>
      Cases_on ‘u’ >> gvs[] >> metis_tac[])
  >- metis_tac [APPEND]
  >- metis_tac [APPEND]
QED

Theorem LEFT_QUOTIENT_SYMBOL_KSTAR:
  LEFT_QUOTIENT [a] (KSTAR L) = LEFT_QUOTIENT [a] L • (KSTAR L)
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  gvs [IN_LEFT_QUOTIENT,IN_dot]
  >- (drule (iffLR KSTAR_CASES) >> rw[] >>
      Cases_on ‘w1’ >> gvs[] >> metis_tac[])
  >- (rw[Once KSTAR_CASES] >>
      rpt (first_x_assum (irule_at Any)) >> rw[])
QED

Definition LEFT_QUOTIENTS_OF_def:
  LEFT_QUOTIENTS_OF [] L = [L] ∧
  LEFT_QUOTIENTS_OF (a::w) L = L :: LEFT_QUOTIENTS_OF w (LEFT_QUOTIENT [a] L)
End

(*---------------------------------------------------------------------------*)
(* There's a coercion between symbols in an alphabet set A and the words     *)
(* needed to build A*.                                                       *)
(*---------------------------------------------------------------------------*)

Theorem KSTAR_Alphabet[simp]:
  w ∈ KSTAR {[a] | a ∈ A} <=> EVERY (λa. a ∈ A) w
Proof
  rw [IN_KSTAR_LIST,EQ_IMP_THM,PULL_EXISTS]
  >- (pop_keep_tac >> Induct_on ‘wlist’ >> rw[] >> rw[])
  >- (qexists_tac ‘MAP (λa. [a]) w’ >> rw[EVERY_MAP] >>
      Induct_on ‘w’ >> rw[])
QED

(*---------------------------------------------------------------------------*)
(* A formal language is a set of strings over a finite set of symbols        *)
(*---------------------------------------------------------------------------*)

Definition IS_FORMAL_LANG_def:
  IS_FORMAL_LANG (L,A) ⇔ FINITE A ∧ L ⊆ KSTAR {[a] | a ∈ A}
End

Theorem IS_FORMAL_LANG_UNION:
  IS_FORMAL_LANG (L,A) ∧ FINITE B ⇒ IS_FORMAL_LANG (L,A ∪ B)
Proof
  simp_tac bool_ss [IS_FORMAL_LANG_def] >> rpt strip_tac
  >- simp [FINITE_UNION]
  >- (irule SUBSET_TRANS >>
      first_x_assum (irule_at Any) >>
      irule KSTAR_MONO >> rw [SUBSET_DEF])
QED

(*---------------------------------------------------------------------------*)
(* Definition of the finite state languages. That these characterize the     *)
(* regular languages is proved in regular/regularTheory.                     *)
(*---------------------------------------------------------------------------*)

Definition INTRINSIC_STATES_def:
  INTRINSIC_STATES (L,A) = {LEFT_QUOTIENT w L | EVERY (λa. a ∈ A) w}
End

Theorem IN_INTRINSIC_STATES[simp]:
  L' ∈ INTRINSIC_STATES (L,A)
  <=>
  ∃w. L' = LEFT_QUOTIENT w L ∧ EVERY (λa. a ∈ A) w
Proof
  simp [INTRINSIC_STATES_def]
QED

Theorem IN_INTRINSIC_STATES_IMP:
 EVERY (λa. a ∈ A) w ⇒ LEFT_QUOTIENT w L ∈ INTRINSIC_STATES (L,A)
Proof
  metis_tac [IN_INTRINSIC_STATES]
QED

Definition FINITE_STATE_def:
  FINITE_STATE (L,A) <=>
    IS_FORMAL_LANG (L,A) ∧
    FINITE (INTRINSIC_STATES (L,A))
End

Theorem IN_FINITE_STATE[simp]:
  (L,A) ∈ FINITE_STATE <=>
  FINITE A ∧
  (∀x. x ∈ L ⇒ EVERY (λa. a ∈ A) x) ∧
  FINITE (INTRINSIC_STATES (L,A))
Proof
  simp [IN_DEF,FINITE_STATE_def,SUBSET_DEF,IS_FORMAL_LANG_def] >>
  metis_tac[]
QED

Theorem FINITE_STATE_EMPTYSET:
  FINITE A ==> FINITE_STATE ({},A)
Proof
  rw[FINITE_STATE_def, INTRINSIC_STATES_def,
     LEFT_QUOTIENT_EMPTYSET,IS_FORMAL_LANG_def] >>
  rw[combinTheory.o_DEF, GSPEC_IMAGE, IMAGE_CONST]
QED

Theorem FINITE_STATE_EPSILONSET:
  FINITE A ⇒ FINITE_STATE ({ε},A)
Proof
  rw[FINITE_STATE_def, INTRINSIC_STATES_def,
     LEFT_QUOTIENT_EPSILON,IS_FORMAL_LANG_def] >>
  irule SUBSET_FINITE >> rw [SUBSET_DEF] >>
  qexists_tac ‘{{ε}; ∅}’ >> rw[] >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Following leads up to FINITE_STATE_FINITE_SET, which is a language-level  *)
(* version of the "all finite sets are regular" theorem.                     *)
(*---------------------------------------------------------------------------*)

Definition prefixes_def:
  prefixes w = {w1 | ∃w2. w = w1 ++ w2}
End

Triviality prefixes_snoc:
  prefixes (SNOC h t) = (SNOC h t) INSERT prefixes t
Proof
  rw[prefixes_def,EXTENSION,EQ_IMP_THM, SNOC_APPEND]
  >- (strip_assume_tac (SNOC_CASES |> Q.SPEC ‘w2’) >>
      rw[] >> gvs[SNOC_APPEND])
  >- metis_tac[APPEND_NIL]
  >- metis_tac[APPEND_ASSOC]
QED

Theorem FINITE_prefixes:
  ∀w. FINITE (prefixes w)
Proof
  recInduct SNOC_INDUCT >> rw[]
  >- rw[prefixes_def]
  >- rw[prefixes_snoc]
QED

Definition PREFIXES_def:
  PREFIXES L = BIGUNION (IMAGE prefixes L)
End

Theorem FINITE_PREFIXES:
  FINITE L ⇒ FINITE (PREFIXES L)
Proof
  rw [PREFIXES_def] >> metis_tac[FINITE_prefixes]
QED

Theorem LEFT_QUOTIENT_PREFIXES:
 w ∉ PREFIXES L ⇔ LEFT_QUOTIENT w L = {}
Proof
  rw[PREFIXES_def,LEFT_QUOTIENT_def] >>
  rw [GSYM IMP_DISJ_THM,PULL_FORALL,prefixes_def] >>
  rw [EQ_IMP_THM,EXTENSION] >> metis_tac[]
QED

(* TODO: put in pred_setTheory *)

Theorem finite_image_const:
 (∀x. x ∈ s ⇒ f x = c) ⇒ FINITE(IMAGE f s)
Proof
  Cases_on ‘s = {}’ >> rw[] >>
  ‘IMAGE f s = {c}’ by
    (rw[EXTENSION,EQ_IMP_THM]
     >- metis_tac[]
     >- (Cases_on ‘s’ >> gvs[] >> metis_tac[])) >>
  rw[]
QED

Theorem FINITE_STATE_FINITE_SET:
  FINITE L ⇒ FINITE_STATE (L,ALPHABET_OF L)
Proof
  rw[FINITE_STATE_def, INTRINSIC_STATES_def,
     LEFT_QUOTIENT_EPSILON,IS_FORMAL_LANG_def]
  >- metis_tac[FINITE_ALPHABET_OF]
  >- rw[SUBSET_DEF,word_alphabet_of]
  >- (simp [combinTheory.o_DEF, GSPEC_IMAGE] >>
      qabbrev_tac ‘words = λw. EVERY (λa. a ∈ ALPHABET_OF L) w’ >>
      ‘words = words ∩ (PREFIXES L ∪ COMPL (PREFIXES L))’ by
         rw[EXTENSION,EQ_IMP_THM] >>
      pop_assum SUBST1_TAC >> rw[UNION_OVER_INTER]
      >- (irule IMAGE_FINITE >> irule FINITE_INTER >>
          metis_tac[FINITE_PREFIXES])
      >- (irule finite_image_const >> rw[] >>
          metis_tac [LEFT_QUOTIENT_PREFIXES]))
QED

(*---------------------------------------------------------------------------*)
(* Closure properties for FINITE_STATE                                       *)
(*---------------------------------------------------------------------------*)

fun Conjecture name q s = Parse.Term q

val _ =
  Conjecture "FINITE_STATE_UNION"
    ‘FINITE_STATE(L1,A) ∧ FINITE_STATE (L2,A) ⇒ FINITE_STATE(L1 ∪ L2, A)’
    "";

val _ =
  Conjecture "FINITE_STATE_DOT"
    ‘FINITE_STATE(L1,A) ∧ FINITE_STATE (L2,A) ⇒ FINITE_STATE(L1 • L2, A)’
    "";

val _ =
  Conjecture "FINITE_STATE_KSTAR"
    ‘FINITE_STATE(L,A) ⇒ FINITE_STATE(KSTAR L, A)’
    "";

(*---------------------------------------------------------------------------*)
(* Inductive definition of regular sets                                      *)
(*---------------------------------------------------------------------------*)

Inductive REGSET:
[~empty:]
  (FINITE A ⇒ REGSET ({},A))
[~alphabet:]
  (∀a. FINITE A ∧ a ∈ A ⇒ REGSET ({[a]}, A))
[~union:]
  (∀L1 L2. REGSET (L1,A) ∧ REGSET (L2,A) ⇒ REGSET (L1 ∪ L2, A))
[~dot:]
  (∀L1 L2. REGSET (L1,A) ∧ REGSET (L2,A) ⇒ REGSET (L1 • L2, A))
[~star:]
  (∀L. REGSET (L,A) ⇒ REGSET (KSTAR L, A))
End

val _ =
  Conjecture "REGSET_SUBSET_FINITE_STATE"
    ‘REGSET ⊆ FINITE_STATE’
    "";
