(*===========================================================================*)
(* Formal Language Theory                                                    *)
(*                                                                           *)
(* A formal language is a set of strings over an alphabet. The type 'a list  *)
(* is the representation of strings. The following language operations are   *)
(* introduced: concatenation, iterated concatenation, Kleene Star, and left  *)
(* quotient. We prove a collection of the standard algebraic laws, including *)
(* Arden's lemma, and then define the notion of finite state language and    *)
(* prove some basic results about it.                                        *)
(*===========================================================================*)


(*===========================================================================*)
(*   Load and open context theories and proof support (lists and sets).      *)
(*===========================================================================*)

open HolKernel boolLib bossLib Parse;
open pred_setLib pred_setTheory arithmeticTheory listTheory;

val _ = new_theory "FormalLang";

(*---------------------------------------------------------------------------*)
(* Basic simplification support                                              *)
(*---------------------------------------------------------------------------*)

val APPEND_EQNS = LIST_CONJ [APPEND,APPEND_NIL,APPEND_eq_NIL];

val basic_ss = list_ss ++ PRED_SET_ss ++ rewrites [APPEND_EQNS];


(*---------------------------------------------------------------------------*)
(* Basic lexical support for readability                                     *)
(*---------------------------------------------------------------------------*)

Type lang = ``:'a list set``

val epsilon = UTF8.chr 0x03B5;

val _ = temp_overload_on (epsilon,listSyntax.nil_tm);

(*---------------------------------------------------------------------------*)
(* Binary language concatenation. Right infix                                *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "dot" (Infixr 675);

Definition dot_def :
  A dot B = {x ++ y | x IN A /\ y IN B}
End

Theorem  IN_dot:
  !w A B. w IN (A dot B) <=> ?u v. (w = u ++ v) /\ u IN A /\ v IN B
Proof
  RW_TAC basic_ss [dot_def]
QED

Theorem DOT_EMPTYSET:
 !A. (A dot {} = {}) /\ ({} dot A = {})
Proof
 RW_TAC basic_ss [dot_def,EXTENSION]
QED

Theorem DOT_EPSILON:
  !A. (A dot {ε} = A) /\ ({ε} dot A = A)
Proof
 RW_TAC basic_ss [dot_def,EXTENSION]
QED

Theorem STRCAT_IN_dot:
  !a b A B. a IN A /\ b IN B ==> (a ++ b) IN (A dot B)
Proof
 METIS_TAC[IN_dot]
QED

val LEVY_LEMMA = listTheory.APPEND_EQ_APPEND;

Theorem STRCAT_IN_dot_IFF:
 (w1 ++ w2 IN A dot B)
 <=>
 ∃u v. u ∈ A ∧ v ∈ B /\
       ((∃l. w1 = u ⧺ l ∧ v = l ⧺ w2) ∨
         ∃l. u = w1 ⧺ l ∧ w2 = l ⧺ v)
Proof
  simp[IN_dot,LEVY_LEMMA] >> metis_tac[]
QED

Theorem EPSILON_IN_DOT:
 !A B. ε IN (A dot B) <=> ε IN A /\ ε IN B
Proof
 METIS_TAC [IN_dot,APPEND_EQNS]
QED

Theorem DOT_ASSOC:
  !A B C. A dot (B dot C) = (A dot B) dot C
Proof
  RW_TAC basic_ss [EXTENSION,IN_dot] >> METIS_TAC [APPEND_ASSOC]
QED

Theorem DOT_UNION_LDISTRIB:
 !A B C. A dot (B UNION C) = (A dot B) UNION (A dot C)
Proof
 RW_TAC basic_ss [EXTENSION,IN_dot] >> METIS_TAC []
QED

Theorem DOT_UNION_RDISTRIB:
  !A B C. (A UNION B) dot C = (A dot C) UNION (B dot C)
Proof
 RW_TAC basic_ss [EXTENSION,IN_dot] >> METIS_TAC []
QED

Theorem DOT_MONO:
  !A B C D. A SUBSET C /\ B SUBSET D ==> (A dot B) SUBSET (C dot D)
Proof
  RW_TAC basic_ss [SUBSET_DEF,IN_dot] >> METIS_TAC []
QED

(*---------------------------------------------------------------------------*)
(* Iterated language concatenation.                                          *)
(*---------------------------------------------------------------------------*)

Definition DOTn_def:
  DOTn A 0 = {ε} ∧
  DOTn A (SUC n) = A dot (DOTn A n)
End

Theorem DOTn_RIGHT:
 !n A. A dot DOTn A n = DOTn A n dot A
Proof
 Induct >> RW_TAC basic_ss [DOTn_def]
  >- RW_TAC basic_ss [EXTENSION,IN_dot]
  >- METIS_TAC [DOT_ASSOC]
QED

Theorem SUBSET_DOTn:
  !A. A SUBSET DOTn A (SUC 0)
Proof
  RW_TAC basic_ss [SUBSET_DEF,DOTn_def,IN_dot]
QED

Theorem EPSILON_IN_DOTn_ZERO:
 !x A. x IN DOTn A 0 <=> (x = ε)
Proof
  RW_TAC basic_ss [DOTn_def]
QED

Theorem STRCAT_IN_DOTn_SUC:
 !a b A n.
    (a IN A /\ b IN DOTn A n) \/
    (a IN DOTn A n /\ b IN A)
     ==> (a ++ b) IN DOTn A (SUC n)
Proof
 RW_TAC basic_ss [DOTn_def] >> METIS_TAC [STRCAT_IN_dot,DOTn_RIGHT]
QED

Theorem STRCAT_IN_DOTn_ADD:
 !m n a b A.
    a IN DOTn A m /\ b IN DOTn A n ==> (a ++ b) IN DOTn A (m + n)
Proof
 Induct >> RW_TAC basic_ss [DOTn_def]
  >> FULL_SIMP_TAC basic_ss [IN_dot]
  >> `(v ++ b) IN DOTn A (m + n)` by METIS_TAC []
  >> METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_ASSOC,
                DECIDE``SUC(m+n) = n + SUC m``]
QED

Theorem DOTn_EMPTYSET:
  !n. DOTn {} n = if n=0 then {ε} else {}
Proof
  Induct >> RW_TAC basic_ss [DOTn_def,DOT_EMPTYSET]
QED

Theorem DOTn_EPSILON:
 !n. DOTn {ε} n = {ε}
Proof
  Induct
   >> RW_TAC basic_ss [DOTn_def,dot_def,EXTENSION]
   >> METIS_TAC[APPEND_EQNS]
QED

Theorem EPSILON_IN_DOTn:
 !n. (ε IN DOTn A n) <=> (n=0) \/ (ε IN A)
Proof
  Induct
   >> RW_TAC basic_ss [DOTn_def,EPSILON_IN_DOT]
   >> METIS_TAC[]
QED

Theorem DOTn_UNION:
 !n x A B. x IN DOTn A n ==> x IN DOTn (A UNION B) n
Proof
  Induct >> RW_TAC basic_ss [DOTn_def,IN_dot] >> METIS_TAC[]
QED

Theorem DOTn_DIFF:
 !n x A B. x IN DOTn (A DIFF B) n ==> x IN DOTn A n
Proof
  Induct >> RW_TAC basic_ss [DOTn_def,IN_dot] >> METIS_TAC[]
QED

Theorem DOTn_EPSILON_FREE:
 !n A w. w IN DOTn A n ==>
     (w = ε) \/
     ?k. w IN DOTn (A DELETE ε) k
Proof
 Induct >> RW_TAC basic_ss [DOTn_def,IN_dot] >>
 RES_TAC >> Cases_on `u` >> RW_TAC basic_ss [] >>
 `h::t IN (A DELETE [])` by RW_TAC basic_ss []
 >- METIS_TAC [SUBSET_DOTn,SUBSET_DEF]
 >- METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_EQNS]
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

Theorem IN_KSTAR:
  x IN KSTAR(L) <=> ?n. x IN DOTn L n
Proof
  RW_TAC basic_ss [KSTAR_def,BIGUNION] >>
  RW_TAC basic_ss [SPECIFICATION] >>
  METIS_TAC[]
QED

Theorem KSTAR_EQ_EPSILON_UNION_DOT:
  KSTAR A = {ε} UNION (A dot KSTAR A)
Proof
  rw[EXTENSION,EQ_IMP_THM,IN_KSTAR]
  >- (Cases_on `n` >> gvs[DOTn_def] >>
      gvs[IN_dot,IN_KSTAR,PULL_EXISTS] >> metis_tac[])
  >- metis_tac[EPSILON_IN_DOTn]
  >- (gvs[IN_dot,IN_KSTAR] >> metis_tac [STRCAT_IN_DOTn_SUC])
QED

Theorem IN_KSTAR_THM:
  w IN KSTAR L
  <=>
  w = ε \/ ?w1 w2. (w = w1++w2) /\ w1 IN L /\ w2 IN KSTAR L
Proof
  simp[SimpLHS, Once KSTAR_EQ_EPSILON_UNION_DOT] >>
  rw[EQ_IMP_THM] >> gvs[IN_dot] >> metis_tac[]
QED

Triviality IN_KSTAR_THM_STRONG_lemma:
 ∀w.
  w ∈ KSTAR L ∧ w ≠ ε
   ⇒
  ∃w1 w2. w = w1++w2 ∧ w1 ≠ ε ∧ w1 ∈ L ∧ w2 ∈ KSTAR L
Proof
 simp [IN_KSTAR,PULL_EXISTS] >>
 Induct_on ‘n’ >> rw[DOTn_def,IN_dot] >>
 Cases_on ‘u = ε’ >> gvs[] >> metis_tac[]
QED

Theorem IN_KSTAR_THM_STRONG:
  w ∈ KSTAR L
   ⇔
  w = ε ∨ ∃w1 w2. w = w1++w2 ∧ w1 ≠ ε ∧ w1 ∈ L ∧ w2 ∈ KSTAR L
Proof
 metis_tac [IN_KSTAR_THM_STRONG_lemma,IN_KSTAR_THM]
QED

Theorem KSTAR_EMPTYSET:
 KSTAR {} = {ε}
Proof
 RW_TAC basic_ss [EXTENSION,IN_KSTAR,DOTn_EMPTYSET,EQ_IMP_THM]
  >- (Cases_on `n` >> FULL_SIMP_TAC basic_ss [])
  >- METIS_TAC [IN_INSERT]
QED

Theorem EPSILON_IN_KSTAR:
 ε IN KSTAR A
Proof
  RW_TAC basic_ss [IN_KSTAR] >> METIS_TAC [DOTn_def,IN_INSERT]
QED

Theorem KSTAR_SING:
  x ∈ KSTAR {x}
Proof
 RW_TAC basic_ss [IN_KSTAR] >>
 Q.EXISTS_TAC `SUC 0` >>
 RW_TAC basic_ss [DOTn_def,IN_dot]
QED

Theorem SUBSET_KSTAR:
  A ⊆ KSTAR(A)
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR] >>
 Q.EXISTS_TAC `SUC 0` >>
 RW_TAC basic_ss [DOTn_def,IN_dot]
QED

Theorem KSTAR_TRIVIAL:
  s ⊆ {ε} ⇒ KSTAR s = {ε}
Proof
  rw [SUBSET_SING]
  >- metis_tac[KSTAR_EMPTYSET]
  >- rw [EXTENSION,IN_KSTAR,EQ_IMP_THM,DOTn_EPSILON]
QED

Theorem KSTAR_TRIVIAL_IFF:
  KSTAR s = {ε} ⇔ s ⊆ {ε}
Proof
  rw [EQ_IMP_THM,KSTAR_TRIVIAL] >>
  rw [SUBSET_DEF] >> Cases_on ‘x’ >> gvs[] >>
  ‘h::t ∈ KSTAR s’ by
    metis_tac [SUBSET_DEF,SUBSET_KSTAR] >>
  gvs[]
QED

Theorem SUBSET_KSTAR_DOT:
  B SUBSET (KSTAR A) dot B
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] >>
 MAP_EVERY Q.EXISTS_TAC [`[]`,`x`] >>
 RW_TAC basic_ss [] >> METIS_TAC [DOTn_def,IN_INSERT]
QED

Theorem STRCAT_IN_KSTAR:
  u IN A /\ v IN KSTAR(A) dot B ==> (u ++ v) IN KSTAR(A) dot B
Proof
 RW_TAC list_ss [IN_KSTAR,IN_dot] >>
 MAP_EVERY Q.EXISTS_TAC [`u++u'`,`v'`] >>
 RW_TAC list_ss [APPEND_ASSOC] >>
 Q.EXISTS_TAC `SUC n` >> RW_TAC std_ss [DOTn_def] >>
 METIS_TAC [STRCAT_IN_dot]
QED

Theorem KSTAR_EQ_INTRO:
 !A B. (!n. DOTn A n = DOTn B n) ==> (KSTAR A = KSTAR B)
Proof
  RW_TAC basic_ss [EXTENSION,IN_KSTAR]
QED

Theorem IN_KSTAR_LIST:
  s IN KSTAR A <=> ?wlist. EVERY (\w. w IN A) wlist /\ (s = FLAT wlist)
Proof
 RW_TAC list_ss [IN_KSTAR,EQ_IMP_THM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `s`
     >> Induct_on `n` >> RW_TAC list_ss []
     >- (FULL_SIMP_TAC list_ss [EPSILON_IN_DOTn_ZERO]
         >> RW_TAC list_ss []
         >> Q.EXISTS_TAC `[]`
         >> RW_TAC list_ss [])
     >- (FULL_SIMP_TAC list_ss [DOTn_def,IN_dot]
         >> RW_TAC list_ss [] >> RES_TAC
         >> Q.EXISTS_TAC `u::wlist` >> RW_TAC list_ss []))
 >- (Induct_on `wlist` >> FULL_SIMP_TAC list_ss []
     >- METIS_TAC [EPSILON_IN_DOTn]
     >- (RW_TAC list_ss [] >> RES_TAC
          >> Q.EXISTS_TAC `SUC n`
          >> RW_TAC list_ss [DOTn_def]
          >> METIS_TAC[IN_dot]))
QED

Theorem KSTAR_MONO:
  L1 ⊆ L2 ⇒ KSTAR L1 ⊆ KSTAR L2
Proof
 rw [IN_KSTAR_LIST,SUBSET_DEF] >>
 irule_at Any EQ_REFL >>
 gvs [EVERY_MEM]
QED

(*---------------------------------------------------------------------------*)
(* Theorems about L+                                                         *)
(*---------------------------------------------------------------------------*)

Theorem IN_KPLUS:
  w ∈ KPLUS L <=> ∃n. 0 < n ∧ w ∈ DOTn L n
Proof
  RW_TAC basic_ss [KPLUS_def,BIGUNION,EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
  metis_tac[]
QED

Theorem EPSILON_IN_KPLUS:
  ε ∈ KPLUS L ⇔ ε ∈ L
Proof
  RW_TAC basic_ss [IN_KPLUS,EQ_IMP_THM]
  >- (Induct_on ‘n’ >> rw[] >> fs[DOTn_def,EPSILON_IN_DOT])
  >- (qexists_tac ‘SUC 0’ >> rw[DOTn_def,EPSILON_IN_DOT])
QED

Theorem KPLUS_KSTAR:
  KPLUS L = L dot KSTAR L
Proof
  RW_TAC basic_ss [EXTENSION, IN_KPLUS,EQ_IMP_THM]
  >- (Cases_on ‘n’ >> fs[DOTn_def,IN_dot,IN_KSTAR] >> metis_tac[])
  >- (fs [IN_dot,IN_KSTAR] >> qexists_tac ‘SUC n’ >>
      RW_TAC basic_ss [DOTn_def,IN_dot] >> metis_tac[])
QED

Theorem KPLUS_EQ_KSTAR_DIFF_EPSILON:
  ε ∉ L ⇒ KPLUS L = KSTAR L DIFF {ε}
Proof
  rw [EXTENSION,IN_KPLUS,IN_KSTAR,EQ_IMP_THM]
  >- metis_tac[]
  >- (Cases_on ‘n’ >> fs[DOTn_def,IN_dot] >> metis_tac[])
  >- (Cases_on ‘n’ >> fs[DOTn_def] >> qexists_tac‘SUC n'’ >> rw[DOTn_def])
QED

Theorem KPLUS_EQ_KSTAR:
  ε ∈ L ⇔ (KPLUS L = KSTAR L)
Proof
 rw[EQ_IMP_THM]
 >- (rw[EXTENSION,IN_KSTAR,IN_KPLUS,EQ_IMP_THM]
     >- metis_tac[]
     >- (Cases_on ‘n’ >> fs[DOTn_def]
         >- (qexists_tac ‘SUC 0’ >> rw[DOTn_def,DOT_EPSILON])
         >- (qexists_tac ‘SUC n'’ >> rw[DOTn_def])))
 >- (spose_not_then assume_tac >> drule KPLUS_EQ_KSTAR_DIFF_EPSILON >>
     rw [] >> WEAKEN_TAC is_eq >>
     assume_tac (Q.INST [‘A’ |-> ‘L’] EPSILON_IN_KSTAR) >>
     ‘ε ∉ KSTAR L DIFF {ε}’ by rw[] >> metis_tac[EXTENSION])
QED

Triviality UNION_ABSORPTION:
  x ∈ s ⇒ s ∪ {x} = s
Proof
  rw [EXTENSION,EQ_IMP_THM] >> metis_tac[]
QED

Triviality UNION_ABSORPTION_EQ:
  s ∪ {x} = s ⇔ x ∈ s
Proof
  rw [EXTENSION,EQ_IMP_THM] >> metis_tac[]
QED

Theorem KPLUS_UNION_EPSILON_EQ_KSTAR:
  KPLUS L ∪ {ε} = KSTAR L
Proof
  Cases_on ‘ε ∈ L’
  >- (‘ε ∈ KPLUS L’ by metis_tac [EPSILON_IN_KPLUS] >>
      rw [UNION_ABSORPTION] >> metis_tac [KPLUS_EQ_KSTAR])
  >- (drule KPLUS_EQ_KSTAR_DIFF_EPSILON >> rw[] >>
      rw [GSYM (SRULE [Once UNION_COMM] SUBSET_UNION_ABSORPTION)] >>
      metis_tac [EPSILON_IN_KSTAR])
QED

Theorem IN_KPLUS_LIST_EPSILON_FREE:
  ε ∉ L ⇒
   (w IN KPLUS L
    ⇔
    ∃wlist. wlist ≠ [] ∧ EVERY (λw. w ∈ L) wlist ∧ (w = FLAT wlist))
Proof
  rw[EQ_IMP_THM]
  >- (drule KPLUS_EQ_KSTAR_DIFF_EPSILON >>
      disch_then SUBST_ALL_TAC >> gvs [IN_KSTAR_LIST] >>
      first_x_assum (irule_at Any) >>
      fs[FLAT_EQ_NIL,combinTheory.o_DEF] >>
      disch_then SUBST_ALL_TAC >> fs[])
  >- (rw [IN_KPLUS] >> qexists_tac ‘LENGTH wlist’ >> rw[]
      >- (Cases_on ‘wlist’ >> fs[])
      >- (Induct_on ‘wlist’ >> fs[] >> rw[] >>
          Cases_on ‘wlist’ >> fs[ONE,DOTn_def,IN_dot] >>
          rw[PULL_EXISTS] >> metis_tac[]))
QED

Theorem IN_KPLUS_LIST:
   w IN KPLUS L
   ⇔
   ∃wlist. wlist ≠ [] ∧ EVERY (λw. w ∈ L) wlist ∧ (w = FLAT wlist)
Proof
  Cases_on ‘ε ∈ L’
  >- (rw [iffLR KPLUS_EQ_KSTAR,IN_KSTAR_LIST,EQ_IMP_THM]
      >- (qexists_tac ‘ε :: wlist’ >> rw[])
      >- metis_tac[])
  >- metis_tac [IN_KPLUS_LIST_EPSILON_FREE]
QED

(*---------------------------------------------------------------------------*)
(* Some more complex equalities                                              *)
(*---------------------------------------------------------------------------*)

val lang_ss = basic_ss ++
               rewrites [IN_KSTAR, IN_dot, DOTn_def,
                         DOT_EMPTYSET,DOT_EPSILON, DOTn_EPSILON,
                         KSTAR_SING,KSTAR_EMPTYSET,EPSILON_IN_KSTAR];

Theorem KSTAR_EQ_KSTAR_UNION:
 KSTAR A = KSTAR ({ε} UNION A)
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- METIS_TAC [DOTn_UNION,UNION_COMM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `x` >>
     Induct_on `n` >> RW_TAC lang_ss [] THENL
     [METIS_TAC [EPSILON_IN_DOTn_ZERO],
      METIS_TAC [APPEND_EQNS],
      METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_EQNS]])
QED

Theorem KSTAR_DOT_KSTAR:
 (KSTAR A dot KSTAR A) = KSTAR A
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- METIS_TAC [STRCAT_IN_DOTn_ADD]
 >- (Cases_on `n` >> FULL_SIMP_TAC lang_ss[]
     >- METIS_TAC [APPEND_eq_NIL,EPSILON_IN_DOTn_ZERO]
     >- METIS_TAC [SUBSET_DOTn,SUBSET_DEF])
QED

Theorem KSTAR_KSTAR_EQ_KSTAR:
 !A. KSTAR(KSTAR A) = KSTAR A
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `x` >>
     Induct_on `n` >> RW_TAC lang_ss [] >>
     METIS_TAC [EPSILON_IN_DOTn_ZERO,STRCAT_IN_DOTn_ADD])
 >- METIS_TAC [SUBSET_KSTAR,IN_KSTAR,SUBSET_DEF]
QED

Theorem DOT_KSTAR_EQ_KSTAR_DOT:
 !A. (A dot KSTAR A) = (KSTAR A dot A)
Proof
  RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
  [‘(u++v) IN (DOTn A n dot A)’ by METIS_TAC [DOTn_RIGHT,EXTENSION,IN_dot],
   `(u++v) IN (A dot DOTn A n)` by METIS_TAC [DOTn_RIGHT,EXTENSION,IN_dot]]
 >> METIS_TAC [IN_dot]
QED

Triviality lemma:
 (!n. DOTn (A dot B) n dot A = A dot DOTn (B dot A) n)
   ==> (KSTAR (A dot B) dot A = A dot KSTAR(B dot A))
Proof
  RW_TAC lang_ss [EXTENSION] >> METIS_TAC[]
QED

Theorem KSTAR_DOT_SHIFT:
 !A. KSTAR (A dot B) dot A = A dot KSTAR(B dot A)
Proof
  GEN_TAC >> MATCH_MP_TAC lemma >>
  Induct >> RW_TAC lang_ss [] >> METIS_TAC [DOT_ASSOC]
QED

Theorem DOT_SQUARED_SUBSET:
 (L dot L) ⊆ L ==> (L dot KSTAR L) ⊆ L
Proof
 RW_TAC lang_ss [SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
 NTAC 2 (POP_ASSUM MP_TAC) >> MAP_EVERY Q.ID_SPEC_TAC [`v`, `u`] >>
 Induct_on `n` >> RW_TAC lang_ss [] >>
 METIS_TAC [DOT_ASSOC]
QED

Theorem KSTAR_UNION:
 !A B. KSTAR (A UNION B) = KSTAR(KSTAR A dot B) dot KSTAR A
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `x` >> Induct_on `n` THENL
  [METIS_TAC [EPSILON_IN_DOTn_ZERO,APPEND_EQNS],
   SIMP_TAC basic_ss [DOTn_def,DOTn_RIGHT] >> RW_TAC lang_ss [] THENL
   [`?u1 u2. (u = u1 ++ u2) /\ (?m. u1 IN DOTn (KSTAR A dot B) m) /\
             ?k. u2 IN DOTn A k` by METIS_TAC[] >>
     METIS_TAC [APPEND_ASSOC,STRCAT_IN_DOTn_SUC],
   `?u1 u2. (u = u1 ++ u2) /\ (?m. u1 IN DOTn (KSTAR A dot B) m) /\
            ?k. u2 IN DOTn A k` by METIS_TAC[] >>
     Q.EXISTS_TAC `u1 ++ (u2 ++ v)` >> Q.EXISTS_TAC `[]` >>
     RW_TAC lang_ss [APPEND_ASSOC] THENL
     [`u2 ++ v IN (KSTAR A dot B)` by (RW_TAC lang_ss [] >> METIS_TAC[])
        >> METIS_TAC [APPEND_ASSOC,STRCAT_IN_DOTn_SUC],
      METIS_TAC [EPSILON_IN_DOTn_ZERO]]]]
   ,
   REPEAT (POP_ASSUM MP_TAC) >> MAP_EVERY Q.ID_SPEC_TAC [`v`, `u`, `n`]
   >> Induct_on `n'` >> RW_TAC lang_ss [] THENL
   [POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `u` >>
     Induct_on`n` >> RW_TAC lang_ss [] THENL
     [METIS_TAC [EPSILON_IN_DOTn_ZERO],
      METIS_TAC [IN_UNION,APPEND_ASSOC,STRCAT_IN_DOTn_ADD,
                 STRCAT_IN_DOTn_SUC,DOTn_UNION]],
    `u' ++ v' IN DOTn A n' dot A` by METIS_TAC [IN_dot,DOTn_RIGHT] >>
    FULL_SIMP_TAC lang_ss [] >>
    METIS_TAC [IN_UNION,APPEND_ASSOC,STRCAT_IN_DOTn_ADD,
               STRCAT_IN_DOTn_SUC,DOTn_UNION]]]
QED

(*===========================================================================*)
(* Arden's Lemma.                                                            *)
(*===========================================================================*)

Triviality LENGTH_LESS:
 !u x v. (x = u++v) /\ ~(u = ε) ==> LENGTH v < LENGTH x
Proof
  Cases_on `u` >> RW_TAC list_ss []
QED

Theorem ARDEN_LEM1[local]:
  ε ∉ A ∧ (X = A dot X ∪ B) ⇒ X ⊆ KSTAR A dot B
Proof
 strip_tac >> simp[SUBSET_DEF] >> qx_gen_tac ‘w’ >>
 measureInduct_on `LENGTH w` >> Cases_on `LENGTH w` >> disch_tac
 >- (gvs[] >> metis_tac [EPSILON_IN_KSTAR,EPSILON_IN_DOT,IN_UNION])
 >- (‘w ∈ A dot X ∨ w ∈ B’ by metis_tac[EXTENSION,IN_UNION]
     >- (‘?u v. (w = u ++ v) /\ u ∈ A /\ v ∈ X ∧ u ≠ ε’
             by metis_tac [IN_dot] >>
         ‘LENGTH v < SUC n’ by metis_tac [LENGTH_LESS] >>
         ‘v IN KSTAR A dot B’ by metis_tac [] >>
         metis_tac [STRCAT_IN_KSTAR])
     >- metis_tac [SUBSET_DEF,SUBSET_KSTAR_DOT]
    )
QED

Triviality lemma:
  !A B X. (!n. (DOTn A n dot B) ⊆ X) ==> KSTAR(A) dot B ⊆ X
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] >> METIS_TAC []
QED

Theorem ARDEN_LEM2[local]:
  X = A dot X ∪ B ⇒ (KSTAR A dot B) ⊆ X
Proof
  strip_tac >> irule lemma >> Induct_on ‘n’
  >- (rw [DOTn_def,SUBSET_DEF,dot_def] >> metis_tac [IN_UNION])
  >- (‘A dot (DOTn A n dot B) ⊆ (A dot X)’
          by metis_tac [DOT_MONO,SUBSET_REFL] >>
      gvs [DOTn_def,GSYM DOT_ASSOC] >>
      metis_tac [IN_UNION,SUBSET_DEF])
QED

Theorem ARDENS_LEMMA:
  ε ∉ A ∧ (X = (A dot X) ∪ B)
  ==>
  X = KSTAR(A) dot B
Proof
  metis_tac [ARDEN_LEM1,ARDEN_LEM2,SET_EQ_SUBSET]
QED

(*===========================================================================*)
(* Left quotient. Brzozowski derivatives (see regular/regexpScript.sml) are  *)
(* left quotient on regexps.                                                 *)
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
  LEFT_QUOTIENT [a] (L1 dot L2) =
    ((LEFT_QUOTIENT [a] L1 dot L2)
    ∪
    (if ε ∈ L1 then LEFT_QUOTIENT [a] L2 else {}))
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  gvs [IN_LEFT_QUOTIENT,IN_dot]
  >- (Cases_on ‘u = ε’ >> gvs[] >> disj1_tac >>
      Cases_on ‘u’ >> gvs[] >> metis_tac[])
  >- metis_tac [APPEND]
  >- metis_tac [APPEND]
  >- (Cases_on ‘u’ >> gvs[] >> metis_tac[])
  >- metis_tac [APPEND]
QED

Theorem LEFT_QUOTIENT_SYMBOL_KSTAR:
  LEFT_QUOTIENT [a] (KSTAR L) = LEFT_QUOTIENT [a] L dot (KSTAR L)
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  gvs [IN_LEFT_QUOTIENT,IN_dot]
  >- (drule (iffLR IN_KSTAR_THM_STRONG) >> rw[] >>
      Cases_on ‘w1’ >> gvs[] >> metis_tac[])
  >- metis_tac [APPEND,IN_KSTAR_THM]
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
  Induct_on ‘w’ >>
  simp [Once IN_KSTAR_THM] >>
  rw [EQ_IMP_THM,PULL_EXISTS]
QED

(*---------------------------------------------------------------------------*)
(* The finite state languages are an abstract characterization of the        *)
(* regular languages.                                                        *)
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

(*---------------------------------------------------------------------------*)
(* Essentially the same as "all finite sets are regular"                     *)
(*---------------------------------------------------------------------------*)

Definition prefixes_def:
  prefixes w = {w1 | ∃w2. w = w1 ++ w2}
End

Triviality prefixes_len:
   w ∈ prefixes x ⇒ LENGTH w ≤ LENGTH x
Proof
 rw[prefixes_def] >> rw []
QED

Theorem prefixes_snoc:
  prefixes (SNOC h t) = (SNOC h t) INSERT prefixes t
Proof
  rw[prefixes_def,EXTENSION,EQ_IMP_THM]
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
  FINITE L ==> FINITE (PREFIXES L)
Proof
  rw [PREFIXES_def] >> metis_tac[FINITE_prefixes]
QED

Theorem LEFT_QUOTIENT_PREFIXES:
 x ∉ PREFIXES L ⇔ LEFT_QUOTIENT x L = {}
Proof
  rw[PREFIXES_def,LEFT_QUOTIENT_def] >>
  rw [GSYM IMP_DISJ_THM,PULL_FORALL,prefixes_def] >>
  rw [EQ_IMP_THM,EXTENSION] >> metis_tac[]
QED

Theorem finite_image_const:
 s ≠ ∅ ∧ (∀x. x ∈ s ⇒ f x = c) ⇒ FINITE(IMAGE f s)
Proof
  rw[] >>
  ‘IMAGE f s = {c}’ by
    (rw[EXTENSION,EQ_IMP_THM]
     >- metis_tac[]
     >- (Cases_on ‘s’ >> gvs[] >> metis_tac[])) >>
  rw[]
QED

Triviality lemma:
  w ∈ L ⇒ EVERY (λa. a ∈ ALPHABET_OF L) w
Proof
  rw [ALPHABET_OF_def,PULL_EXISTS,EVERY_MEM] >> metis_tac[]
QED

Theorem FINITE_STATE_FINITE_SET:
  FINITE L ⇒ FINITE_STATE (L,ALPHABET_OF L)
Proof
  strip_tac >>
  Cases_on ‘L = {} ∨ L = {ε}’ >> rw[]
  >- metis_tac[FINITE_ALPHABET_OF, FINITE_STATE_EMPTYSET]
  >- metis_tac[FINITE_ALPHABET_OF, FINITE_STATE_EPSILONSET]
  >- (gvs [] >>
      rw[FINITE_STATE_def, INTRINSIC_STATES_def,
         LEFT_QUOTIENT_EPSILON,IS_FORMAL_LANG_def]
      >- (rw[ALPHABET_OF_def]
          >- (drule IMAGE_FINITE >>
              rw[combinTheory.o_DEF, GSPEC_IMAGE] >>
              irule IMAGE_FINITE >> rw[IN_DEF] >> metis_tac[])
          >- rw[])
      >- (rw [SUBSET_DEF,ALPHABET_OF_def,PULL_EXISTS] >>
          rw [EVERY_MEM] >> metis_tac[])
      >- (simp [combinTheory.o_DEF, GSPEC_IMAGE] >>
          qabbrev_tac ‘words = λw. EVERY (λa. a ∈ ALPHABET_OF L) w’ >>
          ‘words = (words ∩ PREFIXES L) ∪ (words ∩ COMPL (PREFIXES L))’ by
              rw[EXTENSION,EQ_IMP_THM] >>
          qunabbrev_tac ‘words’ >> pop_assum SUBST_ALL_TAC >> rw[] >>
          qabbrev_tac ‘words = λw. EVERY (λa. a ∈ ALPHABET_OF L) w’
          >- (irule IMAGE_FINITE >> irule FINITE_INTER >>
              disj2_tac >> metis_tac[FINITE_PREFIXES])
          >- (irule finite_image_const >> rw[]
              >- metis_tac [LEFT_QUOTIENT_PREFIXES]
              >- (simp[EXTENSION] >>
                  ‘FINITE (IMAGE LENGTH L)’ by
                     metis_tac [IMAGE_FINITE] >>
                  ‘∃maxL. maxL ∈ L ∧ ∀w. w ∈ L ⇒ LENGTH w <= LENGTH maxL’ by
                     (imp_res_tac in_max_set >>
                      ‘IMAGE LENGTH L ≠ ∅’ by rw[IMAGE_EQ_EMPTY] >>
                      drule_all MAX_SET_IN_SET >> rw[IMAGE_DEF] >>
                      gvs[GSYM IMAGE_DEF] >> first_assum (irule_at Any) >> rw[] >>
                      first_x_assum irule >> metis_tac[]) >>
                  ‘∃h t. maxL = h::t’ by
                     (Cases_on ‘maxL’ >> gvs[EXTENSION] >> metis_tac[]) >>
                  qexists_tac ‘h::maxL’ >> rw[]
                  >- (qunabbrev_tac ‘words’ >> drule lemma >> rw[])
                  >- (rw[PREFIXES_def] >> rw[GSYM IMP_DISJ_THM] >>
                      strip_tac >> drule prefixes_len >>
                      first_x_assum drule >> rw[])))))
QED

(*
val _ = gen_remove_ovl_mapping epsilon listSyntax.nil_tm;
*)

val _ = export_theory();
