(*****************************************************************************)
(* Formal Language Theory                                                    *)
(*                                                                           *)
(* A formal language is a set of strings over an alphabet. The notion of     *)
(* 'a list exactly captures such strings. We define the following language   *)
(* operations: concatenation, iterated concatenation, and Kleene Star. We    *)
(* prove a collection of lemmas about these operations, including Arden's    *)
(* lemma.                                                                    *)
(*****************************************************************************)


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
(* A language is a set of strings over an alphabet. A string is represented  *)
(* by an 'a list.                                                            *)
(*---------------------------------------------------------------------------*)

Type lang = ``:'a list set``

val epsilon = UTF8.chr 0x03B5;

Overload epsilon = “[]”;

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

Theorem DOT_EMPTYSTRING:
  !A. (A dot {[]} = A) /\ ({[]} dot A = A)
Proof
 RW_TAC basic_ss [dot_def,EXTENSION]
QED

Theorem STRCAT_IN_dot:
  !a b A B. a IN A /\ b IN B ==> (a ++ b) IN (A dot B)
Proof
 METIS_TAC[IN_dot]
QED

Theorem EMPTY_IN_DOT:
 !A B. [] IN (A dot B) <=> [] IN A /\ [] IN B
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
  DOTn A 0 = {[]} /\
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

Theorem EMPTY_IN_DOTn_ZERO:
 !x A. x IN DOTn A 0 <=> (x = [])
Proof
  RW_TAC basic_ss [DOTn_def]
QED

Theorem STRCAT_IN_DOTn_SUC:
 !a b A n.
    (a IN A /\ b IN DOTn A n) \/
    (a IN DOTn A n /\ b IN A)
     ==> (a ++ b) IN DOTn A (SUC n)
Proof
 RW_TAC basic_ss [DOTn_def]
  >> METIS_TAC [STRCAT_IN_dot,DOTn_RIGHT]
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
  !n. DOTn {} n = if n=0 then {[]} else {}
Proof
  Induct >> RW_TAC basic_ss [DOTn_def,DOT_EMPTYSET]
QED

Theorem DOTn_EMPTYSTRING:
 !n. DOTn {[]} n = {[]}
Proof
  Induct
   >> RW_TAC basic_ss [DOTn_def,dot_def,EXTENSION]
   >> METIS_TAC[APPEND_EQNS]
QED

Theorem EMPTY_IN_DOTn:
 !n. ([] IN DOTn A n) <=> (n=0) \/ ([] IN A)
Proof
  Induct
   >> RW_TAC basic_ss [DOTn_def,EMPTY_IN_DOT]
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

(*---------------------------------------------------------------------------*)
(* This lemma can be extended so that k is as large or small as possible. It *)
(* says that a word in A^n is either empty or can be split into k non-empty  *)
(* pieces.                                                                   *)
(*---------------------------------------------------------------------------*)

Theorem DOTn_EMPTYSTRING_FREE:
 !n A w. w IN DOTn A n ==>
     (w = []) \/
     ?k. w IN DOTn (A DELETE []) k
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

Theorem IN_KSTAR:
   x IN KSTAR(L) <=> ?n. x IN DOTn L n
Proof
  RW_TAC basic_ss [KSTAR_def,BIGUNION] >>
  RW_TAC basic_ss [SPECIFICATION] >>
  METIS_TAC[]
QED

Theorem KSTAR_EMPTYSET:
 KSTAR {} = {[]}
Proof
 RW_TAC basic_ss [EXTENSION,IN_KSTAR,DOTn_EMPTYSET,EQ_IMP_THM]
  >- (Cases_on `n` >> FULL_SIMP_TAC basic_ss [])
  >- METIS_TAC [IN_INSERT]
QED

Theorem EMPTY_IN_KSTAR:
 !A. [] IN (KSTAR A)
Proof
  RW_TAC basic_ss [IN_KSTAR] >> METIS_TAC [DOTn_def,IN_INSERT]
QED

Theorem KSTAR_SING:
 !x. x IN (KSTAR {x})
Proof
 RW_TAC basic_ss [IN_KSTAR] >>
 Q.EXISTS_TAC `SUC 0` >>
 RW_TAC basic_ss [DOTn_def,IN_dot]
QED

Theorem SUBSET_KSTAR:
  !A. A SUBSET KSTAR(A)
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR] >>
 Q.EXISTS_TAC `SUC 0` >>
 RW_TAC basic_ss [DOTn_def,IN_dot]
QED

Theorem SUBSET_KSTAR_DOT:
  !A B. B SUBSET (KSTAR A) dot B
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] >>
 MAP_EVERY Q.EXISTS_TAC [`[]`,`x`] >>
 RW_TAC basic_ss [] >> METIS_TAC [DOTn_def,IN_INSERT]
QED

Theorem STRCAT_IN_KSTAR:
 !u v A B.
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
  !s A. s IN KSTAR A <=> ?wlist. EVERY (\w. w IN A) wlist /\ (s = FLAT wlist)
Proof
 RW_TAC list_ss [IN_KSTAR,EQ_IMP_THM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `s`
     >> Induct_on `n` >> RW_TAC list_ss []
     >- (FULL_SIMP_TAC list_ss [EMPTY_IN_DOTn_ZERO]
         >> RW_TAC list_ss []
         >> Q.EXISTS_TAC `[]`
         >> RW_TAC list_ss [])
     >- (FULL_SIMP_TAC list_ss [DOTn_def,IN_dot]
         >> RW_TAC list_ss [] >> RES_TAC
         >> Q.EXISTS_TAC `u::wlist` >> RW_TAC list_ss []))
 >- (Induct_on `wlist` >> FULL_SIMP_TAC list_ss []
     >- METIS_TAC [EMPTY_IN_DOTn]
     >- (RW_TAC list_ss [] >> RES_TAC
          >> Q.EXISTS_TAC `SUC n`
          >> RW_TAC list_ss [DOTn_def]
          >> METIS_TAC[IN_dot]))
QED

(*---------------------------------------------------------------------------*)
(* Some more complex equalities                                              *)
(*---------------------------------------------------------------------------*)

val lang_ss = basic_ss ++
               rewrites [IN_KSTAR, IN_dot, DOTn_def,
                         DOT_EMPTYSET,DOT_EMPTYSTRING, DOTn_EMPTYSTRING,
                         KSTAR_SING,KSTAR_EMPTYSET,EMPTY_IN_KSTAR];

Theorem KSTAR_EQ_EPSILON_UNION_DOT:
 !A. KSTAR A = {[]} UNION (A dot KSTAR A)
Proof
  RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
  >- (Cases_on `n` THENL
      [METIS_TAC[EMPTY_IN_DOTn_ZERO],
       FULL_SIMP_TAC lang_ss [] >> METIS_TAC[]])
  >- METIS_TAC [EMPTY_IN_DOTn_ZERO]
  >- METIS_TAC [STRCAT_IN_DOTn_SUC]
QED

Theorem IN_KSTAR_THM:
  !w L. w IN KSTAR L
        <=>
          (w = []) \/
           ?w1 w2. (w = w1++w2) /\ w1 IN L /\ w2 IN KSTAR L
Proof RW_TAC list_ss [Once KSTAR_EQ_EPSILON_UNION_DOT,IN_UNION, IN_SING,IN_dot]
QED

Theorem KSTAR_EQ_KSTAR_UNION:
 !A. KSTAR A = KSTAR ({[]} UNION A)
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- METIS_TAC [DOTn_UNION,UNION_COMM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `x` >>
     Induct_on `n` >> RW_TAC lang_ss [] THENL
     [METIS_TAC [EMPTY_IN_DOTn_ZERO],
      METIS_TAC [APPEND_EQNS],
      METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_EQNS]])
QED

Theorem KSTAR_DOT_KSTAR:
 !A. (KSTAR A dot KSTAR A) = KSTAR A
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- METIS_TAC [STRCAT_IN_DOTn_ADD]
 >- (Cases_on `n` >> FULL_SIMP_TAC lang_ss[]
     >- METIS_TAC [APPEND_eq_NIL,EMPTY_IN_DOTn_ZERO]
     >- METIS_TAC [SUBSET_DOTn,SUBSET_DEF])
QED

Theorem KSTAR_KSTAR_EQ_KSTAR:
 !A. KSTAR(KSTAR A) = KSTAR A
Proof
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM]
 >- (POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `x` >>
     Induct_on `n` >> RW_TAC lang_ss [] >>
     METIS_TAC [EMPTY_IN_DOTn_ZERO,STRCAT_IN_DOTn_ADD])
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
 !L. (L dot L) SUBSET L ==> (L dot KSTAR L) SUBSET L
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
  [METIS_TAC [EMPTY_IN_DOTn_ZERO,APPEND_EQNS],
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
      METIS_TAC [EMPTY_IN_DOTn_ZERO]]]]
   ,
   REPEAT (POP_ASSUM MP_TAC) >> MAP_EVERY Q.ID_SPEC_TAC [`v`, `u`, `n`]
   >> Induct_on `n'` >> RW_TAC lang_ss [] THENL
   [POP_ASSUM MP_TAC >> Q.ID_SPEC_TAC `u` >>
     Induct_on`n` >> RW_TAC lang_ss [] THENL
     [METIS_TAC [EMPTY_IN_DOTn_ZERO],
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
 !u x v. (x = u++v) /\ ~(u = epsilon) ==> LENGTH v < LENGTH x
Proof
  Cases_on `u` >> RW_TAC list_ss []
QED

Triviality lemma:
  !A B X. (!n. (DOTn A n dot B) ⊆ X) ==> KSTAR(A) dot B SUBSET X
Proof
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] >> METIS_TAC []
QED

Theorem ARDENS_LEMMA:
 !A B X:'a lang.
    ~(epsilon IN A) /\ (X = (A dot X) UNION B) ==> (X = KSTAR(A) dot B)
Proof
 rpt strip_tac >> rw_tac basic_ss [SET_EQ_SUBSET]
 >- (rewrite_tac [SUBSET_DEF] >> gen_tac >>
     measureInduct_on `LENGTH x` >>
     Cases_on `LENGTH x`
     >- (gvs [EMPTY_IN_DOT] >> metis_tac [EMPTY_IN_KSTAR,EMPTY_IN_DOT,IN_UNION])
     >- (strip_tac >>
         `x IN A dot X \/ x IN B` by metis_tac [IN_UNION]
         >- (`?u v. (x = u ++ v) /\ u IN A /\ v IN X` by metis_tac [IN_dot] >>
             `~(u = [])` by metis_tac [] >>
             `LENGTH v < LENGTH x` by metis_tac [LENGTH_LESS] >>
             `v IN KSTAR A dot B` by metis_tac [] >>
             metis_tac [STRCAT_IN_KSTAR])
         >- metis_tac [SUBSET_DEF,SUBSET_KSTAR_DOT])
    )
 >- (irule lemma >> Induct
     >- (RW_TAC basic_ss [DOTn_def,SUBSET_DEF,dot_def] >> metis_tac [IN_UNION])
     >- (`A dot (DOTn A n dot B) SUBSET (A dot X)`
            by metis_tac [DOT_MONO,SUBSET_REFL] >>
         gvs [DOTn_def,GSYM DOT_ASSOC] >> metis_tac [IN_UNION,SUBSET_DEF])
    )
QED

(*---------------------------------------------------------------------------*)
(* Abstract definition of the finite state languages. This is based on the   *)
(* "left quotient" operation. Brzozowski derivatives are the syntactic       *)
(* counterpart of left quotient.                                             *)
(*---------------------------------------------------------------------------*)

Definition Drop_def:
  Drop x L = {y | (x ++ y) ∈ L}
End

Definition Intrinsic_States_def:
  Intrinsic_States L = {Drop x L | x ∈ (UNIV:'a list set)}
End

Definition Finite_State_def:
  Finite_State L <=> FINITE (Intrinsic_States L)
End

(* TODO: put in pred_setTheory *)
Theorem IMAGE_CONSTANT:
  IMAGE (\y. x) s = (if s = {} then {} else {x})
Proof
  rw_tac lang_ss [EXTENSION,EQ_IMP_THM] >> metis_tac[]
QED

(* TODO: put in pred_setTheory *)
Theorem IMAGE_K:
  IMAGE (K x) s = (if s = {} then {} else {x})
Proof
  metis_tac [IMAGE_CONSTANT, combinTheory.K_DEF]
QED

Theorem Drop_EMPTY:
  Drop x {} = {}
Proof
 rw[Drop_def]
QED

Theorem Drop_epsilon:
  Drop epsilon L = L
Proof
 rw[Drop_def]
QED

Theorem Drop_word:
  Drop x L =
   case x
    of epsilon => L
     | h::t => Drop t (Drop [h] L)
Proof
 Induct_on ‘x’ >> rw[Drop_def]
QED

Theorem Finite_State_EMPTY:
  Finite_State {}
Proof
  rw[Finite_State_def, Intrinsic_States_def,Drop_EMPTY] >>
  rw[combinTheory.o_DEF, GSPEC_IMAGE, IMAGE_CONSTANT]
QED


val _ = export_theory();
