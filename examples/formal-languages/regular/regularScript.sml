(*===========================================================================*)
(* Basic automata theory: nfas, dfas, their equivalence via the subset       *)
(* construction, closure constructions, etc. The approach taken is           *)
(* set-oriented, rather than computational.                                  *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;
open combinTheory pairTheory listTheory
     mp_then nlistTheory numpairTheory
     pred_setTheory relationTheory
     rich_listTheory prim_recTheory
     arithmeticTheory FormalLangTheory;

infix byA;
val op byA = BasicProvers.byA;

val sym = SYM
val subst_all_tac = SUBST_ALL_TAC
val sym_subst_all_tac = subst_all_tac o sym
val pop_subst_tac = pop_assum subst_all_tac;
val pop_sym_subst_tac = pop_assum sym_subst_all_tac;
val pop_keep_tac = pop_assum mp_tac
val qpat_keep_tac = Lib.C qpat_x_assum mp_tac;
val pop_forget_tac = pop_assum kall_tac
val qpat_forget_tac = Lib.C qpat_x_assum kall_tac;
val forget_tac = WEAKEN_TAC

fun obtain_then q tac ttac = ttac (Q.prove(q,tac))

val PUSH_EXISTS = LIST_CONJ
  [GSYM RIGHT_OR_EXISTS_THM,
   GSYM LEFT_OR_EXISTS_THM,
   RIGHT_EXISTS_IMP_THM,
   RIGHT_EXISTS_AND_THM,
   LEFT_EXISTS_IMP_THM,
   LEFT_EXISTS_AND_THM,
   EXISTS_OR_THM];


val epsilon = UTF8.chr 0x03B5;

val _ = temp_overload_on (epsilon,listSyntax.nil_tm);

fun dty_metis_tac list =
  let open TypeBasePure
      val dtys =  TypeBase.elts()
      val distinct = List.mapPartial distinct_of dtys
      val one_one  = List.mapPartial one_one_of dtys
   in metis_tac (list @ distinct @ one_one)
   end

val _ = new_theory "regular";

(* NOTE: duplicate theorems:

pred_setTheory.in_max_set (THEOREM)
-----------------------------------
⊢ ∀s. FINITE s ⇒ ∀x. x ∈ s ⇒ x ≤ MAX_SET s

pred_setTheory.X_LE_MAX_SET (THEOREM)
-------------------------------------
⊢ ∀s. FINITE s ⇒ ∀x. x ∈ s ⇒ x ≤ MAX_SET s
*)

(*---------------------------------------------------------------------------*)
(* Local lemmas, possibly of wider use. Start with sets                      *)
(*---------------------------------------------------------------------------*)

Theorem ELT_SUBSET:
  a ∈ s ⇔ {a} ⊆ s
Proof
 rw[EQ_IMP_THM]
QED

Theorem SUBSET_SKOLEM_THM :
  (!x. P x ==> ?y. Q x y) <=> ?f. !x. P x ==> Q x (f x)
Proof
 metis_tac[]
QED

Triviality SUBSET_UNION_RIGHT:
 x ⊆ y ⇒ x ⊆ y ∪ z
Proof
  rw[SUBSET_DEF]
QED

Triviality UNION_EQ_DIFF:
 A ∪ B = C ⇒ A DIFF B = C DIFF B
Proof
  rw [EXTENSION] >> metis_tac[]
QED

Triviality DIFF_EQ_UNION:
 A DIFF B = C ⇒ A ∪ B = C ∪ B
Proof
  rw [EXTENSION] >> metis_tac[]
QED

Theorem SET_TO_LIST_11[simp]:
  ∀s1 s2. FINITE s1 ∧ FINITE s2 ⇒ (SET_TO_LIST s1 = SET_TO_LIST s2 ⇔ s1 = s2)
Proof
  metis_tac[listTheory.SET_TO_LIST_INV]
QED

Theorem MAX_SET_BOUNDED:
  FINITE s ∧ MAX_SET s < n ⇒ n ∉ s
Proof
 rw[] >> spose_not_then assume_tac >> drule_all X_LE_MAX_SET >> decide_tac
QED

(*---------------------------------------------------------------------------*)
(* List destructors: HD, TL, and LAST                                        *)
(*---------------------------------------------------------------------------*)

Triviality HD_APPEND[simp]:
 ∀l1 l2. l1 ≠ [] ⇒ HD (l1 ++ l2) = HD l1
Proof
 Cases >> rw[]
QED

Triviality HD_SNOC[simp]:
 ∀l x. l ≠ [] ⇒ HD (SNOC x l) = HD l
Proof
  Cases >> rw[]
QED

Triviality HD_FRONT[simp]:
 ∀l. 1 < LENGTH l ⇒ HD (FRONT l) = HD l
Proof
  Cases >> rw[FRONT_DEF]
QED

Triviality HD_MAP[simp]:
 l ≠ [] ⇒ HD (MAP f l) = f (HD l)
Proof
 Cases_on ‘l’ >> rw[]
QED

Triviality TL_APPEND[simp]:
 ∀l1 l2. l1 ≠ [] ⇒ TL (l1 ++ l2) = TL l1 ++ l2
Proof
 Cases >> rw[]
QED

Triviality LAST_MAP[simp]:
 l ≠ [] ⇒ LAST (MAP f l) = f (LAST l)
Proof
 Cases_on ‘l’ >> rw[]
QED

Triviality LAST_TL[simp]:
  ∀l. TL l ≠ [] ⇒ LAST (TL l) = LAST l
Proof
 Cases >> rw[LAST_DEF]
QED

Triviality EL_TL[simp]:
  ∀l. l ≠ [] ⇒ EL n (TL l) = EL (n+1) l
Proof
 Cases >> rw[GSYM ADD1]
QED

Triviality LENGTH_TL_ALT:
 n < LENGTH l ⇒ LENGTH (TL l) = LENGTH l − 1
Proof
 rw [LENGTH_TL]
QED

Triviality LESS_FRONT_LENGTH[simp]:
 ∀l n. 0 < n ∧ n < LENGTH l ⇒ n-1 < LENGTH (FRONT l)
Proof
  Cases >> rw[FRONT_DEF]
QED

(*---------------------------------------------------------------------------*)
(* EXISTS and EVERY                                                          *)
(*---------------------------------------------------------------------------*)

Theorem EXISTS_EL:
  EXISTS P l ⇔ ∃n. n < LENGTH l ∧ P (EL n l)
Proof
  Induct_on ‘l’ >> rw[] >> pop_forget_tac >> rw[EQ_IMP_THM]
  >- (irule_at Any (DECIDE “0 < SUC n”) >> rw[])
  >- (‘SUC n < SUC (LENGTH l)’ by decide_tac >>
      first_x_assum (irule_at Any) >> rw[])
  >- (Cases_on ‘n’ >> fs[] >> metis_tac[])
QED

Theorem EVERY_LAST:
  list ≠ [] ∧ EVERY P list ⇒ P (LAST list)
Proof
 rw[EVERY_EL,LAST_EL] >> fs[NOT_NIL_EQ_LENGTH_NOT_0]
QED

Theorem EVERY_HD:
  list ≠ [] ∧ EVERY P list ⇒ P (HD list)
Proof
 rw[EVERY_EL] >> metis_tac [EL,NOT_NIL_EQ_LENGTH_NOT_0]
QED

Triviality EVERY_TL:
  l ≠ [] ∧ EVERY P l ⇒ EVERY P (TL l)
Proof
 Cases_on ‘l’ >> rw[]
QED

Theorem EVERY_DISJ_LEFT:
  ∀P Q l. EVERY P l ⇒ EVERY (λx. P x ∨ Q x) l
Proof
  Induct_on ‘l’ >> rw[]
QED

Theorem EVERY_DISJ_RIGHT:
  ∀P Q l. EVERY Q l ⇒ EVERY (λx. P x ∨ Q x) l
Proof
  Induct_on ‘l’ >> rw[]
QED

Triviality POS_LENGTH_NOT_NIL:
  n < LENGTH list ⇒ list ≠ []
Proof
 Cases_on ‘list’ >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* FLAT                                                                      *)
(*---------------------------------------------------------------------------*)

Triviality FLAT_NOT_NIL:
  ll ≠ [] ∧ LAST ll ≠ [] ⇒ FLAT ll ≠ []
Proof
  rw [FLAT_EQ_NIL,o_DEF,EXISTS_EL] >> rfs [LAST_EL] >>
  first_x_assum (irule_at Any) >> fs[NOT_NIL_EQ_LENGTH_NOT_0]
QED

Theorem HD_FLAT:
  ll ≠ [] ∧ HD ll ≠ []
  ⇒
  HD (FLAT ll) = HD (HD ll)
Proof
  Cases_on ‘ll’ >> rw[]
QED

Theorem LAST_FLAT:
  ll ≠ [] ∧ LAST ll ≠ []
  ⇒
  LAST (FLAT ll) = LAST(LAST ll)
Proof
  Induct_on ‘ll’ >> rw[LAST_DEF] >> fs[] >>
  drule FLAT_NOT_NIL >> rw[LAST_APPEND_NOT_NIL,LAST_DEF]
QED

(*---------------------------------------------------------------------------*)
(* EL                                                                        *)
(*---------------------------------------------------------------------------*)

Triviality el_last[simp]:
 EL (LENGTH list) (list ⧺ [a]) = a
Proof
  MATCH_ACCEPT_TAC
   (SRULE[]
     (Q.SPEC ‘[]’ (Q.ID_SPEC (Q.ID_SPEC el_append3))))
QED

Theorem EL_APPEND2_ALT:
  (n < LENGTH L2 ==> EL (LENGTH L1 + n) (L1 ++ L2) = EL n L2) ∧
  (n < LENGTH L2 ==> EL (n + LENGTH L1) (L1 ++ L2) = EL n L2)
Proof
  rw [EL_APPEND_EQN]
QED

Triviality EL_LENGTH_LAST:
 ∀l1 l2. LENGTH l1 = LENGTH l2 + 1 ⇒ EL (LENGTH l2) l1 = LAST l1
Proof
 ho_match_mp_tac SNOC_INDUCT >> rw[ADD1] >>
 pop_assum (SUBST_ALL_TAC o GSYM) >> rw [EL_LENGTH_SNOC]
QED

Triviality LAST_MAP2:
  ∀l1 l2 f.
    l1 ≠ [] ∧ l2 ≠ [] ∧ LENGTH l1 = LENGTH l2
    ⇒ LAST (MAP2 f l1 l2) = f (LAST l1) (LAST l2)
Proof
  rw[] >>
  ‘MAP2 f l1 l2 ≠ []’ by (map_every Cases_on [‘l1’, ‘l2’] >> fs[]) >>
  rw [LAST_EL] >> irule EL_MAP2 >> Cases_on ‘l2’ >> fs[]
QED

Triviality snoc2:
 ∀list n. LENGTH list = n+2 ⇒ ∃z f. list = SNOC z f ∧ f ≠ []
Proof
  rpt strip_tac >> Cases_on ‘list = []’
  >- fs[]
  >- (drule SNOC_LAST_FRONT >> Cases_on ‘FRONT list = []’
      >- (Cases_on ‘list’ >> fs[])
      >- metis_tac [])
QED

(*---------------------------------------------------------------------------*)
(* KSTAR and RTC                                                             *)
(*---------------------------------------------------------------------------*)

Theorem KSTAR_FLAT:
  KSTAR L = {FLAT ls | ∀w. MEM w ls ⇒ w ∈ L}
Proof
 rw[EXTENSION,IN_KSTAR_LIST,EVERY_MEM] >> metis_tac[]
QED

Theorem KSTAR_DEF_ALT:
  KSTAR L = BIGUNION (IMAGE (DOTn L) UNIV)
Proof
  MP_TAC
    (KSTAR_def
       |> SIMP_RULE (srw_ss()) [GSPEC_IMAGE, combinTheory.o_DEF])
    >> rw [UNIV_DEF]
    >> metis_tac[]
QED

Triviality RTC_LIST_LR:
  ∀x y. RTC R x y ⇒
        ∃l. l ≠ [] ∧ HD l = x ∧ LAST l = y ∧
            ∀n. n < LENGTH l - 1 ⇒ R (EL n l) (EL (n + 1) l)
Proof
  Induct_on ‘RTC’ >> rw[]
  >- (rename [‘HD _ = q’] >> qexists_tac ‘[q]’ >> simp[])
  >- (rename [‘R q (HD l)’] >> qexists_tac ‘q::l’ >> simp[] >>
      conj_tac
      >- (Cases_on ‘l’ >> fs[])
      >- (Cases >> simp[arithmeticTheory.ADD_CLAUSES]))
QED

Triviality RTC_LIST_RL:
  ∀l. l ≠ [] ∧
      (∀n. n < LENGTH l - 1 ⇒ R (EL n l) (EL (n + 1) l))
     ⇒ RTC R (HD l) (LAST l)
Proof
  Induct_on ‘l’ >> gvs [LAST_DEF] >> rw[] >> fs[NOT_NIL_EQ_LENGTH_NOT_0] >>
  res_tac >> fs[] >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
  qexists_tac ‘HD l’ >> fs[] >> first_x_assum match_mp_tac >> rw[] >>
  ‘SUC n < LENGTH l’ by decide_tac >> res_tac >> fs[ADD_CLAUSES]
QED

Theorem RTC_LIST:
  ∀R x y. RTC R x y
        <=>
        ∃l. l ≠ [] ∧ HD l = x ∧ LAST l = y ∧
            ∀n. n < LENGTH l - 1 ⇒ R (EL n l) (EL (n + 1) l)
Proof
  metis_tac [RTC_LIST_LR, RTC_LIST_RL]
QED

(*---------------------------------------------------------------------------*)
(* Basic type abbreviations                                                  *)
(*---------------------------------------------------------------------------*)

Type state  = “:num”
Type symbol = “:num”
Type word   = “:symbol list”
Type language = “:word set”

(*---------------------------------------------------------------------------*)
(* Non-deterministic finite state automata (NFAs).                           *)
(*---------------------------------------------------------------------------*)

Datatype:
  nfa = <|
    Q : state set ;
    Sigma : symbol set ;
    delta : state -> symbol -> state set;
    initial : state set;
    final : state set
  |>
End

Definition wf_nfa_def:
  wf_nfa N ⇔
    FINITE N.Q ∧
    FINITE N.Sigma ∧
    N.initial ⊆ N.Q ∧
    N.final ⊆ N.Q ∧
    (∀q a. a ∈ N.Sigma ∧ q ∈ N.Q ⇒ N.delta q a ⊆ N.Q)
End

Theorem finite_nfa_successors:
 wf_nfa N ⇒
  ∀eq a. s ⊆ N.Q ∧ a ∈ N.Sigma ==> FINITE (BIGUNION {N.delta q a | q ∈ s})
Proof
  rw [] >>
  ‘FINITE s’ by metis_tac [SUBSET_FINITE,wf_nfa_def]
  >- (fs[GSPEC_IMAGE,o_DEF,IN_DEF] >> metis_tac [IMAGE_FINITE])
  >- (fs [wf_nfa_def] >> metis_tac [SUBSET_FINITE,SUBSET_DEF])
QED

Theorem nfa_initial_id[simp]:
 (N with initial := N.initial) = N
Proof
 rw [fetch "-" "nfa_component_equality"]
QED

(*---------------------------------------------------------------------------*)
(* A deterministic finite state automaton (DFA) is an NFA with a single      *)
(* start state, and where there is exactly one transition from a state for   *)
(* each symbol in Sigma.                                                     *)
(*---------------------------------------------------------------------------*)

Definition is_dfa_def:
  is_dfa N ⇔
    wf_nfa N ∧
    (∃q_0. N.initial = {q_0}) ∧
    (∀q a. q ∈ N.Q ∧ a ∈ N.Sigma ⇒ ∃q'. N.delta q a = {q'})
End

(*---------------------------------------------------------------------------

                                           /-----------\
                                           v           |
   --> ( 1 )  --a-->  (( 2 ))  --a,b-->  ( 4 ) --a,b --'
         |                                 ^
         b                                 |
         |                                 |
         V______________a,b________________/
       ( 3 )

 ---------------------------------------------------------------------------*)

Definition example_dfa_def:
  example_dfa =
   <| Q := {0;1;2;3;4};
      Sigma := { 1 (* a *); 2 (* b *) };
      delta := (λq. case q of
              | 1 => (λc. if c = 1 then {2} else
                          if c = 2 then {3} else {0})
              | 2 => (λc. if (c = 1) \/ (c = 2) then {4} else {0})
              | 3 => (λc. if (c = 1) \/ (c = 2) then {4} else {0})
              | 4 => (λc. if (c = 1) \/ (c = 2) then {4} else {0})
              | _ => \c.{0} ) ;
      initial := {1};
      final := {2} |>
End

Theorem example_dfa_wellformed:
  is_dfa example_dfa
Proof
  EVAL_TAC >> rpt (rw[])
QED


(*---------------------------------------------------------------------------*)
(* NFA acceptance                                                            *)
(*---------------------------------------------------------------------------*)

Definition nfa_lang_def:
  nfa_lang N =
   {w | w ∈ KSTAR {[a] | a ∈ N.Sigma} ∧
        ∃qs. LENGTH qs = LENGTH w + 1 ∧
             HD qs ∈ N.initial ∧
             LAST qs ∈ N.final ∧
         (∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w))}
End

Theorem in_nfa_lang:
 w ∈ nfa_lang N
  <=>
 w ∈ KSTAR {[a] | a ∈ N.Sigma} ∧
 ∃qs. LENGTH qs = LENGTH w + 1 ∧
          HD qs ∈ N.initial ∧
        LAST qs ∈ N.final ∧
       (∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w))
Proof
 rw [nfa_lang_def]
QED

(*---------------------------------------------------------------------------*)
(* The NFA- and DFA-recognizable languages.                                  *)
(*---------------------------------------------------------------------------*)

Definition NFA_LANGS_def:
  NFA_LANGS = {nfa_lang N | wf_nfa N}
End

Definition DFA_LANGS_def:
  DFA_LANGS = {nfa_lang N | is_dfa N}
End

Triviality IN_NFA_LANGS:
  L ∈ NFA_LANGS <=> ∃N. wf_nfa N ∧ L = nfa_lang N
Proof
  rw[EXTENSION,NFA_LANGS_def] >> metis_tac[]
QED

Triviality IN_DFA_LANGS:
  L ∈ DFA_LANGS <=> ∃N. is_dfa N ∧ L = nfa_lang N
Proof
  rw[EXTENSION,DFA_LANGS_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Encode/decode of (finite) state sets, to avoid HOL type constructions     *)
(* mirroring automata constructions. This leaves states as numbers, notably  *)
(* after the subset construction.                                            *)
(*---------------------------------------------------------------------------*)

val _ = temp_overload_on ("enc", “λs. nlist_of (SET_TO_LIST s)”);
val _ = temp_overload_on ("dec", “λn. set (listOfN n)”);

Theorem dec_enc_iden[simp]:
  ∀s. FINITE s ⇒ dec (enc s) = s
Proof
  rw[listOfN_nlist,SET_TO_LIST_INV]
QED

Theorem MEM_listOfN_enc[simp]:
  FINITE s ⇒ (MEM x (listOfN (enc s)) ⇔ x ∈ s)
Proof
  simp[listOfN_nlist]
QED

Theorem enc_11[simp]:
  FINITE s1 ∧ FINITE s2 ⇒ ((enc s1 = enc s2) ⇔ (s1 = s2))
Proof
  simp[]
QED

(*---------------------------------------------------------------------------*)
(* Basics for NFAs and DFAs. It's often neater to base the proofs on the     *)
(* notion of an execution, a generalization of the notion of *accepting      *)
(* execution* used to characterize NFA languages.                            *)
(*---------------------------------------------------------------------------*)

Definition is_exec_def :
 is_exec N qs w ⇔
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH qs = LENGTH w + 1 ∧
   HD qs ∈ N.Q ∧
   (∀n. n < LENGTH w ⇒ EL (n+1) qs ∈ N.delta (EL n qs) (EL n w))
End

Definition is_accepting_exec_def :
 is_accepting_exec N qs w
  ⇔
 is_exec N qs w ∧ HD qs ∈ N.initial ∧ LAST qs ∈ N.final
End

Theorem in_nfa_lang_is_exec:
  wf_nfa N ∧ w ∈ nfa_lang N ⇒ ∃qs. is_exec N qs w
Proof
 rw [is_exec_def,in_nfa_lang,wf_nfa_def] >> metis_tac [SUBSET_DEF]
QED

Theorem in_nfa_lang_is_accepting_exec:
  wf_nfa N ∧ w ∈ nfa_lang N
  ⇒
  ∃qs. is_accepting_exec N qs w ∧ ~NULL qs
Proof
  rw [is_accepting_exec_def,is_exec_def,in_nfa_lang,wf_nfa_def] >>
  ‘~NULL qs’ by (Cases_on ‘qs’ >> fs[]) >>
  metis_tac [SUBSET_DEF]
QED

Theorem in_nfa_lang_iff_accepting_exec:
  wf_nfa N ⇒
  (w ∈ nfa_lang N ⇔ ∃qs. is_accepting_exec N qs w)
Proof
  rw [is_accepting_exec_def,is_exec_def,in_nfa_lang,wf_nfa_def,EQ_IMP_THM] >>
  metis_tac [SUBSET_DEF]
QED

Theorem epsilon_in_nfa_lang:
  wf_nfa N ⇒ (ε ∈ nfa_lang N ⇔ N.initial ∩ N.final ≠ ∅)
Proof
  rw [wf_nfa_def, in_nfa_lang, LENGTH_EQ_NUM_compute, EQ_IMP_THM] >>
  fs [EXTENSION,IN_INTER,PULL_EXISTS] >> metis_tac []
QED

Theorem is_exec_length:
  is_exec N qs w ⇒ LENGTH qs = LENGTH w + 1
Proof
 rw [is_exec_def]
QED

Theorem is_exec_Sigma:
  is_exec N qs w ⇒ EVERY (λa. a ∈ N.Sigma) w
Proof
 rw [is_exec_def]
QED

Theorem is_exec_hd_state:
  is_exec N qs w ⇒ HD qs ∈ N.Q
Proof
 rw [is_exec_def]
QED

Theorem is_exec_delta:
  is_exec N qs w ∧ n < LENGTH w ⇒ EL (n+1) qs ∈ N.delta (EL n qs) (EL n w)
Proof
 rw [is_exec_def]
QED

Theorem is_exec_nonempty:
  is_exec N qs w ⇒ qs ≠ []
Proof
 rw [is_exec_def] >> Cases_on ‘qs’ >> fs[]
QED

Theorem is_exec_tl_nonempty:
  w ≠ ε ∧ is_exec N qs w ⇒ TL qs ≠ []
Proof
 rw [is_exec_def] >>
 Cases_on ‘qs’ >> fs[GSYM ADD1] >>
 Cases_on ‘t’ >> fs[]
QED

Theorem is_exec_states:
  wf_nfa N ∧ is_exec N qs w ⇒ EVERY (λq. q ∈ N.Q) qs
Proof
  rw [is_exec_def,EVERY_EL] >> Induct_on ‘n’ >> rw[] >> fs[] >>
  ‘n < LENGTH w’ by decide_tac >> last_x_assum drule >>
  metis_tac [ADD1, wf_nfa_def,SUBSET_DEF]
QED

Theorem is_exec_TL:
  wf_nfa N ∧ is_exec N qs w ∧ w ≠ ε ⇒ is_exec N (TL qs) (TL w)
Proof
  rw [is_exec_def]
  >- (Cases_on ‘w’ >> fs [])
  >- (Cases_on ‘qs’ >> Cases_on ‘w’ >> fs[])
  >- (Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> fs[GSYM ADD1] >>
      ‘0 < LENGTH w’ by decide_tac >> first_x_assum drule >> rw[] >>
      Cases_on ‘w’ >> fs[] >> metis_tac [wf_nfa_def,SUBSET_DEF])
  >- (‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >> rw [] >>
      ‘0 < LENGTH w’ by (Cases_on ‘w’ >> fs[]) >> fs [LENGTH_TL] >>
      ‘n+1 < LENGTH w’ by decide_tac >> rw[] >> first_x_assum drule >> rw[])
QED

Theorem is_exec_TL_alt:
  wf_nfa N ∧ is_exec N (q::qs) (a::w) ⇒ is_exec N qs w
Proof
  rpt strip_tac >> drule is_exec_TL >> rw[] >> res_tac >> fs[]
QED

Triviality is_exec_drop_right:
  wf_nfa N ∧ is_exec N (qs ++ [q]) (w ++ [a]) ⇒ is_exec N qs w
Proof
  rpt strip_tac >> rw [is_exec_def]
  >- (drule is_exec_Sigma >> rw[])
  >- (drule is_exec_length >> rw[])
  >- (drule is_exec_length >> Cases_on ‘qs’ >> rw[] >>
      drule_all is_exec_states >> rw[])
  >- (‘n < LENGTH (w ++ [a])’ by
        (drule is_exec_length >> rw[]) >>
      drule_all is_exec_delta >>
      ‘n < LENGTH qs ∧ n+1 < LENGTH qs’ by
        (drule is_exec_length >> rw[]) >>
      simp[EL_APPEND1])
QED

Triviality is_exec_extend_right:
  wf_nfa N ∧ is_exec N qs w ∧
  a ∈ N.Sigma ∧ q ∈ N.delta (LAST qs) a
    ⇒
  is_exec N (qs ++ [q]) (w ++ [a])
Proof
 rpt strip_tac >> imp_res_tac is_exec_nonempty >>
 rw [is_exec_def]
 >- metis_tac [is_exec_Sigma]
 >- (drule is_exec_length >> decide_tac)
 >- (drule_all is_exec_states >> Cases_on ‘qs’ >> rw[])
 >- (‘n < LENGTH qs’ by
       (drule is_exec_length >> rw[]) >>
     ‘n < LENGTH w ∨ n = LENGTH w’ by
       decide_tac
     >- (‘n+1 < LENGTH qs’ by
          (drule is_exec_length >> rw[]) >>
         rw [EL_APPEND1] >> metis_tac [is_exec_delta])
     >- (‘n+1 = LENGTH qs’ by
          (drule is_exec_length >> rw[]) >>
         rw[el_last] >> rw[EL_APPEND] >> rw[EL_LENGTH_LAST]))
QED

Theorem is_exec_delta_step:
  wf_nfa N
  ⇒
  (is_exec N qs w ∧ a ∈ N.Sigma ∧ q ∈ N.delta (LAST qs) a
   ⇔
  is_exec N (qs ++ [q]) (w ++ [a]))
Proof
  rpt (strip_tac ORELSE eq_tac)
  >- metis_tac [is_exec_extend_right]
  >- metis_tac [is_exec_drop_right]
  >- gvs [is_exec_def]
  >- (imp_res_tac is_exec_drop_right >>
      ‘∃q qs'. qs = SNOC q qs'’ by
         metis_tac [is_exec_nonempty,SNOC_CASES] >>
      gvs[SNOC_APPEND] >> pop_forget_tac >>
      gvs [is_exec_def] >>
      ‘LENGTH w < LENGTH w + 1’ by decide_tac >>
      first_x_assum drule >> simp[] >>
      qpat_x_assum ‘_ = _’ sym_subst_all_tac >>
      simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND] >>
      simp_tac bool_ss [EL_LENGTH_APPEND_0,EL_LENGTH_APPEND_1])
QED

(*
Theorem is_exec_append:
  wf_nfa N ∧ w2 ≠ ε ∧
  is_exec N qs1 w1 ∧ is_exec N qs2 w2 ∧
  HD qs2 ∈ N.delta (LAST qs1) (HD w2)
    ⇒
  is_exec N (qs1 ++ qs1) (w1 ++ w2)
Proof
 cheat
QED
*)

Theorem is_exec_extend_left:
  wf_nfa N ∧
  a ∈ N.Sigma ∧
  q1 ∈ N.Q ∧
  q2 ∈ N.delta q1 a ∧
  is_exec N (q2::qs) w ⇒ is_exec N (q1::q2::qs) (a::w)
Proof
  rw [is_exec_def] >> Cases_on ‘n’ >> gvs[GSYM ADD1]
QED

Theorem is_exec_step_left:
  wf_nfa N ∧ is_exec N (q1::q2::qs) (a::w) ⇒ q2 ∈ N.delta q1 a ∧ is_exec N (q2::qs) w
Proof
  rw[is_exec_def,wf_nfa_def]
  >- (‘0 < SUC(LENGTH w)’ by decide_tac >> first_x_assum drule >> rw[])
  >- (‘0 < SUC(LENGTH w)’ by decide_tac >> first_x_assum drule >>
      gvs[SUBSET_DEF] >> metis_tac[])
  >- (‘SUC n < SUC(LENGTH w)’ by decide_tac >>
      first_x_assum drule >> rw[GSYM ADD1])
QED

Theorem is_exec_epsilon:
 is_exec N qs ε ⇔ (∃q. q ∈ N.Q ∧ qs = [q])
Proof
 rw[is_exec_def,EQ_IMP_THM] >> simp[] >>
 first_x_assum (irule_at Any) >>
 Cases_on ‘qs’ >> gvs[]
QED

Theorem is_accepting_exec_length:
 wf_nfa N ∧ w ≠ ε ∧ is_accepting_exec N qs w
 ⇒
 TL qs ≠ []
Proof
 rw[is_accepting_exec_def,is_exec_def] >>
 ‘0 < LENGTH w’ by metis_tac[NOT_NIL_EQ_LENGTH_NOT_0] >>
 Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> fs[]
QED

Theorem is_accepting_exec_final:
 is_accepting_exec N qs w ⇒ LAST qs ∈ N.final
Proof
 rw[is_accepting_exec_def]
QED

Theorem accepting_exec_states_not_nil:
  is_accepting_exec M qs w ⇒ qs ≠ []
Proof
  rw [is_accepting_exec_def] >>
  drule is_exec_length >>
  rpt strip_tac >> gvs[]
QED

Theorem accepting_exec_min_lengths:
  wf_nfa M ∧
  ε ∉ nfa_lang M ∧
  is_accepting_exec M qs w
  ⇒
  qs ≠ [] ∧ (∀x. qs ≠ [x]) ∧ w ≠ ε
Proof
 rw [is_accepting_exec_def] >> strip_tac >>
 rw[] >> rfs[epsilon_in_nfa_lang,EXTENSION]
  >- metis_tac [is_exec_nonempty]
  >- metis_tac[]
  >- (gvs [is_exec_def] >> Cases_on ‘qs’ >> gvs[] >> metis_tac[])
QED

Theorem epsilon_free_exec_left_cons:
  w ≠ ε ∧ is_exec M qs w
  ⇒
  ∃q1 q2 qs' a w'. qs = q1::q2::qs' ∧ w = a::w'
Proof
  rw [is_exec_def] >>
  Cases_on ‘w’ >>
  Cases_on ‘qs’ >> gvs[] >>
  Cases_on ‘t'’ >> gvs[]
QED

Theorem nfa_execution_states_closed:
  wf_nfa N ⇒
  ∀w Q.
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH Q = LENGTH w + 1 ∧
   HD Q ∈ N.Q ∧
   (∀n. n < LENGTH w ⇒ EL (n+1) Q ∈ N.delta (EL n Q) (EL n w))
   ==>
   EVERY (λq. q ∈ N.Q) Q
Proof
  rpt strip_tac >> irule is_exec_states >> rw[is_exec_def] >> metis_tac[]
QED

Theorem nfa_execution_last_state:
  wf_nfa N ⇒
  ∀w Q.
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH Q = LENGTH w + 1 ∧
   HD Q ∈ N.initial ∧
   (∀n. n < LENGTH w ⇒ EL (n+1) Q ∈ N.delta (EL n Q) (EL n w))
   ==>
   EL (LENGTH w) Q ∈ N.Q
Proof
  rpt strip_tac >>
  ‘Q ≠ []’ by (Cases_on ‘Q’ >> fs[]) >>
  ‘HD Q ∈ N.Q’ by metis_tac [wf_nfa_def,SUBSET_DEF] >>
  drule_all nfa_execution_states_closed >> strip_tac >>
  drule_all EVERY_LAST >> simp[EL_LENGTH_LAST]
QED

(*---------------------------------------------------------------------------*)
(* DFA execution on valid words.                                             *)
(*---------------------------------------------------------------------------*)

Theorem dfa_execution:
  is_dfa N ⇒
  ∀w.
    EVERY (λa. a ∈ N.Sigma) w
     ⇒
    ∃qs. LENGTH qs = LENGTH w + 1 ∧ {HD qs} = N.initial ∧
         EVERY (λq. q ∈ N.Q) qs ∧
         (∀n. n<LENGTH w ⇒ {EL (n+1) qs} = N.delta (EL n qs) (EL n w))
Proof
  disch_tac >> ho_match_mp_tac SNOC_INDUCT >> rw[EVERY_SNOC]
  >- gvs [LENGTH_EQ_NUM_compute,is_dfa_def,PULL_EXISTS,wf_nfa_def]
  >- (first_x_assum drule >> rw[] >> rename1 ‘a ∈ N.Sigma’ >>
      ‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >>
      ‘LAST qs ∈ N.Q’ by
        (‘EL (LENGTH w) qs ∈ N.Q’ by
           (irule nfa_execution_last_state >> fs [is_dfa_def] >> rw[]
            >- metis_tac[EXTENSION,IN_INSERT]
            >- rfs[]) >> metis_tac [EL_LENGTH_LAST]) >>
      fs [is_dfa_def, wf_nfa_def] >>
      ‘∃q. {q} = N.delta (LAST qs) a’ by metis_tac[] >>
      ‘q ∈ N.Q’ by metis_tac [SUBSET_DEF,EXTENSION,IN_INSERT] >>
      qexists_tac ‘SNOC q qs’ >> rw[EVERY_SNOC]
      >- rfs[]
      >- (‘n < LENGTH w ∨ n = LENGTH w’ by decide_tac
          >- rw [EL_SNOC]
          >- (rw [EL_SNOC, EL_LENGTH_LAST] >>
              qpat_x_assum ‘LENGTH qs = LENGTH w + 1’ (SUBST_ALL_TAC o GSYM) >>
              rw [EL_LENGTH_SNOC]))
     )
QED

Theorem dfa_execution_deterministic:
  is_dfa N ⇒
  ∀w Q1 Q2.
    EVERY (λa. a ∈ N.Sigma) w ∧
    LENGTH Q1 = LENGTH w + 1 ∧
    HD Q1 ∈ N.initial ∧
    (∀n. n<LENGTH w ⇒ EL (n+1) Q1 ∈ N.delta (EL n Q1) (EL n w))
    ∧
    LENGTH Q2 = LENGTH w + 1 ∧
    HD Q2 ∈ N.initial ∧
    (∀n. n<LENGTH w ⇒ EL (n+1) Q2 ∈ N.delta (EL n Q2) (EL n w))
  ⇒
  Q1 = Q2
Proof
  disch_tac >> ho_match_mp_tac SNOC_INDUCT >> rw[]
  >- gvs [LENGTH_EQ_NUM_compute,is_dfa_def]
  >- (rename1 ‘SNOC a w’ >> fs [EVERY_SNOC] >>
      ‘LENGTH Q1 = LENGTH w + 2 ∧ LENGTH Q2 = LENGTH w + 2’ by decide_tac >>
      ‘∃qs1 q1. Q1 = SNOC q1 qs1 ∧ qs1 ≠ []’ by metis_tac[snoc2] >>
      ‘∃qs2 q2. Q2 = SNOC q2 qs2 ∧ qs2 ≠ []’ by metis_tac[snoc2] >> fs[] >>
      irule (METIS_PROVE [] “(b' ⇒ a=a') ∧ (a' ⇒ b=b') ∧ a' ∧ b' ⇒ a ∧ b”) >>
      qexists_tac ‘qs1 = qs2’ >> qexists_tac ‘T’ >> simp[] >> conj_tac
      >- (first_x_assum irule >> rw[LENGTH_FRONT] >> fs[GSYM SNOC_APPEND]
          >- (‘EL (n+1) (SNOC q1 qs1) ∈
               N.delta (EL n (SNOC q1 qs1)) (EL n (SNOC a w))’ by rw[] >>
               rpt (forget_tac is_forall) >> pop_assum mp_tac >> simp [EL_SNOC])
          >- (‘EL (n+1) (SNOC q2 qs2) ∈
               N.delta (EL n (SNOC q2 qs2)) (EL n (SNOC a w))’ by rw[] >>
               rpt(forget_tac is_forall) >> pop_assum mp_tac >> simp[EL_SNOC]))
      >- (rw[] >> forget_tac is_neg >> forget_tac is_eq >>
          fs [GSYM SNOC_APPEND] >> ‘LENGTH w < SUC (LENGTH w)’ by decide_tac >>
          first_x_assum drule >> fs [Once BOUNDED_FORALL_THM] >>
          ‘LENGTH w + 1 = LENGTH qs1’ by decide_tac >>
          gvs[EL_LENGTH_SNOC,EL_SNOC] >>
          ‘EL (LENGTH w) qs1 ∈ N.Q’ by
            (irule nfa_execution_last_state >> rw[] >> fs [is_dfa_def]) >>
          fs [is_dfa_def] >>
          ‘∃qf. N.delta (EL (LENGTH w) qs1) a = {qf}’ by metis_tac[] >> gvs[])
     )
QED

(*---------------------------------------------------------------------------*)
(* Subset construction                                                       *)
(*---------------------------------------------------------------------------*)

Definition nfa_to_dfa_def:
  nfa_to_dfa N =
    <|Q       := {enc s | s ⊆ N.Q};
      Sigma   := N.Sigma;
      delta   := λq a. {enc (BIGUNION {N.delta qi a | qi ∈ dec q})};
      initial := {enc N.initial};
      final   := {enc s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅} |>
End

Triviality nfa_to_dfa_builtin_simps[simp]:
  (nfa_to_dfa N).Sigma = N.Sigma ∧
  (nfa_to_dfa N).initial = {enc N.initial} ∧
  (nfa_to_dfa N).final   = {enc s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅} ∧
  (∀q. q ∈ (nfa_to_dfa N).Q <=> ∃s. q = enc s ∧ s ⊆ N.Q)
Proof
  rw[nfa_to_dfa_def]
QED

(*---------------------------------------------------------------------------*)
(* Well-formedness of subset DFA                                             *)
(*---------------------------------------------------------------------------*)

Theorem is_dfa_nfa_to_dfa:
  wf_nfa N ⇒ is_dfa (nfa_to_dfa N)
Proof
  fs[wf_nfa_def,is_dfa_def,nfa_to_dfa_def] >> rw[]
  >- (rw [GSPEC_IMAGE, o_DEF] >> irule IMAGE_FINITE >>
      last_x_assum (mp_tac o MATCH_MP FINITE_POW) >>
      PURE_REWRITE_TAC[GSYM IN_POW,SPECIFICATION,ETA_THM] >> metis_tac[])
  >- metis_tac []
  >- (rw [SUBSET_DEF] >> metis_tac[])
  >- (irule_at Any EQ_REFL >> rw[BIGUNION_SUBSET] >>
      ‘FINITE s’ by metis_tac [SUBSET_FINITE] >>
      gvs[MEM_SET_TO_LIST] >> metis_tac [SUBSET_DEF])
QED

(*---------------------------------------------------------------------------*)
(* This seems very close to nfa_states_closed above.                         *)
(*---------------------------------------------------------------------------*)

Theorem dfa_states_closed:
  wf_nfa N ⇒
  ∀w eqs.
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH eqs = LENGTH w + 1 ∧
   HD eqs = enc N.initial ∧
   (∀n. n<LENGTH w ⇒ EL (n+1) eqs ∈ (nfa_to_dfa N).delta (EL n eqs) (EL n w))
   ==>
   EVERY (λeq. eq ∈ (nfa_to_dfa N).Q) eqs
Proof
  disch_tac >>
  ho_match_mp_tac SNOC_INDUCT >> simp[LENGTH_EQ_NUM_compute] >> rw[]
  >- (fs[wf_nfa_def] >> metis_tac[])
  >- (rename [‘SNOC a w’,‘HD (eqs ++ [eq]) = enc N.initial’] >>
      ‘eqs ≠ []’ by (Cases_on ‘eqs’ >> gvs[]) >>
      ‘EVERY (λeq. ∃s. eq = enc s ∧ s ⊆ N.Q) eqs’ by
         (first_x_assum irule >> rw[] >> fs [EVERY_SNOC]
          >- (fs [Once BOUNDED_FORALL_THM] >> first_x_assum drule >>
              full_simp_tac std_ss [GSYM SNOC_APPEND] >> simp[EL_SNOC])
          >- (rw[PULL_EXISTS] >>  qexistsl_tac [‘FRONT eqs’, ‘LAST eqs’] >>
              rw [LENGTH_FRONT,APPEND_FRONT_LAST])) >>
      drule_all EVERY_LAST >> rw[] >> fs [Once BOUNDED_FORALL_THM] >>
      rpt (forget_tac is_forall) >> qpat_x_assum ‘_ ∈ _’ mp_tac >>
      fs[EVERY_SNOC,EL_LENGTH_SNOC] >>
      ‘LENGTH w + 1 = LENGTH eqs’ by decide_tac >> pop_subst_tac >>
      simp_tac std_ss [GSYM SNOC_APPEND] >> simp [EL_LENGTH_SNOC,EL_SNOC] >>
      ‘EL (LENGTH w) eqs = LAST eqs’ by
         (‘LENGTH w = PRE (LENGTH eqs)’ by decide_tac >>
          pop_assum SUBST1_TAC >> rw [Once EL_PRE_LENGTH]) >> pop_subst_tac >>
      ‘FINITE s’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
      rw [nfa_to_dfa_def] >> irule_at Any EQ_REFL >>
      rw[BIGUNION_SUBSET,SUBSET_DEF] >> metis_tac[wf_nfa_def,SUBSET_DEF])
QED


Theorem nfa_to_dfa_execution_states:
  wf_nfa N ⇒
  ∀w eqs.
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH eqs = LENGTH w + 1 ∧
   HD eqs = enc N.initial ∧
   (∀n. n<LENGTH w ⇒ EL (n+1) eqs ∈ (nfa_to_dfa N).delta (EL n eqs) (EL n w))
   ==>
   (LAST eqs) ∈ (nfa_to_dfa N).Q
Proof
  rw [] >>
  ‘eqs ≠ []’ by (Cases_on ‘eqs’ >> gvs[]) >>
  drule_all dfa_states_closed >> disch_tac >>
  drule_all EVERY_LAST >> rw [nfa_to_dfa_def]
QED

(*---------------------------------------------------------------------------*)
(* Main lemma for the subset construction. The last state in an execution of *)
(* the DFA on input w, when decoded, is equal to the set of states reachable *)
(* by NFA execution on w.                                                    *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_inductive:
  wf_nfa N ⇒
  ∀w eqs.
   EVERY (λa. a ∈ N.Sigma) w ∧
   LENGTH eqs = LENGTH w + 1 ∧
   HD eqs = enc N.initial ∧
   (∀n. n<LENGTH w ⇒ EL (n+1) eqs ∈ (nfa_to_dfa N).delta (EL n eqs) (EL n w))
   ==>
   dec(LAST eqs) =
   {LAST qs |qs| LENGTH qs = LENGTH w + 1 ∧ HD qs ∈ N.initial ∧
                 ∀n. n<LENGTH w ⇒ EL (n+1) qs ∈ N.delta (EL n qs) (EL n w)}
Proof
 disch_tac >> ho_match_mp_tac SNOC_INDUCT >> rpt strip_tac
 >- (‘FINITE N.initial’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
     gvs [LENGTH_EQ_NUM_compute,EXTENSION,MEM_SET_TO_LIST] >>
     rw[EQ_IMP_THM,PULL_EXISTS])
 >- (rename1 ‘SNOC a w’ >>
     fs [EVERY_SNOC,PULL_EXISTS,DECIDE ``SUC x + 1 = x + 2``] >>
     (* IH *)
     ‘∃eqs' eq. eqs = SNOC eq eqs' ∧ eqs' ≠ []’ by metis_tac[snoc2] >> rw[] >>
     ‘dec (LAST eqs') =
       {LAST qs |
         LENGTH qs = LENGTH w + 1 ∧ HD qs ∈ N.initial ∧
         ∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w)}’
        by (first_x_assum irule >> rw[] >> fs[] >>
            fs [Once BOUNDED_FORALL_THM] >> first_x_assum drule >>
            full_simp_tac std_ss [GSYM SNOC_APPEND] >> simp[EL_SNOC]) >>
     qpat_forget_tac ‘$∀ (M:num list->bool)’ >> rw[] >> fs[] >>
     (* LAST eqs' encodes a set of states s *)
     ‘∃s. LAST eqs' = enc s ∧ s ⊆ N.Q’ by
       (‘(LAST eqs') ∈ (nfa_to_dfa N).Q’
          by (irule nfa_to_dfa_execution_states >> fs[BOUNDED_FORALL_THM] >>
             qexists_tac‘w’ >> rw[] >> first_x_assum drule >> fs [EL_SNOC]) >>
        pop_assum mp_tac >> simp [nfa_to_dfa_def]) >>
     ‘FINITE s’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
     fs [SET_TO_LIST_INV] >>
     (* enc s --> {eq} step *)
     ‘eq ∈ (nfa_to_dfa N).delta (enc s) a’
        by (irule (METIS_PROVE []
            “A=A' ∧ B=B' ∧ C=C' ∧ A' ∈ (nfa_to_dfa N).delta B' C' ⇒
             A ∈ (nfa_to_dfa N).delta B C”) >>
            first_x_assum (irule_at Any) >> qexists_tac ‘LENGTH w’ >>
            simp[GSYM SNOC_APPEND,EL_LENGTH_SNOC] >>
            ‘LENGTH w + 1 = LENGTH eqs' ∧ LENGTH w = PRE (LENGTH eqs')’
              by decide_tac >> fs[Once EL_PRE_LENGTH,EL_SNOC,EL_LENGTH_SNOC]) >>
     qpat_x_assum ‘_ ∈ _’ (mp_tac o GSYM o SRULE [nfa_to_dfa_def]) >>
     drule_then (rewrite_tac o single) MEM_SET_TO_LIST >>
     disch_then (SUBST1_TAC o SYM) >>
     ‘FINITE (BIGUNION {N.delta qi a | qi ∈ s})’
        by metis_tac[finite_nfa_successors] >> simp[] >>
     ntac 2 pop_forget_tac >> qpat_forget_tac ‘s = GSPEC _’ >>
     (* Now show equality between the two fringe state sets *)
     rw [EXTENSION] >> eq_tac >> rpt strip_tac >> fs[] >> rw[PULL_EXISTS] >>
     ‘qs ≠ []’ by (Cases_on ‘qs’ >> gvs[])
     >- (qexists_tac ‘SNOC x qs’ >> rw[EL_SNOC] >>
         ‘n < LENGTH w ∨ n=LENGTH w’ by decide_tac
         >- rw [EL_SNOC]
         >- (rw[EL_LENGTH_SNOC] >>
             ‘LENGTH w + 1 = LENGTH qs /\ LENGTH w = PRE (LENGTH qs)’ by decide_tac >>
             pop_subst_tac >>
             fs[Once EL_PRE_LENGTH,EL_SNOC,EL_LENGTH_SNOC]))
     >- (qexistsl_tac [‘N.delta (EL (LENGTH w) qs) a’, ‘FRONT qs’] >> rw[]
         >- (‘LENGTH w < SUC(LENGTH w)’ by decide_tac >> first_x_assum drule >>
             ‘LAST qs = EL (LENGTH w + 1) qs’
               by (drule_then (SUBST_ALL_TAC o GSYM) EL_PRE_LENGTH >>
                   AP_THM_TAC >> AP_TERM_TAC >> rw[]) >> simp [EL_LENGTH_SNOC])
         >- (AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
             fs [LENGTH_EQ_NUM_compute] >>
             qpat_x_assum ‘LENGTH l1 = LENGTH w’ (subst_all_tac o GSYM) >>
             fs [EL_LENGTH_APPEND,FRONT_APPEND])
         >- fs [LENGTH_FRONT]
         >- (‘n+1 < LENGTH (FRONT qs)’
               by (‘0 < n+2 ∧ n+2 < LENGTH qs’ by decide_tac >>
                   drule_all LESS_FRONT_LENGTH >> decide_tac) >>
             rw [EL_FRONT |> SRULE [NULL_EQ]] >>
             ‘n < SUC(LENGTH w)’ by decide_tac >>
             first_x_assum drule >> rw[EL_SNOC]))
    )
QED

Theorem nfa_path_to_dfa_path:
  wf_nfa N ⇒
  ∀w qs. EVERY (λa. a ∈ N.Sigma) w ∧
         LENGTH qs = LENGTH w + 1 ∧ HD qs ∈ N.initial ∧
         (∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w))
       ==>
      ∃eqs.
        LENGTH eqs = LENGTH w + 1 ∧ HD eqs = enc N.initial ∧
        (∀n. n < LENGTH w ⇒
             EL (n + 1) eqs ∈ (nfa_to_dfa N).delta (EL n eqs) (EL n w))
Proof
  disch_tac >>
  ho_match_mp_tac SNOC_INDUCT >>
  rw[PULL_EXISTS,LENGTH_EQ_NUM_compute,EVERY_SNOC] >>
  rename [‘a ∈ N.Sigma’, ‘HD (qs ⧺ [q])’] >>
  ‘qs ≠ []’ by (Cases_on ‘qs’ >> gvs[]) >>
  ‘LENGTH (FRONT qs) = LENGTH w’ by rw[LENGTH_FRONT] >> gvs[] >>
  first_x_assum drule >> disch_then (mp_tac o Q.ISPEC‘LAST qs:num’) >>
  fs [GSYM SNOC_APPEND,SNOC_LAST_FRONT] >>
  fs [Once BOUNDED_FORALL_THM] >>
  ‘LENGTH w + 1 = LENGTH qs’ by decide_tac >> pop_subst_tac >>
  fs [EL_LENGTH_SNOC] >>
  ‘LENGTH w < LENGTH qs’ by decide_tac >> fs [EL_SNOC] >> rw[] >>
  rename1 ‘HD (SNOC eq eqs) = enc N.initial’ >>
  qpat_x_assum ‘LENGTH eqs = LENGTH w’ (assume_tac o GSYM) >> fs[EL_SNOC] >>
  qexists_tac ‘SNOC eq eqs’ >>
  rw[EL_LENGTH_SNOC,
     EL_LENGTH_SNOC |> Q.ISPEC ‘SNOC eq eqs: num list’
                    |> SIMP_RULE std_ss [LENGTH_SNOC],EL_SNOC] >>
  rw [nfa_to_dfa_def]
QED

(*---------------------------------------------------------------------------*)
(* Language of the constructed DFA is the same as that of the original NFA.  *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_correct:
  wf_nfa N ⇒ ∀w. w ∈ nfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
 rw [in_nfa_lang] >> eq_tac >> strip_tac >> rw[]
 >- (rename1 ‘LAST eqs = enc s’ >> drule_all nfa_to_dfa_inductive >> rw[] >>
     ‘FINITE s’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
     qpat_x_assum ‘set (SET_TO_LIST _) = _’ mp_tac >> simp [SET_TO_LIST_INV] >>
     ‘∃qa. qa ∈ s ∧ qa ∈ N.final’ by (fs[EXTENSION] >> metis_tac[]) >>
     rw[EXTENSION] >> metis_tac[])
 >- (drule_all nfa_path_to_dfa_path >> rw[] >> qexists_tac ‘eqs’ >> rw[] >>
     drule_all dfa_states_closed >> disch_tac >>
     drule_all nfa_to_dfa_inductive >>
     ‘eqs ≠ []’ by (Cases_on ‘eqs’ >> gvs[]) >>
     ‘eqs = SNOC (LAST eqs) (FRONT eqs)’ by metis_tac [SNOC_LAST_FRONT] >>
     pop_subst_tac >> fs [EVERY_SNOC,PULL_EXISTS] >>
     ‘FINITE s’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
     disch_then (fn th => irule_at Any EQ_REFL >> rw[] >> mp_tac th) >>
     rw [SET_TO_LIST_INV,EXTENSION,PULL_EXISTS] >> metis_tac[])
QED

Theorem NFA_LANGS_EQ_DFA_LANGS:
  NFA_LANGS = DFA_LANGS
Proof
  rw [EXTENSION,IN_NFA_LANGS,IN_DFA_LANGS,EQ_IMP_THM]
  >- metis_tac [is_dfa_nfa_to_dfa,nfa_to_dfa_correct]
  >- metis_tac[is_dfa_def]
QED

(*===========================================================================*)
(* Machine constructions and closure properties                              *)
(*===========================================================================*)

Definition nfa_compl_def:
  nfa_compl N =
    <|Q     := N.Q;
      Sigma := N.Sigma;
      delta := N.delta;
      initial := N.initial;
      final   := (N.Q DIFF N.final)
    |>
End

Definition nfa_inter_def:
  nfa_inter N1 N2 =
    <|Q  := {q1 ⊗ q2 | q1 ∈ N1.Q ∧ q2 ∈ N2.Q};
      Sigma := N1.Sigma ∩ N2.Sigma;
      delta := λq a. {q1 ⊗ q2 | q1 ∈ N1.delta (nfst q) a ∧ q2 ∈ N2.delta (nsnd q) a};
      initial := {q1 ⊗ q2 | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      final   := {q1 ⊗ r2 | q1 ∈ N1.final ∧ r2 ∈ N2.final}
    |>
End

Definition nfa_union_def:
  nfa_union N1 N2 =
    <|Q  := {q1 ⊗ q2 | q1 ∈ N1.Q ∧ q2 ∈ N2.Q };
      Sigma := N1.Sigma ∩ N2.Sigma;
      delta := λq a. {q1 ⊗ q2 | q1 ∈ N1.delta (nfst q) a ∧ q2 ∈ N2.delta (nsnd q) a};
      initial := {q1 ⊗ q2 | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      final   := {q1 ⊗ q2 | (q1 ∈ N1.final ∧ q2 ∈ N2.Q) ∨
                            (q1 ∈ N1.Q ∧ q2 ∈ N2.final)};
    |>
End

Definition nfa_dot_def:
  nfa_dot N1 N2 =
    <|Q  := N1.Q ∪ N2.Q; (* N1.Q and N2.Q are disjoint *)
      Sigma := N1.Sigma ∩ N2.Sigma;
      delta := λq a.
        if q ∈ N1.Q then
          (if q ∉ N1.final then N1.delta q a
           else N1.delta q a ∪
                BIGUNION {N2.delta q' a |q'| q' ∈ N2.initial})
        else N2.delta q a;
      initial := N1.initial;
      final   := N2.final;
    |>
End

Definition nfa_plus_def:
  nfa_plus N =
   <|Q := N.Q;
     Sigma := N.Sigma ;
     delta := λq a.
       if q ∉ N.final then
         N.delta q a
       else
         N.delta q a ∪
         BIGUNION {N.delta q' a |q'| q' ∈ N.initial};
     initial := N.initial ;
     final   := N.final;
   |>
End

(*---------------------------------------------------------------------------*)
(* Wellformedness of constructions                                           *)
(*---------------------------------------------------------------------------*)

Theorem wf_nfa_compl:
  wf_nfa N ⇒ wf_nfa (nfa_compl N)
Proof
  rw[wf_nfa_def, nfa_compl_def]
QED

Theorem wf_nfa_inter:
  wf_nfa N1 ∧ wf_nfa N2 ⇒ wf_nfa (nfa_inter N1 N2)
Proof
  rw [wf_nfa_def,nfa_inter_def,SUBSET_DEF]
  >- (rw [GSPEC_IMAGE, o_DEF,pairTheory.LAMBDA_PROD] >>
      irule IMAGE_FINITE >> irule SUBSET_FINITE >>
      qexists ‘N1.Q CROSS N2.Q’ >> rw[] >>
      rw [SUBSET_DEF,CROSS_DEF,pairTheory.LAMBDA_PROD,pairTheory.FORALL_PROD])
  >- metis_tac[]
  >- metis_tac[]
  >- (fs[] >> metis_tac[])
QED

Theorem wf_nfa_union:
  wf_nfa N1 ∧ wf_nfa N2 ⇒ wf_nfa (nfa_union N1 N2)
Proof
  rw [wf_nfa_def,nfa_union_def,SUBSET_DEF]
  >- (rw [GSPEC_IMAGE, o_DEF,pairTheory.LAMBDA_PROD] >>
      irule IMAGE_FINITE >> irule SUBSET_FINITE >>
      qexists ‘N1.Q CROSS N2.Q’ >> rw[] >>
      rw [SUBSET_DEF,CROSS_DEF,pairTheory.LAMBDA_PROD,pairTheory.FORALL_PROD])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (fs[] >> metis_tac[])
QED

Triviality nfa_dot_builtin_simps[simp]:
  (∀q. q ∈ (nfa_dot N1 N2).Q <=> q ∈ N1.Q ∨ q ∈ N2.Q) ∧
  (∀a. a ∈ (nfa_dot N1 N2).Sigma ⇔ a ∈ N1.Sigma ∧ a ∈ N2.Sigma) ∧
  (nfa_dot N1 N2).initial = N1.initial ∧
  (nfa_dot N1 N2).final = N2.final
Proof
  rw[nfa_dot_def]
QED

Triviality nfa_plus_builtin_simps[simp]:
  (nfa_plus N).Sigma = N.Sigma ∧
  (nfa_plus N).Q = N.Q ∧
  (nfa_plus N).initial = N.initial ∧
  (nfa_plus N).final = N.final
Proof
  rw[nfa_plus_def]
QED

Theorem wf_nfa_dot:
  wf_nfa N1 ∧ wf_nfa N2 ∧ N1.Q ∩ N2.Q = {} ==> wf_nfa (nfa_dot N1 N2)
Proof
  fs [wf_nfa_def, nfa_dot_def] >> rw[]
  >- metis_tac [SUBSET_UNION_RIGHT]
  >- metis_tac [SUBSET_UNION_RIGHT,UNION_COMM]
  >- (rw[]
       >- metis_tac [SUBSET_UNION_RIGHT,UNION_COMM]
       >- metis_tac [SUBSET_UNION_RIGHT,UNION_COMM]
       >- (simp [Once UNION_COMM] >> irule SUBSET_UNION_RIGHT >>
           rw [SUBSET_DEF] >> metis_tac [SUBSET_DEF]))
  >- (rw[] >> fs[EXTENSION] >> rw[]
       >- metis_tac [SUBSET_UNION_RIGHT,UNION_COMM]
       >- (gvs [SUBSET_DEF] >> metis_tac[])
       >- (gvs [SUBSET_DEF] >> metis_tac[])
       >- (simp [Once UNION_COMM] >> irule SUBSET_UNION_RIGHT >> metis_tac[]))
QED

Theorem wf_nfa_plus:
  wf_nfa N ==> wf_nfa (nfa_plus N)
Proof
  rw [wf_nfa_def, nfa_plus_def,SUBSET_DEF] >>
  pop_keep_tac >> rw[] >> metis_tac []
QED

Theorem is_dfa_compl:
  is_dfa N ⇒ is_dfa (nfa_compl N)
Proof
  rw [is_dfa_def]
  >- metis_tac [wf_nfa_compl]
  >- simp[nfa_compl_def]
  >- fs[nfa_compl_def]
QED

Theorem is_dfa_inter:
 is_dfa N1 ∧ is_dfa N2 ⇒ is_dfa (nfa_inter N1 N2)
Proof
 rw [is_dfa_def]
 >- metis_tac [wf_nfa_inter]
 >- (rw [nfa_inter_def,EXTENSION] >> metis_tac[])
 >- (ntac 2 pop_keep_tac >> rw [nfa_inter_def,EXTENSION,PULL_EXISTS] >>
     ‘∃qa qb. {qa} = N1.delta q1 a ∧
              {qb} = N2.delta q2 a’ by metis_tac[] >>
     qexists_tac ‘qa ⊗ qb’ >> rw[EQ_IMP_THM]
     >- (RULE_ASSUM_TAC GSYM >> rfs[])
     >- metis_tac [EXTENSION,IN_INSERT]
     >- metis_tac [EXTENSION,IN_INSERT])
QED

Theorem is_dfa_union:
 is_dfa N1 ∧ is_dfa N2 ⇒ is_dfa (nfa_union N1 N2)
Proof
 rw [is_dfa_def]
 >- metis_tac [wf_nfa_union]
 >- (rw [nfa_union_def,EXTENSION] >> metis_tac[])
 >- (ntac 2 pop_keep_tac >> rw [nfa_union_def,EXTENSION,PULL_EXISTS] >>
     ‘∃qa qb. {qa} = N1.delta q1 a ∧
              {qb} = N2.delta q2 a’ by metis_tac[] >>
     qexists_tac ‘qa ⊗ qb’ >> rw[EQ_IMP_THM]
     >- (RULE_ASSUM_TAC GSYM >> rfs[])
     >- metis_tac [EXTENSION,IN_INSERT]
     >- metis_tac [EXTENSION,IN_INSERT])
QED

(*---------------------------------------------------------------------------*)
(* Correctness of constructions                                              *)
(*---------------------------------------------------------------------------*)

Theorem dfa_compl_correct :
  is_dfa N ⇒
  ∀w. w ∈ nfa_lang (nfa_compl N) <=>
      w ∈ (KSTAR {[a] | a ∈ N.Sigma} DIFF (nfa_lang N))
Proof
  rw [in_nfa_lang, nfa_compl_def, EQ_IMP_THM]
  >- (rw_tac std_ss [GSYM IMP_DISJ_THM] >> spose_not_then assume_tac >>
      ‘qs = qs'’ by
        (irule dfa_execution_deterministic >> rw [] >> metis_tac[]) >>
      rw[] >> metis_tac[])
  >- metis_tac [NOT_EVERY]
  >- (drule_all dfa_execution >> rw[] >> first_x_assum drule >> rw[]
      >- metis_tac [EXTENSION,IN_INSERT]
      >- (qexists_tac ‘qs’ >> rw[]
          >- metis_tac [EXTENSION,IN_INSERT]
          >- (fs [EVERY_EL] >>
              drule_then (fn th => SUBST_TAC [SYM th]) EL_LENGTH_LAST >>
              first_x_assum irule >> decide_tac)
          >- (first_x_assum drule >> disch_then (SUBST_ALL_TAC o SYM) >>
              metis_tac [IN_INSERT]))
      >- (first_x_assum drule >> disch_then (SUBST_ALL_TAC o SYM) >>
          metis_tac [IN_INSERT]))
QED

Theorem dfa_inter_correct :
  is_dfa N1 ∧ is_dfa N2 ∧ N1.Sigma = N2.Sigma
  ⇒
  ∀w. w ∈ nfa_lang (nfa_inter N1 N2) <=>
      w ∈ nfa_lang N1 ∧ w ∈ nfa_lang N2
Proof
  strip_tac >> rw [in_nfa_lang, nfa_inter_def, EQ_IMP_THM]
  >- (qexists_tac ‘MAP nfst qs’ >> rw[]
      >- (Cases_on ‘qs’ >> fs[])
      >- (Cases_on ‘qs’ >> fs[])
      >- (first_x_assum drule >> rw[EL_MAP] >> rw[]))
  >- (qexists_tac ‘MAP nsnd qs’ >> rw[]
      >- (Cases_on ‘qs’ >> fs[])
      >- (Cases_on ‘qs’ >> fs[])
      >- (first_x_assum drule >> rw[EL_MAP] >> rw[]))
  >- (qexists_tac ‘MAP2 npair qs qs'’ >> rw[]
      >- (Cases_on ‘qs’ >> Cases_on ‘qs'’ >> fs[])
      >- (‘qs ≠ [] ∧ qs' ≠ []’ by (Cases_on ‘qs’ >> Cases_on ‘qs'’ >> fs[]) >>
          rw[LAST_MAP2])
      >- (ntac 2 (first_x_assum drule) >> ntac 2 disch_tac >>
          qexists_tac ‘EL (n+1) qs’ >> qexists_tac ‘EL (n+1) qs'’ >> rw[EL_MAP2]))
QED

Theorem dfa_union_correct :
  is_dfa N1 ∧ is_dfa N2 ∧ N1.Sigma = N2.Sigma
  ⇒
  ∀w. w ∈ nfa_lang (nfa_union N1 N2) <=>
      w ∈ nfa_lang N1 ∨ w ∈ nfa_lang N2
Proof
  strip_tac >> rw [in_nfa_lang, nfa_union_def, EQ_IMP_THM]
  >- (disj1_tac >> qexists_tac ‘MAP nfst qs’ >> rw[]
      >- (Cases_on ‘qs’ >> fs[])
      >- (Cases_on ‘qs’ >> fs[])
      >- (first_x_assum drule >> rw[EL_MAP] >> rw[]))
  >- (disj2_tac >> qexists_tac ‘MAP nsnd qs’ >> rw[]
      >- (Cases_on ‘qs’ >> fs[])
      >- (Cases_on ‘qs’ >> fs[])
      >- (first_x_assum drule >> rw[EL_MAP] >> rw[]))
  >- metis_tac[]
  >- (qpat_forget_tac ‘N1.Sigma = N2.Sigma’ >> qpat_forget_tac ‘is_dfa N1’ >>
      drule_all dfa_execution >> rw[] >>
      qexists_tac ‘MAP2 npair qs qs'’ >> rw[]
      >- (Cases_on‘qs’ >> Cases_on‘qs'’ >> fs[] >> metis_tac[EXTENSION,IN_INSERT])
      >- (‘qs ≠ [] ∧ qs' ≠ []’ by (Cases_on ‘qs’ >> Cases_on ‘qs'’ >> fs[]) >>
          rw[LAST_MAP2] >> disj1_tac >> drule_all EVERY_LAST >> rw[])
      >- (ntac 2 (first_x_assum drule) >> ntac 2 disch_tac >>
          qexists_tac ‘EL (n+1) qs’ >> qexists_tac ‘EL (n+1) qs'’ >> rw[EL_MAP2] >>
          metis_tac [EXTENSION,IN_INSERT]))
  >- metis_tac[]
  >- (qpat_x_assum ‘N1.Sigma = N2.Sigma’ (SUBST_ALL_TAC o GSYM) >>
      qpat_forget_tac ‘is_dfa N2’ >> drule_all dfa_execution >> rw[] >>
      qexists_tac ‘MAP2 npair qs' qs’ >> rw[]
      >- (Cases_on‘qs’ >> Cases_on‘qs'’ >> fs[] >> metis_tac[EXTENSION,IN_INSERT])
      >- (‘qs ≠ [] ∧ qs' ≠ []’ by (Cases_on ‘qs’ >> Cases_on ‘qs'’ >> fs[]) >>
          rw[LAST_MAP2] >> disj2_tac >> drule_all EVERY_LAST >> rw[])
      >- (ntac 2 (first_x_assum drule) >> ntac 2 disch_tac >>
          qexists_tac ‘EL (n+1) qs'’ >> qexists_tac ‘EL (n+1) qs’ >>
          rw[EL_MAP2] >> metis_tac [EXTENSION,IN_INSERT]))
QED

Theorem dfa_union_closed:
  is_dfa N1 ∧ is_dfa N2 ∧ N1.Sigma = N2.Sigma
  ⇒
  nfa_lang N1 ∪ nfa_lang N2 ∈ NFA_LANGS
Proof
  rw [NFA_LANGS_def] >> qexists_tac ‘nfa_union N1 N2’ >>
  ‘wf_nfa N1 ∧ wf_nfa N2’ by metis_tac [is_dfa_def] >>
  rw [wf_nfa_union,EXTENSION,dfa_union_correct]
QED

(*---------------------------------------------------------------------------*)
(* A regular language L is a subset of A*, where A is a finite alphabet. L   *)
(* is defined by the strings accepted by a given NFA.                        *)
(*---------------------------------------------------------------------------*)

Definition REGULAR_def:
  REGULAR = {(L,A) | ∃N. N.Sigma = A ∧ wf_nfa N ∧ L = nfa_lang N}
End

Theorem IN_REGULAR:
  (L,A) ∈ REGULAR ⇔ ∃N. N.Sigma = A ∧ wf_nfa N ∧ L = nfa_lang N
Proof
 rw [REGULAR_def,pairTheory.LAMBDA_PROD]
QED

Theorem IN_REGULAR_AS_DFA:
  (L,A) ∈ REGULAR ⇔ ∃M. M.Sigma = A ∧ is_dfa M ∧ L = nfa_lang M
Proof
  rw [IN_REGULAR,EQ_IMP_THM]
  >- (qexists_tac ‘nfa_to_dfa N’ >> rw[is_dfa_nfa_to_dfa] >>
      metis_tac [nfa_to_dfa_correct,EXTENSION])
  >- (fs [is_dfa_def] >> metis_tac[])
QED

Theorem REGULAR_BOUNDED:
  (L,A) ∈ REGULAR ⇒ L ⊆ KSTAR {[a] | a ∈ A}
Proof
  rw [IN_REGULAR,SUBSET_DEF] >>
  fs [in_nfa_lang,wf_nfa_def]
QED

Theorem REGULAR_SIGMA_FINITE:
  (L,A) ∈ REGULAR ⇒ FINITE A
Proof
  rw [IN_REGULAR,SUBSET_DEF] >> metis_tac [wf_nfa_def]
QED

Theorem EMPTYSET_IN_REGULAR:
  FINITE A ⇒ ({},A) ∈ REGULAR
Proof
  rw [IN_REGULAR] >>
  qexists_tac
    ‘<| Q := {}; Sigma := A;
        initial := {}; final := {};
        delta := λq a. {} |>’ >>
  rw [wf_nfa_def,EXTENSION,in_nfa_lang]
QED

Theorem EPSILON_LANG_IN_REGULAR:
  FINITE A ⇒ ({ε},A) ∈ REGULAR
Proof
  rw [IN_REGULAR] >>
  qexists_tac
    ‘<| Q := {0}; Sigma := A;
        initial := {0}; final := {0};
        delta := λq a. {} |>’ >>
  rw [wf_nfa_def,EXTENSION,in_nfa_lang,EQ_IMP_THM]
  >- (fs [NOT_LESS] >> Cases_on ‘x’ >> fs[] >>
      first_x_assum (mp_tac o Q.SPEC ‘0’) >> rw[])
  >- (qexists_tac ‘[0]’ >> rw[])
QED

Theorem REGULAR_CLOSED_UNDER_COMPL:
  (L,A) ∈ REGULAR ⇒ (KSTAR {[a] | a ∈ A} DIFF L, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >>
  qexists_tac ‘nfa_compl M’ >> rw[]
  >- simp[nfa_compl_def]
  >- metis_tac [is_dfa_compl]
  >- (drule dfa_compl_correct >> simp [EXTENSION])
QED

Theorem REGULAR_CLOSED_UNDER_UNION:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 ∪ L2, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >> rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘nfa_union M1 M2’ >> rw[]
  >- simp[nfa_union_def]
  >- metis_tac [is_dfa_union]
  >- (drule_all dfa_union_correct >> simp [EXTENSION])
QED

Theorem REGULAR_CLOSED_UNDER_INTER:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 ∩ L2, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >> rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘nfa_inter M1 M2’ >> rw[]
  >- simp[nfa_inter_def]
  >- metis_tac [is_dfa_inter]
  >- (drule_all dfa_inter_correct >> simp [EXTENSION])
QED

(*  TODO: need to understand where A* and complement comes into play
Theorem REGULAR_CLOSED_UNDER_DIFF:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 DIFF L2, A) ∈ REGULAR
Proof
  rw [DIFF_INTER_COMPL] >> irule REGULAR_CLOSED_UNDER_INTER >> rw[] >>
  drule REGULAR_CLOSED_UNDER_COMPL >>
  drule REGULAR_BOUNDED
QED
*)

(*---------------------------------------------------------------------------*)
(* Support for proving closure under concatenation. Adding a new start state *)
(* with arrows to all targets of the original start state(s) gives a machine *)
(* that accepts the original language less ε.                                *)
(*---------------------------------------------------------------------------*)

Definition new_state_def:
  new_state N = MAX_SET N.Q + 1
End

Theorem new_state_thm:
  FINITE N.Q ⇒ new_state N ∉ N.Q
Proof
  rw[new_state_def] >> strip_tac >>
  ‘MAX_SET N.Q + 1 <= MAX_SET N.Q’ by metis_tac[X_LE_MAX_SET] >>
  decide_tac
QED

Definition new_start_state_def:
 new_start_state N =
   let start' = new_state N
   in
     N with <|Q := N.Q ∪ {start'};
              initial := {start'};
              delta := (λq a.
                 if q = start' then
                    BIGUNION {N.delta q a |q| q ∈ N.initial}
                  else N.delta q a) |>
End

Theorem new_start_state_builtin_simps[simp]:
 (new_start_state N).Sigma = N.Sigma ∧
 (new_start_state N).Q = N.Q ∪ {new_state N} ∧
 (new_start_state N).initial = {new_state N} ∧
 (new_start_state N).final = N.final
Proof
  rw[new_start_state_def]
QED

Theorem new_start_state_delta:
  is_dfa N ∧ q ∈ N.Q ∧ a ∈ N.Sigma
   ⇒
 (new_start_state N).delta q a = N.delta q a
Proof
  rw [new_start_state_def,is_dfa_def, wf_nfa_def] >>
  metis_tac [new_state_thm]
QED

Theorem wf_new_start_state:
  wf_nfa N ==> wf_nfa (new_start_state N)
Proof
  fs [wf_nfa_def, new_start_state_def] >> rw[]
  >- metis_tac [SUBSET_UNION_RIGHT]
  >- (rw [] >> metis_tac [new_state_thm,SUBSET_UNION_RIGHT])
  >- (irule SUBSET_UNION_RIGHT >> rw [SUBSET_DEF] >> metis_tac [SUBSET_DEF])
QED

Theorem is_dfa_new_start_state:
  is_dfa N ⇒ is_dfa (new_start_state N)
Proof
  rw [is_dfa_def,wf_new_start_state] >>
  fs [new_start_state_def] >> rw[]
  >- metis_tac [new_state_thm,wf_nfa_def]
  >- (‘∃qa. N.delta q_0 a = {qa}’
            by metis_tac [wf_nfa_def,EXTENSION,IN_INSERT,SUBSET_DEF] >>
      qexists_tac ‘qa’ >> rw [EXTENSION,EQ_IMP_THM]
      >- metis_tac[]
      >- (qexists_tac ‘{qa}’ >> rw[]))
QED

Theorem epsilon_not_in_new_start_state_lang:
  wf_nfa N ⇒ ε ∉ nfa_lang (new_start_state N)
Proof
  rpt strip_tac >> drule_then assume_tac wf_new_start_state >>
  drule epsilon_in_nfa_lang >> rw[] >>
  rw [new_start_state_def] >> ntac 2 pop_forget_tac >>
  fs [wf_nfa_def,EXTENSION] >> metis_tac [new_state_thm,SUBSET_DEF]
QED

Theorem new_start_state_closed:
  wf_nfa N ∧
  is_exec (new_start_state N) qs w ⇒
  ∀n. 0 < n ∧ n < LENGTH qs ⇒ EL n qs ∈ N.Q
Proof
  strip_tac >> Induct >> rw[] >>
  ‘n < LENGTH qs’ by decide_tac >>
  fs [is_exec_def,EVERY_EL,wf_nfa_def,SUBSET_DEF] >>
  ‘n < LENGTH w’ by decide_tac >>
  first_x_assum drule >> rw [new_start_state_def,ADD1] >>
  ‘EL n w ∈ N.Sigma’ by metis_tac[]
  >- metis_tac[]
  >- (Cases_on ‘n=0’ >> fs[] >> rw[] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on ‘n=0’ >> fs[] >> rw[] >> metis_tac[])
QED

Theorem new_start_state_subset:
  is_dfa N ⇒ nfa_lang (new_start_state N) ⊆ nfa_lang N
Proof
  rw[SUBSET_DEF] >> rename1 ‘w ∈ nfa_lang N’ >>
  ‘w ≠ ε’ by metis_tac [is_dfa_def,epsilon_not_in_new_start_state_lang] >>
  fs [in_nfa_lang] >> rw[] >>
  ‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >>
  ‘∃q_0. N.initial = {q_0}’ by metis_tac [is_dfa_def] >>
  qexists_tac ‘q_0 :: TL qs’ >>
  fs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL] >> rw[]
  >- (‘TL qs ≠ []’ by (Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> gvs[]) >>
      rw [LAST_DEF])
  >- (rw [GSYM ADD1] >> Cases_on ‘n’ >> fs[]
      >- (first_x_assum drule >> rw[] >>
          rfs [new_start_state_def,PULL_EXISTS] >>
          Cases_on ‘qs’ >> fs [] >> Cases_on ‘t’ >> fs[])
      >- (rename1 ‘SUC m < LENGTH w’ >>
          ‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >> rw[GSYM ADD1] >>
          ‘EL (SUC m) w ∈ N.Sigma’ by fs [EVERY_EL] >>
          ‘EL (SUC m) qs ∈ N.Q’ by
             (fs [is_dfa_def] >> drule new_start_state_closed >> disch_then irule >>
              rw[is_exec_def] >> metis_tac[]) >>
          metis_tac [new_start_state_delta, ADD1]))
QED

Theorem new_start_state_diff_epsilon:
  is_dfa N ⇒ nfa_lang N DIFF {ε} ⊆ nfa_lang (new_start_state N)
Proof
  rw [EXTENSION,in_nfa_lang,SUBSET_DEF] >> rename1 ‘LENGTH w + 1’ >>
  qexists_tac ‘new_state N :: TL qs’ >>
  fs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL] >> rw[]
  >- (‘TL qs ≠ []’
       by (Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> gvs[]) >>
      rw [LAST_DEF])
  >- (‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >>
      Cases_on ‘n’ >> fs[]
      >- (first_x_assum drule >> rw[] >>
          rw [new_start_state_def,PULL_EXISTS] >> metis_tac[])
      >- (fs [is_dfa_def] >>
          ‘EL (SUC n') qs ∈ N.Q’ by
            (‘HD qs ∈ N.Q’
               by metis_tac [wf_nfa_def,SUBSET_DEF] >>
             drule_all nfa_execution_states_closed >>
             rw [EVERY_EL]) >>
          ‘EL (SUC n') w ∈ N.Sigma’ by fs [EVERY_EL] >> rw[GSYM ADD1] >>
          metis_tac[new_start_state_delta,ADD1,is_dfa_def]))
QED

Theorem nfa_lang_new_start_state:
  is_dfa N ⇒ nfa_lang (new_start_state N) = nfa_lang N DIFF {ε}
Proof
  rw[EXTENSION,EQ_IMP_THM]
   >- metis_tac [new_start_state_subset,SUBSET_DEF]
   >- metis_tac [epsilon_not_in_new_start_state_lang,is_dfa_def]
   >- metis_tac [new_start_state_diff_epsilon |> SRULE [SUBSET_DEF]]
QED

Theorem is_dfa_final_union:
  is_dfa N ∧ qs ⊆ N.Q ⇒ is_dfa (N with final := N.final ∪ qs)
Proof
 rw [is_dfa_def,wf_nfa_def]
QED

Theorem nfa_lang_final_union:
  nfa_lang (N with final := N.final ∪ qs) =
  nfa_lang N ∪ nfa_lang (N with final := qs)
Proof
 rw [EXTENSION,in_nfa_lang] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Given a machine that accepts ε, obtain a machine that recognizes the same *)
(* language, except ε is rejected. And vice-versa.                           *)
(*---------------------------------------------------------------------------*)

Theorem REGULAR_CLOSED_UNDER_EPSILON_ADDITION_OR_DELETION:
 (L ∪ {ε},A) ∈ REGULAR ⇔ (L DIFF {ε},A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA,EQ_IMP_THM] THENL
  [qexists_tac ‘new_start_state M’,
   qexists_tac ‘let M' = new_start_state M
                in M' with <| final := M'.final ∪ {new_state M} |>’]
  >> rw[]
  >- metis_tac [is_dfa_new_start_state]
  >- (drule_then subst_all_tac UNION_EQ_DIFF >> pop_forget_tac >>
      metis_tac [nfa_lang_new_start_state])
  >- (drule is_dfa_new_start_state >> rpt pop_forget_tac >> disch_tac >>
      ‘M.final = (new_start_state M).final’ by rw[] >> pop_subst_tac >>
      irule is_dfa_final_union >> rw[])
  >- (drule_then subst_all_tac DIFF_EQ_UNION >> pop_forget_tac >>
     ‘M.final = (new_start_state M).final’ by rw[] >> pop_subst_tac >>
      rw [EXTENSION,nfa_lang_final_union,nfa_lang_new_start_state] >>
      rw [EQ_IMP_THM]
      >- rw[in_nfa_lang,new_start_state_def,LENGTH_EQ_NUM_compute,PULL_EXISTS]
      >- rw[in_nfa_lang,new_start_state_def,LENGTH_EQ_NUM_compute,PULL_EXISTS]
      >- rw[]
      >- (disj2_tac >> rename1 ‘w = ε’ >> CCONTR_TAC >>
          fs [in_nfa_lang,NOT_NIL_EQ_LENGTH_NOT_0] >>
          ‘EL (LENGTH w) qs ∈ M.Q’
             by (fs [is_dfa_def] >> drule new_start_state_closed >>
                 disch_then irule >> rw[is_exec_def] >> metis_tac[]) >>
          gvs [EL_LENGTH_LAST] >>
          metis_tac [new_state_thm, is_dfa_def, wf_nfa_def]))
QED

(* Better to have this as an instance of closure under difference? *)
Theorem REGULAR_CLOSED_UNDER_EPSILON_DELETION:
 (L,A) ∈ REGULAR ⇒ (L DIFF {ε},A) ∈ REGULAR
Proof
  disch_tac >> Cases_on ‘ε ∈ L’
  >- (‘L = L ∪ {ε}’ by (rw [EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
      metis_tac [REGULAR_CLOSED_UNDER_EPSILON_ADDITION_OR_DELETION])
  >- (‘L DIFF {ε} = L’ by (rw [EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
      metis_tac [])
QED

Theorem isolate_trivial_cases:
 ∀L. ∃L0. L0 ⊆ {ε} ∧ L = L0 ∪ (L DIFF {ε})
Proof
  rw [SUBSET_DEF,EXTENSION] >>
  qexists_tac ‘if ε ∈ L then {ε} else {}’ >>
  rw[EQ_IMP_THM] >> metis_tac[]
QED

Theorem TRIVIAL_DOT_TRIVIAL_IN_REGULAR:
 L1 ⊆ {ε} ∧ L2 ⊆ {ε} ∧ FINITE A ⇒ (L1 dot L2,A) ∈ REGULAR
Proof
  rw [SUBSET_SING] >> simp [DOT_EMPTYSET, DOT_EPSILON] >>
  metis_tac [EMPTYSET_IN_REGULAR,EPSILON_LANG_IN_REGULAR]
QED

Triviality TRIVIAL_DOT_EPSILON_FREE_IN_REGULAR:
  (L,A) ∈ REGULAR ∧
  s1 ⊆ {ε} ∧ s2 ⊆ {ε}
  ⇒
  (L = s2 ∪ (L DIFF {ε}) ⇒ (s1 dot (L DIFF {ε}),A) ∈ REGULAR) ∧
  (L = s1 ∪ (L DIFF {ε}) ⇒ ((L DIFF {ε}) dot s2,A) ∈ REGULAR)
Proof
  rw [SUBSET_SING] >>
  fs [DOT_EMPTYSET, DOT_EPSILON] >>
  metis_tac [EMPTYSET_IN_REGULAR, REGULAR_CLOSED_UNDER_EPSILON_DELETION,
             UNION_COMM,REGULAR_SIGMA_FINITE]
QED

(*---------------------------------------------------------------------------*)
(* Mechanism for renaming states apart when combining machines, used in, eg, *)
(* the nfa_dot machine. Without renaming, the composed transition function   *)
(* could be confused when given a state that happened to occur in both       *)
(* components. NB: we could also prevent confusion via the encode/decode     *)
(* functions used elsewhere in this theory.                                  *)
(*---------------------------------------------------------------------------*)

Definition newFn_def:
  newFn base n = base + n
End

Theorem INJ_newFn:
  INJ (newFn base) 𝕌(:num) 𝕌(:num)
Proof
  rw [newFn_def,INJ_DEF]
QED

Theorem newFn_eq[simp]:
  newFn base q1 = newFn base q2 ⇔ q1 = q2
Proof
  assume_tac INJ_newFn >> fs [INJ_DEF] >> metis_tac[]
QED

Theorem BIJ_newFn:
  BIJ (newFn base) N.Q (IMAGE (newFn base) N.Q)
Proof
 irule INJ_BIJ_SUBSET >> qexists_tac ‘𝕌(:num)’ >>
 rw [SUBSET_DEF] >> metis_tac [INJ_newFn]
QED

Theorem oldFn_newFn:
  q ∈ N.Q ⇒ LINV (newFn base) N.Q (newFn base q) = q
Proof
  rw [] >> assume_tac BIJ_newFn >> drule BIJ_LINV_INV >>
  rw[PULL_EXISTS] >> fs [newFn_def]
QED

Definition rename_states_def:
  rename_states N base =
    let newq = newFn base in
    let oldq = LINV newq N.Q in
    N with <| Q       := IMAGE newq N.Q;
              initial := IMAGE newq N.initial;
              final   := IMAGE newq N.final;
              delta   := λnq a. IMAGE newq (N.delta (oldq nq) a)
            |>
End

Theorem rename_states_builtin_simps[simp]:
 (rename_states N base).Sigma = N.Sigma
Proof
 simp [rename_states_def]
QED

Theorem wf_nfa_rename_states:
  wf_nfa N ⇒ wf_nfa (rename_states N base)
Proof
  rw[wf_nfa_def,rename_states_def,SUBSET_DEF] >> metis_tac[oldFn_newFn]
QED

Theorem rename_states_delta_commutes:
 wf_nfa N ∧ q ∈ N.Q ∧ a ∈ N.Sigma
  ⇒
 N.delta q a = IMAGE (LINV (newFn base) N.Q)
                     ((rename_states N base).delta (newFn base q) a)
Proof
  rw[EXTENSION,EQ_IMP_THM,rename_states_def] >>
  qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
  metis_tac [wf_nfa_def,SUBSET_DEF,oldFn_newFn]
QED

Theorem is_dfa_rename_states:
  wf_nfa N ⇒ (is_dfa (rename_states N base) ⇔ is_dfa N)
Proof
  rw [is_dfa_def,EQ_IMP_THM,wf_nfa_rename_states]
  >- (pop_forget_tac >> pop_keep_tac >> simp [rename_states_def] >>
      ‘BIJ (newFn base) N.initial (IMAGE (newFn base) N.initial)’ by
         (irule INJ_BIJ_SUBSET >> qexists_tac ‘𝕌(:num)’ >>
          rw [SUBSET_DEF] >> metis_tac [INJ_newFn]) >>
      ‘FINITE N.initial’ by metis_tac [wf_nfa_def,SUBSET_FINITE] >>
      drule_all FINITE_BIJ_CARD >> rw[] >> fs[] >>
      ‘SING N.initial’ by metis_tac [SING_IFF_CARD1] >> fs [SING_DEF])
  >- (‘newFn base q ∈ (rename_states N base).Q’ by rw [rename_states_def] >>
      first_x_assum drule_all >> rw[] >>
      qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
      rename [‘_.delta _ a = {q1}’] >>
      qexists_tac ‘oldFn q1’ >>
      drule_all_then (qspec_then ‘base’ assume_tac)
        rename_states_delta_commutes >>  rw[])
  >- rw [rename_states_def]
  >- (gvs[rename_states_def] >> first_x_assum drule_all >> rw[] >>
      rename [‘N.delta x q = {q1}’] >>
      qexists_tac ‘newFn base q1’ >> rw [oldFn_newFn])
QED

Theorem nfa_lang_rename_states:
  wf_nfa N ⇒ nfa_lang (rename_states N base) = nfa_lang N
Proof
  rw [EXTENSION,EQ_IMP_THM]
  >- (drule_then (qspec_then ‘base’ assume_tac) wf_nfa_rename_states >>
      drule_all in_nfa_lang_is_accepting_exec >>
      rw[NULL_EQ,is_accepting_exec_def,in_nfa_lang]
      >- (drule is_exec_Sigma >> rw[])
      >- (qpat_forget_tac ‘_ ∈ nfa_lang _’ >>
          qpat_keep_tac ‘HD qs ∈ _’ >> qpat_keep_tac ‘LAST qs ∈ _’ >>
          rw [rename_states_def] >> rename [‘qi ∈ N.initial’, ‘qf ∈ N.final’] >>
          qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
          qexists_tac ‘MAP oldFn qs’ >> rw[]
          >- (drule is_exec_length >> rw[])
          >- metis_tac [oldFn_newFn,wf_nfa_def,SUBSET_DEF]
          >- metis_tac [oldFn_newFn,wf_nfa_def,SUBSET_DEF]
          >- (drule is_exec_length >> rename1 ‘n < LENGTH w’ >> disch_tac >>
              ‘n < LENGTH qs’ by decide_tac >> rw[EL_MAP] >>
              drule_all is_exec_states >>
              rw [rename_states_def,EVERY_EL,PULL_EXISTS] >>
              ‘n < LENGTH w + 1’ by metis_tac [] >> first_x_assum drule >> rw[] >>
              rw[Abbr ‘oldFn’,oldFn_newFn] >>
              qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
              drule_all is_exec_delta >> rw [rename_states_def] >> rw[] >>
              pop_keep_tac >> rw [Abbr‘oldFn’, oldFn_newFn] >>
              ‘EL n w ∈ N.Sigma’ by (drule is_exec_Sigma >> rw [EVERY_EL]) >>
              metis_tac [wf_nfa_def, SUBSET_DEF,oldFn_newFn])))
  >- (drule_all in_nfa_lang_is_accepting_exec >>
      rw[NULL_EQ,in_nfa_lang,is_accepting_exec_def]
      >- metis_tac[is_exec_Sigma]
      >- (rename1 ‘is_exec N qs w’ >>
          qexists_tac ‘MAP (newFn base) qs’ >> rw[]
          >- metis_tac [is_exec_length]
          >- rw [rename_states_def]
          >- rw [rename_states_def]
          >- (rw [rename_states_def] >> drule is_exec_length >> disch_tac >>
              ‘n < LENGTH qs’ by decide_tac >> rw[EL_MAP] >>
              drule_all is_exec_states >> rw [EVERY_EL] >>
              ‘n < LENGTH w + 1’ by metis_tac [] >> first_x_assum drule >> rw[] >>
              ‘EL n w ∈ N.Sigma’ by (drule is_exec_Sigma >> rw [EVERY_EL]) >>
              rw [oldFn_newFn] >> metis_tac [is_exec_delta])))
QED

Theorem RENAME_STATES_APART:
  FINITE Q ∧ wf_nfa N
  ⇒
  ∃N'. N'.Sigma = N.Sigma ∧
       Q ∩ N'.Q = ∅ ∧
       wf_nfa N' ∧
       (is_dfa N' ⇔ is_dfa N) ∧
       nfa_lang N' = nfa_lang N
Proof
 strip_tac >>
 qexists_tac ‘rename_states N (MAX_SET (Q ∪ N.Q) + 1)’ >> rw[]
 >- (rw [rename_states_def,EXTENSION, Once (GSYM IMP_DISJ_THM),newFn_def] >>
     CCONTR_TAC >> pop_forget_tac >>
     ‘FINITE N.Q’ by metis_tac [wf_nfa_def] >> qpat_keep_tac ‘_ ∈ _’ >>
     rw [MAX_SET_UNION,MAX_DEF] >> irule MAX_SET_BOUNDED >> rw[])
 >- metis_tac [wf_nfa_rename_states]
 >- metis_tac [is_dfa_rename_states]
 >- metis_tac [nfa_lang_rename_states]
QED

(*---------------------------------------------------------------------------*)
(* Correctness of nfa_dot construction for epsilon-free machines is based on *)
(* two lemmas: one for pasting together component executions, and one for    *)
(* breaking an nfa-dot execution into two component executions.              *)
(*---------------------------------------------------------------------------*)

Theorem is_accepting_exec_paste:
  is_dfa M1 ∧ is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧ M1.Q ∩ M2.Q = ∅ ∧
  w1 ≠ ε ∧ w2 ≠ ε ∧
  is_accepting_exec M1 qs1 w1 ∧
  is_accepting_exec M2 qs2 w2
  ⇒
  is_accepting_exec (nfa_dot M1 M2) (qs1 ++ TL qs2) (w1 ++ w2)
Proof
  rw [is_accepting_exec_def] >>
  ‘EVERY (λq. q ∈ M1.Q) qs1 ∧ EVERY (λq. q ∈ M2.Q) qs2’ by
      metis_tac [is_dfa_def,is_exec_states] >>
  ‘qs1 ≠ [] ∧ qs2 ≠ []’ by metis_tac [is_exec_nonempty] >>
  ‘TL qs2 ≠ []’ by
     metis_tac [is_accepting_exec_length,is_accepting_exec_def,is_dfa_def] >>
  rw [is_exec_def]
  >- metis_tac [is_exec_Sigma]
  >- metis_tac [is_exec_Sigma]
  >- (imp_res_tac is_exec_length >> rw[LENGTH_TL])
  >- metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF]
  >- (‘n < LENGTH w1 ∨ n = LENGTH w1 ∨ LENGTH w1 < n’ by decide_tac
      >- (rev_drule is_exec_Sigma >> rw[EVERY_EL] >>
          rev_drule is_exec_length >> strip_tac >>
          ‘n < LENGTH qs1’ by decide_tac >> ‘n+1 < LENGTH qs1’ by decide_tac >>
          rw[EL_APPEND1] >> rw [nfa_dot_def]
          >- metis_tac [is_exec_delta,is_dfa_def]
          >- metis_tac [is_exec_delta,is_dfa_def]
          >- (qpat_keep_tac ‘EVERY _ qs1’ >> rw[EVERY_EL] >> metis_tac[]))
      >- (rw[] >> rfs[] >> rev_drule is_exec_length >>
          disch_then(assume_tac o SYM) >> ONCE_ASM_REWRITE_TAC[] >>
          rw[SRULE [NULL_EQ] EL_LENGTH_APPEND] >>
          ‘LENGTH w1 < LENGTH qs1’ by decide_tac >> rw [EL_APPEND1] >>
          ‘LENGTH w1 = PRE (LENGTH qs1)’ by decide_tac >> pop_subst_tac >>
          rw [EL_PRE_LENGTH] >> rw [nfa_dot_def,PULL_EXISTS]
          >- (disj2_tac >> rfs [is_dfa_def,NOT_NIL_EQ_LENGTH_NOT_0] >> rw[] >>
              ‘0 < LENGTH w1’ by decide_tac >> PURE_REWRITE_TAC[GSYM EL] >>
              drule is_exec_delta >> disch_then drule >> simp[] >> rfs[])
          >- metis_tac[is_dfa_def,wf_nfa_def,SUBSET_DEF])
      >- (‘∃k. 0 < k ∧ k < LENGTH w2 ∧ n = LENGTH w1 + k’
            by (qexists_tac ‘n - LENGTH w1’ >> fs[]) >> rw[EL_APPEND2_ALT] >>
          rev_drule is_exec_length >> disch_tac >>
          ‘k + (LENGTH w1 + 1) = LENGTH qs1 + k’ by decide_tac >> pop_subst_tac >>
          drule is_exec_length >> disch_tac >>
          ‘k < LENGTH (TL qs2)’
            by (‘k + 1 < LENGTH qs2’ by decide_tac >>
                drule LENGTH_TL_ALT >> rw[]) >>
          ‘k < LENGTH qs2’ by decide_tac >>
          rw [EL_APPEND2_ALT] >> rw [EL_APPEND_EQN] >> rw [nfa_dot_def]
          >- (fs [EVERY_EL,EXTENSION] >> metis_tac[])
          >- (fs [EVERY_EL,EXTENSION] >> metis_tac[])
          >- metis_tac [is_exec_delta])
     )
  >- rw[LAST_APPEND_NOT_NIL]
QED

Theorem nfa_dot_paste:
  is_dfa M1 ∧ is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧ M1.Q ∩ M2.Q = ∅ ∧
  ε ∉ nfa_lang M1 ∧ ε ∉ nfa_lang M2
  ⇒
  nfa_lang M1 dot nfa_lang M2 ⊆ nfa_lang (nfa_dot M1 M2)
Proof
  rw [SUBSET_DEF, IN_dot] >>
  ‘u ≠ ε ∧ v ≠ ε’ by metis_tac[] >>
  ntac 2 (qpat_forget_tac ‘ε ∉ _’) >>
  ‘wf_nfa M1 ∧ wf_nfa M2 ∧ wf_nfa (nfa_dot M1 M2)’ by
    metis_tac [is_dfa_def,wf_nfa_dot] >>
  fs [in_nfa_lang_iff_accepting_exec] >>
  metis_tac[is_accepting_exec_paste]
QED

Triviality nfa_dot_delta_states:
  wf_nfa M1 ∧ wf_nfa M2 ∧
  M1.Sigma = M2.Sigma ∧ a ∈ M1.Sigma ∧ q ∈ M1.Q ∪ M2.Q
  ⇒
  (nfa_dot M1 M2).delta q a ⊆ M1.Q ∪ M2.Q
Proof
  rw [wf_nfa_def, nfa_dot_def,SUBSET_DEF] >> metis_tac[]
QED

Triviality nfa_dot_delta_second_states:
  wf_nfa M1 ∧ wf_nfa M2 ∧ M1.Q ∩ M2.Q = ∅ ∧
  M1.Sigma = M2.Sigma ∧ a ∈ M1.Sigma ∧ q ∈ M2.Q ∧
  q' ∈ (nfa_dot M1 M2).delta q a
  ⇒
  q' ∈ M2.Q
Proof
  rw [wf_nfa_def, nfa_dot_def,EXTENSION,SUBSET_DEF] >> metis_tac[]
QED

Triviality nfa_dot_states:
   wf_nfa M1 ∧ wf_nfa M2 ∧ M1.Sigma = M2.Sigma ∧
   is_exec (nfa_dot M1 M2) qs w
   ⇒
   EVERY (λq. q ∈ M1.Q ∪ M2.Q) qs
Proof
  simp[EVERY_EL] >> disch_tac >> Induct >> rw[] >>
  imp_res_tac POS_LENGTH_NOT_NIL >> fs [is_exec_def,EVERY_EL] >>
  ‘n < LENGTH w’ by decide_tac >>
  first_x_assum drule >> first_x_assum drule >> rw[] >>
  metis_tac[nfa_dot_delta_states, IN_UNION, ADD1, SUBSET_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Lemma about nfa_dot executions being split into component executions.     *)
(*                                                                           *)
(*   Let qs be an nfa_dot execution accepting word w. The first state        *)
(*   of qs is in M1.Q and the last state is in M2.Q. Therefore there is      *)
(*   a first state of qs that is in M2.Q; say it occurs at index j. Since    *)
(*   M1 and M2 do not accept epsilon, 1 < j < length(qs). Thus               *)
(*   qs[0 .. j-1] is a sequence of M1.Q states, and                          *)
(*   qs[j .. length(qs)-1] is a sequence of M2.Q states. Moreover            *)
(*                                                                           *)
(*    * qs[j-1] ∈ M1.final                                                   *)
(*    * qs[j] = M2.delta M2.initial (w[j-1])                                 *)
(*    * (nfa_dot M1 M2).delta behaves the same as M1.delta below j-1,        *)
(*      and the same as M2.delta at j and above.                             *)
(*---------------------------------------------------------------------------*)

Theorem nfa_dot_snip_lemma:
   is_dfa M1 ∧
   is_dfa M2 ∧
   M1.Sigma = M2.Sigma ∧
   M1.Q ∩ M2.Q = ∅ ∧
   ε ∉ nfa_lang M1 ∧
   ε ∉ nfa_lang M2 ∧
   is_exec (nfa_dot M1 M2) qs w ∧
   HD qs ∈ M1.initial ∧
   LAST qs ∈ M2.final
  ⇒
  ∃q0 j.
    M2.initial = {q0} ∧
    1 < j ∧ j < LENGTH qs ∧
    (∀i. i < j-1 ⇒ EL (i+1) qs ∈ M1.delta (EL i qs) (EL i w)) ∧
    EL (j-1) qs ∈ M1.final ∧
    EL j qs ∈ M2.delta q0 (EL (j-1) w) ∧
    (∀k. j + k < LENGTH w ⇒
         EL (j+k+1) qs ∈ M2.delta (EL (j+k) qs) (EL (j+k) w))
Proof
  rw[] >>
  ‘∃q0. M2.initial = {q0}’ by
    metis_tac [is_dfa_def] >> qexists_tac ‘q0’ >> simp[] >>
  ‘∃j. j < LENGTH qs ∧ EL j qs ∈ M2.Q ∧ ∀m. m < j ⇒ EL m qs ∈ M1.Q’ by
     (qexists_tac ‘LEAST i. i < LENGTH qs ∧ EL i qs ∈ M2.Q’ >>
      numLib.LEAST_ELIM_TAC >> rw[]
      >- (‘qs ≠ []’ by metis_tac [is_exec_nonempty] >>
          fs [LAST_EL,NOT_NIL_EQ_LENGTH_NOT_0] >>
          qexists_tac ‘PRE (LENGTH qs)’ >> rw[] >>
          metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF])
      >- (first_x_assum drule >> rw[] >>
          ‘EVERY (λq. q ∈ M1.Q ∪ M2.Q) qs’ by
             (irule nfa_dot_states >> metis_tac [is_dfa_def]) >>
          fs [EVERY_EL] >> metis_tac [LESS_TRANS])) >>
  qexists_tac ‘j’ >> rpt conj_asm1_tac
  >- (spose_not_then assume_tac >> ‘j= 0 ∨ j = 1’ by decide_tac >> rw[]
      >- (fs[EXTENSION] >> metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF])
      >- (pop_forget_tac >>
          ‘EL 0 qs ∈ M1.Q’ by metis_tac [DECIDE “0 < 1”] >>
          forget_tac is_forall >>
          ‘M1.initial ∩ M1.final = ∅’ by
             metis_tac[is_dfa_def, epsilon_in_nfa_lang] >>
          ‘HD qs ∉ M1.final’ by
             (fs[EXTENSION] >> metis_tac []) >>
          drule is_exec_length >> strip_tac >>
          ‘0 < LENGTH w’ by decide_tac >>
          drule is_exec_Sigma >> disch_tac >> fs [EVERY_EL] >>
          first_x_assum drule >> strip_tac >>
          drule is_exec_delta >> rw[] >>
          qexists_tac ‘0’ >> rw [nfa_dot_def] >> fs[EXTENSION] >>
          metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF]))
  >- asm_rewrite_tac[]
  >- (rw[] >> ‘EL i qs ∈ M1.Q ∧ EL (i+1) qs ∈ M1.Q’ by rw[] >>
      drule is_exec_length >> rw [] >> fs[] >>
      ‘i < LENGTH w’ by decide_tac >>
      drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
      first_x_assum drule >> rw[] >>
      drule is_exec_delta >> rw[] >> first_x_assum drule >>
      rw [nfa_dot_def] >> fs[EXTENSION] >>
      metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF])
  >- (drule is_exec_length >> rw [] >> fs[] >>
      ‘EL (j-1) qs ∈ M1.Q ∧ j-1 < LENGTH w’ by rw[] >>
      drule is_exec_delta >> rw[] >> first_x_assum drule >>
      rw [nfa_dot_def] >> fs[] >> strip_tac >>
      drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
      fs [EXTENSION] >>
      ‘j-1 < LENGTH w’ by rw[] >>
      metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF])
  >- (drule is_exec_length >> rw [] >> fs[] >>
       ‘EL (j-1) qs ∈ M1.Q ∧ j-1 < LENGTH w’ by rw[] >>
       drule is_exec_delta >> rw[] >> first_x_assum drule >>
       rw [nfa_dot_def] >> fs[] >>
       drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
       fs [EXTENSION] >>
       ‘j-1 < LENGTH w’ by rw[] >>
      metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF])
  >- (rw [] >> rpt (forget_tac is_forall) >>
      drule is_exec_length >> rw [] >> fs[] >> rw[] >>
      ‘EL (j+k) qs ∈ M2.Q’ by
         (Induct_on ‘k’ >> rw[] >>
          irule nfa_dot_delta_second_states >> rw []
          >- metis_tac [is_dfa_def]
          >- (qexistsl_tac [‘M1’, ‘EL (j+k) w’,‘EL (j+k) qs’] >>
              simp[] >> rpt conj_asm1_tac
              >- metis_tac [is_dfa_def]
              >- (drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL])
              >- (‘EL (j + k) qs ∈ M2.Q’ by rw[] >>
                  ‘j+k < LENGTH w’ by rw[] >>
                  drule_all is_exec_delta >>
                  metis_tac [DECIDE “j + k + 1 = j + SUC k”]))) >>
      drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
      drule is_exec_delta >> rw[] >> first_x_assum drule >>
      rw [nfa_dot_def] >> fs[EXTENSION] >> metis_tac[])
QED

Theorem nfa_dot_snip:
  is_dfa M1 ∧ is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧ M1.Q ∩ M2.Q = ∅ ∧
  ε ∉ nfa_lang M1 ∧ ε ∉ nfa_lang M2
  ⇒
   nfa_lang (nfa_dot M1 M2) ⊆ nfa_lang M1 dot nfa_lang M2
Proof
  rw [SUBSET_DEF] >> rename1 ‘w ∈ _’ >>
  ‘wf_nfa (nfa_dot M1 M2)’ by
    metis_tac [is_dfa_def,wf_nfa_dot] >>
  drule_all in_nfa_lang_is_accepting_exec >> rw[is_accepting_exec_def] >>
  qpat_forget_tac ‘w ∈ nfa_lang _’ >> qpat_forget_tac ‘~NULL qs’ >>
  drule_all nfa_dot_snip_lemma >> rw [IN_dot] >>
  qexistsl_tac [‘TAKE (j-1) w’, ‘DROP (j-1) w’] >> rw[in_nfa_lang] >>
  TRY (drule is_exec_Sigma >> rw [nfa_dot_def,EVERY_TAKE,EVERY_DROP])
  >- (qexists_tac ‘TAKE j qs’ >> rw[]
      >- (drule is_exec_length >> rw[LENGTH_TAKE])
      >- rw [HD_TAKE]
      >- (‘LAST (TAKE j qs) = EL (j − 1) qs’ suffices_by metis_tac[] >>
          ‘TAKE j qs ≠ []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0] >>
          rw [LAST_EL,EL_TAKE])
      >- (drule is_exec_length >> disch_tac >>
          ‘j - 1 < LENGTH w’ by decide_tac >>
          fs [LENGTH_TAKE,EL_TAKE]))
  >- (qexists_tac ‘q0::DROP j qs’ >> rw[]
      >- (drule is_exec_length >> rw[])
      >- (‘DROP j qs ≠ []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0] >>
          rw [LAST_DEF,last_drop])
      >- (rename1 ‘k < LENGTH w + 1 − j’ >>
          Cases_on ‘k’ >> rw[]
          >- rw [HD_DROP]
          >- (rw [Once (GSYM ADD1),EL_restricted] >>
              drule is_exec_length >> rw [EL_DROP] >>
              ‘j + SUC n - 1 = j + n’ by decide_tac >> pop_subst_tac >>
              ‘j + SUC n = j + (n + 1)’ by decide_tac >> pop_subst_tac >>
              first_x_assum irule >> decide_tac)))
QED

Theorem REGULAR_CLOSED_UNDER_EPSILON_FREE_DOT:
  ε ∉ L1 ∧ ε ∉ L2 ∧
  (L1,A) ∈ REGULAR ∧
  (L2,A) ∈ REGULAR
  ⇒
  (L1 dot L2, A) ∈ REGULAR
Proof
  disch_then (strip_assume_tac o SRULE [IN_REGULAR_AS_DFA]) >> rw[] >>
  rename1 ‘M1.Sigma = M2.Sigma’ >>
  ‘∃M2a. is_dfa M2a ∧ nfa_lang M2a = nfa_lang M2 ∧
         M1.Q ∩ M2a.Q = ∅ ∧ M2a.Sigma = M2.Sigma’ by
    (‘FINITE M1.Q ∧ wf_nfa M2’ by metis_tac [is_dfa_def, wf_nfa_def] >>
     drule_all RENAME_STATES_APART >> metis_tac []) >>
  rw [IN_REGULAR] >> pop_sym_subst_tac >> qpat_forget_tac ‘is_dfa M2’ >>
  qpat_x_assum ‘nfa_lang M2a = nfa_lang M2’ sym_subst_all_tac >>
  rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘nfa_dot M1 M2’ >> rpt conj_tac
  >- rw [nfa_dot_def]
  >- metis_tac [is_dfa_def,wf_nfa_dot]
  >- metis_tac [nfa_dot_paste, nfa_dot_snip, SET_EQ_SUBSET]
QED

(*---------------------------------------------------------------------------*)
(* Closure under concatenation, at last. There's some case analysis on       *)
(* whether the component languages include the empty string before getting   *)
(* to the main argument, in which both languages do not include ε.           *)
(*---------------------------------------------------------------------------*)

Theorem REGULAR_CLOSED_UNDER_DOT:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 dot L2,A) ∈ REGULAR
Proof
  strip_tac >> imp_res_tac REGULAR_SIGMA_FINITE >>
  strip_assume_tac (Q.ISPEC ‘L1 : num list -> bool’ isolate_trivial_cases) >>
  rename1 ‘s1 ⊆ {ε}’ >>
  strip_assume_tac (Q.ISPEC ‘L2 : num list -> bool’ isolate_trivial_cases) >>
  rename1 ‘s2 ⊆ {ε}’ >>
  ONCE_ASM_REWRITE_TAC[] >>
  simp [DOT_UNION_LDISTRIB,DOT_UNION_RDISTRIB,PUSH_EXISTS,GSYM UNION_ASSOC] >>
  rpt (irule REGULAR_CLOSED_UNDER_UNION ORELSE conj_tac)
  >- metis_tac [TRIVIAL_DOT_TRIVIAL_IN_REGULAR]
  >- metis_tac [TRIVIAL_DOT_EPSILON_FREE_IN_REGULAR]
  >- metis_tac [TRIVIAL_DOT_EPSILON_FREE_IN_REGULAR]
  >- (irule REGULAR_CLOSED_UNDER_EPSILON_FREE_DOT >> rw[] >>
      metis_tac [REGULAR_CLOSED_UNDER_EPSILON_DELETION])
QED

(*---------------------------------------------------------------------------*)
(* Closure under Kleene                                                      *)
(*---------------------------------------------------------------------------*)

(*
  From

    wlist = [w1 ; ... ; wn]

  obtain

    qslist = [qs1 ; ... ; qsn]

  where

    is_accepting_exec qsi wi holds, for i < LENGTH wlist

  To then build the execution for the nfa_plus machine, we basically want
  to build the full nfa_plus state list as "FLAT qslist". But, as for the
  nfa_dot pasting lemma, we have to arrange for the branching back from
  accept states to skip over the initial state. Thus for every qsi, i > 1,
  drop the HD:

        nfa_plus_qs = qs1 ++ TL qs2 ++ ... ++ TL qsn
*)

Triviality qslist_length:
  ∀wlist qslist.
  LIST_REL (is_accepting_exec M) qslist wlist
  ⇒
  LENGTH (FLAT qslist) = LENGTH (FLAT wlist) + LENGTH wlist
Proof
 Induct_on ‘wlist’ >> rw[] >> fs[] >>
 rename1 ‘is_accepting_exec M qs w’ >>
 ‘LENGTH qs = LENGTH w + 1’ suffices_by decide_tac >>
 metis_tac [is_accepting_exec_def,is_exec_length]
QED

Triviality length_flat_tl_lem:
  EVERY (λlist. list ≠ []) ll
  ⇒
  LENGTH (FLAT (MAP TL ll)) + LENGTH ll = LENGTH (FLAT ll)
Proof
  Induct_on ‘ll’ >> rw[] >> fs[] >>
  rw [DECIDE“a + (b + SUC c) = (a + c) + b + 1”] >>
  qpat_x_assum ‘_ = _’ (subst_all_tac o SYM) >> rw[] >>
  ‘LENGTH (TL h) + 1 = LENGTH h’ suffices_by decide_tac >>
  fs[NOT_NIL_EQ_LENGTH_NOT_0,LENGTH_TL]
QED

Triviality LAST_APPEND_FLAT:
  ll ≠ [] ∧ LAST ll ≠ []
  ⇒
  LAST (list ++ FLAT ll) = LAST (LAST ll)
Proof
  rw[] >> drule_all LAST_FLAT >> disch_tac >>
  drule FLAT_NOT_NIL >> rw[LAST_APPEND_NOT_NIL]
QED

Theorem nfa_plus_delta_subset:
 M.delta q a ⊆ (nfa_plus M).delta q a
Proof
 rw [nfa_plus_def]
QED

Theorem is_accepting_exec_nfa_plus:
  is_accepting_exec M qs w ⇒ is_accepting_exec (nfa_plus M) qs w
Proof
  rw [is_accepting_exec_def, nfa_plus_def,is_exec_def] >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Similar to the pasting theorem for nfa_dot. The difference is that, for   *)
(* nfa_kplus, there's only one machine, which loops back from final states   *)
(* to the successors of the start state.                                     *)
(*---------------------------------------------------------------------------*)

Theorem is_accepting_exec_nfa_plus_paste:
  is_dfa M ∧
  w1 ≠ ε ∧ w2 ≠ ε ∧
  is_accepting_exec (nfa_plus M) qs1 w1 ∧
  is_accepting_exec M qs2 w2
  ⇒
  is_accepting_exec (nfa_plus M) (qs1 ++ TL qs2) (w1 ++ w2)
Proof
  rw [is_accepting_exec_def] >>
  ‘wf_nfa M ∧ wf_nfa (nfa_plus M)’ by
     metis_tac [is_dfa_def,wf_nfa_plus] >>
  ‘EVERY (λq. q ∈ (nfa_plus M).Q) qs1 ∧ EVERY (λq. q ∈ M.Q) qs2’ by
     metis_tac [is_dfa_def,is_exec_states] >>
  ‘qs1 ≠ [] ∧ qs2 ≠ []’ by
     metis_tac [is_exec_nonempty] >>
  ‘TL qs2 ≠ []’ by
     metis_tac [is_accepting_exec_length,is_accepting_exec_def,is_dfa_def] >>
  rw [is_exec_def]
  >- fs [is_exec_def]
  >- fs [is_exec_def]
  >- (imp_res_tac is_exec_length >> rw[LENGTH_TL])
  >- metis_tac [is_dfa_def,wf_nfa_def,SUBSET_DEF]
  >- (‘n < LENGTH w1 ∨ n = LENGTH w1 ∨ LENGTH w1 < n’ by decide_tac
      >- (rev_drule is_exec_Sigma >> simp[] >> rw[EVERY_EL] >>
          rev_drule is_exec_length >> strip_tac >>
          ‘n < LENGTH qs1’ by decide_tac >> ‘n+1 < LENGTH qs1’ by decide_tac >>
          rw[EL_APPEND1] >>metis_tac [is_exec_delta,is_dfa_def])
      >- (rw[] >> rfs[] >> rev_drule is_exec_length >>
          disch_then(assume_tac o SYM) >> ONCE_ASM_REWRITE_TAC[] >>
          rw[SRULE [NULL_EQ] EL_LENGTH_APPEND] >>
          ‘LENGTH w1 < LENGTH qs1’ by decide_tac >> rw [EL_APPEND1] >>
          ‘LENGTH w1 = PRE (LENGTH qs1)’ by decide_tac >> pop_subst_tac >>
          rw [EL_PRE_LENGTH] >> rw [nfa_plus_def,PULL_EXISTS] >>
          disj2_tac >> rfs [is_dfa_def,NOT_NIL_EQ_LENGTH_NOT_0] >> rw[] >>
          ‘0 < LENGTH w1’ by decide_tac >> PURE_REWRITE_TAC[GSYM EL] >>
          drule is_exec_delta >> disch_then drule >> simp[] >> rfs[])
      >- (‘∃k. 0 < k ∧ k < LENGTH w2 ∧ n = LENGTH w1 + k’
            by (qexists_tac ‘n - LENGTH w1’ >> fs[]) >> rw[EL_APPEND2_ALT] >>
          rev_drule is_exec_length >> disch_tac >>
          ‘k + (LENGTH w1 + 1) = LENGTH qs1 + k’ by decide_tac >> pop_subst_tac >>
          drule is_exec_length >> disch_tac >>
          ‘k < LENGTH (TL qs2)’ by
             (‘k + 1 < LENGTH qs2’ by decide_tac >>
              drule LENGTH_TL_ALT >> rw[]) >>
          ‘k < LENGTH qs2’ by decide_tac >>
          rw[EL_APPEND2_ALT] >> rw[EL_APPEND_EQN] >> rw [nfa_plus_def,PULL_EXISTS]
          >- metis_tac [is_exec_delta]
          >- (disj1_tac >>
             ‘EL k qs2 ∈ M.Q’ by
                metis_tac[is_dfa_def,wf_nfa_def, SUBSET_DEF] >>
             drule is_exec_delta >> disch_then drule >> metis_tac[]))
     )
  >- rw[LAST_APPEND_NOT_NIL]
QED

Theorem is_accepting_exec_nfa_plus_paste_list:
  ∀f qs qslist wlist w.
    (f = λa b c. a ⧺ TL b) ∧
    is_dfa M ∧ w ≠ ε ∧
    EVERY (λw. w ≠ ε) wlist ∧
    is_accepting_exec (nfa_plus M) qs w ∧
    LIST_REL (is_accepting_exec M) qslist wlist
    ⇒
    is_accepting_exec (nfa_plus M)
      (FOLDL2 f qs qslist wlist)
      (FLAT (w::wlist))
Proof
  ho_match_mp_tac FOLDL2_ind >> rw[] >>
  first_x_assum irule >> rw[] >>
  irule is_accepting_exec_nfa_plus_paste >> rw[]
QED

Theorem KPLUS_SUBSET_NFA_PLUS:
  is_dfa M ∧ ε ∉ nfa_lang M
  ⇒
  KPLUS (nfa_lang M) ⊆ nfa_lang (nfa_plus M)
Proof
  rw [SUBSET_DEF] >>
  drule_all (iffLR IN_KPLUS_LIST_EPSILON_FREE) >> rw[] >>
  ‘wf_nfa M ∧ wf_nfa (nfa_plus M)’ by
     metis_tac [is_dfa_def,wf_nfa_plus] >>
  ‘∃qslist. LIST_REL (is_accepting_exec M) qslist wlist’ by
     (fs [in_nfa_lang_iff_accepting_exec,EVERY_EL,SUBSET_SKOLEM_THM] >>
      qexists_tac ‘GENLIST f (LENGTH wlist)’ >> rw[LIST_REL_EL_EQN]) >>
  ‘qslist ≠ []’ by
     (Cases_on ‘qslist’ >> fs[]) >>
  ‘EVERY (λqs. qs ≠ []) qslist’ by
     (rw [EVERY_EL] >> fs[LIST_REL_EL_EQN,is_accepting_exec_def] >>
      metis_tac [is_exec_nonempty]) >>
  ‘EVERY (λqs. TL qs ≠ []) qslist’ by
     (fs [EVERY_EL,LIST_REL_EL_EQN,is_accepting_exec_def] >>
      metis_tac [is_exec_tl_nonempty]) >>
  ‘EVERY (λw. w ≠ ε) wlist’ by
     (fs [EVERY_EL] >> rw[] >> metis_tac[]) >>
  ‘LENGTH qslist = LENGTH wlist’ by
     metis_tac [LIST_REL_LENGTH] >>
  rw [in_nfa_lang_iff_accepting_exec] >>
  qexists_tac
    ‘FOLDL2 (λa b c. a ++ TL b)
       (HD qslist) (TL qslist) (TL wlist)’ >>
  ‘∃qs qslist'. qslist = qs::qslist'’ by (Cases_on‘qslist’ >> fs[]) >>
  ‘∃w wlist'. wlist = w::wlist'’ by (Cases_on ‘wlist’ >> fs[]) >> rw[] >> fs[] >>
  drule is_accepting_exec_nfa_plus >> rw_tac bool_ss [Once (GSYM FLAT)] >>
  irule is_accepting_exec_nfa_plus_paste_list >> rw[]
QED

(*
Triviality SPLITP_EXISTS:
  EXISTS P list ⇒ ∃prefix h t. SPLITP P list = (prefix,h::t)
Proof
  Induct_on ‘list’ >> rw[SPLITP] >> gvs[]
QED

Theorem zip_expand_id:
 ZIP (MAP FST plist, MAP SND plist) = plist
Proof
 Induct_on ‘plist’ >> rw[]
QED

Theorem pair_list_as_zip:
  ∀plist:('a # 'b) list. ∃l1 l2. LENGTH l1 = LENGTH l2 ∧ plist = ZIP (l1,l2)
Proof
 Induct_on ‘plist’ >> rw[]
 >- (ntac 2 (qexists_tac ‘[]’) >> rw[])
 >- (namedCases_on ‘h’ ["a b"] >>
     qexists_tac ‘a::l1’ >> qexists_tac ‘b::l2’ >> rw[])
QED

Triviality UNZIP_APPEND:
 ∀L1 L2. UNZIP (L1 ++ L2) = (FST (UNZIP L1) ++ FST (UNZIP L2),
                             SND (UNZIP L1) ++ SND (UNZIP L2))
Proof
 Induct >> rw[]
QED

Theorem ZIP_EQ_NIL_OR:
 ZIP(l1,l2) = [] ⇔ l1 = [] ∨ l2 = []
Proof
 Induct_on ‘l1’ >> Induct_on ‘l2’ >> rw[ZIP_def]
QED


*)

Triviality nfa_plus_diff:
  is_dfa M ∧
  a ∈ M.Sigma ∧
  q2 ∈ (nfa_plus M).delta q1 a ∧
  q2 ∉ M.delta q1 a ⇒
  q1 ∈ M.final ∧ BIGUNION {M.delta q0 a | q0 | q0 ∈ M.initial} = {q2}
Proof
  rw [is_dfa_def,nfa_plus_def] >> rfs[] >> rw[] >>
  rename1 ‘q2 ∈ M.delta q0 a’ >>
  rw [EXTENSION,EQ_IMP_THM]
  >- (‘∃q'. M.delta q0 a = {q'}’ by
        metis_tac [wf_nfa_def,SUBSET_DEF,IN_INSERT] >> gvs[])
  >- metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* One step of splitting an "nfa_plus(M)" execution into a leading "M"       *)
(* execution followed by either (A) an empty execution, or, (B) by another   *)
(* nfa_plus(M) execution. Note the start state has to be attached before the *)
(* tail nfa_plus(M) execution becomes well-formed.                           *)
(*                                                                           *)
(* Subtlety: cronch splits off the longest M-execution possible.             *)
(*---------------------------------------------------------------------------*)

Definition cronch_def:
  cronch M [] [] = ([],[],[],[]) ∧
  cronch M [a] [q] = ([a],[],[q],[]) ∧
  cronch M (a::b::w) (q1::q2::qs) =
     if q2 ∈ M.delta q1 b then
       (case cronch M (b::w) (q2::qs)
         of (wpref,wsuff,qpref,qsuff) =>
            (a::wpref, wsuff, q1::qpref, qsuff))
     else ([a], b::w, [q1], q2::qs)
End

Triviality cronch_splits_input:
 ∀M w qs wpref wsuff qpref qsuff.
   LENGTH qs = LENGTH w ∧
   cronch M w qs = (wpref,wsuff,qpref,qsuff)
   ⇒
   wpref ++ wsuff = w ∧
   qpref ++ qsuff = qs ∧
   LENGTH wpref = LENGTH qpref ∧
   LENGTH wsuff = LENGTH qsuff
Proof
  recInduct cronch_ind >>
  rw [cronch_def,AllCaseEqs()] >> simp[]
QED

Triviality cronch_consumes_lem:
 ∀M w qs wpref wsuff qpref qsuff a q w' qs'.
   LENGTH qs = LENGTH w ∧
   w = a::w' ∧ qs = q::qs' ∧
   cronch M w qs = (wpref,wsuff,qpref,qsuff)
   ⇒
   ∃wpref' qpref'.  wpref = a::wpref' ∧ qpref = q::qpref'
Proof
  recInduct cronch_ind >> rw [cronch_def,AllCaseEqs()]
QED

Theorem cronch_consumes = cronch_consumes_lem |> SRULE[];

(*---------------------------------------------------------------------------*)
(* Given |- ∀xs. P ⇒ Q1 ∧ Q2, return |- ∀xs. P ⇒ Q1 and |- ∀xs. P ⇒ Q2       *)
(*---------------------------------------------------------------------------*)

fun fst_conj th =
 let val (xs,t) = strip_forall(concl th)
     val ant = fst(dest_imp t)
     val th1 = CONJUNCT1(UNDISCH(SPEC_ALL th))
 in
   GENL xs (DISCH ant th1)
 end

fun snd_conj th =
 let val (xs,t) = strip_forall(concl th)
     val ant = fst(dest_imp t)
     val th1 = CONJUNCT2(UNDISCH(SPEC_ALL th))
 in
   GENL xs (DISCH ant th1)
 end

Theorem cronch_exec:
 ∀M w qs q0 wpref wsuff qpref qsuff.
   is_dfa M ∧
   M.initial = {q0} ∧
   w ≠ ε ∧
   LAST qs ∈ M.final ∧
   is_exec (nfa_plus M) qs (TL w) ∧
   cronch M w qs = (wpref,wsuff,qpref,qsuff)
   ⇒
     is_exec M qpref (TL wpref) ∧
     LAST qpref ∈ M.final ∧
     (qsuff = [] ∨ is_exec (nfa_plus M) (q0::qsuff) wsuff)
Proof
  recInduct cronch_ind >> simp [] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_tac)
  >~ [‘cronch M (a::b::w) (q1::q2::qs) = (wpref,wsuff,qpref,qsuff)’]
  >- (pop_keep_tac >> simp [cronch_def,AllCaseEqs(),PULL_EXISTS] >>
      rw[] >> gvs[]
      >- (‘LENGTH qs = LENGTH w’ by gvs[is_exec_def] >>
          imp_res_tac cronch_consumes >> rw[] >> gvs[] >>
          irule is_exec_extend_left >> gvs [is_dfa_def] >>
          drule is_exec_Sigma >> rw[]
          >- gvs [is_exec_def]
          >- (first_x_assum (irule_at Any o fst_conj) >>
              irule (snd_conj is_exec_step_left) >> metis_tac [wf_nfa_plus]))
      >- (‘LENGTH qs = LENGTH w’ by gvs[is_exec_def] >>
          imp_res_tac cronch_consumes >> rw[] >> gvs[] >>
          first_x_assum (irule_at Any o fst_conj o snd_conj) >>
          irule (snd_conj is_exec_step_left) >>
          metis_tac [is_dfa_def,wf_nfa_plus])
      >- (first_x_assum (irule_at Any o snd_conj o snd_conj) >>
          irule (snd_conj is_exec_step_left) >>
          metis_tac [is_dfa_def,wf_nfa_plus])
      >- gvs [is_exec_def]
      >- (gvs [is_exec_def,nfa_plus_def] >>
          ‘0 < SUC (LENGTH w)’ by decide_tac >>
          first_x_assum drule >> simp[] >> rw[])
      >- (‘LENGTH w = LENGTH qs’ by gvs[is_exec_def] >>
          ‘wf_nfa (nfa_plus M)’ by metis_tac [wf_nfa_plus,is_dfa_def] >>
          imp_res_tac is_exec_step_left >>
          ‘b ∈ M.Sigma’ by gvs [is_exec_def] >>
          irule is_exec_extend_left >> rw[]
          >- metis_tac [IN_INSERT,SUBSET_DEF,wf_nfa_def,is_dfa_def]
          >- (‘b ∈ M.Sigma’ by gvs [is_exec_def] >>
              drule_all nfa_plus_diff >> rw[nfa_plus_def] >>
              irule (iffRL ELT_SUBSET) >> pop_sym_subst_tac >>
              simp[SUBSET_DEF])))
  >> gvs[cronch_def, is_exec_def]
QED

Theorem cronch_accepting_exec:
   is_dfa M ∧ M.initial = {q0} ∧ w ≠ ε ∧
   is_accepting_exec (nfa_plus M) qs (TL w) ∧
   cronch M w qs = (wprefix,wsuffix,qprefix,qsuffix)
   ⇒
   is_accepting_exec M qprefix (TL wprefix) ∧
   (qsuffix = [] ∨ is_accepting_exec (nfa_plus M) (q0::qsuffix) wsuffix)
Proof
 rw[is_accepting_exec_def] >>
 ‘LENGTH qs = LENGTH w’ by
   (Cases_on ‘w’ >> Cases_on ‘qs’ >> gvs[is_exec_def]) >>
 drule_all cronch_exec >>
 rpt CASE_TAC >> rw[]
 >- (Cases_on ‘qs’ >> Cases_on ‘w’ >> gvs[is_exec_def] >>
     drule_all cronch_consumes >> rw[] >> gvs[])
 >- (Cases_on ‘qs’ >> Cases_on ‘w’ >> gvs[is_exec_def] >>
     drule_all cronch_consumes >> rw[] >> gvs[])
 >- (Cases_on ‘qsuffix’ >> simp[] >>
     drule_all cronch_splits_input >> rw[] >>
     metis_tac [NOT_CONS_NIL,LAST_APPEND_NOT_NIL,APPEND_ASSOC,APPEND])
QED

Triviality cronch_accepting_exec_alt:
  is_dfa M ∧ M.initial = {q0} ∧ is_accepting_exec (nfa_plus M) qs w ∧
  cronch M (ARB::w) qs = (wprefix,wsuffix,qprefix,qsuffix)
  ⇒
  is_accepting_exec M qprefix (TL wprefix) ∧
  (qsuffix = [] ∨ is_accepting_exec (nfa_plus M) (q0::qsuffix) wsuffix)
Proof
 ACCEPT_TAC
 (cronch_accepting_exec
     |> Q.INST [‘w’ |-> ‘ARB::w’]
     |> SRULE[])
QED

(*---------------------------------------------------------------------------*)
(* Termination: the input gets smaller since an M-execution (which must have *)
(* at least two states) is removed each time.                                *)
(*---------------------------------------------------------------------------*)

Theorem epsilon_free_accepting_exec_length:
   wf_nfa N ∧ ε ∉ nfa_lang N ∧
   is_accepting_exec N qs w
   ⇒
   ∃q1 q2 qs'. qs = q1::q2::qs'
Proof
  rw[] >> gvs [in_nfa_lang_iff_accepting_exec] >>
  ‘w ≠ ε’ by metis_tac[] >>
  metis_tac[epsilon_free_exec_left_cons,is_accepting_exec_def]
QED

Definition cronch_all_def:
  cronch_all M q0 w qs =
    if is_dfa M ∧ ε ∉ nfa_lang M ∧
       is_accepting_exec (nfa_plus M) qs w
   then
    (case cronch M (ARB::w) qs of (wprefix,wsuffix,qprefix,qsuffix)
      => if qsuffix = [] then
           ([TL wprefix],[qprefix])
         else
          case cronch_all M q0 wsuffix (q0::qsuffix)
           of (wprefixes,qprefixes) => (TL wprefix::wprefixes, qprefix::qprefixes))
  else
    ARB
Termination
  WF_REL_TAC ‘measure (λ(a,b,c,d). LENGTH d)’ >> rw[] >>
  rename1 ‘cronch M (ARB::w) qs = (wprefix,wsuffix,qprefix,qsuffix)’ >>
  ‘∃q0. M.initial = {q0}’ by metis_tac [is_dfa_def] >>
  imp_res_tac (cronch_accepting_exec_alt |> fst_conj) >>
  ‘∃q1 q2 qs'. qprefix = q1::q2::qs'’ by
     metis_tac [epsilon_free_accepting_exec_length,is_dfa_def] >>
  ‘LENGTH qs = LENGTH (ARB::w)’ by gvs [is_accepting_exec_def,is_exec_def] >>
  drule_all cronch_splits_input >> rw[] >> gvs[]
End

Theorem cronch_all_thm:
  ∀M q0 w qs wslist qslist.
  is_dfa M ∧ M.initial = {q0} ∧
  ε ∉ nfa_lang M ∧
  is_accepting_exec (nfa_plus M) qs w ∧
  cronch_all M q0 w qs = (wslist,qslist)
  ⇒
  LIST_REL (is_accepting_exec M) qslist wslist ∧
  w = FLAT wslist ∧
  wslist ≠ []
Proof
  recInduct cronch_all_ind >> rw[] >> fs[] >> pop_keep_tac >>
  rw [Once cronch_all_def,AllCaseEqs(),PULL_EXISTS] >> fs[] >>
  drule_all cronch_accepting_exec_alt >> rw[] >>
  ‘LENGTH qs = LENGTH (ARB::w)’ by
    gvs [is_accepting_exec_def,is_exec_def] >>
  imp_res_tac cronch_splits_input >> gvs[] >>
  qpat_x_assum ‘wprefix ⧺ FLAT wprefixes = ARB::w’
    (SUBST1_TAC o SYM o SRULE[] o Q.AP_TERM ‘TL’) >> rw[] >>
  irule TL_APPEND >>
  ‘∃q1 q2 qs'. qprefix = q1::q2::qs'’ by
    metis_tac[epsilon_free_accepting_exec_length,is_dfa_def] >> rw[] >>
  Cases_on ‘wprefix’ >> gvs[]
QED

Theorem nfa_plus_exec_to_nfa_execs:
  is_dfa M ∧
  ε ∉ nfa_lang M ∧
  is_accepting_exec (nfa_plus M) qs w
  ⇒
  ∃qslist wlist.
    LIST_REL (is_accepting_exec M) qslist wlist ∧
    w = FLAT wlist ∧
    wlist ≠ []
Proof
  metis_tac [cronch_all_thm,ABS_PAIR_THM,is_dfa_def]
QED

Triviality LIST_REL_EVERY:
  LIST_REL R l1 l2 ⇒ EVERY (λx. ∃y. R x y) l1
Proof
  rw[EVERY_MEM] >> drule_all LIST_REL_MEM_IMP >> metis_tac[]
QED

Triviality LIST_REL_EVERY_R:
  LIST_REL R l1 l2 ⇒ EVERY (λy. ∃x. R x y) l2
Proof
  rw[EVERY_MEM] >> drule_all LIST_REL_MEM_IMP_R >> metis_tac[]
QED

Theorem NFA_PLUS_SUBSET_KPLUS:
  is_dfa M ∧ ε ∉ nfa_lang M
  ⇒
  nfa_lang (nfa_plus M) ⊆ KPLUS (nfa_lang M)
Proof
  strip_tac >> simp[SUBSET_DEF] >>
  ‘wf_nfa M ∧ wf_nfa (nfa_plus M)’ by
     metis_tac [is_dfa_def,wf_nfa_plus] >>
  rw [in_nfa_lang_iff_accepting_exec] >>
  rw [IN_KPLUS_LIST] >>
  rw [in_nfa_lang_iff_accepting_exec] >>
  drule_all nfa_plus_exec_to_nfa_execs >> rw[] >>
  first_x_assum (irule_at Any) >> rw[] >>
  metis_tac [LIST_REL_EVERY_R]
QED

Theorem REGULAR_CLOSED_UNDER_EPSILON_FREE_KPLUS:
  ε ∉ L ∧ (L,A) ∈ REGULAR ⇒ (KPLUS L, A) ∈ REGULAR
Proof
  disch_then (strip_assume_tac o SRULE [IN_REGULAR_AS_DFA]) >> rw[] >>
  rw [IN_REGULAR] >> qexists_tac ‘nfa_plus M’ >> rpt conj_tac
  >- rw [nfa_plus_def]
  >- metis_tac[wf_nfa_plus,is_dfa_def]
  >- metis_tac [SET_EQ_SUBSET, KPLUS_SUBSET_NFA_PLUS, NFA_PLUS_SUBSET_KPLUS]
QED

Theorem REGULAR_CLOSED_UNDER_KSTAR:
  (L,A) ∈ REGULAR ⇒ (KSTAR L,A) ∈ REGULAR
Proof
  strip_tac >>
  strip_assume_tac (isolate_trivial_cases |> Q.ISPEC ‘L:num list->bool’) >>
  rename1 ‘s ⊆ {ε}’ >> ONCE_ASM_REWRITE_TAC[] >>
  rw [KSTAR_UNION,KSTAR_TRIVIAL,DOT_EPSILON] >>
  rw [GSYM KPLUS_UNION_EPSILON_EQ_KSTAR] >>
  irule REGULAR_CLOSED_UNDER_UNION >> reverse conj_tac
  >- metis_tac [EPSILON_LANG_IN_REGULAR,REGULAR_SIGMA_FINITE]
  >- (irule REGULAR_CLOSED_UNDER_EPSILON_FREE_KPLUS >> rw[] >>
      metis_tac [REGULAR_CLOSED_UNDER_EPSILON_DELETION])
QED

Theorem REGULAR_CLOSED_UNDER_KPLUS:
  (L,A) ∈ REGULAR ⇒ (KPLUS L,A) ∈ REGULAR
Proof
  Cases_on ‘ε ∈ L’
  >- metis_tac [KPLUS_EQ_KSTAR,REGULAR_CLOSED_UNDER_KSTAR]
  >- metis_tac [REGULAR_CLOSED_UNDER_EPSILON_FREE_KPLUS]
QED

(*===========================================================================*)
(* The Regular languages coincide with the Finite State languages.           *)
(*===========================================================================*)

Definition nfa_lang_from_def:
  nfa_lang_from N qset = nfa_lang (N with <| initial := qset |>)
End

Triviality finite_image_states:
  wf_nfa N ⇒ FINITE{f N qset | qset | qset ⊆ N.Q}
Proof
  rw [GSPEC_IMAGE, o_DEF,LAMBDA_PROD,wf_nfa_def] >>
  irule IMAGE_FINITE >> irule SUBSET_FINITE >>
  qexists_tac ‘POW N.Q’ >> conj_tac
  >- metis_tac [FINITE_POW]
  >- rw[SUBSET_DEF,POW_DEF]
QED

Theorem FOLDL_IND:
  ∀P. (∀f a. P f a []) ∧
      (∀f a h t. P f (f a h) t ⇒ P f a (h::t))
       ⇒
      ∀f a l. P f a l
Proof
  gen_tac >> strip_tac >> Induct_on ‘l’  >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Evaluate an NFA from a set of states                                      *)
(*---------------------------------------------------------------------------*)

Definition nfa_eval_foldl_def:
  nfa_eval N qset w =
    FOLDL (λfringe a. BIGUNION {N.delta q a | q | q ∈ fringe}) qset w
End

Theorem nfa_eval_eqns:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (BIGUNION {N.delta q a | q | q ∈ qset}) w
Proof
 rw [nfa_eval_foldl_def]
QED

Theorem nfa_eval_states_foldl:
  ∀f qset w.
   wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ∧
   f = (λfringe a. BIGUNION {N.delta q a | q | q ∈ fringe})
   ⇒
   FOLDL f qset w ⊆ N.Q
Proof
  recInduct FOLDL_IND >> rw[] >> gvs[] >>
  first_x_assum irule >> rw [SUBSET_DEF] >>
  metis_tac [wf_nfa_def,SUBSET_DEF]
QED

Theorem nfa_eval_states_closed:
   wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
   ⇒
   nfa_eval N qset w ⊆ N.Q
Proof
  rw[nfa_eval_foldl_def, nfa_eval_states_foldl |> SRULE[]]
QED

Theorem dfa_eval_states_closed:
   is_dfa M ∧ EVERY (λa. a ∈ M.Sigma) w
   ⇒
   ∀q. nfa_eval M M.initial w = {q} ⇒ q ∈ M.Q
Proof
  rw[is_dfa_def] >>
  ‘M.initial ⊆ M.Q’ by metis_tac [wf_nfa_def] >>
  drule_all nfa_eval_states_closed >>
  rw[]
QED

Theorem nfa_eval_append:
 ∀w1 w2 qset.
    wf_nfa N ∧
    EVERY (λa. a ∈ N.Sigma) w1 ∧
    EVERY (λa. a ∈ N.Sigma) w2 ∧
    qset ⊆ N.Q
    ⇒
   nfa_eval N qset (w1 ++ w2) = nfa_eval N (nfa_eval N qset w1) w2
Proof
  Induct >> rw [nfa_eval_eqns] >>
  first_x_assum irule >>
  simp[BIGUNION_SUBSET,PULL_EXISTS] >>
  metis_tac[wf_nfa_def,SUBSET_DEF]
QED

(*---------------------------------------------------------------------------*)
(* NB: decent test for rewrite-enhanced irule                                *)
(*---------------------------------------------------------------------------*)

Theorem dfa_eval_final_state:
  ∀w. is_dfa M ∧
      EVERY (λa. a ∈ M.Sigma) w
      ⇒
      ∃q. nfa_eval M M.initial w = {q}
Proof
  recInduct SNOC_INDUCT >>
  rw[is_dfa_def,nfa_eval_eqns,SNOC_APPEND] >>
  gvs[] >> rename1 ‘a ∈ N.Sigma’ >>
  ‘EVERY (λa. a ∈ N.Sigma) [a]’ by rw[] >>
  ‘{q_0} ⊆ N.Q’ by metis_tac[wf_nfa_def] >>
  rw[nfa_eval_append] >>
  rev_drule_all nfa_eval_states_closed >> rw[] >>
  ‘∃q'. N.delta q a = {q'}’ by metis_tac[] >>
  qexists_tac ‘q'’ >>
  rw [nfa_eval_eqns,EXTENSION,EQ_IMP_THM]
  >- metis_tac[]
  >- (qexists_tac ‘{q'}’ >> rw[])
QED

(* NB: The statement of this "Theorem" is not true: nfa_eval relies on
   the input word having all its symbols drawn from the alphabet. The
   N.delta q a transition is not defined when a is not in the alphabet. But,
   in HOL such an expression has a "value"---an unspecified value---which,
   typically, doesn't have enough info to push proofs ahead.

Theorem nfa_eval_Sigma:
  ∀w. wf_nfa N ∧ w ∉ KSTAR{[a] | a ∈ N.Sigma}
       ⇒
      nfa_eval N qset w = ∅
Proof
QED
 *)

(*---------------------------------------------------------------------------*)
(* Relationship of nfa evaluation and is_exec. Say the fringe is the set of  *)
(* states the nfa could be in after processing w: it is the leaves of the    *)
(* nfa-computation tree rooted at qset. Then, every exec-path for w starting *)
(* in qset ends in the fringe, and every element of the fringe is at the end *)
(* of a path starting in qset.                                               *)
(*---------------------------------------------------------------------------*)

Theorem nfa_eval_is_exec:
  ∀w qset.
  wf_nfa N ∧ qset ⊆ N.Q ∧ EVERY (λa. a ∈ N.Sigma) w
   ⇒
  nfa_eval N qset w = {LAST qs | qs | is_exec N qs w ∧ HD qs ∈ qset}
Proof
  recInduct SNOC_INDUCT >> rw[] >> gvs[]
  >- (gvs [nfa_eval_eqns,is_exec_epsilon] >>
     rw[EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
     metis_tac[SUBSET_DEF])
  >- (rename1 ‘SNOC a w’ >>
      gvs[SNOC_APPEND] >> first_x_assum drule >>
      rw[nfa_eval_append,nfa_eval_eqns] >> pop_forget_tac >>
      rw[EXTENSION,PULL_EXISTS] >> eq_tac >> rpt strip_tac
      >- (rename1 ‘q ∈ s’ >>
          ‘q ∈ N.delta (LAST qs) a’ by metis_tac[] >>
          drule_all (iffLR is_exec_delta_step) >>
          metis_tac [LAST_APPEND,LAST_DEF,HD_APPEND,is_exec_nonempty])
      >- (rw[] >>
          strip_assume_tac (Q.ISPEC ‘qs:num list’ SNOC_CASES)
          >- metis_tac[is_exec_nonempty]
          >- (rename1 ‘qs = SNOC q qs'’ >>
              rw[] >> gvs [SNOC_APPEND] >>
              gvs [GSYM is_exec_delta_step] >>
              simp [Once SWAP_EXISTS_THM] >>
              qexists_tac ‘qs'’ >> simp[] >>
              qexists_tac ‘N.delta (LAST qs') a’ >> simp[] >>
              drule is_exec_nonempty >> strip_tac >>
              Cases_on ‘qs'’ >> gvs[] >> metis_tac [HD])))
QED

Theorem in_nfa_lang_nfa_eval:
  wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w
  ⇒
  (w ∈ nfa_lang N ⇔ nfa_eval N N.initial w ∩ N.final ≠ ∅)
Proof
  rpt strip_tac >>
  rw [in_nfa_lang_iff_accepting_exec, is_accepting_exec_def] >>
  gvs[wf_nfa_def, nfa_eval_is_exec, EXTENSION] >> metis_tac[]
QED

Theorem in_nfa_lang_nfa_eval_alt:
  wf_nfa N
   ⇒
  (w ∈ nfa_lang N
   ⇔
   EVERY (λa. a ∈ N.Sigma) w ∧
   nfa_eval N N.initial w ∩ N.final ≠ ∅)
Proof
  rw [EQ_IMP_THM]
  >- gvs [in_nfa_lang]
  >- (‘EVERY (λa. a ∈ N.Sigma) w’ by gvs [in_nfa_lang] >>
      gvs [in_nfa_lang_iff_accepting_exec, is_accepting_exec_def] >>
      ‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
      gvs[nfa_eval_is_exec, EXTENSION] >> metis_tac[])
  >- (‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
      gvs[nfa_eval_is_exec, EXTENSION] >>
      gvs [in_nfa_lang_iff_accepting_exec, is_accepting_exec_def] >> metis_tac[])
QED

(* TODO : strengthen to

  w2 ∈ nfa_lang_from N (nfa_eval N qset w1) iff
  (w1++w2) ∈ nfa_lang_from N qset
*)

Theorem nfa_eval_lemma:
  qset ⊆ N.Q ∧
  a ∈ N.Sigma ∧ EVERY (λa. a ∈ N.Sigma) w
  ⇒
   (w ∈ nfa_lang_from N (nfa_eval N qset [a])
    ⇔
   (a::w) ∈ nfa_lang_from N qset)
Proof
  rw [nfa_lang_from_def,nfa_eval_eqns] >>
  rw [EQ_IMP_THM,in_nfa_lang]
  >- (qexists_tac ‘q::qs’ >> rw[]
      >- (‘qs ≠ []’ by (Cases_on ‘qs’ >> gvs[]) >> rw [LAST_CONS_cond])
      >- (rw [GSYM ADD1] >> Cases_on ‘n’ >> gvs[] >> metis_tac [ADD1]))
  >- (‘∃q1 q2 t. qs = q1::q2::t’ by
        (Cases_on ‘qs’ >> gvs[GSYM ADD1] >> Cases_on ‘t’ >> gvs[]) >>
      rw[] >> gvs[GSYM ADD1] >>
      qexists_tac ‘q2::t’ >> rw[PULL_EXISTS] >> gvs[]
      >- metis_tac[SUC_POS,EL,HD]
      >- (‘SUC n < SUC (LENGTH w)’ by decide_tac >>
          first_x_assum drule >> simp[]))
QED

(*---------------------------------------------------------------------------*)
(* Relationship of nfa evaluation, is_exec, and left quotients.              *)
(*---------------------------------------------------------------------------*)

Theorem nfa_lang_left_quotient:
  ∀w.
   wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w
   ⇒
    nfa_lang (N with <| initial := nfa_eval N N.initial w |>)
     =
    LEFT_QUOTIENT w (nfa_lang N)
Proof
  recInduct SNOC_INDUCT >>
  rw[nfa_eval_eqns] >> gvs [EVERY_SNOC] >>
  rw [SNOC_APPEND,LEFT_QUOTIENT_APPEND] >>
  qpat_x_assum ‘_ = _’ sym_subst_all_tac >>
  rw [LEFT_QUOTIENT_def,EXTENSION] >>
  rename1 ‘w2 ∈ nfa_lang (N with initial := nfa_eval _ _ (w1 ++ [a]))’ >>
  ‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
  rw [nfa_eval_append] >>
  reverse (Cases_on ‘EVERY (λa. a ∈ N.Sigma) w2’) >- rw [in_nfa_lang] >>
  irule (nfa_eval_lemma |> SRULE [nfa_lang_from_def]) >> simp[] >>
  irule nfa_eval_states_closed >> simp[]
QED

Theorem REGULAR_SUBSET_FINITE_STATE:
  REGULAR ⊆ FINITE_STATE
Proof
  rw [SUBSET_DEF, IN_REGULAR, FORALL_PROD, INTRINSIC_STATES_def]
  >- gvs[wf_nfa_def]
  >- gvs[in_nfa_lang]
  >- (irule SUBSET_FINITE >>
      qexists_tac ‘{nfa_lang_from N qset | qset | qset ⊆ N.Q}’ >> rw[]
      >- (irule finite_image_states >> metis_tac [])
      >- (rw [SUBSET_DEF,nfa_lang_from_def] >>
          irule_at Any (GSYM nfa_lang_left_quotient) >> simp[] >>
          metis_tac [SUBSET_DEF,nfa_eval_states_closed,wf_nfa_def]))
QED

(*---------------------------------------------------------------------------*)
(* To show that every finite state language L is regular, we assume that the *)
(* set of left quotients on L, drawing the words from A*, is finite. These   *)
(* left quotients become states in the construction of an NFA (actually a    *)
(* DFA). A delta step in the NFA is made by taking the left quotient on the  *)
(* next symbol in the given word. This construction, where states are        *)
(* languages, can't directly be captured by the nfa datatype, in which a     *)
(* state is a number. Since the state set is by assumption finite, we can    *)
(* nonetheless proceed by creating a bijection to a finite set of numbers    *)
(* and working through the bijection.                                        *)
(*---------------------------------------------------------------------------*)

Triviality LEFT_QUOTIENTS_OF_CONS:
  ∃t. LEFT_QUOTIENTS_OF x L = L::t
Proof
  Cases_on ‘x’ >> simp[LEFT_QUOTIENTS_OF_def]
QED

Triviality LENGTH_LEFT_QUOTIENTS_OF:
  ∀x L. LENGTH (LEFT_QUOTIENTS_OF x L) = LENGTH x + 1
Proof
  Induct >> simp[LEFT_QUOTIENTS_OF_def]
QED

Triviality LAST_LEFT_QUOTIENTS_OF:
  ∀x L.
  LAST(LEFT_QUOTIENTS_OF x L) = LEFT_QUOTIENT x L
Proof
  Induct >>
  rw[LEFT_QUOTIENTS_OF_def,LEFT_QUOTIENT_REC,LAST_CONS_cond] >>
  dty_metis_tac [LEFT_QUOTIENTS_OF_CONS]
QED

Triviality LEFT_QUOTIENTS_OF_TAKE:
  ∀x n L.
    n < LENGTH x
    ⇒
    EL n (LEFT_QUOTIENTS_OF x L) = LEFT_QUOTIENT (TAKE n x) L
Proof
  Induct >> rw[LEFT_QUOTIENTS_OF_def] >>
  Cases_on ‘n’ >> gvs[LEFT_QUOTIENT_REC]
QED

Triviality EL_LEFT_QUOTIENTS_OF:
  ∀x n L.
    n < LENGTH x ⇒
    EL (SUC n) (LEFT_QUOTIENTS_OF x L) =
    LEFT_QUOTIENT [EL n x] (EL n (LEFT_QUOTIENTS_OF x L))
Proof
  Induct >> rw[LEFT_QUOTIENTS_OF_def] >>
  Cases_on ‘n’ >> gvs[] >> dty_metis_tac [LEFT_QUOTIENTS_OF_CONS,HD]
QED

Theorem FINITE_STATE_SUBSET_REGULAR:
  FINITE_STATE ⊆ REGULAR
Proof
  rw [SUBSET_DEF, IN_REGULAR, FORALL_PROD, INTRINSIC_STATES_def] >>
  rename1 ‘FINITE {LEFT_QUOTIENT w L | EVERY (λa. a ∈ A) w}’ >>
  qabbrev_tac ‘Qlangs = {LEFT_QUOTIENT w L | EVERY (λa. a ∈ A) w}’ >>
  ‘∃langOf k. BIJ langOf (count k) Qlangs’ by metis_tac [FINITE_BIJ_COUNT] >>
  imp_res_tac BIJ_LINV_INV >>
  qabbrev_tac ‘numOf = LINV langOf (count k)’ >>
  ‘INJ numOf Qlangs (count k)’ by
    (imp_res_tac BIJ_LINV_BIJ >> gvs [BIJ_DEF]) >>
  qexists_tac
   ‘<| Sigma := A;
       Q := IMAGE numOf Qlangs;
       initial := {numOf L};
       final   := IMAGE numOf {state | state | state ∈ Qlangs ∧ ε ∈ state};
       delta   := (λq a. {numOf (LEFT_QUOTIENT [a] (langOf q))})
   |>’ >> rw[]
  >- (rw [wf_nfa_def]
      >- (irule_at Any EQ_REFL >> qunabbrev_tac ‘Qlangs’ >> simp[] >>
          metis_tac [LEFT_QUOTIENT_EPSILON,EVERY_DEF])
      >- (irule IMAGE_SUBSET >> rw[SUBSET_DEF])
      >- (rw[] >> irule_at Any EQ_REFL >>
          qunabbrev_tac ‘Qlangs’ >> gvs[] >>
          qexists_tac ‘w ++ [a]’ >>
          simp [LEFT_QUOTIENT_APPEND]))
  >- (rw [EXTENSION,in_nfa_lang,EQ_IMP_THM]
      >- (qexists_tac ‘MAP numOf (LEFT_QUOTIENTS_OF x L)’ >> rw[]
          >- (rpt pop_forget_tac >> map_every qid_spec_tac [‘L’, ‘x’] >>
              Induct >> simp[LEFT_QUOTIENTS_OF_def])
          >- dty_metis_tac[LEFT_QUOTIENTS_OF_CONS,HD_MAP,HD]
          >- (qexists_tac ‘LEFT_QUOTIENT x L’ >>
              simp [GSYM LEFT_QUOTIENT_ELT] >>
              qunabbrev_tac ‘Qlangs’ >> gvs[PULL_EXISTS] >>
              irule_at Any EQ_REFL >> simp[] >>
              dty_metis_tac[LAST_LEFT_QUOTIENTS_OF,LEFT_QUOTIENTS_OF_CONS,LAST_MAP])
          >- (‘n+1 < LENGTH (LEFT_QUOTIENTS_OF x L)’ by rw[LENGTH_LEFT_QUOTIENTS_OF] >>
              rw [EL_MAP] >> AP_TERM_TAC >>
              ‘EL n (LEFT_QUOTIENTS_OF x L) ∈ Qlangs’ by
                (qunabbrev_tac ‘Qlangs’ >> simp[] >>
                 qexists_tac ‘TAKE n x’ >>
                 metis_tac [LEFT_QUOTIENTS_OF_TAKE,EVERY_TAKE]) >>
              simp[] >> metis_tac [EL_LEFT_QUOTIENTS_OF,ADD1])
         )
     >- (rename1 ‘Lx ∈ Qlangs’ >>
         rw_tac bool_ss [Once LEFT_QUOTIENT_ELT] >>
         ‘ε ∈ LAST (LEFT_QUOTIENTS_OF x L)’ suffices_by
           metis_tac [LAST_LEFT_QUOTIENTS_OF] >>
         ‘qs = MAP numOf (LEFT_QUOTIENTS_OF x L)’ by
           (irule LIST_EQ >> simp[LENGTH_LEFT_QUOTIENTS_OF,EL_MAP] >>
            Induct >> rw[]
             >- dty_metis_tac[LEFT_QUOTIENTS_OF_CONS,HD]
             >- (rename1 ‘SUC i < LENGTH x + 1’ >>
                 ‘i < LENGTH x’ by decide_tac >>
                 gvs[GSYM ADD1] >> AP_TERM_TAC >>
                 simp [EL_LEFT_QUOTIENTS_OF] >> AP_TERM_TAC >>
                 simp[LEFT_QUOTIENTS_OF_TAKE] >>
                 ‘LEFT_QUOTIENT (TAKE i x) L ∈ Qlangs’ by
                   (qunabbrev_tac ‘Qlangs’ >> simp[] >>
                    metis_tac [EVERY_TAKE]) >> simp[])) >> rw[] >>
         ‘LEFT_QUOTIENTS_OF x L ≠ []’ by
            dty_metis_tac [LEFT_QUOTIENTS_OF_CONS] >>
         gvs [LAST_MAP,LAST_LEFT_QUOTIENTS_OF] >>
         ‘LEFT_QUOTIENT x L ∈ Qlangs’ by
           (qunabbrev_tac ‘Qlangs’ >> simp[] >> metis_tac[]) >>
         metis_tac [LEFT_QUOTIENT_ELT,INJ_IFF]
      ))
QED

Theorem FINITE_STATE_EQ_REGULAR:
  FINITE_STATE = REGULAR
Proof
  simp[SET_EQ_SUBSET,
       REGULAR_SUBSET_FINITE_STATE,
       FINITE_STATE_SUBSET_REGULAR]
QED

(*===========================================================================*)
(* Myhill-Nerode theorem                                                     *)
(*                                                                           *)
(* This theorem is about various equivalences over A*, and how they relate.  *)
(* The two principal equivalences are based on (1) nfa evaluation and (2)    *)
(* a purely language-level operation (concatenation).                        *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Work with relations relativized to sets, typically A*                     *)
(*---------------------------------------------------------------------------*)

Definition nfa_eval_equiv_def:
  nfa_eval_equiv N x y ⇔
     (nfa_eval N N.initial x = nfa_eval N N.initial y)
End

Definition lang_equiv_def:
 lang_equiv (L,A) x y ⇔
   ∀z. z ∈ KSTAR{[a] | a ∈ A} ⇒ (x ++ z ∈ L ⇔ y ++ z ∈ L)
End

Theorem nfa_eval_equiv_refines_lang_equiv:
  wf_nfa N ∧
  x ∈ KSTAR{[a] | a ∈ N.Sigma} ∧
  y ∈ KSTAR{[a] | a ∈ N.Sigma} ∧
  nfa_eval_equiv N x y
  ⇒
  lang_equiv (nfa_lang N,N.Sigma) x y
Proof
  rw[nfa_eval_equiv_def,lang_equiv_def] >>
  rw [in_nfa_lang_nfa_eval] >>
  ‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
  rw [nfa_eval_append]
QED

Theorem equiv_on_lang_equiv:
  lang_equiv(L,A) equiv_on KSTAR{[a] | a ∈ A}
Proof
  rw[equiv_on_def,lang_equiv_def] >> metis_tac[]
QED

Theorem equiv_on_nfa_eval_equiv:
  (nfa_eval_equiv N) equiv_on KSTAR{[a] | a ∈ N.Sigma}
Proof
  rw[equiv_on_def,nfa_eval_equiv_def] >> metis_tac[]
QED

Definition right_invar_def:
  right_invar U R ⇔
   ∀x y. x ∈ U ∧ y ∈ U ∧ R x y ⇒ ∀z. z ∈ U ⇒ R (x ++ z) (y ++ z)
End

Theorem right_invar_lang_equiv:
  right_invar (KSTAR{[a] | a ∈ A}) (lang_equiv(L,A))
Proof
  rw[right_invar_def,lang_equiv_def] >>
  rw_tac bool_ss [Ntimes(GSYM APPEND_ASSOC) 2] >>
  first_x_assum irule >> rw[]
QED

Theorem right_invar_nfa_eval_equiv:
  wf_nfa N ⇒
  right_invar (KSTAR{[a] | a ∈ N.Sigma}) (nfa_eval_equiv N)
Proof
  rw[right_invar_def,nfa_eval_equiv_def] >>
  ‘N.initial ⊆ N.Q’ by metis_tac[wf_nfa_def] >>
  rw[nfa_eval_append]
QED

Theorem partition_def_alt:
  partition R s = {equiv_class R s x | x | x ∈ s}
Proof
  rw[EXTENSION,partition_def,EQ_IMP_THM,PULL_EXISTS] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Not used here, but perhaps useful somewhere                               *)
(*---------------------------------------------------------------------------*)

Theorem partition_def_as_image:
  partition R s = IMAGE (λx y. y ∈ s ∧ R x y) s
Proof
  rw[partition_def_alt,GSPEC_IMAGE,combinTheory.o_DEF] >>
  simp[IN_DEF,ETA_THM]
QED

(*---------------------------------------------------------------------------*)
(* The set of words that evaluate to the given state. M will be a DFA.       *)
(*---------------------------------------------------------------------------*)

Definition words_of_state_def:
  words_of_state M q =
   {w | w ∈ KSTAR {[a] | a ∈ M.Sigma} ∧ nfa_eval M M.initial w = {q}}
End

Theorem in_words_of_state:
  w ∈ words_of_state N q
   ⇔
  EVERY (λa. a ∈ N.Sigma) w ∧ nfa_eval N N.initial w = {q}
Proof
  rw[words_of_state_def]
QED

Triviality words_of_state_in_partition:
  EVERY (λa. a ∈ M.Sigma) x ∧
  nfa_eval M M.initial x = {q}
  ⇒
  words_of_state M q ∈
    partition (nfa_eval_equiv M) (KSTAR {[a] | a ∈ M.Sigma})
Proof
  rw[words_of_state_def,partition_def_alt] >>
  qexists_tac ‘x’ >>
  rw [nfa_eval_equiv_def,EXTENSION] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* An eval-partition is defined by words_of_state                            *)
(*---------------------------------------------------------------------------*)

Theorem exists_state_class[local]:
   is_dfa M ⇒
    ∀class.
      class ∈ partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma})
      ⇒ ∃q. q ∈ M.Q ∧ class = words_of_state M q
Proof
  rw [partition_def_alt] >>
  rename1 ‘EVERY (λa. a ∈ M.Sigma) w’ >>
  rw [words_of_state_def] >>
  ‘∃q. nfa_eval M M.initial w = {q}’ by
     metis_tac [dfa_eval_final_state] >>
  rw [nfa_eval_equiv_def] >>
  qexists_tac ‘q’ >> rw [EXTENSION] >>
  metis_tac [dfa_eval_states_closed]
QED

Theorem state_of_class_witness[local]:
∃state_of_class.
  ∀M. is_dfa M ⇒
      ∀class.
       class ∈ partition (nfa_eval_equiv M) (KSTAR {[a] | a ∈ M.Sigma})
       ⇒
       state_of_class M class ∈ M.Q ∧
       class = words_of_state M (state_of_class M class)
Proof
  qexists_tac ‘λM class. @q. q ∈ M.Q ∧ class = words_of_state M q’ >>
  rw[] >> SELECT_ELIM_TAC >>
  metis_tac[exists_state_class]
QED

(*---------------------------------------------------------------------------*)
(* So can make a map from classes to states                                  *)
(*                                                                           *)
(* state_of_class_def:                                                       *)
(*  |- ∀M. is_dfa M ⇒                                                        *)
(*         ∀class.                                                           *)
(*           class ∈ partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}) *)
(*           ⇒                                                               *)
(*           state_of_class M class ∈ M.Q ∧                                  *)
(*           class = words_of_state M (state_of_class M class)               *)
(*---------------------------------------------------------------------------*)

val state_of_class_def =
  new_specification
   ("state_of_class_def", ["state_of_class"], state_of_class_witness);


Theorem state_of_class_inj:
  is_dfa M ⇒
  class1 ∈ partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}) ∧
  class2 ∈ partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}) ∧
  state_of_class M class1 = state_of_class M class2
  ⇒
  class1 = class2
Proof
  rw[] >>
  ‘state_of_class M class1 ∈ M.Q ∧
   state_of_class M class2 ∈ M.Q ∧
   class1 = words_of_state M (state_of_class M class1) ∧
   class2 = words_of_state M (state_of_class M class2)’ by
    metis_tac[state_of_class_def] >>
  metis_tac[]
QED

Triviality state_of_class_words_of_state_id:
  is_dfa M ∧ EVERY (λa. a ∈ M.Sigma) x ∧
  nfa_eval M M.initial x = {q}
   ⇒
  state_of_class M (words_of_state M q) = q
Proof
 strip_tac >> drule state_of_class_def >> disch_tac >>
 ‘words_of_state M q =
  words_of_state M (state_of_class M (words_of_state M q))’ by
    metis_tac[words_of_state_in_partition] >>
  pop_keep_tac >> simp[EXTENSION,in_words_of_state] >>
  disch_then (mp_tac o Q.SPEC ‘x’) >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* The partition is finite because state_of_class is an injection from the   *)
(* partition into the set of states.                                         *)
(*---------------------------------------------------------------------------*)

Theorem finite_nfa_eval_equiv_partition:
  is_dfa M ⇒
  FINITE (partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}))
Proof
  strip_tac >>
  irule (FINITE_INJ
           |> INST_TYPE [alpha |-> “:word set”,beta |-> “:state”]) >>
  simp[Once SWAP_EXISTS_THM] >>
  qexists_tac ‘{q | q ∈ M.Q ∧
                words_of_state M q ∈
                  partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma})}’ >>
  qexists_tac ‘state_of_class M’ >> conj_tac
  >- (irule SUBSET_FINITE >> qexists_tac ‘M.Q’ >>
      gvs [is_dfa_def,wf_nfa_def, SUBSET_DEF])
  >- (rw [INJ_DEF]
      >- metis_tac[state_of_class_def]
      >- metis_tac[state_of_class_def]
      >- (irule state_of_class_inj >>
          first_x_assum (irule_at Any) >>
          first_x_assum (irule_at Any) >>
          first_x_assum (irule_at Any) >>
          metis_tac[state_of_class_def]))
QED

(*---------------------------------------------------------------------------*)
(* If (L,A) is regular, then there is a right-invariant equivalence on A*    *)
(* that has finitely many equivalence classes, and L is the union of a       *)
(* subset of the classes.                                                    *)
(*                                                                           *)
(* Note: the witness for the equivalence is nfa-evaluation equivalence, and  *)
(* the present theorem could be phrased directly in terms of it. However the *)
(* extra abstraction makes Myhill_Nerode_B stronger.                         *)
(*---------------------------------------------------------------------------*)

Theorem Myhill_Nerode_A:
  (L,A) ∈ REGULAR ⇒
  ∃R. R equiv_on (KSTAR{[a] | a ∈ A}) ∧
      right_invar (KSTAR{[a] | a ∈ A}) R ∧
      FINITE (partition R (KSTAR{[a] | a ∈ A})) ∧
      ∃classes. classes ⊆ partition R (KSTAR{[a] | a ∈ A}) ∧ L = BIGUNION classes
Proof
  strip_tac >>
  gvs [IN_REGULAR_AS_DFA] >>
  qexists_tac ‘nfa_eval_equiv M’ >> rw[]
  >- metis_tac [equiv_on_nfa_eval_equiv]
  >- metis_tac [right_invar_nfa_eval_equiv,is_dfa_def]
  >- metis_tac [finite_nfa_eval_equiv_partition]
  >- (qexists_tac
       ‘{class |
         state_of_class M class ∈ M.final ∧
         class ∈ partition (nfa_eval_equiv M)
                           (KSTAR {[a] | a ∈ M.Sigma})}’ >> conj_tac
      >- rw [SUBSET_DEF]
      >- (simp [EXTENSION] >> ‘wf_nfa M’ by metis_tac [is_dfa_def] >>
          rw[in_nfa_lang_nfa_eval_alt,EQ_IMP_THM]
          >- (drule_all dfa_eval_final_state >> rw[] >> gvs[] >>
              qexists_tac ‘words_of_state M q’ >> rw[]
              >- simp[words_of_state_def]
              >- (‘state_of_class M (words_of_state M q) = q’
                     suffices_by gvs [EXTENSION] >>
                  irule state_of_class_words_of_state_id >> metis_tac[])
              >- metis_tac [words_of_state_in_partition])
          >- gvs [partition_def]
          >- (rename1 ‘state_of_class M class ∈ M.final’ >>
              drule state_of_class_def >> disch_tac >>
              first_x_assum drule >>
              rw [words_of_state_def] >> gvs [EXTENSION]))
     )
QED


val _ = export_theory();
