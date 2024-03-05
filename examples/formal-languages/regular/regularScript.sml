(*===========================================================================*)
(* Basic automata theory: dfas, nfas, their equivalence via the subset       *)
(* construction, further closure constructions, regular expressions,         *)
(* equivalence of regexps and automata, pumping lemma, Myhill-Nerode,        *)
(* minimization, etc.                                                        *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;
open combinTheory
     listTheory
     mp_then
     nlistTheory
     numpairTheory
     pred_setTheory
     relationTheory
     rich_listTheory
     arithmeticTheory
     FormalLangTheory;

infix byA;
val op byA = BasicProvers.byA;

val subst_all_tac = SUBST_ALL_TAC
val pop_subst_tac = pop_assum subst_all_tac;
val pop_forget_tac = pop_assum kall_tac
val qpat_weaken_tac = Lib.C qpat_x_assum kall_tac;
val weaken_tac = WEAKEN_TAC

fun obtain_then q tac ttac = ttac (Q.prove(q,tac))


val _ = new_theory "regular";

(*---------------------------------------------------------------------------*)
(* Local lemmas, possibly of wider use                                       *)
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

Triviality LESS_FRONT_LENGTH[simp]:
 ∀l n. 0 < n ∧ n < LENGTH l ⇒ n-1 < LENGTH (FRONT l)
Proof
  Cases >> rw[FRONT_DEF]
QED

Triviality EVERY_LAST:
  ∀list. list ≠ [] ∧ EVERY P list ⇒ P (LAST list)
Proof
 Induct >> rw[LAST_DEF]
QED

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

Theorem SET_TO_LIST_11[simp]:
  ∀s1 s2. FINITE s1 ∧ FINITE s2 ⇒ (SET_TO_LIST s1 = SET_TO_LIST s2 ⇔ s1 = s2)
Proof
  metis_tac[listTheory.SET_TO_LIST_INV]
QED

(*---------------------------------------------------------------------------*)
(* Non-deterministic finite state automata (NFAs).                           *)
(*---------------------------------------------------------------------------*)

Type state  = “:num”
Type symbol = “:num”
Type word   = “:symbol list”
Type language = “:word set”

Datatype:
  nfa = <|
    Q : state set ;
    Sigma : symbol set ;
    delta : state -> symbol -> state set;
    initial : state set;
    acceptors : state set
  |>
End

Definition wf_nfa_def:
  wf_nfa N ⇔
    FINITE N.Q ∧
    FINITE N.Sigma ∧
    N.initial ⊆ N.Q ∧
    N.acceptors ⊆ N.Q ∧
    (∀q a. a ∈ N.Sigma ∧ q ∈ N.Q ⇒ N.delta q a ⊆ N.Q)
End

(*---------------------------------------------------------------------------*)
(* A deterministic finite state automaton (DFA) is an NFA with a single      *)
(* start state, and where there is exactly one transition from a state for   *)
(* each symbol in Sigma.                                                     *)
(*---------------------------------------------------------------------------*)

Definition is_dfa_def:
  is_dfa N ⇔ wf_nfa N ∧ (∃q_0. N.initial = {q_0}) ∧
             (∀q a. q ∈ N.Q ∧ a ∈ N.Sigma ⇒ ∃q'. N.delta q a = {q'})
End

(*
                                           /-----------\
                                           v           |
   --> ( 1 )  --a-->  (( 2 ))  --a,b-->  ( 4 )  --a,b -'
         |                                 ^
         b                                 |
         |                                 |
         \______________a,b________________/
       ( 3 )


*)

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
      acceptors := {2} |>
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
   {w | w ∈ KSTAR (IMAGE (λa. [a]) N.Sigma) ∧
        ∃qs. LENGTH qs = LENGTH w + 1 ∧
             HD qs ∈ N.initial ∧
             LAST qs ∈ N.acceptors ∧
         (∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w))}
End

Theorem in_nfa_lang:
 w ∈ nfa_lang N
  <=>
 w ∈ KSTAR (IMAGE (λa. [a]) N.Sigma) ∧
 ∃qs. LENGTH qs = LENGTH w + 1 ∧
          HD qs ∈ N.initial ∧
        LAST qs ∈ N.acceptors ∧
       (∀n. n < LENGTH w ⇒ EL (n + 1) qs ∈ N.delta (EL n qs) (EL n w))
Proof
 rw [nfa_lang_def]
QED

(*---------------------------------------------------------------------------*)
(* There's a coercion between symbols in the alphabet and the words needed   *)
(* for application of KSTAR                                                  *)
(*---------------------------------------------------------------------------*)

Triviality KSTAR_SIGMA[simp]:
  ∀w. w ∈ KSTAR (IMAGE (λa. [a]) sigma) <=> EVERY (λa. a ∈ sigma) w
Proof
  Induct >> simp [Once IN_KSTAR_THM] >> rw [EQ_IMP_THM,PULL_EXISTS]
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
(* Encode/decode of state sets, to avoid HOL type constructions mirroring    *)
(* automata constructions. This leaves states as numbers, even after the     *)
(* subset construction.                                                      *)
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
(* Subset construction                                                       *)
(*---------------------------------------------------------------------------*)

Definition nfa_to_dfa_def:
  nfa_to_dfa N =
    <|Q := {enc s | s ⊆ N.Q};
      Sigma := N.Sigma;
      delta := λq a. {enc (BIGUNION {N.delta qi a | qi ∈ dec q})};
      initial := {enc N.initial};
      acceptors := {enc s | s ⊆ N.Q ∧ s ∩ N.acceptors ≠ ∅} |>
End

Triviality in_nfa_to_dfa_states[simp]:
  ∀q. q ∈ (nfa_to_dfa N).Q <=> ∃s. q = enc s ∧ s ⊆ N.Q
Proof
  rw[nfa_to_dfa_def]
QED

Triviality nfa_to_dfa_Sigma[simp]:
  (nfa_to_dfa N).Sigma = N.Sigma
Proof
  rw[nfa_to_dfa_def]
QED

Triviality nfa_to_dfa_initial[simp]:
  (nfa_to_dfa N).initial = {enc N.initial}
Proof
  rw[nfa_to_dfa_def]
QED

Triviality nfa_to_dfa_acceptors[simp]:
  (nfa_to_dfa N).acceptors = {enc s | s ⊆ N.Q ∧ s ∩ N.acceptors ≠ ∅}
Proof
  rw[nfa_to_dfa_def]
QED

Theorem finite_dfa_delta_successors:
 wf_nfa N ⇒
  ∀eq a. s ⊆ N.Q ∧ a ∈ N.Sigma ==> FINITE (BIGUNION {N.delta q a | q ∈ s})
Proof
  rw [] >>
  ‘FINITE s’ by metis_tac [SUBSET_FINITE,wf_nfa_def]
  >- (fs[GSPEC_IMAGE,o_DEF,IN_DEF] >> metis_tac [IMAGE_FINITE])
  >- (fs [wf_nfa_def] >> metis_tac [SUBSET_FINITE,SUBSET_DEF])
QED

(*---------------------------------------------------------------------------*)
(* Well-formedness of a constructed DFA                                      *)
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
(* All lemmas about DFA executions go by SNOC induction. The SNOC step       *)
(* assumes the property for the front of the list and wants to show it for   *)
(* the last element. The last element is obtained by a Delta step from the   *)
(* last element of the front of the list. In order to expand the Delta step, *)
(* the last element of the front of the list has to shown to be in the state *)
(* set.                                                                      *)
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
      rpt (weaken_tac is_forall) >> qpat_x_assum ‘_ ∈ _’ mp_tac >>
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

Triviality snoc2:
 ∀list n. LENGTH list = n+2 ⇒ ∃a b. list = SNOC a b ∧ b ≠ []
Proof
  rpt strip_tac >> Cases_on ‘list = []’
  >- fs[]
  >- (drule SNOC_LAST_FRONT >> Cases_on ‘FRONT list = []’
      >- (Cases_on ‘list’ >> fs[])
      >- metis_tac [])
QED

(*---------------------------------------------------------------------------*)
(* Main lemma for the subset construction. The last state in an execution of *)
(* the DFA on input w, when decoded, is equal to the set of states reachable *)
(* by NFA executions on w.                                                   *)
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
     qpat_weaken_tac ‘$∀ (M:num list->bool)’ >> rw[] >> fs[] >>
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
        by metis_tac[finite_dfa_delta_successors] >> simp[] >>
     ntac 2 pop_forget_tac >> qpat_weaken_tac ‘s = GSPEC _’ >>
     (* Finally equality between the two fringe state sets *)
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
     ‘∃qa. qa ∈ s ∧ qa ∈ N.acceptors’ by (fs[EXTENSION] >> metis_tac[]) >>
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
  >- (qexists_tac ‘nfa_to_dfa N’ >>
      rw [is_dfa_nfa_to_dfa,nfa_to_dfa_correct])
  >- (fs [is_dfa_def] >> metis_tac[])
QED

(*===========================================================================*)
(* NFA and DFA languages are Finite_State languages.                         *)
(*===========================================================================*)

Theorem DFA_Finite_State:
  DFA_LANGS ⊆ Finite_State
Proof
 cheat
QED

Theorem Finite_State_DFA:
  Finite_State ⊆ DFA_LANGS
Proof
 cheat
QED

Theorem NFA_LANGS_EQ_Finite_State:
  Finite_State = NFA_LANGS
Proof
  metis_tac [SET_EQ_SUBSET,NFA_LANGS_EQ_DFA_LANGS,
             DFA_Finite_State, Finite_State_DFA]
QED


(*===========================================================================*)
(* Boolean, and other, closure properties via machine constructions          *)
(*===========================================================================*)

Definition nfa_compl_def:
  nfa_compl N =
    <|Q     := N.Q;
      Sigma := N.Sigma;
      delta := N.delta;
      initial := N.initial;
      acceptors := (N.Q DIFF N.acceptors)
    |>
End

Definition nfa_inter_def:
  nfa_inter N1 N2 =
    <|Q  := {q1 ⊗ q2 | q1 ∈ N1.Q ∧ q2 ∈ N2.Q};
      Sigma := N1.Sigma ∪ N2.Sigma;
      delta := λq a. {q1 ⊗ q2 | q1 ∈ N1.delta (nfst q) a ∧ q2 ∈ N2.delta (nsnd q) a};
      initial   := {q1 ⊗ q2 | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      acceptors := {q1 ⊗ r2 | q1 ∈ N1.acceptors ∧ r2 ∈ N2.acceptors}
    |>
End

Definition nfa_union_def:
  nfa_union N1 N2 =
    <|Q  := {q1 ⊗ q2 | q1 ∈ N1.Q ∧ q2 ∈ N2.Q };
      Sigma := N1.Sigma ∪ N2.Sigma;
      delta := λq a. {q1 ⊗ q2 | q1 ∈ N1.delta (nfst q) a ∧ q2 ∈ N2.delta (nsnd q) a};
      initial   := {q1 ⊗ q2 | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      acceptors := {q1 ⊗ q2 | (q1 ∈ N1.acceptors ∧ q2 ∈ N2.Q) ∨
                              (q1 ∈ N1.Q ∧ q2 ∈ N2.acceptors)};
    |>
End

Definition nfa_cat_def:
  nfa_cat N1 N2 =
    <|Q  := {0 ⊗ q | q ∈ N1.Q} ∪ {1 ⊗ q | q ∈ N2.Q};
      Sigma := N1.Sigma ∪ N2.Sigma;
      delta := λq a.
              if nfst q = 0 then
                let
                  N1kids = {0 ⊗ q1 | q1 ∈ N1.delta (nsnd q) a}
                in
                  if nsnd q ∈ N1.acceptors ∧ copt = NONE then frs ∪ {1 ⊗ N2.q_0}
                  else frs
              else
                {1 ⊗ s' | s' ∈ N2.tf (nsnd s) copt};
      initial   := {0 ⊗ q | q ∈ N1.initial};
      acceptors := {1 ⊗ q | q ∈ N2.acceptors};
    |>
End

Definition nfa_star_def:
  nfa_star N =
   <| Q :=  IMAGE SUC N.Q ∪ {0} ;
     Sigma := N.Sigma ;
     tf := λs0 copt.
             case s0 of
               0 => if copt = NONE then {SUC N.q_0} else ∅
             | SUC s0' =>
                if copt = NONE ∧ s0' ∈ N.C then
                  IMAGE SUC (N.tf s0' copt) ∪ {0}
                else IMAGE SUC (N.tf s0' copt) ;
     initia := 0 ;
     acceptors := {0};
   |>
End

(* Theorem 1.25 *)
Theorem wf_dfa_nfa_union :
  ∀M1 N2. wf_dfa M1 ∧ wf_dfa N2 ⇒ wf_dfa (machine_union M1 N2)
Proof
  rw[wf_dfa_def,machine_union_def] (* 11 *) >> simp[]
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (UNCURRY npair) (M1.Q CROSS M2.Q)’ suffices_by simp[] >>
      simp[Abbr‘s’, EXTENSION, pairTheory.EXISTS_PROD])
  >- (simp[SUBSET_DEF,PULL_EXISTS] >> metis_tac[SUBSET_DEF])
  >- (Cases_on ‘c ∈ M2.A’ >> simp[])
  >- metis_tac[]
QED

(* regular languages closed under union *)
Theorem thm_1_25:
  ∀ lA lB. regularLanguage lA ∧
           regularLanguage lB ⇒
           regularLanguage (lA ∪ lB)
Proof
  rw [regularLanguage_def] >>
  rename [‘recogLangD M1 ∪ recogLangD M2’] >>
  qexists_tac ‘machine_union M1 M2’ >>
  rw [recogLangD_def, EXTENSION,
      has_Accepting_Execution_Delta_coincide_thm,
      wf_dfa_machine_union] >>
  qabbrev_tac ‘MU = machine_union M1 M2’ >>
  rw[accepts_def] >>
  ‘(MU.A = M1.A ∪ M2.A) ∧ (MU.q_0 = M1.q_0 ⊗ M2.q_0)’
    by rw[machine_union_def, Abbr ‘MU’] >>
  simp[] >>
  ‘∀ q1 q2. q1 ∈ M1.Q ∧ q2 ∈ M2.Q
    ⇒ (Delta MU (q1 ⊗ q2) x ∈ MU.C ⇔
      Delta M1 q1 x ∈ M1.C ∨ Delta M2 q2 x ∈ M2.C)’
    suffices_by (rpt strip_tac >>
                 metis_tac[wf_dfa_def]) >>
  Induct_on ‘x’
  >- (rw[Abbr ‘MU’, Delta_def,machine_union_def])
  >- (rw[Delta_def, DISJ_IMP_THM, FORALL_AND_THM] >>
      ‘MU.tf (q1 ⊗ q2) h = M1.tf q1 h ⊗ M2.tf q2 h’
        by rw[Abbr ‘MU’, machine_union_def] >>
      first_x_assum (fn x => SUBST_TAC [x]) >>
      ‘M1.tf q1 h ∈ M1.Q ∧ M2.tf q2 h ∈ M2.Q’
        suffices_by metis_tac[] >>
      metis_tac[wf_dfa_def])
QED

(*---------------------------------------------------------------------------*)
(* Closure under concatenation                                               *)
(*---------------------------------------------------------------------------*)

Definition machine_link_def:
  machine_link N1 N2 =
    <|Q  := {0 ⊗ q1 | q1 ∈ N1.Q} ∪ {1 ⊗ r2 | r2 ∈ N2.Q};
      A  := N1.A ∪ N2.A;
      tf := λs copt.
              if nfst s = 0 then
                let
                  frs = { 0 ⊗ s' | s' ∈ N1.tf (nsnd s) copt}
                in
                  if nsnd s ∈ N1.C ∧ copt = NONE then frs ∪ {1 ⊗ N2.q_0}
                  else frs
              else
                {1 ⊗ s' | s' ∈ N2.tf (nsnd s) copt};
      q_0 := 0 ⊗ N1.q_0;
      C  := {1 ⊗ r2 | r2 ∈ N2.C };
    |>
End

val _ =
  set_mapped_fixity
     {term_name = "machine_link",
      fixity = Infixl 500,
      tok = "⌢"}

Theorem machine_link_q_0[simp]:
  (N1 ⌢ N2).q_0 = 0 ⊗ N1.q_0
Proof
  simp[machine_link_def]
QED

Theorem wfNFA_machine_link:
  ∀N1 N2.
    wfNFA N1 ∧ wfNFA N2 ⇒ wfNFA (N1 ⌢ N2)
Proof
  rw[wfNFA_def,machine_link_def]
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (npair 0) N1.Q’
        suffices_by metis_tac[IMAGE_FINITE] >>
      simp[EXTENSION,Abbr ‘s’])
  >- (qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = IMAGE (npair 1) N2.Q’
        suffices_by metis_tac[IMAGE_FINITE] >>
      simp[EXTENSION,Abbr ‘s’]) >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
  metis_tac[SUBSET_DEF,NOT_IN_EMPTY]
QED

Theorem machine_link_tf0:
  (N1 ⌢ N2).tf (0 ⊗ n1) c =
   if n1 ∈ N1.C ∧ c = NONE then
      {0 ⊗ n | n ∈ N1.tf n1 NONE} ∪ {1 ⊗ N2.q_0}
    else {0 ⊗ n | n ∈ N1.tf n1 c}
Proof
  simp[machine_link_def]
QED

Theorem machine_link_A:
  (N1 ⌢ N2).A = N1.A ∪ N2.A
Proof
  simp[machine_link_def]
QED

Theorem machine_link_C[simp]:
  (N1 ⌢ N2).C = { 1 ⊗ n | n ∈ N2.C }
Proof
  simp[machine_link_def]
QED

Theorem NF_transition_link2_E:
  ∀q1 n. NF_transition (N1 ⌢ N2) (1 ⊗ q1) ts n ⇒ ∃q2. n = 1 ⊗ q2
Proof
  Induct_on ‘NF_transition’ >> simp[] >> rw[] >> first_x_assum irule >>
  qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >> simp[machine_link_def] >>
  simp[PULL_EXISTS]
QED

Theorem NF_transition_link21_impossible[simp]:
  ¬NF_transition (N1 ⌢ N2) (1 ⊗ q1) ts (0 ⊗ q2)
Proof
  strip_tac >> drule NF_transition_link2_E >> simp[]
QED

Theorem NF_transition_machine_link1[simp]:
  wfNFA N1 ⇒
  (NF_transition (N1 ⌢ N2) (0 ⊗ q1) ts (0 ⊗ q2) ⇔ NF_transition N1 q1 ts q2)
Proof
  strip_tac >> eq_tac
  >- (map_every qid_spec_tac [‘q1’, ‘q2’] >> Induct_on ‘NF_transition’ >>
      rw[] >> fs[NF_transition_rules] >>
      qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
      rw[machine_link_def] >> fs[] >>
      irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
      fs[machine_link_A] >> fs[wfNFA_def] >>
      metis_tac[NF_transition_rules, NOT_IN_EMPTY]) >>
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  simp[machine_link_A] >> goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[machine_link_def] >>
  asm_simp_tac (srw_ss() ++ boolSimps.COND_elim_ss)[] >> metis_tac[]
QED

Theorem NF_transition_machine_link2[simp]:
  wfNFA N2 ⇒
  (NF_transition (N1 ⌢ N2) (1 ⊗ q1) ts (1 ⊗ q2) ⇔ NF_transition N2 q1 ts q2)
Proof
  strip_tac >> eq_tac
  >- (map_every qid_spec_tac [‘q1’, ‘q2’] >> Induct_on ‘NF_transition’ >>
      rw[] >> fs[NF_transition_rules] >>
      qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
      rw[machine_link_def] >> fs[] >>
      irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
      fs[machine_link_A] >> fs[wfNFA_def] >>
      metis_tac[NF_transition_rules, NOT_IN_EMPTY]) >>
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  simp[machine_link_A] >> goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[machine_link_def]
QED


Theorem NF_transition_machine_link_shift12:
  wfNFA N1 ∧ wfNFA N2 ∧
  NF_transition (N1 ⌢ N2) q_0 ts q ∧
  q_0 ∈ { 0 ⊗ n1 | n1 ∈ N1.Q } ∧ q ∈ { 1 ⊗ n2 | n2 ∈ N2.Q }
⇒
  ∃q1 ts1 ts2.
    q1 ∈ N1.C ∧ (* q2 = 1 ⊗ N2.q_0 *)
    NF_transition N1 (nsnd q_0) ts1 q1 ∧
    NF_transition N2 N2.q_0 ts2 (nsnd q) ∧
    ts = ts1 ++ [NONE] ++ ts2
Proof
  Induct_on ‘NF_transition’ >> rw[]
  >- (qspec_then ‘q_0’ strip_assume_tac npair_cases >> simp[] >>
      rename [‘q_0 = m ⊗ n’] >> Cases_on ‘m = 0’ >> simp[]) >>
  fs[PULL_EXISTS] >>
  rename [‘NF_transition _ q1 ts (1 ⊗ n2)’] >>
  qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
  rw[machine_link_def] >> fs[]
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF] >>
      fs[] >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q_0 ts2 n2’] >>
      ‘NF_transition N1 n1 (NONE::ts1) q1’
         by metis_tac[NF_transition_rules, optionTheory.NOT_SOME_NONE] >>
      map_every qexists_tac [‘q1’, ‘NONE::ts1’, ‘ts2’] >> simp[])
  >- (goal_assum drule >> qexists_tac ‘[]’ >> simp[NF_transition_rules])
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF, NOT_IN_EMPTY,
                                optionTheory.option_CASES] >> fs[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q_0 ts2 n2’] >>
      ‘NF_transition N1 n1 (c::ts1) q1’
         by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
             reverse conj_tac >- metis_tac[] >> fs[machine_link_A] >>
             metis_tac[wfNFA_def, NOT_IN_EMPTY]) >>
      metis_tac[APPEND])
QED

Theorem munge_exists:
!ts. ?n xnlist cs.
  ts = munge n (ZIP (cs,xnlist)) ∧ LENGTH xnlist = LENGTH cs
Proof
  Induct_on ‘ts’ >> csimp[ZIP_EQ_NIL] >>
  strip_tac >> fs[] >> Cases_on ‘h’ (* 2 *)
  >- (map_every qexists_tac [‘SUC n’,‘xnlist’, ‘cs’] >> simp[munge_SUC]) >>
  rename [‘SOME c :: munge n (ZIP (cs, xnlist))’] >>
  map_every qexists_tac [‘0’,‘n::xnlist’, ‘c::cs’] >>
  simp[]
QED

Theorem NF_transition_concat:
  NF_transition m q_0 ts1 q1 ∧ NF_transition m q1 ts2 q2
  ==>
  NF_transition m q_0 (ts1 ++ ts2) q2
Proof
  Induct_on ‘NF_transition’ >> rw[] >> fs[] >>
  metis_tac[NF_transition_rules]
QED

Theorem front_cons_snoc[simp]:
∀h t x.  FRONT (h::(t++[x])) = h::t
Proof
  Induct_on‘t’ >> simp[]
QED

Theorem replicate_single[simp]:
  REPLICATE 1 e = [e]
Proof
  rw[rich_listTheory.REPLICATE_compute]
QED

Theorem replicate_snoc[simp]:
  ∀r.  REPLICATE r NONE ⧺ [NONE] = REPLICATE (r + 1) NONE
Proof
  Induct_on ‘r’ >> rw[GSYM arithmeticTheory.ADD1] >> rw[ADD_CLAUSES]
QED

Theorem munge_middle_none:
∀ xnlist1 xnlist2 n1 n2.
  munge n1 xnlist1 ⧺ NONE::munge n2 xnlist2 =
    if xnlist1 = [] then munge (n1+n2+1) xnlist2
    else munge n1 (FRONT xnlist1 ++
                   (FST $ LAST xnlist1, (SND $ LAST xnlist1) + 1 + n2)::xnlist2)
Proof
  rw[munge_def,rich_listTheory.REPLICATE_APPEND]
  >> pop_assum mp_tac
  >> map_every qid_spec_tac [‘n2’, ‘n1’, ‘xnlist2’, ‘xnlist1’]
  >> ho_match_mp_tac SNOC_INDUCT >> rw[Excl"APPEND_ASSOC"]
  >> Cases_on‘xnlist1’ >> fs[]
  >> rename [‘SOME (FST cn)’] >> Cases_on‘cn’ >>
  simp[rich_listTheory.REPLICATE_APPEND]
QED

Theorem WF_IND_I:
  ∀R P. WF R ∧ (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. P x
Proof
  metis_tac[relationTheory.WF_INDUCTION_THM]
QED

Theorem munge_inj[simp]:
 ∀n1 l1 n2 l2. munge n1 l1 = munge n2 l2 <=> n1 = n2 ∧ l1 = l2
Proof
  ‘∀p n2 l2 n1 l1.
     p = (n1,l1) ⇒ (munge n1 l1 = munge n2 l2 ⇔ n1 = n2 ∧ l1 = l2)’
     suffices_by simp[] >>
  ho_match_mp_tac WF_IND_I >> simp[GSYM RIGHT_FORALL_IMP_THM] >>
  qexists_tac ‘inv_image ($< LEX $<) (λ(n,l). (LENGTH l, n))’ >>
  conj_tac
  >- simp[relationTheory.WF_inv_image, pairTheory.WF_LEX] >>
  simp[pairTheory.LEX_DEF] >> rw[] >>
  Cases_on ‘n1’ >> simp[]
  >- (reverse (Cases_on ‘n2’) >> simp[munge_SUC]
      >- (Cases_on ‘l1’ >> simp[] >> Cases_on ‘h’ >> simp[munge0CONS]) >>
      map_every Cases_on [‘l1’, ‘l2’] >> simp[] >>
      rename [‘munge 0 (h1::t1) = munge 0 (h2::t2)’] >>
      map_every Cases_on [‘h1’, ‘h2’] >> simp[munge0CONS] >> metis_tac[]) >>
  Cases_on ‘n2’ >> simp[munge_SUC] >>
  Cases_on ‘l2’ >> simp[] >> Cases_on ‘h’ >> simp[munge0CONS]
QED

Theorem NON_NIL_FRONT:
  t ≠ [] ⇒ FRONT(h::t) = h::FRONT t
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem FRONT_ZIP:
  ∀l1 l2. l1 ≠ [] ∧ LENGTH l1 = LENGTH l2 ⇒
          FRONT (ZIP (l1,l2)) = ZIP (FRONT l1, FRONT l2)
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[] >>
  Cases_on ‘l1 = []’ >> simp[] >> fs[] >>
  rename [‘LENGTH l1 = LENGTH l2’] >> rw[] >>
  ‘l2 ≠ []’ by (strip_tac >> fs[]) >>
  simp[NON_NIL_FRONT, ZIP_EQ_NIL]
QED

Theorem LAST_ZIP:
  ∀l1 l2. l1 ≠ [] ∧ LENGTH l1 = LENGTH l2 ⇒
          LAST (ZIP (l1, l2)) = (LAST l1, LAST l2)
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[] >>
  Cases_on ‘l1 = []’ >> simp[] >> fs[] >> rw[] >>
  rename [‘LENGTH l1 = LENGTH l2’] >> ‘l2 ≠ []’ by (strip_tac >> fs[]) >>
  simp[LAST_CONS_cond, ZIP_EQ_NIL]
QED

(*---------------------------------------------------------------------------*)
(* Finally, regular languages are closed under concatenation                 *)
(*---------------------------------------------------------------------------*)

Theorem thm_1_47:
  ∀L1 L2.
    regularLanguage L1 ∧ regularLanguage L2 ⇒ regularLanguage (L1 dot L2)
Proof
  rw[corollary_1_40] >>
  rename1 ‘recogLangN _ = (_ N1) dot (_ N2)’ >>
  qexists_tac ‘N1 ⌢ N2’ >>
  rw[wfNFA_machine_link,EXTENSION,dot_def, recogLangN_def,
     Sipser_ND_Accepts_NF_transition, EQ_IMP_THM]
  >- (rename [‘LENGTH epslist = LENGTH s’,
              ‘NF_transition (N1 ⌢ N2) _ (munge eps0 _)’] >>
      drule_then (drule_then drule) NF_transition_machine_link_shift12 >>
      simp[] >> impl_tac >- metis_tac[wfNFA_def, SUBSET_DEF] >>
      strip_tac >>
      rename [‘munge _ _ = ts1 ⧺ [NONE] ⧺ ts2’,
              ‘NF_transition _ _ _ (1 *, n)’] >>
      simp[PULL_EXISTS] >>
      qspec_then ‘ts1’
         (qx_choosel_then [‘n1’,‘s1’,‘nlist1’] strip_assume_tac) munge_exists >>
      qspec_then ‘ts2’
         (qx_choosel_then [‘n2’,‘s2’,‘nlist2’] strip_assume_tac) munge_exists >>
      rw[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      simp[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      simp[] >>
      first_x_assum
        (mp_tac o AP_TERM “drop_epsilon: num option list -> num list”) >>
      simp[drop_epsilon_munge]) >>
  rename [‘machine_link N1 N2’,
          ‘NF_transition N1 _ (munge n1 (ZIP (s1,nlist1))) q1’,
          ‘NF_transition N2 _ (munge n2 (ZIP (s2,nlist2))) q2’] >>
  ‘NF_transition (N1 ⌢ N2) (0 ⊗ N1.q_0) (munge n1 (ZIP (s1,nlist1))) (0 ⊗ q1)’
     by simp[] >>
  ‘NF_transition (N1 ⌢ N2) (1 ⊗ N2.q_0) (munge n2 (ZIP (s2,nlist2))) (1 ⊗ q2)’
     by simp[] >>
  ‘NF_transition (N1 ⌢ N2) (0 ⊗ q1) (NONE::munge n2 (ZIP (s2,nlist2))) (1 ⊗ q2)’
     by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >> simp[] >>
         qexists_tac ‘1 ⊗ N2.q_0’ >> simp[] >> simp[machine_link_def]) >>
  drule_all NF_transition_concat >> rw[munge_middle_none]
  >- (‘s1 = [] ∧ nlist1 = []’ by metis_tac[ZIP_EQ_NIL] >> rw[] >> metis_tac[])>>
  simp[PULL_EXISTS] >>
  map_every qexists_tac [
    ‘n1’, ‘FRONT nlist1 ++ (n2 + LAST nlist1 + 1) :: nlist2’, ‘q2’
  ] >> rw[]
  >- (Cases_on‘nlist1 = []’
      >- (fs[] >> rw[] >> fs[])
      >> rw[rich_listTheory.LENGTH_FRONT]
      >> Cases_on ‘LENGTH s1’ >> simp[] >> fs[]) >> pop_assum mp_tac >>
  qmatch_abbrev_tac‘NF_transition _ _ l1 _ ==> NF_transition _ _ l2 _’ >>
  ‘l1 = l2’ suffices_by fs[] >> simp[Abbr‘l1’,Abbr‘l2’] >>
  ‘s1 ≠ [] ∧ nlist1 ≠ []’ by (rfs[ZIP_EQ_NIL] >> rpt strip_tac >> fs[]) >>
  ‘0 < LENGTH nlist1’ by (Cases_on ‘nlist1’ >> fs[]) >>
  simp[FRONT_ZIP, LAST_ZIP, GSYM ZIP_APPEND, LENGTH_FRONT] >>
  simp[GSYM ZIP_SNOC, Excl "LIST_EQ_SIMP_CONV",LENGTH_FRONT,GSYM SNOC_APPEND] >>
  simp[SNOC_APPEND, APPEND_FRONT_LAST]
QED

(*---------------------------------------------------------------------------*)
(* Closure under Kleene star                                                 *)
(*---------------------------------------------------------------------------*)

Definition machine_star_def:
  machine_star N =
   <|
     Q :=  IMAGE SUC N.Q ∪ {0} ;
     A :=  N.A ;
     q_0 := 0 ;
     tf := λs0 copt.
             case s0 of
               0 => if copt = NONE then {SUC N.q_0} else ∅
             | SUC s0' =>
                if copt = NONE ∧ s0' ∈ N.C then
                  IMAGE SUC (N.tf s0' copt) ∪ {0}
                else IMAGE SUC (N.tf s0' copt) ;
     C := {0};
   |>
End

Theorem wfNFA_machine_star:
  wfNFA N ⇒ wfNFA (machine_star N)
Proof
  simp[wfNFA_def, machine_star_def, DISJ_IMP_THM, PULL_EXISTS,
       AllCaseEqs()] >>
  rw[] >> simp[]
  >- (simp[] >> fs[SUBSET_DEF, PULL_EXISTS] >> metis_tac[])
  >- (rw[] >> fs[SUBSET_DEF, PULL_EXISTS] >> metis_tac[])
  >- metis_tac[TypeBase.nchotomy_of “:num”]
QED

Theorem machine_star_accepting_states[simp]:
  (machine_star N).C = {0}
Proof
  simp[machine_star_def]
QED

Theorem machine_star_alphabet[simp]:
  (machine_star N).A = N.A
Proof
  simp[machine_star_def]
QED

Theorem machine_star_tf0[simp]:
  (machine_star N).tf 0 NONE = {SUC N.q_0} ∧
  (machine_star N).tf 0 (SOME c) = ∅ ∧
  ((q ∈ (machine_star N).tf 0 cO) ⇔ (cO = NONE ∧ q = SUC N.q_0))
Proof
  rw[machine_star_def]
QED

Theorem machine_star_q_0[simp]:
  (machine_star N).q_0 = 0
Proof
  simp[machine_star_def]
QED

Theorem machine_star_tfSUC:
  (machine_star N).tf (SUC q_0) (SOME c) =
    {SUC q | q ∈ N.tf q_0 (SOME c)} ∧
  (machine_star N).tf (SUC q_0) NONE =
    {SUC q | q ∈ N.tf q_0 NONE} ∪
    (if q_0 ∈ N.C then {0} else ∅) ∧
  (SUC q ∈ (machine_star N).tf (SUC q_0) cO ⇔
    q ∈ N.tf q_0 cO)
Proof
  simp[machine_star_def, EXTENSION] >> rw[]
QED

Theorem NF_transition_machine_star_SUC:
∀q cs. NF_transition (machine_star N) (SUC q) cs 0 ⇒
  ∃s1 s2 nc. cs = s1++[NONE]++s2 ∧ nc ∈ N.C ∧ NF_transition N q s1 nc ∧
             NF_transition (machine_star N) 0 s2 0
Proof
  Induct_on ‘NF_transition’ >> rw[] >>
  rename [‘qI ∈ _ _ _’] >> Cases_on ‘qI’
  >- (Cases_on ‘c’ >> fs[machine_star_tfSUC] >>
      rw[] >> Cases_on ‘q ∈ N.C’ >> fs[] >>
      rw[] >> MAP_EVERY qexists_tac [‘[]’,‘cs’,‘q’] >>
      simp[NF_transition_rules])
  >- (fs[] >> MAP_EVERY qexists_tac [‘c::s1’,‘s2’,‘nc’] >> simp[] >>
      fs[machine_star_tfSUC] >> metis_tac[NF_transition_rules])
QED

Theorem NF_transition_machine_star:
  NF_transition (machine_star N) 0 cs 0 ⇒
  cs = [] ∨
  ∃s1 s2 nc. cs = NONE::s1++[NONE]++s2 ∧ nc ∈ N.C ∧ NF_transition N N.q_0 s1 nc ∧
             NF_transition (machine_star N) 0 s2 0
Proof
  Cases_on ‘cs’ >> simp[] >>
  simp[SimpL“$==>”, Once NF_transition_cases] >>
  csimp[] >> metis_tac[NF_transition_machine_star_SUC]
QED

Theorem LENGTH_mungeNIL[simp]:
  LENGTH (munge n []) = n
Proof
  Induct_on ‘n’ >> simp[munge_SUC]
QED

Theorem mungeNIL_IFF:
  (munge n [] = s ⇔ s = REPLICATE n NONE) ∧
  (s = munge n [] ⇔ s = REPLICATE n NONE)
Proof
  simp[munge_def, EQ_SYM_EQ]
QED

(*---------------------------------------------------------------------------*)
(* Already in numLib somewhere                                               *)
(*---------------------------------------------------------------------------*)

Triviality EXISTS_NUM:
  (∃n. P n) ⇔ P 0 ∨ (∃n. P (SUC n))
Proof
  rw[EQ_IMP_THM] >- (Cases_on ‘n’ >> metis_tac[]) >>
  metis_tac[]
QED

Triviality FORALL_NUM:
  (∀n. P n) ⇔ P 0 ∧ ∀n. P (SUC n)
Proof
  rw[EQ_IMP_THM] >> Cases_on ‘n’ >> simp[]
QED

Theorem drop_epsilon_EQ_NIL:
  drop_epsilon l = [] ⇔ ∃n. l = REPLICATE n NONE
Proof
  Induct_on ‘l’ >> simp[] >>
  Cases >> simp[] >- simp[Once EXISTS_NUM, SimpRHS] >>
  Cases >> simp[]
QED

Triviality REPLICATE_NIL'[simp]:
  [] = REPLICATE n e ⇔ n = 0
Proof
  metis_tac[REPLICATE_NIL]
QED

Theorem REPLICATE_EQ_APPEND:
  ∀n e l1 l2.
     REPLICATE n e = l1 ++ l2 ⇔
     ∃n1 n2. n1 + n2 = n ∧ l1 = REPLICATE n1 e ∧ l2 = REPLICATE n2 e
Proof
  Induct_on ‘n’ >> simp[APPEND_EQ_CONS, PULL_EXISTS] >>
  rw[EQ_IMP_THM] >> simp[]
  >- (simp[Once EXISTS_NUM, arithmeticTheory.ADD_CLAUSES] >> metis_tac[]) >>
  Cases_on ‘n1’ >> simp[] >> fs[arithmeticTheory.ADD_CLAUSES] >>
  metis_tac[]
QED

Definition munge'_def[simp]:
  munge' 0 [] = [] ∧
  munge' 0 ((c,n)::t) = SOME c :: munge' n t ∧
  munge' (SUC n) cs = NONE :: munge' n cs
End

Theorem munge_alt_def:
  ∀n l. munge n l = munge' n l
Proof
  ho_match_mp_tac munge'_ind >>
  rw[munge_SUC,munge_eq_nil]
QED

Theorem munge'_split:
  ∀n l str nlist s1 s2.
   munge' n l = s1 ⧺ [NONE] ⧺ s2 ∧
   ZIP (str,nlist) = l ∧
   LENGTH str = LENGTH nlist ⇒
   ∃nR strR nlistR.
    s2 = munge' nR (ZIP (strR,nlistR)) ∧
    LENGTH strR = LENGTH nlistR ∧
    str = drop_epsilon s1 ++ strR
Proof
  ho_match_mp_tac munge'_ind >>
  simp[] >> rw[] >> Cases_on ‘n’ >> fs[] >>
  Cases_on ‘s1’ >> fs[] >> rw[]
  >- (Cases_on ‘str’ >> Cases_on ‘nlist’ >> fs[] >>
      last_x_assum irule >> metis_tac[])
  >- (Cases_on ‘str’ >> Cases_on ‘nlist’ >> fs[] >>
      rw[] >> last_x_assum irule >> metis_tac[])
  >- metis_tac[]
  >- (last_x_assum irule >> metis_tac[])
  >- metis_tac[munge'_def]
  >- (last_x_assum irule >> metis_tac[])
QED

Theorem munge_split:
 ∀str n nlist s1 s2.
   munge n (ZIP (str,nlist)) = (s1 ⧺ [NONE] ⧺ s2) ∧
   LENGTH str = LENGTH nlist ⇒
   ∃nR strR nlistR.
    s2 = munge nR (ZIP (strR,nlistR)) ∧
    LENGTH strR = LENGTH nlistR ∧
    str = drop_epsilon s1 ++ strR
Proof
 metis_tac[munge_alt_def,munge'_split]
QED

Theorem munge_drop_epsilon_exists:
  ∀s.
    ∃n nlist.
      munge n (ZIP (drop_epsilon s, nlist)) = s ∧
      LENGTH nlist = LENGTH (drop_epsilon s)
Proof
  metis_tac[munge_exists,drop_epsilon_munge]
QED

Theorem NF_transition_machine_star_i:
  NF_transition M q_0 cs q ⇒ NF_transition (machine_star M) (SUC q_0) cs (SUC q)
Proof
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  rw[] >> qexists_tac ‘SUC q_0'’ >> rw[] >> rw[machine_star_def] >> rw[]
QED

Theorem NF_transition_cons =
        NF_transition_rules |> SPEC_ALL |> CONJUNCT2 |> Q.GEN‘a’;

Theorem machine_star_single:
  x ∈ recogLangN M0 ⇒ x ∈ recogLangN (machine_star M0)
Proof
  simp[recogLangN_def, Sipser_ND_Accepts_NF_transition_l] >>
  rw[] >> drule NF_transition_machine_star_i >> rw[] >>
  qexists_tac ‘NONE::l ++ [NONE]’ >> simp[] >> irule NF_transition_cons >>
  rw[] >> irule NF_transition_concat >> rw[] >> qexists_tac ‘SUC q’ >> rw[] >>
  irule NF_transition_cons >> rw[] >> qexists_tac ‘0’ >>
  rw[NF_transition_rules] >> rw[machine_star_def]
QED

Theorem thm_1_50:
  regularLanguage L ⇒ regularLanguage (KSTAR L)
Proof
  simp[corollary_1_40] >>
  disch_then (qx_choose_then ‘M0’ strip_assume_tac) >>
  qexists_tac ‘machine_star M0’ >>
  simp[wfNFA_machine_star, KSTAR_DEF_ALT, Once EXTENSION, PULL_EXISTS,EQ_IMP_THM] >>
  qx_gen_tac ‘str’ >> conj_tac
  >- (simp[recogLangN_def, Sipser_ND_Accepts_NF_transition] >>
      rw[] >> pop_assum mp_tac >>
      completeInduct_on ‘LENGTH (munge n (ZIP (str,nlist)))’ >>
      fs[PULL_FORALL] >> rw[] >> drule NF_transition_machine_star >>
      rw[]
      >- (rfs[ZIP_EQ_NIL] >> qexists_tac ‘0’ >> rw[DOTn_def]) >>
      rename1 ‘NONE::(s1 ++ [NONE] ++ s2)’ >>
      ‘NONE::(s1 ++ [NONE] ++ s2) = (NONE::s1 ++ [NONE] ++ s2)’
        by rw[] >>
      pop_assum SUBST_ALL_TAC >>
      drule_then strip_assume_tac munge_split >> rw[] >>
      rfs[] >> rw[] >>
      first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos last) mp_tac) >>
      simp[] >> disch_then (qx_choose_then ‘N’ strip_assume_tac) >>
      qexists_tac ‘SUC N’ >>
      simp[DOTn_def] >>
      simp[dot_def] >>
      qexistsl_tac [‘drop_epsilon s1’,‘strR’] >>
      simp[recogLangN_def,Sipser_ND_Accepts_NF_transition] >>
      metis_tac[munge_drop_epsilon_exists]) >>
  qx_gen_tac ‘n’ >> MAP_EVERY qid_spec_tac [‘str’,‘n’] >>
  fs[recogLangN_def, Sipser_ND_Accepts_NF_transition_l] >>
  rw[] >> pop_assum mp_tac >> qid_spec_tac ‘str’ >>
  Induct_on ‘n’
  >- (simp[DOTn_def] >> qexists_tac ‘[]’ >> rw[NF_transition_rules])
  >> simp[DOTn_def, dot_def, PULL_EXISTS] >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac ‘NONE::l++[NONE]++l'’ >>
  rw[] >> irule NF_transition_cons >> rw[] >> irule NF_transition_concat >>
  qexists_tac ‘0’ >> rw[] >> irule NF_transition_concat >>
  qexists_tac ‘SUC q’ >> rw[]
  >- rw[NF_transition_machine_star_i]
  >> irule NF_transition_cons >> rw[] >> qexists_tac ‘0’ >>
  rw[NF_transition_rules] >> rw[machine_star_def]
QED

(* TODO: Closure under complement, reversal *)

(*===========================================================================*)
(* Regular expressions. A more elaborate version is in regexpScript, need to *)
(* reconcile.                                                                *)
(*===========================================================================*)

Datatype:
regexp = Concat regexp regexp |
         Star regexp |
         Alt regexp regexp |
         Single num |
         Epsilon |
         Empty
End

Definition regexp_lang[simp]:
  regexp_lang (Concat r1 r2) = regexp_lang r1 dot regexp_lang r2 ∧
  regexp_lang (Star r) = KSTAR (regexp_lang r) ∧
  regexp_lang (Alt r1 r2) = regexp_lang r1 ∪ regexp_lang r2 ∧
  regexp_lang (Single c) = { [c] } ∧
  regexp_lang Epsilon = { [] } ∧
  regexp_lang Empty = {}
End

Theorem lemma_1_55:
  ∀r. regularLanguage (regexp_lang r)
Proof
  Induct >> simp[]
  >- metis_tac[thm_1_47]
  >- metis_tac[thm_1_50]
  >- metis_tac[thm_1_25]
  >- (rw[regularLanguage_def] >>
      qexists_tac ‘<| Q := {0;1;2};
                      A := {n};
                      tf := (λs0 c. if c = n ∧ s0 = 1 then 2 else 0);
                      q_0 := 1;
                      C := {2};|>’ >>
      conj_asm1_tac >>
      rw[wf_dfa_def, recogLangD_def] >>
      rw[EXTENSION, has_Accepting_Execution_Delta_coincide] >>
      rw[accepts_def] >> eq_tac
      >- (Cases_on ‘x’ >> rw[]
          >- (Cases_on ‘t’ >> fs[Delta_def] >> Induct_on‘t'’ >> fs[])
          >> Induct_on ‘t’ >> fs[])
      >> simp[])
  >- (rw[regularLanguage_def] >>
      qexists_tac ‘<| Q := {0;1};
                      A := {};
                      tf := (λs0 c. 0);
                      q_0 := 1;
                      C := {1};|>’ >>
      conj_asm1_tac >>
      rw[wf_dfa_def, recogLangD_def] >>
      rw[EXTENSION, has_Accepting_Execution_Delta_coincide] >>
      rw[accepts_def] >> eq_tac
      >- (Cases_on ‘x’ >> rw[] >> Induct_on ‘t’ >> simp[])
      >> simp[])
  >> rw[regularLanguage_def] >>
     qexists_tac ‘<| Q := {0;1;2};
                      A := {};
                      tf := (λs0 c. 0);
                      q_0 := 1;
                      C := {2};|>’ >>
     conj_asm1_tac >>
     rw[wf_dfa_def, recogLangD_def] >>
     rw[EXTENSION, has_Accepting_Execution_Delta_coincide] >>
     rw[accepts_def] >>
     Cases_on ‘x’ >> rw[] >> Induct_on ‘t’ >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Every FSA has a corresponding regexp, via GNFAs                           *)
(*---------------------------------------------------------------------------*)

(* Definition 1.64 *)
Datatype:
  gnfa = <|
    Q : state set;
    A : symbol set;
    tf : state -> state -> regexp;
    q_0 : state;
    C : state;
  |>
End

Definition wfm_gnfa_def:
  wfm_gnfa G ⇔ FINITE G.Q ∧ G.q_0 ∈ G.Q ∧ G.C ∈ G.Q ∧ G.q_0 ≠ G.C ∧
               (∀s. G.tf s G.q_0 = Empty) ∧
               (∀s. G.tf G.C  s = Empty)
End

Inductive gnfa_accepts:
[~nil:]
  ∀q_0. q_0 IN G.Q ⇒ gnfa_accepts G q_0 [] q_0
[~step:]
  ∀q' q. q_0 IN G.Q ∧ q' IN G.Q ∧ c1 ∈ regexp_lang (G.tf q_0 q') ∧
         gnfa_accepts G q' c2 q ⇒
         gnfa_accepts G q_0 (c1++c2) q
End

Inductive charset_reR:
  charset_reR ∅ Empty ∧
  (e ∉ s ∧ charset_reR s re ⇒ charset_reR (e INSERT s) (Alt (Single e) re))
End

Theorem charset_reR_correct:
  charset_reR cs re ⇒ regexp_lang re = {[c] | c ∈ cs}
Proof
  Induct_on ‘charset_reR’ >> rw[EXTENSION] >> metis_tac[]
QED

Theorem charset_reR_exists:
  ∀cs. FINITE cs ⇒ ∃re. charset_reR cs re
Proof
  Induct_on ‘FINITE’ >> metis_tac[charset_reR_rules]
QED

Definition charset_re_def:
  charset_re cs = @re. charset_reR cs re
End

Theorem regexp_lang_charset_re:
  ∀cs. FINITE cs ⇒ regexp_lang (charset_re cs) = {[c] | c ∈ cs}
Proof
  rw[charset_re_def] >> SELECT_ELIM_TAC >>
  simp[charset_reR_correct, charset_reR_exists]
QED

Definition dfa_to_gnfa_def:
  dfa_to_gnfa d = <| Q := {0; 1} ∪ IMAGE ($+2) d.Q;
                          A := d.A;
                          tf := (λs1 s2. if s1 = 0 ∧ s2 = d.q_0+2 then Epsilon
                                         else if s1 ∈ IMAGE ($+2) d.C ∧ s2 = 1
                                         then
                                           Epsilon
                                         else if 1 < s1 ∧ 1 < s2 then
                                         let s = {cs | d.tf (s1-2) cs = s2-2}
                                         in
                                            charset_re s
                                         else Empty);
                          q_0 := 0;
                          C := 1; |>
End

Theorem dfa_to_gnfa_wfm:
  wf_dfa d ⇒ wfm_gnfa (dfa_to_gnfa d)
Proof
  rw[wf_dfa_def, wfm_gnfa_def, dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_q_0[simp]:
  ∀d. (dfa_to_gnfa d).q_0 = 0
Proof
  rw[dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_tf_0[simp]:
  ∀d x. ((dfa_to_gnfa d).tf 0 x = if x = d.q_0 + 2 then Epsilon else Empty) ∧
        ((dfa_to_gnfa d).tf x 0 = Empty)
Proof
  rw[dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_Q[simp]:
  ∀d. (dfa_to_gnfa d).Q = {0;1} ∪ {q+2 | q ∈ d.Q}
Proof
  rw[EXTENSION ,dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_never_looks_back:
  ∀d s. gnfa_accepts (dfa_to_gnfa d) s cs 0 ⇒ (s = 0 ∧ cs = [])
Proof
  rpt gen_tac >> Induct_on ‘gnfa_accepts’ >>
  rw[] >> fs[]
QED

Theorem dfa_prod_gnfa_shuffle_start:
  ∀d cs es. gnfa_accepts (dfa_to_gnfa d) (d.q_0 + 2) cs es
              ⇔ es ≠ 0 ∧ gnfa_accepts (dfa_to_gnfa d) (dfa_to_gnfa d).q_0 cs es
Proof
  rw[SimpRHS, Once gnfa_accepts_cases] >>
  simp_tac (srw_ss () ++ boolSimps.COND_elim_ss) [] >>
  rw[EQ_IMP_THM] >>
  fs[Once gnfa_accepts_cases]
  >- (strip_tac >>
      fs[] >>
      drule_all_then strip_assume_tac dfa_to_gnfa_never_looks_back >>
      fs[] >> rw[] >> fs[])
  >- (rpt strip_tac >> rw[] >> fs[] >>
      metis_tac[dfa_to_gnfa_never_looks_back, DECIDE “1≠0”]) >>
  rpt strip_tac >> rw[] >> fs[] >>
  metis_tac[dfa_to_gnfa_never_looks_back, DECIDE “q+2≠0”]
QED

Theorem dfa_to_gnfa_c[simp]:
  (dfa_to_gnfa d).C = 1
Proof
  rw[dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_final_state_no_op:
∀d s.
  wf_dfa d ∧ s ∈ d.Q ∧ s ∈ d.C
  ⇒
  gnfa_accepts (dfa_to_gnfa d) (s + 2) [] 1
Proof
  rw[] >>
  ‘[] ∈ regexp_lang ((dfa_to_gnfa d).tf (s+2) 1)’ by rw[dfa_to_gnfa_def] >>
  ‘1 ∈ (dfa_to_gnfa d).Q ∧ s+2 ∈ (dfa_to_gnfa d).Q’ by simp[] >>
  dxrule_then (drule_then (drule_then strip_assume_tac)) gnfa_accepts_step >>
  fs[] >> simp[gnfa_accepts_rules]
QED

Theorem Delta_c_in_A:
  ∀d s c cs. Delta d (d.tf s c) cs ∈ d.C ∧ wf_dfa d ⇒ c ∈ d.A
Proof
  CCONTR_TAC >> fs[] >> ‘d.tf s c = 0’ by fs[wf_dfa_def] >> fs[] >>
  drule_then strip_assume_tac Delta_0_Sink >> metis_tac[wf_dfa_def]
QED

Theorem gnfa_error_sink:
  ∀d. (wf_dfa d ⇒ ∀q cs. gnfa_accepts (dfa_to_gnfa d) 2 cs q ⇒ (q = 2))
Proof
  ntac 2 strip_tac >>
  Induct_on ‘gnfa_accepts’ >>
  rw[] >> fs[]
  >- (rw[] >> fs[dfa_to_gnfa_def] >> rfs[wf_dfa_def]) >>
  rw[] >>
  pop_assum irule >>
  pop_assum kall_tac >>
  fs[dfa_to_gnfa_def] >>
  rfs[wf_dfa_def] >> rw[] >> CCONTR_TAC >> fs[] >>
  fs[regexp_lang_charset_re]
QED

Theorem Delta_append[simp]:
  ∀d s c1 c2. Delta d s (c1++c2) = Delta d (Delta d s c1) c2
Proof
  Induct_on ‘c1’ >> rw[]
QED

Theorem gnfa_accepts_1_to_1:
  ∀d cs. wf_dfa d ∧ gnfa_accepts (dfa_to_gnfa d) 1 cs 1 ⇒ cs = []
Proof
  rw[Once gnfa_accepts_cases] >> qpat_x_assum ‘c1 ∈ _’ mp_tac >>
  rw[dfa_to_gnfa_def]
QED

Theorem gnfa_accepts_2_to_1:
  ∀d cs. wf_dfa d ⇒ ¬gnfa_accepts (dfa_to_gnfa d) 2 cs 1
Proof
  ‘∀d x cs y. gnfa_accepts (dfa_to_gnfa d) x cs y ⇒ x = 2 ⇒ y = 1 ⇒ wf_dfa d ⇒ F’
    suffices_by metis_tac[] >> gen_tac >>
  ho_match_mp_tac gnfa_accepts_ind >> rw[] >>
  fs[dfa_to_gnfa_def] >> strip_tac >> fs[] >> fs[wf_dfa_def] >>
  Cases_on ‘1 < x'’ >> fs[regexp_lang_charset_re]
QED

Theorem dfa_to_gnfa_correct:
  ∀d. wf_dfa d ⇒
      ∃g. wfm_gnfa g ∧ ∀cs. has_Accepting_Execution d cs ⇔ gnfa_accepts g g.q_0 cs g.C
Proof
  rw[] >> qexists_tac ‘dfa_to_gnfa d’ >> rw[dfa_to_gnfa_wfm] >>
  rw[has_Accepting_Execution_Delta_coincide_thm,accepts_def] >>
  ‘∀s. s ∈ d.Q ⇒
    (Delta d s cs ∈ d.C ⇔
    gnfa_accepts (dfa_to_gnfa d) (s + 2) cs (dfa_to_gnfa d).C)’
    suffices_by (fs[dfa_prod_gnfa_shuffle_start,wf_dfa_def] >>
                 simp[dfa_to_gnfa_def]) >>
  simp[EQ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM] >> conj_tac
  >- (Induct_on ‘cs’
      >- rw[dfa_to_gnfa_final_state_no_op]
      >> rw[] >> ‘h::cs = [h]++cs’ by simp[] >> pop_assum SUBST_ALL_TAC >>
      irule $ CONJUNCT2 $ SPEC_ALL gnfa_accepts_rules >> simp[] >>
      qexists_tac ‘(d.tf s h)+2’ >> rw[]
      >- (rw[dfa_to_gnfa_def] >>
         ‘FINITE {cs | d.tf s cs = d.tf s h}’
            by (irule SUBSET_FINITE_I >> qexists_tac ‘d.A’ >> conj_tac
                >- fs[wf_dfa_def]
                >> rw[SUBSET_DEF] >> metis_tac[Delta_c_in_A]) >>
          simp[regexp_lang_charset_re])
      >- (fs[wf_dfa_def] >> metis_tac[]) >>
      first_x_assum irule >> rw[] >> metis_tac[wf_dfa_def, Delta_c_in_A]) >>
  Induct_on ‘gnfa_accepts’ >> rw[] >> qpat_x_assum ‘c1 ∈ _’ mp_tac >>
  rw[dfa_to_gnfa_def] >> fs[]
  >- (drule gnfa_accepts_1_to_1 >> rw[]) >>
  rfs[] >> rw[] >> ‘Delta d q c1 = q'’ suffices_by simp[] >>
  ‘FINITE {cs | d.tf q cs = q'}’
        by (irule SUBSET_FINITE_I >> qexists_tac ‘d.A’ >> fs[wf_dfa_def] >>
            rw[SUBSET_DEF] >> metis_tac[Delta_c_in_A, wf_dfa_def]) >>
  fs[regexp_lang_charset_re] >> rw[] >> fs[wf_dfa_def]
QED

Definition rip_def:
  rip G q = if q IN G.Q ∧ q ≠ G.q_0 ∧ q <> G.C then
            G with
            <| Q := G.Q DELETE q ;
               tf := \i j. if i = G.C then Empty
                           else if j = G.q_0 then Empty
                           else
                             Alt (Concat (G.tf i q)
                                  (Concat (Star (G.tf q q)) (G.tf q j)))
                                 (G.tf i j)
             |>
            else G
End

Theorem wfm_rip_wfm:
  wfm_gnfa G ⇒ wfm_gnfa (rip G q)
Proof
  rw[rip_def,wfm_gnfa_def]
QED

Theorem gnfa_accepts_q_in_Q:
  ∀G q_0 l q. gnfa_accepts G q_0 l q ⇒ q_0 ∈ G.Q ∧ q ∈ G.Q
Proof
  gen_tac >> Induct_on ‘gnfa_accepts’ >> simp[]
QED

Theorem gnfa_accepts_star:
 ∀x G q_0 l q.
   x IN KSTAR (regexp_lang (G.tf q_0 q_0)) ∧
   gnfa_accepts G q_0 l q ⇒ gnfa_accepts G q_0 (x ⧺ l) q
Proof
 simp[KSTAR_DEF_ALT, PULL_EXISTS] >>
 CONV_TAC (RENAME_VARS_CONV ["s","G","q_0","l","q","n"]) >>
 Induct_on ‘n’ >> simp[DOTn_def,dot_def,PULL_EXISTS] >> rw[] >>
 metis_tac[APPEND_ASSOC,gnfa_accepts_step,gnfa_accepts_q_in_Q]
QED

Theorem G_rip_Q:
q ∈ G.Q ∧ q ≠ G.q_0 ∧ q ≠ G.C ⇒ (rip G q).Q = G.Q DELETE q
Proof
rw[rip_def]
QED


Theorem G_rip_back_sim:
  ∀q_0 s. wfm_gnfa G ∧ q_0 ≠ q ∧ q ≠ G.q_0 ∧ q ≠ G.C ∧ q IN G.Q ∧
         gnfa_accepts (rip G q) q_0 s G.C ⇒ gnfa_accepts G q_0 s G.C
Proof
  Induct_on ‘gnfa_accepts’ >>
  reverse (rw[rip_def,gnfa_accepts_rules])
  >- metis_tac[gnfa_accepts_rules]
  >> Cases_on ‘q_0 = G.C’ >> fs[] >>
  Cases_on ‘q_0' = G.q_0’ >> reverse (fs[])
  >- (reverse (Cases_on ‘q_0' = q’)
      >- metis_tac[gnfa_accepts_rules]
      >> fs[])
  >> fs[dot_def] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  irule gnfa_accepts_step >> simp[] >>
  qexists_tac ‘q’ >>
  ASM_REWRITE_TAC [GSYM APPEND_ASSOC] >> irule gnfa_accepts_star >> simp[] >>
  metis_tac[gnfa_accepts_step,gnfa_accepts_q_in_Q]
QED

Inductive gnfaA':
  (∀q_0. q_0 ∈ G.Q ⇒ gnfaA' G q_0 [] [q_0] q_0) ∧
  (∀q_0 q1 q2 s1 s2 states.
     q_0 ∈ G.Q ∧ q1 ∈ G.Q ∧
     s1 ∈ regexp_lang (G.tf q_0 q1) ∧
     gnfaA' G q1 s2 states q2
     ⇒
     gnfaA' G q_0 (s1 ++ s2) (q_0::states) q2)
End

Theorem gnfaA'_states_nonempty:
  gnfaA' G q_0 str sts q ⇒ sts ≠ [] ∧ HD sts = q_0 ∧ LAST sts = q
Proof
  Induct_on ‘gnfaA'’ >> simp[LAST_CONS_cond]
QED

Theorem gnfa_accepts_gnfaA':
  gnfa_accepts G q_0 str q ⇒ ∃sts. gnfaA' G q_0 str sts q
Proof
  Induct_on ‘gnfa_accepts’ >> simp[] >> metis_tac[gnfaA'_rules]
QED

Theorem gnfaA'_gnfa_accepts:
  gnfaA' G q_0 str sts q ⇒ gnfa_accepts G q_0 str q
Proof
  Induct_on ‘gnfaA'’ >> simp[gnfa_accepts_rules] >>
  metis_tac[gnfa_accepts_rules]
QED

Theorem IN_ripQ:
  x ≠ r ∧ x IN G.Q ⇒ x IN (rip G r).Q
Proof
  rw[rip_def]
QED

Theorem repeated_head_elements:
  ∀l e. ∃n sfx. l = REPLICATE n e ++ sfx ∧ (sfx ≠ [] ⇒ HD sfx ≠ e)
Proof
  rpt gen_tac >> Induct_on ‘l’ >> simp[] >> fs[] >>
  qx_gen_tac ‘h’ >> Cases_on ‘h = e’
  >- (rw[] >> qexistsl_tac [‘SUC n’, ‘sfx’] >> simp[]) >>
  qexistsl_tac [‘0’, ‘h::REPLICATE n e ++ sfx’] >> simp[]
QED

Theorem gnfaA'_APPEND_states:
  ∀G q_0 str sts1 sts2 q.
    gnfaA' G q_0 str (sts1 ++ sts2) q ∧ sts1 ≠ [] ∧ sts2 ≠ [] ⇒
    ∃str1 str2 q1. str = str1 ++ str2 ∧
                   q1 ∈ G.Q ∧
                   gnfaA' G q_0 str1 (sts1 ++ [HD sts2]) q1 ∧
                   gnfaA' G q1 str2 sts2 q
Proof
  Induct_on ‘sts1’ >> rw[] >> qpat_x_assum (‘gnfaA' _ _ _ _ _’) mp_tac >>
  simp[Once gnfaA'_cases, SimpL “$==>”] >> rw[] >>
  Cases_on ‘sts1 = []’
  >- (rw[] >> fs[] >>
      first_assum (goal_assum o resolve_then (Pos last) mp_tac) >>
      simp[] >> drule gnfaA'_states_nonempty >> rw[] >>
      drule_at (Pos $ el 3) (cj 2 gnfaA'_rules) >> rw[] >>
      first_x_assum (resolve_then (Pos hd) mp_tac (cj 1 gnfaA'_rules)) >>
      rw[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_assum (goal_assum o resolve_then (Pos last) mp_tac) >> rw[] >>
  drule_at (Pos $ el 3) (cj 2 gnfaA'_rules) >> rw[]
QED

Theorem gnfaA'_q_to_q_0:
  wfm_gnfa G ⇒ gnfaA' G q str sts G.q_0 ⇒ q = G.q_0 ∧ sts = [G.q_0]
Proof
  Induct_on ‘gnfaA'’ >> rw[] >> Cases_on ‘wfm_gnfa G’ >> fs[] >> rw[] >>
  fs[wfm_gnfa_def]
QED

Theorem gnfaA'_in_G:
∀s l q_0 q. gnfaA' G q_0 s l q ⇒ ∀st. MEM st l ⇒ st IN G.Q
Proof
Induct_on ‘gnfaA'’ >> simp[DISJ_IMP_THM]
QED

Theorem gnfaA'_APPEND_states2:
  ∀G q_0 str sts1 sts2 q.
         gnfaA' G q_0 str (sts1 ⧺ sts2) q ∧ sts1 ≠ [] ∧ sts2 ≠ [] ⇒
         ∃str1 str2 q1.
             str = str1 ⧺ str2 ∧ q1 ∈ G.Q ∧
             gnfaA' G q_0 str1 sts1 q1 ∧ gnfaA' G q1 str2 (LAST sts1 :: sts2) q
Proof
 rw[] >> Cases_on ‘sts1’ >> fs[] >> rename [‘q1 :: (sts1 ++ sts2)’] >>
 ‘q_0 = q1’ by (drule gnfaA'_states_nonempty >> simp[]) >> rw[] >>
 Cases_on ‘sts1 = []’ >> fs[] (* 2 *)
 >- (first_assum (goal_assum o resolve_then (Pos last) mp_tac) >>
     csimp[gnfaA'_rules] >>
     metis_tac[gnfaA'_in_G,MEM]) >>
 ‘q_0::(sts1 ⧺ sts2) = FRONT (q_0::sts1) ++ LAST (q_0::sts1) :: sts2’
   by (‘LAST (q_0::sts1)::sts2 = [LAST (q_0::sts1)] ++ sts2’ by simp[] >>
      simp[APPEND_FRONT_LAST]) >>
 qpat_x_assum ‘gnfaA' _ _ _ _ _’ mp_tac >> simp[] >>
 strip_tac >> drule gnfaA'_APPEND_states >> simp[APPEND_FRONT_LAST]
QED

Theorem gnfaA'_REPLICATE:
  ∀G q s n.
    gnfaA' G q s (REPLICATE n q) q ⇒
    s ∈ KSTAR (regexp_lang (G.tf q q))
Proof
  Induct_on ‘n’ >> rw[]
  >- fs[Once gnfaA'_cases]  >>
  pop_assum mp_tac >> simp[Once gnfaA'_cases] >>
  rw[] >- fs[EMPTY_IN_KSTAR] >>
  Cases_on ‘n = 0’
  >- (qpat_x_assum ‘gnfaA' _ _ _ _ _ ’ mp_tac >> simp[Once gnfaA'_cases]) >>
  rename [‘s1 ∈ regexp_lang (G.tf q q1)’] >>
  ‘q1 = q’
    by (drule gnfaA'_states_nonempty >>
        simp[HD_REPLICATE]) >>
  gvs[] >> first_x_assum $ drule_all_then assume_tac >>
  gvs[KSTAR_FLAT] >> rename1 ‘s1 ++ FLAT ls’ >> qexists_tac ‘s1::ls’ >>
  rw[] >> rw[]
QED

Theorem gnfaA'_rip_filter:
  ∀sts q_0 str q r.
    wfm_gnfa G ∧ gnfaA' G q_0 str sts q ∧ q_0 ≠ r ∧ q ≠ r ∧ r ∈ G.Q ∧ r ≠ G.q_0 ∧
    r ≠ G.C ⇒
    gnfaA' (rip G r) q_0 str (FILTER (λq. q ≠ r) sts) q
Proof
  gen_tac >>
  completeInduct_on ‘LENGTH sts’ >> fs[PULL_FORALL] >> rpt gen_tac >>
  strip_tac >>
  simp[Once gnfaA'_cases, SimpL “$==>”] >> rw[]
  >- simp[IN_ripQ, gnfaA'_rules] >>
  simp[] >>
  qspecl_then [‘states’, ‘r’] (qx_choosel_then [‘n’, ‘sfx’] strip_assume_tac)
              repeated_head_elements >>
  rw[FILTER_APPEND, FILTER_REPLICATE] >>
  drule gnfaA'_APPEND_states >> simp[] >> Cases_on ‘sfx = []’ >> rw[]
  >- (fs[] >> drule gnfaA'_states_nonempty >> rw[] >> fs[LAST_REPLICATE]) >>
  Cases_on ‘n = 0’ >> fs[] >> rw[]
  >- (irule (cj 2 gnfaA'_rules) >> rw[IN_ripQ] >> qexists_tac ‘q1’ >> rw[]
      >- (rw[rip_def] >> fs[wfm_gnfa_def] >> rfs[])
      >- (drule gnfaA'_states_nonempty >> rw[] >> rw[IN_ripQ]) >>
      first_x_assum irule >> rw[] >> drule gnfaA'_states_nonempty >> rw[]) >>
  ‘q1 = r’ by (rev_drule gnfaA'_states_nonempty >> rw[] >>
               simp[HD_APPEND, HD_REPLICATE]) >>
  rw[] >> rename [‘gnfaA' G q1 str1 (REPLICATE n q1 ⧺ [HD sfx]) q2’] >>
  ‘q2 = HD sfx’ by (drule gnfaA'_states_nonempty >> rw[]) >> rw[] >>
  irule (cj 2 gnfaA'_rules) >> rw[IN_ripQ] >> qexists_tac ‘HD sfx’ >>
  rw[] (* 2 *)
  >- (simp[rip_def] >> rw[]
      >- rfs[wfm_gnfa_def]
      >- (fs[] >> rw[] >> drule_all gnfaA'_q_to_q_0 >> rw[]) >>
      DISJ1_TAC >> simp[Once dot_def] >> goal_assum (drule_at (Pos $ el 2))>>
      simp[] >>
      drule gnfaA'_APPEND_states2 >> simp[] >> strip_tac >>
      drule gnfaA'_states_nonempty >> simp[] >> rw[] >> rfs[LAST_REPLICATE] >>
      simp[dot_def] >> simp[] >>
      rename [‘s1 ++ s2 = _ ++ _’] >> qexistsl_tac [‘s1’,‘s2’] >> simp[] >>
      reverse conj_tac (* 2 *)
      >- (pop_assum mp_tac >> simp[Ntimes gnfaA'_cases 3]) >>
      metis_tac[gnfaA'_REPLICATE]) >>
  rw[rip_def]
QED

Theorem G_rip_forw_sim:
  ∀q_0 s q1 q. wfm_gnfa G ∧ q_0 ∈ G.Q ∧ q ≠ q_0 ∧ q1 ∈ G.Q ∧ q ≠ q1 ∧ q ∈ G.Q ∧
         gnfa_accepts G q_0 s q1 ⇒ gnfa_accepts (rip G q) q_0 s q1
Proof
  rw[] >>
  Cases_on ‘q = G.q_0’ >- gvs[rip_def] >>
  Cases_on ‘q = G.C’  >- gvs[rip_def] >>
  metis_tac[gnfaA'_gnfa_accepts,gnfa_accepts_gnfaA',gnfaA'_rip_filter]
QED

Theorem G_rip_sim:
  ∀s q. wfm_gnfa G ∧ q ≠ G.q_0 ∧ q ≠ G.C ∧ q ∈ G.Q ⇒
         (gnfa_accepts (rip G q) G.q_0 s G.C ⇔ gnfa_accepts G G.q_0 s G.C)
Proof
  metis_tac[G_rip_back_sim,G_rip_forw_sim,wfm_gnfa_def]
QED

Definition reduced_gnfa_def:
  reduced_gnfa G =
    if FINITE G.Q ∧ 2 < CARD G.Q then
      reduced_gnfa (rip G (MAX_SET (G.Q DIFF {G.q_0; G.C})))
    else
      G
Termination
  WF_REL_TAC ‘measure (λG. CARD G.Q)’ >>
  rw[rip_def] >> Cases_on ‘FINITE G.Q’ >> simp[] >> strip_tac >>
  ‘G.Q DIFF {G.q_0; G.C} ≠ ∅’
    by (simp[SUBSET_DIFF_EMPTY] >> strip_tac >>
        drule_at (Pos last) CARD_SUBSET >>
        gvs[]) >>
  ‘FINITE (G.Q DIFF {G.q_0; G.C})’
    by simp[] >>
  drule_all (cj 1 MAX_SET_DEF) >> gvs[]
End

Theorem reduced_gnfa_same:
  wfm_gnfa G ⇒
    (gnfa_accepts G G.q_0 s G.C ⇔
    gnfa_accepts (reduced_gnfa G) (reduced_gnfa G).q_0 s (reduced_gnfa G).C)
Proof
  reverse (Cases_on ‘FINITE G.Q’)
  >- (ntac 3 (rw[Once reduced_gnfa_def])) >>
  pop_assum mp_tac >> qid_spec_tac ‘G’ >>
  ho_match_mp_tac reduced_gnfa_ind  >> rw[] >>
  qabbrev_tac ‘ms = MAX_SET (G.Q DIFF {G.q_0; G.C})’ >>
  gvs[] >> reverse (Cases_on ‘2 < CARD G.Q’)
  >- (ntac 3 (rw[Once reduced_gnfa_def])) >>
  gvs[] >>
  ‘FINITE (rip G ms).Q’
    by rw[rip_def] >>
  gvs[wfm_rip_wfm] >>
  ONCE_REWRITE_TAC [reduced_gnfa_def] >>
  simp[] >>
  last_x_assum (SUBST1_TAC o SYM) >>
  simp[Once EQ_SYM_EQ] >>
  ‘(rip G ms).q_0 = G.q_0 ∧ (rip G ms).C = G.C’
    by rw[rip_def] >>
  simp[] >> irule G_rip_sim >>
  qunabbrev_tac ‘ms’ >>
  ‘G.Q DIFF {G.q_0; G.C} ≠ ∅’
    by (simp[SUBSET_DIFF_EMPTY] >> strip_tac >>
        drule_at (Pos last) CARD_SUBSET >>
        gvs[]) >>
  ‘FINITE (G.Q DIFF {G.q_0; G.C})’
    by simp[] >>
  drule_all (cj 1 MAX_SET_DEF) >> gvs[]
QED

Theorem reduced_gnfa_facts[simp]:
  ∀GN. (reduced_gnfa GN).q_0 = GN.q_0 ∧ (reduced_gnfa GN).C = GN.C
Proof
  ho_match_mp_tac reduced_gnfa_ind >> simp[] >> qx_gen_tac ‘GN’ >> strip_tac >>
  ONCE_REWRITE_TAC[reduced_gnfa_def] >>
  Cases_on ‘FINITE GN.Q ∧ 2 < CARD GN.Q’ >> simp[] >>
  qmatch_abbrev_tac ‘(rip GN s).q_0 = GN.q_0 ∧ _’ >>
  rw[rip_def]
QED

Theorem reduced_gnfas_have_two_states:
  ∀GN. wfm_gnfa GN ⇒
       (reduced_gnfa GN).Q = {GN.q_0 ; GN.C }
Proof
  ho_match_mp_tac reduced_gnfa_ind >> qx_gen_tac ‘GN’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [reduced_gnfa_def] >> reverse (rw[])
  >- (gvs[wfm_gnfa_def, arithmeticTheory.NOT_LESS] >>
      simp[EXTENSION, EQ_IMP_THM, DISJ_IMP_THM] >> CCONTR_TAC >> gvs[] >>
      rename [‘s ≠ GN.C’, ‘s ≠ GN.q_0’] >>
      ‘{s; GN.C; GN.q_0} ⊆ GN.Q’ by simp[SUBSET_DEF] >>
      ‘CARD {s;GN.C;GN.q_0} ≤ CARD GN.Q’ by metis_tac[CARD_SUBSET] >>
      gvs[]) >>
  gvs[wfm_rip_wfm] >> rw[rip_def]
QED

Theorem wfm_gnfa_reduced:
  ∀GN. wfm_gnfa GN ⇒ wfm_gnfa (reduced_gnfa GN)
Proof
  ho_match_mp_tac reduced_gnfa_ind >> rw[] >>
  ONCE_REWRITE_TAC [reduced_gnfa_def] >> rw[] >> gvs[] >>
  simp[wfm_rip_wfm]
QED

Theorem thm_1_54_ltr:
  ∀l. regularLanguage l ⇒ ∃r. regexp_lang r = l
Proof
  simp[regularLanguage_def, recogLangD_def, PULL_EXISTS] >>
  simp[EXTENSION] >>
  qx_gen_tac ‘D’ >> strip_tac >>
  drule_then (qx_choose_then ‘GN’ strip_assume_tac) dfa_to_gnfa_correct >>
  simp[] >>
  drule_then strip_assume_tac reduced_gnfa_same >> simp[] >>
  ‘wfm_gnfa (reduced_gnfa GN)’ by simp[wfm_gnfa_reduced] >>
  ONCE_REWRITE_TAC [gnfa_accepts_cases] >>
  ‘GN.C ≠ GN.q_0’ by gvs[wfm_gnfa_def] >> simp[reduced_gnfas_have_two_states] >>
  qexists_tac ‘(reduced_gnfa GN).tf GN.q_0 GN.C’ >> qx_gen_tac ‘str’ >> eq_tac
  >- (strip_tac >> qexistsl_tac [‘str’, ‘[]’, ‘GN.C’] >>
      simp[Once gnfa_accepts_cases, reduced_gnfas_have_two_states]) >>
  rw[] >- gvs[wfm_gnfa_def] >>
  ‘c2 = []’ suffices_by simp[] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC[gnfa_accepts_cases] >>
  rw[] >> gvs[wfm_gnfa_def]
QED

Theorem thm_1_54:
  regularLanguage l ⇔ ∃r. regexp_lang r = l
Proof
  metis_tac[thm_1_54_ltr, lemma_1_55]
QED

Definition exp_def:
  (exp s 0 = []) ∧
  (exp s (SUC n) = s ++ (exp s n))
End

Theorem wf_dfa_remain_Q:
  ∀M. wf_dfa M ⇒
    ∀ss.
      (∀n. n < LENGTH ss - 1 ⇒
          ∃c.
            M.tf (EL n ss) c = (EL (SUC n) ss)) ∧
      HD ss ∈ M.Q ⇒
      (∀e. MEM e ss ⇒ e ∈ M.Q)
Proof
 ntac 2 strip_tac >>
 Induct_on ‘ss’ >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
 rw[] >>
 first_x_assum irule >>
 rw[]
 >- (first_x_assum (qspec_then ‘SUC n’ assume_tac) >>
     rfs[] >> metis_tac[])
 >- (first_x_assum (qspec_then ‘0’ assume_tac) >>
     Cases_on ‘ss’ >> fs[wf_dfa_def] >>
     metis_tac[])
QED

Theorem Delta_segment:
∀i j ss s M.
  (∀n. n < LENGTH ss − 1 ⇒ M.tf (EL n ss) (EL n s) = EL (n + 1) ss) ∧
  i < LENGTH ss ∧ j ≤ i ∧ LENGTH ss = LENGTH s + 1 ⇒
  Delta M (EL j ss) (DROP j (TAKE i s)) = EL i ss
Proof
  Induct_on ‘i - j’ >> rw[] >- (‘i = j’ by simp[] >> rw[DROP_TAKE]) >>
  ‘v = i - (SUC j)’ by simp[] >>
  ‘DROP j (TAKE i s) = EL j s :: DROP (SUC j) (TAKE i s)’
    by simp[DROP_CONS_EL, LENGTH_TAKE, EL_TAKE] >>
  simp[] >> fs[ADD1]
QED

Theorem pumpingLemma:
  ∀l. regularLanguage l ⇒
      ∃p.∀s.
           s ∈ l ∧ p ≤ LENGTH s ⇒
           ∃x y z.
             s = x ++ y ++ z ∧
             ∀i.
               (x ++ exp y i ++ z) ∈ l
Proof
  (* We decided this should be changed to use Delta and
     GENLIST instead of has_Accepting_Execution in the assumptions *)
  rw[regularLanguage_def,recogLangD_def] >>
  qexists_tac ‘SUC (CARD(M.Q))’ >>
  rw[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [has_Accepting_Execution_def]) >>
  fs[] >>
  ‘∃ n m. n < m ∧ m < LENGTH ss ∧ EL n ss = EL m ss’
    by (‘¬INJ (λx. EL x ss) (count (LENGTH ss)) M.Q’
          suffices_by (rw[INJ_IFF]
                       >- (metis_tac[wf_dfa_def,wf_dfa_remain_Q,MEM_EL,
                                     arithmeticTheory.ADD1]) >>
                       rename[‘EL i ss = EL j ss ⇔ i = j’] >>
                       ‘i ≠ j’ by metis_tac[] >>
                       fs[] >>
                       metis_tac[DECIDE “a ≠ b ⇒ a < b ∨ b < a”]) >>
        irule PHP >>
        simp[] >> fs[wf_dfa_def]) >>
  map_every qexists_tac [‘TAKE n s’,‘DROP n (TAKE m s)’,‘DROP m s’] >>
  simp[has_Accepting_Execution_Delta_coincide,accepts_def,Delta_append] >>
  conj_tac
  >- simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", Excl "LIST_EQ_SIMP_CONV",
          GSYM DROP_APPEND1] >> ‘n < LENGTH ss - 1’ by fs[] >>
  ‘Delta M M.q_0 (TAKE n s) = EL n ss’
    by (drule Delta_segment >> rw[] >>
        first_x_assum (qspecl_then [‘n’, ‘0’] MP_TAC) >> simp[]) >> simp[] >>
  ‘∀i. Delta M (EL m ss) (exp (DROP n (TAKE m s)) i) = EL m ss’
    by (Induct_on ‘i’ >> rw[] >> simp[exp_def] >>
        ‘Delta M (EL m ss) (DROP n (TAKE m s)) = EL m ss’
          suffices_by simp[] >> drule Delta_segment >> simp[] >>
        disch_then $ qspecl_then [‘m’, ‘n’] mp_tac >> rw[]) >> simp[] >>
  drule_then (qspecl_then [‘LENGTH s’, ‘m’] mp_tac) Delta_segment >> rw[]>>
  ‘EL (LENGTH s) ss = LAST ss’ suffices_by simp[] >>
  simp[LAST_EL, GSYM ADD1]
QED

val _ = export_theory();

(* Moved stuff: possibly not needed


(*---------------------------------------------------------------------------*)
(* An accepting execution starts in the start state, ends with a state in    *)
(* the accepting state set, and each state in the sequence is obtained by    *)
(* a legit delta transition.                                                 *)
(*---------------------------------------------------------------------------*)

Definition has_Accepting_Execution_def:
  has_Accepting_Execution M w ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      LENGTH ss = LENGTH w + 1 ∧
      HD ss = M.q_0 ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (M.delta (EL n ss) (EL n w) = EL (n + 1) ss)) ∧
      LAST ss ∈ M.C ∧
      wf_dfa M
End

(*---------------------------------------------------------------------------*)
(* The zero state does not occur in an accepting execution                   *)
(*---------------------------------------------------------------------------*)

Theorem has_Accepting_Execution_NoZero:
  has_Accepting_Execution M w ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (∀s. MEM s ss ⇒ s ≠ 0) ∧
      LENGTH ss = LENGTH w + 1 ∧
      HD ss = M.q_0 ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (M.delta (EL n ss) (EL n w) = EL (n + 1) ss)) ∧
      LAST ss ∈ M.C ∧
      wf_dfa M
Proof
  reverse (rw[EQ_IMP_THM])
  >- metis_tac[has_Accepting_Execution_def]
  >- (fs[has_Accepting_Execution_def] >>
      qexists_tac ‘ss’ >>
      rw[] >>
      ‘∀ss w. LAST ss ≠ 0 ∧
              LENGTH ss = LENGTH w + 1 ∧
               (∀n. n < LENGTH ss - 1 ⇒
                    M.delta (EL n ss) (EL n w) =
                    EL (n + 1) ss) ⇒
              ¬MEM 0 ss’
        suffices_by metis_tac[wf_dfa_def] >>
      ntac 5 (last_x_assum (K ALL_TAC)) >>
      Induct_on ‘ss’ >> simp[arithmeticTheory.ADD1] >>
      rw[]
      >> (Cases_on ‘ss’ >> fs[] >>
          Cases_on ‘w’ >> fs[] >>
          rename [‘LAST (s1::st) ≠ 0’,‘EL _ (s0::s1::st)’,
                  ‘LENGTH st = LENGTH ct’,‘EL _ (c0::ct)’] >>
          last_x_assum (qspec_then ‘ct’ assume_tac) >>
          rfs[arithmeticTheory.ADD1] >>
          pop_assum mp_tac >>
          impl_tac
          >- (rw[] >>
              first_x_assum (qspec_then ‘n + 1’ mp_tac) >>
              simp[rich_listTheory.EL_CONS,
                   DECIDE “PRE n = n - 1”])
          >- (strip_tac >> first_x_assum (qspec_then ‘0’ mp_tac) >>
              simp[] >> metis_tac[wf_dfa_def])))
QED

Theorem sipser_rm:
∀ss input.
   (∀n. n < LENGTH input ⇒
        (M.delta (EL n ss) (EL n input) = EL (n + 1) ss)) ∧
   (LENGTH input + 1 = LENGTH ss)  ⇒
   (Delta M (HD ss) input = LAST ss)
Proof
  Induct_on ‘input’ >>
  rw[] >>
  Cases_on ‘ss’ >>
  fs[] >>
  simp[listTheory.LAST_DEF] >>
  rw[] >>
  fs[LT_SUC, DISJ_IMP_THM, FORALL_AND_THM,
     PULL_EXISTS, arithmeticTheory.ADD_CLAUSES]
QED

(*---------------------------------------------------------------------------*)
(* Build an execution starting from a given state                            *)
(*---------------------------------------------------------------------------*)

Definition buildstates_def[simp]:
  buildstates M q [] = [q] ∧
  buildstates M q (c::cs) = q :: buildstates M (M.delta q c) cs
End

Theorem LENGTH_buildstates[simp]:
  ∀q inp. LENGTH (buildstates M q inp) = LENGTH inp + 1
Proof
  Induct_on ‘inp’ >> simp[]
QED

Theorem HD_buildstates[simp]:
  HD (buildstates M q inp) = q
Proof
  Cases_on ‘inp’ >> simp[]
QED

Theorem buildstates_EQ_NIL[simp]:
  buildstates M q inp ≠ []
Proof
  Cases_on ‘inp’ >> simp[]
QED

Theorem LAST_buildstates[simp]:
  ∀q inp. LAST (buildstates M q inp) = Delta M q inp
Proof
  Induct_on ‘inp’ >>
  simp[Delta_def] >>
  simp[listTheory.LAST_DEF]
QED

Theorem buildstates_transition:
  ∀n q_0 i.
    n < LENGTH i ⇒
    (M.delta (EL n (buildstates M q_0 i)) (EL n i) =
     EL (n + 1) (buildstates M q_0 i))
Proof
  Induct_on ‘i’ >>
  simp[] >>
  rw[] >>
  Cases_on ‘n’ >>
  fs[] >>
  simp[GSYM arithmeticTheory.ADD1]
QED

Theorem wf_dfa_accepts_characters_ok:
  wf_dfa M ∧ w ∈ dfa_lang M ⇒ EVERY M.Sigma w
Proof
  simp[dfa_accepts_def] >>
  ‘wf_dfa M ⇒ ∀q c. q ∈ M.Q ∧ Delta M q cs ∈ M.C ∧ MEM c cs ⇒ c ∈ M.Sigma’
    suffices_by metis_tac[wf_dfa_def] >>
  strip_tac >> Induct_on ‘cs’ >> simp[] >> rw[]
  >- (spose_not_then assume_tac >>
      ‘M.delta q c = 0’ by metis_tac[wf_dfa_def] >> fs[] >>
      rfs[Delta_0_Sink] >> metis_tac[wf_dfa_def])
  >- (‘h ∈ M.Sigma’ suffices_by metis_tac[wf_dfa_def] >>
      spose_not_then assume_tac >>
      ‘M.delta q h = 0’ by metis_tac[wf_dfa_def] >> fs[] >>
      rfs[Delta_0_Sink] >> metis_tac[wf_dfa_def])
QED

Theorem has_Accepting_Execution_Delta_coincide:
  ∀A cs. wf_dfa M ⇒ (has_Accepting_Execution M cs <=> dfa_accepts M cs)
Proof
  simp[has_Accepting_Execution_def, dfa_accepts_def,
       EQ_IMP_THM, FUN_EQ_THM, PULL_EXISTS] >>
  rw[]
  >- (rfs[] >> metis_tac[sipser_rm])
  >- (rename [‘Delta M _ input’] >>
      qexists_tac ‘buildstates M M.q_0 input’ >>
      simp[] >> metis_tac[buildstates_transition])
QED

Theorem has_Accepting_Execution_Delta_coincide_thm:
  ∀A w. has_Accepting_Execution M w ⇔ wf_dfa M ∧ dfa_accepts M w
Proof
  metis_tac[has_Accepting_Execution_Delta_coincide,
            has_Accepting_Execution_def]
QED
 *)
