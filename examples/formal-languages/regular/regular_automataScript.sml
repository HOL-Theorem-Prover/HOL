open HolKernel Parse boolLib bossLib;
open combinTheory
     listTheory
     mp_then
     nlistTheory
     numpairTheory
     pred_setTheory
     relationTheory
     rich_listTheory
     arithmeticTheory;

(* This material was first developed as part of a HOL reading group in a
   separate repository by

     Elliot Catt, Zhuo Chen, Michael Norrish, James Shaker, and Yiming Xu

   from March 2019 to September 2020, meeting for an hour a week, roughly.

   Adding it to HOL has removed that other repo's git history, sadly.

   We worked from Chapter 1 of the 3rd edition Sipser's "Introduction to
   the Theory of Computation".                           [22 January 2024]
*)

val _ = new_theory "regular_automata";

(* a finite automaton is a 5-tuple of
     Q : set of states
     A : alphabet - set of characters
     δ : transition function
          Q × A → Q
     q0 : start state
     C : final states

  Subject to constraints:
     - Q finite,
     - A finite,
     - C ⊆ Q
     - q0 ∈ Q
*)

Type state  = “:num”
Type symbol = “:num”


(* Definition 1.5 *)
Datatype:
  fa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol -> state)
          (* or state # symbol -> state,
             encoding Q * A -> Q *) ;
    q0 : state ;
    C : state set
  |>
End

Definition wfFA_def:
  wfFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c.
      c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q c ∈ a.Q) ∧
    (* if you apply the transition function to a state in
       the machine's state set, and a character in the
       machine's alphabet, then you'd better stay in the
       set of machine states *)
    0 ∈ a.Q ∧
    0 ∉ a.C ∧
    0 ≠ a.q0 ∧
    (∀q c. c ∉ a.A ⇒ (a.tf q c = 0)) ∧
    (∀c. a.tf 0 c = 0)
End

(* Note that the same automaton can be encoded as two different
   fa values because the two values can have tf functions that
   differ on values of q and a outside of the expected domain.

   The special zero state is a non-initial, non-final state where
   the transition function takes all non-alphabet characters from
   all states.  Keeping tf as a function rather than a finite map, or
   a function into options, seems advantageous.
*)


(*
                                           /-----------\
                                           v           |
   --> ( 1 )  --a-->  (( 2 ))  --a,b-->  ( 4 )  --a,b -'
         |                                 ^
         b                                 |
         |                                 |
         \- - - - - - - - - - -- - - - - - /
       ( 3 )


*)

Definition example_def:
  example = <| Q := {0;1;2;3;4}; A := { 1 (* a *); 2 (* b *) };
               tf := (λq. case q of
                          |  1 => (λc. if c = 1 then 2 else
                                       if c = 2 then 3 else 0)
                          |  2 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          |  3 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          |  4 => (λc. if (c = 1) \/ (c = 2) then 4
                                       else 0)
                          | _ => \c.0 ) ;
               q0 := 1;
               C := {2} |>
End

(* prove that example is well-formed *)
Theorem example_wellformed:
  wfFA example
Proof
  simp[wfFA_def, example_def]>>
  rpt strip_tac (* generates 8 subgoals *) >>
  simp[] (* 9 *)
  >- rw[] >> rfs[]
QED

Type sipser_string = “:symbol list”
Type language = “:sipser_string set”

Definition runMachine_def[simp]:
  (runMachine a q [] = q)  ∧
  (runMachine a q (c::cs) = runMachine a (a.tf q c) cs)
End

Theorem runMachine_in_Q:
  ∀d s cs.
    wfFA d ∧ s ∈ d.Q ⇒ runMachine d s cs ∈ d.Q
Proof
  Induct_on ‘cs’ >> rw[] >>
  metis_tac[wfFA_def]
QED

Definition accepts_def:
  accepts a cs ⇔ runMachine a a.q0 cs ∈ a.C
End

Theorem example_acceptsA = EVAL “accepts example [1]”;
Theorem example_doesnt_acceptB = EVAL “accepts example [2]”;
Theorem example_doesnt_acceptAB = EVAL “accepts example [1;2]”;

Definition Sipser_Accepts_def:
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (LENGTH ss = LENGTH cs + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C ∧
      wfFA A
End

Theorem Sipser_Accepts_NoZero:
  Sipser_Accepts A cs ⇔
    ∃ss : state list.
      ss ≠ [] ∧
      (∀s. MEM s ss ⇒ s ≠ 0) ∧
      (LENGTH ss = LENGTH cs + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           (A.tf (EL n ss) (EL n cs) = EL (n + 1) ss)) ∧
      LAST ss ∈ A.C ∧
      wfFA A
Proof
  reverse (rw[EQ_IMP_THM])
  >- metis_tac[Sipser_Accepts_def]
  >- (fs[Sipser_Accepts_def] >>
      qexists_tac ‘ss’ >>
      rw[] >>
      ‘∀ss cs. LAST ss ≠ 0 ∧
               LENGTH ss = LENGTH cs + 1 ∧
               (∀n. n < LENGTH ss - 1 ⇒
                    A.tf (EL n ss) (EL n cs) =
                    EL (n + 1) ss) ⇒
              ¬(MEM 0 ss)’
        suffices_by metis_tac[wfFA_def] >>
      ntac 5 (last_x_assum (K ALL_TAC)) >>
      Induct_on ‘ss’ >> simp[arithmeticTheory.ADD1] >>
      rw[]
      >> (Cases_on ‘ss’ >> fs[] >>
          Cases_on ‘cs’ >> fs[] >>
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
              simp[] >> metis_tac[wfFA_def])))
QED

Theorem sipser_rm:
∀ss input.
   (∀n. n < LENGTH input ⇒
        (A.tf (EL n ss) (EL n input) = EL (n + 1) ss)) ∧
   (LENGTH input + 1 = LENGTH ss)  ⇒
   (runMachine A (HD ss) input = LAST ss)
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

Definition buildstates_def[simp]:
  (buildstates A q [] = [q]) ∧
  (buildstates A q (c::cs) = q :: buildstates A (A.tf q c) cs)
End

Theorem LENGTH_buildstates[simp]:
  ∀q inp. LENGTH (buildstates A q inp) = LENGTH inp + 1
Proof
  Induct_on ‘inp’ >>
  simp[]
QED

Theorem HD_buildstates[simp]:
  HD (buildstates A q inp) = q
Proof
  Cases_on ‘inp’ >>
  simp[]
QED

Theorem buildstates_EQ_NIL[simp]:
  buildstates A q inp ≠ []
Proof
  Cases_on ‘inp’ >>
  simp[]
QED

Theorem LAST_buildstates[simp]:
  ∀q inp. LAST (buildstates A q inp) = runMachine A q inp
Proof
  Induct_on ‘inp’ >>
  simp[runMachine_def] >>
  simp[listTheory.LAST_DEF]
QED

Theorem buildstates_transition:
  ∀n q0 i.
    n < LENGTH i ⇒
    (A.tf (EL n (buildstates A q0 i)) (EL n i) =
     EL (n + 1) (buildstates A q0 i))
Proof
  Induct_on ‘i’ >>
  simp[] >>
  rw[] >>
  Cases_on ‘n’ >>
  fs[] >>
  simp[GSYM arithmeticTheory.ADD1]
QED

Theorem runMachine_0_sticks:
  wfFA A ⇒ runMachine A 0 cs = 0
Proof
  strip_tac >> Induct_on ‘cs’ >> simp[] >>
  fs[wfFA_def]
QED

Theorem wfFA_accepts_characters_ok:
  wfFA A ∧ accepts A cs ∧ MEM c cs ⇒ c ∈ A.A
Proof
  simp[accepts_def] >>
  ‘wfFA A ⇒ ∀q c. q ∈ A.Q ∧ runMachine A q cs ∈ A.C ∧ MEM c cs ⇒ c ∈ A.A’
    suffices_by metis_tac[wfFA_def] >>
  strip_tac >> Induct_on ‘cs’ >> simp[] >> rw[]
  >- (spose_not_then assume_tac >>
      ‘A.tf q c = 0’ by metis_tac[wfFA_def] >> fs[] >>
      rfs[runMachine_0_sticks] >> metis_tac[wfFA_def])
  >- (‘h ∈ A.A’ suffices_by metis_tac[wfFA_def] >>
      spose_not_then assume_tac >>
      ‘A.tf q h = 0’ by metis_tac[wfFA_def] >> fs[] >>
      rfs[runMachine_0_sticks] >> metis_tac[wfFA_def])
QED

Theorem Sipser_Accepts_runMachine_coincide:
  ∀A cs. wfFA A ⇒ (Sipser_Accepts A cs = accepts A cs)
Proof
  simp[FUN_EQ_THM, Sipser_Accepts_def, accepts_def, EQ_IMP_THM,
       PULL_EXISTS] >>
  rw[]
  >- (rfs[] >>
      metis_tac[sipser_rm])
  >- (rename [‘runMachine A _ input’] >>
      qexists_tac ‘buildstates A A.q0 input’ >>
      simp[] >>
      metis_tac[buildstates_transition])
QED

Theorem Sipser_Accepts_runMachine_coincide_thm:
  ∀A cs. Sipser_Accepts A cs ⇔ wfFA A ∧ accepts A cs
Proof
  metis_tac[Sipser_Accepts_runMachine_coincide,Sipser_Accepts_def]
QED

(* Just prior to 1.16 *)
Definition recogLangD_def:
  recogLangD D = {w | Sipser_Accepts D w}
End

(* Definition 1.16 *)
Definition regularLanguage_def:
  regularLanguage l ⇔ ∃M. wfFA M ∧ recogLangD M = l
End

(* Definition 1.23 *)
(* The Regular Operations *)
(* Union is already defined (set union...) *)

Definition concat_def:
  concat lA lB = {x ++ y | x ∈ lA ∧ y ∈ lB}
End


Definition star_def:
  star l = {FLAT ls | ∀s. MEM s ls ⇒ s ∈ l}
End

Theorem empty_in_star:
  ∀ l. [] ∈ star l
Proof
  rw [star_def] >>
  qexists_tac ‘[]’ >>
  rw[]
QED

Definition machine_union_def:
  machine_union M1 M2 =
    <|Q  := {r1 ⊗ r2 | r1 ∈ M1.Q ∧ r2 ∈ M2.Q };
      A  := M1.A ∪ M2.A;
      tf := λs c. M1.tf (nfst s) c ⊗ M2.tf (nsnd s) c;
      q0 := M1.q0 ⊗ M2.q0;
      C  := {r1 ⊗ r2 | (r1 ∈ M1.C ∧ r2 ∈ M2.Q) ∨ (r1 ∈ M1.Q ∧ r2 ∈ M2.C)};
    |>
End


(* Theorem 1.25 *)
Theorem wfFA_machine_union :
  ∀M1 M2. wfFA M1 ∧ wfFA M2 ⇒ wfFA (machine_union M1 M2)
Proof
  rw[wfFA_def,machine_union_def] (* 11 *) >> simp[]
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
      Sipser_Accepts_runMachine_coincide_thm,
      wfFA_machine_union] >>
  qabbrev_tac ‘MU = machine_union M1 M2’ >>
  rw[accepts_def] >>
  ‘(MU.A = M1.A ∪ M2.A) ∧ (MU.q0 = M1.q0 ⊗ M2.q0)’
    by rw[machine_union_def, Abbr ‘MU’] >>
  simp[] >>
  ‘∀ q1 q2. q1 ∈ M1.Q ∧ q2 ∈ M2.Q
    ⇒ (runMachine MU (q1 ⊗ q2) x ∈ MU.C ⇔
      runMachine M1 q1 x ∈ M1.C ∨ runMachine M2 q2 x ∈ M2.C)’
    suffices_by (rpt strip_tac >>
                 metis_tac[wfFA_def]) >>
  Induct_on ‘x’
  >- (rw[Abbr ‘MU’, runMachine_def,machine_union_def])
  >- (rw[runMachine_def, DISJ_IMP_THM, FORALL_AND_THM] >>
      ‘MU.tf (q1 ⊗ q2) h = M1.tf q1 h ⊗ M2.tf q2 h’
        by rw[Abbr ‘MU’, machine_union_def] >>
      first_x_assum (fn x => SUBST_TAC [x]) >>
      ‘M1.tf q1 h ∈ M1.Q ∧ M2.tf q2 h ∈ M2.Q’
        suffices_by metis_tac[] >>
      metis_tac[wfFA_def])
QED

Datatype:
  nfa = <|
    Q : state set ;
    A : symbol set ;
    tf : state -> (symbol option -> state set);
    q0 : state ;
    C : state set
  |>
End

Definition wfNFA_def:
  wfNFA a ⇔
    FINITE a.Q ∧
    FINITE a.A ∧
    a.C ⊆ a.Q  ∧
    a.q0 ∈ a.Q ∧
    (∀q c. c ∈ a.A ∧ q ∈ a.Q ⇒ a.tf q (SOME c) ⊆ a.Q) ∧
    (∀q.   q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ∧
    (∀q c. c ∉ a.A ⇒ a.tf q (SOME c) = ∅)
End


Definition strip_option_def[simp]:
  (strip_option [] = []) ∧
  (strip_option (NONE :: t) = strip_option t) ∧
  (strip_option (SOME c :: t) = c :: strip_option t)
End

Theorem strip_MAP_SOME[simp]:
  strip_option (MAP SOME x) = x
Proof
  Induct_on ‘x’ >> simp[]
QED

Definition Sipser_ND_Accepts_def:
  Sipser_ND_Accepts A cs ⇔
    ∃ss : state list cs':(symbol option) list.
      ss ≠ [] ∧
      (strip_option cs' = cs) ∧
      (LENGTH ss = LENGTH cs' + 1) ∧
      (HD ss = A.q0) ∧
      (∀n. n < LENGTH ss - 1 ⇒
           EL (n + 1) ss ∈ A.tf (EL n ss) (EL n cs')) ∧
      LAST ss ∈ A.C ∧
      (∀c. MEM c cs ⇒ c ∈ A.A)
End

Definition recogLangN_def:
  recogLangN N = {w | Sipser_ND_Accepts N w}
End


Definition e_closure_def:
  e_closure a Q = {s | ∃q. q ∈ Q ∧  RTC (λs0 s. s ∈ a.tf s0 NONE) q s}
End

val _ = temp_overload_on ("E",“e_closure”);

val _ = temp_overload_on ("enc", “λs. nlist_of (SET_TO_LIST s)”);
val _ = temp_overload_on ("dec", “λs. set (listOfN s)”);

Theorem dec_enc_iden[simp]:
  ∀s. FINITE s ⇒ dec (enc s) = s
Proof
  rw[listOfN_nlist,SET_TO_LIST_INV]
QED

Definition NFA2DFA_def:
  NFA2DFA a =
    <|Q  := {enc s| s ⊆ a.Q};
      A  := a.A;
      tf := λs c. enc (E a {s' | ∃s0. s0 ∈ dec s ∧ s' ∈ a.tf s0 (SOME c)});
      q0 := enc (E a {a.q0});
      C := {enc s |s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C} |>
End


Theorem e_in_states:
  (∀q. q ∈ a.Q ⇒ a.tf q NONE ⊆ a.Q) ⇒
  s ⊆ a.Q ⇒ E a s ⊆ a.Q
Proof
  strip_tac >>
  simp[e_closure_def,PULL_EXISTS,SUBSET_DEF] >>
  ‘∀x0 x. (λs0 s. s ∈ a.tf s0 NONE)^* x0 x ⇒ x0 ∈ a.Q ⇒ x ∈ a.Q’
    suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
  first_x_assum drule >> simp[SUBSET_DEF]
QED

Theorem nlist_of_11[simp]:
  (nlist_of x = nlist_of y) ⇔ (x = y)
Proof
  metis_tac[listOfN_nlist]
QED

Theorem nlist_of_EQ_0[simp]:
  (nlist_of l = 0 ⇔ l = []) ∧
  (0 = nlist_of l ⇔ l = [])
Proof
  metis_tac[nlist_of_11, nlist_of_def]
QED

Theorem SET_TO_LIST_EQ_NIL[simp]:
  FINITE s ⇒
  (SET_TO_LIST s = [] ⇔ s = ∅) ∧
  ([] = SET_TO_LIST s ⇔ s = ∅)
Proof
  rw[EQ_IMP_THM] >>
  metis_tac[listTheory.SET_TO_LIST_INV, listTheory.LIST_TO_SET_THM]
QED

Theorem enc_EQ_0[simp]:
  FINITE s ⇒ (enc s = 0 ⇔ s = ∅) ∧ (0 = enc s ⇔ s = ∅)
Proof
  simp[]
QED

Theorem wfFA_NFA2DFA:
  wfNFA a ⇒ wfFA (NFA2DFA a)
Proof
  fs[wfNFA_def,wfFA_def,NFA2DFA_def] >> rw[] >>~-
  ([‘SET_TO_LIST (E a ∅) = []’],
  ‘E a ∅ = ∅’ suffices_by simp[] >>
  simp[e_closure_def]) >~
  [‘FINITE {enc s | s ⊆ a.Q }’]
  >- (‘{enc s | s ⊆ a.Q} = IMAGE enc (POW a.Q)’ by
        fs[EXTENSION,IN_POW] >> simp[FINITE_POW] ) >~
  [‘SET_TO_LIST (E a {a.q0}) = SET_TO_LIST _ ∧ _’]
  >- (irule_at Any EQ_REFL >> simp[e_in_states]) >~
  [‘SET_TO_LIST _ = SET_TO_LIST _ ∧ _’]
  >- (irule_at Any EQ_REFL >> irule e_in_states >>
      rw[] >> ‘FINITE s’ by metis_tac[SUBSET_FINITE_I] >>
      simp[SUBSET_DEF,PULL_EXISTS,listOfN_nlist] >>
      metis_tac[SUBSET_DEF]) >~
  [‘SET_TO_LIST _ = [] ∧ _’] >- (qexists ‘{}’ >> simp[]) >~
  [‘SET_TO_LIST (E a _) ≠ []’]
  >- (‘FINITE (E a {a.q0}) ∧ E a {a.q0} ≠ ∅’ suffices_by simp[] >>
      conj_tac
      >- (‘E a {a.q0} ⊆ a.Q’ suffices_by metis_tac[SUBSET_FINITE] >>
          irule e_in_states >> simp[])
      >- (simp[e_closure_def, EXTENSION] >> qexists_tac ‘a.q0’ >>
          simp[])) >~
  [‘¬(s ⊆ a.Q)’]
  >- (Cases_on ‘s ⊆ a.Q’ >> simp[] >>
      ‘FINITE s’ by metis_tac[SUBSET_FINITE] >>
      gs[SET_TO_LIST_EQ_NIL]) >~
  [‘_ ⊆ {enc s | s ⊆ a.Q}’]
  >- (rw[SUBSET_DEF,PULL_EXISTS] >> metis_tac[])
QED

Definition DFA2NFA_def:
  DFA2NFA a = <|Q  := a.Q;
                A  := a.A;
                tf := λs copt. case copt of
                                  NONE => {}
                                | SOME c =>
                                    if a.tf s c = 0 then ∅
                                    else {a.tf s c};
                q0 := a.q0;
                C := a.C |>
End

(* also need: wfNFA (DFA2NFA a) *)
Theorem wfNFA_DFA2NFA:
  ∀D. wfFA D ⇒ wfNFA (DFA2NFA D)
Proof
  rw[wfFA_def,wfNFA_def,DFA2NFA_def] >>
  rw[]
QED

Theorem strip_option_length:
  ¬MEM NONE l ⇒ LENGTH (strip_option l) = LENGTH l
Proof
  Induct_on ‘l’ >> rw[] >> fs[] >> Cases_on ‘h’ >> simp[] >> fs[]
QED

Theorem EL_strip_option:
  ∀n. ¬MEM NONE l ∧ n < LENGTH l ⇒ EL n l = SOME (EL n (strip_option l))
Proof
  Induct_on ‘l’ >> simp[] >> Cases >> simp[] >>
  Cases >> simp[]
QED

Theorem DFA_SUBSET_NFA:
  wfFA a ⇒ (Sipser_ND_Accepts (DFA2NFA a) cs ⇔ Sipser_Accepts a cs)
Proof
  rw[] >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_def,Sipser_Accepts_NoZero, DFA2NFA_def] >>
      map_every qexists_tac [‘ss’,‘MAP SOME cs’] >> rw[]
      >- (fs[listTheory.EL_MAP] >>
          ‘EL (n + 1) ss ≠ 0’
            suffices_by rw[] >>
          metis_tac[MEM_EL,DECIDE“(n < x) ∧ (y = x + 1) ⇒ (n + 1 < y)”])
      >- (‘Sipser_Accepts a cs’ by metis_tac[Sipser_Accepts_def] >>
          fs[Sipser_Accepts_runMachine_coincide_thm] >>
          metis_tac[wfFA_accepts_characters_ok])) >>
  rw[Sipser_ND_Accepts_def,Sipser_Accepts_NoZero, DFA2NFA_def] >>
  rename [‘LENGTH ss = LENGTH cs + 1’, ‘LAST ss ∈ A.C’] >>
  qexists_tac ‘ss’ >>
  ‘¬MEM NONE cs’ by
     (rw[MEM_EL] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
  reverse (rw[strip_option_length])
  >- (rename [‘n < LENGTH cs’] >> last_x_assum (qspec_then‘n’ mp_tac) >>
      simp[EL_strip_option] >> rw[])
  >- (rw[MEM_EL] >> strip_tac >> gvs[] >>
      rename[‘n < LENGTH cs + 1’] >>
      Cases_on ‘n’ >- fs[EL,wfFA_def] >>
      rename [‘EL (SUC n) ss = 0’] >> gvs[ADD1] >>
      first_x_assum drule >> simp[] >>
      simp[] >> Cases_on ‘EL n cs’ >> rw[])
QED

Theorem MEM_listOfN_enc[simp]:
  FINITE s ⇒ (MEM x (listOfN (enc s)) ⇔ x ∈ s)
Proof
  simp[listOfN_nlist]
QED

Theorem e_closure_safe:
  wfNFA a ∧ s0 ⊆ a.Q ⇒ E a s0 ⊆ a.Q
Proof
  strip_tac >> simp[e_closure_def, SUBSET_DEF, PULL_EXISTS] >>
  ‘∀s0 s. (λq0 q. q ∈ a.tf q0 NONE)^* s0 s ⇒ (s0 ∈ a.Q ⇒ s ∈ a.Q)’
    suffices_by metis_tac[SUBSET_DEF] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rw[] >>
  fs[wfNFA_def] >> metis_tac[SUBSET_DEF]
QED

Theorem IN_eclosure_originator:
  x ∈ E a s ⇒ ∃x0. x0 ∈ s ∧ (λs0 s. s ∈ a.tf s0 NONE)^* x0 x
Proof
  simp[e_closure_def]
QED

Theorem IN_eclosure_originator_rev:
  (∃x0. x0 ∈ s ∧ (λs0 s. s ∈ a.tf s0 NONE)^* x0 x) ⇒ x ∈ E a s
Proof
  simp[e_closure_def]
QED

Theorem SET_TO_LIST_11[simp]:
  ∀s1 s2. FINITE s1 ∧ FINITE s2 ⇒ (SET_TO_LIST s1 = SET_TO_LIST s2 ⇔ s1 = s2)
Proof
  metis_tac[listTheory.SET_TO_LIST_INV]
QED

Theorem enc_11[simp]:
  FINITE s1 ∧ FINITE s2 ⇒ ((enc s1 = enc s2) ⇔ (s1 = s2))
Proof
  simp[]
QED

Theorem NFA2DFA_1step:
  wfNFA a ∧ s0 ⊆ a.Q ∧ c ∈ a.A ⇒
  (((NFA2DFA a).tf (enc s0) c = q) ⇔
   ∃s. (q = enc s) ∧ s ⊆ a.Q ∧
      ∀nq. nq ∈ s ⇔
           ∃nq0. nq0 ∈ s0 ∧ nq ∈ E a (a.tf nq0 (SOME c)))
Proof
  simp[NFA2DFA_def] >> strip_tac >> eq_tac >> rw[]
  >- (qho_match_abbrev_tac ‘∃s. enc X = enc s ∧ _ s’ >> qexists_tac ‘X’ >>
      simp[] >> rw[Abbr‘X’]
      >- (‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> simp[] >>
          irule e_closure_safe >> simp[SUBSET_DEF, PULL_EXISTS] >>
          fs[wfNFA_def] >> metis_tac[SUBSET_DEF]) >>
      ‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> fs[] >>
      fs[e_closure_def, PULL_EXISTS] >> metis_tac[]) >>
  ‘FINITE s0’ by metis_tac[wfNFA_def, SUBSET_FINITE_I] >> simp[] >>
  AP_TERM_TAC >> fs[e_closure_def, EXTENSION, PULL_EXISTS] >>
  metis_tac[]
QED

Inductive NF_transition:
  (∀q0. NF_transition a q0 [] q0) ∧
  (∀q0 q1 q c cs.
     q1 ∈ a.tf q0 c ∧ NF_transition a q1 cs q ∧ (∀c0. c = SOME c0 ⇒ c0 ∈ a.A)
    ⇒
     NF_transition a q0 (c::cs) q)
End

Theorem E_FINITE:
  wfNFA N ∧ s ⊆ N.Q ⇒ FINITE (E N s)
Proof
  rw[] >> drule_all (GEN_ALL e_closure_safe) >> strip_tac >>
  irule SUBSET_FINITE_I >> qexists_tac ‘N.Q’ >> fs[wfNFA_def]
QED

Definition munge_def:
   munge n cnlist =
    REPLICATE n NONE ++ FLAT (MAP (λ(c,n). SOME c :: REPLICATE n NONE) cnlist)
End

Theorem munge_SUC:
  munge (SUC n) cs = NONE :: munge n cs
Proof
  simp[munge_def]
QED

Theorem munge0NIL[simp]:
  munge 0 [] = []
Proof
  simp[munge_def]
QED

Theorem munge0CONS[simp]:
  munge 0 ((c,n)::t) = SOME c::munge n t
Proof
  simp[munge_def]
QED

Theorem munge_eq_nil[simp]:
  munge n l = [] <=> l=[] ∧ n=0
Proof
  simp[munge_def,REPLICATE_NIL,FLAT_EQ_NIL,EVERY_MAP,EVERY_MEM,
       pairTheory.FORALL_PROD, EQ_IMP_THM] >> Cases_on‘l’ >>
  simp[] >> metis_tac[pairTheory.PAIR]
QED

Theorem Sipser_ND_Accepts_NF_transition:
  Sipser_ND_Accepts a cs ⇔
  ∃q n nlist.
     LENGTH nlist = LENGTH cs ∧
     NF_transition a a.q0 (munge n (ZIP (cs,nlist))) q ∧ q ∈ a.C
Proof
  simp[Sipser_ND_Accepts_def] >> qspec_tac(‘a.q0’, ‘s0’) >> rw[] >>
  eq_tac >> rw[]
  >- (rpt (pop_assum mp_tac) >> qid_spec_tac ‘ss’ >>
      rename [‘strip_option cs’] >> Induct_on ‘cs’ >> simp[]
      >- (Cases >> simp[] >> rw[] >>
          map_every qexists_tac [‘h’, ‘0’] >>
          simp[NF_transition_rules]) >>
      rw[] >> Cases_on ‘ss’ >> fs[] >>
      rename [‘NF_transition _ s0 _ _’, ‘LAST (s0::ss) ∈ a.C’] >>
      ‘ss ≠ []’ by (strip_tac >> fs[]) >>
      ‘LENGTH ss = LENGTH cs + 1’ by fs[arithmeticTheory.ADD1] >>
      fs[LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, ADD_CLAUSES] >>
      ‘∀x. LAST (x :: ss) = LAST ss’ by simp[listTheory.LAST_CONS_cond] >>
      fs[] >> rename [‘HD ss ∈ A.tf s0 copt’] >> Cases_on ‘copt’ >> fs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac ‘q’
      >- (map_every qexists_tac [‘SUC n’ , ‘nlist’] >> simp[munge_SUC] >>
          metis_tac[NF_transition_rules,optionTheory.NOT_NONE_SOME]) >>
      map_every qexists_tac [‘0’, ‘n::nlist’] >> simp[] >>
      metis_tac[NF_transition_rules,optionTheory.SOME_11]) >>
  rpt (pop_assum mp_tac) >>
  qho_match_abbrev_tac ‘P ⇒ Q ⇒ R q cs s0’ >>
  ‘∀q0 csoptl q.
      NF_transition a q0 csoptl q ⇒
      ∀cs n nlist.
        LENGTH nlist = LENGTH cs ∧
        csoptl = munge n (ZIP(cs,nlist)) ⇒
        R q cs q0’ suffices_by metis_tac[] >>
   simp[Abbr‘R’] >> markerLib.UNABBREV_ALL_TAC >>
   Induct_on ‘NF_transition’ >> simp[] >> rw[]
   >- (rfs[ZIP_EQ_NIL] >>
       map_every qexists_tac [‘[q0]’,‘[]’] >> simp[]) >>
   rename[‘q1 ∈ a.tf a0 copt’,‘LENGTH nlist = LENGTH cs’,‘munge n’,
          ‘NF_transition a q1 csoptl q’] >>
   Cases_on ‘copt’
   >- ((* nfa made an ε transition *)
       ‘∃m. n = SUC m’
         by (Cases_on ‘n’ >> fs[] >>
             map_every Cases_on [‘cs’, ‘nlist’] >> fs[]) >>
       fs[] >> first_x_assum (drule_then (qspec_then ‘m’ mp_tac)) >>
       simp[] >> strip_tac >> rfs[munge_SUC] >>
       rename [‘strip_option IHcs = cs’, ‘HD IHss = q1’] >>
       map_every qexists_tac [‘a0 :: IHss’, ‘NONE :: IHcs’] >>
       simp[listTheory.LAST_CONS_cond] >> qx_gen_tac ‘N’ >> strip_tac >>
       Cases_on ‘N’ >> simp[] >> rename [‘SUC N0 < LENGTH IHcs + 1’] >>
       simp[arithmeticTheory.ADD_CLAUSES]) >>
   (* copt = SOME ?; nfa made a "real" transition *)
   rename [‘SOME c:: _ = _’] >> ‘n = 0’ by (Cases_on ‘n’ >> fs[munge_SUC]) >>
   fs[] >>
   Cases_on ‘cs’ >> fs[] >- (rw[] >> fs[]) >>
   rename [‘ZIP (c1::cs,_)’] >>
   Cases_on ‘nlist’ >> fs[] >> rw[] >>
   rename [‘NF_transition a q1 ( munge n (ZIP(cs,ns)) ) q’] >>
   first_x_assum (drule_then (qspec_then ‘n’ mp_tac)) >> simp[] >>
   strip_tac >> rename [‘strip_option IHcs = cs’, ‘IHss ≠ []’] >>
   map_every qexists_tac [‘a0::IHss’, ‘SOME c :: IHcs’] >>
   simp[listTheory.LAST_CONS_cond] >> rw[]
   >- (rename [‘N<LENGTH _ + 1’] >>
       Cases_on ‘N’ >> simp[] >> rename [‘SUC N0 < LENGTH IHcs + 1’] >>
       simp[arithmeticTheory.ADD_CLAUSES])
   >- (fs[])
   >- (metis_tac[])
QED

Theorem list_to_munge:
  ∀l.
      ∃n nlist.
        LENGTH nlist = LENGTH (strip_option l) ∧
        munge n (ZIP (strip_option l,nlist)) = l
Proof
  Induct >> rw[] >>
  Cases_on ‘h’ >> rw[]
  >- (qexistsl_tac [‘SUC n’, ‘nlist’] >> rw[munge_SUC])
  >> (qexistsl_tac [‘0’, ‘n::nlist’] >> rw[])
QED

Theorem strip_option_append[simp]:
  strip_option (a++b) = strip_option a ++ strip_option b
Proof
  Induct_on ‘a’ >> fs[] >> Cases >> simp[]
QED

Theorem strip_option_replicate_none[simp]:
  strip_option (REPLICATE n NONE) = []
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem strip_option_flat:
  strip_option (FLAT l) = FLAT (MAP strip_option l)
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem strip_option_munge:
  ∀cs nlist. LENGTH cs = LENGTH nlist ⇒
             strip_option (munge n (ZIP (cs,nlist))) = cs
Proof
  simp[munge_def,strip_option_flat,MAP_MAP_o,combinTheory.o_DEF,
       pairTheory.UNCURRY] >>
  Induct_on‘cs’ >> simp[] >> Cases_on‘nlist’ >> simp[]
QED

Theorem Sipser_ND_Accepts_NF_transition_l:
  Sipser_ND_Accepts a cs ⇔
  ∃q l. strip_option l = cs ∧ NF_transition a a.q0 l q ∧ q ∈ a.C
Proof
  eq_tac
  >- (rw[Sipser_ND_Accepts_NF_transition] >>
      qexistsl_tac [‘q’, ‘munge n (ZIP (cs,nlist))’] >> rw[strip_option_munge])
  >> simp[PULL_EXISTS, Sipser_ND_Accepts_NF_transition] >>
  metis_tac[list_to_munge]
QED

Theorem E_SUBSET:
  x ∈ Q ⇒ x ∈ E a Q
Proof
  simp[e_closure_def] >> metis_tac[relationTheory.RTC_RULES]
QED

Theorem E_IDEMPOTENT[simp]:
  E a (E a Q) = E a Q
Proof
  simp[e_closure_def, EXTENSION, PULL_EXISTS] >>
  metis_tac[relationTheory.RTC_CASES_RTC_TWICE]
QED


Theorem NF_transition_NFA2DFA:
  wfNFA a ⇒
  ∀q0 cs q.
     NF_transition a q0 cs q ⇒
     (∀c. MEM (SOME c) cs ⇒ c ∈ a.A) ⇒
     ∀Q0.
       q0 ∈ Q0 ∧ Q0 ⊆ a.Q ⇒
       ∃Q. enc Q = runMachine (NFA2DFA a) (enc (E a Q0)) (strip_option cs) ∧
           q ∈ Q ∧ Q ⊆ a.Q
Proof
  strip_tac >>
  Induct_on ‘NF_transition’ >> rw[] >- metis_tac[E_SUBSET,e_closure_safe] >>
  rename [‘q1 ∈ a.tf q0 copt’] >> Cases_on ‘copt’ >> simp[]
  >- (fs[] >> first_x_assum (qspec_then ‘E a Q0’ mp_tac) >> simp[] >>
      disch_then irule >> conj_tac
      >- (simp[e_closure_def] >> qexists_tac ‘q0’ >>
          simp[relationTheory.RTC_SINGLE]) >>
      simp[e_closure_safe]) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> rename [‘q1 ∈ a.tf q0 (SOME c)’] >>
  ‘∃Q1. q1 ∈ Q1 ∧ Q1 ⊆ a.Q ∧ (NFA2DFA a).tf (enc (E a Q0)) c = enc (E a Q1)’
     suffices_by metis_tac[] >>
  simp[NFA2DFA_def] >>
  qexists_tac ‘{q | ∃q0'. q0' ∈ E a Q0 ∧ q ∈ a.tf q0' (SOME c)}’ >> simp[] >>
  rpt conj_tac
  >- metis_tac[E_SUBSET]
  >- (fs[wfNFA_def, SUBSET_DEF, PULL_EXISTS] >>
      metis_tac[e_closure_safe, SUBSET_DEF, wfNFA_def]) >>
  AP_TERM_TAC >> simp[EXTENSION] >>
  ‘FINITE (E a Q0)’
    by metis_tac[wfNFA_def, e_closure_safe, SUBSET_FINITE_I] >>
  simp[MEM_listOfN_enc]
QED

Theorem MEM_REPLICATE_CORR[simp]:
  MEM x (REPLICATE n y) ⇔ 0 < n ∧ x = y
Proof
  Induct_on ‘n’ >> fs[] >> metis_tac[]
QED


Theorem fst_list_lem:
  (λ(c,n). [c]) = (λx. [x]) o FST
Proof
  simp[FUN_EQ_THM,pairTheory.FORALL_PROD]
QED

Theorem flat_map_sing[simp]:
  FLAT (MAP (λx. [x]) l) = l
Proof
  Induct_on‘l’ >> simp[]
QED

Theorem NFA2DFA_q0:
  (NFA2DFA a).q0 = enc (E a {a.q0})
Proof
  simp[NFA2DFA_def]
QED

Theorem NFA2DFA_C:
  (NFA2DFA a).C = {enc s | s ⊆ a.Q ∧ ∃c. c ∈ s ∧ c ∈ a.C}
Proof
  simp[NFA2DFA_def]
QED

Theorem nf_transition_okay:
  ∀q0 copts q. NF_transition a q0 copts q ⇒ ∀c. MEM (SOME c) copts ⇒ c ∈ a.A
Proof
  Induct_on‘NF_transition’ >> simp[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem RTC_LIST:
  ∀x y. RTC R x y ⇒
        ∃l. l ≠ [] ∧ HD l = x ∧ LAST l = y ∧
            ∀i. i < LENGTH l - 1 ⇒ R (EL i l) (EL (i + 1) l)
Proof
  Induct_on ‘RTC’ >> rw[]
  >- (rename [‘HD _ = a’] >> qexists_tac ‘[a]’ >> simp[]) >>
  rename [‘R a (HD l0)’] >> qexists_tac ‘a::l0’ >> simp[] >>
  conj_tac >- (Cases_on ‘l0’ >> fs[])>>
  Cases >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem E_closure_NF_transition:
  ∀q0 q. q ∈ E N {q0} ⇒ ∃n. NF_transition N q0 (munge n []) q
Proof
  rw[munge_def] >> drule IN_eclosure_originator >> simp[] >> Induct_on ‘RTC’ >>
  rw[]
  >- (qexists_tac ‘0’ >> simp[NF_transition_rules]) >>
  rename [‘NF_transition N _ (REPLICATE m NONE) _’] >>
  qexists_tac ‘SUC m’ >>
  simp[] >> metis_tac[NF_transition_rules, TypeBase.distinct_of “:α option”]
QED

Theorem NF_transition_prepend_NONEs:
  ∀n0 n cnlist.
    NF_transition N q0 (munge n0 []) q1 ∧
    NF_transition N q1 (munge n cnlist) q2 ⇒
    NF_transition N q0 (munge (n0 + n) cnlist) q2
Proof
  Induct_on ‘NF_transition’ >> rw[] >>
  rename [‘munge n0 [] = none1::nones’] >>
  Cases_on ‘n0’ >> fs[munge_SUC] >> rw[] >>
  rename [‘munge _ [] = munge nn []’] >>
  first_x_assum (qspec_then ‘nn’ mp_tac) >> simp[] >>
  disch_then (drule_then assume_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  metis_tac[NF_transition_rules, TypeBase.distinct_of “:α option”, munge_SUC]
QED

Theorem MEM_munge:
  MEM (SOME c) (munge n l) <=> ∃m. MEM (c,m) l
Proof
  simp[munge_def,MEM_FLAT,MEM_MAP,pairTheory.EXISTS_PROD,PULL_EXISTS]
QED

Theorem NFA_SUBSET_DFA:
  wfNFA N ⇒ (Sipser_Accepts (NFA2DFA N) cs ⇔ Sipser_ND_Accepts N cs)
Proof
  strip_tac >> reverse eq_tac
  >- (rw[Sipser_ND_Accepts_NF_transition, Sipser_Accepts_runMachine_coincide,
         accepts_def,wfFA_NFA2DFA] >>
      drule_then (drule_then strip_assume_tac) NF_transition_NFA2DFA >>
      rfs[MEM_FLAT,PULL_EXISTS,MEM_MAP,MEM_ZIP,strip_option_flat,MAP_MAP_o,
          pairTheory.o_UNCURRY_R,
          combinTheory.o_ABS_R,fst_list_lem,MAP_ZIP,NFA2DFA_C,NFA2DFA_q0] >>
      qabbrev_tac ‘s = munge n (ZIP (cs,nlist))’ >>
      ‘∀c. MEM (SOME c) s ⇒ c ∈ N.A’ by metis_tac[nf_transition_okay] >>
      ‘(∀n'. n' < LENGTH cs ⇒ EL n' cs ∈ N.A)’
        by (rw[] >>
            ‘MEM (SOME (EL n' cs)) s’
              by (fs[Abbr‘s’] >>
                  ‘MEM (EL n' cs) cs’ by fs[rich_listTheory.EL_MEM] >>
                  simp[MEM_FLAT,MEM_munge,MEM_ZIP] >>
                  metis_tac[]) >>
            fs[]) >> fs[] >>
      ‘N.q0 ∈ {N.q0} ∧ {N.q0} ⊆ N.Q ∧ strip_option s = cs’
        suffices_by metis_tac[] >>
      fs[wfNFA_def,Abbr‘s’,strip_option_munge])

  >> rw[Sipser_Accepts_runMachine_coincide, Sipser_ND_Accepts_NF_transition,
     wfFA_NFA2DFA, accepts_def] >>
  pop_assum mp_tac >>
  ‘∀s. s ⊆ N.Q ∧
       runMachine (NFA2DFA N) (enc s) cs ∈ (NFA2DFA N).C ⇒
       ∃nq0 nq n nlist.
           LENGTH nlist = LENGTH cs ∧ nq0 ∈ s ∧
           NF_transition N nq0 (munge n (ZIP (cs, nlist)))
                           nq ∧ nq ∈ N.C’
     suffices_by (rpt strip_tac >>
                  first_x_assum (qspec_then ‘E N {N.q0}’ mp_tac) >>
                  impl_tac
                  >- (‘{N.q0} ⊆ N.Q’ by fs[wfNFA_def] >> simp[e_closure_safe] >>
                      ‘enc (E N {N.q0}) = (NFA2DFA N).q0’ suffices_by simp[] >>
                      simp[NFA2DFA_def]) >>
                  rw[] >>
                  drule_then(qx_choose_then ‘n0’ assume_tac)
                     E_closure_NF_transition >>
                  drule_all NF_transition_prepend_NONEs >> metis_tac[]) >>
  Induct_on ‘cs’ >> simp[]
  >- (simp[NFA2DFA_def, PULL_EXISTS] >> rw[] >>
      rename [‘SET_TO_LIST s1 = SET_TO_LIST s2’] >>
      ‘FINITE s1 ∧ FINITE s2’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
      fs[SET_TO_LIST_11] >> rw[] >>
      map_every qexists_tac [‘c’, ‘c’, ‘0’] >> simp[NF_transition_rules]) >>
  rw[] >> rename [‘(NFA2DFA N).tf (enc s) c0’] >>
  ‘FINITE s’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
  ‘∃s'. (NFA2DFA N).tf (enc s) c0 = enc s' ∧ s' ⊆ N.Q’
    by (simp[NFA2DFA_def] >>
        qmatch_abbrev_tac
          ‘∃s'. SET_TO_LIST (E N ss) = SET_TO_LIST s' ∧ s' ⊆ N.Q’ >>
        ‘ss ⊆ N.Q’ suffices_by metis_tac[e_closure_safe] >>
        simp[Abbr‘ss’, SUBSET_DEF, PULL_EXISTS] >>
        fs[wfNFA_def] >> Cases_on ‘c0 ∈ N.A’ >- metis_tac[SUBSET_DEF] >>
        first_assum (pop_assum o mp_then Any mp_tac) >> simp[]) >>
  fs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum ‘_.tf (enc s) _ = _’ mp_tac >>
  simp[NFA2DFA_def] >>
  ‘FINITE s'’ by metis_tac[wfNFA_def, SUBSET_FINITE] >>
  qmatch_abbrev_tac ‘SET_TO_LIST ss = SET_TO_LIST _ ⇒ _’ >>
  ‘FINITE ss’
    by (simp[Abbr‘ss’] >> irule E_FINITE >> simp[] >>
        simp[SUBSET_DEF, PULL_EXISTS] >> fs[wfNFA_def] >>
        Cases_on ‘c0 ∈ N.A’ >- metis_tac[SUBSET_DEF] >>
        first_assum (pop_assum o mp_then Any mp_tac) >> simp[]) >>
  simp[SET_TO_LIST_11] >> simp[Abbr‘ss’] >> rw[] >>
  drule IN_eclosure_originator >> simp[PULL_EXISTS] >> rw[] >>
  rename [‘nq1 ∈ N.tf nq0 (SOME c0)’, ‘nq0 ∈ s’, ‘RTC _ nq1 nq2’] >>
  qexists_tac ‘nq0’ >> qexists_tac ‘nq’ >> qexists_tac ‘0’ >>
  ‘nq2 ∈ E N {nq1}’
    by (irule IN_eclosure_originator_rev >>
        simp[]) >>
  drule_then (qx_choose_then ‘nn’ assume_tac) E_closure_NF_transition >>
  qexists_tac ‘(nn+n)::nlist’ >> simp[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >> simp[] >>
  reverse conj_tac
  >- metis_tac[NF_transition_prepend_NONEs,arithmeticTheory.ADD_COMM] >>
  CCONTR_TAC >>
  ‘N.tf nq0 (SOME c0) = ∅’
    suffices_by metis_tac[NOT_IN_EMPTY] >>
  fs[wfNFA_def]
QED

Theorem thm_1_39:
  (∃D. wfFA D ∧ recogLangD D = l) ⇔ (∃N. wfNFA N ∧ recogLangN N = l)
Proof
  rw[] >> eq_tac >> rw[recogLangD_def,recogLangN_def]
  >- (simp[EXTENSION] >> qexists_tac ‘DFA2NFA D’ >>
      metis_tac[DFA_SUBSET_NFA,wfNFA_DFA2NFA])
  >- (simp[EXTENSION] >> qexists_tac ‘NFA2DFA N’ >>
      metis_tac[NFA_SUBSET_DFA,wfFA_NFA2DFA])
QED

Theorem corollary_1_40:
  ∀L.
    regularLanguage L ⇔ ∃M. wfNFA M ∧ recogLangN M = L
Proof
  metis_tac[regularLanguage_def,thm_1_39]
QED

Definition machine_link_def:
  machine_link N1 N2 =
    <|Q  := {0 ⊗ r1 | r1 ∈ N1.Q} ∪ {1 ⊗ r2 | r2 ∈ N2.Q};
      A  := N1.A ∪ N2.A;
      tf := λs copt.
              if nfst s = 0 then
                let
                  frs = { 0 ⊗ s' | s' ∈ N1.tf (nsnd s) copt}
                in
                  if nsnd s ∈ N1.C ∧ copt = NONE then frs ∪ {1 ⊗ N2.q0}
                  else frs
              else
                {1 ⊗ s' | s' ∈ N2.tf (nsnd s) copt};
      q0 := 0 ⊗ N1.q0;
      C  := {1 ⊗ r2 | r2 ∈ N2.C };
    |>
End

val _ = set_mapped_fixity {term_name = "machine_link",
                           fixity = Infixl 500,
                           tok = "⌢"}

Theorem machine_link_q0[simp]:
  (N1 ⌢ N2).q0 = 0 ⊗ N1.q0
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
      {0 ⊗ n | n ∈ N1.tf n1 NONE} ∪ {1 ⊗ N2.q0}
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
  NF_transition (N1 ⌢ N2) q0 ts q ∧
  q0 ∈ { 0 ⊗ n1 | n1 ∈ N1.Q } ∧ q ∈ { 1 ⊗ n2 | n2 ∈ N2.Q }
⇒
  ∃q1 ts1 ts2.
    q1 ∈ N1.C ∧ (* q2 = 1 ⊗ N2.q0 *)
    NF_transition N1 (nsnd q0) ts1 q1 ∧
    NF_transition N2 N2.q0 ts2 (nsnd q) ∧
    ts = ts1 ++ [NONE] ++ ts2
Proof
  Induct_on ‘NF_transition’ >> rw[]
  >- (qspec_then ‘q0’ strip_assume_tac npair_cases >> simp[] >>
      rename [‘q0 = m ⊗ n’] >> Cases_on ‘m = 0’ >> simp[]) >>
  fs[PULL_EXISTS] >>
  rename [‘NF_transition _ q1 ts (1 ⊗ n2)’] >>
  qpat_x_assum ‘_ ∈ _.tf _ _’ mp_tac >>
  rw[machine_link_def] >> fs[]
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF] >>
      fs[] >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q0 ts2 n2’] >>
      ‘NF_transition N1 n1 (NONE::ts1) q1’
         by metis_tac[NF_transition_rules, optionTheory.NOT_SOME_NONE] >>
      map_every qexists_tac [‘q1’, ‘NONE::ts1’, ‘ts2’] >> simp[])
  >- (goal_assum drule >> qexists_tac ‘[]’ >> simp[NF_transition_rules])
  >- (rename [‘n1' ∈ N1.tf n1 _’] >>
      ‘n1' ∈ N1.Q’ by metis_tac[wfNFA_def, SUBSET_DEF, NOT_IN_EMPTY,
                                optionTheory.option_CASES] >> fs[] >>
      goal_assum (first_assum o mp_then (Pos (el 3)) mp_tac) >>
      rename [‘ts = ts1 ++ [NONE] ++ ts2’, ‘NF_transition N1 n1' ts1 q1’,
              ‘NF_transition N2 N2.q0 ts2 n2’] >>
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
  NF_transition m q0 ts1 q1 ∧ NF_transition m q1 ts2 q2
  ==>
  NF_transition m q0 (ts1 ++ ts2) q2
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

(* regular languages are closed under concatenation *)
Theorem thm_1_47:
  ∀L1 L2.
    regularLanguage L1 ∧ regularLanguage L2 ⇒ regularLanguage (concat L1 L2)
Proof
  rw[corollary_1_40] >>
  rename1 ‘recogLangN _ = concat (_ N1) (_ N2)’ >>
  qexists_tac ‘N1 ⌢ N2’ >>
  rw[wfNFA_machine_link,EXTENSION,concat_def, recogLangN_def,
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
        (mp_tac o AP_TERM “strip_option: num option list -> num list”) >>
      simp[strip_option_munge]) >>
  rename [‘machine_link N1 N2’,
          ‘NF_transition N1 _ (munge n1 (ZIP (s1,nlist1))) q1’,
          ‘NF_transition N2 _ (munge n2 (ZIP (s2,nlist2))) q2’] >>
  ‘NF_transition (N1 ⌢ N2) (0 ⊗ N1.q0) (munge n1 (ZIP (s1,nlist1))) (0 ⊗ q1)’
     by simp[] >>
  ‘NF_transition (N1 ⌢ N2) (1 ⊗ N2.q0) (munge n2 (ZIP (s2,nlist2))) (1 ⊗ q2)’
     by simp[] >>
  ‘NF_transition (N1 ⌢ N2) (0 ⊗ q1) (NONE::munge n2 (ZIP (s2,nlist2))) (1 ⊗ q2)’
     by (irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >> simp[] >>
         qexists_tac ‘1 ⊗ N2.q0’ >> simp[] >> simp[machine_link_def]) >>
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

(* ----------------------------------------------------------------------
    Regular languages closed under the Kleene star operator
   ---------------------------------------------------------------------- *)

Definition machine_star_def:
  machine_star N =
   <|
     Q :=  IMAGE SUC N.Q ∪ {0} ;
     A :=  N.A ;
     q0 := 0 ;
     tf := λs0 copt.
             case s0 of
               0 => if copt = NONE then {SUC N.q0} else ∅
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
  (machine_star N).tf 0 NONE = {SUC N.q0} ∧
  (machine_star N).tf 0 (SOME c) = ∅ ∧
  ((q ∈ (machine_star N).tf 0 cO) ⇔ (cO = NONE ∧ q = SUC N.q0))
Proof
  rw[machine_star_def]
QED

Theorem machine_star_q0[simp]:
  (machine_star N).q0 = 0
Proof
  simp[machine_star_def]
QED

Theorem machine_star_tfSUC:
  (machine_star N).tf (SUC q0) (SOME c) =
    {SUC q | q ∈ N.tf q0 (SOME c)} ∧
  (machine_star N).tf (SUC q0) NONE =
    {SUC q | q ∈ N.tf q0 NONE} ∪
    (if q0 ∈ N.C then {0} else ∅) ∧
  (SUC q ∈ (machine_star N).tf (SUC q0) cO ⇔
    q ∈ N.tf q0 cO)
Proof
  simp[machine_star_def, EXTENSION] >> rw[]
QED

Definition Lpow_def:
  Lpow lang 0 = {[]} ∧
  Lpow lang (SUC n) = concat lang (Lpow lang n)
End

Theorem star_Lpow:
  star L = BIGUNION (IMAGE (Lpow L) UNIV)
Proof
  simp[Once EXTENSION, star_def, PULL_EXISTS] >> qx_gen_tac ‘s’ >>
  eq_tac >> rw[]
  >- (qexists_tac ‘LENGTH ls’ >> simp[] >>
      Induct_on ‘ls’ >> simp[Lpow_def, DISJ_IMP_THM, FORALL_AND_THM]>>
      simp[concat_def] >> metis_tac[]) >>
  rename [‘s ∈ Lpow L n’] >> pop_assum mp_tac >> qid_spec_tac ‘s’ >>
  Induct_on ‘n’ >> simp[Lpow_def] >> rw[]
  >- (qexists_tac ‘[]’ >> simp[]) >>
  fs[concat_def] >> first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac ‘x::ls’ >> simp[DISJ_IMP_THM]
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
  ∃s1 s2 nc. cs = NONE::s1++[NONE]++s2 ∧ nc ∈ N.C ∧ NF_transition N N.q0 s1 nc ∧
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

Theorem strip_option_EQ_NIL:
  strip_option l = [] ⇔ ∃n. l = REPLICATE n NONE
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
    str = strip_option s1 ++ strR
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
    str = strip_option s1 ++ strR
Proof
 metis_tac[munge_alt_def,munge'_split]
QED

(*

          |-   x = y
        -------------- AP_TERM f
          |- f x = f y

*)

Theorem munge_strip_option_exists:
  ∀s.
    ∃n nlist.
      munge n (ZIP (strip_option s, nlist)) = s ∧
      LENGTH nlist = LENGTH (strip_option s)
Proof
  metis_tac[munge_exists,strip_option_munge]
QED

Theorem NF_transition_machine_star_i:
  NF_transition M q0 cs q ⇒ NF_transition (machine_star M) (SUC q0) cs (SUC q)
Proof
  Induct_on ‘NF_transition’ >> simp[NF_transition_rules] >> rw[] >>
  irule (NF_transition_rules |> SPEC_ALL |> CONJUNCT2) >>
  rw[] >> qexists_tac ‘SUC q0'’ >> rw[] >> rw[machine_star_def] >> rw[]
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
  regularLanguage L ⇒ regularLanguage (star L)
Proof
  simp[corollary_1_40] >>
  disch_then (qx_choose_then ‘M0’ strip_assume_tac) >>
  qexists_tac ‘machine_star M0’ >>
  simp[wfNFA_machine_star, star_Lpow, Once EXTENSION, PULL_EXISTS,EQ_IMP_THM] >>
  qx_gen_tac ‘str’ >> conj_tac
  >- (simp[recogLangN_def, Sipser_ND_Accepts_NF_transition] >>
      rw[] >> pop_assum mp_tac >>
      completeInduct_on ‘LENGTH (munge n (ZIP (str,nlist)))’ >>
      fs[PULL_FORALL] >> rw[] >> drule NF_transition_machine_star >>
      rw[]
      >- (rfs[ZIP_EQ_NIL] >> qexists_tac ‘0’ >> rw[Lpow_def]) >>
      rename1 ‘NONE::(s1 ++ [NONE] ++ s2)’ >>
      ‘NONE::(s1 ++ [NONE] ++ s2) = (NONE::s1 ++ [NONE] ++ s2)’
        by rw[] >>
      pop_assum SUBST_ALL_TAC >>
      drule_then strip_assume_tac munge_split >> rw[] >>
      rfs[] >> rw[] >>
      first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos last) mp_tac) >>
      simp[] >> disch_then (qx_choose_then ‘N’ strip_assume_tac) >>
      qexists_tac ‘SUC N’ >>
      simp[Lpow_def] >>
      simp[concat_def] >>
      qexistsl_tac [‘strip_option s1’,‘strR’] >>
      simp[recogLangN_def,Sipser_ND_Accepts_NF_transition] >>
      metis_tac[munge_strip_option_exists]) >>
  qx_gen_tac ‘n’ >> MAP_EVERY qid_spec_tac [‘str’,‘n’] >>
  fs[recogLangN_def, Sipser_ND_Accepts_NF_transition_l] >>
  rw[] >> pop_assum mp_tac >> qid_spec_tac ‘str’ >>
  Induct_on ‘n’
  >- (simp[Lpow_def] >> qexists_tac ‘[]’ >> rw[NF_transition_rules])
  >> simp[Lpow_def, concat_def, PULL_EXISTS] >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac ‘NONE::l++[NONE]++l'’ >>
  rw[] >> irule NF_transition_cons >> rw[] >> irule NF_transition_concat >>
  qexists_tac ‘0’ >> rw[] >> irule NF_transition_concat >>
  qexists_tac ‘SUC q’ >> rw[]
  >- rw[NF_transition_machine_star_i]
  >> irule NF_transition_cons >> rw[] >> qexists_tac ‘0’ >>
  rw[NF_transition_rules] >> rw[machine_star_def]
QED

Datatype:
regexp = Concat regexp regexp |
         Star regexp |
         Alt regexp regexp |
         Single num |
         Epsilon |
         Empty
End

(* Definition 1.52 *)
Definition regexp_lang[simp]:
  regexp_lang (Concat r1 r2) = concat (regexp_lang r1) (regexp_lang r2) ∧
  regexp_lang (Star r) = star (regexp_lang r) ∧
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
                      q0 := 1;
                      C := {2};|>’ >>
      conj_asm1_tac >>
      rw[wfFA_def, recogLangD_def] >>
      rw[EXTENSION, Sipser_Accepts_runMachine_coincide] >>
      rw[accepts_def] >> eq_tac
      >- (Cases_on ‘x’ >> rw[]
          >- (Cases_on ‘t’ >> fs[runMachine_def] >> Induct_on‘t'’ >> fs[])
          >> Induct_on ‘t’ >> fs[])
      >> simp[])
  >- (rw[regularLanguage_def] >>
      qexists_tac ‘<| Q := {0;1};
                      A := {};
                      tf := (λs0 c. 0);
                      q0 := 1;
                      C := {1};|>’ >>
      conj_asm1_tac >>
      rw[wfFA_def, recogLangD_def] >>
      rw[EXTENSION, Sipser_Accepts_runMachine_coincide] >>
      rw[accepts_def] >> eq_tac
      >- (Cases_on ‘x’ >> rw[] >> Induct_on ‘t’ >> simp[])
      >> simp[])
  >> rw[regularLanguage_def] >>
     qexists_tac ‘<| Q := {0;1;2};
                      A := {};
                      tf := (λs0 c. 0);
                      q0 := 1;
                      C := {2};|>’ >>
     conj_asm1_tac >>
     rw[wfFA_def, recogLangD_def] >>
     rw[EXTENSION, Sipser_Accepts_runMachine_coincide] >>
     rw[accepts_def] >>
     Cases_on ‘x’ >> rw[] >> Induct_on ‘t’ >> rw[]
QED

(* Definition 1.64 *)
Datatype:
  gnfa = <|
    Q : state set;
    A : symbol set;
    tf : state -> state -> regexp;
    q0 : state;
    C : state;
  |>
End

Definition wfm_gnfa_def:
  wfm_gnfa G ⇔ FINITE G.Q ∧ G.q0 ∈ G.Q ∧ G.C ∈ G.Q ∧ G.q0 ≠ G.C ∧
               (∀s. G.tf s G.q0 = Empty) ∧
               (∀s. G.tf G.C  s = Empty)
End

Inductive gnfa_accepts:
[~nil:]
  ∀q0. q0 IN G.Q ⇒ gnfa_accepts G q0 [] q0
[~step:]
  ∀q' q. q0 IN G.Q ∧ q' IN G.Q ∧ c1 ∈ regexp_lang (G.tf q0 q') ∧
         gnfa_accepts G q' c2 q ⇒
         gnfa_accepts G q0 (c1++c2) q
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
                          tf := (λs1 s2. if s1 = 0 ∧ s2 = d.q0+2 then Epsilon
                                         else if s1 ∈ IMAGE ($+2) d.C ∧ s2 = 1
                                         then
                                           Epsilon
                                         else if 1 < s1 ∧ 1 < s2 then
                                         let s = {cs | d.tf (s1-2) cs = s2-2}
                                         in
                                            charset_re s
                                         else Empty);
                          q0 := 0;
                          C := 1; |>
End

Theorem dfa_to_gnfa_wfm:
  wfFA d ⇒ wfm_gnfa (dfa_to_gnfa d)
Proof
  rw[wfFA_def, wfm_gnfa_def, dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_q0[simp]:
  ∀d. (dfa_to_gnfa d).q0 = 0
Proof
  rw[dfa_to_gnfa_def]
QED

Theorem dfa_to_gnfa_tf_0[simp]:
  ∀d x. ((dfa_to_gnfa d).tf 0 x = if x = d.q0 + 2 then Epsilon else Empty) ∧
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
  ∀d cs es. gnfa_accepts (dfa_to_gnfa d) (d.q0 + 2) cs es
              ⇔ es ≠ 0 ∧ gnfa_accepts (dfa_to_gnfa d) (dfa_to_gnfa d).q0 cs es
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
  wfFA d ∧ s ∈ d.Q ∧ s ∈ d.C
  ⇒
  gnfa_accepts (dfa_to_gnfa d) (s + 2) [] 1
Proof
  rw[] >>
  ‘[] ∈ regexp_lang ((dfa_to_gnfa d).tf (s+2) 1)’ by rw[dfa_to_gnfa_def] >>
  ‘1 ∈ (dfa_to_gnfa d).Q ∧ s+2 ∈ (dfa_to_gnfa d).Q’ by simp[] >>
  dxrule_then (drule_then (drule_then strip_assume_tac)) gnfa_accepts_step >>
  fs[] >> simp[gnfa_accepts_rules]
QED

Theorem runMachine_c_in_A:
  ∀d s c cs. runMachine d (d.tf s c) cs ∈ d.C ∧ wfFA d ⇒ c ∈ d.A
Proof
  CCONTR_TAC >> fs[] >> ‘d.tf s c = 0’ by fs[wfFA_def] >> fs[] >>
  drule_then strip_assume_tac runMachine_0_sticks >> metis_tac[wfFA_def]
QED

Theorem gnfa_error_sink:
  ∀d. (wfFA d ⇒ ∀q cs. gnfa_accepts (dfa_to_gnfa d) 2 cs q ⇒ (q = 2))
Proof
  ntac 2 strip_tac >>
  Induct_on ‘gnfa_accepts’ >>
  rw[] >> fs[]
  >- (rw[] >> fs[dfa_to_gnfa_def] >> rfs[wfFA_def]) >>
  rw[] >>
  pop_assum irule >>
  pop_assum kall_tac >>
  fs[dfa_to_gnfa_def] >>
  rfs[wfFA_def] >> rw[] >> CCONTR_TAC >> fs[] >>
  fs[regexp_lang_charset_re]
QED

Theorem runMachine_append[simp]:
  ∀d s c1 c2. runMachine d s (c1++c2) = runMachine d (runMachine d s c1) c2
Proof
  Induct_on ‘c1’ >> rw[]
QED

Theorem gnfa_accepts_1_to_1:
  ∀d cs. wfFA d ∧ gnfa_accepts (dfa_to_gnfa d) 1 cs 1 ⇒ cs = []
Proof
  rw[Once gnfa_accepts_cases] >> qpat_x_assum ‘c1 ∈ _’ mp_tac >>
  rw[dfa_to_gnfa_def]
QED

Theorem gnfa_accepts_2_to_1:
  ∀d cs. wfFA d ⇒ ¬gnfa_accepts (dfa_to_gnfa d) 2 cs 1
Proof
  ‘∀d x cs y. gnfa_accepts (dfa_to_gnfa d) x cs y ⇒ x = 2 ⇒ y = 1 ⇒ wfFA d ⇒ F’
    suffices_by metis_tac[] >> gen_tac >>
  ho_match_mp_tac gnfa_accepts_ind >> rw[] >>
  fs[dfa_to_gnfa_def] >> strip_tac >> fs[] >> fs[wfFA_def] >>
  Cases_on ‘1 < x'’ >> fs[regexp_lang_charset_re]
QED

Theorem dfa_to_gnfa_correct:
  ∀d. wfFA d ⇒
      ∃g. wfm_gnfa g ∧ ∀cs. Sipser_Accepts d cs ⇔ gnfa_accepts g g.q0 cs g.C
Proof
  rw[] >> qexists_tac ‘dfa_to_gnfa d’ >> rw[dfa_to_gnfa_wfm] >>
  rw[Sipser_Accepts_runMachine_coincide_thm,accepts_def] >>
  ‘∀s. s ∈ d.Q ⇒
    (runMachine d s cs ∈ d.C ⇔
    gnfa_accepts (dfa_to_gnfa d) (s + 2) cs (dfa_to_gnfa d).C)’
    suffices_by (fs[dfa_prod_gnfa_shuffle_start,wfFA_def] >>
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
                >- fs[wfFA_def]
                >> rw[SUBSET_DEF] >> metis_tac[runMachine_c_in_A]) >>
          simp[regexp_lang_charset_re])
      >- (fs[wfFA_def] >> metis_tac[]) >>
      first_x_assum irule >> rw[] >> metis_tac[wfFA_def, runMachine_c_in_A]) >>
  Induct_on ‘gnfa_accepts’ >> rw[] >> qpat_x_assum ‘c1 ∈ _’ mp_tac >>
  rw[dfa_to_gnfa_def] >> fs[]
  >- (drule gnfa_accepts_1_to_1 >> rw[]) >>
  rfs[] >> rw[] >> ‘runMachine d q c1 = q'’ suffices_by simp[] >>
  ‘FINITE {cs | d.tf q cs = q'}’
        by (irule SUBSET_FINITE_I >> qexists_tac ‘d.A’ >> fs[wfFA_def] >>
            rw[SUBSET_DEF] >> metis_tac[runMachine_c_in_A, wfFA_def]) >>
  fs[regexp_lang_charset_re] >> rw[] >> fs[wfFA_def]
QED

Definition rip_def:
  rip G q = if q IN G.Q ∧ q ≠ G.q0 ∧ q <> G.C then
            G with
            <| Q := G.Q DELETE q ;
               tf := \i j. if i = G.C then Empty
                           else if j = G.q0 then Empty
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
  ∀G q0 l q. gnfa_accepts G q0 l q ⇒ q0 ∈ G.Q ∧ q ∈ G.Q
Proof
  gen_tac >> Induct_on ‘gnfa_accepts’ >> simp[]
QED

Theorem gnfa_accepts_star:
 ∀x G q0 l q.
   x IN star (regexp_lang (G.tf q0 q0)) ∧
   gnfa_accepts G q0 l q ⇒ gnfa_accepts G q0 (x ⧺ l) q
Proof
 simp[star_Lpow, PULL_EXISTS] >>
 CONV_TAC (RENAME_VARS_CONV ["s","G","q0","l","q","n"]) >>
 Induct_on ‘n’ >> simp[Lpow_def,concat_def,PULL_EXISTS] >> rw[] >>
 metis_tac[APPEND_ASSOC,gnfa_accepts_step,gnfa_accepts_q_in_Q]
QED

Theorem G_rip_Q:
q ∈ G.Q ∧ q ≠ G.q0 ∧ q ≠ G.C ⇒ (rip G q).Q = G.Q DELETE q
Proof
rw[rip_def]
QED


Theorem G_rip_back_sim:
  ∀q0 s. wfm_gnfa G ∧ q0 ≠ q ∧ q ≠ G.q0 ∧ q ≠ G.C ∧ q IN G.Q ∧
         gnfa_accepts (rip G q) q0 s G.C ⇒ gnfa_accepts G q0 s G.C
Proof
  Induct_on ‘gnfa_accepts’ >>
  reverse (rw[rip_def,gnfa_accepts_rules])
  >- metis_tac[gnfa_accepts_rules]
  >> Cases_on ‘q0 = G.C’ >> fs[] >>
  Cases_on ‘q0' = G.q0’ >> reverse (fs[])
  >- (reverse (Cases_on ‘q0' = q’)
      >- metis_tac[gnfa_accepts_rules]
      >> fs[])
  >> fs[concat_def] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  irule gnfa_accepts_step >> simp[] >>
  qexists_tac ‘q’ >>
  ASM_REWRITE_TAC [GSYM APPEND_ASSOC] >> irule gnfa_accepts_star >> simp[] >>
  metis_tac[gnfa_accepts_step,gnfa_accepts_q_in_Q]
QED

Inductive gnfaA':
  (∀q0. q0 ∈ G.Q ⇒ gnfaA' G q0 [] [q0] q0) ∧
  (∀q0 q1 q2 s1 s2 states.
     q0 ∈ G.Q ∧ q1 ∈ G.Q ∧
     s1 ∈ regexp_lang (G.tf q0 q1) ∧
     gnfaA' G q1 s2 states q2
     ⇒
     gnfaA' G q0 (s1 ++ s2) (q0::states) q2)
End

Theorem gnfaA'_states_nonempty:
  gnfaA' G q0 str sts q ⇒ sts ≠ [] ∧ HD sts = q0 ∧ LAST sts = q
Proof
  Induct_on ‘gnfaA'’ >> simp[LAST_CONS_cond]
QED

Theorem gnfa_accepts_gnfaA':
  gnfa_accepts G q0 str q ⇒ ∃sts. gnfaA' G q0 str sts q
Proof
  Induct_on ‘gnfa_accepts’ >> simp[] >> metis_tac[gnfaA'_rules]
QED

Theorem gnfaA'_gnfa_accepts:
  gnfaA' G q0 str sts q ⇒ gnfa_accepts G q0 str q
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

Theorem FILTER_REPLICATE:
  FILTER P (REPLICATE n e) = if P e then REPLICATE n e else []
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem gnfaA'_APPEND_states:
  ∀G q0 str sts1 sts2 q.
    gnfaA' G q0 str (sts1 ++ sts2) q ∧ sts1 ≠ [] ∧ sts2 ≠ [] ⇒
    ∃str1 str2 q1. str = str1 ++ str2 ∧
                   q1 ∈ G.Q ∧
                   gnfaA' G q0 str1 (sts1 ++ [HD sts2]) q1 ∧
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

Theorem LAST_REPLICATE:
  0 < n ⇒ LAST (REPLICATE n r) = r
Proof
  Induct_on ‘n’ >> rw[LAST_CONS_cond]
QED

Theorem HD_APPEND:
  a ≠ [] ⇒ HD (a ++ b) = HD a
Proof
  Cases_on ‘a’ >> rw[]
QED

Theorem HD_REPLICATE:
  0 < n ⇒ HD (REPLICATE n r) = r
Proof
  Cases_on ‘n’ >> rw[]
QED

Theorem gnfaA'_q_to_q0:
  wfm_gnfa G ⇒ gnfaA' G q str sts G.q0 ⇒ q = G.q0 ∧ sts = [G.q0]
Proof
  Induct_on ‘gnfaA'’ >> rw[] >> Cases_on ‘wfm_gnfa G’ >> fs[] >> rw[] >>
  fs[wfm_gnfa_def]
QED

Theorem gnfaA'_in_G:
∀s l q0 q. gnfaA' G q0 s l q ⇒ ∀st. MEM st l ⇒ st IN G.Q
Proof
Induct_on ‘gnfaA'’ >> simp[DISJ_IMP_THM]
QED

Theorem gnfaA'_APPEND_states2:
  ∀G q0 str sts1 sts2 q.
         gnfaA' G q0 str (sts1 ⧺ sts2) q ∧ sts1 ≠ [] ∧ sts2 ≠ [] ⇒
         ∃str1 str2 q1.
             str = str1 ⧺ str2 ∧ q1 ∈ G.Q ∧
             gnfaA' G q0 str1 sts1 q1 ∧ gnfaA' G q1 str2 (LAST sts1 :: sts2) q
Proof
 rw[] >> Cases_on ‘sts1’ >> fs[] >> rename [‘q1 :: (sts1 ++ sts2)’] >>
 ‘q0 = q1’ by (drule gnfaA'_states_nonempty >> simp[]) >> rw[] >>
 Cases_on ‘sts1 = []’ >> fs[] (* 2 *)
 >- (first_assum (goal_assum o resolve_then (Pos last) mp_tac) >>
     csimp[gnfaA'_rules] >>
     metis_tac[gnfaA'_in_G,MEM]) >>
 ‘q0::(sts1 ⧺ sts2) = FRONT (q0::sts1) ++ LAST (q0::sts1) :: sts2’
   by (‘LAST (q0::sts1)::sts2 = [LAST (q0::sts1)] ++ sts2’ by simp[] >>
      simp[APPEND_FRONT_LAST]) >>
 qpat_x_assum ‘gnfaA' _ _ _ _ _’ mp_tac >> simp[] >>
 strip_tac >> drule gnfaA'_APPEND_states >> simp[APPEND_FRONT_LAST]
QED


Theorem gnfaA'_REPLICATE:
  ∀G q s n.
    gnfaA' G q s (REPLICATE n q) q ⇒
    s ∈ star (regexp_lang (G.tf q q))
Proof
  Induct_on ‘n’ >> rw[]
  >- fs[Once gnfaA'_cases]  >>
  pop_assum mp_tac >> simp[Once gnfaA'_cases] >>
  rw[] >- fs[empty_in_star] >>
  Cases_on ‘n = 0’
  >- (qpat_x_assum ‘gnfaA' _ _ _ _ _ ’ mp_tac >> simp[Once gnfaA'_cases]) >>
  rename [‘s1 ∈ regexp_lang (G.tf q q1)’] >>
  ‘q1 = q’
    by (drule gnfaA'_states_nonempty >>
        simp[HD_REPLICATE]) >>
  gvs[] >> first_x_assum $ drule_all_then assume_tac >>
  gvs[star_def] >> rename1 ‘s1 ++ FLAT ls’ >> qexists_tac ‘s1::ls’ >>
  rw[] >> rw[]
QED

Theorem gnfaA'_rip_filter:
  ∀sts q0 str q r.
    wfm_gnfa G ∧ gnfaA' G q0 str sts q ∧ q0 ≠ r ∧ q ≠ r ∧ r ∈ G.Q ∧ r ≠ G.q0 ∧
    r ≠ G.C ⇒
    gnfaA' (rip G r) q0 str (FILTER (λq. q ≠ r) sts) q
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
      >- (fs[] >> rw[] >> drule_all gnfaA'_q_to_q0 >> rw[]) >>
      DISJ1_TAC >> simp[Once concat_def] >> goal_assum (drule_at (Pos $ el 2))>>
      simp[] >>
      drule gnfaA'_APPEND_states2 >> simp[] >> strip_tac >>
      drule gnfaA'_states_nonempty >> simp[] >> rw[] >> rfs[LAST_REPLICATE] >>
      simp[concat_def] >> simp[] >>
      rename [‘s1 ++ s2 = _ ++ _’] >> qexistsl_tac [‘s1’,‘s2’] >> simp[] >>
      reverse conj_tac (* 2 *)
      >- (pop_assum mp_tac >> simp[Ntimes gnfaA'_cases 3]) >>
      metis_tac[gnfaA'_REPLICATE]) >>
  rw[rip_def]
QED

Theorem G_rip_forw_sim:
  ∀q0 s q1 q. wfm_gnfa G ∧ q0 ∈ G.Q ∧ q ≠ q0 ∧ q1 ∈ G.Q ∧ q ≠ q1 ∧ q ∈ G.Q ∧
         gnfa_accepts G q0 s q1 ⇒ gnfa_accepts (rip G q) q0 s q1
Proof
  rw[] >>
  Cases_on ‘q = G.q0’ >- gvs[rip_def] >>
  Cases_on ‘q = G.C’  >- gvs[rip_def] >>
  metis_tac[gnfaA'_gnfa_accepts,gnfa_accepts_gnfaA',gnfaA'_rip_filter]
QED

Theorem G_rip_sim:
  ∀s q. wfm_gnfa G ∧ q ≠ G.q0 ∧ q ≠ G.C ∧ q ∈ G.Q ⇒
         (gnfa_accepts (rip G q) G.q0 s G.C ⇔ gnfa_accepts G G.q0 s G.C)
Proof
  metis_tac[G_rip_back_sim,G_rip_forw_sim,wfm_gnfa_def]
QED

Definition reduced_gnfa_def:
  reduced_gnfa G =
    if FINITE G.Q ∧ 2 < CARD G.Q then
      reduced_gnfa (rip G (MAX_SET (G.Q DIFF {G.q0; G.C})))
    else
      G
Termination
  WF_REL_TAC ‘measure (λG. CARD G.Q)’ >>
  rw[rip_def] >> Cases_on ‘FINITE G.Q’ >> simp[] >> strip_tac >>
  ‘G.Q DIFF {G.q0; G.C} ≠ ∅’
    by (simp[SUBSET_DIFF_EMPTY] >> strip_tac >>
        drule_at (Pos last) CARD_SUBSET >>
        gvs[]) >>
  ‘FINITE (G.Q DIFF {G.q0; G.C})’
    by simp[] >>
  drule_all (cj 1 MAX_SET_DEF) >> gvs[]
End


Theorem reduced_gnfa_same:
  wfm_gnfa G ⇒
    (gnfa_accepts G G.q0 s G.C ⇔
    gnfa_accepts (reduced_gnfa G) (reduced_gnfa G).q0 s (reduced_gnfa G).C)
Proof
  reverse (Cases_on ‘FINITE G.Q’)
  >- (ntac 3 (rw[Once reduced_gnfa_def])) >>
  pop_assum mp_tac >> qid_spec_tac ‘G’ >>
  ho_match_mp_tac reduced_gnfa_ind  >> rw[] >>
  qabbrev_tac ‘ms = MAX_SET (G.Q DIFF {G.q0; G.C})’ >>
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
  ‘(rip G ms).q0 = G.q0 ∧ (rip G ms).C = G.C’
    by rw[rip_def] >>
  simp[] >> irule G_rip_sim >>
  qunabbrev_tac ‘ms’ >>
  ‘G.Q DIFF {G.q0; G.C} ≠ ∅’
    by (simp[SUBSET_DIFF_EMPTY] >> strip_tac >>
        drule_at (Pos last) CARD_SUBSET >>
        gvs[]) >>
  ‘FINITE (G.Q DIFF {G.q0; G.C})’
    by simp[] >>
  drule_all (cj 1 MAX_SET_DEF) >> gvs[]
QED

Theorem reduced_gnfa_facts[simp]:
  ∀GN. (reduced_gnfa GN).q0 = GN.q0 ∧ (reduced_gnfa GN).C = GN.C
Proof
  ho_match_mp_tac reduced_gnfa_ind >> simp[] >> qx_gen_tac ‘GN’ >> strip_tac >>
  ONCE_REWRITE_TAC[reduced_gnfa_def] >>
  Cases_on ‘FINITE GN.Q ∧ 2 < CARD GN.Q’ >> simp[] >>
  qmatch_abbrev_tac ‘(rip GN s).q0 = GN.q0 ∧ _’ >>
  rw[rip_def]
QED

Theorem reduced_gnfas_have_two_states:
  ∀GN. wfm_gnfa GN ⇒
       (reduced_gnfa GN).Q = {GN.q0 ; GN.C }
Proof
  ho_match_mp_tac reduced_gnfa_ind >> qx_gen_tac ‘GN’ >> rpt strip_tac >>
  ONCE_REWRITE_TAC [reduced_gnfa_def] >> reverse (rw[])
  >- (gvs[wfm_gnfa_def, arithmeticTheory.NOT_LESS] >>
      simp[EXTENSION, EQ_IMP_THM, DISJ_IMP_THM] >> CCONTR_TAC >> gvs[] >>
      rename [‘s ≠ GN.C’, ‘s ≠ GN.q0’] >>
      ‘{s; GN.C; GN.q0} ⊆ GN.Q’ by simp[SUBSET_DEF] >>
      ‘CARD {s;GN.C;GN.q0} ≤ CARD GN.Q’ by metis_tac[CARD_SUBSET] >>
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
  ‘GN.C ≠ GN.q0’ by gvs[wfm_gnfa_def] >> simp[reduced_gnfas_have_two_states] >>
  qexists_tac ‘(reduced_gnfa GN).tf GN.q0 GN.C’ >> qx_gen_tac ‘str’ >> eq_tac
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

Theorem wfFA_remain_Q:
  ∀M. wfFA M ⇒
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
     Cases_on ‘ss’ >> fs[wfFA_def] >>
     metis_tac[])
QED


Theorem runMachine_segment:
∀i j ss s M.
  (∀n. n < LENGTH ss − 1 ⇒ M.tf (EL n ss) (EL n s) = EL (n + 1) ss) ∧
  i < LENGTH ss ∧ j ≤ i ∧ LENGTH ss = LENGTH s + 1 ⇒
  runMachine M (EL j ss) (DROP j (TAKE i s)) = EL i ss
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
  (* We decided this should be changed to use runMachine and
     GENLIST instead of Sipser_Accepts in the assumptions *)
  rw[regularLanguage_def,recogLangD_def] >>
  qexists_tac ‘SUC (CARD(M.Q))’ >>
  rw[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [Sipser_Accepts_def]) >>
  fs[] >>
  ‘∃ n m. n < m ∧ m < LENGTH ss ∧ EL n ss = EL m ss’
    by (‘¬INJ (λx. EL x ss) (count (LENGTH ss)) M.Q’
          suffices_by (rw[INJ_IFF]
                       >- (metis_tac[wfFA_def,wfFA_remain_Q,MEM_EL,
                                     arithmeticTheory.ADD1]) >>
                       rename[‘EL i ss = EL j ss ⇔ i = j’] >>
                       ‘i ≠ j’ by metis_tac[] >>
                       fs[] >>
                       metis_tac[DECIDE “a ≠ b ⇒ a < b ∨ b < a”]) >>
        irule PHP >>
        simp[] >> fs[wfFA_def]) >>
  map_every qexists_tac [‘TAKE n s’,‘DROP n (TAKE m s)’,‘DROP m s’] >>
  simp[Sipser_Accepts_runMachine_coincide,accepts_def,runMachine_append] >>
  conj_tac
  >- simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", Excl "LIST_EQ_SIMP_CONV",
          GSYM DROP_APPEND1] >> ‘n < LENGTH ss - 1’ by fs[] >>
  ‘runMachine M M.q0 (TAKE n s) = EL n ss’
    by (drule runMachine_segment >> rw[] >>
        first_x_assum (qspecl_then [‘n’, ‘0’] MP_TAC) >> simp[]) >> simp[] >>
  ‘∀i. runMachine M (EL m ss) (exp (DROP n (TAKE m s)) i) = EL m ss’
    by (Induct_on ‘i’ >> rw[] >> simp[exp_def] >>
        ‘runMachine M (EL m ss) (DROP n (TAKE m s)) = EL m ss’
          suffices_by simp[] >> drule runMachine_segment >> simp[] >>
        disch_then $ qspecl_then [‘m’, ‘n’] mp_tac >> rw[]) >> simp[] >>
  drule_then (qspecl_then [‘LENGTH s’, ‘m’] mp_tac) runMachine_segment >> rw[]>>
  ‘EL (LENGTH s) ss = LAST ss’ suffices_by simp[] >>
  simp[LAST_EL, GSYM ADD1]
QED


val _ = export_theory();
