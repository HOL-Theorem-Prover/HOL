(*===========================================================================*)
(* Basic automata theory: nfas, dfas, their equivalence via the subset       *)
(* construction, closure constructions, Myhill-Nerode, etc. The approach     *)
(* taken is set-oriented, rather than computational.                         *)
(*===========================================================================*)

Theory regular
Ancestors
  combin relation pred_set pair
  prim_rec arithmetic list rich_list
  FormalLang dirGraph dft
Libs
  mp_then dep_rewrite

(*---------------------------------------------------------------------------*)
(* Syntax support                                                            *)
(*---------------------------------------------------------------------------*)

Overload "\206\181"[local] = listSyntax.nil_tm  (* epsilon = UTF8.chr 0x03B5 *)
Overload "\226\138\136"[local] = “λx y. ~(x ⊆ y)” (* not_subset = UTF8.chr 0x2288 *)

Overload "RTC"[local] = “λs. KSTAR{[a] | a ∈ s}”
Overload "RTC"[local] = “KSTAR”
Overload "TC"[local]  = “KPLUS”

val _ = set_fixity (UTF8.chr 0x2288) (Infix(NONASSOC, 450))

val sym = SYM
val subst_all_tac = SUBST_ALL_TAC
val sym_subst_all_tac = subst_all_tac o sym
val pop_subst_tac = pop_assum subst_all_tac;
val pop_sym_subst_tac = pop_assum sym_subst_all_tac;
val pop_keep_tac = pop_assum mp_tac
val qpat_stage_tac = Lib.C qpat_x_assum mp_tac;
val pop_forget_tac = pop_assum kall_tac
val qpat_forget_tac = Lib.C qpat_x_assum kall_tac;
val staged_forget_tac = disch_then kall_tac;
val forget_tac = WEAKEN_TAC

val PUSH_EXISTS = LIST_CONJ
  [GSYM RIGHT_OR_EXISTS_THM,
   GSYM LEFT_OR_EXISTS_THM,
   RIGHT_EXISTS_IMP_THM,
   RIGHT_EXISTS_AND_THM,
   LEFT_EXISTS_IMP_THM,
   LEFT_EXISTS_AND_THM,
   EXISTS_OR_THM];

fun dty_metis_tac list =
  let open TypeBasePure
      val dtys =  TypeBase.elts()
      val distinct = List.mapPartial distinct_of dtys
      val one_one  = List.mapPartial one_one_of dtys
   in metis_tac (list @ distinct @ one_one)
   end

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

Theorem gspec_lemma[local]:
  {f x | x = y} = {f y}
Proof
  rw [EXTENSION,EQ_IMP_THM]
QED

Theorem SUBSET_SKOLEM_THM :
  (!x. P x ==> ?y. Q x y) <=> ?f. !x. P x ==> Q x (f x)
Proof
 metis_tac[]
QED

Theorem SUBSET_UNION_RIGHT[local]:
 x ⊆ y ⇒ x ⊆ y ∪ z
Proof
  rw[SUBSET_DEF]
QED

Theorem UNION_EQ_DIFF[local]:
 A ∪ B = C ⇒ A DIFF B = C DIFF B
Proof
  rw [EXTENSION] >> metis_tac[]
QED

Theorem DIFF_EQ_UNION[local]:
 A DIFF B = C ⇒ A ∪ B = C ∪ B
Proof
  rw [EXTENSION] >> metis_tac[]
QED

Theorem MAX_SET_BOUNDED:
  FINITE s ∧ MAX_SET s < n ⇒ n ∉ s
Proof
 rw[] >> spose_not_then assume_tac >> drule_all X_LE_MAX_SET >> decide_tac
QED

Theorem finite_image_range[local]:
  FINITE t ⇒ (∀x. x ∈ s ⇒ f x ∈ t) ⇒ FINITE(IMAGE f s)
Proof
  rw [] >>
  ‘IMAGE f s ⊆ t’ by
    (rw[SUBSET_DEF] >> metis_tac[]) >>
  irule SUBSET_FINITE >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* List destructors: HD, TL, and LAST                                        *)
(*---------------------------------------------------------------------------*)

Theorem HD_APPEND[local,simp]:
 ∀l1 l2. l1 ≠ [] ⇒ HD (l1 ++ l2) = HD l1
Proof
 Cases >> rw[]
QED

Theorem HD_SNOC[local,simp]:
 ∀l x. l ≠ [] ⇒ HD (SNOC x l) = HD l
Proof
  Cases >> rw[]
QED

Theorem HD_FRONT[local,simp]:
 FRONT l ≠ [] ⇒ HD (FRONT l) = HD l
Proof
  Cases_on ‘l’ >> rw[FRONT_DEF]
QED

Theorem HD_MAP[local,simp]:
 l ≠ [] ⇒ HD (MAP f l) = f (HD l)
Proof
 Cases_on ‘l’ >> rw[]
QED

Theorem HD_MAP2[local,simp]:
 l1 ≠ [] ∧ l2 ≠ [] ⇒ HD (MAP2 f l1 l2) = f (HD l1) (HD l2)
Proof
 Cases_on ‘l1’ >> Cases_on ‘l2’ >> rw[]
QED

Theorem TL_APPEND[local,simp]:
 ∀l1 l2. l1 ≠ [] ⇒ TL (l1 ++ l2) = TL l1 ++ l2
Proof
 Cases >> rw[]
QED

Theorem LAST_MAP[local,simp]:
 l ≠ [] ⇒ LAST (MAP f l) = f (LAST l)
Proof
 Cases_on ‘l’ >> rw[]
QED

Theorem LAST_TL[local,simp]:
  ∀l. TL l ≠ [] ⇒ LAST (TL l) = LAST l
Proof
 Cases >> rw[LAST_DEF]
QED

Theorem EL_TL[local,simp]:
  ∀l. l ≠ [] ⇒ EL n (TL l) = EL (n+1) l
Proof
 Cases >> rw[GSYM ADD1]
QED

Theorem LENGTH_TL_ALT[local]:
 n < LENGTH l ⇒ LENGTH (TL l) = LENGTH l − 1
Proof
 rw [LENGTH_TL]
QED

Theorem LESS_FRONT_LENGTH[local,simp]:
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

Theorem EVERY_TL[local]:
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

Theorem POS_LENGTH_NOT_NIL[local]:
  n < LENGTH list ⇒ list ≠ []
Proof
 Cases_on ‘list’ >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* FLAT                                                                      *)
(*---------------------------------------------------------------------------*)

Theorem FLAT_NOT_NIL[local]:
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

Theorem el_last[local,simp]:
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

Theorem EL_LENGTH_LAST[local]:
 ∀l1 l2. LENGTH l1 = LENGTH l2 + 1 ⇒ EL (LENGTH l2) l1 = LAST l1
Proof
 ho_match_mp_tac SNOC_INDUCT >> rw[ADD1] >>
 pop_assum (SUBST_ALL_TAC o GSYM) >> rw [EL_LENGTH_SNOC]
QED

Theorem LAST_MAP2[local]:
  ∀l1 l2 f.
    l1 ≠ [] ∧ l2 ≠ [] ∧ LENGTH l1 = LENGTH l2
    ⇒ LAST (MAP2 f l1 l2) = f (LAST l1) (LAST l2)
Proof
  rw[] >>
  ‘MAP2 f l1 l2 ≠ []’ by (map_every Cases_on [‘l1’, ‘l2’] >> fs[]) >>
  rw [LAST_EL] >> irule EL_MAP2 >> Cases_on ‘l2’ >> fs[]
QED

(*---------------------------------------------------------------------------*)
(* SNOC                                                                      *)
(*---------------------------------------------------------------------------*)

Theorem snoc2[local]:
 ∀list n. LENGTH list = n+2 ⇒ ∃z f. list = SNOC z f ∧ f ≠ []
Proof
  rpt strip_tac >> Cases_on ‘list = []’
  >- fs[]
  >- (drule SNOC_LAST_FRONT >> Cases_on ‘FRONT list = []’
      >- (Cases_on ‘list’ >> fs[])
      >- metis_tac [])
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
    Sigma : 'a set ;
    delta : state -> 'a -> state set;
    initial : state set;
    final : state set
  |>
End

Definition is_nfa_def:
  is_nfa N ⇔
    FINITE N.Q ∧
    FINITE N.Sigma ∧
    N.initial ⊆ N.Q ∧
    N.final ⊆ N.Q ∧
    (∀q a. a ∈ N.Sigma ∧ q ∈ N.Q ⇒ N.delta q a ⊆ N.Q)
End

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
    is_nfa N ∧
    (∃q_0. N.initial = {q_0}) ∧
    (∀q a. q ∈ N.Q ∧ a ∈ N.Sigma ⇒ ∃q'. N.delta q a = {q'})
End

Theorem dfa_is_nfa:
  is_dfa N ⇒ is_nfa N
Proof
  metis_tac[is_dfa_def]
QED

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

Theorem is_dfa_example:
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
  is_nfa N ∧ w ∈ nfa_lang N ⇒ ∃qs. is_exec N qs w
Proof
 rw [is_exec_def,in_nfa_lang,is_nfa_def] >> metis_tac [SUBSET_DEF]
QED

Theorem in_nfa_lang_is_accepting_exec:
  is_nfa N ∧ w ∈ nfa_lang N
  ⇒
  ∃qs. is_accepting_exec N qs w ∧ ~NULL qs
Proof
  rw [is_accepting_exec_def,is_exec_def,in_nfa_lang,is_nfa_def] >>
  ‘~NULL qs’ by (Cases_on ‘qs’ >> fs[]) >>
  metis_tac [SUBSET_DEF]
QED

Theorem in_nfa_lang_iff_accepting_exec:
  is_nfa N ⇒
  (w ∈ nfa_lang N ⇔ ∃qs. is_accepting_exec N qs w)
Proof
  rw [is_accepting_exec_def,is_exec_def,in_nfa_lang,is_nfa_def,EQ_IMP_THM] >>
  metis_tac [SUBSET_DEF]
QED

Theorem epsilon_in_nfa_lang:
  is_nfa N ⇒ (ε ∈ nfa_lang N ⇔ N.initial ∩ N.final ≠ ∅)
Proof
  rw [is_nfa_def, in_nfa_lang, LENGTH_EQ_NUM_compute, EQ_IMP_THM] >>
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

Theorem is_exec_nonempty_as_snoc:
  is_nfa N ∧ is_exec N qs w ⇒ ∃qs' q. qs = SNOC q qs'
Proof
 metis_tac [is_exec_nonempty,SNOC_CASES]
QED

Theorem is_exec_tl_nonempty:
  w ≠ ε ∧ is_exec N qs w ⇒ TL qs ≠ []
Proof
 rw [is_exec_def] >>
 Cases_on ‘qs’ >> fs[GSYM ADD1] >>
 Cases_on ‘t’ >> fs[]
QED

Theorem is_exec_states:
  is_nfa N ∧ is_exec N qs w ⇒ EVERY (λq. q ∈ N.Q) qs
Proof
  rw [is_exec_def,EVERY_EL] >> Induct_on ‘n’ >> rw[] >> fs[] >>
  ‘n < LENGTH w’ by decide_tac >> last_x_assum drule >>
  metis_tac [ADD1, is_nfa_def,SUBSET_DEF]
QED

Theorem is_exec_hd_state:
  is_exec N qs w ⇒ HD qs ∈ N.Q
Proof
 rw [is_exec_def]
QED

Theorem is_exec_last_state:
  is_nfa N ∧ is_exec N qs w ⇒ LAST qs ∈ N.Q
Proof
  rw [] >> drule is_exec_nonempty >>
  drule_all is_exec_states >> rw [] >>
  drule_all EVERY_LAST >> simp[]
QED

Theorem is_exec_TL:
  is_nfa N ∧ is_exec N qs w ∧ w ≠ ε ⇒ is_exec N (TL qs) (TL w)
Proof
  rw [is_exec_def]
  >- (Cases_on ‘w’ >> fs [])
  >- (Cases_on ‘qs’ >> Cases_on ‘w’ >> fs[])
  >- (Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> fs[GSYM ADD1] >>
      ‘0 < LENGTH w’ by decide_tac >> first_x_assum drule >> rw[] >>
      Cases_on ‘w’ >> fs[] >> metis_tac [is_nfa_def,SUBSET_DEF])
  >- (‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >> rw [] >>
      ‘0 < LENGTH w’ by (Cases_on ‘w’ >> fs[]) >> fs [LENGTH_TL] >>
      ‘n+1 < LENGTH w’ by decide_tac >> rw[] >> first_x_assum drule >> rw[])
QED

Theorem is_exec_TL_alt:
  is_nfa N ∧ is_exec N (q::qs) (a::w) ⇒ is_exec N qs w
Proof
  rpt strip_tac >> drule is_exec_TL >> rw[] >> res_tac >> fs[]
QED

Theorem is_exec_drop_right[local]:
  is_nfa N ∧ is_exec N (qs ++ [q]) (w ++ [a]) ⇒ is_exec N qs w
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

Theorem is_exec_extend_right[local]:
  is_nfa N ∧ is_exec N qs w ∧
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
  is_nfa N
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

Theorem is_exec_extend_left:
  is_nfa N ∧
  a ∈ N.Sigma ∧
  q1 ∈ N.Q ∧
  q2 ∈ N.delta q1 a ∧
  is_exec N (q2::qs) w ⇒ is_exec N (q1::q2::qs) (a::w)
Proof
  rw [is_exec_def] >> Cases_on ‘n’ >> gvs[GSYM ADD1]
QED

Theorem is_exec_step_left:
  is_nfa N ∧ is_exec N (q1::q2::qs) (a::w)
  ⇒ q2 ∈ N.delta q1 a ∧ is_exec N (q2::qs) w
Proof
  rw[is_exec_def,is_nfa_def]
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

Theorem is_dfa_delta:
  is_dfa N ∧ q ∈ N.Q ∧ a ∈ N.Sigma ⇒ ∃r. N.delta q a = {r}
Proof
  metis_tac [is_dfa_def]
QED

Theorem is_dfa_delta_alt:
  is_dfa N ∧ q ∈ N.Q ∧ a ∈ N.Sigma ∧ q' ∈ N.delta q a
  ⇒ N.delta q a = {q'}
Proof
  rw [] >> drule_all is_dfa_delta >> rw[] >> gvs [is_dfa_def]
QED

Theorem is_dfa_initial:
  is_dfa N ⇒ ∃q_0. N.initial = {q_0}
Proof
  metis_tac [is_dfa_def]
QED

Theorem is_dfa_initial_alt:
  is_dfa N ∧ x ∈ N.initial ⇒ N.initial = {x}
Proof
  rw[] >> imp_res_tac is_dfa_initial >> gvs[]
QED

Theorem is_dfa_initial_unique:
  is_dfa N ∧ x ∈ N.initial ∧ y ∈ N.initial ⇒ x = y
Proof
  rw[] >> imp_res_tac is_dfa_initial >> gvs[]
QED

Theorem is_accepting_exec_length:
 is_nfa N ∧ w ≠ ε ∧ is_accepting_exec N qs w
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

Theorem accepting_exec_min_lengths:
  is_nfa M ∧
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

(* A dfa can consume any string in Sigma* starting from any state *)
Theorem dfa_has_exec:
  is_dfa N ∧ q ∈ N.Q ⇒
  ∀w. EVERY (λa. a ∈ N.Sigma) w ⇒
      ∃qs. is_exec N qs w ∧ HD qs = q
Proof
 strip_tac >>
 ho_match_mp_tac SNOC_INDUCT >> rw[EVERY_SNOC]
  >- (qexists_tac ‘[q]’ >> rw [is_exec_def])
  >- (first_x_assum drule >> rw[] >>
      rename1 ‘a ∈ N.Sigma’ >>
      subgoal ‘∃q. q ∈ N.delta (LAST qs) a’ >-
        (gvs [is_dfa_def] >>
         drule_all is_exec_last_state >>
         metis_tac [IN_INSERT]) >>
      qexists_tac ‘qs ++ [q]’ >> simp [SNOC_APPEND] >>
      imp_res_tac is_exec_nonempty >> simp [HD_APPEND] >>
      metis_tac [dfa_is_nfa,is_exec_extend_right])
QED

Theorem dfa_exec_deterministic:
  is_dfa N ⇒
  ∀w qs1 qs2.
      is_exec N qs1 w ∧
      is_exec N qs2 w ∧ HD qs1 = HD qs2
      ⇒ qs1 = qs2
Proof
  disch_tac >> ho_match_mp_tac SNOC_INDUCT >> rw[]
  >- gvs [is_dfa_def,is_exec_def,LENGTH_EQ_NUM_compute]
  >- (drule is_exec_nonempty >> rev_drule is_exec_nonempty >> rw[] >>
      drule APPEND_FRONT_LAST >> disch_then (SUBST_ALL_TAC o SYM) >>
      rev_drule APPEND_FRONT_LAST >> disch_then (SUBST_ALL_TAC o SYM) >>
      gvs [SNOC_APPEND] >> imp_res_tac dfa_is_nfa >>
      drule_all is_exec_drop_right >>
      rev_drule_all is_exec_drop_right >> ntac 2 disch_tac >>
      conj_asm1_tac
      >- (first_x_assum irule >> simp[] >>
          ‘FRONT qs1 ≠ [] ∧ FRONT qs2 ≠ []’ by
            metis_tac[is_exec_nonempty] >> gvs[])
      >- (gvs [] >> drule is_exec_nonempty >>
          drule_all is_exec_last_state >>
          rename1 ‘w ++ [a]’ >> subgoal ‘a ∈ N.Sigma’ >-
            (rev_drule is_exec_Sigma >> simp[]) >>
          ntac 2 disch_tac >> imp_res_tac dfa_is_nfa >>
          gvs [GSYM is_exec_delta_step] >>
          drule_all is_dfa_delta >> rw[] >> gvs[]))
QED

(*---------------------------------------------------------------------------*)
(* Abstract encode/decode functions for finite states                        *)
(*---------------------------------------------------------------------------*)

Definition encode_def:
  encode s = @f. ∃b. BIJ f s (count b)
End

Definition decode_def:
  decode s = LINV (encode s) s
End

Theorem codec:
  FINITE s ∧ x ∈ s ⇒ decode s (encode s x) = x
Proof
  rw [decode_def,encode_def] >>
  SELECT_ELIM_TAC >> rw[]
   >- (drule FINITE_BIJ_COUNT >> metis_tac [BIJ_SYM]) >>
  irule LINV_DEF >> metis_tac [BIJ_DEF]
QED

Theorem encode_11:
  FINITE s ∧ {x;y} ⊆ s
  ⇒ ((encode s x = encode s y) ⇔ (x = y))
Proof
  rw [SUBSET_DEF,encode_def] >>
  SELECT_ELIM_TAC >> rw[]
  >- (drule FINITE_BIJ_COUNT >> metis_tac [BIJ_SYM]) >>
  metis_tac [BIJ_DEF,INJ_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Instantiation to subsets                                                  *)
(*---------------------------------------------------------------------------*)

Definition encode_subset_def:
  encode_subset N = encode (POW N.Q)
End

Definition decode_subset_def:
  decode_subset N = decode (POW N.Q)
End

Theorem codec_subset:
  is_nfa N ∧ s ⊆ N.Q ⇒ decode_subset N (encode_subset N s) = s
Proof
  rw[encode_subset_def, decode_subset_def] >>
  ‘FINITE (POW N.Q)’ by metis_tac [FINITE_POW,is_nfa_def] >>
  metis_tac [codec,IN_POW,SUBSET_DEF]
QED

Theorem encode_subset_11:
  is_nfa N ∧ {s1;s2} ⊆ POW N.Q
  ⇒ (encode_subset N s1 = encode_subset N s2 ⇔ s1 = s2)
Proof
  rw [encode_subset_def] >>
  ‘FINITE (POW N.Q)’ by metis_tac [FINITE_POW,is_nfa_def] >>
  irule encode_11 >> rw [SUBSET_DEF]
QED

Overload "enc"[local] = “encode_subset N”
Overload "dec"[local] = “decode_subset N”;

(*---------------------------------------------------------------------------*)
(* Subset construction                                                       *)
(*---------------------------------------------------------------------------*)

Definition nfa_to_dfa_def:
  nfa_to_dfa N : 'a nfa =
    <|Q       := {enc s | s | s ⊆ N.Q};
      Sigma   := N.Sigma;
      delta   := λqs a. {enc (BIGUNION{N.delta q a | q | q ∈ dec qs})};
      initial := {enc N.initial};
      final   := {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
    |>
End

Theorem nfa_to_dfa_builtin_simps[local,simp]:
  (nfa_to_dfa N:'a nfa).Sigma = N.Sigma ∧
  (nfa_to_dfa N).initial = {enc N.initial} ∧
  (nfa_to_dfa N).final   = {enc s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅} ∧
  (∀q. q ∈ (nfa_to_dfa N).Q <=> ∃s. q = enc s ∧ s ⊆ N.Q)
Proof
  rw[SF ETA_ss, nfa_to_dfa_def]
QED

Theorem is_dfa_nfa_to_dfa:
  is_nfa N ⇒ is_dfa (nfa_to_dfa N)
Proof
  strip_tac >> imp_res_tac codec_subset >>
  fs[is_nfa_def,is_dfa_def,nfa_to_dfa_def] >> rw[]
  >- (rw [GSPEC_IMAGE, o_DEF] >> irule IMAGE_FINITE >>
      last_x_assum (mp_tac o MATCH_MP FINITE_POW) >>
      PURE_REWRITE_TAC[GSYM IN_POW,SPECIFICATION,ETA_THM] >> metis_tac[])
  >- metis_tac []
  >- (rw [SUBSET_DEF] >> metis_tac[])
  >- (irule_at Any EQ_REFL >> rw[BIGUNION_SUBSET] >>
      first_x_assum irule >> gvs[SUBSET_DEF])
QED

(*---------------------------------------------------------------------------*)
(* Main lemma for the subset construction. The last state in an execution of *)
(* the DFA on input w, when decoded, is equal to the set of states reachable *)
(* by NFA execution on w.                                                    *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_inductive:
  is_nfa (N:'a nfa) ⇒
  ∀w eqs.
   is_exec (nfa_to_dfa N) eqs w ∧ HD eqs = enc N.initial
    ==>
   dec(LAST eqs) = {LAST qs |qs| is_exec N qs w ∧ HD qs ∈ N.initial}
Proof
  strip_tac >>
  imp_res_tac is_dfa_nfa_to_dfa >>
  imp_res_tac dfa_is_nfa >>
  ho_match_mp_tac SNOC_INDUCT >>
  rpt strip_tac >-
    (gvs [is_exec_epsilon] >> pop_keep_tac >>
     dep_rewrite.DEP_REWRITE_TAC [codec_subset,encode_subset_11] >> rw[]
     >- metis_tac [is_nfa_def]
     >- metis_tac [IN_POW]
     >- metis_tac [is_nfa_def,IN_POW]
     >- (rw [EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
         metis_tac [is_nfa_def,SUBSET_DEF])) >>
  rename1 ‘SNOC a w’ >>
  ‘is_exec (nfa_to_dfa N) (FRONT eqs ++ [LAST eqs]) (w ++ [a])’ by
     metis_tac [is_exec_nonempty,APPEND_FRONT_LAST,SNOC_APPEND] >>
  pop_keep_tac >> qpat_forget_tac ‘is_exec _ _ _’ >>
  rw [GSYM $ is_exec_delta_step] >> first_x_assum drule >>
  dep_rewrite.DEP_REWRITE_TAC [HD_FRONT] >> simp[] >>
  conj_tac >- (drule is_exec_nonempty >> rw[]) >> (* Now have IH *)
  ‘a ∈ (nfa_to_dfa N).Sigma ∧ LAST (FRONT eqs) ∈ (nfa_to_dfa N).Q ’ by
     (conj_tac >- simp[nfa_to_dfa_def] >> metis_tac [is_exec_last_state]) >>
  dxrule_all is_dfa_delta_alt >> simp[nfa_to_dfa_def] >>
  disch_then (mp_tac o Q.AP_TERM ‘dec’) >>
  dep_rewrite.DEP_REWRITE_TAC [codec_subset] >> simp[] >> conj_tac >-
    (rw [SUBSET_DEF] >> drule_all is_exec_last_state >>
     rw [nfa_to_dfa_def] >> gvs[] >> qpat_stage_tac ‘q ∈ dec (enc _)’ >>
     dep_rewrite.DEP_REWRITE_TAC [codec_subset] >> simp[] >>
     metis_tac [is_nfa_def,SUBSET_DEF]) >>
  disch_then sym_subst_all_tac >>
  disch_then subst_all_tac >> qpat_forget_tac ‘is_exec _ _ _’ >>
  rw [EXTENSION] >> eq_tac >> rpt strip_tac
  >- (qexists_tac ‘SNOC x qs’ >> simp[SNOC_APPEND] >>
      reverse conj_tac >- metis_tac [HD_APPEND,is_exec_nonempty] >>
      rw [GSYM $ is_exec_delta_step] >> metis_tac[])
  >- (simp [PULL_EXISTS] >> drule_all is_exec_nonempty_as_snoc >> rw[] >>
      gvs [SNOC_APPEND,GSYM $ is_exec_delta_step] >>
      metis_tac[is_exec_nonempty,HD_APPEND])
QED

Theorem nfa_exec_to_dfa_exec:
  is_nfa (N:'a nfa) ⇒
  ∀w qs. is_exec N qs w ∧ HD qs ∈ N.initial ⇒
         ∃eqs. is_exec (nfa_to_dfa N) eqs w ∧
               HD eqs = enc N.initial
Proof
  disch_tac >>
  imp_res_tac is_dfa_nfa_to_dfa >> imp_res_tac dfa_is_nfa >>
  ho_match_mp_tac SNOC_INDUCT >> rw[] >-
    (qexists_tac ‘[enc N.initial]’ >>
     simp [is_exec_def] >> metis_tac [is_nfa_def]) >>
  drule_all is_exec_nonempty_as_snoc >> rw[] >> gvs [SNOC_APPEND] >>
  qpat_stage_tac ‘is_exec _ _ _’ >> rw [GSYM $ is_exec_delta_step] >>
  rename1 ‘a ∈ N.Sigma’ >> imp_res_tac is_exec_nonempty >> gvs [HD_APPEND] >>
  first_x_assum drule_all >>  rw[] >>
  drule is_exec_nonempty >> disch_tac >>
  subgoal ‘∃eq. (nfa_to_dfa N).delta (LAST eqs) a = {eq}’ >-
    (irule is_dfa_delta >> simp [nfa_to_dfa_def] >>
     drule_all is_exec_last_state >> simp [nfa_to_dfa_def]) >>
  qexists_tac ‘eqs ++ [eq]’ >> reverse conj_tac >- simp [HD_APPEND] >>
  rw [GSYM $ is_exec_delta_step]
QED

(*---------------------------------------------------------------------------*)
(* Language of the constructed DFA is the same as that of the original NFA.  *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_correct:
  is_nfa N ⇒ ∀w. w ∈ nfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
  strip_tac >>
  imp_res_tac is_dfa_nfa_to_dfa >>
  imp_res_tac dfa_is_nfa >>
  rw [in_nfa_lang_iff_accepting_exec,is_accepting_exec_def,EQ_IMP_THM]
  >- (rename1 ‘LAST eqs = enc s’ >> drule_all nfa_to_dfa_inductive >> rw[] >>
      pop_keep_tac >> dep_rewrite.DEP_REWRITE_TAC [codec_subset] >> simp[] >>
      ‘∃q. q ∈ s ∧ q ∈ N.final’ by (gvs[EXTENSION] >> metis_tac[]) >>
      rw[EXTENSION] >> metis_tac[])
  >- (drule_all nfa_exec_to_dfa_exec >> rw[] >>
      drule_all nfa_to_dfa_inductive >> strip_tac >>
      ntac 2 (first_assum (irule_at Any)) >>
      drule_all is_exec_last_state >> rw [nfa_to_dfa_def] >> rw[] >> gvs[] >>
      irule_at Any EQ_REFL >> simp [] >>
      qpat_stage_tac ‘dec (enc _) = _’ >>
      dep_rewrite.DEP_REWRITE_TAC [codec_subset] >> simp[] >>
      disch_then (assume_tac o sym) >> asm_rewrite_tac [] >>
      rw[EXTENSION] >> metis_tac[])
QED

(*---------------------------------------------------------------------------*)
(* The NFA- and DFA-recognizable languages are the same                      *)
(*---------------------------------------------------------------------------*)

Theorem NFA_LANGS_EQ_DFA_LANGS:
  {nfa_lang N | is_nfa N} = {nfa_lang N | is_dfa N}
Proof
  rw [EXTENSION,EQ_IMP_THM]
  >- metis_tac [is_dfa_nfa_to_dfa,nfa_to_dfa_correct]
  >- metis_tac[is_dfa_def]
QED


(*===========================================================================*)
(* Further machine constructions and closure properties                      *)
(*===========================================================================*)

Definition dfa_compl_def:
  dfa_compl N =
    <|Q     := N.Q;
      Sigma := N.Sigma;
      delta := N.delta;
      initial := N.initial;
      final   := (N.Q DIFF N.final)
    |>
End

(*---------------------------------------------------------------------------*)
(* Abstract encode/decode functions for pairs of states.                     *)
(*---------------------------------------------------------------------------*)

Definition encode_pair_def:
  encode_pair (N1:'a nfa) (N2:'a nfa) = encode (N1.Q × N2.Q)
End

Definition decode_pair_def:
  decode_pair (N1:'a nfa) (N2:'a nfa) = decode (N1.Q × N2.Q)
End

Theorem codec_pair:
  is_nfa N1 ∧ is_nfa N2 ∧ p ∈ N1.Q × N2.Q
  ⇒ decode_pair N1 N2 (encode_pair N1 N2 p) = p
Proof
  rw[encode_pair_def, decode_pair_def] >>
  ‘FINITE (N1.Q × N2.Q)’ by metis_tac [FINITE_CROSS,is_nfa_def] >>
  irule codec >> simp []
QED

Theorem encode_pair_11:
  is_nfa N1 ∧ is_nfa N2 ∧ {p1;p2} ⊆ N1.Q × N2.Q
  ⇒ (encode_pair N1 N2 p1 = encode_pair N1 N2 p2 ⇔ p1 = p2)
Proof
  rw [encode_pair_def] >>
  ‘FINITE (N1.Q × N2.Q)’ by metis_tac [FINITE_CROSS,is_nfa_def] >>
  irule encode_11 >> rw [SUBSET_DEF]
QED

Overload "enc"[local] = “encode_pair N1 N2”
Overload "dec"[local] = “decode_pair N1 N2”;

Definition dfa_inter_def:
  dfa_inter (N1:'a nfa) (N2:'a nfa) =
    <|Q     := {enc (q1,q2) | q1 ∈ N1.Q ∧ q2 ∈ N2.Q};
      Sigma := N1.Sigma ∩ N2.Sigma;
      delta := λq a. {enc (q1,q2) | q1 ∈ N1.delta (FST (dec q)) a ∧
                                    q2 ∈ N2.delta (SND (dec q)) a};
      initial := {enc (q1,q2) | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      final   := {enc (q1,r2) | q1 ∈ N1.final ∧ r2 ∈ N2.final}
    |>
End

Definition dfa_union_def:
  dfa_union (N1:'a nfa) (N2:'a nfa) =
    <|Q  := {enc (q1,q2) | q1 ∈ N1.Q ∧ q2 ∈ N2.Q };
      Sigma := N1.Sigma ∩ N2.Sigma;
      delta := λq a. {enc (q1,q2) | q1 ∈ N1.delta (FST (dec q)) a ∧
                                    q2 ∈ N2.delta (SND (dec q)) a};
      initial := {enc (q1,q2) | q1 ∈ N1.initial ∧ q2 ∈ N2.initial};
      final   := {enc (q1,q2) | (q1 ∈ N1.final ∧ q2 ∈ N2.Q) ∨
                                (q1 ∈ N1.Q ∧ q2 ∈ N2.final)};
    |>
End

Definition dfa_rev_def:
  dfa_rev N =
    <|Q     := N.Q;
      Sigma := N.Sigma;
      delta := λq a. {p | p ∈ N.Q ∧ q ∈ N.delta p a};
      initial := N.final;
      final   := N.initial;
    |>
End

(*---------------------------------------------------------------------------*)
(* Wellformedness of constructions                                           *)
(*---------------------------------------------------------------------------*)

Theorem wf_dfa_compl:
  is_nfa N ⇒ is_nfa (dfa_compl N)
Proof
  rw[is_nfa_def, dfa_compl_def]
QED

Theorem dfa_inter_builtin_simps[local,simp]:
  (dfa_inter (N1:'a nfa) N2).Sigma = N1.Sigma ∩ N2.Sigma ∧
  (dfa_inter N1 N2).Q =
       {enc (q1,q2) | (q1,q2) | q1 ∈ N1.Q ∧ q2 ∈ N2.Q} ∧
  (dfa_inter N1 N2).initial =
       {enc (q1,q2) | (q1,q2) | q1 ∈ N1.initial ∧ q2 ∈ N2.initial} ∧
  (dfa_inter N1 N2).final =
       {enc (q1,q2) | (q1,q2) | q1 ∈ N1.final ∧ q2 ∈ N2.final}
Proof
  rw[dfa_inter_def]
QED

Theorem wf_dfa_inter:
  is_nfa (N1:'a nfa) ∧ is_nfa N2 ⇒ is_nfa (dfa_inter N1 N2)
Proof
  rw [is_nfa_def,dfa_inter_def,SUBSET_DEF]
  >- (rw [GSPEC_IMAGE, o_DEF,pairTheory.LAMBDA_PROD] >>
      irule IMAGE_FINITE >> irule SUBSET_FINITE >>
      qexists ‘N1.Q CROSS N2.Q’ >> rw[] >>
      rw [SUBSET_DEF,CROSS_DEF,pairTheory.LAMBDA_PROD,pairTheory.FORALL_PROD])
  >- metis_tac[]
  >- metis_tac[]
  >- (irule_at Any EQ_REFL >> ntac 2 pop_keep_tac >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      metis_tac[is_nfa_def,SUBSET_DEF])
QED

Theorem dfa_union_builtin_simps[local,simp]:
  (dfa_union (N1:'a nfa) N2).Sigma = N1.Sigma ∩ N2.Sigma ∧
  (dfa_union N1 N2).Q =
       {enc (q1,q2) | (q1,q2) | q1 ∈ N1.Q ∧ q2 ∈ N2.Q} ∧
  (dfa_union N1 N2).initial =
       {enc (q1,q2) | (q1,q2) | q1 ∈ N1.initial ∧ q2 ∈ N2.initial} ∧
  (dfa_union N1 N2).final =
       {enc (q1,q2) | (q1,q2) |
        q1 ∈ N1.final ∧ q2 ∈ N2.Q ∨ q1 ∈ N1.Q ∧ q2 ∈ N2.final}
Proof
  rw[dfa_union_def]
QED

Theorem wf_dfa_union:
  is_nfa N1 ∧ is_nfa N2 ⇒ is_nfa (dfa_union N1 N2)
Proof
  rw [is_nfa_def,dfa_union_def,SUBSET_DEF]
  >- (rw [GSPEC_IMAGE, o_DEF,pairTheory.LAMBDA_PROD] >>
      irule IMAGE_FINITE >> irule SUBSET_FINITE >>
      qexists ‘N1.Q CROSS N2.Q’ >> rw[] >>
      rw [SUBSET_DEF,CROSS_DEF,pairTheory.LAMBDA_PROD,pairTheory.FORALL_PROD])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (irule_at Any EQ_REFL >> ntac 2 pop_keep_tac >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      metis_tac[is_nfa_def,SUBSET_DEF])
QED

Theorem wf_dfa_rev:
  is_nfa N ⇒ is_nfa (dfa_rev N)
Proof
  strip_tac >>
  reverse (rw [is_nfa_def,dfa_rev_def]) >-
     gvs [is_nfa_def,SUBSET_DEF] >>
  metis_tac [is_nfa_def]
QED

Theorem is_dfa_compl:
  is_dfa N ⇒ is_dfa (dfa_compl N)
Proof
  rw [is_dfa_def]
  >- metis_tac [wf_dfa_compl]
  >- simp[dfa_compl_def]
  >- fs[dfa_compl_def]
QED

Theorem is_dfa_inter:
  is_dfa N1 ∧ is_dfa N2 ⇒ is_dfa (dfa_inter N1 N2)
Proof
  rw [is_dfa_def]
  >- metis_tac [wf_dfa_inter]
  >- (‘∃q1 q2. N1.initial = {q1} ∧ N2.initial = {q2}’ by
         metis_tac [is_dfa_def] >>
      qexists_tac ‘enc (q1,q2)’ >> simp [EXTENSION])
  >- (rw [dfa_inter_def,EXTENSION,PULL_EXISTS] >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      ‘∃qa qb. {qa} = N1.delta q1 a ∧ {qb} = N2.delta q2 a’ by
          metis_tac[] >>
      qexists_tac ‘enc (qa,qb)’ >> rw[EQ_IMP_THM]
      >- (dep_rewrite.DEP_REWRITE_TAC [encode_pair_11] >> simp[] >>
          RULE_ASSUM_TAC GSYM >> rfs[] >> gvs[] >>
          metis_tac [EXTENSION,IN_INSERT,is_nfa_def,SUBSET_DEF])
     >- metis_tac [EXTENSION,IN_INSERT,is_nfa_def,SUBSET_DEF])
QED

Theorem is_dfa_union:
  is_dfa N1 ∧ is_dfa N2 ⇒ is_dfa (dfa_union N1 N2)
Proof
  rw [is_dfa_def]
  >- metis_tac [wf_dfa_union]
  >- (rw [dfa_union_def,EXTENSION] >> metis_tac[])
  >- (ntac 2 pop_keep_tac >>
      rw [dfa_union_def,EXTENSION,PULL_EXISTS] >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      ‘∃qa qb. {qa} = N1.delta q1 a ∧ {qb} = N2.delta q2 a’ by
          metis_tac[] >>
      qexists_tac ‘enc (qa,qb)’ >> rw[EQ_IMP_THM]
      >- (dep_rewrite.DEP_REWRITE_TAC [encode_pair_11] >> simp[] >>
          RULE_ASSUM_TAC GSYM >> rfs[] >> gvs[] >>
          metis_tac [EXTENSION,IN_INSERT,is_nfa_def,SUBSET_DEF])
      >- metis_tac [EXTENSION,IN_INSERT,is_nfa_def,SUBSET_DEF])
QED

Theorem dfa_union_exec_split:
  N1.Sigma = N2.Sigma ∧
  is_dfa N1 ∧ is_dfa N2 ∧
  is_exec (dfa_union N1 N2:'a nfa) qs w
  ⇒
  is_exec N1 (MAP (FST o dec) qs) w ∧
  is_exec N2 (MAP (SND o dec) qs) w
Proof
  strip_tac >>
  ‘is_dfa (dfa_union N1 N2)’ by
     metis_tac [is_dfa_union] >> conj_tac >>
  (rw[is_exec_def]
  >- (drule is_exec_Sigma >> simp[])
  >- (drule is_exec_length >> simp[])
  >- (drule is_exec_hd_state >>
      drule is_exec_nonempty >> rw[HD_MAP] >> rw[] >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      metis_tac [dfa_is_nfa])
  >- (drule is_exec_delta >> disch_tac >>
      first_x_assum drule >> rw [dfa_union_def,o_DEF] >>
      dep_rewrite.DEP_REWRITE_TAC [EL_MAP] >> simp[] >>
      drule is_exec_length >> rw[] >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      ‘is_nfa (dfa_union N1 N2)’ by metis_tac [dfa_is_nfa] >>
      drule_all is_exec_states >> simp [dfa_inter_def,EVERY_EL] >>
      ‘n < LENGTH w + 1’ by decide_tac >>
      disch_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      qpat_stage_tac ‘q1 ∈ N1.delta _ _’ >>
      qpat_stage_tac ‘q2 ∈ N2.delta _ _’ >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      drule is_exec_Sigma >> simp[EVERY_EL] >> disch_tac >>
      first_x_assum drule >> metis_tac [is_nfa_def,SUBSET_DEF,dfa_is_nfa])
  )
QED

Theorem dfa_union_exec_join:
  N1.Sigma = N2.Sigma ∧
  is_dfa N1 ∧ is_dfa N2 ∧
  is_exec N1 qs1 w ∧
  is_exec N2 qs2 w
  ⇒
  is_exec (dfa_union N1 N2:'a nfa)
          (MAP2 (λa b. enc (a,b)) qs1 qs2) w
Proof
  rw[] >> rw [is_exec_def, dfa_union_def]
  >- metis_tac [is_exec_Sigma]
  >- metis_tac [is_exec_length, MIN_IDEM]
  >- (drule is_exec_hd_state >> rev_drule is_exec_hd_state >> rw[] >>
      qexists_tac ‘HD qs1’ >> qexists_tac ‘HD qs2’ >> rw[] >>
      dep_rewrite.DEP_REWRITE_TAC [HD_MAP2] >> simp[] >>
      metis_tac [is_exec_nonempty])
  >- (drule is_exec_delta >> rev_drule is_exec_delta >> rw[] >>
      res_tac >>
      qexists_tac ‘EL (n+1) qs1’ >> qexists_tac ‘EL (n+1) qs2’ >>
      rw[] >-
        (dep_rewrite.DEP_REWRITE_TAC [EL_MAP2] >> simp[] >>
         drule is_exec_length >> rev_drule is_exec_length >>
         decide_tac) >>
     (dep_rewrite.DEP_REWRITE_TAC [EL_MAP2] >> simp[] >>
      dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
      ‘is_nfa N1 ∧ is_nfa N2’ by metis_tac [dfa_is_nfa] >>
      simp[] >> reverse conj_tac
      >- (drule is_exec_length >> rev_drule is_exec_length >> decide_tac) >>
      drule_all is_exec_states >> rev_drule_all is_exec_states >>
      rw [EVERY_EL]
      >- (first_x_assum irule >> rev_drule is_exec_length >> decide_tac)
      >- (first_x_assum irule >> drule is_exec_length >> decide_tac)))
QED

(*---------------------------------------------------------------------------*)
(* Correctness of constructions                                              *)
(*---------------------------------------------------------------------------*)

Theorem dfa_compl_exec:
  is_nfa N ⇒ (is_exec (dfa_compl N) qs w ⇔ is_exec N qs w)
Proof
  strip_tac >> rw [is_exec_def,dfa_compl_def] >>
  metis_tac [is_exec_Sigma,is_exec_length,is_exec_hd_state,is_exec_delta]
QED

Theorem dfa_compl_correct :
  is_dfa N ⇒
  ∀w. w ∈ nfa_lang (dfa_compl N) <=>
      w ∈ (KSTAR {[a] | a ∈ N.Sigma} DIFF (nfa_lang N))
Proof
  strip_tac >> EVERY (map imp_res_tac [dfa_is_nfa, wf_dfa_compl]) >>
  simp [in_nfa_lang_iff_accepting_exec] >> rw [EQ_IMP_THM]
  >- metis_tac [is_exec_Sigma,is_accepting_exec_def,dfa_compl_exec]
  >- (strip_tac >> imp_res_tac is_accepting_exec_final >>
      gvs [is_accepting_exec_def,dfa_compl_exec] >>
      subgoal ‘qs = qs'’ >-
         (irule dfa_exec_deterministic >> reverse conj_tac >- metis_tac[] >>
          irule is_dfa_initial_unique >> goal_assum drule >> simp[] >>
          qpat_stage_tac ‘HD qs ∈ _’ >> rw[dfa_compl_def]) >>
      gvs[dfa_compl_def])
  >- (imp_res_tac is_dfa_initial >>
      ‘q_0 ∈ N.Q’ by metis_tac[is_nfa_def,SUBSET_DEF,IN_INSERT] >>
      drule_all dfa_has_exec >>
      rw[is_accepting_exec_def,dfa_compl_exec] >>
      goal_assum drule >> simp [dfa_compl_def] >>
      gvs [is_accepting_exec_def] >>
      metis_tac [is_exec_last_state])
QED

Theorem dfa_inter_correct :
  is_dfa N1 ∧ is_dfa N2 ∧ N1.Sigma = N2.Sigma
  ⇒
  ∀w. w ∈ nfa_lang (dfa_inter N1 N2) <=>
      w ∈ nfa_lang N1 ∧ w ∈ nfa_lang N2
Proof
  strip_tac >>
  ‘is_dfa (dfa_inter N1 N2)’ by
     metis_tac [is_dfa_inter] >>
  imp_res_tac dfa_is_nfa >>
  rw [in_nfa_lang_iff_accepting_exec,is_accepting_exec_def] >>
  reverse eq_tac
  >- (rw [] >> drule is_exec_nonempty >> rw [] >>
      qexists_tac ‘MAP2 (λa b. enc (a,b)) qs qs'’ >> rw[]
      >- (rw [is_exec_def]
          >- (drule is_exec_Sigma >> simp[dfa_inter_def])
          >- metis_tac [is_exec_length,MIN_IDEM]
          >- (drule is_exec_hd_state >> rev_drule is_exec_hd_state >>
              rev_drule is_exec_nonempty >> rw[] >>
              rw [dfa_inter_def] >> metis_tac[])
          >- (drule_all is_exec_delta >>
              rev_drule_all is_exec_delta >>
              rw [dfa_inter_def] >>
              qexists_tac ‘EL (n+1) qs’ >> qexists_tac ‘EL (n+1) qs'’ >>
              dep_rewrite.DEP_REWRITE_TAC [EL_MAP2] >>
              drule is_exec_length >> rev_drule is_exec_length >> simp[] >>
              ntac 2 disch_tac >>
              dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
              drule_all is_exec_states >> rev_drule_all is_exec_states >>
              drule is_exec_length >> rev_drule is_exec_length >>
              rw [EVERY_EL]))
      >- (drule is_exec_hd_state >> rev_drule is_exec_hd_state >>
          rev_drule is_exec_nonempty >> rw[] >>
          rw [dfa_inter_def] >> metis_tac[])
      >- (dep_rewrite.DEP_REWRITE_TAC [LAST_MAP2] >> simp[] >>
          rev_drule is_exec_nonempty >>
          drule is_exec_length >> rev_drule is_exec_length >> rw[] >>
          rw [dfa_inter_def] >> metis_tac[])) >>
  strip_tac >>
  conj_tac THENL
   [qexists_tac ‘MAP (FST o dec) qs’,
    qexists_tac ‘MAP (SND o dec) qs’]
  >>
  (rw[o_DEF] >> drule is_exec_nonempty >> rw[]
   >- (rw [is_exec_def]
       >- (drule is_exec_Sigma >> simp[dfa_inter_def])
       >- (drule is_exec_length >> simp[])
       >- (drule is_exec_hd_state >> rw[dfa_inter_def] >>
           rw[] >> dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[])
       >- (drule_all is_exec_delta >> rw [dfa_inter_def] >>
           imp_res_tac is_exec_length >>
           ‘n+1 < LENGTH qs’ by decide_tac >> rw [EL_MAP] >>
           dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
           rename1 ‘EL (n+1) qs = enc (r1,r2)’ >>
           drule_all is_exec_states >> simp [dfa_inter_def,EVERY_EL] >>
           ‘n < LENGTH w + 1’ by decide_tac >>
           disch_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
           qpat_stage_tac ‘r1 ∈ N1.delta _ _’ >>
           qpat_stage_tac ‘r2 ∈ N2.delta _ _’ >>
           dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
           drule is_exec_Sigma >> simp[EVERY_EL] >> disch_tac >>
           first_x_assum drule >> simp [dfa_inter_def] >>
           metis_tac [is_nfa_def,SUBSET_DEF]))
   >- (dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
       metis_tac [is_nfa_def, SUBSET_DEF])
   >- (dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
       metis_tac [is_nfa_def, SUBSET_DEF]))
QED

Theorem dfa_union_correct :
  is_dfa N1 ∧ is_dfa N2 ∧ N1.Sigma = N2.Sigma
  ⇒
  ∀w. w ∈ nfa_lang (dfa_union N1 N2) <=>
      w ∈ nfa_lang N1 ∨ w ∈ nfa_lang N2
Proof
  strip_tac >>
  ‘is_dfa (dfa_union N1 N2)’ by
     metis_tac [is_dfa_union] >>
  imp_res_tac dfa_is_nfa >>
  rw [in_nfa_lang_iff_accepting_exec,is_accepting_exec_def] >>
  eq_tac >-
    (rw [] THENL
     [disj1_tac >> qexists_tac ‘MAP (FST o dec) qs’,
      disj2_tac >> qexists_tac ‘MAP (SND o dec) qs’] >>
     drule_all dfa_union_exec_split >>
     (rw[]
      >- (drule is_exec_nonempty >> rw[] >>
          dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
          metis_tac [is_nfa_def,SUBSET_DEF])
      >- (drule is_exec_nonempty >> rw[] >>
          dep_rewrite.DEP_REWRITE_TAC [codec_pair] >> simp[] >>
          metis_tac [is_nfa_def,SUBSET_DEF])))
   >> rw[]
   >- (rename1 ‘is_exec N1 qs1 w’ >>
       drule is_exec_Sigma >> disch_tac >>
       ‘EVERY (λa. a ∈ N2.Sigma) w’ by metis_tac[is_exec_Sigma] >>
       ‘∃q_0. N2.initial = {q_0}’ by metis_tac [is_dfa_initial] >>
       ‘q_0 ∈ N2.Q’ by
          metis_tac [is_nfa_def,is_dfa_def,SUBSET_DEF,IN_INSERT] >>
       drule_all dfa_has_exec >> rw [] >>
       rename1 ‘is_exec N2 qs2 w’ >>
       drule_all dfa_union_exec_join >>
       disch_then (irule_at Any) >>
       first_assum (irule_at Any) >> rw[] >>
       CONV_TAC (RESORT_EXISTS_CONV rev) >>
       qexists_tac ‘LAST qs1’ >> simp[] >>
       qexists_tac ‘LAST qs2’ >> simp[] >>
       dep_rewrite.DEP_REWRITE_TAC [HD_MAP2] >> simp[] >>
       dep_rewrite.DEP_REWRITE_TAC [LAST_MAP2] >> simp[] >>
       conj_tac >- metis_tac [is_exec_nonempty,is_exec_length] >>
       conj_tac >- metis_tac [is_exec_nonempty] >>
       disj1_tac >>
       ‘EVERY (λq. q ∈ N2.Q) qs2’ by metis_tac[is_exec_states] >>
       ‘qs2 ≠ []’ by metis_tac[is_exec_nonempty] >>
       drule_all EVERY_LAST >> simp[])
   >- (rename1 ‘is_exec N2 qs2 w’ >>
       imp_res_tac is_exec_Sigma >>
       ‘EVERY (λa. a ∈ N1.Sigma) w’ by metis_tac[is_exec_Sigma] >>
       ‘∃q_0. N1.initial = {q_0}’ by metis_tac [is_dfa_initial] >>
       ‘q_0 ∈ N1.Q’ by
          metis_tac [is_nfa_def,is_dfa_def,SUBSET_DEF,IN_INSERT] >>
       ‘∃qs1. is_exec N1 qs1 w ∧ HD qs1 = q_0’ by
          metis_tac[dfa_has_exec] >>
       drule_all dfa_union_exec_join >>
       disch_then (irule_at Any) >> rw [] >>
       first_assum (irule_at Any) >> CONV_TAC (RESORT_EXISTS_CONV rev) >>
       qexists_tac ‘LAST qs1’ >> simp[] >>
       qexists_tac ‘LAST qs2’ >> simp[] >>
       dep_rewrite.DEP_REWRITE_TAC [HD_MAP2] >> simp[] >>
       dep_rewrite.DEP_REWRITE_TAC [LAST_MAP2] >> simp[] >>
       conj_tac >- metis_tac [is_exec_nonempty,is_exec_length] >>
       conj_tac >- metis_tac [is_exec_nonempty] >>
       disj2_tac >>
       ‘EVERY (λq. q ∈ N1.Q) qs1’ by metis_tac[is_exec_states] >>
       ‘qs1 ≠ []’ by metis_tac[is_exec_nonempty] >>
       drule_all EVERY_LAST >> simp[])
QED

Theorem dfa_rev_execA:
  is_nfa N ∧ is_exec N qs w
  ⇒ is_exec (dfa_rev N) (REVERSE qs) (REVERSE w)
Proof
  strip_tac >> imp_res_tac wf_dfa_rev >> rw[is_exec_def]
  >- (simp [dfa_rev_def] >> metis_tac [is_exec_Sigma])
  >- metis_tac [is_exec_length]
  >- (imp_res_tac is_exec_nonempty >> simp [HD_REVERSE] >>
      simp [dfa_rev_def] >> imp_res_tac is_exec_last_state)
  >- (rw [dfa_rev_def] >-
        (rev_drule_all is_exec_states >>
         simp_tac bool_ss [Once $ GSYM ALL_EL_REVERSE] >>
         ‘n+1 < LENGTH qs’ by (imp_res_tac is_exec_length >> decide_tac) >>
         rw_tac bool_ss [EVERY_EL] >> first_x_assum irule >> rw[]) >>
      dep_rewrite.DEP_REWRITE_TAC [EL_REVERSE] >> simp[] >>
      drule is_exec_length >> rw[] >>
      ‘PRE (LENGTH w + 1 - n) = PRE (LENGTH w − n) + 1’ by decide_tac >>
      pop_subst_tac >> irule is_exec_delta >> simp[])
QED

Theorem dfa_rev_execB:
  is_nfa N ∧ is_exec (dfa_rev N) qs w
  ⇒ is_exec N (REVERSE qs) (REVERSE w)
Proof
  strip_tac >> imp_res_tac wf_dfa_rev >> rw[is_exec_def]
  >- (drule is_exec_Sigma >> simp [dfa_rev_def])
  >- metis_tac [is_exec_length]
  >- (imp_res_tac is_exec_nonempty >> simp [HD_REVERSE] >>
      drule_all is_exec_last_state >> simp [dfa_rev_def])
  >- (dep_rewrite.DEP_REWRITE_TAC [EL_REVERSE] >> simp[] >>
      drule is_exec_length >> rw[] >>
      drule is_exec_delta >> rw [dfa_rev_def] >>
      ‘PRE (LENGTH w + 1 - n) = PRE (LENGTH w − n) + 1’ by decide_tac >>
      pop_subst_tac >> first_x_assum (irule o snd_conj) >>
      imp_res_tac is_exec_length >> decide_tac)
QED

(*---------------------------------------------------------------------------*)
(* A regular language L is a subset of A*, where A is a finite alphabet. L   *)
(* is defined by the strings accepted by a given NFA.                        *)
(*---------------------------------------------------------------------------*)

Definition REGULAR_def:
  REGULAR = {(L,A) | ∃N. N.Sigma = A ∧ is_nfa N ∧ L = nfa_lang N}
End

Theorem IN_REGULAR_AS_NFA:
  (L,A) ∈ REGULAR ⇔ ∃N. N.Sigma = A ∧ is_nfa N ∧ L = nfa_lang N
Proof
 rw [REGULAR_def,pairTheory.LAMBDA_PROD]
QED

Theorem IN_REGULAR_AS_DFA:
  (L,A) ∈ REGULAR ⇔ ∃M. M.Sigma = A ∧ is_dfa M ∧ L = nfa_lang M
Proof
  rw [IN_REGULAR_AS_NFA,EQ_IMP_THM]
  >- (qexists_tac ‘nfa_to_dfa N’ >> rw[is_dfa_nfa_to_dfa] >>
      metis_tac [nfa_to_dfa_correct,EXTENSION])
  >- (fs [is_dfa_def] >> metis_tac[])
QED

Theorem REGULAR_BOUNDED:
  (L,A) ∈ REGULAR ⇒ L ⊆ KSTAR {[a] | a ∈ A}
Proof
  rw [IN_REGULAR_AS_NFA,SUBSET_DEF] >>
  fs [in_nfa_lang,is_nfa_def]
QED

Theorem REGULAR_SIGMA_FINITE:
  (L,A) ∈ REGULAR ⇒ FINITE A
Proof
  rw [IN_REGULAR_AS_NFA,SUBSET_DEF] >> metis_tac [is_nfa_def]
QED

Theorem REGULAR_IS_FORMAL_LANG:
  (L,A) ∈ REGULAR ⇒ IS_FORMAL_LANG(L,A)
Proof
  metis_tac [IS_FORMAL_LANG_def,REGULAR_BOUNDED,REGULAR_SIGMA_FINITE]
QED

(*---------------------------------------------------------------------------*)
(* Transformation that removes symbols from the alphabet of an NFA           *)
(*---------------------------------------------------------------------------*)

Definition nfa_Sigma_extend_def:
  nfa_Sigma_extend N B =
    N with
     <| Sigma := N.Sigma ∪ B;
        delta := λq a. if a ∈ (B DIFF N.Sigma) then {} else N.delta q a |>
End

Theorem is_nfa_Sigma_extend:
  is_nfa N ∧ FINITE A ⇒ is_nfa (nfa_Sigma_extend N A)
Proof
  rw [is_nfa_def,nfa_Sigma_extend_def] >> rw [] >> metis_tac []
QED

Theorem is_exec_nfa_Sigma_extendA[local]:
  is_nfa N ∧ FINITE A ∧ is_exec N qs w
  ⇒ is_exec (nfa_Sigma_extend N A) qs w
Proof
  rw [] >> drule_all is_nfa_Sigma_extend >> disch_tac >>
  rw [is_exec_def]
  >- (rw [nfa_Sigma_extend_def] >>
      drule is_exec_Sigma >> simp [EVERY_DISJ_LEFT])
  >- metis_tac [is_exec_length]
  >- (drule is_exec_hd_state >> rw [nfa_Sigma_extend_def])
  >- (drule is_exec_delta >> rw [nfa_Sigma_extend_def] >>
      goal_assum drule >> drule is_exec_Sigma >> rw [EVERY_EL] >>
      metis_tac[])
QED

Theorem Sigma_extend_word_contents[local]:
  is_nfa N ∧ is_exec (nfa_Sigma_extend N A) qs w
  ⇒ EVERY (λa. a ∈ N.Sigma) w
Proof
  rw [EVERY_EL] >> drule_all is_exec_delta >>
  rw [nfa_Sigma_extend_def] >> gvs [] >>
  drule is_exec_Sigma >>
  rw [EVERY_EL,nfa_Sigma_extend_def] >> metis_tac[]
QED

Theorem is_exec_nfa_Sigma_extendB[local]:
  is_nfa N ∧ FINITE A ∧ is_exec (nfa_Sigma_extend N A) qs w
  ⇒ is_exec N qs w
Proof
  rw [] >> drule_all is_nfa_Sigma_extend >> disch_tac >>
  rw [is_exec_def]
  >- (drule is_exec_Sigma >> rw [nfa_Sigma_extend_def] >>
      metis_tac [Sigma_extend_word_contents])
  >- metis_tac [is_exec_length]
  >- (drule is_exec_hd_state >> rw [nfa_Sigma_extend_def])
  >- (drule is_exec_delta >> rw [nfa_Sigma_extend_def] >>
      first_x_assum drule >> rw[])
QED

Theorem REGULAR_CLOSED_UNDER_ALPHABET_EXTENSION:
  (L,A) ∈ REGULAR ∧ FINITE B ⇒ (L,A ∪ B) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_NFA] >>
  qexists_tac ‘nfa_Sigma_extend N B’ >> rw []
  >- rw[nfa_Sigma_extend_def]
  >- metis_tac [is_nfa_Sigma_extend] >>
  drule_all is_nfa_Sigma_extend >> disch_tac >>
  simp [EXTENSION,in_nfa_lang_iff_accepting_exec,is_accepting_exec_def] >>
  rw [EQ_IMP_THM]
  >- (irule_at Any is_exec_nfa_Sigma_extendA >>
      ntac 3 (goal_assum drule) >>
      simp [nfa_Sigma_extend_def])
  >- (irule_at Any is_exec_nfa_Sigma_extendB >>
      ntac 3 (goal_assum drule) >>
      ntac 2 pop_keep_tac >>
      rw [nfa_Sigma_extend_def])
QED

Theorem EMPTYSET_IN_REGULAR:
  FINITE A ⇒ ({},A) ∈ REGULAR
Proof
  strip_tac >>
  ‘A = ∅ ∪ A’ by simp [] >> pop_subst_tac >>
  irule REGULAR_CLOSED_UNDER_ALPHABET_EXTENSION >>
  gvs [IN_REGULAR_AS_NFA] >>
  qexists_tac
    ‘<| Q := {}; Sigma := {};
        initial := {}; final := {};
        delta := λq a. {} |>’ >>
  rw [is_nfa_def,EXTENSION,in_nfa_lang]
QED

Theorem EPSILONSET_IN_REGULAR:
  FINITE A ⇒ ({ε},A) ∈ REGULAR
Proof
  strip_tac >>
  ‘A = ∅ ∪ A’ by simp [] >> pop_subst_tac >>
  irule REGULAR_CLOSED_UNDER_ALPHABET_EXTENSION >>
  gvs [IN_REGULAR_AS_NFA] >>
  qexists_tac
    ‘<| Q := {0}; Sigma := {};
        initial := {0}; final := {0};
        delta := λq a. {} |>’ >>
  rw [is_nfa_def,EXTENSION,in_nfa_lang,EQ_IMP_THM] >>
  qexists_tac ‘[0]’ >> rw[]
QED

Theorem REGULAR_CLOSED_UNDER_COMPL:
  (L,A) ∈ REGULAR ⇒ (KSTAR {[a] | a ∈ A} DIFF L, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >>
  qexists_tac ‘dfa_compl M’ >> rw[]
  >- simp[dfa_compl_def]
  >- metis_tac [is_dfa_compl]
  >- (drule dfa_compl_correct >> simp [EXTENSION])
QED

Theorem REGULAR_CLOSED_UNDER_UNION:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 ∪ L2, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >>
  rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘dfa_union M1 M2’ >> rw[]
  >- metis_tac [is_dfa_union]
  >- (drule_all dfa_union_correct >> simp [EXTENSION])
QED

Theorem REGULAR_CLOSED_UNDER_INTER:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 ∩ L2, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_DFA] >>
  rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘dfa_inter M1 M2’ >> rw[]
  >- metis_tac [is_dfa_inter]
  >- (drule_all dfa_inter_correct >> simp [EXTENSION])
QED

Theorem REGULAR_CLOSED_UNDER_DIFF:
  (L1,A) ∈ REGULAR ∧ (L2,A) ∈ REGULAR ⇒ (L1 DIFF L2, A) ∈ REGULAR
Proof
  strip_tac >>
  dxrule REGULAR_CLOSED_UNDER_COMPL >> disch_tac >>
  subgoal ‘L1 ∩ (KSTAR {[a] | a ∈ A} DIFF L2) = L1 DIFF L2’ >-
    (simp[EXTENSION,EQ_IMP_THM] >>
     rev_drule REGULAR_BOUNDED >>
     simp [SUBSET_DEF]) >>
  metis_tac [REGULAR_CLOSED_UNDER_INTER]
QED

Theorem REGULAR_CLOSED_UNDER_REVERSE:
  (L,A) ∈ REGULAR ⇒ (IMAGE REVERSE L, A) ∈ REGULAR
Proof
  rw [IN_REGULAR_AS_NFA] >>
  qexists_tac ‘dfa_rev N’ >> rw[]
  >- simp [dfa_rev_def]
  >- metis_tac [wf_dfa_rev] >>
  imp_res_tac wf_dfa_rev >>
  simp [EXTENSION, in_nfa_lang_iff_accepting_exec] >>
  rw [EQ_IMP_THM,PULL_EXISTS,is_accepting_exec_def]
  >- (irule_at Any dfa_rev_execA >>
      first_assum (irule_at Any) >>
      simp [dfa_rev_def] >>
      imp_res_tac is_exec_nonempty >>
      simp [HD_REVERSE,LAST_REVERSE]) >>
  irule_at Any (GSYM REVERSE_REVERSE) >>
  irule_at Any dfa_rev_execB >>
  ntac 2 (goal_assum drule) >>
  drule is_exec_nonempty >>
  simp [HD_REVERSE,LAST_REVERSE] >>
  gvs [dfa_rev_def]
QED

(*---------------------------------------------------------------------------*)
(* Closure under concatenation and KPLUS. Closure under KSTAR is a           *)
(* consequence of closure under KPLUS.                                       *)
(*---------------------------------------------------------------------------*)

Definition dfa_dot_def:
  dfa_dot N1 N2 =
    <|Q := N1.Q ∪ N2.Q; (* N1.Q and N2.Q are disjoint *)
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

Definition dfa_plus_def:
  dfa_plus N =
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

Theorem dfa_dot_builtin_simps[local,simp]:
  (∀q. q ∈ (dfa_dot N1 N2).Q <=> q ∈ N1.Q ∨ q ∈ N2.Q) ∧
  (∀a. a ∈ (dfa_dot N1 N2).Sigma ⇔ a ∈ N1.Sigma ∧ a ∈ N2.Sigma) ∧
  (dfa_dot N1 N2).initial = N1.initial ∧
  (dfa_dot N1 N2).final = N2.final
Proof
  rw[dfa_dot_def]
QED

Theorem dfa_plus_builtin_simps[local,simp]:
  (dfa_plus N).Sigma = N.Sigma ∧
  (dfa_plus N).Q = N.Q ∧
  (dfa_plus N).initial = N.initial ∧
  (dfa_plus N).final = N.final
Proof
  rw[dfa_plus_def]
QED

Theorem is_dfa_dot:
  is_nfa N1 ∧ is_nfa N2 ∧ N1.Q ∩ N2.Q = {} ==> is_nfa (dfa_dot N1 N2)
Proof
  fs [is_nfa_def, dfa_dot_def] >> rw[]
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

Theorem is_dfa_plus:
  is_nfa N ==> is_nfa (dfa_plus N)
Proof
  rw [is_nfa_def, dfa_plus_def,SUBSET_DEF] >>
  pop_keep_tac >> rw[] >> metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* Closure under concatenation needs some support infrastructure. Adding a   *)
(* new start state with arrows to all targets of the original start state(s) *)
(* gives a machine that accepts the original language less ε.                *)
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
   ⇒ (new_start_state N).delta q a = N.delta q a
Proof
  rw [new_start_state_def,is_dfa_def, is_nfa_def] >>
  metis_tac [new_state_thm]
QED

Theorem wf_new_start_state:
  is_nfa N ⇒ is_nfa (new_start_state N)
Proof
  fs [is_nfa_def, new_start_state_def] >> rw[]
  >- metis_tac [SUBSET_UNION_RIGHT]
  >- (rw [] >> metis_tac [new_state_thm,SUBSET_UNION_RIGHT])
  >- (irule SUBSET_UNION_RIGHT >> rw [SUBSET_DEF] >> metis_tac [SUBSET_DEF])
QED

Theorem is_dfa_new_start_state:
  is_dfa N ⇒ is_dfa (new_start_state N)
Proof
  rw [is_dfa_def,wf_new_start_state] >>
  fs [new_start_state_def] >> rw[]
  >- metis_tac [new_state_thm,is_nfa_def]
  >- (‘∃qa. N.delta q_0 a = {qa}’
            by metis_tac [is_nfa_def,EXTENSION,IN_INSERT,SUBSET_DEF] >>
      qexists_tac ‘qa’ >> rw [EXTENSION,EQ_IMP_THM]
      >- metis_tac[]
      >- (qexists_tac ‘{qa}’ >> rw[]))
QED

Theorem epsilon_not_in_new_start_state_lang:
  is_nfa N ⇒ ε ∉ nfa_lang (new_start_state N)
Proof
  rpt strip_tac >> drule_then assume_tac wf_new_start_state >>
  drule epsilon_in_nfa_lang >> rw[] >>
  rw [new_start_state_def] >> ntac 2 pop_forget_tac >>
  fs [is_nfa_def,EXTENSION] >> metis_tac [new_state_thm,SUBSET_DEF]
QED

Theorem new_start_state_closed:
  is_nfa N ∧
  is_exec (new_start_state N) qs w ⇒
  ∀n. 0 < n ∧ n < LENGTH qs ⇒ EL n qs ∈ N.Q
Proof
  strip_tac >> Induct >> rw[] >>
  ‘n < LENGTH qs’ by decide_tac >>
  fs [is_exec_def,EVERY_EL,is_nfa_def,SUBSET_DEF] >>
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
             (fs [is_dfa_def] >> drule new_start_state_closed >>
              disch_then irule >> rw[is_exec_def] >>
              metis_tac[]) >>
          metis_tac [new_start_state_delta, ADD1]))
QED

Theorem new_start_state_diff_epsilon:
  is_dfa N ⇒ nfa_lang N DIFF {ε} ⊆ nfa_lang (new_start_state N)
Proof
  rw [EXTENSION,in_nfa_lang,SUBSET_DEF] >>
  rename1 ‘LENGTH w + 1’ >>
  qexists_tac ‘new_state N :: TL qs’ >>
  fs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL] >> rw[]
  >- (‘TL qs ≠ []’
       by (Cases_on ‘qs’ >> fs[] >> Cases_on ‘t’ >> gvs[]) >>
      rw [LAST_DEF]) >>
  ‘qs ≠ []’ by (Cases_on ‘qs’ >> fs[]) >>
  Cases_on ‘n’ >> fs[]
   >- (first_x_assum drule >> rw[] >>
       rw [new_start_state_def,PULL_EXISTS] >> metis_tac[])
   >- (fs [is_dfa_def] >> rename1 ‘SUC m < LENGTH w’ >>
       subgoal ‘is_exec N qs w’ >-
          (irule (iffRL is_exec_def) >> simp[] >>
           metis_tac [dfa_is_nfa,is_nfa_def,SUBSET_DEF]) >>
       imp_res_tac dfa_is_nfa >> drule_all is_exec_states >>
       rw [EVERY_EL] >> ‘m + 1 < LENGTH w + 1’ by decide_tac >> res_tac >>
       ‘EL (SUC m) w ∈ N.Sigma’ by fs [EVERY_EL] >> rw[GSYM ADD1] >>
       metis_tac[new_start_state_delta,ADD1,is_dfa_def])
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
 rw [is_dfa_def,is_nfa_def]
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
          metis_tac [new_state_thm, is_dfa_def, is_nfa_def]))
QED

Theorem REGULAR_CLOSED_UNDER_EPSILON_DELETION:
  (L,A) ∈ REGULAR ⇒ (L DIFF {ε},A) ∈ REGULAR
Proof
  metis_tac [REGULAR_CLOSED_UNDER_DIFF,
             EPSILONSET_IN_REGULAR,
             REGULAR_SIGMA_FINITE]
QED

Theorem isolate_trivial_cases[local]:
 ∀L. ∃L0. L0 ⊆ {ε} ∧ L = L0 ∪ (L DIFF {ε})
Proof
  rw [SUBSET_DEF,EXTENSION] >>
  qexists_tac ‘if ε ∈ L then {ε} else {}’ >>
  rw[EQ_IMP_THM] >> metis_tac[]
QED

Theorem TRIVIAL_DOT_TRIVIAL_IN_REGULAR:
  L1 ⊆ {ε} ∧ L2 ⊆ {ε} ∧ FINITE A ⇒ (L1 dot L2,A) ∈ REGULAR
Proof
  rw [SUBSET_SING] >> simp [DOT_EMPTYSET, DOT_EPSILONSET] >>
  metis_tac [EMPTYSET_IN_REGULAR,EPSILONSET_IN_REGULAR]
QED

Theorem TRIVIAL_DOT_EPSILON_FREE_IN_REGULAR[local]:
  (L,A) ∈ REGULAR ∧
  s1 ⊆ {ε} ∧ s2 ⊆ {ε}
  ⇒
  (L = s2 ∪ (L DIFF {ε}) ⇒ (s1 dot (L DIFF {ε}),A) ∈ REGULAR) ∧
  (L = s1 ∪ (L DIFF {ε}) ⇒ ((L DIFF {ε}) dot s2,A) ∈ REGULAR)
Proof
  rw [SUBSET_SING] >>
  fs [DOT_EMPTYSET, DOT_EPSILONSET] >>
  metis_tac [EMPTYSET_IN_REGULAR, REGULAR_CLOSED_UNDER_EPSILON_DELETION,
             UNION_COMM,REGULAR_SIGMA_FINITE]
QED

(*---------------------------------------------------------------------------*)
(* Mechanism for renaming states apart when combining machines, Used in the  *)
(* dfa_dot machine. Without renaming, the composed transition function could *)
(* be confused when given a state that happened to occur in both components. *)
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

Theorem is_nfa_rename_states:
  is_nfa N ⇒ is_nfa (rename_states N base)
Proof
  rw[is_nfa_def,rename_states_def,SUBSET_DEF] >> metis_tac[oldFn_newFn]
QED

Theorem rename_states_delta_commutes:
  is_nfa N ∧ q ∈ N.Q ∧ a ∈ N.Sigma
  ⇒ N.delta q a = IMAGE (LINV (newFn base) N.Q)
                     ((rename_states N base).delta (newFn base q) a)
Proof
  rw[EXTENSION,EQ_IMP_THM,rename_states_def] >>
  qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
  metis_tac [is_nfa_def,SUBSET_DEF,oldFn_newFn]
QED

Theorem is_dfa_rename_states:
  is_nfa N ⇒ (is_dfa (rename_states N base) ⇔ is_dfa N)
Proof
  rw [is_dfa_def,EQ_IMP_THM,is_nfa_rename_states]
  >- (pop_forget_tac >> pop_keep_tac >> simp [rename_states_def] >>
      ‘BIJ (newFn base) N.initial (IMAGE (newFn base) N.initial)’ by
         (irule INJ_BIJ_SUBSET >> qexists_tac ‘𝕌(:num)’ >>
          rw [SUBSET_DEF] >> metis_tac [INJ_newFn]) >>
      ‘FINITE N.initial’ by metis_tac [is_nfa_def,SUBSET_FINITE] >>
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
  is_nfa N ⇒ nfa_lang (rename_states N base) = nfa_lang N
Proof
  rw [EXTENSION,EQ_IMP_THM]
  >- (drule_then (qspec_then ‘base’ assume_tac) is_nfa_rename_states >>
      drule_all in_nfa_lang_is_accepting_exec >>
      rw[NULL_EQ,is_accepting_exec_def,in_nfa_lang]
      >- (drule is_exec_Sigma >> rw[])
      >- (qpat_forget_tac ‘_ ∈ nfa_lang _’ >>
          qpat_stage_tac ‘HD qs ∈ _’ >> qpat_stage_tac ‘LAST qs ∈ _’ >>
          rw [rename_states_def] >> rename [‘qi ∈ N.initial’, ‘qf ∈ N.final’] >>
          qabbrev_tac ‘oldFn = LINV (newFn base) N.Q’ >>
          qexists_tac ‘MAP oldFn qs’ >> rw[]
          >- (drule is_exec_length >> rw[])
          >- metis_tac [oldFn_newFn,is_nfa_def,SUBSET_DEF]
          >- metis_tac [oldFn_newFn,is_nfa_def,SUBSET_DEF]
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
              metis_tac [is_nfa_def, SUBSET_DEF,oldFn_newFn])))
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
  FINITE Q ∧ is_nfa N
  ⇒
  ∃N'. N'.Sigma = N.Sigma ∧
       Q ∩ N'.Q = ∅ ∧
       is_nfa N' ∧
       (is_dfa N' ⇔ is_dfa N) ∧
       nfa_lang N' = nfa_lang N
Proof
 strip_tac >>
 qexists_tac ‘rename_states N (MAX_SET (Q ∪ N.Q) + 1)’ >> rw[]
 >- (rw [rename_states_def,EXTENSION, Once (GSYM IMP_DISJ_THM),newFn_def] >>
     CCONTR_TAC >> pop_forget_tac >>
     ‘FINITE N.Q’ by metis_tac [is_nfa_def] >> qpat_stage_tac ‘_ ∈ _’ >>
     rw [MAX_SET_UNION,MAX_DEF] >> irule MAX_SET_BOUNDED >> rw[])
 >- metis_tac [is_nfa_rename_states]
 >- metis_tac [is_dfa_rename_states]
 >- metis_tac [nfa_lang_rename_states]
QED

(*---------------------------------------------------------------------------*)
(* Correctness of dfa_dot construction for epsilon-free machines is based on *)
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
  is_accepting_exec (dfa_dot M1 M2) (qs1 ++ TL qs2) (w1 ++ w2)
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
  >- metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF]
  >- (‘n < LENGTH w1 ∨ n = LENGTH w1 ∨ LENGTH w1 < n’ by decide_tac
      >- (rev_drule is_exec_Sigma >> rw[EVERY_EL] >>
          rev_drule is_exec_length >> strip_tac >>
          ‘n < LENGTH qs1’ by decide_tac >> ‘n+1 < LENGTH qs1’ by decide_tac >>
          rw[EL_APPEND1] >> rw [dfa_dot_def]
          >- metis_tac [is_exec_delta,is_dfa_def]
          >- metis_tac [is_exec_delta,is_dfa_def]
          >- (qpat_stage_tac ‘EVERY _ qs1’ >> rw[EVERY_EL] >> metis_tac[]))
      >- (rw[] >> rfs[] >> rev_drule is_exec_length >>
          disch_then(assume_tac o SYM) >> ONCE_ASM_REWRITE_TAC[] >>
          rw[SRULE [NULL_EQ] EL_LENGTH_APPEND] >>
          ‘LENGTH w1 < LENGTH qs1’ by decide_tac >> rw [EL_APPEND1] >>
          ‘LENGTH w1 = PRE (LENGTH qs1)’ by decide_tac >> pop_subst_tac >>
          rw [EL_PRE_LENGTH] >> rw [dfa_dot_def,PULL_EXISTS]
          >- (disj2_tac >> rfs [is_dfa_def,NOT_NIL_EQ_LENGTH_NOT_0] >> rw[] >>
              ‘0 < LENGTH w1’ by decide_tac >> PURE_REWRITE_TAC[GSYM EL] >>
              drule is_exec_delta >> disch_then drule >> simp[] >> rfs[])
          >- metis_tac[is_dfa_def,is_nfa_def,SUBSET_DEF])
      >- (‘∃k. 0 < k ∧ k < LENGTH w2 ∧ n = LENGTH w1 + k’
            by (qexists_tac ‘n - LENGTH w1’ >> fs[]) >> rw[EL_APPEND2_ALT] >>
          rev_drule is_exec_length >> disch_tac >>
          ‘k + (LENGTH w1 + 1) = LENGTH qs1 + k’ by decide_tac >> pop_subst_tac >>
          drule is_exec_length >> disch_tac >>
          ‘k < LENGTH (TL qs2)’
            by (‘k + 1 < LENGTH qs2’ by decide_tac >>
                drule LENGTH_TL_ALT >> rw[]) >>
          ‘k < LENGTH qs2’ by decide_tac >>
          rw [EL_APPEND2_ALT] >> rw [EL_APPEND_EQN] >> rw [dfa_dot_def]
          >- (fs [EVERY_EL,EXTENSION] >> metis_tac[])
          >- (fs [EVERY_EL,EXTENSION] >> metis_tac[])
          >- metis_tac [is_exec_delta])
     )
  >- rw[LAST_APPEND_NOT_NIL]
QED

Theorem dfa_dot_paste:
  is_dfa M1 ∧ is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧ M1.Q ∩ M2.Q = ∅ ∧
  ε ∉ nfa_lang M1 ∧ ε ∉ nfa_lang M2
  ⇒
  nfa_lang M1 dot nfa_lang M2 ⊆ nfa_lang (dfa_dot M1 M2)
Proof
  rw [SUBSET_DEF, IN_dot] >>
  ‘u ≠ ε ∧ v ≠ ε’ by metis_tac[] >>
  ntac 2 (qpat_forget_tac ‘ε ∉ _’) >>
  ‘is_nfa M1 ∧ is_nfa M2 ∧ is_nfa (dfa_dot M1 M2)’ by
    metis_tac [is_dfa_def,is_dfa_dot] >>
  fs [in_nfa_lang_iff_accepting_exec] >>
  metis_tac[is_accepting_exec_paste]
QED

Theorem dfa_dot_delta_states[local]:
  is_nfa M1 ∧ is_nfa M2 ∧
  M1.Sigma = M2.Sigma ∧ a ∈ M1.Sigma ∧ q ∈ M1.Q ∪ M2.Q
  ⇒
  (dfa_dot M1 M2).delta q a ⊆ M1.Q ∪ M2.Q
Proof
  rw [is_nfa_def, dfa_dot_def,SUBSET_DEF] >> metis_tac[]
QED

Theorem dfa_dot_delta_second_states[local]:
  is_nfa M1 ∧ is_nfa M2 ∧ M1.Q ∩ M2.Q = ∅ ∧
  M1.Sigma = M2.Sigma ∧ a ∈ M1.Sigma ∧ q ∈ M2.Q ∧
  q' ∈ (dfa_dot M1 M2).delta q a
  ⇒
  q' ∈ M2.Q
Proof
  rw [is_nfa_def, dfa_dot_def,EXTENSION,SUBSET_DEF] >> metis_tac[]
QED

Theorem dfa_dot_states[local]:
  is_nfa M1 ∧ is_nfa M2 ∧ M1.Sigma = M2.Sigma ∧
  is_exec (dfa_dot M1 M2) qs w
  ⇒
  EVERY (λq. q ∈ M1.Q ∪ M2.Q) qs
Proof
  simp[EVERY_EL] >> disch_tac >> Induct >> rw[] >>
  imp_res_tac POS_LENGTH_NOT_NIL >> fs [is_exec_def,EVERY_EL] >>
  ‘n < LENGTH w’ by decide_tac >>
  first_x_assum drule >> first_x_assum drule >> rw[] >>
  metis_tac[dfa_dot_delta_states, IN_UNION, ADD1, SUBSET_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Lemma about dfa_dot executions being split into component executions.     *)
(*                                                                           *)
(*   Let qs be an dfa_dot execution accepting word w. The first state        *)
(*   of qs is in M1.Q and the last state is in M2.Q. Therefore there is      *)
(*   a first state of qs that is in M2.Q; say it occurs at index j. Since    *)
(*   M1 and M2 do not accept epsilon, 1 < j < length(qs). Thus               *)
(*   qs[0 .. j-1] is a sequence of M1.Q states, and                          *)
(*   qs[j .. length(qs)-1] is a sequence of M2.Q states. Moreover            *)
(*                                                                           *)
(*    * qs[j-1] ∈ M1.final                                                   *)
(*    * qs[j] = M2.delta M2.initial (w[j-1])                                 *)
(*    * (dfa_dot M1 M2).delta behaves the same as M1.delta below j-1,        *)
(*      and the same as M2.delta at j and above.                             *)
(*---------------------------------------------------------------------------*)

Theorem dfa_dot_snip_lemma:
  is_dfa M1 ∧
  is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧
  M1.Q ∩ M2.Q = ∅ ∧
  ε ∉ nfa_lang M1 ∧
  ε ∉ nfa_lang M2 ∧
  is_exec (dfa_dot M1 M2) qs w ∧
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
          metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF])
      >- (first_x_assum drule >> rw[] >>
          ‘EVERY (λq. q ∈ M1.Q ∪ M2.Q) qs’ by
             (irule dfa_dot_states >> metis_tac [is_dfa_def]) >>
          fs [EVERY_EL] >> metis_tac [LESS_TRANS])) >>
  qexists_tac ‘j’ >> rpt conj_asm1_tac
  >- (spose_not_then assume_tac >> ‘j= 0 ∨ j = 1’ by decide_tac >> rw[]
      >- (fs[EXTENSION] >> metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF])
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
          qexists_tac ‘0’ >> rw [dfa_dot_def] >> fs[EXTENSION] >>
          metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF]))
  >- asm_rewrite_tac[]
  >- (rw[] >> ‘EL i qs ∈ M1.Q ∧ EL (i+1) qs ∈ M1.Q’ by rw[] >>
      drule is_exec_length >> rw [] >> fs[] >>
      ‘i < LENGTH w’ by decide_tac >>
      drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
      first_x_assum drule >> rw[] >>
      drule is_exec_delta >> rw[] >> first_x_assum drule >>
      rw [dfa_dot_def] >> fs[EXTENSION] >>
      metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF])
  >- (drule is_exec_length >> rw [] >> fs[] >>
      ‘EL (j-1) qs ∈ M1.Q ∧ j-1 < LENGTH w’ by rw[] >>
      drule is_exec_delta >> rw[] >> first_x_assum drule >>
      rw [dfa_dot_def] >> fs[] >> strip_tac >>
      drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
      fs [EXTENSION] >>
      ‘j-1 < LENGTH w’ by rw[] >>
      metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF])
  >- (drule is_exec_length >> rw [] >> fs[] >>
       ‘EL (j-1) qs ∈ M1.Q ∧ j-1 < LENGTH w’ by rw[] >>
       drule is_exec_delta >> rw[] >> first_x_assum drule >>
       rw [dfa_dot_def] >> fs[] >>
       drule is_exec_Sigma >> strip_tac >> fs [EVERY_EL] >>
       fs [EXTENSION] >>
       ‘j-1 < LENGTH w’ by rw[] >>
      metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF])
  >- (rw [] >> rpt (forget_tac is_forall) >>
      drule is_exec_length >> rw [] >> fs[] >> rw[] >>
      ‘EL (j+k) qs ∈ M2.Q’ by
         (Induct_on ‘k’ >> rw[] >>
          irule dfa_dot_delta_second_states >> rw []
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
      rw [dfa_dot_def] >> fs[EXTENSION] >> metis_tac[])
QED

Theorem dfa_dot_snip:
  is_dfa M1 ∧ is_dfa M2 ∧
  M1.Sigma = M2.Sigma ∧ M1.Q ∩ M2.Q = ∅ ∧
  ε ∉ nfa_lang M1 ∧ ε ∉ nfa_lang M2
  ⇒ nfa_lang (dfa_dot M1 M2) ⊆ nfa_lang M1 dot nfa_lang M2
Proof
  rw [SUBSET_DEF] >> rename1 ‘w ∈ _’ >>
  ‘is_nfa (dfa_dot M1 M2)’ by
    metis_tac [is_dfa_def,is_dfa_dot] >>
  drule_all in_nfa_lang_is_accepting_exec >> rw[is_accepting_exec_def] >>
  qpat_forget_tac ‘w ∈ nfa_lang _’ >> qpat_forget_tac ‘~NULL qs’ >>
  drule_all dfa_dot_snip_lemma >> rw [IN_dot] >>
  qexistsl_tac [‘TAKE (j-1) w’, ‘DROP (j-1) w’] >> rw[in_nfa_lang] >>
  TRY (drule is_exec_Sigma >> rw [dfa_dot_def,EVERY_TAKE,EVERY_DROP])
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
    (‘FINITE M1.Q ∧ is_nfa M2’ by metis_tac [is_dfa_def, is_nfa_def] >>
     drule_all RENAME_STATES_APART >> metis_tac []) >>
  rw [IN_REGULAR_AS_NFA] >> pop_sym_subst_tac >> qpat_forget_tac ‘is_dfa M2’ >>
  qpat_x_assum ‘nfa_lang M2a = nfa_lang M2’ sym_subst_all_tac >>
  rename1 ‘M1.Sigma = M2.Sigma’ >>
  qexists_tac ‘dfa_dot M1 M2’ >> rpt conj_tac
  >- rw [dfa_dot_def]
  >- metis_tac [is_dfa_def,is_dfa_dot]
  >- metis_tac [dfa_dot_paste, dfa_dot_snip, SET_EQ_SUBSET]
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
  strip_assume_tac (Q.ISPEC ‘L1 : 'a list -> bool’ isolate_trivial_cases) >>
  rename1 ‘s1 ⊆ {ε}’ >>
  strip_assume_tac (Q.ISPEC ‘L2 : 'a list -> bool’ isolate_trivial_cases) >>
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
(* Closure under Kleene Star. From                                           *)
(*                                                                           *)
(*  wlist = [w1 ; ... ; wn]                                                  *)
(*                                                                           *)
(* obtain                                                                    *)
(*                                                                           *)
(*  qslist = [qs1 ; ... ; qsn]                                               *)
(*                                                                           *)
(* where                                                                     *)
(*                                                                           *)
(*  is_accepting_exec qsi wi holds, for i < LENGTH wlist                     *)
(*                                                                           *)
(* To then build the execution for the dfa_plus machine, we basically want   *)
(* to build the full dfa_plus state list as "FLAT qslist". But, as for the   *)
(* dfa_dot pasting lemma, we have to arrange for the branching back from     *)
(* accept states to skip over the initial state. Thus for every qsi,         *)
(* i > 1, drop the HD:                                                       *)
(*                                                                           *)
(*  dfa_plus_qs = qs1 ++ TL qs2 ++ ... ++ TL qsn                             *)
(*---------------------------------------------------------------------------*)

Theorem qslist_length[local]:
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

Theorem length_flat_tl_lem[local]:
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

Theorem LAST_APPEND_FLAT[local]:
  ll ≠ [] ∧ LAST ll ≠ []
  ⇒
  LAST (list ++ FLAT ll) = LAST (LAST ll)
Proof
  rw[] >> drule_all LAST_FLAT >> disch_tac >>
  drule FLAT_NOT_NIL >> rw[LAST_APPEND_NOT_NIL]
QED

Theorem dfa_plus_delta_subset:
  M.delta q a ⊆ (dfa_plus M).delta q a
Proof
 rw [dfa_plus_def]
QED

Theorem is_accepting_exec_dfa_plus:
  is_accepting_exec M qs w ⇒ is_accepting_exec (dfa_plus M) qs w
Proof
  rw [is_accepting_exec_def, dfa_plus_def,is_exec_def] >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Similar to the pasting theorem for dfa_dot. The difference is that, for   *)
(* nfa_kplus, there's only one machine, which loops back from final states   *)
(* to the successors of the start state.                                     *)
(*---------------------------------------------------------------------------*)

Theorem is_accepting_exec_dfa_plus_paste:
  is_dfa M ∧
  w1 ≠ ε ∧ w2 ≠ ε ∧
  is_accepting_exec (dfa_plus M) qs1 w1 ∧
  is_accepting_exec M qs2 w2
  ⇒
  is_accepting_exec (dfa_plus M) (qs1 ++ TL qs2) (w1 ++ w2)
Proof
  rw [is_accepting_exec_def] >>
  ‘is_nfa M ∧ is_nfa (dfa_plus M)’ by
     metis_tac [is_dfa_def,is_dfa_plus] >>
  ‘EVERY (λq. q ∈ (dfa_plus M).Q) qs1 ∧ EVERY (λq. q ∈ M.Q) qs2’ by
     metis_tac [is_dfa_def,is_exec_states] >>
  ‘qs1 ≠ [] ∧ qs2 ≠ []’ by
     metis_tac [is_exec_nonempty] >>
  ‘TL qs2 ≠ []’ by
     metis_tac [is_accepting_exec_length,is_accepting_exec_def,is_dfa_def] >>
  rw [is_exec_def]
  >- fs [is_exec_def]
  >- fs [is_exec_def]
  >- (imp_res_tac is_exec_length >> rw[LENGTH_TL])
  >- metis_tac [is_dfa_def,is_nfa_def,SUBSET_DEF]
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
          rw [EL_PRE_LENGTH] >> rw [dfa_plus_def,PULL_EXISTS] >>
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
          rw[EL_APPEND2_ALT] >> rw[EL_APPEND_EQN] >> rw [dfa_plus_def,PULL_EXISTS]
          >- metis_tac [is_exec_delta]
          >- (disj1_tac >>
             ‘EL k qs2 ∈ M.Q’ by
                metis_tac[is_dfa_def,is_nfa_def, SUBSET_DEF] >>
             drule is_exec_delta >> disch_then drule >> metis_tac[]))
     )
  >- rw[LAST_APPEND_NOT_NIL]
QED

Theorem is_accepting_exec_dfa_plus_paste_list:
  ∀f qs qslist wlist w.
    (f = λa b c. a ⧺ TL b) ∧
    is_dfa M ∧ w ≠ ε ∧
    EVERY (λw. w ≠ ε) wlist ∧
    is_accepting_exec (dfa_plus M) qs w ∧
    LIST_REL (is_accepting_exec M) qslist wlist
    ⇒
    is_accepting_exec (dfa_plus M)
      (FOLDL2 f qs qslist wlist)
      (FLAT (w::wlist))
Proof
  ho_match_mp_tac FOLDL2_ind >> rw[] >>
  first_x_assum irule >> rw[] >>
  irule is_accepting_exec_dfa_plus_paste >> rw[]
QED

Theorem KPLUS_SUBSET_DFA_PLUS:
  is_dfa M ∧ ε ∉ nfa_lang M
  ⇒ KPLUS (nfa_lang M) ⊆ nfa_lang (dfa_plus M)
Proof
  rw [SUBSET_DEF] >>
  drule_all (iffLR IN_KPLUS_LIST) >> rw[] >>
  ‘is_nfa M ∧ is_nfa (dfa_plus M)’ by
     metis_tac [is_dfa_def,is_dfa_plus] >>
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
  drule is_accepting_exec_dfa_plus >> rw_tac bool_ss [Once (GSYM FLAT)] >>
  irule is_accepting_exec_dfa_plus_paste_list >> rw[]
QED

Theorem dfa_plus_diff[local]:
  is_dfa M ∧
  a ∈ M.Sigma ∧
  q2 ∈ (dfa_plus M).delta q1 a ∧
  q2 ∉ M.delta q1 a ⇒
  q1 ∈ M.final ∧ BIGUNION {M.delta q0 a | q0 | q0 ∈ M.initial} = {q2}
Proof
  rw [is_dfa_def,dfa_plus_def] >> rfs[] >> rw[] >>
  rename1 ‘q2 ∈ M.delta q0 a’ >>
  rw [EXTENSION,EQ_IMP_THM]
  >- (‘∃q'. M.delta q0 a = {q'}’ by
        metis_tac [is_nfa_def,SUBSET_DEF,IN_INSERT] >> gvs[])
  >- metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* One step of splitting an "dfa_plus(M)" execution into a leading "M"       *)
(* execution followed by either (A) an empty execution, or, (B) by another   *)
(* dfa_plus(M) execution. Note the start state has to be attached before the *)
(* tail dfa_plus(M) execution becomes well-formed.                           *)
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

Theorem cronch_splits_input[local]:
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
  rw[AllCaseEqs(),cronch_def] >> gvs[]
QED

Theorem cronch_consumes_lem[local]:
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

Theorem cronch_exec:
  ∀M w qs q0 wpref wsuff qpref qsuff.
   is_dfa M ∧
   M.initial = {q0} ∧
   w ≠ ε ∧
   LAST qs ∈ M.final ∧
   is_exec (dfa_plus M) qs (TL w) ∧
   cronch M w qs = (wpref,wsuff,qpref,qsuff)
   ⇒
     is_exec M qpref (TL wpref) ∧
     LAST qpref ∈ M.final ∧
     (qsuff = [] ∨ is_exec (dfa_plus M) (q0::qsuff) wsuff)
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
              irule (snd_conj is_exec_step_left) >> metis_tac [is_dfa_plus]))
      >- (‘LENGTH qs = LENGTH w’ by gvs[is_exec_def] >>
          imp_res_tac cronch_consumes >> rw[] >> gvs[] >>
          first_x_assum (irule_at Any o fst_conj o snd_conj) >>
          irule (snd_conj is_exec_step_left) >>
          metis_tac [is_dfa_def,is_dfa_plus])
      >- (first_x_assum (irule_at Any o snd_conj o snd_conj) >>
          irule (snd_conj is_exec_step_left) >>
          metis_tac [is_dfa_def,is_dfa_plus])
      >- gvs [is_exec_def]
      >- (gvs [is_exec_def,dfa_plus_def] >>
          ‘0 < SUC (LENGTH w)’ by decide_tac >>
          first_x_assum drule >> simp[] >> rw[])
      >- (‘LENGTH w = LENGTH qs’ by gvs[is_exec_def] >>
          ‘is_nfa (dfa_plus M)’ by metis_tac [is_dfa_plus,is_dfa_def] >>
          imp_res_tac is_exec_step_left >>
          ‘b ∈ M.Sigma’ by gvs [is_exec_def] >>
          irule is_exec_extend_left >> rw[]
          >- metis_tac [IN_INSERT,SUBSET_DEF,is_nfa_def,is_dfa_def]
          >- (‘b ∈ M.Sigma’ by gvs [is_exec_def] >>
              drule_all dfa_plus_diff >> rw[dfa_plus_def] >>
              irule (iffRL ELT_SUBSET) >>
              qpat_x_assum ‘BIGUNION _ = _’ sym_subst_all_tac >>
              simp[SUBSET_DEF])))
  >> gvs[cronch_def, is_exec_def]
QED

Theorem cronch_accepting_exec:
  is_dfa M ∧ M.initial = {q0} ∧ w ≠ ε ∧
  is_accepting_exec (dfa_plus M) qs (TL w) ∧
  cronch M w qs = (wprefix,wsuffix,qprefix,qsuffix)
  ⇒
  is_accepting_exec M qprefix (TL wprefix) ∧
  (qsuffix = [] ∨ is_accepting_exec (dfa_plus M) (q0::qsuffix) wsuffix)
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

Theorem cronch_accepting_exec_alt[local]:
  is_dfa M ∧ M.initial = {q0} ∧ is_accepting_exec (dfa_plus M) qs w ∧
  cronch M (ARB::w) qs = (wprefix,wsuffix,qprefix,qsuffix)
  ⇒
  is_accepting_exec M qprefix (TL wprefix) ∧
  (qsuffix = [] ∨ is_accepting_exec (dfa_plus M) (q0::qsuffix) wsuffix)
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
  is_nfa N ∧ ε ∉ nfa_lang N ∧
  is_accepting_exec N qs w
  ⇒ ∃q1 q2 qs'. qs = q1::q2::qs'
Proof
  rw[] >> gvs [in_nfa_lang_iff_accepting_exec] >>
  ‘w ≠ ε’ by metis_tac[] >>
  metis_tac[epsilon_free_exec_left_cons,is_accepting_exec_def]
QED

Definition cronch_all_def:
  cronch_all M q0 w qs =
    if is_dfa M ∧ ε ∉ nfa_lang M ∧
       is_accepting_exec (dfa_plus M) qs w
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
    is_accepting_exec (dfa_plus M) qs w ∧
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

Theorem dfa_plus_exec_to_nfa_execs:
  is_dfa M ∧
  ε ∉ nfa_lang M ∧
  is_accepting_exec (dfa_plus M) qs w
  ⇒
  ∃qslist wlist.
    LIST_REL (is_accepting_exec M) qslist wlist ∧
    w = FLAT wlist ∧
    wlist ≠ []
Proof
  metis_tac [cronch_all_thm,ABS_PAIR_THM,is_dfa_def]
QED

Theorem LIST_REL_EVERY[local]:
  LIST_REL R l1 l2 ⇒ EVERY (λx. ∃y. R x y) l1
Proof
  rw[EVERY_MEM] >> drule_all LIST_REL_MEM_IMP >> metis_tac[]
QED

Theorem LIST_REL_EVERY_R[local]:
  LIST_REL R l1 l2 ⇒ EVERY (λy. ∃x. R x y) l2
Proof
  rw[EVERY_MEM] >> drule_all LIST_REL_MEM_IMP_R >> metis_tac[]
QED

Theorem DFA_PLUS_SUBSET_KPLUS:
  is_dfa M ∧ ε ∉ nfa_lang M
  ⇒
  nfa_lang (dfa_plus M) ⊆ KPLUS (nfa_lang M)
Proof
  strip_tac >> simp[SUBSET_DEF] >>
  ‘is_nfa M ∧ is_nfa (dfa_plus M)’ by
     metis_tac [is_dfa_def,is_dfa_plus] >>
  rw [in_nfa_lang_iff_accepting_exec] >>
  rw [IN_KPLUS_LIST] >>
  rw [in_nfa_lang_iff_accepting_exec] >>
  drule_all dfa_plus_exec_to_nfa_execs >> rw[] >>
  first_x_assum (irule_at Any) >> rw[] >>
  metis_tac [LIST_REL_EVERY_R]
QED

Theorem REGULAR_CLOSED_UNDER_EPSILON_FREE_KPLUS:
  ε ∉ L ∧ (L,A) ∈ REGULAR ⇒ (KPLUS L, A) ∈ REGULAR
Proof
  disch_then (strip_assume_tac o SRULE [IN_REGULAR_AS_DFA]) >> rw[] >>
  rw [IN_REGULAR_AS_NFA] >> qexists_tac ‘dfa_plus M’ >> rpt conj_tac
  >- rw [dfa_plus_def]
  >- metis_tac[is_dfa_plus,is_dfa_def]
  >- metis_tac [SET_EQ_SUBSET, KPLUS_SUBSET_DFA_PLUS, DFA_PLUS_SUBSET_KPLUS]
QED

Theorem REGULAR_CLOSED_UNDER_KSTAR:
  (L,A) ∈ REGULAR ⇒ (KSTAR L,A) ∈ REGULAR
Proof
  strip_tac >>
  strip_assume_tac (isolate_trivial_cases |> Q.ISPEC ‘L:'a list->bool’) >>
  rename1 ‘s ⊆ {ε}’ >> ONCE_ASM_REWRITE_TAC[] >>
  rw [KSTAR_UNION] >>
  rw [GSYM KPLUS_UNION_EPSILONSET] >>
  ‘KPLUS s ∪ {ε} = {ε}’ by
     rw[KPLUS_UNION_EPSILONSET] >> rw[] >>
  irule REGULAR_CLOSED_UNDER_UNION >> reverse conj_tac
  >- metis_tac [EPSILONSET_IN_REGULAR,REGULAR_SIGMA_FINITE]
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

Theorem finite_image_states[local]:
  is_nfa N ⇒ FINITE{f N qset | qset | qset ⊆ N.Q}
Proof
  rw [GSPEC_IMAGE, o_DEF,LAMBDA_PROD,is_nfa_def] >>
  irule IMAGE_FINITE >> irule SUBSET_FINITE >>
  qexists_tac ‘POW N.Q’ >> conj_tac
  >- metis_tac [FINITE_POW]
  >- rw[SUBSET_DEF,POW_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Evaluate an NFA from a set of states                                      *)
(*---------------------------------------------------------------------------*)

Definition nfa_eval_def:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (BIGUNION {N.delta q a | q | q ∈ qset}) w
End

Theorem nfa_eval_append:
  ∀w1 w2 qset.
    is_nfa N ∧
    EVERY (λa. a ∈ N.Sigma) w1 ∧
    EVERY (λa. a ∈ N.Sigma) w2 ∧
    qset ⊆ N.Q
    ⇒
   nfa_eval N qset (w1 ++ w2) = nfa_eval N (nfa_eval N qset w1) w2
Proof
  Induct >> rw [nfa_eval_def] >>
  first_x_assum irule >>
  simp[BIGUNION_SUBSET,PULL_EXISTS] >>
  metis_tac[is_nfa_def,SUBSET_DEF]
QED

Theorem nfa_eval_states_closed:
  ∀w. is_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
  ⇒ nfa_eval N qset w ⊆ N.Q
Proof
  recInduct SNOC_INDUCT >>
  rw [nfa_eval_def,SNOC_APPEND] >>
  dep_rewrite.DEP_REWRITE_TAC [nfa_eval_append] >> simp [] >>
  first_x_assum drule >> simp [nfa_eval_def] >>
  rw [SUBSET_DEF] >> metis_tac [is_nfa_def,SUBSET_DEF]
QED

Theorem dfa_eval_states_closed:
  is_dfa M ∧ EVERY (λa. a ∈ M.Sigma) w
  ⇒
  ∀q. nfa_eval M M.initial w = {q} ⇒ q ∈ M.Q
Proof
  rw[is_dfa_def] >>
  ‘M.initial ⊆ M.Q’ by metis_tac [is_nfa_def] >>
  drule_all nfa_eval_states_closed >>
  rw[]
QED

(*---------------------------------------------------------------------------*)
(* NB: decent test for rewrite-enhanced irule                                *)
(*---------------------------------------------------------------------------*)

Theorem dfa_eval_final_state:
  ∀w. is_dfa M ∧
      EVERY (λa. a ∈ M.Sigma) w
      ⇒ ∃q. nfa_eval M M.initial w = {q}
Proof
  recInduct SNOC_INDUCT >>
  rw[is_dfa_def,nfa_eval_def,SNOC_APPEND] >>
  gvs[] >> rename1 ‘a ∈ N.Sigma’ >>
  ‘EVERY (λa. a ∈ N.Sigma) [a]’ by rw[] >>
  ‘{q_0} ⊆ N.Q’ by metis_tac[is_nfa_def] >>
  rw[nfa_eval_append] >>
  rev_drule_all nfa_eval_states_closed >> rw[] >>
  ‘∃q'. N.delta q a = {q'}’ by metis_tac[] >>
  qexists_tac ‘q'’ >>
  rw [nfa_eval_def,EXTENSION,EQ_IMP_THM]
  >- metis_tac[]
  >- (qexists_tac ‘{q'}’ >> rw[])
QED

(* NB: The following Theorem statement is not true: nfa_eval relies on
   the input word having all its symbols drawn from the alphabet. The
   N.delta q a transition is not defined when a is not in the alphabet. But,
   in HOL such an expression has a "value"---an unspecified value---which,
   typically, doesn't have enough info to push proofs ahead.

Theorem nfa_eval_Sigma:
  ∀w. is_nfa N ∧ w ∉ KSTAR{[a] | a ∈ N.Sigma}
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
  is_nfa N ∧ qset ⊆ N.Q ∧ EVERY (λa. a ∈ N.Sigma) w
   ⇒
  nfa_eval N qset w = {LAST qs | qs | is_exec N qs w ∧ HD qs ∈ qset}
Proof
  recInduct SNOC_INDUCT >> rw[] >> gvs[]
  >- (gvs [nfa_eval_def,is_exec_epsilon] >>
     rw[EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
     metis_tac[SUBSET_DEF])
  >- (rename1 ‘SNOC a w’ >>
      gvs[SNOC_APPEND] >> first_x_assum drule >>
      rw[nfa_eval_append,nfa_eval_def] >> pop_forget_tac >>
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
  is_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w
  ⇒
  (w ∈ nfa_lang N ⇔ nfa_eval N N.initial w ∩ N.final ≠ ∅)
Proof
  rpt strip_tac >>
  rw [in_nfa_lang_iff_accepting_exec, is_accepting_exec_def] >>
  gvs[is_nfa_def, nfa_eval_is_exec, EXTENSION] >> metis_tac[]
QED

Theorem in_nfa_lang_nfa_eval_alt:
  is_nfa N
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
      ‘N.initial ⊆ N.Q’ by metis_tac [is_nfa_def] >>
      gvs[nfa_eval_is_exec, EXTENSION] >> metis_tac[])
  >- (‘N.initial ⊆ N.Q’ by metis_tac [is_nfa_def] >>
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
  rw [nfa_lang_from_def,nfa_eval_def] >>
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
   is_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w
   ⇒
    nfa_lang (N with <| initial := nfa_eval N N.initial w |>)
     =
    LEFT_QUOTIENT w (nfa_lang N)
Proof
  recInduct SNOC_INDUCT >>
  rw[nfa_eval_def] >> gvs [EVERY_SNOC] >>
  rw [SNOC_APPEND,LEFT_QUOTIENT_APPEND] >>
  qpat_x_assum ‘_ = _’ sym_subst_all_tac >>
  rw [LEFT_QUOTIENT_def,EXTENSION] >>
  rename1 ‘w2 ∈ nfa_lang (N with initial := nfa_eval _ _ (w1 ++ [a]))’ >>
  ‘N.initial ⊆ N.Q’ by metis_tac [is_nfa_def] >>
  rw [nfa_eval_append] >>
  reverse (Cases_on ‘EVERY (λa. a ∈ N.Sigma) w2’) >- rw [in_nfa_lang] >>
  irule (nfa_eval_lemma |> SRULE [nfa_lang_from_def]) >> simp[] >>
  irule nfa_eval_states_closed >> simp[]
QED

Theorem REGULAR_SUBSET_FINITE_STATE:
  REGULAR ⊆ FINITE_STATE
Proof
  rw [SUBSET_DEF, IN_REGULAR_AS_NFA, FORALL_PROD, INTRINSIC_STATES_def]
  >- gvs[is_nfa_def]
  >- gvs[in_nfa_lang]
  >- (irule SUBSET_FINITE >>
      qexists_tac ‘{nfa_lang_from N qset | qset | qset ⊆ N.Q}’ >> rw[]
      >- (irule finite_image_states >> metis_tac [])
      >- (rw [SUBSET_DEF,nfa_lang_from_def] >>
          irule_at Any (GSYM nfa_lang_left_quotient) >> simp[] >>
          metis_tac [SUBSET_DEF,nfa_eval_states_closed,is_nfa_def]))
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

Theorem LEFT_QUOTIENTS_OF_CONS[local]:
  ∃t. LEFT_QUOTIENTS_OF x L = L::t
Proof
  Cases_on ‘x’ >> simp[LEFT_QUOTIENTS_OF_def]
QED

Theorem LENGTH_LEFT_QUOTIENTS_OF[local]:
  ∀x L. LENGTH (LEFT_QUOTIENTS_OF x L) = LENGTH x + 1
Proof
  Induct >> simp[LEFT_QUOTIENTS_OF_def]
QED

Theorem LAST_LEFT_QUOTIENTS_OF[local]:
  ∀x L. LAST(LEFT_QUOTIENTS_OF x L) = LEFT_QUOTIENT x L
Proof
  Induct >>
  rw[LEFT_QUOTIENTS_OF_def,LEFT_QUOTIENT_REC,LAST_CONS_cond] >>
  dty_metis_tac [LEFT_QUOTIENTS_OF_CONS]
QED

Theorem LEFT_QUOTIENTS_OF_TAKE[local]:
  ∀x n L.
    n < LENGTH x
    ⇒
    EL n (LEFT_QUOTIENTS_OF x L) = LEFT_QUOTIENT (TAKE n x) L
Proof
  Induct >> rw[LEFT_QUOTIENTS_OF_def] >>
  Cases_on ‘n’ >> gvs[LEFT_QUOTIENT_REC]
QED

Theorem EL_LEFT_QUOTIENTS_OF[local]:
  ∀x n L.
    n < LENGTH x ⇒
    EL (SUC n) (LEFT_QUOTIENTS_OF x L) =
    LEFT_QUOTIENT [EL n x] (EL n (LEFT_QUOTIENTS_OF x L))
Proof
  Induct >> rw[LEFT_QUOTIENTS_OF_def] >>
  Cases_on ‘n’ >> gvs[] >> dty_metis_tac [LEFT_QUOTIENTS_OF_CONS,HD]
QED

(*---------------------------------------------------------------------------*)
(* Encode/decode for intrinsic states                                        *)
(*---------------------------------------------------------------------------*)

Definition encode_intrinsic_state_def:
  encode_intrinsic_state = encode o INTRINSIC_STATES
End

Definition decode_intrinsic_state_def:
  decode_intrinsic_state = decode o INTRINSIC_STATES
End

Theorem codec_intrinsic_state:
  FINITE_STATE (L,A) ∧ q ∈ INTRINSIC_STATES (L,A)
  ⇒ decode_intrinsic_state (L,A)
       (encode_intrinsic_state (L,A) q) = q
Proof
  rw [decode_intrinsic_state_def,encode_intrinsic_state_def] >>
  ‘FINITE (INTRINSIC_STATES (L,A))’ by
     metis_tac [FINITE_STATE_def] >>
  dep_rewrite.DEP_REWRITE_TAC [codec] >>
  rw [INTRINSIC_STATES_def] >> metis_tac[]
QED

Theorem encode_intrinsic_state_11:
  FINITE_STATE (L,A) ∧ {q1;q2} ⊆ INTRINSIC_STATES (L,A)
  ⇒ (encode_intrinsic_state (L,A) q1 = encode_intrinsic_state (L,A) q2 ⇔ q1 = q2)
Proof
  rw [encode_intrinsic_state_def] >>
  ‘FINITE (INTRINSIC_STATES (L,A))’ by metis_tac [FINITE_STATE_def] >>
  dep_rewrite.DEP_REWRITE_TAC [encode_11] >>
  rw [IN_INTRINSIC_STATES,SUBSET_DEF] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* The states of the intrinsic-state dfa are languages, obtained by applying *)
(* left-quotient to L with each word in A*. A step in the dfa drops the      *)
(* input symbol from the head of each word in the current state, ie, does a  *)
(* left-quotient.                                                            *)
(*---------------------------------------------------------------------------*)

Definition intrinsic_dfa_def:
  intrinsic_dfa (L,A) =
    <| Sigma   := A;
       Q       := IMAGE (encode_intrinsic_state (L,A)) (INTRINSIC_STATES (L,A));
       initial := {encode_intrinsic_state (L,A) L};
       final   := IMAGE (encode_intrinsic_state (L,A))
                    {lang | lang | lang ∈ INTRINSIC_STATES (L,A) ∧ ε ∈ lang};
       delta   := (λq a. {encode_intrinsic_state (L,A)
                           (LEFT_QUOTIENT [a] (decode_intrinsic_state (L,A) q))})
    |>
End

(* Something wrong about these overloads ... maybe they need to be lambdas?

Overload "index_of"[local] = “encode_intrinsic_state (L,A)”;
Overload "lang_of"[local] = “decode_intrinsic_state (L,A)”;
*)

Theorem is_nfa_intrinsic_dfa:
  FINITE_STATE(L,A) ⇒ is_nfa (intrinsic_dfa (L,A))
Proof
  rw [FINITE_STATE_def,is_nfa_def]
  >- simp [intrinsic_dfa_def]
  >- gvs[intrinsic_dfa_def,IS_FORMAL_LANG_def]
  >- (simp [intrinsic_dfa_def,SUBSET_DEF] >>
      metis_tac [LEFT_QUOTIENT_EPSILON,EVERY_DEF])
  >- (rw [intrinsic_dfa_def,SUBSET_DEF,PULL_EXISTS] >> metis_tac []) >>
  gvs [intrinsic_dfa_def,SUBSET_DEF,PULL_EXISTS] >>
  qexists_tac ‘w ++ [a]’ >> simp[] >> AP_TERM_TAC >>
  dep_rewrite.DEP_REWRITE_TAC[codec_intrinsic_state] >>
  reverse (rw_tac std_ss [FINITE_STATE_def])
  >- metis_tac [LEFT_QUOTIENT_APPEND] >>
  simp [SUBSET_DEF,GSYM LEFT_QUOTIENT_APPEND] >>
  irule_at Any EQ_REFL >> simp [EVERY_APPEND]
QED

Theorem is_dfa_intrinsic_dfa:
  FINITE_STATE(L,A) ⇒ is_dfa (intrinsic_dfa (L,A))
Proof
  rw [is_dfa_def,is_nfa_intrinsic_dfa] >>
  simp [intrinsic_dfa_def]
QED

Theorem intrinsic_dfa_exec[local]:
  FINITE_STATE(L,A) ∧ w ∈ L
  ⇒ is_exec (intrinsic_dfa (L,A))
            (MAP (encode_intrinsic_state (L,A))
                 (LEFT_QUOTIENTS_OF w L)) w
Proof
  rw [is_exec_def]
  >- (gvs [FINITE_STATE_def,IS_FORMAL_LANG_def,SUBSET_DEF] >>
      simp [intrinsic_dfa_def])
  >- metis_tac [LENGTH_LEFT_QUOTIENTS_OF]
  >- (rw [intrinsic_dfa_def,PULL_EXISTS] >>
      ‘∃t. LEFT_QUOTIENTS_OF w L = L::t’ by metis_tac [LEFT_QUOTIENTS_OF_CONS] >>
      dep_rewrite.DEP_REWRITE_TAC[HD_MAP] >> simp [] >>
      irule_at Any (iffRL $ CONJUNCT1 EVERY_DEF) >> simp []) >>
  rw [intrinsic_dfa_def,PULL_EXISTS] >>
  ‘n+1 < LENGTH (LEFT_QUOTIENTS_OF w L)’ by rw[LENGTH_LEFT_QUOTIENTS_OF] >>
  rw [EL_MAP] >> AP_TERM_TAC >>
  dep_rewrite.DEP_REWRITE_TAC[codec_intrinsic_state] >> simp [] >>
  conj_tac
  >- (qexists_tac ‘TAKE n w’ >>
      gvs [FINITE_STATE_def,IS_FORMAL_LANG_def,SUBSET_DEF] >>
      metis_tac [LEFT_QUOTIENTS_OF_TAKE,EVERY_TAKE])
  >- metis_tac [EL_LEFT_QUOTIENTS_OF,ADD1]
QED

Theorem intrinsic_dfa_exec_states[local]:
  FINITE_STATE(L,A) ∧
  is_exec (intrinsic_dfa (L,A)) qs x ∧
  HD qs ∈ (intrinsic_dfa (L,A)).initial
  ⇒ qs = MAP (encode_intrinsic_state (L,A)) (LEFT_QUOTIENTS_OF x L)
Proof
  strip_tac >> irule LIST_EQ >>
  imp_res_tac is_exec_length >> rw[LENGTH_LEFT_QUOTIENTS_OF,EL_MAP] >>
  rename1 ‘i < LENGTH x + 1’ >>
  Induct_on ‘i’ >> rw[]
  >- (qpat_stage_tac ‘HD qs ∈ _’ >> rw [intrinsic_dfa_def] >>
      ‘∃t. LEFT_QUOTIENTS_OF x L = L::t’ by
      metis_tac [LEFT_QUOTIENTS_OF_CONS] >> simp[]) >>
  ‘i < LENGTH x + 1’ by decide_tac >> first_x_assum dxrule >>
  ‘i < LENGTH x’ by decide_tac >> drule is_exec_delta >>
  disch_then dxrule >>
  simp [EL_LEFT_QUOTIENTS_OF] >>
  rw [intrinsic_dfa_def,GSYM ADD1] >> AP_TERM_TAC >>
  dep_rewrite.DEP_REWRITE_TAC[codec_intrinsic_state] >> simp[] >>
  irule_at Any LEFT_QUOTIENTS_OF_TAKE >> simp [] >>
  drule is_exec_Sigma >> simp [intrinsic_dfa_def] >>
  metis_tac [EVERY_TAKE]
QED

Theorem FINITE_STATE_SUBSET_REGULAR:
  FINITE_STATE ⊆ REGULAR
Proof
  simp [SUBSET_DEF,IN_DEF] >>
  Cases >> strip_tac >> imp_res_tac is_nfa_intrinsic_dfa >>
  rename1 ‘FINITE_STATE(L,A)’ >> simp [Once $ GSYM SPECIFICATION] >>
  rw [IN_REGULAR_AS_NFA] >>
  qexists_tac ‘intrinsic_dfa(L,A)’ >>
  conj_tac >- rw [intrinsic_dfa_def] >>
  conj_tac >- metis_tac [] >>
  rw [EXTENSION,EQ_IMP_THM,in_nfa_lang_iff_accepting_exec]
  >- (qexists_tac‘MAP (encode_intrinsic_state(L,A)) (LEFT_QUOTIENTS_OF x L)’ >>
      rw[is_accepting_exec_def]
      >- metis_tac [intrinsic_dfa_exec]
      >- (‘∃t. LEFT_QUOTIENTS_OF x L = L::t’ by
             metis_tac [LEFT_QUOTIENTS_OF_CONS] >>
          dep_rewrite.DEP_REWRITE_TAC[HD_MAP] >> rw [intrinsic_dfa_def])
      >- (‘∃t. LEFT_QUOTIENTS_OF x L = L::t’ by
             metis_tac [LEFT_QUOTIENTS_OF_CONS] >>
          dep_rewrite.DEP_REWRITE_TAC[LAST_MAP] >>
          rw [intrinsic_dfa_def,PULL_EXISTS,GSYM LEFT_QUOTIENT_ELT] >>
          first_assum (irule_at Any) >> conj_tac
          >- (AP_TERM_TAC >> metis_tac[LAST_LEFT_QUOTIENTS_OF])
          >- gvs [FINITE_STATE_def,IS_FORMAL_LANG_def,SUBSET_DEF])) >>
  gvs [is_accepting_exec_def] >>
  simp [Once LEFT_QUOTIENT_ELT] >>
  imp_res_tac intrinsic_dfa_exec_states >> rw [] >>
  ‘LEFT_QUOTIENTS_OF x L ≠ []’ by metis_tac [LEFT_QUOTIENTS_OF_nonempty] >>
  gvs [LAST_MAP,LAST_LEFT_QUOTIENTS_OF] >>
  qpat_stage_tac ‘_ ∈ (intrinsic_dfa (L,A)).final’ >> rw[intrinsic_dfa_def] >>
  qpat_stage_tac ‘_ = _’ >>
  dep_rewrite.DEP_REWRITE_TAC[encode_intrinsic_state_11] >> simp [] >>
  ‘(intrinsic_dfa (L,A)).Sigma = A’ by simp [intrinsic_dfa_def] >>
  metis_tac [is_exec_Sigma]
QED

Theorem FINITE_STATE_EQ_REGULAR:
  FINITE_STATE = REGULAR
Proof
  metis_tac[SET_EQ_SUBSET,
       REGULAR_SUBSET_FINITE_STATE,
       FINITE_STATE_SUBSET_REGULAR]
QED

(*===========================================================================*)
(* Myhill-Nerode theorem                                                     *)
(*===========================================================================*)

Definition nfa_eval_equiv_def:
  nfa_eval_equiv N x y ⇔
     x ∈ KSTAR{[a] | a ∈ N.Sigma} ∧
     y ∈ KSTAR{[a] | a ∈ N.Sigma} ∧
     (nfa_eval N N.initial x = nfa_eval N N.initial y)
End

Definition lang_equiv_def:
  lang_equiv (L,A) x y ⇔
    x ∈ KSTAR{[a] | a ∈ A} ∧
    y ∈ KSTAR{[a] | a ∈ A} ∧
   (∀z. z ∈ KSTAR{[a] | a ∈ A} ⇒ (x ++ z ∈ L ⇔ y ++ z ∈ L))
End

Theorem nfa_eval_equiv_refines_lang_equiv[local]:
  is_nfa N ∧ nfa_eval_equiv N x y
  ⇒
  lang_equiv (nfa_lang N,N.Sigma) x y
Proof
  rw[nfa_eval_equiv_def,lang_equiv_def] >>
  rw [in_nfa_lang_nfa_eval] >>
  ‘N.initial ⊆ N.Q’ by metis_tac [is_nfa_def] >>
  rw [nfa_eval_append]
QED

Theorem equiv_on_lang_equiv:
  lang_equiv(L,A) equiv_on KSTAR{[a] | a ∈ A}
Proof
  rw[equiv_on_def,lang_equiv_def] >> metis_tac[]
QED

Theorem lang_equiv_refl:
 EVERY (λa. a ∈ A) x ⇒ lang_equiv(L,A) x x
Proof
  mp_tac equiv_on_lang_equiv >> rw [equiv_on_def]
QED

Theorem lang_equiv_sym:
  EVERY (λa. a ∈ A) x ∧ EVERY (λa. a ∈ A) y ∧ lang_equiv(L,A) x y
  ⇒ lang_equiv(L,A) y x
Proof
  mp_tac equiv_on_lang_equiv >> rw [equiv_on_def]
QED

Theorem lang_equiv_trans:
  EVERY (λa. a ∈ A) x ∧ EVERY (λa. a ∈ A) y ∧ EVERY (λa. a ∈ A) z ∧
  lang_equiv(L,A) x y ∧ lang_equiv(L,A) y z
  ⇒ lang_equiv(L,A) x z
Proof
  rw [] >> mp_tac equiv_on_lang_equiv >>
  rw [equiv_on_def] >> metis_tac[]
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
  is_nfa N ⇒
  right_invar (KSTAR{[a] | a ∈ N.Sigma}) (nfa_eval_equiv N)
Proof
  rw[right_invar_def,nfa_eval_equiv_def] >>
  ‘N.initial ⊆ N.Q’ by metis_tac[is_nfa_def] >>
  rw[nfa_eval_append]
QED

(*---------------------------------------------------------------------------*)
(* Lemmas on partitions                                                      *)
(*---------------------------------------------------------------------------*)

Theorem partition_def_alt:
  partition R s = {equiv_class R s x | x | x ∈ s}
Proof
  rw[EXTENSION,partition_def,EQ_IMP_THM,PULL_EXISTS] >> metis_tac[]
QED

Theorem partition_def_as_image:
  partition R s = IMAGE (λx y. y ∈ s ∧ R x y) s
Proof
  rw[partition_def_alt,GSPEC_IMAGE,combinTheory.o_DEF] >>
  simp[IN_DEF,ETA_THM]
QED

Theorem in_partition[local]:
  class ∈ partition R s ⇔
   ∃x. x ∈ s ∧ ∀y. y ∈ class ⇔ y ∈ s ∧ R x y
Proof
  rw [partition_def,EQ_IMP_THM,EXTENSION]
QED

Theorem in_partition_alt[local]:
  class ∈ partition R s ⇔ ∃x. x ∈ s ∧ class = equiv_class R s x
Proof
  rw [partition_def,EQ_IMP_THM,EXTENSION]
QED

Theorem partition_empty[local]:
  partition R s = ∅ ⇔ s = ∅
Proof
  rw [EQ_IMP_THM]
  >- (gvs [EXTENSION,in_partition] >>
      gen_tac >> disch_tac >> gvs [GSYM IMP_DISJ_THM] >>
      first_x_assum drule >> simp[] >>
      qexists_tac ‘equiv_class R s x’ >> simp[])
  >- simp[partition_def]
QED

Theorem kstar_partition_inhab_word[local]:
  E equiv_on (KSTAR{[a] | a ∈ A}) ∧
  class ∈ partition E (KSTAR{[a] | a ∈ A}) ⇒
  ∃w. w ∈ class ∧ equiv_class E (KSTAR{[a] | a ∈ A}) w = class
Proof
  rw[in_partition_alt] >> qexists_tac ‘x’ >> gvs[equiv_on_def]
QED

Theorem partition_elts:
  R equiv_on s ∧
  t1 ∈ partition R s ∧
  t2 ∈ partition R s ∧
  w ∈ t1 ∧ w ∈ t2 ⇒ t1 = t2
Proof
  rw [in_partition_alt] >>
  gvs[EXTENSION,equiv_on_def] >>
  rw [EQ_IMP_THM] >> metis_tac[]
QED

Theorem partition_emptylang[local]:
  partition (lang_equiv({},A)) (KSTAR{[a] | a ∈ A}) = {KSTAR{[a] | a ∈ A}}
Proof
  simp [EXTENSION, in_partition, lang_equiv_def] >>
  rw [EQ_IMP_THM]
  >- metis_tac[]
  >- metis_tac[]
  >- (qexists_tac ‘ε’ >> rw[])
QED

(*---------------------------------------------------------------------------*)
(* The set of words that evaluate to the given state. M will be a DFA.       *)
(*---------------------------------------------------------------------------*)

Definition words_of_state_def:
  words_of_state M q =
   {w | w ∈ KSTAR {[a] | a ∈ M.Sigma} ∧ nfa_eval M M.initial w = {q}}
End

Theorem in_words_of_state:
  w ∈ words_of_state M q
   ⇔
  EVERY (λa. a ∈ M.Sigma) w ∧ nfa_eval M M.initial w = {q}
Proof
  rw[words_of_state_def]
QED

Theorem words_of_state_in_partition[local]:
  EVERY (λa. a ∈ M.Sigma) x ∧
  nfa_eval M M.initial x = {q}
  ⇒
  words_of_state M q ∈ partition(nfa_eval_equiv M) (KSTAR {[a] | a ∈ M.Sigma})
Proof
  rw[words_of_state_def,partition_def_alt] >>
  qexists_tac ‘x’ >>
  rw [nfa_eval_equiv_def,EXTENSION] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Create an injective map from E-classes to machine states                  *)
(*                                                                           *)
(* state_of_class_def:                                                       *)
(*  |- ∀M. is_dfa M ⇒                                                        *)
(*         ∀class.                                                           *)
(*           class ∈ partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}) *)
(*           ⇒                                                               *)
(*           state_of_class M class ∈ M.Q ∧                                  *)
(*           class = words_of_state M (state_of_class M class)               *)
(*---------------------------------------------------------------------------*)

Theorem state_of_class_witness[local]:
  ∃state_of_class.
    ∀M. is_dfa M ⇒
        ∀class.
         class ∈ partition (nfa_eval_equiv M) (KSTAR {[a] | a ∈ M.Sigma})
         ⇒
         state_of_class M class ∈ M.Q ∧
         class = words_of_state M (state_of_class M class)
Proof
  rw[GSYM SKOLEM_THM,PUSH_EXISTS] >>
  gvs [partition_def_alt] >>
  rename1 ‘EVERY (λa. a ∈ M.Sigma) w’ >>
  rw [words_of_state_def] >>
  ‘∃q. nfa_eval M M.initial w = {q}’ by
     metis_tac [dfa_eval_final_state] >>
  rw [nfa_eval_equiv_def] >>
  qexists_tac ‘q’ >> rw [EXTENSION] >>
  metis_tac [dfa_eval_states_closed]
QED

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

Theorem state_of_class_words_of_state_id[local]:
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
(* The "nfa-eval"-partition is finite because state_of_class is an injection *)
(* from the partition into the (finite) set of states.                       *)
(*---------------------------------------------------------------------------*)

Theorem finite_nfa_eval_equiv_partition:
  is_dfa M ⇒
  FINITE (partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma}))
Proof
  strip_tac >>
  irule (FINITE_INJ
           |> INST_TYPE [alpha |-> “:'a list set”,beta |-> “:state”]) >>
  simp[Once SWAP_EXISTS_THM] >>
  qexists_tac ‘{q | q ∈ M.Q ∧
                words_of_state M q ∈
                  partition (nfa_eval_equiv M) (KSTAR{[a] | a ∈ M.Sigma})}’ >>
  qexists_tac ‘state_of_class M’ >> conj_tac
  >- (irule SUBSET_FINITE >> qexists_tac ‘M.Q’ >>
      gvs [is_dfa_def,is_nfa_def, SUBSET_DEF])
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
      >- (simp [EXTENSION] >> ‘is_nfa M’ by metis_tac [is_dfa_def] >>
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

(*---------------------------------------------------------------------------*)
(* Every right-invariant equivalence on A* is a refinement of language       *)
(* equivalence.                                                              *)
(*---------------------------------------------------------------------------*)

Theorem lang_equiv_refinement:
  E equiv_on (KSTAR{[a] | a ∈ A}) ∧
  right_invar (KSTAR{[a] | a ∈ A}) E ∧
  classes ⊆ partition E (KSTAR{[a] | a ∈ A}) ∧
  x ∈ KSTAR{[a] | a ∈ A} ∧
  y ∈ KSTAR{[a] | a ∈ A} ∧
  E x y
   ⇒
  lang_equiv (BIGUNION classes,A) x y
Proof
  rw[] >> gvs [right_invar_def] >>
  ‘∀z. EVERY (λa. a ∈ A) z ⇒ E (x ⧺ z) (y ⧺ z)’ by
      (gvs [right_invar_def] >> metis_tac[]) >>
  rw[lang_equiv_def] >>
  ‘E (x++z) (y++z)’ by metis_tac[] >>
  rw[EQ_IMP_THM] >> qexists_tac ‘s’ >> simp[] >>
  ‘s ∈ partition E (KSTAR {[a] | a ∈ A})’ by
     metis_tac [SUBSET_DEF] >> pop_keep_tac >>
  rw[in_partition]
     >- (‘EVERY (λa. a ∈ A) (x++z) ∧ E x' (x++z)’ by metis_tac[] >>
         simp[] >> qpat_x_assum ‘_ equiv_on _’ mp_tac >>
         simp[equiv_on_def] >>
         disch_then (irule o last o CONJUNCTS) >> rw[] >>
         first_x_assum (irule_at Any) >> simp[])
     >- (‘EVERY (λa. a ∈ A) (y++z) ∧ E x' (y++z)’ by metis_tac[] >>
         simp[] >> qpat_x_assum ‘_ equiv_on _’ mp_tac >>
         simp[equiv_on_def] >> strip_tac >>
         pop_assum irule >> simp[] >>
         qexists_tac ‘y ++ z’ >> simp[])
QED

Theorem equiv_class_subset:
  E equiv_on (KSTAR{[a] | a ∈ A}) ∧
  right_invar (KSTAR{[a] | a ∈ A}) E ∧
  classes ⊆ partition E (KSTAR{[a] | a ∈ A}) ∧
  w ∈ KSTAR{[a] | a ∈ A}
  ⇒
  equiv_class E (KSTAR{[a] | a ∈ A}) w ⊆
  equiv_class (lang_equiv(BIGUNION classes,A)) (KSTAR{[a] | a ∈ A}) w
Proof
  rw[SUBSET_DEF, EXTENSION] >>
  irule lang_equiv_refinement >> rw[] >>
  rpt (first_assum (irule_at Any)) >>
  metis_tac [SUBSET_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Create an injective map from L-classes to (some) E-classes                *)
(*                                                                           *)
(* E_class_def:                                                              *)
(* |- ∀A E classes class'.                                                   *)
(*     E equiv_on KSTAR{[a] | a ∈ A} ∧                                       *)
(*     right_invar (KSTAR {[a] | a ∈ A}) E ∧                                 *)
(*     classes ⊆ partition E (KSTAR {[a] | a ∈ A}) ∧                         *)
(*     class' ∈ partition                                                    *)
(*                (lang_equiv (BIGUNION classes,A)) (KSTAR {[a] | a ∈ A})    *)
(*     ==>                                                                   *)
(*     E_class A E classes class' ∈ partition E (KSTAR {[a] | a ∈ A}) ∧      *)
(*     E_class A E classes class' ⊆ class'                                   *)
(*---------------------------------------------------------------------------*)

Theorem E_class_witness[local]:
  ∃E_part.
    ∀A E classes class'.
     E equiv_on (KSTAR{[a] | a ∈ A}) ∧
     right_invar (KSTAR{[a] | a ∈ A}) E ∧
     classes ⊆ partition E (KSTAR{[a] | a ∈ A}) ∧
     class' ∈ partition (lang_equiv(BIGUNION classes,A)) (KSTAR{[a] | a ∈ A})
     ⇒
     E_part A E classes class' ∈ partition E (KSTAR{[a] | a ∈ A}) ∧
     E_part A E classes class' ⊆ class'
Proof
  rw [GSYM SKOLEM_THM,PUSH_EXISTS] >>
  ‘lang_equiv (BIGUNION classes,A) equiv_on KSTAR{[a] | a ∈ A}’ by
     metis_tac[equiv_on_lang_equiv] >>
  drule_all kstar_partition_inhab_word >> strip_tac >>
  ‘w ∈ KSTAR{[a] | a ∈ A}’ by
    gvs [in_partition_alt] >>
  drule_all equiv_class_subset >> ASM_REWRITE_TAC[] >> disch_tac >>
  first_x_assum (irule_at Any) >> rw[in_partition_alt] >>
  gvs[] >> metis_tac[]
QED

val E_class_def =
  new_specification ("E_class_def", ["E_class"], E_class_witness);

Theorem E_class_inj:
  E equiv_on (KSTAR{[a] | a ∈ A}) ∧
  right_invar (KSTAR{[a] | a ∈ A}) E ∧
  classes ⊆ partition E (KSTAR{[a] | a ∈ A}) ∧
  class1 ∈ partition (lang_equiv (BIGUNION classes,A)) (KSTAR {[a] | a ∈ A}) ∧
  class2 ∈ partition (lang_equiv (BIGUNION classes,A)) (KSTAR {[a] | a ∈ A}) ∧
  E_class A E classes class1 = E_class A E classes class2
  ⇒
  class1 = class2
Proof
  rw[] >>
  drule_all E_class_def >> rev_drule_all E_class_def >> rw[] >>
  Cases_on ‘class1 = class2’ >> rw[] >>
  ‘lang_equiv (BIGUNION classes,A) equiv_on KSTAR{[a] | a ∈ A}’ by
     metis_tac[equiv_on_lang_equiv] >>
  drule_all partition_elements_disjoint >> pop_forget_tac >>
  drule_all kstar_partition_inhab_word >> strip_tac >> pop_forget_tac >>
  ‘w ∈ class1 ∧ w ∈ class2’ by
    metis_tac[SUBSET_DEF] >> rw[DISJOINT_DEF,EXTENSION] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* The injection is into a subset of the E-partition, which is finite. Thus  *)
(* the source L-partition is finite. NB: one can become confused about the   *)
(* role of the "classes" subset of the E-partition, but it doesn't figure at *)
(* this stage of the argument. (It is only needed in the crucial             *)
(* lang_equiv_refinement lemma.)                                             *)
(*---------------------------------------------------------------------------*)

Theorem Myhill_Nerode_B:
  E equiv_on (KSTAR{[a] | a ∈ A}) ∧
  right_invar (KSTAR{[a] | a ∈ A}) E ∧
  FINITE (partition E (KSTAR{[a] | a ∈ A})) ∧
  classes ⊆ partition E (KSTAR{[a] | a ∈ A}) ∧
  L = BIGUNION classes
   ⇒
  FINITE (partition (lang_equiv(L,A)) (KSTAR{[a] | a ∈ A}))
Proof
  rw[] >>
  irule (iffLR
    (FINITE_IMAGE_INJ_EQ
       |> Q.ISPEC ‘f : (α list -> bool) -> (α list -> bool)’)) >>
  qexists_tac ‘E_class A E classes’ >> rw[]
  >- (irule E_class_inj >> metis_tac[])
  >- (irule finite_image_range >>
      first_x_assum (irule_at Any) >> rw[E_class_def])
QED

(*---------------------------------------------------------------------------*)
(* Encode/decode for lang_equiv classes                                      *)
(*---------------------------------------------------------------------------*)

Definition classes_of_def:
  classes_of (L,A) = partition (lang_equiv (L,A)) (KSTAR {[a] | a ∈ A})
End

Definition class_of_def:
  class_of(L,A) u = equiv_class (lang_equiv (L,A)) (KSTAR {[a] | a ∈ A}) u
End

Theorem class_of_in_classes:
  EVERY (λa. a ∈ A) w ⇒ class_of (L,A) w ∈ classes_of (L,A)
Proof
  rw [in_partition_alt, classes_of_def, class_of_def] >> metis_tac[]
QED

Definition encode_class_def:
  encode_class = encode o classes_of
End

Definition decode_class_def:
  decode_class = decode o classes_of
End

Theorem codec_class:
  FINITE (classes_of(L,A)) ∧ class ∈ classes_of(L,A)
  ⇒ decode_class(L,A) (encode_class(L,A) class) = class
Proof
  rw [decode_class_def,encode_class_def] >>
  irule codec >> metis_tac[]
QED

Theorem encode_class_11:
  FINITE (classes_of(L,A)) ∧ {c1;c2} ⊆ classes_of(L,A)
  ⇒ ((encode_class(L,A) c1 = encode_class(L,A) c2) ⇔ (c1 = c2))
Proof
  rw [encode_class_def] >> irule encode_11 >> simp[SUBSET_DEF]
QED

(*---------------------------------------------------------------------------*)
(* The Myhill-Nerode machine. States are lang-equiv classes partitioning A*  *)
(* and transitions are made by appending the input symbol to any word in the *)
(* current state and finding the class of the resulting word.                *)
(*---------------------------------------------------------------------------*)

Definition mn_dfa_def:
  mn_dfa (L,A) =
   <| Sigma := A;
          Q := IMAGE (encode_class(L,A)) (classes_of (L,A));
       initial := {encode_class(L,A) (class_of(L,A) ε)};
       final   := IMAGE (encode_class(L,A) o class_of(L,A)) L;
       delta   := (λnq a. {encode_class(L,A)
                            (class_of(L,A)
                               ((@w. w ∈ decode_class(L,A) nq) ++ [a]))})
  |>
End

Theorem mn_dfa_builtin_simps[simp]:
  (mn_dfa(L,A)).Sigma = A ∧
  (mn_dfa(L,A)).Q = IMAGE (encode_class(L,A)) (classes_of (L,A)) ∧
  (mn_dfa(L,A)).initial = {encode_class(L,A) (class_of(L,A) ε)} ∧
  (mn_dfa(L,A)).final = IMAGE (encode_class(L,A) o class_of(L,A)) L
Proof
  rw[mn_dfa_def]
QED

Theorem is_nfa_mn_dfa:
  IS_FORMAL_LANG(L,A) ∧ FINITE (classes_of(L,A))
  ⇒ is_nfa (mn_dfa(L,A))
Proof
  rw [is_nfa_def, mn_dfa_def]
  >- metis_tac [IS_FORMAL_LANG_def]
  >- metis_tac [class_of_in_classes,EVERY_DEF]
  >- (rw [SUBSET_DEF] >> irule_at Any EQ_REFL >>
      gvs [IS_FORMAL_LANG_def,SUBSET_DEF] >>
      metis_tac[class_of_in_classes]) >>
  rename1 ‘class ∈ classes_of (L,A)’ >>
  dep_rewrite.DEP_REWRITE_TAC[codec_class] >> simp [] >>
  irule_at Any EQ_REFL >>
  SELECT_ELIM_TAC >> conj_tac
  >- metis_tac [classes_of_def,kstar_partition_inhab_word, equiv_on_lang_equiv]
  >- (rw [] >> irule class_of_in_classes >>
      gvs [in_partition_alt, classes_of_def, class_of_def])
QED

Theorem is_dfa_mn_dfa:
  IS_FORMAL_LANG(L,A) ∧ FINITE (classes_of(L,A))
  ⇒ is_dfa (mn_dfa(L,A))
Proof
  rw [is_dfa_def,is_nfa_mn_dfa,mn_dfa_def]
QED

Theorem nfa_eval_mn_dfa:
  is_nfa (mn_dfa(L,A)) ∧ FINITE (classes_of(L,A))
  ⇒
   ∀x y. x ∈ KSTAR {[a] | a ∈ A} ∧ y ∈ KSTAR {[a] | a ∈ A}
         ⇒ nfa_eval (mn_dfa(L,A)) {encode_class(L,A)(class_of(L,A) x)} y =
           {encode_class(L,A) (class_of(L,A) (x++y))}
Proof
  strip_tac >> gen_tac >>
  recInduct SNOC_INDUCT >>
  rw[SNOC_APPEND,nfa_eval_def] >>
  dep_rewrite.DEP_REWRITE_TAC [nfa_eval_append] >>
  conj_tac >-
    (simp [mn_dfa_def] >>
     irule_at Any EQ_REFL >> metis_tac [class_of_in_classes]) >>
  rw [] >> qpat_forget_tac ‘_ ⇒ _’ >> rename1 ‘a ∈ A’ >>
  ‘∃w. x ++ l = w ∧ EVERY (λa. a ∈ A) w’ by
      (irule_at Any EQ_REFL >> simp []) >>
  qpat_forget_tac ‘EVERY _ x’ >>
  qpat_forget_tac ‘EVERY _ l’ >>
  qpat_x_assum ‘_ = _’ subst_all_tac >>
  rw[nfa_eval_def] >>
  rw [GSPEC_IMAGE, o_DEF, BIGUNION_IMAGE] >>
  simp [EXTENSION,PULL_EXISTS] >>
  rw [mn_dfa_def] >>
  dep_rewrite.DEP_REWRITE_TAC[codec_class] >>
  simp [class_of_in_classes] >>
  ntac 2 AP_TERM_TAC >> SELECT_ELIM_TAC >> rw[]
  >- (rw [class_of_def] >> metis_tac [lang_equiv_refl]) >>
  dep_rewrite.DEP_REWRITE_TAC[class_of_def,equiv_class_eq] >>
  rw [equiv_on_lang_equiv] >> gvs [class_of_def] >>
  irule $ iffLR right_invar_def >> conj_tac
  >- metis_tac [lang_equiv_sym]
  >- (irule_at Any right_invar_lang_equiv >> rw[])
QED

Theorem Myhill_Nerode_C:
  IS_FORMAL_LANG(L,A) ∧ FINITE (classes_of(L,A)) ⇒ (L,A) ∈ REGULAR
Proof
  rw[IN_REGULAR_AS_NFA] >>
  imp_res_tac is_nfa_mn_dfa >>
  qexists_tac ‘mn_dfa(L,A)’ >>
  simp [EXTENSION, in_nfa_lang_nfa_eval_alt] >>
  rw [PULL_EXISTS,EQ_IMP_THM]
  >- (‘x ∈ KSTAR {[a] | a ∈ A}’ by metis_tac [IS_FORMAL_LANG_def,SUBSET_DEF] >>
      dep_rewrite.DEP_REWRITE_TAC[nfa_eval_mn_dfa] >> gvs [] >>
      metis_tac[]) >>
  pop_keep_tac >> rename1 ‘y ∈ L ⇒ x ∈ L’ >> disch_tac >>
  ‘y ∈ KSTAR {[a] | a ∈ A}’ by metis_tac [IS_FORMAL_LANG_def,SUBSET_DEF] >> fs [] >>
  qpat_stage_tac ‘encode_class _ _ ∈ _’ >>
  dep_rewrite.DEP_REWRITE_TAC[nfa_eval_mn_dfa] >> simp [] >>
  dep_rewrite.DEP_REWRITE_TAC[encode_class_11] >> conj_tac
  >- gvs [class_of_in_classes] >>
  simp [class_of_def,EXTENSION] >>
  disch_then (mp_tac o Q.SPEC ‘x’) >>
  simp [lang_equiv_refl] >>
  simp [lang_equiv_def] >> metis_tac [APPEND_NIL,EVERY_DEF]
QED

Theorem Myhill_Nerode:
  IS_FORMAL_LANG (L,A)
  ⇒
  ((L,A) ∈ REGULAR ⇔ FINITE (classes_of(L,A)))
Proof
  metis_tac [Myhill_Nerode_A, Myhill_Nerode_B, Myhill_Nerode_C,classes_of_def]
QED

(*===========================================================================*)
(* DFA state minimization. This is accomplished by removing all              *)
(* non-accessible states, then coalescing all non-distinguishable states.    *)
(* Both of these operations preserve the language originally recognized.     *)
(*===========================================================================*)

Definition accessible_states_def:
  accessible_states M =
     {q | ∃w. w ∈ KSTAR {[a] | a ∈ M.Sigma} ∧
              nfa_eval M M.initial w = {q}}
End

Definition accessible_nfa_def:
  accessible_nfa M ⇔ M.Q ⊆ accessible_states M
End

Theorem accessible_states_subset:
  is_nfa M ⇒ accessible_states M ⊆ M.Q
Proof
  rw[accessible_states_def,SUBSET_DEF] >>
  REWRITE_TAC[ELT_SUBSET] >> pop_sym_subst_tac >>
  irule nfa_eval_states_closed >>
  metis_tac[is_nfa_def]
QED

Theorem nfa_eval_subset_accessible:
  is_dfa M ∧ w ∈ KSTAR {[a] | a ∈ M.Sigma}
  ⇒
  nfa_eval M M.initial w ⊆ accessible_states M
Proof
  rw[accessible_states_def,SUBSET_DEF] >>
  drule_all dfa_eval_final_state >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem initial_subset_accessible:
  is_dfa M ⇒ M.initial ⊆ accessible_states M
Proof
  strip_tac >>
  ‘ε ∈ KSTAR {[a] | a ∈ M.Sigma}’ by rw[] >>
  metis_tac [nfa_eval_def,nfa_eval_subset_accessible]
QED

(*---------------------------------------------------------------------------*)
(* Remove inaccessible states from a DFA                                     *)
(*---------------------------------------------------------------------------*)

Definition mk_accessible_def:
  mk_accessible M =
    M with
      <| Q := accessible_states M;
         final := M.final ∩ accessible_states M |>
End

Theorem mk_accessible_simps[simp]:
  (mk_accessible M).Q = accessible_states M ∧
  (mk_accessible M).final = (M.final ∩ accessible_states M) ∧
  (mk_accessible M).initial = M.initial ∧
  (mk_accessible M).Sigma = M.Sigma ∧
  (mk_accessible M).delta = M.delta
Proof
  rw [mk_accessible_def]
QED

Theorem is_dfa_mk_accessible:
  is_dfa M ⇒ is_dfa (mk_accessible M)
Proof
  rw [mk_accessible_def] >> reverse (rw [is_dfa_def])
  >- (gvs [accessible_states_def,is_dfa_def] >>
      first_x_assum irule >> simp[] >>
      irule (nfa_eval_states_closed |> SRULE[SUBSET_DEF]) >>
      rw[] >> qexists_tac ‘{q_0}’ >> qexists_tac ‘w’ >> rw[] >>
      metis_tac [ELT_SUBSET,is_nfa_def])
  >-  metis_tac [is_dfa_def]
  >- (gvs [is_dfa_def] >> rw [is_nfa_def]
      >- (irule SUBSET_FINITE >>
          metis_tac [accessible_states_subset,is_nfa_def])
      >- metis_tac [is_nfa_def]
      >- metis_tac [ELT_SUBSET,initial_subset_accessible,is_dfa_def]
      >- (‘q ∈ M.Q’ by
             metis_tac [SUBSET_DEF, accessible_states_subset] >>
          ‘∃q'. M.delta q a = {q'}’ by
            metis_tac[] >>
          gvs [accessible_states_def] >>
          qexists_tac ‘w ++ [a]’ >> rw[] >>
          dep_rewrite.DEP_REWRITE_TAC [nfa_eval_append] >>
          rw[]
          >- metis_tac [ELT_SUBSET,is_nfa_def]
          >- (rw [nfa_eval_def] >> simp [gspec_lemma])))
QED

Theorem nfa_eval_mk_accessible:
  is_dfa M
   ⇒
   ∀w. EVERY (λa. a ∈ M.Sigma) w ⇒
       nfa_eval (mk_accessible M) M.initial w = nfa_eval M M.initial w
Proof
  disch_tac >>
  ‘is_dfa (mk_accessible M) ∧ is_nfa M ∧ is_nfa (mk_accessible M)’ by
     metis_tac[is_dfa_mk_accessible,is_dfa_def] >>
  recInduct (SNOC_INDUCT |> SRULE [SNOC_APPEND]) >> rw[]
  >- rw[nfa_eval_def] >>
  rename [‘a ∈ M.Sigma’, ‘EVERY (λa. a ∈ M.Sigma) w’] >> gvs[] >>
  dep_rewrite.DEP_REWRITE_TAC [nfa_eval_append] >> rw[]
  >- metis_tac[initial_subset_accessible]
  >- metis_tac [is_nfa_def]
  >- (drule_all dfa_eval_final_state >> rw[] >> rw[] >>
      simp [nfa_eval_def])
QED

Theorem dfa_mk_accessible_is_accessible:
  is_dfa M ⇒ accessible_nfa (mk_accessible M)
Proof
  rw [accessible_nfa_def,SUBSET_DEF] >>
  rename1 ‘q ∈ accessible_states M’ >>
  gvs [accessible_states_def] >>
  first_assum (irule_at Any) >>
  metis_tac [nfa_eval_mk_accessible]
QED

Theorem nfa_lang_mk_accessible:
  is_dfa M ⇒ nfa_lang (mk_accessible M) = nfa_lang M
Proof
  rw [EXTENSION] >>
  dep_rewrite.DEP_REWRITE_TAC [in_nfa_lang_nfa_eval_alt] >> rw[]
  >- metis_tac [is_dfa_mk_accessible,is_dfa_def]
  >- metis_tac [is_dfa_def]
  >- (rw [EQ_IMP_THM,EXTENSION]
      >- metis_tac [nfa_eval_mk_accessible]
      >- (rw [nfa_eval_mk_accessible] >>
          rpt (first_assum (irule_at Any)) >>
          drule_all (nfa_eval_subset_accessible |> SRULE[]) >>
          metis_tac[ELT_SUBSET,SUBSET_TRANS]))
QED

(*---------------------------------------------------------------------------*)
(* Sub-automata and automata isomorphism (equivalence up to renaming of      *)
(* states).                                                                  *)
(*---------------------------------------------------------------------------*)

Definition preserves_nfa_structure_def:
  preserves_nfa_structure fn N1 N2 ⇔
    (∀q. q ∈ N1.initial ⇔ fn q ∈ N2.initial) ∧
    (∀q. q ∈ N1.final ⇔ fn q ∈ N2.final) ∧
    (∀q1 q2 a. q1 ∈ N1.Q ∧ a ∈ N1.Sigma ⇒
               (q2 ∈ N1.delta q1 a ⇔ fn q2 ∈ N2.delta (fn q1) a))
End

Definition sub_nfa_def:
  sub_nfa N1 N2 ⇔
    N1.Sigma = N2.Sigma ∧
    ∃fn. INJ fn N1.Q N2.Q ∧
         preserves_nfa_structure fn N1 N2
End

Definition isomorphic_nfas_def:
  isomorphic_nfas N1 N2 ⇔
    N1.Sigma = N2.Sigma ∧
    ∃fn. INJ fn N1.Q N2.Q ∧
         preserves_nfa_structure fn N1 N2 ∧
         preserves_nfa_structure (LINV fn N1.Q) N2 N1
End

Theorem finite_inj_inj_bij:
  FINITE s ∧ FINITE t ∧
  INJ f s t ∧ INJ g t s ⇒ BIJ f s t
Proof
  rw [] >>
  drule_all INJ_CARD >>
  rev_drule_all INJ_CARD >> rw[] >>
  ‘CARD s = CARD t’ by decide_tac >>
  irule FINITE_SURJ_BIJ >> rw[] >>
  ‘IMAGE f s ⊆ t’ by
    (gvs [SUBSET_DEF,INJ_DEF] >> rw[] >> metis_tac[]) >>
  drule_all SURJECTIVE_IFF_INJECTIVE_GEN >>
  gvs [INJ_DEF] >> rw[SURJ_DEF]
QED

(*
Theorem sub_nfas_initial:
  is_nfa N1 ∧ is_nfa N2 ∧
  sub_nfa N1 N2 ∧ sub_nfa N2 N1
  ⇒
  CARD N1.initial = CARD N2.initial
Proof
  rw [sub_nfa_def] >>
  qpat_forget_tac ‘_ = _’ >>
  rw[isomorphic_nfas_def] >>
  pop_forget_tac >>
  rpt (first_assum (irule_at Any)) >>
  ‘BIJ fn N1.Q N2.Q’ by
    metis_tac [is_nfa_def,finite_inj_inj_bij] >>
  drule BIJ_LINV_INV >>
  gvs [preserves_nfa_structure_def] >> rw[]
  >- (rw [EQ_IMP_THM]
      >- metis_tac[is_nfa_def,SUBSET_DEF]
      >- (qabbrev_tac ‘a = LINV fn N1.Q q’ >>
          ‘a ∈ N1.initial’ by metis_tac[] >>
QED

Theorem finite_initial_final[local,simp]:
  is_nfa N ⇒ FINITE N.initial ∧ FINITE N.final
Proof
  metis_tac [is_nfa_def,SUBSET_FINITE]
QED

STOP

Theorem sub_nfas_isomorphic:
  is_nfa N1 ∧ is_nfa N2 ∧
  sub_nfa N1 N2 ∧ sub_nfa N2 N1
  ⇒
  isomorphic_nfas N1 N2
Proof
  rw [sub_nfa_def] >>
  qpat_forget_tac ‘_ = _’ >>
  rw[isomorphic_nfas_def] >>
  pop_forget_tac >>
  rpt (first_assum (irule_at Any)) >>
  ‘BIJ fn N1.Q N2.Q’ by
    metis_tac [is_nfa_def,finite_inj_inj_bij] >>
  rw[preserves_nfa_structure_def]
  drule BIJ_LINV_INV
  >- (‘N2.initial = IMAGE fn N1.initial’ by
        (gvs [preserves_nfa_structure_def] >>
         reverse (rw[EXTENSION,EQ_IMP_THM])
         >- metis_tac[] >>
         drule BIJ_LINV_INV >>
         ‘x ∈ N2.Q’ by metis_tac[is_nfa_def,SUBSET_DEF] >>
         disch_then drule >> metis_tac[]) >>
       rw[EQ_IMP_THM]
       >- (drule BIJ_LINV_INV >>
           ‘fn x ∈ N2.Q’ by cheat >>
           disch_then drule >> gvs [INJ_DEF]

  ‘N2.final = IMAGE fn N1.final’ by
    (gvs [preserves_nfa_structure_def] >>
     reverse(rw[EXTENSION,EQ_IMP_THM])
     >- metis_tac[] >>
     drule BIJ_LINV_INV >>
     ‘x ∈ N2.Q’ by metis_tac[is_nfa_def,SUBSET_DEF] >>
     disch_then drule >> metis_tac[]) >>
‘BIJ fn N1.initial N2.initial’ byA all_tac
     (irule finite_inj_inj_bij >> rw[]
      >- (irule INJ_SUBSET >>
          first_assum (irule_at Any) >>
          metis_tac[is_nfa_def]

     gvs[is_nfa_def]

  gvs [preserves_nfa_structure_def] >> rw[]
  >- (rw [EQ_IMP_THM]
      >- metis_tac[is_nfa_def,SUBSET_DEF]
      >- (qabbrev_tac ‘a = LINV fn N1.Q q’ >>
          ‘a ∈ N1.initial’ by metis_tac[] >>
QED
*)

(*---------------------------------------------------------------------------*)
(* Accessibility is computed by an instance of depth-first traversal.        *)
(*---------------------------------------------------------------------------*)

Definition kidlist_def:
  kidlist N q =
    if q ∈ N.Q then
      SET_TO_LIST(BIGUNION{N.delta q a | a | a ∈ N.Sigma})
    else []
End

Theorem nfa_parents_finite:
  is_nfa N ⇒ FINITE (Parents (kidlist N))
Proof
  strip_tac >> irule SUBSET_FINITE >>
  qexists_tac ‘N.Q’ >>
  gvs [is_nfa_def] >>
  rw[Parents_def, kidlist_def,SUBSET_DEF] >>
  pop_keep_tac >> IF_CASES_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Invocation:  reachable_states N [] (SET_TO_LIST N.initial) []             *)
(*---------------------------------------------------------------------------*)

Definition reachable_states_def:
  reachable_states N = DFT (kidlist N) (list$CONS)
End

Theorem reachable_states_eqns:
  is_nfa N
  ⇒
  reachable_states N seen [] acc = acc ∧
  reachable_states N seen (h::t) acc =
   if MEM h seen
     then reachable_states N seen t acc
     else reachable_states N (h::seen) (kidlist N h ++ t) (h::acc)
Proof
  PURE_REWRITE_TAC[reachable_states_def] >> strip_tac >>
  imp_res_tac nfa_parents_finite >>
  rw[DFT_def]
QED

(*---------------------------------------------------------------------------*)
(* A state is accessible iff reachable_states finds it                       *)
(*---------------------------------------------------------------------------*)

Theorem reachable_states:
  is_nfa N ⇒
  ∀q. q ∈ REACH_LIST (kidlist N) (SET_TO_LIST N.initial)
      ⇔
      q ∈ set(reachable_states N [] (SET_TO_LIST N.initial) [])
Proof
  PURE_REWRITE_TAC[reachable_states_def] >>
  strip_tac >>
  imp_res_tac nfa_parents_finite >>
  irule DFT_REACH_THM >> metis_tac[]
QED

Theorem reachable_accessible[local]:
  is_dfa M ⇒
  ∀p q. (λx y. set (kidlist M x) y)꙳ p q ⇒ p ∈ M.initial ⇒ q ∈ accessible_states M
Proof
 strip_tac >>
 ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
 gvs [is_dfa_def] >> rw[accessible_states_def]
 >- (qexists_tac ‘ε’ >> rw[nfa_eval_def])
 >- (qpat_x_assum ‘set(kidlist M x) q’ mp_tac >>
     ‘FINITE(BIGUNION {M.delta x a | a | a ∈ M.Sigma})’ by
       (rw[GSPEC_IMAGE,combinTheory.o_DEF]
        >- (irule IMAGE_FINITE >> rw[IN_DEF] >> metis_tac[is_nfa_def])
        >- (irule SUBSET_FINITE >> drule nfa_eval_states_closed >>
            disch_then drule >>
            ‘{q_0} ⊆ M.Q’ by metis_tac [is_nfa_def] >>
            disch_then drule >> rw[] >> metis_tac[is_nfa_def])) >>
     rw [kidlist_def,SET_TO_LIST_INV] >>
     qexists_tac ‘w ++ [a]’ >>
     ‘{q_0} ⊆ M.Q’ by metis_tac [is_nfa_def] >>
     rw [nfa_eval_append] >> rw [nfa_eval_def] >>
     first_x_assum drule_all >> rw[] >> gvs[] >>
     pop_assum sym_subst_all_tac >>
     rw[EXTENSION,GSPECIFICATION] >> metis_tac[])
QED

Theorem accessible_reachable[local]:
  ∀w p q.
    is_dfa M ∧
    M.initial = {p} ∧
    q ∈ accessible_states M
    ⇒
    (λx y. set (kidlist M x) y)꙳ p q
Proof
   simp [accessible_states_def,PULL_EXISTS] >>
   CONV_TAC (RESORT_FORALL_CONV List.rev) >>
   recInduct SNOC_INDUCT >> rw[]
   >- gvs [nfa_eval_def] >>
   gvs [EVERY_SNOC,SNOC_APPEND] >>
   pop_keep_tac >>
   ‘{p} ⊆ M.Q’ by
      metis_tac [is_dfa_def,is_nfa_def] >>
   drule_all dfa_eval_final_state >>
   gvs [is_dfa_def] >> rw[nfa_eval_append] >> gvs[] >>
   simp [Once RTC_CASES2] >> disj2_tac >>
   first_x_assum (irule_at Any) >>
   rw [kidlist_def]
   >- (‘FINITE(BIGUNION {M.delta q' a | a | a ∈ M.Sigma})’ by
         (rw[GSPEC_IMAGE,combinTheory.o_DEF]
          >- (irule IMAGE_FINITE >> rw[IN_DEF] >> metis_tac[is_nfa_def])
          >- (irule SUBSET_FINITE >> drule nfa_eval_states_closed >>
              disch_then drule >>
              ‘{p} ⊆ M.Q’ by metis_tac [is_nfa_def] >>
              disch_then drule >> rw[] >> metis_tac[is_nfa_def])) >>
      rw [SET_TO_LIST_INV,PULL_EXISTS] >>
      first_assum (irule_at Any) >>
      qpat_x_assum ‘nfa_eval _ _ [_] = _’ mp_tac >>
      simp [nfa_eval_def,EXTENSION] >> metis_tac[])
  >- (‘{p} ⊆ M.Q’ by
         metis_tac [is_nfa_def] >>
      drule_all nfa_eval_states_closed >> rw[])
QED

Theorem accessible_state_reach_list:
  is_dfa M
  ⇒
  (q ∈ accessible_states M
    ⇔
   REACH_LIST (kidlist M) (SET_TO_LIST M.initial) q)
Proof
  strip_tac >>
  ‘FINITE M.initial’ by
     metis_tac [is_dfa_def,is_nfa_def,SUBSET_FINITE] >>
  rw [REACH_LIST_def,REACH_def,MEM_SET_TO_LIST] >>
  rw [EQ_IMP_THM]
  >- (‘∃p. M.initial = {p}’ by
        metis_tac [is_dfa_def] >> simp[] >>
      simp[IN_DEF] >> irule_at Any accessible_reachable >> simp[])
  >- (irule reachable_accessible >> simp [] >>
      first_x_assum (irule_at Any) >> gvs[IN_DEF])
QED

Theorem accessible_state_eq_reachable_states:
  is_dfa M ⇒
  (accessible_states M
    =
   set(reachable_states M [] (SET_TO_LIST M.initial) []))
Proof
  metis_tac [accessible_state_reach_list,reachable_states,
             is_dfa_def, EXTENSION,IN_DEF]
QED

(*---------------------------------------------------------------------------*)
(* States q1 and q2 are distinguishable if there is at least one string w    *)
(* s.t. executing M on w from one of q1 or q2 ends in an accepting state but *)
(* executing from the other ends in a non-accepting state.                   *)
(*---------------------------------------------------------------------------*)

Definition distinguishable_states_def:
  distinguishable_states M q1 q2 ⇔
    {q1; q2} ⊆ M.Q ∧
    ∃w. w ∈ KSTAR {[a] | a ∈ M.Sigma} ∧
        (nfa_eval M {q1} w ⊆ M.final
          ⇔
         nfa_eval M {q2} w ⊈ M.final)
End

Definition distinguishable_nfa_def:
  distinguishable_nfa M ⇔
    ∀q1 q2. {q1; q2} ⊆ M.Q ∧ q1 ≠ q2 ⇒ distinguishable_states M q1 q2
End
