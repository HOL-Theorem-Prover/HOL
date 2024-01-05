(* See:

     Wu and Goré, "Verified Decision Procedures for Modal Logics", ITP 2019

   for inspiration

*)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory listTheory relationTheory;
open modalBasicsTheory tableauBasicsTheory
open arithmeticTheory;

val _ = new_theory "tableauS4";

Datatype:
  premodel = Nd α (premodel list)
End

Definition pt_rel_def:
  pt_rel t1 t2 ⇔ ∃vs ts. t1 = Nd vs ts ∧ MEM t2 ts
End

Definition get_htk[simp]:
  get_htk (Nd (id, htk, request) l) = htk
End

Definition get_id[simp]:
  get_id (Nd (id, htk, request) l) = id
End

Definition get_request[simp]:
  get_request (Nd (id, htk, request) l) = request
End

Definition get_kids[simp]:
  get_kids (Nd a l) = l
End

val _ = add_record_field("htk", ``get_htk``)
val _ = add_record_field("id", ``get_id``)
val _ = add_record_field("request", ``get_request``)
val _ = add_record_field("l", ``get_kids``)

Datatype:
  S4_sequent = <|
          As : (nnfform # nnfform list) list;
          Ss : (nnfform # nnfform list) option;
          Hs : nnfform list;
          Sg : nnfform list;
          Gm : nnfform list;
         |>
End

Type S4_result = ``:(S4_sequent #
                           nnfform list #
                           (nnfform # nnfform list) list)
                          premodel``

Overload CLOSED = “NONE : S4_result option”

Overload OPEN = “SOME :  S4_result -> S4_result option”

Definition closure_list_conc_def[simp]:
  closure_list_conc [] = [] ∧
  closure_list_conc (Conj f1 f2::rest) =
    Conj f1 f2::closure_list_conc [f1] ⧺ closure_list_conc [f2] ⧺
    closure_list_conc rest ∧
  closure_list_conc (Disj f1 f2::rest) =
    Disj f1 f2::closure_list_conc [f1] ⧺ closure_list_conc [f2] ⧺
    closure_list_conc rest ∧
  closure_list_conc (Box f::rest) =
    Box f :: closure_list_conc [f] ++ (closure_list_conc rest) ∧
  closure_list_conc (Dia f::rest) =
    Dia f :: closure_list_conc [f] ++ (closure_list_conc rest) ∧
  closure_list_conc (f::rest) = f :: (closure_list_conc rest)
Termination
  WF_REL_TAC `measure gsize` >> rw[]
End

Theorem mem_lst_closure:
  ∀s l. MEM s l ⇒ MEM s (closure_list_conc l)
Proof
  Induct_on `l` >> rw[] >> Cases_on `h` >> fs[]
QED

Theorem sublist_closure:
  ∀f lst h. MEM f (closure_list_conc lst) ⇒  MEM f (closure_list_conc (h::lst))
Proof
  rw[] >> Induct_on `lst` >> rw[] >>
  Cases_on `f=h` >> rw[]
  >- (Cases_on `f` >> rw[])
  >> Cases_on `f=h'` >> rw[]
  >> Cases_on `h` >> rw[]
QED

Theorem mem_closure:
  ∀f e lst. MEM e lst ∧ MEM f (closure_list_conc [e]) ⇒
            MEM f (closure_list_conc lst)
Proof
  Induct_on `lst` >> rw[]
  >- (Cases_on `e` >> fs[])
  >> metis_tac[FORALL_AND_THM, sublist_closure]
QED

Theorem transitive_closure:
  ∀p f h. MEM p (closure_list_conc [f]) ∧ MEM f (closure_list_conc [h])
          ⇒ MEM p (closure_list_conc [h])
Proof
  rw[] >> Induct_on `h`
  >- (Cases_on `f` >> fs[MEM])
  >- (Cases_on `f` >> fs[MEM])
  >- (Induct_on `f` >> fs[] >> rw[] >> rw[])
  >- (Induct_on `f` >> fs[] >> rw[] >> rw[])
  >- (Induct_on `f` >> fs[] >> rw[] >> rw[])
  >> (Induct_on `f` >> fs[] >> rw[] >> rw[])
QED

Theorem mem_closure_of_closure:
∀f lst.  MEM f (closure_list_conc lst) ⇒
        (∀p. MEM p (closure_list_conc [f]) ⇒ MEM p (closure_list_conc lst))
Proof
  Induct_on `lst` >> rw[] >>
  Cases_on `MEM f (closure_list_conc [h])`
  >- metis_tac[transitive_closure, MEM, mem_closure]
  >> `closure_list_conc (h::lst) =
      closure_list_conc [h] ++
      (closure_list_conc lst)` by (Cases_on `h` >> fs[]) >>
  fs[] >> `MEM p (closure_list_conc lst)` suffices_by simp[] >>
  metis_tac[mem_closure]
QED

Theorem mem_closure_self:
  ∀f. MEM f (closure_list_conc [f])
Proof
  Cases_on `f` >> rw[]
QED

Theorem box_subformula_closure:
  ∀l f. MEM (Box f) (closure_list_conc l) ⇒ MEM f (closure_list_conc l)
Proof
  ho_match_mp_tac closure_list_conc_ind >> rw[]
  >> metis_tac[mem_closure_self]
QED

Theorem form_size_none_zero:
  0 < form_size f
Proof
  Induct_on `f` >> rw[]
QED

Theorem in_subset:
  ∀p s l1 l2. p ∈ (set l1) ∧ (set l1 ⊆ (set l2)) ⇒ p ∈ (set l2)
Proof
  Induct_on `l1` >> rw[] >> rw[]
QED

Theorem head_list_mem:
  ∀l s r. l = s::r ⇒ MEM s l
Proof
  fs[]
QED

Theorem tail_list_subset:
  ∀l s r. l = s::r ⇒ set r ⊆ set l
Proof
  rw[INSERT_DEF, SUBSET_DEF]
QED

Theorem in_psubset:
  ∀p s l1 l2. p ∈ (set l1) ∧ (set l1 PSUBSET (set l2)) ⇒ p ∈ (set l2)
Proof
  Induct_on `l1` >> rw[] >> fs[INSERT_DEF, PSUBSET_DEF, SUBSET_DEF]
QED

Theorem mem_subset:
  ∀p s l1 l2. MEM p l1 ∧ (set l1 ⊆ (set l2)) ⇒ MEM p l2
Proof
  metis_tac[in_subset]
QED

Theorem mem_psubset:
  ∀p s l1 l2. MEM p l1 ∧ (set l1 PSUBSET (set l2)) ⇒ MEM p l2
Proof
  metis_tac[in_psubset]
QED

Theorem sublist_to_subset:
  ∀l1 l2. (∀x. MEM x l1 ⇒ MEM x l2) ⇒ set l1 ⊆ set l2
Proof
  Induct_on `l1` >> rw[SUBSET_DEF]
QED

Theorem gsize_head:
  ∀l e l1. l = e::l1 ⇒ gsize l = form_size e + gsize l1
Proof
  Induct_on `l1` >> rw[]
QED

Theorem gsize_append:
  ∀l1 l2. gsize (l1++l2) = gsize l1 + gsize l2
Proof
  Induct_on `l1` >> rw[] >> rw[SUM_APPEND]
QED

Theorem gsize_mem:
  ∀f l. MEM f l ⇒ form_size f <= gsize l
Proof
  Induct_on `l` >> fs[MEM] >> rw[]
  >- (Cases_on `f` >> rw[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]
QED

Theorem gsize_mem_single:
  ∀f l. MEM f l ∧ gsize l <= form_size f ==> l = [f]
Proof
  Induct_on `l` >> rw[]
  >- (`form_size f = 0 + form_size f` by rw[] >>
      `gsize l + form_size f ≤ 0 + form_size f` by fs[] >>
      `gsize l ≤ 0` by metis_tac[LE_ADD_RCANCEL] >>
      Cases_on `l` >> rw[] >> Cases_on `h` >> fs[])
  >> `gsize l ≤ form_size f` by fs[LESS_EQ_TRANS, LESS_EQ_ADD] >>
  first_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  fs[] >> Cases_on `h` >> fs[]
QED

Theorem proper_subset:
  ∀a l1 l2. ALL_DISTINCT l1 ∧ a ∉ set l1 ∧ a ∈ set l2 ∧ set l1 ⊆ set l2 ⇒
            gsize l1 < gsize l2
Proof
  Induct_on `l1` >> rw[]
  >- (Induct_on `l2` >> rw[]
      >- (`0 < form_size a` suffices_by rw[] >> simp[form_size_none_zero])
      >> `0 < form_size h` suffices_by rw[] >> simp[form_size_none_zero])
  >> `∃t1 t2. l2 = t1 ⧺ h::t2` by metis_tac[MEM_SPLIT] >>
  `gsize l1 + form_size h < gsize (t1 ⧺ h::t2)` suffices_by rw[] >>
  simp[gsize_append] >> `gsize l1 < gsize t1 + gsize t2` suffices_by rw[] >>
  `gsize l1 < gsize (t1++t2)` suffices_by rw[gsize_append] >>
  first_x_assum irule >> rw[]
  >- (qexists_tac `a` >> rw[] >> fs[] >> fs[])
  >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem proper_psubset:
  ∀a l1 l2. ALL_DISTINCT l1 ∧ a ∉ set l1 ∧ a ∈ set l2 ∧ set l1 ⊂ set l2 ⇒
            gsize l1 < gsize l2
Proof
  metis_tac[proper_subset, PSUBSET_DEF]
QED

Theorem gsize_filter:
  ∀l f. gsize (FILTER (λy. f ≠ y) l) <= gsize l
Proof
  Induct_on `l` >> rw[] >> metis_tac[LESS_EQ_ADD, LESS_EQ_TRANS]
QED

Theorem gsize_filter_sml_sub_single:
  ∀l f. MEM f l ⇒ gsize (FILTER (λy. f ≠ y) l) <= gsize l − form_size f
Proof
  Induct_on `l` >> rw[]
  >- (`gsize l - form_size f >= 0` by (Induct_on `l` >> rw[]) >>
      Cases_on `gsize l - form_size f = 0`
      >- (Cases_on `l = [f]` >> fs[MEM] >>
          `form_size f <= gsize l` by rw[gsize_mem] >>
          `gsize l = form_size f` by fs[] >> drule gsize_mem_single >> rw[]) >>
      fs[NOT_LESS_EQUAL] >> first_x_assum (drule_then strip_assume_tac) >>
      `gsize l + form_size h − form_size f = gsize l − form_size f +form_size h`
        by fs[SUB_RIGHT_ADD] >>
      metis_tac[LESS_EQ_MONO_ADD_EQ])
  >> rw[gsize_filter]
QED

Theorem all_distinct_psubst:
  ∀a l1 l2. ALL_DISTINCT l1 ∧ set l1 ⊂ set l2 ⇒ gsize l1 < gsize l2
Proof
  Induct_on `l1` >> rw[]
  >- (Induct_on `l2` >> rw[] >> Cases_on `h` >> fs[]) >>
  fs[PSUBSET_DEF, SUBSET_DEF, INSERT_DEF] >>
  `gsize l1 < gsize l2 - form_size h` suffices_by rw[] >>
  `∃p. p ≠ h ∧ MEM p l2 ∧ ¬MEM p l1`
    by (SPOSE_NOT_THEN ASSUME_TAC >>
        fs[EXTENSION] >> Cases_on `x = h` >> fs[] >>
        qpat_x_assum ` ∀l2'.
            (∀x. MEM x l1 ⇒ MEM x l2') ∧ (∃x. MEM x l1 ⇎ MEM x l2') ⇒
            gsize l1 < gsize l2'` (fn _ => all_tac) >>
        last_assum (drule_then strip_assume_tac) >> metis_tac[]) >>
  `set l1 ≠ set (FILTER ($≠ h) l2)`
    by (fs[EXTENSION] >> qexists_tac `p` >> fs[MEM_FILTER] >> metis_tac[]) >>
  `(∀x. MEM x l1 ⇒ MEM x (FILTER ($≠ h) l2))`
    by (rw[] >> fs[MEM_FILTER] >> metis_tac[]) >>
  last_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >> fs[] >>
  metis_tac[gsize_filter_sml_sub_single ,LESS_LESS_EQ_TRANS]
QED

Definition wfm_S4_sequent:
  wfm_S4_sequent Γ0 s ⇔
    ALL_DISTINCT s.Sg ∧ ALL_DISTINCT s.Hs ∧
    set s.Sg PSUBSET set (closure_list_conc [Γ0]) ∧
    set s.Hs SUBSET set (closure_list_conc [Γ0]) ∧
    set s.Gm SUBSET set (closure_list_conc [Γ0]) ∧
    EVERY is_box s.Sg ∧
    (∀x. MEM x s.Hs ⇒ MEM (Dia x) (closure_list_conc [Γ0])) ∧
    (∀p. MEM p s.Hs ⇒ MEM (p, s.Sg) s.As) ∧
    (∀q r. s.Ss = SOME (q, r) ⇒ MEM q s.Gm ∧ set r ⊆ set s.Gm)
End

(* pluck the first element from list that satisfies P,
   otherwise return NONE *)
Definition pluck_def:
  pluck P []     = NONE ∧
  pluck P (h::t) = if P h then SOME (h, t)
                   else (case pluck P t of NONE => NONE
                                          |SOME (a, b) => SOME (a, h::b))
End

Definition dest_box_def:
  dest_box (Box f) = SOME f ∧
  dest_box f = NONE
End

Definition trule_s4_def:
  trule_s4 s =
  case pluck is_box s.Gm of
    NONE        => NONE
  | SOME(b, rest) =>
      if MEM b s.Sg then
        SOME (b, s with <| Ss := NONE ; Gm := THE (dest_box b)::rest |>)
      else
        SOME (b, s with <| Ss := NONE;
                           Hs := [];
                           Sg := b::s.Sg;
                           Gm := THE (dest_box b)::rest;  |>)
End

Theorem pluck_eq_some_append:
  ∀l h rest. pluck P l = SOME (h, rest) ⇒
             P h ∧ ∃p s. l = p++[h]++s ∧ rest = p++s
Proof
  Induct_on `l` >> rw[pluck_def, AllCaseEqs()] >> rw[]
  >-(qexistsl_tac [`[]`, `l`] >> rw[])
  >> first_x_assum (drule_then strip_assume_tac) >> rw[] >>
  qexistsl_tac [`h::p`, `s`] >> rw[]
QED

Theorem trule_s4_length:
∀s f s'.
    trule_s4 s = SOME (f, s') ⇒
    (gsize s.Sg < gsize s'.Sg) ∨
    (gsize s.Sg = gsize s'.Sg ∧ gsize s.Hs = gsize s'.Hs ∧
      gsize s'.Gm < gsize s.Gm)
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[]
  >-(simp[] >> drule pluck_eq_some_append >> rw[] >> simp[SUM_APPEND] >>
     Cases_on `b` >> fs[dest_box_def] >> rw[]) >>
  simp[] >> drule pluck_eq_some_append >> rw[] >> Cases_on `b` >>
  fs[dest_box_def] >> rw[]
QED

Theorem f_neq_box_f[simp]:
  ∀f. f ≠ Box f
Proof
  Induct_on `f` >> rw[]
QED

Theorem f_neq_dia_f[simp]:
  ∀f. f ≠ Dia f
Proof
  Induct_on `f` >> rw[]
QED

Definition add_rule:
  add_rule rule (Nd (s, r) lst) = Nd (s, rule) [Nd (s, r) lst]
End

Definition conjsplit_s4_def[simp]:
  (conjsplit_s4 (Conj f1 f2 :: rest) = SOME (Conj f1 f2, f1 :: f2 :: rest)) ∧
  (conjsplit_s4 (f :: rest) = OPTION_MAP (I ## CONS f) (conjsplit_s4 rest)) ∧
  (conjsplit_s4 [] = NONE)
End

Definition disjsplit_s4_def[simp]:
  disjsplit_s4 (Disj f1 f2 :: rest) = SOME (Disj f1 f2, (f1::rest, f2::rest)) ∧
  disjsplit_s4 (f :: rest) =
    OPTION_MAP (I ## (CONS f ## CONS f)) (disjsplit_s4 rest) ∧
  disjsplit_s4 [] = NONE
End

Theorem conjsplit_s4_size:
  ∀Γ fs f. conjsplit_s4 Γ = SOME (f, fs) ⇒
           SUM (MAP form_size fs) < SUM (MAP form_size Γ)
Proof
  Induct >> simp[conjsplit_s4_def] >> Cases >>
  simp[conjsplit_s4_def, FORALL_PROD, PULL_EXISTS]
QED

Theorem disjsplit_s4_size:
  ∀Γ fs1 fs2. disjsplit_s4 Γ = SOME (f, (fs1, fs2)) ⇒
                  SUM (MAP form_size fs1) < SUM (MAP form_size Γ) ∧
                  SUM (MAP form_size fs2) < SUM (MAP form_size Γ)
Proof
  Induct_on ‘Γ’ >> Cases >>
  simp[FORALL_PROD, PULL_EXISTS]
QED

Definition s4_request_local[simp]:
  s4_request_local [] _ = [] ∧
  s4_request_local (s::xs) sg = (s, sg)::(s4_request_local xs sg)
End

(* tableau_S4 Ancestors Signatures History Sigma Gamma *)
Definition tableau_S4_def:
  tableau_S4 Γ0 s = if  ¬ wfm_S4_sequent Γ0 s then CLOSED else
    case contradiction s.Gm of
      SOME i => CLOSED
    | NONE =>
        case conjsplit_s4 s.Gm of
          SOME (pf, Γ') =>
            (case tableau_S4 Γ0 (s with <| Ss:=NONE; Gm:=Γ'; |>) of
               NONE => NONE
             |  SOME (Nd (id, h, r) cs) => SOME (Nd (s, pf::h, r) cs))
        | NONE =>
            case disjsplit_s4 s.Gm of
              SOME (pf, (Γ1, Γ2)) =>
                (case tableau_S4 Γ0 (s with <| Ss:=NONE; Gm:=Γ1; |>) of
                   SOME (Nd (id, h, r) cs) => SOME (Nd (s, pf::h, r) cs)
                 | NONE =>
                     case tableau_S4 Γ0 (s with <| Ss:=NONE; Gm:=Γ2; |>) of
                       SOME (Nd (id, h, r) cs) => SOME (Nd (s, pf::h, r) cs)
                     | NONE => NONE)
            | NONE =>
                if EXISTS is_box s.Gm then
                  case trule_s4 s of
                    SOME (pf, s') =>
                      (case tableau_S4 Γ0 s' of
                         NONE => NONE
                       | SOME (Nd (id, h, r) cs) =>
                           SOME (Nd (s, pf::h, r) cs))
                  | NONE => NONE
                else if EXISTS is_dia s.Gm then
                  let
                    children =
                    scmap
                    (λdf. tableau_S4 Γ0 (s with <| As := (df, s.Sg)::s.As;
                                                   Ss := SOME (df, s.Sg);
                                                   Hs := df::s.Hs;
                                                   Gm := df::s.Sg |>))
                    (FILTER (λf. ¬ MEM f s.Hs) (undia s.Gm))
                  in
                    case children of
                      SOME ms =>
                        SOME (Nd (s, s.Gm, s4_request_local s.Hs s.Sg) ms)
                    | NONE => CLOSED
                else SOME (Nd (s, s.Gm, s4_request_local s.Hs s.Sg) [])
Termination
  WF_REL_TAC ‘(inv_image ((<) LEX ((<) LEX (<)))
               (λ(Γ0,s). ((SUM $ MAP form_size (closure_list_conc [Γ0])) -
                          (SUM $ MAP form_size s.Sg))
                ,    ( ((SUM $ MAP form_size (closure_list_conc [Γ0])) -
                        (SUM $ MAP form_size s.Hs))
                       , (SUM $ MAP form_size s.Gm) )))’ >> rpt conj_tac
  >-(* S4 *)
     (rw[] >> DISJ1_TAC >> fs[wfm_S4_sequent] >> csimp[] >>
      rw[form_size_none_zero] >>
      fs[MEM_FILTER] >> fs[MEM_undia] >>
      `MEM (Dia df) (closure_list_conc [Γ0])` by metis_tac[mem_subset] >>
      drule mem_closure_of_closure >> rw[] >>
      `MEM df (closure_list_conc [Dia df])`
        by (rw[] >> metis_tac[mem_closure_self]) >>
      fs[] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      first_x_assum (drule_then strip_assume_tac) >>
      `gsize s.Hs < gsize (closure_list_conc [Γ0])` suffices_by rw[] >>
      irule proper_subset >> metis_tac[])
  >- (rw[] >> fs[wfm_S4_sequent] >> drule_all trule_s4_length >> rw[]
      >- (DISJ1_TAC >> simp[] >>
          `gsize s.Sg < gsize (closure_list_conc [Γ0])` suffices_by simp[] >>
          qpat_x_assum `ALL_DISTINCT s.Hs` (fn _ => all_tac) >>
          drule all_distinct_psubst >> rw[] >>
          first_x_assum (drule_then strip_assume_tac))
      >> simp[])
  >- rw[conjsplit_s4_size]
  >- (rw[] >> drule disjsplit_s4_size >> simp[])
  >> rw[] >> metis_tac[disjsplit_s4_size]
End

Definition final_tableau_S4_def:
  final_tableau_S4 f = tableau_S4 f <|   As := [];
                                         Ss := NONE;
                                         Hs := [];
                                         Sg := [];
                                         Gm := [f]
                                      |>
End

Theorem tableau_S4_s_eq_id:
  ∀Γ0 s id h r cs. tableau_S4 Γ0 s = SOME (Nd (id,h,r) cs) ⇒ s = id
Proof
  rw[Once tableau_S4_def] >> fs[AllCaseEqs()]
QED

Theorem sublist_subset:
  ∀l h v. l = h::v ⇒ set v SUBSET set l
Proof
  Induct_on `l` >> rw[INSERT_DEF, SUBSET_DEF]
QED

Theorem sublist_psubset:
  ∀l1 h v. l1 = h::v ⇒ set v PSUBSET set l1 ∨ set v = set l1
Proof
  Induct_on `l1` >> rw[INSERT_DEF] >>
  Cases_on `set l1 ⊂ {y | y = h ∨ MEM y l1}` >> rw[] >>
  fs[PSUBSET_DEF, SUBSET_DEF]
QED

Theorem psubset_subset:
  ∀l2 l3 l1. l1 PSUBSET l2 ∧ l2 ⊆ l3 ⇒ l1 PSUBSET l3
Proof
  rw[SUBSET_DEF, PSUBSET_DEF] >> SPOSE_NOT_THEN ASSUME_TAC >>
  `∀x. x ∈ l2 ⇒ x ∈ l1` by fs[] >> `l1 SUBSET l2` by fs[SUBSET_DEF] >>
  `l2 SUBSET l1` by fs[SUBSET_DEF] >>
  `l1 = l2` by metis_tac[SUBSET_ANTISYM]
QED

Theorem closure_ele_literal:
  ∀p. ∃f. MEM f (closure_list_conc [p]) ∧ (is_literal f)
Proof
  Induct_on `p`
  >- rw[]
  >- rw[]
  >> fs[] >> qexists_tac `f` >> rw[] >> irule mem_closure_of_closure >>
  qexists_tac `p` >> rw[] >> metis_tac[mem_closure_self]
QED

Theorem closure_lst_literal:
  ∀p. p = [] ∨ ∃f. MEM f (closure_list_conc p) ∧ (is_literal f)
Proof
  Induct_on `p` >> rw[]
  >- metis_tac[closure_ele_literal]
  >> qexists_tac `f` >> rw[] >> drule sublist_closure >> rw[]
QED

Theorem wfm_S4_trule:
  ∀s Γ0 p q. wfm_S4_sequent Γ0 s ∧ trule_s4 s = SOME (p, q) ⇒
             wfm_S4_sequent Γ0 q
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[]
  >-(drule pluck_eq_some_append >> rw[] >> fs[wfm_S4_sequent] >>
     Cases_on `b` >> fs[dest_box_def] >> metis_tac[box_subformula_closure])
  >> drule pluck_eq_some_append >> rw[] >> fs[wfm_S4_sequent] >>
  Cases_on `b` >> fs[dest_box_def] >> reverse(rw[])
  >- metis_tac[box_subformula_closure]
  >> rw[PSUBSET_DEF, SUBSET_DEF, INSERT_DEF] >> rw[]
  >- metis_tac[PSUBSET_DEF, SUBSET_DEF]
  >> simp[EXTENSION]
  >> qspec_then `Γ0` (qx_choose_then `ff` strip_assume_tac) closure_ele_literal
  >> qexists_tac `ff` >> simp[] >> rpt strip_tac
  >- fs[is_literal_def]
  >> `is_box ff` by metis_tac[EVERY_MEM] >> Cases_on `ff`
  >> fs[is_box_def, is_literal_def]
QED

Theorem mem_trule_gamma:
  ∀s f p q. trule_s4 s = SOME (p, q) ∧ MEM f q.Gm ⇒
            MEM f s.Gm ∨ MEM (Box f) s.Gm
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[] >>
  drule pluck_eq_some_append >> rw[] >> Cases_on `b` >> fs[dest_box_def]
QED

Theorem mem_trule_sigma:
  ∀s f p q. trule_s4 s = SOME (p, q) ∧ MEM f q.Sg ==> MEM f s.Gm ∨ MEM f s.Sg
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[] >>
  drule pluck_eq_some_append >> rw[] >> Cases_on `b` >> fs[dest_box_def]
QED

Theorem undia_dia_in_closure:
  MEM df (undia s.Gm) ∧
  set s.Gm ⊆ set (closure_list_conc [Γ0])
  ⇒
  MEM df (closure_list_conc [Γ0])
Proof
  fs[MEM_undia] >> rw[] >>
  `MEM (Dia df) (closure_list_conc [Γ0])` by metis_tac[mem_subset] >>
  drule mem_closure_of_closure >> rw[] >> metis_tac[mem_closure_self]
QED

Theorem mem_closure_head_tail:
  ∀h r f. MEM f (closure_list_conc (h::r)) ⇒
          MEM f (closure_list_conc [h]) ∨ MEM f (closure_list_conc r)
Proof
  rw[] >> Cases_on `MEM f (closure_list_conc [h])` >> rw[] >>
  `closure_list_conc (h::r) = (closure_list_conc [h]) ++ (closure_list_conc r)`
    by (Cases_on `h` >> fs[]) >> fs[]
QED

Theorem closure_subset_closure:
  ∀l1 l2. set l1 ⊆ set (closure_list_conc l2) ⇒
          set (closure_list_conc l1) ⊆ set (closure_list_conc l2)
Proof
  Induct_on `l1` >> rw[] >> rw[] >>
  fs[SUBSET_DEF] >> rw[] >>
  Cases_on `MEM x (closure_list_conc [h])` >> fs[]
  >- metis_tac[mem_closure_of_closure]
  >> drule mem_closure_head_tail >> rw[]
QED

Theorem MEM_disjsplit1:
  ∀Γ Γ1 Γ2 f1.
     MEM f1 Γ1 ∧ disjsplit_s4 Γ = SOME (f, (Γ1,Γ2)) ⇒
     MEM f1 Γ ∨ (∃f2. MEM f2 Γ2 ∧ MEM (Disj f1 f2) Γ)
Proof
  ho_match_mp_tac disjsplit_s4_ind >> rw[]
  >- (fs[] >> rw[] >> metis_tac[])
  >> Cases_on `z` >> fs[] >> Cases_on `r` >> fs[] >> metis_tac[]
QED

Theorem MEM_disjsplit2:
  ∀Γ Γ1 Γ2 f2.
     MEM f2 Γ2 ∧ disjsplit_s4 Γ = SOME (f, (Γ1,Γ2)) ⇒
     MEM f2 Γ ∨ (∃f1. MEM f1 Γ1 ∧ MEM (Disj f1 f2) Γ)
Proof
  ho_match_mp_tac disjsplit_s4_ind >> rw[]
  >- (fs[] >> rw[] >> metis_tac[])
  >> Cases_on `z` >> fs[] >> Cases_on `r` >> fs[] >> metis_tac[]
QED

Theorem wfm_S4_Disj:
∀s Γ0 Γ1 Γ2.   wfm_S4_sequent Γ0 s ∧ disjsplit_s4 s.Gm = SOME (f, (Γ1,Γ2))
               ⇒
               wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ1|>) ∧
               wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ2|>)
Proof
  rw[wfm_S4_sequent]
  >- (simp[SUBSET_DEF] >> rw[] >> drule_all MEM_disjsplit1 >> rw[]
      >- metis_tac[SUBSET_DEF]
      >> `MEM (Disj x f2) (closure_list_conc [Γ0])` by  metis_tac[SUBSET_DEF] >>
         drule mem_closure_of_closure >> rw[] >> metis_tac[mem_closure_self])
  >> simp[SUBSET_DEF] >> rw[] >> drule_all MEM_disjsplit2 >> rw[]
  >- metis_tac[SUBSET_DEF]
  >> `MEM (Disj f1 x) (closure_list_conc [Γ0])` by  metis_tac[SUBSET_DEF] >>
  drule mem_closure_of_closure >> rw[] >> metis_tac[mem_closure_self]
QED

Theorem conjsplit_s4_MEM2:
  ∀Γ₀ Γ ϕ. conjsplit_s4 Γ₀ = SOME (f, Γ) ∧ MEM ϕ Γ ⇒
           MEM ϕ Γ₀ ∨ (∃ϕ'. MEM (Conj ϕ ϕ') Γ₀) ∨
           (∃ϕ'. MEM (Conj ϕ' ϕ) Γ₀)
Proof
  Induct >> simp[] >> Cases >~
  [‘Conj f1 f2’]
  >- (rpt strip_tac >> rw[] >> fs[conjsplit_s4_def] >>
      Cases_on `MEM ϕ Γ₀` >> gvs[] >> simp[EXISTS_OR_THM]) >>
  rw[] >> Cases_on `z` >> gvs[] >> metis_tac[]
QED

Theorem wfm_S4_Conj:
∀s Γ0 Γ'.  wfm_S4_sequent Γ0 s ∧ conjsplit_s4 s.Gm = SOME (f, Γ')
           ⇒
           wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ'|>)
Proof
  rw[wfm_S4_sequent] >> simp[SUBSET_DEF] >> rw[] >>
  drule_all conjsplit_s4_MEM2 >> rw[]
  >- metis_tac[SUBSET_DEF]
  >- (`MEM (Conj x ϕ') (closure_list_conc [Γ0])` by metis_tac[SUBSET_DEF] >>
      drule mem_closure_of_closure >> rw[] >> metis_tac[mem_closure_self])
  >> `MEM (Conj ϕ' x) (closure_list_conc [Γ0])` by metis_tac[SUBSET_DEF] >>
  drule mem_closure_of_closure >> rw[] >> metis_tac[mem_closure_self]
QED

Theorem wfm_S4_Transitive:
  ∀Γ0 s m w. tableau_S4 Γ0 s = SOME m ∧
             wfm_S4_sequent Γ0 s ∧
             RTC pt_rel m w ⇒
             wfm_S4_sequent Γ0 w.id
Proof
  ho_match_mp_tac tableau_S4_ind >> ntac 2 gen_tac >> strip_tac >>
  simp[Once tableau_S4_def] >> simp[AllCaseEqs()] >> rw[]
  (* Trule *)
  >-(fs[] >> rw[] >> first_x_assum (qspec_then `w` ASSUME_TAC) >>
     fs[Once RTC_CASES1] >> rw[] >> first_x_assum irule >> reverse (rw[])
     >- metis_tac[wfm_S4_trule]
     >> drule tableau_S4_s_eq_id >> rw[] >> DISJ2_TAC >>
     qexists_tac `u` >> fs[pt_rel_def])
  (* S4 *)
  >-(fs[] >> rw[] >> fs[Once RTC_CASES1] >> rw[] >> fs[pt_rel_def] >>
     drule scmap_MEM >> rw[] >> fs[MEM_FILTER, MEM_undia] >>
     first_x_assum (drule_then strip_assume_tac) >>
     first_x_assum (drule_then strip_assume_tac) >>
     first_x_assum (drule_then strip_assume_tac) >>
     first_x_assum (drule_then strip_assume_tac) >>
     `wfm_S4_sequent Γ0
          (s with
           <|As := (e0,s.Sg)::s.As; Ss := SOME (e0,s.Sg); Hs := e0::s.Hs;
             Gm := e0::s.Sg|>)`
                by (first_x_assum (qspec_then `w` (fn _ => all_tac)) >>
                    fs[wfm_S4_sequent] >> rw[]
                    >-(`MEM (Dia e0) (closure_list_conc [Γ0])`
                         by metis_tac[SUBSET_DEF] >>
                       drule mem_closure_of_closure >> rw[] >>
                       metis_tac[mem_closure_self])
                    >-(`MEM (Dia e0) (closure_list_conc [Γ0])`
                         by metis_tac[SUBSET_DEF] >>
                       drule mem_closure_of_closure >> rw[] >>
                       metis_tac[mem_closure_self])
                    >- metis_tac[SUBSET_DEF, PSUBSET_DEF]
                    >- metis_tac[SUBSET_DEF]
                    >- metis_tac[SUBSET_DEF]
                    >- metis_tac[]
                    >> rw[SUBSET_DEF, INSERT_DEF]) >>
     first_x_assum (qspec_then `w` ASSUME_TAC) >>
     first_x_assum (drule_then strip_assume_tac) >>
     first_x_assum irule >> metis_tac[RTC_CASES1, pt_rel_def])
  (* Literal *)
  >-(fs[] >> rw[] >> fs[Once RTC_CASES1] >> rw[] >> fs[pt_rel_def])
  (* DISJ2 *)
  >-(fs[] >> rw[] >> fs[Once RTC_CASES1] >> rw[] >> fs[pt_rel_def] >>
     metis_tac[wfm_S4_Disj])
  (* DISJ1 *)
  >-(fs[] >> rw[] >> fs[Once RTC_CASES1] >> rw[] >> fs[pt_rel_def] >>
     metis_tac[wfm_S4_Disj])
  >> fs[] >> rw[] >> fs[Once RTC_CASES1] >> rw[] >> fs[pt_rel_def] >>
  metis_tac[wfm_S4_Conj]
QED

Theorem pluck_eq_none:
  ∀P l. pluck P l = NONE ⇒ ¬EXISTS P l
Proof
  Induct_on `l` >> rw[pluck_def] >> rw[EVERY_MEM] >>
  fs[EXISTS_MEM, EVERY_MEM, AllCaseEqs()]
QED

Theorem disjsplit_s4_MEM2:
  ∀Γ Γ1 Γ2 f1 f2.
     MEM f1 Γ1 ∧ MEM f2 Γ2 ∧ disjsplit_s4 Γ = SOME (pf, Γ1,Γ2) ⇒
     MEM f1 Γ ∨ MEM f2 Γ ∨ MEM (Disj f1 f2) Γ
Proof
  Induct >> simp[] >> Cases >> simp[PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED

Theorem tableau_S4_complete:
  ∀Γ0 s. wfm_S4_sequent Γ0 s ⇒
         tableau_S4 Γ0 s = CLOSED ⇒
         ∀M w.
             w ∈ M.frame.world ∧ reflexive_M M ∧ transitive_M M ⇒
             ∃f. MEM f (s.Gm++s.Sg) ∧ ¬forces M w f
Proof
   ho_match_mp_tac tableau_S4_ind >> ntac 2 gen_tac >>
   strip_tac >> simp[Once tableau_S4_def] >>
   simp[AllCaseEqs()] >> rw[] >~
   [‘trule_s4 s = NONE’]
   >- (* Trule contradiction *)
      (fs[] >> rw[] >> fs[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >>
       metis_tac[pluck_eq_none]) >~
   [‘trule_s4 s = SOME (pf,s')’]
   >- (* Trule *)
      (fs[] >> rw[] >> `wfm_S4_sequent Γ0 s'` by metis_tac[wfm_S4_trule] >>
       first_x_assum (qspec_then `ARB` (fn _ => all_tac)) >>
       first_x_assum (drule_all_then strip_assume_tac)
       >- (*   MEM f s'.Gm *)
          (rw[] >> drule mem_trule_gamma >> rw[] >>
           first_x_assum (drule_then strip_assume_tac)
           >- (qexists_tac `f` >> metis_tac[])
           >> qexists_tac `Box f` >> rw[] >> qexists_tac `w` >> fs[reflexive_M])
       >> (*  MEM f s'.Sg *) metis_tac[mem_trule_sigma]) >~
   [‘EXISTS is_dia s.Gm’, ‘MEM df _’]
   >- (* S4 *)
      (fs[MEM_FILTER] >>
       qpat_x_assum ‘∀pf s'. EXISTS is_box s.Gm ∧ trule_s4 s = SOME (pf,s') ⇒ _’
                    (fn _ => all_tac) >>
       first_x_assum (drule_then (drule_then strip_assume_tac)) >>
       first_x_assum (first_assum o mp_then (Pos last) strip_assume_tac) >>
       first_assum (first_assum o mp_then (Pos last) strip_assume_tac) >>
       first_x_assum (first_assum o mp_then (Pos last) strip_assume_tac) >>
       qpat_x_assum `wfm_S4_sequent Γ0
          (s with
           <|As := (df,s.Sg)::s.As; Ss := SOME (df,s.Sg); Hs := df::s.Hs;
             Gm := df::s.Sg|>) ∧
        tableau_S4 Γ0
          (s with
           <|As := (df,s.Sg)::s.As; Ss := SOME (df,s.Sg); Hs := df::s.Hs;
             Gm := df::s.Sg|>) =
        NONE ⇒
        ∃f. ((f = df ∨ MEM f s.Sg) ∨ MEM f s.Sg) ∧ ¬forces M w f` mp_tac >>
       impl_tac
       (* wfm *)
       >- (fs[wfm_S4_sequent] >> rw[]
           >- (rw[PSUBSET_DEF, INSERT_DEF] >> metis_tac[undia_dia_in_closure])
           >- metis_tac[undia_dia_in_closure]
           >- fs[PSUBSET_DEF, SUBSET_DEF]
           >> fs[MEM_undia, EXTENSION, SUBSET_DEF, mem_subset]) >> rw[]
       (* ∃f. (f = df ∨ MEM f s.Sg) ∧ ¬forces M w f *)
       >- (Cases_on `forces M w (Dia df)`
           >- (fs[] >>
               ‘wfm_S4_sequent Γ0
                (s with
                 <|As := (df,s.Sg)::s.As; Ss := SOME (df,s.Sg);
                   Hs := df::s.Hs; Gm := df::s.Sg|>)’
                 by (fs[wfm_S4_sequent] >> rw[]
                     >- metis_tac[undia_dia_in_closure]
                     >- metis_tac[undia_dia_in_closure]
                     >- fs[PSUBSET_DEF, SUBSET_DEF]
                     >> fs[MEM_undia, mem_subset]
                     >- metis_tac[SUBSET_DEF]
                     >> rw[SUBSET_DEF, INSERT_DEF]) >>
               ‘∃f. ((f = df ∨ MEM f s.Sg) ∨ MEM f s.Sg) ∧ ¬forces M v f’
                 by metis_tac[]
               >- metis_tac[] >>
               qexists_tac `f` >> rw[] >> fs[wfm_S4_sequent] >>
               fs[EVERY_MEM] >> first_x_assum (drule_then strip_assume_tac) >>
               ‘∃p. Box p = f’ by (Cases_on `f` >> fs[is_box_def]) >> rw[] >>
               fs[reflexive_M] >> qexists_tac `v'` >> rw[] >>
               fs[transitive_M] >> metis_tac[])
           >> fs[MEM_undia] >> qexists_tac `Dia df` >> rw[])
       >- (qexists_tac `f` >> fs[])
       >> (qexists_tac `f` >> fs[])) >~
   [‘disjsplit_s4 s.Gm = SOME (pf, Γ1, Γ2)’]
   >- (* Disj *)
      (drule_all_then strip_assume_tac wfm_S4_Disj >> fs[] >>
       rpt (first_x_assum (drule_all_then strip_assume_tac))
       >- (drule_all disjsplit_s4_MEM2 >> rw[]
           >- metis_tac[]
           >- metis_tac[] >>
           rename [‘MEM (Disj f1 f2) s.Gm’] >>
           qexists_tac ‘Disj f1 f2’ >> rw[] >> metis_tac[])
       >> metis_tac[]) >~
   [‘conjsplit_s4 s.Gm = SOME (pf, Γ')’]
   >- (* Con j *)
      (drule_all_then strip_assume_tac wfm_S4_Conj >> fs[] >>
       rpt (first_x_assum (drule_all_then strip_assume_tac))
       >- (drule_all conjsplit_s4_MEM2 >> rw[] >>
           metis_tac[forces_def])
       >> metis_tac[]) >~
   [‘contradiction Γ = SOME j’] >>
   (* Literal *)fs[] >>
   drule_then strip_assume_tac contradiction_EQ_SOME >>
   Cases_on ‘w ∈ M.valt j’
   >- (qexists_tac ‘NVar j’ >> simp[]) >>
   qexists_tac ‘Var j’ >> simp[]
QED

Theorem final_tableau_S4_complete:
  ∀f.  final_tableau_S4 f = CLOSED ⇒
       ∀M w.
         w ∈ M.frame.world ∧ reflexive_M M ∧ transitive_M M ⇒
         ¬forces M w f
Proof
  rw[final_tableau_S4_def] >> drule_at (Pos $ el 2) tableau_S4_complete >>
  rw[] >> first_x_assum irule >> rw[] >>
  simp[wfm_S4_sequent] >> rw[PSUBSET_DEF]
  >- (Cases_on `f` >> fs[]) >> metis_tac[mem_closure_self]
QED

Definition pre_hintikka_def:
  pre_hintikka l =
    (
      contradiction l = NONE ∧
      (∀f1 f2. MEM (Conj f1 f2) l ⇒ MEM f1 l ∧ MEM f2 l) ∧
      (∀f1 f2. MEM (Disj f1 f2) l ⇒ MEM f1 l ∨ MEM f2 l) ∧
      (∀f. MEM (Box f) l ⇒ MEM f l)
    )
End

Theorem tableau_S4_s_eq_id':
  ∀Γ0 s m. tableau_S4 Γ0 s = SOME m ⇒ m.id = s
Proof
  Cases_on `m` >> PairCases_on `a` >> rw[Once tableau_S4_def] >>
  fs[AllCaseEqs()]
QED

Theorem pre_hintikka_box_cons:
  ∀f h. pre_hintikka h ∧ MEM f h ⇒ pre_hintikka ((Box f)::h)
Proof
  rw[pre_hintikka_def] >> rw[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem conjsplit_s4_EQ_NONE:
  ∀Γ. conjsplit_s4 Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Conj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem disjsplit_s4_EQ_NONE:
  ∀Γ. disjsplit_s4 Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Disj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem pre_hintikka_s4:
∀G.
  contradiction G = NONE ∧
  conjsplit_s4 G = NONE ∧
  disjsplit_s4 G = NONE ∧
  EVERY ($¬ ∘ is_box) G
  ⇒
  pre_hintikka G
Proof
  rw[pre_hintikka_def]
  >- metis_tac[conjsplit_s4_EQ_NONE]
  >- metis_tac[conjsplit_s4_EQ_NONE]
  >- metis_tac[disjsplit_s4_EQ_NONE]
  >> fs[EVERY_MEM] >> metis_tac[is_box_def]
QED

Theorem pre_hintikka_disj_left_cons:
  ∀f1 h. pre_hintikka h ∧ MEM f1 h ⇒ ∀f2. pre_hintikka ((Disj f1 f2)::h)
Proof
  rw[pre_hintikka_def] >> rw[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem disj_s4_pf_eq_some:
  ∀s pf s1 s2. disjsplit_s4 s = SOME (pf, s1, s2) ⇒
    ∃f1 f2. pf = (Disj f1 f2) ∧ MEM f1 s1 ∧ MEM f2 s2 ∧
      set s ⊆ pf INSERT set s1 ∧ set s ⊆ pf INSERT set s2
Proof
  ho_match_mp_tac disjsplit_s4_ind >> rw[disjsplit_s4_def] >> rw[SUBSET_DEF] >>
  TRY (PairCases_on `z` >> fs[]) >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem disj_s4_g2_in_g0:
  ∀s pf s1 s2. disjsplit_s4 s = SOME (pf, s1, s2) ⇒
               set s2 ⊆ set (closure_list_conc s)
Proof
  ho_match_mp_tac disjsplit_s4_ind >> rw[SUBSET_DEF]
  >-(Cases_on `x = f2` >> fs[] >> rw[]
     >- metis_tac[mem_closure_self]
     >> metis_tac[mem_lst_closure])
  >-(PairCases_on `z` >> fs[] >> rw[] >> Cases_on `x = Var v2` >> fs[])
  >> PairCases_on `z` >> fs[] >> rw[] >> Cases_on `x = NVar v2` >> fs[]
QED

Theorem disj_s4_g1_in_g0:
  ∀s pf s1 s2.
    disjsplit_s4 s = SOME (pf, s1, s2) ⇒ set s1 ⊆ set (closure_list_conc s)
Proof
  ho_match_mp_tac disjsplit_s4_ind >> rw[SUBSET_DEF]
  >-(Cases_on `x = f1` >> fs[] >> rw[]
     >- metis_tac[mem_closure_self]
     >> metis_tac[mem_lst_closure])
  >-(PairCases_on `z` >> fs[] >> rw[] >> Cases_on `x = Var v2` >> fs[])
  >> PairCases_on `z` >> fs[] >> rw[] >> Cases_on `x = NVar v2` >> fs[]
QED

Theorem pre_hintikka_disj_right_cons:
  ∀f2 h. pre_hintikka h ∧ MEM f2 h ⇒ ∀f1. pre_hintikka ((Disj f1 f2)::h)
Proof
  rw[pre_hintikka_def] >> rw[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem pre_hintikka_conj_cons:
  ∀f1 f2 h.
    pre_hintikka h ∧ MEM f1 h ∧ MEM f2 h ⇒ pre_hintikka ((Conj f1 f2)::h)
Proof
  rw[pre_hintikka_def] >> rw[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem conj_s4_pf_eq_some:
  ∀s pf s1 s2 g. conjsplit_s4 s = SOME (pf, g) ⇒
    ∃f1 f2. pf = (Conj f1 f2) ∧ MEM f1 g ∧ MEM f2 g ∧ set s ⊆ pf INSERT set g
Proof
  ho_match_mp_tac conjsplit_s4_ind >> rw[conjsplit_s4_def] >> rw[SUBSET_DEF] >>
  TRY (PairCases_on `z` >> fs[]) >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem premodel_size_thm[simp] = definition "premodel_size_def"

Definition thm_3_17_prop:
  thm_3_17_prop (Nd (id, h, r) cs) ⇔ pre_hintikka h ∧
                                     set id.Gm ⊆ set h ∧
                                     ∀s. MEM s cs ⇒ thm_3_17_prop s
Termination
  WF_REL_TAC `measure (premodel_size (K 1))`
End
 (* >> Induct_on `cs` >> fs[] >> rw[]
  >- rw[] >> first_x_assum (drule_then strip_assume_tac) >> simp[]
End *)
(* TODO: Not sure why this part of the termination proof
         is no longer needed *)


Theorem thm_3_17_prop_RTC:
  ∀m w. thm_3_17_prop m ⇒ RTC pt_rel m w ⇒ thm_3_17_prop w
Proof
  Induct_on `RTC` >> rw[] >> Cases_on `m` >> PairCases_on `a` >>
  fs[thm_3_17_prop] >> fs[pt_rel_def]
QED

Theorem thm_3_17:
  ∀Γ0 s m.
    tableau_S4 Γ0 s = OPEN m ⇒ thm_3_17_prop m
Proof
  ho_match_mp_tac tableau_S4_ind >> ntac 3 strip_tac >>
  simp[Once tableau_S4_def] >>
  simp[AllCaseEqs()] >> rpt gen_tac >> strip_tac >> fs[]
  >- (* trule *)
    (rw[] >> fs[thm_3_17_prop] >> rw[] >>
     drule tableau_S4_s_eq_id >> rw[] >> drule pre_hintikka_box_cons >> rw[] >>
     fs[trule_s4_def, AllCaseEqs(), PULL_EXISTS]
     (* MEM b s.Sg ==> pre_hintikka,  *)
     >-(rw[] >> fs[wfm_S4_sequent, EVERY_MEM] >> `is_box b` by metis_tac[] >>
        Cases_on `b` >> fs[] >> rw[] >> fs[dest_box_def])
     (* not MEM b s.Sg ==> pre_hintikka *)
     >-(rw[] >> fs[] >> drule pluck_eq_some_append >> rw[] >> fs[] >> rw[] >>
        Cases_on `b` >> fs[dest_box_def])
     (* MEM b s.Sg ==> sbst *)
     >-(rw[] >> fs[] >> drule pluck_eq_some_append >> rw[] >> fs[] >> rw[] >>
        Cases_on `b` >> fs[dest_box_def] >> rw[] >> fs[SUBSET_DEF])
     (* not MEM b s.Sg ==> sbst *)
     >> rw[] >> fs[] >> drule pluck_eq_some_append >> rw[] >> fs[] >> rw[] >>
        Cases_on `b` >> fs[dest_box_def] >> rw[] >> fs[SUBSET_DEF])
  >- (* s4 *)
    (rw[] >> fs[thm_3_17_prop] >> rw[]
     >- metis_tac[pre_hintikka_s4] >>
     last_x_assum irule >> drule_all scmap_MEM >>
     rw[MEM_FILTER, MEM_undia] >> metis_tac[])
  >- (* request *)
    (rw[] >> fs[thm_3_17_prop] >> rw[] >> metis_tac[pre_hintikka_s4])
  >- (* disj right *)
    (rw[] >> fs[thm_3_17_prop] >> rw[]
     >- (drule_then strip_assume_tac disj_s4_pf_eq_some >> rw[] >>
        irule pre_hintikka_disj_right_cons >> rw[] >>
        drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
        metis_tac[SUBSET_DEF]) >>
     drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
     drule_then strip_assume_tac disj_s4_pf_eq_some >> rw[] >> fs[SUBSET_DEF] >>
     metis_tac[])
  >- (* disj left *)
    (rw[] >> fs[thm_3_17_prop] >> rw[]
     >- (drule_then strip_assume_tac disj_s4_pf_eq_some >> rw[] >>
        irule pre_hintikka_disj_left_cons >> rw[] >>
        drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
        metis_tac[SUBSET_DEF]) >>
     drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
     drule_then strip_assume_tac disj_s4_pf_eq_some >> rw[] >>
     fs[SUBSET_DEF] >> metis_tac[])
  >> (* conj *)
     rw[] >> fs[thm_3_17_prop] >> rw[]
     >- (drule_then strip_assume_tac conj_s4_pf_eq_some >> rw[] >>
        drule_then strip_assume_tac pre_hintikka_conj_cons >> rw[] >>
        drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
        metis_tac[SUBSET_DEF]) >>
  drule_then strip_assume_tac tableau_S4_s_eq_id >> rw[] >> fs[] >>
  drule_then strip_assume_tac conj_s4_pf_eq_some >> rw[] >> fs[SUBSET_DEF] >>
  metis_tac[]
QED

Theorem trule_sg_subset:
  ∀id f pf id'. MEM f id.Sg ∧ trule_s4 id = SOME (pf, id') ⇒ MEM f id'.Sg
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[]
QED

Theorem trule_s4_pf_sg:
  ∀id pf id'. trule_s4 id = SOME (pf, id') ⇒ MEM pf id'.Sg
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[]
QED

Theorem trule_s4_As_eq:
  ∀id pf id'. trule_s4 id = SOME (pf, id') ⇒ id.As = id'.As
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[]
QED

Theorem his_sig_pair_in_local:
  ∀p hs sg.  MEM (p,sg) (s4_request_local hs sg) ⇔ MEM p hs
Proof
  Induct_on `hs` >> rw[] >> first_x_assum (drule_then strip_assume_tac) >>
  metis_tac[]
QED

Theorem all_his_id_sg:
  ∀g d hs sg. MEM (g, d) (s4_request_local hs sg) ⇒ d = sg
Proof
  Induct_on `hs` >> rw[] >> first_x_assum drule >> simp[]
QED

Definition thm_3_19_prop[simp]:
  thm_3_19_prop (Nd (id, h, r) l) ⇔
            (∀s p. MEM s l ∧ MEM p id.Sg ⇒ MEM p (get_htk s)) ∧
            (∀s p. MEM s l ∧ MEM (Box p) h ⇒ MEM (Box p) (get_htk s)) ∧
            (∀p.
                 MEM (Dia p) h ⇒
                 (∃d. MEM (p,d) r) ∨ ∃s. MEM s l ∧ MEM p (get_htk s)) ∧
            (∀g d p. MEM (g,d) r ∧ MEM (Box p) (h ⧺ id.Sg) ⇒ MEM (Box p) d) ∧
            set r ⊆ set id.As ∧
            (∀s. MEM s l ⇒ thm_3_19_prop s)
Termination
  WF_REL_TAC `measure (premodel_size (K 1))`
End

Definition thm_3_19_prop':
  thm_3_19_prop' m ⇔
    (∀s p. MEM s m.l ∧ MEM p m.id.Sg ⇒ MEM p (get_htk s)) ∧
    (∀s p. MEM s m.l ∧ MEM (Box p) m.htk ⇒ MEM (Box p) (get_htk s)) ∧
    (∀p.
       MEM (Dia p) m.htk ⇒
       (∃d. MEM (p,d) m.request) ∨ ∃s. MEM s m.l ∧ MEM p (get_htk s)) ∧
    (∀g d p. MEM (g,d) m.request ∧ MEM (Box p) (m.htk ⧺ m.id.Sg) ⇒
             MEM (Box p) d) ∧
    set m.request ⊆ set m.id.As ∧
    (∀s. MEM s m.l ⇒ thm_3_19_prop' s)
Termination
  WF_REL_TAC `measure (premodel_size (K 1))` >>
  Cases_on `m` >> PairCases_on `a` >> Induct_on `l` >> fs[] >> rw[]
  >- rw[] >> first_x_assum (drule_then strip_assume_tac) >> simp[]
End

Theorem thm_3_19_prop_RTC:
  ∀m w. thm_3_19_prop m ⇒ RTC pt_rel m w ⇒ thm_3_19_prop w
Proof
  Induct_on `RTC` >> rw[] >> Cases_on `m` >> PairCases_on `a` >>
  fs[thm_3_19_prop] >> fs[pt_rel_def]
QED

Theorem thm_3_19_2_RTC_pt_rel:
  ∀w s p. thm_3_19_prop w ⇒ RTC pt_rel w s ∧ MEM (Box p) w.htk ⇒
          MEM (Box p) s.htk
Proof
  Induct_on `RTC` >> rw[] >> Cases_on `w` >> PairCases_on `a` >>
  fs[thm_3_19_prop] >> fs[pt_rel_def]
QED

Theorem S4_sequent_component_equality[allow_rebind] =
  DB.fetch "-" "S4_sequent_component_equality"
(*
h: htk
r: request
*)
Theorem thm_3_19:
  ∀Γ0 Γ m. tableau_S4 Γ0 Γ = OPEN m ⇒ thm_3_19_prop m
Proof
  ho_match_mp_tac tableau_S4_ind >> ntac 3 strip_tac >>
  ONCE_REWRITE_TAC[tableau_S4_def] >> simp_tac(srw_ss ())[AllCaseEqs()] >>
  rpt strip_tac
  (* Trule *)
  >- (rw[] >> fs[]
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
        metis_tac[trule_sg_subset])
      >- (fs[] >> rw[] >> fs[] >> rw[] >>
          drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          metis_tac[trule_s4_pf_sg])
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          fs[] >> rw[] >> fs[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >>
          fs[] >> rw[] >> drule pluck_eq_some_append >> rw[])
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          fs[] >> rw[] >> metis_tac[trule_s4_pf_sg])
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          metis_tac[trule_sg_subset])
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          metis_tac[trule_sg_subset])
      >- (fs[] >> rw[] >> drule_then SUBST_ALL_TAC tableau_S4_s_eq_id >>
          metis_tac[trule_s4_As_eq]))
  (* S4 *)
  >- (fs[AllCaseEqs()] >> rw[]
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> rw[] >> drule_all scmap_MEM >>
          rw[MEM_FILTER] >> first_x_assum (drule_then drule) >> Cases_on `s` >>
          PairCases_on `a` >> disch_then $ drule_then strip_assume_tac >>
          simp[] >> drule thm_3_17 >> fs[thm_3_17_prop] >> rw[] >>
          drule_then (SUBST_ALL_TAC o SYM) tableau_S4_s_eq_id >> fs[] >>
          metis_tac[SUBSET_DEF])
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> fs[EVERY_MEM] >>first_x_assum drule >>
          rw[])
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> rw[] >> Cases_on `MEM p Γ.Hs`
          >- (fs[wfm_S4_sequent] >> first_x_assum drule >> rw[] >>
              DISJ1_TAC >> qexists_tac `Γ.Sg` >>
              metis_tac[his_sig_pair_in_local]) >>
          first_x_assum drule >> fs[MEM_undia] >> strip_tac >>
          drule scmap_MEM2 >>
          simp[MEM_FILTER, MEM_undia] >> disch_then drule_all >> rw[] >>
          Cases_on `e` >> PairCases_on `a` >> first_x_assum drule >> rw[] >>
          DISJ2_TAC >> qexists_tac `(Nd (a0,a1,a2) l)` >> rw[] >>
          drule thm_3_17 >> fs[thm_3_17_prop] >>
          rw[] >> drule_then (SUBST_ALL_TAC o SYM) tableau_S4_s_eq_id >> fs[])
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> rw[] >> fs[EVERY_MEM] >>
          metis_tac[is_box_def])
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> rw[] >> fs[wfm_S4_sequent] >>
          metis_tac[all_his_id_sg])
      >- (fs[] >> rw[] >>
          first_x_assum (qspecl_then [`f`, `gamma`] (K all_tac)) >>
          fs[AllCaseEqs(), MEM_FILTER] >> rw[] >> fs[wfm_S4_sequent] >>
          rw[SUBSET_DEF] >> Cases_on `x` >> drule all_his_id_sg >> rw[] >>
          metis_tac[his_sig_pair_in_local])
      >- (fs[MEM_FILTER] >> drule scmap_MEM >> rw[MEM_FILTER] >>
          first_x_assum drule >> rw[] >> metis_tac[]))
  (* Litral *)
  >- (rw[] >> fs[]
      >- (fs[EVERY_MEM] >> first_x_assum drule >> metis_tac[is_dia_def])
      >- (fs[EVERY_MEM] >> first_x_assum drule >> metis_tac[is_box_def])
      >- (drule all_his_id_sg >> rw[])
      >- (rw[SUBSET_DEF] >> Cases_on `x` >> drule all_his_id_sg >> rw[] >>
          fs[wfm_S4_sequent] >> metis_tac[his_sig_pair_in_local]))
  (* disj2 *)
  >- (rw[] >> fs[]
      >- (‘Γ with <|Ss := NONE; Gm := Γ2|> = id’
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ2|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ2|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> `Γ with <|Ss := NONE; Gm := Γ2|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.As = id.As` by fs[S4_sequent_component_equality] >> fs[]))
  (* disj1 *)
  >- (rw[] >> fs[]
      >- (`Γ with <|Ss := NONE; Gm := Γ1|> = id`
             by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule disj_s4_pf_eq_some >> rw[] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ1|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ1|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> `Γ with <|Ss := NONE; Gm := Γ1|> = id`
           by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.As = id.As` by fs[S4_sequent_component_equality] >> fs[]))
  (* conj *)
  >- (rw[] >> fs[]
      >- (`Γ with <|Ss := NONE; Gm := Γ'|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[])
      >- (fs[] >> rw[] >> drule conj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule conj_s4_pf_eq_some >> rw[] >> fs[])
      >- (fs[] >> rw[] >> drule conj_s4_pf_eq_some >> rw[] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ'|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> fs[wfm_S4_sequent] >>
          `Γ with <|Ss := NONE; Gm := Γ'|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.Sg = id.Sg` by fs[S4_sequent_component_equality] >> fs[] >>
          metis_tac[])
      >- (fs[] >> rw[] >> `Γ with <|Ss := NONE; Gm := Γ'|> = id`
            by metis_tac[tableau_S4_s_eq_id] >>
          `Γ.As = id.As` by fs[S4_sequent_component_equality] >> fs[]))
QED

Theorem pt_rel_attach:
  ∀u cs s. MEM u cs ∧ RTC pt_rel u s ⇒
           ∀id h r. RTC pt_rel (Nd (id, h, r) cs) s
Proof
  rw[] >> simp[Once RTC_CASES1, pt_rel_def] >> metis_tac[]
QED

Theorem pt_rel_attach_r':
  ∀u v w. RTC pt_rel u v ∧ MEM w v.l ⇒ RTC pt_rel u w
Proof
  rw[] >> Cases_on `v` >> fs[] >>
  simp[Once RTC_CASES2, pt_rel_def] >>
  metis_tac[]
QED

Theorem trule_s4_Ss_reset:
  ∀s pf s'. trule_s4 s = SOME (pf, s') ⇒ s'.Ss = NONE
Proof
  simp[trule_s4_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> fs[]
QED

Definition thm_3_20_prop:
  thm_3_20_prop m ⇔
      (∀s r. RTC pt_rel m s ∧ MEM r s.request ⇒
        MEM r m.id.As ∨ ∃d. RTC pt_rel m d ∧ SOME r = d.id.Ss) ∧
      (∀s. pt_rel m s ⇒ thm_3_20_prop s)
Termination
  WF_REL_TAC `measure (premodel_size (K 1))` >> Cases_on `m` >>
  rw[pt_rel_def] >> Induct_on `l` >> fs[] >> rw[] >- simp[]
  >> fs[]
End

Theorem thm_3_20_prop_RTC:
  ∀m w. thm_3_20_prop m ⇒ RTC pt_rel m w ⇒ thm_3_20_prop w
Proof
  Induct_on `RTC` >> rw[] >> Cases_on `m` >> PairCases_on `a` >>
  pop_assum mp_tac >> simp[Once thm_3_20_prop]
QED

(* thm_3_20 *)
Theorem s4_fulfillment:
  ∀Γ0 Γ m s. tableau_S4 Γ0 Γ = OPEN m ⇒ thm_3_20_prop m
Proof
  ho_match_mp_tac tableau_S4_ind >> ntac 3 strip_tac >>
  ONCE_REWRITE_TAC[tableau_S4_def] >> ONCE_REWRITE_TAC[tableau_S4_def] >>
  rewrite_tac[AllCaseEqs()] >> rpt strip_tac >>~-
  ([‘CLOSED = OPEN _’] , gs[]) >~
  [‘trule_s4 Γ = SOME x’] (* trule *)
  >- (Cases_on `x` >> fs[] >> rw[] >>
      Cases_on `tableau_S4 Γ0 r` >> fs[] >>
      Cases_on `x` >> PairCases_on `a` >> fs[] >>
      fs[Once thm_3_20_prop] >> rw[]
      (* current *)
      >- (qpat_x_assum `RTC _ _ _` mp_tac >>
          simp[SimpL ``$==>``, Once RTC_CASES1] >>
          strip_tac
          (* fulfilled in As *)
          >- (rw[] >> fs[] >> drule thm_3_19 >> fs[thm_3_19_prop] >> rw[] >>
              drule trule_s4_As_eq >>
              rw[] >> drule tableau_S4_s_eq_id >> rw[] >> metis_tac[SUBSET_DEF])
          (* fulfilled in descendant *)
          >> fs[pt_rel_def] >> drule_all pt_rel_attach >> rw[] >>
          first_x_assum (qspecl_then [`a0`, `a1`, `a2`] (ASSUME_TAC)) >>
          last_x_assum (drule_all_then strip_assume_tac)
          >- (drule trule_s4_As_eq >> rw[] >> drule tableau_S4_s_eq_id >> rw[])
          >> qpat_x_assum `RTC _ _ _` mp_tac >>
          simp[SimpL ``$==>``, Once RTC_CASES1] >> rw[]
          >- (fs[] >> drule trule_s4_Ss_reset >> rw[] >>
              drule tableau_S4_s_eq_id >> rw[] >> fs[])
          >> fs[pt_rel_def] >> metis_tac[pt_rel_attach])
      (* descendant *)
      >> fs[pt_rel_def]) >~
  [‘¬EXISTS is_box Γ.Gm’, ‘EXISTS is_dia Γ.Gm’]
  (* S4 *)
  >- (fs[] >> rw[] >> first_x_assum (qspecl_then [`pf`, `gm`] (K all_tac)) >>
      fs[MEM_FILTER, AllCaseEqs()] >> rw[] >> simp[Once thm_3_20_prop] >> rw[]
       (* current *)
       >- (qpat_x_assum `RTC _ _ _` mp_tac >>
           simp[SimpL ``$==>``, Once RTC_CASES1] >> rw[]
           >- (fs[] >> fs[wfm_S4_sequent] >> Cases_on `r` >>
               drule all_his_id_sg >> rw[] >> metis_tac[his_sig_pair_in_local])
           >> drule scmap_MEM >> rw[MEM_FILTER, MEM_undia] >>
           `MEM u ms` by fs[pt_rel_def] >>
           first_x_assum (drule_all_then strip_assume_tac) >>
           fs[MEM_undia] >> first_x_assum (drule_all_then strip_assume_tac) >>
           fs[Once thm_3_20_prop] >>
           first_x_assum (drule_all_then strip_assume_tac)
           >- (`RTC pt_rel (Nd (Γ,Γ.Gm,s4_request_local Γ.Hs Γ.Sg) ms) u`
                 by metis_tac[RTC_CASES1] >>
               Cases_on `u` >> PairCases_on `a` >> drule tableau_S4_s_eq_id >>
               rw[] >> fs[] >> DISJ2_TAC >>
               qexists_tac
               `(Nd
                 (Γ with
                  <|As := (e0,Γ.Sg)::Γ.As; Ss := SOME (e0,Γ.Sg); Hs := e0::Γ.Hs;
                    Gm := e0::Γ.Sg|>,a1,a2) l)` >> rw[])
           >> DISJ2_TAC >> fs[pt_rel_def] >> drule_all pt_rel_attach >>
           metis_tac[])
        (* descendant *)
        >> drule scmap_MEM >> rw[MEM_FILTER, MEM_undia] >>
           `MEM s ms` by fs[pt_rel_def] >>
           first_x_assum (drule_all_then strip_assume_tac) >>
           first_x_assum (drule_then strip_assume_tac) >> fs[MEM_undia]) >~
  [‘¬EXISTS is_box Γ.Gm’, ‘¬EXISTS is_dia Γ.Gm’]
  (* Literal *)
  >- (fs[] >> rw[] >> first_x_assum (qspecl_then [`pf`, `gm`] (K all_tac)) >>
      first_x_assum (qspecl_then [`pf`] (K all_tac)) >>
      simp[Once thm_3_20_prop] >> rw[]
      (* current *)
      >- (fs[Once RTC_CASES1]
          >- (fs[wfm_S4_sequent] >>
              `MEM r (s4_request_local Γ.Hs Γ.Sg)` by metis_tac[get_request] >>
              Cases_on `r` >> drule all_his_id_sg >> rw[] >>
             `MEM q Γ.Hs` by metis_tac[his_sig_pair_in_local] >> metis_tac[])
          >> fs[pt_rel_def])
      (* descendant *)
      >> fs[pt_rel_def]) >~
  [‘disjsplit_s4 Γ.Gm = SOME x’]
  (* disj2 *)
  >- (fs[] >> rw[] >> PairCases_on `x` >> fs[] >> simp[Once thm_3_20_prop] >>
      rw[]
      (* current fulfillment *)
      >- (fs[Once RTC_CASES1]
          >-(Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
             >-(Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x2|>)` >>
                fs[] >> Cases_on `x` >> PairCases_on `a` >> fs[] >>
                drule thm_3_19 >> rw[] >>
                drule tableau_S4_s_eq_id >> rw[] >> fs[] >>
                metis_tac[SUBSET_DEF])
             >> Cases_on `x` >> PairCases_on `a` >> fs[] >> drule thm_3_19 >>
             rw[] >> drule tableau_S4_s_eq_id >> rw[] >> fs[] >>
             metis_tac[SUBSET_DEF])
          >> Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
          >-(Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x2|>)` >>
             fs[] >>
             Cases_on `x` >> PairCases_on `a` >> fs[] >>
             fs[pt_rel_def, Once thm_3_20_prop] >>
             rw[] >> drule pt_rel_attach >> rw[] >>
             first_x_assum (qspecl_then [`s`, `a0`, `a1`, `a2`] (ASSUME_TAC)) >>
             first_x_assum drule >> rw[] >>
             last_x_assum (drule_all_then strip_assume_tac)
             >-(drule tableau_S4_s_eq_id >> rw[] >> fs[])
             >> qpat_x_assum `RTC pt_rel (_ _ _) d` mp_tac >>
             simp[Once RTC_CASES1] >>
             rw[pt_rel_def]
             >- (drule tableau_S4_s_eq_id >> rw[] >> fs[])
             >> DISJ2_TAC >> qexists_tac `d` >> rw[RIGHT_AND_OVER_OR] >>
             DISJ2_TAC >> qexists_tac `u'` >> rw[])
          >> Cases_on `x` >> PairCases_on `a` >> fs[] >>
          fs[pt_rel_def, Once thm_3_20_prop] >>
          rw[] >> drule pt_rel_attach >> rw[] >>
          first_x_assum (qspecl_then [`s`, `a0`, `a1`, `a2`] (ASSUME_TAC)) >>
          first_x_assum drule >> rw[] >>
          last_x_assum (drule_all_then strip_assume_tac)
          >-(drule tableau_S4_s_eq_id >> rw[] >> fs[])
          >> qpat_x_assum `RTC pt_rel (_ _ _) d` mp_tac >>
          simp[Once RTC_CASES1] >> rw[pt_rel_def]
          >- (drule tableau_S4_s_eq_id >> rw[] >> fs[])
          >> DISJ2_TAC >> qexists_tac `d` >> rw[RIGHT_AND_OVER_OR] >>
          DISJ2_TAC >> qexists_tac `u'` >> rw[])
      (* descendant fulfillment*)
      >> Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
         >-(Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x2|>)` >> fs[]>>
            Cases_on `x` >> PairCases_on `a` >> fs[] >> rw[] >>
            fs[Once thm_3_20_prop] >>
            `pt_rel (Nd (a0,a1,a2) l) s` by fs[pt_rel_def] >>
            metis_tac[thm_3_20_prop])
         >> Cases_on `x` >> PairCases_on `a` >> fs[] >> rw[] >>
      fs[Once thm_3_20_prop] >>
      `pt_rel (Nd (a0,a1,a2) l) s` by fs[pt_rel_def] >>
      metis_tac[thm_3_20_prop]) >~
  [‘conjsplit_s4 Γ.Gm = SOME x’]
  >- (fs[] >> rw[] >> PairCases_on `x` >> fs[] >> simp[Once thm_3_20_prop] >>
      rw[]
      (* current fulfillment *)
      >- (fs[Once RTC_CASES1]
          >-(Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
             >> Cases_on `x` >> PairCases_on `a` >> fs[] >> drule thm_3_19 >>
             rw[]
             >> drule tableau_S4_s_eq_id >> rw[] >> fs[] >>
             metis_tac[SUBSET_DEF])
          >> Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
          >> Cases_on `x` >> PairCases_on `a` >> fs[] >>
          fs[pt_rel_def, Once thm_3_20_prop]
          >> rw[] >> drule pt_rel_attach >> rw[]
          >> first_x_assum (qspecl_then [`s`, `a0`, `a1`, `a2`] (ASSUME_TAC))
          >> first_x_assum drule >> rw[] >>
          last_x_assum (drule_all_then strip_assume_tac)
          >-(drule tableau_S4_s_eq_id >> rw[] >> fs[])
          >> qpat_x_assum `RTC pt_rel (_ _ _) d` mp_tac >>
          simp[Once RTC_CASES1] >> rw[pt_rel_def]
          >- (drule tableau_S4_s_eq_id >> rw[] >> fs[])
          >> DISJ2_TAC >> qexists_tac `d` >> rw[RIGHT_AND_OVER_OR] >>
          DISJ2_TAC >> qexists_tac `u'` >> rw[])
      (* descendant fulfillment*)
      >> Cases_on `tableau_S4 Γ0 (Γ with <|Ss := NONE; Gm := x1|>)` >> fs[]
      >> Cases_on `x` >> PairCases_on `a` >> fs[] >> rw[] >>
      fs[Once thm_3_20_prop]
      >> `pt_rel (Nd (a0,a1,a2) l) s` by fs[pt_rel_def] >>
      metis_tac[thm_3_20_prop])
QED

(*
A state s reaches a state t by one step,
  if t is a child of s,
  or the signature of t is in the request of s.
*)

Definition reach_step:
  reach_step m s t ⇔
    MEM t s.l ∨ ∃sig. RTC pt_rel m t ∧ t.id.Ss = SOME sig ∧ MEM sig s.request
End

Definition s4_tree_model:
  s4_tree_model m =
    <| frame := <| rel := RTC (reach_step m);
                   world := {m' | RTC (reach_step m) m m'}; |>;
       valt   := (λv s. MEM (Var v) s.htk);
    |>
End

Theorem reach_step_from_root:
∀f m x w.
  final_tableau_S4 f = OPEN m ⇒
    RTC (reach_step m) x w ⇒
      RTC pt_rel m x ⇒
      RTC pt_rel m w
Proof
  simp[final_tableau_S4_def] >> ntac 2 gen_tac >> Induct_on `RTC` >>
  rw[] >> first_x_assum (drule_then strip_assume_tac) >> fs[reach_step] >>
  first_x_assum irule >> irule (CONJUNCT2 $ SPEC_ALL $ RTC_RULES_RIGHT1) >>
  simp[pt_rel_def] >> simp[PULL_EXISTS] >> Cases_on `x` >> fs[] >> metis_tac[]
QED

Theorem reach_step_from_root':
∀x w.
    RTC (reach_step m) x w ⇒
      RTC pt_rel m x ⇒
      RTC pt_rel m w
Proof
  Induct_on `RTC` >>
  rw[] >> fs[reach_step] >> metis_tac[pt_rel_attach_r']
QED

Definition tableau_S4_Ss_eq_Gm_prop:
  tableau_S4_Ss_eq_Gm_prop m ⇔
  (m.id.Ss = NONE ∨ ∃p sg. m.id.Ss = SOME (p, sg) ∧ set (p::sg) ⊆ set m.id.Gm) ∧
  (∀s. pt_rel m s ⇒ tableau_S4_Ss_eq_Gm_prop s)
Termination
  WF_REL_TAC `measure (premodel_size (K 1))` >> Cases_on `m` >> rw[pt_rel_def]>>
  Induct_on `l` >> fs[] >> rw[]
  >- simp[]
  >> fs[]
End

Theorem tableau_S4_Ss_eq_Gm_prop_RTC:
  ∀m w. tableau_S4_Ss_eq_Gm_prop m ⇒ RTC pt_rel m w ⇒ tableau_S4_Ss_eq_Gm_prop w
Proof
  Induct_on `RTC` >> rw[] >> pop_assum mp_tac >>
  simp[Once tableau_S4_Ss_eq_Gm_prop]
QED

Theorem tableau_S4_Ss_eq_Gm:
  ∀Γ0 s m. tableau_S4 Γ0 s = OPEN m ⇒
           wfm_S4_sequent Γ0 s ⇒
           tableau_S4_Ss_eq_Gm_prop m
Proof
  ho_match_mp_tac tableau_S4_ind >> ntac 3 strip_tac >>
  simp[Once tableau_S4_Ss_eq_Gm_prop] >> simp[Once tableau_S4_def] >>
  simp[AllCaseEqs()] >> ntac 2 strip_tac >> gvs[] >~
  [‘trule_s4 s = SOME (pf, s')’]
  (* Trule *)
  >-(conj_tac
     >-(fs[wfm_S4_sequent] >> Cases_on `s.Ss` >> fs[] >>
        rename [‘s.Ss = SOME x’] >> Cases_on ‘x’ >>
        rw[]) >>
     first_x_assum (qspec_then `df` (K all_tac)) >>
     drule wfm_S4_trule >> rw[] >> first_x_assum (drule_then strip_assume_tac)>>
     rename [‘pt_rel (Nd (s,pf::h,r) cs) s''’] >>
     ‘pt_rel (Nd (id, h, r) cs) s''’ by fs[pt_rel_def] >>
     metis_tac[tableau_S4_Ss_eq_Gm_prop]) >~
  [‘EXISTS is_dia s.Gm’]
  (* S4 *)
  >-(first_x_assum (qspecl_then [`pf`, `gm`] (K all_tac)) >> conj_tac
     >-(fs[wfm_S4_sequent] >>
        Cases_on `s.Ss` >> fs[] >>
        rename [‘s.Ss = SOME x’] >> Cases_on `x` >> rw[]) >>
     fs[pt_rel_def] >> rw[] >> drule scmap_MEM >> rw[] >> first_x_assum drule >>
     rw[] >>
     `wfm_S4_sequent Γ0
      (s with <|As := (e0,s.Sg)::s.As; Ss := SOME (e0,s.Sg); Hs := e0::s.Hs;
                Gm := e0::s.Sg|>)`
       by (fs[wfm_S4_sequent] >> rw[]
           >- fs[MEM_FILTER]
           >-(fs[MEM_FILTER] >> metis_tac[undia_dia_in_closure])
           >-(fs[MEM_FILTER] >> metis_tac[undia_dia_in_closure])
           >- fs[PSUBSET_DEF, SUBSET_DEF]
           >- fs[MEM_FILTER, MEM_undia, SUBSET_DEF]
           >- metis_tac[]
           >- metis_tac[]
           >> rw[SUBSET_DEF]) >> metis_tac[]) >~
  [‘contradiction s.Gm = NONE’, ‘conjsplit_s4 _ = NONE’,
   ‘disjsplit_s4 _ = NONE’, ‘EVERY ($¬ o is_box) _’, ‘EVERY ($¬ o is_dia) _’]
  (* Literal *)
  >-(rw[]
     >-(fs[wfm_S4_sequent] >> rw[] >> Cases_on `s.Ss` >> fs[] >> Cases_on `x` >>
        metis_tac[])
     >> fs[pt_rel_def] >> rw[]) >~
  [‘disjsplit_s4 s.Gm = SOME (pf, Γ1, Γ2)’,
   ‘tableau_S4 _ (s with <| Ss := NONE; Gm := Γ2|>) = OPEN(Nd(id,h,r) cs)’]
  (* disj2 *)
  >-(rw[] >> fs[] >> rw[]
     >-(fs[wfm_S4_sequent] >> rw[] >> Cases_on `s.Ss` >> fs[] >> Cases_on `x` >>
        metis_tac[])
     >> `pt_rel (Nd (id, h, r) cs) s'` by fs[pt_rel_def] >>
     `wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ2|>)`
        by (fs[wfm_S4_sequent] >> drule disj_s4_g2_in_g0 >> rw[] >>
            `set (closure_list_conc s.Gm) ⊆ set (closure_list_conc [Γ0])`
                 by fs[closure_subset_closure] >> metis_tac[SUBSET_DEF]) >>
     metis_tac[tableau_S4_Ss_eq_Gm_prop]) >~
  [‘disjsplit_s4 s.Gm = SOME (pf, Γ1, Γ2)’,
   ‘tableau_S4 _ (s with <| Ss := NONE; Gm := Γ1|>) = OPEN(Nd(id,h,r) cs)’]
  (* disj1 *)
  >-(rw[] >> fs[] >> rw[]
     >-(fs[wfm_S4_sequent] >> rw[] >> Cases_on `s.Ss` >> fs[] >> Cases_on `x` >>
        metis_tac[])
     >> `pt_rel (Nd (id, h, r) cs) s'` by fs[pt_rel_def] >>
     `wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ1|>)`
        by (fs[wfm_S4_sequent] >> drule disj_s4_g1_in_g0 >> rw[] >>
            `set (closure_list_conc s.Gm) ⊆ set (closure_list_conc [Γ0])`
                 by fs[closure_subset_closure] >> metis_tac[SUBSET_DEF]) >>
     metis_tac[tableau_S4_Ss_eq_Gm_prop]) >>
  rw[]
  >-(fs[wfm_S4_sequent] >> rw[] >> Cases_on `s.Ss` >> fs[] >> Cases_on `x` >>
     metis_tac[])
  >> `pt_rel (Nd (id, h, r) cs) s'` by fs[pt_rel_def] >>
  `wfm_S4_sequent Γ0 (s with <|Ss := NONE; Gm := Γ'|>)`
      by (fs[wfm_S4_sequent] >> drule conjsplit_s4_MEM2 >> rw[] >>
          fs[SUBSET_DEF] >> rw[] >>
          first_x_assum (drule_then strip_assume_tac)
          >- metis_tac[]
          >> first_x_assum (drule_then strip_assume_tac) >>
          drule mem_closure_of_closure >>
          rw[] >> metis_tac[mem_closure_self]) >>
  metis_tac[tableau_S4_Ss_eq_Gm_prop]
QED

Theorem RTC_pt_rel_imp_RTC_reach_step:
  ∀x w. RTC pt_rel x w ⇒ x = m ⇒ RTC (reach_step m) x w
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >> fs[pt_rel_def] >>
  `(reach_step m) w w'` by rw[reach_step] >>
  metis_tac[RTC_CASES2]
QED

Theorem reach_step_preserve_box:
∀w v.
    reach_step m w v ⇒
    MEM (Box p) w.htk ⇒
    thm_3_19_prop w ⇒
    thm_3_17_prop v ⇒
    wfm_S4_sequent Γ0 v.id ⇒
    MEM (Box p) v.htk
Proof
  rw[reach_step] >- (Cases_on `w` >> PairCases_on `a` >> fs[thm_3_19_prop]) >>
  fs[wfm_S4_sequent] >> Cases_on `sig` >> first_x_assum drule >> rw[] >>
  Cases_on `w` >> PairCases_on `a` >> fs[thm_3_19_prop] >>
  `MEM (Box p) r` by metis_tac[] >>
  Cases_on `v` >> PairCases_on `a` >> fs[thm_3_17_prop] >>
  metis_tac[SUBSET_DEF]
QED

Theorem RTC_reach_step_reserve_box:
∀w v.
    RTC (reach_step m) w v ∧
    RTC pt_rel m w ∧
    MEM (Box p) w.htk ∧
    thm_3_19_prop m ∧
    thm_3_17_prop m ∧
    (∀s. RTC pt_rel m s ⇒ wfm_S4_sequent Γ0 s.id) ⇒
    MEM (Box p) v.htk
Proof
  Induct_on `RTC` >> rw[] >> fs[] >>
  first_x_assum irule >> rw[]
  >- (irule reach_step_preserve_box >> rw[]
      >-(irule thm_3_17_prop_RTC >> qexists_tac `m` >> rw[] >>
         fs[reach_step] >> metis_tac[pt_rel_attach_r'])
      >-(drule reach_step_from_root' >> rw[] >>
         fs[reach_step] >> metis_tac[pt_rel_attach_r'])
      >> qexistsl_tac [`m`,`w`] >> metis_tac[thm_3_19_prop_RTC])
  >> fs[reach_step] >> metis_tac[pt_rel_attach_r']
QED

(* thm_3_22*)
Theorem tableau_S4_sound:
  ∀f m. final_tableau_S4 f = OPEN m ⇒
          ∀w. w ∈ (s4_tree_model m).frame.world ⇒
               ∀p. MEM p w.htk ⇒
                   forces (s4_tree_model m) w p
Proof
  simp[PULL_FORALL] >> Induct_on ‘p’
  (* Var *)
  >-(simp[forces_def, s4_tree_model])
  (* NVAr *)
  >-(simp[forces_def, s4_tree_model] >> rpt strip_tac >>
     drule reach_step_from_root >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     ‘RTC pt_rel m m’ by simp[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[final_tableau_S4_def] >> drule thm_3_17 >> strip_tac >>
     drule thm_3_17_prop_RTC >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     Cases_on ‘w’ >> PairCases_on ‘a’ >> fs[thm_3_17_prop] >>
     fs[pre_hintikka_def] >> metis_tac[contradiction_EQ_NONE])
  (* Conj *)
  >-(simp[forces_def, s4_tree_model] >> rpt strip_tac >>
     ‘w ∈ (s4_tree_model m).frame.world’ by fs[s4_tree_model] >>
     drule reach_step_from_root >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     ‘RTC pt_rel m m’ by simp[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[final_tableau_S4_def] >> drule thm_3_17 >> strip_tac >>
     drule thm_3_17_prop_RTC >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     Cases_on ‘w’ >> PairCases_on ‘a’ >> fs[thm_3_17_prop] >>
     fs[pre_hintikka_def] >> first_x_assum (drule_then strip_assume_tac)
     >-(last_x_assum (drule_then strip_assume_tac) >>
        first_x_assum (drule_then strip_assume_tac) >>
        fs[] >> first_x_assum (drule_then strip_assume_tac) >>
        fs[s4_tree_model])
     >> first_x_assum (drule_then strip_assume_tac) >>
        first_x_assum (drule_then strip_assume_tac) >>
        fs[] >> first_x_assum (drule_then strip_assume_tac) >>
     fs[s4_tree_model])
  (* Disj *)
  >-(simp[forces_def, s4_tree_model] >> rpt strip_tac >>
     ‘w ∈ (s4_tree_model m).frame.world’ by fs[s4_tree_model] >>
     drule reach_step_from_root >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     ‘RTC pt_rel m m’ by simp[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[final_tableau_S4_def] >> drule thm_3_17 >> strip_tac >>
     drule thm_3_17_prop_RTC >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     Cases_on ‘w’ >> PairCases_on ‘a’ >> fs[thm_3_17_prop] >>
     fs[pre_hintikka_def] >> first_x_assum (drule_then strip_assume_tac) >>
     last_x_assum (drule_then strip_assume_tac) >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[] >> first_x_assum (drule_then strip_assume_tac) >> fs[s4_tree_model])
  (* Box *)
  >-(simp[forces_def, s4_tree_model] >> rpt strip_tac >>
     ‘v ∈ (s4_tree_model m).frame.world’ by fs[s4_tree_model] >>
     first_x_assum (drule_then strip_assume_tac) >>
     first_x_assum (drule_then strip_assume_tac) >>
     fs[s4_tree_model] >> last_x_assum irule >> rw[] >>
     drule reach_step_from_root >> rw[] >>
     first_assum (qspecl_then [‘m’, ‘v’] (ASSUME_TAC)) >>
     ‘RTC pt_rel m m’ by simp[] >>
     first_x_assum (drule_all_then strip_assume_tac) >>
     fs[final_tableau_S4_def] >> drule thm_3_17 >> rw[] >>
     drule thm_3_17_prop_RTC >> rw[] >>
     first_assum (drule_then strip_assume_tac) >>
     ‘MEM (Box p) v.htk’ suffices_by
       (Cases_on ‘v’ >> PairCases_on ‘a’ >> fs[thm_3_17_prop] >>
        fs[pre_hintikka_def] >> metis_tac[]) >>
     drule thm_3_19 >> rw[] >>
     drule thm_3_19_prop_RTC >> rw[] >>
     first_assum (drule_then strip_assume_tac) >>
     ‘w ∈ (s4_tree_model m).frame.world’ by fs[s4_tree_model] >>
     last_assum (qspecl_then [‘m’, ‘w’] (ASSUME_TAC)) >>
     ‘RTC pt_rel m m’ by simp[] >>
     first_x_assum (drule_all_then strip_assume_tac) >>
     fs[] >> rw[] >> first_assum (drule_then strip_assume_tac) >>
     ‘thm_3_17_prop w’ by fs[] >>
     ‘wfm_S4_sequent f <|As := []; Ss := NONE; Hs := []; Sg := []; Gm := [f]|>’
        by (simp[wfm_S4_sequent] >> rw[PSUBSET_DEF]
            >- (Cases_on ‘f’ >> fs[])
            >> metis_tac[mem_closure_self]) >>
     drule tableau_S4_Ss_eq_Gm >> rw[] >>
     drule tableau_S4_Ss_eq_Gm_prop_RTC >> rw[] >>
     drule wfm_S4_Transitive >> rw[] >>
     irule RTC_reach_step_reserve_box >> qexistsl_tac [‘m’, ‘w’, ‘f’] >> rw[])
  (* Dia *)
  >> simp[forces_def, s4_tree_model] >> rpt strip_tac >>
  ‘w ∈ (s4_tree_model m).frame.world’ by fs[s4_tree_model] >>
  drule reach_step_from_root >> rw[] >>
  first_assum (qspecl_then [‘m’, ‘w’] (ASSUME_TAC)) >>
  ‘RTC pt_rel m m’ by simp[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  fs[final_tableau_S4_def] >> drule thm_3_19 >> rw[] >>
  drule thm_3_19_prop_RTC >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  last_x_assum (drule_then strip_assume_tac) >>
  ‘(∀p. MEM (Dia p) w.htk ⇒
        (∃d. MEM (p,d) w.request) ∨ ∃s. MEM s w.l ∧ MEM p s.htk)’
    by (Cases_on ‘w’ >> PairCases_on ‘a’ >> fs[]) >>
  first_x_assum (drule_then strip_assume_tac)
  (* 3_19: MEM (p,d) w.request *)
  >-(drule s4_fulfillment >> rw[] >>
     fs[Once thm_3_20_prop] >> rw[] >>
     first_x_assum (drule_all_then strip_assume_tac)
     (* 3_20: MEM (p,d) m.id.As *)
     >-(drule tableau_S4_s_eq_id' >> rw[] >> fs[])
     (* 3_20:  pt_rel⃰ m d' /\  SOME (p,d) = d'.id.Ss *)
     >> qexists_tac ‘d'’ >> rw[]
     >- metis_tac[RTC_pt_rel_imp_RTC_reach_step]
     >- (rw[Once RTC_CASES1] >> fs[] >>
         DISJ2_TAC >> qexists_tac ‘d'’ >> rw[reach_step] >>
         DISJ2_TAC >> qexists_tac ‘(p,d)’ >> fs[])
     >> fs[s4_tree_model] >> first_x_assum irule >> rw[]
     >-(drule tableau_S4_Ss_eq_Gm >> rw[] >>
        ‘wfm_S4_sequent f <|As := []; Ss := NONE; Hs := [];Sg := [];Gm := [f]|>’
            by (simp[wfm_S4_sequent] >> rw[PSUBSET_DEF]
                >- (Cases_on ‘f’ >> fs[])
                >> metis_tac[mem_closure_self]) >>
        first_x_assum (drule_then strip_assume_tac) >>
        drule tableau_S4_Ss_eq_Gm_prop_RTC >> rw[] >>
        first_x_assum (drule_then strip_assume_tac) >>
        fs[Once tableau_S4_Ss_eq_Gm_prop] >> fs[] >> rw[]
        >> drule thm_3_17 >> rw[] >> drule thm_3_17_prop_RTC >> rw[] >>
        first_x_assum drule >> rw[] >>
        Cases_on ‘d'’ >> PairCases_on ‘a’ >> rw[] >>
        fs[thm_3_17_prop] >> metis_tac[SUBSET_DEF])
     >> drule RTC_pt_rel_imp_RTC_reach_step >> rw[])
  (* 3_19: MEM s w.l ∧ MEM p s.htk *)
  >> qexists_tac ‘s’ >> rw[]
  >-(simp[Once RTC_CASES2] >> DISJ2_TAC >> qexists_tac ‘w’ >> rw[reach_step])
  >-(simp[Once RTC_CASES2] >> DISJ2_TAC >> qexists_tac ‘w’ >> rw[reach_step])
  >> first_x_assum (qspec_then ‘s’ ASSUME_TAC) >> fs[s4_tree_model] >>
  first_x_assum irule >> rw[] >> rw[Once RTC_CASES2] >> DISJ2_TAC >>
  qexists_tac ‘w’ >> rw[reach_step]
QED

Theorem tableau_S4_local_sound:
  ∀f m. final_tableau_S4 f = OPEN m ⇒
        forces (s4_tree_model m) m f
Proof
  rw[] >> drule tableau_S4_sound >> rw[] >> first_x_assum irule >> rw[]
  >-(fs[final_tableau_S4_def] >> drule thm_3_17 >> rw[] >>
     Cases_on `m` >> PairCases_on `a` >> fs[thm_3_17_prop] >>
     drule tableau_S4_s_eq_id >> rw[] >> fs[])
  >> simp[s4_tree_model]
QED

val _ = export_theory();
