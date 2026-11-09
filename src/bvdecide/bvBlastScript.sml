(* A bit-blaster for a word-expression DAG, verified against the DAG's
   semantics.  Literals are ints: variable v is &v, its negation -&v, and
   literal 1 is TRUE (the CNF always holds the unit clause [1]).  The
   blasting state is (next fresh variable, clauses emitted so far). *)
Theory bvBlast
Ancestors
  pair list integer sptree words blast lratCheck
Libs
  cv_transLib wordsLib

(* ------------------------------------------------------------------------
   Tseitin gates with constant folding
   ------------------------------------------------------------------------ *)

Definition and2_def:
  and2 (a:int) (b:int) ((n:num), (cs:int list list)) =
    if a = -1 ∨ b = -1 ∨ a = -b then (-1, (n, cs))
    else if a = 1 then (b, (n, cs))
    else if b = 1 ∨ a = b then (a, (n, cs))
    else let v = &n in (v, (n + 1, [-v; a] :: [-v; b] :: [v; -a; -b] :: cs))
End

Definition xor2_def:
  xor2 (a:int) (b:int) ((n:num), (cs:int list list)) =
    if a = -1 then (b, (n, cs))
    else if b = -1 then (a, (n, cs))
    else if a = 1 then (-b, (n, cs))
    else if b = 1 then (-a, (n, cs))
    else if a = b then (-1, (n, cs))
    else if a = -b then (1, (n, cs))
    else let v = &n in
      (v, (n + 1, [-v; a; b] :: [-v; -a; -b] :: [v; -a; b] :: [v; a; -b] :: cs))
End

Definition or2_def:
  or2 a b s = let p = and2 (-a) (-b) s in (- FST p, SND p)
End

(* ------------------------------------------------------------------------
   The invariant: a satisfies every clause so far, every literal names a
   variable below the next fresh one, and variable 1 is TRUE.
   ------------------------------------------------------------------------ *)

Definition ok_lit_def:
  ok_lit n (l:int) ⇔ l ≠ 0 ∧ Num (ABS l) < n
End

Definition inv_def:
  inv a s ⇔ 2 ≤ FST s ∧ a 1 ∧ EVERY (EVERY (ok_lit (FST s))) (SND s) ∧
            EVERY (sat_clause a) (SND s)
End

(* a' extends a from state s to state s' *)
Definition next_def:
  next a s a' s' ⇔ FST s ≤ FST s' ∧ (∀v. v < FST s ⇒ a' v = a v) ∧ inv a' s'
End

Definition gate_ok_def:
  gate_ok g f ⇔
    ∀a s x y r s'.
      inv a s ∧ ok_lit (FST s) x ∧ ok_lit (FST s) y ∧ g x y s = (r, s') ⇒
      ∃a'. next a s a' s' ∧ ok_lit (FST s') r ∧
           (sat_lit a' r ⇔ f (sat_lit a x) (sat_lit a y))
End

Theorem sat_lit_cases[local]:
  (sat_lit a (&m) ⇔ m ≠ 0 ∧ a m) ∧ (sat_lit a (-&m) ⇔ m ≠ 0 ∧ ¬a m)
Proof
  rw[sat_lit_def] >> gvs[] >> Cases_on ‘m’ >> gvs[] >> intLib.ARITH_TAC
QED

Theorem ok_lit_cases[local]:
  (ok_lit n (&m) ⇔ m ≠ 0 ∧ m < n) ∧ (ok_lit n (-&m) ⇔ m ≠ 0 ∧ m < n)
Proof
  rw[ok_lit_def, INT_ABS_NEG, INT_ABS_NUM]
QED

Theorem lit_cases[local]:
  ∀l. ok_lit n l ⇒ ∃m. m ≠ 0 ∧ m < n ∧ (l = &m ∨ l = -&m)
Proof
  rw[] >> strip_assume_tac (Q.SPEC ‘l’ INT_NUM_CASES) >> gvs[ok_lit_cases] >>
  gvs[ok_lit_def]
QED

Theorem sat_lit_neg_eq:
  ok_lit n l ⇒ (sat_lit a (-l) ⇔ ¬sat_lit a l)
Proof
  rw[] >> drule lit_cases >> rw[] >> simp[sat_lit_cases]
QED

Theorem ok_lit_neg:
  ok_lit n (-l) ⇔ ok_lit n l
Proof
  simp[ok_lit_def, INT_ABS_NEG]
QED

Theorem ok_lit_mono:
  ok_lit n l ∧ n ≤ n' ⇒ ok_lit n' l
Proof
  simp[ok_lit_def]
QED

Theorem sat_lit_agree:
  ok_lit n l ∧ (∀v. v < n ⇒ a' v = a v) ⇒ (sat_lit a' l ⇔ sat_lit a l)
Proof
  rw[] >> drule lit_cases >> rw[] >> simp[sat_lit_cases]
QED

Theorem sat_clause_agree:
  EVERY (ok_lit n) c ∧ (∀v. v < n ⇒ a' v = a v) ⇒
    (sat_clause a' c ⇔ sat_clause a c)
Proof
  rw[sat_clause_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[sat_lit_agree]
QED

Theorem inv_lits:
  inv a s ⇒ ok_lit (FST s) 1 ∧ ok_lit (FST s) (-1) ∧ sat_lit a 1 ∧
    ¬sat_lit a (-1)
Proof
  rw[inv_def] >> simp[ok_lit_cases,
    sat_lit_cases |> CONJUNCT2 |> Q.INST [‘m’ |-> ‘1’]
                                     |> SIMP_RULE std_ss []] >>
  simp[sat_lit_def]
QED

Theorem next_refl:
  inv a s ⇒ next a s a s
Proof
  simp[next_def]
QED

Theorem next_trans:
  next a s a' s' ∧ next a' s' a'' s'' ⇒ next a s a'' s''
Proof
  rw[next_def] >> gvs[]
QED

(* Adding a fresh variable n whose value b makes the new clauses hold. *)
Theorem fresh_ok:
  inv a (n, cs) ∧ (∀v. v < n ⇒ a' v = a v) ∧ a' n = b ∧
  EVERY (EVERY (ok_lit (n + 1))) new ∧ EVERY (sat_clause a') new ⇒
  next a (n, cs) a' (n + 1, new ++ cs) ∧ ok_lit (n + 1) (&n) ∧
    (sat_lit a' (&n) ⇔ b)
Proof
  rw[next_def, inv_def, ok_lit_cases, sat_lit_cases]
  >- (gvs[EVERY_MEM] >> metis_tac[ok_lit_mono, DECIDE “n ≤ n + 1n”])
  >- (gvs[EVERY_MEM] >> rw[] >> ‘EVERY (ok_lit n) e’ by (simp[EVERY_MEM] >>
    metis_tac[]) >>
      metis_tac[sat_clause_agree])
QED

(* The facts a fresh-variable case of a gate needs, for a' = (n =+ b) a. *)
Theorem fresh_facts[local]:
  inv a (n, cs) ∧ ok_lit n x ∧ ok_lit n y ⇒
  2 ≤ n ∧ (∀v. v < n ⇒ (n =+ b) a v = a v) ∧ (n =+ b) a n = b ∧
  ok_lit (n + 1) x ∧ ok_lit (n + 1) y ∧ ok_lit (n + 1) (-x) ∧
    ok_lit (n + 1) (-y) ∧
  ok_lit (n + 1) (&n) ∧ ok_lit (n + 1) (-&n) ∧
  (sat_lit ((n =+ b) a) x ⇔ sat_lit a x) ∧
    (sat_lit ((n =+ b) a) y ⇔ sat_lit a y) ∧
  (sat_lit ((n =+ b) a) (-x) ⇔ ¬sat_lit a x) ∧
    (sat_lit ((n =+ b) a) (-y) ⇔ ¬sat_lit a y) ∧
  (sat_lit ((n =+ b) a) (&n) ⇔ b) ∧ (sat_lit ((n =+ b) a) (-&n) ⇔ ¬b)
Proof
  strip_tac >> ‘2 ≤ n’ by gvs[inv_def] >>
  ‘∀v. v < n ⇒ (n =+ b) a v = a v’ by simp[combinTheory.APPLY_UPDATE_THM] >>
  ‘n ≤ n + 1’ by simp[] >>
  ‘ok_lit (n + 1) x ∧ ok_lit (n + 1) y’ by metis_tac[ok_lit_mono] >>
  ‘(sat_lit ((n =+ b) a) x ⇔ sat_lit a x) ∧
    (sat_lit ((n =+ b) a) y ⇔ sat_lit a y)’
    by metis_tac[sat_lit_agree] >>
  ‘(sat_lit ((n =+ b) a) (-x) ⇔ ¬sat_lit ((n =+ b) a) x) ∧
   (sat_lit ((n =+ b) a) (-y) ⇔ ¬sat_lit ((n =+ b) a) y)’
    by metis_tac[sat_lit_neg_eq] >>
  simp[ok_lit_cases, sat_lit_cases, ok_lit_neg, combinTheory.APPLY_UPDATE_THM]
QED

Theorem and2_ok:
  gate_ok and2 (λp q. p ∧ q)
Proof
  simp[gate_ok_def, FORALL_PROD, and2_def] >> rpt gen_tac >> strip_tac >>
  rename1 ‘inv a (n, cs)’ >> drule inv_lits >> simp[] >> strip_tac >>
  ‘∀l. ok_lit n l ⇒ (sat_lit a (-l) ⇔ ¬sat_lit a l)’ by
    metis_tac[sat_lit_neg_eq] >>
  qpat_x_assum ‘_ = (r, _)’ mp_tac >> rpt IF_CASES_TAC >> strip_tac >> gvs[]
  >~ [‘n + 1’] >- (
    qabbrev_tac ‘b = (sat_lit a x ∧ sat_lit a y)’ >>
    mp_tac fresh_facts >> impl_tac >- simp[] >> strip_tac >>
    qexists_tac ‘(n =+ b) a’ >>
    mp_tac (Q.INST [‘a'’ |-> ‘(n =+ b) a’,
                    ‘new’ |-> ‘[[-&n; x]; [-&n; y]; [&n; -x; -y]]’] fresh_ok) >>
    impl_tac >- (rpt conj_tac >> gvs[sat_clause_def, Abbr ‘b’] >>
      metis_tac[]) >>
    simp[Abbr ‘b’]) >>
  qexists_tac ‘a’ >> gvs[next_refl] >> metis_tac[]
QED

Theorem xor2_ok:
  gate_ok xor2 (λp q. p ≠ q)
Proof
  simp[gate_ok_def, FORALL_PROD, xor2_def] >> rpt gen_tac >> strip_tac >>
  rename1 ‘inv a (n, cs)’ >> drule inv_lits >> simp[] >> strip_tac >>
  ‘∀l. ok_lit n l ⇒ (sat_lit a (-l) ⇔ ¬sat_lit a l)’ by
    metis_tac[sat_lit_neg_eq] >>
  qpat_x_assum ‘_ = (r, _)’ mp_tac >> rpt IF_CASES_TAC >> strip_tac >> gvs[]
  >~ [‘n + 1’] >- (
    qabbrev_tac ‘b = (sat_lit a x ≠ sat_lit a y)’ >>
    mp_tac fresh_facts >> impl_tac >- simp[] >> strip_tac >>
    qexists_tac ‘(n =+ b) a’ >>
    mp_tac (Q.INST [‘a'’ |-> ‘(n =+ b) a’,
      ‘new’ |-> ‘[[-&n; x; y]; [-&n; -x; -y]; [&n; -x; y]; [&n; x; -y]]’]
        fresh_ok) >>
    impl_tac >- (rpt conj_tac >> gvs[sat_clause_def, Abbr ‘b’] >>
      metis_tac[]) >>
    simp[Abbr ‘b’]) >>
  qexists_tac ‘a’ >> gvs[next_refl, ok_lit_neg] >> metis_tac[]
QED

Theorem or2_ok:
  gate_ok or2 (λp q. p ∨ q)
Proof
  rw[gate_ok_def, or2_def] >> Cases_on ‘and2 (-x) (-y) s’ >> gvs[] >>
  rename1 ‘and2 (-x) (-y) s = (q, s')’ >>
  mp_tac and2_ok >> simp[gate_ok_def] >>
  disch_then (qspecl_then [‘a’, ‘s’, ‘-x’, ‘-y’, ‘q’, ‘s'’] mp_tac) >>
  simp[ok_lit_neg] >> strip_tac >> qexists_tac ‘a'’ >> simp[] >>
  ‘ok_lit (FST s') q’ by gvs[next_def] >>
  ‘sat_lit a' (-q) ⇔ ¬sat_lit a' q’ by metis_tac[sat_lit_neg_eq] >>
  ‘(sat_lit a (-x) ⇔ ¬sat_lit a x) ∧ (sat_lit a (-y) ⇔ ¬sat_lit a y)’
    by metis_tac[sat_lit_neg_eq] >>
  gvs[]
QED

(* ------------------------------------------------------------------------
   Bit-vector operations on literal lists, least significant bit first
   ------------------------------------------------------------------------ *)

Definition bb_and_def:
  (bb_and [] _ s = ([]:int list, s)) ∧ (bb_and _ [] s = ([], s)) ∧
  (bb_and (x::xs) (y::ys) s =
     let p = and2 x y s in
     let q = bb_and xs ys (SND p) in
       (FST p :: FST q, SND q))
End

Definition bb_or_def:
  (bb_or [] _ s = ([]:int list, s)) ∧ (bb_or _ [] s = ([], s)) ∧
  (bb_or (x::xs) (y::ys) s =
     let p = or2 x y s in
     let q = bb_or xs ys (SND p) in
       (FST p :: FST q, SND q))
End

Definition bb_xor_def:
  (bb_xor [] _ s = ([]:int list, s)) ∧ (bb_xor _ [] s = ([], s)) ∧
  (bb_xor (x::xs) (y::ys) s =
     let p = xor2 x y s in
     let q = bb_xor xs ys (SND p) in
       (FST p :: FST q, SND q))
End

Definition bb_not_def:
  (bb_not [] = []) ∧ (bb_not (x::xs) = (-x:int) :: bb_not xs)
End

(* ripple-carry adder with carry-in c *)
Definition bb_add_def:
  (bb_add [] _ (c:int) s = ([]:int list, s)) ∧ (bb_add _ [] c s = ([], s)) ∧
  (bb_add (x::xs) (y::ys) c s =
     let p = xor2 x y s in
     let r = xor2 (FST p) c (SND p) in
     let g = and2 x y (SND r) in
     let t = and2 (FST p) c (SND g) in
     let k = or2 (FST g) (FST t) (SND t) in
     let q = bb_add xs ys (FST k) (SND k) in (FST r :: FST q, SND q))
End

(* the carry out of xs + ys + c *)
Definition bb_carry_def:
  (bb_carry [] _ (c:int) s = (c, s)) ∧ (bb_carry _ [] c s = (c, s)) ∧
  (bb_carry (x::xs) (y::ys) c s =
     let p = xor2 x y s in
     let g = and2 x y (SND p) in
     let t = and2 (FST p) c (SND g) in
     let k = or2 (FST g) (FST t) (SND t) in
     bb_carry xs ys (FST k) (SND k))
End

(* the conjunction of all of xs *)
Definition bb_all_def:
  (bb_all [] s = (1:int, s)) ∧
  (bb_all (x::xs) s = let p = bb_all xs s in and2 x (FST p) (SND p))
End

Definition bb_const_def:
  bb_const (w:num) (k:num) =
    if w = 0 then []
    else (if ODD k then 1 else -1:int) :: bb_const (w - 1) (k DIV 2)
End

Definition bb_vars_def:
  bb_vars (w:num) (n:num) =
    if w = 0 then [] else (&n:int) :: bb_vars (w - 1) (n + 1)
End

Definition bb_rep_def:
  bb_rep (k:num) (l:int) = if k = 0 then [] else l :: bb_rep (k - 1) l
End

Definition bb_last_def:
  (bb_last [] = (-1:int)) ∧ (bb_last [x] = x) ∧
  (bb_last (x::y::xs) = bb_last (y::xs))
End

Definition bb_shl_def:
  bb_shl (xs:int list) k = TAKE (LENGTH xs) (bb_rep k (-1) ++ xs)
End

Definition bb_lsr_def:
  bb_lsr (xs:int list) k = DROP k xs ++ bb_rep (MIN k (LENGTH xs)) (-1)
End

Definition bb_asr_def:
  bb_asr (xs:int list) k =
    DROP k xs ++ bb_rep (MIN k (LENGTH xs)) (bb_last xs)
End

(* ------------------------------------------------------------------------
   The DAG and its semantics.  Node i may refer only to nodes before it.  A
   variable node denotes env i (or benv i) for its own position i, and the
   root is the last node, which must be Boolean.
   ------------------------------------------------------------------------ *)

Datatype:
  node = WVar | WConst num | WNot num | WAnd num num | WOr num num
       | WXor num num | WAdd num num | WNeg num
       | WShl num num | WLsr num num | WAsr num num
       | BVar | BConst bool | BUlt num num | BEq num num | BBit num num
       | BAnd num num | BOr num num | BNot num | BImp num num | BIff num num
End

Datatype:
  value = Word ('a word) | Bool bool
End

Definition wval_def:
  (wval (Word w) = w) ∧ (wval (Bool _) = 0w)
End

Definition bval_def:
  (bval (Bool b) = b) ∧ (bval (Word _) = F)
End

Definition eval_node_def:
  eval_node (env : num -> 'a word) (benv : num -> bool) (vs : 'a value list)
            (i:num) nd =
    case nd of
      WVar => Word (env i)
    | WConst k => Word (n2w k)
    | WNot x => Word (~wval (EL x vs))
    | WAnd x y => Word (wval (EL x vs) && wval (EL y vs))
    | WOr x y => Word (wval (EL x vs) || wval (EL y vs))
    | WXor x y => Word (wval (EL x vs) ⊕ wval (EL y vs))
    | WAdd x y => Word (wval (EL x vs) + wval (EL y vs))
    | WNeg x => Word (-wval (EL x vs))
    | WShl x k => Word (wval (EL x vs) << k)
    | WLsr x k => Word (wval (EL x vs) >>> k)
    | WAsr x k => Word (wval (EL x vs) >> k)
    | BVar => Bool (benv i)
    | BConst c => Bool c
    | BUlt x y => Bool (wval (EL x vs) <+ wval (EL y vs))
    | BEq x y => Bool (wval (EL x vs) = wval (EL y vs))
    | BBit x k => Bool (wval (EL x vs) ' k)
    | BAnd x y => Bool (bval (EL x vs) ∧ bval (EL y vs))
    | BOr x y => Bool (bval (EL x vs) ∨ bval (EL y vs))
    | BNot x => Bool (¬bval (EL x vs))
    | BImp x y => Bool (bval (EL x vs) ⇒ bval (EL y vs))
    | BIff x y => Bool (bval (EL x vs) ⇔ bval (EL y vs))
End

Definition eval_nodes_def:
  (eval_nodes env benv vs [] = vs) ∧
  (eval_nodes env benv vs (nd::nds) =
     eval_nodes env benv (vs ++ [eval_node env benv vs (LENGTH vs) nd]) nds)
End

Definition eval_dag_def:
  eval_dag env benv dag = bval (LAST (eval_nodes env benv [] dag))
End

(* ------------------------------------------------------------------------
   Blasting the DAG.  The map holds each earlier node's literals; a node whose
   arguments are missing or of the wrong kind, or a bit index out of range,
   makes the whole CNF empty, which no certificate refutes.
   ------------------------------------------------------------------------ *)

Datatype:
  lits = Wl (int list) | Bl int
End

Definition wlits_def:
  wlits m (x:num) =
    case lookup x m of SOME (Wl xs) => SOME xs | _ => NONE
End

Definition blits_def:
  blits m (x:num) =
    case lookup x m of SOME (Bl l) => SOME l | _ => NONE
End

Definition wres_def:
  wres p = (SOME (Wl (FST p)), SND p)
End

Definition bres_def:
  bres p = (SOME (Bl (FST p)), SND p)
End

Definition blast_node_def:
  blast_node (w:num) m nd ((n:num), (cs:int list list)) =
    let s = (n, cs) in
    case nd of
      WVar => (SOME (Wl (bb_vars w n)), (n + w, cs))
    | WConst k => (SOME (Wl (bb_const w k)), s)
    | WNot x =>
        (case wlits m x of
           SOME xs => (SOME (Wl (bb_not xs)), s)
         | NONE => (NONE, s))
    | WAnd x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) => wres (bb_and xs ys s)
         | _ => (NONE, s))
    | WOr x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) => wres (bb_or xs ys s)
         | _ => (NONE, s))
    | WXor x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) => wres (bb_xor xs ys s)
         | _ => (NONE, s))
    | WAdd x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) => wres (bb_add xs ys (-1) s)
         | _ => (NONE, s))
    | WNeg x =>
        (case wlits m x of
           SOME xs => wres (bb_add (bb_rep w (-1)) (bb_not xs) 1 s)
         | NONE => (NONE, s))
    | WShl x k =>
        (case wlits m x of
           SOME xs => (SOME (Wl (bb_shl xs k)), s)
         | NONE => (NONE, s))
    | WLsr x k =>
        (case wlits m x of
           SOME xs => (SOME (Wl (bb_lsr xs k)), s)
         | NONE => (NONE, s))
    | WAsr x k =>
        (case wlits m x of
           SOME xs => (SOME (Wl (bb_asr xs k)), s)
         | NONE => (NONE, s))
    | BVar => (SOME (Bl (&n)), (n + 1, cs))
    | BConst c => (SOME (Bl (if c then 1 else -1)), s)
    | BUlt x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) =>
             (let k = bb_carry xs (bb_not ys) 1 s in
                (SOME (Bl (- FST k)), SND k))
         | _ => (NONE, s))
    | BEq x y =>
        (case (wlits m x, wlits m y) of
           (SOME xs, SOME ys) =>
             (let e = bb_xor xs ys s in
                bres (bb_all (bb_not (FST e)) (SND e)))
         | _ => (NONE, s))
    | BBit x k =>
        (case wlits m x of
           SOME xs =>
             if k < LENGTH xs then (SOME (Bl (EL k xs)), s) else (NONE, s)
         | NONE => (NONE, s))
    | BAnd x y =>
        (case (blits m x, blits m y) of
           (SOME p, SOME q) => bres (and2 p q s)
         | _ => (NONE, s))
    | BOr x y =>
        (case (blits m x, blits m y) of
           (SOME p, SOME q) => bres (or2 p q s)
         | _ => (NONE, s))
    | BNot x =>
        (case blits m x of
           SOME p => (SOME (Bl (-p)), s)
         | NONE => (NONE, s))
    | BImp x y =>
        (case (blits m x, blits m y) of
           (SOME p, SOME q) => bres (or2 (-p) q s)
         | _ => (NONE, s))
    | BIff x y =>
        (case (blits m x, blits m y) of
           (SOME p, SOME q) =>
             (let r = xor2 p q s in (SOME (Bl (- FST r)), SND r))
         | _ => (NONE, s))
End

Definition blast_nodes_def:
  (blast_nodes w m (i:num) [] s = SOME (m, s)) ∧
  (blast_nodes w m i (nd::nds) s =
     case blast_node w m nd s of
       (NONE, _) => NONE
     | (SOME l, s1) => blast_nodes w (insert i l m) (i + 1) nds s1)
End

(* The CNF of the negated root, with [1] making literal 1 TRUE. *)
Definition blast_dag_def:
  blast_dag w dag =
    case blast_nodes w LN 0 dag (2, []) of
      NONE => []
    | SOME (m, (n, cs)) =>
        case blits m (LENGTH dag - 1) of
          SOME l => [1] :: [-l] :: cs
        | NONE => []
End

(* Logical representation interface, independent of the executable checker. *)
Definition bits_rel_def:
  bits_rel a n xs (w:'a word) <=>
    LENGTH xs = dimindex(:'a) /\ EVERY (ok_lit n) xs /\
    (!j. j < dimindex(:'a) ==> (sat_lit a (EL j xs) <=> w ' j))
End

Definition value_rel_def:
  (value_rel a n (Wl xs) (Word w) <=> bits_rel a n xs w) /\
  (value_rel a n (Bl l) (Bool b) <=> ok_lit n l /\ (sat_lit a l <=> b)) /\
  (value_rel a n (Wl xs) (Bool b) <=> F) /\
  (value_rel a n (Bl l) (Word w) <=> F)
End

Definition map_rel_def:
  map_rel a n m (vs:'a value list) <=>
    (!i. LENGTH vs <= i ==> lookup i m = NONE) /\
    (!i. i < LENGTH vs ==> ?l. lookup i m = SOME l /\ value_rel a n l (EL i vs))
End

Theorem bits_rel_next:
  bits_rel a (FST s) xs w /\ next a s a' s' ==>
  bits_rel a' (FST s') xs w
Proof
  rw[bits_rel_def, next_def]
  >- (gvs[EVERY_MEM] >> metis_tac[ok_lit_mono]) >>
  `ok_lit (FST s) (EL j xs)` by metis_tac[EVERY_EL] >>
  metis_tac[sat_lit_agree]
QED

Theorem value_rel_next:
  value_rel a (FST s) l v /\ next a s a' s' ==>
  value_rel a' (FST s') l v
Proof
  Cases_on `l` >> Cases_on `v` >> simp[value_rel_def]
  >- metis_tac[bits_rel_next] >>
  rw[next_def] >> metis_tac[ok_lit_mono, sat_lit_agree]
QED

Theorem map_rel_next:
  map_rel a (FST s) m vs /\ next a s a' s' ==>
  map_rel a' (FST s') m vs
Proof
  rw[map_rel_def] >> metis_tac[value_rel_next]
QED

Theorem map_rel_empty:
  map_rel a n LN []
Proof
  simp[map_rel_def, lookup_def]
QED

Theorem map_rel_insert:
  map_rel a n m vs /\ value_rel a n l v ==>
  map_rel a n (insert (LENGTH vs) l m) (vs ++ [v])
Proof
  rw[map_rel_def, lookup_insert, EL_APPEND_EQN] >>
  Cases_on `i < LENGTH vs` >> gvs[] >>
  `i = LENGTH vs` by decide_tac >> gvs[]
QED

Theorem map_rel_wlits:
  map_rel a n m vs /\ wlits m i = SOME xs ==>
  i < LENGTH vs /\ ?w. EL i vs = Word w /\ bits_rel a n xs w
Proof
  rw[wlits_def, AllCaseEqs()] >>
  `i < LENGTH vs` by (gvs[map_rel_def] >> spose_not_then assume_tac >>
    `LENGTH vs <= i` by decide_tac >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  gvs[map_rel_def] >> first_x_assum drule >> strip_tac >>
  Cases_on `EL i vs` >> gvs[value_rel_def]
QED

Theorem map_rel_blits:
  map_rel a n m vs /\ blits m i = SOME l ==>
  i < LENGTH vs /\ EL i vs = Bool (sat_lit a l) /\ ok_lit n l
Proof
  rw[blits_def, AllCaseEqs()] >>
  `i < LENGTH vs` by (gvs[map_rel_def] >> spose_not_then assume_tac >>
    `LENGTH vs <= i` by decide_tac >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  gvs[map_rel_def] >> first_x_assum drule >> strip_tac >>
  Cases_on `EL i vs` >> gvs[value_rel_def]
QED

Theorem bb_rep_eq:
  bb_rep k l = REPLICATE k l
Proof
  Induct_on `k` >> simp[Once bb_rep_def, rich_listTheory.REPLICATE]
QED

Theorem bb_vars_eq:
  !n. bb_vars k n = GENLIST (\j. &(n + j)) k
Proof
  Induct_on `k` >> simp[Once bb_vars_def, GENLIST_CONS] >>
  gen_tac >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, combinTheory.o_DEF]
QED

Theorem bb_const_eq:
  !k. bb_const w k = GENLIST (\j. if BIT j k then 1 else -1) w
Proof
  Induct_on `w` >> simp[Once bb_const_def, GENLIST_CONS,
    bitTheory.BIT0_ODD, bitTheory.BIT_DIV2, combinTheory.o_DEF]
QED

Theorem bb_not_eq:
  bb_not xs = MAP ($~ : int -> int) xs
Proof
  Induct_on `xs` >> simp[bb_not_def]
QED

Theorem bb_last_eq:
  xs <> [] ==> bb_last xs = LAST xs
Proof
  Induct_on `xs` >> simp[] >> Cases_on `xs` >> simp[bb_last_def]
QED

Theorem bits_rel_not:
  bits_rel a n xs w ==> bits_rel a n (bb_not xs) (~w)
Proof
  rw[bits_rel_def, bb_not_eq, EVERY_MAP, EL_MAP,
     word_1comp_def, fcpTheory.FCP_BETA]
  >- (gvs[EVERY_MEM] >> metis_tac[ok_lit_neg]) >>
  `ok_lit n (EL j xs)` by metis_tac[EVERY_EL] >>
  metis_tac[sat_lit_neg_eq]
QED

Theorem bits_rel_const:
  inv a s ==> bits_rel a (FST s) (bb_const (dimindex(:'a)) k) (n2w k:'a word)
Proof
  strip_tac >> drule inv_lits >> strip_tac >>
  rw[bits_rel_def, bb_const_eq, EVERY_GENLIST, EL_GENLIST, word_index] >>
  Cases_on `BIT j k` >> simp[]
QED

Theorem bits_rel_shl:
  bits_rel a (FST s) xs w /\ inv a s ==>
  bits_rel a (FST s) (bb_shl xs k) (w << k)
Proof
  strip_tac >> drule inv_lits >> strip_tac >>
  gvs[bits_rel_def, bb_shl_def, bb_rep_eq] >>
  rw[bits_rel_def, LENGTH_TAKE, rich_listTheory.LENGTH_REPLICATE,
     word_lsl_def, fcpTheory.FCP_BETA]
  >- (irule rich_listTheory.EVERY_TAKE >> simp[EVERY_APPEND,
    rich_listTheory.EVERY_REPLICATE]) >>
  simp[EL_TAKE, EL_APPEND_EQN, rich_listTheory.LENGTH_REPLICATE] >>
  Cases_on `j < k` >> simp[rich_listTheory.EL_REPLICATE]
QED

Theorem bits_rel_lsr:
  bits_rel a (FST s) xs w /\ inv a s ==>
  bits_rel a (FST s) (bb_lsr xs k) (w >>> k)
Proof
  strip_tac >> drule inv_lits >> strip_tac >>
  gvs[bits_rel_def, bb_lsr_def, bb_rep_eq] >>
  rw[bits_rel_def, rich_listTheory.LENGTH_REPLICATE, LENGTH_DROP,
     word_lsr_def, fcpTheory.FCP_BETA]
  >- (simp[arithmeticTheory.MIN_DEF] >> decide_tac)
  >- (simp[EVERY_APPEND, rich_listTheory.EVERY_REPLICATE] >>
      irule rich_listTheory.EVERY_DROP >> simp[]) >>
  simp[EL_APPEND_EQN, LENGTH_DROP] >>
  Cases_on `j + k < dimindex(:'a)` >>
  simp[EL_DROP, rich_listTheory.EL_REPLICATE] >>
  `j - (dimindex(:'a) - k) < MIN k (dimindex(:'a))` by intLib.COOPER_TAC >>
  simp[rich_listTheory.EL_REPLICATE]
QED

Theorem bits_rel_asr:
  bits_rel a (FST s) xs w ==>
  bits_rel a (FST s) (bb_asr xs k) (w >> k)
Proof
  strip_tac >>
  `LENGTH xs = dimindex(:'a)` by gvs[bits_rel_def] >>
  `xs <> []` by (strip_tac >> gvs[]) >>
  `bb_last xs = EL (dimindex(:'a) - 1) xs` by
    simp[bb_last_eq, LAST_EL, arithmeticTheory.PRE_SUB1] >>
  `ok_lit (FST s) (bb_last xs)` by
    (gvs[bits_rel_def] >> irule (iffLR EVERY_EL) >> simp[]) >>
  gvs[bits_rel_def, bb_asr_def, bb_rep_eq] >>
  rw[bits_rel_def, rich_listTheory.LENGTH_REPLICATE, LENGTH_DROP,
     word_asr_def, fcpTheory.FCP_BETA, word_msb_def]
  >- (simp[arithmeticTheory.MIN_DEF] >> decide_tac)
  >- (simp[EVERY_APPEND, rich_listTheory.EVERY_REPLICATE] >>
      irule rich_listTheory.EVERY_DROP >> simp[]) >>
  simp[EL_APPEND_EQN, LENGTH_DROP] >>
  Cases_on `j + k < dimindex(:'a)` >> gvs[EL_DROP] >>
  `j - (dimindex(:'a) - k) < MIN k (dimindex(:'a))` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  simp[rich_listTheory.EL_REPLICATE]
QED

Theorem next_alloc:
  inv a (n,cs) /\ n <= n' /\ (!v. v < n ==> a' v = a v) ==>
  next a (n,cs) a' (n',cs)
Proof
  rw[next_def, inv_def]
  >- (gvs[EVERY_MEM] >> metis_tac[ok_lit_mono]) >>
  gvs[EVERY_MEM] >> rw[] >>
  `EVERY (ok_lit n) e` by (simp[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[sat_clause_agree]
QED

Theorem bool_alloc:
  inv a (n,cs) ==> ?a'. next a (n,cs) a' (n+1,cs) /\
    ok_lit (n+1) (&n) /\ (sat_lit a' (&n) <=> b)
Proof
  strip_tac >> qexists_tac `(n =+ b) a` >>
  `2 <= n` by gvs[inv_def] >>
  simp[ok_lit_cases, sat_lit_cases, combinTheory.APPLY_UPDATE_THM] >>
  irule next_alloc >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem word_alloc:
  inv a (n,cs) ==> ?a'. next a (n,cs) a' (n+dimindex(:'a),cs) /\
    bits_rel a' (n+dimindex(:'a)) (bb_vars (dimindex(:'a)) n) (w:'a word)
Proof
  strip_tac >>
  qexists_tac `\v. if v < n then a v else w ' (v - n)` >>
  conj_tac
  >- (irule next_alloc >> simp[]) >>
  `2 <= n` by gvs[inv_def] >>
  rw[bits_rel_def, bb_vars_eq, EVERY_GENLIST, EL_GENLIST,
     ok_lit_cases, sat_lit_cases] >> simp[]
QED

Theorem bits_rel_zero:
  inv a s ==> bits_rel a (FST s) (bb_rep (dimindex(:'a)) (-1)) (0w:'a word)
Proof
  strip_tac >> drule inv_lits >> strip_tac >>
  simp[bits_rel_def, bb_rep_eq, rich_listTheory.LENGTH_REPLICATE,
       rich_listTheory.EVERY_REPLICATE, rich_listTheory.EL_REPLICATE, word_0]
QED

Theorem lits_next:
  EVERY (ok_lit (FST s)) xs /\ next a s a' s' ==>
  EVERY (ok_lit (FST s')) xs /\ MAP (sat_lit a') xs = MAP (sat_lit a) xs
Proof
  rw[next_def]
  >- (gvs[EVERY_MEM] >> metis_tac[ok_lit_mono]) >>
  irule MAP_CONG >> gvs[EVERY_MEM] >> metis_tac[sat_lit_agree]
QED

Definition list_gate_rel_def:
  list_gate_rel h f <=>
  !xs ys a s zs s'. inv a s /\
    EVERY (ok_lit (FST s)) xs /\ EVERY (ok_lit (FST s)) ys /\
    LENGTH xs = LENGTH ys /\ h xs ys s = (zs,s') ==>
    ?a'. next a s a' s' /\ EVERY (ok_lit (FST s')) zs /\
      MAP (sat_lit a') zs = MAP2 f (MAP (sat_lit a) xs) (MAP (sat_lit a) ys)
End

Theorem list_gate_ok:
  gate_ok g f /\
  (!ys s. h [] ys s = ([],s)) /\
  (!x xs y ys s. h (x::xs) (y::ys) s =
    let p = g x y s in let q = h xs ys (SND p) in (FST p :: FST q,SND q)) ==>
  list_gate_rel h f
Proof
  strip_tac >> simp[list_gate_rel_def] >> Induct >> rpt gen_tac
  >- (simp[] >> strip_tac >> gvs[] >> metis_tac[next_refl]) >>
  Cases_on `ys` >> simp[] >> strip_tac >>
  rename1 `g x y s` >> rename1 `h xs ys (SND (g x y s))` >>
  Cases_on `g x y s` >> rename1 `g x y s = (hr,hs)` >>
  Cases_on `h xs ys hs` >> rename1 `h xs ys hs = (rs,u)` >> gvs[] >>
  `?b. next a s b hs /\ ok_lit (FST hs) hr /\
       (sat_lit b hr <=> f (sat_lit a x) (sat_lit a y))` by
    metis_tac[gate_ok_def] >>
  `EVERY (ok_lit (FST hs)) xs /\ MAP (sat_lit b) xs = MAP (sat_lit a) xs` by
    metis_tac[lits_next] >>
  `EVERY (ok_lit (FST hs)) ys /\ MAP (sat_lit b) ys = MAP (sat_lit a) ys` by
    metis_tac[lits_next] >>
  `inv b hs` by gvs[next_def] >>
  qpat_x_assum `!ys a s zs s'. _` (qspecl_then [`ys`,`b`,`hs`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a'` >> simp[] >>
  conj_tac >- metis_tac[next_trans] >>
  qpat_x_assum `next b hs a' s'` mp_tac >> simp[next_def] >> strip_tac >>
  conj_tac >- metis_tac[ok_lit_mono] >> metis_tac[sat_lit_agree]
QED

Theorem bb_and_ok:
  list_gate_rel bb_and (\p q. p /\ q)
Proof
  irule list_gate_ok >> simp[bb_and_def, bb_or_def, bb_xor_def] >>
    qexists_tac `and2` >> simp[and2_ok, bb_and_def]
QED

Theorem bb_or_ok:
  list_gate_rel bb_or (\p q. p \/ q)
Proof
  irule list_gate_ok >> simp[bb_and_def, bb_or_def, bb_xor_def] >>
    qexists_tac `or2` >> simp[or2_ok, bb_or_def]
QED

Theorem bb_xor_ok:
  list_gate_rel bb_xor (\p q. p <> q)
Proof
  irule list_gate_ok >> simp[bb_and_def, bb_or_def, bb_xor_def] >>
    qexists_tac `xor2` >> simp[xor2_ok, bb_xor_def]
QED

Theorem bits_rel_gate:
  list_gate_rel h f /\ inv a s /\ bits_rel a (FST s) xs (x:'a word) /\
    bits_rel a (FST s) ys (y:'a word) /\ h xs ys s = (zs,s') /\
    (!j. j < dimindex(:'a) ==> ((z:'a word) ' j <=> f (x ' j) (y ' j))) ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') zs z
Proof
  rw[bits_rel_def] >>
  `?b. next a s b s' /\ EVERY (ok_lit (FST s')) zs /\
    MAP (sat_lit b) zs = MAP2 f (MAP (sat_lit a) xs) (MAP (sat_lit a) ys)` by
    gvs[list_gate_rel_def] >>
  qexists_tac `b` >> simp[] >>
  `LENGTH zs = dimindex(:'a)` by
    (qpat_x_assum `MAP (sat_lit b) zs = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[]) >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_x_assum `MAP (sat_lit b) zs = _` (mp_tac o Q.AP_TERM `EL j`) >>
  simp[EL_MAP, EL_MAP2]
QED

Theorem bits_rel_and:
  inv a s /\ bits_rel a (FST s) xs x /\ bits_rel a (FST s) ys y /\
    bb_and xs ys s = (zs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') zs (x && y)
Proof
  strip_tac >>
  irule (Q.INST [`h` |-> `bb_and`, `f` |-> `(\p q. p /\ q)`] bits_rel_gate) >>
  simp[bb_and_ok, word_and_def, fcpTheory.FCP_BETA] >> metis_tac[]
QED

Theorem bits_rel_or:
  inv a s /\ bits_rel a (FST s) xs x /\ bits_rel a (FST s) ys y /\
    bb_or xs ys s = (zs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') zs (x || y)
Proof
  strip_tac >>
  irule (Q.INST [`h` |-> `bb_or`, `f` |-> `(\p q. p \/ q)`] bits_rel_gate) >>
  simp[bb_or_ok, word_or_def, fcpTheory.FCP_BETA] >> metis_tac[]
QED

Theorem bits_rel_xor:
  inv a s /\ bits_rel a (FST s) xs x /\ bits_rel a (FST s) ys y /\
    bb_xor xs ys s = (zs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') zs (x ?? y)
Proof
  strip_tac >>
  irule (Q.INST [`h` |-> `bb_xor`, `f` |-> `(\p q. p <> q)`] bits_rel_gate) >>
  simp[bb_xor_ok, word_xor_def, fcpTheory.FCP_BETA] >> metis_tac[]
QED

Theorem bb_all_ok:
  !xs a s r s'. inv a s /\ EVERY (ok_lit (FST s)) xs /\ bb_all xs s = (r,s') ==>
    ?a'. next a s a' s' /\ ok_lit (FST s') r /\
         (sat_lit a' r <=> EVERY (sat_lit a) xs)
Proof
  Induct >> rpt gen_tac
  >- (simp[bb_all_def] >> strip_tac >> gvs[] >> metis_tac[next_refl,
    inv_lits]) >>
  simp[Once bb_all_def] >> strip_tac >>
  rename1 `and2 x (FST (bb_all xs s)) (SND (bb_all xs s)) = (r,s')` >>
  Cases_on `bb_all xs s` >> rename1 `bb_all xs s = (tr,ts)` >> gvs[] >>
  qpat_x_assum `!a s r s'. _` (qspecl_then [`a`,`s`] mp_tac) >>
  simp[] >> strip_tac >>
  `inv a' ts /\ ok_lit (FST ts) x /\ (sat_lit a' x <=> sat_lit a x)` by
    (gvs[next_def] >> metis_tac[ok_lit_mono, sat_lit_agree]) >>
  `?b. next a' ts b s' /\ ok_lit (FST s') r /\
       (sat_lit b r <=> sat_lit a' x /\ sat_lit a' tr)` by
    (irule (SRULE [gate_ok_def] and2_ok) >> simp[]) >>
  qexists_tac `b` >> simp[] >> metis_tac[next_trans]
QED

Theorem bits_rel_all:
  inv a s /\ bits_rel a (FST s) xs (w:'a word) /\ bb_all xs s = (r,s') ==>
  ?a'. next a s a' s' /\ ok_lit (FST s') r /\ (sat_lit a' r <=> w = ~0w)
Proof
  rw[bits_rel_def] >> drule_all bb_all_ok >> strip_tac >>
  qexists_tac `a'` >> simp[] >>
  simp[EVERY_EL, fcpTheory.CART_EQ, word_1comp_def, word_0,
    fcpTheory.FCP_BETA] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem bits_rel_eq:
  inv a s /\ bits_rel a (FST s) xs x /\ bits_rel a (FST s) ys y /\
    bb_xor xs ys s = (es,t) /\ bb_all (bb_not es) t = (r,s') ==>
  ?a'. next a s a' s' /\ ok_lit (FST s') r /\ (sat_lit a' r <=> x = y)
Proof
  strip_tac >> drule_all bits_rel_xor >> strip_tac >>
  `inv a' t` by gvs[next_def] >>
  drule bits_rel_not >> strip_tac >> drule_all bits_rel_all >> strip_tac >>
  qexists_tac `a''` >>
  `next a s a'' s'` by metis_tac[next_trans] >> simp[] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem BCARRY_shift:
  !k x y c. BCARRY (SUC k) x y c =
    BCARRY k (x o SUC) (y o SUC) (bcarry (x 0) (y 0) c)
Proof
  Induct >- simp[BCARRY_def] >> rpt gen_tac >>
  pure_once_rewrite_tac[BCARRY_def] >> simp[combinTheory.o_DEF]
QED

Theorem BSUM_shift:
  BSUM (SUC k) x y c =
    BSUM k (x o SUC) (y o SUC) (bcarry (x 0) (y 0) c)
Proof
  simp[BSUM_def, BCARRY_shift, combinTheory.o_DEF]
QED

Theorem gate_step:
  gate_ok g f /\ inv a s /\ EVERY (ok_lit (FST s)) ls /\
    MEM x ls /\ MEM y ls /\ g x y s = (r,s') ==>
  ?a'. next a s a' s' /\ EVERY (ok_lit (FST s')) (r::ls) /\
    MAP (sat_lit a') ls = MAP (sat_lit a) ls /\
    (sat_lit a' r <=> f (sat_lit a x) (sat_lit a y))
Proof
  strip_tac >>
  `ok_lit (FST s) x /\ ok_lit (FST s) y` by gvs[EVERY_MEM] >>
  qpat_x_assum `gate_ok g f` mp_tac >> simp[gate_ok_def] >>
  disch_then drule_all >> strip_tac >> qexists_tac `a'` >>
  drule_all lits_next >> simp[]
QED

Theorem carry_network_ok:
  inv a s /\ EVERY (ok_lit (FST s)) [x;y;p;c] /\
  and2 x y s = (g,t) /\ and2 p c t = (h,u) /\ or2 g h u = (r,s') ==>
  ?a'. next a s a' s' /\ EVERY (ok_lit (FST s')) [r;x;y;p;c] /\
    MAP (sat_lit a') [x;y;p;c] = MAP (sat_lit a) [x;y;p;c] /\
    (sat_lit a' r <=>
       (sat_lit a x /\ sat_lit a y) \/ (sat_lit a p /\ sat_lit a c))
Proof
  strip_tac >>
  `?b. next a s b t /\ EVERY (ok_lit (FST t)) [g;x;y;p;c] /\
    MAP (sat_lit b) [x;y;p;c] = MAP (sat_lit a) [x;y;p;c] /\
    (sat_lit b g <=> sat_lit a x /\ sat_lit a y)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `and2`,
      `f` |-> `(\p q. p /\ q)`] (SPEC_ALL gate_step))) >>
     simp[and2_ok] >> metis_tac[MEM]) >>
  `inv b t` by gvs[next_def] >>
  `?d. next b t d u /\ EVERY (ok_lit (FST u)) [h;g;x;y;p;c] /\
    MAP (sat_lit d) [g;x;y;p;c] = MAP (sat_lit b) [g;x;y;p;c] /\
    (sat_lit d h <=> sat_lit b p /\ sat_lit b c)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `and2`,
      `f` |-> `(\p q. p /\ q)`] (SPEC_ALL gate_step))) >>
     simp[and2_ok] >> metis_tac[MEM]) >>
  `inv d u` by gvs[next_def] >>
  `?e. next d u e s' /\ EVERY (ok_lit (FST s')) [r;h;g;x;y;p;c] /\
    MAP (sat_lit e) [h;g;x;y;p;c] = MAP (sat_lit d) [h;g;x;y;p;c] /\
    (sat_lit e r <=> sat_lit d g \/ sat_lit d h)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `or2`,
      `f` |-> `(\p q. p \/ q)`] (SPEC_ALL gate_step))) >>
     simp[or2_ok] >> metis_tac[MEM]) >>
  qexists_tac `e` >> gvs[] >> metis_tac[next_trans]
QED

Theorem bb_carry_ok:
  !xs ys a s c r s'.
    inv a s /\ EVERY (ok_lit (FST s)) xs /\
    EVERY (ok_lit (FST s)) ys /\ ok_lit (FST s) c /\
    LENGTH xs = LENGTH ys /\ bb_carry xs ys c s = (r,s') ==>
    ?a'. next a s a' s' /\ ok_lit (FST s') r /\
      (sat_lit a' r <=> BCARRY (LENGTH xs)
        (\i. sat_lit a (EL i xs)) (\i. sat_lit a (EL i ys)) (sat_lit a c))
Proof
  Induct >- (simp[bb_carry_def, BCARRY_def] >> rpt strip_tac >>
    gvs[] >> metis_tac[next_refl]) >>
  Cases_on `ys` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `bb_carry (x::xs) (y::ys) c s = (r,s')` >>
  Cases_on `xor2 x y s` >> rename1 `xor2 x y s = (p,t)` >>
  Cases_on `and2 x y t` >> rename1 `and2 x y t = (g,u)` >>
  Cases_on `and2 p c u` >> rename1 `and2 p c u = (h,v)` >>
  Cases_on `or2 g h v` >> rename1 `or2 g h v = (k,z)` >>
  gvs[bb_carry_def] >>
  `?b. next a s b t /\ EVERY (ok_lit (FST t)) [p;x;y;c] /\
    MAP (sat_lit b) [x;y;c] = MAP (sat_lit a) [x;y;c] /\
    (sat_lit b p <=> sat_lit a x <> sat_lit a y)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `xor2`,
      `f` |-> `(\p q. p <> q)`] (SPEC_ALL gate_step))) >>
     simp[xor2_ok] >> metis_tac[MEM]) >>
  `inv b t` by gvs[next_def] >>
  `EVERY (ok_lit (FST t)) [x;y;p;c]` by gvs[] >>
  drule_all carry_network_ok >> strip_tac >>
  `next a s a' z` by metis_tac[next_trans] >>
  `EVERY (ok_lit (FST z)) xs /\ MAP (sat_lit a') xs = MAP (sat_lit a) xs` by
    metis_tac[lits_next] >>
  `EVERY (ok_lit (FST z)) ys /\ MAP (sat_lit a') ys = MAP (sat_lit a) ys` by
    metis_tac[lits_next] >>
  `inv a' z /\ ok_lit (FST z) k` by gvs[next_def] >>
  first_x_assum (qspecl_then [`ys`,`a'`,`z`,`k`,`r`,`s'`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `a''` >>
  conj_tac >- metis_tac[next_trans] >>
  gvs[BCARRY_shift, combinTheory.o_DEF] >>
  `(sat_lit a x /\ sat_lit a y \/ (sat_lit a x <> sat_lit a y) /\ sat_lit a c) =
    bcarry (sat_lit a x) (sat_lit a y) (sat_lit a c)` by
    (simp[bcarry_def] >> metis_tac[]) >>
  simp[] >> irule BCARRY_EQ >> rpt strip_tac >>
  metis_tac[EL_MAP]
QED

Theorem bb_add_ok:
  !xs ys a s c rs s'.
    inv a s /\ EVERY (ok_lit (FST s)) xs /\
    EVERY (ok_lit (FST s)) ys /\ ok_lit (FST s) c /\
    LENGTH xs = LENGTH ys /\ bb_add xs ys c s = (rs,s') ==>
    ?a'. next a s a' s' /\ EVERY (ok_lit (FST s')) rs /\
      LENGTH rs = LENGTH xs /\
      !j. j < LENGTH xs ==>
          (sat_lit a' (EL j rs) <=>
           BSUM j (\i. sat_lit a (EL i xs)) (\i. sat_lit a (EL i ys))
             (sat_lit a c))
Proof
  Induct >- (simp[bb_add_def] >> rpt strip_tac >>
    gvs[] >> metis_tac[next_refl]) >>
  Cases_on `ys` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `bb_add (x::xs) (y::ys) c s = (rs,s')` >>
  Cases_on `xor2 x y s` >> rename1 `xor2 x y s = (p,t)` >>
  Cases_on `xor2 p c t` >> rename1 `xor2 p c t = (q,u)` >>
  Cases_on `and2 x y u` >> rename1 `and2 x y u = (g,v)` >>
  Cases_on `and2 p c v` >> rename1 `and2 p c v = (h,z)` >>
  Cases_on `or2 g h z` >> rename1 `or2 g h z = (k,st)` >>
  Cases_on `bb_add xs ys k st` >> rename1 `bb_add xs ys k st = (qs,fin)` >>
  gvs[bb_add_def] >>
  `?b. next a s b t /\ EVERY (ok_lit (FST t)) [p;x;y;c] /\
    MAP (sat_lit b) [x;y;c] = MAP (sat_lit a) [x;y;c] /\
    (sat_lit b p <=> sat_lit a x <> sat_lit a y)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `xor2`,
      `f` |-> `(\p q. p <> q)`] (SPEC_ALL gate_step))) >>
     simp[xor2_ok] >> metis_tac[MEM]) >>
  `inv b t` by gvs[next_def] >>
  `?d. next b t d u /\ EVERY (ok_lit (FST u)) [q;p;x;y;c] /\
    MAP (sat_lit d) [p;x;y;c] = MAP (sat_lit b) [p;x;y;c] /\
    (sat_lit d q <=> sat_lit b p <> sat_lit b c)` by
    (irule (BETA_RULE (Q.INST [`g` |-> `xor2`,
      `f` |-> `(\p q. p <> q)`] (SPEC_ALL gate_step))) >>
     simp[xor2_ok] >> metis_tac[MEM]) >>
  `inv d u` by gvs[next_def] >>
  `EVERY (ok_lit (FST u)) [x;y;p;c]` by gvs[] >>
  drule_all carry_network_ok >> strip_tac >>
  `next a s a' st /\ next d u a' st` by metis_tac[next_trans] >>
  `EVERY (ok_lit (FST st)) xs /\ MAP (sat_lit a') xs = MAP (sat_lit a) xs` by
    metis_tac[lits_next] >>
  `EVERY (ok_lit (FST st)) ys /\ MAP (sat_lit a') ys = MAP (sat_lit a) ys` by
    metis_tac[lits_next] >>
  `inv a' st /\ ok_lit (FST st) k` by gvs[next_def] >>
  first_x_assum (qspecl_then [`ys`,`a'`,`st`,`k`,`qs`,`fin`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `a''` >>
  conj_tac >- metis_tac[next_trans] >>
  `next d u a'' fin` by metis_tac[next_trans] >>
  `EVERY (ok_lit (FST fin)) [q;p;x;y;c] /\
    MAP (sat_lit a'') [q;p;x;y;c] = MAP (sat_lit d) [q;p;x;y;c]` by
    metis_tac[lits_next] >>
  gvs[] >> Cases_on `j`
  >- (simp[BSUM_def, BCARRY_def, bsum_def] >> metis_tac[]) >>
  simp[BSUM_shift, combinTheory.o_DEF] >> strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  `(sat_lit a x /\ sat_lit a y \/ (sat_lit a x <> sat_lit a y) /\ sat_lit a c) =
    bcarry (sat_lit a x) (sat_lit a y) (sat_lit a c)` by
    (simp[bcarry_def] >> metis_tac[]) >>
  simp[] >> irule BSUM_EQ >> rpt strip_tac >> `i < LENGTH ys` by decide_tac >>
    metis_tac[EL_MAP]
QED

Theorem bits_rel_sum:
  inv a s /\ bits_rel a (FST s) xs (x:'a word) /\
  bits_rel a (FST s) ys (y:'a word) /\ ok_lit (FST s) c /\
  bb_add xs ys c s = (rs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') rs
    ((FCP i. BSUM i ($' x) ($' y) (sat_lit a c)):'a word)
Proof
  strip_tac >>
  `EVERY (ok_lit (FST s)) xs /\ EVERY (ok_lit (FST s)) ys /\
    LENGTH xs = LENGTH ys` by gvs[bits_rel_def] >>
  drule_all bb_add_ok >> strip_tac >> qexists_tac `a'` >> simp[] >>
  simp[bits_rel_def, fcpTheory.FCP_BETA] >> conj_tac
  >- gvs[bits_rel_def] >>
  rpt strip_tac >> `j < LENGTH xs` by gvs[bits_rel_def] >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  irule BSUM_EQ >> gvs[bits_rel_def] >> rpt strip_tac >>
  `i < dimindex(:'a)` by decide_tac >> simp[]
QED

Theorem bits_rel_add:
  inv a s /\ bits_rel a (FST s) xs (x:'a word) /\
  bits_rel a (FST s) ys (y:'a word) /\ bb_add xs ys (-1) s = (rs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') rs (x + y)
Proof
  strip_tac >> `ok_lit (FST s) (-1) /\ ~sat_lit a (-1)` by
    metis_tac[inv_lits] >>
  drule_all bits_rel_sum >> simp[GSYM BITWISE_ADD]
QED

Theorem bits_rel_neg:
  inv a s /\ bits_rel a (FST s) xs (x:'a word) /\
  bb_add (bb_rep (dimindex(:'a)) (-1)) (bb_not xs) 1 s = (rs,s') ==>
  ?a'. next a s a' s' /\ bits_rel a' (FST s') rs (-x)
Proof
  strip_tac >>
  `bits_rel a (FST s) (bb_rep (dimindex(:'a)) (-1)) (0w:'a word)` by
    metis_tac[bits_rel_zero] >>
  `bits_rel a (FST s) (bb_not xs) (~x)` by metis_tac[bits_rel_not] >>
  `ok_lit (FST s) 1 /\ sat_lit a 1` by metis_tac[inv_lits] >>
  drule_all bits_rel_sum >> simp[] >>
  `((FCP i. BSUM i ($' (0w:'a word)) ($' (~x)) T):'a word) = -x` by
    (simp[GSYM WORD_SUB_LZERO, BITWISE_SUB, fcpTheory.CART_EQ,
      fcpTheory.FCP_BETA] >>
     rpt strip_tac >> irule BSUM_EQ >> rpt strip_tac >>
     `i < dimindex(:'a)` by decide_tac >>
     simp[word_1comp_def, fcpTheory.FCP_BETA, combinTheory.o_DEF]) >>
  simp[]
QED

Theorem bits_rel_ult:
  inv a s /\ bits_rel a (FST s) xs (x:'a word) /\
  bits_rel a (FST s) ys (y:'a word) /\ bb_carry xs (bb_not ys) 1 s = (r,s') ==>
  ?a'. next a s a' s' /\ ok_lit (FST s') (-r) /\ (sat_lit a' (-r) <=> x <+ y)
Proof
  strip_tac >> drule_at (Pos last) bits_rel_not >> strip_tac >>
  `EVERY (ok_lit (FST s)) xs /\ EVERY (ok_lit (FST s)) (bb_not ys) /\
    LENGTH xs = LENGTH (bb_not ys)` by gvs[bits_rel_def] >>
  `ok_lit (FST s) 1 /\ sat_lit a 1` by metis_tac[inv_lits] >>
  drule_all bb_carry_ok >> strip_tac >> qexists_tac `a'` >> simp[] >>
  conj_tac >- metis_tac[ok_lit_neg] >>
  simp[sat_lit_neg_eq] >>
  `BCARRY (LENGTH xs) (\i. sat_lit a (EL i xs))
      (\i. sat_lit a (EL i (bb_not ys))) T =
    BCARRY (dimindex(:'a)) ($' x) ((~) o ($' y)) T` by
    (gvs[bits_rel_def] >> irule BCARRY_EQ >> rpt strip_tac >>
     simp[word_1comp_def, fcpTheory.FCP_BETA]) >>
  gvs[BITWISE_LO] >> metis_tac[sat_lit_neg_eq]
QED

Theorem blast_node_ok:
  inv a s /\ map_rel a (FST s) m vs /\
    blast_node (dimindex(:'a)) m nd s = (SOME l,s') ==>
  ?a'. next a s a' s' /\ value_rel a' (FST s') l
    (eval_node (env:num -> 'a word) benv vs (LENGTH vs) nd)
Proof
  strip_tac >> Cases_on `s` >> rename1 `inv a (q,r)` >> Cases_on `nd`
  >- suspend "var"
  >- suspend "const"
  >- suspend "not"
  >- suspend "and"
  >- suspend "or"
  >- suspend "xor"
  >- suspend "add"
  >- suspend "neg"
  >- suspend "shl"
  >- suspend "lsr"
  >- suspend "asr"
  >- suspend "bvar"
  >- suspend "bconst"
  >- suspend "ult"
  >- suspend "eq"
  >- suspend "bit"
  >- suspend "band"
  >- suspend "bor"
  >- suspend "bnot"
  >- suspend "imp"
  >> suspend "iff"
QED

Resume blast_node_ok[var]:
  gvs[blast_node_def, eval_node_def, value_rel_def] >> metis_tac[word_alloc]
QED
Resume blast_node_ok[const]:
  gvs[blast_node_def, eval_node_def, value_rel_def] >>
  qexists_tac `a` >> conj_tac >- metis_tac[next_refl] >>
  drule bits_rel_const >> simp[]
QED
Resume blast_node_ok[not]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  gvs[eval_node_def, wval_def, value_rel_def] >> metis_tac[next_refl,
    bits_rel_not]
QED
Resume blast_node_ok[and]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_and xs ys (q,r)` >> gvs[wres_def, eval_node_def, wval_def,
    value_rel_def] >>
  irule bits_rel_and >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[or]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_or xs ys (q,r)` >> gvs[wres_def, eval_node_def, wval_def,
    value_rel_def] >>
  irule bits_rel_or >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[xor]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_xor xs ys (q,r)` >> gvs[wres_def, eval_node_def, wval_def,
    value_rel_def] >>
  irule bits_rel_xor >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[add]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_add xs ys (-1) (q,r)` >> gvs[wres_def, eval_node_def, wval_def,
    value_rel_def] >>
  irule bits_rel_add >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[neg]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  rename1 `wlits m i = SOME xs` >>
  Cases_on `bb_add (bb_rep (dimindex(:'a)) (-1)) (bb_not xs) 1 (q,r)` >>
  gvs[wres_def, eval_node_def, wval_def, value_rel_def] >>
  irule (SRULE [] bits_rel_neg) >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[shl]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  gvs[eval_node_def, wval_def, value_rel_def] >>
  qexists_tac `a` >> simp[next_refl] >> metis_tac[bits_rel_shl, FST]
QED
Resume blast_node_ok[lsr]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  gvs[eval_node_def, wval_def, value_rel_def] >>
  qexists_tac `a` >> simp[next_refl] >> metis_tac[bits_rel_lsr, FST]
QED
Resume blast_node_ok[asr]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  gvs[eval_node_def, wval_def, value_rel_def] >>
  qexists_tac `a` >> simp[next_refl] >> metis_tac[bits_rel_asr, FST]
QED
Resume blast_node_ok[bvar]:
  gvs[blast_node_def, eval_node_def, value_rel_def] >> metis_tac[bool_alloc]
QED
Resume blast_node_ok[bconst]:
  gvs[blast_node_def, eval_node_def, value_rel_def] >>
  drule inv_lits >> strip_tac >> qexists_tac `a` >>
  simp[next_refl] >> Cases_on `b` >> gvs[]
QED
Resume blast_node_ok[ult]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_carry xs (bb_not ys) 1 (q,r)` >>
  gvs[eval_node_def, wval_def, value_rel_def] >>
  irule bits_rel_ult >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[eq]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `wlits m i = SOME xs` >> rename1 `wlits m j = SOME ys` >>
  `?x. EL i vs = Word x /\ bits_rel a (FST (q,r)) xs x` by
    metis_tac[map_rel_wlits, FST] >>
  `?y. EL j vs = Word y /\ bits_rel a (FST (q,r)) ys y` by
    metis_tac[map_rel_wlits, FST] >>
  Cases_on `bb_xor xs ys (q,r)` >> rename1 `bb_xor xs ys (q,r) = (es,t)` >>
  Cases_on `bb_all (bb_not es) t` >>
  gvs[bres_def, eval_node_def, wval_def, value_rel_def] >>
  irule bits_rel_eq >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[bit]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_wlits >> strip_tac >>
  gvs[eval_node_def, wval_def, value_rel_def] >>
  qexists_tac `a` >> simp[next_refl] >> gvs[bits_rel_def] >> metis_tac[EVERY_EL]
QED
Resume blast_node_ok[band]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `blits m i = SOME p` >> rename1 `blits m j = SOME z` >>
  `EL i vs = Bool (sat_lit a p) /\ ok_lit q p` by metis_tac[map_rel_blits] >>
  `EL j vs = Bool (sat_lit a z) /\ ok_lit q z` by metis_tac[map_rel_blits] >>
  Cases_on `and2 p z (q,r)` >>
  gvs[bres_def, eval_node_def, bval_def, value_rel_def] >>
  irule (SRULE [gate_ok_def] and2_ok) >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[bor]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `blits m i = SOME p` >> rename1 `blits m j = SOME z` >>
  `EL i vs = Bool (sat_lit a p) /\ ok_lit q p` by metis_tac[map_rel_blits] >>
  `EL j vs = Bool (sat_lit a z) /\ ok_lit q z` by metis_tac[map_rel_blits] >>
  Cases_on `or2 p z (q,r)` >>
  gvs[bres_def, eval_node_def, bval_def, value_rel_def] >>
  irule (SRULE [gate_ok_def] or2_ok) >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[bnot]:
  gvs[blast_node_def, AllCaseEqs()] >> drule_all map_rel_blits >> strip_tac >>
  gvs[eval_node_def, bval_def, value_rel_def] >>
  qexists_tac `a` >> simp[next_refl] >> metis_tac[ok_lit_neg, sat_lit_neg_eq]
QED
Resume blast_node_ok[imp]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `blits m i = SOME p` >> rename1 `blits m j = SOME z` >>
  `EL i vs = Bool (sat_lit a p) /\ ok_lit q p` by metis_tac[map_rel_blits] >>
  `EL j vs = Bool (sat_lit a z) /\ ok_lit q z` by metis_tac[map_rel_blits] >>
  Cases_on `or2 (-p) z (q,r)` >> rename1 `or2 (-p) z (q,r) = (out,t)` >>
  gvs[bres_def, eval_node_def, bval_def, value_rel_def] >>
  `ok_lit (FST (q,r)) (-p) /\ (sat_lit a (-p) <=> ~sat_lit a p)` by
    metis_tac[ok_lit_neg, sat_lit_neg_eq, FST] >>
  `?b. next a (q,r) b s' /\ ok_lit (FST s') out /\
    (sat_lit b out <=> sat_lit a (-p) \/ sat_lit a z)` by
    (irule (SRULE [gate_ok_def] or2_ok) >> simp[] >> metis_tac[]) >>
  qexists_tac `b` >> simp[] >> metis_tac[]
QED
Resume blast_node_ok[iff]:
  gvs[blast_node_def, AllCaseEqs()] >>
  rename1 `blits m i = SOME p` >> rename1 `blits m j = SOME z` >>
  `EL i vs = Bool (sat_lit a p) /\ ok_lit q p` by metis_tac[map_rel_blits] >>
  `EL j vs = Bool (sat_lit a z) /\ ok_lit q z` by metis_tac[map_rel_blits] >>
  Cases_on `xor2 p z (q,r)` >> rename1 `xor2 p z (q,r) = (out,t)` >>
  gvs[bres_def, eval_node_def, bval_def, value_rel_def] >>
  `?b. next a (q,r) b t /\ ok_lit (FST t) out /\
    (sat_lit b out <=> sat_lit a p <> sat_lit a z)` by
    (irule (SRULE [gate_ok_def] xor2_ok) >> simp[] >> metis_tac[]) >>
  qexists_tac `b` >> simp[] >> metis_tac[ok_lit_neg, sat_lit_neg_eq]
QED
Finalise blast_node_ok

Theorem blast_nodes_ok:
  !nds a s m vs m' s'.
  inv a s /\ map_rel a (FST s) m vs /\
  blast_nodes (dimindex(:'a)) m (LENGTH vs) nds s = SOME (m',s') ==>
  ?a'. next a s a' s' /\
       map_rel a' (FST s') m' (eval_nodes env benv (vs:'a value list) nds)
Proof
  Induct_on `nds`
  >- (simp[blast_nodes_def, eval_nodes_def] >> metis_tac[next_refl]) >>
  rpt gen_tac >> strip_tac >>
  gvs[blast_nodes_def, AllCaseEqs()] >>
  drule_all blast_node_ok >>
  disch_then (qspecl_then [`env`,`benv`] strip_assume_tac) >>
  `map_rel a' (FST s1) m vs` by metis_tac[map_rel_next] >>
  drule_all map_rel_insert >> strip_tac >>
  `inv a' s1` by gvs[next_def] >>
  first_x_assum (qspecl_then [`a'`,`s1`,`insert (LENGTH vs) l m`,
    `vs ++ [eval_node env benv vs (LENGTH vs) h]`,`m'`,`s'`] mp_tac) >>
  simp[eval_nodes_def] >> strip_tac >>
  qexists_tac `a''` >> simp[] >> metis_tac[next_trans]
QED

Theorem eval_nodes_length[local]:
  !vs. LENGTH (eval_nodes env benv vs nds) = LENGTH vs + LENGTH nds
Proof
  Induct_on `nds` >> simp[eval_nodes_def]
QED

(* Why it holds: if some env, benv make the root false, the CNF has a model.
   Give each word variable node's SAT variables the bits of env i (BVar: benv
   i) and each fresh Tseitin variable the value of its gate on its inputs;
   then every gate clause holds, [1] holds, and [-root] holds.  The gate
   lemmas above (gate_ok, next, fresh_ok) are the per-variable step of that
   construction.  Word operations correspond bit by bit (bit j = EL j, least
   significant first) through blastTheory's BITWISE_ADD, BITWISE_SUB (for
   negation as 0w - x) and BITWISE_LO (for <+). *)
Theorem blast_dag_sound:
  check_unsat steps (blast_dag (dimindex(:'a)) dag) ⇒
  ∀(env : num -> 'a word) benv. eval_dag env benv dag
Proof
  strip_tac >> rpt gen_tac >> spose_not_then assume_tac >>
  drule check_unsat_sound >>
  Cases_on `blast_nodes (dimindex(:'a)) LN 0 dag (2,[])`
  >- simp[blast_dag_def] >>
  rename1 `blast_nodes (dimindex(:'a)) LN 0 dag (2,[]) = SOME result` >>
  PairCases_on `result` >>
  Cases_on `blits result0 (LENGTH dag - 1)`
  >- simp[blast_dag_def] >>
  rename1 `blits result0 (LENGTH dag - 1) = SOME root` >>
  `inv (\v. T) (2,[])` by simp[inv_def] >>
  `map_rel (\v. T) (FST (2,[])) LN ([]:'a value list)` by simp[map_rel_empty] >>
  `blast_nodes (dimindex(:'a)) LN (LENGTH ([]:'a value list)) dag (2,[]) =
    SOME (result0,result1,result2)` by simp[] >>
  drule blast_nodes_ok >> simp[map_rel_empty] >>
  disch_then (qspecl_then [`env`,`benv`] strip_assume_tac) >>
  `map_rel (\v. T) 2 LN ([]:'a value list)` by simp[map_rel_empty] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all map_rel_blits >> simp[eval_nodes_length] >> strip_tac >>
  qpat_x_assum `check_unsat _ _` kall_tac >>
  qpat_x_assum `blast_nodes _ LN (LENGTH []) _ _ = _` kall_tac >>
  qpat_x_assum `map_rel (\v. T) 2 LN []` kall_tac >>
  qpat_x_assum `map_rel (\v. T) (FST _) LN []` kall_tac >>
  qpat_x_assum `inv (\v. T) _` kall_tac >>
  `LENGTH (eval_nodes env benv [] dag) = LENGTH dag` by
    simp[eval_nodes_length] >>
  `eval_nodes env benv [] dag <> []` by (strip_tac >> fs[]) >>
  `LAST (eval_nodes env benv [] dag) = Bool (sat_lit a' root)` by
    (qpat_x_assum `EL _ _ = _` mp_tac >> simp[LAST_EL,
    arithmeticTheory.PRE_SUB1]) >>
  `~sat_lit a' root` by (qpat_x_assum `~eval_dag _ _ _` mp_tac >>
    simp[eval_dag_def, bval_def]) >>
  `inv a' (result1,result2)` by fs[next_def] >>
  `sat_lit a' (-root)` by metis_tac[sat_lit_neg_eq] >>
  qexists_tac `a'` >>
  qpat_x_assum `blast_nodes _ LN 0 _ _ = _`
    (fn th => rewrite_tac[blast_dag_def, th]) >>
  qpat_x_assum `blits _ _ = _` (fn th => simp[th]) >>
  fs[inv_def, sat_clause_def, sat_lit_def]
QED

Definition check_dag_def:
  check_dag w dag steps = check_unsat steps (blast_dag w dag)
End

val _ = cv_auto_trans check_dag_def;
