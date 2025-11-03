Theory path_aux
Ancestors
  option pair pred_set finite_map string list llist path
Libs
  intLib

(* Stuff about paths in an LTS that should end up in HOL's path library *)


val ect = BasicProvers.EVERY_CASE_TAC;

(* Copied from pathScript in HOL and generalised to 2 relations *)
val okpath_pmap2 = store_thm(
  "okpath_pmap2",
  ``!R1 R2 f g p. okpath R1 p /\ (!x r y. R1 x r y ==> R2 (f x) (g r) (f y)) ==>
                  okpath R2 (pmap f g p)``,
  REPEAT STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!p. (?p0. okpath R1 p0 /\ (p = pmap f g p0)) ==> okpath R2 p` THEN1
        METIS_TAC[] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p0` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

Theorem PL_pgenerate:
 !x f g. x ∈ PL (pgenerate f g)
Proof
 rw [] >>
 metis_tac [infinite_PL, pgenerate_infinite]
QED

Theorem PL_take_eq:
 n ∈ PL p ⇒ (x ∈ PL (take n p) ⇔ x ≤ n ∧ x ∈ PL p)
Proof
 rw [] >>
 imp_res_tac PL_take >>
 fs [EXTENSION] >>
 eq_tac >>
 rw [] >>
 Cases_on `x = n` >>
 fs [] >>
 `x < n` by decide_tac >>
 metis_tac [PL_downward_closed]
QED

Theorem tail_take:
 !n p. n ≠ 0 ⇒ tail (take n p) = take (n - 1) (tail p)
Proof
 Induct_on `n` >>
 rw []
QED

Theorem el_take:
 !m n p. m ≤ n ⇒ el m (take n p) = el m p
Proof
 Induct_on `m` >>
 rw [] >>
 Cases_on `n = 0` >>
 fs [] >>
 `m ≤ n - 1` by decide_tac >>
 res_tac >>
 rw [tail_take]
QED

Theorem path_eq:
 !p1 p2.
  p1 = p2
  ⇔
  PL p1 = PL p2 ∧
  !n. (n ∈ PL p1 ⇒ el n p1 = el n p2) ∧ (SUC n ∈ PL p1 ⇒ nth_label n p1 = nth_label n p2)
Proof
 rw [] >>
 eq_tac >>
 rw [] >>
 rw [Once path_bisimulation] >>
 qexists_tac `\p1 p2. PL p1 = PL p2 ∧ !n. (n ∈ PL p1 ⇒ el n p1 = el n p2) ∧ (SUC n ∈ PL p1 ⇒ nth_label n p1 = nth_label n p2)` >>
 rw [] >>
 `(?x. q1 = stopped_at x) ∨ ?x l p1'. q1 = pcons x l p1'` by metis_tac [path_cases] >>
 `(?x. q2 = stopped_at x) ∨ ?x l p1'. q2 = pcons x l p1'` by metis_tac [path_cases] >>
 rw [] >>
 fs [alt_length_thm, length_never_zero] >>
 fs [EXTENSION] >>
 rw [] >>
 fs []
 >- metis_tac [PL_0, arithmeticTheory.SUC_NOT, prim_recTheory.INV_SUC_EQ, arithmeticTheory.num_CASES]
 >- metis_tac [PL_0, arithmeticTheory.SUC_NOT, prim_recTheory.INV_SUC_EQ, arithmeticTheory.num_CASES]
 >- (pop_assum (qspec_then `0` mp_tac) >>
     rw [])
 >- (pop_assum (qspec_then `0` mp_tac) >>
     rw [])
 >- (Cases_on `x''` >>
     metis_tac [PL_0, arithmeticTheory.SUC_NOT, prim_recTheory.INV_SUC_EQ, arithmeticTheory.num_CASES])
 >- (first_x_assum (qspec_then `SUC n` mp_tac) >>
     rw [] >>
     metis_tac [PL_0, arithmeticTheory.SUC_NOT, prim_recTheory.INV_SUC_EQ, arithmeticTheory.num_CASES])
 >- (first_x_assum (qspec_then `SUC n` mp_tac) >>
     rw [] >>
     metis_tac [PL_0, arithmeticTheory.SUC_NOT, prim_recTheory.INV_SUC_EQ, arithmeticTheory.num_CASES])
QED

Theorem take_eq:
 !n p1 p2.
  (n ∈ PL p1 ∧ n ∈ PL p2)
  ⇒
  (take n p1 = take n p2
   ⇔
   (!m. m ≤ n ⇒ el m p1 = el m p2) ∧
   (!m. m < n ⇒ nth_label m p1 = nth_label m p2))
Proof
 rw [] >>
 eq_tac >>
 rw [path_eq]
 >- (first_x_assum (qspec_then `m` mp_tac) >>
     rw [] >>
     rfs [el_take])
 >- (first_x_assum (qspec_then `m` mp_tac) >>
     rw [] >>
     rfs [nth_label_take] >>
     pop_assum match_mp_tac >>
     decide_tac)
 >- rw [el_take] >>
 `n' < n` by decide_tac >>
  rw [nth_label_take]
QED

Theorem first_pconcat[simp]:
 !p1 l p2. first (pconcat p1 l p2) = first p1
Proof
 rw [] >>
 `(?x. p1 = stopped_at x) ∨ ?x l p1'. p1 = pcons x l p1'` by metis_tac [path_cases] >>
 rw [pconcat_thm]
QED

Theorem last_pconcat[simp]:
 !p1. finite p1 ⇒ !l p2. last (pconcat p1 l p2) = last p2
Proof
 ho_match_mp_tac finite_path_ind >>
 rw [pconcat_thm]
QED

Theorem okpath_pconcat[simp]:
 !p1.
  finite p1
  ⇒
  !R l p2.
    (okpath R (pconcat p1 l p2) ⇔ okpath R p1 ∧ okpath R p2 ∧ R (last p1) l (first p2))
Proof
 ho_match_mp_tac finite_path_ind >>
 rw [pconcat_thm]
 >- metis_tac [] >>
 eq_tac >>
 rw [] >>
 fs [first_pconcat]
QED

Theorem pmap_pmap:
 !f g f' g' p. pmap f g (pmap f' g' p) = pmap (f o f') (g o g') p
Proof
 rw [path_eq]
QED

Theorem labels_pmap[simp]:
 !f g p. labels (pmap f g p) = LMAP g (labels p)
Proof
 rw [labels_LMAP, LMAP_MAP, pmap_def, path_rep_bijections_thm] >>
 rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
 rw [FUN_EQ_THM]
QED

Theorem labels_pconcat[simp]:
 !p1 l p2. labels (pconcat p1 l p2) = (LAPPEND (labels p1) (l:::labels p2))
Proof
 rw [labels_LMAP, pconcat_def, path_rep_bijections_thm,LMAP_APPEND]
QED

Theorem lmap_I[simp]:
 !l. LMAP I l = l
Proof
 rw [Once LLIST_BISIMULATION] >>
 qexists_tac `(\x y. LMAP I y = x)` >>
 rw [] >>
 `ll4 = [||] ∨ ?x y. ll4=x:::y` by metis_tac [llist_CASES] >>
 rw []
QED

Theorem LTAKE_length:
 !n l. LLENGTH l = SOME n ⇒ LTAKE n l = toList l
Proof
 Induct_on `n` >>
 rw [] >>
 `l = [||] ∨ ?x y. l=x:::y` by metis_tac [llist_CASES] >>
 rw [toList] >>
 fs [LLENGTH]
QED

Theorem toList_lappend:
 !l1.
  LFINITE l1 ⇒ !l2. LFINITE l2
  ⇒
  THE (toList (LAPPEND l1 l2)) = THE (toList l1) ++ THE (toList l2)
Proof
 ho_match_mp_tac LFINITE_ind >>
 rw [toList] >>
 fs [LFINITE_APPEND, LLENGTH_APPEND] >>
 rfs [] >>
 res_tac >>
 imp_res_tac LFINITE_HAS_LENGTH >>
 fs [] >>
 `LLENGTH (LAPPEND l1 l2) = SOME (n' + n)` by rw [LLENGTH_APPEND] >>
 imp_res_tac LTAKE_length >>
 fs [] >>
 `LFINITE (LAPPEND l1 l2)` by rw [LFINITE_APPEND] >>
 imp_res_tac LFINITE_toList >>
 fs []
QED

val okpath_steps_lem1 = Q.prove (
`!p.
  (!n. n + 1 ∈ PL p ⇒ rel (el n p) (nth_label n p) (el (n+1) p))
  ⇒
  okpath rel p`,
 ho_match_mp_tac okpath_co_ind >>
 rw []
 >- (pop_assum (qspec_then `0` mp_tac) >>
     rw [el_compute]) >>
 first_x_assum (qspec_then `n+1` mp_tac) >>
 fs [GSYM arithmeticTheory.ADD1]);

val okpath_steps_lem2 = Q.prove (
`!n p rel.
  okpath rel p ∧
  n + 1 ∈ PL p
  ⇒
  rel (el n p) (nth_label n p) (el (n+1) p)`,
 Induct_on `n` >>
 rw [] >>
 fs [Once okpath_cases] >>
 rw [] >>
 fs []
 >- (rw_tac (bool_ss) [DECIDE ``1 = SUC 0``, el_def] >>
     rw []) >>
 fs [DECIDE ``!x. x + 1 = SUC x``] >>
 rw [] >>
 fs [el_def] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 `(?s. p' = stopped_at s) ∨ (?s1 l s'. p' = pcons s1 l s')` by metis_tac [path_cases] >>
 rw [] >>
 fs []);

Theorem okpath_steps:
 !p rel.
  okpath rel p
  ⇔
  (!n. n + 1 ∈ PL p ⇒ rel (el n p) (nth_label n p) (el (n+1) p))
Proof
 metis_tac [okpath_steps_lem2, okpath_steps_lem1]
QED

Theorem path_limit:
 !P rel.
  (!p. p ∈ P ⇒ finite p ∧ okpath rel p) ∧
  (!n. ?p. p ∈ P ∧ n ∈ PL p) ∧
  (!p1 p2 n. p1 ∈ P ∧ p2 ∈ P ∧ n ∈ PL p1 ∧ n ∈ PL p2 ⇒ take n p1 = take n p2)
  ⇒
  ?p.
    ~finite p ∧
    okpath rel p ∧
    !n p'.
      p' ∈ P ⇒
      (n ∈ PL p' ⇒ take n p' = take n p)
Proof
 rw [SKOLEM_THM, PULL_EXISTS] >>
 qexists_tac `pgenerate (\n. el n (f (SUC n))) (λn. nth_label n (f (SUC n)))` >>
 rw []
 >- metis_tac [finite_length, pgenerate_infinite]
 >- (fs [okpath_steps, el_pgenerate, nth_label_pgenerate] >>
     rw [] >>
     `take (n+1) (f (SUC (n+1))) = take (n+1) (f (SUC n))`
            by (first_x_assum match_mp_tac >>
                rw [] >>
                fs [GSYM arithmeticTheory.ADD1] >>
                `SUC n < SUC (SUC n)` by decide_tac >>
                metis_tac [PL_downward_closed]) >>
     `n + 1 ∈ PL (f (SUC (n + 1)))` by metis_tac [PL_downward_closed, DECIDE ``n+1 < SUC (n+1)``] >>
     `n + 1 ∈ PL (f (SUC (n)))` by metis_tac [arithmeticTheory.ADD1] >>
     fs [take_eq])
 >- (rw [path_eq, el_take, el_pgenerate, nth_label_take]
     >- (rw [EXTENSION] >>
         `n ∈ PL (pgenerate (λn. el n (f (SUC n))) (λn. nth_label n (f (SUC n))))`
                by rw [PL_pgenerate] >>
         rw [PL_take_eq, PL_pgenerate])
     >- (`take n' p' = take n' (f (SUC n'))`
              by (first_x_assum match_mp_tac >>
                  rw [] >>
                  `n' < n ∨ n' = n` by decide_tac >>
                  rw [] >>
                  metis_tac [DECIDE ``!x:num. x < SUC x``, PL_downward_closed]) >>
         `n' ∈ PL p'`
                 by metis_tac [PL_downward_closed, arithmeticTheory.LESS_OR_EQ] >>
         `SUC n' ∈ PL (f (SUC n'))` by metis_tac [] >>
         `n' ∈ PL (f (SUC n'))` by metis_tac [DECIDE ``!x:num. x < SUC x``, PL_downward_closed] >>
         fs [take_eq])
     >- (`take (SUC n') p' = take (SUC n') (f (SUC n'))`
              by (first_x_assum match_mp_tac >>
                  rw [] >>
                  `SUC n' < n ∨ SUC n' = n` by decide_tac >>
                  rw [] >>
                  metis_tac [DECIDE ``!x:num. x < SUC x``, PL_downward_closed]) >>
         `n' < n` by decide_tac >>
         `n ∈ PL (pgenerate (λn. el n (f (SUC n))) (λn. nth_label n (f (SUC n))))`
                     by rw [PL_pgenerate] >>
         rw [nth_label_take, nth_label_pgenerate] >>
         `SUC n' ∈ PL p'` by metis_tac [arithmeticTheory.LESS_OR_EQ, PL_downward_closed] >>
         `SUC n' ∈ PL (f (SUC n'))` by metis_tac [PL_downward_closed] >>
         fs [take_eq]))
QED

Definition lfilter_map_def:
lfilter_map f l = LMAP THE (LFILTER (\x. x ≠ NONE) (LMAP f l))
End

Theorem lfinite_lfilter:
 !l. LFINITE l ⇒ LFINITE (LFILTER P l)
Proof
 ho_match_mp_tac LFINITE_ind >>
 rw []
QED

Definition inf_const_def:
inf_const c = LUNFOLD (\x:unit. SOME (x,c)) ARB
End

Definition complete_def:
complete rel p ⇔ (finite p ⇒ ¬?l s. rel (last p) l s)
End

Definition compose_paths_def:
compose_paths p1 p2 =
  unfold (\(p1,p2). (first p1, first p2))
         (\(p1,p2).
           if is_stopped p1 ∨ is_stopped p2 then
             NONE
           else if first_label p1 = first_label p2 then
             SOME ((tail p1, tail p2), first_label p1)
           else NONE)
        (p1,p2)
End

Theorem compose_paths_stopped[simp]:
 (!x y. compose_paths (stopped_at x) (stopped_at y) = stopped_at (x,y))
Proof
 rw [compose_paths_def] >>
 rw [Once unfold_thm]
QED

Theorem compose_paths_pcons[simp]:
 (!x y l p1 p2. compose_paths (pcons x l p1) (pcons y l p2) = pcons (x,y) l (compose_paths p1 p2))
Proof
 rw [compose_paths_def] >>
 rw [Once unfold_thm]
QED

Theorem okpath_compose_paths:
 !r1 r2 p1 p2.
  okpath r1 p1 ∧
  okpath r2 p2
  ⇒
  okpath (parallel_comp r1 r2) (compose_paths p1 p2)
Proof
 rw [compose_paths_def, okpath_parallel_comp] >>
 match_mp_tac okpath_pmap2
 >- (qexists_tac `\s1 l s2. r1 (FST s1) l (FST s2)` >>
     rw [] >>
     match_mp_tac okpath_unfold >>
     qexists_tac `λ(p1,p2). okpath r1 p1` >>
     rw [] >>
     PairCases_on `s` >>
     fs [] >>
     rw [] >>
     `(?s. s0 = stopped_at s) ∨ (?s1 l s'. s0 = pcons s1 l s')` by metis_tac [path_cases] >>
     rw [] >>
     fs [])
 >- (qexists_tac `\s1 l s2. r2 (SND s1) l (SND s2)` >>
     rw [] >>
     match_mp_tac okpath_unfold >>
     qexists_tac `λ(p1,p2). okpath r2 p2` >>
     rw [] >>
     PairCases_on `s` >>
     fs [] >>
     rw [] >>
     `(?s. s1 = stopped_at s) ∨ (?s2 l s'. s1 = pcons s2 l s')` by metis_tac [path_cases] >>
     rw [] >>
     fs [])
QED

Theorem first_compose_paths:
 !p1 p2. first (compose_paths p1 p2) = (first p1, first p2)
Proof
 rw [compose_paths_def] >>
 rw [Once unfold_thm]
QED

Theorem labels_compose_paths:
 !p1 p2.
  labels p1 = labels p2
  ⇒
  labels (compose_paths p1 p2) = labels p1
Proof
 rw [] >>
 rw [Once LLIST_BISIMULATION] >>
 qexists_tac `\l1 l2. ?p1 p2. labels p1 = labels p2 ∧ l1 = labels (compose_paths p1 p2) ∧ l2 = labels p2` >>
 rw []
 >- metis_tac [] >>
 `(?x. p1' = stopped_at x) ∨ (?s l p3. p1' = pcons s l p3)` by metis_tac [path_cases] >>
 `(?x. p2' = stopped_at x) ∨ (?s l p4. p2' = pcons s l p4)` by metis_tac [path_cases] >>
 rw [] >>
 fs [] >>
 metis_tac []
QED

Theorem last_compose_paths:
 !p1.
  finite p1
  ⇒
  !p2.
  labels p2 = labels p1
  ⇒
  last (compose_paths p1 p2) = (last p1, last p2)
Proof
 ho_match_mp_tac finite_path_ind >>
 rw [] >>
 `(?s. p2 = stopped_at s) ∨ (?s1 l p'. p2 = pcons s1 l p')` by metis_tac [path_cases] >>
 rw [] >>
 fs [] >>
 rw [compose_paths_def] >>
 rw [Once unfold_thm] >>
 res_tac >>
 fs [compose_paths_def]
QED

val llength_labels_lem = Q.prove (
`!p n. LLENGTH (labels p) = SOME n ⇔ length p = SOME (SUC n)`,
 Induct_on `n` >>
 rw [] >>
 `(?s. p = stopped_at s) ∨ (?s1 l p'. p = pcons s1 l p')` by metis_tac [path_cases] >>
 fs [DECIDE ``!x. x + 1 = SUC x``] >>
 rw [alt_length_thm, length_never_zero]);

Theorem llength_labels:
 !p. OPTION_MAP SUC (LLENGTH (labels p)) = length p
Proof
 rw [] >>
 Cases_on `finite p` >>
 fs [finite_length] >>
 CCONTR_TAC >>
 fs []
 >- (Cases_on `n` >>
     fs [length_never_zero] >>
     metis_tac [llength_labels_lem, NOT_SOME_NONE, option_CASES]) >>
 metis_tac [llength_labels_lem, NOT_SOME_NONE, option_CASES]
QED

Theorem labels_eq_length:
 !p1 p2. labels p1 = labels p2 ⇒ length p1 = length p2
Proof
 metis_tac [llength_labels]
QED

val length_compose_paths_lem = Q.prove (
`!p1 p2 n.
  labels p1 = labels p2 ⇒
  (length (compose_paths p1 p2) = SOME n ⇔ length p1 = SOME n)`,
 Induct_on `n` >>
 rw [] >>
 `(?s. p1 = stopped_at s) ∨ (?s1 l p'. p1 = pcons s1 l p')` by metis_tac [path_cases] >>
 `(?s. p2 = stopped_at s) ∨ (?s1 l p'. p2 = pcons s1 l p')` by metis_tac [path_cases] >>
 fs [] >>
 rw [alt_length_thm, length_never_zero]);

Theorem length_compose_paths:
 !p1 p2.
  labels p1 = labels p2
  ⇒
  length (compose_paths p1 p2) = length p1
Proof
 rw [] >>
 Cases_on `finite p` >>
 fs [finite_length] >>
 CCONTR_TAC >>
 fs []
 >- (Cases_on `n` >>
     fs [length_never_zero] >>
     metis_tac [length_compose_paths_lem, NOT_SOME_NONE, option_CASES]) >>
 metis_tac [length_compose_paths_lem, NOT_SOME_NONE, option_CASES]
QED

Theorem length_pconcat:
 !p1 l p2.
  length (pconcat p1 l p2) =
    OPTION_JOIN (OPTION_MAP (\l1. OPTION_MAP ((+) l1) (length p2)) (length p1))
Proof
 rw [] >>
 Cases_on `finite p1` >>
 Cases_on `finite p2` >>
 rw [length_def, pconcat_def, path_rep_bijections_thm, toList_THM] >>
 fs [finite_def] >>
 rw [toList_lappend, toList_THM, path_rep_bijections_thm] >>
 simp [] >>
 imp_res_tac LFINITE_toList >>
 rw [] >>
 simp [LFINITE_APPEND]
QED

local val rw = srw_tac[] val fs = fsrw_tac[] in
Theorem PL_pconcat:
 !p1 l p2. PL (pconcat p1 l p2) = 0 INSERT { x + y + 1 | x ∈ PL p1 ∧ y ∈ PL p2 }
Proof
 rw [PL_def, EXTENSION] >>
 eq_tac >>
 rw [] >>
 fs [finite_length, length_pconcat] >>
 fs [] >>
 simp [] >>
 Cases_on `length p1` >>
 Cases_on `length p2` >>
 fs [] >>
 rw [METIS_PROVE [] ``x ∨ y ⇔ (~x ⇒ y)``]
 >- intLib.ARITH_TAC
 >- (qexists_tac `x - 1` >>
     qexists_tac `0` >>
     simp [] >>
     metis_tac [length_never_zero, DECIDE ``!x. x ≠ 0 ⇒ 0 < x:num``])
 >- (qexists_tac `0` >>
     qexists_tac `x - 1` >>
     simp [] >>
     metis_tac [length_never_zero, DECIDE ``!x. x ≠ 0 ⇒ 0 < x:num``])
 >- (`x' ≠ 0 ∧ x'' ≠ 0` by metis_tac [length_never_zero] >>
     intLib.ARITH_TAC)
 >- (`x ≠ 0 ∧ x' ≠ 0` by metis_tac [length_never_zero] >>
     intLib.ARITH_TAC)
 >- (`x ≠ 0 ∧ x'' ≠ 0` by metis_tac [length_never_zero] >>
     intLib.ARITH_TAC)
QED
end

Theorem complete_path:
 !r p1.
  okpath r p1 ∧ ~complete r p1
  ⇒
  ?l p2. okpath r (pconcat p1 l p2) ∧ complete r (pconcat p1 l p2)
Proof
 rw [complete_def] >>
 qexists_tac `l` >>
 qexists_tac `unfold (\s. s) (\s. some (s',l). r s l s') s` >>
 rw []
 >- (match_mp_tac okpath_unfold >>
     qexists_tac `\x.T` >>
     rw [] >>
     `(\x. x = SOME (s'',l')) ($some (\(x,y). r s' y x))` by rw [] >>
     imp_res_tac some_elim >>
     fs [])
 >- (rw [Once unfold_thm] >>
     ect >>
     rw [])
 >- (fs [finite_pconcat] >>
     pop_assum mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw [finite_length] >>
     pop_assum mp_tac >>
     Q.SPEC_TAC (`s`, `s`) >>
     Induct_on `n` >>
     rw [] >>
     fs [length_never_zero] >>
     pop_assum mp_tac >>
     ONCE_REWRITE_TAC [unfold_thm] >>
     rw [] >>
     Cases_on `some(s',l). r s l s'` >>
     fs []
     >- (`(\x. x = NONE) ($some (\(x,y). r s y x))` by rw [] >>
         imp_res_tac some_elim >>
         fs [LAMBDA_PROD, FORALL_PROD])
     >- (`(\y. y = SOME x) ($some (\(x,y). r s y x))` by rw [] >>
         imp_res_tac some_elim >>
         fs [LAMBDA_PROD, FORALL_PROD] >>
         PairCases_on `x` >>
         fs [] >>
         rw [] >>
         first_x_assum match_mp_tac >>
         fs [length_thm, arithmeticTheory.ADD1, finite_length] >>
         rfs []))
QED

Theorem determ_path_unique:
 !r p1 p2.
  (!s l1 s1 l2 s2. r s l1 s1 ∧ r s l2 s2 ⇒ l1 = l2 ∧ s1 = s2) ∧
  first p1 = first p2 ∧ complete r p1 ∧ complete r p2 ∧ okpath r p1 ∧ okpath r p2
  ⇒
  p1 = p2
Proof
 rw [] >>
 rw [Once path_bisimulation] >>
 qexists_tac `\p1 p2. first p1 = first p2 ∧ complete r p1 ∧ complete r p2 ∧ okpath r p1 ∧ okpath r p2` >>
 rw [] >>
 `(?x. q1 = stopped_at x) ∨ ?x l p1'. q1 = pcons x l p1'` by metis_tac [path_cases] >>
 `(?x. q2 = stopped_at x) ∨ ?x l p1'. q2 = pcons x l p1'` by metis_tac [path_cases] >>
 rw [] >>
 fs [complete_def] >>
 rw [] >>
 metis_tac []
QED

Theorem el_pconcat:
 !n p1 l p2.
  n ∈ PL p1
  ⇒
  el n (pconcat p1 l p2) = el n p1
Proof
 Induct_on `n` >>
 rw [] >>
 `(?x. p1 = stopped_at x) ∨ ?x l p1'. p1 = pcons x l p1'` by metis_tac [path_cases] >>
 rw [pconcat_thm] >>
 fs []
QED

Theorem nth_label_pconcat:
 !n p1 l p2.
  SUC n ∈ PL p1
  ⇒
  nth_label n (pconcat p1 l p2) = nth_label n p1
Proof
 Induct_on `n` >>
 rw [] >>
 `(?x. p1 = stopped_at x) ∨ ?x l p1'. p1 = pcons x l p1'` by metis_tac [path_cases] >>
 rw [pconcat_thm] >>
 fs []
QED
 (*

val lrep_ok_thm = Q.store_thm ("lrep_ok_thm",
`lrep_ok f ⇔ !n. f n = NONE ⇒ f (SUC n) = NONE`,
 rw [lrep_ok_def] >>
 eq_tac >>
 rw []
 >- (rpt (pop_assum mp_tac) >>
     Q.SPEC_TAC (`f`, `f`) >>
     Induct_on `n` >>
     rw [] >>
     res_tac >>
     rw [] >>
     fs [])
 >- (qexists_tac `(\f. !n. f n = NONE ⇒ f (SUC n) = NONE)` >>
     rw [] >>
     rw [METIS_PROVE [] ``x ∨ y ⇔ (~x ⇒ y)``] >>
     qexists_tac `THE (g (0:num))` >>
     qexists_tac `(\n. g (n + 1))` >>
     rw []
     >- (res_tac >>
         Cases_on `n = 0` >>
         full_simp_tac (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1]) >>
     rw [FUN_EQ_THM] >>
     Cases_on `n = 0` >>
     fs []
     >- (Cases_on `g 0` >>
         fs [FUN_EQ_THM] >>
         Induct_on `n'` >>
         fs []) >>
     simp []));

val lnth_abs = Q.store_thm ("lnth_abs",
`!n f. lrep_ok f ⇒ LNTH n (llist_abs f) = f n`,
 Induct_on `n` >>
 rw [LNTH, LHD, LTL]
 >- fs [llist_absrep] >>
 ect >>
 rw []
 >- (`f 0 = NONE` by metis_tac [llist_absrep] >>
     pop_assum mp_tac >>
     pop_assum kall_tac >>
     pop_assum mp_tac >>
     pop_assum kall_tac >>
     Induct_on `n` >>
     fs [lrep_ok_thm] >>
     metis_tac [DECIDE ``SUC 0 = 1``, lrep_ok_thm]) >>
 `llist_rep (llist_abs f) = f` by metis_tac [llist_absrep] >>
 fs [] >>
 `lrep_ok (λn'. f (n' + 1))`
          by (fs [lrep_ok_thm] >>
              rw [] >>
              res_tac >>
              fs [arithmeticTheory.ADD1]) >>
 first_x_assum (qspec_then `(λn'. f (n' + 1))` mp_tac) >>
 rw [arithmeticTheory.ADD1]);

 *)
 (*
val _ = augment_srw_ss [rewrites
  [toList_THM, finite_labels, labels_plink, LFINITE_APPEND, finite_pconcat,
   LFINITE_MAP, LAPPEND_NIL_2ND]];

   *)
