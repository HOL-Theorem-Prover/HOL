open bossLib Theory Parse boolTheory pairTheory Defn Tactic boolLib
open lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;


val _ = new_theory "SplayHeap"

val _ = Hol_datatype `
heaps = Empty | Node of heaps => 'a => heaps`;

val _ = Define `
empty = Empty`;

val _ = Define `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val partition_def = Define `
(partition element_leq pivot Empty = (Empty, Empty)) ∧
(partition element_leq pivot (Node a x b) =
  if element_leq x pivot then
    (case b of
        Empty => (Node a x b, Empty)
      | Node b1 y b2 =>
          if element_leq y pivot then
            let (small, big) = partition element_leq pivot b2 in
              (Node (Node a x b1) y small, big)
          else
            let (small, big) = partition element_leq pivot b1 in
              (Node a x small, Node big y b2))
  else
    (case a of
        Empty => (Empty, Node a x b)
      | Node a1 y a2 =>
          if element_leq y pivot then
            let (small, big) = partition element_leq pivot a2 in
              (Node a1 y small, Node big x b)
          else
            let (small, big) = partition element_leq pivot a1 in
              (small, Node big y (Node a2 x b))))`;

val partition_ind = fetch "-" "partition_ind" 
val heaps_size_def = fetch "-" "heaps_size_def" 

val partition_smaller = Q.prove (
`!element_leq p h1 h2 h3.
  ((h2,h3) = partition element_leq p h1)
  ⇒
  heaps_size f h2 ≤ heaps_size f h1 ∧
  heaps_size f h3 ≤ heaps_size f h1`,
recInduct partition_ind >>
rw [heaps_size_def, partition_def] >>
full_case_tac >>
fs [] >>
rw [heaps_size_def] >>
full_case_tac >>
fs [] >>
rw [heaps_size_def] >|
[cases_on `partition element_leq pivot h0`,
 cases_on `partition element_leq pivot h`,
 cases_on `partition element_leq pivot h0`,
 cases_on `partition element_leq pivot h`,
 cases_on `partition element_leq pivot h0`,
 cases_on `partition element_leq pivot h`,
 cases_on `partition element_leq pivot h0`,
 cases_on `partition element_leq pivot h`] >>
fs [LET_THM] >>
rw [heaps_size_def] >>
decide_tac);

val _ = Define `
(insert element_leq x t = 
  let (a, b) = partition element_leq x t in 
    Node a x b)`;

val merge_def = tDefine "merge" `
(merge element_leq Empty h2 = h2) ∧
(merge element_leq (Node a x b) h2 =
  let (ta, tb) = partition element_leq x h2 in
    Node (merge element_leq ta a) x (merge element_leq tb b))`
(WF_REL_TAC `measure (\(x,y,z). 
                        heaps_size (\_.1) y + 
                        heaps_size (\_.1) z)` >>
 rw [] >>
 imp_res_tac partition_smaller >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [partition_smaller]); 

val find_min_defn = Define `
(find_min (Node Empty x b) = x) ∧
(find_min (Node a x b) = find_min a)`;

val delete_min_defn = Hol_defn "delete_min" `
(delete_min (Node Empty x b) = b) ∧
(delete_min (Node (Node Empty x b) y c) = Node b y c) ∧
(delete_min (Node (Node a x b) y c) = Node (delete_min a) x (Node b y c))`;

val _ = export_theory()

