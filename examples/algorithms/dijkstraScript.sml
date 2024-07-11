(*
  Dijkstra's algorithm for computing shortest paths
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory pred_setTheory listTheory;
open finite_mapTheory optionTheory pairTheory;

val _ = new_theory "dijkstra";

(* --- definition of algorithm --- *)

Datatype:
  res_info = <| prev_node : num;
                dist_from_root : num |>
End

Definition min_elem_def:
  min_elem (n:num) v queue ⇔
    FLOOKUP queue n = SOME v ∧
    ∀m w. FLOOKUP queue m = SOME w ⇒ v.dist_from_root ≤ w.dist_from_root
End

Definition update_def:
  update [] n d k q = q ∧
  update ((i,len)::es) n d k q =
    case FLOOKUP k i of
    | SOME _ => update es n d k q
    | NONE =>
        case FLOOKUP q i of
        | NONE =>
            update es n d k (q |+ (i,<| prev_node := n ;
                                        dist_from_root := d + len |>))
        | SOME j =>
            if j.dist_from_root ≤ d + len then
              update es n d k q
            else
              update es n d k (q |+ (i,<| prev_node := n ;
                                          dist_from_root := d + len |>))
End

Inductive calc:
[~empty:]
  calc known FEMPTY edges known
[~step:]
  min_elem n v queue ∧
  FLOOKUP edges n = SOME neighbours ∧
  new_known = known |+ (n,v) ∧
  new_queue = update neighbours n v.dist_from_root new_known (queue \\ n) ∧
  calc new_known new_queue edges result ⇒
  calc known queue edges result
End

Definition root_node_def:
  root_node r = <| prev_node := r; dist_from_root := 0 |>
End

Definition dijkstra_def:
  dijkstra root edges result ⇔
    calc FEMPTY (FEMPTY |+ (root, root_node root)) edges result
End

(* --- definitions used in main correctness theorem --- *)

Inductive has_edge:
  FLOOKUP edges n1 = SOME neighbours ∧ MEM (n2,len) neighbours ⇒
  has_edge edges n1 len n2
End

Inductive has_path:
[~end:]
  has_path edges n 0 n
[~step:]
  has_path edges n1 len1 n2 ∧
  has_edge edges n2 len2 n3 ⇒
  has_path edges n1 (len1 + len2) n3
End

Definition correct_result_def:
  correct_result edges root known ⇔
    (∀n v.
       FLOOKUP known n = SOME v ⇒
       has_path edges root v.dist_from_root n ∧
       (∀l. l < v.dist_from_root ⇒ ~ has_path edges root l n) ∧
       (n = root ⇒ v.prev_node = root) ∧
       (n ≠ root ⇒ ∃w l.
                     FLOOKUP known v.prev_node = SOME w ∧
                     has_edge edges v.prev_node l n ∧
                     v.dist_from_root = l + w.dist_from_root))
End

Definition complete_result_def:
  complete_result edges root known ⇔
    (∀n len. has_path edges root len n ⇒ n ∈ FDOM known)
End

(* --- verification --- *)

Triviality FDOM_update:
  ∀xs root n q.
    FDOM (update xs root n k q) =
    FDOM q ∪ (set (MAP FST xs) DIFF FDOM k)
Proof
  Induct \\ gvs [update_def]
  \\ Cases \\ gvs [update_def]
  \\ rw [] \\ BasicProvers.every_case_tac \\ gvs []
  \\ gvs [EXTENSION]
  \\ gvs [TO_FLOOKUP]
  \\ metis_tac [NOT_NONE_SOME]
QED

Theorem has_path_exists_known:
  ∀edges root l n.
    has_path edges root l n ∧
    root ∈ FDOM known ∧ n ∉ FDOM (known: num |-> res_info)
    ⇒
    ∃m1 m2 l1 l2 l3.
      has_path edges root l1 m1 ∧ m1 ∈ FDOM known ∧
      has_edge edges m1 l2 m2 ∧ m2 ∉ FDOM known ∧
      l1 + l2 ≤ l
Proof
  rewrite_tac [GSYM AND_IMP_INTRO] \\ gen_tac
  \\ ho_match_mp_tac (has_path_strongind |> Q.SPEC ‘edges’)
  \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘n ∉ FDOM known’ \\ gvs []
  >-
   (qpat_x_assum ‘has_edge edges m1 l2 m2’ $ irule_at Any \\ gvs []
    \\ qpat_x_assum ‘has_path edges root l1 m1’ $ irule_at Any \\ gvs []
    \\ metis_tac [has_path_rules, ADD_COMM])
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ gvs []
QED

Theorem FLOOKUP_update_neq:
  ∀i ns n d k q j v.
    i ≠ j ⇒
    FLOOKUP (update ns n d k (q |+ (j,v))) i =
    FLOOKUP (update ns n d k q) i
Proof
  gen_tac \\ Induct \\ gvs [update_def,FLOOKUP_SIMP]
  \\ PairCases \\ gvs [update_def] \\ rpt strip_tac
  \\ Cases_on ‘FLOOKUP k h0’ \\ gvs [FLOOKUP_SIMP]
  \\ Cases_on ‘j = h0’ \\ gvs []
  >- (BasicProvers.EVERY_CASE_TAC \\ gvs [])
  \\ Cases_on ‘FLOOKUP q h0’ \\ gvs []
  >- (dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC [FUPDATE_COMMUTES] \\ gvs [])
  \\ dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC [FUPDATE_COMMUTES] \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem FLOOKUP_update_cons_neq:
  ∀i ns n d k q j v m.
    i ≠ j ⇒
    FLOOKUP (update ((j,m)::ns) n d k q) i =
    FLOOKUP (update ns n d k q) i
Proof
  gvs [update_def] \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ gvs [FLOOKUP_update_neq]
QED

Triviality pull_if:
  (f (if b then x else y) = if b then f x else f y) ∧
  ((if b then g1 else g2) z = if b then g1 z else g2 z)
Proof
  Cases_on ‘b’ \\ gvs []
QED

Theorem FLOOKUP_update_pass:
  ∀i k ns h n d h1 q.
    (∀l. MEM (i,l) ns ⇒ h ≤ l) ⇒
    FLOOKUP
      (update ns n d k
            (q |+ (i,<|prev_node := n; dist_from_root := d + h|>))) i =
    SOME <|prev_node := n; dist_from_root := d + h|>
Proof
  gen_tac \\ gen_tac \\ Induct \\ gvs [update_def,FLOOKUP_SIMP]
  \\ PairCases \\ gvs [] \\ rename [‘(m1,w)::_’]
  \\ Cases_on ‘m1 ≠ i’ >- (gvs [FLOOKUP_update_cons_neq,SF SFY_ss])
  \\ simp [update_def]
  \\ rpt gen_tac \\ gvs [FLOOKUP_SIMP]
  \\ strip_tac \\ gvs [SF DNF_ss]
  \\ Cases_on ‘FLOOKUP k i’ \\ gvs [SF SFY_ss]
QED

Theorem FLOOKUP_update_skip:
  ∀i k ns h n d h1 q l.
    FLOOKUP k i = NONE ∧ MEM (i,l) ns ∧ l < h ∧
    (∀x. FLOOKUP q i = SOME x ⇒ d + h < x.dist_from_root) ⇒
    FLOOKUP
      (update ns n d k
            (q |+ (i,<|prev_node := n; dist_from_root := d + h|>))) i =
    FLOOKUP (update ns n d k q) i
Proof
  gen_tac \\ gen_tac \\ Induct \\ gvs [update_def,FLOOKUP_SIMP]
  \\ PairCases \\ gvs [] \\ rename [‘(m1,w)::_’]
  \\ rpt strip_tac \\ gvs []
  \\ simp [update_def]
  >- (gvs [FLOOKUP_SIMP] \\ Cases_on ‘FLOOKUP q i’ \\ gvs [])
  \\ reverse $ Cases_on ‘FLOOKUP k m1’ >- gvs [SF SFY_ss] \\ gvs []
  \\ gvs [FLOOKUP_SIMP] \\ reverse IF_CASES_TAC \\ gvs []
  >-
   (dep_rewrite.DEP_ONCE_REWRITE_TAC [FUPDATE_COMMUTES] \\ simp []
    \\ Cases_on ‘FLOOKUP q m1’ \\ gvs []
    >- (first_x_assum irule \\ gvs [FLOOKUP_SIMP] \\ metis_tac [])
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum irule \\ gvs [FLOOKUP_SIMP] \\ metis_tac [])
  \\ CONV_TAC (PATH_CONV "lr" (SCONV [pull_if])) \\ simp [SF SFY_ss]
  \\ Cases_on ‘FLOOKUP q i’ \\ gvs []
  >- (rw [] \\ gvs [] \\ last_x_assum (irule o GSYM)
      \\ gvs [] \\ first_x_assum $ irule_at Any \\ gvs [])
  \\ rw []
  >- (last_x_assum (irule o GSYM)
      \\ gvs [] \\ first_x_assum $ irule_at Any \\ gvs [])
  \\ first_x_assum irule \\ gvs []
QED

Theorem FLOOKUP_update_MEM:
  ∀i k ns h n d h1 q.
    FLOOKUP k i = NONE ∧
    (∀x. FLOOKUP q i = SOME x ⇒ d + h < x.dist_from_root) ⇒
    FLOOKUP
      (update ns n d k
            (q |+ (i,<|prev_node := n; dist_from_root := d + h|>))) i =
    if ∃l. MEM (i,l) ns ∧ l < h then
      FLOOKUP (update ns n d k q) i
    else
      SOME <|prev_node := n; dist_from_root := d + h|>
Proof
  rw []
  >- (irule FLOOKUP_update_skip \\ gvs [] \\ metis_tac [])
  \\ irule FLOOKUP_update_pass \\ gvs [] \\ metis_tac [NOT_LESS]
QED

Theorem update_thm:
  ∀i ns n d k q v.
    FLOOKUP (update ns n d k q) i = SOME v ∧ i ∉ FDOM k
    ⇒
    (* the original value in q survived *)
    (FLOOKUP q i = SOME v ∧
     (* all matching pairs in ns must have been ignored *)
     ∀len. MEM (i,len) ns ∧ FLOOKUP k i = NONE ⇒ v.dist_from_root ≤ d + len)
    ∨
    (* mem in ns has been picked *)
    ∃len. MEM (i,len) ns ∧
          v.dist_from_root = d + len ∧
          v.prev_node = n ∧
          (∀len2. MEM (i,len2) ns ⇒ len ≤ len2) ∧
          (* any mapping in q must have been larger *)
          ∀w. FLOOKUP q i = SOME w ⇒ d + len ≤ w.dist_from_root
Proof
  gen_tac \\ Induct \\ gvs [update_def] \\ PairCases
  \\ Cases_on ‘i ≠ h0’ >- gvs [FLOOKUP_update_cons_neq]
  \\ rpt gen_tac
  \\ simp [update_def,TO_FLOOKUP]
  \\ reverse $ Cases_on ‘FLOOKUP k h0’ >- gvs [] \\ gvs []
  \\ Cases_on ‘FLOOKUP q h0’ \\ gvs []
  >-
   (simp [FLOOKUP_update_MEM]
    \\ IF_CASES_TAC \\ gvs [TO_FLOOKUP]
    >-
     (strip_tac \\ last_x_assum drule \\ gvs []
      \\ strip_tac
      \\ gvs [SF DNF_ss, SF SFY_ss]
      \\ res_tac
      \\ Cases_on ‘len ≤ h1’ \\ gvs []
      \\ res_tac \\ fs [])
    \\ gvs [] \\ rw [] \\ gvs [NOT_LESS]
    \\ rw [] \\ gvs []
    \\ metis_tac [])
  \\ IF_CASES_TAC
  >-
   (strip_tac \\ last_x_assum drule \\ gvs [TO_FLOOKUP]
    \\ strip_tac \\ gvs [] \\ gvs [SF DNF_ss, SF SFY_ss])
  \\ gvs [NOT_LESS]
  \\ strip_tac
  \\ pop_assum (fn th => mp_tac th \\ assume_tac th)
  \\ last_assum dxrule
  \\ simp [FLOOKUP_update_MEM]
  \\ strip_tac
  \\ gvs [TO_FLOOKUP,FLOOKUP_SIMP]
  \\ IF_CASES_TAC \\ gvs [TO_FLOOKUP,NOT_LESS]
  \\ gvs [SF DNF_ss, SF SFY_ss]
  \\ metis_tac []
QED

Theorem FLOOKUP_update_k[simp,local]:
  ∀ns q. i ∈ FDOM k ⇒ FLOOKUP (update ns n d k q) i = FLOOKUP q i
Proof
  Induct \\ gvs [update_def] \\ PairCases \\ gvs [update_def]
  \\ Cases_on ‘FLOOKUP k h0’ \\ gvs [] \\ rw [] \\ gvs []
  \\ Cases_on ‘h0 = i’ \\ gvs [TO_FLOOKUP]
  \\ Cases_on ‘FLOOKUP q h0’ \\ gvs [FLOOKUP_SIMP]
  \\ rw [] \\ gvs [FLOOKUP_SIMP]
QED

Theorem update_not_eq:
  ∀ns n d k q i v.
    FLOOKUP (update ns n d k q) i = SOME v ∧
    v.prev_node ≠ n ⇒
    FLOOKUP q i = SOME v ∧
    ∀len1.
      MEM (i,len1) ns ∧ i ∉ FDOM k ⇒
      v.dist_from_root ≤ len1 + d
Proof
  rpt gen_tac \\ strip_tac
  \\ reverse $ Cases_on ‘i ∈ FDOM k’ \\ gvs []
  \\ drule_all update_thm \\ gvs [] \\ gvs [TO_FLOOKUP]
QED

Theorem update_eq:
  ∀ns d k q i v.
    FLOOKUP (update ns v.prev_node d k q) i = SOME v ∧
    (∀w. FLOOKUP q i = SOME w ⇒ w ≠ v) ⇒
    ∃len.
      i ∉ FDOM k ∧
      MEM (i,len) ns ∧ v.dist_from_root = len + d ∧
      (∀len1. MEM (i,len1) ns ⇒ len ≤ len1) ∧
      (∀x. FLOOKUP q i = SOME x ⇒
           d + len ≤ x.dist_from_root)
Proof
  rpt strip_tac
  \\ reverse $ Cases_on ‘i ∈ FDOM k’ \\ gvs []
  \\ drule_all update_thm
  \\ metis_tac []
QED

Theorem dijkstra_thm:
  ∀root known queue edges res.
    calc known queue edges res ⇒
    FLOOKUP known root = SOME (root_node root) ⇒
    DISJOINT (FDOM known) (FDOM queue) ∧
    (* content in known is shortest *)
    correct_result edges root known ∧
    (* all neighbours of known are in known or queue *)
    (∀n len i.
       n ∈ FDOM known ∧ has_edge edges n len i ⇒
       i ∈ FDOM known ∨ i ∈ FDOM queue) ∧
    (* each queue points at shortest node in known *)
    (∀n v.
       FLOOKUP queue n = SOME v ⇒
       ∃x len.
         FLOOKUP known v.prev_node = SOME x ∧
         has_edge edges v.prev_node len n ∧
         v.dist_from_root = x.dist_from_root + len ∧
         ∀other y len1.
           FLOOKUP known other = SOME y ∧
           has_edge edges other len1 n ⇒
           v.dist_from_root ≤ y.dist_from_root + len1) ⇒
    correct_result edges root res ∧
    complete_result edges root res
Proof
  gen_tac \\ Induct_on ‘calc’ \\ conj_tac
  \\ rpt gen_tac \\ rpt disch_tac
  >-
   (gvs [complete_result_def] \\ pop_assum mp_tac
    \\ last_x_assum mp_tac
    \\ pop_assum kall_tac
    \\ Induct_on ‘has_path’
    \\ conj_tac >- gvs [TO_FLOOKUP]
    \\ rpt strip_tac
    \\ metis_tac [])
  \\ gvs []
  \\ first_x_assum irule
  \\ simp [FDOM_update]
  \\ ‘n ≠ root’ by
    (strip_tac \\ gvs [min_elem_def,IN_DISJOINT,TO_FLOOKUP]
     \\ metis_tac [NOT_SOME_NONE])
  \\ rpt conj_tac
  >- (gen_tac \\ rename [‘n1 = n2 ∨ _’]
      \\ reverse (Cases_on ‘n1 = n2’) \\ gvs [] >- metis_tac []
      \\ simp [Once has_edge_cases,MEM_MAP,EXISTS_PROD] \\ metis_tac [])
  \\ rename [‘min_elem n v queue’]
  >- (rpt strip_tac \\ rename [‘_ k = SOME w’]
      \\ reverse $ Cases_on ‘w.prev_node = n’
      >- (gvs [FLOOKUP_SIMP,TO_FLOOKUP,AllCaseEqs(),DOMSUB_FLOOKUP_THM]
          \\ gvs [correct_result_def]
          \\ drule_all update_not_eq \\ strip_tac
          \\ gvs [DOMSUB_FLOOKUP_THM]
          \\ first_assum drule \\ strip_tac \\ gvs [SF DNF_ss, SF SFY_ss]
          \\ simp [Once has_edge_cases]
          \\ ‘k ∉ FDOM known’ by
            (gvs [TO_FLOOKUP,IN_DISJOINT] \\ metis_tac [NOT_SOME_NONE])
          \\ gvs [])
      \\ gvs [] \\ simp [FLOOKUP_SIMP,AllCaseEqs(),SF DNF_ss]
      \\ simp [Once has_edge_cases]
      \\ simp [Once has_edge_cases]
      \\ drule update_eq
      \\ impl_tac
      >- (gvs [DOMSUB_FLOOKUP_THM]
          \\ rw [] \\ CCONTR_TAC \\ gvs [] \\ res_tac
          \\ gvs [min_elem_def,IN_DISJOINT,TO_FLOOKUP]
          \\ metis_tac [NOT_NONE_SOME])
      \\ strip_tac \\ gvs []
      \\ rpt strip_tac
      \\ gvs [DOMSUB_FLOOKUP_THM]
      \\ ‘k ∈ FDOM queue’ by metis_tac [TO_FLOOKUP,NOT_NONE_SOME]
      \\ gvs [TO_FLOOKUP]
      \\ Cases_on ‘FLOOKUP queue k’ \\ gvs []
      \\ qpat_x_assum ‘∀n' v'. FLOOKUP queue n' = SOME v' ⇒ _’ drule
      \\ strip_tac
      \\ qpat_x_assum ‘FLOOKUP known other = SOME y’ assume_tac
      \\ first_x_assum drule
      \\ disch_then drule \\ strip_tac
      \\ irule LESS_EQ_TRANS
      \\ pop_assum $ irule_at $ Pos last
      \\ gvs [min_elem_def])
  >- gvs [FLOOKUP_SIMP]
  >- (gvs [IN_DISJOINT] \\ metis_tac [])
  >- (gvs [IN_DISJOINT] \\ metis_tac [])
  \\ gvs [correct_result_def,FLOOKUP_SIMP,AllCaseEqs()]
  \\ reverse (rpt gen_tac \\ disch_tac \\ gvs [])
  >- (first_x_assum drule \\ strip_tac \\ gvs []
      \\ strip_tac \\ gvs []
      \\ irule_at (Pos last) EQ_REFL \\ gvs []
      \\ CCONTR_TAC
      \\ gvs [min_elem_def,IN_DISJOINT,TO_FLOOKUP]
      \\ metis_tac [NOT_SOME_NONE])
  \\ gvs [min_elem_def]
  \\ last_x_assum assume_tac
  \\ rename [‘FLOOKUP queue n = SOME v’]
  \\ first_assum drule \\ strip_tac
  \\ qpat_assum ‘∀n v. FLOOKUP known n = SOME v ⇒ _’ drule \\ strip_tac
  \\ conj_tac
  >- (simp [Once has_path_cases] \\ metis_tac [ADD_COMM])
  \\ reverse conj_tac
  >- (gvs [] \\ irule_at (Pos last) EQ_REFL \\ gvs []
      \\ CCONTR_TAC
      \\ gvs [min_elem_def,IN_DISJOINT,TO_FLOOKUP]
      \\ metis_tac [NOT_SOME_NONE])
  \\ CCONTR_TAC \\ gvs []
  \\ drule has_path_exists_known
  \\ disch_then $ qspec_then ‘known’ mp_tac
  \\ impl_tac
  >- (gvs [TO_FLOOKUP,IN_DISJOINT] \\ metis_tac [NOT_NONE_SOME])
  \\ strip_tac \\ gvs []
  \\ qsuff_tac ‘len + x.dist_from_root ≤ l1 + l2’ >- gvs []
  \\ pop_assum kall_tac
  \\ CCONTR_TAC \\ fs [GSYM NOT_LESS]
  \\ ‘m2 ∈ FDOM queue’ by metis_tac []
  \\ gvs [TO_FLOOKUP]
  \\ Cases_on ‘FLOOKUP known m1’ \\ gvs [] \\ rename [‘_ = SOME m1_info’]
  \\ Cases_on ‘FLOOKUP queue m2’ \\ gvs [] \\ rename [‘_ = SOME m2_info’]
  \\ ‘m1_info.dist_from_root ≤ l1’ by
    (qpat_x_assum ‘FLOOKUP known m1 = SOME x1’ assume_tac
     \\ qpat_assum ‘∀n v. FLOOKUP known n = SOME v ⇒ _’ drule \\ strip_tac
     \\ metis_tac [NOT_LESS])
  \\ qpat_assum ‘∀n v. FLOOKUP queue n = SOME v ⇒ _’ drule \\ strip_tac
  \\ qpat_x_assum ‘has_edge edges m1 l2 m2’ assume_tac
  \\ first_x_assum $ drule_at $ Pos last \\ strip_tac
  \\ gvs [NOT_LESS] \\ last_x_assum drule \\ gvs []
QED

(* --- main correctness theorem --- *)

Theorem dijkstra_imp_correct_result:
  dijkstra root edges result
  ⇒
  correct_result edges root result ∧
  complete_result edges root result
Proof
  simp [dijkstra_def]
  \\ simp [Once calc_cases]
  \\ simp [min_elem_def,FLOOKUP_SIMP]
  \\ gvs [EVAL “(root_node root).dist_from_root”]
  \\ strip_tac
  \\ drule dijkstra_thm
  \\ simp [FLOOKUP_SIMP]
  \\ disch_then irule
  \\ rpt conj_tac
  >-
   (simp [has_edge_cases] \\ rw []
    \\ gvs [FDOM_update,MEM_MAP,EXISTS_PROD]
    \\ metis_tac [])
  >-
   (gvs [root_node_def]
    \\ simp [has_edge_cases] \\ rpt gen_tac \\ strip_tac
    \\ Cases_on ‘n = root’ >-  gvs [FLOOKUP_DEF,FDOM_update]
    \\ drule update_thm \\ gvs [])
  \\ simp [FDOM_update]
  \\ gvs [correct_result_def,FLOOKUP_SIMP,root_node_def]
  \\ irule_at Any has_path_end
QED

val _ = export_theory();
