open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory;
open probabilityTheory measureTheory sortingTheory;

val _ = new_theory "graph";

(*  set_grammar_ancestry ["probability","measure"]  *)

Theorem dist_joint_dist_eq:
  joint_distribution p X Y = distribution p (λx. (X x,Y x) )
Proof
  fs[joint_distribution_def,distribution_def]
QED

(*
val _ = type_abbrev ("graph",``:(α list) # (α->α->bool)``);
*)



val _ = type_abbrev ("graph",``:(α list) # (num set list)``);

Definition nodes_def:
  nodes ((n,pa):α graph) = n
End

Definition parents_def:
  parents ((n,pa):α graph) k = QSORT (<) (SET_TO_LIST (EL k pa))
End

(*
Definition edges_def:
  edges ((n,e):α graph) = e
End
*)

Definition edges_def:
  edges ((n,pa):α graph) b a = (a < LENGTH pa ∧ b ∈ (EL a pa))
End

(*
Definition path_def:
  path G a b = (∃ls. ls <> [] ∧ (LRC (edges G) ls a b) ∧ (set ls SUBSET set (nodes G)))
End
*)

Definition path_def:
  path G a b = ∃ls. ls <> [] ∧ (LRC (edges G) ls a b) ∧ b < LENGTH (nodes G)
End

(*
Definition parents_def:
  parents G a = FILTER (λb. edges G b a) (nodes G)
End
*)

Definition wf_def:
  wf G = ∀a b. edges G a b ==> MEM a (nodes G) ∧ MEM b (nodes G)
End

Definition acyclic_def:
  acyclic G = ∀x. ¬path G x x
End

Definition joint_distribution_n_def:
  joint_distribution_n p Xs = (λa. prob p (PREIMAGE (λx. MAP (λX. X x) Xs) a ∩ p_space p))
End

Theorem joint_distribution_n_eq_distribution:
  joint_distribution_n p Xs = distribution p (λx. MAP (λX. X x) Xs)
Proof
  fs[joint_distribution_n_def,distribution_def]
QED

Definition conditional_distribution_n_def:
  conditional_distribution_n p Xs Ys As Bs = 
    joint_distribution_n p (Xs ++ Ys) {a++b | a ∈ As ∧ b ∈ Bs} / joint_distribution_n p Ys Bs 
End

Definition REAL_PROD_IMAGE_DEF:
  REAL_PROD_IMAGE f s = ITSET (λe acc. f e * acc) s 1r
End

Definition real_prod_list:
  (real_prod_list f [] = 1r) ∧
  real_prod_list f (h::t) = (f h)*(real_prod_list f t)
End

Definition respects:
  respects p G = 
   ∀As. joint_distribution_n p (nodes G) As = 0 ∨
   joint_distribution_n p (nodes G) As =
   real_prod_list (λX. conditional_distribution_n p [EL X (nodes G)] 
                                                    (MAP (λn. EL n (nodes G)) (parents G X) ) 
                                                    {[EL X a] | a ∈ As} 
                                                    {MAP (λn. EL n a) (parents G X) | a ∈ As} )
                  (COUNT_LIST (LENGTH (nodes G)))
End


Definition conditional_independence_n_def:
  conditional_independence_n p Xs Ys Zs =
  ∀As Bs Cs. conditional_distribution_n p Ys Zs Bs Cs = 0 ∨ 
          conditional_distribution_n p Xs (Ys++Zs) As {b++c| b ∈ Bs ∧ c ∈ Cs} = conditional_distribution_n p Xs Zs As Cs
End


Theorem joint_dist_n_comm:
  ((∀a. a ∈ As ==> LENGTH a = LENGTH Xs) ∨ (∀b. b ∈ Bs ==> LENGTH b = LENGTH Ys)) ==>
  joint_distribution_n p (Xs++Ys) {a++b | a ∈ As ∧ b ∈ Bs} = joint_distribution_n p (Ys++Xs) {b++a | a ∈ As ∧ b ∈ Bs}
Proof
  strip_tac >> fs[joint_distribution_n_eq_distribution,distribution_def] >> 
  `PREIMAGE (λx. MAP (λX. X x) Xs ⧺ MAP (λX. X x) Ys)
        {a ⧺ b | a ∈ As ∧ b ∈ Bs} = PREIMAGE (λx. MAP (λX. X x) Ys ⧺ MAP (λX. X x) Xs)
        {b ⧺ a | a ∈ As ∧ b ∈ Bs}`
  suffices_by metis_tac[] >> fs[PREIMAGE_def,EXTENSION] >> rw[] >> eq_tac >> rw[]
  >- (qexists_tac`b` >> qexists_tac`a` >> simp[] >> 
      `LENGTH (MAP (λX. X x) Xs) = LENGTH a` by fs[LENGTH_MAP] >> 
      `DROP (LENGTH (MAP (λX. X x) Xs)) (MAP (λX. X x) Xs ⧺ MAP (λX. X x) Ys) = DROP (LENGTH a) (a++b)` by fs[] >>
      fs[rich_listTheory.DROP_LENGTH_APPEND] )
  >- (qexists_tac`a` >> qexists_tac`b` >> simp[] >> 
      `LENGTH (MAP (λX. X x) Xs) = LENGTH a` by fs[LENGTH_MAP] >> 
      `TAKE ((LENGTH (MAP (λX. X x) Ys ⧺ MAP (λX. X x) Xs)) - LENGTH (MAP (λX. X x) Xs)) (MAP (λX. X x) Ys ⧺ MAP (λX. X x) Xs) = TAKE (LENGTH (b++a) - LENGTH a) (b++a)` by metis_tac[] >>
      fs[rich_listTheory.TAKE_LENGTH_APPEND] >> 
      `TAKE (LENGTH (MAP (λX. X x) Ys)) (MAP (λX. X x) Ys ⧺ MAP (λX. X x) Xs) = b` by metis_tac[LENGTH_MAP] >>
      fs[rich_listTheory.TAKE_LENGTH_APPEND] )
  >- (qexists_tac`b` >> qexists_tac`a` >> simp[] >> 
      `LENGTH (MAP (λX. X x) Ys) = LENGTH b` by fs[LENGTH_MAP] >>
      `TAKE ((LENGTH (MAP (λX. X x) Xs ⧺ MAP (λX. X x) Ys)) - LENGTH (MAP (λX. X x) Ys)) (MAP (λX. X x) Xs ⧺ MAP (λX. X x) Ys) = TAKE (LENGTH (a++b) - LENGTH b) (a++b)` by metis_tac[] >>
      fs[rich_listTheory.TAKE_LENGTH_APPEND] >> 
      `TAKE (LENGTH (MAP (λX. X x) Xs)) (MAP (λX. X x) Xs ⧺ MAP (λX. X x) Ys) = a` by metis_tac[LENGTH_MAP] >>
      fs[rich_listTheory.TAKE_LENGTH_APPEND]  )
  >- (qexists_tac`a` >> qexists_tac`b` >> simp[] >> 
      `LENGTH (MAP (λX. X x) Ys) = LENGTH b` by fs[LENGTH_MAP] >> 
      `DROP (LENGTH (MAP (λX. X x) Ys)) (MAP (λX. X x) Ys ⧺ MAP (λX. X x) Xs) = DROP (LENGTH b) (b++a)` by fs[] >>
      fs[rich_listTheory.DROP_LENGTH_APPEND])
QED

(* Up to here *)

Theorem conditional_indep_equiv:
  conditional_independence_n p Xs Ys Zs <=> 
  (∀As Bs Cs. conditional_distribution_n p (Xs++Ys) Zs {a++b | a ∈ As ∧ b ∈ Bs} Cs = 
  conditional_distribution_n p Xs Zs As Cs * conditional_distribution_n p Ys Zs Bs Cs )
Proof
  fs[conditional_independence_n_def] >> rpt (AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac) >>
  Cases_on`conditional_distribution_n p Ys Zs Bs Cs = 0` >> simp[] 
  >- ()
  >- ()
QED
