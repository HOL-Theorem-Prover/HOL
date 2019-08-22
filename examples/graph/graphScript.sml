open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory;
open probabilityTheory measureTheory;

val _ = new_theory "graph";

set_grammar_ancestry ["probability","measure"]

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
  parents ((n,pa):α graph) k = EL k pa
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
  wf G = ∀a b. edges G a b ==> MEM a (nodes G) ∧ b ∈ set (nodes G)
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

Definition respects:
  respects p G = 
   ∀As. joint_distribution_n p (nodes G) As =
   REAL_PROD_IMAGE (λX. conditional_distribution_n p [X] (parents G X)  )
                    (set (nodes G))  
End
