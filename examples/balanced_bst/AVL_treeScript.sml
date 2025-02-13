(* ----------------------------------------------------------------------------
-- Thesis : Formalization of AVL Trees in HOL4
-- Author : Sineeha Kodwani (supervisor: Chun Tian)
--
-- The core implementations in this reference module cover size-balanced binary
   trees, and have served as a foundation for defining AVL tree operations such
   as insertion, deletion, and balancing through rotations in HOL4.
--
-- Acknowledgement of Resources and Contributions:
--
-- This section draws on key theorems, definitions, and properties from the
   book *Basic Concepts in Data Structures* by Shmuel Tomi Klein, specifically
   Chapter 5 "AVL Trees" (doi: 10.1017/CBO9781316676226.006).
----------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib BasicProvers;

open optionTheory pairTheory stringTheory arithmeticTheory pred_setTheory
     listTheory finite_mapTheory alistTheory sortingTheory comparisonTheory
     pred_setTheory hurdUtils numberTheory;

open fibonacciTheory;

val _ = intLib.deprecate_int ();
val _ = numLib.prefer_num ();

val _ = new_theory "AVL_tree";

Datatype:
  avl_tree = Tip | Bin int num 'a avl_tree avl_tree
End

Definition height_def[simp]:
  height Tip = 0 ∧
  height (Bin h k v l r) = MAX (height l) (height r) + 1
End

Definition singleton_avl_def:
  singleton_avl k v = Bin 0 k v Tip Tip
End

Definition avl_def[simp]:
  avl Tip = T ∧
  avl (Bin bf k v l r) =
    ((height l = height r ∨ height l = height r + 1 ∨ height r = height l + 1) ∧
     bf = &height r - &height l ∧
     avl l ∧ avl r)
End

Definition node_count_def[simp] :
  node_count Tip = 0n ∧
  node_count (Bin bf k v l r) = node_count l + node_count r + 1
End

Definition N_def:
 N k = MIN_SET(IMAGE node_count {x:num avl_tree | height x = k ∧ avl x})
End

Definition complete_avl_def[simp]:
  complete_avl 0 = Tip ∧
  complete_avl (SUC n) = Bin 0 0 ARB (complete_avl n) (complete_avl n)
End

Definition minimal_avl_def:
  minimal_avl (t: 'a avl_tree) ⇔
    avl t ∧
    ∀t': 'a avl_tree.
      avl t' ∧ height t' = height t ⇒
      node_count t ≤ node_count t'
End

Definition tree_def:
  tree k v l r =
    Bin (&height r - &height l) k v l r
End

(*
   Definition of balanceL for balancing an AVL tree after an insertion
   on the left subtree. The function takes a key (k), a value (v),
   the left subtree (l), and the right subtree (r) as arguments.
*)
Definition balanceL_def:
  balanceL k v l r =

    (* Check if the left subtree height is exactly two more than the right subtree height,
       indicating an imbalance that requires a left rotation to restore balance. *)
    if height l = height r + 2 then

      (* Pattern match on the left subtree to determine the exact rotation needed. *)
      (case l of
         (* If the left subtree (l) has a root node with key `lk`, value `lv`, left child `ll`,
            and right child `lr`, further checks are performed on the heights of `ll` and `lr`. *)
         Bin _ lk lv ll lr =>

           (* Check if `ll` (left child of `l`) is shorter than `lr` (right child of `l`),
              which would require a double rotation (left-right). *)
           if height ll < height lr then

             (* Perform a double rotation: first a left rotation on `lr`,
                then a right rotation on `l` to restore balance. *)
             (case lr of
                Bin _ lrn lrv lrl lrr => tree lrn lrv (tree lk lv ll lrl) (tree k v lrr r)

                (* If `lr` is not a tree, just perform a simple rotation with `k` and `v`. *)
              | _ => tree lk lv ll (tree k v lr r))

           (* If `ll` is taller or equal to `lr`, perform a single rotation
              by making `l` the new root. *)
           else
             tree lk lv ll (tree k v lr r)

       (* If `l` is a Tip (an empty tree), no rotation is needed; return the tree as is. *)
       | Tip => tree k v l r)

    (* If no imbalance (left subtree is not 2 levels taller), return the original tree structure. *)
    else
      tree k v l r
End

(*
   Definition of balanceR for balancing an AVL tree after an insertion
   on the right subtree. This function takes a key (k), a value (v),
   the left subtree (l), and the right subtree (r) as arguments.
*)
Definition balanceR_def:
  balanceR k v l r =

    (* Check if the right subtree height is exactly two more than the left subtree height,
       indicating an imbalance that requires a right rotation to restore balance. *)
    if height r = height l + 2 then

      (* Pattern match on the right subtree to determine the exact rotation needed. *)
      (case r of
         (* If the right subtree (r) has a root node with key `rk`, value `rv`, left child `rl`,
            and right child `rr`, further checks are performed on the heights of `rl` and `rr`. *)
         Bin _ rk rv rl rr =>

           (* Check if `rl` (left child of `r`) is taller than `rr` (right child of `r`),
              which would require a double rotation (right-left). *)
           if height rl > height rr then

             (* Perform a double rotation: first a right rotation on `rl`,
                then a left rotation on `r` to restore balance. *)
             (case rl of
                Bin _ rln rlv rll rlr => tree rln rlv (tree k v l rll) (tree rk rv rlr rr)

                (* If `rl` is not a tree, just perform a simple rotation with `k` and `v`. *)
              | _ => tree rk rv (tree k v l rl) rr)

           (* If `rr` is taller or equal to `rl`, perform a single rotation
              by making `r` the new root. *)
           else
             tree rk rv (tree k v l rl) rr

       (* If `r` is a Tip (an empty tree), no rotation is needed; return the tree as is. *)
       | Tip => tree k v l r)

    (* If no imbalance (right subtree is not 2 levels taller), return the original tree structure. *)
    else
      tree k v l r
End

(*
   Definition of insert_avl, which inserts a key (x) with value (v) into an AVL tree.
   This function ensures that the AVL properties of balance and sorted order are maintained.
*)
Definition insert_avl_def:

  (* Base case: If the tree is empty (Tip), create a new singleton node with key x and value v. *)
  insert_avl x v Tip = singleton_avl x v ∧

  (* Recursive case: If the tree is not empty, check the relationship between x and the root key k. *)
  insert_avl x v (Bin bf k kv l r) =

    (* Case where the key to insert (x) is equal to the root key (k):
       In this case, the key already exists, so we do not insert a duplicate; return the tree as is. *)
    if x = k then
      Bin bf k kv l r

    (* Case where the key to insert (x) is less than the root key (k):
       Recursively insert x into the left subtree (l). After insertion, call balanceL to rebalance the tree
       if necessary, ensuring that the AVL property is maintained. *)
    else if x < k then
      balanceL k kv (insert_avl x v l) r

    (* Case where the key to insert (x) is greater than the root key (k):
       Recursively insert x into the right subtree (r). After insertion, call balanceR to rebalance the tree
       if necessary, ensuring that the AVL property is maintained. *)
    else
      balanceR k kv l (insert_avl x v r)
End

(*
   Definition of remove_max, which removes the maximum key (and its associated value)
   from an AVL tree. This function is used in AVL deletions to find the predecessor
   of a node when both children are present.
*)
Definition remove_max_def:

  (* Base case: If the right subtree is empty (Tip), this node is the maximum.
     Return the key (k), value (v), and left subtree (l), effectively removing this node. *)
  remove_max (Bin _ k v l Tip) = (k, v, l) ∧

  (* Recursive case: If the right subtree is not empty, keep traversing right to find the maximum node. *)
  remove_max (Bin _ k v l r) =

    (* Recursively call remove_max on the right subtree (r) to find the maximum key-value pair.
       Store the results in (max_k, max_v) for the maximum key and value,
       and `r'` for the updated right subtree after removing the maximum node. *)
    let (max_k, max_v, r') = remove_max r in

    (* Rebalance the tree using balanceL after removing the maximum node from the right subtree
       to ensure that the AVL property is maintained. *)
    (max_k, max_v, balanceL k v l r')
End


(*
   Definition of delete_avl, which removes a specified key (x) from an AVL tree.
   The Definition handles several cases to ensure the AVL property is maintained.
*)
Definition delete_avl_def:
  delete_avl x Tip = Tip ∧

    (* If the tree is empty (Tip), return Tip, as there is nothing to delete. *)

  delete_avl x (Bin bf k kv l r) =

    (* If the tree is not empty, we proceed based on comparisons with the root key (k). *)

    if x = k then

      (* Case where the key to delete (x) matches the root key (k): *)
      (case (l, r) of

         (* Subcase 1: Both left and right subtrees are empty (leaf node), so return Tip. *)
         (Tip, Tip) => Tip

         (* Subcase 2: Only the left subtree is empty, so replace the current node with `r`. *)
       | (Tip, _)   => r

         (* Subcase 3: Only the right subtree is empty, so replace the current node with `l`. *)
       | (_, Tip)   => l

         (* Subcase 4: Both subtrees are non-empty. To maintain AVL balance, replace the current
            node with the maximum node from the left subtree, effectively preserving the ordering.
          *)
       | (_, _)     =>
           (* `remove_max l` removes the maximum element from `l` and returns it as `pred_k` and `pred_v`,
              with the modified left subtree `l'`. *)
           let (pred_k, pred_v, l') = remove_max l in

           (* Rebalance the tree with `pred_k` and `pred_v` as the new root, balancing on the right. *)
           balanceR pred_k pred_v l' r
      )

    (* Case where x is smaller than k: recursively delete from the left subtree and rebalance using balanceR. *)
    else if x < k then
      balanceR k kv (delete_avl x l) r

    (* Case where x is larger than k: recursively delete from the right subtree and rebalance using balanceL. *)
    else
      balanceL k kv l (delete_avl x r)
End

(*
   Definition of lookup_avl, which searches for a key (x) in an AVL tree.
   It returns SOME kv if the key is found, where kv is the associated value,
   and NONE if the key does not exist in the tree.
*)
Definition lookup_avl_def:

  (* Base case: If the tree is empty (Tip), return NONE since the key cannot be found. *)
  lookup_avl x Tip = NONE ∧

  (* Recursive case: If the tree is not empty, compare the key to search for (x) with the root key (k). *)
  lookup_avl x (Bin _ k kv l r) =

    (* Case where the key to search for (x) matches the root key (k):
       Return SOME kv, where kv is the value associated with k, indicating that the key was found. *)
    if x = k then
      SOME kv

    (* Case where the key to search for (x) is less than the root key (k):
       Recursively search for x in the left subtree (l). *)
    else if x < k then
      lookup_avl x l

    (* Case where the key to search for (x) is greater than the root key (k):
       Recursively search for x in the right subtree (r). *)
    else
      lookup_avl x r
End

Definition keys_def[simp]:
  keys Tip = {} ∧
  keys (Bin _ k v l r) = {k} ∪ keys l ∪ keys r
End

(*-------Theorems related to AVL Trees and its properties----*)

Theorem height_eq_0[simp]:
  (height t = 0 ⇔ t = Tip) ∧
  (0 = height t ⇔ t = Tip)
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem N_0:
  N 0 = 0
Proof
  csimp[N_def, MIN_SET_THM]
QED

Theorem N_1:
   N 1 = 1
Proof
     REWRITE_TAC [N_def, height_def, avl_def, node_count_def]
  >> sg ‘IMAGE node_count {x :num avl_tree| height x = 1 ∧ avl x} = {1}’
  >- (REWRITE_TAC [EXTENSION, IN_IMAGE]
      >> GEN_TAC
      >> EQ_TAC
      >> STRIP_TAC
      >> ASM_REWRITE_TAC []
      >-(Cases_on ‘x'’
         >> ASM_REWRITE_TAC [height_def,avl_def,node_count_def]
         >> fs[])
      >> fs[]
      >> Q.EXISTS_TAC ‘Bin 0 k v Tip Tip’
      >> fs[])
  >> ASM_REWRITE_TAC[MIN_SET_SING]
QED


Theorem height_complete_avl[simp]:
  height (complete_avl n) = n
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem avl_complete_avl[simp]:
  avl (complete_avl k) = T
Proof
  Induct_on ‘k’ >> simp[]
QED

Theorem trees_of_height_exist:
  ∀k. ∃t. avl t ∧ height t = k
Proof
  GEN_TAC
  >> Q.EXISTS_TAC‘complete_avl k’
  >> simp[]
QED


Theorem minimal_avl_exists:
  ∀k. ∃t. minimal_avl t ∧ height t = k
Proof
  GEN_TAC
  >> qabbrev_tac ‘P = λt. avl t ∧ height t = k’
  >> MP_TAC (Q.SPECL [‘P’, ‘node_count’]
              (INST_TYPE [“:'a” |-> “:'a avl_tree”] WOP_measure))
  >> impl_tac
  >- (rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘complete_avl k’
      >> simp[])
  >> rw [Abbr ‘P’]
  >> Q.EXISTS_TAC ‘b’ >> rw[]
  >> rw[minimal_avl_def]
QED

(* NOTE: This theorem is provided by Chun TIAN *)
Theorem minimal_avl_node_count :
  ∀k (t :num avl_tree). minimal_avl t ∧ height t = k
                                    ⇒ node_count t = N k
Proof
    rw [N_def]
 >> irule MIN_SET_TEST >> rw []
 >- (fs [minimal_avl_def])
 >- (rw [Once EXTENSION] \\
     Q.EXISTS_TAC ‘complete_avl (height t)’ >> rw [])
 >> Q.EXISTS_TAC ‘t’
 >> fs [minimal_avl_def]
QED


Theorem minimal_avl_l_is_avl:
  ∀t. minimal_avl t ⇒ avl t
Proof
  GEN_TAC >>
          rw[avl_def , minimal_avl_def]
  >> fs[minimal_avl_def]
QED

Theorem height_of_minimal_avl_diff_1:
  ∀ bf k v l r. minimal_avl (Bin bf k v l r) ⇒
                (l = Tip ∧ r = Tip) ∨
                height l = height r + 1 ∨
                height r = height l + 1
Proof
  rw[minimal_avl_def,avl_def]
  >> fs[]
  >> CCONTR_TAC
  >> Cases_on ‘l’ >> gvs[] >> gvs[] >> gvs[]
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a0 r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
QED


Theorem children_of_minimal_avl:
  ∀bf k v l r. minimal_avl (Bin bf k v l r) ⇒
                           minimal_avl l ∧ minimal_avl r
Proof
  rw[minimal_avl_def,avl_def]
     >> CCONTR_TAC
  >> gvs[NOT_LE]
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 0 k v t' r’ mp_tac)
    >> simp[]
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 0 k v l t'’ mp_tac)
    >> simp[]
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin (-1) k v t' r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (-1) k v l t'’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
      )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (1) k v t' r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
      )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (1) k v l t'’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
QED

Theorem N_k:
  ∀k. N (k+2) = N (k+1) + N(k) + 1
Proof
  GEN_TAC
  >> Q.SPEC_THEN ‘k+2’ mp_tac
                 (INST_TYPE [“:'a” |-> “:num”]minimal_avl_exists)
  >> STRIP_TAC
  >> ‘N (k+2) = node_count t’
    by metis_tac[minimal_avl_node_count]
  >> simp[]
  >> Cases_on ‘t’
  >- gvs[]
  >> rename1 ‘minimal_avl (Bin bf s v l r)’
  >> ‘minimal_avl l ∧ minimal_avl r’
     by metis_tac[children_of_minimal_avl]
  >> gvs[]
  >> Q.PAT_X_ASSUM ‘minimal_avl (Bin bf s v l r)’
     (MP_TAC o (MATCH_MP height_of_minimal_avl_diff_1))
  >> STRIP_TAC
  >- gvs[]
  >- ( fs[MAX_DEF] >>
      Q_TAC SUFF_TAC ‘node_count r = N k ∧ node_count l = N (k+1)’
       >- rw[]
       >> STRIP_TAC
       >- metis_tac[minimal_avl_node_count]
       >> metis_tac[minimal_avl_node_count]
     )
  >> fs[MAX_DEF] >>
      Q_TAC SUFF_TAC ‘node_count r = N (k+1) ∧ node_count l = N k’
       >- rw[]
       >> STRIP_TAC
       >- metis_tac[minimal_avl_node_count]
       >> metis_tac[minimal_avl_node_count]
QED

Theorem Fibonacci_thm[local] = cj 3 fib
Theorem Fibonacci_increasing[local] = REWRITE_RULE [ADD1] FIB_MONO_SUC
Theorem Fibonacci_monotone[local] = FIB_INCREASES_LE

(* Relationship between node count and Fibonacci sequence*)

Theorem N_fibonacci_relation:
  ∀k. N k = Fibonacci (k+2)-1
Proof
  completeInduct_on ‘k’
  >> Cases_on ‘k’
  >- (simp[N_0]
  >> ONCE_REWRITE_TAC[fib_def]
  >> gvs[]
  >> ONCE_REWRITE_TAC[fib_def]
  >> gvs[])
  >> gvs[SUC_ONE_ADD]
  >> ONCE_REWRITE_TAC[fib_def]
  >> gvs[]
  >> Cases_on ‘n’
  >-( simp[N_1]
      >>ONCE_REWRITE_TAC[fib_def]
      >> gvs[]
      >> ONCE_REWRITE_TAC[fib_def]
      >> gvs[]
    )
  >>gvs[SUC_ONE_ADD]
  >> qabbrev_tac ‘k = n'+2’
  >> sg ‘N k = N(k-1) + N(k-2)+1’
  >- gvs[N_k,Abbr‘k’]
  >> rw[]
  >> ‘k-1<k ∧ k-2<k’ by rw[Abbr‘k’]
  >> rw[Abbr‘k’]
  >> gvs[]
  >> sg ‘Fibonacci 1 ≤ Fibonacci (n'+2) ’
  >- rw[Fibonacci_monotone]
  >> sg ‘Fibonacci 1 ≤ Fibonacci (n'+3)’
  >- rw[Fibonacci_monotone]
  >> sg ‘Fibonacci 1 = 1’
  >-(ONCE_REWRITE_TAC[fib_def]
      >> gvs[]
    )
  >> rw[]
QED

(*-----------Theorems related to balancing and insertion------*)

Theorem keys_balanceL[simp]:
  ∀ k v t1 t2. keys(balanceL k v t1 t2) = {k} ∪ keys t1 ∪ keys t2
Proof
  rw[balanceL_def,tree_def]
  >> reverse(Cases_on ‘t1’ >> rw[])
  >-(SET_TAC[])
  >> rename [‘height t1 < height t2’]
  >> Cases_on ‘t2’ >> rw[] >> SET_TAC[]
QED

Theorem keys_balanceR[simp]:
  ∀ k v t1 t2. keys(balanceR k v t1 t2) = {k} ∪ keys t1 ∪ keys t2
Proof
  rw[balanceR_def,tree_def]
  >> reverse(Cases_on ‘t2’ >> rw[])
  >-(SET_TAC[])
  >> rename [‘height t1 > height t2’]
  >> Cases_on ‘t1’ >> rw[] >> SET_TAC[]
QED

Theorem keys_insert:
  ∀ x v t. keys(insert_avl x v t) = (keys t ∪ {x})
Proof
   Induct_on ‘t’
  >> rw[insert_avl_def,singleton_avl_def]
   >>SET_TAC[]
QED

Theorem height_balL:
  ∀ k v l r. height l = height r+2 ∧ avl l ∧ avl r ⇒
             height (balanceL k v l r) = height r+2 ∨
             height (balanceL k v l r) = height r+3
Proof
  rpt STRIP_TAC
  >> Cases_on ‘l’
  >- gvs[]
  >> gvs[tree_def]
  >> gvs[balanceL_def]
  >> gvs[MAX_DEF]
  >> gvs[balanceL_def]
  >> gvs[tree_def]
  >> gvs[MAX_DEF]
  >> gvs[height_def,MAX_DEF]
  >> Cases_on ‘a0’
  >- gvs[]
  >> gvs[height_def]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def]
QED

Theorem height_balR:
  ∀ k v l r. height r = height l+2 ∧ avl l ∧ avl r ⇒
             height (balanceR k v l r) = height l+2 ∨
             height (balanceR k v l r) = height l+3
Proof
  rpt STRIP_TAC
  >> Cases_on ‘r’
  >- gvs[]
  >> gvs[tree_def]
  >> gvs[balanceR_def]
  >> gvs[MAX_DEF]
  >> Cases_on ‘a’
  >- gvs[]
  >> gvs[height_def]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def]
  >> gvs[balanceR_def]
  >> gvs[tree_def]
  >> gvs[MAX_DEF]
QED

Theorem height_balL2:
  ∀ k v l r. avl l ∧ avl r ∧ height l ≠ height r + 2 ⇒
  height (balanceL k v l r) = (1 + MAX (height l) (height r))
Proof
  rpt STRIP_TAC
  >> Cases_on ‘l’
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
QED

Theorem height_balR2:
  ∀ k v l r. avl l ∧ avl r ∧ height r ≠ height l + 2 ⇒
  height (balanceR k v l r) = (1 + MAX (height l) (height r))
Proof
  rpt STRIP_TAC
  >> Cases_on ‘r’
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
QED


Theorem avl_balL:
  ∀ k v l r. avl l ∧ avl r ∧ (height l = height r ∨ height l = height r+1 ∨ height r = height l+1 ∨ height l = height r+2)
                 ⇒ avl(balanceL k v l r)
Proof
  rpt STRIP_TAC
  >> gvs[balanceL_def,tree_def,height_def]
  >> gvs[balanceL_def,tree_def,height_def]
  >> gvs[balanceL_def,tree_def,height_def]
  >> Cases_on ‘l’
  >- gvs[]
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
  >> Cases_on ‘a0’
  >- gvs[]
  >> gvs[height_def,MAX_DEF]
QED

Theorem avl_balR:
  ∀ k v l r. avl l ∧ avl r ∧ (height r = height l ∨ height r = height l+1 ∨ height l = height r+1 ∨ height r = height l+2)                     ⇒ avl(balanceR k v l r)
Proof
  rpt STRIP_TAC
  >> gvs[balanceR_def,tree_def,height_def]
  >> gvs[balanceR_def,tree_def,height_def]
  >> gvs[balanceR_def,tree_def,height_def]
  >> Cases_on ‘r’
  >- gvs[]
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
  >> Cases_on ‘a’
  >- gvs[]
  >> gvs[height_def,MAX_DEF]
QED

Theorem avl_tree_preserves_avl:
  ∀ l r k v. avl l ∧ avl r ∧ (height l = height r ∨ height l = height r+1 ∨ height  r = height l+1) ⇒ avl (tree k v l r)
Proof
  rpt STRIP_TAC
  >- (rw[tree_def])
  >- (rw[tree_def])
  >> rw[tree_def]
QED

Theorem avl_insert_aux:
  ∀ k v t. avl t ⇒
         avl (insert_avl k v t) ∧
         (height (insert_avl k v t) = height t ∨ height (insert_avl k v t) = height t + 1)
Proof
    rpt GEN_TAC
 >> Induct_on ‘t’
 >- rw[insert_avl_def,singleton_avl_def]
 >> rw[insert_avl_def] (* 12 subgoals *)
 (* goal 1 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 2 (of 12) *)
 >- (simp [] (* eliminate MAX *) \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC \\
     rw [height_balL,height_balL2] >> rw [] \\
     DISJ2_TAC \\
     simp [MAX_DEF] (* eliminate MAX *))
 (* goal 3 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 4 (of 12) *)
 >- (simp [MAX_DEF] (* eliminate MAX *) \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [] (* 2 subgoals *)
     >- (Know ‘height (balanceL n a1 (insert_avl k v t) t') =
               1 + MAX (height (insert_avl k v t)) (height t')’
         >- (MATCH_MP_TAC height_balL2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
      rw [height_balL])
 (* goal 5 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 6 (of 12) *)
 >- (simp [MAX_DEF] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw []
     >- (Know ‘height (balanceL n a1 (insert_avl k v t) t') =
               1 + MAX (height (insert_avl k v t)) (height t')’
         >- (MATCH_MP_TAC height_balL2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
     Know ‘height (balanceL n a1 (insert_avl k v t) t') =
           1 + MAX (height (insert_avl k v t)) (height t')’
     >- (MATCH_MP_TAC height_balL2 >> simp []) \\
     rw [])
 >- (MATCH_MP_TAC avl_balR >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC >> rw [])
 >- (simp [] \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC \\
     rw [height_balR,height_balR2] >> rw [] \\
     DISJ2_TAC \\
     simp [MAX_DEF] )
 >- (MATCH_MP_TAC avl_balR >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC >> rw [])
 >- (simp [MAX_DEF] \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC >> rw []
     >- (Know ‘height (balanceR n a1 t (insert_avl k v t')) =
               1 + MAX (height t)(height(insert_avl k v t'))’
         >- (MATCH_MP_TAC height_balR2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
     Know ‘height (balanceR n a1 t (insert_avl k v t')) =
           1 + MAX (height t)(height(insert_avl k v t'))’
     >- (MATCH_MP_TAC height_balR2 >> simp []) \\
     rw [])
  >- (MATCH_MP_TAC avl_balR >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC >> rw [])
  >- (simp [MAX_DEF]  \\
     Q.PAT_X_ASSUM ‘avl t' ==> _’ MP_TAC >> rw []
     >- (Know ‘height (balanceR n a1 t (insert_avl k v t')) =
               1 + MAX (height t)(height(insert_avl k v t')) ’
         >- (MATCH_MP_TAC height_balR2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
      rw[height_balR])
QED

(*------------ Testing the AVL Tree Operations-----------------*)
(* Test insertion on the tree *)
val t1_t = ``insert_avl 3 3 Tip``
Theorem t1[local] = EVAL ``^t1_t``

val t2_t = ``insert_avl 5 5 ^t1_t``
Theorem t2[local] = EVAL ``^t2_t``

val t3_t = ``insert_avl 2 2 ^t2_t``
Theorem t3[local] = EVAL ``^t3_t``

val t4_t = ``insert_avl 4 4 ^t3_t``
Theorem t4[local] = EVAL ``^t4_t``

val t5_t = ``insert_avl 13 13 ^t4_t``
Theorem t5[local] = EVAL ``^t5_t``

val t6_t = ``insert_avl 14 14 ^t5_t``
Theorem t6[local] = EVAL ``^t6_t``

val t7_t = ``insert_avl 1 1 ^t6_t``
Theorem t7[local] = EVAL ``^t7_t``

val t8_t = ``insert_avl 6 6 ^t7_t``
Theorem t8[local] = EVAL ``^t8_t``

val t9_t = ``insert_avl 7 7 ^t8_t``
Theorem t9[local] = EVAL ``^t9_t``

(* This function takes one of the above t* theorems and return another one
   saying the corresponding tree is indeed an AVL tree. -- Chun TIAN
 *)
fun is_avl th =
    EVAL (mk_comb (“avl :num avl_tree -> bool”, rhs (concl th)));

(* |- avl (Bin 0 3 3 Tip Tip) *)
Theorem avl_t1 = is_avl t1 |> EQT_ELIM

Theorem avl_t2 = is_avl t2 |> EQT_ELIM
Theorem avl_t3 = is_avl t3 |> EQT_ELIM
Theorem avl_t4 = is_avl t4 |> EQT_ELIM
Theorem avl_t5 = is_avl t5 |> EQT_ELIM
Theorem avl_t6 = is_avl t6 |> EQT_ELIM
Theorem avl_t7 = is_avl t7 |> EQT_ELIM

(* (rhs o concl) (|- a = b) returns b *)
(* Test deletion on the tree *)
val t10_t = ``delete_avl 14 ^(t9_t)``;
Theorem t10[local] = EVAL ``^t10_t``

val t11_t = ``delete_avl 5 ^((rhs o concl) t10)``;
Theorem t11[local] = EVAL ``^t11_t``

val t12_t = ``delete_avl 4 ^((rhs o concl) t11)``;
Theorem t12[local] = EVAL ``^t12_t``

(* Test lookup on the tree after insertion *)
val lookup1_t = ``lookup_avl 3 ^((rhs o concl) t9)``
Theorem lookup1[local] = EVAL ``^lookup1_t``

val lookup2_t = ``lookup_avl 14 ^((rhs o concl) t9)``
Theorem lookup2[local] = EVAL ``^lookup2_t``

val lookup3_t = ``lookup_avl 4 ^((rhs o concl) t12)``
Theorem lookup3[local] = EVAL ``^lookup3_t``

val lookup4_t = ``lookup_avl 6 ^((rhs o concl) t9)``
Theorem lookup4[local] = EVAL ``^lookup4_t``

val lookup5_t = ``lookup_avl 10 ^((rhs o concl) t9)``
Theorem lookup5[local] = EVAL ``^lookup5_t``

val _ = export_theory ();
val _ = html_theory "AVL_tree";
