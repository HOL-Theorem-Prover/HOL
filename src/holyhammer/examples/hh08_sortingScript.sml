(* ========================================================================= *)
(* FILE          : hh08_sortingScript.sml                                    *)
(* DESCRIPTION   : HolyHammer examples: case study, insertion sort           *)
(* ADAPTED FROM  : the insertion sort of CoqHammer's tutorial.               *)
(*                                                                           *)
(* Every proof below calls the hammer: each hh runs HolyHammer when the      *)
(* theory is built, so building needs a prover (see README.md).  The         *)
(* comment after each hh is the verified, minimised proof that               *)
(* HolyHammer printed when the example was written.                          *)
(* ========================================================================= *)
Theory hh08_sorting
Ancestors
  arithmetic list sorting
Libs
  holyHammer

(* -------------------------------------------------------------------------
   A small verification project, done the way the CoqHammer authors
   recommend: split the development into many small lemmas, prove each
   one with the hammer (doing inductions by hand), and let later hammer
   calls use the earlier lemmas.

   The specification of a sorting function has two parts: the output is
   a permutation of the input, and the output is sorted.  sortingTheory
   provides PERM and SORTED, with a few hundred lemmas about them.
   ------------------------------------------------------------------------- *)

Definition ins_def:
  (ins (x:num) [] = [x]) /\
  (ins x (y::ys) = if x <= y then x::y::ys else y :: ins x ys)
End

Definition isort_def:
  (isort [] = []) /\
  (isort (x::xs) = ins x (isort xs))
End

(* -------------------------------------------------------------------------
   Part 1: permutation
   ------------------------------------------------------------------------- *)

(* The step case has to deal with both branches of the if-then-else in
   ins_def.  The provers handle that themselves: no case split needed.
   The second branch is y :: ins x ys, a permutation of x :: y :: ys
   because swapping the first two elements is a permutation
   (PERM_FUN_SWAP_AT_FRONT) and PERM is a congruence for cons
   (PERM_MONO). *)
Theorem perm_ins:
  PERM (ins x l) (x::l)
Proof
  Induct_on `l`
  >- hh (* metis_tac [ins_def, PERM_REFL] *)
  >- hh (* metis_tac [ins_def, PERM_REFL, PERM_FUN_SWAP_AT_FRONT, PERM_MONO,
                      PERM_SYM] *)
QED

(* The step case uses the lemma just proved. *)
Theorem perm_isort:
  PERM (isort l) l
Proof
  Induct_on `l`
  >- hh (* metis_tac [isort_def, PERM_REFL] *)
  >- hh (* metis_tac [isort_def, perm_ins, PERM_TRANS, PERM_CONS_IFF] *)
QED

(* Two corollaries.  No induction: the hammer combines perm_isort with
   facts about PERM from the library. *)
Theorem length_isort:
  LENGTH (isort l) = LENGTH l
Proof
  hh
  (* metis_tac [perm_isort, PERM_LENGTH] *)
QED

Theorem mem_isort:
  MEM x (isort l) <=> MEM x l
Proof
  hh
  (* metis_tac [perm_isort, PERM_LIST_TO_SET] *)
QED

(* -------------------------------------------------------------------------
   Part 2: sortedness

   This is where the hammer first gets stuck.  For
     SORTED $<= l ==> SORTED $<= (ins x l)
   it fails on the whole statement, and also on the step case after
   Induct_on `l`, even after rw [ins_def] has split the if-then-else.
   The remaining case is
     SORTED $<= (h::l), ~(x <= h), IH  |-  SORTED $<= (h :: ins x l)
   which needs to know what the elements of ins x l are.  No library
   lemma says that, since ins is our own function.

   The fix is tip 3 of README.md: state the missing fact as a lemma.
   The hammer proves it from perm_ins (a permutation has the same
   elements).
   ------------------------------------------------------------------------- *)

Theorem mem_ins:
  MEM y (ins x l) <=> y = x \/ MEM y l
Proof
  hh
  (* metis_tac [perm_ins, MEM, PERM_LIST_TO_SET] *)
QED

(* With mem_ins available, the same hammer call that failed before
   succeeds.  rw [ins_def] closes the base case and the x <= h case by
   itself; the hammer does the remaining case, using SORTED_EQ (sorted
   cons for a transitive order) and mem_ins. *)
Theorem sorted_ins:
  SORTED $<= l ==> SORTED $<= (ins x l)
Proof
  Induct_on `l` >> rw [ins_def] >>
  hh
  (* metis_tac [mem_ins, NOT_LESS, SORTED_EQ, LESS_OR_EQ, transitive_LE] *)
QED

Theorem sorted_isort:
  SORTED $<= (isort l)
Proof
  Induct_on `l`
  >- hh (* metis_tac [isort_def, SORTED_NIL] *)
  >- hh (* metis_tac [sorted_ins, isort_def] *)
QED

(* -------------------------------------------------------------------------
   Part 3: consequences of the specification

   A sorted permutation of a list is unique (SORTED_PERM_EQ, for a
   transitive and antisymmetric order).  The hammer finds that theorem,
   and the facts that <= is transitive and antisymmetric, and combines
   them with perm_isort and sorted_isort.  No induction is needed.
   ------------------------------------------------------------------------- *)

Theorem isort_sorted_id:
  SORTED $<= l ==> isort l = l
Proof
  hh
  (* metis_tac [sorted_isort, perm_isort, EQ_LESS_EQ, transitive_LE,
                relationTheory.antisymmetric_def, SORTED_PERM_EQ] *)
QED

Theorem isort_idem:
  isort (isort l) = isort l
Proof
  hh
  (* metis_tac [perm_isort, sorted_isort, EQ_LESS_EQ, transitive_LE,
                relationTheory.antisymmetric_def, SORTED_PERM_EQ] *)
QED

(* Sorting respects permutations.  The hammer fails on

     PERM l1 l2 ==> isort l1 = isort l2

   directly.  It is two steps away from the library: first the outputs
   are permutations of each other, then both are sorted, so they are
   equal.  The first step is a hammer call: *)
Theorem perm_isort_perm:
  PERM l1 l2 ==> PERM (isort l1) (isort l2)
Proof
  hh
  (* metis_tac [perm_isort, PERM_CONG_2] *)
QED

(* The hammer still fails on the second step, even with
   perm_isort_perm available.  But the hammer's proof of isort_idem
   above shows what such a proof looks like, and the same metis_tac
   call with perm_isort_perm in place of perm_isort proves it.  Hammer
   output is a good template for proofs of similar goals. *)
Theorem isort_perm_eq:
  PERM l1 l2 ==> isort l1 = isort l2
Proof
  metis_tac [perm_isort_perm, sorted_isort, EQ_LESS_EQ, transitive_LE,
             relationTheory.antisymmetric_def, SORTED_PERM_EQ]
QED
