(* ========================================================================= *)
(* FILE          : hh07_inductionScript.sml                                  *)
(* DESCRIPTION   : HolyHammer examples: your own definitions, and induction  *)
(*                                                                           *)
(* Every proof below was found by calling the hammer at the point marked     *)
(* (* hh *); the tactic that follows is the verified, minimised proof that   *)
(* HolyHammer printed.  See README.md for how to replay the calls.           *)
(* ========================================================================= *)
Theory hh07_induction
Ancestors
  arithmetic list rich_list

(* -------------------------------------------------------------------------
   Two lessons in this file.

   1. The hammer sees your own definitions.  Definition equations (and
      every theorem stored in the current theory) are premises like any
      library theorem.  In the hammer's output they appear as
      fetch "hh07_induction" "size_def", that is, DB.fetch; in the
      script we write size_def.

   2. The hammer never does induction.  This is the most common reason
      it fails on goals about recursive functions.  The remedy, which the
      CoqHammer tutorial also recommends, is to start the induction
      yourself and then hammer each case:

        Induct_on `t` >> hh

      The induction hypotheses are assumptions of the step goals, and the
      hammer uses assumptions.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Binary trees
   ------------------------------------------------------------------------- *)

Datatype:
  tree = Lf | Nd tree 'a tree
End

Definition mirror_def:
  (mirror Lf = Lf) /\
  (mirror (Nd l x r) = Nd (mirror r) x (mirror l))
End

Definition size_def:
  (size Lf = 0) /\
  (size (Nd l x r) = size l + 1 + size r)
End

Definition flatten_def:
  (flatten Lf = []) /\
  (flatten (Nd l x r) = flatten l ++ [x] ++ flatten r)
End

(* Called on the whole statement, the hammer fails ("ATPs could not find
   a proof"): no finite set of library facts implies it without
   induction.  After Induct_on, both cases are easy.  The step case has
   two induction hypotheses, one per subtree, and needs commutativity
   and associativity of + to put the sizes in the right order. *)
Theorem size_mirror:
  size (mirror t) = size t
Proof
  Induct_on `t`
  >- (* hh *) metis_tac [mirror_def]
  >- (* hh *) metis_tac [size_def, mirror_def, ADD_SYM, ADD_ASSOC,
                         SUC_ONE_ADD]
QED

Theorem mirror_mirror:
  mirror (mirror t) = t
Proof
  Induct_on `t`
  >- (* hh *) metis_tac [mirror_def]
  >- (* hh *) metis_tac [mirror_def]
QED

(* Here the step case needs list lemmas too: REVERSE distributes over ++
   in reverse order, and the reverse of a singleton is itself. *)
Theorem flatten_mirror:
  flatten (mirror t) = REVERSE (flatten t)
Proof
  Induct_on `t`
  >- (* hh *) metis_tac [flatten_def, mirror_def, REVERSE_DEF]
  >- (* hh *) metis_tac [flatten_def, mirror_def, APPEND_ASSOC,
                         REVERSE_APPEND, REVERSE_SING]
QED

Theorem length_flatten:
  LENGTH (flatten t) = size t
Proof
  Induct_on `t`
  >- (* hh *) metis_tac [size_def, flatten_def, LENGTH]
  >- (* hh *) metis_tac [size_def, flatten_def, LENGTH, NUMERAL_DEF,
                         ALT_ZERO, ADD_CLAUSES, SUC_ONE_ADD, APPEND_ASSOC,
                         LENGTH_APPEND]
QED

(* Once the inductive lemmas are proved, corollaries need no induction:
   the hammer finds flatten_mirror and length_flatten in the current
   theory and combines them with library facts. *)
Theorem length_flatten_mirror:
  LENGTH (flatten (mirror t)) = size t
Proof
  (* hh *)
  metis_tac [flatten_mirror, length_flatten, LENGTH_REVERSE]
QED

Theorem mem_flatten_mirror:
  MEM x (flatten (mirror t)) <=> MEM x (flatten t)
Proof
  (* hh *)
  metis_tac [flatten_mirror, MEM_REVERSE]
QED

(* -------------------------------------------------------------------------
   Arithmetic by induction: Gauss's sum
   ------------------------------------------------------------------------- *)

Definition sum_to_def:
  (sum_to 0 = 0) /\
  (sum_to (SUC n) = SUC n + sum_to n)
End

(* The step case is the classic
     2 * (SUC n + sum_to n) = SUC n * (SUC n + 1)
   given 2 * sum_to n = n * (n + 1).  It is non-linear, so DECIDE_TAC
   cannot do it, and the usual manual proof is a careful simp with
   distributivity lemmas.  The hammer found a 12-lemma equational proof
   in about 16 seconds (in an earlier run it needed 25 seconds and
   found a slightly different list).  Such a long list is a sign that
   the goal is near the limit of what the hammer can do.

   The base case used sum_to_compute, a numeral-friendly version of the
   definition that Definition stores automatically.  It is stored in the
   theory but not bound as an ML value, so the fetch form printed by the
   hammer has to stay. *)
Theorem gauss_sum:
  2 * sum_to n = n * (n + 1)
Proof
  Induct_on `n`
  >- (* hh *) metis_tac [fetch "hh07_induction" "sum_to_compute",
                         MULT_CLAUSES]
  >- (* hh *) metis_tac [sum_to_def, ADD_CLAUSES, ADD_SUC, SUC_ADD_SYM, MULT,
                         MULT_SUC, MULT_LEFT_1, NUMERAL_DEF, BIT1, BIT2,
                         RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB]
QED

Theorem le_sum_to:
  n <= sum_to n
Proof
  Induct_on `n`
  >- (* hh *) metis_tac [ZERO_LESS_EQ]
  >- (* hh *) metis_tac [sum_to_def, LE_EXISTS]
QED

(* The same advice applies to library functions.  arithmeticTheory has
   FACT_LESS (0 < FACT n) but no monotonicity lemma for FACT, and the
   hammer fails on the whole statement.  After
   Induct_on `n` the base case is m <= 0 ==> FACT m <= FACT 0, and the
   step case combines the recursion equation FACT (SUC n) = SUC n *
   FACT n with transitivity of <=. *)
Theorem fact_mono:
  m <= n ==> FACT m <= FACT n
Proof
  Induct_on `n`
  >- (* hh *) metis_tac [LE, LESS_OR_EQ]
  >- (* hh *) metis_tac [ADD_MONO_LESS_EQ, ZERO_LESS_EQ, ADD, MULT, ADD_SYM,
                         FACT, LESS_EQ_TRANS, LESS_OR_EQ,
                         LESS_EQ_IFF_LESS_SUC]
QED

(* -------------------------------------------------------------------------
   Definitions that test equality with if-then-else
   ------------------------------------------------------------------------- *)

Definition count_occ_def:
  (count_occ x [] = 0) /\
  (count_occ x (y::ys) = (if x = y then 1 else 0) + count_occ x ys)
End

(* A known weak spot.  With count_occ_def as the only description of
   count_occ, the hammer fails on goals as simple as
     count_occ x (x::l) = count_occ x l + 1
   and on both cases of count_occ_append below.  The provers see the
   definition, but the translation has to encode the boolean test x = y
   inside the if-then-else as a term, and the provers do not manage to
   connect that encoding with ordinary equality.

   The remedy is to state the two branches as separate equations.  The
   simplifier proves them at once, since it handles if-then-else well,
   and after that the hammer works normally.  (For count_occ_append
   alone, Induct_on `l1` >> rw [count_occ_def] is also a complete proof:
   when the simplifier can do a goal, prefer it.) *)
Theorem count_occ_same:
  count_occ x (x::l) = count_occ x l + 1
Proof
  rw [count_occ_def]
QED

Theorem count_occ_other:
  x <> y ==> count_occ x (y::l) = count_occ x l
Proof
  rw [count_occ_def]
QED

Theorem count_occ_append:
  count_occ x (l1 ++ l2) = count_occ x l1 + count_occ x l2
Proof
  Induct_on `l1`
  >- (* hh *) metis_tac [APPEND, count_occ_def, ADD_0, ADD_COMM]
  >- (* hh *) metis_tac [count_occ_same, ADD_COMM, count_occ_other, APPEND,
                         ADD, SUC_ONE_ADD]
QED

(* Here the step case does its own case split on whether x = h, using
   the two equations. *)
Theorem count_occ_le_length:
  count_occ x l <= LENGTH l
Proof
  Induct_on `l`
  >- (* hh *) metis_tac [count_occ_def, LESS_EQ_REFL, LENGTH]
  >- (* hh *) metis_tac [count_occ_other, ADD_SYM, count_occ_same, LENGTH,
                         LESS_EQ_MONO, ALT_ZERO, LESS_EQ, SUC_ONE_ADD,
                         LESS_OR_EQ]
QED

Theorem count_occ_not_mem:
  ~MEM x l ==> count_occ x l = 0
Proof
  Induct_on `l`
  >- (* hh *) metis_tac [count_occ_def]
  >- (* hh *) metis_tac [count_occ_other, MEM]
QED
