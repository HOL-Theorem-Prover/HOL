(* ------------------------------------------------------------------------- *)
(* Pattern Theory.                                                           *)
(* List patterns to be investigated by similar lists.                        *)
(* List sub-patterns to be investigated with period and order.               *)
(* ------------------------------------------------------------------------- *)

(*

This is applying the new cycle theory to the original Necklace Proof,
i.e. using the idea of action, but not explicitly mentioning it.

Cycle Theory
============

Necklaces are represented by linear lists of length n.

Since they are necklaces, it is natural to join them end to end. For example,
the following "cycling" necklaces are considered equivalent:

+--+--+--+--+--+--+--+
|2 |4 |0 |3 |1 |2 |3 |
+--+--+--+--+--+--+--+
|4 |0 |3 |1 |2 |3 |2 |
+--+--+--+--+--+--+--+
|0 |3 |1 |2 |3 |2 |4 |
+--+--+--+--+--+--+--+
|3 |1 |2 |3 |2 |4 |0 |
+--+--+--+--+--+--+--+
|1 |2 |3 |2 |4 |0 |3 |
+--+--+--+--+--+--+--+
|2 |3 |2 |4 |0 |3 |1 |
+--+--+--+--+--+--+--+
|3 |2 |4 |0 |3 |1 |2 | (next cycle identical to first)
+--+--+--+--+--+--+--+

We shall define and investigate the "cycle" operation on a list.

We shall consider a "similar" relation between lists via cycling.

We shall prove that "similar" is reflexive, symmetric and transitive.

Hence "similar" is an equivalence relation, giving partitions via
equivalent classes on necklaces of length n.

Cycle Order Theory
==================

The basic cycle theory considers necklaces of length n, ignoring its colors.

Ignoring colors, there are only two ways that guarantee cycling to the original:
(1) with 0 steps:  cycle 0 l = l
(2) with n steps:  cycle n l = l   where n = length of the list.

With colors, necklaces have patterns, which may consist of sub-patterns.

This give rise to the concept of order: the least number of steps to cycle
the necklace to its original. The trivial case of 0 steps is excluded to
make the least number interesting.

The main result of this investigation are:
(a) the order k must divide the length n.
(b) the order k of a list is the cardinality of the list's associate,
    the equivalent class of "similar" relation with the given list.

Example of order/associate:

Take LENGTH l = 4, e.g. l = [2;3;2;3]

   cycle 0 l = [2;3;2;3]
   cycle 1 l = [3;2;3;2]
   cycle 2 l = [2;3;2;3]
   cycle 3 l = [3;2;3;2]
   cycle 4 l = [2;3;2;3]

   So, similar in this set is true:
   similar l l
   similar l1 l2 ==> similar l2 l1
   similar l1 l2 /\ similar l2 l3 ==> similar l1 l3

   However, the size of this set is 2, not LENGTH l = 4.

   Hence for n = 4 (length of necklace), a = 2 (colors)
   The set of multicoloured necklaces = M, with CARD M = a^n - a = 2^4 - 2 = 16 - 2 = 14.

   Let the colors be {0,1}. The 14 multicoloured necklaces are:

   #01 [0;0;0;1] cycle with: #02, #04, #08, size of set = 4.
   #02 [0;0;1;0] (see #01)
   #03 [0;0;1;1] cycle with: #06, #12, #09, size of set = 4.
   #04 [0;1;0;0] (see #01)
   #05 [0;1;0;1] cycle with: #10,           size of set = 2.
   #06 [0;1;1;0] (see #03)
   #07 [0;1;1;1] cycle with: #14, #13, #11, size of set = 4.
   #08 [1;0;0;0] (see #01)
   #09 [1;0;0;1] (see #03)
   #10 [1;0;1;0] (see #05)
   #11 [1;0;1;1] (see #07)
   #12 [1;1;0;0] (see #03)
   #13 [1;1;0;1] (see #07)
   #14 [1;1;1;0] (see #07)

   That is, similar partitions the set, but the partitions are of different sizes.
   Note that: 4 + 4 + 2 + 4 = 14 = a^n - a.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "pattern";

(* ------------------------------------------------------------------------- *)

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory numberTheory dividesTheory
     combinatoricsTheory;

open cycleTheory;

(* ------------------------------------------------------------------------- *)
(* Pattern Theory Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   l1 == l2      = similar l1 l2 (infix)
   closed R s    = !x y. x IN s /\ R x y ==> y IN s
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Pattern Theory:
   similar_def         |- !l1 l2. l1 == l2 <=> ?n. l2 = cycle n l1
   similar_nil         |- !ls. ls == [] \/ [] == ls <=> ls = []
   similar_length      |- !l1 l2. l1 == l2 ==> LENGTH l1 = LENGTH l2
   similar_refl        |- !ls. ls == ls
   similar_sym         |- !l1 l2. l1 == l2 ==> l2 == l1
   similar_trans       |- !l1 l2 l3. l1 == l2 /\ l2 == l3 ==> l1 == l3

   Similar associates:
   associate_def       |- !x. associate x = {y | x == y}
   associate_element   |- !x y. y IN associate x <=> x == y
   associate_nil       |- associate [] = {[]}
   associate_has_self  |- !x. x IN associate x
   associate_nonempty  |- !x. associate x <> {}
   associate_eq_similar_class
                       |- !x s. x IN s /\ closed similar s ==>
                                associate x = equiv_class similar s x
   associate_as_image  |- !ls. ls <> [] ==>
                               associate ls = IMAGE (\n. cycle n ls) (count (LENGTH ls))
   associate_finite    |- !ls. FINITE (associate ls)
   associate_card_upper|- !ls. ls <> [] ==> CARD (associate ls) <= LENGTH ls

   Period of a list:
   period_def          |- !ls k. period ls k <=> 0 < k /\ cycle k ls = ls
   cycle_period_exists |- !ls. ls <> [] ==> period ls (LENGTH ls)
   cycle_period_multiple
                       |- !n k ls. 0 < n /\ period ls k ==> period ls (n * k)
   cycle_period_similar|- !k x y. period x k /\ x == y ==> period y k

   Order of a list:
   order_def           |- !ls. order ls = LEAST k. period ls k
   cycle_order_period  |- !ls. ls <> [] ==> period ls (order ls)
   cycle_order_minimal |- !k ls. ls <> [] /\ k < order ls ==> ~period ls k
   cycle_order_property|- !ls. ls <> [] ==> 0 < order ls /\ cycle (order ls) ls = ls
   cycle_order_eqn     |- !n ls. ls <> [] ==>
                                 (n = order ls <=> 0 < n /\ cycle n ls = ls /\
                                       !j. 0 < j /\ j < n ==> cycle j ls <> ls)
   cycle_order_multiple|- !n ls. cycle (n * order ls) ls = ls
   cycle_mod_order     |- !n ls. cycle n ls = cycle (n MOD order ls) ls
   cycle_order_divides_length
                       |- !ls. ls <> [] ==> LENGTH ls MOD order ls = 0
   cycle_order_similar |- !x y. x == y ==> order x = order y

   Deduction of associate cardinality:
   associate_eq_order_image
                       |- !ls. ls <> [] ==>
                               associate ls = IMAGE (\n. cycle n ls) (count (order ls))
   associate_order_map_surj
                       |- !ls. ls <> [] ==>
                               SURJ (\n. cycle n ls) (count (order ls)) (associate ls)
   associate_order_map_inj_imp
                       |- !m n ls. ls <> [] /\ m < order ls /\ n < order ls /\ m <= n /\
                                   cycle m ls = cycle n ls ==> m = n
   associate_order_map_inj
                       |- !ls. ls <> [] ==>
                               INJ (\n. cycle n ls) (count (order ls)) (associate ls)
   associate_order_map_bij
                       |- !ls. ls <> [] ==>
                               BIJ (\n. cycle n ls) (count (order ls)) (associate ls)
   associate_card_eq_order
                       |- !ls. ls <> [] ==> CARD (associate ls) = order ls
   associate_card_divides_length
                       |- !ls. ls <> [] ==> LENGTH ls MOD CARD (associate ls) = 0

   Cycle 1 and Order 1:
   cycle_1_eq_order_1  |- !ls. ls <> [] ==> (cycle 1 ls = ls <=> order ls = 1)
   cycle_order_prime_length
                       |- !ls. prime (LENGTH ls) ==>
                               order ls = 1 \/ order ls = LENGTH ls
   associate_card_prime_length
                       |- !ls. prime (LENGTH ls) ==>
                               CARD (associate ls) = 1 \/ CARD (associate ls) = LENGTH ls

*)

(* ------------------------------------------------------------------------- *)
(* Two lists are similar if they are related through cycle.                  *)
(* ------------------------------------------------------------------------- *)

(* Define similar to relate two lists *)
Definition similar_def[nocompute]:
    similar l1 l2 = ?n. l2 = cycle n l1
End
(* Note: use [nocompute] as this is not effective. *)

(* set infix and overload for similar *)
val _ = set_fixity "==" (Infixl 480);
val _ = overload_on ("==", ``similar``);

(* ------------------------------------------------------------------------- *)
(* Know about Similar between Cycles.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: only NIL can be similar to NIL. *)

(* Theorem: ls == [] \/ [] == ls <=> ls = [] *)
(* Proof:
      ls == [] \/ [] == ls
  <=> ?n. [] = cycle n ls \/ ?n. ls = cycle n []   by similar_def
  <=> ls = []                                      by cycle_eq_nil, any n
*)
Theorem similar_nil:
  !ls. ls == [] \/ [] == ls <=> ls = []
Proof
  metis_tac[similar_def, cycle_eq_nil]
QED

(* Idea: only same length lists can be similar to each other. *)

(* Theorem: l1 == l2 ==> LENGTH l1 = LENGTH l2 *)
(* Proof:
       l1 == l2
   ==> ?n. l2 = cycle n l1   by similar_def
   ==> LENGTH l2 = LENGTH l1    by cycle_same_length
*)
Theorem similar_length:
  !l1 l2. l1 == l2 ==> LENGTH l1 = LENGTH l2
Proof
  metis_tac[similar_def, cycle_same_length]
QED

(* ------------------------------------------------------------------------- *)
(* Show that Similar is an equivalence relation.                             *)
(* ------------------------------------------------------------------------- *)

(* Idea: similar is reflexive. *)

(* Theorem: ls == ls *)
(* Proof:
       ls == ls
   <=> ?n. ls = cycle n ls     by similar_def
   Take n = 0,
       cycle 0 ls = ls         by cycle_0
*)
Theorem similar_refl:
  !ls. ls == ls
Proof
  metis_tac[similar_def, cycle_0]
QED

(* Idea: similar is symmetric. *)

(* Theorem: l1 == l2 ==> l2 == l1 *)
(* Proof:
   If l1 = [],
      Then l2 = []                   by similar_nil
      so l2 == []                    by similar_nil
   If l1 <> [],
      Let k = LENGTH l1.
      Then k <> 0                    by LENGTH_NIL, l1 <> []
      Note l1 == l2 means
           ?n. l2 = cycle n l1       by similar_def
       and n MOD k < k               by MOD_LESS, 0 < k
       Let m = k - (n MOD k).
       cycle m l2
     = cycle m (cycle (n MOD k) l1)  by cycle_mod_length
     = l1                            by cycle_inv
   Hence l2 == l1                    by similar_def
*)
Theorem similar_sym:
  !l1 l2. (l1 == l2) ==> (l2 == l1)
Proof
  rw[similar_def] >>
  Cases_on `l1 = []` >-
  metis_tac[cycle_eq_nil] >>
  qabbrev_tac `k = LENGTH l1` >>
  qexists_tac `k - (n MOD k)` >>
  `0 < k` by fs[LENGTH_NON_NIL, Abbr`k`] >>
  `n MOD k < k` by rw[MOD_LESS] >>
  `n MOD k <= k` by decide_tac >>
  metis_tac[cycle_mod_length, cycle_inv]
QED

(* Idea: similar is transitive. *)

(* Theorem: l1 == l2 /\ l2 == l3 ==> l1 == l3 *)
(* Proof:
   Note l1 == l2 ==> ?n1. l2 = cycle n1 l1   by similar_def
    and l2 == l3 ==> ?n2. l3 = cycle n2 l2   by similar_def
        l3 = cycle n2 l2
           = cycle n2 (cycle n1 l1)
           = cycle (n2 + n1) l1              by cycle_add
   Thus l1 == l3                             by similar_def
*)
Theorem similar_trans:
  !l1 l2 l3. (l1 == l2) /\ (l2 == l3) ==> (l1 == l3)
Proof
  metis_tac[similar_def, cycle_add]
QED

(* ------------------------------------------------------------------------- *)
(* Similar associates.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the associate of list: all those that are similar to the list. *)
Definition associate_def[nocompute]:
    associate x = {y | x == y }
End
(* Note: use [nocompute] as this is not effective. *)

(* Theorem: y IN associate x <=> x == y *)
(* Proof: by associate_def. *)
Theorem associate_element:
  !x y. y IN associate x <=> x == y
Proof
  simp[associate_def]
QED

(* ------------------------------------------------------------------------- *)
(* Know the associates.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Idea: associate NIL is singleton {NIL}. *)

(* Theorem: associate [] = {[]} *)
(* Proof:
     associate []
   = {y | [] == y}     by associate_def
   = {[]}              by similar_nil
*)
Theorem associate_nil:
  associate [] = {[]}
Proof
  rw[associate_def, EXTENSION] >>
  metis_tac[similar_nil]
QED

(* Idea: associate x has x itself. *)

(* Theorem: x IN associate x *)
(* Proof:
   Note x == x                       by similar_refl
     so x IN associate x             by associate_element
*)
Theorem associate_has_self:
  !x. x IN associate x
Proof
  metis_tac[similar_refl, associate_element]
QED

(* Idea: associate x is non-EMPTY. *)

(* Theorem: associate x <> {} *)
(* Proof:
   Note x IN associate x       by associate_has_self
    ==> associate x <> {}      by MEMBER_NOT_EMPTY
*)
Theorem associate_nonempty:
  !x. associate x <> {}
Proof
  metis_tac[associate_has_self, MEMBER_NOT_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Associates as equivalent classes.                                         *)
(* ------------------------------------------------------------------------- *)

(* Overload a closed relation R on set s *)
val _ = overload_on("closed", ``\R s. !x y. x IN s /\ R x y ==> y IN s``);

(* Idea: associates are equivalent classes of similar, for sets closed under similar. *)

(* Theorem: x IN s /\ (closed similar s) ==>
            associate x = equiv_class similar s x *)
(* Proof:
   By EXTENSION, this is to show:
      x IN s /\ closed $== s ==> (y IN associate x <=> y IN s /\ x == y)
   But y IN associate x <=> x == y        by associate_element
   and x == y ==> y IN s                  by closed notation
   Hence true.
*)
Theorem associate_eq_similar_class:
  !x s. x IN s /\ (closed similar s) ==>
        associate x = equiv_class similar s x
Proof
  rw[associate_def, EXTENSION] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* To show: associates are FINITE.                                           *)
(* ------------------------------------------------------------------------- *)

(* Idea: the map (\n. cycle n ls): count (LENGTH ls) -> (associate ls)
         is surjective. *)

(* Theorem: ls <> [] ==>
            associate ls = IMAGE (\n. cycle n ls) (count (LENGTH ls)) *)
(* Proof:
   Let k = LENGTH ls, then 0 < k                by LENGTH_NIL
   and n MOD k < k                              by MOD_LESS, 0 < k
   By associate_def, similar_def this is to prove:
   (1) ls <> [] ==> ?n'. (cycle n ls = cycle n' ls) /\ n' < k
       Take n' = n MOD k, then true             by cycle_mod_length
   (2) ls <> [] /\ n < k ==> ?n'. cycle n ls = cycle n' ls
       Take n' = n LENGTH ls, then true         by cycle_mod_length
*)
Theorem associate_as_image:
  !ls. ls <> [] ==>
       associate ls = IMAGE (\n. cycle n ls) (count (LENGTH ls))
Proof
  rw[associate_def, similar_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[cycle_mod_length, LENGTH_NIL, MOD_LESS, NOT_ZERO] >>
  metis_tac[cycle_mod_length]
QED

(* Idea: (associate ls) is FINITE. *)

(* Theorem: FINITE (associate ls) *)
(* Proof:
   If ls = [],
      associate [] = {[])          by associate_nil
      hence FINITE.
   If ls <> [],
      Let k = LENGTH ls.
        associate ls
      = IMAGE (\n. cycle n ls) (count k)
                                   by associate_as_image
      Note FINITE (count k)        by FINITE_COUNT
        so FINITE (associate ls)   by IMAGE_FINITE
*)
Theorem associate_finite:
  !ls. FINITE (associate ls)
Proof
  rpt strip_tac >>
  Cases_on `ls` >-
  rw[associate_nil] >>
  rw[associate_as_image]
QED

(* ------------------------------------------------------------------------- *)
(* To give an estimate of CARD (associate ls).                               *)
(* ------------------------------------------------------------------------- *)

(* Idea: size of (associate ls) <= LENGTH ls. *)

(* Theorem: ls <> [] ==> CARD (associate ls) <= LENGTH ls *)
(* Proof:
   Let k = LENGTH ls.
   Note FINITE (count k)                        by FINITE_COUNT
     CARD (associate ls)
   = CARD (IMAGE (\n. cycle n ls) (count k))    by associate_as_image
   <= CARD (count k)                            by CARD_IMAGE
    = k                                         by CARD_COUNT
*)
Theorem associate_card_upper:
  !ls. ls <> [] ==> CARD (associate ls) <= LENGTH ls
Proof
  metis_tac[associate_as_image, FINITE_COUNT, CARD_IMAGE, CARD_COUNT]
QED

(* ------------------------------------------------------------------------- *)
(* Cycle sub-patterns                                                        *)
(* ------------------------------------------------------------------------- *)

(* We know: cycle_0     cycle 0 ls = ls.
       and: cycle_back  cycle (LENGTH ls) ls = ls.
   Is there some  0 < k < LENGTH ls such that   cycle k ls = ls ?
   If there is such a k, it is very special,
   by the DIVISION algorithm and nature of cycle.
*)

(* ------------------------------------------------------------------------- *)
(* Period of a list.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define period k for a list ls, as a predicate. *)
Definition period_def:
    period ls k <=> 0 < k /\ cycle k ls = ls
End
(* Note:
   . 0 is excluded as a period.
   . Since LENGTH [] = 0, [] cannot have a period.
*)

(* Idea: a non-NIL list has a period: its length. *)

(* Theorem: ls <> [] ==> period ls (LENGTH ls) *)
(* Proof:
   Let k = LENGTH ls.
   By period_def, this is to show:
   (1) 0 < k, true              by LENGTH_NON_NIL
   (2) cycle k ls = ls, true    by cycle_back
*)
Theorem cycle_period_exists:
  !ls. ls <> [] ==> period ls (LENGTH ls)
Proof
  simp[period_def, LENGTH_NON_NIL, cycle_back]
QED

(* Idea: if list ls has period k, then multiples of k are also periods. *)

(* Theorem: 0 < n /\ period ls k ==> period ls (n * k) *)
(* Proof:
   Note 0 < k /\ cycle k ls = ls       by period_def
   By period_def, this is to show:
   (1) 0 < n * k, true                 by LESS_MULT2
   (2) cycle (n * k) ls = ls, true     by cycle_multiple_back
*)
Theorem cycle_period_multiple:
  !n k ls. 0 < n /\ period ls k ==> period ls (n * k)
Proof
  rw[period_def] >>
  metis_tac[cycle_multiple_back, MULT_COMM]
QED

(* Idea: if list x has period k, and x == y, then k is also a period of y. *)

(* Theorem: period x k /\ x == y ==> period y k *)
(* Proof:
   Note 0 < k /\ (cycle n x = x)  by period_def
    and ?n. y = cycle n x         by similar_def
     cycle k (cycle n x)
   = cycle (k + n) x              by cycle_add
   = cycle (n + k) x              by ADD_COMM
   = cycle n (cycle k x)          by cycle_add
   = cycle n x                    by k being a period
*)
Theorem cycle_period_similar:
  !k x y. period x k /\ x == y ==> period y k
Proof
  rw[period_def, similar_def] >>
  metis_tac[cycle_add, ADD_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Order of a list - or minimal period of a list.                            *)
(* ------------------------------------------------------------------------- *)

(* Define order as minimal period of a list. *)
Definition order_def:
    order ls = LEAST k. period ls k
End

(*
> EVAL ``order [2;3;2;3]``; = 2
> EVAL ``order [2;3;2;3;2]``; = 5
*)

(* Idea: the list order is indeed a period. *)

(* Theorem: ls <> [] ==> period ls (order ls) *)
(* Proof:
   Let k = LENGTH ls.
   Note period ls k                      by cycle_period_exists
     so period ls ($LEAST (period ls k)) by LEAST_INTRO
     or period ls (order ls)             by order_def
*)
Theorem cycle_order_period:
  !ls. ls <> [] ==> period ls (order ls)
Proof
  rw[order_def] >>
  metis_tac[cycle_period_exists, whileTheory.LEAST_INTRO]
QED

(* Idea: if k < list order, k is not a period. *)

(* Theorem: ls <> [] /\ k < order ls ==> ~(period ls k) *)
(* Proof:
   Let m = LENGTH ls.
   Note period ls m                by cycle_period_exists
        k < order ls
    ==> k < $LEAST (period ls m)   by order_def
    ==> ~(period ls k)             by LESS_LEAST
*)
Theorem cycle_order_minimal:
  !k ls. ls <> [] /\ k < order ls ==> ~(period ls k)
Proof
  rw[order_def] >>
  metis_tac[cycle_period_exists, whileTheory.LESS_LEAST]
QED

(* Idea: the list order is positive and a period. *)

(* Theorem: ls <> [] ==> 0 < order ls /\ cycle (order ls) ls = ls *)
(* Proof:
   Note period ls (order ls)      by cycle_order_period
     so 0 < order ls /\
        cycle (order ls) ls = ls  by period_def
*)
Theorem cycle_order_property:
  !ls. ls <> [] ==> 0 < order ls /\ cycle (order ls) ls = ls
Proof
  metis_tac[cycle_order_period, period_def]
QED

(* Idea: a criterion to determine list order. *)

(* Theorem: ls <> [] ==> (n = order ls <=>
            0 < n /\ cycle n ls = ls /\ !j. 0 < j /\ j < n ==> cycle j ls <> ls) *)
(* Proof:
   If part: n = order ls ==> 0 < n /\ cycle n ls = ls /\
                         (!j. 0 < j /\ j < n ==> cycle j ls <> ls)
      Note  0 < n /\ cycle n ls = ls   by cycle_order_property
       and !j. 0 < j /\ j < n
            ==> ~period ls j           by cycle_order_minimal
            ==> cycle j ls <> ls       by period_def
   Only-if part: 0 < n /\ cycle n ls = ls /\
       (!j. 0 < j /\ j < n ==> cycle j ls <> ls) ==> n = order ls
      By order_def, period_def, and eliminating LEAST by LEAST_ELIM_TAC,
      this is to show:
      (1) 0 < n /\ cycle n ls = ls ==> ?n'. 0 < n' /\ (cycle n' ls = ls)
          Take n' = n, then true.
      (2) (!m. m < n' ==> (m = 0) \/ cycle m ls <> ls) /\
          0 < n' /\ cycle n' ls = ls ==> n = n'
          By contradiction, suppose n <> n'.
          Then n < n' or n' < n.
          If n < n', then cycle n ls <> ls     by second given implication
          which contradicts cycle n ls = ls.
          If n' < n. then cycle n ls <> ls     by first given implication
          which contradicts cycle n' ls = ls.
*)
Theorem cycle_order_eqn:
  !n ls. ls <> [] ==> (n = order ls <=>
         0 < n /\ cycle n ls = ls /\ !j. 0 < j /\ j < n ==> cycle j ls <> ls)
Proof
  (rw[EQ_IMP_THM] >> simp[cycle_order_property]) >-
  metis_tac[cycle_order_minimal, period_def] >>
  rw[order_def] >>
  numLib.LEAST_ELIM_TAC >>
  rw[period_def] >-
  metis_tac[] >>
  spose_not_then strip_assume_tac >>
  `n < n' \/ n' < n` by decide_tac >-
  metis_tac[NOT_ZERO] >>
  metis_tac[]
QED

(* Idea: cycle through multiples of order is still itself. *)

(* Theorem: cycle (n * (order ls)) ls = ls. *)
(* Proof:
   If ls = [],
      This is true                 by cycle_nil
   Otherwise ls <> [],
   If n = 0,
        cycle (0 * (order ls)) ls
      = cycle 0 ls                 by MULT
      = ls                         by cycle_0
   If n <> 0, 0 < n.
      Let p = order ls.
      Note period ls p             by cycle_order_period
       ==> period ls (n * p)       by cycle_period_multiple
        so cycle (n * p) ls = ls   by period_def
*)
Theorem cycle_order_multiple:
  !n ls. cycle (n * (order ls)) ls = ls
Proof
  rpt strip_tac >>
  Cases_on `ls = []` >-
  simp[cycle_nil] >>
  Cases_on `n = 0` >-
  simp[cycle_0] >>
  metis_tac[cycle_order_period, cycle_period_multiple, period_def, NOT_ZERO]
QED

(* Idea: the number of cycles can be reduced by multiples of order. *)

(* Theorem: cycle n ls = cycle (n MOD (order ls)) ls *)
(* Proof:
   If ls = [],
      This is true                      by cycle_nil
   Otherwise ls <> [],
   Let k = order ls.
   Then 0 < k                           by cycle_order_property
   Let q = n DIV k, r = n MOD k.
   Then n = q * k + r                   by DIVISION, 0 < k
       cycle n ls
     = cycle (r + q * k) ls             by above
     = cycle r (cycle (q * k) ls)       by cycle_add
     = cycle r ls                       by cycle_order_multiple
*)
Theorem cycle_mod_order:
  !n ls. cycle n ls = cycle (n MOD (order ls)) ls
Proof
  rpt strip_tac >>
  Cases_on `ls = []` >-
  simp[cycle_nil] >>
  qabbrev_tac `k = order ls` >>
  qabbrev_tac `q = n DIV k` >>
  qabbrev_tac `r = n MOD k` >>
  `0 < k` by metis_tac[cycle_order_property] >>
  `n = q * k + r` by rw[DIVISION, Abbr`q`, Abbr`r`] >>
  `_ = r + q * k` by decide_tac >>
  metis_tac[cycle_add, cycle_order_multiple]
QED

(* Idea: the list order divides its length. *)

(* Theorem: ls <> [] ==> LENGTH ls MOD (order ls) = 0 *)
(* Proof:
   Let n = LENGTH ls = n, k = order ls, q = n DIV k, r = n MOD k.
   Then cycle k ls = ls                 by cycle_order_period
    and n = q * k + r with r < k        by DIVISION, [1]
        cycle r ls
      = cycle r (cycle (q * k) ls)      by cycle_period_multiple
      = cycle (r + q * k) ls            by cycle_add
      = cycle n ls                      by arithmetic, [1]
      = ls                              by cycle_back
   If r <> 0,
      then cycle r ls = ls              by cycle_order_multiple
        so period ls r                  by period_def, 0 < r
   This contradicts
      r < k ==> ~period ls r            by cycle_order_minimal
   Thus r = 0, or r = n MOD k = 0       by MOD_UNIQUE
*)
Theorem cycle_order_divides_length:
  !ls. ls <> [] ==> LENGTH ls MOD (order ls) = 0
Proof
  rpt strip_tac >>
  qabbrev_tac `n = LENGTH ls` >>
  qabbrev_tac `k = order ls` >>
  `0 < k /\ cycle k ls = ls` by rw[cycle_order_property, Abbr`k`] >>
  qabbrev_tac `q = n DIV k` >>
  qabbrev_tac `r = n MOD k` >>
  `n = q * k + r /\ r < k` by rw[DIVISION, Abbr`q`, Abbr`r`] >>
  (Cases_on `r = 0` >> simp[]) >>
  `cycle r ls = ls` by metis_tac[cycle_order_multiple, cycle_add, cycle_back, ADD_COMM] >>
  metis_tac[cycle_order_minimal, period_def, NOT_ZERO]
QED

(* ------------------------------------------------------------------------- *)
(* Similar lists have the same order.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: if list x has order k, and x == y, then k is also a order of y. *)

(* Theorem: x == y ==> order x k = order y k *)
(* Proof:
   If x = [] or y = [],
      then x = y = []              by similar_nil
      hence true.
   Otherwise x <> [] and y <> [].
   Let a = order x, b = order y.
   Note x == y ==> y == x           by similar_sym
     so period x b and period y a   by cycle_order_period, cycle_period_similar
     if a < b, a contradiction      by cycle_order_minimal
     if b < a, a contradiction      by cycle_order_minimal
   thus a = b.
*)
Theorem cycle_order_similar:
  !x y. x == y ==> order x = order y
Proof
  rpt strip_tac >>
  Cases_on `(x = []) \/ (y = [])` >-
  metis_tac[similar_nil] >>
  `y == x` by rw[similar_sym] >>
  `period x (order y) /\ period y (order x)` by metis_tac[cycle_order_period, cycle_period_similar] >>
  qabbrev_tac `a = order x` >>
  qabbrev_tac `b = order y` >>
  (`a = b \/ a < b \/ b < a` by decide_tac >> metis_tac[cycle_order_minimal])
QED

(* ------------------------------------------------------------------------- *)
(* Deduction of associate cardinality.                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: for k = order ls, associate ls = IMAGE (\n. cycle n ls) (count k). *)

(* Theorem: ls <> [] ==>
            associate ls = IMAGE (\n. cycle n ls) (count (order ls)) *)
(* Proof:
   Let k = order ls.
   By SUBSET_ANTISYM, this is to show:
   (1) (associate ls) SUBSET IMAGE (\n. cycle n ls) (count (order ls))
           x IN associate ls
       <=> ls == x             by associate_def
       <=> ?n. x = cycle n ls  by similar_def
                 = cycle (n MOD k) ls
                               by cycle_mod_order
       Now 0 < k               by cycle_order_property
        so n MOD k < k         by MOD_LESS
       ==> x IN IMAGE (\n. cycle n ls) (count k)
                               by IN_IMAGE
   (2) IMAGE (\n. cycle n ls) (count (order ls)) SUBSET (associate ls)
           x IN IMAGE (\n. cycle n ls) (count k)
       <=> ?n. n IN (count k) /\ (x = cycle n ls)
                               by IN_IMAGE
       ==> ?n. x = cycle n ls
       <=> ls == x             by similar_def
       <=> x IN associate ls   by associate_def
*)
Theorem associate_eq_order_image:
  !ls. ls <> [] ==>
       associate ls = IMAGE (\n. cycle n ls) (count (order ls))
Proof
  rpt strip_tac >>
  irule SUBSET_ANTISYM >>
  rw[SUBSET_DEF, associate_def, similar_def] >| [
    qabbrev_tac `k = order ls` >>
    `0 < k` by rw[cycle_order_property, Abbr`k`] >>
    `n MOD k < k` by rw[MOD_LESS] >>
    metis_tac[cycle_mod_order],
    metis_tac[]
  ]
QED

(* Idea: for order k, (\n. cycle n ls) (count k) (associate ls) is surjective. *)

(* Theorem: ls <> [] ==>
            SURJ (\n. cycle n ls) (count (order ls)) (associate ls) *)
(* Proof:
   Let k = order ls, f = (\n. cycle n ls).
   Note IMAGE f (count k) = associate ls     by associate_eq_order_image, ls <> []
     so SURJ f (count k) (associate ls)      by IMAGE_SURJ
*)
Theorem associate_order_map_surj:
  !ls. ls <> [] ==>
       SURJ (\n. cycle n ls) (count (order ls)) (associate ls)
Proof
  simp[IMAGE_SURJ, associate_eq_order_image]
QED

(* Idea: for order k, x < k and y < k and x <= y,
         cycle x ls = cycle y ls ==> x = y. *)

(* Theorem: ls <> [] /\ m < order ls /\ n < order ls /\
            m <= n /\ cycle m ls = cycle n ls ==> m = n *)
(* Proof:
   Let k = order ls, then 0 < k    by cycle_order_property
   Let d = n - m, then n = d + m   by arithmetic
   Suppose d <> 0.
   Then 0 < d, and d <= n < k, so d < k.
          cycle d (cycle n ls)
        = cycle d (cycle m ls)     by given
        = cycle (d + m) ls         by cycle_add
        = cycle n ls               by n = d + m
   Thus period (cycle n ls) d      by period_def
    But ls == cycle n ls           by similar_def
     so cycle n ls == ls           by similar_sym
    ==> period ls d                by cycle_period_similar
   With 0 < d < k, a contradiction by cycle_order_minimal, ls <> []
*)
Theorem associate_order_map_inj_imp:
  !m n ls. ls <> [] /\ m < order ls /\ n < order ls /\
           m <= n /\ cycle m ls = cycle n ls ==> m = n
Proof
  rpt strip_tac >>
  qabbrev_tac `k = order ls` >>
  `0 < k` by rw[cycle_order_property, Abbr`k`] >>
  `n = (n - m) + m` by decide_tac >>
  qabbrev_tac `d = n - m` >>
  (Cases_on `d = 0` >> simp[]) >>
  `0 < d /\ d < k` by decide_tac >>
  `cycle d (cycle n ls) = cycle d (cycle m ls)` by rw[] >>
  `_ = cycle n ls` by fs[cycle_add] >>
  `ls == cycle n ls` by metis_tac[similar_def] >>
  `period (cycle n ls) d` by rw[period_def] >>
  `period ls d` by metis_tac[cycle_period_similar, similar_sym] >>
  metis_tac[cycle_order_minimal]
QED

(* Idea: for k = order ls,
         (\n. cycle n ls) (count k) (associate ls) is injective. *)

(* Theorem: ls <> [] ==> INJ (\n. cycle n ls) (count (order ls)) (associate ls) *)
(* Proof:
   By associate_def, similar_def, INJ_DEF, this is to show:
   (1) n < order ls ==> ?n'. cycle n ls = cycle n' ls
       Take n' = n, hence true.
   (2) n < order ls /\ n' < order ls /\ cycle n ls = cycle n' ls ==> n = n'
       If n <= n', n = n'         by associate_order_map_inj_imp, ls <> []
       If n' <= n, n' = n         by associate_order_map_inj_imp, ls <> []
       Thus n = n'.
*)
Theorem associate_order_map_inj:
  !ls. ls <> [] ==> INJ (\n. cycle n ls) (count (order ls)) (associate ls)
Proof
  rw[associate_def, similar_def, INJ_DEF] >-
  metis_tac[] >>
  `n <= n' \/ n' <= n` by decide_tac >-
  metis_tac[associate_order_map_inj_imp] >>
  metis_tac[associate_order_map_inj_imp]
QED

(* Idea: for k = order ls, (\n. cycle n ls) (count k) (associate ls) is bijective. *)

(* Theorem: ls <> [] ==> BIJ (\n. cycle n ls) (count (order ls)) (associate ls) *)
(* Proof: by BIJ_DEF, associate_order_map_inj, associate_order_map_surj. *)
Theorem associate_order_map_bij:
  !ls. ls <> [] ==>
       BIJ (\n. cycle n ls) (count (order ls)) (associate ls)
Proof
  simp[BIJ_DEF, associate_order_map_inj, associate_order_map_surj]
QED

(* Theorem: CARD (associate ls) = order ls *)
(* Proof:
   Let k = order ls, f = (\n. cycle n ls).
   Note FINITE (count k)                 by FINITE_COUNT
    and FINITE (associate ls)            by associate_finite
    and BIJ f (count k) (associate ls)   by associate_order_map_bij
        CARD (associate ls)
      = CARD (count k)                   by FINITE_BIJ_CARD_EQ
      = k                                by CARD_COUNT
*)
Theorem associate_card_eq_order:
  !ls. ls <> [] ==> CARD (associate ls) = order ls
Proof
  rpt strip_tac >>
  qabbrev_tac `k = order ls` >>
  `FINITE (count k)` by rw[] >>
  `FINITE (associate ls)` by rw[associate_finite] >>
  `BIJ (\n. cycle n ls) (count k) (associate ls)` by rw[associate_order_map_bij, Abbr`k`] >>
  metis_tac[FINITE_BIJ_CARD_EQ, CARD_COUNT]
QED

(* Idea: CARD (associate ls) divides LENGTH ls. *)

(* Theorem: ls <> [] ==> (LENGTH ls) MOD (CARD (associate ls)) = 0 *)
(* Proof:
   Let k = order ls.
   Note (LENGTH ls) MOD k = 0                  by cycle_order_divides_length
    and CARD (associate ls) = k                by associate_card_eq_order
   Thus CARD (associate ls) divides LENGTH ls  by above
*)
Theorem associate_card_divides_length:
  !ls. ls <> [] ==> (LENGTH ls) MOD (CARD (associate ls)) = 0
Proof
  simp[cycle_order_divides_length, associate_card_eq_order]
QED

(* ------------------------------------------------------------------------- *)
(* Cycle 1 and Order 1.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Idea: a list with cycle 1 ls = ls iff order 1. *)

(* Theorem: ls <> [] ==> (cycle 1 ls = ls <=> order ls = 1) *)
(* Proof:
   If part: cycle 1 ls = ls ==> order ls = 1
      This is true            by cycle_order_eqn
   Only-if part: order ls = 1 ==> cycle 1 ls = ls
      This is true            by cycle_order_property
*)
Theorem cycle_1_eq_order_1:
  !ls. ls <> [] ==> (cycle 1 ls = ls <=> order ls = 1)
Proof
  rw[EQ_IMP_THM] >| [
    `0 < 1 /\ (!j. 0 < j /\ j < 1) ==> (cycle j ls <> ls)` by rw[] >>
    fs[cycle_order_eqn],
    metis_tac[cycle_order_property]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Finally, primes enter into the picture.                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: if length of a list is prime p, its order is either 1 or p. *)

(* Theorem: prime (LENGTH ls) ==> order ls = 1 \/ order ls = LENGTH ls *)
(* Proof:
   Note LENGTH ls <> 0            by NOT_PRIME_0
     so ls <> []                  by LENGTH_NIL
    Let k = order ls.
   Then 0 < k                     by cycle_order_property
    and (LENGTH ls) MOD k = 0     by cycle_order_divides_length
     or k divides (LENGTH ls)     by DIVIDES_MOD_0
    ==> k = 1 or k = LENGTH ls    by prime_def
*)
Theorem cycle_order_prime_length:
  !ls. prime (LENGTH ls) ==> order ls = 1 \/ order ls = LENGTH ls
Proof
  rpt strip_tac >>
  `ls <> []` by metis_tac[LENGTH_NIL, NOT_PRIME_0] >>
  qabbrev_tac `k = order ls` >>
  `0 < k` by rw[cycle_order_property, Abbr`k`] >>
  `k divides (LENGTH ls)` by fs[cycle_order_divides_length, DIVIDES_MOD_0, Abbr`k`] >>
  metis_tac[prime_def]
QED

(* Idea: if length of a list is prime p, its associate size is 1 or p. *)

(* Theorem: prime (LENGTH ls) ==>
            CARD (associate ls) = 1 \/ CARD (associate ls) = LENGTH ls *)
(* Proof:
   Note LENGTH ls <> 0                   by NOT_PRIME_0
     so ls <> []                         by LENGTH_NIL
   Thus CARD (associate ls) = order ls   by associate_card_eq_order
    the result follows                   by cycle_order_prime_length
*)
Theorem associate_card_prime_length:
  !ls. prime (LENGTH ls) ==>
       CARD (associate ls) = 1 \/ CARD (associate ls) = LENGTH ls
Proof
  rpt strip_tac >>
  `ls <> []` by metis_tac[LENGTH_NIL, NOT_PRIME_0] >>
  simp[cycle_order_prime_length, associate_card_eq_order]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
