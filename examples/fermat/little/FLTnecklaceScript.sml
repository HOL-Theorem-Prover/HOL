(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Combinatorial proof.                            *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Combinatorial proof)
=============================================
Solomon W. Golomb (1956)
http://www.cimat.mx/~mmoreno/teaching/spring08/Fermats_Little_Thm.pdf

Original proof by J. Petersen in 1872:

Take p elements from q with repetitions in all ways, that is, in q^p ways.
The q sets with elements all alike are not changed by a cyclic permutation of the elements,
while the remaining q<sup>p</sup>-q sets are permuted in sets of p. Hence p divides q^p - q.

This is a combinatorial proof without reference to Group Theory.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "FLTnecklace";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory dividesTheory logrootTheory gcdTheory pred_setTheory
     numberTheory combinatoricsTheory;

open cycleTheory patternTheory;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by necklace Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Cycle and Necklaces:
   necklace_cycle      |- !n a ls k. ls IN necklace n a ==> cycle k ls IN necklace n a
   multicoloured_cycle |- !n a ls k. ls IN multicoloured n a ==> cycle k ls IN multicoloured n a
   multicoloured_not_cycle_1
                       |- !n a ls. ls IN multicoloured n a ==> cycle 1 ls <> ls
   monocoloured_cycle  |- !n a ls k. ls IN monocoloured n a ==> cycle k ls IN monocoloured n a
   monocoloured_cycle_1|- !n a ls. ls IN monocoloured n a ==> cycle 1 ls = ls
   cycle_1_monocoloured|- !n a ls. ls IN necklace n a /\ cycle 1 ls = ls ==> ls IN monocoloured n a
   monocoloured_iff_cycle_1
                       |- !n a ls. ls IN necklace n a ==>
                                  (ls IN monocoloured n a <=> cycle 1 ls = ls)

   Similar Necklaces:
   necklace_similar    |- !n a. closed similar (necklace n a)
   similar_equiv_on_necklace
                       |- !n a. similar equiv_on necklace n a
   necklace_partition_def
                       |- !n a. necklace_partition n a = partition similar (necklace n a)
   necklace_partition_element_nonempty
                       |- !n a e. e IN necklace_partition n a ==> e <> {}
   necklace_partition_element_finite
                       |- !n a e. e IN necklace_partition n a ==> FINITE e
   necklace_associate  |- !n a e ls. e IN necklace_partition n a /\
                                     ls IN e ==> e = associate ls
   necklace_in_associate
                       |- !n a e ls. e IN necklace_partition n a /\
                                     ls IN e ==> ls IN necklace n a
   necklace_associate_card_nonzero
                       |- !n a e. e IN necklace_partition n a ==> 0 < CARD e
   necklace_associate_card_divides_length
                       |- !n a e. e IN necklace_partition n a ==> n MOD CARD e = 0

   Similar Multicoloured Necklaces:
   multicoloured_similar
                       |- !n a. closed similar (multicoloured n a)
   similar_equiv_on_multicoloured
                       |- !n a. similar equiv_on multicoloured n a

   Similar Monocoloured Necklaces:
   monocoloured_similar|- !n a. closed similar (monocoloured n a)
   similar_equiv_on_monocoloured
                       |- !n a. similar equiv_on monocoloured n a

   Similar Monocoloured similar equivalence partitions:
   monocoloured_order_1      |- !n a ls. 0 < n /\ ls IN monocoloured n a ==> order ls = 1
   order_1_monocoloured      |- !n a ls. 0 < n /\ ls IN necklace n a /\ order ls = 1 ==>
                                         ls IN monocoloured n a
   monocoloured_iff_order_1  |- !n a ls. 0 < n /\ ls IN necklace n a ==>
                                        (ls IN monocoloured n a <=> order ls = 1)
   multicoloured_not_order_1 |- !n a ls. 0 < n /\ ls IN multicoloured n a ==> order ls <> 1

   Multicoloured similar equivalence partitions:
   multicoloured_partition_def
                       |- !n a. multicoloured_partition n a = partition similar (multicoloured n a)
   multicoloured_partition_finite
                       |- !n a. FINITE (multicoloured_partition n a)
   multicoloured_partition_element_nonempty
                       |- !n a e. e IN multicoloured_partition n a ==> e <> {}
   multicoloured_partition_element_finite
                       |- !n a e. e IN multicoloured_partition n a ==> FINITE e
   multicoloured_associate
                       |- !n a e ls. e IN multicoloured_partition n a /\
                                     ls IN e ==> e = associate ls
   multicoloured_in_associate
                       |- !n a e ls. e IN multicoloured_partition n a /\
                                     ls IN e ==> ls IN multicoloured n a
   multicoloured_prime_order
                       |- !p a ls. prime p /\ ls IN multicoloured p a ==> order ls = p
   multicoloured_partition_card_prime
                       |- !p a e. prime p /\ e IN multicoloured_partition p a ==> CARD e = p
   multicoloured_card_prime
                       |- !p a. prime p ==>
                                CARD (multicoloured p a) = p * CARD (multicoloured_partition p a)

   Monocoloured similar equivalence partitions:
   monocoloured_partition_def
                       |- !n a. monocoloured_partition n a = partition similar (monocoloured n a)
   monocoloured_partition_finite
                       |- !n a. FINITE (monocoloured_partition n a)
   monocoloured_partition_element_nonempty
                       |- !n a e. e IN monocoloured_partition n a ==> e <> {}
   monocoloured_partition_element_finite
                       |- !n a e. e IN monocoloured_partition n a ==> FINITE e
   monocoloured_associate
                       |- !n a e ls. e IN monocoloured_partition n a /\
                                     ls IN e ==> e = associate ls
   monocoloured_in_associate
                       |- !n a e ls. e IN monocoloured_partition n a /\
                                     ls IN e ==> ls IN monocoloured n a
   monocoloured_associate_sing
                       |- !n a e ls. e IN monocoloured_partition n a /\ ls IN e ==> e = {ls}

   Application to Fermat's Little Theorem:
   fermat_little_1     |- !p a. prime p ==> (a ** p - a) MOD p = 0
   fermat_little_2     |- !p a. prime p ==> p divides a ** p - a

   Revised necklace proof using associates:
   multicoloured_associate_prime_inj
                       |- !p a ls. prime p /\ ls IN multicoloured p a ==>
                                   INJ (\k. cycle k ls) (count p) (associate ls)
   multicoloured_associate_surj
                       |- !n a ls. ls IN multicoloured n a ==>
                                   SURJ (\k. cycle k ls) (count n) (associate ls)
   multicoloured_associate_prime_bij
                       |- !p a ls. prime p /\ ls IN multicoloured p a ==>
                                   BIJ (\k. cycle k ls) (count p) (associate ls)
   multicoloured_associate_card_prime
                       |- !p a ls. prime p /\ ls IN multicoloured p a ==>
                                   CARD (associate ls) = p
   multicoloured_partition_element_card_prime
                       |- !p a e. prime p /\ e IN multicoloured_partition p a ==> CARD e = p
   fermat_little_3     |- !p a. prime p ==> a ** p MOD p = a MOD p

*)

(* ------------------------------------------------------------------------- *)
(* Combinatorial Proof without Group Theory explicitly.                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Cycle and Necklaces.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Idea: if ls is a necklace, (cycle k ls) is also a necklace. *)

(* Theorem: ls IN necklace n a ==> (cycle k ls) IN necklace n a *)
(* Proof:
   Note LENGTH (cycle k ls) = LENGTH ls     by cycle_same_length
    and set (cycle k ls) = set ls           by cycle_same_set
     so (cycle k ls) IN necklace n a        by necklace_def
*)
Theorem necklace_cycle:
  !n a ls k. ls IN necklace n a ==> (cycle k ls) IN necklace n a
Proof
  simp[necklace_def, cycle_same_length, cycle_same_set]
QED

(* Idea: [Closure of cycle for multicoloured necklaces]
         if ls is a multicoloured necklace, (cycle k ls) is also multicoloured. *)

(* Theorem: ls IN multicoloured n a ==> (cycle k ls) IN multicoloured n a *)
(* Proof:
   By multicoloured_element,
   Given: ls IN necklace n a /\ ls <> [] /\ ~SING (set ls),
   this is to show:
   (1) cycle k ls IN necklace n a, true  by necklace_cycle
   (2) cycle k ls <> [], true            by cycle_eq_nil
   (3) ~SING (cycle k ls), true          by cycle_same_set
*)
Theorem multicoloured_cycle:
  !n a ls k. ls IN multicoloured n a ==> (cycle k ls) IN multicoloured n a
Proof
  rw[multicoloured_element] >-
  simp[necklace_cycle] >-
  simp[cycle_eq_nil] >>
  simp[cycle_same_set]
QED

(* Idea: for ls IN (multicoloured n a), cycle 1 ls <> ls. *)

(* Theorem: ls IN multicoloured n a ==> cycle 1 ls <> ls *)
(* Proof:
   By multicoloured_def, monocoloured_def, this is to show:
      ls <> [] /\ ~SING (set ls) ==> cycle 1 ls <> ls
   By contradiction, suppose cycle 1 ls = ls.
   Then SING (set ls)              by cycle_1_set_sing
   This contradicts ~SING (set ls).
*)
Theorem multicoloured_not_cycle_1:
  !n a ls. ls IN multicoloured n a ==> cycle 1 ls <> ls
Proof
  rw[multicoloured_def, monocoloured_def] >>
  metis_tac[cycle_1_set_sing]
QED

(* Idea: [Closure of cycle for monocoloured necklaces]
         if ls is a monocoloured necklace, cycle k ls is also monocoloured. *)

(* Theorem: ls IN monocoloured n a ==> (cycle k ls) IN monocoloured n a *)
(* Proof:
   By monocoloured_element,
   Given: ls IN necklace n a /\ (ls <> [] ==> SING (set ls)),
   this is to show:
   (1) cycle k ls IN necklace n a, true  by necklace_cycle
   (2) cycle k ls <> [] ==> SING (cycle k ls),
       Note ls <> []                     by cycle_eq_nil
        and set (cycle k ls) = set ls    by cycle_same_set
       Hence true.
*)
Theorem monocoloured_cycle:
  !n a ls k. ls IN monocoloured n a ==> (cycle k ls) IN monocoloured n a
Proof
  rw[monocoloured_element] >-
  simp[necklace_cycle] >>
  fs[cycle_eq_nil, cycle_same_set]
QED

(* Idea: a monocoloured necklace ls has cycle 1 ls = ls *)

(* Theorem: ls IN monocoloured n a ==> cycle 1 ls = ls *)
(* Proof:
   If n = 0,
      Note monocoloured 0 a = {[]}   by monocoloured_0
        so ls = [], so true          by cycle_nil
   If n <> 0, then 0 < n.
   Note ls IN necklace n a /\
        ls <> [] ==> SING (set ls)   by monocoloured_def
    Now ls <> []                     by necklace_not_nil, 0 < n
     so SING (set ls)                by implication
    ==> cycle 1 ls = ls              by sing_has_cycle_1
*)
Theorem monocoloured_cycle_1:
  !n a ls. ls IN monocoloured n a ==> cycle 1 ls = ls
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  fs[monocoloured_0, cycle_nil] >>
  `0 < n` by decide_tac >>
  fs[monocoloured_def] >>
  `ls <> []` by metis_tac[necklace_not_nil] >>
  simp[sing_has_cycle_1]
QED

(* Idea: if a necklace ls has cycle 1 ls = ls, it must be monocoloured *)

(* Theorem: ls IN necklace n a /\ cycle 1 ls = ls ==> ls IN monocoloured n a *)
(* Proof:
   Note ls <> [] ==> SING (set ls)   by cycle_1_set_sing
     so ls IN monocoloured n a       by monocoloured_def
*)
Theorem cycle_1_monocoloured:
  !n a ls. ls IN necklace n a /\ cycle 1 ls = ls ==> ls IN monocoloured n a
Proof
  simp[monocoloured_def, cycle_1_set_sing]
QED

(* Idea: a necklace ls is monocoloured iff cycle 1 ls = ls *)

(* Theorem: ls IN necklace n a ==>
            (ls IN monocoloured n a <=> cycle 1 ls = ls) *)
(* Proof: by cycle_1_monocoloured, monocoloured_cycle_1. *)
Theorem monocoloured_iff_cycle_1:
  !n a ls. ls IN necklace n a ==>
           (ls IN monocoloured n a <=> cycle 1 ls = ls)
Proof
  metis_tac[cycle_1_monocoloured, monocoloured_cycle_1]
QED

(* Another proof of monocoloured_iff_cycle_1 according to the paper. *)

(* Idea: a necklace ls is monocoloured iff cycle 1 ls = 1 *)

(* Theorem: ls IN necklace n a ==> (ls IN monocoloured n a <=> cycle 1 ls = ls) *)
(* Proof:
   If n = 0,
      Note necklace 0 a = {[]}        by necklace_0
      Thus ls = {}.
        so ls IN monocoloured 0 a     by monocoloured_0
       and cycle 1 [] = []            by cycle_nil
   Otherwise n <> 0, or 0 < n.
      Note ls <> []                   by necklace_not_nil, 0 < n
      If part: ls IN monocoloured n a ==> cycle 1 ls = ls.
           so SING (set ls)           by monocoloured_element
         thus cycle 1 ls = ls         by cycle_1_iff_set_sing, SING (set ls)
      Only-if part: cycle 1 ls = ls ==> ls IN monocoloured n a.
         Note SING (set ls)           by cycle_1_iff_set_sing, cycle 1 ls = ls
         thus ls IN monocoloured n a  by monocoloured_element
*)
Theorem monocoloured_iff_cycle_1[allow_rebind]:
  !n a ls. ls IN necklace n a ==>
           (ls IN monocoloured n a <=> cycle 1 ls = ls)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  fs[necklace_0, monocoloured_0, cycle_nil] >>
  `ls <> []` by metis_tac[necklace_not_nil, NOT_ZERO] >>
  metis_tac[cycle_1_iff_set_sing, monocoloured_element]
QED

(* ------------------------------------------------------------------------- *)
(* Similar Necklaces.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: if x is a necklace and x == y, then y is also a necklace. *)

(* Theorem: x IN necklace n a /\ (x == y) ==> y IN necklace n a *)
(* Proof:
   Note x == y <=> ?k. y = cycle k x     by similar_def
     so y IN necklace n a                by necklace_cycle
*)
Theorem necklace_similar:
  !n a x y. x IN necklace n a /\ (x == y) ==> y IN necklace n a
Proof
  metis_tac[similar_def, necklace_cycle]
QED

(*
> necklace_similar |> SPEC ``n:num`` |> SPEC ``a:num``;
val it = |- closed $== (necklace n a): thm
*)

(* ------------------------------------------------------------------------- *)
(* Similar as an Equivalence Relation and look at its Partition Sets         *)
(* ------------------------------------------------------------------------- *)

(* Idea: similarity is an equivalence relation on necklaces. *)

(* Theorem: similar equiv_on necklace n a *)
(* Proof:
   By equiv_on_def, this is to show, for x, y, z IN (necklace n a)
   (1) x == x, true                          by similar_refl
   (2) x == y ==> y == x, true               by similar_sym
   (3) x == y /\ y == z ==> x == z, true     by similar_trans
*)
Theorem similar_equiv_on_necklace:
  !n a. similar equiv_on necklace n a
Proof
  simp[equiv_on_def] >>
  metis_tac[similar_refl, similar_sym, similar_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Partitions of necklaces by similarity.                                    *)
(* ------------------------------------------------------------------------- *)

(* Define partitions of necklaces by similarity *)
Definition necklace_partition_def[nocompute]:
    necklace_partition n a = partition similar (necklace n a)
End
(* Note: use [nocompute] as this is not effective. *)

(* Idea: elements in (necklace_partition n a) are non-empty. *)

(* Theorem: e IN necklace_partition n a ==> e <> {} *)
(* Proof:
   Let R = similar, s = necklace n a.
   Then R equiv_on s                   by similar_equiv_on_necklace
     so {} NOTIN partition R s         by EMPTY_NOT_IN_partition
        e IN necklace_partition n a
    <=> e IN partition R s             by necklace_partition_def
    <=> e <> {}                        by above
*)
Theorem necklace_partition_element_nonempty:
  !n a e. e IN necklace_partition n a ==> e <> {}
Proof
  simp[necklace_partition_def, similar_equiv_on_necklace, EMPTY_NOT_IN_partition]
QED

(* Idea: elements in (necklace_partition n a) are finite. *)

(* Theorem: e IN necklace_partition n a ==> FINITE e *)
(* Proof:
   Let R = similar, s = necklace n a.
   Then R equiv_on s                        by similar_equiv_on_necklace
    and FINITE s                            by necklace_finite
     so EVERY_FINITE (partition R s)        by FINITE_partition
     or e IN necklace_partition n a ==>     by necklace_partition_def
        FINITE e
*)
Theorem necklace_partition_element_finite:
  !n a e. e IN necklace_partition n a ==> FINITE e
Proof
  metis_tac[necklace_partition_def, similar_equiv_on_necklace, FINITE_partition, necklace_finite]
QED

(* ------------------------------------------------------------------------- *)
(* Relate partition to associate.                                            *)
(* ------------------------------------------------------------------------- *)

(* Idea: elements in (necklace_partition n a) have associates of its member. *)

(* Theorem: e IN necklace_partition n a /\ ls IN e ==> e = associate ls *)
(* Proof:
   By necklace_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM,
   this is to show:
   Let s = necklace n a.
   Given: x IN s, ls IN e,
          !y. (y IN e ==> y IN s /\ x == y) /\ (y IN s /\ x == y ==> y IN e)
   (1) y IN e ==> ls == y
       Note ls IN s /\ x == ls     by implication
        and y IN s /\ x == y       by implication
       Thus ls == x                by similar_sym
         so ls == y                by similar_trans
   (2) ls == y ==> y IN e
       Note ls IN s /\ x == ls     by implication
        and y IN s                 by necklace_similar, ls == y
       also x == y                 by similar_trans
         so y IN e                 by implication
*)
Theorem necklace_associate:
  !n a e ls. e IN necklace_partition n a /\ ls IN e ==> e = associate ls
Proof
  rw[necklace_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[similar_trans, similar_sym] >>
  metis_tac[necklace_similar, similar_trans]
QED

(* Idea: members of elements in (necklace_partition n a) are necklaces. *)

(* Theorem: e IN necklace_partition n a /\ ls IN e ==> ls IN necklace n a *)
(* Proof:
   By necklace_partition_def, partition_def, EXTENSION,
   this is to show:
        x IN necklace n a, ls IN e,
        !x'. x' IN e <=> x' IN necklace n a /\ x == x'
    ==> ls IN necklace n a
   This is true by implication.
*)
Theorem necklace_in_associate:
  !n a e ls. e IN necklace_partition n a /\ ls IN e ==> ls IN necklace n a
Proof
  rw[necklace_partition_def, partition_def, EXTENSION] >>
  rfs[]
QED

(* Idea: for e in (necklace_partition n a), (CARD e) > 0. *)

(* Theorem: e IN necklace_partition n a ==> 0 < CARD e *)
(* Proof:
   Note e <> EMPTY     by necklace_partition_element_nonempty
    and FINITE e       by necklace_partition_element_finite
     so 0 < CARD e     by CARD_EQ_0
*)
Theorem necklace_associate_card_nonzero:
  !n a e. e IN necklace_partition n a ==> 0 < CARD e
Proof
  metis_tac[necklace_partition_element_nonempty, necklace_partition_element_finite, CARD_EQ_0, NOT_ZERO]
QED

(* Idea: for e in (necklace_partition n a), (CARD e) divides n. *)

(* Theorem: e IN necklace_partition n a ==> n MOD (CARD e) = 0 *)
(* Proof:
   Note 0 < CARD e                 by necklace_associate_card_nonzero
   If n = 0,
      Then 0 MOD (CARD e) = 0      by ZERO_MOD, 0 < CARD e
   If n <> 0, then 0 < n.
      Note e <> {}                 by necklace_partition_element_nonempty
        so ?ls. ls IN e            by MEMBER_NOT_EMPTY
       and ls IN necklace n a      by necklace_in_associate
       and ls <> []                by necklace_not_nil, 0 < n
       and n = LENGTH ls           by necklace_property
       and e = associate ls        by necklace_associate
       ==> LENGTH ls MOD CARD (associate ls) = 0
                                   by associate_card_divides_length
        or n MOD CARD e = 0        by above
*)
Theorem necklace_associate_card_divides_length:
  !n a e. e IN necklace_partition n a ==> n MOD (CARD e) = 0
Proof
  rpt strip_tac >>
  `0 < CARD e` by metis_tac[necklace_associate_card_nonzero] >>
  Cases_on `n = 0` >-
  simp[] >>
  `0 < n` by decide_tac >>
  `?ls. ls IN e` by metis_tac[necklace_partition_element_nonempty, MEMBER_NOT_EMPTY] >>
  `ls IN necklace n a` by metis_tac[necklace_in_associate] >>
  `ls <> []` by metis_tac[necklace_not_nil] >>
  `n = LENGTH ls` by metis_tac[necklace_property] >>
  `e = associate ls` by metis_tac[necklace_associate] >>
  simp[associate_card_divides_length]
QED

(* ------------------------------------------------------------------------- *)
(* Similar Multicoloured Necklaces.                                          *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Closure of similar for multicoloured necklaces]
         only multicoloured necklaces can be similar to each other. *)

(* Theorem: x IN multicoloured n a /\ (x == y) ==> y IN multicoloured n a *)
(* Proof:
   Note ?k. y = cycle k x       by similar_def
   Thus y IN multicoloured n a  by multicoloured_cycle
*)
Theorem multicoloured_similar:
  !n a x y. x IN multicoloured n a /\ (x == y) ==> y IN multicoloured n a
Proof
  metis_tac[similar_def, multicoloured_cycle]
QED

(*
> multicoloured_similar |> SPEC ``n:num`` |> SPEC ``a:num``;
val it = |- closed $== (multicoloured n a): thm
*)

(* Idea: similarity is an equivalence relation on multicoloured necklaces. *)

(* Theorem: similar equiv_on multicoloured n a *)
(* Proof:
   By equiv_on_def, this is to show, for x, y, z IN (multicoloured n a)
   (1) x == x, true                          by similar_refl
   (2) x == y ==> y == x, true               by similar_sym
   (3) x == y /\ y == z ==> x == z, true     by similar_trans

   similarity is reflexive, symmetric and transitive on multicoloured necklaces.
*)
Theorem similar_equiv_on_multicoloured:
  !n a. similar equiv_on multicoloured n a
Proof
  simp[equiv_on_def] >>
  metis_tac[similar_refl, similar_sym, similar_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Similar Monocoloured Necklaces.                                           *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Closure of similar for monocoloured necklaces]
         only monocoloured necklaces can be similar to each other. *)

(* Theorem: x IN monocoloured n a /\ (x == y) ==> y IN monocoloured n a *)
(* Proof:
   Note ?k. y = cycle k x      by similar_def
   Thus y IN monocoloured n a  by monocoloured_cycle
*)
Theorem monocoloured_similar:
  !n a x y. x IN monocoloured n a /\ (x == y) ==> y IN monocoloured n a
Proof
  metis_tac[similar_def, monocoloured_cycle]
QED

(*
> monocoloured_similar |> SPEC ``n:num`` |> SPEC ``a:num``;
val it = |- closed $== (monocoloured n a): thm
*)

(* Idea: similarity is an equivalence relation on monocoloured necklaces. *)

(* Theorem: similar equiv_on monocoloured n a *)
(* Proof:
   By equiv_on_def, this is to show, for x, y, z IN (monocoloured n a)
   (1) x == x, true                          by similar_refl
   (2) x == y ==> y == x, true               by similar_sym
   (3) x == y /\ y == z ==> x == z, true     by similar_trans

   similarity is reflexive, symmetric and transitive on monocoloured necklaces.
*)
Theorem similar_equiv_on_monocoloured:
  !n a. similar equiv_on monocoloured n a
Proof
  simp[equiv_on_def] >>
  metis_tac[similar_refl, similar_sym, similar_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Order of monocoloured necklaces.                                          *)
(* ------------------------------------------------------------------------- *)

(* Idea: the order of a monocoloured necklace is 1. *)

(* Theorem: 0 < n /\ ls IN monocoloured n a ==> order ls = 1 *)
(* Proof:
   Note cycle 1 ls = ls        by monocoloured_cycle_1
    and ls IN necklace n a     by monocoloured_necklace
     so ls <> []               by necklace_not_nil, 0 < n
     so order ls = 1           by cycle_1_eq_order_1, ls <> []
*)
Theorem monocoloured_order_1:
  !n a ls. 0 < n /\ ls IN monocoloured n a ==> order ls = 1
Proof
  rpt strip_tac >>
  `cycle 1 ls = ls` by metis_tac[monocoloured_cycle_1] >>
  `ls <> []` by metis_tac[monocoloured_necklace, necklace_not_nil] >>
  fs[cycle_1_eq_order_1]
QED

(* Idea: a necklace l with order ls = 1 must be monocoloured. *)

(* Theorem: 0 < n /\ ls IN necklace n a /\ order ls = 1 ==> ls IN monocoloured n a *)
(* Proof:
   Note ls <> []                  by necklace_not_nil, 0 < n
     so cycle 1 ls = ls           by cycle_1_eq_order_1, ls <> []
   Thus ls IN monocoloured n a    by monocoloured_iff_cycle_1
*)
Theorem order_1_monocoloured:
  !n a ls. 0 < n /\ ls IN necklace n a /\ order ls = 1 ==> ls IN monocoloured n a
Proof
  rw[monocoloured_iff_cycle_1] >>
  metis_tac[cycle_1_eq_order_1, necklace_not_nil]
QED

(* Idea: a necklace with order ls = 1 iff it is monocoloured *)

(* Theorem: 0 < n /\ ls IN necklace n a ==>
           (ls IN monocoloured n a <=> order ls = 1) *)
(* Proof: by monocoloured_order_1, order_1_monocoloured. *)
Theorem monocoloured_iff_order_1:
  !n a ls. 0 < n /\ ls IN necklace n a ==>
        (ls IN monocoloured n a <=> order ls = 1)
Proof
  metis_tac[monocoloured_order_1, order_1_monocoloured]
QED

(* Idea: for a multicoloured necklace ls, its order is not 1. *)

(* Theorem: 0 < n /\ ls IN multicoloured n a ==> order ls <> 1 *)
(* Proof:
   Note ls IN necklace n a         by multicoloured_necklace
    and ls NOTIN monocoloured n a  by multicoloured_not_monocoloured
     so order ls <> 1              by monocoloured_iff_order_1
*)
Theorem multicoloured_not_order_1:
  !n a ls. 0 < n /\ ls IN multicoloured n a ==> order ls <> 1
Proof
  metis_tac[multicoloured_necklace, multicoloured_not_monocoloured, monocoloured_iff_order_1]
QED

(* ------------------------------------------------------------------------- *)
(* Multicoloured similar equivalence partitions.                             *)
(* ------------------------------------------------------------------------- *)

(* Define partitions of multicoloured necklaces by similarity. *)
Definition multicoloured_partition_def[nocompute]:
    multicoloured_partition n a = partition similar (multicoloured n a)
End
(* Note: use [nocompute] as this is not effective. *)

(* Idea: a multicoloured partition is finite. *)

(* Theorem: FINITE (multicoloured_partition n a) *)
(* Proof:
   Let R = similar, s = multicoloured n a.
   Note FINITE s                              by multicoloured_finite
     so FINITE (partition R s)                by FINITE_partition
     or FINITE (multicoloured_partition n a)  by multicoloured_partition_def
*)
Theorem multicoloured_partition_finite:
  !n a. FINITE (multicoloured_partition n a)
Proof
  simp[multicoloured_partition_def, multicoloured_finite, FINITE_partition]
QED

(* Idea: for e IN (multicoloured_partition n a), e <> EMPTY. *)

(* Theorem: e IN multicoloured_partition n a ==> e <> {} *)
(* Proof:
   Let R = similar, s = multicoloured n a.
   Note R equiv_on s                           by similar_equiv_on_multicoloured
     so {} NOTIN partition R s                 by EMPTY_NOT_IN_partition
     or {} NOTIN (multicoloured_partition n a) by multicoloured_partition_def
    and the result follows.
*)
Theorem multicoloured_partition_element_nonempty:
  !n a e. e IN multicoloured_partition n a ==> e <> {}
Proof
  simp[multicoloured_partition_def, similar_equiv_on_multicoloured, EMPTY_NOT_IN_partition]
QED

(* Idea: for e IN (multicoloured_partition n a), FINITE e. *)

(* Theorem: e IN multicoloured_partition n a ==> FINITE e *)
(* Proof:
   Let R = similar, s = multicoloured n a.
   Note FINITE s                                   by multicoloured_finite
     so EVERY_FINITE (partition R s)               by FINITE_partition
     or EVERY_FINITE (multicoloured_partition n a) by multicoloured_partition_def
    and the result follows.
*)
Theorem multicoloured_partition_element_finite:
  !n a e. e IN multicoloured_partition n a ==> FINITE e
Proof
  metis_tac[multicoloured_partition_def, multicoloured_finite, FINITE_partition]
QED

(* Idea: elements of (multicoloured_partition n a) have associates of each other. *)

(* Theorem: e IN multicoloured_partition n a /\ ls IN e ==> e = associate ls *)
(* Proof:
   By multicoloured_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM,
   this is to show:
   Let s = multicoloured n a.
   Given: x IN s, ls IN e,
          !y. (y IN e ==> y IN s /\ x == y) /\ (y IN s /\ x == y ==> y IN e)
   (1) y IN e ==> ls == y
       Note ls IN s /\ x == ls     by implication
        and y IN s /\ x == y       by implication
       Thus ls == x                by similar_sym
         so ls == y                by similar_trans
   (2) ls == y ==> y IN e
       Note ls IN s /\ x == ls     by implication
        and y IN s                 by multicoloured_similar, ls == y
       also x == y                 by similar_trans
         so y IN e                 by implication
*)
Theorem multicoloured_associate:
  !n a e ls. e IN multicoloured_partition n a /\ ls IN e ==> e = associate ls
Proof
  rw[multicoloured_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[similar_sym, similar_trans] >>
  metis_tac[multicoloured_similar, similar_trans]
QED

(* Idea: elements of (multicoloured_partition n a) have multicoloured necklaces. *)

(* Theorem: e IN multicoloured_partition n a /\ ls IN e ==> ls IN multicoloured n a *)
(* Proof:
   By multicoloured_partition_def, partition_def, EXTENSION, we have:
      x IN multicoloured n a,
      !y. y IN e <=> y IN multicoloured n a /\ x == y,
      ls IN e.
   Thus ls IN multicoloured n a     by implication
*)
Theorem multicoloured_in_associate:
  !n a e ls. e IN multicoloured_partition n a /\ ls IN e ==> ls IN multicoloured n a
Proof
  rw[multicoloured_partition_def, partition_def, EXTENSION] >>
  rfs[]
QED

(* Idea: the order of a prime-length multicoloured necklace is the prime. *)

(* Theorem: prime p /\ ls IN multicoloured p a ==> order ls = p *)
(* Proof:
   Note 0 < p              by PRIME_POS
    and p = LENGTH ls      by multicoloured_necklace, necklace_property
   also order ls <> 1      by multicoloured_not_order_1
    ==> order ls = p       by cycle_order_prime_length
*)
Theorem multicoloured_prime_order:
  !p a ls. prime p /\ ls IN multicoloured p a ==> order ls = p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p = LENGTH ls` by metis_tac[multicoloured_necklace, necklace_property] >>
  `order ls <> 1` by metis_tac[multicoloured_not_order_1] >>
  metis_tac[cycle_order_prime_length]
QED

(* Idea: for length prime p, e IN (multicoloured_partition p a), CARD e = p *)

(* Theorem: prime p /\ e IN multicoloured_partition p a ==> CARD e = p *)
(* Proof:
   Note 0 < p                      by PRIME_POS
    and e <> {}                    by multicoloured_partition_element_nonempty
   Thus ?ls. ls IN e               by MEMBER_NOT_EMPTY
     so ls IN multicoloured n a    by multicoloured_in_associate
    and ls <> []                   by multicoloured_necklace, necklace_not_nil, 0 < p

       CARD e
     = CARD (associate ls)         by multicoloured_associate
     = order ls                    by associate_card_eq_order, ls <> []
     = p                           by multicoloured_prime_order
*)
Theorem multicoloured_partition_card_prime:
  !p a e. prime p /\ e IN multicoloured_partition p a ==> CARD e = p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `?ls. ls IN e` by metis_tac[multicoloured_partition_element_nonempty, MEMBER_NOT_EMPTY] >>
  `ls IN multicoloured p a` by metis_tac[multicoloured_in_associate] >>
  `ls <> []` by metis_tac[multicoloured_necklace, necklace_not_nil] >>
  `CARD e = CARD (associate ls)` by metis_tac[multicoloured_associate] >>
  `_ = order ls` by rw[associate_card_eq_order] >>
  `_ = p` by metis_tac[multicoloured_prime_order] >>
  simp[]
QED

(* Idea: for the (multicoloured p a) with prime length,
         CARD (multicoloured p a) = p * CARD (multicoloured_partition p a) *)

(* Theorem: prime p ==>
            CARD (multicoloured p a) = p * CARD (multicoloured_partition p a) *)
(* Proof:
   By partition_CARD,

     CARD (multicoloured p a)
   = SIGMA CARD (partition similar (multicoloured n a)))
   = SIGMA CARD (associate l)  where l IN (multicoloured n a)
   = SIGMA (order l)       by associate_card_eq_order
   = SIGMA (p)             by order of a multicoloured necklace <> 1
                           and for prime length, order = 1 or p.
   = p * CARD (multicoloured_partition p a)  by multicoloured_partition_card_prime, SIGMA_CARD_CONSTANT
*)
Theorem multicoloured_card_prime:
  !p a. prime p ==>
        CARD (multicoloured p a) = p * CARD (multicoloured_partition p a)
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `FINITE (multicoloured p a)` by rw[multicoloured_finite] >>
  `FINITE (multicoloured_partition p a)` by rw[multicoloured_partition_finite] >>
  `similar equiv_on (multicoloured p a)` by rw[similar_equiv_on_multicoloured] >>
  `CARD (multicoloured p a) = SIGMA CARD (multicoloured_partition p a)` by rw[multicoloured_partition_def, partition_CARD] >>
  metis_tac[multicoloured_partition_card_prime, SIGMA_CARD_CONSTANT]
QED

(* ------------------------------------------------------------------------- *)
(* Monocoloured similar equivalence partitions.                              *)
(* ------------------------------------------------------------------------- *)

(* Define partitions of monocoloured necklaces by similarity. *)
Definition monocoloured_partition_def[nocompute]:
    monocoloured_partition n a = partition similar (monocoloured n a)
End
(* Note: use [nocompute] as this is not effective. *)

(* Idea: a monocoloured partition is finite. *)

(* Theorem: FINITE (monocoloured_partition n a) *)
(* Proof:
   Let R = similar, s = monocoloured n a.
   Note FINITE s                             by monocoloured_finite
     so FINITE (partition R s)               by FINITE_partition
     or FINITE (monocoloured_partition n a)  by monocoloured_partition_def
*)
Theorem monocoloured_partition_finite:
  !n a. FINITE (monocoloured_partition n a)
Proof
  simp[monocoloured_partition_def, monocoloured_finite, FINITE_partition]
QED

(* Idea: for e IN (monocoloured_partition n a), e <> EMPTY. *)

(* Theorem: e IN monocoloured_partition n a ==> e <> {} *)
(* Proof:
   Let R = similar, s = monocoloured n a.
   Note R equiv_on s                           by similar_equiv_on_monocoloured
     so {} NOTIN partition R s                 by EMPTY_NOT_IN_partition
     or {} NOTIN (monocoloured_partition n a)  by monocoloured_partition_def
    and the result follows.
*)
Theorem monocoloured_partition_element_nonempty:
  !n a e. e IN monocoloured_partition n a ==> e <> {}
Proof
  simp[monocoloured_partition_def, similar_equiv_on_monocoloured, EMPTY_NOT_IN_partition]
QED

(* Idea: for e IN (monocoloured_partition n a), FINITE e. *)

(* Theorem: e IN monocoloured_partition n a ==> FINITE e *)
(* Proof:
   Let R = similar, s = monocoloured n a.
   Note FINITE s                                   by monocoloured_finite
     so EVERY_FINITE (partition R s)               by FINITE_partition
     or EVERY_FINITE (monocoloured_partition n a)  by monocoloured_partition_def
    and the result follows.
*)
Theorem monocoloured_partition_element_finite:
  !n a e. e IN monocoloured_partition n a ==> FINITE e
Proof
  metis_tac[monocoloured_partition_def, monocoloured_finite, FINITE_partition]
QED

(* Idea: elements of (monocoloured_partition n a) have associates of each other. *)

(* Theorem: e IN monocoloured_partition n a /\ ls IN e ==> e = associate ls *)
(* Proof:
   By monocoloured_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM,
   this is to show:
   Let s = monocoloured n a.
   Given: x IN s, ls IN e,
          !y. (y IN e ==> y IN s /\ x == y) /\ (y IN s /\ x == y ==> y IN e)
   (1) y IN e ==> ls == y
       Note ls IN s /\ x == ls     by implication
        and y IN s /\ x == y       by implication
       Thus ls == x                by similar_sym
         so ls == y                by similar_trans
   (2) ls == y ==> y IN e
       Note ls IN s /\ x == ls     by implication
        and y IN s                 by monocoloured_similar, ls == y
       also x == y                 by similar_trans
         so y IN e                 by implication
*)
Theorem monocoloured_associate:
  !n a e ls. e IN monocoloured_partition n a /\ ls IN e ==> e = associate ls
Proof
  rw[monocoloured_partition_def, partition_def, associate_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[similar_sym, similar_trans] >>
  metis_tac[monocoloured_similar, similar_trans]
QED

(* Idea: elements of (monocoloured_partition n a) have monocoloured necklaces. *)

(* Theorem: e IN monocoloured_partition n a /\ ls IN e ==> ls IN monocoloured n a *)
(* Proof:
   By monocoloured_partition_def, partition_def, EXTENSION, we have:
      x IN monocoloured n a,
      !y. y IN e <=> y IN monocoloured n a /\ x == y,
      ls IN e.
   Thus ls IN monocoloured n a     by implication
*)
Theorem monocoloured_in_associate:
  !n a e ls. e IN monocoloured_partition n a /\ ls IN e ==> ls IN monocoloured n a
Proof
  rw[monocoloured_partition_def, partition_def, EXTENSION] >>
  rfs[]
QED

(* Idea: elements of (monocoloured_partition n a) are singletons. *)

(* Theorem: e IN monocoloured_partition n a /\ ls IN e ==> e = {ls} *)
(* Proof:
   Note e = associate ls           by monocoloured_associate
     so e = {x | ls == x}          by associate_def
    Now ls IN monocoloured n a     by monocoloured_in_associate
     so cycle 1 ls = ls            by monocoloured_cycle_1
   For any x IN e,
   Then ?k. x = cycle k ls         by similar_def
     so x = ls                     by cycle_1_fix
   Hence e = {ls}                  by EXTENSION
*)
Theorem monocoloured_associate_sing:
  !n a e ls. e IN monocoloured_partition n a /\ ls IN e ==> e = {ls}
Proof
  rpt strip_tac >>
  imp_res_tac monocoloured_associate >>
  fs[associate_def, EXTENSION] >>
  rw[EQ_IMP_THM] >>
  `ls IN monocoloured n a` by metis_tac[monocoloured_in_associate] >>
  fs[similar_def] >>
  metis_tac[monocoloured_cycle_1, cycle_1_fix]
QED

(* ------------------------------------------------------------------------- *)
(* Application to Fermat's Little Theorem.                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Fermat's Little Theorem]
         for 0 < a < p, and prime p, (a^p - a) MOD p = 0 *)

(* Theorem: prime p ==> (a ** p - a) MOD p = 0 *)
(* Proof:
   Note 0 < p                                  by PRIME_POS
        a ** p - a
      = CARD (multicoloured p a)               by multicoloured_card, 0 < p
      = p * CARD (multicoloured_partition p a) by multicoloured_card_prime
   Hence (a ** p - a) MOD p = 0                by MULT_EQ_DIV, 0 < p
*)
Theorem fermat_little_1:
  !p a. prime p ==> (a ** p - a) MOD p = 0
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `a ** p - a = CARD (multicoloured p a)` by rw[multicoloured_card] >>
  `_ = p * CARD (multicoloured_partition p a)` by rw[multicoloured_card_prime] >>
  simp[MULT_EQ_DIV]
QED

(* Idea: for 0 < a < p, and prime p, p divides (a^p - a) *)

(* Theorem: prime p ==> p divides (a ** p - a) *)
(* Proof:
   Note 0 < p                      by PRIME_POS
    and (a ** p - a) MOD p = 0     by fermat_little_1
     so p divides (a ** p - a)     by DIVIDES_MOD_0, 0 < p
*)
Theorem fermat_little_2:
  !p a. prime p ==> p divides (a ** p - a)
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  simp[fermat_little_1, DIVIDES_MOD_0]
QED

(* ------------------------------------------------------------------------- *)
(* Revised necklace proof using associates.                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea: for multicoloured ls, prime p = LENGTH ls,
         the map (count p) to (associate ls) is injective. *)

(* Theorem: prime p /\ ls IN multicoloured p a ==>
            INJ (\k. cycle k ls) (count p) (associate ls) *)
(* Proof:
   By associate_def, INJ_DEF, this is to show:
   (1) k < p ==> ls == cycle k ls, true      by similar_def
   (2) k < p /\ h < p /\ cycle k ls = cycle h ls ==> k = h
       Claim: !x y. x < p /\ y < p /\ x <= y /\ (cycle x ls = cycle y ls) ==> (x = y)
       Proof: By contradiction, suppose x <> y.
              Then x < y.
              Let d = y - x, then y = d + x, and 0 < d < p.
              Note ls IN necklace p a        by multicoloured_necklace
               and LENGTH ls = p             by necklace_property
              Let t = cycle x ls.
                so LENGTH t = p              by cycle_same_length

                   cycle d t
                 = cycle d (cycle x ls)      by notation
                 = cycle (d + x) ls          by cycle_add
                 = cycle y l = t             by notation, and given
              Also cycle p t = t             by cycle_back, p = LENGTH t
                so cycle (gcd d p) t = t     by cycle_gcd_back

              For prime p, 0 < d < p,
              means gcd d p = 1              by NOT_LT_DIVIDES, PRIME_GCD
              But t IN multicoloured p a     by multicoloured_cycle
              This is a contradiction        by multicoloured_not_cycle_1

      Now for k, h. If k <= h, then k = h by lemma.
                    If h <= k, then h = k by lemma.
      Thus k = h.
*)
Theorem multicoloured_associate_prime_inj:
  !p a ls. prime p /\ ls IN multicoloured p a ==>
           INJ (\k. cycle k ls) (count p) (associate ls)
Proof
  rw[associate_def, INJ_DEF] >-
  metis_tac[similar_def] >>
  `!x y. x < p /\ y < p /\ x <= y /\ (cycle x ls = cycle y ls) ==> (x = y)` by
  (spose_not_then strip_assume_tac >>
  `y = (y - x) + x` by decide_tac >>
  qabbrev_tac `d = y - x` >>
  `0 < d /\ d < p /\ 0 < p` by decide_tac >>
  qabbrev_tac `t = cycle x ls` >>
  `ls IN necklace p a` by rw[multicoloured_necklace] >>
  `LENGTH ls = p` by metis_tac[necklace_property] >>
  `LENGTH t = p` by rw[cycle_same_length, Abbr`t`] >>
  `cycle d t = t` by fs[cycle_add, Abbr`t`] >>
  `cycle p t = t` by rw[cycle_back] >>
  `cycle (gcd d p) t = t` by rw[cycle_gcd_back] >>
  `gcd d p = 1` by metis_tac[NOT_LT_DIVIDES, PRIME_GCD, GCD_SYM] >>
  metis_tac[multicoloured_cycle, multicoloured_not_cycle_1]) >>
  (`k <= k' \/ k' <= k` by decide_tac >> metis_tac[])
QED

(* Idea: for multicoloured ls, n = LENGTH ls,
         the map (count n) to (associate ls) is surjective *)

(* Theorem: ls IN multicoloured n a ==>
            SURJ (\k. cycle k ls) (count n) (associate ls) *)
(* Proof:
   By associate_def, SURJ_DEF, this is to show:
   (1) k < n ==> ls == cycle k ls, true  by similar_def
   (2) ls == x ==> ?k. k < n /\ (cycle k ls = x)
       Note 0 < n                 by multicoloured_0, MEMBER_NOT_EMPTY
        and ls IN necklace n a    by multicoloured_necklace
         so LENGTH ls = n         by necklace_length
       Also ?h. x = cycle h ls    by similar_def, ls == x
       Take k = h MOD n.
       Then k < n                 by MOD_LESS, 0 < n
        and cycle k ls
          = cycle (h MOD n) ls    by notation
          = cycle h ls            by cycle_mod_length
          = x                     by above
*)
Theorem multicoloured_associate_surj:
  !n a ls. ls IN multicoloured n a ==>
           SURJ (\k. cycle k ls) (count n) (associate ls)
Proof
  rw[associate_def, SURJ_DEF] >-
  metis_tac[similar_def] >>
  `0 < n` by metis_tac[multicoloured_0, MEMBER_NOT_EMPTY, NOT_ZERO] >>
  `LENGTH ls = n` by metis_tac[multicoloured_necklace, necklace_length] >>
  metis_tac[similar_def, cycle_mod_length, MOD_LESS]
QED

(* Idea: for multicoloured ls, prime p = LENGTH ls,
         the map (count p) to (associate ls) is bijective *)

(* Theorem: prime p /\ ls IN multicoloured p a ==>
            BIJ (\k. cycle k ls) (count p) (associate ls) *)
(* Proof:
   Let f = (\k. cycle k ls).
   By BIJ_DEF, this is to show:
   (1) INJ f (count p) (associate ls), true    by multicoloured_associate_prime_inj
   (2) SURJ f (count p) (associate ls), true   by multicoloured_associate_surj
*)
Theorem multicoloured_associate_prime_bij:
  !p a ls. prime p /\ ls IN multicoloured p a ==>
           BIJ (\k. cycle k ls) (count p) (associate ls)
Proof
  metis_tac[BIJ_DEF, multicoloured_associate_prime_inj, multicoloured_associate_surj]
QED

(* Idea: for multicoloured ls, prime p = LENGTH ls, size of (associate ls) = p. *)

(* Theorem: prime p /\ ls IN multicoloured p a ==> CARD (associate ls) = p *)
(* Proof:
   Let f = (\k. cycle k ls).
   Then BIJ f (count p) (associate ls)   by multicoloured_associate_prime_bij
    Now FINITE (count p)                 by FINITE_COUNT
        CARD (associate ls)
      = CARD (count p)                   by FINITE_BIJ_CARD
      = p                                by CARD_COUNT
*)
Theorem multicoloured_associate_card_prime:
  !p a ls. prime p /\ ls IN multicoloured p a ==> CARD (associate ls) = p
Proof
  metis_tac[multicoloured_associate_prime_bij, FINITE_BIJ_CARD, FINITE_COUNT, CARD_COUNT]
QED

(* Idea: multicoloured partition of prime length necklaces have elements of size prime. *)

(* Theorem: prime p /\ e IN (multicoloured_partition p a) ==> CARD e = p *)
(* Proof:
   Let s = multicoloured n a.
   Note closed similar s                    by multicoloured_similar
       e IN (multicoloured_partition p a)
   <=> e IN partition similar s             by multicoloured_partition_def
   <=> ?ls. ls IN s /\
            (e = equiv_class similar s ls)  by partition_element
   <=> ?ls. ls IN s /\ e = associate ls   by associate_eq_similar_class

       CARD e
     = CARD (associate ls)                  by above
     = p                                    by multicoloured_associate_card_prime
*)
Theorem multicoloured_partition_element_card_prime:
  !p a e. prime p /\ e IN (multicoloured_partition p a) ==> CARD e = p
Proof
  rw[multicoloured_partition_def] >>
  qabbrev_tac `s =  multicoloured p a` >>
  `?ls. ls IN s /\ (e = equiv_class similar s ls)` by rw[GSYM partition_element] >>
  `_ = associate ls` by metis_tac[associate_eq_similar_class, multicoloured_similar] >>
  metis_tac[multicoloured_associate_card_prime]
QED

(* Idea: For prime p, a^p MDD p = a MOD p. *)

(* Theorem: prime p ==> p divides (a ** p - a) *)
(* Proof:
   Note 0 < p                      by PRIME_POS
   Let s = multicoloured p a,
       ps = partition similar s.
   Then FINITE s                   by multicoloured_finite
    and CARD s = a ** p - a        by multicoloured_card
    Now !e. e IN ps                by multicoloured_partition_def
        ==> e IN (multicoloured_partition p a)
        ==> CARD e = p             by multicoloured_partition_element_card_prime
   Note similar equiv_on s         by similar_equiv_on_multicoloured
   Thus p divides CARD s           by equal_partition_factor
     so (a ** p - a) MOD p = 0     by DIVIDES_MOD_0, 0 < p
    Now a <= a ** p                by EXP_LE, 0 < p
    ==> a ** p MOD p = a MOD p     by MOD_EQ, 0 < p
*)
Theorem fermat_little_3:
  !p a. prime p ==> a ** p MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `s = multicoloured p a` >>
  qabbrev_tac `ps = partition similar s` >>
  `FINITE s` by rw[multicoloured_finite, Abbr`s`] >>
  `CARD s = a ** p - a` by rw[multicoloured_card, Abbr`s`] >>
  `!e. e IN ps ==> CARD e = p` by metis_tac[multicoloured_partition_def, multicoloured_partition_element_card_prime] >>
  `p divides (a ** p - a)` by metis_tac[similar_equiv_on_multicoloured, equal_partition_factor] >>
  `a <= a ** p` by rw[EXP_LE] >>
  metis_tac[DIVIDES_MOD_0, MOD_EQ]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
