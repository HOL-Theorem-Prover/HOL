(* ------------------------------------------------------------------------- *)
(* Combinatorics: combinations, permutations and arrangements.               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "combinatorics";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)

(* val _ = load "helperCountTheory"; *)
open helperCountTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def, prime_def *)
open EulerTheory; (* for upto_delete *)

(* for later computation *)
open listTheory;
open rich_listTheory;
open helperListTheory;
open listRangeTheory;

(* (* val _ = load "binomialTheory"; *) *)
open binomialTheory; (* for binomial_iff, binomial_n_n, binomial_formula2 *)

(* (* val _ = load "necklaceTheory"; *) *)
open necklaceTheory; (* for necklace_def, necklace_finite *)


(* ------------------------------------------------------------------------- *)
(* Combinatorics Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Counting number of combinations:
   sub_count_def       |- !n k. sub_count n k = {s | s SUBSET count n /\ CARD s = k}
   choose_def          |- !n k. n choose k = CARD (sub_count n k)
   sub_count_element   |- !n k s. s IN sub_count n k <=> s SUBSET count n /\ CARD s = k
   sub_count_subset    |- !n k. sub_count n k SUBSET POW (count n)
   sub_count_finite    |- !n k. FINITE (sub_count n k)
   sub_count_element_no_self
                       |- !n k s. s IN sub_count n k ==> n NOTIN s
   sub_count_element_finite
                       |- !n k s. s IN sub_count n k ==> FINITE s
   sub_count_n_0       |- !n. sub_count n 0 = {{}}
   sub_count_0_n       |- !n. sub_count 0 n = if n = 0 then {{}} else {}
   sub_count_n_1       |- !n. sub_count n 1 = {{j} | j < n}
   sub_count_n_n       |- !n. sub_count n n = {count n}
   sub_count_eq_empty  |- !n k. sub_count n k = {} <=> n < k
   sub_count_union     |- !n k. sub_count (n + 1) (k + 1) =
                                IMAGE (\s. n INSERT s) (sub_count n k) UNION
                                sub_count n (k + 1)
   sub_count_disjoint  |- !n k. DISJOINT (IMAGE (\s. n INSERT s) (sub_count n k))
                                         (sub_count n (k + 1))
   sub_count_insert    |- !n k s. s IN sub_count n k ==>
                                  n INSERT s IN sub_count (n + 1) (k + 1)
   sub_count_insert_card
                       |- !n k. CARD (IMAGE (\s. n INSERT s) (sub_count n k)) =
                                n choose k
   sub_count_alt       |- !n k. sub_count n 0 = {{}} /\ sub_count 0 (k + 1) = {} /\
                                sub_count (n + 1) (k + 1) =
                                IMAGE (\s. n INSERT s) (sub_count n k) UNION
                                sub_count n (k + 1)
!  sub_count_eqn       |- !n k. sub_count n k =
                                if k = 0 then {{}}
                                else if n = 0 then {}
                                else IMAGE (\s. n - 1 INSERT s) (sub_count (n - 1) (k - 1)) UNION
                                     sub_count (n - 1) k
   choose_n_0          |- !n. n choose 0 = 1
   choose_n_1          |- !n. n choose 1 = n
   choose_eq_0         |- !n k. n choose k = 0 <=> n < k
   choose_0_n          |- !n. 0 choose n = if n = 0 then 1 else 0
   choose_1_n          |- !n. 1 choose n = if 1 < n then 0 else 1
   choose_n_n          |- !n. n choose n = 1
   choose_recurrence   |- !n k. (n + 1) choose (k + 1) = n choose k + n choose (k + 1)
   choose_alt          |- !n k. n choose 0 = 1 /\ 0 choose (k + 1) = 0 /\
                                (n + 1) choose (k + 1) = n choose k + n choose (k + 1)
!  choose_eqn          |- !n k. n choose k = binomial n k

   Partition of the set of subsets by bijective equivalence:
   sub_sets_def        |- !P k. sub_sets P k = {s | s SUBSET P /\ CARD s = k}
   sub_sets_sub_count  |- !n k. sub_sets (count n) k = sub_count n k
   sub_sets_equiv_class|- !s t. FINITE t /\ s SUBSET t ==>
                                sub_sets t (CARD s) = equiv_class $=b= (POW t) s
   sub_count_equiv_class
                       |- !n k. k <= n ==>
                                sub_count n k =
                                equiv_class $=b= (POW (count n)) (count k)
   count_power_partition   |- !n. partition $=b= (POW (count n)) =
                                  IMAGE (sub_count n) (upto n)
   sub_count_count_inj     |- !n m. INJ (sub_count n) (upto n)
                                        univ(:(num -> bool) -> bool)
   choose_sum_over_count   |- !n. SIGMA ($choose n) (upto n) = 2 ** n
   choose_sum_over_all     |- !n. SUM (MAP ($choose n) [0 .. n]) = 2 ** n

   Counting number of permutations:
   perm_count_def      |- !n. perm_count n = {ls | ALL_DISTINCT ls /\ set ls = count n}
   perm_def            |- !n. perm n = CARD (perm_count n)
   perm_count_element  |- !ls n. ls IN perm_count n <=> ALL_DISTINCT ls /\ set ls = count n
   perm_count_element_no_self
                       |- !ls n. ls IN perm_count n ==> ~MEM n ls
   perm_count_element_length
                       |- !ls n. ls IN perm_count n ==> LENGTH ls = n
   perm_count_subset   |- !n. perm_count n SUBSET necklace n n
   perm_count_finite   |- !n. FINITE (perm_count n)
   perm_count_0        |- perm_count 0 = {[]}
   perm_count_1        |- perm_count 1 = {[0]}
   interleave_def      |- !x ls. x interleave ls =
                                 IMAGE (\k. TAKE k ls ++ x::DROP k ls) (upto (LENGTH ls))
   interleave_alt      |- !ls x. x interleave ls =
                                 {TAKE k ls ++ x::DROP k ls | k | k <= LENGTH ls}
   interleave_element  |- !ls x y. y IN x interleave ls <=>
                               ?k. k <= LENGTH ls /\ y = TAKE k ls ++ x::DROP k ls
   interleave_nil      |- !x. x interleave [] = {[x]}
   interleave_length   |- !ls x y. y IN x interleave ls ==> LENGTH y = 1 + LENGTH ls
   interleave_distinct |- !ls x y. ALL_DISTINCT (x::ls) /\ y IN x interleave ls ==>
                                   ALL_DISTINCT y
   interleave_distinct_alt
                       |- !ls x y. ALL_DISTINCT ls /\ ~MEM x ls /\
                                   y IN x interleave ls ==> ALL_DISTINCT y
   interleave_set      |- !ls x y. y IN x interleave ls ==> set y = set (x::ls)
   interleave_set_alt  |- !ls x y. y IN x interleave ls ==> set y = x INSERT set ls
   interleave_has_cons |- !ls x. x::ls IN x interleave ls
   interleave_not_empty|- !ls x. x interleave ls <> {}
   interleave_eq       |- !n x y. ~MEM n x /\ ~MEM n y ==>
                                  (n interleave x = n interleave y <=> x = y)
   interleave_disjoint |- !l1 l2 x. ~MEM x l1 /\ l1 <> l2 ==>
                                    DISJOINT (x interleave l1) (x interleave l2)
   interleave_finite   |- !ls x. FINITE (x interleave ls)
   interleave_count_inj|- !ls x. ~MEM x ls ==>
                                INJ (\k. TAKE k ls ++ x::DROP k ls)
                                    (upto (LENGTH ls)) univ(:'a list)
   interleave_card     |- !ls x. ~MEM x ls ==> CARD (x interleave ls) = 1 + LENGTH ls
   interleave_revert   |- !ls h. ALL_DISTINCT ls /\ MEM h ls ==>
                             ?t. ALL_DISTINCT t /\ ls IN h interleave t /\
                                 set t = set ls DELETE h
   interleave_revert_count
                       |- !ls n. ALL_DISTINCT ls /\ set ls = upto n ==>
                             ?t. ALL_DISTINCT t /\ ls IN n interleave t /\
                                 set t = count n
   perm_count_suc     |- !n. perm_count (SUC n) =
                              BIGUNION (IMAGE ($interleave n) (perm_count n))
   perm_count_suc_alt |- !n. perm_count (n + 1) =
                              BIGUNION (IMAGE ($interleave n) (perm_count n))
!  perm_count_eqn     |- !n. perm_count n =
                              if n = 0 then {[]}
                              else BIGUNION (IMAGE ($interleave (n - 1)) (perm_count (n - 1)))
   perm_0              |- perm 0 = 1
   perm_1              |- perm 1 = 1
   perm_count_interleave_finite
                       |- !n e. e IN IMAGE ($interleave n) (perm_count n) ==> FINITE e
   perm_count_interleave_card
                       |- !n e. e IN IMAGE ($interleave n) (perm_count n) ==> CARD e = n + 1
   perm_count_interleave_disjoint
                       |- !n e s t. s IN IMAGE ($interleave n) (perm_count n) /\
                                    t IN IMAGE ($interleave n) (perm_count n) /\ s <> t ==>
                                    DISJOINT s t
   perm_count_interleave_inj
                       |- !n. INJ ($interleave n) (perm_count n) univ(:num list -> bool)
   perm_suc            |- !n. perm (SUC n) = SUC n * perm n
   perm_suc_alt        |- !n. perm (n + 1) = (n + 1) * perm n
!  perm_eq_fact        |- !n. perm n = FACT n

   Permutations of a set:
   perm_set_def        |- !s. perm_set s = {ls | ALL_DISTINCT ls /\ set ls = s}
   perm_set_element    |- !ls s. ls IN perm_set s <=> ALL_DISTINCT ls /\ set ls = s
   perm_set_perm_count |- !n. perm_set (count n) = perm_count n
   perm_set_empty      |- perm_set {} = {[]}
   perm_set_sing       |- !x. perm_set {x} = {[x]}
   perm_set_eq_empty_sing
                       |- !s. perm_set s = {[]} <=> s = {}
   perm_set_has_self_list
                       |- !s. FINITE s ==> SET_TO_LIST s IN perm_set s
   perm_set_not_empty  |- !s. FINITE s ==> perm_set s <> {}
   perm_set_list_not_empty
                       |- !ls. perm_set (set ls) <> {}
   perm_set_map_element|- !ls f s n. ls IN perm_set s /\ BIJ f s (count n) ==>
                                     MAP f ls IN perm_count n
   perm_set_map_inj    |- !f s n. BIJ f s (count n) ==> INJ (MAP f) (perm_set s) (perm_count n)
   perm_set_map_surj   |- !f s n. BIJ f s (count n) ==> SURJ (MAP f) (perm_set s) (perm_count n)
   perm_set_map_bij    |- !f s n. BIJ f s (count n) ==> BIJ (MAP f) (perm_set s) (perm_count n)
   perm_set_bij_eq_perm_count
                       |- !s. FINITE s ==> perm_set s =b= perm_count (CARD s)
   perm_set_finite     |- !s. FINITE s ==> FINITE (perm_set s)
   perm_set_card       |- !s. FINITE s ==> CARD (perm_set s) = perm (CARD s)
   perm_set_card_alt   |- !s. FINITE s ==> CARD (perm_set s) = FACT (CARD s)

   Counting number of arrangements:
   list_count_def      |- !n k. list_count n k =
                                {ls | ALL_DISTINCT ls /\
                                      set ls SUBSET count n /\ LENGTH ls = k}
   arrange_def         |- !n k. n arrange k = CARD (list_count n k)
   list_count_alt      |- !n k. list_count n k =
                                {ls | ALL_DISTINCT ls /\
                                      set ls SUBSET count n /\ CARD (set ls) = k}
   list_count_element  |- !ls n k. ls IN list_count n k <=>
                                   ALL_DISTINCT ls /\ set ls SUBSET count n /\ LENGTH ls = k
   list_count_element_alt
                       |- !ls n k. ls IN list_count n k <=>
                                   ALL_DISTINCT ls /\ set ls SUBSET count n /\ CARD (set ls) = k
   list_count_element_set_card
                       |- !ls n k. ls IN list_count n k ==> CARD (set ls) = k
   list_count_subset   |- !n k. list_count n k SUBSET necklace k n
   list_count_finite   |- !n k. FINITE (list_count n k)
   list_count_n_0      |- !n. list_count n 0 = {[]}
   list_count_0_n      |- !n. 0 < n ==> list_count 0 n = {}
   list_count_n_n      |- !n. list_count n n = perm_count n
   list_count_eq_empty |- !n k. list_count n k = {} <=> n < k
   list_count_by_image |- !n k. 0 < k ==>
                                list_count n k =
                                IMAGE (\ls. if ALL_DISTINCT ls then ls else [])
                                      (necklace k n) DELETE []
!  list_count_eqn      |- !n k. list_count n k =
                                if k = 0 then {[]}
                                else IMAGE (\ls. if ALL_DISTINCT ls then ls else [])
                                           (necklace k n) DELETE []
   feq_set_equiv       |- !s. feq set equiv_on s
   list_count_set_eq_class
                       |- !ls n k. ls IN list_count n k ==>
                              equiv_class (feq set) (list_count n k) ls = perm_set (set ls)
   list_count_set_eq_class_card
                       |- !ls n k. ls IN list_count n k ==>
                              CARD (equiv_class (feq set) (list_count n k) ls) = perm k
   list_count_set_partititon_element_card
                       |- !n k e. e IN partition (feq set) (list_count n k) ==> CARD e = perm k
   list_count_element_perm_set_not_empty
                       |- !ls n k. ls IN list_count n k ==> perm_set (set ls) <> {}
   list_count_set_map_element
                       |- !s n k. s IN partition (feq set) (list_count n k) ==>
                                  (set o CHOICE) s IN sub_count n k
   list_count_set_map_inj
                       |- !n k. INJ (set o CHOICE)
                                    (partition (feq set) (list_count n k))
                                    (sub_count n k)
   list_count_set_map_surj
                       |- !n k. SURJ (set o CHOICE)
                                     (partition (feq set) (list_count n k))
                                     (sub_count n k)
   list_count_set_map_bij
                       |- !n k. BIJ (set o CHOICE)
                                    (partition (feq set) (list_count n k))
                                    (sub_count n k)
!  arrange_eqn         |- !n k. n arrange k = (n choose k) * perm k
   arrange_alt         |- !n k. n arrange k = (n choose k) * FACT k
   arrange_formula     |- !n k. n arrange k = binomial n k * FACT k
   arrange_formula2    |- !n k. k <= n ==> n arrange k = FACT n DIV FACT (n - k)
   arrange_n_0         |- !n. n arrange 0 = 1
   arrange_0_n         |- !n. 0 < n ==> 0 arrange n = 0
   arrange_n_n         |- !n. n arrange n = perm n
   arrange_n_n_alt     |- !n. n arrange n = FACT n
   arrange_eq_0        |- !n k. n arrange k = 0 <=> n < k
*)

(* ------------------------------------------------------------------------- *)
(* Counting number of combinations.                                          *)
(* ------------------------------------------------------------------------- *)

(* The strategy:
This is to show, ultimately, C(n,k) = binomial n k.

Conceptually,
C(n,k) = number of ways to choose k elements from a set of n elements.
Each choice gives a k-subset.

Define C(n,k) = number of k-subsets of an n-set.
Prove that C(n,k) = binomial n k:
(1) C(0,0) = 1
(2) C(0,1) = 0
(3) C(SUC n, SUC k) = C(n,k) + C(n,SUC k)
show that any such C's is just the binomial function.

binomial_alt
|- !n k. binomial n 0 = 1 /\ binomial 0 (k + 1) = 0 /\
         binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1)

Moreover, bij_eq is an equivalence relation, and partitions the power set
of (count n) into equivalence classes of k-subsets for k = 0 to n. Thus

SUM (GENLIST (choose n) (SUC n)) = CARD (POW (count n)) = 2 ** n

the counterpart of binomial_sum |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
*)

(* Define the set of choices of k-subsets of (count n). *)
Definition sub_count_def[nocompute]:
    sub_count n k = { (s:num -> bool) | s SUBSET (count n) /\ CARD s = k}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Define the number of choices of k-subsets of (count n). *)
Definition choose_def[nocompute]:
    choose n k = CARD (sub_count n k)
End
(* use [nocompute] as this is not effective for evalutaion. *)
(* make this an infix operator *)
val _ = set_fixity "choose" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)
(* val choose_def = |- !n k. n choose k = CARD (sub_count n k): thm *)

(* Theorem: s IN sub_count n k <=> s SUBSET count n /\ CARD s = k *)
(* Proof: by sub_count_def. *)
Theorem sub_count_element:
  !n k s. s IN sub_count n k <=> s SUBSET count n /\ CARD s = k
Proof
  simp[sub_count_def]
QED

(* Theorem: (sub_count n k) SUBSET (POW (count n)) *)
(* Proof:
       s IN sub_count n k
   ==> s SUBSET (count n)                      by sub_count_def
   ==> s IN POW (count n)                      by POW_DEF
   Thus (sub_count n k) SUBSET (POW (count n)) by SUBSET_DEF
*)
Theorem sub_count_subset:
  !n k. (sub_count n k) SUBSET (POW (count n))
Proof
  simp[sub_count_def, POW_DEF, SUBSET_DEF]
QED

(* Theorem: FINITE (sub_count n k) *)
(* Proof:
   Note (sub_count n k) SUBSET (POW (count n)) by sub_count_subset
    and FINITE (count n)                       by FINITE_COUNT
     so FINITE (POW (count n))                 by FINITE_POW
   Thus FINITE (sub_count n k)                 by SUBSET_FINITE
*)
Theorem sub_count_finite:
  !n k. FINITE (sub_count n k)
Proof
  metis_tac[sub_count_subset, FINITE_COUNT, FINITE_POW, SUBSET_FINITE]
QED

(* Theorem: s IN sub_count n k ==> n NOTIN s *)
(* Proof:
   Note s SUBSET (count n)     by sub_count_element
    and n NOTIN (count n)      by COUNT_NOT_SELF
     so n NOTIN s              by SUBSET_DEF
*)
Theorem sub_count_element_no_self:
  !n k s. s IN sub_count n k ==> n NOTIN s
Proof
  metis_tac[sub_count_element, SUBSET_DEF, COUNT_NOT_SELF]
QED

(* Theorem: s IN sub_count n k ==> FINITE s *)
(* Proof:
   Note s SUBSET (count n)     by sub_count_element
    and FINITE (count n)       by FINITE_COUNT
     so FINITE s               by SUBSET_FINITE
*)
Theorem sub_count_element_finite:
  !n k s. s IN sub_count n k ==> FINITE s
Proof
  metis_tac[sub_count_element, FINITE_COUNT, SUBSET_FINITE]
QED

(* Theorem: sub_count n 0 = { EMPTY } *)
(* Proof:
   By EXTENSION, IN_SING, this is to show:
   (1) x IN sub_count n 0 ==> x = {}
           x IN sub_count n 0
       <=> x SUBSET count n /\ CARD x = 0      by sub_count_def
       ==> FINITE x /\ CARD x = 0              by SUBSET_FINITE, FINITE_COUNT
       ==> x = {}                              by CARD_EQ_0
   (2) {} IN sub_count n 0
           {} IN sub_count n 0
       <=> {} SUBSET count n /\ CARD {} = 0    by sub_count_def
       <=> T /\ CARD {} = 0                    by EMPTY_SUBSET
       <=> T /\ T                              by CARD_EMPTY
       <=> T
*)
Theorem sub_count_n_0:
  !n. sub_count n 0 = { EMPTY }
Proof
  rewrite_tac[EXTENSION, EQ_IMP_THM] >>
  rw[IN_SING] >| [
    fs[sub_count_def] >>
    metis_tac[CARD_EQ_0, SUBSET_FINITE, FINITE_COUNT],
    rw[sub_count_def]
  ]
QED

(* Theorem: sub_count 0 n = if n = 0 then { EMPTY } else EMPTY *)
(* Proof:
   If n = 0,
      then sub_count 0 n = { EMPTY }     by sub_count_n_0
   If n <> 0,
          s IN sub_count 0 n
      <=> s SUBSET count 0 /\ CARD s = n by sub_count_def
      <=> s SUBSET {} /\ CARD s = n      by COUNT_0
      <=> CARD {} = n                    by SUBSET_EMPTY
      <=> 0 = n                          by CARD_EMPTY
      <=> F                              by n <> 0
      Thus sub_count 0 n = {}            by MEMBER_NOT_EMPTY
*)
Theorem sub_count_0_n:
  !n. sub_count 0 n = if n = 0 then { EMPTY } else EMPTY
Proof
  rw[sub_count_n_0] >>
  rw[sub_count_def, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `x = {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  fs[]
QED

(* Theorem: sub_count n 1 = {{j} | j < n } *)
(* Proof:
   By sub_count_def, EXTENSION, this is to show:
      x SUBSET count n /\ CARD x = 1 <=>
      ?j. (!x'. x' IN x <=> x' = j) /\ j < n
   If part:
      Note FINITE x            by SUBSET_FINITE, FINITE_COUNT
        so ?j. x = {j}         by CARD_EQ_1, SING_DEF
      Take this j.
      Then !x'. x' IN x <=> x' = j
                               by IN_SING
       and x SUBSET (count n) ==> j < n
                               by SUBSET_DEF, IN_COUNT
   Only-if part:
      Note j IN x, so x <> {}  by MEMBER_NOT_EMPTY
      The given shows x = {j}  by ONE_ELEMENT_SING
      and j < n ==> x SUBSET (count n)
                               by SUBSET_DEF, IN_COUNT
      and CARD x = 1           by CARD_SING
*)
Theorem sub_count_n_1:
  !n. sub_count n 1 = {{j} | j < n }
Proof
  rw[sub_count_def, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    `FINITE x` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    `?j. x = {j}` by metis_tac[CARD_EQ_1, SING_DEF] >>
    metis_tac[SUBSET_DEF, IN_SING, IN_COUNT],
    rw[SUBSET_DEF],
    metis_tac[ONE_ELEMENT_SING, MEMBER_NOT_EMPTY, CARD_SING]
  ]
QED

(* Theorem: sub_count n n = {count n} *)
(* Proof:
       s IN sub_count n n
   <=> s SUBSET count n /\ CARD s = n    by sub_count_def
   <=> s SUBSET count n /\ CARD s = CARD (count n)
                                         by CARD_COUNT
   <=> s SUBSET count n /\ s = count n   by SUBSET_CARD_EQ
   <=> T /\ s = count n                  by SUBSET_REFL
   Thus sub_count n n = {count n}        by EXTENSION
*)
Theorem sub_count_n_n:
  !n. sub_count n n = {count n}
Proof
  rw_tac bool_ss[EXTENSION] >>
  `FINITE (count n) /\ CARD (count n) = n` by rw[] >>
  metis_tac[sub_count_element, SUBSET_CARD_EQ, SUBSET_REFL, IN_SING]
QED

(* Theorem: sub_count n k = EMPTY <=> n < k *)
(* Proof:
   If part: sub_count n k = {} ==> n < k
      By contradiction, suppose k <= n.
      Then (count k) SUBSET (count n)    by COUNT_SUBSET, k <= n
       and CARD (count k) = k            by CARD_COUNT
        so (count k) IN sub_count n k    by sub_count_element
      Thus sub_count n k <> {}           by MEMBER_NOT_EMPTY
      which is a contradiction.
   Only-if part: n < k ==> sub_count n k = {}
      By contradiction, suppose sub_count n k <> {}.
      Then ?s. s IN sub_count n k        by MEMBER_NOT_EMPTY
       ==> s SUBSET count n /\ CARD s = k
                                         by sub_count_element
      Note FINITE (count n)              by FINITE_COUNT
        so CARD s <= CARD (count n)      by CARD_SUBSET
       ==> k <= n                        by CARD_COUNT
       This contradicts n < k.
*)
Theorem sub_count_eq_empty:
  !n k. sub_count n k = EMPTY <=> n < k
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(count k) SUBSET (count n)` by rw[COUNT_SUBSET] >>
    `CARD (count k) = k` by rw[] >>
    metis_tac[sub_count_element, MEMBER_NOT_EMPTY],
    spose_not_then strip_assume_tac >>
    `?s. s IN sub_count n k` by rw[MEMBER_NOT_EMPTY] >>
    fs[sub_count_element] >>
    `FINITE (count n)` by rw[] >>
    `CARD s <= n` by metis_tac[CARD_SUBSET, CARD_COUNT] >>
    decide_tac
  ]
QED

(* Theorem: sub_count (n + 1) (k + 1) =
            IMAGE (\s. n INSERT s) (sub_count n k) UNION sub_count n (k + 1) *)
(* Proof:
   By sub_count_def, EXTENSION, this is to show:
   (1) x SUBSET count (n + 1) /\ CARD x = k + 1 ==>
       ?s. (!y. y IN x <=> y = n \/ y IN s) /\
            s SUBSET count n /\ CARD s = k) \/ x SUBSET count n
       Suppose ~(x SUBSET count n),
       Then n IN x             by SUBSET_DEF
       Take s = x DELETE n.
       Then y IN x <=>
            y = n \/ y IN s    by EXTENSION
        and s SUBSET x         by DELETE_SUBSET
         so s SUBSET (count (n + 1) DELETE n)
                               by SUBSET_DELETE_BOTH
         or s SUBSET (count n) by count_def
       Note FINITE x           by SUBSET_FINITE, FINITE_COUNT
         so CARD s = k         by CARD_DELETE, CARD_COUNT
   (2) s SUBSET count n /\ x = n INSERT s ==> x SUBSET count (n + 1)
       Note x SUBSET (n INSERT count n)  by SUBSET_INSERT_BOTH
         so x INSERT count (n + 1)       by count_def, or count_add1
   (3) s SUBSET count n /\ x = n INSERT s ==> CARD x = CARD s + 1
       Note n NOTIN s          by SUBSET_DEF, COUNT_NOT_SELF
        and FINITE s           by SUBSET_FINITE, FINITE_COUNT
         so CARD x
          = SUC (CARD s)       by CARD_INSERT
          = CARD s + 1         by ADD1
   (4) x SUBSET count n ==> x SUBSET count (n + 1)
       Note (count n) SUBSET count (n + 1)  by COUNT_SUBSET, n <= n + 1
         so x SUBSET count (n + 1)          by SUBSET_TRANS
*)
Theorem sub_count_union:
  !n k. sub_count (n + 1) (k + 1) =
        IMAGE (\s. n INSERT s) (sub_count n k) UNION sub_count n (k + 1)
Proof
  rw[sub_count_def, EXTENSION, Once EQ_IMP_THM] >> simp[] >| [
    rename [‘x ⊆ count (n + 1)’, ‘CARD x = k + 1’] >>
    Cases_on `x SUBSET count n` >> simp[] >>
    `n IN x` by
      (fs[SUBSET_DEF] >> rename [‘m ∈ x’, ‘¬(m < n)’] >>
       `m < n + 1` by simp[] >>
       `m = n` by decide_tac >>
       fs[]) >>
    qexists_tac `x DELETE n` >>
    `FINITE x` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    rw[] >- (rw[EQ_IMP_THM] >> simp[]) >>
    `x DELETE n SUBSET (count (n + 1)) DELETE n` by rw[SUBSET_DELETE_BOTH] >>
    `count (n + 1) DELETE n = count n` by rw[EXTENSION] >>
    fs[],

    rename [‘s ⊆ count n’, ‘x ⊆ count (n + 1)’] >>
    `x = n INSERT s` by fs[EXTENSION] >>
    `x SUBSET (n INSERT count n)` by rw[SUBSET_INSERT_BOTH] >>
    rfs[count_add1],

    rename [‘s ⊆ count n’, ‘CARD x = CARD s + 1’] >>
    `x = n INSERT s` by fs[EXTENSION] >>
    `n NOTIN s` by metis_tac[SUBSET_DEF, COUNT_NOT_SELF] >>
    `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    rw[],

    metis_tac[COUNT_SUBSET, SUBSET_TRANS, DECIDE “n ≤ n + 1”]
  ]
QED

(* Theorem: DISJOINT (IMAGE (\s. n INSERT s) (sub_count n k)) (sub_count n (k + 1)) *)
(* Proof:
   Let s = IMAGE (\s. n INSERT s) (sub_count n k),
       t = sub_count n (k + 1).
   By DISJOINT_DEF and contradiction, suppose s INTER t <> {}.
   Then ?x. x IN s /\ x IN t       by IN_INTER, MEMBER_NOT_EMPTY
   Note n IN x                     by IN_IMAGE, IN_INSERT
    but n NOTIN x                  by sub_count_element_no_self
   This is a contradiction.
*)
Theorem sub_count_disjoint:
  !n k. DISJOINT (IMAGE (\s. n INSERT s) (sub_count n k)) (sub_count n (k + 1))
Proof
  rw[DISJOINT_DEF, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  rename [‘s ∈ sub_count n k’, ‘x ∈ sub_count n (k + 1)’] >>
  `x = n INSERT s` by fs[EXTENSION] >>
  `n IN x` by fs[] >>
  metis_tac[sub_count_element_no_self]
QED

(* Theorem: s IN sub_count n k ==> (n INSERT s) IN sub_count (n + 1) (k + 1) *)
(* Proof:
   Note s SUBSET count n /\ CARD s = k       by sub_count_element
    and n NOTIN s                            by sub_count_element_no_self
    and FINITE s                             by sub_count_element_finite
    Now (n INSERT s) SUBSET (n INSERT count n)
                                             by SUBSET_INSERT_BOTH
    and n INSERT count n = count (n + 1)     by count_add1
    and CARD (n INSERT s) = CARD s + 1       by CARD_INSERT
                          = k + 1            by given
   Thus (n INSERT s) IN sub_count (n + 1) (k + 1)
                                             by sub_count_element
*)
Theorem sub_count_insert:
  !n k s. s IN sub_count n k ==> (n INSERT s) IN sub_count (n + 1) (k + 1)
Proof
  rw[sub_count_def] >| [
    `!x. x < n ==> x < n + 1` by decide_tac >>
    metis_tac[SUBSET_DEF, IN_COUNT],
    `n NOTIN s` by metis_tac[SUBSET_DEF, COUNT_NOT_SELF] >>
    `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    rw[]
  ]
QED

(* Theorem: CARD (IMAGE (\s. n INSERT s) (sub_count n k)) = n choose k *)
(* Proof:
   Let f = \s. n INSERT s.
   By choose_def, INJ_CARD_IMAGE, this is to show:
   (1) FINITE (sub_count n k), true      by sub_count_finite
   (2) ?t. INJ f (sub_count n k) t
       Let t = sub_count (n + 1) (k + 1).
       By INJ_DEF, this is to show:
       (1) s IN sub_count n k ==> n INSERT s IN sub_count (n + 1) (k + 1)
           This is true                  by sub_count_insert
       (2) s' IN sub_count n k /\ s IN sub_count n k /\
           n INSERT s' = n INSERT s ==> s' = s
           Note n NOTIN s                by sub_count_element_no_self
            and n NOTIN s'               by sub_count_element_no_self
             s'
           = s' DELETE n                 by DELETE_NON_ELEMENT
           = (n INSERT s') DELETE n      by DELETE_INSERT
           = (n INSERT s) DELETE n       by given
           = s DELETE n                  by DELETE_INSERT
           = s                           by DELETE_NON_ELEMENT
*)
Theorem sub_count_insert_card:
  !n k. CARD (IMAGE (\s. n INSERT s) (sub_count n k)) = n choose k
Proof
  rw[choose_def] >>
  qabbrev_tac `f = \s. n INSERT s` >>
  irule INJ_CARD_IMAGE >>
  rpt strip_tac >-
  rw[sub_count_finite] >>
  qexists_tac `sub_count (n + 1) (k + 1)` >>
  rw[INJ_DEF, Abbr`f`] >-
  rw[sub_count_insert] >>
  rename [‘n INSERT s1 = n INSERT s2’] >>
  `n NOTIN s1 /\ n NOTIN s2` by metis_tac[sub_count_element_no_self] >>
  metis_tac[DELETE_INSERT, DELETE_NON_ELEMENT]
QED

(* Theorem: sub_count n 0 = { EMPTY } /\
            sub_count 0 (k + 1) = {} /\
            sub_count (n + 1) (k + 1) =
            IMAGE (\s. n INSERT s) (sub_count n k) UNION sub_count n (k + 1) *)
(* Proof: by sub_count_n_0, sub_count_0_n, sub_count_union. *)
Theorem sub_count_alt:
  !n k. sub_count n 0 = { EMPTY } /\
        sub_count 0 (k + 1) = {} /\
        sub_count (n + 1) (k + 1) =
        IMAGE (\s. n INSERT s) (sub_count n k) UNION sub_count n (k + 1)
Proof
  simp[sub_count_n_0, sub_count_0_n, sub_count_union]
QED

(* Theorem: sub_count n k =
            if k = 0 then { EMPTY }
            else if n = 0 then {}
            else IMAGE (\s. (n - 1) INSERT s) (sub_count (n - 1) (k - 1)) UNION
                 sub_count (n - 1) k *)
(* Proof: by sub_count_n_0, sub_count_0_n, sub_count_union. *)
Theorem sub_count_eqn[compute]:
  !n k. sub_count n k =
        if k = 0 then { EMPTY }
        else if n = 0 then {}
        else IMAGE (\s. (n - 1) INSERT s) (sub_count (n - 1) (k - 1)) UNION
             sub_count (n - 1) k
Proof
  rw[sub_count_n_0, sub_count_0_n] >>
  metis_tac[sub_count_union, num_CASES, SUC_SUB1, ADD1]
QED

(*
> EVAL ``sub_count 3 2``;
val it = |- sub_count 3 2 = {{2; 1}; {2; 0}; {1; 0}}: thm
> EVAL ``sub_count 4 2``;
val it = |- sub_count 4 2 = {{3; 2}; {3; 1}; {3; 0}; {2; 1}; {2; 0}; {1; 0}}: thm
> EVAL ``sub_count 3 3``;
val it = |- sub_count 3 3 = {{2; 1; 0}}: thm
*)

(* Theorem: n choose 0 = 1 *)
(* Proof:
     n choose 0
   = CARD (sub_count n 0)      by choose_def
   = CARD {{}}                 by sub_count_n_0
   = 1                         by CARD_SING
*)
Theorem choose_n_0:
  !n. n choose 0 = 1
Proof
  simp[choose_def, sub_count_n_0]
QED

(* Theorem: n choose 1 = n *)
(* Proof:
   Let s = {{j} | j < n},
       f = \j. {j}.
   Then s = IMAGE f (count n)    by EXTENSION
   Note FINITE (count n)
    and INJ f (count n) (POW (count n))
   Thus n choose 1
      = CARD (sub_count n 1)     by choose_def
      = CARD s                   by sub_count_n_1
      = CARD (count n)           by INJ_CARD_IMAGE
      = n                        by CARD_COUNT
*)
Theorem choose_n_1:
  !n. n choose 1 = n
Proof
  rw[choose_def, sub_count_n_1] >>
  qabbrev_tac `s = {{j} | j < n}` >>
  qabbrev_tac `f = \j:num. {j}` >>
  `s = IMAGE f (count n)` by fs[EXTENSION, Abbr`f`, Abbr`s`] >>
  `CARD (IMAGE f (count n)) = CARD (count n)` suffices_by fs[] >>
  irule INJ_CARD_IMAGE >>
  rw[] >>
  qexists_tac `POW (count n)` >>
  rw[INJ_DEF, Abbr`f`] >>
  rw[POW_DEF]
QED

(* Theorem: n choose k = 0 <=> n < k *)
(* Proof:
   Note FINITE (sub_count n k)     by sub_count_finite
        n choose k = 0
    <=> CARD (sub_count n k) = 0   by choose_def
    <=> sub_count n k = {}         by CARD_EQ_0
    <=> n < k                      by sub_count_eq_empty
*)
Theorem choose_eq_0:
  !n k. n choose k = 0 <=> n < k
Proof
  metis_tac[choose_def, sub_count_eq_empty, sub_count_finite, CARD_EQ_0]
QED

(* Theorem: 0 choose n = if n = 0 then 1 else 0 *)
(* Proof:
     0 choose n
   = CARD (sub_count 0 n)      by choose_def
   = CARD (if n = 0 then {{}} else {})
                               by sub_count_0_n
   = if n = 0 then 1 else 0    by CARD_SING, CARD_EMPTY
*)
Theorem choose_0_n:
  !n. 0 choose n = if n = 0 then 1 else 0
Proof
  rw[choose_def, sub_count_0_n]
QED

(* Theorem: 1 choose n = if 1 < n then 0 else 1 *)
(* Proof:
   If n = 0, 1 choose 0 = 1     by choose_n_0
   If n = 1, 1 choose 1 = 1     by choose_n_1
   Otherwise, 1 choose n = 0    by choose_eq_0, 1 < n
*)
Theorem choose_1_n:
  !n. 1 choose n = if 1 < n then 0 else 1
Proof
  rw[choose_eq_0] >>
  `n = 0 \/ n = 1` by decide_tac >-
  simp[choose_n_0] >>
  simp[choose_n_1]
QED

(* Theorem: n choose n = 1 *)
(* Proof:
     n choose n
   = CARD (sub_count n n)      by choose_def
   = CARD {count n}            by sub_count_n_n
   = 1                         by CARD_SING
*)
Theorem choose_n_n:
  !n. n choose n = 1
Proof
  simp[choose_def, sub_count_n_n]
QED

(* Theorem: (n + 1) choose (k + 1) = n choose k + n choose (k + 1) *)
(* Proof:
   Let s = sub_count (n + 1) (k + 1),
       u = sub_count n k,
       v = sub_count n (k + 1),
       t = IMAGE (\s. n INSERT s) u.
   Then s = t UNION v              by sub_count_union
    and DISJOINT t v               by sub_count_disjoint
    and FINITE u /\ FINITE v       by sub_count_finite
    and FINITE t                   by IMAGE_FINITE
   Thus CARD s = CARD t + CARD v   by CARD_UNION_DISJOINT
               = CARD u + CARD v   by sub_count_insert_card, choose_def
*)
Theorem choose_recurrence:
  !n k. (n + 1) choose (k + 1) = n choose k + n choose (k + 1)
Proof
  rw[choose_def] >>
  qabbrev_tac `s = sub_count (n + 1) (k + 1)` >>
  qabbrev_tac `u = sub_count n k` >>
  qabbrev_tac `v = sub_count n (k + 1)` >>
  qabbrev_tac `t = IMAGE (\s. n INSERT s) u` >>
  `s = t UNION v` by rw[sub_count_union, Abbr`s`, Abbr`t`, Abbr`v`] >>
  `DISJOINT t v` by metis_tac[sub_count_disjoint] >>
  `FINITE u /\ FINITE v` by rw[sub_count_finite, Abbr`u`, Abbr`v`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `CARD s = CARD t + CARD v` by rw[CARD_UNION_DISJOINT] >>
  metis_tac[sub_count_insert_card, choose_def]
QED

(* This is Pascal's identity: C(n+1,k+1) = C(n,k) + C(n,k+1). *)
(* This corresponds to the 'sum of parents' rule of Pascal's triangle. *)

(* Theorem: n choose 0 = 1 /\ 0 choose (k + 1) = 0 /\
            (n + 1) choose (k + 1) = n choose k + n choose (k + 1) *)
(* Proof: by choose_n_0, choose_0_n, choose_recurrence. *)
Theorem choose_alt:
  !n k. n choose 0 = 1 /\ 0 choose (k + 1) = 0 /\
        (n + 1) choose (k + 1) = n choose k + n choose (k + 1)
Proof
  simp[choose_n_0, choose_0_n, choose_recurrence]
QED

(* Theorem: n choose k = binomial n k *)
(* Proof: by binomial_iff, choose_alt. *)
Theorem choose_eqn[compute]:
  !n k. n choose k = binomial n k
Proof
  prove_tac[binomial_iff, choose_alt]
QED

(*
> EVAL ``5 choose 3``;
val it = |- 5 choose 3 = 10: thm
> EVAL ``MAP ($choose 5) [0 .. 5]``;
val it = |- MAP ($choose 5) [0 .. 5] = [1; 5; 10; 10; 5; 1]: thm
*)

(* ------------------------------------------------------------------------- *)
(* Partition of the set of subsets by bijective equivalence.                 *)
(* ------------------------------------------------------------------------- *)

(* Define the set of k-subsets of a set. *)
Definition sub_sets_def[nocompute]:
    sub_sets P k = { s | s SUBSET P /\ CARD s = k}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: s IN sub_sets P k <=> s SUBSET P /\ CARD s = k *)
(* Proof: by sub_sets_def. *)
Theorem sub_sets_element:
  !P k s. s IN sub_sets P k <=> s SUBSET P /\ CARD s = k
Proof
  simp[sub_sets_def]
QED

(* Theorem: sub_sets (count n) k = sub_count n k *)
(* Proof:
     sub_sets (count n) k
   = {s | s SUBSET (count n) /\ CARD s = k}    by sub_sets_def
   = sub_count n k                             by sub_count_def
*)
Theorem sub_sets_sub_count:
  !n k. sub_sets (count n) k = sub_count n k
Proof
  simp[sub_sets_def, sub_count_def]
QED

(* Theorem: FINITE t /\ s SUBSET t ==>
            sub_sets t (CARD s) = equiv_class $=b= (POW t) s *)
(* Proof:
       x IN sub_sets t (CARD s)
   <=> x SUBSET t /\ CARD s = CARD x     by sub_sets_element
   <=> x SUBSET t /\ s =b= x             by bij_eq_card_eq, SUBSET_FINITE
   <=> x IN POW t /\ s =b= x             by IN_POW
   <=> x IN equiv_class $=b= (POW t) s   by equiv_class_element
*)
Theorem sub_sets_equiv_class:
  !s t. FINITE t /\ s SUBSET t ==>
        sub_sets t (CARD s) = equiv_class $=b= (POW t) s
Proof
  rw[sub_sets_def, IN_POW, EXTENSION] >>
  metis_tac[bij_eq_card_eq, SUBSET_FINITE]
QED

(* Theorem: s SUBSET (count n) ==>
            sub_count n (CARD s) = equiv_class $=b= (POW (count n)) s *)
(* Proof:
   Note FINITE (count n)             by FINITE_COUNT
        sub_count n (CARD s)
      = sub_sets (count n) (CARD s)  by sub_sets_sub_count
      = equiv_class $=b= (POW t) s   by sub_sets_equiv_class
*)
Theorem sub_count_equiv_class:
  !n s. s SUBSET (count n) ==>
        sub_count n (CARD s) = equiv_class $=b= (POW (count n)) s
Proof
  simp[sub_sets_equiv_class, GSYM sub_sets_sub_count]
QED

(* Theorem: partition $=b= (POW (count n)) = IMAGE (sub_count n) (upto n) *)
(* Proof:
   Let R = $=b=, t = count n.
   Note CARD t = n                             by CARD_COUNT
   By EXTENSION and LESS_EQ_IFF_LESS_SUC, this is to show:
   (1) x IN partition R (POW t) ==> ?k. x = sub_count n k /\ k <= n
       Note ?s. s IN POW t /\
                x = equiv_class R (POW t) s    by partition_element
       Note FINITE t                           by SUBSET_FINITE
        and s SUBSET t                         by IN_POW
         so CARD s <= CARD t = n               by CARD_SUBSET
       Take k = CARD s.
       Then k <= n /\ x = sub_count n k        by sub_count_equiv_class
   (2) k <= n ==> sub_count n k IN partition R (POW t)
       Let s = count k
       Then CARD s = k                         by CARD_COUNT
        and s SUBSET t                         by COUNT_SUBSET, k <= n
         so s IN POW t                         by IN_POW
        Now sub_count n k
          = equiv_class R (POW t) s            by sub_count_equiv_class
        ==> sub_count n k IN partition R (POW t)
                                               by partition_element
*)
Theorem count_power_partition:
  !n. partition $=b= (POW (count n)) = IMAGE (sub_count n) (upto n)
Proof
  rpt strip_tac >>
  qabbrev_tac `R = \(s:num -> bool) (t:num -> bool). s =b= t` >>
  qabbrev_tac `t = count n` >>
  rw[Once EXTENSION, partition_element, GSYM LESS_EQ_IFF_LESS_SUC, EQ_IMP_THM] >| [
    `FINITE t` by rw[Abbr`t`] >>
    `x' SUBSET t` by fs[IN_POW] >>
    `CARD x' <= n` by metis_tac[CARD_SUBSET, CARD_COUNT] >>
    qexists_tac `CARD x'` >>
    simp[sub_count_equiv_class, Abbr`R`, Abbr`t`],
    qexists_tac `count x'` >>
    `(count x') SUBSET t /\ (count x') IN POW t` by metis_tac[COUNT_SUBSET, IN_POW] >>
    simp[] >>
    qabbrev_tac `s = count x'` >>
    `sub_count n (CARD s) = equiv_class R (POW t) s` suffices_by simp[Abbr`s`] >>
    simp[sub_count_equiv_class, Abbr`R`, Abbr`t`]
  ]
QED

(* Theorem: INJ (sub_count n) (upto n) univ(:(num -> bool) -> bool) *)
(* Proof:
   By INJ_DEF, this is to show:
      !x y. x < SUC n /\ y < SUC n /\ sub_count n x = sub_count n y ==> x = y
   Let s = count x.
   Note x < SUC n <=> x <= n   by arithmetic
    ==> s SUBSET (count n)     by COUNT_SUBSET, x <= n
    and CARD s = x             by CARD_COUNT
     so s IN sub_count n x     by sub_count_element
   Thus s IN sub_count n y     by given, sub_count n x = sub_count n y
    ==> CARD s = x = y
*)
Theorem sub_count_count_inj:
  !n m. INJ (sub_count n) (upto n) univ(:(num -> bool) -> bool)
Proof
  rw[sub_count_def, EXTENSION, INJ_DEF] >>
  `(count x) SUBSET (count n)` by rw[COUNT_SUBSET] >>
  metis_tac[CARD_COUNT]
QED

(* Idea: the sum of sizes of equivalence classes gives size of power set. *)

(* Theorem: SIGMA ($choose n) (upto n) = 2 ** n *)
(* Proof:
   Let R = $=b=, t = count n.
   Then R equiv_on (POW t)         by bij_eq_equiv_on
    and FINITE t                   by FINITE_COUNT
     so FINITE (POW t)             by FINITE_POW
   Thus CARD (POW t) = SIGMA CARD (partition R (POW t))
                                   by partition_CARD
   LHS = CARD (POW t)
       = 2 ** CARD t               by CARD_POW
       = 2 ** n                    by CARD_COUNT
   Note INJ (sub_count n) (upto n) univ            by sub_count_count_inj
   RHS = SIGMA CARD (partition R (POW t))
       = SIGMA CARD (IMAGE (sub_count n) (upto n)) by count_power_partition
       = SIGMA (CARD o sub_count n) (upto n)       by SUM_IMAGE_INJ_o
       = SIGMA ($choose n) (upto n)                by FUN_EQ_THM, choose_def
*)
Theorem choose_sum_over_count:
  !n. SIGMA ($choose n) (upto n) = 2 ** n
Proof
  rpt strip_tac >>
  qabbrev_tac `R = \(s:num -> bool) (t:num -> bool). s =b= t` >>
  qabbrev_tac `t = count n` >>
  `R equiv_on (POW t)` by rw[bij_eq_equiv_on, Abbr`R`] >>
  `FINITE (POW t)` by rw[FINITE_POW, Abbr`t`] >>
  imp_res_tac partition_CARD >>
  `FINITE (upto n)` by rw[] >>
  `SIGMA CARD (partition R (POW t)) = SIGMA CARD (IMAGE (sub_count n) (upto n))` by fs[count_power_partition, Abbr`R`, Abbr`t`] >>
  `_ = SIGMA (CARD o (sub_count n)) (upto n)` by rw[SUM_IMAGE_INJ_o, sub_count_count_inj] >>
  `_ = SIGMA ($choose n) (upto n)` by rw[choose_def, FUN_EQ_THM, SIGMA_CONG] >>
  fs[CARD_POW, Abbr`t`]
QED

(* This corresponds to:
> binomial_sum;
val it = |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n: thm
*)

(* Theorem: SUM (MAP ($choose n) [0 .. n]) = 2 ** n *)
(* Proof:
     SUM (MAP ($choose n) [0 .. n])
  = SIGMA ($choose n) (upto n)     by SUM_IMAGE_upto
  = 2 ** n                         by choose_sum_over_count
*)
Theorem choose_sum_over_all:
  !n. SUM (MAP ($choose n) [0 .. n]) = 2 ** n
Proof
  simp[GSYM SUM_IMAGE_upto, choose_sum_over_count]
QED

(* A better representation of:
> binomial_sum;
val it = |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n: thm
*)

(* ------------------------------------------------------------------------- *)
(* Counting number of permutations.                                          *)
(* ------------------------------------------------------------------------- *)

(* Define the set of permutation tuples of (count n). *)
Definition perm_count_def[nocompute]:
    perm_count n = { ls | ALL_DISTINCT ls /\ set ls = count n}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Define the number of choices of k-tuples of (count n). *)
Definition perm_def[nocompute]:
    perm n = CARD (perm_count n)
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: ls IN perm_count n <=> ALL_DISTINCT ls /\ set ls = count n *)
(* Proof: by perm_count_def. *)
Theorem perm_count_element:
  !ls n. ls IN perm_count n <=> ALL_DISTINCT ls /\ set ls = count n
Proof
  simp[perm_count_def]
QED

(* Theorem: ls IN perm_count n ==> ~MEM n ls *)
(* Proof:
       ls IN perm_count n
   <=> ALL_DISTINCT ls /\ set ls = count n    by perm_count_element
   ==> ~MEM n ls                              by COUNT_NOT_SELF
*)
Theorem perm_count_element_no_self:
  !ls n. ls IN perm_count n ==> ~MEM n ls
Proof
  simp[perm_count_element]
QED

(* Theorem: ls IN perm_count n ==> LENGTH ls = n *)
(* Proof:
       ls IN perm_count n
   <=> ALL_DISTINCT ls /\ set ls = count n     by perm_count_element
       LENGTH ls = CARD (set ls)               by ALL_DISTINCT_CARD_LIST_TO_SET
                 = CARD (count n)              by set ls = count n
                 = n                           by CARD_COUNT
*)
Theorem perm_count_element_length:
  !ls n. ls IN perm_count n ==> LENGTH ls = n
Proof
  metis_tac[perm_count_element, ALL_DISTINCT_CARD_LIST_TO_SET, CARD_COUNT]
QED

(* Theorem: perm_count n SUBSET necklace n n *)
(* Proof:
       ls IN perm_count n
   <=> ALL_DISTINCT ls /\ set ls = count n     by perm_count_element
   Thus set ls SUBSET (count n)                by SUBSET_REFL
    and LENGTH ls = n                          by perm_count_element_length
   Therefore ls IN necklace n n                by necklace_element
*)
Theorem perm_count_subset:
  !n. perm_count n SUBSET necklace n n
Proof
  rw[perm_count_def, necklace_def, perm_count_element_length, SUBSET_DEF]
QED

(* Theorem: FINITE (perm_count n) *)
(* Proof:
   Note perm_count n SUBSET necklace n n by perm_count_subset
    and FINITE (necklace n n)            by necklace_finite
   Thus FINITE (perm_count n)            by SUBSET_FINITE
*)
Theorem perm_count_finite:
  !n. FINITE (perm_count n)
Proof
  metis_tac[perm_count_subset, necklace_finite, SUBSET_FINITE]
QED

(* Theorem: perm_count 0 = {[]} *)
(* Proof:
       ls IN perm_count 0
   <=> ALL_DISTINCT ls /\ set ls = count 0     by perm_count_element
   <=> ALL_DISTINCT ls /\ set ls = {}          by COUNT_0
   <=> ALL_DISTINCT ls /\ ls = []              by LIST_TO_SET_EQ_EMPTY
   <=> ls = []                                 by ALL_DISTINCT
   Thus perm_count 0 = {[]}                    by EXTENSION
*)
Theorem perm_count_0:
  perm_count 0 = {[]}
Proof
  rw[perm_count_def, EXTENSION, EQ_IMP_THM] >>
  metis_tac[MEM, list_CASES]
QED

(* Theorem: perm_count 1 = {[0]} *)
(* Proof:
       ls IN perm_count 1
   <=> ALL_DISTINCT ls /\ set ls = count 1     by perm_count_element
   <=> ALL_DISTINCT ls /\ set ls = {0}         by COUNT_1
   <=> ls = [0]                                by DISTINCT_LIST_TO_SET_EQ_SING
   Thus perm_count 1 = {[0]}                   by EXTENSION
*)
Theorem perm_count_1:
  perm_count 1 = {[0]}
Proof
  simp[perm_count_def, COUNT_1, DISTINCT_LIST_TO_SET_EQ_SING]
QED

(* Define the interleave operation on a list. *)
Definition interleave_def:
    interleave x ls = IMAGE (\k. TAKE k ls ++ x::DROP k ls) (upto (LENGTH ls))
End
(* make this an infix operator *)
val _ = set_fixity "interleave" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)
(* interleave_def;
val it = |- !x ls. x interleave ls =
                   IMAGE (\k. TAKE k ls ++ x::DROP k ls) (upto (LENGTH ls)): thm *)

(*
> EVAL ``2 interleave [0; 1]``;
val it = |- 2 interleave [0; 1] = {[0; 1; 2]; [0; 2; 1]; [2; 0; 1]}: thm
*)

(* Theorem: x interleave ls = {TAKE k ls ++ x::DROP k ls | k | k <= LENGTH ls} *)
(* Proof: by interleave_def, EXTENSION. *)
Theorem interleave_alt:
  !ls x. x interleave ls = {TAKE k ls ++ x::DROP k ls | k | k <= LENGTH ls}
Proof
  simp[interleave_def, EXTENSION] >>
  metis_tac[LESS_EQ_IFF_LESS_SUC]
QED

(* Theorem: y IN x interleave ls <=>
           ?k. k <= LENGTH ls /\ y = TAKE k ls ++ x::DROP k ls *)
(* Proof: by interleave_alt, IN_IMAGE. *)
Theorem interleave_element:
  !ls x y. y IN x interleave ls <=>
        ?k. k <= LENGTH ls /\ y = TAKE k ls ++ x::DROP k ls
Proof
  simp[interleave_alt] >>
  metis_tac[]
QED

(* Theorem: x interleave [] = {[x]} *)
(* Proof:
     x interleave []
   = IMAGE (\k. TAKE k [] ++ x::DROP k []) (upto (LENGTH []))
                                         by interleave_def
   = IMAGE (\k. [] ++ x::[]) (upto 0)    by TAKE_nil, DROP_nil, LENGTH
   = IMAGE (\k. [x]) (count 1)           by APPEND, notation of upto
   = IMAGE (\k. [x]) {0}                 by COUNT_1
   = [x]                                 by IMAGE_DEF
*)
Theorem interleave_nil:
  !x. x interleave [] = {[x]}
Proof
  rw[interleave_def, EXTENSION] >>
  metis_tac[DECIDE``0 < 1``]
QED

(* Theorem: y IN (x interleave ls) ==> LENGTH y = 1 + LENGTH ls *)
(* Proof:
     LENGTH y
   = LENGTH (TAKE k ls ++ x::DROP k ls)            by interleave_element, for some k
   = LENGTH (TAKE k ls) + LENGTH (x::DROP k ls)    by LENGTH_APPEND
   = k + LENGTH (x :: DROP k ls)                   by LENGTH_TAKE, k <= LENGTH ls
   = k + (1 + LENGTH (DROP k ls))                  by LENGTH
   = k + (1 + (LENGTH ls - k))                     by LENGTH_DROP
   = 1 + LENGTH ls                                 by arithmetic, k <= LENGTH ls
*)
Theorem interleave_length:
  !ls x y. y IN (x interleave ls) ==> LENGTH y = 1 + LENGTH ls
Proof
  rw_tac bool_ss[interleave_element] >>
  simp[]
QED

(* Theorem: ALL_DISTINCT (x::ls) /\ y IN (x interleave ls) ==> ALL_DISTINCT y *)
(* Proof:
   By interleave_def, IN_IMAGE, this is to show;
      ALL_DISTINCT (TAKE k ls ++ x::DROP k ls)
   To apply ALL_DISTINCT_APPEND, need to show:
   (1) ~MEM x ls /\ MEM e (TAKE k ls) /\ MEM e (x::DROP k ls) ==> F
           MEM e (x::DROP k ls)
       <=> e = x \/ MEM e (DROP k ls)    by MEM
           MEM e (TAKE k ls)
       ==> MEM e ls                      by MEM_TAKE
       If e = x,
          this contradicts ~MEM x ls.
       If MEM e (DROP k ls),
          with MEM e (TAKE k ls)
          and ALL_DISTINCT ls gives F    by ALL_DISTINCT_TAKE_DROP
   (2) ALL_DISTINCT (TAKE k ls), true    by ALL_DISTINCT_TAKE
   (3) ~MEM x ls ==> ALL_DISTINCT (x::DROP k ls)
           ALL_DISTINCT (x::DROP k ls)
       <=> ~MEM x (DROP k ls) /\
           ALL_DISTINCT (DROP k ls)      by ALL_DISTINCT
       <=> ~MEM x (DROP k ls) /\ T       by ALL_DISTINCT_DROP
       ==> ~MEM x ls /\ T                by MEM_DROP_IMP
       ==> T /\ T = T
*)
Theorem interleave_distinct:
  !ls x y. ALL_DISTINCT (x::ls) /\ y IN (x interleave ls) ==> ALL_DISTINCT y
Proof
  rw_tac bool_ss[interleave_def, IN_IMAGE] >>
  irule (ALL_DISTINCT_APPEND |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >| [
    fs[] >-
    metis_tac[MEM_TAKE] >>
    metis_tac[ALL_DISTINCT_TAKE_DROP],
    fs[ALL_DISTINCT_TAKE],
    fs[ALL_DISTINCT_DROP] >>
    metis_tac[MEM_DROP_IMP]
  ]
QED

(* Theorem: ALL_DISTINCT ls /\ ~(MEM x ls) /\
            y IN (x interleave ls) ==> ALL_DISTINCT y *)
(* Proof: by interleave_distinct, ALL_DISTINCT. *)
Theorem interleave_distinct_alt:
  !ls x y. ALL_DISTINCT ls /\ ~(MEM x ls) /\
           y IN (x interleave ls) ==> ALL_DISTINCT y
Proof
  metis_tac[interleave_distinct, ALL_DISTINCT]
QED

(* Theorem: y IN x interleave ls ==> set y = set (x::ls) *)
(* Proof:
   Note y = TAKE k ls ++ x::DROP k ls    by interleave_element, for some k
   Let u = TAKE k ls, v = DROP k ls.
     set y
   = set (u ++ x::v)                     by above
   = set u UNION set (x::v)              by LIST_TO_SET_APPEND
   = set u UNION (x INSERT set v)        by LIST_TO_SET
   = (x INSERT set v) UNION set u        by UNION_COMM
   = x INSERT (set v UNION set u)        by INSERT_UNION_EQ
   = x INSERT (set u UNION set v)        by UNION_COMM
   = x INSERT (set (u ++ v))             by LIST_TO_SET_APPEND
   = x INSERT set ls                     by TAKE_DROP
   = set (x::ls)                         by LIST_TO_SET
*)
Theorem interleave_set:
  !ls x y. y IN x interleave ls ==> set y = set (x::ls)
Proof
  rw_tac bool_ss[interleave_element] >>
  qabbrev_tac `u = TAKE k ls` >>
  qabbrev_tac `v = DROP k ls` >>
  `set (u ++ x::v) = set u UNION set (x::v)` by rw[] >>
  `_ = set u UNION (x INSERT set v)` by rw[] >>
  `_ = (x INSERT set v) UNION set u` by rw[UNION_COMM] >>
  `_ = x INSERT (set v UNION set u)` by rw[INSERT_UNION_EQ] >>
  `_ = x INSERT (set u UNION set v)` by rw[UNION_COMM] >>
  `_ = x INSERT (set (u ++ v))` by rw[] >>
  `_ = x INSERT set ls` by metis_tac[TAKE_DROP] >>
  simp[]
QED

(* Theorem: y IN x interleave ls ==> set y = x INSERT set ls *)
(* Proof:
   Note set y = set (x::ls)        by interleave_set
              = x INSERT set ls    by LIST_TO_SET
*)
Theorem interleave_set_alt:
  !ls x y. y IN x interleave ls ==> set y = x INSERT set ls
Proof
  metis_tac[interleave_set, LIST_TO_SET]
QED

(* Theorem: (x::ls) IN x interleave ls *)
(* Proof:
       (x::ls) IN x interleave ls
   <=> ?k. x::ls = TAKE k ls ++ [x] ++ DROP k ls /\ k < SUC (LENGTH ls)
                               by interleave_def
   Take k = 0.
   Then 0 < SUC (LENGTH ls)    by SUC_POS
    and TAKE 0 ls ++ [x] ++ DROP 0 ls
      = [] ++ [x] ++ ls        by TAKE_0, DROP_0
      = x::ls                  by APPEND
*)
Theorem interleave_has_cons:
  !ls x. (x::ls) IN x interleave ls
Proof
  rw[interleave_def] >>
  qexists_tac `0` >>
  simp[]
QED

(* Theorem: x interleave ls <> EMPTY *)
(* Proof:
   Note (x::ls) IN x interleave ls by interleave_has_cons
   Thus x interleave ls <> {}      by MEMBER_NOT_EMPTY
*)
Theorem interleave_not_empty:
  !ls x. x interleave ls <> EMPTY
Proof
  metis_tac[interleave_has_cons, MEMBER_NOT_EMPTY]
QED

(*
MEM_APPEND_lemma
|- !a b c d x. a ++ [x] ++ b = c ++ [x] ++ d /\ ~MEM x b /\ ~MEM x a ==>
               a = c /\ b = d
*)

(* Theorem: ~MEM n x /\ ~MEM n y ==> (n interleave x = n interleave y <=> x = y) *)
(* Proof:
   Let f = (\k. TAKE k x ++ n::DROP k x),
       g = (\k. TAKE k y ++ n::DROP k y).
   By interleave_def, this is to show:
      IMAGE f (upto (LENGTH x)) = IMAGE g (upto (LENGTH y)) <=> x = y
   Only-part part is trivial.
   For the if part,
   Note 0 IN (upto (LENGTH x)                  by SUC_POS, IN_COUNT
     so f 0 IN IMAGE f (upto (LENGTH x))
   thus ?k. k < SUC (LENGTH y) /\ f 0 = g k    by IN_IMAGE, IN_COUNT
     so n::x = TAKE k y ++ [n] ++ DROP k y     by notation of f 0
    but n::x = TAKE 0 x ++ [n] ++ DROP 0 x     by TAKE_0, DROP_0
    and ~MEM n (TAKE 0 x) /\ ~MEM n (DROP 0 x) by TAKE_0, DROP_0
     so TAKE 0 x = TAKE k y /\
        DROP 0 x = DROP k y                    by MEM_APPEND_lemma
     or x = y                                  by TAKE_DROP
*)
Theorem interleave_eq:
  !n x y. ~MEM n x /\ ~MEM n y ==> (n interleave x = n interleave y <=> x = y)
Proof
  rw[interleave_def, EQ_IMP_THM] >>
  qabbrev_tac `f = \k. TAKE k x ++ n::DROP k x` >>
  qabbrev_tac `g = \k. TAKE k y ++ n::DROP k y` >>
  `f 0 IN IMAGE f (upto (LENGTH x))` by fs[] >>
  `?k. k < SUC (LENGTH y) /\ f 0 = g k` by metis_tac[IN_IMAGE, IN_COUNT] >>
  fs[Abbr`f`, Abbr`g`] >>
  `n::x = TAKE 0 x ++ [n] ++ DROP 0 x` by rw[] >>
  `~MEM n (TAKE 0 x) /\ ~MEM n (DROP 0 x)` by rw[] >>
  metis_tac[MEM_APPEND_lemma, TAKE_DROP]
QED

(* Theorem: ~MEM x l1 /\ l1 <> l2 ==> DISJOINT (x interleave l1) (x interleave l2) *)
(* Proof:
   Use DISJOINT_DEF, by contradiction, suppose y is in both.
   Then ?k h. k <= LENGTH l1 and h <= LENGTH l2
   with y = TAKE k l1 ++ [x] ++ DROP k l1      by interleave_element
    and y = TAKE h l2 ++ [x] ++ DROP h l2      by interleave_element
    Now ~MEM x (TAKE k l1)                     by MEM_TAKE
    and ~MEM x (DROP k l1)                     by MEM_DROP_IMP
   Thus TAKE k l1 = TAKE h l2 /\
        DROP k l1 = DROP h l2                  by MEM_APPEND_lemma
     or l1 = l2                                by TAKE_DROP
    but this contradicts l1 <> l2.
*)
Theorem interleave_disjoint:
  !l1 l2 x. ~MEM x l1 /\ l1 <> l2 ==> DISJOINT (x interleave l1) (x interleave l2)
Proof
  rw[interleave_def, DISJOINT_DEF, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `~MEM x (TAKE k l1) /\ ~MEM x (DROP k l1)` by metis_tac[MEM_TAKE, MEM_DROP_IMP] >>
  metis_tac[MEM_APPEND_lemma, TAKE_DROP]
QED

(* Theorem: FINITE (x interleave ls) *)
(* Proof:
   Let f = (\k. TAKE k ls ++ x::DROP k ls),
       n = LENGTH ls.
       FINITE (x interleave ls)
   <=> FINITE (IMAGE f (upto n))   by interleave_def
   <=> T                           by IMAGE_FINITE, FINITE_COUNT
*)
Theorem interleave_finite:
  !ls x. FINITE (x interleave ls)
Proof
  simp[interleave_def, IMAGE_FINITE]
QED

(* Theorem: ~MEM x ls ==>
            INJ (\k. TAKE k ls ++ x::DROP k ls) (upto (LENGTH ls)) univ(:'a list) *)
(* Proof:
   Let n = LENGTH ls,
       s = upto n,
       f = (\k. TAKE k ls ++ x::DROP k ls).
   By INJ_DEF, this is to show:
   (1) k IN s ==> f k IN univ(:'a list), true  by types.
   (2) k IN s /\ h IN s /\ f k = f h ==> k = h.
       Note k <= LENGTH ls               by IN_COUNT, k IN s
        and h <= LENGTH ls               by IN_COUNT, h IN s
        and ls = TAKE k ls ++ DROP k ls  by TAKE_DROP
         so ~MEM x (TAKE k ls) /\
            ~MEM x (DROP k ls)           by MEM_APPEND, ~MEM x ls
       Thus TAKE k ls = TAKE h ls        by MEM_APPEND_lemma
        ==>         k = h                by LENGTH_TAKE

MEM_APPEND_lemma
|- !a b c d x. a ++ [x] ++ b = c ++ [x] ++ d /\
               ~MEM x b /\ ~MEM x a ==> a = c /\ b = d
*)
Theorem interleave_count_inj:
  !ls x. ~MEM x ls ==>
         INJ (\k. TAKE k ls ++ x::DROP k ls) (upto (LENGTH ls)) univ(:'a list)
Proof
  rw[INJ_DEF] >>
  `k <= LENGTH ls /\ k' <= LENGTH ls` by fs[] >>
  `~MEM x (TAKE k ls) /\ ~MEM x (DROP k ls)` by metis_tac[TAKE_DROP, MEM_APPEND] >>
  metis_tac[MEM_APPEND_lemma, LENGTH_TAKE]
QED

(* Theorem: ~MEM x ls ==> CARD (x interleave ls) = 1 + LENGTH ls *)
(* Proof:
   Let f = (\k. TAKE k ls ++ x::DROP k ls),
       n = LENGTH ls.
   Note FINITE (upto n)            by FINITE_COUNT
    and INJ f (upto n) univ(:'a list)
                                   by interleave_count_inj, ~MEM x ls
     CARD (x interleave ls)
   = CARD (IMAGE f (upto n))       by interleave_def
   = CARD (upto n)                 by INJ_CARD_IMAGE
   = SUC n = 1 + n                 by CARD_COUNT, ADD1
*)
Theorem interleave_card:
  !ls x. ~MEM x ls ==> CARD (x interleave ls) = 1 + LENGTH ls
Proof
  rw[interleave_def] >>
  imp_res_tac interleave_count_inj >>
  qabbrev_tac `n = LENGTH ls` >>
  qabbrev_tac `s = upto n` >>
  qabbrev_tac `f = (\k. TAKE k ls ++ x::DROP k ls)` >>
  `FINITE s` by rw[Abbr`s`] >>
  metis_tac[INJ_CARD_IMAGE, CARD_COUNT, ADD1]
QED

(* Note:
  interleave_distinct, interleave_length, and interleave_set
  are effects after interleave. Now we need a kind of inverse:
  deduce the effects before interleave.
*)

(* Idea: a member h in a distinct list is the interleave of h with a smaller one. *)

(* Theorem: ALL_DISTINCT ls /\ h IN set ls ==>
            ?t. ALL_DISTINCT t /\ ls IN h interleave t /\ set t = (set ls) DELETE h *)
(* Proof:
   By induction on ls.
   Base: ALL_DISTINCT [] /\ MEM h [] ==> ?t. ...
         Since MEM h [] = F, this is true      by MEM
   Step: (ALL_DISTINCT ls /\ MEM h ls ==>
          ?t. ALL_DISTINCT t /\ ls IN h interleave t /\ set t = set ls DELETE h) ==>
         !h'. ALL_DISTINCT (h'::ls) /\ MEM h (h'::ls) ==>
          ?t. ALL_DISTINCT t /\ h'::ls IN h interleave t /\ set t = set (h'::ls) DELETE h
      If h' = h,
         Note ~MEM h ls /\ ALL_DISTINCT ls     by ALL_DISTINCT
         Take this ls,
         Then set (h::ls) DELETE h
            = (h INSERT set ls) DELETE h       by LIST_TO_SET
            = set ls                           by INSERT_DELETE_NON_ELEMENT
         and h::ls IN h interleave ls          by interleave_element, take k = 0.
      If h' <> h,
         Note ~MEM h' ls /\ ALL_DISTINCT ls    by ALL_DISTINCT
          and MEM h ls                         by MEM, h <> h'
         Thus ?t. ALL_DISTINCT t /\
                  ls IN h interleave t /\
                  set t = set ls DELETE h      by induction hypothesis
         Note ~MEM h' t                        by set t = set ls DELETE h, ~MEM h' ls
         Take this (h'::t),
         Then ALL_DISTINCT (h'::t)             by ALL_DISTINCT, ~MEM h' t
          and set (h'::ls) DELETE h
            = (h' INSERT set ls) DELETE h      by LIST_TO_SET
            = h' INSERT (set ls DELETE h)      by DELETE_INSERT, h' <> h
            = h' INSERT set t                  by above
            = set (h'::t)
          and h'::ls IN h interleave t         by interleave_element,
                                               take k = SUC k from ls IN h interleave t
*)
Theorem interleave_revert:
  !ls h. ALL_DISTINCT ls /\ h IN set ls ==>
      ?t. ALL_DISTINCT t /\ ls IN h interleave t /\ set t = (set ls) DELETE h
Proof
  rpt strip_tac >>
  Induct_on `ls` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `h' = h` >| [
    fs[] >>
    qexists_tac `ls` >>
    simp[INSERT_DELETE_NON_ELEMENT] >>
    simp[interleave_element] >>
    qexists_tac `0` >>
    simp[],
    fs[] >>
    `~MEM h' t` by fs[] >>
    qexists_tac `h'::t` >>
    simp[DELETE_INSERT] >>
    fs[interleave_element] >>
    qexists_tac `SUC k` >>
    simp[]
  ]
QED

(* A useful corollary for set s = count n. *)

(* Theorem: ALL_DISTINCT ls /\ set ls = upto n ==>
            ?t. ALL_DISTINCT t /\ ls IN n interleave t /\ set t = count n *)
(* Proof:
   Note MEM n ls                         by set ls = upto n
     so ?t. ALL_DISTINCT t /\
            ls IN n interleave t /\
            set t = set ls DELETE n      by interleave_revert
                  = (upto n) DELETE n    by given
                  = count n              by upto_delete
*)
Theorem interleave_revert_count:
  !ls n. ALL_DISTINCT ls /\ set ls = upto n ==>
     ?t. ALL_DISTINCT t /\ ls IN n interleave t /\ set t = count n
Proof
  rpt strip_tac >>
  `MEM n ls` by fs[] >>
  drule_then strip_assume_tac interleave_revert >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  metis_tac[upto_delete]
QED

(* Theorem: perm_count (SUC n) =
            BIGUNION (IMAGE ($interleave n) (perm_count n)) *)
(* Proof:
   By induction on n.
   Base: perm_count (SUC 0) =
         BIGUNION (IMAGE ($interleave 0) (perm_count 0))
         LHS = perm_count (SUC 0)
             = perm_count 1                           by ONE
             = {[0]}                                  by perm_count_1
         RHS = BIGUNION (IMAGE ($interleave 0) (perm_count 0))
             = BIGUNION (IMAGE ($interleave 0) {[]}   by perm_count_0
             = BIGUNION {0 interleave []}             by IMAGE_SING
             = BIGUNION {{[0]}}                       by interleave_nil
             = {[0]} = LHS                            by BIGUNION_SING
   Step: perm_count (SUC n) = BIGUNION (IMAGE ($interleave n) (perm_count n)) ==>
         perm_count (SUC (SUC n)) =
              BIGUNION (IMAGE ($interleave (SUC n)) (perm_count (SUC n)))
         Let f = $interleave (SUC n),
             s = perm_count n, t = perm_count (SUC n).
             y IN BIGUNION (IMAGE f t)
         <=> ?x. x IN t /\ y IN f x      by IN_BIGUNION_IMAGE
         <=> ?x. (?z. z IN s /\ x IN n interleave z) /\ y IN (SUC n) interleave x
                                         by IN_BIGUNION_IMAGE, induction hypothesis
         <=> ?x z. ALL_DISTINCT z /\ set z = count n /\
                   x IN n interleave z /\
                   y IN (SUC n) interleave x      by perm_count_element
         If part: y IN perm_count (SUC (SUC n)) ==> ?x and z.
            Note ALL_DISTINCT y /\
                 set y = count (SUC (SUC n))      by perm_count_element
            Then ?x. ALL_DISTINCT x /\ y IN (SUC n) interleave x /\ set x = upto n
                                                  by interleave_revert_count
              so ?z. ALL_DISTINCT z /\ x IN n interleave z /\ set z = count n
                                                  by interleave_revert_count
            Take these x and z.
         Only-if part: ?x and z ==> y IN perm_count (SUC (SUC n))
            Note ~MEM n z                         by set z = count n, COUNT_NOT_SELF
             ==> ALL_DISTINCT x /\                by interleave_distinct_alt
                 set x = upto n                   by interleave_set_alt, COUNT_SUC
            Note ~MEM (SUC n) x                   by set x = upto n, COUNT_NOT_SELF
             ==> ALL_DISTINCT y /\                by interleave_distinct_alt
                 set y = count (SUC (SUC n))      by interleave_set_alt, COUNT_SUC
             ==> y IN perm_count (SUC (SUC n))    by perm_count_element
*)
Theorem perm_count_suc:
  !n. perm_count (SUC n) =
      BIGUNION (IMAGE ($interleave n) (perm_count n))
Proof
  Induct >| [
    rw[perm_count_0, perm_count_1] >>
    simp[interleave_nil],
    rw[IN_BIGUNION_IMAGE, EXTENSION, EQ_IMP_THM] >| [
      imp_res_tac perm_count_element >>
      `?y. ALL_DISTINCT y /\ x IN (SUC n) interleave y /\ set y = upto n` by rw[interleave_revert_count] >>
      `?t. ALL_DISTINCT t /\ y IN n interleave t /\ set t = count n` by rw[interleave_revert_count] >>
      (qexists_tac `y` >> simp[]) >>
      (qexists_tac `t` >> simp[]) >>
      simp[perm_count_element],
      fs[perm_count_element] >>
      `~MEM n x''` by fs[] >>
      `ALL_DISTINCT x' /\ set x' = upto n` by metis_tac[interleave_distinct_alt, interleave_set_alt, COUNT_SUC] >>
      `~MEM (SUC n) x'` by fs[] >>
      metis_tac[interleave_distinct_alt, interleave_set_alt, COUNT_SUC]
    ]
  ]
QED

(* Theorem: perm_count (n + 1) =
      BIGUNION (IMAGE ($interleave n) (perm_count n)) *)
(* Proof: by perm_count_suc, GSYM ADD1. *)
Theorem perm_count_suc_alt:
  !n. perm_count (n + 1) =
      BIGUNION (IMAGE ($interleave n) (perm_count n))
Proof
  simp[perm_count_suc, GSYM ADD1]
QED

(* Theorem: perm_count n =
            if n = 0 then {[]}
            else BIGUNION (IMAGE ($interleave (n - 1)) (perm_count (n - 1))) *)
(* Proof: by perm_count_0, perm_count_suc. *)
Theorem perm_count_eqn[compute]:
  !n. perm_count n =
      if n = 0 then {[]}
      else BIGUNION (IMAGE ($interleave (n - 1)) (perm_count (n - 1)))
Proof
  rw[perm_count_0] >>
  metis_tac[perm_count_suc, num_CASES, SUC_SUB1]
QED

(*
> EVAL ``perm_count 3``;
val it = |- perm_count 3 =
{[0; 1; 2]; [0; 2; 1]; [2; 0; 1]; [1; 0; 2]; [1; 2; 0]; [2; 1; 0]}: thm
*)

(* Historical note.
This use of interleave to list all permutations is called
the Steinhaus–Johnson–Trotter algorithm, due to re-discovery by various people.
Outside mathematics, this method was known already to 17th-century English change ringers.
Equivalently, this algorithm finds a Hamiltonian cycle in the permutohedron.

Steinhaus–Johnson–Trotter algorithm
https://en.wikipedia.org/wiki/Steinhaus–Johnson–Trotter_algorithm

1677 A book by Fabian Stedman lists the solutions for up to six bells.
1958 A book by Steinhaus describes a related puzzle of generating all permutations by a system of particles.
Selmer M. Johnson and Hale F. Trotter discovered the algorithm independently of each other in the early 1960s.
1962 Hale F. Trotter, "Algorithm 115: Perm", August 1962.
1963 Selmer M. Johnson, "Generation of permutations by adjacent transposition".

*)

(* Theorem: perm 0 = 1 *)
(* Proof:
     perm 0
   = CARD (perm_count 0)     by perm_def
   = CARD {[]}               by perm_count_0
   = 1                       by CARD_SING
*)
Theorem perm_0:
  perm 0 = 1
Proof
  simp[perm_def, perm_count_0]
QED

(* Theorem: perm 1 = 1 *)
(* Proof:
     perm 1
   = CARD (perm_count 1)     by perm_def
   = CARD {[0]}              by perm_count_1
   = 1                       by CARD_SING
*)
Theorem perm_1:
  perm 1 = 1
Proof
  simp[perm_def, perm_count_1]
QED

(* Theorem: e IN IMAGE ($interleave n) (perm_count n) ==> FINITE e *)
(* Proof:
       e IN IMAGE ($interleave n) (perm_count n)
   <=> ?ls. ls IN perm_count n /\
            e = n interleave ls    by IN_IMAGE
   Thus FINITE e                   by interleave_finite
*)
Theorem perm_count_interleave_finite:
  !n e. e IN IMAGE ($interleave n) (perm_count n) ==> FINITE e
Proof
  rw[] >>
  simp[interleave_finite]
QED

(* Theorem: e IN IMAGE ($interleave n) (perm_count n) ==> CARD e = n + 1 *)
(* Proof:
       e IN IMAGE ($interleave n) (perm_count n)
   <=> ?ls. ls IN perm_count n /\
            e = n interleave ls    by IN_IMAGE
   Note ~MEM n ls                  by perm_count_element_no_self
    and LENGTH ls = n              by perm_count_element_length
   Thus CARD e = n + 1             by interleave_card, ~MEM n ls
*)
Theorem perm_count_interleave_card:
  !n e. e IN IMAGE ($interleave n) (perm_count n) ==> CARD e = n + 1
Proof
  rw[] >>
  `~MEM n x` by rw[perm_count_element_no_self] >>
  `LENGTH x = n` by rw[perm_count_element_length] >>
  simp[interleave_card]
QED

(* Theorem: PAIR_DISJOINT (IMAGE ($interleave n) (perm_count n)) *)
(* Proof:
   By IN_IMAGE, this is to show:
        x IN perm_count n /\ y IN perm_count n /\
        n interleave x <> n interleave y ==>
        DISJOINT (n interleave x) (n interleave y)
   By contradiction, suppose there is a list ls in both.
   Then x = y                  by interleave_disjoint
   This contradicts n interleave x <> n interleave y.
*)
Theorem perm_count_interleave_disjoint:
  !n e. PAIR_DISJOINT (IMAGE ($interleave n) (perm_count n))
Proof
  rw[perm_count_def] >>
  `~MEM n x` by fs[] >>
  metis_tac[interleave_disjoint]
QED

(* Theorem: INJ ($interleave n) (perm_count n) univ(:(num list -> bool)) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN perm_count n ==> n interleave x IN univ
       This is true by type.
   (2) x IN perm_count n /\ y IN perm_count n /\
       n interleave x = n interleave y ==> x = y
       Note ~MEM n x       by perm_count_element_no_self
        and ~MEM n y       by perm_count_element_no_self
       Thus x = y          by interleave_eq
*)
Theorem perm_count_interleave_inj:
  !n. INJ ($interleave n) (perm_count n) univ(:(num list -> bool))
Proof
  rw[INJ_DEF, perm_count_def, interleave_eq]
QED

(* Theorem: perm (SUC n) = (SUC n) * perm n *)
(* Proof:
   Let f = $interleave n,
       s = IMAGE f (perm_count n).
   Note FINITE (perm_count n)      by perm_count_finite
     so FINITE s                   by IMAGE_FINITE
    and !e. e IN s ==>
            FINITE e /\            by perm_count_interleave_finite
            CARD e = n + 1         by perm_count_interleave_card
    and PAIR_DISJOINT s            by perm_count_interleave_disjoint
    and INJ f (perm_count n) univ(:(num list -> bool))
                                   by perm_count_interleave_inj
     perm (SUC n)
   = CARD (perm_count (SUC n))     by perm_def
   = CARD (BIGUNION s)             by perm_count_suc
   = CARD s * (n + 1)              by CARD_BIGUNION_SAME_SIZED_SETS
   = CARD (perm_count n) * (n + 1) by INJ_CARD_IMAGE
   = perm n * (n + 1)              by perm_def
   = (SUC n) * perm n              by MULT_COMM, ADD1
*)
Theorem perm_suc:
  !n. perm (SUC n) = (SUC n) * perm n
Proof
  rpt strip_tac >>
  qabbrev_tac `f = $interleave n` >>
  qabbrev_tac `s = IMAGE f (perm_count n)` >>
  `FINITE (perm_count n)` by rw[perm_count_finite] >>
  `FINITE s` by rw[Abbr`s`] >>
  `!e. e IN s ==> FINITE e /\ CARD e = n + 1`
        by metis_tac[perm_count_interleave_finite, perm_count_interleave_card] >>
  `PAIR_DISJOINT s` by metis_tac[perm_count_interleave_disjoint] >>
  `INJ f (perm_count n) univ(:(num list -> bool))` by rw[perm_count_interleave_inj, Abbr`f`] >>
  simp[perm_def] >>
  `CARD (perm_count (SUC n)) = CARD (BIGUNION s)` by rw[perm_count_suc, Abbr`s`, Abbr`f`] >>
  `_ = CARD s * (n + 1)` by rw[CARD_BIGUNION_SAME_SIZED_SETS] >>
  `_ = CARD (perm_count n) * (n + 1)` by metis_tac[INJ_CARD_IMAGE] >>
  simp[ADD1]
QED

(* Theorem: perm (n + 1) = (n + 1) * perm n *)
(* Proof: by perm_suc, ADD1 *)
Theorem perm_suc_alt:
  !n. perm (n + 1) = (n + 1) * perm n
Proof
  simp[perm_suc, GSYM ADD1]
QED

(* Theorem: perm 0 = 1 /\ !n. perm (n + 1) = (n + 1) * perm n *)
(* Proof: by perm_0, perm_suc_alt *)
Theorem perm_alt:
  perm 0 = 1 /\ !n. perm (n + 1) = (n + 1) * perm n
Proof
  simp[perm_0, perm_suc_alt]
QED

(* Theorem: perm n = FACT n *)
(* Proof: by FACT_iff, perm_alt. *)
Theorem perm_eq_fact[compute]:
  !n. perm n = FACT n
Proof
  metis_tac[FACT_iff, perm_alt, ADD1]
QED

(* This is fantastic! *)

(*
> EVAL ``perm 3``; = 6
> EVAL ``MAP perm [0 .. 10]``; =
[1; 1; 2; 6; 24; 120; 720; 5040; 40320; 362880; 3628800]
*)

(* ------------------------------------------------------------------------- *)
(* Permutations of a set.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Note: SET_TO_LIST, using CHOICE and REST, is not effective for computations.
SET_TO_LIST_THM
|- FINITE s ==>
   SET_TO_LIST s = if s = {} then [] else CHOICE s::SET_TO_LIST (REST s)
*)

(* Define the set of permutation lists of a set. *)
Definition perm_set_def[nocompute]:
    perm_set s = {ls | ALL_DISTINCT ls /\ set ls = s}
End
(* use [nocompute] as this is not effective for evalutaion. *)
(* Note: this cannot be made effective, unless sort s to list by some ordering. *)

(* Theorem: ls IN perm_set s <=> ALL_DISTINCT ls /\ set ls = s *)
(* Proof: perm_set_def *)
Theorem perm_set_element:
  !ls s. ls IN perm_set s <=> ALL_DISTINCT ls /\ set ls = s
Proof
  simp[perm_set_def]
QED

(* Theorem: perm_set (count n) = perm_count n *)
(* Proof: by perm_count_def, perm_set_def. *)
Theorem perm_set_perm_count:
  !n. perm_set (count n) = perm_count n
Proof
  simp[perm_count_def, perm_set_def]
QED

(* Theorem: perm_set {} = {[]} *)
(* Proof:
     perm_set {}
   = {ls | ALL_DISTINCT ls /\ set ls = {}}     by perm_set_def
   = {ls | ALL_DISTINCT ls /\ ls = []}         by LIST_TO_SET_EQ_EMPTY
   = {[]}                                      by ALL_DISTINCT
*)
Theorem perm_set_empty:
  perm_set {} = {[]}
Proof
  rw[perm_set_def, EXTENSION] >>
  metis_tac[ALL_DISTINCT]
QED

(* Theorem: perm_set {x} = {[x]} *)
(* Proof:
     perm_set {x}
   = {ls | ALL_DISTINCT ls /\ set ls = {x}}    by perm_set_def
   = {ls | ls = [x]}                           by DISTINCT_LIST_TO_SET_EQ_SING
   = {[x]}                                     by notation
*)
Theorem perm_set_sing:
  !x. perm_set {x} = {[x]}
Proof
  simp[perm_set_def, DISTINCT_LIST_TO_SET_EQ_SING]
QED

(* Theorem: perm_set s = {[]} <=> s = {} *)
(* Proof:
   If part: perm_set s = {[]} ==> s = {}
      By contradiction, suppose s <> {}.
          ls IN perm_set s
      <=> ALL_DISTINCT ls /\ set ls = s        by perm_set_element
      ==> ls <> []                             by LIST_TO_SET_EQ_EMPTY
      This contradicts perm_set s = {[]}       by IN_SING
   Only-if part: s = {} ==> perm_set s = {[]}
      This is true                             by perm_set_empty
*)
Theorem perm_set_eq_empty_sing:
  !s. perm_set s = {[]} <=> s = {}
Proof
  rw[perm_set_empty, EQ_IMP_THM] >>
  `[] IN perm_set s` by fs[] >>
  fs[perm_set_element]
QED

(* Theorem: FINITE s ==> (SET_TO_LIST s) IN perm_set s *)
(* Proof:
   Let ls = SET_TO_LIST s.
   Note ALL_DISTINCT ls        by ALL_DISTINCT_SET_TO_LIST
    and set ls = s             by SET_TO_LIST_INV
   Thus ls IN perm_set s       by perm_set_element
*)
Theorem perm_set_has_self_list:
  !s. FINITE s ==> (SET_TO_LIST s) IN perm_set s
Proof
  simp[perm_set_element, ALL_DISTINCT_SET_TO_LIST, SET_TO_LIST_INV]
QED

(* Theorem: FINITE s ==> perm_set s <> {} *)
(* Proof:
   Let ls = SET_TO_LIST s.
   Then ls IN perm_set s       by perm_set_has_self_list
   Thus perm_set s <> {}       by MEMBER_NOT_EMPTY
*)
Theorem perm_set_not_empty:
  !s. FINITE s ==> perm_set s <> {}
Proof
  metis_tac[perm_set_has_self_list, MEMBER_NOT_EMPTY]
QED

(* Theorem: perm_set (set ls) <> {} *)
(* Proof:
   Note FINITE (set ls)            by FINITE_LIST_TO_SET
     so perm_set (set ls) <> {}    by perm_set_not_empty
*)
Theorem perm_set_list_not_empty:
  !ls. perm_set (set ls) <> {}
Proof
  simp[FINITE_LIST_TO_SET, perm_set_not_empty]
QED

(* Theorem: ls IN perm_set s /\ BIJ f s (count n) ==> MAP f ls IN perm_count n *)
(* Proof:
   By perm_set_def, perm_count_def, this is to show:
   (1) ALL_DISTINCT ls /\ BIJ f (set ls) (count n) ==> ALL_DISTINCT (MAP f ls)
       Note INJ f (set ls) (count n)     by BIJ_DEF
         so ALL_DISTINCT (MAP f ls)      by ALL_DISTINCT_MAP_INJ, INJ_DEF
   (2) ALL_DISTINCT ls /\ BIJ f (set ls) (count n) ==> set (MAP f ls) = count n
       Note SURJ f (set ls) (count n)    by BIJ_DEF
         so set (MAP f ls)
          = IMAGE f (set ls)             by LIST_TO_SET_MAP
          = count n                      by IMAGE_SURJ
*)
Theorem perm_set_map_element:
  !ls f s n. ls IN perm_set s /\ BIJ f s (count n) ==> MAP f ls IN perm_count n
Proof
  rw[perm_set_def, perm_count_def] >-
  metis_tac[ALL_DISTINCT_MAP_INJ, BIJ_IS_INJ] >>
  simp[LIST_TO_SET_MAP] >>
  fs[IMAGE_SURJ, BIJ_DEF]
QED

(* Theorem: BIJ f s (count n) ==>
            INJ (MAP f) (perm_set s) (perm_count n) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN perm_set s ==> MAP f x IN perm_count n
       This is true                by perm_set_map_element
   (2) x IN perm_set s /\ y IN perm_set s /\ MAP f x = MAP f y ==> x = y
       Note LENGTH x = LENGTH y    by LENGTH_MAP
       By LIST_EQ, it remains to show:
          !j. j < LENGTH x ==> EL j x = EL j y
       Note EL j x IN s            by perm_set_element, MEM_EL
        and EL j y IN s            by perm_set_element, MEM_EL
                   MAP f x = MAP f y
        ==> EL j (MAP f x) = EL j (MAP f y)
        ==>     f (EL j x) = f (EL j y)        by EL_MAP
        ==>         EL j x = EL j y            by BIJ_IS_INJ
*)
Theorem perm_set_map_inj:
  !f s n. BIJ f s (count n) ==>
          INJ (MAP f) (perm_set s) (perm_count n)
Proof
  rw[INJ_DEF] >-
  metis_tac[perm_set_map_element] >>
  irule LIST_EQ >>
  `LENGTH x = LENGTH y` by metis_tac[LENGTH_MAP] >>
  rw[] >>
  `EL x' x IN s` by metis_tac[perm_set_element, MEM_EL] >>
  `EL x' y IN s` by metis_tac[perm_set_element, MEM_EL] >>
  metis_tac[EL_MAP, BIJ_IS_INJ]
QED

(* Theorem: BIJ f s (count n) ==>
            SURJ (MAP f) (perm_set s) (perm_count n) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) x IN perm_set s ==> MAP f x IN perm_count n
       This is true                                by perm_set_map_element
   (2) x IN perm_count n ==> ?y. y IN perm_set s /\ MAP f y = x
       Let y = MAP (LINV f s) x. Then to show:
       (1) y IN perm_set s,
           Note BIJ (LINV f s) (count n) s         by BIJ_LINV_BIJ
           By perm_set_element, perm_count_element, to show:
           (1) ALL_DISTINCT (MAP (LINV f s) x)
               Note INJ (LINV f s) (count n) s     by BIJ_DEF
                 so ALL_DISTINCT (MAP (LINV f s) x)
                                                   by ALL_DISTINCT_MAP_INJ, INJ_DEF
           (2) set (MAP (LINV f s) x) = s
               Note SURJ (LINV f s) (count n) s    by BIJ_DEF
                 so set (MAP (LINV f s) x)
                  = IMAGE (LINV f s) (set x)       by LIST_TO_SET_MAP
                  = IMAGE (LINV f s) (count n)     by set x = count n
                  = s                              by IMAGE_SURJ
       (2) x IN perm_count n ==> MAP f (MAP (LINV f s) x) = x
           Let g = f o LINV f s.
           The goal is: MAP g x = x                by MAP_COMPOSE
           Note LENGTH (MAP g x) = LENGTH x        by LENGTH_MAP
           To apply LIST_EQ, just need to show:
                   !k. k < LENGTH x ==>
                       EL k (MAP g x) = EL k x
           or to show: g (EL k x) = EL k x         by EL_MAP
            Now set x = count n                    by perm_count_element
             so EL k x IN (count n)                by MEM_EL
           Thus g (EL k x) = EL k x                by BIJ_LINV_INV
*)
Theorem perm_set_map_surj:
  !f s n. BIJ f s (count n) ==>
          SURJ (MAP f) (perm_set s) (perm_count n)
Proof
  rw[SURJ_DEF] >-
  metis_tac[perm_set_map_element] >>
  qexists_tac `MAP (LINV f s) x` >>
  rpt strip_tac >| [
    `BIJ (LINV f s) (count n) s` by rw[BIJ_LINV_BIJ] >>
    fs[perm_set_element, perm_count_element] >>
    rpt strip_tac >-
    metis_tac[ALL_DISTINCT_MAP_INJ, BIJ_IS_INJ] >>
    simp[LIST_TO_SET_MAP] >>
    fs[IMAGE_SURJ, BIJ_DEF],
    simp[MAP_COMPOSE] >>
    qabbrev_tac `g = f o LINV f s` >>
    irule LIST_EQ >>
    `LENGTH (MAP g x) = LENGTH x` by rw[LENGTH_MAP] >>
    rw[] >>
    simp[EL_MAP] >>
    fs[perm_count_element, Abbr`g`] >>
    metis_tac[MEM_EL, BIJ_LINV_INV]
  ]
QED

(* Theorem: BIJ f s (count n) ==>
            BIJ (MAP f) (perm_set s) (perm_count n) *)
(* Proof:
   Note  INJ (MAP f) (perm_set s) (perm_count n)  by perm_set_map_inj
    and SURJ (MAP f) (perm_set s) (perm_count n)  by perm_set_map_surj
   Thus  BIJ (MAP f) (perm_set s) (perm_count n)  by BIJ_DEF
*)
Theorem perm_set_map_bij:
  !f s n. BIJ f s (count n) ==>
          BIJ (MAP f) (perm_set s) (perm_count n)
Proof
  simp[BIJ_DEF, perm_set_map_inj, perm_set_map_surj]
QED

(* Theorem: FINITE s ==> perm_set s =b= perm_count (CARD s) *)
(* Proof:
   Note ?f. BIJ f s (count (CARD s))               by bij_eq_count, FINITE s
   Thus BIJ (MAP f) (perm_set s) (perm_count (CARD s))
                                                   by perm_set_map_bij
   showing perm_set s =b= perm_count (CARD s)      by notation
*)
Theorem perm_set_bij_eq_perm_count:
  !s. FINITE s ==> perm_set s =b= perm_count (CARD s)
Proof
  rpt strip_tac >>
  imp_res_tac bij_eq_count >>
  metis_tac[perm_set_map_bij]
QED

(* Theorem: FINITE s ==> FINITE (perm_set s) *)
(* Proof:
   Note perm_set s =b= perm_count (CARD s)     by perm_set_bij_eq_perm_count
    and FINITE (perm_count (CARD s))           by perm_count_finite
     so FINITE (perm_set s)                    by bij_eq_finite
*)
Theorem perm_set_finite:
  !s. FINITE s ==> FINITE (perm_set s)
Proof
  metis_tac[perm_set_bij_eq_perm_count, perm_count_finite, bij_eq_finite]
QED

(* Theorem: FINITE s ==> CARD (perm_set s) = perm (CARD s) *)
(* Proof:
   Note perm_set s =b= perm_count (CARD s)     by perm_set_bij_eq_perm_count
    and FINITE (perm_count (CARD s))           by perm_count_finite
     so CARD (perm_set s)
      = CARD (perm_count (CARD s))             by bij_eq_card
      = perm (CARD s)                          by perm_def
*)
Theorem perm_set_card:
  !s. FINITE s ==> CARD (perm_set s) = perm (CARD s)
Proof
  metis_tac[perm_set_bij_eq_perm_count, perm_count_finite, bij_eq_card, perm_def]
QED

(* This is a major result! *)

(* Theorem: FINITE s ==> CARD (perm_set s) = FACT (CARD s) *)
(* Proof: by perm_set_card, perm_eq_fact. *)
Theorem perm_set_card_alt:
  !s. FINITE s ==> CARD (perm_set s) = FACT (CARD s)
Proof
  simp[perm_set_card, perm_eq_fact]
QED

(* ------------------------------------------------------------------------- *)
(* Counting number of arrangements.                                          *)
(* ------------------------------------------------------------------------- *)

(* Define the set of choices of k-tuples of (count n). *)
Definition list_count_def[nocompute]:
    list_count n k =
        { ls | ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k}
End
(* use [nocompute] as this is not effective for evalutaion. *)
(* Note: if defined as:
   list_count n k = { ls | (set ls) SUBSET (count n) /\ CARD (set ls) = k}
then non-distinct lists will be in the set, which is not desirable.
*)

(* Define the number of choices of k-tuples of (count n). *)
Definition arrange_def[nocompute]:
    arrange n k = CARD (list_count n k)
End
(* use [nocompute] as this is not effective for evalutaion. *)
(* make this an infix operator *)
val _ = set_fixity "arrange" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)
(* arrange_def;
val it = |- !n k. n arrange k = CARD (list_count n k): thm *)

(* Theorem: list_count n k =
        { ls | ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ CARD (set ls) = k} *)
(* Proof:
       ls IN list_count n k
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k
                                   by list_count_def
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ CARD (set ls) = k
                                   by ALL_DISTINCT_CARD_LIST_TO_SET
   Hence the sets are equal by EXTENSION.
*)
Theorem list_count_alt:
  !n k. list_count n k =
        { ls | ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ CARD (set ls) = k}
Proof
  simp[list_count_def, EXTENSION] >>
  metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Theorem: ls IN list_count n k <=>
            ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k *)
(* Proof: by list_count_def. *)
Theorem list_count_element:
  !ls n k. ls IN list_count n k <=>
           ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k
Proof
  simp[list_count_def]
QED

(* Theorem: ls IN list_count n k <=>
            ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ CARD (set ls) = k *)
(* Proof: by list_count_alt. *)
Theorem list_count_element_alt:
  !ls n k. ls IN list_count n k <=>
           ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ CARD (set ls) = k
Proof
  simp[list_count_alt]
QED

(* Theorem: ls IN list_count n k ==> CARD (set ls) = k *)
(* Proof:
       ls IN list_count n k
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k
                                   by list_count_element
   ==> CARD (set ls) = k           by ALL_DISTINCT_CARD_LIST_TO_SET
*)
Theorem list_count_element_set_card:
  !ls n k. ls IN list_count n k ==> CARD (set ls) = k
Proof
  simp[list_count_def, ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Theorem: list_count n k SUBSET necklace k n *)
(* Proof:
       ls IN list_count n k
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = k
                                               by list_count_element
   ==> (set ls) SUBSET (count n) /\ LENGTH ls = k
   ==> ls IN necklace k n                      by necklace_def
   Thus list_count n k SUBSET necklace k n     by SUBSET_DEF
*)
Theorem list_count_subset:
  !n k. list_count n k SUBSET necklace k n
Proof
  simp[list_count_def, necklace_def, SUBSET_DEF]
QED

(* Theorem: FINITE (list_count n k) *)
(* Proof:
   Note list_count n k SUBSET necklace k n     by list_count_subset
    and FINITE (necklace k n)                  by necklace_finite
     so FINITE (list_count n k)                by SUBSET_FINITE
*)
Theorem list_count_finite:
  !n k. FINITE (list_count n k)
Proof
  metis_tac[list_count_subset, necklace_finite, SUBSET_FINITE]
QED

(* Note:
list_count 4 2 has P(4,2) = 4 * 3 = 12 elements.
necklace 2 4 has 2 ** 4 = 16 elements.

> EVAL ``necklace 2 4``;
val it = |- necklace 2 4 =
      {[3; 3]; [3; 2]; [3; 1]; [3; 0]; [2; 3]; [2; 2]; [2; 1]; [2; 0];
       [1; 3]; [1; 2]; [1; 1]; [1; 0]; [0; 3]; [0; 2]; [0; 1]; [0; 0]}: thm
> EVAL ``IMAGE set (necklace 2 4)``;
val it = |- IMAGE set (necklace 2 4) =
      {{3}; {2; 3}; {2}; {1; 3}; {1; 2}; {1}; {0; 3}; {0; 2}; {0; 1}; {0}}:
> EVAL ``IMAGE (\ls. if CARD (set ls) = 2 then ls else []) (necklace 2 4)``;
val it = |- IMAGE (\ls. if CARD (set ls) = 2 then ls else []) (necklace 2 4) =
      {[3; 2]; [3; 1]; [3; 0]; [2; 3]; [2; 1]; [2; 0]; [1; 3]; [1; 2];
       [1; 0]; [0; 3]; [0; 2]; [0; 1]; []}: thm
> EVAL ``let n = 4; k = 2 in (IMAGE (\ls. if CARD (set ls) = k then ls else []) (necklace k n)) DELETE []``;
val it = |- (let n = 4; k = 2 in
IMAGE (\ls. if CARD (set ls) = k then ls else []) (necklace k n) DELETE []) =
      {[3; 2]; [3; 1]; [3; 0]; [2; 3]; [2; 1]; [2; 0]; [1; 3]; [1; 2];
       [1; 0]; [0; 3]; [0; 2]; [0; 1]}: thm
> EVAL ``let n = 4; k = 2 in (IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n)) DELETE []``;
val it = |- (let n = 4; k = 2 in
         IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE []) =
      {[3; 2]; [3; 1]; [3; 0]; [2; 3]; [2; 1]; [2; 0]; [1; 3]; [1; 2];
       [1; 0]; [0; 3]; [0; 2]; [0; 1]}: thm
*)

(* Note:
P(n,k) = C(n,k) * k!
P(n,0) = C(n,0) * 0! = 1
P(0,k+1) = C(0,k+1) * (k+1)! = 0
*)

(* Theorem: list_count n 0 = {[]} *)
(* Proof:
       ls IN list_count n 0
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ LENGTH ls = 0
                                   by list_count_element
   <=> ALL_DISTINCT ls /\ (set ls) SUBSET (count n) /\ ls = []
                                   by LENGTH_NIL
   <=> T /\ T /\ ls = []           by ALL_DISTINCT, LIST_TO_SET, EMPTY_SUBSET
   Thus list_count n 0 = {[]}      by EXTENSION
*)
Theorem list_count_n_0:
  !n. list_count n 0 = {[]}
Proof
  rw[list_count_def, EXTENSION, EQ_IMP_THM]
QED

(* Theorem: 0 < n ==> list_count 0 n = {} *)
(* Proof:
   Note (list_count 0 n) SUBSET (necklace n 0)
                                   by list_count_subset
    but (necklace n 0) = {}        by necklace_empty, 0 < n
   Thus (list_count 0 n) = {}      by SUBSET_EMPTY
*)
Theorem list_count_0_n:
  !n. 0 < n ==> list_count 0 n = {}
Proof
  metis_tac[list_count_subset, necklace_empty, SUBSET_EMPTY]
QED

(* Theorem: list_count n n = perm_count n *)
(* Proof:
       ls IN list_count n n
   <=> ALL_DISTINCT ls /\ set ls SUBSET count n /\ CARD (set ls) = n
                                               by list_count_element_alt
   <=> ALL_DISTINCT ls /\ set ls SUBSET count n /\ CARD (set ls) = CARD (count n)
                                               by CARD_COUNT
   <=> ALL_DISTINCT ls /\ set ls SUBSET count n /\ set ls = count n
                                               by SUBSET_CARD_EQ
   <=> ALL_DISTINCT ls /\ set ls = count n     by SUBSET_REFL
   <=> ls IN perm_count n                      by perm_count_element
*)
Theorem list_count_n_n:
  !n. list_count n n = perm_count n
Proof
  rw_tac bool_ss[list_count_element_alt, EXTENSION] >>
  `FINITE (count n) /\ CARD (count n) = n` by rw[] >>
  metis_tac[SUBSET_REFL, SUBSET_CARD_EQ, perm_count_element]
QED

(* Theorem: list_count n k = {} <=> n < k *)
(* Proof:
   If part: list_count n k = {} ==> n < k
      By contradiction, suppose k <= n.
      Let ls = SET_TO_LIST (count k).
      Note FINITE (count k)              by FINITE_COUNT
      Then ALL_DISTINCT ls               by ALL_DISTINCT_SET_TO_LIST
       and set ls = count k              by SET_TO_LIST_INV
       Now (count k) SUBSET (count n)    by COUNT_SUBSET, k <= n
       and CARD (count k) = k            by CARD_COUNT
        so ls IN list_count n k          by list_count_element_alt
      Thus list_count n k <> {}          by MEMBER_NOT_EMPTY
      which is a contradiction.
   Only-if part: n < k ==> list_count n k = {}
      By contradiction, suppose sub_count n k <> {}.
      Then ?ls. ls IN list_count n k     by MEMBER_NOT_EMPTY
       ==> ALL_DISTINCT ls /\ set ls SUBSET count n /\ CARD (set ls) = k
                                         by sub_count_element_alt
      Note FINITE (count n)              by FINITE_COUNT
        so CARD (set ls) <= CARD (count n)
                                         by CARD_SUBSET
       ==> k <= n                        by CARD_COUNT
       This contradicts n < k.
*)
Theorem list_count_eq_empty:
  !n k. list_count n k = {} <=> n < k
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `ls = SET_TO_LIST (count k)` >>
    `FINITE (count k)` by rw[FINITE_COUNT] >>
    `ALL_DISTINCT ls` by rw[ALL_DISTINCT_SET_TO_LIST, Abbr`ls`] >>
    `set ls = count k` by rw[SET_TO_LIST_INV, Abbr`ls`] >>
    `(count k) SUBSET (count n)` by rw[COUNT_SUBSET] >>
    `CARD (count k) = k` by rw[] >>
    metis_tac[list_count_element_alt, MEMBER_NOT_EMPTY],
    spose_not_then strip_assume_tac >>
    `?ls. ls IN list_count n k` by rw[MEMBER_NOT_EMPTY] >>
    fs[list_count_element_alt] >>
    `FINITE (count n)` by rw[] >>
    `CARD (set ls) <= n` by metis_tac[CARD_SUBSET, CARD_COUNT] >>
    decide_tac
  ]
QED

(* Theorem: 0 < k ==>
            list_count n k =
            IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE [] *)
(* Proof:
       x IN IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE []
   <=> ?ls. x = (if ALL_DISTINCT ls then ls else []) /\
            LENGTH ls = k /\ set ls SUBSET count n) /\ x <> []   by IN_IMAGE, IN_DELETE
   <=> ALL_DISTINCT x /\ LENGTH x = k /\ set x SUBSET count n    by LENGTH_NIL, 0 < k, ls = x
   <=> x IN list_count n k                                       by list_count_element
   Thus the two sets are equal by EXTENSION.
*)
Theorem list_count_by_image:
  !n k. 0 < k ==>
        list_count n k =
        IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE []
Proof
  rw[list_count_def, necklace_def, EXTENSION] >>
  (rw[EQ_IMP_THM] >> metis_tac[LENGTH_NIL, NOT_ZERO])
QED

(* Theorem: list_count n k =
            if k = 0 then {[]}
            else IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE [] *)
(* Proof: by list_count_n_0, list_count_by_image *)
Theorem list_count_eqn[compute]:
  !n k. list_count n k =
        if k = 0 then {[]}
        else IMAGE (\ls. if ALL_DISTINCT ls then ls else []) (necklace k n) DELETE []
Proof
  rw[list_count_n_0, list_count_by_image]
QED

(*
> EVAL ``list_count 3 2``;
val it = |- list_count 3 2 = {[2; 1]; [2; 0]; [1; 2]; [1; 0]; [0; 2]; [0; 1]}: thm
> EVAL ``list_count 4 2``;
val it = |- list_count 4 2 =
{[3; 2]; [3; 1]; [3; 0]; [2; 3]; [2; 1]; [2; 0]; [1; 3]; [1; 2]; [1; 0]; [0; 3]; [0; 2]; [0; 1]}: thm
*)

(* Idea: define an equivalence relation feq set:  set x = set y.
         There are k! elements in each equivalence class.
         Thus n arrange k = perm k * n choose k. *)

(* Theorem: (feq set) equiv_on s *)
(* Proof: by feq_equiv. *)
Theorem feq_set_equiv:
  !s. (feq set) equiv_on s
Proof
  simp[feq_equiv]
QED

(*
> EVAL ``list_count 3 2``;
val it = |- list_count 3 2 = {[2; 1]; [1; 2]; [2; 0]; [0; 2]; [1; 0]; [0; 1]}: thm
*)

(* Theorem: ls IN list_count n k ==>
            equiv_class (feq set) (list_count n k) ls = perm_set (set ls) *)
(* Proof:
   Note ALL_DISTINCT ls /\ set ls SUBSET count n /\ LENGTH ls = k
                                                   by list_count_element
       x IN equiv_class (feq set) (list_count n k) ls
   <=> x IN (list_count n k) /\ (feq set) ls x     by equiv_class_element
   <=> x IN (list_count n k) /\ set ls = set x     by feq_def
   <=> ALL_DISTINCT x /\ set x SUBSET count n /\ LENGTH x = k /\
       set x = set ls                              by list_count_element
   <=> ALL_DISTINCT x /\ LENGTH x = LENGTH ls /\ set x = set ls
                                                   by given
   <=> ALL_DISTINCT x /\ set x = set ls            by ALL_DISTINCT_CARD_LIST_TO_SET
   <=> x IN perm_set (set ls)                      by perm_set_element
*)
Theorem list_count_set_eq_class:
  !ls n k. ls IN list_count n k ==>
           equiv_class (feq set) (list_count n k) ls = perm_set (set ls)
Proof
  rw[list_count_def, perm_set_def, fequiv_def, Once EXTENSION] >>
  rw[EQ_IMP_THM] >>
  metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Theorem: ls IN list_count n k ==>
            CARD (equiv_class (feq set) (list_count n k) ls) = perm k *)
(* Proof:
   Note ALL_DISTINCT ls /\ set ls SUBSET count n /\ LENGTH ls = k
                                   by list_count_element
     CARD (equiv_class (feq set) (list_count n k) ls)
   = CARD (perm_set (set ls))      by list_count_set_eq_class
   = perm (CARD (set ls))          by perm_set_card
   = perm (LENGTH ls)              by ALL_DISTINCT_CARD_LIST_TO_SET
   = perm k                        by LENGTH ls = k
*)
Theorem list_count_set_eq_class_card:
  !ls n k. ls IN list_count n k ==>
            CARD (equiv_class (feq set) (list_count n k) ls) = perm k
Proof
  rw[list_count_set_eq_class] >>
  fs[list_count_element] >>
  simp[perm_set_card, ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Theorem: e IN partition (feq set) (list_count n k) ==> CARD e = perm k *)
(* Proof:
   By partition_element, this is to show:
      ls IN list_count n k ==>
      CARD (equiv_class (feq set) (list_count n k) ls) = perm k
   This is true by list_count_set_eq_class_card.
*)
Theorem list_count_set_partititon_element_card:
  !n k e. e IN partition (feq set) (list_count n k) ==> CARD e = perm k
Proof
  rw_tac bool_ss [partition_element] >>
  simp[list_count_set_eq_class_card]
QED

(* Theorem: ls IN list_count n k ==> perm_set (set ls) <> {} *)
(* Proof:
   Note (feq set) equiv_on (list_count n k)        by feq_set_equiv
    and perm_set (set ls)
      = equiv_class (feq set) (list_count n k) ls  by list_count_set_eq_class
     <> {}                                         by equiv_class_not_empty
*)
Theorem list_count_element_perm_set_not_empty:
  !ls n k. ls IN list_count n k ==> perm_set (set ls) <> {}
Proof
  metis_tac[list_count_set_eq_class, feq_set_equiv, equiv_class_not_empty]
QED

(* This is more restrictive than perm_set_list_not_empty, hence not useful. *)

(* Theorem: s IN (partition (feq set) (list_count n k)) ==>
            (set o CHOICE) s IN (sub_count n k) *)
(* Proof:
        s IN (partition (feq set) (list_count n k))
    <=> ?x. x IN list_count n k /\
            s = equiv_class (feq set) (list_count n k) x   by partition_element
    ==> ?x. x IN list_count n k /\ s = perm_set (set x)    by list_count_set_eq_class
   Thus ALL_DISTINCT x /\ set x SUBSET count n /\ LENGTH x = k
                                               by list_count_element
    and (set o CHOICE) s
      = set (CHOICE (perm_set (set x)))        by o_THM
   Note perm_set (set x) <> {}                 by perm_set_list_not_empty
   Let ls = CHOICE (perm_set (set x)).
   Then ls IN perm_set (set x)                 by CHOICE_DEF
     so ALL_DISTINCT ls /\ set ls = set x      by perm_set_element
   Thus (set o CHOICE) s = set x
   With set x SUBSET count n                   by above
    and CARD (set x) = LENGTH x = k            by ALL_DISTINCT_CARD_LIST_TO_SET
     so (set x) IN (sub_count n k)             by sub_count_element
*)
Theorem list_count_set_map_element:
  !s n k. s IN (partition (feq set) (list_count n k)) ==>
          (set o CHOICE) s IN (sub_count n k)
Proof
  rw_tac bool_ss [partition_element] >>
  simp[list_count_set_eq_class] >>
  qabbrev_tac `ls = CHOICE (perm_set (set x))` >>
  `perm_set (set x) <> {}` by metis_tac[perm_set_list_not_empty] >>
  `ls IN perm_set (set x)` by fs[CHOICE_DEF, Abbr`ls`] >>
  fs[list_count_element, perm_set_element, sub_count_element] >>
  simp[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Another proof of the same theorem, slightly better. *)

(* Theorem: s IN (partition (feq set) (list_count n k)) ==>
            (set o CHOICE) s IN (sub_count n k) *)
(* Proof:
        s IN (partition (feq set) (list_count n k))
    <=> ?z. z IN list_count n k /\
        !x. x IN s <=> x IN list_count n k /\ set x = set z
                                         by feq_partition_element
    ==> z IN s, so s <> {}               by MEMBER_NOT_EMPTY
    Let ls = CHOICE s.
    Then ls IN s                         by CHOICE_DEF
      so ls IN list_count n k /\ set ls = set z
                                         by implication
      or ALL_DISTINCT ls /\ set ls SUBSET count n /\ LENGTH ls = k
                                         by list_count_element
    Note (set o CHOICE) s = set ls       by o_THM
     and CARD (set ls) = LENGTH ls       by ALL_DISTINCT_CARD_LIST_TO_SET
      so set ls IN (sub_count n k)       by sub_count_element_alt
*)
Theorem list_count_set_map_element[allow_rebind]:
  !s n k. s IN (partition (feq set) (list_count n k)) ==>
          (set o CHOICE) s IN (sub_count n k)
Proof
  rw[feq_partition_element] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `(CHOICE s) IN s` by fs[CHOICE_DEF] >>
  fs[list_count_element, sub_count_element] >>
  metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

(* Theorem: INJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k) *)
(* Proof:
   Let R = feq set,
       s = list_count n k,
       t = sub_count n k.
   By INJ_DEF, this is to show:
   (1) x IN partition R s ==> (set o CHOICE) x IN t
       This is true                by list_count_set_map_element
   (2) x IN partition R s /\ y IN partition R s /\
       (set o CHOICE) x = (set o CHOICE) y ==> x = y
       Note ?u. u IN list_count n k
            !ls. ls IN x <=> ls IN list_count n k /\ set ls = set u
                                   by feq_partition_element
        and ?v. v IN list_count n k
            !ls. ls IN y <=> ls IN list_count n k /\ set ls = set v
                                   by feq_partition_element
       Thus u IN x, so x <> {}     by MEMBER_NOT_EMPTY
        and v IN y, so y <> {}     by MEMBER_NOT_EMPTY
        Let lx = CHOICE x IN x     by CHOICE_DEF
        and ly = CHOICE y IN y     by CHOICE_DEF
       With set lx = set ly        by o_THM
       Thus set lx = set u         by implication
        and set ly = set v         by implication
         so set u = set v          by above
       Thus x = y                  by EXTENSION
*)
Theorem list_count_set_map_inj:
  !n k. INJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k)
Proof
  rw_tac bool_ss[INJ_DEF] >-
  simp[list_count_set_map_element] >>
  fs[feq_partition_element] >>
  `x <> {} /\ y <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `CHOICE x IN x /\ CHOICE y IN y` by fs[CHOICE_DEF] >>
  `set z = set z'` by rfs[] >>
  simp[EXTENSION]
QED

(* Theorem: SURJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k) *)
(* Proof:
   Let R = feq set,
       s = list_count n k,
       t = sub_count n k.
   By SURJ_DEF, this is to show:
   (1) x IN partition R s ==> (set o CHOICE) x IN t
       This is true                            by list_count_set_map_element
   (2) x IN t ==> ?y. y IN partition R s /\ (set o CHOICE) y = x
       Note x SUBSET count n /\ CARD x = k     by sub_count_element
       Thus FINITE x                           by SUBSET_FINITE, FINITE_COUNT
       Let y = perm_set x.
       To show;
       (1) y IN partition R s
       Note y IN partition R s
        <=> ?ls. ls IN list_count n k /\
            !z. z IN perm_set x <=> z IN list_count n k /\ set z = set ls
                                         by feq_partition_element
       Let ls = SET_TO_LIST x.
       Then ALL_DISTINCT ls              by ALL_DISTINCT_SET_TO_LIST, FINITE x
        and set ls = x                   by SET_TO_LIST_INV, FINITE x
         so set ls SUBSET (count n)      by above, x SUBSET count n
        and LENGTH ls = k                by SET_TO_LIST_CARD, FINITE x
         so ls IN list_count n k         by list_count_element
       To show: !z. z IN perm_set x <=> z IN list_count n k /\ set z = set ls
           z IN perm_set x
       <=> ALL_DISTINCT z /\ set z = x   by perm_set_element
       <=> ALL_DISTINCT z /\ set z SUBSET count n /\ set z = x
                                         by x SUBSET count n
       <=> ALL_DISTINCT z /\ set z SUBSET count n /\ LENGTH z = CARD x
                                         by ALL_DISTINCT_CARD_LIST_TO_SET
       <=> z IN list_count n k /\ set z = set ls
                                         by list_count_element, CARD x = k, set ls = x.
       (2) (set o CHOICE) y = x
       Note y <> {}                      by perm_set_not_empty, FINITE x
       Then CHOICE y IN y                by CHOICE_DEF
         so (set o CHOICE) y
          = set (CHOICE y)               by o_THM
          = x                            by perm_set_element, y = perm_set x
*)
Theorem list_count_set_map_surj:
  !n k. SURJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k)
Proof
  rw_tac bool_ss[SURJ_DEF] >-
  simp[list_count_set_map_element] >>
  fs[sub_count_element] >>
  `FINITE x` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  qexists_tac `perm_set x` >>
  simp[feq_partition_element, list_count_element, perm_set_element] >>
  rpt strip_tac >| [
    qabbrev_tac `ls = SET_TO_LIST x` >>
    qexists_tac `ls` >>
    `ALL_DISTINCT ls` by rw[ALL_DISTINCT_SET_TO_LIST, Abbr`ls`] >>
    `set ls = x` by rw[SET_TO_LIST_INV, Abbr`ls`] >>
    `LENGTH ls = k` by rw[SET_TO_LIST_CARD, Abbr`ls`] >>
    rw[EQ_IMP_THM] >>
    metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET],
    `perm_set x <> {}` by fs[perm_set_not_empty] >>
    qabbrev_tac `ls = CHOICE (perm_set x)` >>
    `ls IN perm_set x` by fs[CHOICE_DEF, Abbr`ls`] >>
    fs[perm_set_element]
  ]
QED

(* Theorem: BIJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k) *)
(* Proof:
   Let f = set o CHOICE,
       s = partition (feq set) (list_count n k),
       t = sub_count n k.
   Note  INJ f s t         by list_count_set_map_inj
    and SURJ f s t         by list_count_set_map_surj
     so  BIJ f s t         by BIJ_DEF
*)
Theorem list_count_set_map_bij:
  !n k. BIJ (set o CHOICE) (partition (feq set) (list_count n k)) (sub_count n k)
Proof
  simp[BIJ_DEF, list_count_set_map_inj, list_count_set_map_surj]
QED

(* Theorem: n arrange k = (n choose k) * perm k *)
(* Proof:
   Let R = feq set,
       s = list_count n k,
       t = sub_count n k.
   Then FINITE s                 by list_count_finite
    and R equiv_on s             by feq_set_equiv
    and !e. e IN partition R s ==> CARD e = perm k
                                 by list_count_set_partititon_element_card
   Thus CARD s = perm k * CARD (partition R s)
                                 by equal_partition_card, [1]
   Note CARD s = n arrange k     by arrange_def
    and BIJ (set o CHOICE) (partition R s) t
                                 by list_count_set_map_bij
    and FINITE t                 by sub_count_finite
     so CARD (partition R s)
      = CARD t                   by bij_eq_card
      = n choose k               by choose_def
   Hence n arrange k = n choose k * perm k
                                 by MULT_COMM, [1], above.
*)
Theorem arrange_eqn[compute]:
  !n k. n arrange k = (n choose k) * perm k
Proof
  rpt strip_tac >>
  assume_tac list_count_set_map_bij >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  qabbrev_tac `R = feq (set :num list -> num -> bool)` >>
  qabbrev_tac `s = list_count n k` >>
  qabbrev_tac `t = sub_count n k` >>
  `FINITE s` by rw[list_count_finite, Abbr`s`] >>
  `R equiv_on s` by rw[feq_set_equiv, Abbr`R`] >>
  `!e. e IN partition R s ==> CARD e = perm k` by metis_tac[list_count_set_partititon_element_card] >>
  imp_res_tac equal_partition_card >>
  `FINITE t` by rw[sub_count_finite, Abbr`t`] >>
  `CARD (partition R s) = CARD t` by metis_tac[bij_eq_card] >>
  simp[arrange_def, choose_def, Abbr`s`, Abbr`t`]
QED

(* This is P(n,k) = C(n,k) * k! *)

(* Theorem: n arrange k = (n choose k) * FACT k *)
(* Proof:
     n arrange k
   = (n choose k) * perm k     by arrange_eqn
   = (n choose k) * FACT k     by perm_eq_fact
*)
Theorem arrange_alt:
  !n k. n arrange k = (n choose k) * FACT k
Proof
  simp[arrange_eqn, perm_eq_fact]
QED

(*
> EVAL ``5 arrange 2``; = 20
> EVAL ``MAP ($arrange 5) [0 .. 5]``;  = [1; 5; 20; 60; 120; 120]
*)

(* Theorem: n arrange k = (binomial n k) * FACT k *)
(* Proof:
     n arrange k
   = (n choose k) * FACT k     by arrange_alt
   = (binomial n k) * FACT k   by choose_eqn
*)
Theorem arrange_formula:
  !n k. n arrange k = (binomial n k) * FACT k
Proof
  simp[arrange_alt, choose_eqn]
QED

(* Theorem: k <= n ==> n arrange k = FACT n DIV FACT (n - k) *)
(* Proof:
   Note 0 < FACT (n - k)                       by FACT_LESS
     (n arrange k) * FACT (n - k)
   = (binomial n k) * FACT k * FACT (n - k)    by arrange_formula
   = binomial n k * (FACT (n - k) * FACT k)    by arithmetic
   = FACT n                                    by binomial_formula2, k <= n
   Thus n arrange k = FACT n DIV FACT (n - k)  by DIV_SOLVE
*)
Theorem arrange_formula2:
  !n k. k <= n ==> n arrange k = FACT n DIV FACT (n - k)
Proof
  rpt strip_tac >>
  `0 < FACT (n - k)` by rw[FACT_LESS] >>
  `(n arrange k) * FACT (n - k) = (binomial n k) * FACT k * FACT (n - k)` by rw[arrange_formula] >>
  `_ = binomial n k * (FACT (n - k) * FACT k)` by rw[] >>
  `_ = FACT n` by rw[binomial_formula2] >>
  simp[DIV_SOLVE]
QED

(* Theorem: n arrange 0 = 1 *)
(* Proof:
     n arrange 0
   = CARD (list_count n 0)     by arrange_def
   = CARD {[]}                 by list_count_n_0
   = 1                         by CARD_SING
*)
Theorem arrange_n_0:
  !n. n arrange 0 = 1
Proof
  simp[arrange_def, perm_def, list_count_n_0]
QED

(* Theorem: 0 < n ==> 0 arrange n = 0 *)
(* Proof:
     0 arrange n
   = CARD (list_count 0 n)     by arrange_def
   = CARD {}                   by list_count_0_n, 0 < n
   = 0                         by CARD_EMPTY
*)
Theorem arrange_0_n:
  !n. 0 < n ==> 0 arrange n = 0
Proof
  simp[arrange_def, perm_def, list_count_0_n]
QED

(* Theorem: n arrange n = perm n *)
(* Proof:
     n arrange n
   = CARD (list_count n n)     by arrange_def
   = CARD (perm_count n)       by list_count_n_n
   = perm n                    by perm_def
*)
Theorem arrange_n_n:
  !n. n arrange n = perm n
Proof
  simp[arrange_def, perm_def, list_count_n_n]
QED

(* Another proof of the same theorem. *)

(* Theorem: n arrange n = perm n *)
(* Proof:
     n arrange n
   = (binomial n n) * FACT n   by arrange_formula
   = 1 * FACT n                by binomial_n_n
   = perm n                    by perm_eq_fact
*)
Theorem arrange_n_n[allow_rebind]:
  !n. n arrange n = perm n
Proof
  simp[arrange_formula, binomial_n_n, perm_eq_fact]
QED

(* Theorem: n arrange n = FACT n *)
(* Proof:
     n arrange n
   = (binomial n n) * FACT n   by arrange_formula
   = 1 * FACT n                by binomial_n_n
*)
Theorem arrange_n_n_alt:
  !n. n arrange n = FACT n
Proof
  simp[arrange_formula, binomial_n_n]
QED

(* Theorem: n arrange k = 0 <=> n < k *)
(* Proof:
   Note FINITE (list_count n k)    by list_count_finite
        n arrange k = 0
    <=> CARD (list_count n k) = 0  by arrange_def
    <=> list_count n k = {}        by CARD_EQ_0
    <=> n < k                      by list_count_eq_empty
*)
Theorem arrange_eq_0:
  !n k. n arrange k = 0 <=> n < k
Proof
  metis_tac[arrange_def, list_count_eq_empty, list_count_finite, CARD_EQ_0]
QED

(* Note:

k-permutation recurrence?

P(n,k) = C(n,k) * k!
P(n,0) = C(n,0) * 0! = 1
P(0,k+1) = C(0,k+1) * (k+1)! = 0

C(n+1,k+1) = C(n,k) + C(n,k+1)
P(n+1,k+1)/(k+1)! = P(n,k)/k! + P(n,k+1)/(k+1)!
P(n+1,k+1) = (k+1) * P(n,k) + P(n,k+1)
P(n+1,k+1) = P(n,k) * (k + 1) + P(n,k+1)

P(2,1) = 2:    [0] [1]
P(2,2) = 2:    [0,1] [1,0]
P(3,2) = 6:    [0,1] [0,2]   include 2: [0,2] [1,2] [2,0] [2,1]
               [1,0] [1,2]   exclude 2: [0,1] [1,0]
               [2,0] [2,1]
P(3,2) = P(2,1) * 2 + P(2,2) = ([0][1],2 + 2,[0][1]) + to_lists {0,1}
P(4,3): include 3: P(3,2) * 3
        exclude 3: P(3,3)

list_count (n+1) (k+1) = IMAGE (interleave k) (list_count n k) UNION list_count n (k + 1)

closed?
https://math.stackexchange.com/questions/3060456/
using Pascal argument

*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
