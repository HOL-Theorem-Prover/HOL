(* ------------------------------------------------------------------------- *)
(* Combinatorics Theory                                                      *)
(*  (Combined theory of Euler, Gauss, Mobius, triangle and binomial, etc.,   *)
(*   originally under "examples/algebra/lib")                                *)
(*                                                                           *)
(* Author: (Joseph) Hing-Lun Chan (Australian National University, 2019)     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Necklace Theory - monocoloured and multicoloured.                         *)
(* ------------------------------------------------------------------------- *)
(*

Necklace Theory
===============

Consider the set N of necklaces of length n (i.e. with number of beads = n)
with a colors (i.e. the number of bead colors = a). A linear picture of such
a necklace is:

+--+--+--+--+--+--+--+
|2 |4 |0 |3 |1 |2 |3 |  p = 7, with (lots of) beads of a = 5 colors: 01234.
+--+--+--+--+--+--+--+

Since a bead can have any of the a colors, and there are n beads in total,

Number of such necklaces = CARD N = a*a*...*a = a^n.

There is only 1 necklace of pure color A, 1 necklace with pure color B, etc.

Number of monocoloured necklaces = a = CARD S, where S = monocoloured necklaces.

So, N = S UNION M, where M = multicoloured necklaces (i.e. more than one color).

Since S and M are disjoint, CARD M = CARD N - CARD S = a^n - a.

*)

open HolKernel boolLib Parse bossLib;

open prim_recTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     logrootTheory pred_setTheory listTheory rich_listTheory numberTheory
     listRangeTheory  indexedListsTheory relationTheory;

val _ = new_theory "combinatorics";

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* List Reversal.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Overload for REVERSE [m .. n] *)
val _ = overload_on ("downto", ``\n m. REVERSE [m .. n]``);
val _ = set_fixity "downto" (Infix(NONASSOC, 450)); (* same as relation *)

(* ------------------------------------------------------------------------- *)
(* Extra List Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R *)
(* Proof: by EVERY_EL. *)
val EVERY_ELEMENT_PROPERTY = store_thm(
  "EVERY_ELEMENT_PROPERTY",
  ``!p R. EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R``,
  rw[EVERY_EL]);

(* Theorem: (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l) *)
(* Proof:
   Since !x. P x ==> (Q o f) x,
         EVERY P l
     ==> EVERY Q o f l         by EVERY_MONOTONIC
     ==> EVERY Q (MAP f l)     by EVERY_MAP
*)
val EVERY_MONOTONIC_MAP = store_thm(
  "EVERY_MONOTONIC_MAP",
  ``!l f P Q. (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l)``,
  metis_tac[EVERY_MONOTONIC, EVERY_MAP]);

(* Theorem: EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls *)
(* Proof: by EVERY_EL, arithmetic. *)
val EVERY_LT_IMP_EVERY_LE = store_thm(
  "EVERY_LT_IMP_EVERY_LE",
  ``!ls n. EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls``,
  simp[EVERY_EL, LESS_IMP_LESS_OR_EQ]);

(* Theorem: (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
            (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
           (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2)) *)
(* Proof:
   Put k = 0,
   Then LENGTH (h1::t1) = SUC (LENGTH t1)     by LENGTH
                        > 0                   by SUC_POS
    and P (EL 0 (h1::t1)) (EL 0 (h2::t2))     by implication, 0 < LENGTH (h1::t1)
     or P HD (h1::t1) HD (h2::t2)             by EL
     or P h1 h2                               by HD
   Note k < LENGTH t1
    ==> k + 1 < SUC (LENGTH t1)                           by ADD1
              = LENGTH (h1::t1)                           by LENGTH
   Thus P (EL (k + 1) (h1::t1)) (EL (k + 1) (h2::t2))     by implication
     or P (EL (PRE (k + 1) t1)) (EL (PRE (k + 1)) t2)     by EL_CONS
     or P (EL k t1) (EL k t2)                             by PRE, ADD1
*)
val EL_ALL_PROPERTY = store_thm(
  "EL_ALL_PROPERTY",
  ``!h1 t1 h2 t2 P. (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
     (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
     (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2))``,
  rpt strip_tac >| [
    `0 < LENGTH (h1::t1)` by metis_tac[LENGTH, SUC_POS] >>
    metis_tac[EL, HD],
    `k + 1 < SUC (LENGTH t1)` by decide_tac >>
    `k + 1 < LENGTH (h1::t1)` by metis_tac[LENGTH] >>
    `0 < k + 1 /\ (PRE (k + 1) = k)` by decide_tac >>
    metis_tac[EL_CONS]
  ]);

(*
LUPDATE_SEM     |- (!e n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
                    !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l
EL_LUPDATE      |- !ys x i k. EL i (LUPDATE x k ys) = if i = k /\ k < LENGTH ys then x else EL i ys
LENGTH_LUPDATE  |- !x n ys. LENGTH (LUPDATE x n ys) = LENGTH ys
*)

(* Extract useful theorem from LUPDATE semantics *)
val LUPDATE_LEN = save_thm("LUPDATE_LEN", LUPDATE_SEM |> CONJUNCT1);
(* val LUPDATE_LEN = |- !e n l. LENGTH (LUPDATE e n l) = LENGTH l: thm *)
val LUPDATE_EL = save_thm("LUPDATE_EL", LUPDATE_SEM |> CONJUNCT2);
(* val LUPDATE_EL = |- !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l: thm *)

(* Theorem: LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p n ls), l2 = LUPDATE q n ls.
   By LIST_EQ, this is to show:
   (1) LENGTH l1 = LENGTH l2
         LENGTH l1
       = LENGTH (LUPDATE q n (LUPDATE p n ls))  by notation
       = LENGTH (LUPDATE p n ls)                by LUPDATE_LEN
       = ls                                     by LUPDATE_LEN
       = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
       = LENGTH l2                              by notation
   (2) !x. x < LENGTH l1 ==> EL x l1 = EL x l2
         EL x l1
       = EL x (LUPDATE q n (LUPDATE p n ls))    by notation
       = if x = n then q else EL x (LUPDATE p n ls)            by LUPDATE_EL
       = if x = n then q else (if x = n then p else EL x ls)   by LUPDATE_EL
       = if x = n then q else EL x ls           by simplification
       = EL x (LUPDATE q n ls)                  by LUPDATE_EL
       = EL x l2                                by notation
*)
val LUPDATE_SAME_SPOT = store_thm(
  "LUPDATE_SAME_SPOT",
  ``!ls n p q. LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p n ls)` >>
  qabbrev_tac `l2 = LUPDATE q n ls` >>
  `LENGTH l1 = LENGTH l2` by rw[LUPDATE_LEN, Abbr`l1`, Abbr`l2`] >>
  `!x. x < LENGTH l1 ==> (EL x l1 = EL x l2)` by fs[LUPDATE_EL, Abbr`l1`, Abbr`l2`] >>
  rw[LIST_EQ]);

(* Theorem: m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls)) *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p m ls),
       l2 = LUPDATE p m (LUPDATE q n ls).
       LENGTH l1
     = LENGTH (LUPDATE q n (LUPDATE p m ls))  by notation
     = LENGTH (LUPDATE p m ls)                by LUPDATE_LEN
     = LENGTH ls                              by LUPDATE_LEN
     = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
     = LENGTH (LUPDATE p m (LUPDATE q n ls))  by LUPDATE_LEN
     = LENGTH l2                              by notation
      !x. x < LENGTH l1 ==>
      EL x l1
    = EL x ((LUPDATE q n (LUPDATE p m ls))    by notation
    = EL x ls  if x <> n, x <> m, or p if x = m, q if x = n
                                              by LUPDATE_EL
      EL x l2
    = EL x ((LUPDATE p m (LUPDATE q n ls))    by notation
    = EL x ls  if x <> m, x <> n, or q if x = n, p if x = m
                                              by LUPDATE_EL
    = EL x l1
   Hence l1 = l2                              by LIST_EQ
*)
val LUPDATE_DIFF_SPOT = store_thm(
  "LUPDATE_DIFF_SPOT",
  `` !ls m n p q. m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls))``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p m ls)` >>
  qabbrev_tac `l2 = LUPDATE p m (LUPDATE q n ls)` >>
  irule LIST_EQ >>
  rw[LUPDATE_EL, Abbr`l1`, Abbr`l2`]);

(* Theorem: LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t) *)
(* Proof:
     LUPDATE a (LENGTH ls) (ls ++ h::t)
   = ls ++ LUPDATE a (LENGTH ls - LENGTH ls) (h::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE a 0 (h::t)                         by arithmetic
   = ls ++ (a::t)                                     by LUPDATE_def
*)
val LUPDATE_APPEND_0 = store_thm(
  "LUPDATE_APPEND_0",
  ``!ls a h t. LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t)``,
  rw_tac std_ss[LUPDATE_APPEND2, LUPDATE_def]);

(* Theorem: LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t *)
(* Proof:
     LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t)
   = ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE b 1 (h::k::t)                      by arithmetic
   = ls ++ (h::b::t)                                  by LUPDATE_def
*)
val LUPDATE_APPEND_1 = store_thm(
  "LUPDATE_APPEND_1",
  ``!ls b h k t. LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t``,
  rpt strip_tac >>
  `LUPDATE b 1 (h::k::t) = h::LUPDATE b 0 (k::t)` by rw[GSYM LUPDATE_def] >>
  `_ = h::b::t` by rw[LUPDATE_def] >>
  `LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) =
    ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)` by metis_tac[LUPDATE_APPEND2, DECIDE``n <= n + 1``] >>
  fs[]);

(* Theorem: LUPDATE b (LENGTH ls + 1)
              (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t *)
(* Proof:
   Let l1 = LUPDATE a (LENGTH ls) (ls ++ h::k::t)
          = ls ++ a::k::t       by LUPDATE_APPEND_0
     LUPDATE b (LENGTH ls + 1) l1
   = LUPDATE b (LENGTH ls + 1) (ls ++ a::k::t)
   = ls ++ a::b::t              by LUPDATE_APPEND2_1
*)
val LUPDATE_APPEND_0_1 = store_thm(
  "LUPDATE_APPEND_0_1",
  ``!ls a b h k t.
    LUPDATE b (LENGTH ls + 1)
      (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t``,
  rw_tac std_ss[LUPDATE_APPEND_0, LUPDATE_APPEND_1]);

(* Theorem: let fs = FILTER P ls in
            ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
            (findi y fs = 1 + findi x fs <=> FILTER P l2 = []) *)
(* Proof:
   Let j = LENGTH (FILTER P l1).

   Note fs = FILTER P l1 ++ x::FILTER P l2 ++
                            y::FILTER P l3     by FILTER_APPEND_DISTRIB
   Thus LENGTH fs = j +
                    SUC (LENGTH (FILTER P l2)) +
                    SUC (LENGTH (FILTER P l3)) by LENGTH_APPEND
     or j + 2 <= LENGTH fs                     by arithmetic
     or j < LENGTH fs /\ j + 1 < LENGTH fs     by j + 2 <= LENGTH fs

   Let l4 = y::l3,
   Then ls = l1 ++ x::l2 ++ l4
           = l1 ++ x::(l2 ++ l4)               by APPEND_ASSOC_CONS
    ==> x = EL j fs                            by FILTER_EL_IMP

   Note ALL_DISTINCT fs                        by FILTER_ALL_DISTINCT
    and MEM x ls /\ MEM y ls                   by MEM_APPEND
     so MEM x fs /\ MEM y fs                   by MEM_FILTER
    and x = EL j fs <=> findi x fs = j            by findi_EL_iff
    and y = EL (j + 1) fs <=> findi y fs = j + 1  by findi_EL_iff

        FILTER P l2 = []
     <=> x = EL j fs /\ y = EL (j + 1) fs      by FILTER_EL_NEXT_IFF
     <=> findi y fs = 1 + findi x fs           by above
*)
Theorem FILTER_EL_NEXT_IDX:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls in
                      ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                      (findi y fs = 1 + findi x fs <=> FILTER P l2 = [])
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = l1 ++ x::l2 ++ y::l3` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `j + 2 <= LENGTH fs` by
  (`fs = FILTER P l1 ++ x::FILTER P l2 ++ y::FILTER P l3` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
  `LENGTH fs = j + SUC (LENGTH (FILTER P l2)) + SUC (LENGTH (FILTER P l3))` by fs[Abbr`j`] >>
  decide_tac) >>
  `j < LENGTH fs /\ j + 1 < LENGTH fs` by decide_tac >>
  `x = EL j fs` by
    (qabbrev_tac `l4 = y::l3` >>
  `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
  metis_tac[FILTER_EL_IMP]) >>
  `MEM x ls /\ MEM y ls` by fs[Abbr`ls`] >>
  `MEM x fs /\ MEM y fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
  `x = EL j fs <=> findi x fs = j` by fs[findi_EL_iff] >>
  `y = EL (j + 1) fs <=> findi y fs = 1 + j` by fs[findi_EL_iff] >>
  metis_tac[FILTER_EL_NEXT_IFF]
QED

(* ------------------------------------------------------------------------- *)
(* List Rotation.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define rotation of a list *)
val rotate_def = Define `
  rotate n l = DROP n l ++ TAKE n l
`;

(* Theorem: Rotate shifts element
            rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l) *)
(* Proof:
   h h t t t t t t  --> t t t t t h h
       k                k
   TAKE 2 x = h h
   DROP 2 x = t t t t t t
              k
   DROP 2 x ++ TAKE 2 x   has element k at front.

   Proof: by induction on l.
   Base case: !n. n < LENGTH [] ==> (DROP n [] = EL n []::DROP (SUC n) [])
     Since n < LENGTH [] = 0 is F, this is true.
   Step case: !h n. n < LENGTH (h::l) ==> (DROP n (h::l) = EL n (h::l)::DROP (SUC n) (h::l))
     i.e. n <> 0 /\ n < SUC (LENGTH l) ==> DROP (n - 1) l = EL n (h::l)::DROP n l  by DROP_def
     n <> 0 means ?j. n = SUC j < SUC (LENGTH l), so j < LENGTH l.
     LHS = DROP (SUC j - 1) l
         = DROP j l                    by SUC j - 1 = j
         = EL j l :: DROP (SUC j) l    by induction hypothesis
     RHS = EL (SUC j) (h::l) :: DROP (SUC (SUC j)) (h::l)
         = EL j l :: DROP (SUC j) l    by EL, DROP_def
         = LHS
*)
Theorem rotate_shift_element:
  !l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))
Proof
  rw[rotate_def] >>
  pop_assum mp_tac >>
  qid_spec_tac `n` >>
  Induct_on `l` >- rw[] >>
  rw[DROP_def] >> Cases_on `n` >> fs[]
QED

(* Theorem: rotate 0 l = l *)
(* Proof:
     rotate 0 l
   = DROP 0 l ++ TAKE 0 l   by rotate_def
   = l ++ []                by DROP_def, TAKE_def
   = l                      by APPEND
*)
val rotate_0 = store_thm(
  "rotate_0",
  ``!l. rotate 0 l = l``,
  rw[rotate_def]);

(* Theorem: rotate n [] = [] *)
(* Proof:
     rotate n []
   = DROP n [] ++ TAKE n []   by rotate_def
   = [] ++ []                 by DROP_def, TAKE_def
   = []                       by APPEND
*)
val rotate_nil = store_thm(
  "rotate_nil",
  ``!n. rotate n [] = []``,
  rw[rotate_def]);

(* Theorem: rotate (LENGTH l) l = l *)
(* Proof:
     rotate (LENGTH l) l
   = DROP (LENGTH l) l ++ TAKE (LENGTH l) l   by rotate_def
   = [] ++ TAKE (LENGTH l) l                  by DROP_LENGTH_NIL
   = [] ++ l                                  by TAKE_LENGTH_ID
   = l
*)
val rotate_full = store_thm(
  "rotate_full",
  ``!l. rotate (LENGTH l) l = l``,
  rw[rotate_def, DROP_LENGTH_NIL]);

(* Theorem: n < LENGTH l ==> rotate (SUC n) l = rotate 1 (rotate n l) *)
(* Proof:
   Since n < LENGTH l, l <> [] by LENGTH_NIL.
   Thus  DROP n l <> []  by DROP_EQ_NIL  (need n < LENGTH l)
   Expand by rotate_def, this is to show:
   DROP (SUC n) l ++ TAKE (SUC n) l = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
   LHS = DROP (SUC n) l ++ TAKE (SUC n) l
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_SUC, TAKE_SUC
   Since DROP n l <> []  from above,
   RHS = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_1_APPEND, TAKE_1_APPEND
       = LHS
*)
val rotate_suc = store_thm(
  "rotate_suc",
  ``!l n. n < LENGTH l ==> (rotate (SUC n) l = rotate 1 (rotate n l))``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `DROP n l <> []` by simp[DROP_EQ_NIL] >>
  rw[rotate_def, DROP_1_APPEND, TAKE_1_APPEND, DROP_SUC, TAKE_SUC]);

(* Theorem: Rotate keeps LENGTH (of necklace): LENGTH (rotate n l) = LENGTH l *)
(* Proof:
     LENGTH (rotate n l)
   = LENGTH (DROP n l ++ TAKE n l)           by rotate_def
   = LENGTH (DROP n l) + LENGTH (TAKE n l)   by LENGTH_APPEND
   = LENGTH (TAKE n l) + LENGTH (DROP n l)   by arithmetic
   = LENGTH (TAKE n l ++ DROP n l)           by LENGTH_APPEND
   = LENGTH l                                by TAKE_DROP
*)
val rotate_same_length = store_thm(
  "rotate_same_length",
  ``!l n. LENGTH (rotate n l) = LENGTH l``,
  rpt strip_tac >>
  `LENGTH (rotate n l) = LENGTH (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = LENGTH (DROP n l) + LENGTH (TAKE n l)` by rw[] >>
  `_ = LENGTH (TAKE n l) + LENGTH (DROP n l)` by rw[ADD_COMM] >>
  `_ = LENGTH (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: Rotate keeps SET (of elements): set (rotate n l) = set l *)
(* Proof:
     set (rotate n l)
   = set (DROP n l ++ TAKE n l)            by rotate_def
   = set (DROP n l) UNION set (TAKE n l)   by LIST_TO_SET_APPEND
   = set (TAKE n l) UNION set (DROP n l)   by UNION_COMM
   = set (TAKE n l ++ DROP n l)            by LIST_TO_SET_APPEND
   = set l                                 by TAKE_DROP
*)
val rotate_same_set = store_thm(
  "rotate_same_set",
  ``!l n. set (rotate n l) = set l``,
  rpt strip_tac >>
  `set (rotate n l) = set (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = set (DROP n l) UNION set (TAKE n l)` by rw[] >>
  `_ = set (TAKE n l) UNION set (DROP n l)` by rw[UNION_COMM] >>
  `_ = set (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: n + m <= LENGTH l ==> rotate n (rotate m l) = rotate (n + m) l *)
(* Proof:
   By induction on n.
   Base case: !m l. 0 + m <= LENGTH l ==> (rotate 0 (rotate m l) = rotate (0 + m) l)
       rotate 0 (rotate m l)
     = rotate m l                by rotate_0
     = rotate (0 + m) l          by ADD
   Step case: !m l. SUC n + m <= LENGTH l ==> (rotate (SUC n) (rotate m l) = rotate (SUC n + m) l)
       rotate (SUC n) (rotate m l)
     = rotate 1 (rotate n (rotate m l))    by rotate_suc
     = rotate 1 (rotate (n + m) l)         by induction hypothesis
     = rotate (SUC (n + m)) l              by rotate_suc
     = rotate (SUC n + m) l                by ADD_CLAUSES
*)
val rotate_add = store_thm(
  "rotate_add",
  ``!n m l. n + m <= LENGTH l ==> (rotate n (rotate m l) = rotate (n + m) l)``,
  Induct >-
  rw[rotate_0] >>
  rw[] >>
  `LENGTH (rotate m l) = LENGTH l` by rw[rotate_same_length] >>
  `LENGTH (rotate (n + m) l) = LENGTH l` by rw[rotate_same_length] >>
  `n < LENGTH l /\ n + m < LENGTH l /\ n + m <= LENGTH l` by decide_tac >>
  rw[rotate_suc, ADD_CLAUSES]);

(* Theorem: !k. k < LENGTH l ==> rotate (LENGTH l - k) (rotate k l) = l *)
(* Proof:
   Since k < LENGTH l
     LENGTH 1 - k + k = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate (LENGTH l - k) (rotate k l)
   = rotate (LENGTH l - k + k) l        by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_lcancel = store_thm(
  "rotate_lcancel",
  ``!k l. k < LENGTH l ==> (rotate (LENGTH l - k) (rotate k l) = l)``,
  rpt strip_tac >>
  `LENGTH l - k + k = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* Theorem: !k. k < LENGTH l ==> rotate k (rotate (LENGTH l - k) l) = l *)
(* Proof:
   Since k < LENGTH l
     k + (LENGTH 1 - k) = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate k  (rotate (LENGTH l - k) l)
   = rotate (k + (LENGTH l - k)) l      by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_rcancel = store_thm(
  "rotate_rcancel",
  ``!k l. k < LENGTH l ==> (rotate k (rotate (LENGTH l - k) l) = l)``,
  rpt strip_tac >>
  `k + (LENGTH l - k) = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* ------------------------------------------------------------------------- *)
(* List Turn                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define a rotation turn of a list (like a turnstile) *)
val turn_def = Define`
    turn l = if l = [] then [] else ((LAST l) :: (FRONT l))
`;

(* Theorem: turn [] = [] *)
(* Proof: by turn_def *)
val turn_nil = store_thm(
  "turn_nil",
  ``turn [] = []``,
  rw[turn_def]);

(* Theorem: l <> [] ==> (turn l = (LAST l) :: (FRONT l)) *)
(* Proof: by turn_def *)
val turn_not_nil = store_thm(
  "turn_not_nil",
  ``!l. l <> [] ==> (turn l = (LAST l) :: (FRONT l))``,
  rw[turn_def]);

(* Theorem: LENGTH (turn l) = LENGTH l *)
(* Proof:
   If l = [],
        LENGTH (turn []) = LENGTH []     by turn_def
   If l <> [],
      Then LENGTH l <> 0                 by LENGTH_NIL
        LENGTH (turn l)
      = LENGTH ((LAST l) :: (FRONT l))   by turn_def
      = SUC (LENGTH (FRONT l))           by LENGTH
      = SUC (PRE (LENGTH l))             by LENGTH_FRONT
      = LENGTH l                         by SUC_PRE, 0 < LENGTH l
*)
val turn_length = store_thm(
  "turn_length",
  ``!l. LENGTH (turn l) = LENGTH l``,
  metis_tac[turn_def, list_CASES, LENGTH, LENGTH_FRONT_CONS, SUC_PRE, NOT_ZERO_LT_ZERO]);

(* Theorem: (turn p = []) <=> (p = []) *)
(* Proof:
       turn p = []
   <=> LENGTH (turn p) = 0     by LENGTH_NIL
   <=> LENGTH p = 0            by turn_length
   <=> p = []                  by LENGTH_NIL
*)
val turn_eq_nil = store_thm(
  "turn_eq_nil",
  ``!p. (turn p = []) <=> (p = [])``,
  metis_tac[turn_length, LENGTH_NIL]);

(* Theorem: ls <> [] ==> (HD (turn ls) = LAST ls) *)
(* Proof:
     HD (turn ls)
   = HD (LAST ls :: FRONT ls)    by turn_def, ls <> []
   = LAST ls                     by HD
*)
val head_turn = store_thm(
  "head_turn",
  ``!ls. ls <> [] ==> (HD (turn ls) = LAST ls)``,
  rw[turn_def]);

(* Theorem: ls <> [] ==> (TL (turn ls) = FRONT ls) *)
(* Proof:
     TL (turn ls)
   = TL (LAST ls :: FRONT ls)  by turn_def, ls <> []
   = FRONT ls                  by TL
*)
Theorem tail_turn:
  !ls. ls <> [] ==> (TL (turn ls) = FRONT ls)
Proof
  rw[turn_def]
QED

(* Theorem: turn (SNOC x ls) = x :: ls *)
(* Proof:
   Note (SNOC x ls) <> []                    by NOT_SNOC_NIL
     turn (SNOC x ls)
   = LAST (SNOC x ls) :: FRONT (SNOC x ls)   by turn_def
   = x :: FRONT (SNOC x ls)                  by LAST_SNOC
   = x :: ls                                 by FRONT_SNOC
*)
Theorem turn_snoc:
  !ls x. turn (SNOC x ls) = x :: ls
Proof
  metis_tac[NOT_SNOC_NIL, turn_def, LAST_SNOC, FRONT_SNOC]
QED

(* Overload repeated turns *)
val _ = overload_on("turn_exp", ``\l n. FUNPOW turn n l``);

(* Theorem: turn_exp l 0 = l *)
(* Proof:
     turn_exp l 0
   = FUNPOW turn 0 l    by notation
   = l                  by FUNPOW
*)
val turn_exp_0 = store_thm(
  "turn_exp_0",
  ``!l. turn_exp l 0 = l``,
  rw[]);

(* Theorem: turn_exp l 1 = turn l *)
(* Proof:
     turn_exp l 1
   = FUNPOW turn 1 l    by notation
   = turn l             by FUNPOW
*)
val turn_exp_1 = store_thm(
  "turn_exp_1",
  ``!l. turn_exp l 1 = turn l``,
  rw[]);

(* Theorem: turn_exp l 2 = turn (turn l) *)
(* Proof:
     turn_exp l 2
   = FUNPOW turn 2 l         by notation
   = turn (FUNPOW turn 1 l)  by FUNPOW_SUC
   = turn (turn_exp l 1)     by notation
   = turn (turn l)           by turn_exp_1
*)
val turn_exp_2 = store_thm(
  "turn_exp_2",
  ``!l. turn_exp l 2 = turn (turn l)``,
  metis_tac[FUNPOW_SUC, turn_exp_1, TWO]);

(* Theorem: turn_exp l (SUC n) = turn_exp (turn l) n *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = FUNPOW turn n (turn l)   by FUNPOW
   = turn_exp (turn l) n      by notation
*)
val turn_exp_SUC = store_thm(
  "turn_exp_SUC",
  ``!l n. turn_exp l (SUC n) = turn_exp (turn l) n``,
  rw[FUNPOW]);

(* Theorem: turn_exp l (SUC n) = turn (turn_exp l n) *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = turn (FUNPOW turn n l)   by FUNPOW_SUC
   = turn (turn_exp l n)      by notation
*)
val turn_exp_suc = store_thm(
  "turn_exp_suc",
  ``!l n. turn_exp l (SUC n) = turn (turn_exp l n)``,
  rw[FUNPOW_SUC]);

(* Theorem: LENGTH (turn_exp l n) = LENGTH l *)
(* Proof:
   By induction on n.
   Base: LENGTH (turn_exp l 0) = LENGTH l
      True by turn_exp l 0 = l         by turn_exp_0
   Step: LENGTH (turn_exp l n) = LENGTH l ==> LENGTH (turn_exp l (SUC n)) = LENGTH l
        LENGTH (turn_exp l (SUC n))
      = LENGTH (turn (turn_exp l n))   by turn_exp_suc
      = LENGTH (turn_exp l n)          by turn_length
      = LENGTH l                       by induction hypothesis
*)
val turn_exp_length = store_thm(
  "turn_exp_length",
  ``!l n. LENGTH (turn_exp l n) = LENGTH l``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[turn_exp_suc, turn_length]);

(* Theorem: n < LENGTH ls ==>
            (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls) *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==>
              HD (turn_exp ls 0) = EL 0 ls
           HD (turn_exp ls 0)
         = HD ls                 by FUNPOW_0
         = EL 0 ls               by EL
   Step: !ls. n < LENGTH ls ==> HD (turn_exp ls n) = EL (if n = 0 then 0 else (LENGTH ls - n)) ls ==>
         !ls. SUC n < LENGTH ls ==> HD (turn_exp ls (SUC n)) = EL (LENGTH ls - SUC n) ls
         Let k = LENGTH ls, then SUC n < k
         Note LENGTH (FRONT ls) = PRE k     by FRONT_LENGTH
          and n < PRE k                     by SUC n < k
         Also LENGTH (turn ls) = k          by turn_length
           so n < k                         by n < SUC n, SUC n < k
         Note ls <> []                      by k <> 0

           HD (turn_exp ls (SUC n))
         = HD (turn_exp (turn ls) n)                    by turn_exp_SUC
         = EL (if n = 0 then 0 else (LENGTH (turn ls) - n)) (turn ls)
                                                        by induction hypothesis, apply to (turn ls)
         = EL (if n = 0 then 0 else (k - n) (turn ls))  by above

         If n = 0,
         = EL 0 (turn ls)
         = LAST ls                           by turn_def
         = EL (PRE k) ls                     by LAST_EL
         = EL (k - SUC 0) ls                 by ONE
         If n <> 0
         = EL (k - n) (turn ls)
         = EL (k - n) (LAST ls :: FRONT ls)  by turn_def
         = EL (k - n - 1) (FRONT ls)         by EL
         = EL (k - n - 1) ls                 by FRONT_EL, k - n - 1 < PRE k, n <> 0
         = EL (k - SUC n) ls                 by arithmetic
*)
val head_turn_exp = store_thm(
  "head_turn_exp",
  ``!ls n. n < LENGTH ls ==>
         (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls)``,
  (Induct_on `n` >> simp[]) >>
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH ls` >>
  `n < k` by rw[Abbr`k`] >>
  `LENGTH (turn ls) = k` by rw[turn_length, Abbr`k`] >>
  `HD (turn_exp ls (SUC n)) = HD (turn_exp (turn ls) n)` by rw[turn_exp_SUC] >>
  `_ = EL (if n = 0 then 0 else (k - n)) (turn ls)` by rw[] >>
  `k <> 0` by decide_tac >>
  `ls <> []` by metis_tac[LENGTH_NIL] >>
  (Cases_on `n = 0` >> fs[]) >| [
    `PRE k = k - 1` by decide_tac >>
    rw[head_turn, LAST_EL],
    `k - n = SUC (k - SUC n)` by decide_tac >>
    rw[turn_def, Abbr`k`] >>
    `LENGTH (FRONT ls) = PRE (LENGTH ls)` by rw[FRONT_LENGTH] >>
    `n < PRE (LENGTH ls)` by decide_tac >>
    rw[FRONT_EL]
  ]);

(* ------------------------------------------------------------------------- *)
(* SUM Theorems                                                              *)
(* ------------------------------------------------------------------------- *)

(* Defined: SUM for summation of list = sequence *)

(* Theorem: SUM [] = 0 *)
(* Proof: by definition. *)
val SUM_NIL = save_thm("SUM_NIL", SUM |> CONJUNCT1);
(* > val SUM_NIL = |- SUM [] = 0 : thm *)

(* Theorem: SUM h::t = h + SUM t *)
(* Proof: by definition. *)
val SUM_CONS = save_thm("SUM_CONS", SUM |> CONJUNCT2);
(* val SUM_CONS = |- !h t. SUM (h::t) = h + SUM t: thm *)

(* Theorem: SUM [n] = n *)
(* Proof: by SUM *)
val SUM_SING = store_thm(
  "SUM_SING",
  ``!n. SUM [n] = n``,
  rw[]);

(* Theorem: SUM (s ++ t) = SUM s + SUM t *)
(* Proof: by induction on s *)
(*
val SUM_APPEND = store_thm(
  "SUM_APPEND",
  ``!s t. SUM (s ++ t) = SUM s + SUM t``,
  Induct_on `s` >-
  rw[] >>
  rw[ADD_ASSOC]);
*)
(* There is already a SUM_APPEND in up-to-date listTheory *)

(* Theorem: constant multiplication: k * SUM s = SUM (k * s)  *)
(* Proof: by induction on s.
   Base case: !k. k * SUM [] = SUM (MAP ($* k) [])
     LHS = k * SUM [] = k * 0 = 0         by SUM_NIL, MULT_0
         = SUM []                         by SUM_NIL
         = SUM (MAP ($* k) []) = RHS      by MAP
   Step case: !k. k * SUM s = SUM (MAP ($* k) s) ==>
              !h k. k * SUM (h::s) = SUM (MAP ($* k) (h::s))
     LHS = k * SUM (h::s)
         = k * (h + SUM s)                by SUM_CONS
         = k * h + k * SUM s              by LEFT_ADD_DISTRIB
         = k * h + SUM (MAP ($* k) s)     by induction hypothesis
         = SUM (k * h :: (MAP ($* k) s))  by SUM_CONS
         = SUM (MAP ($* k) (h::s))        by MAP
         = RHS
*)
val SUM_MULT = store_thm(
  "SUM_MULT",
  ``!s k. k * SUM s = SUM (MAP ($* k) s)``,
  Induct_on `s` >-
  metis_tac[SUM, MAP, MULT_0] >>
  metis_tac[SUM, MAP, LEFT_ADD_DISTRIB]);

(* Theorem: (m + n) * SUM s = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- RIGHT_ADD_DISTRIB;
> val it = |- !m n p. (m + n) * p = m * p + n * p : thm
     (m + n) * SUM s
   = m * SUM s + n * SUM s                               by RIGHT_ADD_DISTRIB
   = SUM (MAP (\x. m * x) s) + SUM (MAP (\x. n * x) s)   by SUM_MULT
*)
val SUM_RIGHT_ADD_DISTRIB = store_thm(
  "SUM_RIGHT_ADD_DISTRIB",
  ``!s m n. (m + n) * SUM s = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[RIGHT_ADD_DISTRIB, SUM_MULT]);

(* Theorem: (SUM s) * (m + n) = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- LEFT_ADD_DISTRIB;
> val it = |- !m n p. p * (m + n) = p * m + p * n : thm
     (SUM s) * (m + n)
   = (m + n) * SUM s                           by MULT_COMM
   = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)   by SUM_RIGHT_ADD_DISTRIB
*)
val SUM_LEFT_ADD_DISTRIB = store_thm(
  "SUM_LEFT_ADD_DISTRIB",
  ``!s m n. (SUM s) * (m + n) = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[SUM_RIGHT_ADD_DISTRIB, MULT_COMM]);


(*
- EVAL ``GENLIST I 4``;
> val it = |- GENLIST I 4 = [0; 1; 2; 3] : thm
- EVAL ``GENLIST SUC 4``;
> val it = |- GENLIST SUC 4 = [1; 2; 3; 4] : thm
- EVAL ``GENLIST (\k. binomial 4 k) 5``;
> val it = |- GENLIST (\k. binomial 4 k) 5 = [1; 4; 6; 4; 1] : thm
- EVAL ``GENLIST (\k. binomial 5 k) 6``;
> val it = |- GENLIST (\k. binomial 5 k) 6 = [1; 5; 10; 10; 5; 1] : thm
- EVAL ``GENLIST (\k. binomial 10 k) 11``;
> val it = |- GENLIST (\k. binomial 10 k) 11 = [1; 10; 45; 120; 210; 252; 210; 120; 45; 10; 1] : thm
*)

(* Theorems on GENLIST:

- GENLIST;
> val it = |- (!f. GENLIST f 0 = []) /\
               !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) : thm
- NULL_GENLIST;
> val it = |- !n f. NULL (GENLIST f n) <=> (n = 0) : thm
- GENLIST_CONS;
> val it = |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n : thm
- EL_GENLIST;
> val it = |- !f n x. x < n ==> (EL x (GENLIST f n) = f x) : thm
- EXISTS_GENLIST;
> val it = |- !n. EXISTS P (GENLIST f n) <=> ?i. i < n /\ P (f i) : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
- GENLIST_APPEND;
> val it = |- !f a b. GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a : thm
- HD_GENLIST;
> val it = |- HD (GENLIST f (SUC n)) = f 0 : thm
- TL_GENLIST;
> val it = |- !f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n : thm
- HD_GENLIST_COR;
> val it = |- !n f. 0 < n ==> (HD (GENLIST f n) = f 0) : thm
- GENLIST_FUN_EQ;
> val it = |- !n f g. (GENLIST f n = GENLIST g n) <=> !x. x < n ==> (f x = g x) : thm

*)

(* Theorem: SUM (GENLIST f n) = SIGMA f (count n) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f 0) = SIGMA f (count 0)

         SUM (GENLIST f 0)
       = SUM []                by GENLIST_0
       = 0                     by SUM_NIL
       = SIGMA f {}            by SUM_IMAGE_THM
       = SIGMA f (count 0)     by COUNT_0

   Step: SUM (GENLIST f n) = SIGMA f (count n) ==>
         SUM (GENLIST f (SUC n)) = SIGMA f (count (SUC n))

         SUM (GENLIST f (SUC n))
       = SUM (SNOC (f n) (GENLIST f n))   by GENLIST
       = f n + SUM (GENLIST f n)          by SUM_SNOC
       = f n + SIGMA f (count n)          by induction hypothesis
       = f n + SIGMA f (count n DELETE n) by IN_COUNT, DELETE_NON_ELEMENT
       = SIGMA f (n INSERT count n)       by SUM_IMAGE_THM, FINITE_COUNT
       = SIGMA f (count (SUC n))          by COUNT_SUC
*)
val SUM_GENLIST = store_thm(
  "SUM_GENLIST",
  ``!f n. SUM (GENLIST f n) = SIGMA f (count n)``,
  strip_tac >>
  Induct >-
  rw[SUM_IMAGE_THM] >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by rw[GENLIST] >>
  `_ = f n + SUM (GENLIST f n)` by rw[SUM_SNOC] >>
  `_ = f n + SIGMA f (count n)` by rw[] >>
  `_ = f n + SIGMA f (count n DELETE n)`
    by metis_tac[IN_COUNT, prim_recTheory.LESS_REFL, DELETE_NON_ELEMENT] >>
  `_ = SIGMA f (n INSERT count n)` by rw[SUM_IMAGE_THM] >>
  `_ = SIGMA f (count (SUC n))` by rw[COUNT_SUC] >>
  decide_tac);

(* Theorem: SUM (k=0..n) f(k) = f(0) + SUM (k=1..n) f(k)  *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (f 0 :: GENLIST (f o SUC) n)   by GENLIST_CONS
   = f 0 + SUM (GENLIST (f o SUC) n)    by SUM definition.
*)
val SUM_DECOMPOSE_FIRST = store_thm(
  "SUM_DECOMPOSE_FIRST",
  ``!f n. SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) n)``,
  metis_tac[GENLIST_CONS, SUM]);

(* Theorem: SUM (k=0..n) f(k) = SUM (k=0..(n-1)) f(k) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (SNOC (f n) (GENLIST f n))  by GENLIST definition
   = SUM ((GENLIST f n) ++ [f n])    by SNOC_APPEND
   = SUM (GENLIST f n) + SUM [f n]   by SUM_APPEND
   = SUM (GENLIST f n) + f n         by SUM definition: SUM (h::t) = h + SUM t, and SUM [] = 0.
*)
val SUM_DECOMPOSE_LAST = store_thm(
  "SUM_DECOMPOSE_LAST",
  ``!f n. SUM (GENLIST f (SUC n)) = SUM (GENLIST f n) + f n``,
  rpt strip_tac >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by metis_tac[GENLIST] >>
  `_ = SUM ((GENLIST f n) ++ [f n])` by metis_tac[SNOC_APPEND] >>
  `_ = SUM (GENLIST f n) + SUM [f n]` by metis_tac[SUM_APPEND] >>
  rw[SUM]);

(* Theorem: SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof: by induction on n.
   Base case: !a b. SUM (GENLIST a 0) + SUM (GENLIST b 0) = SUM (GENLIST (\k. a k + b k) 0)
     Since GENLIST f 0 = []    by GENLIST
       and SUM [] = 0          by SUM_NIL
     This is just 0 + 0 = 0, true by arithmetic.
   Step case: !a b. SUM (GENLIST a n) + SUM (GENLIST b n) =
                    SUM (GENLIST (\k. a k + b k) n) ==>
              !a b. SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)) =
                    SUM (GENLIST (\k. a k + b k) (SUC n))
       SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)
     = (SUM (GENLIST a n) + a n) + (SUM (GENLIST b n) + b n)  by SUM_DECOMPOSE_LAST
     = SUM (GENLIST a n) + SUM (GENLIST b n) + (a n + b n)    by arithmetic
     = SUM (GENLIST (\k. a k + b k) n) + (a n + b n)          by induction hypothesis
     = SUM (GENLIST (\k. a k + b k) (SUC n))                  by SUM_DECOMPOSE_LAST
*)
val SUM_ADD_GENLIST = store_thm(
  "SUM_ADD_GENLIST",
  ``!a b n. SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  Induct_on `n` >-
  rw[] >>
  rw[SUM_DECOMPOSE_LAST]);

(* Theorem: SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof:
     SUM (GENLIST a n ++ GENLIST b n)
   = SUM (GENLIST a n) + SUM (GENLIST b n)  by SUM_APPEND
   = SUM (GENLIST (\k. a k + b k) n)        by SUM_ADD_GENLIST
*)
val SUM_GENLIST_APPEND = store_thm(
  "SUM_GENLIST_APPEND",
  ``!a b n. SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  metis_tac[SUM_APPEND, SUM_ADD_GENLIST]);

(* Theorem: 0 < n ==> SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (GENLIST f n) + f n                       by SUM_DECOMPOSE_LAST
   = SUM (GENLIST f (SUC m)) + f n                 by n = SUC m, 0 < n
   = f 0 + SUM (GENLIST (f o SUC) m) + f n         by SUM_DECOMPOSE_FIRST
   = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n   by PRE_SUC_EQ
*)
val SUM_DECOMPOSE_FIRST_LAST = store_thm(
  "SUM_DECOMPOSE_FIRST_LAST",
  ``!f n. 0 < n ==> (SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n)``,
  metis_tac[SUM_DECOMPOSE_LAST, SUM_DECOMPOSE_FIRST, SUC_EXISTS, PRE_SUC_EQ]);

(* Theorem: (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n *)
(* Proof: by list induction.
   Base case: SUM [] MOD n = SUM (MAP (\x. x MOD n) []) MOD n
      true by SUM [] = 0, MAP f [] = 0, and 0 MOD n = 0.
   Step case: SUM l MOD n = SUM (MAP (\x. x MOD n) l) MOD n ==>
              !h. SUM (h::l) MOD n = SUM (MAP (\x. x MOD n) (h::l)) MOD n
      SUM (h::l) MOD n
    = (h + SUM l) MOD n                                           by SUM
    = (h MOD n + (SUM l) MOD n) MOD n                             by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n           by induction hypothesis
    = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n   by MOD_MOD
    = ((h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n) MOD n         by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n                 by MOD_MOD
    = (SUM (h MOD n ::(MAP (\x. x MOD n) l))) MOD n               by SUM
    = (SUM (MAP (\x. x MOD n) (h::l))) MOD n                      by MAP
*)
val SUM_MOD = store_thm(
  "SUM_MOD",
  ``!n. 0 < n ==> !l. (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n``,
  rpt strip_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `SUM (h::l) MOD n = (h MOD n + (SUM l) MOD n) MOD n` by rw_tac std_ss[SUM, MOD_PLUS] >>
  `_ = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n` by rw_tac std_ss[MOD_MOD] >>
  rw[MOD_PLUS]);

(* Theorem: SUM l = 0 <=> l = EVERY (\x. x = 0) l *)
(* Proof: by induction on l.
   Base case: (SUM [] = 0) <=> EVERY (\x. x = 0) []
      true by SUM [] = 0 and GENLIST f 0 = [].
   Step case: (SUM l = 0) <=> EVERY (\x. x = 0) l ==>
              !h. (SUM (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
       SUM (h::l) = 0
   <=> h + SUM l = 0                  by SUM
   <=> h = 0 /\ SUM l = 0             by ADD_EQ_0
   <=> h = 0 /\ EVERY (\x. x = 0) l   by induction hypothesis
   <=> EVERY (\x. x = 0) (h::l)       by EVERY_DEF
*)
val SUM_EQ_0 = store_thm(
  "SUM_EQ_0",
  ``!l. (SUM l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[]);

(* Theorem: SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
            SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n *)
(* Proof:
     SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n
   = SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n  by SUM_MOD
   = SUM (GENLIST ((\x. x MOD n) o ((\k. f k) o SUC)) (PRE n)) MOD n    by MAP_GENLIST
   = SUM (GENLIST ((\x. x MOD n) o (\k. f k) o SUC) (PRE n)) MOD n      by composition associative
   = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n                by composition
*)
val SUM_GENLIST_MOD = store_thm(
  "SUM_GENLIST_MOD",
  ``!n. 0 < n ==> !f. SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n``,
  rpt strip_tac >>
  `SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
    SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n` by metis_tac[SUM_MOD] >>
  rw_tac std_ss[MAP_GENLIST, combinTheory.o_ASSOC, combinTheory.o_ABS_L]);

(* Theorem: SUM (GENLIST (\j. x) n) = n * x *)
(* Proof:
   By induction on n.
   Base case: !x. SUM (GENLIST (\j. x) 0) = 0 * x
       SUM (GENLIST (\j. x) 0)
     = SUM []                   by GENLIST
     = 0                        by SUM
     = 0 * x                    by MULT
   Step case: !x. SUM (GENLIST (\j. x) n) = n * x ==>
              !x. SUM (GENLIST (\j. x) (SUC n)) = SUC n * x
       SUM (GENLIST (\j. x) (SUC n))
     = SUM (SNOC x (GENLIST (\j. x) n))   by GENLIST
     = SUM (GENLIST (\j. x) n) + x        by SUM_SNOC
     = n * x + x                          by induction hypothesis
     = SUC n * x                          by MULT
*)
val SUM_CONSTANT = store_thm(
  "SUM_CONSTANT",
  ``!n x. SUM (GENLIST (\j. x) n) = n * x``,
  Induct >-
  rw[] >>
  rw_tac std_ss[GENLIST, SUM_SNOC, MULT]);

(* Theorem: SUM (GENLIST (K m) n) = m * n *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST (K m) 0) = m * 0
        SUM (GENLIST (K m) 0)
      = SUM []                 by GENLIST
      = 0                      by SUM
      = m * 0                  by MULT_0
   Step: SUM (GENLIST (K m) n) = m * n ==> SUM (GENLIST (K m) (SUC n)) = m * SUC n
        SUM (GENLIST (K m) (SUC n))
      = SUM (SNOC m (GENLIST (K m) n))    by GENLIST
      = SUM (GENLIST (K m) n) + m         by SUM_SNOC
      = m * n + m                         by induction hypothesis
      = m + m * n                         by ADD_COMM
      = m * SUC n                         by MULT_SUC
*)
val SUM_GENLIST_K = store_thm(
  "SUM_GENLIST_K",
  ``!m n. SUM (GENLIST (K m) n) = m * n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, SUM_SNOC, MULT_SUC]);

(* Theorem: (LENGTH l1 = LENGTH l2) /\ (!k. k <= LENGTH l1 ==> EL k l1 <= EL k l2) ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on l1.
   Base: LENGTH [] = LENGTH l2 ==> SUM [] <= SUM l2
       Note l2 = []               by LENGTH_EQ_0
         so SUM [] = SUM []
         or SUM [] <= SUM l2      by EQ_LESS_EQ
   Step: !l2. (LENGTH l1 = LENGTH l2) /\ ... ==> SUM l1 <= SUM l2 ==>
         (LENGTH (h::l1) = LENGTH l2) /\ ... ==> SUM h::l1 <= SUM l2
       Note l2 <> []              by LENGTH_EQ_0
         so ?h1 t2. l2 = h1::t1   by list_CASES
        and LENGTH l1 = LENGTH t1 by LENGTH
            SUM (h::l1)
          = h + SUM l1            by SUM_CONS
          <= h1 + SUM t1          by EL_ALL_PROPERTY, induction hypothesis
           = SUM l2               by SUM_CONS
*)
val SUM_LE = store_thm(
  "SUM_LE",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) /\ (!k. k < LENGTH l1 ==> EL k l1 <= EL k l2) ==>
           SUM l1 <= SUM l2``,
  Induct >-
  metis_tac[LENGTH_EQ_0, EQ_LESS_EQ] >>
  rpt strip_tac >>
  `?h1 t1. l2 = h1::t1` by metis_tac[LENGTH_EQ_0, list_CASES] >>
  `LENGTH l1 = LENGTH t1` by metis_tac[LENGTH, SUC_EQ] >>
  `SUM (h::l1) = h + SUM l1` by rw[SUM_CONS] >>
  `SUM l2 = h1 + SUM t1` by rw[SUM_CONS] >>
  `(h <= h1) /\ SUM l1 <= SUM t1` by metis_tac[EL_ALL_PROPERTY] >>
  decide_tac);

(* Theorem: MEM x l ==> x <= SUM l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= SUM []
      True since MEM x [] = F              by MEM
   Step: !x. MEM x l ==> x <= SUM l ==> !h x. MEM x (h::l) ==> x <= SUM (h::l)
      If x = h,
         Then h <= h + SUM l = SUM (h::l)  by SUM
      If x <> h,
         Then MEM x l                      by MEM
          ==> x <= SUM l                   by induction hypothesis
           or x <= h + SUM l = SUM (h::l)  by SUM
*)
val SUM_LE_MEM = store_thm(
  "SUM_LE_MEM",
  ``!l x. MEM x l ==> x <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >-
  decide_tac >>
  `x <= SUM l` by rw[] >>
  decide_tac);

(* Theorem: n < LENGTH l ==> (EL n l) <= SUM l *)
(* Proof: by SUM_LE_MEM, MEM_EL *)
val SUM_LE_EL = store_thm(
  "SUM_LE_EL",
  ``!l n. n < LENGTH l ==> (EL n l) <= SUM l``,
  metis_tac[SUM_LE_MEM, MEM_EL]);

(* Theorem: m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l *)
(* Proof:
   By induction on l.
   Base: !m n. m < n /\ n < LENGTH [] ==> EL m [] + EL n [] <= SUM []
      True since n < LENGTH [] = F              by LENGTH
   Step: !m n. m < LENGTH l /\ n < LENGTH l ==> EL m l + EL n l <= SUM l ==>
         !h m n. m < LENGTH (h::l) /\ n < LENGTH (h::l) ==> EL m (h::l) + EL n (h::l) <= SUM (h::l)
      Note 0 < n, or n <> 0             by m < n
        so ?k. n = SUC k            by num_CASES
       and k < LENGTH l             by SUC k < SUC (LENGTH l)
       and EL n (h::l) = EL k l     by EL_restricted
      If m = 0,
         Then EL m (h::l) = h       by EL_restricted
          and EL k l <= SUM l       by SUM_LE_EL
         Thus EL m (h::l) + EL n (h::l)
            = h + SUM l
            = SUM (h::l)            by SUM
      If m <> 0,
         Then ?j. m = SUC j         by num_CASES
          and j < k                 by SUC j < SUC k
          and EL m (h::l) = EL j l  by EL_restricted
         Thus EL m (h::l) + EL n (h::l)
            = EL j l + EL k l       by above
           <= SUM l                 by induction hypothesis
           <= h + SUM l             by arithmetic
            = SUM (h::l)            by SUM
*)
val SUM_LE_SUM_EL = store_thm(
  "SUM_LE_SUM_EL",
  ``!l m n. m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >>
  `n <> 0` by decide_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES] >>
  `k < LENGTH l` by decide_tac >>
  `EL n (h::l) = EL k l` by rw[] >>
  Cases_on `m = 0` >| [
    `EL m (h::l) = h` by rw[] >>
    `EL k l <= SUM l` by rw[SUM_LE_EL] >>
    decide_tac,
    `?j. m = SUC j` by metis_tac[num_CASES] >>
    `j < k` by decide_tac >>
    `EL m (h::l) = EL j l` by rw[] >>
    `EL j l + EL k l <= SUM l` by rw[] >>
    decide_tac
  ]);

(* Theorem: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) *)
(* Proof:
   The computation is:
       n + (n * 2) + (n * 4) + ... + (n * (2 ** (m - 1)))
     = n * (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n * (2 ** m - 1)

   By induction on m.
   Base: SUM (GENLIST (\j. n * 2 ** j) 0) = n * (2 ** 0 - 1)
      LHS = SUM (GENLIST (\j. n * 2 ** j) 0)
          = SUM []                by GENLIST_0
          = 0                     by PROD
      RHS = n * (1 - 1)           by EXP_0
          = n * 0 = 0 = LHS       by MULT_0
   Step: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) ==>
         SUM (GENLIST (\j. n * 2 ** j) (SUC m)) = n * (2 ** SUC m - 1)
         SUM (GENLIST (\j. n * 2 ** j) (SUC m))
       = SUM (SNOC (n * 2 ** m) (GENLIST (\j. n * 2 ** j) m))   by GENLIST
       = SUM (GENLIST (\j. n * 2 ** j) m) + (n * 2 ** m)        by SUM_SNOC
       = n * (2 ** m - 1) + n * 2 ** m                          by induction hypothesis
       = n * (2 ** m - 1 + 2 ** m)                              by LEFT_ADD_DISTRIB
       = n * (2 * 2 ** m - 1)                                   by arithmetic
       = n * (2 ** SUC m - 1)                                   by EXP
*)
val SUM_DOUBLING_LIST = store_thm(
  "SUM_DOUBLING_LIST",
  ``!m n. SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n * 2 ** j` >>
  `SUM (GENLIST f (SUC m)) = SUM (SNOC (n * 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = SUM (GENLIST f m) + (n * 2 ** m)` by rw[SUM_SNOC] >>
  `_ = n * (2 ** m - 1) + n * 2 ** m` by rw[] >>
  `_ = n * (2 ** m - 1 + 2 ** m)` by rw[LEFT_ADD_DISTRIB] >>
  rw[EXP]);


(* Idea: key theorem, almost like pigeonhole principle. *)

(* List equivalent sum theorems. This is an example of digging out theorems. *)

(* Theorem: EVERY (\x. 0 < x) ls ==> LENGTH ls <= SUM ls *)
(* Proof:
   Let P = (\x. 0 < x).
   By induction on list ls.
   Base: EVERY P [] ==> LENGTH [] <= SUM []
      Note EVERY P [] = T      by EVERY_DEF
       and LENGTH [] = 0       by LENGTH
       and SUM [] = 0          by SUM
      Hence true.
   Step: EVERY P ls ==> LENGTH ls <= SUM ls ==>
         !h. EVERY P (h::ls) ==> LENGTH (h::ls) <= SUM (h::ls)
      Note 0 < h /\ EVERY P ls by EVERY_DEF
           LENGTH (h::ls)
         = 1 + LENGTH ls       by LENGTH
        <= 1 + SUM ls          by induction hypothesis
        <= h + SUM ls          by 0 < h
         = SUM (h::ls)         by SUM
*)
Theorem list_length_le_sum:
  !ls. EVERY (\x. 0 < x) ls ==> LENGTH ls <= SUM ls
Proof
  Induct >-
  rw[] >>
  rw[] >>
  `1 <= h` by decide_tac >>
  fs[]
QED

(* Theorem: EVERY (\x. 0 < x) ls /\ LENGTH ls = SUM ls ==> EVERY (\x. x = 1) ls *)
(* Proof:
   Let P = (\x. 0 < x), Q = (\x. x = 1).
   By induction on list ls.
   Base: EVERY P [] /\ LENGTH [] = SUM [] ==> EVERY Q []
      Note EVERY Q [] = T      by EVERY_DEF
      Hence true.
   Step: EVERY P ls /\ LENGTH ls = SUM ls ==> EVERY Q ls ==>
         !h. EVERY P (h::ls) /\ LENGTH (h::ls) = SUM (h::ls) ==> EVERY Q (h::ls)
      Note 0 < h /\ EVERY P ls by EVERY_DEF
      LHS = LENGTH (h::ls)
          = 1 + LENGTH ls      by LENGTH
         <= 1 + SUM ls         by list_length_le_sum
      RHS = SUM (h::ls)
          = h + SUM ls         by SUM
      Thus h + SUM ls <= 1 + SUM ls
       or h <= 1               by arithmetic
      giving h = 1             by 0 < h
      Thus LENGTH ls = SUM ls  by arithmetic
       and EVERY Q ls          by induction hypothesis
        or EVERY Q (h::ls)     by EVERY_DEF, h = 1
*)
Theorem list_length_eq_sum:
  !ls. EVERY (\x. 0 < x) ls /\ LENGTH ls = SUM ls ==> EVERY (\x. x = 1) ls
Proof
  Induct >-
  rw[] >>
  rpt strip_tac >>
  fs[] >>
  `LENGTH ls <= SUM ls` by rw[list_length_le_sum] >>
  `h + LENGTH ls <= SUC (LENGTH ls)` by fs[] >>
  `h = 1` by decide_tac >>
  `SUM ls = LENGTH ls` by fs[] >>
  simp[]
QED

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MAX_LIST (MAP f []) = f (MAX_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MAX_LIST (MAP f ls) = f (MAX_LIST ls) ==>
         !h. h::ls <> [] ==> MAX_LIST (MAP f (h::ls)) = f (MAX_LIST (h::ls))
      If ls = [],
         MAX_LIST (MAP f [h])
       = MAX_LIST [f h]             by MAP
       = f h                        by MAX_LIST_def
       = f (MAX_LIST [h])           by MAX_LIST_def
      If ls <> [],
         MAX_LIST (MAP f (h::ls))
       = MAX_LIST (f h::MAP f ls)        by MAP
       = MAX (f h) MAX_LIST (MAP f ls)   by MAX_LIST_def
       = MAX (f h) (f (MAX_LIST ls))     by induction hypothesis
       = f (MAX h (MAX_LIST ls))         by MAX_SWAP
       = f (MAX_LIST (h::ls))            by MAX_LIST_def
*)
val MAX_LIST_MONO_MAP = store_thm(
  "MAX_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MAX_SWAP]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MIN_LIST (MAP f []) = f (MIN_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MIN_LIST (MAP f ls) = f (MIN_LIST ls) ==>
         !h. h::ls <> [] ==> MIN_LIST (MAP f (h::ls)) = f (MIN_LIST (h::ls))
      If ls = [],
         MIN_LIST (MAP f [h])
       = MIN_LIST [f h]             by MAP
       = f h                        by MIN_LIST_def
       = f (MIN_LIST [h])           by MIN_LIST_def
      If ls <> [],
         MIN_LIST (MAP f (h::ls))
       = MIN_LIST (f h::MAP f ls)        by MAP
       = MIN (f h) MIN_LIST (MAP f ls)   by MIN_LIST_def
       = MIN (f h) (f (MIN_LIST ls))     by induction hypothesis
       = f (MIN h (MIN_LIST ls))         by MIN_SWAP
       = f (MIN_LIST (h::ls))            by MIN_LIST_def
*)
val MIN_LIST_MONO_MAP = store_thm(
  "MIN_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MIN_SWAP]);

(* ------------------------------------------------------------------------- *)
(* List Nub and Set                                                          *)
(* ------------------------------------------------------------------------- *)

(* Note:
> nub_def;
|- (nub [] = []) /\ !x l. nub (x::l) = if MEM x l then nub l else x::nub l
*)

(* Theorem: nub [] = [] *)
(* Proof: by nub_def *)
val nub_nil = save_thm("nub_nil", nub_def |> CONJUNCT1);
(* val nub_nil = |- nub [] = []: thm *)

(* Theorem: nub (x::l) = if MEM x l then nub l else x::nub l *)
(* Proof: by nub_def *)
val nub_cons = save_thm("nub_cons", nub_def |> CONJUNCT2);
(* val nub_cons = |- !x l. nub (x::l) = if MEM x l then nub l else x::nub l: thm *)

(* Theorem: nub [x] = [x] *)
(* Proof:
     nub [x]
   = nub (x::[])   by notation
   = x :: nub []   by nub_cons, MEM x [] = F
   = x ::[]        by nub_nil
   = [x]           by notation
*)
val nub_sing = store_thm(
  "nub_sing",
  ``!x. nub [x] = [x]``,
  rw[nub_def]);

(* Theorem: ALL_DISTINCT (nub l) *)
(* Proof:
   By induction on l.
   Base: ALL_DISTINCT (nub [])
         ALL_DISTINCT (nub [])
     <=> ALL_DISTINCT []               by nub_nil
     <=> T                             by ALL_DISTINCT
   Step: ALL_DISTINCT (nub l) ==> !h. ALL_DISTINCT (nub (h::l))
     If MEM h l,
        Then nub (h::l) = nub l        by nub_cons
        Thus ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (nub (h::l))
     If ~(MEM h l),
        Then nub (h::l) = h:nub l      by nub_cons
        With ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (h::nub l)   by ALL_DISTINCT, ~(MEM h l)
          or ALL_DISTINCT (nub (h::l))
*)
val nub_all_distinct = store_thm(
  "nub_all_distinct",
  ``!l. ALL_DISTINCT (nub l)``,
  Induct >-
  rw[nub_nil] >>
  rw[nub_cons]);

(* Theorem: CARD (set l) = LENGTH (nub l) *)
(* Proof:
   Note set (nub l) = set l    by nub_set
    and ALL_DISTINCT (nub l)   by nub_all_distinct
        CARD (set l)
      = CARD (set (nub l))     by above
      = LENGTH (nub l)         by ALL_DISTINCT_CARD_LIST_TO_SET, ALL_DISTINCT (nub l)
*)
val CARD_LIST_TO_SET_EQ = store_thm(
  "CARD_LIST_TO_SET_EQ",
  ``!l. CARD (set l) = LENGTH (nub l)``,
  rpt strip_tac >>
  `set (nub l) = set l` by rw[nub_set] >>
  `ALL_DISTINCT (nub l)` by rw[nub_all_distinct] >>
  rw[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]);

(* Theorem: set [x] = {x} *)
(* Proof:
     set [x]
   = x INSERT set []              by LIST_TO_SET
   = x INSERT {}                  by LIST_TO_SET
   = {x}                          by INSERT_DEF
*)
val MONO_LIST_TO_SET = store_thm(
  "MONO_LIST_TO_SET",
  ``!x. set [x] = {x}``,
  rw[]);

(* Theorem: ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
            ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2)) *)
(* Proof:
   Note MEM h (h::l1)          by MEM
     or h IN set (h::l1)       by notation
     so h IN set l2            by given
     or h IN set (nub l2)      by nub_set
     so MEM h (nub l2)         by notation
     or ?p1 p2. nub l2 = p1 ++ [h] ++ h2
     and  ~(MEM h p1) /\ ~(MEM h p2)           by MEM_SPLIT_APPEND_distinct
   Remaining goal: set l1 = set (p1 ++ p2)

   Step 1: show set l1 SUBSET set (p1 ++ p2)
       Let x IN set l1.
       Then MEM x l1 ==> MEM x (h::l1)   by MEM
         so x IN set (h::l1)
         or x IN set l2                  by given
         or x IN set (nub l2)            by nub_set
         or MEM x (nub l2)               by notation
        But h <> x  since MEM x l1 but ~MEM h l1
         so MEM x (p1 ++ p2)             by MEM, MEM_APPEND
         or x IN set (p1 ++ p2)          by notation
        Thus l1 SUBSET set (p1 ++ p2)    by SUBSET_DEF

   Step 2: show set (p1 ++ p2) SUBSET set l1
       Let x IN set (p1 ++ p2)
        or MEM x (p1 ++ p2)              by notation
        so MEM x (nub l2)                by MEM, MEM_APPEND
        or x IN set (nub l2)             by notation
       ==> x IN set l2                   by nub_set
        or x IN set (h::l1)              by given
        or MEM x (h::l1)                 by notation
       But x <> h                        by MEM_APPEND, MEM x (p1 ++ p2) but ~(MEM h p1) /\ ~(MEM h p2)
       ==> MEM x l1                      by MEM
        or x IN set l1                   by notation
      Thus set (p1 ++ p2) SUBSET set l1  by SUBSET_DEF

  Thus set l1 = set (p1 ++ p2)           by SUBSET_ANTISYM
*)
val LIST_TO_SET_REDUCTION = store_thm(
  "LIST_TO_SET_REDUCTION",
  ``!l1 l2 h. ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
   ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))``,
  rpt strip_tac >>
  `MEM h (nub l2)` by metis_tac[MEM, nub_set] >>
  qabbrev_tac `l = nub l2` >>
  `?n. n < LENGTH l /\ (h = EL n l)` by rw[GSYM MEM_EL] >>
  `ALL_DISTINCT l` by rw[nub_all_distinct, Abbr`l`] >>
  `?p1 p2. (l = p1 ++ [h] ++ p2) /\ ~MEM h p1 /\ ~MEM h p2` by rw[GSYM MEM_SPLIT_APPEND_distinct] >>
  qexists_tac `p1` >>
  qexists_tac `p2` >>
  rpt strip_tac >-
  rw[] >>
  `set l1 SUBSET set (p1 ++ p2) /\ set (p1 ++ p2) SUBSET set l1` suffices_by metis_tac[SUBSET_ANTISYM] >>
  rewrite_tac[SUBSET_DEF] >>
  rpt strip_tac >-
  metis_tac[MEM_APPEND, MEM, nub_set] >>
  metis_tac[MEM_APPEND, MEM, nub_set]);

(* ------------------------------------------------------------------------- *)
(* List Padding                                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: PAD_LEFT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_LEFT *)
val PAD_LEFT_NIL = store_thm(
  "PAD_LEFT_NIL",
  ``!n c. PAD_LEFT c n [] = GENLIST (K c) n``,
  rw[PAD_LEFT]);

(* Theorem: PAD_RIGHT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_RIGHT *)
val PAD_RIGHT_NIL = store_thm(
  "PAD_RIGHT_NIL",
  ``!n c. PAD_RIGHT c n [] = GENLIST (K c) n``,
  rw[PAD_RIGHT]);

(* Theorem: LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (GENLIST (K c) (n - LENGTH s) ++ s)           by PAD_LEFT
   = LENGTH (GENLIST (K c) (n - LENGTH s)) + LENGTH s     by LENGTH_APPEND
   = n - LENGTH s + LENGTH s                              by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_LEFT_LENGTH = store_thm(
  "PAD_LEFT_LENGTH",
  ``!n c s. LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s)``,
  rw[PAD_LEFT, MAX_DEF]);

(* Theorem: LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (s ++ GENLIST (K c) (n - LENGTH s))           by PAD_RIGHT
   = LENGTH s + LENGTH (GENLIST (K c) (n - LENGTH s))     by LENGTH_APPEND
   = LENGTH s + (n - LENGTH s)                            by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_RIGHT_LENGTH = store_thm(
  "PAD_RIGHT_LENGTH",
  ``!n c s. LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s)``,
  rw[PAD_RIGHT, MAX_DEF]);

(* Theorem: n <= LENGTH l ==> (PAD_LEFT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_LEFT c (LENGTH l) l
   = GENLIST (K c) 0 ++ l      by PAD_LEFT
   = [] ++ l                   by GENLIST
   = l                         by APPEND
*)
val PAD_LEFT_ID = store_thm(
  "PAD_LEFT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_LEFT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_LEFT]);

(* Theorem: n <= LENGTH l ==> (PAD_RIGHT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_RIGHT c (LENGTH l) l
   = ll ++ GENLIST (K c) 0     by PAD_RIGHT
   = [] ++ l                   by GENLIST
   = l                         by APPEND_NIL
*)
val PAD_RIGHT_ID = store_thm(
  "PAD_RIGHT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_RIGHT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_RIGHT]);

(* Theorem: PAD_LEFT c 0 l = l *)
(* Proof: by PAD_LEFT_ID *)
val PAD_LEFT_0 = store_thm(
  "PAD_LEFT_0",
  ``!l c. PAD_LEFT c 0 l = l``,
  rw_tac std_ss[PAD_LEFT_ID]);

(* Theorem: PAD_RIGHT c 0 l = l *)
(* Proof: by PAD_RIGHT_ID *)
val PAD_RIGHT_0 = store_thm(
  "PAD_RIGHT_0",
  ``!l c. PAD_RIGHT c 0 l = l``,
  rw_tac std_ss[PAD_RIGHT_ID]);

(* Theorem: LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l *)
(* Proof:
     PAD_LEFT c (SUC n) l
   = GENLIST (K c) (SUC n - LENGTH l) ++ l         by PAD_LEFT
   = GENLIST (K c) (SUC (n - LENGTH l)) ++ l       by LENGTH l <= n
   = SNOC c (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST
   = (GENLIST (K c) (n - LENGTH l)) ++ [c] ++ l    by SNOC_APPEND
   = [c] ++ (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST_K_APPEND_K
   = [c] ++ ((GENLIST (K c) (n - LENGTH l)) ++ l)  by APPEND_ASSOC
   = [c] ++ PAD_LEFT c n l                         by PAD_LEFT
   = c :: PAD_LEFT c n l                           by CONS_APPEND
*)
val PAD_LEFT_CONS = store_thm(
  "PAD_LEFT_CONS",
  ``!l n. LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  `PAD_LEFT c (SUC n) l = GENLIST (K c) (SUC n - m) ++ l` by rw[PAD_LEFT, Abbr`m`] >>
  `_ = SNOC c (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST] >>
  `_ = (GENLIST (K c) (n - m)) ++ [c] ++ l` by rw[SNOC_APPEND] >>
  `_ = [c] ++ (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST_K_APPEND_K] >>
  `_ = [c] ++ ((GENLIST (K c) (n - m)) ++ l)` by rw[APPEND_ASSOC] >>
  `_ = [c] ++ PAD_LEFT c n l` by rw[PAD_LEFT] >>
  `_ = c :: PAD_LEFT c n l` by rw[] >>
  rw[]);

(* Theorem: LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l) *)
(* Proof:
     PAD_RIGHT c (SUC n) l
   = l ++ GENLIST (K c) (SUC n - LENGTH l)         by PAD_RIGHT
   = l ++ GENLIST (K c) (SUC (n - LENGTH l))       by LENGTH l <= n
   = l ++ SNOC c (GENLIST (K c) (n - LENGTH l))    by GENLIST
   = SNOC c (l ++ (GENLIST (K c) (n - LENGTH l)))  by APPEND_SNOC
   = SNOC c (PAD_RIGHT c n l)                      by PAD_RIGHT
*)
val PAD_RIGHT_SNOC = store_thm(
  "PAD_RIGHT_SNOC",
  ``!l n. LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l)``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  rw[PAD_RIGHT, GENLIST, APPEND_SNOC]);

(* Theorem: h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t) *)
(* Proof:
     h :: PAD_RIGHT c n t
   = h :: (t ++ GENLIST (K c) (n - LENGTH t))          by PAD_RIGHT
   = (h::t) ++ GENLIST (K c) (n - LENGTH t)            by APPEND
   = (h::t) ++ GENLIST (K c) (SUC n - LENGTH (h::t))   by LENGTH
   = PAD_RIGHT c (SUC n) (h::t)                        by PAD_RIGHT
*)
val PAD_RIGHT_CONS = store_thm(
  "PAD_RIGHT_CONS",
  ``!h t c n. h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t)``,
  rw[PAD_RIGHT]);

(* Theorem: l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l) *)
(* Proof:
   Note ?h t. l = h::t     by list_CASES
     LAST (PAD_LEFT c n l)
   = LAST (GENLIST (K c) (n - LENGTH (h::t)) ++ (h::t))   by PAD_LEFT
   = LAST (h::t)           by LAST_APPEND_CONS
   = LAST l                by notation
*)
val PAD_LEFT_LAST = store_thm(
  "PAD_LEFT_LAST",
  ``!l c n. l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l)``,
  rpt strip_tac >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[PAD_LEFT, LAST_APPEND_CONS]);

(* Theorem: (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_LEFT c n l = []
   <=> GENLIST (K c) (n - LENGTH l) ++ l = []        by PAD_LEFT
   <=> GENLIST (K c) (n - LENGTH l) = [] /\ l = []   by APPEND_eq_NIL
   <=> GENLIST (K c) n = [] /\ l = []                by LENGTH l = 0
   <=> n = 0 /\ l = []                               by GENLIST_EQ_NIL
*)
val PAD_LEFT_EQ_NIL = store_thm(
  "PAD_LEFT_EQ_NIL",
  ``!l c n. (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_LEFT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_RIGHT c n l = []
   <=> l ++ GENLIST (K c) (n - LENGTH l) = []        by PAD_RIGHT
   <=> l = [] /\ GENLIST (K c) (n - LENGTH l) = []   by APPEND_eq_NIL
   <=> l = [] /\ GENLIST (K c) n = []                by LENGTH l = 0
   <=> l = [] /\ n = 0                               by GENLIST_EQ_NIL
*)
val PAD_RIGHT_EQ_NIL = store_thm(
  "PAD_RIGHT_EQ_NIL",
  ``!l c n. (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_RIGHT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c]) *)
(* Proof:
      PAD_LEFT c n []
    = GENLIST (K c) n          by PAD_LEFT, APPEND_NIL
    = GENLIST (K c) (SUC k)    by n = SUC k, 0 < n
    = SNOC c (GENLIST (K c) k) by GENLIST, (K c) k = c
    = GENLIST (K c) k ++ [c]   by SNOC_APPEND
    = PAD_LEFT c n [c]         by PAD_LEFT
*)
val PAD_LEFT_NIL_EQ = store_thm(
  "PAD_LEFT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c])``,
  rw[PAD_LEFT] >>
  `SUC (n - 1) = n` by decide_tac >>
  qabbrev_tac `f = (K c):num -> 'a` >>
  `f (n - 1) = c` by rw[Abbr`f`] >>
  metis_tac[SNOC_APPEND, GENLIST]);

(* Theorem: 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c]) *)
(* Proof:
      PAD_RIGHT c n []
    = GENLIST (K c) n                by PAD_RIGHT
    = GENLIST (K c) (SUC (n - 1))    by 0 < n
    = c :: GENLIST (K c) (n - 1)     by GENLIST_K_CONS
    = [c] ++ GENLIST (K c) (n - 1)   by CONS_APPEND
    = PAD_RIGHT c (SUC (n - 1)) [c]  by PAD_RIGHT
    = PAD_RIGHT c n [c]              by 0 < n
*)
val PAD_RIGHT_NIL_EQ = store_thm(
  "PAD_RIGHT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c])``,
  rw[PAD_RIGHT] >>
  `SUC (n - 1) = n` by decide_tac >>
  metis_tac[GENLIST_K_CONS]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0)   by APPEND_NIL, LENGTH
   = ls ++ PAD_RIGHT c (n - LENGTH ls) []               by PAD_RIGHT
*)
val PAD_RIGHT_BY_RIGHT = store_thm(
  "PAD_RIGHT_BY_RIGHT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ (GENLIST (K c) ((n - LENGTH ls) - 0) ++ [])  by APPEND_NIL, LENGTH
   = ls ++ PAD_LEFT c (n - LENGTH ls) []               by PAD_LEFT
*)
val PAD_RIGHT_BY_LEFT = store_thm(
  "PAD_RIGHT_BY_LEFT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls               by PAD_LEFT
   = ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls            by PAD_RIGHT
*)
val PAD_LEFT_BY_RIGHT = store_thm(
  "PAD_LEFT_BY_RIGHT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls                 by PAD_LEFT
   = ((GENLIST (K c) ((n - LENGTH ls) - 0) ++ []) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_LEFT c (n - LENGTH ls) []) ++ ls               by PAD_LEFT
*)
val PAD_LEFT_BY_LEFT = store_thm(
  "PAD_LEFT_BY_LEFT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_LEFT]);

(* ------------------------------------------------------------------------- *)
(* PROD for List, similar to SUM for List                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload a positive list *)
val _ = overload_on("POSITIVE", ``\l. !x. MEM x l ==> 0 < x``);
val _ = overload_on("EVERY_POSITIVE", ``\l. EVERY (\k. 0 < k) l``);

(* Theorem: EVERY_POSITIVE ls <=> POSITIVE ls *)
(* Proof: by EVERY_MEM *)
val POSITIVE_THM = store_thm(
  "POSITIVE_THM",
  ``!ls. EVERY_POSITIVE ls <=> POSITIVE ls``,
  rw[EVERY_MEM]);

(* Note: For product of a number list, any zero element will make the product 0. *)

(* Define PROD, similar to SUM *)
val PROD = new_recursive_definition
      {name = "PROD",
       rec_axiom = list_Axiom,
       def = ``(PROD [] = 1) /\
          (!h t. PROD (h::t) = h * PROD t)``};

(* export simple definition *)
val _ = export_rewrites["PROD"];

(* Extract theorems from definition *)
val PROD_NIL = save_thm("PROD_NIL", PROD |> CONJUNCT1);
(* val PROD_NIL = |- PROD [] = 1: thm *)

val PROD_CONS = save_thm("PROD_CONS", PROD |> CONJUNCT2);
(* val PROD_CONS = |- !h t. PROD (h::t) = h * PROD t: thm *)

(* Theorem: PROD [n] = n *)
(* Proof: by PROD *)
val PROD_SING = store_thm(
  "PROD_SING",
  ``!n. PROD [n] = n``,
  rw[]);

(* Theorem: PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls) *)
(* Proof: by PROD *)
val PROD_eval = store_thm(
  "PROD_eval[compute]", (* put in computeLib *)
  ``!ls. PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls)``,
  metis_tac[PROD, list_CASES, HD, TL]);

(* enable PROD computation -- use [compute] above. *)
(* val _ = computeLib.add_persistent_funs ["PROD_eval"]; *)

(* Theorem: (PROD ls = 1) = !x. MEM x ls ==> (x = 1) *)
(* Proof:
   By induction on ls.
   Base: (PROD [] = 1) <=> !x. MEM x [] ==> (x = 1)
      LHS: PROD [] = 1 is true          by PROD
      RHS: is true since MEM x [] = F   by MEM
   Step: (PROD ls = 1) <=> !x. MEM x ls ==> (x = 1) ==>
         !h. (PROD (h::ls) = 1) <=> !x. MEM x (h::ls) ==> (x = 1)
      Note 1 = PROD (h::ls)                     by given
             = h * PROD ls                      by PROD
      Thus h = 1 /\ PROD ls = 1                 by MULT_EQ_1
        or h = 1 /\ !x. MEM x ls ==> (x = 1)    by induction hypothesis
        or !x. MEM x (h::ls) ==> (x = 1)        by MEM
*)
val PROD_eq_1 = store_thm(
  "PROD_eq_1",
  ``!ls. (PROD ls = 1) = !x. MEM x ls ==> (x = 1)``,
  Induct >>
  rw[] >>
  metis_tac[]);

(* Theorem: PROD (SNOC x l) = (PROD l) * x *)
(* Proof:
   By induction on l.
   Base: PROD (SNOC x []) = PROD [] * x
        PROD (SNOC x [])
      = PROD [x]                by SNOC
      = x                       by PROD
      = 1 * x                   by MULT_LEFT_1
      = PROD [] * x             by PROD
   Step: PROD (SNOC x l) = PROD l * x ==> !h. PROD (SNOC x (h::l)) = PROD (h::l) * x
        PROD (SNOC x (h::l))
      = PROD (h:: SNOC x l)     by SNOC
      = h * PROD (SNOC x l)     by PROD
      = h * (PROD l * x)        by induction hypothesis
      = (h * PROD l) * x        by MULT_ASSOC
      = PROD (h::l) * x         by PROD
*)
val PROD_SNOC = store_thm(
  "PROD_SNOC",
  ``!x l. PROD (SNOC x l) = (PROD l) * x``,
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: PROD (APPEND l1 l2) = PROD l1 * PROD l2 *)
(* Proof:
   By induction on l1.
   Base: PROD ([] ++ l2) = PROD [] * PROD l2
         PROD ([] ++ l2)
       = PROD l2                   by APPEND
       = 1 * PROD l2               by MULT_LEFT_1
       = PROD [] * PROD l2         by PROD
   Step: !l2. PROD (l1 ++ l2) = PROD l1 * PROD l2 ==> !h l2. PROD (h::l1 ++ l2) = PROD (h::l1) * PROD l2
         PROD (h::l1 ++ l2)
       = PROD (h::(l1 ++ l2))      by APPEND
       = h * PROD (l1 ++ l2)       by PROD
       = h * (PROD l1 * PROD l2)   by induction hypothesis
       = (h * PROD l1) * PROD l2   by MULT_ASSOC
       = PROD (h::l1) * PROD l2    by PROD
*)
val PROD_APPEND = store_thm(
  "PROD_APPEND",
  ``!l1 l2. PROD (APPEND l1 l2) = PROD l1 * PROD l2``,
  Induct >> rw[]);

(* Theorem: PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls *)
(* Proof:
   By SNOC_INDUCT |- !P. P [] /\ (!l. P l ==> !x. P (SNOC x l)) ==> !l. P l
   Base: PROD (MAP f []) = FOLDL (\a e. a * f e) 1 []
         PROD (MAP f [])
       = PROD []                     by MAP
       = 1                           by PROD
       = FOLDL (\a e. a * f e) 1 []  by FOLDL
   Step: !f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls ==>
         PROD (MAP f (SNOC x ls)) = FOLDL (\a e. a * f e) 1 (SNOC x ls)
         PROD (MAP f (SNOC x ls))
       = PROD (SNOC (f x) (MAP f ls))                      by MAP_SNOC
       = PROD (MAP f ls) * (f x)                           by PROD_SNOC
       = (FOLDL (\a e. a * f e) 1 ls) * (f x)              by induction hypothesis
       = (\a e. a * f e) (FOLDL (\a e. a * f e) 1 ls) x    by function application
       = FOLDL (\a e. a * f e) 1 (SNOC x ls)               by FOLDL_SNOC
*)
val PROD_MAP_FOLDL = store_thm(
  "PROD_MAP_FOLDL",
  ``!ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls``,
  HO_MATCH_MP_TAC SNOC_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  rw[MAP_SNOC, PROD_SNOC, FOLDL_SNOC]);

(* Theorem: FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s)) *)
(* Proof:
     PI f s
   = ITSET (\e acc. f e * acc) s 1                            by PROD_IMAGE_DEF
   = FOLDL (combin$C (\e acc. f e * acc)) 1 (SET_TO_LIST s)   by ITSET_eq_FOLDL_SET_TO_LIST, FINITE s
   = FOLDL (\a e. a * f e) 1 (SET_TO_LIST s)                  by FUN_EQ_THM
   = PROD (MAP f (SET_TO_LIST s))                             by PROD_MAP_FOLDL
*)
val PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST = store_thm(
  "PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST",
  ``!s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))``,
  rw[PROD_IMAGE_DEF] >>
  rw[ITSET_eq_FOLDL_SET_TO_LIST, PROD_MAP_FOLDL] >>
  rpt AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM]);

(* Define PROD using accumulator *)
val PROD_ACC_DEF = Lib.with_flag (Defn.def_suffix, "_DEF") Define
  `(PROD_ACC [] acc = acc) /\
   (PROD_ACC (h::t) acc = PROD_ACC t (h * acc))`;

(* Theorem: PROD_ACC L n = PROD L * n *)
(* Proof:
   By induction on L.
   Base: !n. PROD_ACC [] n = PROD [] * n
        PROD_ACC [] n
      = n                 by PROD_ACC_DEF
      = 1 * n             by MULT_LEFT_1
      = PROD [] * n       by PROD
   Step: !n. PROD_ACC L n = PROD L * n ==> !h n. PROD_ACC (h::L) n = PROD (h::L) * n
        PROD_ACC (h::L) n
      = PROD_ACC L (h * n)   by PROD_ACC_DEF
      = PROD L * (h * n)     by induction hypothesis
      = (PROD L * h) * n     by MULT_ASSOC
      = (h * PROD L) * n     by MULT_COMM
      = PROD (h::L) * n      by PROD
*)
val PROD_ACC_PROD_LEM = store_thm(
  "PROD_ACC_PROD_LEM",
  ``!L n. PROD_ACC L n = PROD L * n``,
  Induct >>
  rw[PROD_ACC_DEF]);
(* proof SUM_ACC_SUM_LEM *)
val PROD_ACC_PROD_LEM = store_thm
("PROD_ACC_SUM_LEM",
 ``!L n. PROD_ACC L n = PROD L * n``,
 Induct THEN RW_TAC arith_ss [PROD_ACC_DEF, PROD]);

(* Theorem: PROD L = PROD_ACC L 1 *)
(* Proof: Put n = 1 in PROD_ACC_PROD_LEM *)
Theorem PROD_PROD_ACC[compute]:
  !L. PROD L = PROD_ACC L 1
Proof
  rw[PROD_ACC_PROD_LEM]
QED

(* EVAL ``PROD [1; 2; 3; 4]``; --> 24 *)

(* Theorem: PROD (GENLIST (K m) n) = m ** n *)
(* Proof:
   By induction on n.
   Base: PROD (GENLIST (K m) 0) = m ** 0
        PROD (GENLIST (K m) 0)
      = PROD []                by GENLIST
      = 1                      by PROD
      = m ** 0                 by EXP
   Step: PROD (GENLIST (K m) n) = m ** n ==> PROD (GENLIST (K m) (SUC n)) = m ** SUC n
        PROD (GENLIST (K m) (SUC n))
      = PROD (SNOC m (GENLIST (K m) n))    by GENLIST
      = PROD (GENLIST (K m) n) * m         by PROD_SNOC
      = m ** n * m                         by induction hypothesis
      = m * m ** n                         by MULT_COMM
      = m * SUC n                          by EXP
*)
val PROD_GENLIST_K = store_thm(
  "PROD_GENLIST_K",
  ``!m n. PROD (GENLIST (K m) n) = m ** n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, PROD_SNOC, EXP]);

(* Same as PROD_GENLIST_K, formulated slightly different. *)

(* Theorem: PPROD (GENLIST (\j. x) n) = x ** n *)
(* Proof:
   Note (\j. x) = K x             by FUN_EQ_THM
        PROD (GENLIST (\j. x) n)
      = PROD (GENLIST (K x) n)    by GENLIST_FUN_EQ
      = x ** n                    by PROD_GENLIST_K
*)
val PROD_CONSTANT = store_thm(
  "PROD_CONSTANT",
  ``!n x. PROD (GENLIST (\j. x) n) = x ** n``,
  rpt strip_tac >>
  `(\j. x) = K x` by rw[FUN_EQ_THM] >>
  metis_tac[PROD_GENLIST_K, GENLIST_FUN_EQ]);

(* Theorem: (PROD l = 0) <=> MEM 0 l *)
(* Proof:
   By induction on l.
   Base: (PROD [] = 0) <=> MEM 0 []
      LHS = F    by PROD_NIL, 1 <> 0
      RHS = F    by MEM
   Step: (PROD l = 0) <=> MEM 0 l ==> !h. (PROD (h::l) = 0) <=> MEM 0 (h::l)
      Note PROD (h::l) = h * PROD l     by PROD_CONS
      Thus PROD (h::l) = 0
       ==> h = 0 \/ PROD l = 0          by MULT_EQ_0
      If h = 0, then MEM 0 (h::l)       by MEM
      If PROD l = 0, then MEM 0 l       by induction hypothesis
                       or MEM 0 (h::l)  by MEM
*)
val PROD_EQ_0 = store_thm(
  "PROD_EQ_0",
  ``!l. (PROD l = 0) <=> MEM 0 l``,
  Induct >-
  rw[] >>
  metis_tac[PROD_CONS, MULT_EQ_0, MEM]);

(* Theorem: EVERY (\x. 0 < x) l ==> 0 < PROD l *)
(* Proof:
   By contradiction, suppose PROD l = 0.
   Then MEM 0 l              by PROD_EQ_0
     or 0 < 0 = F            by EVERY_MEM
*)
val PROD_POS = store_thm(
  "PROD_POS",
  ``!l. EVERY (\x. 0 < x) l ==> 0 < PROD l``,
  metis_tac[EVERY_MEM, PROD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: POSITIVE l ==> 0 < PROD l *)
(* Proof: PROD_POS, EVERY_MEM *)
val PROD_POS_ALT = store_thm(
  "PROD_POS_ALT",
  ``!l. POSITIVE l ==> 0 < PROD l``,
  rw[PROD_POS, EVERY_MEM]);

(* Theorem: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) *)
(* Proof:
   The computation is:
       n * (n ** 2) * (n ** 4) * ... * (n ** (2 ** (m - 1)))
     = n ** (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n ** (2 ** m - 1)

   By induction on m.
   Base: PROD (GENLIST (\j. n ** 2 ** j) 0) = n ** (2 ** 0 - 1)
      LHS = PROD (GENLIST (\j. n ** 2 ** j) 0)
          = PROD []                by GENLIST_0
          = 1                      by PROD
      RHS = n ** (1 - 1)           by EXP_0
          = n ** 0 = 1 = LHS       by EXP_0
   Step: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) ==>
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m)) = n ** (2 ** SUC m - 1)
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m))
       = PROD (SNOC (n ** 2 ** m) (GENLIST (\j. n ** 2 ** j) m))   by GENLIST
       = PROD (GENLIST (\j. n ** 2 ** j) m) * (n ** 2 ** m)        by PROD_SNOC
       = n ** (2 ** m - 1) * n ** 2 ** m                           by induction hypothesis
       = n ** (2 ** m - 1 + 2 ** m)                                by EXP_ADD
       = n ** (2 * 2 ** m - 1)                                     by arithmetic
       = n ** (2 ** SUC m - 1)                                     by EXP
*)
val PROD_SQUARING_LIST = store_thm(
  "PROD_SQUARING_LIST",
  ``!m n. PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n ** 2 ** j` >>
  `PROD (GENLIST f (SUC m)) = PROD (SNOC (n ** 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = PROD (GENLIST f m) * (n ** 2 ** m)` by rw[PROD_SNOC] >>
  `_ = n ** (2 ** m - 1) * n ** 2 ** m` by rw[] >>
  `_ = n ** (2 ** m - 1 + 2 ** m)` by rw[EXP_ADD] >>
  rw[EXP]);

(* ------------------------------------------------------------------------- *)
(* List Range                                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m ==> 0 < PROD [m .. n] *)
(* Proof:
   Note MEM 0 [m .. n] = F        by MEM_listRangeINC
   Thus PROD [m .. n] <> 0        by PROD_EQ_0
   The result follows.
   or
   Note EVERY_POSITIVE [m .. n]   by listRangeINC_EVERY
   Thus 0 < PROD [m .. n]         by PROD_POS
*)
val listRangeINC_PROD_pos = store_thm(
  "listRangeINC_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m .. n]``,
  rw[PROD_POS, listRangeINC_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)]) *)
(* Proof:
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           PROD [1 .. n]
         = PROD [1 .. n] DIV 1            by DIV_ONE
         = PROD [1 .. n] DIV PROD []      by PROD_NIL
   If m <> 1, then 1 <= m                 by m <> 0, m <> 1
   Note 1 <= m - 1 /\ m - 1 < n /\ (m - 1 + 1 = m)            by arithmetic
   Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]                 by listRangeINC_APPEND
     or PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]   by PROD_POS
    Now 0 < PROD [1 .. (m - 1)]                               by listRangeINC_PROD_pos
   The result follows                                         by MULT_TO_DIV
*)
val listRangeINC_PROD = store_thm(
  "listRangeINC_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)])``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
  `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
  `PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]` by rw[GSYM PROD_APPEND] >>
  `0 < PROD [1 .. (m - 1)]` by rw[listRangeINC_PROD_pos] >>
  metis_tac[MULT_TO_DIV]);

(* Theorem: 0 < m ==> 0 < PROD [m ..< n] *)
(* Proof:
   Note MEM 0 [m ..< n] = F        by MEM_listRangeLHI
   Thus PROD [m ..< n] <> 0        by PROD_EQ_0
   The result follows.
   or,
   Note EVERY_POSITIVE [m ..< n]   by listRangeLHI_EVERY
   Thus 0 < PROD [m ..< n]         by PROD_POS
*)
val listRangeLHI_PROD_pos = store_thm(
  "listRangeLHI_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m ..< n]``,
  rw[PROD_POS, listRangeLHI_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m]) *)
(* Proof:
   Note n <> 0                    by 0 < m /\ m <= n
   Let m = m' + 1, n = n' + 1     by num_CASES, ADD1
   If m = n,
      Note 0 < PROD [1 ..< n]     by listRangeLHI_PROD_pos
      LHS = PROD [n ..< n]
          = PROD [] = 1           by listRangeLHI_EMPTY
      RHS = PROD [1 ..< n] DIV PROD [1 ..< n]
          = 1                     by DIVMOD_ID, 0 < PROD [1 ..< n]
   If m <> n,
      Then m < n, or m <= n'      by arithmetic
        PROD [m ..< n]
      = PROD [m .. n']                          by listRangeLHI_to_INC
      = PROD [1 .. n'] DIV PROD [1 .. m - 1]    by listRangeINC_PROD, m <= n'
      = PROD [1 .. n'] DIV PROD [1 .. m']       by m' = m - 1
      = PROD [1 ..< n] DIV PROD [1 ..< m]       by listRangeLHI_to_INC
*)
val listRangeLHI_PROD = store_thm(
  "listRangeLHI_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m])``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  Cases_on `m = n` >| [
    `0 < PROD [1 ..< n]` by rw[listRangeLHI_PROD_pos] >>
    rfs[listRangeLHI_EMPTY, DIVMOD_ID],
    `m <= n'` by decide_tac >>
    `PROD [m ..< n] = PROD [m .. n']` by rw[listRangeLHI_to_INC] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m - 1]` by rw[GSYM listRangeINC_PROD] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m']` by rw[] >>
    `_ = PROD [1 ..< n] DIV PROD [1 ..< m]` by rw[GSYM listRangeLHI_to_INC] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* List Summation and Product                                                *)
(* ------------------------------------------------------------------------- *)

(*
> numpairTheory.tri_def;
val it = |- tri 0 = 0 /\ !n. tri (SUC n) = SUC n + tri n: thm
*)

(* Theorem: SUM [1 .. n] = tri n *)
(* Proof:
   By induction on n,
   Base: SUM [1 .. 0] = tri 0
         SUM [1 .. 0]
       = SUM []          by listRangeINC_EMPTY
       = 0               by SUM_NIL
       = tri 0           by tri_def
   Step: SUM [1 .. n] = tri n ==> SUM [1 .. SUC n] = tri (SUC n)
         SUM [1 .. SUC n]
       = SUM (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = SUM [1 .. n] + (SUC n)          by SUM_SNOC
       = tri n + (SUC n)                 by induction hypothesis
       = tri (SUC n)                     by tri_def
*)
val sum_1_to_n_eq_tri_n = store_thm(
  "sum_1_to_n_eq_tri_n",
  ``!n. SUM [1 .. n] = tri n``,
  Induct >-
  rw[listRangeINC_EMPTY, SUM_NIL, numpairTheory.tri_def] >>
  rw[listRangeINC_SNOC, ADD1, SUM_SNOC, numpairTheory.tri_def]);

(* Theorem: SUM [1 .. n] = HALF (n * (n + 1)) *)
(* Proof:
     SUM [1 .. n]
   = tri n                by sum_1_to_n_eq_tri_n
   = HALF (n * (n + 1))   by tri_formula
*)
val sum_1_to_n_eqn = store_thm(
  "sum_1_to_n_eqn",
  ``!n. SUM [1 .. n] = HALF (n * (n + 1))``,
  rw[sum_1_to_n_eq_tri_n, numpairTheory.tri_formula]);

(* Theorem: 2 * SUM [1 .. n] = n * (n + 1) *)
(* Proof:
   Note EVEN (n * (n + 1))         by EVEN_PARTNERS
     or 2 divides (n * (n + 1))    by EVEN_ALT
   Thus n * (n + 1)
      = ((n * (n + 1)) DIV 2) * 2  by DIV_MULT_EQ
      = (SUM [1 .. n]) * 2         by sum_1_to_n_eqn
      = 2 * SUM [1 .. n]           by MULT_COMM
*)
val sum_1_to_n_double = store_thm(
  "sum_1_to_n_double",
  ``!n. 2 * SUM [1 .. n] = n * (n + 1)``,
  rpt strip_tac >>
  `2 divides (n * (n + 1))` by rw[EVEN_PARTNERS, GSYM EVEN_ALT] >>
  metis_tac[sum_1_to_n_eqn, DIV_MULT_EQ, MULT_COMM, DECIDE``0 < 2``]);

(* Theorem: PROD [1 .. n] = FACT n *)
(* Proof:
   By induction on n,
   Base: PROD [1 .. 0] = FACT 0
         PROD [1 .. 0]
       = PROD []          by listRangeINC_EMPTY
       = 1                by PROD_NIL
       = FACT 0           by FACT
   Step: PROD [1 .. n] = FACT n ==> PROD [1 .. SUC n] = FACT (SUC n)
         PROD [1 .. SUC n] = FACT (SUC n)
       = PROD (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = PROD [1 .. n] * (SUC n)          by PROD_SNOC
       = (FACT n) * (SUC n)               by induction hypothesis
       = FACT (SUC n)                     by FACT
*)
val prod_1_to_n_eq_fact_n = store_thm(
  "prod_1_to_n_eq_fact_n",
  ``!n. PROD [1 .. n] = FACT n``,
  Induct >-
  rw[listRangeINC_EMPTY, PROD_NIL, FACT] >>
  rw[listRangeINC_SNOC, ADD1, PROD_SNOC, FACT]);

(* This is numerical version of:
poly_cyclic_cofactor  |- !r. Ring r /\ #1 <> #0 ==> !n. unity n = unity 1 * cyclic n
*)
(* Theorem: (t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])) *)
(* Proof:
   Let f = (\j. t ** j).
   By induction on n.
   Base: t ** 0 - 1 = (t - 1) * SUM (MAP f [0 ..< 0])
         LHS = t ** 0 - 1 = 0           by EXP_0
         RHS = (t - 1) * SUM (MAP f [0 ..< 0])
             = (t - 1) * SUM []         by listRangeLHI_EMPTY
             = (t - 1) * 0 = 0          by SUM
   Step: t ** n - 1 = (t - 1) * SUM (MAP f [0 ..< n]) ==>
         t ** SUC n - 1 = (t - 1) * SUM (MAP f [0 ..< SUC n])
       If t = 0,
          LHS = 0 ** SUC n - 1 = 0              by EXP_0
          RHS = (0 - 1) * SUM (MAP f [0 ..< SUC n])
              = 0 * SUM (MAP f [0 ..< SUC n])   by integer subtraction
              = 0 = LHS
       If t <> 0,
          Then 0 < t ** n                       by EXP_POS
            or 1 <= t ** n                      by arithmetic
            so (t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1
            (t - 1) * SUM (MAP (\j. t ** j) [0 ..< (SUC n)])
          = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n + 1])        by ADD1
          = (t - 1) * SUM (MAP (\j. t ** j) (SNOC n [0 ..< n]))   by listRangeLHI_SNOC
          = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))       by MAP_SNOC
          = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)            by SUM_SNOC
          = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n    by RIGHT_ADD_DISTRIB
          = (t ** n - 1) + (t - 1) * t ** n                       by induction hypothesis
          = t ** SUC n - 1                                        by EXP
*)
val power_predecessor_eqn = store_thm(
  "power_predecessor_eqn",
  ``!t n. t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. t ** j` >>
  Induct_on `n` >-
  rw[EXP_0, Abbr`f`] >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP, Abbr`f`] >>
  `(t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1` by
  (`0 < t` by decide_tac >>
  `0 < t ** n` by rw[EXP_POS] >>
  `1 <= t ** n` by decide_tac >>
  `t ** n <= t * t ** n` by rw[] >>
  decide_tac) >>
  `(t - 1) * SUM (MAP f [0 ..< (SUC n)]) = (t - 1) * SUM (MAP f [0 ..< n + 1])` by rw[ADD1] >>
  `_ = (t - 1) * SUM (MAP f (SNOC n [0 ..< n]))` by rw[listRangeLHI_SNOC] >>
  `_ = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))` by rw[MAP_SNOC, Abbr`f`] >>
  `_ = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)` by rw[SUM_SNOC] >>
  `_ = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = (t ** n - 1) + (t - 1) * t ** n` by rw[] >>
  `_ = (t ** n - 1) + (t * t ** n - t ** n)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = t * t ** n - 1` by rw[] >>
  `_ =  t ** SUC n - 1 ` by rw[GSYM EXP] >>
  rw[]);

(* Above is the formal proof of the following observation for any base:
        9 = 9 * 1
       99 = 9 * 11
      999 = 9 * 111
     9999 = 9 * 1111
    99999 = 8 * 11111
   etc.

  This asserts:
     (t ** n - 1) = (t - 1) * (1 + t + t ** 2 + ... + t ** (n-1))
  or  1 + t + t ** 2 + ... + t ** (n - 1) = (t ** n - 1) DIV (t - 1),
  which is the sum of the geometric series.
*)

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1)) *)
(* Proof:
   Note 0 < t - 1                     by 1 < t
    Let s = SUM (MAP (\j. t ** j) [0 ..< n]).
   Then (t ** n - 1) = (t - 1) * s    by power_predecessor_eqn
   Thus s = (t ** n - 1) DIV (t - 1)  by MULT_TO_DIV, 0 < t - 1
*)
val geometric_sum_eqn = store_thm(
  "geometric_sum_eqn",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1))``,
  rpt strip_tac >>
  `0 < t - 1` by decide_tac >>
  rw_tac std_ss[power_predecessor_eqn, MULT_TO_DIV]);

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1)) *)
(* Proof:
     SUM (MAP (\j. t ** j) [0 .. n])
   = SUM (MAP (\j. t ** j) [0 ..< n + 1])   by listRangeLHI_to_INC
   = (t ** (n + 1) - 1) DIV (t - 1)         by geometric_sum_eqn
*)
val geometric_sum_eqn_alt = store_thm(
  "geometric_sum_eqn_alt",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1))``,
  rw_tac std_ss[GSYM listRangeLHI_to_INC, geometric_sum_eqn]);

(* Theorem: SUM [1 ..< n] = HALF (n * (n - 1)) *)
(* Proof:
   If n = 0,
      LHS = SUM [1 ..< 0]
          = SUM [] = 0                by listRangeLHI_EMPTY
      RHS = HALF (0 * (0 - 1))
          = 0 = LHS                   by arithmetic
   If n <> 0,
      Then n = (n - 1) + 1            by arithmetic, n <> 0
        SUM [1 ..< n]
      = SUM [1 .. n - 1]              by listRangeLHI_to_INC
      = HALF ((n - 1) * (n - 1 + 1))  by sum_1_to_n_eqn
      = HALF (n * (n - 1))            by arithmetic
*)
val arithmetic_sum_eqn = store_thm(
  "arithmetic_sum_eqn",
  ``!n. SUM [1 ..< n] = HALF (n * (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  `n = (n - 1) + 1` by decide_tac >>
  `SUM [1 ..< n] = SUM [1 .. n - 1]` by rw[GSYM listRangeLHI_to_INC] >>
  `_ = HALF ((n - 1) * (n - 1 + 1))` by rw[sum_1_to_n_eqn] >>
  `_ = HALF (n * (n - 1))` by rw[] >>
  rw[]);

(* Theorem alias *)
val arithmetic_sum_eqn_alt = save_thm("arithmetic_sum_eqn_alt", sum_1_to_n_eqn);
(* val arithmetic_sum_eqn_alt = |- !n. SUM [1 .. n] = HALF (n * (n + 1)): thm *)

(* Theorem: SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n]) *)
(* Proof:
     SUM (GENLIST (\j. f (n - j)) n)
   = SUM (REVERSE (GENLIST (\j. f (n - j)) n))     by SUM_REVERSE
   = SUM (GENLIST (\j. f (n - (PRE n - j))) n)     by REVERSE_GENLIST
   = SUM (GENLIST (\j. f (1 + j)) n)               by LIST_EQ, SUB_SUB
   = SUM (GENLIST (f o SUC) n)                     by FUN_EQ_THM
   = SUM (MAP f [1 .. n])                          by listRangeINC_MAP
*)
val SUM_GENLIST_REVERSE = store_thm(
  "SUM_GENLIST_REVERSE",
  ``!f n. SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n])``,
  rpt strip_tac >>
  `GENLIST (\j. f (n - (PRE n - j))) n = GENLIST (f o SUC) n` by
  (irule LIST_EQ >>
  rw[] >>
  `n + x - PRE n = SUC x` by decide_tac >>
  simp[]) >>
  qabbrev_tac `g = \j. f (n - j)` >>
  `SUM (GENLIST g n) = SUM (REVERSE (GENLIST g n))` by rw[SUM_REVERSE] >>
  `_ = SUM (GENLIST (\j. g (PRE n - j)) n)` by rw[REVERSE_GENLIST] >>
  `_ = SUM (GENLIST (f o SUC) n)` by rw[Abbr`g`] >>
  `_ = SUM (MAP f [1 .. n])` by rw[listRangeINC_MAP] >>
  decide_tac);
(* Note: locate here due to use of listRangeINC_MAP *)

(* Theorem: SIGMA f (count n) = SUM (MAP f [0 ..< n]) *)
(* Proof:
     SIGMA f (count n)
   = SUM (GENLIST f n)         by SUM_GENLIST
   = SUM (MAP f [0 ..< n])     by listRangeLHI_MAP
*)
Theorem SUM_IMAGE_count:
  !f n. SIGMA f (count n) = SUM (MAP f [0 ..< n])
Proof
  simp[SUM_GENLIST, listRangeLHI_MAP]
QED
(* Note: locate here due to use of listRangeINC_MAP *)

(* Theorem: SIGMA f (count (SUC n)) = SUM (MAP f [0 .. n]) *)
(* Proof:
     SIGMA f (count (SUC n))
   = SUM (GENLIST f (SUC n))       by SUM_GENLIST
   = SUM (MAP f [0 ..< (SUC n)])   by SUM_IMAGE_count
   = SUM (MAP f [0 .. n])          by listRangeINC_to_LHI
*)
Theorem SUM_IMAGE_upto:
  !f n. SIGMA f (count (SUC n)) = SUM (MAP f [0 .. n])
Proof
  simp[SUM_GENLIST, SUM_IMAGE_count, listRangeINC_to_LHI]
QED

(* ------------------------------------------------------------------------- *)
(* MAP of function with 3 list arguments                                     *)
(* ------------------------------------------------------------------------- *)

(* Define MAP3 similar to MAP2 in listTheory. *)
val dDefine = Lib.with_flag (Defn.def_suffix, "_DEF") Define;
val MAP3_DEF = dDefine`
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3) /\
  (MAP3 f x y z = [])`;
val _ = export_rewrites["MAP3_DEF"];
val MAP3 = store_thm ("MAP3",
``(!f. MAP3 f [] [] [] = []) /\
  (!f h1 t1 h2 t2 h3 t3. MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)``,
  METIS_TAC[MAP3_DEF]);

(*
LENGTH_MAP   |- !l f. LENGTH (MAP f l) = LENGTH l
LENGTH_MAP2  |- !xs ys. LENGTH (MAP2 f xs ys) = MIN (LENGTH xs) (LENGTH ys)
*)

(* Theorem: LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz f. LENGTH (MAP3 f [] ly lz) = MIN (MIN (LENGTH []) (LENGTH ly)) (LENGTH lz)
      LHS = LENGTH [] = 0                         by MAP3, LENGTH
      RHS = MIN (MIN 0 (LENGTH ly)) (LENGTH lz)   by LENGTH
          = MIN 0 (LENGTH lz) = 0 = LHS           by MIN_DEF
   Step: !ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !h ly lz f. LENGTH (MAP3 f (h::lx) ly lz) = MIN (MIN (LENGTH (h::lx)) (LENGTH ly)) (LENGTH lz)
      If ly = [],
         LHS = LENGTH (MAP3 f (h::lx) [] lz) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH [])) (LENGTH lz)
             = MIN 0 (LENGTH lz) = 0 = LHS        by MIN_DEF
      Otherwise, ly = h'::t.
      If lz = [],
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) []) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH [])
             = 0 = LHS                                 by MIN_DEF
      Otherwise, lz = h''::t'.
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) (h''::t'))
             = LENGTH (f h' h''::MAP3 lx t t'')        by MAP3
             = SUC (LENGTH MAP3 lx t t'')              by LENGTH
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t''))   by induction hypothesis
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH (h''::t'))
             = MIN (MIN (SUC (LENGTH lx)) (SUC (LENGTH t))) (SUC (LENGTH t'))  by LENGTH
             = MIN (SUC (MIN (LENGTH lx) (LENGTH t))) (SUC (LESS_TWICE t'))    by MIN_DEF
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t'')) = LHS       by MIN_DEF
*)
val LENGTH_MAP3 = store_thm(
  "LENGTH_MAP3",
  ``!lx ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz)``,
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[MIN_DEF]);

(*
EL_MAP   |- !n l. n < LENGTH l ==> !f. EL n (MAP f l) = f (EL n l)
EL_MAP2  |- !ts tt n. n < MIN (LENGTH ts) (LENGTH tt) ==> (EL n (MAP2 f ts tt) = f (EL n ts) (EL n tt))
*)

(* Theorem: n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
           !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) *)
(* Proof:
   By induction on n.
   Base: !lx ly lz. 0 < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !f. EL 0 (MAP3 f lx ly lz) = f (EL 0 lx) (EL 0 ly) (EL 0 lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
          EL 0 (MAP3 f lx ly lz)
        = EL 0 (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL 0 (f x y z::MAP3 f tx ty tz)    by MAP3
        = f x y z                            by EL
        = f (EL 0 lx) (EL 0 ly) (EL 0 lz)    by EL
   Step: !lx ly lz. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) ==>
         !lx ly lz. SUC n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL (SUC n) (MAP3 f lx ly lz) = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
      Also n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz    by LENGTH
      Thus n < MIN (MIN (LENGTH tx) (LENGTH ty)) (LENGTH tz)  by MIN_DEF
          EL (SUC n) (MAP3 f lx ly lz)
        = EL (SUC n) (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL (SUC n) (f x y z::MAP3 f tx ty tz)    by MAP3
        = EL n (MAP3 f tx ty tz)                   by EL
        = f (EL n tx) (EL n ty) (EL n tz)          by induction hypothesis
        = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
                                                   by EL
*)
val EL_MAP3 = store_thm(
  "EL_MAP3",
  ``!lx ly lz n. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
   !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz)``,
  Induct_on `n` >| [
    rw[] >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    rw[],
    rw[] >>
    `!a. SUC n < a ==> a <> 0` by decide_tac >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz` by fs[] >>
    rw[]
  ]);

(*
MEM_MAP  |- !l f x. MEM x (MAP f l) <=> ?y. x = f y /\ MEM y l
*)

(* Theorem: MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 *)
(* Proof:
   By induction on l1.
   Base: !l2. MEM x (MAP2 f [] l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 [] /\ MEM y2 l2
      Note MAP2 f [] l2 = []         by MAP2_DEF
       and MEM x [] = F, hence true  by MEM
   Step: !l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 ==>
         !h l2. MEM x (MAP2 f (h::l1) l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 l2
      If l2 = [],
         Then MEM x (MAP2 f (h::l1) []) = F, hence true    by MEM
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP2 f (h::l1) (h'::t)) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t)
         Note MAP2 f (h::l1) (h'::t)
            = (f h h')::MAP2 f l1 t                      by MAP2
         Thus x = f h h'  or MEM x (MAP2 f l1 t)         by MEM
         If x = f h h',
            Take y1 = h, y2 = h', and the result follows by MEM
         If MEM x (MAP2 f l1 t)
            Then ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 t   by induction hypothesis
            Take this y1 and y2, the result follows      by MEM
*)
val MEM_MAP2 = store_thm(
  "MEM_MAP2",
  ``!f x l1 l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. (x = f y1 y2) /\ MEM y1 l1 /\ MEM y2 l2``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: MEM x (MAP3 f l1 l2 l3) ==> ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 *)
(* Proof:
   By induction on l1.
   Base: !l2 l3. MEM x (MAP3 f [] l2 l3) ==> ...
      Note MAP3 f [] l2 l3 = [], and MEM x [] = F, hence true.
   Step: !l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 ==>
         !h l2 l3. MEM x (MAP3 f (h::l1) l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 l2 /\ MEM y3 l3
      If l2 = [],
         Then MEM x (MAP3 f (h::l1) [] l3) = MEM x [] = F, hence true   by MAP3_DEF
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP3 f (h::l1) (h'::t) l3) ==>
                  ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 l3
         If l3 = [],
            Then MEM x (MAP3 f (h::l1) l2 []) = MEM x [] = F, hence true   by MAP3_DEF
         Otherwise, l3 = h''::t',
            to show: MEM x (MAP3 f (h::l1) (h'::t) (h''::t')) ==>
                     ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 (h''::t')

         Note MAP3 f (h::l1) (h'::t) (h''::t')
            = (f h h' h'')::MAP3 f l1 t t'              by MAP3
         Thus x = f h h' h''  or MEM x (MAP3 f l1 t t') by MEM
         If x = f h h' h'',
            Take y1 = h, y2 = h', y3 = h'' and the result follows by MEM
         If MEM x (MAP3 f l1 t t')
            Then ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 t /\ MEM y2 l2 /\ MEM y3 t'
                                                         by induction hypothesis
            Take this y1, y2 and y3, the result follows  by MEM
*)
val MEM_MAP3 = store_thm(
  "MEM_MAP3",
  ``!f x l1 l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
   ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  Cases_on `l3` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: SUM (MAP (K c) ls) = c * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: !c. SUM (MAP (K c) []) = c * LENGTH []
      LHS = SUM (MAP (K c) [])
          = SUM [] = 0             by MAP, SUM
      RHS = c * LENGTH []
          = c * 0 = 0 = LHS        by LENGTH
   Step: !c. SUM (MAP (K c) ls) = c * LENGTH ls ==>
         !h c. SUM (MAP (K c) (h::ls)) = c * LENGTH (h::ls)
        SUM (MAP (K c) (h::ls))
      = SUM (c :: MAP (K c) ls)    by MAP
      = c + SUM (MAP (K c) ls)     by SUM
      = c + c * LENGTH ls          by induction hypothesis
      = c * (1 + LENGTH ls)        by RIGHT_ADD_DISTRIB
      = c * (SUC (LENGTH ls))      by ADD1
      = c * LENGTH (h::ls)         by LENGTH
*)
val SUM_MAP_K = store_thm(
  "SUM_MAP_K",
  ``!ls c. SUM (MAP (K c) ls) = c * LENGTH ls``,
  Induct >-
  rw[] >>
  rw[ADD1]);

(* Theorem: a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls) *)
(* Proof:
      SUM (MAP (K a) ls)
    = a * LENGTH ls             by SUM_MAP_K
   <= b * LENGTH ls             by a <= b
    = SUM (MAP (K b) ls)        by SUM_MAP_K
*)
val SUM_MAP_K_LE = store_thm(
  "SUM_MAP_K_LE",
  ``!ls a b. a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls)``,
  rw[SUM_MAP_K]);

(* Theorem: SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly c. SUM (MAP2 (\x y. c) [] ly) = c * LENGTH (MAP2 (\x y. c) [] ly)
      LHS = SUM (MAP2 (\x y. c) [] ly)
          = SUM [] = 0             by MAP2_DEF, SUM
      RHS = c * LENGTH (MAP2 (\x y. c) [] ly)
          = c * 0 = 0 = LHS        by MAP2_DEF, LENGTH
   Step: !ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) ==>
         !h ly c. SUM (MAP2 (\x y. c) (h::lx) ly) = c * LENGTH (MAP2 (\x y. c) (h::lx) ly)
      If ly = [],
         to show: SUM (MAP2 (\x y. c) (h::lx) []) = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
         LHS = SUM (MAP2 (\x y. c) (h::lx) [])
             = SUM [] = 0          by MAP2_DEF, SUM
         RHS = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
             = c * 0 = 0 = LHS     by MAP2_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP2 (\x y. c) (h::lx) (h'::t)) = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))

           SUM (MAP2 (\x y. c) (h::lx) (h'::t))
         = SUM (c :: MAP2 (\x y. c) lx t)               by MAP2_DEF
         = c + SUM (MAP2 (\x y. c) lx t)                by SUM
         = c + c * LENGTH (MAP2 (\x y. c) lx t)         by induction hypothesis
         = c * (1 + LENGTH (MAP2 (\x y. c) lx t)        by RIGHT_ADD_DISTRIB
         = c * (SUC (LENGTH (MAP2 (\x y. c) lx t))      by ADD1
         = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))  by LENGTH
*)
val SUM_MAP2_K = store_thm(
  "SUM_MAP2_K",
  ``!lx ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  rw[ADD1, MIN_DEF]);

(* Theorem: SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz c. SUM (MAP3 (\x y z. c) [] ly lz) = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
      LHS = SUM (MAP3 (\x y z. c) [] ly lz)
          = SUM [] = 0             by MAP3_DEF, SUM
      RHS = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
          = c * 0 = 0 = LHS        by MAP3_DEF, LENGTH
   Step: !ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) ==>
         !h ly lz c. SUM (MAP3 (\x y z. c) (h::lx) ly lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) ly lz)
      If ly = [],
         to show: SUM (MAP3 (\x y z. c) (h::lx) [] lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
         LHS = SUM (MAP3 (\x y z. c) (h::lx) [] lz)
             = SUM [] = 0          by MAP3_DEF, SUM
         RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
             = c * 0 = 0 = LHS     by MAP3_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) lz)
        If lz = [],
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) []) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
           LHS = SUM (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = SUM [] = 0                  by MAP3_DEF, SUM
           RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = c * 0 = 0                   by MAP3_DEF, LENGTH
        Otherwise, lz = h''::t',
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t')) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
              SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
            = SUM (c :: MAP3 (\x y z. c) lx t t')                      by MAP3_DEF
            = c + SUM (MAP3 (\x y z. c) lx t t')                       by SUM
            = c + c * LENGTH (MAP3 (\x y z. c) lx t t')                by induction hypothesis
            = c * (1 + LENGTH (MAP3 (\x y z. c) lx t t')               by RIGHT_ADD_DISTRIB
            = c * (SUC (LENGTH (MAP3 (\x y z. c) lx t t'))             by ADD1
            = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))  by LENGTH
*)
val SUM_MAP3_K = store_thm(
  "SUM_MAP3_K",
  ``!lx ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[ADD1]);

(* ------------------------------------------------------------------------- *)
(* Bounds on Lists                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SUM ls <= (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: SUM [] <= MAX_LIST [] * LENGTH []
      LHS = SUM [] = 0          by SUM
      RHS = MAX_LIST [] * LENGTH []
          = 0 * 0 = 0           by MAX_LIST, LENGTH
      Hence true.
   Step: SUM ls <= MAX_LIST ls * LENGTH ls ==>
         !h. SUM (h::ls) <= MAX_LIST (h::ls) * LENGTH (h::ls)
        SUM (h::ls)
      = h + SUM ls                                       by SUM
     <= h + MAX_LIST ls * LENGTH ls                      by induction hypothesis
     <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls       by MAX_LIST_PROPERTY
     <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls  by MAX_LIST_LE
      = MAX_LIST (h::ls) * (1 + LENGTH ls)               by LEFT_ADD_DISTRIB
      = MAX_LIST (h::ls) * LENGTH (h::ls)                by LENGTH
*)
val SUM_UPPER = store_thm(
  "SUM_UPPER",
  ``!ls. SUM ls <= (MAX_LIST ls) * LENGTH ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  `SUM (h::ls) <= h + MAX_LIST ls * LENGTH ls` by rw[] >>
  `h + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls = MAX_LIST (h::ls) * (1 + LENGTH ls)` by rw[] >>
  `_ = MAX_LIST (h::ls) * LENGTH (h::ls)` by rw[] >>
  decide_tac);

(* Theorem: (MIN_LIST ls) * LENGTH ls <= SUM ls *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST [] * LENGTH [] <= SUM []
      LHS = (MIN_LIST []) * LENGTH [] = 0     by LENGTH
      RHS = SUM [] = 0                        by SUM
      Hence true.
   Step: MIN_LIST ls * LENGTH ls <= SUM ls ==>
         !h. MIN_LIST (h::ls) * LENGTH (h::ls) <= SUM (h::ls)
      If ls = [],
         LHS = (MIN_LIST [h]) * LENGTH [h]
             = h * 1 = h             by MIN_LIST_def, LENGTH
         RHS = SUM [h] = h           by SUM
         Hence true.
      If ls <> [],
          MIN_LIST (h::ls) * LENGTH (h::ls)
        = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)   by MIN_LIST_def, LENGTH
        = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls
                                                    by RIGHT_ADD_DISTRIB
       <= h + (MIN_LIST ls) * LENGTH ls             by MIN_IS_MIN
       <= h + SUM ls                                by induction hypothesis
        = SUM (h::ls)                               by SUM
*)
val SUM_LOWER = store_thm(
  "SUM_LOWER",
  ``!ls. (MIN_LIST ls) * LENGTH ls <= SUM ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `MIN_LIST (h::ls) * LENGTH (h::ls) = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)` by rw[] >>
  `_ = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls` by rw[] >>
  `(MIN h (MIN_LIST ls)) <= h` by rw[] >>
  `(MIN h (MIN_LIST ls)) * LENGTH ls <= (MIN_LIST ls) * LENGTH ls` by rw[] >>
  rw[]);

(* Theorem: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] ==> SUM (MAP f []) <= SUM (MAP g [])
         EVERY (\x. f x <= g x) [] = T    by EVERY_DEF
           SUM (MAP f [])
         = SUM []                         by MAP
         = SUM (MAP g [])                 by MAP
   Step: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h <= g h /\
              EVERY (\x. f x <= g x) ls   by EVERY_DEF
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
        <= g h + SUM (MAP g ls)           by above, induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LE = store_thm(
  "SUM_MAP_LE",
  ``!f g ls. EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  fs[]);

(* Theorem: EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] /\ [] <> [] ==> SUM (MAP f []) <= SUM (MAP g [])
         True since [] <> [] = F.
   Step: EVERY (\x. f x <= g x) ls ==> ls <> [] ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> h::ls <> [] ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h < g h /\
              EVERY (\x. f x < g x) ls    by EVERY_DEF

         If ls = [],
           SUM (MAP f [h])
         = SUM (f h)          by MAP
         = f h                by SUM
         < g h                by above
         = SUM (g h)          by SUM
         = SUM (MAP g [h])    by MAP

         If ls <> [],
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
         < g h + SUM (MAP g ls)           by induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LT = store_thm(
  "SUM_MAP_LT",
  ``!f g ls. EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  (Cases_on `ls = []` >> fs[]));

(*
MAX_LIST_PROPERTY  |- !l x. MEM x l ==> x <= MAX_LIST l
MIN_LIST_PROPERTY  |- !l. l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x
*)

(* Theorem: MONO f  ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls) *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and   y <= MAX_LIST ls           by MAX_LIST_PROPERTY
   Thus f y <= f (MAX_LIST ls)       by given
     or   e <= f (MAX_LIST ls)       by e = f y
*)
val MEM_MAP_UPPER = store_thm(
  "MEM_MAP_UPPER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls)``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `y <= MAX_LIST ls` by rw[MAX_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly    by MEM_MAP2
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_UPPER = store_thm(
  "MEM_MAP2_UPPER",
  ``!f. MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly)``,
  metis_tac[MEM_MAP2, MAX_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                   MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
    and ez <= MAX_LIST lz                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_UPPER = store_thm(
  "MEM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)``,
  metis_tac[MEM_MAP3, MAX_LIST_PROPERTY]);

(* Theorem: MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and ls <> []                     by MEM, MEM y ls
   then     MIN_LIST ls <= y         by MIN_LIST_PROPERTY, ls <> []
   Thus f (MIN_LIST ls) <= f y       by given
     or f (MIN_LIST ls) <= e         by e = f y
*)
val MEM_MAP_LOWER = store_thm(
  "MEM_MAP_LOWER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `ls <> []` by metis_tac[MEM] >>
  `MIN_LIST ls <= y` by rw[MIN_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==>
            !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly   by MEM_MAP2
    and lx <> [] /\ ly <> []             by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_LOWER = store_thm(
  "MEM_MAP2_LOWER",
  ``!f. MONO2 f ==>
   !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e``,
  metis_tac[MEM_MAP2, MEM, MIN_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and lx <> [] /\ ly <> [] /\ lz <> [] by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
    and MIN_LIST lz <= ez                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_LOWER = store_thm(
  "MEM_MAP3_LOWER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e``,
  rpt strip_tac >>
  `?ex ey ez. (e = f ex ey ez) /\ MEM ex lx /\ MEM ey ly /\ MEM ez lz` by rw[MEM_MAP3] >>
  `lx <> [] /\ ly <> [] /\ lz <> []` by metis_tac[MEM] >>
  rw[MIN_LIST_PROPERTY]);

(* Theorem: (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: !n. EL n (MAP f []) <= EL n (MAP g [])
      LHS = EL n [] = RHS             by MAP
   Step: !n. EL n (MAP f ls) <= EL n (MAP g ls) ==>
         !h n. EL n (MAP f (h::ls)) <= EL n (MAP g (h::ls))
      If n = 0,
          EL 0 (MAP f (h::ls))
        = EL 0 (f h::MAP f ls)        by MAP
        = f h                         by EL
       <= g h                         by given
        = EL 0 (g h::MAP g ls)        by EL
        = EL 0 (MAP g (h::ls))        by MAP
      If n <> 0, then n = SUC k       by num_CASES
         EL n (MAP f (h::ls))
       = EL (SUC k) (f h::MAP f ls)   by MAP
       = EL k (MAP f ls)              by EL
      <= EL k (MAP g ls)              by induction hypothesis
       = EL (SUC k) (g h::MAP g ls)   by EL
       = EL n (MAP g (h::ls))         by MAP
*)
val MAP_LE = store_thm(
  "MAP_LE",
  ``!(f:num -> num) g. (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls)``,
  ntac 3 strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y. f x y <= g x y) ==> !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly n. EL n (MAP2 f [] ly) <= EL n (MAP2 g [] ly)
      LHS = EL n [] = RHS             by MAP2_DEF
   Step: !ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) ==>
         !h ly n. EL n (MAP2 f (h::lx) ly) <= EL n (MAP2 g (h::lx) ly)
      If ly = [],
         to show: EL n (MAP2 f (h::lx) []) <= EL n (MAP2 g (h::lx) [])
         True since LHS = EL n [] = RHS         by MAP2_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP2 f (h::lx) (h'::t)) <= EL n (MAP2 g (h::lx) (h'::t))
         If n = 0,
             EL 0 (MAP2 f (h::lx) (h'::t))
           = EL 0 (f h h'::MAP2 f lx t)        by MAP2
           = f h h'                            by EL
          <= g h h'                            by given
           = EL 0 (g h h'::MAP2 g lx t)        by EL
           = EL 0 (MAP2 g (h::lx) (h'::t))     by MAP2
         If n <> 0, then n = SUC k             by num_CASES
            EL n (MAP2 f (h::lx) (h'::t))
          = EL (SUC k) (f h h'::MAP2 f lx t)   by MAP2
          = EL k (MAP2 f lx t)                 by EL
         <= EL k (MAP2 g lx t)                 by induction hypothesis
          = EL (SUC k) (g h h'::MAP2 g lx t)   by EL
          = EL n (MAP2 g (h::lx) (h'::t))      by MAP2
*)
val MAP2_LE = store_thm(
  "MAP2_LE",
  ``!(f:num -> num -> num) g. (!x y. f x y <= g x y) ==>
   !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y z. f x y z <= g x y z) ==>
            !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz n. EL n (MAP3 f [] ly lz) <= EL n (MAP3 g [] ly lz)
      LHS = EL n [] = RHS             by MAP3_DEF
   Step: !ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) ==>
         !h ly lz n. EL n (MAP3 f (h::lx) ly lz) <= EL n (MAP3 g (h::lx) ly lz)
      If ly = [],
         to show: EL n (MAP3 f (h::lx) [] lz) <= EL n (MAP3 g (h::lx) [] lz)
         True since LHS = EL n [] = RHS          by MAP3_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP3 f (h::lx) (h'::t) lz) <= EL n (MAP3 g (h::lx) (h'::t) lz)
         If lz = [],
            to show: EL n (MAP3 f (h::lx) (h'::t) []) <= EL n (MAP3 g (h::lx) (h'::t) [])
            True since LHS = EL n [] = RHS       by MAP3_DEF
         Otherwise, lz = h''::t'.
            to show: EL n (MAP3 f (h::lx) (h'::t) (h''::t')) <= EL n (MAP3 g (h::lx) (h'::t) (h''::t'))
            If n = 0,
                EL 0 (MAP3 f (h::lx) (h'::t) (h''::t'))
              = EL 0 (f h h' h''::MAP3 f lx t t')        by MAP3
              = f h h' h''                               by EL
             <= g h h' h''                               by given
              = EL 0 (g h h' h''::MAP3 g lx t t')        by EL
              = EL 0 (MAP3 g (h::lx) (h'::t) (h''::t'))  by MAP3
            If n <> 0, then n = SUC k                    by num_CASES
               EL n (MAP3 f (h::lx) (h'::t) (h''::t'))
             = EL (SUC k) (f h h' h''::MAP3 f lx t t')   by MAP3
             = EL k (MAP3 f lx t t')                     by EL
            <= EL k (MAP3 g lx t t')                     by induction hypothesis
             = EL (SUC k) (g h h' h''::MAP3 g lx t t')   by EL
             = EL n (MAP3 g (h::lx) (h'::t) (h''::t'))   by MAP3
*)
val MAP3_LE = store_thm(
  "MAP3_LE",
  ``!(f:num -> num -> num -> num) g. (!x y z. f x y z <= g x y z) ==>
   !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(*
SUM_MAP_PLUS       |- !f g ls. SUM (MAP (\x. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)
SUM_MAP_PLUS_ZIP   |- !ls1 ls2. LENGTH ls1 = LENGTH ls2 /\ (!x y. f (x,y) = g x + h y) ==>
                                SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2)
*)

(* Theorem: (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP f1 ls) ==> EL k (MAP f1 ls) <= EL k (MAP f2 ls)
       This is true                by EL_MAP
   (2) LENGTH (MAP f1 ls) = LENGTH (MAP f2 ls)
       This is true                by LENGTH_MAP
*)
val SUM_MONO_MAP = store_thm(
  "SUM_MONO_MAP",
  ``!f1 f2. (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP]);

(* Theorem: (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP2 f1 lx ly) ==> EL k (MAP2 f1 lx ly) <= EL k (MAP2 f2 lx ly)
       This is true                by EL_MAP2, LENGTH_MAP2
   (2) LENGTH (MAP2 f1 lx ly) = LENGTH (MAP2 f2 lx ly)
       This is true                by LENGTH_MAP2
*)
val SUM_MONO_MAP2 = store_thm(
  "SUM_MONO_MAP2",
  ``!f1 f2. (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP2]);

(* Theorem: (!x y z. f1 x y z <= f2 x y z) ==> !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP3 f1 lx ly lz) ==> EL k (MAP3 f1 lx ly lz) <= EL k (MAP3 f2 lx ly lz)
       This is true                by EL_MAP3, LENGTH_MAP3
   (2)LENGTH (MAP3 f1 lx ly lz) = LENGTH (MAP3 f2 lx ly lz)
       This is true                by LENGTH_MAP3
*)
val SUM_MONO_MAP3 = store_thm(
  "SUM_MONO_MAP3",
  ``!f1 f2. (!x y z. f1 x y z <= f2 x y z) ==>
   !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP3, LENGTH_MAP3]);

(* Theorem: MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   Let c = f (MAX_LIST ls).

   Claim: SUM (MAP f ls) <= SUM (MAP (K c) ls)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP f ls) = LENGTH (MAP (K c) ls)
              This is true                           by LENGTH_MAP
          (2) !k. k < LENGTH (MAP f ls) ==> EL k (MAP f ls) <= EL k (MAP (K c) ls)
              Note EL k (MAP f ls) = f (EL k ls)     by EL_MAP
               and EL k (MAP (K c) ls)
                 = (K c) (EL k ls)                   by EL_MAP
                 = c                                 by K_THM
               Now MEM (EL k ls) ls                  by EL_MEM
                so EL k ls <= MAX_LIST ls            by MAX_LIST_PROPERTY
              Thus f (EL k ls) <= c                  by property of f

   Note SUM (MAP (K c) ls) = c * LENGTH ls           by SUM_MAP_K
   Thus SUM (MAP f ls) <= c * LENGTH ls              by Claim
*)
val SUM_MAP_UPPER = store_thm(
  "SUM_MAP_UPPER",
  ``!f. MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST ls)` >>
  `SUM (MAP f ls) <= SUM (MAP (K c) ls)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP (K c) ls) = c * LENGTH ls` by rw[SUM_MAP_K] >>
  decide_tac);

(* Theorem: MONO2 f ==>
            !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly).

   Claim: SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP2 f lx ly) = LENGTH (MAP2 (\x y. c) lx ly)
              This is true                           by LENGTH_MAP2
          (2) !k. k < LENGTH (MAP2 f lx ly) ==> EL k (MAP2 f lx ly) <= EL k (MAP2 (\x y. c) lx ly)
              Note EL k (MAP2 f lx ly)
                 = f (EL k lx) (EL k ly)             by EL_MAP2
               and EL k (MAP2 (\x y. c) lx ly)
                 = (\x y. c) (EL k lx) (EL k ly)     by EL_MAP2
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly      by LENGTH_MAP2
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) <= c        by property of f

   Note SUM (MAP (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)  by SUM_MAP2_K
    and LENGTH (MAP2 (\x y. c) lx ly) = LENGTH (MAP2 f lx ly)          by LENGTH_MAP2
   Thus SUM (MAP f lx ly) <= c * LENGTH (MAP2 f lx ly)                 by Claim
*)
val SUM_MAP2_UPPER = store_thm(
  "SUM_MAP2_UPPER",
  ``!f. MONO2 f ==>
   !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly)` >>
  `SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP2, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)` by rw[SUM_MAP2_K, Abbr`c`] >>
  `c * LENGTH (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 f lx ly)` by rw[] >>
  decide_tac);

(* Theorem: MONO3 f ==>
           !lx ly lz. SUM (MAP3 f lx ly lz) <=
                      f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz).

   Claim: SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)
              This is true                           by LENGTH_MAP3
          (2) !k. k < LENGTH (MAP3 f lx ly lz) ==> EL k (MAP3 f lx ly lz) <= EL k (MAP3 (\x y z. c) lx ly lz)
              Note EL k (MAP3 f lx ly lz)
                 = f (EL k lx) (EL k ly) (EL k lz)   by EL_MAP3
               and EL k (MAP3 (\x y z. c) lx ly lz)
                 = (\x y z. c) (EL k lx) (EL k ly) (EL k lz)  by EL_MAP3
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly, k < LENGTH lz
                                                     by LENGTH_MAP3
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
               and MEM (EL k lz) lz                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
               and EL k lz <= MAX_LIST lz            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) (EL k lz) <= c  by property of f

   Note SUM (MAP (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)   by SUM_MAP3_K
    and LENGTH (MAP3 (\x y z. c) lx ly lz) = LENGTH (MAP3 f lx ly lz)             by LENGTH_MAP3
   Thus SUM (MAP f lx ly lz) <= c * LENGTH (MAP3 f lx ly lz)                      by Claim
*)
val SUM_MAP3_UPPER = store_thm(
  "SUM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz. SUM (MAP3 f lx ly lz) <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)` >>
  `SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)` by
  (`LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[LENGTH_MAP3] >>
  (irule SUM_LE >> rw[]) >>
  fs[LENGTH_MAP3] >>
  rw[EL_MAP3, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[SUM_MAP3_K] >>
  `c * LENGTH (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 f lx ly lz)` by rw[LENGTH_MAP3] >>
  decide_tac);

(* Theorem: MONO f ==> MONO_INC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_INC ls
*)
val GENLIST_MONO_INC = store_thm(
  "GENLIST_MONO_INC",
  ``!f:num -> num n. MONO f ==> MONO_INC (GENLIST f n)``,
  rw[]);

(* Theorem: RMONO f ==> MONO_DEC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_DEC ls
*)
val GENLIST_MONO_DEC = store_thm(
  "GENLIST_MONO_DEC",
  ``!f:num -> num n. RMONO f ==> MONO_DEC (GENLIST f n)``,
  rw[]);

(* Theorem: MONO_INC [m .. n] *)
(* Proof:
   This is to show:
        !j k. j <= k /\ k < LENGTH [m .. n] ==> EL j [m .. n] <= EL k [m .. n]
   Note LENGTH [m .. n] = n + 1 - m            by listRangeINC_LEN
     so m + j <= n                             by j < LENGTH [m .. n]
    ==> EL j [m .. n] = m + j                  by listRangeINC_EL
   also m + k <= n                             by k < LENGTH [m .. n]
    ==> EL k [m .. n] = m + k                  by listRangeINC_EL
   Thus EL j [m .. n] <= EL k [m .. n]         by arithmetic
*)
Theorem listRangeINC_MONO_INC:
  !m n. MONO_INC [m .. n]
Proof
  simp[listRangeINC_EL, listRangeINC_LEN]
QED

(* Theorem: MONO_INC [m ..< n] *)
(* Proof:
   This is to show:
        !j k. j <= k /\ k < LENGTH [m ..< n] ==> EL j [m ..< n] <= EL k [m ..< n]
   Note LENGTH [m ..< n] = n - m               by listRangeLHI_LEN
     so m + j < n                              by j < LENGTH [m ..< n]
    ==> EL j [m ..< n] = m + j                 by listRangeLHI_EL
   also m + k < n                              by k < LENGTH [m ..< n]
    ==> EL k [m ..< n] = m + k                 by listRangeLHI_EL
   Thus EL j [m ..< n] <= EL k [m ..< n]       by arithmetic
*)
Theorem listRangeLHI_MONO_INC:
  !m n. MONO_INC [m ..< n]
Proof
  simp[listRangeLHI_EL]
QED

(* ------------------------------------------------------------------------- *)
(* List Dilation                                                             *)
(* ------------------------------------------------------------------------- *)

(*
Use the concept of dilating a list.

Let p = [1;2;3], that is, p = 1 + 2x + 3x^2.
Then q = peval p (x^3) is just q = 1 + 2(x^3) + 3(x^3)^2 = [1;0;0;2;0;0;3]

DILATE 3 [] = []
DILATE 3 (h::t) = [h;0;0] ++ MDILATE 3 t

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3; 0; 0]: thm

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 [h] = [h]) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Multiplicative)                                            *)
(* ------------------------------------------------------------------------- *)

(* Note:
   It would be better to define:  MDILATE e n l = inserting n (e)'s,
   that is, using GENLIST (K e) n, so that only MDILATE e 0 l = l.
   However, the intention is to have later, for polynomials:
       peval p (X ** n) = pdilate n p
   and since X ** 1 = X, and peval p X = p,
   it is desirable to have MDILATE e 1 l = l, with the definition below.

   However, the multiplicative feature at the end destroys such an application.
*)

(* Dilate a list with an element e, for a factor n (n <> 0) *)
val MDILATE_def = Define`
   (MDILATE e n [] = []) /\
   (MDILATE e n (h::t) = if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t))
`;
(*
> EVAL ``MDILATE 0 2 [1;2;3]``;
val it = |- MDILATE 0 2 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``MDILATE 0 3 [1;2;3]``;
val it = |- MDILATE 0 3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``MDILATE #0 3 [a;b;#1]``;
val it = |- MDILATE #0 3 [a; b; #1] = [a; #0; #0; b; #0; #0; #1]: thm
*)

(* Theorem: MDILATE e n [] = [] *)
(* Proof: by MDILATE_def *)
val MDILATE_NIL = store_thm(
  "MDILATE_NIL",
  ``!e n. MDILATE e n [] = []``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_NIL"];

(* Theorem: MDILATE e n [x] = [x] *)
(* Proof: by MDILATE_def *)
val MDILATE_SING = store_thm(
  "MDILATE_SING",
  ``!e n x. MDILATE e n [x] = [x]``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_SING"];

(* Theorem: MDILATE e n (h::t) =
            if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t) *)
(* Proof: by MDILATE_def *)
val MDILATE_CONS = store_thm(
  "MDILATE_CONS",
  ``!e n h t. MDILATE e n (h::t) =
    if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t)``,
  rw[MDILATE_def]);

(* Theorem: MDILATE e 1 l = l *)
(* Proof:
   By induction on l.
   Base: !e. MDILATE e 1 [] = [], true     by MDILATE_NIL
   Step: !e. MDILATE e 1 l = l ==> !h e. MDILATE e 1 (h::l) = h::l
      If l = [],
        MDILATE e 1 [h]
      = [h]                                by MDILATE_SING
      If l <> [],
        MDILATE e 1 (h::l)
      = (h:: GENLIST (K e) (PRE 1)) ++ (MDILATE e n l)   by MDILATE_CONS
      = (h:: GENLIST (K e) (PRE 1)) ++ l   by induction hypothesis
      = (h:: GENLIST (K e) 0) ++ l         by PRE
      = [h] ++ l                           by GENLIST_0
      = h::l                               by CONS_APPEND
*)
val MDILATE_1 = store_thm(
  "MDILATE_1",
  ``!l e. MDILATE e 1 l = l``,
  Induct_on `l` >>
  rw[MDILATE_def]);

(* Theorem: MDILATE e 0 l = l *)
(* Proof:
   By induction on l, and note GENLIST (K e) (PRE 0) = GENLIST (K e) 0 = [].
*)
val MDILATE_0 = store_thm(
  "MDILATE_0",
  ``!l e. MDILATE e 0 l = l``,
  Induct_on `l` >> rw[MDILATE_def]);

(* Theorem: LENGTH (MDILATE e n l) =
            if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l       by MDILATE_0
      Hence true.
   If n <> 0,
      Then 0 < n                   by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: LENGTH (MDILATE e n []) = if n = 0 then LENGTH [] else if [] = [] then 0 else SUC (n * PRE (LENGTH []))
       LENGTH (MDILATE e n [])
     = LENGTH []                   by MDILATE_NIL
     = 0                           by LENGTH_NIL
   Step: LENGTH (MDILATE e n l) = if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) ==>
         !h. LENGTH (MDILATE e n (h::l)) = if n = 0 then LENGTH (h::l) else if h::l = [] then 0 else SUC (n * PRE (LENGTH (h::l)))
       Note h::l = [] <=> F           by NOT_CONS_NIL
       If l = [],
         LENGTH (MDILATE e n [h])
       = LENGTH [h]                   by MDILATE_SING
       = 1                            by LENGTH_EQ_1
       = SUC 0                        by ONE
       = SUC (n * 0)                  by MULT_0
       = SUC (n * (PRE (LENGTH [h]))) by LENGTH_EQ_1, PRE_SUC_EQ
       If l <> [],
         Then LENGTH l <> 0           by LENGTH_NIL
         LENGTH (MDILATE e n (h::l))
       = LENGTH (h:: GENLIST (K e) (PRE n) ++ MDILATE e n l)          by MDILATE_CONS
       = LENGTH (h:: GENLIST (K e) (PRE n)) + LENGTH (MDILATE e n l)  by LENGTH_APPEND
       = n + LENGTH (MDILATE e n l)       by LENGTH_GENLIST
       = n + SUC (n * PRE (LENGTH l))     by induction hypothesis
       = SUC (n + n * PRE (LENGTH l))     by ADD_SUC
       = SUC (n * SUC (PRE (LENGTH l)))   by MULT_SUC
       = SUC (n * LENGTH l)               by SUC_PRE, 0 < LENGTH l
       = SUC (n * PRE (LENGTH (h::l)))    by LENGTH, PRE_SUC_EQ
*)
val MDILATE_LENGTH = store_thm(
  "MDILATE_LENGTH",
  ``!l e n. LENGTH (MDILATE e n l) =
   if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rw[MDILATE_def] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < LENGTH l` by decide_tac >>
  `PRE n + SUC (n * PRE (LENGTH l)) = SUC (PRE n) + n * PRE (LENGTH l)` by rw[] >>
  `_ = n + n * PRE (LENGTH l)` by decide_tac >>
  `_ = n * SUC (PRE (LENGTH l))` by rw[MULT_SUC] >>
  `_ = n * LENGTH l` by metis_tac[SUC_PRE] >>
  decide_tac);

(* Theorem: LENGTH l <= LENGTH (MDILATE e n l) *)
(* Proof:
   If n = 0,
        LENGTH (MDILATE e 0 l)
      = LENGTH l                       by MDILATE_LENGTH
      >= LENGTH l
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                      by MDILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (MDILATE e n (h::t))
      = SUC (n * PRE (LENGTH (h::t)))  by MDILATE_LENGTH
      = SUC (n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (n * LENGTH t)             by PRE
      = n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val MDILATE_LENGTH_LOWER = store_thm(
  "MDILATE_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (MDILATE e n l)``,
  rw[MDILATE_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l)) *)
(* Proof:
   Since n <> 0,
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                  by MDILATE_NIL
      = 0                          by LENGTH_NIL
        SUC (n * PRE (LENGTH []))
      = SUC (n * PRE 0)            by LENGTH_NIL
      = SUC 0                      by PRE, MULT_0
      > 0                          by LESS_SUC
   If l <> [],
        LENGTH (MDILATE e n l)
      = SUC (n * PRE (LENGTH l))   by MDILATE_LENGTH, n <> 0
*)
val MDILATE_LENGTH_UPPER = store_thm(
  "MDILATE_LENGTH_UPPER",
  ``!l e n. 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l))``,
  rw[MDILATE_LENGTH]);

(* Theorem: k < LENGTH (MDILATE e n l) ==>
            (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l     by MDILATE_0
      Hence true trivially.
   If n <> 0,
      Then 0 < n                 by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: !k. k < LENGTH (MDILATE e n []) ==>
         (EL k (MDILATE e n []) = if n = 0 then EL k [] else if k MOD n = 0 then EL (k DIV n) [] else e)
      Note LENGTH (MDILATE e n [])
         = LENGTH []         by MDILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (MDILATE e n l) ==> (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) ==>
         !h k. k < LENGTH (MDILATE e n (h::l)) ==> (EL k (MDILATE e n (h::l)) = if n = 0 then EL k (h::l) else if k MOD n = 0 then EL (k DIV n) (h::l) else e)
      Note LENGTH (MDILATE e n [h]) = 1    by MDILATE_SING
       and LENGTH (MDILATE e n (h::l))
         = SUC (n * PRE (LENGTH (h::l)))   by MDILATE_LENGTH, n <> 0
         = SUC (n * PRE (SUC (LENGTH l)))  by LENGTH
         = SUC (n * LENGTH l)              by PRE

      If l = [],
        Then MDILATE e n [h] = [h]         by MDILATE_SING
         and LENGTH (MDILATE e n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV n = 0                   by ZERO_DIV, 0 < n
         and 0 MOD n = 0                   by ZERO_MOD, 0 < n
        Thus EL k [h] = EL (k DIV n) [h].

      If l <> [],
        Let t = h::GENLIST (K e) (PRE n)
        Note LENGTH t = n                  by LENGTH_GENLIST
        If k < n,
           Then k MOD n = k                by LESS_MOD, k < n
             EL k (MDILATE e n (h::l))
           = EL k (t ++ MDILATE e n l)     by MDILATE_CONS
           = EL k t                        by EL_APPEND, k < LENGTH t
           If k = 0,
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV n) (h::l)          by EL, HD
           If k <> 0,
              EL k t
            = EL k (h:: GENLIST (K e) (PRE n))    by notation of t
            = EL (PRE k) (GENLIST (K e) (PRE n))  by EL_CONS
            = (K e) (PRE k)                by EL_GENLIST, PRE k < PRE n
            = e                            by application of K
        If ~(k < n), n <= k.
           Given k < LENGTH (MDILATE e n (h::l))
              or k < SUC (n * LENGTH l)    by above
             ==> k - n < SUC (n * LENGTH l) - n      by n <= k
                       = SUC (n * LENGTH l - n)      by SUB
                       = SUC (n * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (n * PRE (LENGTH l))    by PRE_SUB1
              or k - n < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - n) MOD n = k MOD n             by SUB_MOD
             and (k - n) DIV n = k DIV n - 1         by SUB_DIV
          If k MOD n = 0,
             Note 0 < k DIV n                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = EL (k DIV n - 1) l                      by induction hypothesis, (k - n) MOD n = 0
           = EL (PRE (k DIV n)) l                    by PRE_SUB1
           = EL (k DIV n) (h::l)                     by EL_CONS, 0 < k DIV n
          If k MOD n <> 0,
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - n) MOD n <> 0
*)
val MDILATE_EL = store_thm(
  "MDILATE_EL",
  ``!l e n k. k < LENGTH (MDILATE e n l) ==>
      (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e)``,
  ntac 3 strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `LENGTH (MDILATE e n [h]) = 1` by rw[MDILATE_SING] >>
  `LENGTH (MDILATE e n (h::l)) = SUC (n * LENGTH l)` by rw[MDILATE_LENGTH] >>
  qabbrev_tac `t = h:: GENLIST (K e) (PRE n)` >>
  `!k. k < 1 <=> (k = 0)` by decide_tac >>
  rw_tac std_ss[MDILATE_def] >-
  metis_tac[ZERO_DIV] >-
  metis_tac[ZERO_MOD] >-
 (rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `!x. EL 0 (h::x) = h` by rw[] >>
    metis_tac[ZERO_DIV],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `(k - n) DIV n = k DIV n - 1` by rw[GSYM SUB_DIV] >>
    `0 < k DIV n` by rw[DIVIDES_MOD_0, DIV_POS] >>
    `EL (k - n) (MDILATE e n l) = EL (k DIV n - 1) l` by rw[] >>
    `_ = EL (PRE (k DIV n)) l` by rw[PRE_SUB1] >>
    `_ = EL (k DIV n) (h::l)` by rw[EL_CONS] >>
    rw[]
  ]) >>
  rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `0 < k /\ PRE k < PRE n` by decide_tac >>
    `EL k t = EL (PRE k) (GENLIST (K e) (PRE n))` by rw[EL_CONS, Abbr`t`] >>
    `_ = e` by rw[] >>
    rw[],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `n <= k` by decide_tac >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `EL (k - n) (MDILATE e n l) = e` by rw[] >>
    rw[]
  ]);

(* This is a milestone theorem. *)

(* Theorem: (MDILATE e n l = []) <=> (l = []) *)
(* Proof:
   If part: MDILATE e n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then MDILATE e 0 l = l     by MDILATE_0
         This contradicts MDILATE e 0 l = [].
      If n <> 0,
         Then LENGTH (MDILATE e n l)
            = SUC (n * PRE (LENGTH l))  by MDILATE_LENGTH
            <> 0                    by SUC_NOT
         So (MDILATE e n l) <> []   by LENGTH_NIL
         This contradicts MDILATE e n l = []
   Only-if part: l = [] ==> MDILATE e n l = []
      True by MDILATE_NIL
*)
val MDILATE_EQ_NIL = store_thm(
  "MDILATE_EQ_NIL",
  ``!l e n. (MDILATE e n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `MDILATE e 0 l = l` by rw[GSYM MDILATE_0] >>
    metis_tac[],
    `LENGTH (MDILATE e n l) = SUC (n * PRE (LENGTH l))` by rw[MDILATE_LENGTH] >>
    `LENGTH (MDILATE e n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (MDILATE e n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (MDILATE e n [])
      = LAST []                by MDILATE_NIL
   If l <> [],
      If n = 0,
        LAST (MDILATE e 0 l)
      = LAST l                 by MDILATE_0
      If n <> 0, then 0 < m    by LESS_0
        Then MDILATE e n l <> []             by MDILATE_EQ_NIL
          or LENGTH (MDILATE e n l) <> 0     by LENGTH_NIL
        Note PRE (LENGTH (MDILATE e n l))
           = PRE (SUC (n * PRE (LENGTH l)))  by MDILATE_LENGTH
           = n * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (MDILATE e n l)).
        Then k < LENGTH (MDILATE e n l)      by PRE x < x
         and k MOD n = 0                     by MOD_EQ_0, MULT_COMM, 0 < n
         and k DIV n = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (MDILATE e n l)
      = EL k (MDILATE e n l)                 by LAST_EL
      = EL (k DIV n) l                       by MDILATE_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val MDILATE_LAST = store_thm(
  "MDILATE_LAST",
  ``!l e n. LAST (MDILATE e n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  `MDILATE e n l <> []` by rw[MDILATE_EQ_NIL] >>
  `LENGTH (MDILATE e n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (MDILATE e n l))` >>
  rw[LAST_EL] >>
  `k = n * PRE (LENGTH l)` by rw[MDILATE_LENGTH, Abbr`k`] >>
  `k MOD n = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV n = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (MDILATE e n l)` by rw[Abbr`k`] >>
  rw[MDILATE_EL]);

(*
Succesive dilation:

> EVAL ``MDILATE #0 3 [a; b; c]``;
val it = |- MDILATE #0 3 [a; b; c] = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 4 [a; b; c]``;
val it = |- MDILATE #0 4 [a; b; c] = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 1 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 1 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; #0; #0; #0; b; #0; #0; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]) <=> T: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]) <=> F: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]) <=> T: thm

So successive dilation is related to product, or factorisation, or primes:
MDILATE e m (MDILATE e n l) = MDILATE e (m * n) l, for 0 < m, 0 < n.

*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Additive)                                                  *)
(* ------------------------------------------------------------------------- *)

(* Dilate by inserting m zeroes, at position n of tail *)
Definition DILATE_def:
  (DILATE e n m [] = []) /\
  (DILATE e n m [h] = [h]) /\
  (DILATE e n m (h::t) = h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)))
Termination
  WF_REL_TAC `measure (λ(a,b,c,d). LENGTH d)` >>
  rw[LENGTH_DROP]
End

(*
> EVAL ``DILATE 0 0 1 [1;2;3]``;
val it = |- DILATE 0 0 1 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``DILATE 0 0 2 [1;2;3]``;
val it = |- DILATE 0 0 2 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 [1;2;3]``;
val it = |- DILATE 0 1 1 [1; 2; 3] = [1; 2; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 1 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 1 [1; 2; 3]) = [1; 0; 0; 2; 0; 0; 3]: thm
>  EVAL ``DILATE 0 0 3 [1;2;3]``;
val it = |- DILATE 0 0 3 [1; 2; 3] = [1; 0; 0; 0; 2; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 2 [1; 2; 3]) = [1; 0; 0; 0; 2; 0; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 0 3 [1;2;3] = DILATE 0 2 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- (DILATE 0 0 3 [1; 2; 3] = DILATE 0 2 1 (DILATE 0 0 2 [1; 2; 3])) <=> T: thm

> EVAL ``DILATE 0 0 0 [1;2;3]``;
val it = |- DILATE 0 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 0 [1;2;3]``;
val it = |- DILATE 1 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 1 [1;2;3]``;
val it = |- DILATE 1 0 1 [1; 2; 3] = [1; 1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 1 [1;2;3]``;
val it = |- DILATE 1 1 1 [1; 2; 3] = [1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 2 [1;2;3]``;
val it = |- DILATE 1 1 2 [1; 2; 3] = [1; 2; 1; 1; 3]: thm
> EVAL ``DILATE 1 1 3 [1;2;3]``;
val it = |- DILATE 1 1 3 [1; 2; 3] = [1; 2; 1; 1; 1; 3]: thm
*)

(* Theorem: DILATE e n m [] = [] *)
(* Proof: by DILATE_def *)
val DILATE_NIL = save_thm("DILATE_NIL", DILATE_def |> CONJUNCT1);
(* val DILATE_NIL = |- !n m e. DILATE e n m [] = []: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_NIL"];

(* Theorem: DILATE e n m [h] = [h] *)
(* Proof: by DILATE_def *)
val DILATE_SING = save_thm("DILATE_SING", DILATE_def |> CONJUNCT2 |> CONJUNCT1);
(* val DILATE_SING = |- !n m h e. DILATE e n m [h] = [h]: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_SING"];

(* Theorem: DILATE e n m (h::t) =
            if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)) *)
(* Proof: by DILATE_def, list_CASES *)
val DILATE_CONS = store_thm(
  "DILATE_CONS",
  ``!n m h t e. DILATE e n m (h::t) =
    if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t))``,
  metis_tac[DILATE_def, list_CASES]);

(* Theorem: DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t) *)
(* Proof:
   If t = [],
     DILATE e 0 n (h::t) = [h]    by DILATE_CONS
   If t <> [],
     DILATE e 0 n (h::t)
   = h:: (TAKE 0 t ++ (GENLIST (K e) n) ++ DILATE e 0 n (DROP 0 t))  by DILATE_CONS
   = h:: ([] ++ (GENLIST (K e) n) ++ DILATE e 0 n t)                 by TAKE_0, DROP_0
   = h:: (GENLIST (K e) n ++ DILATE e 0 n t)                         by APPEND
*)
val DILATE_0_CONS = store_thm(
  "DILATE_0_CONS",
  ``!n h t e. DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t)``,
  rw[DILATE_CONS]);

(* Theorem: DILATE e 0 0 l = l *)
(* Proof:
   By induction on l.
   Base: DILATE e 0 0 [] = [], true         by DILATE_NIL
   Step: DILATE e 0 0 l = l ==> !h. DILATE e 0 0 (h::l) = h::l
      If l = [],
         DILATE e 0 0 [h] = [h]             by DILATE_SING
      If l <> [],
         DILATE e 0 0 (h::l)
       = h::(GENLIST (K e) 0 ++ DILATE e 0 0 l)   by DILATE_0_CONS
       = h::([] ++ DILATE e 0 0 l)                by GENLIST_0
       = h:: DILATE e 0 0 l                       by APPEND
       = h::l                                     by induction hypothesis
*)
val DILATE_0_0 = store_thm(
  "DILATE_0_0",
  ``!l e. DILATE e 0 0 l = l``,
  Induct >>
  rw[DILATE_0_CONS]);

(* Theorem: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) *)
(* Proof:
   If n = 0,
      DILATE e 0 1 l = DILATE e 0 1 (DILATE e 0 0 l)   by DILATE_0_0
   If n <> 0,
      GENLIST (K e) n <> []       by LENGTH_GENLIST, LENGTH_NIL
   By induction on l.
   Base: DILATE e 0 (SUC n) [] = DILATE e n 1 (DILATE e 0 n [])
      DILATE e 0 (SUC n) [] = []                  by DILATE_NIL
        DILATE e n 1 (DILATE e 0 n [])
      = DILATE e n 1 [] = []                      by DILATE_NIL
   Step: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) ==>
         !h. DILATE e 0 (SUC n) (h::l) = DILATE e n 1 (DILATE e 0 n (h::l))
      If l = [],
        DILATE e 0 (SUC n) [h] = [h]       by DILATE_SING
          DILATE e n 1 (DILATE e 0 n [h])
        = DILATE e n 1 [h] = [h]           by DILATE_SING
      If l <> [],
          DILATE e 0 (SUC n) (h::l)
        = h::(GENLIST (K e) (SUC n) ++ DILATE e 0 (SUC n) l)                by DILATE_0_CONS
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by induction hypothesis

        Note LENGTH (GENLIST (K e) n) = n                 by LENGTH_GENLIST
          so (GENLIST (K e) n ++ DILATE e 0 n l) <> []    by APPEND_eq_NIL, LENGTH_NIL [1]
         and TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) = GENLIST (K e) n   by TAKE_LENGTH_APPEND [2]
         and DROP n (GENLIST (K e) n ++ DILATE e 0 n l) = DILATE e 0 n l    by DROP_LENGTH_APPEND [3]
         and GENLIST (K e) (SUC n)
           = GENLIST (K e) (1 + n)                        by SUC_ONE_ADD
           = GENLIST (K e) n ++ GENLIST (K e) 1           by GENLIST_K_ADD [4]

          DILATE e n 1 (DILATE e 0 n (h::l))
        = DILATE e n 1 (h::(GENLIST (K e) n ++ DILATE e 0 n l))             by DILATE_0_CONS
        = h::(TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) ++ GENLIST (K e) 1 ++
               DILATE e n 1 (DROP n (GENLIST (K e) n ++ DILATE e 0 n l)))   by DILATE_CONS, [1]
        = h::(GENLIST (K e) n ++ GENLIST (K e) 1 ++ DILATE e n 1 (DILATE e 0 n l))   by above [2], [3]
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by above [4]
*)
val DILATE_0_SUC = store_thm(
  "DILATE_0_SUC",
  ``!l e n. DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[DILATE_SING] >>
  qabbrev_tac `a = GENLIST (K e) n ++ DILATE e 0 n l` >>
  `LENGTH (GENLIST (K e) n) = n` by rw[] >>
  `a <> []` by metis_tac[APPEND_eq_NIL, LENGTH_NIL] >>
  `TAKE n a = GENLIST (K e) n` by metis_tac[TAKE_LENGTH_APPEND] >>
  `DROP n a = DILATE e 0 n l` by metis_tac[DROP_LENGTH_APPEND] >>
  `GENLIST (K e) (SUC n) = GENLIST (K e) n ++ GENLIST (K e) 1` by rw_tac std_ss[SUC_ONE_ADD, GENLIST_K_ADD] >>
  metis_tac[DILATE_0_CONS, DILATE_CONS]);

(* Theorem: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   By induction on l.
   Base: LENGTH (DILATE e 0 n []) = 0
         LENGTH (DILATE e 0 n [])
       = LENGTH []                       by DILATE_NIL
       = 0                               by LENGTH_NIL
   Step: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) ==>
         !h. LENGTH (DILATE e 0 n (h::l)) = SUC (SUC n * PRE (LENGTH (h::l)))
       If l = [],
          LENGTH (DILATE e 0 n [h])
        = LENGTH [h]                     by DILATE_SING
        = 1                              by LENGTH
          SUC (SUC n * PRE (LENGTH [h])
        = SUC (SUC n * PRE 1)            by LENGTH
        = SUC (SUC n * 0)                by PRE_SUB1
        = SUC 0                          by MULT_0
        = 1                              by ONE
       If l <> [],
          Note LENGTH l <> 0             by LENGTH_NIL
          LENGTH (DILATE e 0 n (h::l))
        = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))           by DILATE_0_CONS
        = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))          by LENGTH
        = SUC (LENGTH (GENLIST (K e) n) + LENGTH (DILATE e 0 n l))  by LENGTH_APPEND
        = SUC (n + LENGTH (DILATE e 0 n l))        by LENGTH_GENLIST
        = SUC (n + SUC (SUC n * PRE (LENGTH l)))   by induction hypothesis
        = SUC (SUC (n + SUC n * PRE (LENGTH l)))   by ADD_SUC
        = SUC (SUC n  + SUC n * PRE (LENGTH l))    by ADD_COMM, ADD_SUC
        = SUC (SUC n * SUC (PRE (LENGTH l)))       by MULT_SUC
        = SUC (SUC n * LENGTH l)                   by SUC_PRE, 0 < LENGTH l
        = SUC (SUC n * PRE (LENGTH (h::l)))        by LENGTH, PRE_SUC_EQ
*)
val DILATE_0_LENGTH = store_thm(
  "DILATE_0_LENGTH",
  ``!l e n. LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l))``,
  Induct >-
  rw[] >>
  rw_tac std_ss[LENGTH] >>
  Cases_on `l = []` >-
  rw[] >>
  `0 < LENGTH l` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  `LENGTH (DILATE e 0 n (h::l)) = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))` by rw[DILATE_0_CONS] >>
  `_ = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + LENGTH (DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + SUC (SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC (n + SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC n + SUC n * PRE (LENGTH l))` by rw[] >>
  `_ = SUC (SUC n * SUC (PRE (LENGTH l)))` by rw[MULT_SUC] >>
  `_ = SUC (SUC n * LENGTH l)` by rw[SUC_PRE] >>
  rw[]);

(* Theorem: LENGTH l <= LENGTH (DILATE e 0 n l) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (DILATE e 0 n (h::t))
      = SUC (SUC n * PRE (LENGTH (h::t)))  by DILATE_0_LENGTH
      = SUC (SUC n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (SUC n * LENGTH t)             by PRE
      = SUC n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < SUC n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val DILATE_0_LENGTH_LOWER = store_thm(
  "DILATE_0_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (DILATE e 0 n l)``,
  rw[DILATE_0_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      = 0                              by LENGTH_NIL
        SUC (SUC n * PRE (LENGTH []))
      = SUC (SUC n * PRE 0)            by LENGTH_NIL
      = SUC 0                          by PRE, MULT_0
      > 0                              by LESS_SUC
   If l <> [],
        LENGTH (DILATE e 0 n l)
      = SUC (SUC n * PRE (LENGTH l))   by DILATE_0_LENGTH
*)
val DILATE_0_LENGTH_UPPER = store_thm(
  "DILATE_0_LENGTH_UPPER",
  ``!l e n. LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l))``,
  rw[DILATE_0_LENGTH]);

(* Theorem: k < LENGTH (DILATE e 0 n l) ==>
            (EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l else e) *)
(* Proof:
   Let m = SUC n, then 0 < m.
   By induction on l.
   Base: !k. k < LENGTH (DILATE e 0 n []) ==> (EL k (DILATE e 0 n []) = if k MOD m = 0 then EL (k DIV m) [] else e)
      Note LENGTH (DILATE e 0 n [])
         = LENGTH []         by DILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (DILATE e 0 n l) ==> (EL k (DILATE e 0 n l) = if k MOD m = 0 then EL (k DIV m) l else e) ==>
         !h k. k < LENGTH (DILATE e 0 n (h::l)) ==> (EL k (DILATE e 0 n (h::l)) = if k MOD m = 0 then EL (k DIV m) (h::l) else e)
      Note LENGTH (DILATE e 0 n [h]) = 1    by DILATE_SING
       and LENGTH (DILATE e 0 n (h::l))
         = SUC (m * PRE (LENGTH (h::l)))    by DILATE_0_LENGTH, n <> 0
         = SUC (m * PRE (SUC (LENGTH l)))   by LENGTH
         = SUC (m * LENGTH l)               by PRE

      If l = [],
        Then DILATE e 0 n [h] = [h]         by DILATE_SING
         and LENGTH (DILATE e 0 n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV m = 0                    by ZERO_DIV, 0 < m
         and 0 MOD m = 0                    by ZERO_MOD, 0 < m
        Thus EL k [h] = EL (k DIV m) [h].

      If l <> [],
        Let t = h:: GENLIST (K e) n.
        Note LENGTH t = SUC n = m           by LENGTH_GENLIST
        If k < m,
           Then k MOD m = k                 by LESS_MOD, k < m
             EL k (DILATE e 0 n (h::l))
           = EL k (t ++ DILATE e 0 n l)     by DILATE_0_CONS
           = EL k t                         by EL_APPEND, k < LENGTH t
           If k = 0, i.e. k MOD m = 0.
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV m) (h::l)           by EL, HD
           If k <> 0, i.e. k MOD m <> 0.
              EL k t
            = EL k (h:: GENLIST (K e) n)    by notation of t
            = EL (PRE k) (GENLIST (K e) n)  by EL_CONS
            = (K e) (PRE k)                 by EL_GENLIST, PRE k < PRE m = n
            = e                             by application of K
        If ~(k < m), then m <= k.
           Given k < LENGTH (DILATE e 0 n (h::l))
              or k < SUC (m * LENGTH l)              by above
             ==> k - m < SUC (m * LENGTH l) - m      by m <= k
                       = SUC (m * LENGTH l - m)      by SUB
                       = SUC (m * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (m * PRE (LENGTH l))    by PRE_SUB1
              or k - m < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - m) MOD m = k MOD m             by SUB_MOD
             and (k - m) DIV m = k DIV m - 1         by SUB_DIV
          If k MOD m = 0,
             Note 0 < k DIV m                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, m <= k
           = EL (k DIV m - 1) l                      by induction hypothesis, (k - m) MOD m = 0
           = EL (PRE (k DIV m)) l                    by PRE_SUB1
           = EL (k DIV m) (h::l)                     by EL_CONS, 0 < k DIV m
          If k MOD m <> 0,
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - m) MOD n <> 0
*)
Theorem DILATE_0_EL:
  !l e n k. k < LENGTH (DILATE e 0 n l) ==>
     (EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l else e)
Proof
  ntac 3 strip_tac >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `LENGTH (DILATE e 0 n [h]) = 1` by rw[DILATE_SING] >>
  `LENGTH (DILATE e 0 n (h::l)) = SUC (m * LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`m`] >>
  Cases_on `l = []` >| [
    `k = 0` by rw[] >>
    `k MOD m = 0` by rw[] >>
    `k DIV m = 0` by rw[ZERO_DIV] >>
    rw_tac std_ss[DILATE_SING],
    qabbrev_tac `t = h::GENLIST (K e) n` >>
    `DILATE e 0 n (h::l) = t ++ DILATE e 0 n l` by rw[DILATE_0_CONS, Abbr`t`] >>
    `m = LENGTH t` by rw[Abbr`t`] >>
    Cases_on `k < m` >| [
      `k MOD m = k` by rw[] >>
      `EL k (DILATE e 0 n (h::l)) = EL k t` by rw[EL_APPEND] >>
      Cases_on `k = 0` >| [
        `EL 0 t = h` by rw[Abbr`t`] >>
        rw[ZERO_DIV],
        `PRE m = n` by rw[Abbr`m`] >>
        `PRE k < n` by decide_tac >>
        `EL k t = EL (PRE k) (GENLIST (K e) n)` by rw[EL_CONS, Abbr`t`] >>
        `_ = (K e) (PRE k)` by rw[EL_GENLIST] >>
        rw[]
      ],
      `m <= k` by decide_tac >>
      `EL k (t ++ DILATE e 0 n l) = EL (k - m) (DILATE e 0 n l)` by simp[EL_APPEND] >>
      `k - m < LENGTH (DILATE e 0 n l)` by rw[DILATE_0_LENGTH] >>
      `(k - m) MOD m = k MOD m` by simp[SUB_MOD] >>
      `(k - m) DIV m = k DIV m - 1` by simp[SUB_DIV] >>
      Cases_on `k MOD m = 0` >| [
        `0 < k DIV m` by rw[DIVIDES_MOD_0, DIV_POS] >>
        `EL (k - m) (DILATE e 0 n l) = EL (k DIV m - 1) l` by rw[] >>
        `_ = EL (PRE (k DIV m)) l` by rw[PRE_SUB1] >>
        `_ = EL (k DIV m) (h::l)` by rw[EL_CONS] >>
        rw[],
        `EL (k - m) (DILATE e 0 n l)  = e` by rw[] >>
        rw[]
      ]
    ]
  ]
QED

(* This is a milestone theorem. *)

(* Theorem: (DILATE e 0 n l = []) <=> (l = []) *)
(* Proof:
   If part: DILATE e 0 n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then DILATE e n 0 l = l     by DILATE_0_0
         This contradicts DILATE e n 0 l = [].
      If n <> 0,
         Then LENGTH (DILATE e 0 n l)
            = SUC (SUC n * PRE (LENGTH l))  by DILATE_0_LENGTH
            <> 0                     by SUC_NOT
         So (DILATE e 0 n l) <> []   by LENGTH_NIL
         This contradicts DILATE e 0 n l = []
   Only-if part: l = [] ==> DILATE e 0 n l = []
      True by DILATE_NIL
*)
val DILATE_0_EQ_NIL = store_thm(
  "DILATE_0_EQ_NIL",
  ``!l e n. (DILATE e 0 n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `DILATE e 0 0 l = l` by rw[GSYM DILATE_0_0] >>
    metis_tac[],
    `LENGTH (DILATE e 0 n l) = SUC (SUC n * PRE (LENGTH l))` by rw[DILATE_0_LENGTH] >>
    `LENGTH (DILATE e 0 n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (DILATE e 0 n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (DILATE e 0 n [])
      = LAST []                by DILATE_NIL
   If l <> [],
      If n = 0,
        LAST (DILATE e 0 0 l)
      = LAST l                 by DILATE_0_0
      If n <> 0,
        Then DILATE e 0 n l <> []            by DILATE_0_EQ_NIL
          or LENGTH (DILATE e 0 n l) <> 0    by LENGTH_NIL
        Let m = SUC n, then 0 < m            by LESS_0
        Note PRE (LENGTH (DILATE e 0 n l))
           = PRE (SUC (m * PRE (LENGTH l)))  by DILATE_0_LENGTH
           = m * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (DILATE e 0 n l)).
        Then k < LENGTH (DILATE e 0 n l)     by PRE x < x
         and k MOD m = 0                     by MOD_EQ_0, MULT_COMM, 0 < m
         and k DIV m = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (DILATE e 0 n l)
      = EL k (DILATE e 0 n l)                by LAST_EL
      = EL (k DIV m) l                       by DILATE_0_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val DILATE_0_LAST = store_thm(
  "DILATE_0_LAST",
  ``!l e n. LAST (DILATE e 0 n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  `0 < n` by decide_tac >>
  `DILATE e 0 n l <> []` by rw[DILATE_0_EQ_NIL] >>
  `LENGTH (DILATE e 0 n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (DILATE e 0 n l))` >>
  rw[LAST_EL] >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  `k = m * PRE (LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`k`, Abbr`m`] >>
  `k MOD m = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV m = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (DILATE e 0 n l)` by simp[Abbr`k`] >>
  Q.RM_ABBREV_TAC ‘k’ >>
  rw[DILATE_0_EL]);

(* ------------------------------------------------------------------------- *)
(* FUNPOW with incremental cons.                                             *)
(* ------------------------------------------------------------------------- *)

(* Note from HelperList: m downto n = REVERSE [m .. n] *)

(* Idea: when applying incremental cons (f head) to a list for n times,
         head of the result is f^n (head of list). *)

(* Theorem: HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls) *)
(* Proof:
   Let h = (\ls. f (HD ls)::ls).
   By induction on n.
   Base: !ls. HD (FUNPOW h 0 ls) = FUNPOW f 0 (HD ls)
           HD (FUNPOW h 0 ls)
         = HD ls                by FUNPOW_0
         = FUNPOW f 0 (HD ls)   by FUNPOW_0
   Step: !ls. HD (FUNPOW h n ls) = FUNPOW f n (HD ls) ==>
         !ls. HD (FUNPOW h (SUC n) ls) = FUNPOW f (SUC n) (HD ls)
           HD (FUNPOW h (SUC n) ls)
         = HD (FUNPOW h n (h ls))    by FUNPOW
         = FUNPOW f n (HD (h ls))    by induction hypothesis
         = FUNPOW f n (f (HD ls))    by definition of h
         = FUNPOW f (SUC n) (HD ls)  by FUNPOW
*)
Theorem FUNPOW_cons_head:
  !f n ls. HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls)
Proof
  strip_tac >>
  qabbrev_tac `h = \ls. f (HD ls)::ls` >>
  Induct >-
  simp[] >>
  rw[FUNPOW, Abbr`h`]
QED

(* Idea: when applying incremental cons (f head) to a singleton [u] for n times,
         the result is the list [f^n(u), .... f(u), u]. *)

(* Theorem: FUNPOW (\ls. f (HD ls)::ls) n [u] =
            MAP (\j. FUNPOW f j u) (n downto 0) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [u] = MAP h (0 downto 0)
           FUNPOW g 0 [u]
         = [u]                       by FUNPOW_0
         = [FUNPOW f 0 u]            by FUNPOW_0
         = MAP h [0]                 by MAP
         = MAP h (0 downto 0)  by REVERSE
   Step: FUNPOW g n [u] = MAP h (n downto 0) ==>
         FUNPOW g (SUC n) [u] = MAP h (SUC n downto 0)
           FUNPOW g (SUC n) [u]
         = g (FUNPOW g n [u])             by FUNPOW_SUC
         = g (MAP h (n downto 0))   by induction hypothesis
         = f (HD (MAP h (n downto 0))) ::
             MAP h (n downto 0)     by definition of g
         Now f (HD (MAP h (n downto 0)))
           = f (HD (MAP h (MAP (\x. n - x) [0 .. n])))    by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n - x) [0 .. n]))        by MAP_COMPOSE
           = f ((h o (\x. n - x)) 0)                      by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 0)
           = MAP h ((n + 1) :: (n downto 0))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [0 .. n]))   by REVERSE_SNOC
           = MAP h (SUC n downto 0)                  by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_0:
  !f u n. FUNPOW (\ls. f (HD ls)::ls) n [u] =
          MAP (\j. FUNPOW f j u) (n downto 0)
Proof
  ntac 2 strip_tac >>
  Induct >-
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  rw[] >>
  `f (HD (MAP h (n downto 0))) = h (n + 1)` by
  (`[0 .. n] = 0 :: [1 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `FUNPOW g (SUC n) [u] = g (FUNPOW g n [u])` by rw[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 0))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 0)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 0))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [0 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* Idea: when applying incremental cons (f head) to a singleton [f(u)] for (n-1) times,
         the result is the list [f^n(u), .... f(u)]. *)

(* Theorem: 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
            MAP (\j. FUNPOW f j u) (n downto 1)) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [f u] = MAP h (REVERSE [1 .. 1])
           FUNPOW g 0 [f u]
         = [f u]                     by FUNPOW_0
         = [FUNPOW f 1 u]            by FUNPOW_1
         = MAP h [1]                 by MAP
         = MAP h (REVERSE [1 .. 1])  by REVERSE
   Step: 0 < n ==> FUNPOW g (n-1) [f u] = MAP h (n downto 1) ==>
         FUNPOW g n [f u] = MAP h (REVERSE [1 .. SUC n])
         The case n = 0 is the base case. For n <> 0,
           FUNPOW g n [f u]
         = g (FUNPOW g (n-1) [f u])       by FUNPOW_SUC
         = g (MAP h (n downto 1))         by induction hypothesis
         = f (HD (MAP h (n downto 1))) ::
             MAP h (n downto 1)           by definition of g
         Now f (HD (MAP h (n downto 1)))
           = f (HD (MAP h (MAP (\x. n + 1 - x) [1 .. n])))  by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n + 1 - x) [1 .. n]))      by MAP_COMPOSE
           = f ((h o (\x. n + 1 - x)) 1)                    by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 1)
           = MAP h ((n + 1) :: (n downto 1))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [1 .. n]))   by REVERSE_SNOC
           = MAP h (REVERSE [1 .. SUC n])            by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_1:
  !f u n. 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
          MAP (\j. FUNPOW f j u) (n downto 1))
Proof
  ntac 2 strip_tac >>
  Induct >-
  simp[] >>
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  Cases_on `n = 0` >-
  rw[Abbr`g`, Abbr`h`] >>
  `f (HD (MAP h (n downto 1))) = h (n + 1)` by
  (`[1 .. n] = 1 :: [2 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `n = SUC (n-1)` by decide_tac >>
  `FUNPOW g n [f u] = g (FUNPOW g (n - 1) [f u])` by metis_tac[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 1))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 1)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 1))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [1 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* ------------------------------------------------------------------------- *)
(* Binomial Documentation                                                    *)
(* ------------------------------------------------------------------------- *)
(* Definitions and Theorems (# are exported):

   Binomial Coefficients:
   binomial_def        |- (binomial 0 0 = 1) /\ (!n. binomial (SUC n) 0 = 1) /\
                          (!k. binomial 0 (SUC k) = 0) /\
                          !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_alt        |- !n k. binomial n 0 = 1 /\ binomial 0 (k + 1) = 0 /\
                                binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1)
   binomial_less_0     |- !n k. n < k ==> (binomial n k = 0)
   binomial_n_0        |- !n. binomial n 0 = 1
   binomial_n_n        |- !n. binomial n n = 1
   binomial_0_n        |- !n. binomial 0 n = if n = 0 then 1 else 0
   binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_formula    |- !n k. binomial (n + k) k * (FACT n * FACT k) = FACT (n + k)
   binomial_formula2   |- !n k. k <= n ==> (FACT n = binomial n k * (FACT (n - k) * FACT k))
   binomial_formula3   |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_fact       |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_n_k        |- !n k. k <= n ==> (binomial n k = FACT n DIV FACT k DIV FACT (n - k)
   binomial_n_1        |- !n. binomial n 1 = n
   binomial_sym        |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
   binomial_is_integer |- !n k. k <= n ==> (FACT k * FACT (n - k)) divides (FACT n)
   binomial_pos        |- !n k. k <= n ==> 0 < binomial n k
   binomial_eq_0       |- !n k. (binomial n k = 0) <=> n < k
   binomial_1_n        |- !n. binomial 1 n = if 1 < n then 0 else 1
   binomial_up_eqn     |- !n. 0 < n ==> !k. n * binomial (n - 1) k = (n - k) * binomial n k
   binomial_up         |- !n. 0 < n ==> !k. binomial (n - 1) k = (n - k) * binomial n k DIV n
   binomial_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * binomial n (k + 1) = (n - k) * binomial n k
   binomial_right      |- !n. 0 < n ==> !k. binomial n (k + 1) = (n - k) * binomial n k DIV (k + 1)
   binomial_monotone   |- !n k. k < HALF n ==> binomial n k < binomial n (k + 1)
   binomial_max        |- !n k. binomial n k <= binomial n (HALF n)
   binomial_iff        |- !f. f = binomial <=>
                              !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\
                                    f (n + 1) (k + 1) = f n k + f n (k + 1)

   Primes and Binomial Coefficients:
   prime_divides_binomials     |- !n.  prime n ==> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_divides_binomials_alt |- !n k. prime n /\ 0 < k /\ k < n ==> n divides binomial n k
   prime_divisor_property      |- !n p. 1 < n /\ p < n /\ prime p /\ p divides n ==> ~(p divides (FACT (n - 1) DIV FACT (n - p)))
   divides_binomials_imp_prime |- !n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n
   prime_iff_divides_binomials |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_iff_divides_binomials_alt
                               |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> binomial n k MOD n = 0

   Binomial Theorem:
   GENLIST_binomial_index_shift |- !n x y. GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n =
                                           GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** SUC k) n
   binomial_index_shift   |- !n x y. (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) o SUC =
                                     (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** SUC k)
   binomial_term_merge_x  |- !n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** SUC (n - k) * y ** k)
   binomial_term_merge_y  |- !n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** (n - k) * y ** SUC k)
   binomial_thm     |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))
   binomial_thm_alt |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1))
   binomial_sum     |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
   binomial_sum_alt |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n

   Binomial Horizontal List:
   binomial_horizontal_0        |- binomial_horizontal 0 = [1]
   binomial_horizontal_len      |- !n. LENGTH (binomial_horizontal n) = n + 1
   binomial_horizontal_mem      |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
   binomial_horizontal_mem_iff  |- !n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n
   binomial_horizontal_member   |- !n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)
   binomial_horizontal_element  |- !n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)
   binomial_horizontal_pos      |- !n. EVERY (\x. 0 < x) (binomial_horizontal n)
   binomial_horizontal_pos_alt  |- !n x. MEM x (binomial_horizontal n) ==> 0 < x
   binomial_horizontal_sum      |- !n. SUM (binomial_horizontal n) = 2 ** n
   binomial_horizontal_max      |- !n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)
   binomial_row_max             |- !n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)
   binomial_product_identity    |- !m n k. k <= m /\ m <= n ==>
                          (binomial m k * binomial n m = binomial n k * binomial (n - k) (m - k))
   binomial_middle_upper_bound  |- !n. binomial n (HALF n) <= 4 ** HALF n

   Stirling's Approximation:
   Stirling = (!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
              (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
              (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
              (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)
   binomial_middle_by_stirling  |- Stirling ==>
               !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))

   Useful theorems for Binomial:
   binomial_range_shift  |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                                            (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))
   binomial_mod_zero     |- !n. 0 < n ==> !k. (binomial n k MOD n = 0) <=>
                                          (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)
   binomial_range_shift_alt   |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==>
            (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))
   binomial_mod_zero_alt  |- !n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)

   Binomial Theorem with prime exponent:
   binomial_thm_prime  |- !p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)
*)

(* ------------------------------------------------------------------------- *)
(* Binomial Coefficients                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define Binomials:
   C(n,0) = 1
   C(0,k) = 0 if k > 0
   C(n+1,k+1) = C(n,k) + C(n,k+1)
*)
val binomial_def = Define`
    (binomial 0 0 = 1) /\
    (binomial (SUC n) 0 = 1) /\
    (binomial 0 (SUC k) = 0)  /\
    (binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k))
`;

(* Theorem: alternative definition of C(n,k). *)
(* Proof: by binomial_def. *)
Theorem binomial_alt:
  !n k. (binomial n 0 = 1) /\
         (binomial 0 (k + 1) = 0) /\
         (binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1))
Proof
  rewrite_tac[binomial_def, GSYM ADD1] >>
  (Cases_on `n` >> simp[binomial_def])
QED

(* Basic properties *)

(* Theorem: C(n,k) = 0 if n < k *)
(* Proof:
   By induction on n.
   Base case: C(0,k) = 0 if 0 < k, by definition.
   Step case: assume C(n,k) = 0 if n < k.
   then for SUC n < k,
        C(SUC n, k)
      = C(SUC n, SUC h)   where k = SUC h
      = C(n,h) + C(n,SUC h)  h < SUC h = k
      = 0 + 0             by induction hypothesis
      = 0
*)
val binomial_less_0 = store_thm(
  "binomial_less_0",
  ``!n k. n < k ==> (binomial n k = 0)``,
  Induct_on `n` >-
  metis_tac[binomial_def, num_CASES, NOT_ZERO] >>
  rw[binomial_def] >>
  `?h. k = SUC h` by metis_tac[SUC_NOT, NOT_ZERO, SUC_EXISTS, LESS_TRANS] >>
  metis_tac[binomial_def, LESS_MONO_EQ, LESS_TRANS, LESS_SUC, ADD_0]);

(* Theorem: C(n,0) = 1 *)
(* Proof:
   If n = 0, C(n, 0) = C(0, 0) = 1            by binomial_def
   If n <> 0, n = SUC m, and C(SUC m, 0) = 1  by binomial_def
*)
val binomial_n_0 = store_thm(
  "binomial_n_0",
  ``!n. binomial n 0 = 1``,
  metis_tac[binomial_def, num_CASES]);

(* Theorem: C(n,n) = 1 *)
(* Proof:
   By induction on n.
   Base case: C(0,0) = 1,  true by binomial_def.
   Step case: assume C(n,n) = 1
     C(SUC n, SUC n)
   = C(n,n) + C(n,SUC n)
   = 1 + C(n,SUC n)      by induction hypothesis
   = 1 + 0               by binomial_less_0
   = 1
*)
val binomial_n_n = store_thm(
  "binomial_n_n",
  ``!n. binomial n n = 1``,
  Induct_on `n` >-
  metis_tac[binomial_def] >>
  metis_tac[binomial_def, LESS_SUC, binomial_less_0, ADD_0]);

(* Theorem: binomial 0 n = if n = 0 then 1 else 0 *)
(* Proof:
   If n = 0,
      binomial 0 0 = 1     by binomial_n_0
   If n <> 0, then 0 < n.
      binomial 0 n = 0     by binomial_less_0
*)
val binomial_0_n = store_thm(
  "binomial_0_n",
  ``!n. binomial 0 n = if n = 0 then 1 else 0``,
  rw[binomial_n_0, binomial_less_0]);

(* Theorem: C(n+1,k+1) = C(n,k) + C(n,k+1) *)
(* Proof: by definition. *)
val binomial_recurrence = store_thm(
  "binomial_recurrence",
  ``!n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)``,
  rw[binomial_def]);

(* Theorem: C(n+k,k) = (n+k)!/n!k!  *)
(* Proof:
   By induction on k.
   Base case: C(n,0) = n!n! = 1   by binomial_n_0
   Step case: assume C(n+k,k) = (n+k)!/n!k!
   To prove C(n+SUC k, SUC k) = (n+SUC k)!/n!(SUC k)!
      By induction on n.
      Base case: C(SUC k, SUC k) = (SUC k)!/(SUC k)! = 1   by binomial_n_n
      Step case: assume C(n+SUC k, SUC k) = (n +SUC k)!/n!(SUC k)!
      To prove C(SUC n + SUC k, SUC k) = (SUC n + SUC k)!/(SUC n)!(SUC k)!
        C(SUC n + SUC k, SUC k)
      = C(SUC SUC (n+k), SUC k)
      = C(SUC (n+k),k) + C(SUC (n+k), SUC k)
      = C(SUC n + k, k) + C(n + SUC k, SUC k)
      = (SUC n + k)!/(SUC n)!k! + (n + SUC k)!/n!(SUC k)!   by two induction hypothesis
      = ((SUC n + k)!(SUC k) + (n + SUC k)(SUC n))/(SUC n)!(SUC k)!
      = (SUC n + SUC k)!/(SUC n)!(SUC k)!
*)
val binomial_formula = store_thm(
  "binomial_formula",
  ``!n k. binomial (n+k) k * (FACT n * FACT k) = FACT (n+k)``,
  Induct_on `k` >-
  metis_tac[binomial_n_0, FACT, MULT_CLAUSES, ADD_0] >>
  Induct_on `n` >-
  metis_tac[binomial_n_n, FACT, MULT_CLAUSES, ADD_CLAUSES] >>
  `SUC n + SUC k = SUC (SUC (n+k))` by decide_tac >>
  `SUC (n + k) = SUC n + k` by decide_tac >>
  `binomial (SUC n + SUC k) (SUC k) * (FACT (SUC n) * FACT (SUC k)) =
    (binomial (SUC (n + k)) k +
     binomial (SUC (n + k)) (SUC k)) * (FACT (SUC n) * FACT (SUC k))`
    by metis_tac[binomial_recurrence] >>
  `_ = binomial (SUC (n + k)) k * (FACT (SUC n) * FACT (SUC k)) +
        binomial (SUC (n + k)) (SUC k) * (FACT (SUC n) * FACT (SUC k))`
        by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = binomial (SUC n + k) k * (FACT (SUC n) * ((SUC k) * FACT k)) +
        binomial (n + SUC k) (SUC k) * ((SUC n) * FACT n * FACT (SUC k))`
        by metis_tac[ADD_COMM, SUC_ADD_SYM, FACT] >>
  `_ = binomial (SUC n + k) k * FACT (SUC n) * FACT k * (SUC k) +
        binomial (n + SUC k) (SUC k) * FACT n * FACT (SUC k) * (SUC n)`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC n + k) * SUC k + FACT (n + SUC k) * SUC n`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC (n+k)) * SUC k + FACT (SUC (n+k)) * SUC n`
        by metis_tac[ADD_COMM, SUC_ADD_SYM] >>
  `_ = FACT (SUC (n+k)) * (SUC k + SUC n)` by metis_tac[LEFT_ADD_DISTRIB] >>
  `_ = (SUC n + SUC k) * FACT (SUC (n+k))` by metis_tac[MULT_COMM, ADD_COMM] >>
  metis_tac[FACT]);

(* Theorem: C(n,k) = n!/k!(n-k)!  for 0 <= k <= n *)
(* Proof:
     FACT n
   = FACT ((n-k)+k)                                 by SUB_ADD, k <= n.
   = binomial ((n-k)+k) k * (FACT (n-k) * FACT k)   by binomial_formula
   = binomial n k * (FACT (n-k) * FACT k))          by SUB_ADD, k <= n.
*)
val binomial_formula2 = store_thm(
  "binomial_formula2",
  ``!n k. k <= n ==> (FACT n = binomial n k * (FACT (n-k) * FACT k))``,
  metis_tac[binomial_formula, SUB_ADD]);

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))) *)
(* Proof:
    binomial n k
  = (binomial n k * (FACT (n - k) * FACT k)) DIV ((FACT (n - k) * FACT k))  by MULT_DIV
  = (FACT n) DIV ((FACT (n - k) * FACT k))      by binomial_formula2
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by MULT_COMM
*)
val binomial_formula3 = store_thm(
  "binomial_formula3",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))))``,
  metis_tac[binomial_formula2, MULT_COMM, MULT_DIV, MULT_EQ_0, FACT_LESS, NOT_ZERO]);

(* Theorem alias. *)
val binomial_fact = save_thm("binomial_fact", binomial_formula3);
(* val binomial_fact = |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k))): thm *)

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)) *)
(* Proof:
    binomial n k
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by binomial_formula3
  = (FACT n) DIV (FACT k) DIV (FACT (n - k))    by DIV_DIV_DIV_MULT
*)
val binomial_n_k = store_thm(
  "binomial_n_k",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)))``,
  metis_tac[DIV_DIV_DIV_MULT, binomial_formula3, MULT_EQ_0, FACT_LESS, NOT_ZERO]);

(* Theorem: binomial n 1 = n *)
(* Proof:
   If n = 0,
        binomial 0 1
      = if 1 = 0 then 1 else 0                by binomial_0_n
      = 0                                     by 1 = 0 = F
   If n <> 0, then 0 < n.
      Thus 1 <= n, and n = SUC (n-1)          by 0 < n
        binomial n 1
      = FACT n DIV FACT 1 DIV FACT (n - 1)    by binomial_n_k, 1 <= n
      = FACT n DIV 1 DIV (FACT (n-1))         by FACT, ONE
      = FACT n DIV (FACT (n-1))               by DIV_1
      = (n * FACT (n-1)) DIV (FACT (n-1))     by FACT
      = n                                     by MULT_DIV, FACT_LESS
*)
val binomial_n_1 = store_thm(
  "binomial_n_1",
  ``!n. binomial n 1 = n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  `1 <= n /\ (n = SUC (n-1))` by decide_tac >>
  `binomial n 1 = FACT n DIV FACT 1 DIV FACT (n - 1)` by rw[binomial_n_k] >>
  `_ = FACT n DIV 1 DIV (FACT (n-1))` by EVAL_TAC >>
  `_ = FACT n DIV (FACT (n-1))` by rw[] >>
  `_ = (n * FACT (n-1)) DIV (FACT (n-1))` by metis_tac[FACT] >>
  `_ = n` by rw[MULT_DIV, FACT_LESS] >>
  rw[]);

(* Theorem: k <= n ==> (binomial n k = binomial n (n-k)) *)
(* Proof:
   Note (n-k) <= n always.
     binomial n k
   = (FACT n) DIV (FACT k * FACT (n - k))           by binomial_formula3, k <= n.
   = (FACT n) DIV (FACT (n - k) * FACT k)           by MULT_COMM
   = (FACT n) DIV (FACT (n - k) * FACT (n-(n-k)))   by n - (n-k) = k
   = binomial n (n-k)                               by binomial_formula3, (n-k) <= n.
*)
val binomial_sym = store_thm(
  "binomial_sym",
  ``!n k. k <= n ==> (binomial n k = binomial n (n-k))``,
  rpt strip_tac >>
  `n - (n-k) = k` by decide_tac >>
  `(n-k) <= n` by decide_tac >>
  rw[binomial_formula3, MULT_COMM]);

(* Theorem: k <= n ==> (FACT k * FACT (n-k)) divides (FACT n) *)
(* Proof:
   Since FACT n = binomial n k * (FACT (n - k) * FACT k)   by binomial_formula2
                = binomial n k * (FACT k * FACT (n - k))   by MULT_COMM
   Hence (FACT k * FACT (n-k)) divides (FACT n)            by divides_def
*)
val binomial_is_integer = store_thm(
  "binomial_is_integer",
  ``!n k. k <= n ==> (FACT k * FACT (n-k)) divides (FACT n)``,
  metis_tac[binomial_formula2, MULT_COMM, divides_def]);

(* Theorem: k <= n ==> 0 < binomial n k *)
(* Proof:
   Since  FACT n = binomial n k * (FACT (n - k) * FACT k)  by binomial_formula2
     and  0 < FACT n, 0 < FACT (n-k), 0 < FACT k           by FACT_LESS
   Hence  0 < binomial n k                                 by ZERO_LESS_MULT
*)
val binomial_pos = store_thm(
  "binomial_pos",
  ``!n k. k <= n ==> 0 < binomial n k``,
  metis_tac[binomial_formula2, FACT_LESS, ZERO_LESS_MULT]);

(* Theorem: (binomial n k = 0) <=> n < k *)
(* Proof:
   If part: (binomial n k = 0) ==> n < k
      By contradiction, suppose k <= n.
      Then 0 < binomial n k                by binomial_pos
      This contradicts binomial n k = 0    by NOT_ZERO
   Only-if part: n < k ==> (binomial n k = 0)
      This is true                         by binomial_less_0
*)
val binomial_eq_0 = store_thm(
  "binomial_eq_0",
  ``!n k. (binomial n k = 0) <=> n < k``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `k <= n` by decide_tac >>
    metis_tac[binomial_pos, NOT_ZERO],
    rw[binomial_less_0]
  ]);

(* Theorem: binomial 1 n = if 1 < n then 0 else 1 *)
(* Proof:
   If n = 0, binomial 1 0 = 1     by binomial_n_0
   If n = 1, binomial 1 1 = 1     by binomial_n_1
   Otherwise, binomial 1 n = 0    by binomial_eq_0, 1 < n
*)
Theorem binomial_1_n:
  !n. binomial 1 n = if 1 < n then 0 else 1
Proof
  rw[binomial_eq_0] >>
  `n = 0 \/ n = 1` by decide_tac >-
  simp[binomial_n_0] >>
  simp[binomial_n_1]
QED

(* Relating Binomial to its up-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial (n-1) k = (n-1, k, n-1-k) = (n-1)! / k! (n-1-k)!
                    = (n!/n) / k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / n
*)

(* Theorem: 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k) *)
(* Proof:
   If n <= k, that is n-1 < k.
      So   binomial (n-1) k = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k <= n-1
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = n * FACT (n-1)                                     by FACT
             = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))   by binomial_formula2, k <= n-1.
             = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             n * binomial (n-1) k = (n-k) * (binomial n k)        by MULT_RIGHT_CANCEL
*)
val binomial_up_eqn = store_thm(
  "binomial_up_eqn",
  ``!n. 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n-1 < k /\ (n - k = 0)` by decide_tac >>
    `binomial (n - 1) k = 0` by rw[binomial_less_0] >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k <= n-1` by decide_tac >>
    `SUC (n-1) = n` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
    `_ = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))` by rw_tac std_ss[GSYM binomial_formula2] >>
    `_ = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n *)
(* Proof:
   Since  n * binomial (n-1) k = (n-k) * (binomial n k)        by binomial_up_eqn
              binomial (n-1) k = (n-k) * (binomial n k) DIV n  by DIV_SOLVE, 0 < n.
*)
val binomial_up = store_thm(
  "binomial_up",
  ``!n. 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n``,
  rw[binomial_up_eqn, DIV_SOLVE]);

(* Relating Binomial to its right-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial n (k+1) = (n, k+1, n-k-1) = n! / (k+1)! (n-k-1)!
                    = n! / (k+1) * k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / (k+1)
*)

(* Theorem: 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k *)
(* Proof:
   If n <= k, that is n < k+1.
      So   binomial n (k+1) = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k+1 <= n
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))      by binomial_formula2, k+1 <= n.
             = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))        by SUB_PLUS, ADD_COMM
             = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))  by FACT
             = binomial n (k+1) * ((k+1) * (FACT (n-1-k) * FACT k))  by MULT_ASSOC, MULT_COMM
             = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)    by MULT_COMM, MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             (k+1) * binomial n (k+1) = (n-k) * (binomial n k)    by MULT_RIGHT_CANCEL
*)
val binomial_right_eqn = store_thm(
  "binomial_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n < k+1` by decide_tac >>
    `binomial n (k+1) = 0` by rw[binomial_less_0] >>
    `n - k = 0` by decide_tac >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k+1 <= n` by decide_tac >>
    `SUC k = k + 1` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))` by rw[binomial_formula2] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))` by metis_tac[SUB_PLUS, ADD_COMM] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))` by metis_tac[FACT] >>
    `_ = binomial n (k+1) * ((FACT (n-1-k) * (k+1)) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = binomial n (k+1) * ((k+1) * (FACT (n-1-k)) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `_ = (binomial n (k+1) * (k+1)) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1) *)
(* Proof:
   Since  (k + 1) * binomial n (k+1) = (n - k) * binomial n k  by binomial_right_eqn
          binomial n (k+1) = (n - k) * binomial n k DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val binomial_right = store_thm(
  "binomial_right",
  ``!n. 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1)``,
  rw[binomial_right_eqn, DIV_SOLVE, DECIDE ``!k. 0 < k+1``]);

(*
       k < HALF n <=> k + 1 <= n - k
n = 5, HALF n = 2, binomial 5 k: 1, 5, 10, 10, 5, 1
                              k= 0, 1,  2,  3, 4, 5
       k < 2      <=> k + 1 <= 5 - k
       k = 0              1 <= 5   binomial 5 1 >= binomial 5 0
       k = 1              2 <= 4   binomial 5 2 >= binomial 5 1
n = 6, HALF n = 3, binomial 6 k: 1, 6, 15, 20, 15, 6, 1
                              k= 0, 1, 2,  3,  4,  5, 6
       k < 3      <=> k + 1 <= 6 - k
       k = 0              1 <= 6   binomial 6 1 >= binomial 6 0
       k = 1              2 <= 5   binomial 6 2 >= binomial 6 1
       k = 2              3 <= 4   binomial 6 3 >= binomial 6 2
*)

(* Theorem: k < HALF n ==> binomial n k < binomial n (k + 1) *)
(* Proof:
   Note k < HALF n ==> 0 < n               by ZERO_DIV, 0 < 2
   also k < HALF n ==> k + 1 < n - k       by LESS_HALF_IFF
     so 0 < k + 1 /\ 0 < n - k             by arithmetic
    Now (k + 1) * binomial n (k + 1) = (n - k) * binomial n k   by binomial_right_eqn, 0 < n
   Note HALF n <= n                        by DIV_LESS_EQ, 0 < 2
     so k < HALF n <= n                    by above
   Thus 0 < binomial n k                   by binomial_pos, k <= n
    and 0 < binomial n (k + 1)             by MULT_0, MULT_EQ_0
  Hence binomial n k < binomial n (k + 1)  by MULT_EQ_LESS_TO_MORE
*)
val binomial_monotone = store_thm(
  "binomial_monotone",
  ``!n k. k < HALF n ==> binomial n k < binomial n (k + 1)``,
  rpt strip_tac >>
  `k + 1 < n - k` by rw[GSYM LESS_HALF_IFF] >>
  `0 < k + 1 /\ 0 < n - k` by decide_tac >>
  `(k + 1) * binomial n (k + 1) = (n - k) * binomial n k` by rw[binomial_right_eqn] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `0 < binomial n k` by rw[binomial_pos] >>
  `0 < binomial n (k + 1)` by metis_tac[MULT_0, MULT_EQ_0, NOT_ZERO] >>
  metis_tac[MULT_EQ_LESS_TO_MORE]);

(* Theorem: binomial n k <= binomial n (HALF n) *)
(* Proof:
   Since  (k + 1) * binomial n (k + 1) = (n - k) * binomial n k     by binomial_right_eqn
                    binomial n (k + 1) / binomial n k = (n - k) / (k + 1)
   As k varies from 0, 1,  to (n-1), n
   the ratio varies from n/1, (n-1)/2, (n-2)/3, ...., 1/n, 0/(n+1).
   The ratio is greater than 1 when      (n - k) / (k + 1) > 1
   or  n - k > k + 1
   or      n > 2 * k + 1
   or HALF n >= k + (HALF 1)
   or      k <= HALF n
   Thus (binomial n (HALF n)) is greater than all preceding coefficients.
   For k > HALF n, note that (binomial n k = binomial n (n - k))   by binomial_sym
   Hence (binomial n (HALF n)) is greater than all succeeding coefficients, too.

   If n = 0,
      binomial 0 k = 1 or 0    by binomial_0_n
      binomial 0 (HALF 0) = 1  by binomial_0_n, ZERO_DIV
      Hence true.
   If n <> 0,
      If k = HALF n, trivially true.
      If k < HALF n,
         Then binomial n k < binomial n (HALF n)           by binomial_monotone, MONOTONE_MAX
         Hence true.
      If ~(k < HALF n), HALF n < k.
         Then n - k <= HALF n                              by MORE_HALF_IMP
         If k > n,
            Then binomial n k = 0, hence true              by binomial_less_0
         If ~(k > n), then k <= n.
            Then binomial n k = binomial n (n - k)         by binomial_sym, k <= n
            If n - k = HALF n, trivially true.
            Otherwise, n - k < HALF n,
            Thus binomial n (n - k) < binomial n (HALF n)  by binomial_monotone, MONOTONE_MAX
         Hence true.
*)
val binomial_max = store_thm(
  "binomial_max",
  ``!n k. binomial n k <= binomial n (HALF n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  Cases_on `k = HALF n` >-
  rw[] >>
  Cases_on `k < HALF n` >| [
    `binomial n k < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac,
    `HALF n < k` by decide_tac >>
    `n - k <= HALF n` by rw[MORE_HALF_IMP] >>
    Cases_on `k > n` >-
    rw[binomial_less_0] >>
    `k <= n` by decide_tac >>
    `binomial n k = binomial n (n - k)` by rw[GSYM binomial_sym] >>
    Cases_on `n - k = HALF n` >-
    rw[] >>
    `n - k < HALF n` by decide_tac >>
    `binomial n (n - k) < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac
  ]);

(* Idea: the recurrence relation for binomial defines itself. *)

(* Theorem: f = binomial <=>
            !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\
                  f (n + 1) (k + 1) = f n k + f n (k + 1) *)
(* Proof:
   If part: f = binomial ==> recurrence, true  by binomial_alt
   Only-if part: recurrence ==> f = binomial
   By FUN_EQ_THM, this is to show:
      !n k. f n k = binomial n k
   By double induction, first induct on k.
   Base: !n. f n 0 = binomial n 0, true        by binomial_n_0
   Step: !n. f n k = binomial n k ==>
         !n. f n (SUC k) = binomial n (SUC k)
       By induction on n.
       Base: f 0 (SUC k) = binomial 0 (SUC k)
             This is true                      by binomial_0_n, ADD1
       Step: f n (SUC k) = binomial n (SUC k) ==>
             f (SUC n) (SUC k) = binomial (SUC n) (SUC k)

             f (SUC n) (SUC k)
           = f (n + 1) (k + 1)                 by ADD1
           = f n k + f n (k + 1)               by given
           = binomial n k + binomial n (k + 1) by induction hypothesis
           = binomial (n + 1) (k + 1)          by binomial_alt
           = binomial (SUC n) (SUC k)          by ADD1
*)
Theorem binomial_iff:
  !f. f = binomial <=>
      !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\ f (n + 1) (k + 1) = f n k + f n (k + 1)
Proof
  rw[binomial_alt, EQ_IMP_THM] >>
  simp[FUN_EQ_THM] >>
  Induct_on `x'` >-
  simp[binomial_n_0] >>
  Induct_on `x` >-
  fs[binomial_0_n, ADD1] >>
  fs[binomial_alt, ADD1]
QED

(* ------------------------------------------------------------------------- *)
(* Primes and Binomial Coefficients                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   C(n,k) = n!/k!/(n-k)!
   or n! = C(n,k) k! (n-k)!
   n divides n!, so n divides the product C(n,k) k!(n-k)!
   For a prime n, n cannot divide k!(n-k)!, all factors less than prime n.
   By Euclid's lemma, a prime divides a product must divide a factor.
   So p divides C(n,k).
*)
val prime_divides_binomials = store_thm(
  "prime_divides_binomials",
  ``!n. prime n ==> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  rpt strip_tac >-
  metis_tac[ONE_LT_PRIME] >>
  `(n = n-k + k) /\ (n-k) < n` by decide_tac >>
  `FACT n = (binomial n k) * (FACT (n-k) * FACT k)` by metis_tac[binomial_formula] >>
  `~(n divides (FACT k)) /\ ~(n divides (FACT (n-k)))` by metis_tac[PRIME_BIG_NOT_DIVIDES_FACT] >>
  `n divides (FACT n)` by metis_tac[DIVIDES_FACT, LESS_TRANS] >>
  metis_tac[P_EUCLIDES]);

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof: by prime_divides_binomials *)
val prime_divides_binomials_alt = store_thm(
  "prime_divides_binomials_alt",
  ``!n k. prime n /\ 0 < k /\ k < n ==> n divides (binomial n k)``,
  rw[prime_divides_binomials]);

(* Theorem: If prime p divides n, p does not divide (n-1)!/(n-p)! *)
(* Proof:
   By contradiction.
   (n-1)...(n-p+1)/p  cannot be an integer
   as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val prime_divisor_property = store_thm(
  "prime_divisor_property",
  ``!n p. 1 < n /\ p < n /\ prime p /\ p divides n ==>
   ~(p divides ((FACT (n-1)) DIV (FACT (n-p))))``,
  spose_not_then strip_assume_tac >>
  `1 < p` by metis_tac[ONE_LT_PRIME] >>
  `n-p < n-1` by decide_tac >>
  `(FACT (n-1)) DIV (FACT (n-p)) = PROD_SET (IMAGE SUC ((count (n-1)) DIFF (count (n-p))))`
   by metis_tac[FACT_REDUCTION, MULT_DIV, FACT_LESS] >>
  `(count (n-1)) DIFF (count (n-p)) = {x | (n-p) <= x /\ x < (n-1)}`
   by srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  `IMAGE SUC {x | (n-p) <= x /\ x < (n-1)} = {x | (n-p) < x /\ x < n}` by
  (srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  qexists_tac `x-1` >>
  decide_tac) >>
  `FINITE (count (n - 1) DIFF count (n - p))` by rw[] >>
  `?y. y IN {x| n - p < x /\ x < n} /\ p divides y` by metis_tac[PROD_SET_EUCLID, IMAGE_FINITE] >>
  `!m n y. y IN {x | m < x /\ x < n} ==> m < y /\ y < n` by rw[] >>
  `n-p < y /\ y < n` by metis_tac[] >>
  `y < n + p` by decide_tac >>
  `y = n` by metis_tac[MULTIPLE_INTERVAL] >>
  decide_tac);

(* Theorem: n divides C(n,k)  for all 0 < k < n ==> n is prime *)
(* Proof:
   By contradiction. Let p be a proper factor of n, 1 < p < n.
   Then C(n,p) = n(n-1)...(n-p+1)/p(p-1)..1
   is divisible by n/p, but not n, since
   C(n,p)/n = (n-1)...(n-p+1)/p(p-1)...1
   cannot be an integer as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val divides_binomials_imp_prime = store_thm(
  "divides_binomials_imp_prime",
  ``!n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n``,
  (spose_not_then strip_assume_tac) >>
  `?p. prime p /\ p < n /\ p divides n` by metis_tac[PRIME_FACTOR_PROPER] >>
  `n divides (binomial n p)` by metis_tac[PRIME_POS] >>
  `0 < p` by metis_tac[PRIME_POS] >>
  `(n = n-p + p) /\ (n-p) < n` by decide_tac >>
  `FACT n = (binomial n p) * (FACT (n-p) * FACT p)` by metis_tac[binomial_formula] >>
  `(n = SUC (n-1)) /\ (p = SUC (p-1))` by decide_tac >>
  `(FACT n = n * FACT (n-1)) /\ (FACT p = p * FACT (p-1))` by metis_tac[FACT] >>
  `n * FACT (n-1) = (binomial n p) * (FACT (n-p) * (p * FACT (p-1)))` by metis_tac[] >>
  `0 < n` by decide_tac >>
  `?q. binomial n p = n * q` by metis_tac[divides_def, MULT_COMM] >>
  `0 <> n` by decide_tac >>
  `FACT (n-1) = q * (FACT (n-p) * (p * FACT (p-1)))`
    by metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC] >>
  `_ = q * ((FACT (p-1) * p)* FACT (n-p))` by metis_tac[MULT_COMM] >>
  `_ = q * FACT (p-1) * p * FACT (n-p)` by metis_tac[MULT_ASSOC] >>
  `FACT (n-1) DIV FACT (n-p) = q * FACT (p-1) * p` by metis_tac[MULT_DIV, FACT_LESS] >>
  metis_tac[divides_def, prime_divisor_property]);

(* Theorem: n is prime iff n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   By prime_divides_binomials and
   divides_binomials_imp_prime.
*)
val prime_iff_divides_binomials = store_thm(
  "prime_iff_divides_binomials",
  ``!n. prime n <=> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  metis_tac[prime_divides_binomials, divides_binomials_imp_prime]);

(* Theorem: prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0) *)
(* Proof: by prime_iff_divides_binomials *)
val prime_iff_divides_binomials_alt = store_thm(
  "prime_iff_divides_binomials_alt",
  ``!n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)``,
  rw[prime_iff_divides_binomials, DIVIDES_MOD_0]);

(* ------------------------------------------------------------------------- *)
(* Binomial Theorem                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Binomial Index Shifting, for
     SUM (k=1..n) C(n,k)x^(n+1-k)y^k
   = SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
 *)
(* Proof:
SUM (k=1..n) C(n,k)x^(n+1-k)y^k
= SUM (MAP (\k. (binomial n k)* x**(n+1-k) * y**k) (GENLIST SUC n))
= SUM (GENLIST (\k. (binomial n k)* x**(n+1-k) * y**k) o SUC n)

SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
= SUM (MAP (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) (GENLIST I n))
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) o I n)
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) n)

i.e.

(\k. (binomial n k)* x**(n-k+1) * y**k) o SUC
= (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1))
*)
(* Theorem: Binomial index shift for GENLIST *)
val GENLIST_binomial_index_shift = store_thm(
  "GENLIST_binomial_index_shift",
  ``!n x y. GENLIST ((\k. binomial n k * x ** SUC(n - k) * y ** k) o SUC) n =
           GENLIST (\k. binomial n (SUC k) * x ** (n-k) * y**(SUC k)) n``,
  rw_tac std_ss[GENLIST_FUN_EQ] >>
  `SUC (n - SUC k) = n - k` by decide_tac >>
  rw_tac std_ss[]);

(* This is closely related to above, with (SUC n) replacing (n),
   but does not require k < n. *)
(* Proof: by function equality. *)
val binomial_index_shift = store_thm(
  "binomial_index_shift",
  ``!n x y. (\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC =
           (\k. binomial (SUC n) (SUC k) * x ** (n-k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM]);

(* Pattern for binomial expansion:

    (x+y)(x^3 + 3x^2y + 3xy^2 + y^3)
    = x(x^3) + 3x(x^2y) + 3x(xy^2) + x(y^3) +
                 y(x^3) + 3y(x^2y) + 3y(xy^2) + y(y^3)
    = x^4 + (3+1)x^3y + (3+3)(x^2y^2) + (1+3)(xy^3) + y^4
    = x^4 + 4x^3y     + 6x^2y^2       + 4xy^3       + y^4

*)

(* Theorem: multiply x into a binomial term *)
(* Proof: by function equality and EXP. *)
val binomial_term_merge_x = store_thm(
  "binomial_term_merge_x",
  ``!n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (SUC(n - k)) * y ** k)``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `x * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * (x * x ** (n - k)) * y ** k` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: multiply y into a binomial term *)
(* Proof: by functional equality and EXP. *)
val binomial_term_merge_y = store_thm(
  "binomial_term_merge_y",
  ``!n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (n - k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `y * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * x ** (n - k) * (y * y ** k)` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: [Binomial Theorem]  (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k  *)
(* Proof:
   By induction on n.
   Base case: to prove (x + y)^0 = SUM (k=0..0) C(0,k)x^(0-k)y^k
   (x + y)^0 = 1    by EXP
   SUM (k=0..0) C(0,k)x^(n-k)y^k = C(0,0)x^(0-0)y^0 = C(0,0) = 1  by EXP, binomial_def
   Step case: assume (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k
    to prove: (x + y)^SUC n = SUM (k=0..(SUC n)) C(SUC n,k)x^((SUC n)-k)y^k
      (x + y)^SUC n
    = (x + y)(x + y)^n      by EXP
    = (x + y) SUM (k=0..n) C(n,k)x^(n-k)y^k   by induction hypothesis
    = x (SUM (k=0..n) C(n,k)x^(n-k)y^k) +
      y (SUM (k=0..n) C(n,k)x^(n-k)y^k)       by RIGHT_ADD_DISTRIB
    = SUM (k=0..n) C(n,k)x^(n+1-k)y^k +
      SUM (k=0..n) C(n,k)x^(n-k)y^(k+1)       by moving factor into SUM
    = C(n,0)x^(n+1) + SUM (k=1..n) C(n,k)x^(n+1-k)y^k +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by breaking sum

    = C(n,0)x^(n+1) + SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1) +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by index shifting
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) [C(n,k+1) + C(n,k)] x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by merging sums
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) C(n+1,k+1) x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by binomial recurrence
    = C(n,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n,n)y^(n+1)                           by index shifting again
    = C(n+1,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n+1,n+1)y^(n+1)                       by binomial identities
    = SUM (k=0..(SUC n))C(SUC n,k) x^((SUC n)-k)y^k
                                              by synthesis of sum
*)
val binomial_thm = store_thm(
  "binomial_thm",
  ``!n x y. (x + y) ** n = SUM (GENLIST (\k. (binomial n k) * x ** (n-k) * y ** k) (SUC n))``,
  Induct_on `n` >-
  rw[EXP, binomial_n_n] >>
  rw_tac std_ss[EXP] >>
  `(x + y) * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) =
    x * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) +
    y * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))`
    by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = SUM (GENLIST ((\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n)) +
        SUM (GENLIST ((\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n))`
    by metis_tac[SUM_MULT, MAP_GENLIST] >>
  `_ = SUM (GENLIST (\k. binomial n k * x ** SUC(n - k) * y ** k) (SUC n)) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[binomial_term_merge_x, binomial_term_merge_y] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by rw[SUM_DECOMPOSE_LAST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
         SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by metis_tac[GENLIST_binomial_index_shift] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        (SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
         SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n)) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by decide_tac >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) * x ** (n - k) * y ** (SUC k) +
                           binomial n k * x ** (n - k) * y ** (SUC k))) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by metis_tac[SUM_ADD_GENLIST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) + binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[RIGHT_ADD_DISTRIB, MULT_ASSOC] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[binomial_recurrence, ADD_COMM] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_n_0, binomial_n_n] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST ((\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_index_shift] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)`
        by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC (SUC n)))`
        by rw[SUM_DECOMPOSE_LAST] >>
  decide_tac);

(* This is a milestone theorem. *)

(* Derive an alternative form. *)
val binomial_thm_alt = save_thm("binomial_thm_alt",
    binomial_thm |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_thm_alt =
   |- !n x y. (x + y) ** n =
              SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1)): thm *)

(* Theorem: SUM (GENLIST (binomial n) (SUC n)) = 2 ** n *)
(* Proof: by binomial_sum_alt and function equality. *)
(* Proof:
   Put x = 1, y = 1 in binomial_thm,
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k) (SUC n))    by EXP_1
   or    2 ** n = SUM (GENLIST (binomial n) (SUC n))          by FUN_EQ_THM
*)
Theorem binomial_sum:
  !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
Proof
  rpt strip_tac >>
  `!n. (\k. binomial n k * 1 ** (n - k) * 1 ** k) = binomial n` by rw[FUN_EQ_THM] >>
  `SUM (GENLIST (binomial n) (SUC n)) =
    SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))` by fs[] >>
  `_ = (1 + 1) ** n` by rw[GSYM binomial_thm] >>
  simp[]
QED

(* Derive an alternative form. *)
val binomial_sum_alt = save_thm("binomial_sum_alt",
    binomial_sum |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_sum_alt = |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n: thm *)

(* ------------------------------------------------------------------------- *)
(* Binomial Horizontal List                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define Horizontal List in Pascal Triangle *)
(*
val binomial_horizontal_def = Define `
  binomial_horizontal n = GENLIST (binomial n) (SUC n)
`;
*)

(* Use overloading for binomial_horizontal n. *)
val _ = overload_on("binomial_horizontal", ``\n. GENLIST (binomial n) (n + 1)``);

(* Theorem: binomial_horizontal 0 = [1] *)
(* Proof:
     binomial_horizontal 0
   = GENLIST (binomial 0) (0 + 1)    by notation
   = SNOC (binomial 0 0) []          by GENLIST, ONE
   = [binomial 0 0]                  by SNOC
   = [1]                             by binomial_n_0
*)
val binomial_horizontal_0 = store_thm(
  "binomial_horizontal_0",
  ``binomial_horizontal 0 = [1]``,
  rw[binomial_n_0]);

(* Theorem: LENGTH (binomial_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (binomial_horizontal n)
   = LENGTH (GENLIST (binomial n) (n + 1)) by notation
   = n + 1                                 by LENGTH_GENLIST
*)
val binomial_horizontal_len = store_thm(
  "binomial_horizontal_len",
  ``!n. LENGTH (binomial_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n) *)
(* Proof: by MEM_GENLIST *)
val binomial_horizontal_mem = store_thm(
  "binomial_horizontal_mem",
  ``!n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)``,
  metis_tac[MEM_GENLIST]);

(* Theorem: MEM (binomial n k) (binomial_horizontal n) <=> k <= n *)
(* Proof:
   If part: MEM (binomial n k) (binomial_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then binomial n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = binomial n m    by MEM_GENLIST
        or m <= n ==> binomial n m = 0           by m < n + 1
       Yet binomial n m <> 0                     by binomial_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> MEM (binomial n k) (binomial_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (binomial n k = binomial n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val binomial_horizontal_mem_iff = store_thm(
  "binomial_horizontal_mem_iff",
  ``!n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `binomial n k = 0` by rw[binomial_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = binomial n m)) <=> ?k. k <= n /\ (x = binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val binomial_horizontal_member = store_thm(
  "binomial_horizontal_member",
  ``!n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (binomial_horizontal n) = binomial n k) *)
(* Proof: by EL_GENLIST *)
val binomial_horizontal_element = store_thm(
  "binomial_horizontal_element",
  ``!n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)``,
  rw[EL_GENLIST]);

(* Theorem: EVERY (\x. 0 < x) (binomial_horizontal n) *)
(* Proof:
       EVERY (\x. 0 < x) (binomial_horizontal n)
   <=> EVERY (\x. 0 < x) (GENLIST (binomial n) (n + 1)) by notation
   <=> !k. k < n + 1 ==>  0 < binomial n k              by EVERY_GENLIST
   <=> !k. k <= n ==> 0 < binomial n k                  by arithmetic
   <=> T                                                by binomial_pos
*)
val binomial_horizontal_pos = store_thm(
  "binomial_horizontal_pos",
  ``!n. EVERY (\x. 0 < x) (binomial_horizontal n)``,
  rpt strip_tac >>
  `!k n. k < n + 1 <=> k <= n` by decide_tac >>
  rw_tac std_ss[EVERY_GENLIST, LESS_EQ_IFF_LESS_SUC, binomial_pos]);

(* Theorem: MEM x (binomial_horizontal n) ==> 0 < x *)
(* Proof: by binomial_horizontal_pos, EVERY_MEM *)
val binomial_horizontal_pos_alt = store_thm(
  "binomial_horizontal_pos_alt",
  ``!n x. MEM x (binomial_horizontal n) ==> 0 < x``,
  metis_tac[binomial_horizontal_pos, EVERY_MEM]);

(* Theorem: SUM (binomial_horizontal n) = 2 ** n *)
(* Proof:
     SUM (binomial_horizontal n)
   = SUM (GENLIST (binomial n) (n + 1))   by notation
   = 2 ** n                               by binomial_sum, ADD1
*)
val binomial_horizontal_sum = store_thm(
  "binomial_horizontal_sum",
  ``!n. SUM (binomial_horizontal n) = 2 ** n``,
  rw_tac std_ss[binomial_sum, GSYM ADD1]);

(* Theorem: MAX_LIST (binomial_horizontal n) = binomial n (HALF n) *)
(* Proof:
   Let l = binomial_horizontal n, m = binomial n (HALF n).
   Then l <> []                   by binomial_horizontal_len, LENGTH_NIL
    and HALF n <= n               by DIV_LESS_EQ, 0 < 2
     or HALF n < n + 1            by arithmetic
   Also MEM m l                   by binomial_horizontal_mem
    and !x. MEM x l ==> x <= m    by binomial_max, MEM_GENLIST
   Thus m = MAX_LIST l            by MAX_LIST_TEST
*)
val binomial_horizontal_max = store_thm(
  "binomial_horizontal_max",
  ``!n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `l = binomial_horizontal n` >>
  qabbrev_tac `m = binomial n (HALF n)` >>
  `l <> []` by metis_tac[binomial_horizontal_len, LENGTH_NIL, DECIDE``n + 1 <> 0``] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n < n + 1` by decide_tac >>
  `MEM m l` by rw[binomial_horizontal_mem, Abbr`l`, Abbr`m`] >>
  metis_tac[binomial_max, MEM_GENLIST, MAX_LIST_TEST]);

(* Theorem: MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n) *)
(* Proof:
   Let f = binomial n, s = IMAGE f (count (n + 1)).
   Note FINITE (count (n + 1))      by FINITE_COUNT
     so FINITE s                    by IMAGE_FINITE
   Also count (n + 1) <> {}         by COUNT_EQ_EMPTY, n + 1 <> 0
     so s <> {}                     by IMAGE_EQ_EMPTY
    Now !k. k IN (count (n + 1)) ==> f k <= f (HALF n)   by binomial_max
    ==> !x. x IN s ==> x <= f (HALF n)                   by IN_IMAGE
   Also HALF n <= n                 by DIV_LESS_EQ, 0 < 2
     so HALF n IN (count (n + 1))   by IN_COUNT
    ==> f (HALF n) IN s             by IN_IMAGE
   Thus MAX_SET s = f (HALF n)      by MAX_SET_TEST
*)
val binomial_row_max = store_thm(
  "binomial_row_max",
  ``!n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `f = binomial n` >>
  qabbrev_tac `s = IMAGE f (count (n + 1))` >>
  `FINITE s` by rw[Abbr`s`] >>
  `s <> {}` by rw[COUNT_EQ_EMPTY, Abbr`s`] >>
  `!k. k IN (count (n + 1)) ==> f k <= f (HALF n)` by rw[binomial_max, Abbr`f`] >>
  `!x. x IN s ==> x <= f (HALF n)` by metis_tac[IN_IMAGE] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n IN (count (n + 1))` by rw[] >>
  `f (HALF n) IN s` by metis_tac[IN_IMAGE] >>
  rw[MAX_SET_TEST]);

(* Theorem: k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k))) *)
(* Proof:
   Using binomial_formula2,

     (binomial m k) * (binomial n m)
         n!            m!
   = ----------- * ------------------      binomial formula
     m! (n - m)!    k! (m - k)!
        n!           m!
   = ----------- * ------------------      cancel m!
      k! m!        (m - k)! (n - m)!
        n!            (n - k)!
   = ----------- * ------------------      replace by (n - k)!
     k! (n - k)!   (m - k)! (n - m)!

   = (binomial n k) * (binomial (n - k) (m - k))   binomial formula
*)
val binomial_product_identity = store_thm(
  "binomial_product_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k)))``,
  rpt strip_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT n = binomial n m * (FACT (n - m) * FACT m)` by rw[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial m k) * (binomial n m))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO]);

(* Theorem: binomial n (HALF n) <= 4 ** (HALF n) *)
(* Proof:
   Let m = HALF n, l = binomial_horizontal n
   Note LENGTH l = n + 1               by binomial_horizontal_len
   If EVEN n,
      Then n = 2 * m                   by EVEN_HALF
       and m <= n                      by m <= 2 * m
      Note EL m l <= SUM l             by SUM_LE_EL, m < n + 1
       Now EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 4 ** m                      by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
   If ~EVEN n,
      Then ODD n                       by EVEN_ODD
       and n = 2 * m + 1               by ODD_HALF
        so m + 1 <= n                  by m + 1 <= 2 * m + 1
      with m <= n                      by m + 1 <= n
      Note EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and EL (m + 1) l = binomial n (m + 1)  by binomial_horizontal_element, m + 1 <= n
      Note binomial n (m + 1) = binomial n m  by binomial_sym
      Thus 2 * binomial n m
         = binomial n m + binomial n (m + 1)   by above
         = EL m l + EL (m + 1) l
        <= SUM l                       by SUM_LE_SUM_EL, m < m + 1, m + 1 < n + 1
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 2 * 2 ** (2 * m)            by EXP, ADD1
         = 2 * 4 ** m                  by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
*)
val binomial_middle_upper_bound = store_thm(
  "binomial_middle_upper_bound",
  ``!n. binomial n (HALF n) <= 4 ** (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `m = HALF n` >>
  qabbrev_tac `l = binomial_horizontal n` >>
  `LENGTH l = n + 1` by rw[binomial_horizontal_len, Abbr`l`] >>
  Cases_on `EVEN n` >| [
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    `m < n + 1` by decide_tac >>
    `EL m l <= SUM l` by rw[SUM_LE_EL] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `EL (m + 1) l = binomial n (m + 1)` by rw[binomial_horizontal_element, Abbr`l`] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `EL m l + EL (m + 1) l <= SUM l` by rw[SUM_LE_SUM_EL] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 2 * 2 ** (2 * m)` by metis_tac[EXP, ADD1] >>
    `_ = 2 * 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Stirling's Approximation                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stirling's formula: n! ~ sqrt(2 pi n) (n/e)^n. *)
val _ = overload_on("Stirling",
   ``(!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
     (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
     (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
     (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)``);

(* Theorem: Stirling ==>
            !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n))) *)
(* Proof:
   Note HALF n <= n                 by DIV_LESS_EQ, 0 < 2
   Let k = HALF n, then n = 2 * k   by EVEN_HALF
   Note 0 < k                       by 0 < n = 2 * k
     so (k * 2) DIV k = 2           by MULT_TO_DIV, 0 < k
     or n DIV k = 2                 by MULT_COMM
   Also 0 < pi * n                  by MULT_EQ_0, 0 < pi, 0 < n
     so 0 < 2 * pi * n              by arithmetic

   Some theorems on the fly:
   Claim: !a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j       [1]
   Proof: By induction on j.
          Base: (a ** 0) DIV (b ** 0) = (a DIV b) ** 0
                (a ** 0) DIV (b ** 0)
              = 1 DIV 1 = 1             by EXP, DIVMOD_ID, 0 < 1
              = (a DIV b) ** 0          by EXP
          Step: (a ** j) DIV (b ** j) = (a DIV b) ** j ==>
                (a ** (SUC j)) DIV (b ** (SUC j)) = (a DIV b) ** (SUC j)
                (a ** (SUC j)) DIV (b ** (SUC j))
              = (a * a ** j) DIV (b * b ** j)        by EXP
              = (a DIV b) * ((a ** j) DIV (b ** j))  by assumption
              = (a DIV b) * (a DIV b) ** j           by induction hypothesis
              = (a DIV b) ** (SUC j)                 by EXP

   Claim: !a b c. (a DIV b) * c = (a * c) DIV b      [2]
   Proof:   (a DIV b) * c
          = (a DIV b) * (c DIV 1)                    by DIV_1
          = (a * c) DIV (b * 1)                      by assumption
          = (a * c) DIV b                            by MULT_RIGHT_1

   Claim: !a b. a DIV b = 2 * (a DIV (2 * b))        [3]
   Proof:   a DIV b
          = 1 * (a DIV b)                            by MULT_LEFT_1
          = (n DIV n) * (a DIV b)                    by DIVMOD_ID, 0 < n
          = (n * a) DIV (n * b)                      by assumption
          = (n * a) DIV (k * (2 * b))                by arithmetic, n = 2 * k
          = (n DIV k) * (a DIV (2 * b))              by assumption
          = 2 * (a DIV (2 * b))                      by n DIV k = 2

   Claim: !a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))    [4]
   Proof: Let c = b ** h.
          Then b = c * c               by EXP_EXP_MULT
            so 0 < c                   by MULT_EQ_0, 0 < b
              a * (c DIV b)
            = (c DIV b) * a            by MULT_COMM
            = (a * c) DIV b            by [2]
            = (a * c) DIV (c * c)      by b = c * c
            = (a DIV c) * (c DIV c)    by assumption
            = a DIV c                  by DIVMOD_ID, c DIV c = 1, 0 < c

   Note  (FACT k) ** 2
       = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2    by EXP_BASE_MULT
       = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n           by EXP_EXP_MULT, n = 2 * k
       = (SQRT (pi * n)) ** 2 * (k DIV e) ** n               by MULT_ASSOC, 2 * k = n
       = ((pi * n) ** h) ** 2 * (k DIV e) ** n               by assumption
       = (pi * n) * (k DIV e) ** n                           by EXP_EXP_MULT, h * 2 = 1

     binomial n (HALF n)
   = binomial n k                             by k = HALF n
   = FACT n DIV (FACT k * FACT (n - k))       by binomial_formula3, k <= n
   = FACT n DIV (FACT k * FACT k)             by arithmetic, n - k = 2 * k - k = k
   = FACT n DIV ((FACT k) ** 2)               by EXP_2
   = FACT n DIV ((pi * n) * (k DIV e) ** n)   by above
   = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)        by assumption
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))    by (a * b) DIV (x * y) = (a DIV x) * (b DIV y)
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n           by (a ** n) DIV (b ** n) = (a DIV b) ** n)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n   by MULT_ASSOC, a DIV b = 2 * a DIV (2 * b)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n                   by assumption, apply DIV_DIV_DIV_MULT
   = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n                                    by 2 * x ** h DIV x = 2 DIV (x ** h)
   = 2 DIV (2 * pi * n) ** h * 2 ** n                                            by n DIV k = 2
   = 2 * 2 ** n DIV (2 * pi * n) ** h                                            by (a DIV b) * c = a * c DIV b
   = 2 ** (SUC n) DIV (2 * pi * n) ** h                                          by EXP
   = 2 ** (n + 1)) DIV (SQRT (2 * pi * n))                                       by ADD1, assumption
*)
val binomial_middle_by_stirling = store_thm(
  "binomial_middle_by_stirling",
  ``Stirling ==> !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n)))``,
  rpt strip_tac >>
  `HALF n <= n /\ (n = 2 * HALF n)` by rw[DIV_LESS_EQ, EVEN_HALF] >>
  qabbrev_tac `k = HALF n` >>
  `0 < k` by decide_tac >>
  `n DIV k = 2` by metis_tac[MULT_TO_DIV, MULT_COMM] >>
  `0 < pi * n` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `0 < 2 * pi * n` by decide_tac >>
  `(FACT k) ** 2 = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2` by rw[EXP_BASE_MULT] >>
  `_ = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  `_ = (pi * n) * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  (`!a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j` by (Induct_on `j` >> rw[EXP])) >>
  `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
  `!a b. a DIV b = 2 * (a DIV (2 * b))` by metis_tac[DIVMOD_ID, MULT_LEFT_1] >>
  `!a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))` by
  (rpt strip_tac >>
  qabbrev_tac `c = b ** h` >>
  `b = c * c` by rw[GSYM EXP_EXP_MULT, Abbr`c`] >>
  `0 < c` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `a * (c DIV b) = (a * c) DIV (c * c)` by metis_tac[MULT_COMM] >>
  `_ = (a DIV c) * (c DIV c)` by metis_tac[] >>
  metis_tac[DIVMOD_ID, MULT_RIGHT_1]) >>
  `binomial n k = (FACT n) DIV (FACT k * FACT (n - k))` by metis_tac[binomial_formula3] >>
  `_ = (FACT n) DIV (FACT k) ** 2` by metis_tac[EXP_2, DECIDE``2 * k - k = k``] >>
  `_ = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)` by prove_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))` by metis_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[MULT_ASSOC] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * 2 ** n` by metis_tac[] >>
  `_ = (2 * 2 ** n DIV (2 * pi * n) ** h)` by metis_tac[] >>
  metis_tac[EXP, ADD1]);

(* ------------------------------------------------------------------------- *)
(* Useful theorems for Binomial                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k MOD n = 0) <=>
            !h. 0 <= h /\ h < PRE n ==> (binomial n (SUC h) MOD n = 0) *)
(* Proof: by h = PRE k, or k = SUC h.
   If part: put k = SUC h,
      then 0 < SUC h ==>  0 <= h,
       and SUC h < n ==> PRE (SUC h) = h < PRE n  by prim_recTheory.PRE
   Only-if part: put h = PRE k,
      then 0 <= PRE k ==> 0 < k
       and PRE k < PRE n ==> k < n                by INV_PRE_LESS
*)
val binomial_range_shift = store_thm(
  "binomial_range_shift",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                   (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: binomial n k MOD n = 0 <=> (binomial n k * x ** (n-k) * y ** k) MOD n = 0 *)
(* Proof:
       (binomial n k * x ** (n-k) * y ** k) MOD n = 0
   <=> (binomial n k * (x ** (n-k) * y ** k)) MOD n = 0    by MULT_ASSOC
   <=> (((binomial n k) MOD n) * ((x ** (n - k) * y ** k) MOD n)) MOD n = 0  by MOD_TIMES2
   If part, apply 0 * z = 0  by MULT.
   Only-if part, pick x = 1, y = 1, apply EXP_1.
*)
val binomial_mod_zero = store_thm(
  "binomial_mod_zero",
  ``!n. 0 < n ==> !k. (binomial n k MOD n = 0) <=> (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[MOD_TIMES2, ZERO_MOD, MULT] >>
  metis_tac[EXP_1, MULT_RIGHT_1]);


(* Theorem: (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))) *)
(* Proof: by h = PRE k, or k = SUC h. *)
val binomial_range_shift_alt = store_thm(
  "binomial_range_shift_alt",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
                   (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0 <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0 *)
(* Proof:
       !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0
   <=> !k. 0 < k /\ k < n ==> !x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)   by binomial_mod_zero
   <=> !h. h < PRE n ==> !x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)  by binomial_range_shift_alt
   <=> !x y. EVERY (\z. z = 0) (GENLIST (\k. (binomial n (SUC k) * x ** (n - (SUC k)) * y ** (SUC k)) MOD n) (PRE n)) by EVERY_GENLIST
   <=> !x y. EVERY (\x. x = 0) (GENLIST ((\k. binomial n k * x ** (n - k) * y ** k) o SUC) (PRE n)  by FUN_EQ_THM
   <=> !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0   by SUM_EQ_0
*)
val binomial_mod_zero_alt = store_thm(
  "binomial_mod_zero_alt",
  ``!n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                  !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)``,
  rpt strip_tac >>
  `!x y. (\k. (binomial n (SUC k) * x ** (n - SUC k) * y ** (SUC k)) MOD n) = (\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC` by rw_tac std_ss[FUN_EQ_THM] >>
  `(!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
    (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)))` by rw_tac std_ss[binomial_mod_zero] >>
  `_ = (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)))` by rw_tac std_ss[binomial_range_shift_alt] >>
  `_ = !x y h. h < PRE n ==> (((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))` by metis_tac[] >>
  rw_tac std_ss[EVERY_GENLIST, SUM_EQ_0]);

(* ------------------------------------------------------------------------- *)
(* Binomial Theorem with prime exponent                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Binomial Expansion for prime exponent]  (x + y)^p = x^p + y^p (mod p) *)
(* Proof:
     (x+y)^p  (mod p)
   = SUM (k=0..p) C(p,k)x^(p-k)y^k  (mod p)                                     by binomial theorem
   = (C(p,0)x^py^0 + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + C(p,p)x^0y^p) (mod p)  by breaking sum
   = (x^p + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + y^k) (mod p)                    by binomial_n_0, binomial_n_n
   = ((x^p mod p) + (SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k) (mod p) + (y^p mod p)) mod p   by MOD_PLUS
   = ((x^p mod p) + (SUM (k=1..(p-1)) (C(p,k)x^(p-k)y^k) (mod p)) + (y^p mod p)) mod p
   = (x^p mod p  + 0 + y^p mod p) mod p                                         by prime_iff_divides_binomials
   = (x^p + y^p) (mod p)                                                        by MOD_PLUS
*)
val binomial_thm_prime = store_thm(
  "binomial_thm_prime",
  ``!p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `!k. 0 < k /\ k < p ==> ((binomial p k) MOD p  = 0)` by metis_tac[prime_iff_divides_binomials, DIVIDES_MOD_0] >>
  `SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) MOD p = 0` by metis_tac[SUM_GENLIST_MOD, binomial_mod_zero_alt, ZERO_MOD] >>
  `(x + y) ** p MOD p = (x ** p + SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) + y ** p) MOD p` by rw_tac std_ss[binomial_thm, SUM_DECOMPOSE_FIRST_LAST, binomial_n_0, binomial_n_n, EXP] >>
  metis_tac[MOD_PLUS3, ADD_0, MOD_PLUS]);

(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Type: (# are temp)
   triple                = <| a: num; b: num; c: num |>
#  path                  = :num list
   Overloading:
   leibniz_vertical n    = [1 .. (n+1)]
   leibniz_up       n    = REVERSE (leibniz_vertical n)
   leibniz_horizontal n  = GENLIST (leibniz n) (n + 1)
   binomial_horizontal n = GENLIST (binomial n) (n + 1)
#  ta                    = (triplet n k).a
#  tb                    = (triplet n k).b
#  tc                    = (triplet n k).c
   p1 zigzag p2          = leibniz_zigzag p1 p2
   p1 wriggle p2         = RTC leibniz_zigzag p1 p2
   leibniz_col_arm a b n = MAP (\x. leibniz (a - x) b) [0 ..< n]
   leibniz_seg_arm a b n = MAP (\x. leibniz a (b + x)) [0 ..< n]

   leibniz_seg n k h     = IMAGE (\j. leibniz n (k + j)) (count h)
   leibniz_row n h       = IMAGE (leibniz n) (count h)
   leibniz_col h         = IMAGE (\i. leibniz i 0) (count h)
   lcm_run n             = list_lcm [1 .. n]
#  beta n k              = k * binomial n k
#  beta_horizontal n     = GENLIST (beta n o SUC) n
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   RTC_TRANS          |- R^* x y /\ R^* y z ==> R^* x z

   Leibniz Triangle (Denominator form):
#  leibniz_def        |- !n k. leibniz n k = (n + 1) * binomial n k
   leibniz_0_n        |- !n. leibniz 0 n = if n = 0 then 1 else 0
   leibniz_n_0        |- !n. leibniz n 0 = n + 1
   leibniz_n_n        |- !n. leibniz n n = n + 1
   leibniz_less_0     |- !n k. n < k ==> (leibniz n k = 0)
   leibniz_sym        |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
   leibniz_monotone   |- !n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)
   leibniz_pos        |- !n k. k <= n ==> 0 < leibniz n k
   leibniz_eq_0       |- !n k. (leibniz n k = 0) <=> n < k
   leibniz_alt        |- !n. leibniz n = (\j. (n + 1) * j) o binomial n
   leibniz_def_alt    |- !n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)
   leibniz_up_eqn     |- !n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k
   leibniz_up         |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)
   leibniz_up_alt     |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
   leibniz_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * leibniz n (k + 1) = (n - k) * leibniz n k
   leibniz_right      |- !n. 0 < n ==> !k. leibniz n (k + 1) = (n - k) * leibniz n k DIV (k + 1)
   leibniz_property   |- !n. 0 < n ==> !k. leibniz n k * leibniz (n - 1) k =
                                           leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   leibniz_formula    |- !n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))
   leibniz_recurrence |- !n. 0 < n ==> !k. k < n ==> (leibniz n (k + 1) = leibniz n k *
                                           leibniz (n - 1) k DIV (leibniz n k - leibniz (n - 1) k))
   leibniz_n_k        |- !n k. 0 < k /\ k <= n ==> (leibniz n k =
                                           leibniz n (k - 1) * leibniz (n - 1) (k - 1)
                                           DIV (leibniz n (k - 1) - leibniz (n - 1) (k - 1)))
   leibniz_lcm_exchange  |- !n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n - 1) k) =
                                              lcm (leibniz n k) (leibniz n (k + 1))
   leibniz_middle_lower  |- !n. 4 ** n <= leibniz (TWICE n) n

   LCM of a list of numbers:
#  list_lcm_def          |- (list_lcm [] = 1) /\ !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_nil          |- list_lcm [] = 1
   list_lcm_cons         |- !h t. list_lcm (h::t) = lcm h (list_lcm t)
   list_lcm_sing         |- !x. list_lcm [x] = x
   list_lcm_snoc         |- !x l. list_lcm (SNOC x l) = lcm x (list_lcm l)
   list_lcm_map_times    |- !n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l
   list_lcm_pos          |- !l. EVERY_POSITIVE l ==> 0 < list_lcm l
   list_lcm_pos_alt      |- !l. POSITIVE l ==> 0 < list_lcm l
   list_lcm_lower_bound  |- !l. EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_lower_bound_alt          |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l
   list_lcm_is_common_multiple       |- !x l. MEM x l ==> x divides (list_lcm l)
   list_lcm_is_least_common_multiple |- !l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m
   list_lcm_append       |- !l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)
   list_lcm_append_3     |- !l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]
   list_lcm_reverse      |- !l. list_lcm (REVERSE l) = list_lcm l
   list_lcm_suc          |- !n. list_lcm [1 .. n + 1] = lcm (n + 1) (list_lcm [1 .. n])
   list_lcm_nonempty_lower      |- !l. l <> [] /\ EVERY_POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_nonempty_lower_alt  |- !l. l <> [] /\ POSITIVE l ==> SUM l DIV LENGTH l <= list_lcm l
   list_lcm_divisor_lcm_pair    |- !l x y. MEM x l /\ MEM y l ==> lcm x y divides list_lcm l
   list_lcm_lower_by_lcm_pair   |- !l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> lcm x y <= list_lcm l
   list_lcm_upper_by_common_multiple
                                |- !l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m
   list_lcm_by_FOLDR     |- !ls. list_lcm ls = FOLDR lcm 1 ls
   list_lcm_by_FOLDL     |- !ls. list_lcm ls = FOLDL lcm 1 ls

   Lists in Leibniz Triangle:

   Veritcal Lists in Leibniz Triangle
   leibniz_vertical_alt      |- !n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)
   leibniz_vertical_0        |- leibniz_vertical 0 = [1]
   leibniz_vertical_len      |- !n. LENGTH (leibniz_vertical n) = n + 1
   leibniz_vertical_not_nil  |- !n. leibniz_vertical n <> []
   leibniz_vertical_pos      |- !n. EVERY_POSITIVE (leibniz_vertical n)
   leibniz_vertical_pos_alt  |- !n. POSITIVE (leibniz_vertical n)
   leibniz_vertical_mem      |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_vertical n)
   leibniz_vertical_snoc     |- !n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)

   leibniz_up_0              |- leibniz_up 0 = [1]
   leibniz_up_len            |- !n. LENGTH (leibniz_up n) = n + 1
   leibniz_up_pos            |- !n. EVERY_POSITIVE (leibniz_up n)
   leibniz_up_mem            |- !n x. 0 < x /\ x <= n + 1 <=> MEM x (leibniz_up n)
   leibniz_up_cons           |- !n. leibniz_up (n + 1) = n + 2::leibniz_up n

   leibniz_horizontal_0      |- leibniz_horizontal 0 = [1]
   leibniz_horizontal_len    |- !n. LENGTH (leibniz_horizontal n) = n + 1
   leibniz_horizontal_el     |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_mem    |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
   leibniz_horizontal_mem_iff   |- !n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n
   leibniz_horizontal_member    |- !n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)
   leibniz_horizontal_element   |- !n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)
   leibniz_horizontal_head   |- !n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]
   leibniz_horizontal_divisor|- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_horizontal n)
   leibniz_horizontal_pos    |- !n. EVERY_POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_pos_alt|- !n. POSITIVE (leibniz_horizontal n)
   leibniz_horizontal_alt    |- !n. leibniz_horizontal n = MAP (\j. (n + 1) * j) (binomial_horizontal n)
   leibniz_horizontal_lcm_alt|- !n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)
   leibniz_horizontal_sum          |- !n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)
   leibniz_horizontal_sum_eqn      |- !n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n:
   leibniz_horizontal_average      |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) =
                                          SUM (binomial_horizontal n)
   leibniz_horizontal_average_eqn  |- !n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n

   Using Triplet and Paths:
   triplet_def               |- !n k. triplet n k =
                                           <|a := leibniz n k;
                                             b := leibniz (n + 1) k;
                                             c := leibniz (n + 1) (k + 1)
                                            |>
   leibniz_triplet_member    |- !n k. (ta = leibniz n k) /\
                                      (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))
   leibniz_right_entry       |- !n k. (k + 1) * tc = (n + 1 - k) * tb
   leibniz_up_entry          |- !n k. (n + 2) * ta = (n + 1 - k) * tb
   leibniz_triplet_property  |- !n k. ta * tb = tc * (tb - ta)
   leibniz_triplet_lcm       |- !n k. lcm tb ta = lcm tb tc

   Zigzag Path in Leibniz Triangle:
   leibniz_zigzag_def        |- !p1 p2. p1 zigzag p2 <=>
                                ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
   list_lcm_zigzag           |- !p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_tail       |- !p1 p2. p1 zigzag p2 ==> !x. [x] ++ p1 zigzag [x] ++ p2
   leibniz_horizontal_zigzag |- !n k. k <= n ==>
                                TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                                TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
   leibniz_triplet_0         |- leibniz_up 1 zigzag leibniz_horizontal 1

   Wriggle Paths in Leibniz Triangle:
   list_lcm_wriggle         |- !p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)
   leibniz_zigzag_wriggle   |- !p1 p2. p1 zigzag p2 ==> p1 wriggle p2
   leibniz_wriggle_tail     |- !p1 p2. p1 wriggle p2 ==> !x. [x] ++ p1 wriggle [x] ++ p2
   leibniz_wriggle_refl     |- !p1. p1 wriggle p1
   leibniz_wriggle_trans    |- !p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3
   leibniz_horizontal_wriggle_step  |- !n k. k <= n + 1 ==>
      TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)
   leibniz_horizontal_wriggle |- !n. [leibniz (n + 1) 0] ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1)

   Path Transform keeping LCM:
   leibniz_up_wriggle_horizontal  |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_lcm_property           |- !n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)
   leibniz_vertical_divisor       |- !n k. k <= n ==> leibniz n k divides list_lcm (leibniz_vertical n)

   Lower Bound of Leibniz LCM:
   leibniz_horizontal_lcm_lower  |- !n. 2 ** n <= list_lcm (leibniz_horizontal n)
   leibniz_vertical_lcm_lower    |- !n. 2 ** n <= list_lcm (leibniz_vertical n)
   lcm_lower_bound               |- !n. 2 ** n <= list_lcm [1 .. (n + 1)]

   Leibniz LCM Invariance:
   leibniz_col_arm_0    |- !a b. leibniz_col_arm a b 0 = []
   leibniz_seg_arm_0    |- !a b. leibniz_seg_arm a b 0 = []
   leibniz_col_arm_1    |- !a b. leibniz_col_arm a b 1 = [leibniz a b]
   leibniz_seg_arm_1    |- !a b. leibniz_seg_arm a b 1 = [leibniz a b]
   leibniz_col_arm_len  |- !a b n. LENGTH (leibniz_col_arm a b n) = n
   leibniz_seg_arm_len  |- !a b n. LENGTH (leibniz_seg_arm a b n) = n
   leibniz_col_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b
   leibniz_seg_arm_el   |- !n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)
   leibniz_seg_arm_head |- !a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]
   leibniz_col_arm_cons |- !a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b::leibniz_col_arm a b n

   leibniz_seg_arm_zigzag_step       |- !n k. k < n ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
                   TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
   leibniz_seg_arm_wriggle_step      |- !n k. k < n + 1 ==> !a b.
                   TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_seg_arm_wriggle_row_arm   |- !a b n. [leibniz (a + 1) b] ++ leibniz_seg_arm a b n wriggle
                                                leibniz_seg_arm (a + 1) b (n + 1)
   leibniz_col_arm_wriggle_row_arm   |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                                leibniz_col_arm a b n wriggle leibniz_seg_arm a b n
   leibniz_lcm_invariance            |- !a b n. b <= a /\ n <= a + 1 - b ==>
                                        (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))
   leibniz_col_arm_n_0               |- !n. leibniz_col_arm n 0 (n + 1) = leibniz_up n
   leibniz_seg_arm_n_0               |- !n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n
   leibniz_up_wriggle_horizontal_alt |- !n. leibniz_up n wriggle leibniz_horizontal n
   leibniz_up_lcm_eq_horizontal_lcm  |- !n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)

   Set GCD as Big Operator:
   big_gcd_def                |- !s. big_gcd s = ITSET gcd s 0
   big_gcd_empty              |- big_gcd {} = 0
   big_gcd_sing               |- !x. big_gcd {x} = x
   big_gcd_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))
   big_gcd_is_common_divisor  |- !s. FINITE s ==> !x. x IN s ==> big_gcd s divides x
   big_gcd_is_greatest_common_divisor
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s
   big_gcd_insert             |- !s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)
   big_gcd_two                |- !x y. big_gcd {x; y} = gcd x y
   big_gcd_positive           |- !s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s
   big_gcd_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s

   Set LCM as Big Operator:
   big_lcm_def                |- !s. big_lcm s = ITSET lcm s 1
   big_lcm_empty              |- big_lcm {} = 1
   big_lcm_sing               |- !x. big_lcm {x} = x
   big_lcm_reduction          |- !s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))
   big_lcm_is_common_multiple |- !s. FINITE s ==> !x. x IN s ==> x divides big_lcm s
   big_lcm_is_least_common_multiple
                              |- !s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m
   big_lcm_insert             |- !s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)
   big_lcm_two                |- !x y. big_lcm {x; y} = lcm x y
   big_lcm_positive           |- !s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s
   big_lcm_map_times          |- !s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s

   LCM Lower bound using big LCM:
   leibniz_seg_def            |- !n k h. leibniz_seg n k h = {leibniz n (k + j) | j IN count h}
   leibniz_row_def            |- !n h. leibniz_row n h = {leibniz n j | j IN count h}
   leibniz_col_def            |- !h. leibniz_col h = {leibniz j 0 | j IN count h}
   leibniz_col_eq_natural     |- !n. leibniz_col n = natural n
   big_lcm_seg_transform      |- !n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
                                         big_lcm (leibniz_seg (n + 1) k (h + 1))
   big_lcm_row_transform      |- !n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) =
                                       big_lcm (leibniz_row (n + 1) (h + 1))
   big_lcm_corner_transform   |- !n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))
   big_lcm_count_lower_bound  |- !f n. (!x. x IN count (n + 1) ==> 0 < f x) ==>
                                       SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))
   big_lcm_natural_eqn        |- !n. big_lcm (natural (n + 1)) =
                                     (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))
   big_lcm_lower_bound        |- !n. 2 ** n <= big_lcm (natural (n + 1))
   big_lcm_eq_list_lcm        |- !l. big_lcm (set l) = list_lcm l

   List LCM depends only on its set of elements:
   list_lcm_absorption        |- !x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)
   list_lcm_nub               |- !l. list_lcm (nub l) = list_lcm l
   list_lcm_nub_eq_if_set_eq  |- !l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))
   list_lcm_eq_if_set_eq      |- !l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)

   Set LCM by List LCM:
   set_lcm_def                |- !s. set_lcm s = list_lcm (SET_TO_LIST s)
   set_lcm_empty              |- set_lcm {} = 1
   set_lcm_nonempty           |- !s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))
   set_lcm_sing               |- !x. set_lcm {x} = x
   set_lcm_eq_list_lcm        |- !l. set_lcm (set l) = list_lcm l
   set_lcm_eq_big_lcm         |- !s. FINITE s ==> (set_lcm s = big_lcm s)
   set_lcm_insert             |- !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)
   set_lcm_is_common_multiple        |- !x s. FINITE s /\ x IN s ==> x divides set_lcm s
   set_lcm_is_least_common_multiple  |- !s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m
   pairwise_coprime_prod_set_eq_set_lcm
                             |- !s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)
   pairwise_coprime_prod_set_divides
                             |- !s m. FINITE s /\ PAIRWISE_COPRIME s /\
                                      (!x. x IN s ==> x divides m) ==> PROD_SET s divides m

   Nair's Trick (direct):
   lcm_run_by_FOLDL          |- !n. lcm_run n = FOLDL lcm 1 [1 .. n]
   lcm_run_by_FOLDR          |- !n. lcm_run n = FOLDR lcm 1 [1 .. n]
   lcm_run_0                 |- lcm_run 0 = 1
   lcm_run_1                 |- lcm_run 1 = 1
   lcm_run_suc               |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n)
   lcm_run_pos               |- !n. 0 < lcm_run n
   lcm_run_small             |- (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\
                                (lcm_run 5 = 60) /\ (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\
                                (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)
   lcm_run_divisors          |- !n. n + 1 divides lcm_run (n + 1) /\ lcm_run n divides lcm_run (n + 1)
   lcm_run_monotone          |- !n. lcm_run n <= lcm_run (n + 1)
   lcm_run_lower             |- !n. 2 ** n <= lcm_run (n + 1)
   lcm_run_leibniz_divisor   |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_even        |- !n. n * 4 ** n <= lcm_run (TWICE (n + 1))

   lcm_run_odd_lower         |- !n. ODD n ==> HALF n * HALF (2 ** n) <= lcm_run n
   lcm_run_even_lower        |- !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
   lcm_run_odd_lower_alt     |- !n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n
   lcm_run_even_lower_alt    |- !n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n
   lcm_run_lower_better      |- !n. 7 <= n ==> 2 ** n <= lcm_run n

   Nair's Trick (rework):
   lcm_run_odd_factor        |- !n. 0 < n ==> n * leibniz (TWICE n) n divides lcm_run (TWICE n + 1)
   lcm_run_lower_odd         |- !n. n * 4 ** n <= lcm_run (TWICE n + 1)
   lcm_run_lower_odd_iff     |- !n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)
   lcm_run_lower_even_iff    |- !n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)
   lcm_run_lower_better_iff  |- !n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n

   Nair's Trick (consecutive):
   lcm_upto_def              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_0                |- lcm_upto 0 = 1
   lcm_upto_SUC              |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n)
   lcm_upto_alt              |- (lcm_upto 0 = 1) /\ !n. lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)
   lcm_upto_1                |- lcm_upto 1 = 1
   lcm_upto_small            |- (lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
                                (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
                                (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)
   lcm_upto_eq_list_lcm      |- !n. lcm_upto n = list_lcm [1 .. n]
   lcm_upto_lower            |- !n. 2 ** n <= lcm_upto (n + 1)
   lcm_upto_divisors         |- !n. n + 1 divides lcm_upto (n + 1) /\ lcm_upto n divides lcm_upto (n + 1)
   lcm_upto_monotone         |- !n. lcm_upto n <= lcm_upto (n + 1)
   lcm_upto_leibniz_divisor  |- !n k. k <= n ==> leibniz n k divides lcm_upto (n + 1)
   lcm_upto_lower_odd        |- !n. n * 4 ** n <= lcm_upto (TWICE n + 1)
   lcm_upto_lower_even       |- !n. n * 4 ** n <= lcm_upto (TWICE (n + 1))
   lcm_upto_lower_better     |- !n. 7 <= n ==> 2 ** n <= lcm_upto n

   Simple LCM lower bounds:
   lcm_run_lower_simple      |- !n. HALF (n + 1) <= lcm_run n
   lcm_run_alt               |- !n. lcm_run n = lcm_run (n - 1 + 1)
   lcm_run_lower_good        |- !n. 2 ** (n - 1) <= lcm_run n

   Upper Bound by Leibniz Triangle:
   leibniz_eqn               |- !n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k
   leibniz_right_alt         |- !n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)
   leibniz_binomial_identity         |- !m n k. k <= m /\ m <= n ==>
                   (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
   leibniz_divides_leibniz_factor    |- !m n k. k <= m /\ m <= n ==>
                                         leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
   leibniz_horizontal_member_divides |- !m n x. n <= TWICE m + 1 /\ m <= n /\
                                                MEM x (leibniz_horizontal n) ==>
                               x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
   lcm_run_divides_property  |- !m n. n <= TWICE m /\ m <= n ==>
                                      lcm_run n divides lcm_run m * binomial n m
   lcm_run_bound_recurrence  |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
   lcm_run_upper_bound       |- !n. lcm_run n <= 4 ** n

   Beta Triangle:
   beta_0_n        |- !n. beta 0 n = 0
   beta_n_0        |- !n. beta n 0 = 0
   beta_less_0     |- !n k. n < k ==> (beta n k = 0)
   beta_eqn        |- !n k. beta (n + 1) (k + 1) = leibniz n k
   beta_alt        |- !n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))
   beta_pos        |- !n k. 0 < k /\ k <= n ==> 0 < beta n k
   beta_eq_0       |- !n k. (beta n k = 0) <=> (k = 0) \/ n < k
   beta_sym        |- !n k. k <= n ==> (beta n k = beta n (n - k + 1))

   Beta Horizontal List:
   beta_horizontal_0            |- beta_horizontal 0 = []
   beta_horizontal_len          |- !n. LENGTH (beta_horizontal n) = n
   beta_horizontal_eqn          |- !n. beta_horizontal (n + 1) = leibniz_horizontal n
   beta_horizontal_alt          |- !n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))
   beta_horizontal_mem          |- !n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)
   beta_horizontal_mem_iff      |- !n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n
   beta_horizontal_member       |- !n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   beta_horizontal_element      |- !n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))
   lcm_run_by_beta_horizontal   |- !n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))
   lcm_run_beta_divisor         |- !n k. 0 < k /\ k <= n ==> beta n k divides lcm_run n
   beta_divides_beta_factor     |- !m n k. k <= m /\ m <= n ==> beta n k divides beta m k * binomial n m
   lcm_run_divides_property_alt |- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
   lcm_run_upper_bound          |- !n. lcm_run n <= 4 ** n

   LCM Lower Bound using Maximum:
   list_lcm_ge_max               |- !l. POSITIVE l ==> MAX_LIST l <= list_lcm l
   lcm_lower_bound_by_list_lcm   |- !n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]
   big_lcm_ge_max                |- !s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s
   lcm_lower_bound_by_big_lcm    |- !n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))

   Consecutive LCM function:
   lcm_lower_bound_by_list_lcm_stirling  |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= list_lcm [1 .. n]
   big_lcm_non_decreasing                |- !n. big_lcm (natural n) <= big_lcm (natural (n + 1))
   lcm_lower_bound_by_big_lcm_stirling   |- Stirling /\ (!n c. n DIV SQRT (c * (n - 1)) = SQRT (n DIV c)) ==>
                                            !n. ODD n ==> SQRT (n DIV (2 * pi)) * 2 ** n <= big_lcm (natural n)

   Extra Theorems:
   gcd_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (gcd (p * m) n = m)
   lcm_prime_product_property   |- !p m n. prime p /\ m divides n /\ ~(p * m divides n) ==> (lcm (p * m) n = p * n)
   list_lcm_prime_factor        |- !p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)
   list_lcm_prime_factor_member |- !p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x

*)

(* ------------------------------------------------------------------------- *)
(* Leibniz Harmonic Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(*

Leibniz Harmonic Triangle (fraction form)

       c <= r
r = 1  1
r = 2  1/2  1/2
r = 3  1/3  1/6   1/3
r = 4  1/4  1/12  1/12  1/4
r = 5  1/5  1/10  1/20  1/10  1/5

In general,  L(r,1) = 1/r,  L(r,c) = |L(r-1,c-1) - L(r,c-1)|

Solving, L(r,c) = 1/(r C(r-1,c-1)) = 1/(c C(r,c))
where C(n,m) is the binomial coefficient of Pascal Triangle.

c = 1 are the 1/(1 * natural numbers
c = 2 are the 1/(2 * triangular numbers)
c = 3 are the 1/(3 * tetrahedral numbers)

Sum of denominators of n-th row = n 2**(n-1).

Note that  L(r,c) = Integral(0,1) x ** (c-1) * (1-x) ** (r-c) dx

Another form:  L(n,1) = 1/n, L(n,k) = L(n-1,k-1) - L(n,k-1)
Solving,  L(n,k) = 1/ k C(n,k) = 1/ n C(n-1,k-1)

Still another notation  H(n,r) = 1/ (n+1)C(n,r) = (n-r)!r!/(n+1)!  for 0 <= r <= n

Harmonic Denominator Number Triangle (integer form)
g(d,n) = 1/H(d,n)     where H(d,h) is the Leibniz Harmonic Triangle
g(d,n) = (n+d)C(d,n)  where C(d,h) is the Pascal's Triangle.
g(d,n) = n(n+1)...(n+d)/d!

(k+1)-th row of Pascal's triangle:  x^4 + 4x^3 + 6x^2 + 4x + 1
Perform differentiation, d/dx -> 4x^3 + 12x^2 + 12x + 4
which is k-th row of Harmonic Denominator Number Triangle.

(k+1)-th row of Pascal's triangle: (x+1)^(k+1)
k-th row of Harmonic Denominator Number Triangle: d/dx[(x+1)^(k+1)]

  d/dx[(x+1)^(k+1)]
= d/dx[SUM C(k+1,j) x^j]    j = 0...(k+1)
= SUM C(k+1,j) d/dx[x^j]
= SUM C(k+1,j) j x^(j-1)    j = 1...(k+1)
= SUM C(k+1,j+1) (j+1) x^j  j = 0...k
= SUM D(k,j) x^j            with D(k,j) = (j+1) C(k+1,j+1)  ???

*)

(* Another presentation of triangles:

The harmonic triangle of Leibniz
    1/1   1/2   1/3   1/4    1/5   .... harmonic fractions
       1/2   1/6   1/12   1/20     .... successive difference
          1/3   1/12   1/30   ...
            1/4     1/20  ... ...
                1/5   ... ... ...

Pascal's triangle
    1    1   1   1   1   1   1     .... units
       1   2   3   4   5   6       .... sum left and above
         1   3   6   10  15  21
           1   4   10  20  35
             1   5   15  35
               1   6   21


*)

(* LCM Lemma

(n+1) lcm (C(n,0) to C(n,n)) = lcm (1 to (n+1))

m-th number in the n-th row of Leibniz triangle is:  1/ (n+1)C(n,m)

LHS = (n+1) LCM (C(n,0), C(n,1), ..., C(n,n)) = lcd of fractions in n-th row of Leibniz triangle.

Any such number is an integer linear combination of fractions on triangle’s sides
1/1, 1/2, 1/3, ... 1/n, and vice versa.

So LHS = lcd (1/1, 1/2, 1/3, ..., 1/n) = RHS = lcm (1,2,3, ..., (n+1)).

0-th row:               1
1-st row:           1/2  1/2
2-nd row:        1/3  1/6  1/3
3-rd row:    1/4  1/12  1/12  1/4
4-th row: 1/5  1/20  1/30  1/20  1/5

4-th row: 1/5 C(4,m), C(4,m) = 1 4 6 4 1, hence 1/5 1/20 1/30 1/20 1/5
  lcd (1/5 1/20 1/30 1/20 1/5)
= lcm (5, 20, 30, 20, 5)
= lcm (5 C(4,0), 5 C(4,1), 5 C(4,2), 5 C(4,3), 5 C(4,4))
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))

But 1/5 = harmonic
    1/20 = 1/4 - 1/5 = combination of harmonic
    1/30 = 1/12 - 1/20 = (1/3 - 1/4) - (1/4 - 1/5) = combination of harmonic

  lcd (1/5 1/20 1/30 1/20 1/5)
= lcd (combination of harmonic from 1/1 to 1/5)
= lcd (1/1 to 1/5)
= lcm (1 to 5)

Theorem:  lcd (1/x 1/y 1/z) = lcm (x y z)
Theorem:  lcm (kx ky kz) = k lcm (x y z)
Theorem:  lcd (combination of harmonic from 1/1 to 1/n) = lcd (1/1 to 1/n)
Then apply first theorem, lcd (1/1 to 1/n) = lcm (1 to n)
*)

(* LCM Bound
   0 < n ==> 2^(n-1) < lcm (1 to n)

  lcm (1 to n)
= n lcm (C(n-1,0) to C(n-1,n-1))  by LCM Lemma
>= n max (0 <= j <= n-1) C(n-1,j)
>= SUM (0 <= j <= n-1) C(n-1,j)
= 2^(n-1)

  lcm (1 to 5)
= 5 lcm (C(4,0), C(4,1), C(4,2), C(4,3), C(4,4))


>= C(4,0) + C(4,1) + C(4,2) + C(4,3) + C(4,4)
= (1 + 1)^4
= 2^4

  lcm (1 to 5)             = 1x2x3x4x5/2 = 60
= 5 lcm (1 4 6 4 1)        = 5 x 12
=  lcm (1 4 6 4 1)         --> unfold 5x to add 5 times
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
 + lcm (1 4 6 4 1)
>= 1 + 4 + 6 + 4 + 1       --> pick one of each 5 C(n,m), i.e. diagonal
= (1 + 1)^4                --> fold back binomial
= 2^4                      = 16

Actually, can take 5 lcm (1 4 6 4 1) >= 5 x 6 = 30,
but this will need estimation of C(n, n/2), or C(2n,n), involving Stirling's formula.

Theorem: lcm (x y z) >= x  or lcm (x y z) >= y  or lcm (x y z) >= z

*)

(*

More generally, there is an identity for 0 <= k <= n:

(n+1) lcm (C(n,0), C(n,1), ..., C(n,k)) = lcm (n+1, n, n-1, ..., n+1-k)

This is simply that fact that any integer linear combination of
f(x), delta f(x), delta^2 f(x), ..., delta^k f(x)
is an integer linear combination of f(x), f(x-1), f(x-2), ..., f(x-k)
where delta is the difference operator, f(x) = 1/x, and x = n+1.

BTW, Leibnitz harmonic triangle too gives this identity.

That's correct, but the use of absolute values in the Leibniz triangle and
its specialized definition somewhat obscures the generic, linear nature of the identity.

  f(x) = f(n+1)   = 1/(n+1)
f(x-1) = f(n)     = 1/n
f(x-2) = f(n-1)   = 1/(n-1)
f(x-k) = f(n+1-k) = 1/(n+1-k)

        f(x) = f(n+1) = 1/(n+1) = 1/(n+1)C(n,0)
  delta f(x) = f(x-1) - f(x) = 1/n - 1/(n+1) = 1/n(n+1) = 1/(n+1)C(n,1)
             = C(1,0) f(x-1) - C(1,1) f(x)
delta^2 f(x) = delta f(x-1) - delta f(x) = 1/(n-1)n - 1/n(n+1)
             = (n(n+1) - n(n-1))/(n)(n+1)(n)(n-1)
             = 2n/n(n+1)n(n-1) = 1/(n+1)(n(n-1)/2) = 1/(n+1)C(n,2)
delta^2 f(x) = delta f(x-1) - delta f(x)
             = (f(x-2) - f(x-1)) - (f(x-1) - f(x))
             = f(x-2) - 2 f(x-1) + f(x)
             = C(2,0) f(x-2) - C(2,1) f(x-1) + C(2,2) f(x)
delta^3 f(x) = delta^2 f(x-1) - delta^2 f(x)
             = (f(x-3) - 2 f(x-2) + f(x-1)) - (f(x-2) - 2 f(x-1) + f(x))
             = f(x-3) - 3 f(x-2) + 3 f(x-1) - f(x)
             = C(3,0) f(x-3) - C(3,1) f(x-2) + C(3,2) f(x-2) - C(3,3) f(x)

delta^k f(x) = C(k,0) f(x-k) - C(k,1) f(x-k+1) + ... + (-1)^k C(k,k) f(x)
             = SUM(0 <= j <= k) (-1)^k C(k,j) f(x-k+j)
Also,
        f(x) = 1/(n+1)C(n,0)
  delta f(x) = 1/(n+1)C(n,1)
delta^2 f(x) = 1/(n+1)C(n,2)
delta^k f(x) = 1/(n+1)C(n,k)

so lcd (f(x), df(x), d^2f(x), ..., d^kf(x))
 = lcm ((n+1)C(n,0),(n+1)C(n,1),...,(n+1)C(n,k))   by lcd-to-lcm
 = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))         by linear combination
 = lcm ((n+1), n, (n-1), ..., (n+1-k))             by lcd-to-lcm

How to formalize:
lcd (f(x), df(x), d^2f(x), ..., d^kf(x)) = lcd (f(x), f(x-1), f(x-2), ..., f(x-k))

Simple case: lcd (f(x), df(x)) = lcd (f(x), f(x-1))

  lcd (f(x), df(x))
= lcd (f(x), f(x-1) - f(x))
= lcd (f(x), f(x-1))

Can we have
  LCD {f(x), df(x)}
= LCD {f(x), f(x-1) - f(x)} = LCD {1/x, 1/(x-1) - 1/x}
= LCD {f(x), f(x-1), f(x)}  = lcm {x, x(x-1)}
= LCD {f(x), f(x-1)}        = x(x-1) = lcm {x, x-1} = LCD {1/x, 1/(x-1)}

*)

(* Step 1: From Pascal's Triangle to Leibniz's Triangle

Pascal's Triangle:

row 0    1
row 1    1   1
row 2    1   2   1
row 3    1   3   3   1
row 4    1   4   6   4   1
row 5    1   5  10  10   5  1

The rule is: boundary = 1, entry = up      + left-up
         or: C(n,0) = 1, C(n,k) = C(n-1,k) + C(n-1,k-1)

Multiple each row by successor of its index, i.e. row n -> (n + 1) (row n):
Multiples Triangle (or Modified Triangle):

1 * row 0   1
2 * row 1   2  2
3 * row 2   3  6  3
4 * row 3   4  12 12  4
5 * row 4   5  20 30 20  5
6 * row 5   6  30 60 60 30  6

The rule is: boundary = n, entry = left * left-up / (left - left-up)
         or: L(n,0) = n, L(n,k) = L(n,k-1) * L(n-1,k-1) / (L(n,k-1) - L(n-1,k-1))

Then   lcm(1, 2)
     = lcm(2)
     = lcm(2, 2)

       lcm(1, 2, 3)
     = lcm(lcm(1,2), 3)  using lcm(1,2,...,n,n+1) = lcm(lcm(1,2,...,n), n+1)
     = lcm(2, 3)         using lcm(1,2)
     = lcm(2*3/1, 3)     using lcm(L(n,k-1), L(n-1,k-1)) = lcm(L(n,k-1), L(n-1,k-1)/(L(n,k-1), L(n-1,k-1)), L(n-1,k-1))
     = lcm(6, 3)
     = lcm(3, 6, 3)

       lcm(1, 2, 3, 4)
     = lcm(lcm(1,2,3), 4)
     = lcm(lcm(6,3), 4)
     = lcm(6, 3, 4)
     = lcm(6, 3*4/1, 4)
     = lcm(6, 12, 4)
     = lcm(6*12/6, 12, 4)
     = lcm(12, 12, 4)
     = lcm(4, 12, 12, 4)

       lcm(1, 2, 3, 4, 5)
     = lcm(lcm(2,3,4), 5)
     = lcm(lcm(12,4), 5)
     = lcm(12, 4, 5)
     = lcm(12, 4*5/1, 5)
     = lcm(12, 20, 5)
     = lcm(12*20/8, 20, 5)
     = lcm(30, 20, 5)
     = lcm(5, 20, 30, 20, 5)

       lcm(1, 2, 3, 4, 5, 6)
     = lcm(lcm(1, 2, 3, 4, 5), 6)
     = lcm(lcm(30,20,5), 6)
     = lcm(30, 20, 5, 6)
     = lcm(30, 20, 5*6/1, 6)
     = lcm(30, 20, 30, 6)
     = lcm(30, 20*30/10, 30, 6)
     = lcm(20, 60, 30, 6)
     = lcm(20*60/40, 60, 30, 6)
     = lcm(30, 60, 30, 6)
     = lcm(6, 30, 60, 30, 6)

Invert each entry of Multiples Triangle into a unit fraction:
Leibniz's Triangle:

1/(1 * row 0)   1/1
1/(2 * row 1)   1/2  1/2
1/(3 * row 2)   1/3  1/6  1/3
1/(4 * row 3)   1/4  1/12 1/12 1/4
1/(5 * row 4)   1/5  1/20 1/30 1/20 1/5
1/(6 * row 5)   1/6  1/30 1/60 1/60 1/30 1/6

Theorem: In the Multiples Triangle, the vertical-lcm = horizontal-lcm.
i.e.    lcm (1, 2, 3) = lcm (3, 6, 3) = 6
        lcm (1, 2, 3, 4) = lcm (4, 12, 12, 4) = 12
        lcm (1, 2, 3, 4, 5) = lcm (5, 20, 30, 20, 5) = 60
        lcm (1, 2, 3, 4, 5, 6) = lcm (6, 30, 60, 60, 30, 6) = 60
Proof: With reference to Leibniz's Triangle, note: term = left-up - left
  lcm (5, 20, 30, 20, 5)
= lcm (5, 20, 30)                   by reduce repetition
= lcm (5, d(1/20), d(1/30))         by denominator of fraction
= lcm (5, d(1/4 - 1/5), d(1/30))    by term = left-up - left
= lcm (5, lcm(4, 5), d(1/12 - 1/20))     by denominator of fraction subtraction
= lcm (5, 4, lcm(12, 20))                by lcm (a, lcm (a, b)) = lcm (a, b)
= lcm (5, 4, lcm(d(1/12), d(1/20)))      to fraction again
= lcm (5, 4, lcm(d(1/3 - 1/4), d(1/4 - 1/5)))   by Leibniz's Triangle
= lcm (5, 4, lcm(lcm(3,4),     lcm(4,5)))       by fraction subtraction denominator
= lcm (5, 4, lcm(3, 4, 5))                      by lcm merge
= lcm (5, 4, 3)                                 merge again
= lcm (5, 4, 3, 2)                              by lcm include factor (!!!)
= lcm (5, 4, 3, 2, 1)                           by lcm include 1

Note: to make 30, need 12, 20
      to make 12, need 3, 4; to make 20, need 4, 5
  lcm (1, 2, 3, 4, 5)
= lcm (1, 2, lcm(3,4), lcm(4,5), 5)
= lcm (1, 2, d(1/3 - 1/4), d(1/4 - 1/5), 5)
= lcm (1, 2, d(1/12), d(1/20), 5)
= lcm (1, 2, 12, 20, 5)
= lcm (1, 2, lcm(12, 20), 20, 5)
= lcm (1, 2, d(1/12 - 1/20), 20, 5)
= lcm (1, 2, d(1/30), 20, 5)
= lcm (1, 2, 30, 20, 5)
= lcm (1, 30, 20, 5)             can drop factor !!
= lcm (30, 20, 5)                can drop 1
= lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm (1, 2, 3, 4, 5), lcm(5,6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/5 - 1/6), 6)
= lcm (lcm (5, 20, 30, 20, 5), d(1/30), 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (lcm (5, 20, 30, 20, 5), 30, 6)
= lcm (5, 30, 20, 6)
= lcm (30, 20, 6)               can drop factor !!
= lcm (lcm(20, 30), 30, 6)
= lcm (d(1/20 - 1/30), 30, 6)
= lcm (d(1/60), 30, 6)
= lcm (60, 30, 6)
= lcm (6, 30, 60, 30, 6)

  lcm (1, 2)
= lcm (lcm(1,2), 2)
= lcm (2, 2)

  lcm (1, 2, 3)
= lcm (lcm(1, 2), 3)
= lcm (2, 3) --> lcm (2x3/(3-2), 3) = lcm (6, 3)
= lcm (lcm(2, 3), 3)   -->  lcm (6, 3) = lcm (3, 6, 3)
= lcm (d(1/2 - 1/3), 3)
= lcm (d(1/6), 3)
= lcm (6, 3) = lcm (3, 6, 3)

  lcm (1, 2, 3, 4)
= lcm (lcm(1, 2, 3), 4)
= lcm (lcm(6, 3), 4)
= lcm (6, 3, 4)
= lcm (6, lcm(3, 4), 4) --> lcm (6, 12, 4) = lcm (6x12/(12-6), 12, 4)
= lcm (6, d(1/3 - 1/4), 4)                 = lcm (12, 12, 4) = lcm (4, 12, 12, 4)
= lcm (6, d(1/12), 4)
= lcm (6, 12, 4)
= lcm (lcm(6, 12), 4)
= lcm (d(1/6 - 1/12), 4)
= lcm (d(1/12), 4)
= lcm (12, 4) = lcm (4, 12, 12, 4)

  lcm (1, 2, 3, 4, 5)
= lcm (lcm(1, 2, 3, 4), 5)
= lcm (lcm(12, 4), 5)
= lcm (12, 4, 5)
= lcm (12, lcm(4,5), 5) --> lcm (12, 20, 5) = lcm (12x20/(20-12), 20, 5)
= lcm (12, d(1/4 - 1/5), 5)                 = lcm (240/8, 20, 5) but lcm(12,20) != 30
= lcm (12, d(1/20), 5)                      = lcm (30, 20, 5)    use lcm(a,b,c) = lcm(ab/(b-a), b, c)
= lcm (12, 20, 5)
= lcm (lcm(12,20), 20, 5)
= lcm (d(1/12 - 1/20), 20, 5)
= lcm (d(1/30), 20, 5)
= lcm (30, 20, 5) = lcm (5, 20, 30, 20, 5)

  lcm (1, 2, 3, 4, 5, 6)
= lcm (lcm(1, 2, 3, 4, 5), 6)
= lcm (lcm(30, 20, 5), 6)
= lcm (30, 20, 5, 6)
= lcm (30, 20, lcm(5,6), 6) --> lcm (30, 20, 30, 6) = lcm (30, 20x30/(30-20), 30, 6)
= lcm (30, 20, d(1/5 - 1/6), 6)                     = lcm (30, 60, 30, 6)
= lcm (30, 20, d(1/30), 6)                          = lcm (30x60/(60-30), 60, 30, 6)
= lcm (30, 20, 30, 6)                               = lcm (60, 60, 30, 6)
= lcm (30, lcm(20,30), 30, 6)
= lcm (30, d(1/20 - 1/30), 30, 6)
= lcm (30, d(1/60), 30, 6)
= lcm (30, 60, 30, 6)
= lcm (lcm(30, 60), 60, 30, 6)
= lcm (d(1/30 - 1/60), 60, 30, 6)
= lcm (d(1/60), 60, 30, 6)
= lcm (60, 60, 30, 6)
= lcm (60, 30, 6) = lcm (6, 30, 60, 60, 30, 6)

*)

(* ------------------------------------------------------------------------- *)
(* Leibniz Triangle (Denominator form)                                       *)
(* ------------------------------------------------------------------------- *)

(* Define Leibniz Triangle *)
val leibniz_def = Define`
  leibniz n k = (n + 1) * binomial n k
`;

(* export simple definition *)
val _ = export_rewrites["leibniz_def"];

(* Theorem: leibniz 0 n = if n = 0 then 1 else 0 *)
(* Proof:
     leibniz 0 n
   = (0 + 1) * binomial 0 n     by leibniz_def
   = if n = 0 then 1 else 0     by binomial_n_0
*)
val leibniz_0_n = store_thm(
  "leibniz_0_n",
  ``!n. leibniz 0 n = if n = 0 then 1 else 0``,
  rw[binomial_0_n]);

(* Theorem: leibniz n 0 = n + 1 *)
(* Proof:
     leibniz n 0
   = (n + 1) * binomial n 0     by leibniz_def
   = (n + 1) * 1                by binomial_n_0
   = n + 1
*)
val leibniz_n_0 = store_thm(
  "leibniz_n_0",
  ``!n. leibniz n 0 = n + 1``,
  rw[binomial_n_0]);

(* Theorem: leibniz n n = n + 1 *)
(* Proof:
     leibniz n n
   = (n + 1) * binomial n n     by leibniz_def
   = (n + 1) * 1                by binomial_n_n
   = n + 1
*)
val leibniz_n_n = store_thm(
  "leibniz_n_n",
  ``!n. leibniz n n = n + 1``,
  rw[binomial_n_n]);

(* Theorem: n < k ==> leibniz n k = 0 *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k     by leibniz_def
   = (n + 1) * 0                by binomial_less_0
   = 0
*)
val leibniz_less_0 = store_thm(
  "leibniz_less_0",
  ``!n k. n < k ==> (leibniz n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: k <= n ==> (leibniz n k = leibniz n (n-k)) *)
(* Proof:
     leibniz n k
   = (n + 1) * binomial n k       by leibniz_def
   = (n + 1) * binomial n (n-k)   by binomial_sym
   = leibniz n (n-k)              by leibniz_def
*)
val leibniz_sym = store_thm(
  "leibniz_sym",
  ``!n k. k <= n ==> (leibniz n k = leibniz n (n-k))``,
  rw[leibniz_def, GSYM binomial_sym]);

(* Theorem: k < HALF n ==> leibniz n k < leibniz n (k + 1) *)
(* Proof:
   Assume k < HALF n, and note that 0 < (n + 1).
                  leibniz n k < leibniz n (k + 1)
   <=> (n + 1) * binomial n k < (n + 1) * binomial n (k + 1)    by leibniz_def
   <=>           binomial n k < binomial n (k + 1)              by LT_MULT_LCANCEL
   <=>  T                                                       by binomial_monotone
*)
val leibniz_monotone = store_thm(
  "leibniz_monotone",
  ``!n k. k < HALF n ==> leibniz n k < leibniz n (k + 1)``,
  rw[leibniz_def, binomial_monotone]);

(* Theorem: k <= n ==> 0 < leibniz n k *)
(* Proof:
   Since leibniz n k = (n + 1) * binomial n k  by leibniz_def
     and 0 < n + 1, 0 < binomial n k           by binomial_pos
   Hence 0 < leibniz n k                       by ZERO_LESS_MULT
*)
val leibniz_pos = store_thm(
  "leibniz_pos",
  ``!n k. k <= n ==> 0 < leibniz n k``,
  rw[leibniz_def, binomial_pos, ZERO_LESS_MULT, DECIDE``!n. 0 < n + 1``]);

(* Theorem: (leibniz n k = 0) <=> n < k *)
(* Proof:
       leibniz n k = 0
   <=> (n + 1) * (binomial n k = 0)     by leibniz_def
   <=> binomial n k = 0                 by MULT_EQ_0, n + 1 <> 0
   <=> n < k                            by binomial_eq_0
*)
val leibniz_eq_0 = store_thm(
  "leibniz_eq_0",
  ``!n k. (leibniz n k = 0) <=> n < k``,
  rw[leibniz_def, binomial_eq_0]);

(* Theorem: leibniz n = (\j. (n + 1) * j) o (binomial n) *)
(* Proof: by leibniz_def and function equality. *)
val leibniz_alt = store_thm(
  "leibniz_alt",
  ``!n. leibniz n = (\j. (n + 1) * j) o (binomial n)``,
  rw[leibniz_def, FUN_EQ_THM]);

(* Theorem: leibniz n k = (\j. (n + 1) * j) (binomial n k) *)
(* Proof: by leibniz_def *)
val leibniz_def_alt = store_thm(
  "leibniz_def_alt",
  ``!n k. leibniz n k = (\j. (n + 1) * j) (binomial n k)``,
  rw_tac std_ss[leibniz_def]);

(*
Picture of Leibniz Triangle L-corner:
    b = L (n-1) k
    a = L n     k   c = L n (k+1)

a = L n k = (n+1) * (n, k, n-k) = (n+1, k, n-k) = (n+1)! / k! (n-k)!
b = L (n-1) k = n * (n-1, k, n-1-k) = (n , k, n-k-1) = n! / k! (n-k-1)! = a * (n-k)/(n+1)
c = L n (k+1) = (n+1) * (n, k+1, n-(k+1)) = (n+1, k+1, n-k-1) = (n+1)! / (k+1)! (n-k-1)! = a * (n-k)/(k+1)

a * b = a * a * (n-k)/(n+1)
a - b = a - a * (n-k)/(n+1) = a * (1 - (n-k)/(n+1)) = a * (n+1 - n+k)/(n+1) = a * (k+1)/(n+1)
Hence
  a * b /(a - b)
= [a * a * (n-k)/(n+1)] / [a * (k+1)/(n+1)]
= a * (n-k)/(k+1)
= c
or a * b = c * (a - b)
*)

(* Theorem: 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k *)
(* Proof:
     (n + 1) * leibniz (n - 1) k
   = (n + 1) * ((n-1 + 1) * binomial (n-1) k)     by leibniz_def
   = (n + 1) * (n * binomial (n-1) k)             by SUB_ADD, 1 <= n.
   = (n + 1) * ((n - k) * (binomial n k))         by binomial_up_eqn
   = ((n + 1) * (n - k)) * binomial n k           by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k           by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)           by MULT_ASSOC
   = (n - k) * leibniz n k                        by leibniz_def
*)
val leibniz_up_eqn = store_thm(
  "leibniz_up_eqn",
  ``!n. 0 < n ==> !k. (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k``,
  rw[leibniz_def] >>
  `1 <= n` by decide_tac >>
  metis_tac[SUB_ADD, binomial_up_eqn, MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1) *)
(* Proof:
   Since  (n + 1) * leibniz (n - 1) k = (n - k) * leibniz n k    by leibniz_up_eqn
          leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)  by DIV_SOLVE, 0 < n+1.
*)
val leibniz_up = store_thm(
  "leibniz_up",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * leibniz n k DIV (n + 1)``,
  rw[leibniz_up_eqn, DIV_SOLVE]);

(* Theorem: 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k *)
(* Proof:
     leibniz (n - 1) k
   = (n - k) * leibniz n k DIV (n + 1)                  by leibniz_up, 0 < n
   = (n - k) * ((n + 1) * binomial n k) DIV (n + 1)     by leibniz_def
   = (n + 1) * ((n - k) * binomial n k) DIV (n + 1)     by MULT_ASSOC, MULT_COMM
   = (n - k) * binomial n k                             by MULT_DIV, 0 < n + 1
*)
val leibniz_up_alt = store_thm(
  "leibniz_up_alt",
  ``!n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k``,
  metis_tac[leibniz_up, leibniz_def, MULT_DIV, MULT_ASSOC, MULT_COMM, DECIDE``0 < x + 1``]);

(* Theorem: 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k *)
(* Proof:
     (k + 1) * leibniz n (k+1)
   = (k + 1) * ((n + 1) * binomial n (k+1))   by leibniz_def
   = (k + 1) * (n + 1) * binomial n (k+1)     by MULT_ASSOC
   = (n + 1) * (k + 1) * binomial n (k+1)     by MULT_COMM
   = (n + 1) * ((k + 1) * binomial n (k+1))   by MULT_ASSOC
   = (n + 1) * ((n - k) * (binomial n k))     by binomial_right_eqn
   = ((n + 1) * (n - k)) * binomial n k       by MULT_ASSOC
   = ((n - k) * (n + 1)) * binomial n k       by MULT_COMM
   = (n - k) * ((n + 1) * binomial n k)       by MULT_ASSOC
   = (n - k) * leibniz n k                    by leibniz_def
*)
val leibniz_right_eqn = store_thm(
  "leibniz_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k``,
  metis_tac[leibniz_def, MULT_COMM, MULT_ASSOC, binomial_right_eqn]);

(* Theorem: 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k + 1) *)
(* Proof:
   Since  (k + 1) * leibniz n (k+1) = (n - k) * leibniz n k    by leibniz_right_eqn
          leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val leibniz_right = store_thm(
  "leibniz_right",
  ``!n. 0 < n ==> !k. leibniz n (k+1) = (n - k) * (leibniz n k) DIV (k+1)``,
  rw[leibniz_right_eqn, DIV_SOLVE]);

(* Note: Following is the property from Leibniz Harmonic Triangle:
   1 / leibniz n (k+1) = 1 / leibniz (n-1) k  - 1 / leibniz n k
                       = (leibniz n k - leibniz (n-1) k) / leibniz n k * leibniz (n-1) k
*)

(* The Idea:
                                                b
Actually, lcm a b = lcm b c = lcm c a     for   a c  in Leibniz Triangle.
The only relationship is: c = ab/(a - b), or ab = c(a - b).

Is this a theorem:  ab = c(a - b)  ==> lcm a b = lcm b c = lcm c a
Or in fractions,   1/c = 1/b - 1/a ==> lcm a b = lcm b c = lcm c a ?

lcm a b
= a b / (gcd a b)
= c(a - b) / (gcd a (a - b))
= ac(a - b) / gcd a (a-b) / a
= lcm (a (a-b)) c / a
= lcm (ca c(a-b)) / a
= lcm (ca ab) / a
= lcm (b c)

lcm a b = a b / gcd a b = a b / gcd a (a-b) = a b c / gcd ca c(a-b)
= c (a-b) c / gcd ca c(a-b) = lcm ca c(a-b) / a = lcm ca ab / a = lcm b c

  lcm b c
= b c / gcd b c
= a b c / gcd a*b a*c
= a b c / gcd c*(a-b) c*a
= a b / gcd (a-b) a
= a b / gcd b a
= lcm (a b)
= lcm a b

  lcm a c
= a c / gcd a c
= a b c / gcd b*a b*c
= a b c / gcd c*(a-b) b*c
= a b / gcd (a-b) b
= a b / gcd a b
= lcm a b

Yes!

This is now in LCM_EXCHANGE:
val it = |- !a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c): thm
*)

(* Theorem: 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   If n <= k,
      then  n-1 < k, and n < k+1.
      so    leibniz (n-1) k = 0         by leibniz_less_0, n-1 < k.
      and   leibniz n (k+1) = 0         by leibniz_less_0, n < k+1.
      Hence true                        by MULT_EQ_0
   Otherwise, k < n, or k <= n.
      then  (n+1) - (n-k) = k+1.

        (k + 1) * (c * (a - b))
      = (k + 1) * c * (a - b)                   by MULT_ASSOC
      = ((n+1) - (n-k)) * c * (a - b)           by above
      = (n - k) * a * (a - b)                   by leibniz_right_eqn
      = (n - k) * a * a - (n - k) * a * b       by LEFT_SUB_DISTRIB
      = (n + 1) * b * a - (n - k) * a * b       by leibniz_up_eqn
      = (n + 1) * (a * b) - (n - k) * (a * b)   by MULT_ASSOC, MULT_COMM
      = ((n+1) - (n-k)) * (a * b)               by RIGHT_SUB_DISTRIB
      = (k + 1) * (a * b)                       by above

      Since (k+1) <> 0, the result follows      by MULT_LEFT_CANCEL
*)
val leibniz_property = store_thm(
  "leibniz_property",
  ``!n. 0 < n ==>
   !k. leibniz n k * leibniz (n-1) k = leibniz n (k+1) * (leibniz n k - leibniz (n-1) k)``,
  rpt strip_tac >>
  Cases_on `n <= k` >-
  rw[leibniz_less_0] >>
  `(n+1) - (n-k) = k+1` by decide_tac >>
  `(k+1) <> 0` by decide_tac >>
  qabbrev_tac `a = leibniz n k` >>
  qabbrev_tac `b = leibniz (n - 1) k` >>
  qabbrev_tac `c = leibniz n (k + 1)` >>
  `(k + 1) * (c * (a - b)) = ((n+1) - (n-k)) * c * (a - b)` by rw_tac std_ss[MULT_ASSOC] >>
  `_ = (n - k) * a * (a - b)` by rw_tac std_ss[leibniz_right_eqn, Abbr`c`, Abbr`a`] >>
  `_ = (n - k) * a * a - (n - k) * a * b` by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  `_ = (n + 1) * b * a - (n - k) * a * b` by rw_tac std_ss[leibniz_up_eqn, Abbr`b`, Abbr`a`] >>
  `_ = (n + 1) * (a * b) - (n - k) * (a * b)` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `_ = ((n+1) - (n-k)) * (a * b)` by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  `_ = (k + 1) * (a * b)` by rw_tac std_ss[] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k))) *)
(* Proof:
   Note  (FACT k * FACT (n - k)) divides (FACT n)       by binomial_is_integer
    and  0 < FACT k * FACT (n - k)                      by FACT_LESS, ZERO_LESS_MULT
     leibniz n k
   = (n + 1) * binomial n k                             by leibniz_def
   = (n + 1) * (FACT n DIV (FACT k * FACT (n - k)))     by binomial_formula3
   = (n + 1) * FACT n DIV (FACT k * FACT (n - k))       by MULTIPLY_DIV
*)
val leibniz_formula = store_thm(
  "leibniz_formula",
  ``!n k. k <= n ==> (leibniz n k = (n + 1) * FACT n DIV (FACT k * FACT (n - k)))``,
  metis_tac[leibniz_def, binomial_formula3, binomial_is_integer, FACT_LESS, MULTIPLY_DIV, ZERO_LESS_MULT]);

(* Theorem: 0 < n ==>
   !k. k < n ==> leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k) *)
(* Proof:
   By leibniz_property,
   leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k
   Since 0 < leibniz n k and 0 < leibniz (n-1) k     by leibniz_pos
      so 0 < (leibniz n k - leibniz (n-1) k)         by MULT_EQ_0
   Hence by MULT_COMM, DIV_SOLVE, 0 < (leibniz n k - leibniz (n-1) k),
   leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k)
*)
val leibniz_recurrence = store_thm(
  "leibniz_recurrence",
  ``!n. 0 < n ==>
   !k. k < n ==> (leibniz n (k+1) = leibniz n k * leibniz (n-1) k DIV (leibniz n k - leibniz (n-1) k))``,
  rpt strip_tac >>
  `k <= n /\ k <= (n-1)` by decide_tac >>
  `leibniz n (k+1) * (leibniz n k - leibniz (n-1) k) = leibniz n k * leibniz (n-1) k` by rw[leibniz_property] >>
  `0 < leibniz n k /\ 0 < leibniz (n-1) k` by rw[leibniz_pos] >>
  `0 < (leibniz n k - leibniz (n-1) k)` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw_tac std_ss[DIV_SOLVE, MULT_COMM]);

(* Theorem: 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1))) *)
(* Proof:
   Since 0 < k, k = SUC h     for some h
      or k = h + 1            by ADD1
     and h = k - 1            by arithmetic
   Since 0 < k and k <= n,
         0 < n and h < n.
   Hence true by leibniz_recurrence.
*)
val leibniz_n_k = store_thm(
  "leibniz_n_k",
  ``!n k. 0 < k /\ k <= n ==>
   (leibniz n k = leibniz n (k-1) * leibniz (n-1) (k-1) DIV (leibniz n (k-1) - leibniz (n-1) (k-1)))``,
  rpt strip_tac >>
  `?h. k = h + 1` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO, ADD1] >>
  `(h = k - 1) /\ h < n /\ 0 < n` by decide_tac >>
  metis_tac[leibniz_recurrence]);

(* Theorem: 0 < n ==>
   !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1)) *)
(* Proof:
   By leibniz_property,
   leibniz n k * leibniz (n - 1) k = leibniz n (k + 1) * (leibniz n k - leibniz (n - 1) k)
   Hence true by LCM_EXCHANGE.
*)
val leibniz_lcm_exchange = store_thm(
  "leibniz_lcm_exchange",
  ``!n. 0 < n ==> !k. lcm (leibniz n k) (leibniz (n-1) k) = lcm (leibniz n k) (leibniz n (k+1))``,
  rw[leibniz_property, LCM_EXCHANGE]);

(* Theorem: 4 ** n <= leibniz (2 * n) n *)
(* Proof:
   Let m = 2 * n.
   Then n = HALF m                              by HALF_TWICE
   Let l1 = GENLIST (K (binomial m n)) (m + 1)
   and l2 = GENLIST (binomial m) (m + 1)
   Note LENGTH l1 = LENGTH l2 = m + 1           by LENGTH_GENLIST

   Claim: !k. k < m + 1 ==> EL k l2 <= EL k l1
   Proof: Note EL k l1 = binomial m n           by EL_GENLIST
           and EL k l2 = binomial m k           by EL_GENLIST
         Apply binomial m k <= binomial m n     by binomial_max
           The result follows

     leibniz m n
   = (m + 1) * binomial m n                     by leibniz_def
   = SUM (GENLIST (K (binomial m n)) (m + 1))   by SUM_GENLIST_K
   >= SUM (GENLIST (\k. binomial m k) (m + 1))  by SUM_LE, above
    = SUM (GENLIST (binomial m) (SUC m))        by ADD1
    = 2 ** m                                    by binomial_sum
    = 2 ** (2 * n)                              by notation
    = (2 ** 2) ** n                             by EXP_EXP_MULT
    = 4 ** n                                    by arithmetic
*)
val leibniz_middle_lower = store_thm(
  "leibniz_middle_lower",
  ``!n. 4 ** n <= leibniz (2 * n) n``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n = HALF m` by rw[HALF_TWICE, Abbr`m`] >>
  qabbrev_tac `l1 = GENLIST (K (binomial m n)) (m + 1)` >>
  qabbrev_tac `l2 = GENLIST (binomial m) (m + 1)` >>
  `!k. k < m + 1 ==> EL k l2 <= EL k l1` by rw[binomial_max, EL_GENLIST, Abbr`l1`, Abbr`l2`] >>
  `leibniz m n = (m + 1) * binomial m n` by rw[leibniz_def] >>
  `_ = SUM l1` by rw[SUM_GENLIST_K, Abbr`l1`] >>
  `SUM l2 = SUM (GENLIST (binomial m) (SUC m))` by rw[ADD1, Abbr`l2`] >>
  `_ = 2 ** m` by rw[binomial_sum] >>
  `_ = 4 ** n` by rw[EXP_EXP_MULT, Abbr`m`] >>
  metis_tac[SUM_LE, LENGTH_GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Property of Leibniz Triangle                                              *)
(* ------------------------------------------------------------------------- *)

(*
binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
This means:
           B n k  + B n  k*
                       v
                    B n* k*
However, for the Leibniz Triangle, the recurrence is:
           L n k
           L n* k  -> L n* k* = (L n* k)(L n k) / (L n* k - L n k)
That is, it takes a different style, and has the property:
                    1 / L n* k* = 1 / L n k - 1 / L n* k
Why?
First, some verification.
Pascal:     [1]  3   3
                [4]  6 = 3 + 3 = 6
Leibniz:        12  12
               [20] 30 = 20 * 12 / (20 - 12) = 20 * 12 / 8 = 30
Now, the 20 comes from 4 = 3 + 1.
Originally,  30 = 5 * 6          by definition based on multiple
                = 5 * (3 + 3)    by Pascal
                = 4 * (3 + 3) + (3 + 3)
                = 12 + 12 + 6
In terms of factorials,  30 = 5 * 6 = 5 * B(4,2) = 5 * 4!/2!2!
                         20 = 5 * 4 = 5 * B(4,1) = 5 * 4!/1!3!
                         12 = 4 * 3 = 4 * B(3,1) = 4 * 3!/1!2!
So  1/30 = (2!2!)/(5 4!)     1 / n** B n* k* = k*! (n* - k* )! / n** n*! = (n - k)! k*! / n**!
    1/20 = (1!3!)/(5 4!)     1 / n** B n* k
    1/12 = (1!2!)/(4 3!)     1 / n* B n k
    1/12 - 1/20
  = (1!2!)/(4 3!) - (1!3!)/(5 4!)
  = (1!2!)/4! - (1!3!)/5!
  = 5(1!2!)/5! - (1!3!)/5!
  = (5(1!2!) - (1!3!))/5!
  = (5 1! - 3 1!) 2!/5!
  = (5 - 3)1! 2!/5!
  = 2! 2! / 5!

    1 / n B n k - 1 / n** B n* k
  = k! (n-k)! / n* n! - k! (n* - k)! / n** n*!
  = k! (n-k)! / n*! - k!(n* - k)! / n** n*!
  = (n** (n-k)! - (n* - k)!) k! / n** n*!
  = (n** - (n* - k)) (n - k)! k! / n** n*!
  = (k+1) (n - k)! k! / n** n*!
  = (n* - k* )! k*! / n** n*!
  = 1 / n** B n* k*

Direct without using unit fractions,

L n k = n* B n k = n* n! / k! (n-k)! = n*! / k! (n-k)!
L n* k = n** B n* k = n** n*! / k! (n* - k)! = n**! / k! (n* - k)!
L n* k* = n** B n* k* = n** n*! / k*! (n* - k* )! = n**! / k*! (n-k)!

(L n* k) * (L n k) = n**! n*! / k! (n* - k)! k! (n-k)!
(L n* k) - (L n k) = n**! / k! (n* - k)! - n*! / k! (n-k)!
                   = n**! / k! (n-k)!( 1/(n* - k) - 1/ n** )
                   = n**! / k! (n-k)! (n** - n* + k)/(n* - k)(n** )
                   = n**! / k! (n-k)! k* / (n* - k) n**
                   = n*! k* / k! (n* - k)!
(L n* k) * (L n k) / (L n* k) - (L n k)
= n**! /k! (n-k)! k*
= n**! /k*! (n-k)!
= L n* k*
So:    L n k
       L n* k --> L n* k*

Can the LCM be shown directly?
lcm (L n* k, L n k) = lcm (L n* k, L n* k* )
To prove this, need to show:
both have the same common multiples, and least is the same -- probably yes due to common L n* k.

In general, what is the condition for   lcm a b = lcm a c ?
Well,  lcm a b = a b / gcd a b,  lcm a c = a c / gcd a c
So it must be    a b gcd a c = a c gcd a b, or b * gcd a c = c * gcd a b.

It this true for Leibniz triangle?
Let a = 5, b = 4, c = 20.  b * gcd a c = 4 * gcd 5 20 = 4 * 5 = 20
                           c * gcd a b = 20 * gcd 5 4 = 20
Verify lcm a b = lcm 5 4 = 20 = 5 * 4 / gcd 5 4
       lcm a c = lcm 5 20 = 20 = 5 * 20 / gcd 5 20
       5 * 4 / gcd 5 4 = 5 * 20 / gcd 5 20
or        4 * gcd 5 20 = 20 * gcd 5 4

(L n k) * gcd (L n* k, L n* k* ) = (L n* k* ) * gcd (L n* k, L n k)

or n* B n k * gcd (n** B n* k, n** B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
By GCD_COMMON_FACTOR, !m n k. gcd (k * m) (k * n) = k * gcd m n
   n** n* B n k gcd (B n* k, B n* k* ) = (n** B n* k* ) * gcd (n** B n* k, n* B n k)
*)

(* Special Property of Leibniz Triangle
For:    L n k
        L n+ k --> L n+ k+

L n k  = n+! / k! (n-k)!
L n+ k = n++! / k! (n+ - k)! = n++ n+! / k! (n+ - k) k! = (n++ / n+ - k) L n k
L n+ k+ = n++! / k+! (n-k)! = (L n+ k) * (L n k) / (L n+ k - L n k) = (n++ / k+) L n k
Let g = gcd (L n+ k) (L n k), then L n+ k+ = lcm (L n+ k) (L n k) / (co n+ k - co n k)
where co n+ k = L n+ k / g, co n k = L n k / g.

    L n+ k = (n++ / n+ - k) L n k,
and L n+ k+ = (n++ / k+) L n k
e.g. L 3 1 = 12
     L 4 1 = 20, or (3++ / 3+ - 1) L 3 1 = (5/3) 12 = 20.
     L 4 2 = 30, or (3++ / 1+) L 3 1 = (5/2) 12 = 30.
so lcm (L 4 1) (L 3 1) = lcm (5/3)*12 12 = 12 * 5 = 60   since 3 must divide 12.
   lcm (L 4 1) (L 4 2) = lcm (5/3)*12 (5/2)*12 = 12 * 5 = 60  since 3, 2 must divide 12.

By LCM_COMMON_FACTOR |- !m n k. lcm (k * m) (k * n) = k * lcm m n
lcm a (a * b DIV c) = a * b

So the picture is:     (L n k)
                       (L n k) * (n+2)/(n-k+1)   (L n k) * (n+2)/(k+1)

A better picture:
Pascal:       (B n-1 k) = (n-1, k, n-k-1)
              (B n k)   = (n, k, n-k)     (B n k+1) = (n, k+1, n-k-1)
Leibniz:      (L n-1 k) = (n, k, n-k-1) = (L n k) / (n+1) * (n-k-1)
              (L n k)   = (n+1, k, n-k)   (L n k+1) = (n+1, k+1, n-k-1) = (L n k) / (n-k-1) * (k+1)
And we want:
    LCM (L, (n-k-1) * L DIV (n+1)) = LCM (L, (k+1) * L DIV (n-k-1)).

Theorem:   lcm a ((a * b) DIV c) = (a * b) DIV (gcd b c)
Assume this theorem,
LHS = L * (n-k-1) DIV gcd (n-k-1, n+1)
RHS = L * (k+1) DIV gcd (k+1, n-k-1)
Still no hope to show LHS = RHS !

LCM of fractions:
lcm (a/c, b/c) = lcm(a, b)/c
lcm (a/c, b/d) = ... = lcm(a, b)/gcd(c, d)
Hence lcm (a, a*b/c) = lcm(a*b/b, a*b/c) = a * b / gcd (b, c)
*)

(* Special Property of Leibniz Triangle -- another go
Leibniz:    L(5,1) = 30 = b
            L(6,1) = 42 = a   L(6,2) = 105 = c,  c = ab/(a - b), or ab = c(a - b)
Why is LCM 42 30 = LCM 42 105 = 210 = 2x3x5x7?
First, b = L(5,1) = 30 = (6,1,4) = 6!/1!4! = 7!/1!5! * (5/7) = a * (5/7) = 2x3x5
       a = L(6,1) = 42 = (7,1,5) = 7!/1!5! = 2x3x7 = b * (7/5) = c * (2/5)
       c = L(6,2) = 105 = (7,2,4) = 7!/2!4! = 7!/1!5! * (5/2) = a * (5/2) = 3x5x7
Any common multiple of a, b must have 5, 7 as factor, also with factor 2 (by common k = 1)
Any common multiple of a, c must have 5, 2 as factor, also with factor 7 (by common n = 6)
Also n = 5 implies a factor 6, k = 2 imples a factor 2.
LCM a b = a b / GCD a b
        = c (a - b) / GCD a b
        = (m c') (m a' - (m-1)b') / GCD (m a') (m-1 b')
LCM a c = a c / GCD a c
        = (m a') (m c') / GCD (m a') (m c')     where c' = a' + b' from Pascal triangle
        = m a' (a' + b') / GCD a' (a' + b')
        = m a' (a' + b') / GCD a' b'
        = a' c / GCD a' b'
Can we prove:    c(a - b) / GCD a b = c a' / GCD a' b'
or                 (a - b) GCD a' b' = a' GCD a b ?
or                a GCD a' b' = a' GCD a b + b GCD a' b' ?
or                    ab GCD a' b' = c a' GCD a b?
or                    m (b GCD a' b') = c GCD a b?
or                       b GCD a' b' = c' GCD a b?
b = (a DIV 7) * 5
c = (a DIV 2) * 5
lcm (a, b) = lcm (a, (a DIV 7) * 5) = lcm (a, 5)
lcm (a, c) = lcm (a, (a DIV 2) * 5) = lcm (a, 5)
Is this a theorem: lcm (a, (a DIV p) * b) = lcm (a, b) if p | a ?
Let c = lcm (a, b). Then a | c, b | c.
Since a = (a DIV p) * p, (a DIV p) * p | c.
Hence  ((a DIV p) * b) * p | b * c.
How to conclude ((a DIV p) * b) | c?

A counter-example:
lcm (42, 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 3) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 6) * 9) = 126 = 2x3x3x7.
lcm (42, (42 DIV 2) * 9) = 378 = 2x3x3x3x7.
lcm (42, (42 DIV 7) * 9) = 378 = 2x3x3x3x7.

LCM a c
= LCM a (ab/(a-b))    let g = GCD(a,b), a = gA, b=gB, coprime A,B.
= LCM gA gAB/(A-B)
= g LCM A AB/(A-B)
= (ab/LCM a b) LCM A AB/(A-B)
*)

(* ------------------------------------------------------------------------- *)
(* LCM of a list of numbers                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a list of numbers *)
val list_lcm_def = Define`
  (list_lcm [] = 1) /\
  (list_lcm (h::t) = lcm h (list_lcm t))
`;

(* export simple definition *)
val _ = export_rewrites["list_lcm_def"];

(* Theorem: list_lcm [] = 1 *)
(* Proof: by list_lcm_def. *)
val list_lcm_nil = store_thm(
  "list_lcm_nil",
  ``list_lcm [] = 1``,
  rw[]);

(* Theorem: list_lcm (h::t) = lcm h (list_lcm t) *)
(* Proof: by list_lcm_def. *)
val list_lcm_cons = store_thm(
  "list_lcm_cons",
  ``!h t. list_lcm (h::t) = lcm h (list_lcm t)``,
  rw[]);

(* Theorem: list_lcm [x] = x *)
(* Proof:
     list_lcm [x]
   = lcm x (list_lcm [])    by list_lcm_cons
   = lcm x 1                by list_lcm_nil
   = x                      by LCM_1
*)
val list_lcm_sing = store_thm(
  "list_lcm_sing",
  ``!x. list_lcm [x] = x``,
  rw[]);

(* Theorem: list_lcm (SNOC x l) = list_lcm (x::l) *)
(* Proof:
   By induction on l.
   Base case: list_lcm (SNOC x []) = lcm x (list_lcm [])
     list_lcm (SNOC x [])
   = list_lcm [x]           by SNOC
   = lcm x (list_lcm [])    by list_lcm_def
   Step case: list_lcm (SNOC x l) = lcm x (list_lcm l) ==>
              !h. list_lcm (SNOC x (h::l)) = lcm x (list_lcm (h::l))
     list_lcm (SNOC x (h::l))
   = list_lcm (h::SNOC x l)        by SNOC
   = lcm h (list_lcm (SNOC x l))   by list_lcm_def
   = lcm h (lcm x (list_lcm l))    by induction hypothesis
   = lcm x (lcm h (list_lcm l))    by LCM_ASSOC_COMM
   = lcm x (list_lcm h::l)         by list_lcm_def
*)
val list_lcm_snoc = store_thm(
  "list_lcm_snoc",
  ``!x l. list_lcm (SNOC x l) = lcm x (list_lcm l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[LCM_ASSOC_COMM]);

(* Theorem: list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: !n. list_lcm (MAP (\k. n * k) []) = if [] = [] then 1 else n * list_lcm []
       list_lcm (MAP (\k. n * k) [])
     = list_lcm []                      by MAP
     = 1                                by list_lcm_nil
   Step case: !n. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l ==>
              !h n. list_lcm (MAP (\k. n * k) (h::l)) = if h::l = [] then 1 else n * list_lcm (h::l)
     Note h::l <> []                    by NOT_NIL_CONS
     If l = [], h::l = [h]
       list_lcm (MAP (\k. n * k) [h])
     = list_lcm [n * h]                 by MAP
     = n * h                            by list_lcm_sing
     = n * list_lcm [h]                 by list_lcm_sing
     If l <> [],
       list_lcm (MAP (\k. n * k) (h::l))
     = list_lcm ((n * h) :: MAP (\k. n * k) l)      by MAP
     = lcm (n * h) (list_lcm (MAP (\k. n * k) l))   by list_lcm_cons
     = lcm (n * h) (n * list_lcm l)                 by induction hypothesis
     = n * (lcm h (list_lcm l))                     by LCM_COMMON_FACTOR
     = n * list_lcm (h::l)                          by list_lcm_cons
*)
val list_lcm_map_times = store_thm(
  "list_lcm_map_times",
  ``!n l. list_lcm (MAP (\k. n * k) l) = if l = [] then 1 else n * list_lcm l``,
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw_tac std_ss[LCM_COMMON_FACTOR, MAP, list_lcm_cons]);

(* Theorem: EVERY_POSITIVE l ==> 0 < list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> 0 < list_lcm []
     Note  EVERY_POSITIVE [] = T      by EVERY_DEF
     Since list_lcm [] = 1            by list_lcm_nil
     Hence true since 0 < 1           by SUC_POS, ONE.
   Step case: EVERY_POSITIVE l ==> 0 < list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> 0 < list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l              by EVERY_DEF
     Since list_lcm (h::l) = lcm h (list_lcm l)   by list_lcm_cons
       and 0 < list_lcm l                         by induction hypothesis
        so h <= lcm h (list_lcm l)                by LCM_LE, 0 < h.
     Hence 0 < list_lcm (h::l)                    by LESS_LESS_EQ_TRANS
*)
val list_lcm_pos = store_thm(
  "list_lcm_pos",
  ``!l. EVERY_POSITIVE l ==> 0 < list_lcm l``,
  Induct >-
  rw[] >>
  metis_tac[EVERY_DEF, list_lcm_cons, LCM_LE, LESS_LESS_EQ_TRANS]);

(* Theorem: POSITIVE l ==> 0 < list_lcm l *)
(* Proof: by list_lcm_pos, EVERY_MEM *)
val list_lcm_pos_alt = store_thm(
  "list_lcm_pos_alt",
  ``!l. POSITIVE l ==> 0 < list_lcm l``,
  rw[list_lcm_pos, EVERY_MEM]);

(* Theorem: EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l *)
(* Proof:
   By induction on l.
   Base case: EVERY_POSITIVE [] ==> SUM [] <= LENGTH [] * list_lcm []
     Note EVERY_POSITIVE [] = T      by EVERY_DEF
     Since SUM [] = 0                by SUM
       and LENGTH [] = 0             by LENGTH_NIL
     Hence true by MULT, as 0 <= 0   by LESS_EQ_REFL
   Step case: EVERY_POSITIVE l ==> SUM l <= LENGTH l * list_lcm l ==>
              !h. EVERY_POSITIVE (h::l) ==> SUM (h::l) <= LENGTH (h::l) * list_lcm (h::l)
     Note EVERY_POSITIVE (h::l)
      ==> 0 < h and EVERY_POSITIVE l          by EVERY_DEF
      ==> 0 < h and 0 < list_lcm l            by list_lcm_pos
     If l = [], LENGTH l = 0.
     SUM (h::[]) = SUM [h] = h                by SUM
       LENGTH (h::[]) * list_lcm (h::[])
     = 1 * list_lcm [h]                       by ONE
     = 1 * h                                  by list_lcm_sing
     = h                                      by MULT_LEFT_1
     If l <> [], LENGTH l <> 0                by LENGTH_NIL ... [1]
     SUM (h::l)
   = h + SUM l                                by SUM
   <= h + LENGTH l * list_lcm l               by induction hypothesis
   <= lcm h (list_lcm l) + LENGTH l * list_lcm l            by LCM_LE, 0 < h
   <= lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l))  by LCM_LE, 0 < list_lcm l, [1]
   = (1 + LENGTH l) * (lcm h (list_lcm l))    by RIGHT_ADD_DISTRIB
   = SUC (LENGTH l) * (lcm h (list_lcm l))    by SUC_ONE_ADD
   = LENGTH (h::l) * (lcm h (list_lcm l))     by LENGTH
   = LENGTH (h::l) * list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_lower_bound = store_thm(
  "list_lcm_lower_bound",
  ``!l. EVERY_POSITIVE l ==> SUM l <= (LENGTH l) * list_lcm l``,
  Induct >>
  rw[] >>
  Cases_on `l = []` >-
  rw[] >>
  `lcm h (list_lcm l) + LENGTH l * (lcm h (list_lcm l)) = SUC (LENGTH l) * (lcm h (list_lcm l))` by rw[RIGHT_ADD_DISTRIB, SUC_ONE_ADD] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < list_lcm l` by rw[list_lcm_pos] >>
  `h <= lcm h (list_lcm l) /\ list_lcm l <= lcm h (list_lcm l)` by rw[LCM_LE] >>
  `LENGTH l * list_lcm l <= LENGTH l * (lcm h (list_lcm l))` by rw[LE_MULT_LCANCEL] >>
  `h + SUM l <= h + LENGTH l * list_lcm l` by rw[] >>
  decide_tac);

(* Another version to eliminate EVERY by MEM. *)
val list_lcm_lower_bound_alt = save_thm("list_lcm_lower_bound_alt",
    list_lcm_lower_bound |> SIMP_RULE (srw_ss()) [EVERY_MEM]);
(* > list_lcm_lower_bound_alt;
val it = |- !l. POSITIVE l ==> SUM l <= LENGTH l * list_lcm l: thm
*)

(* Theorem: list_lcm l is a common multiple of its members.
            MEM x l ==> x divides (list_lcm l) *)
(* Proof:
   By induction on l.
   Base case: !x. MEM x [] ==> x divides (list_lcm [])
     True since MEM x [] = F     by MEM
   Step case: !x. MEM x l ==> x divides (list_lcm l) ==>
              !h x. MEM x (h::l) ==> x divides (list_lcm (h::l))
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     If x = h,
        divides h (lcm h (list_lcm l)) is true     by LCM_IS_LEAST_COMMON_MULTIPLE
     If MEM x l,
        x divides (list_lcm l)                     by induction hypothesis
        (list_lcm l) divides (lcm h (list_lcm l))  by LCM_IS_LEAST_COMMON_MULTIPLE
        Hence x divides (lcm h (list_lcm l))       by DIVIDES_TRANS
*)
val list_lcm_is_common_multiple = store_thm(
  "list_lcm_is_common_multiple",
  ``!x l. MEM x l ==> x divides (list_lcm l)``,
  Induct_on `l` >>
  rw[] >>
  metis_tac[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_TRANS]);

(* Theorem: If m is a common multiple of members of l, (list_lcm l) divides m.
           (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m *)
(* Proof:
   By induction on l.
   Base case: !m. (!x. MEM x [] ==> x divides m) ==> divides (list_lcm []) m
     Since list_lcm [] = 1       by list_lcm_nil
       and divides 1 m is true   by ONE_DIVIDES_ALL
   Step case: !m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m ==>
              !h m. (!x. MEM x (h::l) ==> x divides m) ==> divides (list_lcm (h::l)) m
     Note MEM x (h::l) <=> x = h, or MEM x l       by MEM
      and list_lcm (h::l) = lcm h (list_lcm l)     by list_lcm_cons
     Put x = h,   divides h m                      by MEM h (h::l) = T
     Put MEM x l, x divides m                      by MEM x (h::l) = T
         giving   (list_lcm l) divides m           by induction hypothesis
     Hence        divides (lcm h (list_lcm l)) m   by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_is_least_common_multiple = store_thm(
  "list_lcm_is_least_common_multiple",
  ``!l m. (!x. MEM x l ==> x divides m) ==> (list_lcm l) divides m``,
  Induct >-
  rw[] >>
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(*
> EVAL ``list_lcm []``;
val it = |- list_lcm [] = 1: thm
> EVAL ``list_lcm [1; 2; 3]``;
val it = |- list_lcm [1; 2; 3] = 6: thm
> EVAL ``list_lcm [1; 2; 3; 4; 5]``;
val it = |- list_lcm [1; 2; 3; 4; 5] = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5)``;
val it = |- list_lcm (GENLIST SUC 5) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 4)``;
val it = |- list_lcm (GENLIST SUC 4) = 12: thm
> EVAL ``lcm 5 (list_lcm (GENLIST SUC 4))``;
val it = |- lcm 5 (list_lcm (GENLIST SUC 4)) = 60: thm
> EVAL ``SNOC 5 (GENLIST SUC 4)``;
val it = |- SNOC 5 (GENLIST SUC 4) = [1; 2; 3; 4; 5]: thm
> EVAL ``list_lcm (SNOC 5 (GENLIST SUC 4))``;
val it = |- list_lcm (SNOC 5 (GENLIST SUC 4)) = 60: thm
> EVAL ``GENLIST (\k. leibniz 5 k) (SUC 5)``;
val it = |- GENLIST (\k. leibniz 5 k) (SUC 5) = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5)) = 60: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (\k. leibniz 5 k) (SUC 5))) <=> T: thm
> EVAL ``list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))``;
val it = |- (list_lcm (GENLIST SUC 5) = list_lcm (GENLIST (leibniz 5) (SUC 5))) <=> T: thm
*)

(* Theorem: list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) *)
(* Proof:
   By induction on l1.
   Base: !l2. list_lcm ([] ++ l2) = lcm (list_lcm []) (list_lcm l2)
      LHS = list_lcm ([] ++ l2)
          = list_lcm l2                      by APPEND
          = lcm 1 (list_lcm l2)              by LCM_1
          = lcm (list_lcm []) (list_lcm l2)  by list_lcm_nil
          = RHS
   Step:  !l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2) ==>
          !h l2. list_lcm (h::l1 ++ l2) = lcm (list_lcm (h::l1)) (list_lcm l2)
        list_lcm (h::l1 ++ l2)
      = list_lcm (h::(l1 ++ l2))                   by APPEND
      = lcm h (list_lcm (l1 ++ l2))                by list_lcm_cons
      = lcm h (lcm (list_lcm l1) (list_lcm l2))    by induction hypothesis
      = lcm (lcm h (list_lcm l1)) (list_lcm l2)    by LCM_ASSOC
      = lcm (list_lcm (h::l1)) (list_lcm l2)       by list_lcm_cons
*)
val list_lcm_append = store_thm(
  "list_lcm_append",
  ``!l1 l2. list_lcm (l1 ++ l2) = lcm (list_lcm l1) (list_lcm l2)``,
  Induct >-
  rw[] >>
  rw[LCM_ASSOC]);

(* Theorem: list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)] *)
(* Proof:
     list_lcm (l1 ++ l2 ++ l3)
   = lcm (list_lcm (l1 ++ l2)) (list_lcm l3)                    by list_lcm_append
   = lcm (lcm (list_lcm l1) (list_lcm l2)) (list_lcm l3)        by list_lcm_append
   = lcm (list_lcm l1) (lcm (list_lcm l2) (list_lcm l3))        by LCM_ASSOC
   = lcm (list_lcm l1) (list_lcm [(list_lcm l2); list_lcm l3])  by list_lcm_cons
   = list_lcm [list_lcm l1; list_lcm l2; list_lcm l3]           by list_lcm_cons
*)
val list_lcm_append_3 = store_thm(
  "list_lcm_append_3",
  ``!l1 l2 l3. list_lcm (l1 ++ l2 ++ l3) = list_lcm [(list_lcm l1); (list_lcm l2); (list_lcm l3)]``,
  rw[list_lcm_append, LCM_ASSOC, list_lcm_cons]);

(* Theorem: list_lcm (REVERSE l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (REVERSE []) = list_lcm []
       True since REVERSE [] = []          by REVERSE_DEF
   Step: list_lcm (REVERSE l) = list_lcm l ==>
         !h. list_lcm (REVERSE (h::l)) = list_lcm (h::l)
        list_lcm (REVERSE (h::l))
      = list_lcm (REVERSE l ++ [h])        by REVERSE_DEF
      = lcm (list_lcm (REVERSE l)) (list_lcm [h])   by list_lcm_append
      = lcm (list_lcm l) (list_lcm [h])             by induction hypothesis
      = lcm (list_lcm [h]) (list_lcm l)             by LCM_COMM
      = list_lcm ([h] ++ l)                         by list_lcm_append
      = list_lcm (h::l)                             by CONS_APPEND
*)
val list_lcm_reverse = store_thm(
  "list_lcm_reverse",
  ``!l. list_lcm (REVERSE l) = list_lcm l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `list_lcm (REVERSE (h::l)) = list_lcm (REVERSE l ++ [h])` by rw[] >>
  `_ = lcm (list_lcm (REVERSE l)) (list_lcm [h])` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm l) (list_lcm [h])` by rw[] >>
  `_ = lcm (list_lcm [h]) (list_lcm l)` by rw[LCM_COMM] >>
  `_ = list_lcm ([h] ++ l)` by rw[list_lcm_append] >>
  `_ = list_lcm (h::l)` by rw[] >>
  decide_tac);

(* Theorem: list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])) *)
(* Proof:
     list_lcm [1 .. (n + 1)]
   = list_lcm (SONC (n + 1) [1 .. n])   by listRangeINC_SNOC, 1 <= n + 1
   = lcm (n + 1) (list_lcm [1 .. n])    by list_lcm_snoc
*)
val list_lcm_suc = store_thm(
  "list_lcm_suc",
  ``!n. list_lcm [1 .. (n + 1)] = lcm (n + 1) (list_lcm [1 .. n])``,
  rw[listRangeINC_SNOC, list_lcm_snoc]);

(* Theorem: l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower = store_thm(
  "list_lcm_nonempty_lower",
  ``!l. l <> [] /\ EVERY_POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l *)
(* Proof:
   Note LENGTH l <> 0                           by LENGTH_NIL
    and SUM l <= LENGTH l * list_lcm l          by list_lcm_lower_bound_alt
     so (SUM l) DIV (LENGTH l) <= list_lcm l    by DIV_LE
*)
val list_lcm_nonempty_lower_alt = store_thm(
  "list_lcm_nonempty_lower_alt",
  ``!l. l <> [] /\ POSITIVE l ==> (SUM l) DIV (LENGTH l) <= list_lcm l``,
  metis_tac[list_lcm_lower_bound_alt, DIV_LE, LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* Theorem: MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note x divides (list_lcm l)          by list_lcm_is_common_multiple
    and y divides (list_lcm l)          by list_lcm_is_common_multiple
    ==> (lcm x y) divides (list_lcm l)  by LCM_IS_LEAST_COMMON_MULTIPLE
*)
val list_lcm_divisor_lcm_pair = store_thm(
  "list_lcm_divisor_lcm_pair",
  ``!l x y. MEM x l /\ MEM y l ==> (lcm x y) divides list_lcm l``,
  rw[list_lcm_is_common_multiple, LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l *)
(* Proof:
   Note (lcm x y) divides (list_lcm l)  by list_lcm_divisor_lcm_pair
    Now 0 < list_lcm l                  by list_lcm_pos_alt
   Thus (lcm x y) <= list_lcm l         by DIVIDES_LE
*)
val list_lcm_lower_by_lcm_pair = store_thm(
  "list_lcm_lower_by_lcm_pair",
  ``!l x y. POSITIVE l /\ MEM x l /\ MEM y l ==> (lcm x y) <= list_lcm l``,
  rw[list_lcm_divisor_lcm_pair, list_lcm_pos_alt, DIVIDES_LE]);

(* Theorem: 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m *)
(* Proof:
   Note list_lcm l divides m     by list_lcm_is_least_common_multiple
   Thus list_lcm l <= m          by DIVIDES_LE, 0 < m
*)
val list_lcm_upper_by_common_multiple = store_thm(
  "list_lcm_upper_by_common_multiple",
  ``!l m. 0 < m /\ (!x. MEM x l ==> x divides m) ==> list_lcm l <= m``,
  rw[list_lcm_is_least_common_multiple, DIVIDES_LE]);

(* Theorem: list_lcm ls = FOLDR lcm 1 ls *)
(* Proof:
   By induction on ls.
   Base: list_lcm [] = FOLDR lcm 1 []
         list_lcm []
       = 1                        by list_lcm_nil
       = FOLDR lcm 1 []           by FOLDR
   Step: list_lcm ls = FOLDR lcm 1 ls ==>
         !h. list_lcm (h::ls) = FOLDR lcm 1 (h::ls)
         list_lcm (h::ls)
       = lcm h (list_lcm ls)      by list_lcm_def
       = lcm h (FOLDR lcm 1 ls)   by induction hypothesis
       = FOLDR lcm 1 (h::ls)      by FOLDR
*)
val list_lcm_by_FOLDR = store_thm(
  "list_lcm_by_FOLDR",
  ``!ls. list_lcm ls = FOLDR lcm 1 ls``,
  Induct >> rw[]);

(* Theorem: list_lcm ls = FOLDL lcm 1 ls *)
(* Proof:
   Note COMM lcm  since !x y. lcm x y = lcm y x                    by LCM_COMM
    and ASSOC lcm since !x y z. lcm x (lcm y z) = lcm (lcm x y) z  by LCM_ASSOC
    Now list_lcm ls
      = FOLDR lcm 1 ls          by list_lcm_by FOLDR
      = FOLDL lcm 1 ls          by FOLDL_EQ_FOLDR, COMM lcm, ASSOC lcm
*)
val list_lcm_by_FOLDL = store_thm(
  "list_lcm_by_FOLDL",
  ``!ls. list_lcm ls = FOLDL lcm 1 ls``,
  simp[list_lcm_by_FOLDR] >>
  irule (GSYM FOLDL_EQ_FOLDR) >>
  rpt strip_tac >-
  rw[LCM_ASSOC, combinTheory.ASSOC_DEF] >>
  rw[LCM_COMM, combinTheory.COMM_DEF]);

(* ------------------------------------------------------------------------- *)
(* Lists in Leibniz Triangle                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Vertical Lists in Leibniz Triangle                                        *)
(* ------------------------------------------------------------------------- *)

(* Define Vertical List in Leibniz Triangle *)
(*
val leibniz_vertical_def = Define `
  leibniz_vertical n = GENLIST SUC (SUC n)
`;

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. GENLIST ((+) 1) (n + 1)``);
*)

(* Define Vertical (downward list) in Leibniz Triangle *)

(* Use overloading for leibniz_vertical n. *)
val _ = overload_on("leibniz_vertical", ``\n. [1 .. (n+1)]``);

(* Theorem: leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1) *)
(* Proof:
     leibniz_vertical n
   = [1 .. (n+1)]                        by notation
   = GENLIST (\i. 1 + i) (n+1 + 1 - 1)   by listRangeINC_def
   = GENLIST (\i. 1 + i) (n + 1)         by arithmetic
*)
val leibniz_vertical_alt = store_thm(
  "leibniz_vertical_alt",
  ``!n. leibniz_vertical n = GENLIST (\i. 1 + i) (n + 1)``,
  rw[listRangeINC_def]);

(* Theorem: leibniz_vertical 0 = [1] *)
(* Proof:
     leibniz_vertical 0
   = [1 .. (0+1)]         by notation
   = [1 .. 1]             by arithmetic
   = [1]                  by listRangeINC_SING
*)
val leibniz_vertical_0 = store_thm(
  "leibniz_vertical_0",
  ``leibniz_vertical 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_vertical n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_vertical n)
   = LENGTH [1 .. (n+1)]             by notation
   = n + 1 + 1 - 1                   by listRangeINC_LEN
   = n + 1                           by arithmetic
*)
val leibniz_vertical_len = store_thm(
  "leibniz_vertical_len",
  ``!n. LENGTH (leibniz_vertical n) = n + 1``,
  rw[listRangeINC_LEN]);

(* Theorem: leibniz_vertical n <> [] *)
(* Proof:
      LENGTH (leibniz_vertical n)
    = n + 1                         by leibniz_vertical_len
    <> 0                            by ADD1, SUC_NOT_ZERO
    Thus leibniz_vertical n <> []   by LENGTH_EQ_0
*)
val leibniz_vertical_not_nil = store_thm(
  "leibniz_vertical_not_nil",
  ``!n. leibniz_vertical n <> []``,
  metis_tac[leibniz_vertical_len, LENGTH_EQ_0, DECIDE``!n. n + 1 <> 0``]);

(* Theorem: EVERY_POSITIVE (leibniz_vertical n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_vertical n)
   <=> EVERY_POSITIVE GENLIST (\i. 1 + i) (n+1)   by leibniz_vertical_alt
   <=> !i. i < n + 1 ==> 0 < 1 + i                by EVERY_GENLIST
   <=> !i. i < n + 1 ==> T                        by arithmetic
   <=> T
*)
val leibniz_vertical_pos = store_thm(
  "leibniz_vertical_pos",
  ``!n. EVERY_POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_alt, EVERY_GENLIST]);

(* Theorem: POSITIVE (leibniz_vertical n) *)
(* Proof: by leibniz_vertical_pos, EVERY_MEM *)
val leibniz_vertical_pos_alt = store_thm(
  "leibniz_vertical_pos_alt",
  ``!n. POSITIVE (leibniz_vertical n)``,
  rw[leibniz_vertical_pos, EVERY_MEM]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n) *)
(* Proof:
   Note: (leibniz_vertical n) has 1 to (n+1), inclusive:
       MEM x (leibniz_vertical n)
   <=> MEM x [1 .. (n+1)]              by notation
   <=> 1 <= x /\ x <= n + 1            by listRangeINC_MEM
   <=> 0 < x /\ x <= n + 1             by num_CASES, LESS_EQ_MONO
*)
val leibniz_vertical_mem = store_thm(
  "leibniz_vertical_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_vertical n)``,
  rw[]);

(* Theorem: leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n) *)
(* Proof:
     leibniz_vertical (n + 1)
   = [1 .. (n+1 +1)]                     by notation
   = SNOC (n+1 + 1) [1 .. (n+1)]         by listRangeINC_SNOC
   = SNOC (n + 2) (leibniz_vertical n)   by notation
*)
val leibniz_vertical_snoc = store_thm(
  "leibniz_vertical_snoc",
  ``!n. leibniz_vertical (n + 1) = SNOC (n + 2) (leibniz_vertical n)``,
  rw[listRangeINC_SNOC]);;

(* Use overloading for leibniz_up n. *)
val _ = overload_on("leibniz_up", ``\n. REVERSE (leibniz_vertical n)``);

(* Theorem: leibniz_up 0 = [1] *)
(* Proof:
     leibniz_up 0
   = REVERSE (leibniz_vertical 0)  by notation
   = REVERSE [1]                   by leibniz_vertical_0
   = [1]                           by REVERSE_SING
*)
val leibniz_up_0 = store_thm(
  "leibniz_up_0",
  ``leibniz_up 0 = [1]``,
  rw[]);

(* Theorem: LENGTH (leibniz_up n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_up n)
   = LENGTH (REVERSE (leibniz_vertical n))   by notation
   = LENGTH (leibniz_vertical n)             by LENGTH_REVERSE
   = n + 1                                   by leibniz_vertical_len
*)
val leibniz_up_len = store_thm(
  "leibniz_up_len",
  ``!n. LENGTH (leibniz_up n) = n + 1``,
  rw[leibniz_vertical_len]);

(* Theorem: EVERY_POSITIVE (leibniz_up n) *)
(* Proof:
       EVERY_POSITIVE (leibniz_up n)
   <=> EVERY_POSITIVE (REVERSE (leibniz_vertical n))   by notation
   <=> EVERY_POSITIVE (leibniz_vertical n)             by EVERY_REVERSE
   <=> T                                               by leibniz_vertical_pos
*)
val leibniz_up_pos = store_thm(
  "leibniz_up_pos",
  ``!n. EVERY_POSITIVE (leibniz_up n)``,
  rw[leibniz_vertical_pos, EVERY_REVERSE]);

(* Theorem: 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n) *)
(* Proof:
   Note: (leibniz_up n) has (n+1) downto 1, inclusive:
       MEM x (leibniz_up n)
   <=> MEM x (REVERSE (leibniz_vertical n))     by notation
   <=> MEM x (leibniz_vertical n)               by MEM_REVERSE
   <=> T                                        by leibniz_vertical_mem
*)
val leibniz_up_mem = store_thm(
  "leibniz_up_mem",
  ``!n x. 0 < x /\ x <= (n + 1) <=> MEM x (leibniz_up n)``,
  rw[]);

(* Theorem: leibniz_up (n + 1) = (n + 2) :: (leibniz_up n) *)
(* Proof:
     leibniz_up (n + 1)
   = REVERSE (leibniz_vertical (n + 1))            by notation
   = REVERSE (SNOC (n + 2) (leibniz_vertical n))   by leibniz_vertical_snoc
   = (n + 2) :: (leibniz_up n)                     by REVERSE_SNOC
*)
val leibniz_up_cons = store_thm(
  "leibniz_up_cons",
  ``!n. leibniz_up (n + 1) = (n + 2) :: (leibniz_up n)``,
  rw[leibniz_vertical_snoc, REVERSE_SNOC]);

(* ------------------------------------------------------------------------- *)
(* Horizontal List in Leibniz Triangle                                       *)
(* ------------------------------------------------------------------------- *)

(* Define row (horizontal list) in Leibniz Triangle *)
(*
val leibniz_horizontal_def = Define `
  leibniz_horizontal n = GENLIST (leibniz n) (SUC n)
`;

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);
*)

(* Use overloading for leibniz_horizontal n. *)
val _ = overload_on("leibniz_horizontal", ``\n. GENLIST (leibniz n) (n + 1)``);

(*
> EVAL ``leibniz_horizontal 0``;
val it = |- leibniz_horizontal 0 = [1]: thm
> EVAL ``leibniz_horizontal 1``;
val it = |- leibniz_horizontal 1 = [2; 2]: thm
> EVAL ``leibniz_horizontal 2``;
val it = |- leibniz_horizontal 2 = [3; 6; 3]: thm
> EVAL ``leibniz_horizontal 3``;
val it = |- leibniz_horizontal 3 = [4; 12; 12; 4]: thm
> EVAL ``leibniz_horizontal 4``;
val it = |- leibniz_horizontal 4 = [5; 20; 30; 20; 5]: thm
> EVAL ``leibniz_horizontal 5``;
val it = |- leibniz_horizontal 5 = [6; 30; 60; 60; 30; 6]: thm
> EVAL ``leibniz_horizontal 6``;
val it = |- leibniz_horizontal 6 = [7; 42; 105; 140; 105; 42; 7]: thm
> EVAL ``leibniz_horizontal 7``;
val it = |- leibniz_horizontal 7 = [8; 56; 168; 280; 280; 168; 56; 8]: thm
> EVAL ``leibniz_horizontal 8``;
val it = |- leibniz_horizontal 8 = [9; 72; 252; 504; 630; 504; 252; 72; 9]: thm
*)

(* Theorem: leibniz_horizontal 0 = [1] *)
(* Proof:
     leibniz_horizontal 0
   = GENLIST (leibniz 0) (0 + 1)    by notation
   = GENLIST (leibniz 0) 1          by arithmetic
   = [leibniz 0 0]                  by GENLIST
   = [1]                            by leibniz_n_0
*)
val leibniz_horizontal_0 = store_thm(
  "leibniz_horizontal_0",
  ``leibniz_horizontal 0 = [1]``,
  rw_tac std_ss[GENLIST_1, leibniz_n_0]);

(* Theorem: LENGTH (leibniz_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (leibniz_horizontal n)
   = LENGTH (GENLIST (leibniz n) (n + 1))   by notation
   = n + 1                                  by LENGTH_GENLIST
*)
val leibniz_horizontal_len = store_thm(
  "leibniz_horizontal_len",
  ``!n. LENGTH (leibniz_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k <= n ==> EL k (leibniz_horizontal n) = leibniz n k *)
(* Proof:
   Note k <= n means k < SUC n.
     EL k (leibniz_horizontal n)
   = EL k (GENLIST (leibniz n) (n + 1))   by notation
   = EL k (GENLIST (leibniz n) (SUC n))   by ADD1
   = leibniz n k                          by EL_GENLIST, k < SUC n.
*)
val leibniz_horizontal_el = store_thm(
  "leibniz_horizontal_el",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[LESS_EQ_IMP_LESS_SUC]);

(* Theorem: k <= n ==> MEM (leibniz n k) (leibniz_horizontal n) *)
(* Proof:
   Note k <= n ==> k < (n + 1)
   Thus MEM (leibniz n k) (GENLIST (leibniz n) (n + 1))        by MEM_GENLIST
     or MEM (leibniz n k) (leibniz_horizontal n)               by notation
*)
val leibniz_horizontal_mem = store_thm(
  "leibniz_horizontal_mem",
  ``!n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)``,
  metis_tac[MEM_GENLIST, DECIDE``k <= n ==> k < n + 1``]);

(* Theorem: MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n *)
(* Proof:
   If part: (leibniz n k) (leibniz_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then leibniz n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = leibniz n m    by MEM_GENLIST
        or m <= n ==> leibniz n m = 0           by m < n + 1
       Yet leibniz n m <> 0                     by leibniz_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> (leibniz n k) (leibniz_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (leibniz n k = leibniz n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val leibniz_horizontal_mem_iff = store_thm(
  "leibniz_horizontal_mem_iff",
  ``!n k. MEM (leibniz n k) (leibniz_horizontal n) <=> k <= n``,
  rw_tac bool_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `leibniz n k = 0` by rw[leibniz_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = (n + 1) * binomial n m)) <=> ?k. k <= n /\ (x = (n + 1) * binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val leibniz_horizontal_member = store_thm(
  "leibniz_horizontal_member",
  ``!n x. MEM x (leibniz_horizontal n) <=> ?k. k <= n /\ (x = leibniz n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k) *)
(* Proof: by EL_GENLIST *)
val leibniz_horizontal_element = store_thm(
  "leibniz_horizontal_element",
  ``!n k. k <= n ==> (EL k (leibniz_horizontal n) = leibniz n k)``,
  rw[EL_GENLIST]);

(* Theorem: TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2] *)
(* Proof:
     TAKE 1 (leibniz_horizontal (n + 1))
   = TAKE 1 (GENLIST (leibniz (n + 1)) (n + 1 + 1))                      by notation
   = TAKE 1 (GENLIST (leibniz (SUC n)) (SUC (SUC n)))                    by ADD1
   = TAKE 1 ((leibniz (SUC n) 0) :: GENLIST ((leibniz (SUC n)) o SUC) n) by GENLIST_CONS
   = (leibniz (SUC n) 0):: TAKE 0 (GENLIST ((leibniz (SUC n)) o SUC) n)  by TAKE_def
   = [leibniz (SUC n) 0]:: []                                            by TAKE_0
   = [SUC n + 1]                                                         by leibniz_n_0
   = [n + 2]                                                             by ADD1
*)
val leibniz_horizontal_head = store_thm(
  "leibniz_horizontal_head",
  ``!n. TAKE 1 (leibniz_horizontal (n + 1)) = [n + 2]``,
  rpt strip_tac >>
  `(!n. n + 1 = SUC n) /\ (!n. n + 2 = SUC (SUC n))` by decide_tac >>
  rw[GENLIST_CONS, leibniz_n_0]);

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note MEM (leibniz n k) (leibniz_horizontal n)                by leibniz_horizontal_mem
     so (leibniz n k) divides list_lcm (leibniz_horizontal n)   by list_lcm_is_common_multiple
*)
val leibniz_horizontal_divisor = store_thm(
  "leibniz_horizontal_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_horizontal n)``,
  rw[leibniz_horizontal_mem, list_lcm_is_common_multiple]);

(* Theorem: EVERY_POSITIVE (leibniz_horizontal n) *)
(* Proof:
   Let l = leibniz_horizontal n
   Then LENGTH l = n + 1                     by leibniz_horizontal_len
       EVERY_POSITIVE l
   <=> !k. k < LENGTH l ==> 0 < (EL k l)     by EVERY_EL
   <=> !k. k < n + 1 ==> 0 < (EL k l)        by above
   <=> !k. k <= n ==> 0 < EL k l             by arithmetic
   <=> !k. k <= n ==> 0 < leibniz n k        by leibniz_horizontal_el
   <=> T                                     by leibniz_pos
*)
Theorem leibniz_horizontal_pos:
  !n. EVERY_POSITIVE (leibniz_horizontal n)
Proof
  simp[EVERY_EL, binomial_pos]
QED

(* Theorem: POSITIVE (leibniz_horizontal n) *)
(* Proof: by leibniz_horizontal_pos, EVERY_MEM *)
val leibniz_horizontal_pos_alt = store_thm(
  "leibniz_horizontal_pos_alt",
  ``!n. POSITIVE (leibniz_horizontal n)``,
  metis_tac[leibniz_horizontal_pos, EVERY_MEM]);

(* Theorem: leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n) *)
(* Proof:
     leibniz_horizontal n
   = GENLIST (leibniz n) (n + 1)                          by notation
   = GENLIST ((\j. (n + 1) * j) o (binomial n)) (n + 1)   by leibniz_alt
   = MAP (\j. (n + 1) * j) (GENLIST (binomial n) (n + 1)) by MAP_GENLIST
   = MAP (\j. (n + 1) * j) (binomial_horizontal n)        by notation
*)
val leibniz_horizontal_alt = store_thm(
  "leibniz_horizontal_alt",
  ``!n. leibniz_horizontal n = MAP (\j. (n+1) * j) (binomial_horizontal n)``,
  rw_tac std_ss[leibniz_alt, MAP_GENLIST]);

(* Theorem: list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n) *)
(* Proof:
   Since LENGTH (binomial_horizontal n) = n + 1             by binomial_horizontal_len
         binomial_horizontal n <> []                        by LENGTH_NIL ... [1]
     list_lcm (leibniz_horizontal n)
   = list_lcm (MAP (\j (n+1) * j) (binomial_horizontal n))  by leibniz_horizontal_alt
   = (n + 1) * list_lcm (binomial_horizontal n)             by list_lcm_map_times, [1]
*)
val leibniz_horizontal_lcm_alt = store_thm(
  "leibniz_horizontal_lcm_alt",
  ``!n. list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `n + 1 <> 0` by decide_tac >>
  `binomial_horizontal n <> []` by metis_tac[LENGTH_NIL] >>
  rw_tac std_ss[leibniz_horizontal_alt, list_lcm_map_times]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n) *)
(* Proof:
     SUM (leibniz_horizontal n)
   = SUM (MAP (\j. (n + 1) * j) (binomial_horizontal n))   by leibniz_horizontal_alt
   = (n + 1) * SUM (binomial_horizontal n)                 by SUM_MULT
*)
val leibniz_horizontal_sum = store_thm(
  "leibniz_horizontal_sum",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * SUM (binomial_horizontal n)``,
  rw[leibniz_horizontal_alt, SUM_MULT] >>
  `(\j. j * (n + 1)) = $* (n + 1)` by rw[FUN_EQ_THM] >>
  rw[]);

(* Theorem: SUM (leibniz_horizontal n) = (n + 1) * 2 ** n *)
(* Proof:
     SUM (leibniz_horizontal n)
   = (n + 1) * SUM (binomial_horizontal n)       by leibniz_horizontal_sum
   = (n + 1) * 2 ** n                            by binomial_horizontal_sum
*)
val leibniz_horizontal_sum_eqn = store_thm(
  "leibniz_horizontal_sum_eqn",
  ``!n. SUM (leibniz_horizontal n) = (n + 1) * 2 ** n``,
  rw[leibniz_horizontal_sum, binomial_horizontal_sum]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n) *)
(* Proof:
   Note LENGTH (leibniz_horizontal n) = n + 1    by leibniz_horizontal_len
     so 0 < LENGTH (leibniz_horizontal n)        by 0 < n + 1

        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = ((n + 1) * SUM (binomial_horizontal n))  DIV (n + 1)     by leibniz_horizontal_sum
      = SUM (binomial_horizontal n)                              by MULT_TO_DIV, 0 < n + 1
*)
val leibniz_horizontal_average = store_thm(
  "leibniz_horizontal_average",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = SUM (binomial_horizontal n)``,
  metis_tac[leibniz_horizontal_sum, leibniz_horizontal_len, MULT_TO_DIV, DECIDE``0 < n + 1``]);

(* Theorem: SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n *)
(* Proof:
        SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n)
      = SUM (binomial_horizontal n)    by leibniz_horizontal_average
      = 2 ** n                         by binomial_horizontal_sum
*)
val leibniz_horizontal_average_eqn = store_thm(
  "leibniz_horizontal_average_eqn",
  ``!n. SUM (leibniz_horizontal n) DIV LENGTH (leibniz_horizontal n) = 2 ** n``,
  rw[leibniz_horizontal_average, binomial_horizontal_sum]);

(* ------------------------------------------------------------------------- *)
(* Transform from Vertical LCM to Horizontal LCM.                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Using Triplet and Paths                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define a triple type *)
val _ = Hol_datatype`
  triple = <| a: num;
              b: num;
              c: num
            |>
`;

(* A triplet is a triple composed of Leibniz node and children. *)
val triplet_def = Define`
    (triplet n k):triple =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
         |>
`;

(* can even do this after definition of triple type:

val triple_def = Define`
    triple n k =
        <| a := leibniz n k;
           b := leibniz (n + 1) k;
           c := leibniz (n + 1) (k + 1)
          |>
`;
*)

(* Overload elements of a triplet *)
(*
val _ = overload_on("tri_a", ``leibniz n k``);
val _ = overload_on("tri_b", ``leibniz (SUC n) k``);
val _ = overload_on("tri_c", ``leibniz (SUC n) (SUC k)``);

val _ = overload_on("tri_a", ``(triple n k).a``);
val _ = overload_on("tri_b", ``(triple n k).b``);
val _ = overload_on("tri_c", ``(triple n k).c``);
*)
val _ = temp_overload_on("ta", ``(triplet n k).a``);
val _ = temp_overload_on("tb", ``(triplet n k).b``);
val _ = temp_overload_on("tc", ``(triplet n k).c``);

(* Theorem: (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1)) *)
(* Proof: by triplet_def *)
val leibniz_triplet_member = store_thm(
  "leibniz_triplet_member",
  ``!n k. (ta = leibniz n k) /\ (tb = leibniz (n + 1) k) /\ (tc = leibniz (n + 1) (k + 1))``,
  rw[triplet_def]);

(* Theorem: (k + 1) * tc = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_right_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (k + 1) * leibniz (n + 1) (k + 1) = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_right_entry = store_thm(
  "leibniz_right_entry",
  ``!(n k):num. (k + 1) * tc = (n + 1 - k) * tb``,
  rw_tac arith_ss[triplet_def, leibniz_right_eqn]);

(* Theorem: (n + 2) * ta = (n + 1 - k) * tb *)
(* Proof:
   Apply: > leibniz_up_eqn |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. (n + 1 + 1) * leibniz (n + 1 - 1) k = (n + 1 - k) * leibniz (n + 1) k: thm
*)
val leibniz_up_entry = store_thm(
  "leibniz_up_entry",
  ``!(n k):num. (n + 2) * ta = (n + 1 - k) * tb``,
  rw_tac std_ss[triplet_def, leibniz_up_eqn |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   Apply > leibniz_property |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==> !k. !k. leibniz (n + 1) k * leibniz (n + 1 - 1) k =
     leibniz (n + 1) (k + 1) * (leibniz (n + 1) k - leibniz (n + 1 - 1) k): thm
*)
val leibniz_triplet_property = store_thm(
  "leibniz_triplet_property",
  ``!(n k):num. ta * tb = tc * (tb - ta)``,
  rw_tac std_ss[triplet_def, MULT_COMM, leibniz_property |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* Direct proof of same result, for the paper. *)

(* Theorem: ta * tb = tc * (tb - ta) *)
(* Proof:
   If n < k,
      Note n < k ==> ta = 0               by triplet_def, leibniz_less_0
      also n + 1 < k + 1 ==> tc = 0       by triplet_def, leibniz_less_0
      Thus ta * tb = 0 = tc * (tb - ta)   by MULT_EQ_0
   If ~(n < k),
      Then (n + 2) - (n + 1 - k) = k + 1  by arithmetic, k <= n.

        (k + 1) * ta * tb
      = (n + 2 - (n + 1 - k)) * ta * tb
      = (n + 2) * ta * tb - (n + 1 - k) * ta * tb         by RIGHT_SUB_DISTRIB
      = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb     by leibniz_up_entry
      = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta     by MULT_ASSOC, MULT_COMM
      = (n + 1 - k) * tb * (tb - ta)                      by LEFT_SUB_DISTRIB
      = (k + 1) * tc * (tb - ta)                          by leibniz_right_entry

      Since k + 1 <> 0, the result follows                by MULT_LEFT_CANCEL
*)
Theorem leibniz_triplet_property[allow_rebind]:
  !n k:num. ta * tb = tc * (tb - ta)
Proof
  rpt strip_tac >>
  Cases_on ‘n < k’ >-
  rw[triplet_def, leibniz_less_0] >>
  ‘(n + 2) - (n + 1 - k) = k + 1’ by decide_tac >>
  ‘(k + 1) * ta * tb = (n + 2 - (n + 1 - k)) * ta * tb’ by rw[] >>
  ‘_ = (n + 2) * ta * tb - (n + 1 - k) * ta * tb’ by rw_tac std_ss[RIGHT_SUB_DISTRIB] >>
  ‘_ = (n + 1 - k) * tb * tb - (n + 1 - k) * ta * tb’ by rw_tac std_ss[leibniz_up_entry] >>
  ‘_ = (n + 1 - k) * tb * tb - (n + 1 - k) * tb * ta’ by metis_tac[MULT_ASSOC, MULT_COMM] >>
  ‘_ = (n + 1 - k) * tb * (tb - ta)’ by rw_tac std_ss[LEFT_SUB_DISTRIB] >>
  ‘_ = (k + 1) * tc * (tb - ta)’ by rw_tac std_ss[leibniz_right_entry] >>
  ‘k + 1 <> 0’ by decide_tac >>
  metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC]
QED

(* Theorem: lcm tb ta = lcm tb tc *)
(* Proof:
   Apply: > leibniz_lcm_exchange |> SPEC ``n+1``;
   val it = |- 0 < n + 1 ==>
            !k. lcm (leibniz (n + 1) k) (leibniz (n + 1 - 1) k) =
                lcm (leibniz (n + 1) k) (leibniz (n + 1) (k + 1)): thm
*)
val leibniz_triplet_lcm = store_thm(
  "leibniz_triplet_lcm",
  ``!(n k):num. lcm tb ta = lcm tb tc``,
  rw_tac std_ss[triplet_def, leibniz_lcm_exchange |> SPEC ``n+1`` |> SIMP_RULE arith_ss[]]);

(* ------------------------------------------------------------------------- *)
(* Zigzag Path in Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Define a path type *)
val _ = temp_type_abbrev("path", Type `:num list`);

(* Define paths reachable by one zigzag *)
val leibniz_zigzag_def = Define`
    leibniz_zigzag (p1: path) (p2: path) <=>
    ?(n k):num (x y):path. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)
`;
val _ = overload_on("zigzag", ``leibniz_zigzag``);
val _ = set_fixity "zigzag" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   Given p1 zigzag p2,
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

     list_lcm p1
   = list_lcm (x ++ [tb; ta] ++ y)                      by above
   = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)        by list_lcm_append
   = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)      by APPEND_ASSOC
   = lcm (lcm (list_lcm x) (list_lcm ([tb; ta]))) (list_lcm y)   by list_lcm_append
   = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)    by list_lcm_append, list_lcm_sing
   = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)    by leibniz_triplet_lcm
   = lcm (lcm (list_lcm x) (list_lcm ([tb; tc]))) (list_lcm y)   by list_lcm_append, list_lcm_sing
   = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)      by list_lcm_append
   = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)        by APPEND_ASSOC
   = list_lcm (x ++ [tb; tc] ++ y)                      by list_lcm_append
   = list_lcm p2                                        by above
*)
val list_lcm_zigzag = store_thm(
  "list_lcm_zigzag",
  ``!p1 p2. p1 zigzag p2 ==> (list_lcm p1 = list_lcm p2)``,
  rw_tac std_ss[leibniz_zigzag_def] >>
  `list_lcm (x ++ [tb; ta] ++ y) = lcm (list_lcm (x ++ [tb; ta])) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ ([tb; ta]))) (list_lcm y)` by rw[] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb ta)) (list_lcm y)` by rw[list_lcm_append] >>
  `_ = lcm (lcm (list_lcm x) (lcm tb tc)) (list_lcm y)` by rw[leibniz_triplet_lcm] >>
  `_ = lcm (list_lcm (x ++ ([tb; tc]))) (list_lcm y)`  by rw[list_lcm_append] >>
  `_ = lcm (list_lcm (x ++ [tb; tc])) (list_lcm y)` by rw[] >>
  `_ = list_lcm (x ++ [tb; tc] ++ y)` by rw[list_lcm_append] >>
  rw[]);

(* Theorem: p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2) *)
(* Proof:
   Since p1 zigzag p2
     ==> ?n k x y. (p1 = x ++ [tb; ta] ++ y) /\ (p2 = x ++ [tb; tc] ++ y)  by leibniz_zigzag_def

      [x] ++ p1
    = [x] ++ (x ++ [tb; ta] ++ y)        by above
    = [x] ++ x ++ [tb; ta] ++ y          by APPEND
      [x] ++ p2
    = [x] ++ (x ++ [tb; tc] ++ y)        by above
    = [x] ++ x ++ [tb; tc] ++ y          by APPEND
   Take new x = [x] ++ x, new y = y.
   Then ([x] ++ p1) zigzag ([x] ++ p2)   by leibniz_zigzag_def
*)
val leibniz_zigzag_tail = store_thm(
  "leibniz_zigzag_tail",
  ``!p1 p2. p1 zigzag p2 ==> !x. ([x] ++ p1) zigzag ([x] ++ p2)``,
  metis_tac[leibniz_zigzag_def, APPEND]);

(* Theorem: k <= n ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
            TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_horizontal (n + 1)),

    Let x = TAKE k (leibniz_horizontal (n + 1))
    and y = DROP (k + 1) (leibniz_horizontal n)
        TAKE (k + 1) (leibniz_horizontal (n + 1))
      = TAKE (SUC k) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tb x                                   by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb]                                   by SNOC_APPEND
        TAKE (k + 2) (leibniz_horizontal (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_horizontal (SUC n))   by ADD1
      = SNOC tc (SNOC tb x)                         by TAKE_SUC_BY_TAKE, k + 1 < LENGTH (leibniz_horizontal (n + 1))
      = x ++ [tb; tc]                               by SNOC_APPEND
        DROP k (leibniz_horizontal n)
      = ta :: y                                     by DROP_BY_DROP_SUC, k < LENGTH (leibniz_horizontal n)
      = [ta] ++ y                                   by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
           = x ++ [tb] ++ [ta] ++ y
           = x ++ [tb; ta] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
           = x ++ [tb; tc] ++ y
   Therefore p1 zigzag p2                           by leibniz_zigzag_def
*)
val leibniz_horizontal_zigzag = store_thm(
  "leibniz_horizontal_zigzag",
  ``!n k. k <= n ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) zigzag
                    TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_horizontal (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_horizontal n)` >>
  `k <= n + 1` by decide_tac >>
  `EL k (leibniz_horizontal n) = ta` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL k (leibniz_horizontal (n + 1)) = tb` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `EL (k + 1) (leibniz_horizontal (n + 1)) = tc` by rw_tac std_ss[triplet_def, leibniz_horizontal_el] >>
  `k < n + 1` by decide_tac >>
  `k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 1) (leibniz_horizontal (n + 1)) = TAKE (SUC k) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tb x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [tb]` by rw[] >>
  `SUC k < n + 2` by decide_tac >>
  `SUC k < LENGTH (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_len] >>
  `TAKE (k + 2) (leibniz_horizontal (n + 1)) = TAKE (SUC (SUC k)) (leibniz_horizontal (n + 1))` by rw[ADD1] >>
  `_ = SNOC tc (SNOC tb x)` by rw_tac std_ss[TAKE_SUC_BY_TAKE, ADD1, Abbr`x`] >>
  `_ = x ++ [tb; tc]` by rw[] >>
  `DROP k (leibniz_horizontal n) = [ta] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ y` >>
  `p1 = x ++ [tb; ta] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [tb; tc] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: (leibniz_up 1) zigzag (leibniz_horizontal 1) *)
(* Proof:
   Since leibniz_up 1
       = [2; 1]                  by EVAL_TAC
       = [] ++ [2; 1] ++ []      by EVAL_TAC
     and leibniz_horizontal 1
       = [2; 2]                  by EVAL_TAC
       = [] ++ [2; 2] ++ []      by EVAL_TAC
     Now the first Leibniz triplet is:
         (triplet 0 0).a = 1     by EVAL_TAC
         (triplet 0 0).b = 2     by EVAL_TAC
         (triplet 0 0).c = 2     by EVAL_TAC
   Hence (leibniz_up 1) zigzag (leibniz_horizontal 1)   by leibniz_zigzag_def
*)
val leibniz_triplet_0 = store_thm(
  "leibniz_triplet_0",
  ``(leibniz_up 1) zigzag (leibniz_horizontal 1)``,
  `leibniz_up 1 = [] ++ [2; 1] ++ []` by EVAL_TAC >>
  `leibniz_horizontal 1 = [] ++ [2; 2] ++ []` by EVAL_TAC >>
  `((triplet 0 0).a = 1) /\ ((triplet 0 0).b = 2) /\ ((triplet 0 0).c = 2)` by EVAL_TAC >>
  metis_tac[leibniz_zigzag_def]);

(* ------------------------------------------------------------------------- *)
(* Wriggle Paths in Leibniz Triangle                                         *)
(* ------------------------------------------------------------------------- *)

(* Define paths reachable by many zigzags *)
(*
val leibniz_wriggle_def = Define`
    leibniz_wriggle (p1: path) (p2: path) <=>
    ?(m:num) (f:num -> path).
          (p1 = f 0) /\
          (p2 = f m) /\
          (!k. k < m ==> (f k) zigzag (f (SUC k)))
`;
*)

(* Define paths reachable by many zigzags by closure *)
val _ = overload_on("wriggle", ``RTC leibniz_zigzag``); (* RTC = reflexive transitive closure *)
val _ = set_fixity "wriggle" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: list_lcm p1 = list_lcm p1, trivially true.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ list_lcm p1' = list_lcm p2 ==> list_lcm p1 = list_lcm p2
         list_lcm p1
       = list_lcm p1'     by list_lcm_zigzag
       = list_lcm p2      by induction hypothesis
*)
val list_lcm_wriggle = store_thm(
  "list_lcm_wriggle",
  ``!p1 p2. p1 wriggle p2 ==> (list_lcm p1 = list_lcm p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[list_lcm_zigzag]);

(* Theorem: p1 zigzag p2 ==> p1 wriggle p2 *)
(* Proof:
     p1 wriggle p2
   = p1 (RTC zigzag) p2    by notation
   = p1 zigzag p2          by RTC_SINGLE
*)
val leibniz_zigzag_wriggle = store_thm(
  "leibniz_zigzag_wriggle",
  ``!p1 p2. p1 zigzag p2 ==> p1 wriggle p2``,
  rw[]);

(* Theorem: p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2) *)
(* Proof:
   By RTC_STRONG_INDUCT.
   Base: [x] ++ p1 wriggle [x] ++ p1
      True by RTC_REFL.
   Step: p1 zigzag p1' /\ p1' wriggle p2 /\ !x. [x] ++ p1' wriggle [x] ++ p2 ==>
         [x] ++ p1 wriggle [x] ++ p2
      Since p1 zigzag p1',
         so [x] ++ p1 zigzag [x] ++ p1'    by leibniz_zigzag_tail
         or [x] ++ p1 wriggle [x] ++ p1'   by leibniz_zigzag_wriggle
       With [x] ++ p1' wriggle [x] ++ p2   by induction hypothesis
      Hence [x] ++ p1 wriggle [x] ++ p2    by RTC_TRANS
*)
val leibniz_wriggle_tail = store_thm(
  "leibniz_wriggle_tail",
  ``!p1 p2. p1 wriggle p2 ==> !x. ([x] ++ p1) wriggle ([x] ++ p2)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  metis_tac[leibniz_zigzag_tail, leibniz_zigzag_wriggle, RTC_TRANS]);

(* Theorem: p1 wriggle p1 *)
(* Proof: by RTC_REFL *)
val leibniz_wriggle_refl = store_thm(
  "leibniz_wriggle_refl",
  ``!p1. p1 wriggle p1``,
  metis_tac[RTC_REFL]);

(* Theorem: p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3 *)
(* Proof: by RTC_TRANS *)
val leibniz_wriggle_trans = store_thm(
  "leibniz_wriggle_trans",
  ``!p1 p2 p3. p1 wriggle p2 /\ p2 wriggle p3 ==> p1 wriggle p3``,
  metis_tac[RTC_TRANS]);

(* Theorem: k <= n + 1 ==>
            TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
            leibniz_horizontal (n + 1) *)
(* Proof:
   By induction on the difference: n + 1 - k.
   Base: k = n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                       leibniz_horizontal (n + 1)
           TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n)
         = TAKE (n + 2) (leibniz_horizontal (n + 1)) ++ DROP (n + 1) (leibniz_horizontal n)  by k = n + 1
         = leibniz_horizontal (n + 1) ++ []       by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_horizontal (n + 1)             by APPEND_NIL
         Hence they wriggle to each other         by RTC_REFL
   Step: k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)
        Let p1 = leibniz_horizontal (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)
            p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)
       Then p2 zigzag p3                 by leibniz_horizontal_zigzag
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_horizontal_wriggle_step = store_thm(
  "leibniz_horizontal_wriggle_step",
  ``!n k. k <= n + 1 ==> TAKE (k + 1) (leibniz_horizontal (n + 1)) ++ DROP k (leibniz_horizontal n) wriggle
                        leibniz_horizontal (n + 1)``,
  Induct_on `n + 1 - k` >| [
    rpt strip_tac >>
    rw_tac arith_ss[] >>
    `n + 1 = k` by decide_tac >>
    rw[TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt],
    rpt strip_tac >>
    `v = n - k` by decide_tac >>
    `v = (n + 1) - (k + 1)` by decide_tac >>
    `k <= n` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    qabbrev_tac `p1 = leibniz_horizontal (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_horizontal n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_horizontal (n + 1)) ++ DROP (k + 1) (leibniz_horizontal n)` >>
    `p2 zigzag p3` by rw[leibniz_horizontal_zigzag, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1) *)
(* Proof:
   Apply > leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it = |- TAKE 1 (leibniz_horizontal (n + 1)) ++ leibniz_horizontal n wriggle leibniz_horizontal (n + 1): thm
*)
val leibniz_horizontal_wriggle = store_thm(
  "leibniz_horizontal_wriggle",
  ``!n. ([leibniz (n + 1) 0] ++ leibniz_horizontal n) wriggle leibniz_horizontal (n + 1)``,
  rpt strip_tac >>
  `TAKE 1 (leibniz_horizontal (n + 1)) = [leibniz (n + 1) 0]` by rw[leibniz_horizontal_head, binomial_n_0] >>
  metis_tac[leibniz_horizontal_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0]]);

(* ------------------------------------------------------------------------- *)
(* Path Transform keeping LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   By induction on n.
   Base: leibniz_up 0 wriggle leibniz_horizontal 0
      Since leibniz_up 0 = [1]                             by leibniz_up_0
        and leibniz_horizontal 0 = [1]                     by leibniz_horizontal_0
      Hence leibniz_up 0 wriggle leibniz_horizontal 0      by leibniz_wriggle_refl
   Step: leibniz_up n wriggle leibniz_horizontal n ==>
         leibniz_up (SUC n) wriggle leibniz_horizontal (SUC n)
         Let x = leibniz (n + 1) 0.
         Then x = n + 2                                    by leibniz_n_0
          Now leibniz_up (n + 1) = [x] ++ (leibniz_up n)   by leibniz_up_cons
        Since leibniz_up n wriggle leibniz_horizontal n    by induction hypothesis
           so ([x] ++ (leibniz_up n)) wriggle
              ([x] ++ (leibniz_horizontal n))              by leibniz_wriggle_tail
          and ([x] ++ (leibniz_horizontal n)) wriggle
              (leibniz_horizontal (n + 1))                 by leibniz_horizontal_wriggle
        Hence leibniz_up (SUC n) wriggle
              leibniz_horizontal (SUC n)                   by leibniz_wriggle_trans, ADD1
*)
val leibniz_up_wriggle_horizontal = store_thm(
  "leibniz_up_wriggle_horizontal",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  Induct >-
  rw[leibniz_up_0, leibniz_horizontal_0] >>
  qabbrev_tac `x = leibniz (n + 1) 0` >>
  `x = n + 2` by rw[leibniz_n_0, Abbr`x`] >>
  `leibniz_up (n + 1) = [x] ++ (leibniz_up n)` by rw[leibniz_up_cons, Abbr`x`] >>
  `([x] ++ (leibniz_up n)) wriggle ([x] ++ (leibniz_horizontal n))` by rw[leibniz_wriggle_tail] >>
  `([x] ++ (leibniz_horizontal n)) wriggle (leibniz_horizontal (n + 1))` by rw[leibniz_horizontal_wriggle, Abbr`x`] >>
  metis_tac[leibniz_wriggle_trans, ADD1]);

(* Theorem: list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n) *)
(* Proof:
   Since leibniz_up n = REVERSE (leibniz_vertical n)    by notation
     and leibniz_up n wriggle leibniz_horizontal n      by leibniz_up_wriggle_horizontal
         list_lcm (leibniz_vertical n)
       = list_lcm (leibniz_up n)                        by list_lcm_reverse
       = list_lcm (leibniz_horizontal n)                by list_lcm_wriggle
*)
val leibniz_lcm_property = store_thm(
  "leibniz_lcm_property",
  ``!n. list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)``,
  metis_tac[leibniz_up_wriggle_horizontal, list_lcm_wriggle, list_lcm_reverse]);

(* This is a milestone theorem. *)

(* Theorem: k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_horizontal n)   by leibniz_horizontal_divisor
    ==> (leibniz n k) divides list_lcm (leibniz_vertical n)     by leibniz_lcm_property
*)
val leibniz_vertical_divisor = store_thm(
  "leibniz_vertical_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides list_lcm (leibniz_vertical n)``,
  metis_tac[leibniz_horizontal_divisor, leibniz_lcm_property]);

(* ------------------------------------------------------------------------- *)
(* Lower Bound of Leibniz LCM                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 2 ** n <= list_lcm (leibniz_horizontal n) *)
(* Proof:
   Note LENGTH (binomail_horizontal n) = n + 1    by binomial_horizontal_len
    and EVERY_POSITIVE (binomial_horizontal n) by binomial_horizontal_pos .. [1]
     list_lcm (leibniz_horizontal n)
   = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
   >= SUM (binomial_horizontal n)                 by list_lcm_lower_bound, [1]
   = 2 ** n                                       by binomial_horizontal_sum
*)
val leibniz_horizontal_lcm_lower = store_thm(
  "leibniz_horizontal_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_horizontal n)``,
  rpt strip_tac >>
  `LENGTH (binomial_horizontal n) = n + 1` by rw[binomial_horizontal_len] >>
  `EVERY_POSITIVE (binomial_horizontal n)` by rw[binomial_horizontal_pos] >>
  `list_lcm (leibniz_horizontal n) = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `SUM (binomial_horizontal n) = 2 ** n` by rw[binomial_horizontal_sum] >>
  metis_tac[list_lcm_lower_bound]);

(* Theorem: 2 ** n <= list_lcm (leibniz_vertical n) *)
(* Proof:
    list_lcm (leibniz_vertical n)
  = list_lcm (leibniz_horizontal n)      by leibniz_lcm_property
  >= 2 ** n                              by leibniz_horizontal_lcm_lower
*)
val leibniz_vertical_lcm_lower = store_thm(
  "leibniz_vertical_lcm_lower",
  ``!n. 2 ** n <= list_lcm (leibniz_vertical n)``,
  rw_tac std_ss[leibniz_horizontal_lcm_lower, leibniz_lcm_property]);

(* Theorem: 2 ** n <= list_lcm [1 .. (n + 1)] *)
(* Proof: by leibniz_vertical_lcm_lower. *)
val lcm_lower_bound = store_thm(
  "lcm_lower_bound",
  ``!n. 2 ** n <= list_lcm [1 .. (n + 1)]``,
  rw[leibniz_vertical_lcm_lower]);

(* ------------------------------------------------------------------------- *)
(* Leibniz LCM Invariance                                                    *)
(* ------------------------------------------------------------------------- *)

(* Use overloading for leibniz_col_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_col_arm", ``\a b n. MAP (\x. leibniz (a - x) b) [0 ..< n]``);

(* Use overloading for leibniz_seg_arm rooted at leibniz a b, of length n. *)
val _ = overload_on("leibniz_seg_arm", ``\a b n. MAP (\x. leibniz a (b + x)) [0 ..< n]``);

(*
> EVAL ``leibniz_col_arm 5 1 4``;
val it = |- leibniz_col_arm 5 1 4 = [30; 20; 12; 6]: thm
> EVAL ``leibniz_seg_arm 5 1 4``;
val it = |- leibniz_seg_arm 5 1 4 = [30; 60; 60; 30]: thm
> EVAL ``list_lcm (leibniz_col_arm 5 1 4)``;
val it = |- list_lcm (leibniz_col_arm 5 1 4) = 60: thm
> EVAL ``list_lcm (leibniz_seg_arm 5 1 4)``;
val it = |- list_lcm (leibniz_seg_arm 5 1 4) = 60: thm
*)

(* Theorem: leibniz_col_arm a b 0 = [] *)
(* Proof:
     leibniz_col_arm a b 0
   = MAP (\x. leibniz (a - x) b) [0 ..< 0]     by notation
   = MAP (\x. leibniz (a - x) b) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_col_arm_0 = store_thm(
  "leibniz_col_arm_0",
  ``!a b. leibniz_col_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_seg_arm a b 0 = [] *)
(* Proof:
     leibniz_seg_arm a b 0
   = MAP (\x. leibniz a (b + x)) [0 ..< 0]     by notation
   = MAP (\x. leibniz a (b + x)) []            by listRangeLHI_def
   = []                                        by MAP
*)
val leibniz_seg_arm_0 = store_thm(
  "leibniz_seg_arm_0",
  ``!a b. leibniz_seg_arm a b 0 = []``,
  rw[]);

(* Theorem: leibniz_col_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_col_arm a b 1
   = MAP (\x. leibniz (a - x) b) [0 ..< 1]     by notation
   = MAP (\x. leibniz (a - x) b) [0]           by listRangeLHI_def
   = (\x. leibniz (a - x) b) 0 ::[]            by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_col_arm_1 = store_thm(
  "leibniz_col_arm_1",
  ``!a b. leibniz_col_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: leibniz_seg_arm a b 1 = [leibniz a b] *)
(* Proof:
     leibniz_seg_arm a b 1
   = MAP (\x. leibniz a (b + x)) [0 ..< 1]     by notation
   = MAP (\x. leibniz a (b + x)) [0]           by listRangeLHI_def
   = (\x. leibniz a (b + x)) 0 :: []           by MAP
   = [leibniz a b]                             by function application
*)
val leibniz_seg_arm_1 = store_thm(
  "leibniz_seg_arm_1",
  ``!a b. leibniz_seg_arm a b 1 = [leibniz a b]``,
  rw[listRangeLHI_def]);

(* Theorem: LENGTH (leibniz_col_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_col_arm a b n)
   = LENGTH (MAP (\x. leibniz (a - x) b) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_col_arm_len = store_thm(
  "leibniz_col_arm_len",
  ``!a b n. LENGTH (leibniz_col_arm a b n) = n``,
  rw[]);

(* Theorem: LENGTH (leibniz_seg_arm a b n) = n *)
(* Proof:
     LENGTH (leibniz_seg_arm a b n)
   = LENGTH (MAP (\x. leibniz a (b + x)) [0 ..< n])   by notation
   = LENGTH [0 ..< n]                                 by LENGTH_MAP
   = LENGTH (GENLIST (\i. i) n)                       by listRangeLHI_def
   = m                                                by LENGTH_GENLIST
*)
val leibniz_seg_arm_len = store_thm(
  "leibniz_seg_arm_len",
  ``!a b n. LENGTH (leibniz_seg_arm a b n) = n``,
  rw[]);

(* Theorem: k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_col_arm a b n)
   = EL k (MAP (\x. leibniz (a - x) b) [0 ..< n]) by notation
   = (\x. leibniz (a - x) b) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz (a - x) b) k                    by EL_listRangeLHI
   = leibniz (a - k) b
*)
val leibniz_col_arm_el = store_thm(
  "leibniz_col_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_col_arm a b n) = leibniz (a - k) b``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k) *)
(* Proof:
   Note LENGTH [0 ..< n] = n                      by LENGTH_listRangeLHI
     EL k (leibniz_seg_arm a b n)
   = EL k (MAP (\x. leibniz a (b + x)) [0 ..< n]) by notation
   = (\x. leibniz a (b + x)) (EL k [0 ..< n])     by EL_MAP
   = (\x. leibniz a (b + x)) k                    by EL_listRangeLHI
   = leibniz a (b + k)
*)
val leibniz_seg_arm_el = store_thm(
  "leibniz_seg_arm_el",
  ``!n k. k < n ==> !a b. EL k (leibniz_seg_arm a b n) = leibniz a (b + k)``,
  rw[EL_MAP, EL_listRangeLHI]);

(* Theorem: TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b] *)
(* Proof:
   Note LENGTH (leibniz_seg_arm a b (n + 1)) = n + 1   by leibniz_seg_arm_len
    and 0 < n + 1                                      by ADD1, SUC_POS
     TAKE 1 (leibniz_seg_arm a b (n + 1))
   = TAKE (SUC 0) (leibniz_seg_arm a b (n + 1))        by ONE
   = SNOC (EL 0 (leibniz_seg_arm a b (n + 1))) []      by TAKE_SUC_BY_TAKE, TAKE_0
   = [EL 0 (leibniz_seg_arm a b (n + 1))]              by SNOC_NIL
   = leibniz a b                                       by leibniz_seg_arm_el
*)
val leibniz_seg_arm_head = store_thm(
  "leibniz_seg_arm_head",
  ``!a b n. TAKE 1 (leibniz_seg_arm a b (n + 1)) = [leibniz a b]``,
  metis_tac[leibniz_seg_arm_len, leibniz_seg_arm_el,
             ONE, TAKE_SUC_BY_TAKE, TAKE_0, SNOC_NIL, DECIDE``!n. 0 < n + 1 /\ (n + 0 = n)``]);

(* Theorem: leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n *)
(* Proof:
   Note (\x. leibniz (a + 1 - x) b) o SUC
      = (\x. leibniz (a + 1 - (x + 1)) b)     by FUN_EQ_THM
      = (\x. leibniz (a - x) b)               by arithmetic

     leibniz_col_arm (a + 1) b (n + 1)
   = MAP (\x. leibniz (a + 1 - x) b) [0 ..< (n + 1)]                  by notation
   = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])               by listRangeLHI_CONS, 0 < n + 1
   = (\x. leibniz (a + 1 - x) b) 0 :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]   by MAP
   = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [1 ..< (n+1)]       by function application
   = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]   by listRangeLHI_MAP_SUC
   = leibniz (a + 1) b :: MAP (\x. leibniz (a - x) b) [0 ..< n]        by above
   = leibniz (a + 1) b :: leibniz_col_arm a b n                        by notation
*)
val leibniz_col_arm_cons = store_thm(
  "leibniz_col_arm_cons",
  ``!a b n. leibniz_col_arm (a + 1) b (n + 1) = leibniz (a + 1) b :: leibniz_col_arm a b n``,
  rpt strip_tac >>
  `!a x. a + 1 - SUC x + 1 = a - x + 1` by decide_tac >>
  `!a x. a + 1 - SUC x = a - x` by decide_tac >>
  `(\x. leibniz (a + 1 - x) b) o SUC = (\x. leibniz (a + 1 - (x + 1)) b)` by rw[FUN_EQ_THM] >>
  `0 < n + 1` by decide_tac >>
  `leibniz_col_arm (a + 1) b (n + 1) = MAP (\x. leibniz (a + 1 - x) b) (0::[1 ..< (n+1)])` by rw[listRangeLHI_CONS] >>
  `_ = leibniz (a + 1) b :: MAP (\x. leibniz (a + 1 - x) b) [0+1 ..< (n+1)]` by rw[] >>
  `_ = leibniz (a + 1) b :: MAP ((\x. leibniz (a + 1 - x) b) o SUC) [0 ..< n]` by rw[listRangeLHI_MAP_SUC] >>
  `_ = leibniz (a + 1) b :: leibniz_col_arm a b n` by rw[] >>
  rw[]);

(* Theorem: k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n) *)
(* Proof:
   Since k <= n, k < n + 1, and k + 1 < n + 2.
   Hence k < LENGTH (leibniz_seg_arm a b (n + 1)),

    Let x = TAKE k (leibniz_seg_arm a b (n + 1))
    and y = DROP (k + 1) (leibniz_seg_arm a b n)
        TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))   by ADD1
      = SNOC t.b x                                         by TAKE_SUC_BY_TAKE, k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b]                                    by SNOC_APPEND
        TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1))
      = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (SUC n))   by ADD1
      = SNOC t.c (SNOC t.b x)                         by TAKE_SUC_BY_TAKE, SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))
      = x ++ [t.b; t.c]                               by SNOC_APPEND
        DROP k (leibniz_seg_arm a b n)
      = t.a :: y                                      by DROP_BY_DROP_SUC, k < LENGTH (leibniz_seg_arm a b n)
      = [t.a] ++ y                                    by CONS_APPEND
   Hence
    Let p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
           = x ++ [t.b] ++ [t.a] ++ y
           = x ++ [t.b; t.a] ++ y                     by APPEND
    Let p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
           = x ++ [t.b; t.c] ++ y
   Therefore p1 zigzag p2                             by leibniz_zigzag_def
*)
val leibniz_seg_arm_zigzag_step = store_thm(
  "leibniz_seg_arm_zigzag_step",
  ``!n k. k < n ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) zigzag
    TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)``,
  rpt strip_tac >>
  qabbrev_tac `x = TAKE k (leibniz_seg_arm (a + 1) b (n + 1))` >>
  qabbrev_tac `y = DROP (k + 1) (leibniz_seg_arm a b n)` >>
  qabbrev_tac `t = triplet a (b + k)` >>
  `k < n + 1 /\ k + 1 < n + 1` by decide_tac >>
  `EL k (leibniz_seg_arm a b n) = t.a` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL k (leibniz_seg_arm (a + 1) b (n + 1)) = t.b` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `EL (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = t.c` by rw[triplet_def, leibniz_seg_arm_el, Abbr`t`] >>
  `k < LENGTH (leibniz_seg_arm a b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC k) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.b x` by rw[TAKE_SUC_BY_TAKE, Abbr`x`] >>
  `_ = x ++ [t.b]` by rw[] >>
  `SUC k < n + 1` by decide_tac >>
  `SUC k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_len] >>
  `k < LENGTH (leibniz_seg_arm (a + 1) b (n + 1))` by decide_tac >>
  `TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) = TAKE (SUC (SUC k)) (leibniz_seg_arm (a + 1) b (n + 1))` by rw[ADD1] >>
  `_ = SNOC t.c (SNOC t.b x)` by metis_tac[TAKE_SUC_BY_TAKE, ADD1] >>
  `_ = x ++ [t.b; t.c]` by rw[] >>
  `DROP k (leibniz_seg_arm a b n) = [t.a] ++ y` by rw[DROP_BY_DROP_SUC, ADD1, Abbr`y`] >>
  qabbrev_tac `p1 = TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)` >>
  qabbrev_tac `p2 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ y` >>
  `p1 = x ++ [t.b; t.a] ++ y` by rw[Abbr`p1`, Abbr`x`, Abbr`y`] >>
  `p2 = x ++ [t.b; t.c] ++ y` by rw[Abbr`p2`, Abbr`x`] >>
  metis_tac[leibniz_zigzag_def]);

(* Theorem: k < n + 1 ==> !a b.
            TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
            leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   By induction on the difference: n - k.
   Base: k = n ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                   leibniz_seg_arm a b (n + 1)
         Note LENGTH (leibniz_seg_arm (a + 1) b (n + 1)) = n + 1   by leibniz_seg_arm_len
          and LENGTH (leibniz_seg_arm a b n) = n                   by leibniz_seg_arm_len
           TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n)
         = TAKE (n + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP n (leibniz_seg_arm a b n)  by k = n
         = leibniz_seg_arm a b n ++ []           by TAKE_LENGTH_ID, DROP_LENGTH_NIL
         = leibniz_seg_arm a b n                 by APPEND_NIL
         Hence they wriggle to each other        by RTC_REFL
   Step: k < n + 1 ==> TAKE (k + 1) (leibniz_seg_arm a b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
                       leibniz_seg_arm a b (n + 1)
        Let p1 = leibniz_seg_arm (a + 1) b (n + 1)
            p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)
            p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)
       Then p2 zigzag p3                 by leibniz_seg_arm_zigzag_step
        and p3 wriggle p1                by induction hypothesis
       Hence p2 wriggle p1               by RTC_RULES
*)
val leibniz_seg_arm_wriggle_step = store_thm(
  "leibniz_seg_arm_wriggle_step",
  ``!n k. k < n + 1 ==> !a b.
    TAKE (k + 1) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP k (leibniz_seg_arm a b n) wriggle
    leibniz_seg_arm (a + 1) b (n + 1)``,
  Induct_on `n - k` >| [
    rpt strip_tac >>
    `k = n` by decide_tac >>
    metis_tac[leibniz_seg_arm_len, TAKE_LENGTH_ID, DROP_LENGTH_NIL, APPEND_NIL, RTC_REFL],
    rpt strip_tac >>
    qabbrev_tac `p1 = leibniz_seg_arm (a + 1) b (n + 1)` >>
    qabbrev_tac `p2 = TAKE (k + 1) p1 ++ DROP k (leibniz_seg_arm a b n)` >>
    qabbrev_tac `p3 = TAKE (k + 2) (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP (k + 1) (leibniz_seg_arm a b n)` >>
    `p2 zigzag p3` by rw[leibniz_seg_arm_zigzag_step, Abbr`p1`, Abbr`p2`, Abbr`p3`] >>
    `v = n - (k + 1)` by decide_tac >>
    `k + 1 < n + 1` by decide_tac >>
    `k + 1 + 1 = k + 2` by decide_tac >>
    metis_tac[RTC_RULES]
  ]);

(* Theorem: ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1) *)
(* Proof:
   Apply > leibniz_seg_arm_wriggle_step |> SPEC ``n:num`` |> SPEC ``0`` |> SIMP_RULE std_ss[DROP_0];
   val it =
   |- 0 < n + 1 ==> !a b.
     TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n wriggle
     leibniz_seg_arm (a + 1) b (n + 1):
   thm

   Note 0 < n + 1                                       by ADD1, SUC_POS
     [leibniz (a + 1) b] ++ leibniz_seg_arm a b n
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ leibniz_seg_arm a b n           by leibniz_seg_arm_head
   = TAKE 1 (leibniz_seg_arm (a + 1) b (n + 1)) ++ DROP 0 (leibniz_seg_arm a b n)  by DROP_0
   wriggle leibniz_seg_arm (a + 1) b (n + 1)            by leibniz_seg_arm_wriggle_step, put k = 0
*)
val leibniz_seg_arm_wriggle_row_arm = store_thm(
  "leibniz_seg_arm_wriggle_row_arm",
  ``!a b n. ([leibniz (a + 1) b] ++ leibniz_seg_arm a b n) wriggle leibniz_seg_arm (a + 1) b (n + 1)``,
  rpt strip_tac >>
  `0 < n + 1 /\ (0 + 1 = 1)` by decide_tac >>
  metis_tac[leibniz_seg_arm_head, leibniz_seg_arm_wriggle_step, DROP_0]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n) *)
(* Proof:
   By induction on n.
   Base: leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0
      Since leibniz_col_arm a b 0 = []                     by leibniz_col_arm_0
        and leibniz_seg_arm a b 0 = []                     by leibniz_seg_arm_0
      Hence leibniz_col_arm a b 0 wriggle leibniz_seg_arm a b 0   by leibniz_wriggle_refl
   Step: !a b. leibniz_col_arm a b n wriggle leibniz_seg_arm a b n ==>
         leibniz_col_arm a b (SUC n) wriggle leibniz_seg_arm a b (SUC n)
         Induct_on a.
         Base: b <= 0 /\ SUC n <= 0 + 1 - b ==> leibniz_col_arm 0 b (SUC n) wriggle leibniz_seg_arm 0 b (SUC n)
         Note SUC n <= 1 - b ==> n = 0, since 0 <= b.
              leibniz_col_arm 0 b (SUC 0)
            = leibniz_col_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_col_arm_1
              leibniz_seg_arm 0 b (SUC 0)
            = leibniz_seg_arm 0 b 1                       by ONE
            = [leibniz 0 b]                               by leibniz_seg_arm_1
         Hence leibniz_col_arm 0 b 1 wriggle
               leibniz_seg_arm 0 b 1                      by leibniz_wriggle_refl
         Step: b <= SUC a /\ SUC n <= SUC a + 1 - b ==> leibniz_col_arm (SUC a) b (SUC n) wriggle leibniz_seg_arm (SUC a) b (SUC n)
         Note n <= a + 1 - b
           If a + 1 = b,
              Then n = 0,
                leibniz_col_arm (SUC a) b (SUC 0)
              = leibniz_col_arm (SUC a) b 1               by ONE
              = [leibniz (SUC a) b]                       by leibniz_col_arm_1
              = leibniz_seg_arm (SUC a) b 1               by leibniz_seg_arm_1
              = leibniz_seg_arm (SUC a) b (SUC 0)         by ONE
          Hence leibniz_col_arm (SUC a) b 1 wriggle
                leibniz_seg_arm (SUC a) b 1               by leibniz_wriggle_refl
           If a + 1 <> b,
         Then b <= a, and induction hypothesis applies.
         Let x = leibniz (a + 1) b.
         Then leibniz_col_arm (a + 1) b (n + 1)
            = [x] ++ (leibniz_col_arm a b n)              by leibniz_col_arm_cons
        Since leibniz_col_arm a b n
              wriggle leibniz_seg_arm a b n               by induction hypothesis
           so ([x] ++ (leibniz_col_arm a b n)) wriggle
              ([x] ++ (leibniz_seg_arm a b n))            by leibniz_wriggle_tail
          and ([x] ++ (leibniz_seg_arm a b n)) wriggle
              (leibniz_seg_arm (a + 1) b (n + 1))         by leibniz_seg_arm_wriggle_row_arm
        Hence leibniz_col_arm a b (SUC n) wriggle
              leibniz_seg_arm a b (SUC n)                 by leibniz_wriggle_trans, ADD1
*)
val leibniz_col_arm_wriggle_row_arm = store_thm(
  "leibniz_col_arm_wriggle_row_arm",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)``,
  Induct_on `n` >-
  rw[leibniz_col_arm_0, leibniz_seg_arm_0] >>
  rpt strip_tac >>
  Induct_on `a` >| [
    rpt strip_tac >>
    `n = 0` by decide_tac >>
    metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
    rpt strip_tac >>
    `n <= a + 1 - b` by decide_tac >>
    Cases_on `a + 1 = b` >| [
      `n = 0` by decide_tac >>
      metis_tac[leibniz_col_arm_1, leibniz_seg_arm_1, ONE, leibniz_wriggle_refl],
      `b <= a` by decide_tac >>
      qabbrev_tac `x = leibniz (a + 1) b` >>
      `leibniz_col_arm (a + 1) b (n + 1) = [x] ++ (leibniz_col_arm a b n)` by rw[leibniz_col_arm_cons, Abbr`x`] >>
      `([x] ++ (leibniz_col_arm a b n)) wriggle ([x] ++ (leibniz_seg_arm a b n))` by rw[leibniz_wriggle_tail] >>
      `([x] ++ (leibniz_seg_arm a b n)) wriggle (leibniz_seg_arm (a + 1) b (n + 1))` by rw[leibniz_seg_arm_wriggle_row_arm, Abbr`x`] >>
      metis_tac[leibniz_wriggle_trans, ADD1]
    ]
  ]);

(* Theorem: b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n)) *)
(* Proof:
   Since (leibniz_col_arm a b n) wriggle (leibniz_seg_arm a b n)   by leibniz_col_arm_wriggle_row_arm
     the result follows                                            by list_lcm_wriggle
*)
val leibniz_lcm_invariance = store_thm(
  "leibniz_lcm_invariance",
  ``!a b n. b <= a /\ n <= a + 1 - b ==> (list_lcm (leibniz_col_arm a b n) = list_lcm (leibniz_seg_arm a b n))``,
  rw[leibniz_col_arm_wriggle_row_arm, list_lcm_wriggle]);

(* This is a milestone theorem. *)

(* This is used to give another proof of leibniz_up_wriggle_horizontal *)

(* Theorem: leibniz_col_arm n 0 (n + 1) = leibniz_up n *)
(* Proof:
     leibniz_col_arm n 0 (n + 1)
   = MAP (\x. leibniz (n - x) 0) [0 ..< (n + 1)]      by notation
   = MAP (\x. leibniz (n - x) 0) [0 .. n]             by listRangeLHI_to_INC
   = MAP ((\x. leibniz x 0) o (\x. n - x)) [0 .. n]   by function composition
   = REVERSE (MAP (\x. leibniz x 0) [0 .. n])         by listRangeINC_REVERSE_MAP
   = REVERSE (MAP (\x. x + 1) [0 .. n])               by leibniz_n_0
   = REVERSE (MAP SUC [0 .. n])                       by ADD1
   = REVERSE (MAP (I o SUC) [0 .. n])                 by I_THM
   = REVERSE [1 .. (n+1)]                             by listRangeINC_MAP_SUC
   = REVERSE (leibniz_vertical n)                     by notation
   = leibniz_up n                                     by notation
*)
val leibniz_col_arm_n_0 = store_thm(
  "leibniz_col_arm_n_0",
  ``!n. leibniz_col_arm n 0 (n + 1) = leibniz_up n``,
  rpt strip_tac >>
  `(\x. x + 1) = SUC` by rw[FUN_EQ_THM] >>
  `(\x. leibniz x 0) o (\x. n - x + 0) = (\x. leibniz (n - x) 0)` by rw[FUN_EQ_THM] >>
  `leibniz_col_arm n 0 (n + 1) = MAP (\x. leibniz (n - x) 0) [0 .. n]` by rw[listRangeLHI_to_INC] >>
  `_ = MAP ((\x. leibniz x 0) o (\x. n - x + 0)) [0 .. n]` by rw[] >>
  `_ = REVERSE (MAP (\x. leibniz x 0) [0 .. n])` by rw[listRangeINC_REVERSE_MAP] >>
  `_ = REVERSE (MAP (\x. x + 1) [0 .. n])` by rw[leibniz_n_0] >>
  `_ = REVERSE (MAP SUC [0 .. n])` by rw[ADD1] >>
  `_ = REVERSE (MAP (I o SUC) [0 .. n])` by rw[] >>
  `_ = REVERSE [1 .. (n+1)]` by rw[GSYM listRangeINC_MAP_SUC] >>
  rw[]);

(* Theorem: leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n *)
(* Proof:
     leibniz_seg_arm n 0 (n + 1)
   = MAP (\x. leibniz n x) [0 ..< (n + 1)]       by notation
   = MAP (\x. leibniz n x) [0 .. n]              by listRangeLHI_to_INC
   = MAP (leibniz n) [0 .. n]                    by FUN_EQ_THM
   = MAP (leibniz n) (GENLIST (\i. i) (n + 1))   by listRangeINC_def
   = GENLIST ((leibniz n) o I) (n + 1)           by MAP_GENLIST
   = GENLIST (leibniz n) (n + 1)                 by I_THM
   = leibniz_horizontal n                        by notation
*)
val leibniz_seg_arm_n_0 = store_thm(
  "leibniz_seg_arm_n_0",
  ``!n. leibniz_seg_arm n 0 (n + 1) = leibniz_horizontal n``,
  rpt strip_tac >>
  `(\x. x) = I` by rw[FUN_EQ_THM] >>
  `(\x. leibniz n x) = leibniz n` by rw[FUN_EQ_THM] >>
  `leibniz_seg_arm n 0 (n + 1) = MAP (leibniz n) [0 .. n]` by rw_tac std_ss[listRangeLHI_to_INC] >>
  `_ = MAP (leibniz n) (GENLIST (\i. i) (n + 1))` by rw[listRangeINC_def] >>
  `_ = MAP (leibniz n) (GENLIST I (n + 1))` by metis_tac[] >>
  `_ = GENLIST ((leibniz n) o I) (n + 1)` by rw[MAP_GENLIST] >>
  `_ = GENLIST (leibniz n) (n + 1)` by rw[] >>
  rw[]);

(* Theorem: (leibniz_up n) wriggle (leibniz_horizontal n) *)
(* Proof:
   Note 0 <= n /\ n + 1 <= n + 1 - 0, so leibniz_col_arm_wriggle_row_arm applies.
     leibniz_up n
   = leibniz_col_arm n 0 (n + 1)         by leibniz_col_arm_n_0
   wriggle leibniz_seg_arm n 0 (n + 1)   by leibniz_col_arm_wriggle_row_arm
   = leibniz_horizontal n                by leibniz_seg_arm_n_0
*)
val leibniz_up_wriggle_horizontal_alt = store_thm(
  "leibniz_up_wriggle_horizontal_alt",
  ``!n. (leibniz_up n) wriggle (leibniz_horizontal n)``,
  rpt strip_tac >>
  `0 <= n /\ n + 1 <= n + 1 - 0` by decide_tac >>
  metis_tac[leibniz_col_arm_wriggle_row_arm, leibniz_col_arm_n_0, leibniz_seg_arm_n_0]);

(* Theorem: list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n) *)
(* Proof: by leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle *)
val leibniz_up_lcm_eq_horizontal_lcm = store_thm(
  "leibniz_up_lcm_eq_horizontal_lcm",
  ``!n. list_lcm (leibniz_up n) = list_lcm (leibniz_horizontal n)``,
  rw[leibniz_up_wriggle_horizontal_alt, list_lcm_wriggle]);

(* This is another proof of the milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* LCM Lower bound using big LCM                                             *)
(* ------------------------------------------------------------------------- *)

(* Laurent's leib.v and leib.html

Lemma leibn_lcm_swap m n :
   lcmn 'L(m.+1, n) 'L(m, n) = lcmn 'L(m.+1, n) 'L(m.+1, n.+1).
Proof.
rewrite ![lcmn 'L(m.+1, n) _]lcmnC.
by apply/lcmn_swap/leibnS.
Qed.

Notation "\lcm_ ( i < n ) F" :=
 (\big[lcmn/1%N]_(i < n ) F%N)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  ) '/  '  F ']'") : nat_scope.

Canonical Structure lcmn_moid : Monoid.law 1 :=
  Monoid.Law lcmnA lcm1n lcmn1.
Canonical lcmn_comoid := Monoid.ComLaw lcmnC.

Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) =
                   \lcm_(j < k.+1) 'L(n.+1, i + j).
Proof.
elim: k i => [i|k1 IH i].
  by rewrite big_ord_recr !big_ord0 /= lcmn1 lcm1n addn0.
rewrite big_ord_recl /= addn0.
rewrite lcmnA leibn_lcm_swap.
rewrite (eq_bigr (fun j : 'I_k1 => 'L(n, i.+1 + j))).
rewrite -lcmnA.
rewrite IH.
rewrite [RHS]big_ord_recl.
rewrite addn0; congr (lcmn _ _).
by apply: eq_bigr => j _; rewrite addnS.
move=> j _.
by rewrite addnS.
Qed.

Lemma leib_corner n : \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) 'L(n, i).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord_recr !big_ord0 /=.
rewrite big_ord_recr /= IH lcmnC.
rewrite (eq_bigr (fun i : 'I_n.+1 => 'L(n, 0 + i))) //.
by rewrite lieb_line.
Qed.

Lemma main_result n : 2^n.-1 <= \lcm_(i < n) i.+1.
Proof.
case: n => [|n /=]; first by rewrite big_ord0.
have <-: \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) i.+1.
  by apply: eq_bigr => i _; rewrite leibn0.
rewrite leib_corner.
have -> : forall j,  \lcm_(i < j.+1) 'L(n, i) = n.+1 *  \lcm_(i < j.+1) 'C(n, i).
  elim=> [|j IH]; first by rewrite !big_ord_recr !big_ord0 /= !lcm1n.
  by rewrite big_ord_recr [in RHS]big_ord_recr /= IH muln_lcmr.
rewrite (expnDn 1 1) /=  (eq_bigr (fun i : 'I_n.+1 => 'C(n, i))) =>
       [|i _]; last by rewrite !exp1n !muln1.
have <- : forall n m,  \sum_(i < n) m = n * m.
  by move=> m1 n1; rewrite sum_nat_const card_ord.
apply: leq_sum => i _.
apply: dvdn_leq; last by rewrite (bigD1 i) //= dvdn_lcml.
apply big_ind => // [x y Hx Hy|x H]; first by rewrite lcmn_gt0 Hx.
by rewrite bin_gt0 -ltnS.
Qed.

*)

(*
Lemma lieb_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) = \lcm_(j < k.+1) 'L(n.+1, i + j).

translates to:
      !n i k. lcm (leibniz (n + 1) i) (big_lcm {leibniz n (i + j) | j | j < k}) =
              big_lcm {leibniz (n+1) (i + j) | j | j < k + 1};

The picture is:

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))
(n+1)-th row:  L (n+1) i

(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)

If k = 1, this is:  L n i        transform to:
                    L (n+1) i                   L (n+1) i  L (n+1) (i+1)
which is Leibniz triplet.

In general, if true for k, then for the next (k+1)

    n-th row:  L n i          L n (i+1) ....     L n (i + (k-1))  L n (i + k)
(n+1)-th row:  L (n+1) i
=                                                                 L n (i + k)
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k)
by induction hypothesis
=
(n+1)-th row:  L (n+1) i  L (n+1) (i+1) .... L (n+1) (i + (k-1))  L (n+1) (i + k) L (n+1) (i + (k+1))
by Leibniz triplet.

*)

(* Introduce a segment, a partial horizontal row, in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_seg", ``\n k h. IMAGE (\j. leibniz n (k + j)) (count h)``);
(* This is a segment starting at leibniz n k, of length h *)

(* Introduce a horizontal row in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_row", ``\n h. IMAGE (leibniz n) (count h)``);
(* This is a row starting at leibniz n 0, of length h *)

(* Introduce a vertical column in Leibniz Denominator Triangle *)
val _ = overload_on("leibniz_col", ``\h. IMAGE (\i. leibniz i 0) (count h)``);
(* This is a column starting at leibniz 0 0, descending for a length h *)

(* Representations of paths based on indexed sets *)

(* Theorem: leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_seg_def = store_thm(
  "leibniz_seg_def",
  ``!n k h. leibniz_seg n k h = {leibniz n (k + j) | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_row n h = {leibniz n j | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_row_def = store_thm(
  "leibniz_row_def",
  ``!n h. leibniz_row n h = {leibniz n j | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col h = {leibniz j 0 | j | j IN (count h)} *)
(* Proof: by notation *)
val leibniz_col_def = store_thm(
  "leibniz_col_def",
  ``!h. leibniz_col h = {leibniz j 0 | j | j IN (count h)}``,
  rw[EXTENSION]);

(* Theorem: leibniz_col n = natural n *)
(* Proof:
     leibniz_col n
   = IMAGE (\i. leibniz i 0) (count n)    by notation
   = IMAGE (\i. i + 1) (count n)          by leibniz_n_0
   = IMAGE (\i. SUC i) (count n)          by ADD1
   = IMAGE SUC (count n)                  by FUN_EQ_THM
   = natural n                            by notation
*)
val leibniz_col_eq_natural = store_thm(
  "leibniz_col_eq_natural",
  ``!n. leibniz_col n = natural n``,
  rw[leibniz_n_0, ADD1, FUN_EQ_THM]);

(* The following can be taken as a generalisation of the Leibniz Triplet LCM exchange. *)
(* When length h = 1, the top row is a singleton, and the next row is a duplet, altogether a triplet. *)

(* Theorem: lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) = big_lcm (leibniz_seg (n + 1) k (h + 1)) *)
(* Proof:
   Let p = (\j. leibniz n (k + j)), q = (\j. leibniz (n + 1) (k + j)).
   Note q 0 = (leibniz (n + 1) k)                   by function application [1]
   The goal is: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1)))

   By induction on h, length of the row.
   Base case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0))) = big_lcm (IMAGE q (count (0 + 1)))
           lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count 0)))
         = lcm (q 0) (big_lcm (IMAGE p (count 0)))  by [1]
         = lcm (q 0) (big_lcm (IMAGE p {}))         by COUNT_ZERO
         = lcm (q 0) (big_lcm {})                   by IMAGE_EMPTY
         = lcm (q 0) 1                              by big_lcm_empty
         = q 0                                      by LCM_1
         = big_lcm {q 0}                            by big_lcm_sing
         = big_lcm (IMAEG q {0})                    by IMAGE_SING
         = big_lcm (IMAGE q (count 1))              by count_def, EXTENSION

   Step case: lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (count h))) = big_lcm (IMAGE q (count (h + 1))) ==>
              lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h))) = big_lcm (IMAGE q (count (SUC h + 1)))
     Note !n. FINITE (count n)                      by FINITE_COUNT
      and !s. FINITE s ==> FINITE (IMAGE f s)       by IMAGE_FINITE
     Also p h = (triplet n (k + h)).a               by leibniz_triplet_member
          q h = (triplet n (k + h)).b               by leibniz_triplet_member
          q (h + 1) = (triplet n (k + h)).c         by leibniz_triplet_member
     Thus lcm (q h) (p h) = lcm (q h) (q (h + 1))   by leibniz_triplet_lcm

       lcm (leibniz (n + 1) k) (big_lcm (IMAGE p (upto h)))
     = lcm (q 0) (big_lcm (IMAGE p (count (SUC h))))              by [1], notation
     = lcm (q 0) (big_lcm (IMAGE p (h INSERT count h)))           by upto_by_count
     = lcm (q 0) (big_lcm ((p h) INSERT (IMAGE p (count h))))     by IMAGE_INSERT
     = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))        by big_lcm_insert
     = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))        by LCM_ASSOC_COMM
     = lcm (p h) (big_lcm (IMAGE q (count (h + 1))))              by induction hypothesis
     = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))              by ADD1
     = lcm (p h) (big_lcm (IMAGE q (h INSERT (count h)))          by upto_by_count
     = lcm (p h) (big_lcm ((q h) INSERT IMAGE q (count h)))       by IMAGE_INSERT
     = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))        by big_lcm_insert
     = lcm (lcm (p h) (q h)) (big_lcm (IMAGE q (count h)))        by LCM_ASSOC
     = lcm (lcm (q h) (p h)) (big_lcm (IMAGE q (count h)))        by LCM_COM
     = lcm (lcm (q h) (q (h + 1))) (big_lcm (IMAGE q (count h)))  by leibniz_triplet_lcm
     = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))  by LCM_ASSOC, LCM_COMM
     = lcm (q (h + 1)) (big_lcm ((q h) INSERT IMAGE q (count h))) by big_lcm_insert
     = lcm (q (h + 1)) (big_lcm (IMAGE q (h INSERT count h))      by IMAGE_INSERT
     = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))        by upto_by_count, ADD1
     = big_lcm ((q (h + 1)) INSERT (IMAGE q (count (h + 1))))     by big_lcm_insert
     = big_lcm IMAGE q ((h + 1) INSERT (count (h + 1)))           by IMAGE_INSERT
     = big_lcm (IMAGE q (count (SUC (h + 1))))                    by upto_by_count
     = big_lcm (IMAGE q (count (SUC h + 1)))                      by ADD
*)
val big_lcm_seg_transform = store_thm(
  "big_lcm_seg_transform",
  ``!n k h. lcm (leibniz (n + 1) k) (big_lcm (leibniz_seg n k h)) =
           big_lcm (leibniz_seg (n + 1) k (h + 1))``,
  rpt strip_tac >>
  qabbrev_tac `p = (\j. leibniz n (k + j))` >>
  qabbrev_tac `q = (\j. leibniz (n + 1) (k + j))` >>
  Induct_on `h` >| [
    `count 0 = {}` by rw[] >>
    `count 1 = {0}` by rw[COUNT_1] >>
    rw_tac std_ss[IMAGE_EMPTY, big_lcm_empty, IMAGE_SING, LCM_1, big_lcm_sing, Abbr`p`, Abbr`q`],
    `leibniz (n + 1) k = q 0` by rw[Abbr`q`] >>
    simp[] >>
    `lcm (q h) (p h) = lcm (q h) (q (h + 1))` by
  (`p h = (triplet n (k + h)).a` by rw[leibniz_triplet_member, Abbr`p`] >>
    `q h = (triplet n (k + h)).b` by rw[leibniz_triplet_member, Abbr`q`] >>
    `q (h + 1) = (triplet n (k + h)).c` by rw[leibniz_triplet_member, Abbr`q`] >>
    rw[leibniz_triplet_lcm]) >>
    `lcm (q 0) (big_lcm (IMAGE p (count (SUC h)))) = lcm (q 0) (lcm (p h) (big_lcm (IMAGE p (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (p h) (lcm (q 0) (big_lcm (IMAGE p (count h))))` by rw[LCM_ASSOC_COMM] >>
    `_ = lcm (p h) (big_lcm (IMAGE q (count (SUC h))))` by metis_tac[ADD1] >>
    `_ = lcm (p h) (lcm (q h) (big_lcm (IMAGE q (count h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (lcm (q h) (big_lcm (IMAGE q (count h))))` by metis_tac[LCM_ASSOC, LCM_COMM] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (SUC h))))` by rw[upto_by_count, big_lcm_insert] >>
    `_ = lcm (q (h + 1)) (big_lcm (IMAGE q (count (h + 1))))` by rw[ADD1] >>
    `_ = big_lcm (IMAGE q (count (SUC (h + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    metis_tac[ADD]
  ]);

(* Theorem: lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1)) *)
(* Proof:
   Note !n h. leibniz_row n h = leibniz_seg n 0 h   by FUN_EQ_THM
   Take k = 0 in big_lcm_seg_transform, the result follows.
*)
val big_lcm_row_transform = store_thm(
  "big_lcm_row_transform",
  ``!n h. lcm (leibniz (n + 1) 0) (big_lcm (leibniz_row n h)) = big_lcm (leibniz_row (n + 1) (h + 1))``,
  rpt strip_tac >>
  `!n h. leibniz_row n h = leibniz_seg n 0 h` by rw[FUN_EQ_THM] >>
  metis_tac[big_lcm_seg_transform]);

(* Theorem: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) *)
(* Proof:
   Let f = \i. leibniz i 0, then f 0 = leibniz 0 0.
   By induction on n.
   Base: big_lcm (leibniz_col (0 + 1)) = big_lcm (leibniz_row 0 (0 + 1))
         big_lcm (leibniz_col (0 + 1))
       = big_lcm (IMAGE f (count 1))              by notation
       = big_lcm (IMAGE f) {0})                   by COUNT_1
       = big_lcm {f 0}                            by IMAGE_SING
       = big_lcm {leibniz 0 0}                    by f 0
       = big_lcm (IMAGE (leibniz 0) {0})          by IMAGE_SING
       = big_lcm (IMAGE (leibniz 0) (count 1))    by COUNT_1

   Step: big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1)) ==>
         big_lcm (leibniz_col (SUC n + 1)) = big_lcm (leibniz_row (SUC n) (SUC n + 1))
         big_lcm (leibniz_col (SUC n + 1))
       = big_lcm (IMAGE f (count (SUC n + 1)))                             by notation
       = big_lcm (IMAGE f (count (SUC (n + 1))))                           by ADD
       = big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))                by upto_by_count
       = big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))            by IMAGE_INSERT
       = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))               by big_lcm_insert
       = lcm (f (n + 1)) (big_lcm (IMAGE (leibniz n) (count (n + 1))))     by induction hypothesis
       = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))  by f (n + 1)
       = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))             by big_lcm_line_transform
       = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))             by ADD1
*)
val big_lcm_corner_transform = store_thm(
  "big_lcm_corner_transform",
  ``!n. big_lcm (leibniz_col (n + 1)) = big_lcm (leibniz_row n (n + 1))``,
  Induct >-
  rw[COUNT_1, IMAGE_SING] >>
  qabbrev_tac `f = \i. leibniz i 0` >>
  `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
  `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
  `_ = lcm (leibniz (n + 1) 0) (big_lcm (IMAGE (leibniz n) (count (n + 1))))` by rw[Abbr`f`] >>
  `_ = big_lcm (IMAGE (leibniz (n + 1)) (count (n + 1 + 1)))` by rw[big_lcm_row_transform] >>
  `_ = big_lcm (IMAGE (leibniz (SUC n)) (count (SUC n + 1)))` by rw[ADD1] >>
  rw[]);

(* Theorem: (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
            SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f (0 + 1)) <= (0 + 1) * big_lcm (IMAGE f (count (0 + 1)))
      LHS = SUM (GENLIST f 1)
          = SUM [f 0]                 by GENLIST_1
          = f 0                       by SUM
      RHS = 1 * big_lcm (IMAGE f (count 1))
          = big_lcm (IMAGE f {0})     by COUNT_1
          = big_lcm (f 0)             by IMAGE_SING
          = f 0                       by big_lcm_sing
      Thus LHS <= RHS                 by arithmetic
   Step: SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1))) ==>
         SUM (GENLIST f (SUC n + 1)) <= (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
      Note 0 < f (n + 1)                                by (n + 1) IN count (SUC n + 1)
       and !y. y IN count (n + 1) ==> y IN count (SUC n + 1)  by IN_COUNT
       and !x. x IN IMAGE f (count (n + 1)) ==> 0 < x   by IN_IMAGE, above
        so 0 < big_lcm (IMAGE f (count (n + 1)))        by big_lcm_positive
       and 0 < SUC n                                    by SUC_POS
      Thus f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE
       and big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))  by LCM_LE

      LHS = SUM (GENLIST f (SUC n + 1))
          = SUM (GENLIST f (SUC (n + 1)))                         by ADD
          = SUM (SNOC (f (n + 1)) (GENLIST f (n + 1)))            by GENLIST
          = SUM (GENLIST f (n + 1)) + f (n + 1)                   by SUM_SNOC
      RHS = (SUC n + 1) * big_lcm (IMAGE f (count (SUC n + 1)))
          = (SUC n + 1) * big_lcm (IMAGE f (count (SUC (n + 1)))) by ADD
          = (SUC n + 1) * big_lcm (IMAGE f ((n + 1) INSERT (count (n + 1))))      by upto_by_count
          = (SUC n + 1) * big_lcm ((f (n + 1)) INSERT (IMAGE f (count (n + 1))))  by IMAGE_INSERT
          = (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))     by big_lcm_insert
          = SUC n * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))
            +    1 * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))    by RIGHT_ADD_DISTRIB
          >= SUC n * (big_lcm (IMAGE f (count (n + 1))))  + f (n + 1)       by LCM_LE
           = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)      by ADD1
          >= SUM (GENLIST f (n + 1)) + f (n + 1)                            by induction hypothesis
           = LHS                                                            by above
*)
val big_lcm_count_lower_bound = store_thm(
  "big_lcm_count_lower_bound",
  ``!f n. (!x. x IN (count (n + 1)) ==> 0 < f x) ==>
    SUM (GENLIST f (n + 1)) <= (n + 1) * big_lcm (IMAGE f (count (n + 1)))``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rpt strip_tac >>
    `SUM (GENLIST f 1) = f 0` by rw[] >>
    `1 * big_lcm (IMAGE f (count 1)) = f 0` by rw[COUNT_1, big_lcm_sing] >>
    rw[],
    rpt strip_tac >>
    `big_lcm (IMAGE f (count (SUC n + 1))) = big_lcm (IMAGE f (count (SUC (n + 1))))` by rw[ADD] >>
    `_ = lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[upto_by_count, big_lcm_insert] >>
    `!x. (SUC n + 1) * x = SUC n * x + x` by rw[] >>
    `0 < f (n + 1)` by rw[] >>
    `!y. y IN count (n + 1) ==> y IN count (SUC n + 1)` by rw[] >>
    `!x. x IN IMAGE f (count (n + 1)) ==> 0 < x` by metis_tac[IN_IMAGE] >>
    `0 < big_lcm (IMAGE f (count (n + 1)))` by rw[big_lcm_positive] >>
    `0 < SUC n` by rw[] >>
    `f (n + 1) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `big_lcm (IMAGE f (count (n + 1))) <= lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by rw[LCM_LE] >>
    `!a b c x. 0 < a /\ 0 < b /\ 0 < c /\ a <= x /\ b <= x ==> c * a + b <= c * x + x` by
  (rpt strip_tac >>
    `c * a <= c * x` by rw[] >>
    decide_tac) >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) <= (SUC n + 1) * lcm (f (n + 1)) (big_lcm (IMAGE f (count (n + 1))))` by metis_tac[] >>
    `SUC n * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1) = (n + 1) * (big_lcm (IMAGE f (count (n + 1)))) + f (n + 1)` by rw[ADD1] >>
    `SUM (GENLIST f (SUC n + 1)) = SUM (GENLIST f (SUC (n + 1)))` by rw[ADD] >>
    `_ = SUM (GENLIST f (n + 1)) + f (n + 1)` by rw[GENLIST, SUM_SNOC] >>
    metis_tac[LESS_EQ_TRANS, DECIDE``!a x y. 0 < a /\ x <= y ==> x + a <= y + a``]
  ]);

(* Theorem: big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1))) *)
(* Proof:
   Note SUC = \i. i + 1                                      by ADD1, FUN_EQ_THM
            = \i. leibniz i 0                                by leibniz_n_0
    and leibniz n = \j. (n + 1) * binomial n j               by leibniz_def, FUN_EQ_THM
     so !s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s          by IMAGE_CONG
    and !s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s   by IMAGE_CONG
   also !s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s            by FUN_EQ_THM, IMAGE_CONG
    and count (n + 1) <> {}                                  by COUNT_EQ_EMPTY, n + 1 <> 0 [1]

     big_lcm (IMAGE SUC (count (n + 1)))
   = big_lcm (IMAGE (\i. leibniz i 0) (count (n + 1)))       by above
   = big_lcm (IMAGE (leibniz n) (count (n + 1)))             by big_lcm_corner_transform
   = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))       by leibniz_def
   = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))  by IMAGE_COMPOSE, o_DEF
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_map_times, FINITE_COUNT, [1]
*)
val big_lcm_natural_eqn = store_thm(
  "big_lcm_natural_eqn",
  ``!n. big_lcm (natural (n + 1)) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))``,
  rpt strip_tac >>
  `SUC = \i. leibniz i 0` by rw[leibniz_n_0, FUN_EQ_THM] >>
  `leibniz n = \j. (n + 1) * binomial n j` by rw[leibniz_def, FUN_EQ_THM] >>
  `!s. IMAGE SUC s = IMAGE (\i. leibniz i 0) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (leibniz n) s = IMAGE (\j. (n + 1) * binomial n j) s` by rw[IMAGE_CONG] >>
  `!s. IMAGE (binomial n) s = IMAGE (\j. binomial n j) s` by rw[FUN_EQ_THM, IMAGE_CONG] >>
  `count (n + 1) <> {}` by rw[COUNT_EQ_EMPTY] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = big_lcm (IMAGE (leibniz n) (count (n + 1)))` by rw[GSYM big_lcm_corner_transform] >>
  `_ = big_lcm (IMAGE (\j. (n + 1) * binomial n j) (count (n + 1)))` by rw[] >>
  `_ = big_lcm (IMAGE ($* (n + 1)) (IMAGE (binomial n) (count (n + 1))))` by rw[GSYM IMAGE_COMPOSE, combinTheory.o_DEF] >>
  `_ = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_map_times] >>
  rw[]);

(* Theorem: 2 ** n <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note !x. x IN (count (n + 1)) ==> 0 < (binomial n) x      by binomial_pos, IN_COUNT [1]
     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))  by big_lcm_natural_eqn
   >= SUM (GENLIST (binomial n) (n + 1))                     by big_lcm_count_lower_bound, [1]
   = SUM (GENLIST (binomial n) (SUC n))                      by ADD1
   = 2 ** n                                                  by binomial_sum
*)
val big_lcm_lower_bound = store_thm(
  "big_lcm_lower_bound",
  ``!n. 2 ** n <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `!x. x IN (count (n + 1)) ==> 0 < (binomial n) x` by rw[binomial_pos] >>
  `big_lcm (IMAGE SUC (count (n + 1))) = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))` by rw[big_lcm_natural_eqn] >>
  `SUM (GENLIST (binomial n) (n + 1)) = 2 ** n` by rw[GSYM binomial_sum, ADD1] >>
  metis_tac[big_lcm_count_lower_bound]);

(* Another proof of the milestone theorem. *)

(* Theorem: big_lcm (set l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: big_lcm (set []) = list_lcm []
       big_lcm (set [])
     = big_lcm {}        by LIST_TO_SET
     = 1                 by big_lcm_empty
     = list_lcm []       by list_lcm_nil
   Step: big_lcm (set l) = list_lcm l ==> !h. big_lcm (set (h::l)) = list_lcm (h::l)
     Note FINITE (set l)            by FINITE_LIST_TO_SET
       big_lcm (set (h::l))
     = big_lcm (h INSERT set l)     by LIST_TO_SET
     = lcm h (big_lcm (set l))      by big_lcm_insert, FINITE (set t)
     = lcm h (list_lcm l)           by induction hypothesis
     = list_lcm (h::l)              by list_lcm_cons
*)
val big_lcm_eq_list_lcm = store_thm(
  "big_lcm_eq_list_lcm",
  ``!l. big_lcm (set l) = list_lcm l``,
  Induct >-
  rw[big_lcm_empty] >>
  rw[big_lcm_insert]);

(* ------------------------------------------------------------------------- *)
(* List LCM depends only on its set of elements                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x l ==> (list_lcm (x::l) = list_lcm l) *)
(* Proof:
   By induction on l.
   Base: MEM x [] ==> (list_lcm [x] = list_lcm [])
      True by MEM x [] = F                         by MEM
   Step: MEM x l ==> (list_lcm (x::l) = list_lcm l) ==>
         !h. MEM x (h::l) ==> (list_lcm (x::h::l) = list_lcm (h::l))
      Note MEM x (h::l) ==> (x = h) \/ (MEM x l)   by MEM
      If x = h,
         list_lcm (h::h::l)
       = lcm h (lcm h (list_lcm l))   by list_lcm_cons
       = lcm (lcm h h) (list_lcm l)   by LCM_ASSOC
       = lcm h (list_lcm l)           by LCM_REF
       = list_lcm (h::l)              by list_lcm_cons
      If x <> h, MEM x l
         list_lcm (x::h::l)
       = lcm x (lcm h (list_lcm l))   by list_lcm_cons
       = lcm h (lcm x (list_lcm l))   by LCM_ASSOC_COMM
       = lcm h (list_lcm (x::l))      by list_lcm_cons
       = lcm h (list_lcm l)           by induction hypothesis, MEM x l
       = list_lcm (h::l)              by list_lcm_cons
*)
val list_lcm_absorption = store_thm(
  "list_lcm_absorption",
  ``!x l. MEM x l ==> (list_lcm (x::l) = list_lcm l)``,
  rpt strip_tac >>
  Induct_on `l` >-
  metis_tac[MEM] >>
  rw[MEM] >| [
    `lcm h (lcm h (list_lcm l)) = lcm (lcm h h) (list_lcm l)` by rw[LCM_ASSOC] >>
    rw[LCM_REF],
    `lcm x (lcm h (list_lcm l)) = lcm h (lcm x (list_lcm l))` by rw[LCM_ASSOC_COMM] >>
    `_  = lcm h (list_lcm (x::l))` by metis_tac[list_lcm_cons] >>
    rw[]
  ]);

(* Theorem: list_lcm (nub l) = list_lcm l *)
(* Proof:
   By induction on l.
   Base: list_lcm (nub []) = list_lcm []
      True since nub [] = []         by nub_nil
   Step: list_lcm (nub l) = list_lcm l ==> !h. list_lcm (nub (h::l)) = list_lcm (h::l)
      If MEM h l,
           list_lcm (nub (h::l))
         = list_lcm (nub l)         by nub_cons, MEM h l
         = list_lcm l               by induction hypothesis
         = list_lcm (h::l)          by list_lcm_absorption, MEM h l
      If ~(MEM h l),
           list_lcm (nub (h::l))
         = list_lcm (h::nub l)      by nub_cons, ~(MEM h l)
         = lcm h (list_lcm (nub l)) by list_lcm_cons
         = lcm h (list_lcm l)       by induction hypothesis
         = list_lcm (h::l)          by list_lcm_cons
*)
val list_lcm_nub = store_thm(
  "list_lcm_nub",
  ``!l. list_lcm (nub l) = list_lcm l``,
  Induct >-
  rw[nub_nil] >>
  metis_tac[nub_cons, list_lcm_cons, list_lcm_absorption]);

(* Theorem: (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) *)
(* Proof:
   By induction on l1.
   Base: !l2. (set [] = set l2) ==> (list_lcm (nub []) = list_lcm (nub l2))
        Note set [] = set l2 ==> l2 = []    by LIST_TO_SET_EQ_EMPTY
        Hence true.
   Step: !l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2)) ==>
         !h l2. (set (h::l1) = set l2) ==> (list_lcm (nub (h::l1)) = list_lcm (nub l2))
        If MEM h l1,
          Then h IN (set l1)            by notation
                set (h::l1)
              = h INSERT set l1         by LIST_TO_SET
              = set l1                  by ABSORPTION_RWT
           Thus set l1 = set l2,
             so list_lcm (nub (h::l1))
              = list_lcm (nub l1)       by nub_cons, MEM h l1
              = list_lcm (nub l2)       by induction hypothesis, set l1 = set l2

        If ~(MEM h l1),
          Then set (h::l1) = set l2
           ==> ?p1 p2. nub l2 = p1 ++ [h] ++ p2
                  and  set l1 = set (p1 ++ p2)            by LIST_TO_SET_REDUCTION

                list_lcm (nub (h::l1))
              = list_lcm (h::nub l1)                      by nub_cons, ~(MEM h l1)
              = lcm h (list_lcm (nub l1))                 by list_lcm_cons
              = lcm h (list_lcm (nub (p1 ++ p2)))         by induction hypothesis
              = lcm h (list_lcm (p1 ++ p2))               by list_lcm_nub
              = lcm h (lcm (list_lcm p1) (list_lcm p2))   by list_lcm_append
              = lcm (list_lcm p1) (lcm h (list_lcm p2))   by LCM_ASSOC_COMM
              = lcm (list_lcm p1) (list_lcm (h::p2))      by list_lcm_append
              = lcm (list_lcm p1) (list_lcm ([h] ++ p2))  by CONS_APPEND
              = list_lcm (p1 ++ ([h] ++ p2))              by list_lcm_append
              = list_lcm (p1 ++ [h] ++ p2)                by APPEND_ASSOC
              = list_lcm (nub l2)                         by above
*)
val list_lcm_nub_eq_if_set_eq = store_thm(
  "list_lcm_nub_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm (nub l1) = list_lcm (nub l2))``,
  Induct >-
  rw[LIST_TO_SET_EQ_EMPTY] >>
  rpt strip_tac >>
  Cases_on `MEM h l1` >-
  metis_tac[LIST_TO_SET, ABSORPTION_RWT, nub_cons] >>
  `?p1 p2. (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))` by metis_tac[LIST_TO_SET_REDUCTION] >>
  `list_lcm (nub (h::l1)) = list_lcm (h::nub l1)` by rw[nub_cons] >>
  `_ = lcm h (list_lcm (nub l1))` by rw[list_lcm_cons] >>
  `_ = lcm h (list_lcm (nub (p1 ++ p2)))` by metis_tac[] >>
  `_ = lcm h (list_lcm (p1 ++ p2))` by rw[list_lcm_nub] >>
  `_ = lcm h (lcm (list_lcm p1) (list_lcm p2))` by rw[list_lcm_append] >>
  `_ = lcm (list_lcm p1) (lcm h (list_lcm p2))` by rw[LCM_ASSOC_COMM] >>
  `_ = lcm (list_lcm p1) (list_lcm ([h] ++ p2))` by rw[list_lcm_cons] >>
  metis_tac[list_lcm_append, APPEND_ASSOC]);

(* Theorem: (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2) *)
(* Proof:
      set l1 = set l2
   ==> list_lcm (nub l1) = list_lcm (nub l2)   by list_lcm_nub_eq_if_set_eq
   ==>       list_lcm l1 = list_lcm l2         by list_lcm_nub
*)
val list_lcm_eq_if_set_eq = store_thm(
  "list_lcm_eq_if_set_eq",
  ``!l1 l2. (set l1 = set l2) ==> (list_lcm l1 = list_lcm l2)``,
  metis_tac[list_lcm_nub_eq_if_set_eq, list_lcm_nub]);

(* ------------------------------------------------------------------------- *)
(* Set LCM by List LCM                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of a set *)
(* none works!
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   !s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm (s DELETE x))
`;
val set_lcm_def = Define`
   (set_lcm {} = 1) /\
   (!s. FINITE s ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))))
`;
val set_lcm_def = Define`
   set_lcm s = if s = {} then 1 else lcm (CHOICE s) (set_lcm (REST s))
`;
*)
val set_lcm_def = Define`
    set_lcm s = list_lcm (SET_TO_LIST s)
`;

(* Theorem: set_lcm {} = 1 *)
(* Proof:
     set_lcm {}
   = lcm_list (SET_TO_LIST {})   by set_lcm_def
   = lcm_list []                 by SET_TO_LIST_EMPTY
   = 1                           by list_lcm_nil
*)
val set_lcm_empty = store_thm(
  "set_lcm_empty",
  ``set_lcm {} = 1``,
  rw[set_lcm_def]);

(* Theorem: FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s))) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)                         by set_lcm_def
   = list_lcm (CHOICE s::SET_TO_LIST (REST s))        by SET_TO_LIST_THM
   = lcm (CHOICE s) (list_lcm (SET_TO_LIST (REST s))) by list_lcm_cons
   = lcm (CHOICE s) (set_lcm (REST s))                by set_lcm_def
*)
val set_lcm_nonempty = store_thm(
  "set_lcm_nonempty",
  ``!s. FINITE s /\ s <> {} ==> (set_lcm s = lcm (CHOICE s) (set_lcm (REST s)))``,
  rw[set_lcm_def, SET_TO_LIST_THM, list_lcm_cons]);

(* Theorem: set_lcm {x} = x *)
(* Proof:
     set_lcm {x}
   = list_lcm (SET_TO_LIST {x})    by set_lcm_def
   = list_lcm [x]                  by SET_TO_LIST_SING
   = x                             by list_lcm_sing
*)
val set_lcm_sing = store_thm(
  "set_lcm_sing",
  ``!x. set_lcm {x} = x``,
  rw_tac std_ss[set_lcm_def, SET_TO_LIST_SING, list_lcm_sing]);

(* Theorem: set_lcm (set l) = list_lcm l *)
(* Proof:
   Let t = SET_TO_LIST (set l)
   Note FINITE (set l)                    by FINITE_LIST_TO_SET
   Then set t
      = set (SET_TO_LIST (set l))         by notation
      = set l                             by SET_TO_LIST_INV, FINITE (set l)

        set_lcm (set l)
      = list_lcm (SET_TO_LIST (set l))    by set_lcm_def
      = list_lcm t                        by notation
      = list_lcm l                        by list_lcm_eq_if_set_eq, set t = set l
*)
val set_lcm_eq_list_lcm = store_thm(
  "set_lcm_eq_list_lcm",
  ``!l. set_lcm (set l) = list_lcm l``,
  rw[FINITE_LIST_TO_SET, SET_TO_LIST_INV, set_lcm_def, list_lcm_eq_if_set_eq]);

(* Theorem: FINITE s ==> (set_lcm s = big_lcm s) *)
(* Proof:
     set_lcm s
   = list_lcm (SET_TO_LIST s)       by set_lcm_def
   = big_lcm (set (SET_TO_LIST s))  by big_lcm_eq_list_lcm
   = big_lcm s                      by SET_TO_LIST_INV, FINITE s
*)
val set_lcm_eq_big_lcm = store_thm(
  "set_lcm_eq_big_lcm",
  ``!s. FINITE s ==> (big_lcm s = set_lcm s)``,
  metis_tac[set_lcm_def, big_lcm_eq_list_lcm, SET_TO_LIST_INV]);

(* Theorem: FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s) *)
(* Proof: by big_lcm_insert, set_lcm_eq_big_lcm *)
val set_lcm_insert = store_thm(
  "set_lcm_insert",
  ``!s. FINITE s ==> !x. set_lcm (x INSERT s) = lcm x (set_lcm s)``,
  rw[big_lcm_insert, GSYM set_lcm_eq_big_lcm]);

(* Theorem: FINITE s /\ x IN s ==> x divides (set_lcm s) *)
(* Proof:
   Note FINITE s /\ x IN s
    ==> MEM x (SET_TO_LIST s)               by MEM_SET_TO_LIST
    ==> x divides list_lcm (SET_TO_LIST s)  by list_lcm_is_common_multiple
     or x divides (set_lcm s)               by set_lcm_def
*)
val set_lcm_is_common_multiple = store_thm(
  "set_lcm_is_common_multiple",
  ``!x s. FINITE s /\ x IN s ==> x divides (set_lcm s)``,
  rw[set_lcm_def] >>
  `MEM x (SET_TO_LIST s)` by rw[MEM_SET_TO_LIST] >>
  rw[list_lcm_is_common_multiple]);

(* Theorem: FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m *)
(* Proof:
   Note FINITE s
    ==> !x. x IN s <=> MEM x (SET_TO_LIST s)    by MEM_SET_TO_LIST
   Thus list_lcm (SET_TO_LIST s) divides m      by list_lcm_is_least_common_multiple
     or                set_lcm s divides m      by set_lcm_def
*)
val set_lcm_is_least_common_multiple = store_thm(
  "set_lcm_is_least_common_multiple",
  ``!s m. FINITE s /\ (!x. x IN s ==> x divides m) ==> set_lcm s divides m``,
  metis_tac[set_lcm_def, MEM_SET_TO_LIST, list_lcm_is_least_common_multiple]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: set_lcm {} = PROD_SET {}
           set_lcm {}
         = 1                by set_lcm_empty
         = PROD_SET {}      by PROD_SET_EMPTY
   Step: PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s) ==>
         e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==> set_lcm (e INSERT s) = PROD_SET (e INSERT s)
      Note !z. z IN s ==> coprime e z  by IN_INSERT
      Thus coprime e (PROD_SET s)      by every_coprime_prod_set_coprime
           set_lcm (e INSERT s)
         = lcm e (set_lcm s)      by set_lcm_insert
         = lcm e (PROD_SET s)     by induction hypothesis
         = e * (PROD_SET s)       by LCM_COPRIME
         = PROD_SET (e INSERT s)  by PROD_SET_INSERT, e NOTIN s
*)
val pairwise_coprime_prod_set_eq_set_lcm = store_thm(
  "pairwise_coprime_prod_set_eq_set_lcm",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)``,
  `!s. FINITE s ==> PAIRWISE_COPRIME s ==> (set_lcm s = PROD_SET s)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[set_lcm_empty, PROD_SET_EMPTY] >>
  fs[] >>
  `!z. z IN s ==> coprime e z` by metis_tac[] >>
  `coprime e (PROD_SET s)` by rw[every_coprime_prod_set_coprime] >>
  `set_lcm (e INSERT s) = lcm e (set_lcm s)` by rw[set_lcm_insert] >>
  `_ = lcm e (PROD_SET s)` by rw[] >>
  `_ = e * (PROD_SET s)` by rw[LCM_COPRIME] >>
  `_ = PROD_SET (e INSERT s)` by rw[PROD_SET_INSERT] >>
  rw[]);

(* This is a generalisation of LCM_COPRIME |- !m n. coprime m n ==> (lcm m n = m * n)  *)

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m *)
(* Proof:
   Note PROD_SET s = set_lcm s      by pairwise_coprime_prod_set_eq_set_lcm
    and set_lcm s divides m         by set_lcm_is_least_common_multiple
    ==> (PROD_SET s) divides m
*)
val pairwise_coprime_prod_set_divides = store_thm(
  "pairwise_coprime_prod_set_divides",
  ``!s m. FINITE s /\ PAIRWISE_COPRIME s /\ (!x. x IN s ==> x divides m) ==> (PROD_SET s) divides m``,
  rw[set_lcm_is_least_common_multiple, GSYM pairwise_coprime_prod_set_eq_set_lcm]);

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using List LCM directly                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload on consecutive LCM *)
val _ = overload_on("lcm_run", ``\n. list_lcm [1 .. n]``);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDL lcm 1 [1 .. n]   by list_lcm_by_FOLDL
*)
val lcm_run_by_FOLDL = store_thm(
  "lcm_run_by_FOLDL",
  ``!n. lcm_run n = FOLDL lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDL]);

(* Theorem: lcm_run n = FOLDL lcm 1 [1 .. n] *)
(* Proof:
     lcm_run n
   = list_lcm [1 .. n]      by notation
   = FOLDR lcm 1 [1 .. n]   by list_lcm_by_FOLDR
*)
val lcm_run_by_FOLDR = store_thm(
  "lcm_run_by_FOLDR",
  ``!n. lcm_run n = FOLDR lcm 1 [1 .. n]``,
  rw[list_lcm_by_FOLDR]);

(* Theorem: lcm_run 0 = 1 *)
(* Proof:
     lcm_run 0
   = list_lcm [1 .. 0]    by notation
   = list_lcm []          by listRangeINC_EMPTY, 0 < 1
   = 1                    by list_lcm_nil
*)
val lcm_run_0 = store_thm(
  "lcm_run_0",
  ``lcm_run 0 = 1``,
  rw[listRangeINC_EMPTY]);

(* Theorem: lcm_run 1 = 1 *)
(* Proof:
     lcm_run 1
   = list_lcm [1 .. 1]    by notation
   = list_lcm [1]         by leibniz_vertical_0
   = 1                    by list_lcm_sing
*)
val lcm_run_1 = store_thm(
  "lcm_run_1",
  ``lcm_run 1 = 1``,
  rw[leibniz_vertical_0, list_lcm_sing]);

(* Theorem alias *)
val lcm_run_suc = save_thm("lcm_run_suc", list_lcm_suc);
(* val lcm_run_suc = |- !n. lcm_run (n + 1) = lcm (n + 1) (lcm_run n): thm *)

(* Theorem: 0 < lcm_run n *)
(* Proof:
   Note EVERY_POSITIVE [1 .. n]     by listRangeINC_EVERY
     so lcm_run n
      = list_lcm [1 .. n]           by notation
      > 0                           by list_lcm_pos
*)
val lcm_run_pos = store_thm(
  "lcm_run_pos",
  ``!n. 0 < lcm_run n``,
  rw[list_lcm_pos, listRangeINC_EVERY]);

(* Theorem: (lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\ ...  *)
(* Proof: by evaluation *)
val lcm_run_small = store_thm(
  "lcm_run_small",
  ``(lcm_run 2 = 2) /\ (lcm_run 3 = 6) /\ (lcm_run 4 = 12) /\ (lcm_run 5 = 60) /\
   (lcm_run 6 = 60) /\ (lcm_run 7 = 420) /\ (lcm_run 8 = 840) /\ (lcm_run 9 = 2520)``,
  EVAL_TAC);

(* Theorem: (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1) *)
(* Proof:
   If n = 0,
      Then 0 + 1 = 1                by arithmetic
       and lcm_run 0 = 1            by lcm_run_0
      Hence true                    by ONE_DIVIDES_ALL
   If n <> 0,
      Then n - 1 + 1 = n                       by arithmetic, 0 < n
           lcm_run (n + 1)
         = list_lcm [1 .. (n + 1)]             by notation
         = list_lcm (SNOC (n + 1) [1 .. n])    by leibniz_vertical_snoc
         = lcm (n + 1) (list_lcm [1 .. n])     by list_lcm_snoc]
         = lcm (n + 1) (lcm_run n)             by notation
      Hence true                               by LCM_DIVISORS
*)
val lcm_run_divisors = store_thm(
  "lcm_run_divisors",
  ``!n. (n + 1) divides lcm_run (n + 1) /\ (lcm_run n) divides lcm_run (n + 1)``,
  strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `(n - 1 + 1 = n) /\ (n - 1 + 2 = n + 1)` by decide_tac >>
  `lcm_run (n + 1) = list_lcm (SNOC (n + 1) [1 .. n])` by metis_tac[leibniz_vertical_snoc] >>
  `_ = lcm (n + 1) (lcm_run n)` by rw[list_lcm_snoc] >>
  rw[LCM_DIVISORS]);

(* Theorem: lcm_run n <= lcm_run (n + 1) *)
(* Proof:
   Note lcm_run n divides lcm_run (n + 1)   by lcm_run_divisors
    and 0 < lcm_run (n + 1)  ]              by lcm_run_pos
     so lcm_run n <= lcm_run (n + 1)        by DIVIDES_LE
*)
Theorem lcm_run_monotone[allow_rebind]:
  !n. lcm_run n <= lcm_run (n + 1)
Proof rw[lcm_run_divisors, lcm_run_pos, DIVIDES_LE]
QED

(* Theorem: 2 ** n <= lcm_run (n + 1) *)
(* Proof:
     lcm_run (n + 1)
   = list_lcm [1 .. (n + 1)]   by notation
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_run_lower = save_thm("lcm_run_lower", lcm_lower_bound);
(*
val lcm_run_lower = |- !n. 2 ** n <= lcm_run (n + 1): thm
*)

(* Theorem: !n k. k <= n ==> leibniz n k divides lcm_run (n + 1) *)
(* Proof: by notation, leibniz_vertical_divisor *)
val lcm_run_leibniz_divisor = save_thm("lcm_run_leibniz_divisor", leibniz_vertical_divisor);
(*
val lcm_run_leibniz_divisor = |- !n k. k <= n ==> leibniz n k divides lcm_run (n + 1): thm
*)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_run (m + 1)       [1]
   Proof: Note n <= m                                          by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_run (m + 1)           by lcm_run_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_run (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_run (m + 1)             [2]
   Proof: Note 0 < m /\ n <= m - 1                             by 0 < n
           and m - 1 + 1 = m                                   by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_run m           by lcm_run_leibniz_divisor, n <= m - 1
          Note (lcm_run m) divides lcm_run (m + 1)             by lcm_run_divisors
            so (leibniz (m - 1) n) divides lcm_run (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                          by leibniz_up_alt
             = n * binomial m n                                by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_run (m + 1)   by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_run (m + 1)                       by lcm_run_pos
     or n * leibniz m n <= lcm_run (m + 1)        by DIVIDES_LE, 0 < lcm_run (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_run (m + 1)        by LESS_EQ_TRANS
*)
val lcm_run_lower_odd = store_thm(
  "lcm_run_lower_odd",
  ``!n. n * 4 ** n <= lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_run (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_run_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_run (m + 1)` by
    (`0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_run m` by metis_tac[lcm_run_leibniz_divisor] >>
  `(lcm_run m) divides lcm_run (m + 1)` by rw[lcm_run_divisors] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[DIVIDES_TRANS]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_run (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_run (m + 1)` by rw[DIVIDES_LE, lcm_run_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_run (2 * (n + 1)) *)
(* Proof:
     lcm_run (2 * (n + 1))
   = lcm_run (2 * n + 2)        by arithmetic
   >= lcm_run (2 * n + 1)       by lcm_run_monotone
   >= n * 4 ** n                by lcm_run_lower_odd
*)
val lcm_run_lower_even = store_thm(
  "lcm_run_lower_even",
  ``!n. n * 4 ** n <= lcm_run (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_run_monotone, lcm_run_lower_odd, LESS_EQ_TRANS]);

(* Theorem: ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n *)
(* Proof:
   Let k = HALF n.
   Then n = 2 * k + 1              by ODD_HALF
    and HALF (2 ** n)
      = HALF (2 ** (2 * k + 1))    by above
      = HALF (2 ** (SUC (2 * k)))  by ADD1
      = HALF (2 * 2 ** (2 * k))    by EXP
      = 2 ** (2 * k)               by HALF_TWICE
      = 4 ** k                     by EXP_EXP_MULT
   Since k * 4 ** k <= lcm_run (2 * k + 1)  by lcm_run_lower_odd
   The result follows.
*)
val lcm_run_odd_lower = store_thm(
  "lcm_run_odd_lower",
  ``!n. ODD n ==> (HALF n) * HALF (2 ** n) <= lcm_run n``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `n = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  `HALF (2 ** n) = HALF (2 ** (SUC (2 * k)))` by rw[ADD1] >>
  `_ = HALF (2 * 2 ** (2 * k))` by rw[EXP] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  metis_tac[lcm_run_lower_odd]);

Theorem HALF_MULT_EVEN'[local] = ONCE_REWRITE_RULE [MULT_COMM] HALF_MULT_EVEN

(* Theorem: EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n *)
(* Proof:
   If n = 0, HALF (n - 2) = 0, so trivially true.
   If n <> 0,
   Let h = HALF n.
   Then n = 2 * h         by EVEN_HALF
   Note h <> 0            by n <> 0
     so ?k. h = k + 1     by num_CASES, ADD1
     or n = 2 * k + 2     by n = 2 * (k + 1)
    and HALF (HALF (2 ** n))
      = HALF (HALF (2 ** (2 * k + 2)))        by above
      = HALF (HALF (2 ** SUC (SUC (2 * k))))  by ADD1
      = HALF (HALF (2 * (2 * 2 ** (2 * k))))  by EXP
      = 2 ** (2 * k)                          by HALF_TWICE
      = 4 ** k                                by EXP_EXP_MULT
   Also n - 2 = 2 * k                         by 0 < n, n = 2 * k + 2
     so HALF (n - 2) = k                      by HALF_TWICE
   Since k * 4 ** k <= lcm_run (2 * (k + 1))  by lcm_run_lower_even
   The result follows.
*)
Theorem lcm_run_even_lower:
  !n. EVEN n ==> HALF (n - 2) * HALF (HALF (2 ** n)) <= lcm_run n
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  qabbrev_tac `h = HALF n` >>
  `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
  `h <> 0` by rw[Abbr`h`] >>
  `?k. h = k + 1` by metis_tac[num_CASES, ADD1] >>
  `HALF (HALF (2 ** n)) = HALF (HALF (2 ** SUC (SUC (2 * k))))` by simp[ADD1] >>
  `_ = HALF (HALF (2 * (2 * 2 ** (2 * k))))` by rw[EXP, HALF_MULT_EVEN'] >>
  `_ = 2 ** (2 * k)` by rw[HALF_TWICE] >>
  `_ = 4 ** k` by rw[EXP_EXP_MULT] >>
  `n - 2 = 2 * k` by decide_tac >>
  `HALF (n - 2) = k` by rw[HALF_TWICE] >>
  metis_tac[lcm_run_lower_even]
QED

(* Theorem: ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   This follows by lcm_run_odd_lower
   if we can show: 2 ** n <= HALF n * HALF (2 ** n)

   Note HALF 5 = 2            by arithmetic
    and HALF 5 <= HALF n      by DIV_LE_MONOTONE, 0 < 2
   Also n <> 0                by 5 <= n
     so ?m. n = SUC m         by num_CASES
        HALF n * HALF (2 ** n)
      = HALF n * HALF (2 * 2 ** m)     by EXP
      = HALF n * 2 ** m                by HALF_TWICE
      >= 2 * 2 ** m                    by LESS_MONO_MULT
       = 2 ** (SUC m)                  by EXP
       = 2 ** n                        by n = SUC m
*)
val lcm_run_odd_lower_alt = store_thm(
  "lcm_run_odd_lower_alt",
  ``!n. ODD n /\ 5 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `2 ** n <= HALF n * HALF (2 ** n)` by
  (`HALF 5 = 2` by EVAL_TAC >>
  `HALF 5 <= HALF n` by rw[DIV_LE_MONOTONE] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `HALF n * HALF (2 ** n) = HALF n * HALF (2 * 2 ** m)` by rw[EXP] >>
  `_ = HALF n * 2 ** m` by rw[HALF_TWICE] >>
  `2 * 2 ** m <= HALF n * 2 ** m` by rw[LESS_MONO_MULT] >>
  rw[EXP]) >>
  metis_tac[lcm_run_odd_lower, LESS_EQ_TRANS]);

(* Theorem: EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If n = 8,
      Then 2 ** 8 = 256         by arithmetic
       and lcm_run 8 = 840      by lcm_run_small
      Thus true.
   If n <> 8,
      Note ODD 9                by arithmetic
        so n <> 9               by ODD_EVEN
        or 10 <= n              by 8 <= n, n <> 9
      This follows by lcm_run_even_lower
      if we can show: 2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))

       Let m = n - 2.
      Then 8 <= m               by arithmetic
        or HALF 8 <= HALF m     by DIV_LE_MONOTONE, 0 < 2
       and HALF 8 = 4 = 2 * 2   by arithmetic
       Now n = SUC (SUC m)      by arithmetic
           HALF m * HALF (HALF (2 ** n))
         = HALF m * HALF (HALF (2 ** (SUC (SUC m))))    by above
         = HALF m * HALF (HALF (2 * (2 * 2 ** m)))      by EXP
         = HALF m * 2 ** m                              by HALF_TWICE
         >= 4 * 2 ** m          by LESS_MONO_MULT
          = 2 * (2 * 2 ** m)    by MULT_ASSOC
          = 2 ** (SUC (SUC m))  by EXP
          = 2 ** n              by n = SUC (SUC m)
*)
Theorem lcm_run_even_lower_alt:
  !n. EVEN n /\ 8 <= n ==> 2 ** n <= lcm_run n
Proof
  rpt strip_tac >>
  Cases_on `n = 8` >- rw[lcm_run_small] >>
  `2 ** n <= HALF (n - 2) * HALF (HALF (2 ** n))`
    by (`ODD 9` by rw[] >>
        `n <> 9` by metis_tac[ODD_EVEN] >>
        `8 <= n - 2` by decide_tac >>
        qabbrev_tac `m = n - 2` >>
        `n = SUC (SUC m)` by rw[Abbr`m`] >>
        ‘HALF m * HALF (HALF (2 ** n)) =
         HALF m * HALF (HALF (2 * (2 * 2 ** m)))’ by rw[EXP, HALF_MULT_EVEN'] >>
        `_ = HALF m * 2 ** m` by rw[HALF_TWICE] >>
        `HALF 8 <= HALF m` by rw[DIV_LE_MONOTONE] >>
        `HALF 8 = 4` by EVAL_TAC >>
        `2 * (2 * 2 ** m) <= HALF m * 2 ** m` by rw[LESS_MONO_MULT] >>
        rw[EXP]) >>
  metis_tac[lcm_run_even_lower, LESS_EQ_TRANS]
QED

(* Theorem: 7 <= n ==> 2 ** n <= lcm_run n *)
(* Proof:
   If EVEN n,
      Node ODD 7                 by arithmetic
        so n <> 7                by EVEN_ODD
        or 8 <= n                by arithmetic
      Hence true                 by lcm_run_even_lower_alt
   If ~EVEN n, then ODD n        by EVEN_ODD
      Note 7 <= n ==> 5 <= n     by arithmetic
      Hence true                 by lcm_run_odd_lower_alt
*)
val lcm_run_lower_better = store_thm(
  "lcm_run_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_run n``,
  rpt strip_tac >>
  `EVEN n \/ ODD n` by rw[EVEN_OR_ODD] >| [
    `ODD 7` by rw[] >>
    `n <> 7` by metis_tac[ODD_EVEN] >>
    rw[lcm_run_even_lower_alt],
    rw[lcm_run_odd_lower_alt]
  ]);


(* ------------------------------------------------------------------------- *)
(* Nair's Trick -- rework                                                    *)
(* ------------------------------------------------------------------------- *)

(*
Picture:
leibniz_lcm_property    |- !n. lcm_run (n + 1) = list_lcm (leibniz_horizontal n)
leibniz_horizontal_mem  |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
so:
lcm_run (2*n + 1) = list_lcm (leibniz_horizontal (2*n))
and leibniz_horizontal (2*n) has members: 0, 1, 2, ...., n, (n + 1), ....., (2*n)
note: n <= 2*n, always, (n+1) <= 2*n = (n+n) when 1 <= n.
thus:
Both  B = (leibniz 2*n n) and C = (leibniz 2*n n+1) divides lcm_run (2*n + 1),
  or  (lcm B C) divides lcm_run (2*n + 1).
But   (lcm B C) = (lcm B A)    where A = (leibniz 2*n-1 n).
By leibniz_def    |- !n k. leibniz n k = (n + 1) * binomial n k
By leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
 so B = (2*n + 1) * binomial 2*n n
and A = (2*n - n) * binomial 2*n n = n * binomial 2*n n
and lcm B A = lcm ((2*n + 1) * binomial 2*n n) (n * binomial 2*n n)
            = (lcm (2*n + 1) n) * binomial 2*n n        by LCM_COMMON_FACTOR
            = n * (2*n + 1) * binomial 2*n n            by coprime (2*n+1) n
            = n * (leibniz 2*n n)                       by leibniz_def
*)

(* Theorem: 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1) *)
(* Proof:
   Note 1 <= n                 by 0 < n
   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    ==> lcm t.b t.c divides list_lcm (leibniz_horizontal m)  by list_lcm_divisor_lcm_pair
                          = lcm_run (m + 1)   by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)
*)
val lcm_run_odd_factor = store_thm(
  "lcm_run_odd_factor",
  ``!n. 0 < n ==> n * (leibniz (2 * n) n) divides lcm_run (2 * n + 1)``,
  rpt strip_tac >>
  qabbrev_tac `m = 2 * n` >>
  `n <= m /\ n + 1 <= m` by rw[Abbr`m`] >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  qabbrev_tac `t = triplet (m - 1) n` >>
  `t.a = leibniz (m - 1) n` by rw[triplet_def, Abbr`t`] >>
  `t.b = leibniz m n` by rw[triplet_def, Abbr`t`] >>
  `t.c = leibniz m (n + 1)` by rw[triplet_def, Abbr`t`] >>
  `t.b divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `t.c divides lcm_run (m + 1)` by metis_tac[lcm_run_leibniz_divisor] >>
  `lcm t.b t.c divides lcm_run (m + 1)` by rw[LCM_IS_LEAST_COMMON_MULTIPLE] >>
  qabbrev_tac `k = binomial m n` >>
  `lcm t.b t.c = lcm t.b t.a` by rw[leibniz_triplet_lcm, Abbr`t`] >>
  `_ = lcm ((m + 1) * k) ((m - n) * k)` by rw[leibniz_def, leibniz_up_alt, Abbr`k`] >>
  `_ = lcm ((m + 1) * k) (n * k)` by rw[Abbr`m`] >>
  `_ = n * (m + 1) * k` by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  `_ = n * leibniz m n` by rw[leibniz_def, Abbr`k`] >>
  metis_tac[]);

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Note     4 ** n <= leibniz (2 * n) n        by leibniz_middle_lower
     so n * 4 ** n <= n * leibniz (2 * n) n    by LESS_MONO_MULT, MULT_COMM
    Let k = n * leibniz (2 * n) n.
   Then k divides lcm_run (2 * n + 1)          by lcm_run_odd_factor
    Now       0 < lcm_run (2 * n + 1)          by lcm_run_pos
     so             k <= lcm_run (2 * n + 1)   by DIVIDES_LE
   Overall n * 4 ** n <= lcm_run (2 * n + 1)   by LESS_EQ_TRANS
*)
Theorem lcm_run_lower_odd[allow_rebind]:
  !n. n * 4 ** n <= lcm_run (2 * n + 1)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  `4 ** n <= leibniz (2 * n) n` by rw[leibniz_middle_lower] >>
  `n * 4 ** n <= n * leibniz (2 * n) n` by rw[LESS_MONO_MULT, MULT_COMM] >>
  `n * leibniz (2 * n) n <= lcm_run (2 * n + 1)` by rw[lcm_run_odd_factor, lcm_run_pos, DIVIDES_LE] >>
  rw[LESS_EQ_TRANS]
QED

(* Another direct proof of the same theorem *)

(* Theorem: n * 4 ** n <= lcm_run (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n, or 1 <= n                 by arithmetic

   Let m = 2 * n,
   Then n <= 2 * n = m, and
        n + 1 <= n + n = m     by arithmetic, 1 <= n
   Also coprime n (m + 1)      by GCD_EUCLID

   Identify a triplet:
   Let t = triplet (m - 1) n
   Then t.a = leibniz (m - 1) n       by triplet_def
        t.b = leibniz m n             by triplet_def
        t.c = leibniz m (n + 1)       by triplet_def

   Note MEM t.b (leibniz_horizontal m)        by leibniz_horizontal_mem, n <= m
    and MEM t.c (leibniz_horizontal m)        by leibniz_horizontal_mem, n + 1 <= m
    and POSITIVE (leibniz_horizontal m)       by leibniz_horizontal_pos_alt
    ==> lcm t.b t.c <= list_lcm (leibniz_horizontal m)  by list_lcm_lower_by_lcm_pair
                     = lcm_run (m + 1)        by leibniz_lcm_property

   Let k = binomial m n.
        lcm t.b t.c
      = lcm t.b t.a                           by leibniz_triplet_lcm
      = lcm ((m + 1) * k) t.a                 by leibniz_def
      = lcm ((m + 1) * k) ((m - n) * k)       by leibniz_up_alt
      = lcm ((m + 1) * k) (n * k)             by m = 2 * n
      = n * (m + 1) * k                       by LCM_COMMON_COPRIME, LCM_SYM, coprime n (m + 1)
      = n * leibniz m n                       by leibniz_def
   Thus (n * leibniz m n) divides lcm_run (m + 1)

      Note     4 ** n <= leibniz m n          by leibniz_middle_lower
        so n * 4 ** n <= n * leibniz m n      by LESS_MONO_MULT, MULT_COMM
   Overall n * 4 ** n <= lcm_run (2 * n + 1)  by LESS_EQ_TRANS
*)
Theorem lcm_run_lower_odd[allow_rebind]:
  !n. n * 4 ** n <= lcm_run (2 * n + 1)
Proof
  rpt strip_tac >>
  Cases_on ‘n = 0’ >-
  rw[] >>
  qabbrev_tac ‘m = 2 * n’ >>
  ‘n <= m /\ n + 1 <= m’ by rw[Abbr‘m’] >>
  ‘coprime n (m + 1)’ by rw[GCD_EUCLID, Abbr‘m’] >>
  qabbrev_tac ‘t = triplet (m - 1) n’ >>
  ‘t.a = leibniz (m - 1) n’ by rw[triplet_def, Abbr‘t’] >>
  ‘t.b = leibniz m n’ by rw[triplet_def, Abbr‘t’] >>
  ‘t.c = leibniz m (n + 1)’ by rw[triplet_def, Abbr‘t’] >>
  ‘MEM t.b (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_mem] >>
  ‘MEM t.c (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_mem] >>
  ‘POSITIVE (leibniz_horizontal m)’ by metis_tac[leibniz_horizontal_pos_alt] >>
  ‘lcm t.b t.c <= lcm_run (m + 1)’ by metis_tac[leibniz_lcm_property, list_lcm_lower_by_lcm_pair] >>
  ‘lcm t.b t.c = n * leibniz m n’ by
  (qabbrev_tac ‘k = binomial m n’ >>
  ‘lcm t.b t.c = lcm t.b t.a’ by rw[leibniz_triplet_lcm, Abbr‘t’] >>
  ‘_ = lcm ((m + 1) * k) ((m - n) * k)’ by rw[leibniz_def, leibniz_up_alt, Abbr‘k’] >>
  ‘_ = lcm ((m + 1) * k) (n * k)’ by rw[Abbr‘m’] >>
  ‘_ = n * (m + 1) * k’ by rw[LCM_COMMON_COPRIME, LCM_SYM] >>
  ‘_ = n * leibniz m n’ by rw[leibniz_def, Abbr‘k’] >>
  rw[]) >>
  ‘4 ** n <= leibniz m n’ by rw[leibniz_middle_lower, Abbr‘m’] >>
  ‘n * 4 ** n <= n * leibniz m n’ by rw[LESS_MONO_MULT] >>
  metis_tac[LESS_EQ_TRANS]
QED

(* Theorem: ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> 5 <= n
      By contradiction, suppose n < 5.
      By ODD n, n = 1 or n = 3.
      If n = 1, LHS = 2 ** 1 = 2         by arithmetic
                RHS = lcm_run 1 = 1      by lcm_run_1
                Hence false.
      If n = 3, LHS = 2 ** 3 = 8         by arithmetic
                RHS = lcm_run 3 = 6      by lcm_run_small
                Hence false.
   Only-if part: 5 <= n ==> 2 ** n <= lcm_run n
      Let h = HALF n.
      Then n = 2 * h + 1                 by ODD_HALF
        so          4 <= 2 * h           by 5 - 1 = 4
        or          2 <= h               by arithmetic
       ==> 2 * 4 ** h <= h * 4 ** h      by LESS_MONO_MULT
       But 2 * 4 ** h
         = 2 * (2 ** 2) ** h             by arithmetic
         = 2 * 2 ** (2 * h)              by EXP_EXP_MULT
         = 2 ** SUC (2 * h)              by EXP
         = 2 ** n                        by ADD1, n = 2 * h + 1
      With h * 4 ** h <= lcm_run n       by lcm_run_lower_odd
        or     2 ** n <= lcm_run n       by LESS_EQ_TRANS
*)
val lcm_run_lower_odd_iff = store_thm(
  "lcm_run_lower_odd_iff",
  ``!n. ODD n ==> (2 ** n <= lcm_run n <=> 5 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 5` by decide_tac >>
    `EVEN 0 /\ EVEN 2 /\ EVEN 4` by rw[] >>
    `n <> 0 /\ n <> 2 /\ n <> 4` by metis_tac[EVEN_ODD] >>
    `(n = 1) \/ (n = 3)` by decide_tac >-
    fs[] >>
    fs[lcm_run_small],
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h + 1` by rw[ODD_HALF, Abbr`h`] >>
    `2 * 4 ** h <= h * 4 ** h` by rw[] >>
    `2 * 4 ** h = 2 * 2 ** (2 * h)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** n` by rw[GSYM EXP] >>
    `h * 4 ** h <= lcm_run n` by rw[lcm_run_lower_odd] >>
    decide_tac
  ]);

(* Theorem: EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n) *)
(* Proof:
   If part: 2 ** n <= lcm_run n ==> (n = 0) \/ 8 <= n
      By contradiction, suppose n <> 0 /\ n < 8.
      By EVEN n, n = 2 or n = 4 or n = 6.
         If n = 2, LHS = 2 ** 2 = 4              by arithmetic
                   RHS = lcm_run 2 = 2           by lcm_run_small
                   Hence false.
         If n = 4, LHS = 2 ** 4 = 16             by arithmetic
                   RHS = lcm_run 4 = 12          by lcm_run_small
                   Hence false.
         If n = 6, LHS = 2 ** 6 = 64             by arithmetic
                   RHS = lcm_run 6 = 60          by lcm_run_small
                   Hence false.
   Only-if part: (n = 0) \/ 8 <= n ==> 2 ** n <= lcm_run n
         If n = 0, LHS = 2 ** 0 = 1              by arithmetic
                   RHS = lcm_run 0 = 1           by lcm_run_0
                   Hence true.
         If n = 8, LHS = 2 ** 8 = 256            by arithmetic
                   RHS = lcm_run 8 = 840         by lcm_run_small
                   Hence true.
         Otherwise, 10 <= n, since ODD 9.
         Let h = HALF n, k = h - 1.
         Then n = 2 * h                          by EVEN_HALF
                = 2 * (k + 1)                    by k = h - 1
                = 2 * k + 2                      by arithmetic
          But lcm_run (2 * k + 1) <= lcm_run (2 * k + 2)  by lcm_run_monotone
          and k * 4 ** k <= lcm_run (2 * k + 1)           by lcm_run_lower_odd

          Now          5 <= h                    by 10 <= h
           so          4 <= k                    by k = h - 1
          ==> 4 * 4 ** k <= k * 4 ** k           by LESS_MONO_MULT

              4 * 4 ** k
            = (2 ** 2) * (2 ** 2) ** k           by arithmetic
            = (2 ** 2) * (2 ** (2 * k))          by EXP_EXP_MULT
            = 2 ** (2 * k + 2)                   by EXP_ADD
            = 2 ** n                             by n = 2 * k + 2

         Overall 2 ** n <= lcm_run n             by LESS_EQ_TRANS
*)
val lcm_run_lower_even_iff = store_thm(
  "lcm_run_lower_even_iff",
  ``!n. EVEN n ==> (2 ** n <= lcm_run n <=> (n = 0) \/ 8 <= n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < 8` by decide_tac >>
    `ODD 1 /\ ODD 3 /\ ODD 5 /\ ODD 7` by rw[] >>
    `n <> 1 /\ n <> 3 /\ n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    `(n = 2) \/ (n = 4) \/ (n = 6)` by decide_tac >-
    fs[lcm_run_small] >-
    fs[lcm_run_small] >>
    fs[lcm_run_small],
    fs[lcm_run_0],
    Cases_on `n = 8` >-
    rw[lcm_run_small] >>
    `ODD 9` by rw[] >>
    `n <> 9` by metis_tac[EVEN_ODD] >>
    `10 <= n` by decide_tac >>
    qabbrev_tac `h = HALF n` >>
    `n = 2 * h` by rw[EVEN_HALF, Abbr`h`] >>
    qabbrev_tac `k = h - 1` >>
    `lcm_run (2 * k + 1) <= lcm_run (2 * k + 1 + 1)` by rw[lcm_run_monotone] >>
    `2 * k + 1 + 1 = n` by rw[Abbr`k`] >>
    `k * 4 ** k <= lcm_run (2 * k + 1)` by rw[lcm_run_lower_odd] >>
    `4 * 4 ** k <= k * 4 ** k` by rw[Abbr`k`] >>
    `4 * 4 ** k = 2 ** 2 * 2 ** (2 * k)` by rw[EXP_EXP_MULT] >>
    `_ = 2 ** (2 * k + 2)` by rw[GSYM EXP_ADD] >>
    `_ = 2 ** n` by rw[] >>
    metis_tac[LESS_EQ_TRANS]
  ]);

(* Theorem: 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n *)
(* Proof:
   If EVEN n,
      Then n <> 5, n <> 7, so 8 <= n    by arithmetic
      Thus true                         by lcm_run_lower_even_iff
   If ~EVEN n, then ODD n               by EVEN_ODD
      Then n <> 0, n <> 6, so 5 <= n    by arithmetic
      Thus true                         by lcm_run_lower_odd_iff
*)
val lcm_run_lower_better_iff = store_thm(
  "lcm_run_lower_better_iff",
  ``!n. 2 ** n <= lcm_run n <=> (n = 0) \/ (n = 5) \/ 7 <= n``,
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `ODD 5 /\ ODD 7` by rw[] >>
    `n <> 5 /\ n <> 7` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_even_iff, DECIDE``8 <= n <=> (7 <= n /\ n <> 7)``],
    `EVEN 0 /\ EVEN 6` by rw[] >>
    `ODD n /\ n <> 0 /\ n <> 6` by metis_tac[EVEN_ODD] >>
    metis_tac[lcm_run_lower_odd_iff, DECIDE``5 <= n <=> (n = 5) \/ (n = 6) \/ (7 <= n)``]
  ]);

(* This is the ultimate goal! *)

(* ------------------------------------------------------------------------- *)
(* Nair's Trick - using consecutive LCM                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the consecutive LCM function *)
val lcm_upto_def = Define`
    (lcm_upto 0 = 1) /\
    (lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n))
`;

(* Extract theorems from definition *)
val lcm_upto_0 = save_thm("lcm_upto_0", lcm_upto_def |> CONJUNCT1);
(* val lcm_upto_0 = |- lcm_upto 0 = 1: thm *)

val lcm_upto_SUC = save_thm("lcm_upto_SUC", lcm_upto_def |> CONJUNCT2);
(* val lcm_upto_SUC = |- !n. lcm_upto (SUC n) = lcm (SUC n) (lcm_upto n): thm *)

(* Theorem: (lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n)) *)
(* Proof: by lcm_upto_def *)
val lcm_upto_alt = store_thm(
  "lcm_upto_alt",
  ``(lcm_upto 0 = 1) /\ (!n. lcm_upto (n+1) = lcm (n+1) (lcm_upto n))``,
  metis_tac[lcm_upto_def, ADD1]);

(* Theorem: lcm_upto 1 = 1 *)
(* Proof:
     lcm_upto 1
   = lcm_upto (SUC 0)          by ONE
   = lcm (SUC 0) (lcm_upto 0)  by lcm_upto_SUC
   = lcm (SUC 0) 1             by lcm_upto_0
   = lcm 1 1                   by ONE
   = 1                         by LCM_REF
*)
val lcm_upto_1 = store_thm(
  "lcm_upto_1",
  ``lcm_upto 1 = 1``,
  metis_tac[lcm_upto_def, LCM_REF, ONE]);

(* Theorem: lcm_upto n for small n *)
(* Proof: by evaluation. *)
val lcm_upto_small = store_thm(
  "lcm_upto_small",
  ``(lcm_upto 2 = 2) /\ (lcm_upto 3 = 6) /\ (lcm_upto 4 = 12) /\
   (lcm_upto 5 = 60) /\ (lcm_upto 6 = 60) /\ (lcm_upto 7 = 420) /\
   (lcm_upto 8 = 840) /\ (lcm_upto 9 = 2520) /\ (lcm_upto 10 = 2520)``,
  EVAL_TAC);

(* Theorem: lcm_upto n = list_lcm [1 .. n] *)
(* Proof:
   By induction on n.
   Base: lcm_upto 0 = list_lcm [1 .. 0]
         lcm_upto 0
       = 1                     by lcm_upto_0
       = list_lcm []           by list_lcm_nil
       = list_lcm [1 .. 0]     by listRangeINC_EMPTY
   Step: lcm_upto n = list_lcm [1 .. n] ==> lcm_upto (SUC n) = list_lcm [1 .. SUC n]
         lcm_upto (SUC n)
       = lcm (SUC n) (lcm_upto n)            by lcm_upto_SUC
       = lcm (SUC n) (list_lcm [1 .. n])     by induction hypothesis
       = list_lcm (SNOC (SUC n) [1 .. n])    by list_lcm_snoc
       = list_lcm [1 .. (SUC n)]             by listRangeINC_SNOC, ADD1, 1 <= n + 1
*)
val lcm_upto_eq_list_lcm = store_thm(
  "lcm_upto_eq_list_lcm",
  ``!n. lcm_upto n = list_lcm [1 .. n]``,
  Induct >-
  rw[lcm_upto_0, list_lcm_nil, listRangeINC_EMPTY] >>
  rw[lcm_upto_SUC, list_lcm_snoc, listRangeINC_SNOC, ADD1]);

(* Theorem: 2 ** n <= lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   = list_lcm [1 .. (n + 1)]   by lcm_upto_eq_list_lcm
   >= 2 ** n                   by lcm_lower_bound
*)
val lcm_upto_lower = store_thm(
  "lcm_upto_lower",
  ``!n. 2 ** n <= lcm_upto (n + 1)``,
  rw[lcm_upto_eq_list_lcm, lcm_lower_bound]);

(* Theorem: 0 < lcm_upto (n + 1) *)
(* Proof:
     lcm_upto (n + 1)
   >= 2 ** n                   by lcm_upto_lower
    > 0                        by EXP_POS, 0 < 2
*)
val lcm_upto_pos = store_thm(
  "lcm_upto_pos",
  ``!n. 0 < lcm_upto (n + 1)``,
  metis_tac[lcm_upto_lower, EXP_POS, LESS_LESS_EQ_TRANS, DECIDE``0 < 2``]);

(* Theorem: (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1) *)
(* Proof:
   Note lcm_upto (n + 1) = lcm (n + 1) (lcm_upto n)   by lcm_upto_alt
     so (n + 1) divides lcm_upto (n + 1)
    and (lcm_upto n) divides lcm_upto (n + 1)         by LCM_DIVISORS
*)
val lcm_upto_divisors = store_thm(
  "lcm_upto_divisors",
  ``!n. (n + 1) divides lcm_upto (n + 1) /\ (lcm_upto n) divides lcm_upto (n + 1)``,
  rw[lcm_upto_alt, LCM_DIVISORS]);

(* Theorem: lcm_upto n <= lcm_upto (n + 1) *)
(* Proof:
   Note (lcm_upto n) divides lcm_upto (n + 1)   by lcm_upto_divisors
    and 0 < lcm_upto (n + 1)                  by lcm_upto_pos
     so lcm_upto n <= lcm_upto (n + 1)          by DIVIDES_LE
*)
val lcm_upto_monotone = store_thm(
  "lcm_upto_monotone",
  ``!n. lcm_upto n <= lcm_upto (n + 1)``,
  rw[lcm_upto_divisors, lcm_upto_pos, DIVIDES_LE]);

(* Theorem: k <= n ==> (leibniz n k) divides lcm_upto (n + 1) *)
(* Proof:
   Note (leibniz n k) divides list_lcm (leibniz_vertical n)   by leibniz_vertical_divisor
    ==> (leibniz n k) divides list_lcm [1 .. (n + 1)]         by notation
     or (leibniz n k) divides lcm_upto (n + 1)                by lcm_upto_eq_list_lcm
*)
val lcm_upto_leibniz_divisor = store_thm(
  "lcm_upto_leibniz_divisor",
  ``!n k. k <= n ==> (leibniz n k) divides lcm_upto (n + 1)``,
  metis_tac[leibniz_vertical_divisor, lcm_upto_eq_list_lcm]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * n + 1) *)
(* Proof:
   If n = 0, LHS = 0, trivially true.
   If n <> 0, 0 < n.
   Let m = 2 * n.

   Claim: (m + 1) * binomial m n divides lcm_upto (m + 1)       [1]
   Proof: Note n <= m                                           by LESS_MONO_MULT, 1 <= 2
           ==> (leibniz m n) divides lcm_upto (m + 1)           by lcm_upto_leibniz_divisor, n <= m
            or (m + 1) * binomial m n divides lcm_upto (m + 1)  by leibniz_def

   Claim: n * binomial m n divides lcm_upto (m + 1)             [2]
   Proof: Note (lcm_upto m) divides lcm_upto (m + 1)            by lcm_upto_divisors
          Also 0 < m /\ n <= m - 1                              by 0 < n
           and m - 1 + 1 = m                                    by 0 < m
          Thus (leibniz (m - 1) n) divides lcm_upto m           by lcm_upto_leibniz_divisor, n <= m - 1
            or (leibniz (m - 1) n) divides lcm_upto (m + 1)     by DIVIDES_TRANS
           and leibniz (m - 1) n
             = (m - n) * binomial m n                           by leibniz_up_alt
             = n * binomial m n                                 by m - n = n

   Note coprime n (m + 1)                         by GCD_EUCLID, GCD_1, 1 < n
   Thus lcm (n * binomial m n) ((m + 1) * binomial m n)
      = n * (m + 1) * binomial m n                by LCM_COMMON_COPRIME
      = n * ((m + 1) * binomial m n)              by MULT_ASSOC
      = n * leibniz m n                           by leibniz_def
    ==> n * leibniz m n divides lcm_upto (m + 1)  by LCM_DIVIDES, [1], [2]
   Note 0 < lcm_upto (m + 1)                      by lcm_upto_pos
     or n * leibniz m n <= lcm_upto (m + 1)       by DIVIDES_LE, 0 < lcm_upto (m + 1)
    Now          4 ** n <= leibniz m n            by leibniz_middle_lower
     so      n * 4 ** n <= n * leibniz m n        by LESS_MONO_MULT, MULT_COMM
     or      n * 4 ** n <= lcm_upto (m + 1)       by LESS_EQ_TRANS
*)
val lcm_upto_lower_odd = store_thm(
  "lcm_upto_lower_odd",
  ``!n. n * 4 ** n <= lcm_upto (2 * n + 1)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = 2 * n` >>
  `(m + 1) * binomial m n divides lcm_upto (m + 1)` by
  (`n <= m` by rw[Abbr`m`] >>
  metis_tac[lcm_upto_leibniz_divisor, leibniz_def]) >>
  `n * binomial m n divides lcm_upto (m + 1)` by
    (`(lcm_upto m) divides lcm_upto (m + 1)` by rw[lcm_upto_divisors] >>
  `0 < m /\ n <= m - 1` by rw[Abbr`m`] >>
  `m - 1 + 1 = m` by decide_tac >>
  `(leibniz (m - 1) n) divides lcm_upto m` by metis_tac[lcm_upto_leibniz_divisor] >>
  `(leibniz (m - 1) n) divides lcm_upto (m + 1)` by metis_tac[DIVIDES_TRANS] >>
  `leibniz (m - 1) n = (m - n) * binomial m n` by rw[leibniz_up_alt] >>
  `_ = n * binomial m n` by rw[Abbr`m`] >>
  metis_tac[]) >>
  `coprime n (m + 1)` by rw[GCD_EUCLID, Abbr`m`] >>
  `lcm (n * binomial m n) ((m + 1) * binomial m n) = n * (m + 1) * binomial m n` by rw[LCM_COMMON_COPRIME] >>
  `_ = n * leibniz m n` by rw[leibniz_def, MULT_ASSOC] >>
  `n * leibniz m n divides lcm_upto (m + 1)` by metis_tac[LCM_DIVIDES] >>
  `n * leibniz m n <= lcm_upto (m + 1)` by rw[DIVIDES_LE, lcm_upto_pos] >>
  `4 ** n <= leibniz m n` by rw[leibniz_middle_lower, Abbr`m`] >>
  metis_tac[LESS_MONO_MULT, MULT_COMM, LESS_EQ_TRANS]);

(* Theorem: n * 4 ** n <= lcm_upto (2 * (n + 1)) *)
(* Proof:
     lcm_upto (2 * (n + 1))
   = lcm_upto (2 * n + 2)        by arithmetic
   >= lcm_upto (2 * n + 1)       by lcm_upto_monotone
   >= n * 4 ** n                 by lcm_upto_lower_odd
*)
val lcm_upto_lower_even = store_thm(
  "lcm_upto_lower_even",
  ``!n. n * 4 ** n <= lcm_upto (2 * (n + 1))``,
  rpt strip_tac >>
  `2 * (n + 1) = 2 * n + 1 + 1` by decide_tac >>
  metis_tac[lcm_upto_monotone, lcm_upto_lower_odd, LESS_EQ_TRANS]);

(* Theorem: 7 <= n ==> 2 ** n <= lcm_upto n *)
(* Proof:
   If ODD n, ?k. n = SUC (2 * k)       by ODD_EXISTS,
      When 5 <= 7 <= n = 2 * k + 1     by ADD1
           2 <= k                      by arithmetic
       and lcm_upto n
         = lcm_upto (2 * k + 1)        by notation
         >= k * 4 ** k                 by lcm_upto_lower_odd
         >= 2 * 4 ** k                 by k >= 2, LESS_MONO_MULT
          = 2 * 2 ** (2 * k)           by EXP_EXP_MULT
          = 2 ** SUC (2 * k)           by EXP
          = 2 ** n                     by n = SUC (2 * k)
   If EVEN n, ?m. n = 2 * m            by EVEN_EXISTS
      Note ODD 7 /\ ODD 9              by arithmetic
      If n = 8,
         LHS = 2 ** 8 = 256,
         RHS = lcm_upto 8 = 840        by lcm_upto_small
         Hence true.
      Otherwise, 10 <= n               by 7 <= n, n <> 7, n <> 8, n <> 9
      Since 0 < n, 0 < m               by MULT_EQ_0
         so ?k. m = SUC k              by num_CASES
       When 10 <= n = 2 * (k + 1)      by ADD1
             4 <= k                    by arithmetic
       and lcm_upto n
         = lcm_upto (2 * (k + 1))      by notation
         >= k * 4 ** k                 by lcm_upto_lower_even
         >= 4 * 4 ** k                 by k >= 4, LESS_MONO_MULT
          = 4 ** SUC k                 by EXP
          = 4 ** m                     by notation
          = 2 ** (2 * m)               by EXP_EXP_MULT
          = 2 ** n                     by n = 2 * m
*)
val lcm_upto_lower_better = store_thm(
  "lcm_upto_lower_better",
  ``!n. 7 <= n ==> 2 ** n <= lcm_upto n``,
  rpt strip_tac >>
  Cases_on `ODD n` >| [
    `?k. n = SUC (2 * k)` by rw[GSYM ODD_EXISTS] >>
    `2 <= k` by decide_tac >>
    `2 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * k + 1)` by rw[ADD1] >>
    `2 ** n = 2 * 2 ** (2 * k)` by rw[EXP] >>
    `_ = 2 * 4 ** k` by rw[EXP_EXP_MULT] >>
    metis_tac[lcm_upto_lower_odd, LESS_EQ_TRANS],
    `ODD 7 /\ ODD 9` by rw[] >>
    `EVEN n /\ n <> 7 /\ n <> 9` by metis_tac[ODD_EVEN] >>
    `?m. n = 2 * m` by rw[GSYM EVEN_EXISTS] >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    Cases_on `n = 8` >-
    rw[lcm_upto_small] >>
    `4 <= k` by decide_tac >>
    `4 * 4 ** k <= k * 4 ** k` by rw[LESS_MONO_MULT] >>
    `lcm_upto n = lcm_upto (2 * (k + 1))` by rw[ADD1] >>
    `2 ** n = 4 ** m` by rw[EXP_EXP_MULT] >>
    `_ = 4 * 4 ** k` by rw[EXP] >>
    metis_tac[lcm_upto_lower_even, LESS_EQ_TRANS]
  ]);

(* This is a very significant result. *)

(* ------------------------------------------------------------------------- *)
(* Simple LCM lower bounds -- rework                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: HALF (n + 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n.
      Let l = [1 .. n].
      Then l <> []                    by listRangeINC_NIL, n <> 0
        so EVERY_POSITIVE l           by listRangeINC_EVERY
        lcm_run n
      = list_lcm l                    by notation
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = (SUM l) DIV n                by listRangeINC_LEN
       = (HALF (n * (n + 1))) DIV n   by sum_1_to_n_eqn
       = HALF ((n * (n + 1)) DIV n)   by DIV_DIV_DIV_MULT, 0 < 2, 0 < n
       = HALF (n + 1)                 by MULT_TO_DIV
*)
val lcm_run_lower_simple = store_thm(
  "lcm_run_lower_simple",
  ``!n. HALF (n + 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  qabbrev_tac `l = [1 .. n]` >>
  `l <> []` by rw[listRangeINC_NIL, Abbr`l`] >>
  `EVERY_POSITIVE l` by rw[listRangeINC_EVERY, Abbr`l`] >>
  `(SUM l) DIV (LENGTH l) = (SUM l) DIV n` by rw[listRangeINC_LEN, Abbr`l`] >>
  `_ = (HALF (n * (n + 1))) DIV n` by rw[sum_1_to_n_eqn, Abbr`l`] >>
  `_ = HALF ((n * (n + 1)) DIV n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = HALF (n + 1)` by rw[MULT_TO_DIV] >>
  metis_tac[list_lcm_nonempty_lower]);

(* This is a simple result, good but not very useful. *)

(* Theorem: lcm_run n = list_lcm (leibniz_vertical (n - 1)) *)
(* Proof:
   If n = 0,
      Then n - 1 + 1 = 0 - 1 + 1 = 1
       but lcm_run 0 = 1 = lcm_run 1, hence true.
   If n <> 0,
      Then n - 1 + 1 = n, hence true trivially.
*)
val lcm_run_alt = store_thm(
  "lcm_run_alt",
  ``!n. lcm_run n = list_lcm (leibniz_vertical (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0, lcm_run_1] >>
  rw[]);

(* Theorem: 2 ** (n - 1) <= lcm_run n *)
(* Proof:
   If n = 0,
      LHS = HALF 1 = 0                by arithmetic
      RHS = lcm_run 0 = 1             by lcm_run_0
      Hence true.
   If n <> 0, 0 < n, or 1 <= n.
      Let l = leibniz_horizontal (n - 1).
      Then LENGTH l = n               by leibniz_horizontal_len
        so l <> []                    by LENGTH_NIL, n <> 0
       and EVERY_POSITIVE l           by leibniz_horizontal_pos
        lcm_run n
      = list_lcm (leibniz_vertical (n - 1)) by lcm_run_alt
      = list_lcm l                    by leibniz_lcm_property
      >= (SUM l) DIV (LENGTH l)       by list_lcm_nonempty_lower, l <> []
       = 2 ** (n - 1)                 by leibniz_horizontal_average_eqn
*)
val lcm_run_lower_good = store_thm(
  "lcm_run_lower_good",
  ``!n. 2 ** (n - 1) <= lcm_run n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n /\ 1 <= n /\ (n - 1 + 1 = n)` by decide_tac >>
  qabbrev_tac `l = leibniz_horizontal (n - 1)` >>
  `lcm_run n = list_lcm l` by metis_tac[leibniz_lcm_property] >>
  `LENGTH l = n` by metis_tac[leibniz_horizontal_len] >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `EVERY_POSITIVE l` by rw[leibniz_horizontal_pos, Abbr`l`] >>
  metis_tac[list_lcm_nonempty_lower, leibniz_horizontal_average_eqn]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound by Leibniz Triangle                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: leibniz n k = (n + 1 - k) * binomial (n + 1) k *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_eqn = store_thm(
  "leibniz_eqn",
  ``!n k. leibniz n k = (n + 1 - k) * binomial (n + 1) k``,
  rw[GSYM leibniz_up_alt]);

(* Theorem: leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1) *)
(* Proof: by leibniz_up_alt:
leibniz_up_alt |- !n. 0 < n ==> !k. leibniz (n - 1) k = (n - k) * binomial n k
*)
val leibniz_right_alt = store_thm(
  "leibniz_right_alt",
  ``!n k. leibniz n (k + 1) = (n - k) * binomial (n + 1) (k + 1)``,
  metis_tac[leibniz_up_alt, DECIDE``0 < n + 1 /\ (n + 1 - 1 = n) /\ (n + 1 - (k + 1) = n - k)``]);

(* Leibniz Stack:
       \
            \
                \
                    \
                     (L k k) <-- boundary of Leibniz Triangle
                        |    \            |-- (m - k) = distance
                        |   k <= m <= n  <-- m
                        |         \           (n - k) = height, or max distance
                        |     binomial (n+1) (m+1) is at south-east of binomial n m
                        |              \
                        |                   \
   n-th row: ....... (L n k) .................

leibniz_binomial_identity
|- !m n k. k <= m /\ m <= n ==> (leibniz n k * binomial (n - k) (m - k) = leibniz m k * binomial (n + 1) (m + 1))
This says: (leibniz n k) at bottom is related to a stack entry (leibniz m k).
leibniz_divides_leibniz_factor
|- !m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
This is just a corollary of leibniz_binomial_identity, by divides_def.

leibniz_horizontal_member_divides
|- !m n x. n <= TWICE m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
This says: for the n-th row, q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)
           is a common multiple of all members of the n-th row when n <= TWICE m + 1 /\ m <= n
That means, for the n-th row, pick any m-th row for HALF (n - 1) <= m <= n
Compute its list_lcm (leibniz_horizontal m), then multiply by binomial (n + 1) (m + 1) as q.
This value q is a common multiple of all members in n-th row.
The proof goes through all members of n-th row, i.e. (L n k) for k <= n.
To apply leibniz_binomial_identity, the condition is k <= m, not k <= n.
Since m has been picked (between HALF n and n), divide k into two parts: k <= m, m < k <= n.
For the first part, apply leibniz_binomial_identity.
For the second part, use symmetry L n (n - k) = L n k, then apply leibniz_binomial_identity.
With k <= m, m <= n, we apply leibniz_binomial_identity:
(1) Each member x = leibniz n k divides p = leibniz m k * binomial (n + 1) (m + 1), stack member with a factor.
(2) But leibniz m k is a member of (leibniz_horizontal m)
(3) Thus leibniz m k divides list_lcm (leibniz_horizontal m), the stack member divides its row list_lcm
    ==>  p divides q           by multiplying both by binomial (n + 1) (m + 1)
(4) Hence x divides q.
With the other half by symmetry, all members x divides q.
Corollary 1:
lcm_run_divides_property
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n divides binomial n m * lcm_run m
This follows by list_lcm_is_least_common_multiple and leibniz_lcm_property.
Corollary 2:
lcm_run_bound_recurrence
|- !m n. n <= TWICE m /\ m <= n ==> lcm_run n <= lcm_run m * binomial n m
Then lcm_run_upper_bound |- !n. lcm_run n <= 4 ** n  follows by complete induction on n.
*)

(* Theorem: k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1))) *)
(* Proof:
     leibniz n k * (binomial (n - k) (m - k))
   = (n + 1) * (binomial n k) * (binomial (n - k) (m - k))     by leibniz_def
                    n!              (n - k)!
   = (n + 1) * ------------- * ------------------              binomial formula
                 k! (n - k)!    (m - k)! (n - m)!
                    n!                 1
   = (n + 1) * -------------- * ------------------             cancel (n - k)!
                 k! 1           (m - k)! (n - m)!
                    n!               (m + 1)!
   = (n + 1) * -------------- * ------------------             replace by (m + 1)!
                k! (m + 1)!     (m - k)! (n - m)!
                  (n + 1)!           m!
   = (m + 1) * -------------- * ------------------             merge and split factorials
                k! (m + 1)!     (m - k)! (n - m)!
                    m!             (n + 1)!
   = (m + 1) * -------------- * ------------------             binomial formula
                k! (m - k)!      (m + 1)! (n - m)!
   = leibniz m k * binomial (n + 1) (m + 1)                    by leibniz_def
*)
val leibniz_binomial_identity = store_thm(
  "leibniz_binomial_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((leibniz n k) * (binomial (n - k) (m - k)) = (leibniz m k) * (binomial (n + 1) (m + 1)))``,
  rw[leibniz_def] >>
  `m + 1 <= n + 1` by decide_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `(n + 1) - (m + 1) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n + 1) = binomial (n + 1) (m + 1) * (FACT (n - m) * FACT (m + 1))` by metis_tac[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `!n. FACT (n + 1) = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((m + 1) * (binomial m k) * (binomial (n + 1) (m + 1)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT (n + 1) = FACT (n - m) * (FACT k * (FACT (m - k) * ((n + 1) * (binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO_LT_ZERO]);

(* Theorem: k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1) *)
(* Proof:
   Note leibniz m k * binomial (n + 1) (m + 1)
      = leibniz n k * binomial (n - k) (m - k)                 by leibniz_binomial_identity
   Thus leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)
                                                               by divides_def, MULT_COMM
*)
val leibniz_divides_leibniz_factor = store_thm(
  "leibniz_divides_leibniz_factor",
  ``!m n k. k <= m /\ m <= n ==> leibniz n k divides leibniz m k * binomial (n + 1) (m + 1)``,
  metis_tac[leibniz_binomial_identity, divides_def, MULT_COMM]);

(* Theorem: n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
            x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1) *)
(* Proof:
   Let q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1).
   Note MEM x (leibniz_horizontal n)
    ==> ?k. k <= n /\ (x = leibniz n k)          by leibniz_horizontal_member
   Here the picture is:
                HALF n ... m .... n
          0 ........ k .......... n
   We need k <= m to get x divides q, by applying leibniz_divides_leibniz_factor.
   For m < k <= n, we shall use symmetry to get x divides q.
   If k <= m,
      Let p = (leibniz m k) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, k <= m, m <= n
       and MEM (leibniz m k) (leibniz_horizontal m)   by leibniz_horizontal_member, k <= m
       ==> (leibniz m k) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m k) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
   If ~(k <= m), then m < k.
      Note x = leibniz n (n - k)                 by leibniz_sym, k <= n
       Now n <= m + m + 1                        by given n <= 2 * m + 1
        so n - k <= m + m + 1 - k                by arithmetic
       and m + m + 1 - k <= m                    by m < k, so m + 1 <= k
        or n - k <= m                            by LESS_EQ_TRANS
       Let j = n - k, p = (leibniz m j) * binomial (n + 1) (m + 1).
      Then x divides p                           by leibniz_divides_leibniz_factor, j <= m, m <= n
       and MEM (leibniz m j) (leibniz_horizontal m)   by leibniz_horizontal_member, j <= m
       ==> (leibniz m j) divides list_lcm (leibniz_horizontal m)   by list_lcm_is_common_multiple
        so (leibniz m j) * binomial (n + 1) (m + 1)
           divides
           list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)   by DIVIDES_CANCEL, binomial_pos
        or p divides q                           by notation
      Thus x divides q                           by DIVIDES_TRANS
*)
val leibniz_horizontal_member_divides = store_thm(
  "leibniz_horizontal_member_divides",
  ``!m n x. n <= 2 * m + 1 /\ m <= n /\ MEM x (leibniz_horizontal n) ==>
           x divides list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)``,
  rpt strip_tac >>
  qabbrev_tac `q = list_lcm (leibniz_horizontal m) * binomial (n + 1) (m + 1)` >>
  `?k. k <= n /\ (x = leibniz n k)` by rw[GSYM leibniz_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (leibniz m k) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m k) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m k) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS],
    `n - k <= m` by decide_tac >>
    qabbrev_tac `j = n - k` >>
    `x = leibniz n j` by rw[Once leibniz_sym, Abbr`j`] >>
    qabbrev_tac `p = (leibniz m j) * binomial (n + 1) (m + 1)` >>
    `x divides p` by rw[leibniz_divides_leibniz_factor, Abbr`p`] >>
    `MEM (leibniz m j) (leibniz_horizontal m)` by metis_tac[leibniz_horizontal_member] >>
    `(leibniz m j) divides list_lcm (leibniz_horizontal m)` by rw[list_lcm_is_common_multiple] >>
    `p divides q` by rw[GSYM DIVIDES_CANCEL, binomial_pos, Abbr`p`, Abbr`q`] >>
    metis_tac[DIVIDES_TRANS]
  ]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0,
      Then 0 < n, and 0 < m                      by n <= 2 * m
      Thus m - 1 <= n - 1                        by m <= n
       and n - 1 <= 2 * m - 1                    by n <= 2 * m
                  = 2 * (m - 1) + 1
      Thus !x. MEM x (leibniz_horizontal (n - 1)) ==>
            x divides list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by leibniz_horizontal_member_divides
       ==> list_lcm (leibniz_horizontal (n - 1)) divides
           list_lcm (leibniz_horizontal (m - 1)) * binomial n m
                                                 by list_lcm_is_least_common_multiple
       But lcm_run n = leibniz_horizontal (n - 1)          by leibniz_lcm_property
       and lcm_run m = leibniz_horizontal (m - 1)          by leibniz_lcm_property
           list_lcm (leibniz_horizontal h) divides q       by list_lcm_is_least_common_multiple
      Thus (lcm_run n) divides (lcm_run m) * binomial n m  by above
*)
val lcm_run_divides_property = store_thm(
  "lcm_run_divides_property",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  `0 < m` by decide_tac >>
  `m - 1 <= n - 1` by decide_tac >>
  `n - 1 <= 2 * (m - 1) + 1` by decide_tac >>
  `(n - 1 + 1 = n) /\ (m - 1 + 1 = m)` by decide_tac >>
  metis_tac[leibniz_horizontal_member_divides, list_lcm_is_least_common_multiple, leibniz_lcm_property]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m *)
(* Proof:
   Note 0 < lcm_run m                                    by lcm_run_pos
    and 0 < binomial n m                                 by binomial_pos
     so 0 < lcm_run m * binomial n m                     by MULT_EQ_0
    Now (lcm_run n) divides (lcm_run m) * binomial n m   by lcm_run_divides_property
   Thus (lcm_run n) <= (lcm_run m) * binomial n m        by DIVIDES_LE
*)
val lcm_run_bound_recurrence = store_thm(
  "lcm_run_bound_recurrence",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) <= (lcm_run m) * binomial n m``,
  rpt strip_tac >>
  `0 < lcm_run m * binomial n m` by metis_tac[lcm_run_pos, binomial_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw[lcm_run_divides_property, DIVIDES_LE]);

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run m * binomial n m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
          ==> lcm_run n <= c               by lcm_run_bound_recurrence, m <= n
          But m <> 0                       by n <> 0
           so m < n                        by arithmetic
          Now c = lcm_run m * binomial n m by notation
               <= 4 ** m * binomial n m    by induction hypothesis, m < n
               <= 4 ** m * 4 ** m          by binomial_middle_upper_bound
                = 4 ** (m + m)             by EXP_ADD
                = 4 ** n                   by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = lcm_run (m + 1) * binomial n (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          ==> (lcm_run n) <= c             by lcm_run_bound_recurrence, m + 1 <= n
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
          Now c = lcm_run (m + 1) * binomial n (m + 1)   by notation
               <= 4 ** (m + 1) * binomial n (m + 1)      by induction hypothesis, m + 1 < n
                = 4 ** (m + 1) * binomial n m            by binomial_sym, n - (m + 1) = m
               <= 4 ** (m + 1) * 4 ** m                  by binomial_middle_upper_bound
                = 4 ** m * 4 ** (m + 1)    by arithmetic
                = 4 ** (m + (m + 1))       by EXP_ADD
                = 4 ** (2 * m + 1)         by arithmetic
                = 4 ** n                   by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
val lcm_run_upper_bound = store_thm(
  "lcm_run_upper_bound",
  ``!n. lcm_run n <= 4 ** n``,
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run m * binomial n m` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    qabbrev_tac `c = lcm_run (m + 1) * binomial n (m + 1)` >>
    `lcm_run n <= c` by rw[lcm_run_bound_recurrence, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** (m + 1) * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** (m + 1) * 4 ** m = 4 ** n` by metis_tac[MULT_COMM, EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Beta Triangle                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define beta triangle *)
(* Use temp_overload so that beta is invisibe outside:
val beta_def = Define`
    beta n k = k * (binomial n k)
`;
*)
val _ = temp_overload_on ("beta", ``\n k. k * (binomial n k)``); (* for temporary overloading *)
(* can use overload, but then hard to print and change the appearance of too many theorem? *)

(*

Pascal's Triangle (k <= n)
n = 0    1 = binomial 0 0
n = 1    1  1
n = 2    1  2  1
n = 3    1  3  3  1
n = 4    1  4  6  4  1
n = 5    1  5 10 10  5  1
n = 6    1  6 15 20 15  6  1

Beta Triangle (0 < k <= n)
n = 1       1                = 1 * (1)                = leibniz_horizontal 0
n = 2       2  2             = 2 * (1  1)             = leibniz_horizontal 1
n = 3       3  6  3          = 3 * (1  2  1)          = leibniz_horizontal 2
n = 4       4 12 12  4       = 4 * (1  3  3  1)       = leibniz_horizontal 3
n = 5       5 20 30 20  5    = 5 * (1  4  6  4  1)    = leibniz_horizontal 4
n = 6       6 30 60 60 30  6 = 6 * (1  5 10 10  5  1) = leibniz_horizontal 5

> EVAL ``let n = 10 in let k = 6 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 4 in (beta (n+1) (k+1) = leibniz n k)``; --> T
> EVAL ``let n = 10 in let k = 3 in (beta (n+1) (k+1) = leibniz n k)``; --> T

*)

(* Theorem: beta 0 n = 0 *)
(* Proof:
     beta 0 n
   = n * (binomial 0 n)              by notation
   = n * (if n = 0 then 1 else 0)    by binomial_0_n
   = 0
*)
val beta_0_n = store_thm(
  "beta_0_n",
  ``!n. beta 0 n = 0``,
  rw[binomial_0_n]);

(* Theorem: beta n 0 = 0 *)
(* Proof: by notation *)
val beta_n_0 = store_thm(
  "beta_n_0",
  ``!n. beta n 0 = 0``,
  rw[]);

(* Theorem: n < k ==> (beta n k = 0) *)
(* Proof: by notation, binomial_less_0 *)
val beta_less_0 = store_thm(
  "beta_less_0",
  ``!n k. n < k ==> (beta n k = 0)``,
  rw[binomial_less_0]);

(* Theorem: beta (n + 1) (k + 1) = leibniz n k *)
(* Proof:
   If k <= n, then k + 1 <= n + 1                by arithmetic
        beta (n + 1) (k + 1)
      = (k + 1) binomial (n + 1) (k + 1)         by notation
      = (k + 1) (n + 1)!  / (k + 1)! (n - k)!    by binomial_formula2
      = (n + 1) n! / k! (n - k)!                 by factorial composing and decomposing
      = (n + 1) * binomial n k                   by binomial_formula2
      = leibniz_horizontal n k                   by leibniz_def
   If ~(k <= n), then n < k /\ n + 1 < k + 1     by arithmetic
     Then beta (n + 1) (k + 1) = 0               by beta_less_0
      and leibniz n k = 0                        by leibniz_less_0
     Hence true.
*)
val beta_eqn = store_thm(
  "beta_eqn",
  ``!n k. beta (n + 1) (k + 1) = leibniz n k``,
  rpt strip_tac >>
  Cases_on `k <= n` >| [
    `(n + 1) - (k + 1) = n - k` by decide_tac >>
    `k + 1 <= n + 1` by decide_tac >>
    `FACT (n - k) * FACT k * beta (n + 1) (k + 1) = FACT (n - k) * FACT k * ((k + 1) * binomial (n + 1) (k + 1))` by rw[] >>
    `_ = FACT (n - k) * FACT (k + 1) * binomial (n + 1) (k + 1)` by metis_tac[FACT, ADD1, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n + 1)` by metis_tac[binomial_formula2,  MULT_ASSOC, MULT_COMM] >>
    `_ = (n + 1) * FACT n` by metis_tac[FACT, ADD1] >>
    `_ = FACT (n - k) * FACT k * ((n + 1) * binomial n k)` by metis_tac[binomial_formula2, MULT_ASSOC, MULT_COMM] >>
    `_ = FACT (n - k) * FACT k * (leibniz n k)` by rw[leibniz_def] >>
    `FACT k <> 0 /\ FACT (n - k) <> 0` by metis_tac[FACT_LESS, NOT_ZERO_LT_ZERO] >>
    metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC],
    rw[beta_less_0, leibniz_less_0]
  ]);

(* Theorem: 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1)) *)
(* Proof: by beta_eqn *)
val beta_alt = store_thm(
  "beta_alt",
  ``!n k. 0 < n /\ 0 < k ==> (beta n k = leibniz (n - 1) (k - 1))``,
  rw[GSYM beta_eqn]);

(* Theorem: 0 < k /\ k <= n ==> 0 < beta n k *)
(* Proof:
       0 < beta n k
   <=> beta n k <> 0                 by NOT_ZERO_LT_ZERO
   <=> k * (binomial n k) <> 0       by notation
   <=> k <> 0 /\ binomial n k <> 0   by MULT_EQ_0
   <=> k <> 0 /\ k <= n              by binomial_pos
   <=> 0 < k /\ k <= n               by NOT_ZERO_LT_ZERO
*)
val beta_pos = store_thm(
  "beta_pos",
  ``!n k. 0 < k /\ k <= n ==> 0 < beta n k``,
  metis_tac[MULT_EQ_0, binomial_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: (beta n k = 0) <=> (k = 0) \/ n < k *)
(* Proof:
       beta n k = 0
   <=> k * (binomial n k) = 0           by notation
   <=> (k = 0) \/ (binomial n k = 0)    by MULT_EQ_0
   <=> (k = 0) \/ (n < k)               by binomial_eq_0
*)
val beta_eq_0 = store_thm(
  "beta_eq_0",
  ``!n k. (beta n k = 0) <=> (k = 0) \/ n < k``,
  rw[binomial_eq_0]);

(*
binomial_sym  |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
leibniz_sym   |- !n k. k <= n ==> (leibniz n k = leibniz n (n - k))
*)

(* Theorem: k <= n ==> (beta n k = beta n (n - k + 1)) *)
(* Proof:
   If k = 0,
      Then beta n 0 = 0                  by beta_n_0
       and beta n (n + 1) = 0            by beta_less_0
      Hence true.
   If k <> 0, then 0 < k
      Thus 0 < n                         by k <= n
         beta n k
      = leibniz (n - 1) (k - 1)          by beta_alt
      = leibniz (n - 1) (n - k)          by leibniz_sym
      = leibniz (n - 1) (n - k + 1 - 1)  by arithmetic
      = beta n (n - k + 1)               by beta_alt
*)
val beta_sym = store_thm(
  "beta_sym",
  ``!n k. k <= n ==> (beta n k = beta n (n - k + 1))``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[beta_n_0, beta_less_0] >>
  rw[beta_alt, Once leibniz_sym]);

(* ------------------------------------------------------------------------- *)
(* Beta Horizontal List                                                      *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``leibniz_horizontal 3``;    --> [4; 12; 12; 4]
> EVAL ``GENLIST (beta 4) 5``;      --> [0; 4; 12; 12; 4]
> EVAL ``TL (GENLIST (beta 4) 5)``; --> [4; 12; 12; 4]
*)

(* Use overloading for a row of beta n k, k = 1 to n. *)
(* val _ = overload_on("beta_horizontal", ``\n. TL (GENLIST (beta n) (n + 1))``); *)
(* use a direct GENLIST rather than tail of a GENLIST *)
val _ = temp_overload_on("beta_horizontal", ``\n. GENLIST (beta n o SUC) n``); (* for temporary overloading *)

(*
> EVAL ``leibniz_horizontal 5``; --> [6; 30; 60; 60; 30; 6]
> EVAL ``beta_horizontal 6``;    --> [6; 30; 60; 60; 30; 6]
*)

(* Theorem: beta_horizontal 0 = [] *)
(* Proof:
     beta_horizontal 0
   = GENLIST (beta 0 o SUC) 0    by notation
   = []                          by GENLIST
*)
val beta_horizontal_0 = store_thm(
  "beta_horizontal_0",
  ``beta_horizontal 0 = []``,
  rw[]);

(* Theorem: LENGTH (beta_horizontal n) = n *)
(* Proof:
     LENGTH (beta_horizontal n)
   = LENGTH (GENLIST (beta n o SUC) n)     by notation
   = n                                     by LENGTH_GENLIST
*)
val beta_horizontal_len = store_thm(
  "beta_horizontal_len",
  ``!n. LENGTH (beta_horizontal n) = n``,
  rw[]);

(* Theorem: beta_horizontal (n + 1) = leibniz_horizontal n *)
(* Proof:
   Note beta_horizontal (n + 1) = GENLIST ((beta (n + 1) o SUC)) (n + 1)   by notation
    and leibniz_horizontal n = GENLIST (leibniz n) (n + 1)          by notation
    Now (beta (n + 1)) o SUC) k
      = beta (n + 1) (k + 1)                              by ADD1
      = leibniz n k                                       by beta_eqn
   Thus beta_horizontal (n + 1) = leibniz_horizontal n    by GENLIST_FUN_EQ
*)
val beta_horizontal_eqn = store_thm(
  "beta_horizontal_eqn",
  ``!n. beta_horizontal (n + 1) = leibniz_horizontal n``,
  rw[GENLIST_FUN_EQ, beta_eqn, ADD1]);

(* Theorem: 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1)) *)
(* Proof: by beta_horizontal_eqn *)
val beta_horizontal_alt = store_thm(
  "beta_horizontal_alt",
  ``!n. 0 < n ==> (beta_horizontal n = leibniz_horizontal (n - 1))``,
  metis_tac[beta_horizontal_eqn, DECIDE``0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      ?m. m < n /\ (beta n k = beta n (SUC m))
   Since k <> 0, k = SUC m,
     and SUC m = k <= n ==> m < n     by arithmetic
   So take this m, and the result follows.
*)
val beta_horizontal_mem = store_thm(
  "beta_horizontal_mem",
  ``!n k. 0 < k /\ k <= n ==> MEM (beta n k) (beta_horizontal n)``,
  rpt strip_tac >>
  rw[MEM_GENLIST] >>
  `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* too weak:
binomial_horizontal_mem  |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
leibniz_horizontal_mem   |- !n k. k <= n ==> MEM (leibniz n k) (leibniz_horizontal n)
*)

(* Theorem: MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (beta n k = beta n (SUC m))) <=> 0 < k /\ k <= n
   If part: (?m. m < n /\ (beta n k = beta n (SUC m))) ==> 0 < k /\ k <= n
      By contradiction, suppose k = 0 \/ n < k
      Note SUC m <> 0 /\ ~(n < SUC m)     by m < n
      Thus beta n (SUC m) <> 0            by beta_eq_0
        or beta n k <> 0                  by beta n k = beta n (SUC m)
       ==> (k <> 0) /\ ~(n < k)           by beta_eq_0
      This contradicts k = 0 \/ n < k.
  Only-if part: 0 < k /\ k <= n ==> ?m. m < n /\ (beta n k = beta n (SUC m))
      Note k <> 0, so ?m. k = SUC m       by num_CASES
       and SUC m <= n <=> m < n           by LESS_EQ
        so Take this m, and the result follows.
*)
val beta_horizontal_mem_iff = store_thm(
  "beta_horizontal_mem_iff",
  ``!n k. MEM (beta n k) (beta_horizontal n) <=> 0 < k /\ k <= n``,
  rw[MEM_GENLIST] >>
  rewrite_tac[EQ_IMP_THM] >>
  strip_tac >| [
    spose_not_then strip_assume_tac >>
    `SUC m <> 0 /\ ~(n < SUC m)` by decide_tac >>
    `(k <> 0) /\ ~(n < k)` by metis_tac[beta_eq_0] >>
    decide_tac,
    strip_tac >>
    `?m. k = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
    metis_tac[LESS_EQ]
  ]);

(* Theorem: MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n /\ (x = beta n (SUC m))) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)
   Since 0 < k /\ k <= n <=> ?m. (k = SUC m) /\ m < n  by num_CASES, LESS_EQ
   This is trivially true.
*)
val beta_horizontal_member = store_thm(
  "beta_horizontal_member",
  ``!n x. MEM x (beta_horizontal n) <=> ?k. 0 < k /\ k <= n /\ (x = beta n k)``,
  rw[MEM_GENLIST] >>
  metis_tac[num_CASES, NOT_ZERO_LT_ZERO, SUC_NOT_ZERO, LESS_EQ]);

(* Theorem: k < n ==> (EL k (beta_horizontal n) = beta n (k + 1)) *)
(* Proof: by EL_GENLIST, ADD1 *)
val beta_horizontal_element = store_thm(
  "beta_horizontal_element",
  ``!n k. k < n ==> (EL k (beta_horizontal n) = beta n (k + 1))``,
  rw[EL_GENLIST, ADD1]);

(* Theorem: 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n)) *)
(* Proof:
   Note n <> 0
    ==> n = SUC k for some k          by num_CASES
     or n = k + 1                     by ADD1
     lcm_run n
   = lcm_run (k + 1)
   = list_lcm (leibniz_horizontal k)  by leibniz_lcm_property
   = list_lcm (beta_horizontal n)     by beta_horizontal_eqn
*)
val lcm_run_by_beta_horizontal = store_thm(
  "lcm_run_by_beta_horizontal",
  ``!n. 0 < n ==> (lcm_run n = list_lcm (beta_horizontal n))``,
  metis_tac[leibniz_lcm_property, beta_horizontal_eqn, num_CASES, ADD1, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < k /\ k <= n ==> (beta n k) divides lcm_run n *)
(* Proof:
   Note 0 < n                                       by 0 < k /\ k <= n
    and MEM (beta n k) (beta_horizontal n)          by beta_horizontal_mem
   also lcm_run n = list_lcm (beta_horizontal n)    by lcm_run_by_beta_horizontal, 0 < n
   Thus (beta n k) divides lcm_run n                by list_lcm_is_common_multiple
*)
val lcm_run_beta_divisor = store_thm(
  "lcm_run_beta_divisor",
  ``!n k. 0 < k /\ k <= n ==> (beta n k) divides lcm_run n``,
  rw[beta_horizontal_mem, lcm_run_by_beta_horizontal, list_lcm_is_common_multiple]);

(* Theorem: k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m) *)
(* Proof:
   Note (binomial m k) * (binomial n m)
      = (binomial n k) * (binomial (n - k) (m - k))                  by binomial_product_identity
   Thus binomial n k divides binomial m k * binomial n m             by divides_def, MULT_COMM
    ==> k * binomial n k divides k * (binomial m k * binomial n m)   by DIVIDES_CANCEL_COMM
                              = (k * binomial m k) * binomial n m    by MULT_ASSOC
     or (beta n k) divides (beta m k) * (binomial n m)               by notation
*)
val beta_divides_beta_factor = store_thm(
  "beta_divides_beta_factor",
  ``!m n k. k <= m /\ m <= n ==> (beta n k) divides (beta m k) * (binomial n m)``,
  rw[] >>
  `binomial n k divides binomial m k * binomial n m` by metis_tac[binomial_product_identity, divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_CANCEL_COMM, MULT_ASSOC]);

(* Theorem: n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m) *)
(* Proof:
   If n = 0,
      Then lcm_run 0 = 1                         by lcm_run_0
      Hence true                                 by ONE_DIVIDES_ALL
   If n <> 0, then 0 < n.
   Let q = (binomial n m) * (lcm_run m)

   Claim: !x. MEM x (beta_horizontal n) ==> x divides q
   Proof: Note MEM x (beta_horizontal n)
           ==> ?k. 0 < k /\ k <= n /\ (x = beta n k)   by beta_horizontal_member
          Here the picture is:
                     HALF n ... m .... n
              0 ........ k ........... n
          We need k <= m to get x divides q.
          For m < k <= n, we shall use symmetry to get x divides q.
          If k <= m,
             Let p = (beta m k) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, k <= m, m <= n
              and (beta m k) divides lcm_run m   by lcm_run_beta_divisor, 0 < k /\ k <= m
               so (beta m k) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS
          If ~(k <= m), then m < k.
             Note x = beta n (n - k + 1)         by beta_sym, k <= n
              Now n <= m + m                     by given
               so n - k + 1 <= m + m + 1 - k     by arithmetic
              and m + m + 1 - k <= m             by m < k
              ==> n - k + 1 <= m                 by arithmetic
              Let h = n - k + 1, p = (beta m h) * (binomial n m).
             Then x divides p                    by beta_divides_beta_factor, h <= m, m <= n
              and (beta m h) divides lcm_run m   by lcm_run_beta_divisor, 0 < h /\ h <= m
               so (beta m h) * (binomial n m)
                  divides
                  (lcm_run m) * (binomial n m)   by DIVIDES_CANCEL, binomial_pos
               or p divides q                    by MULT_COMM
             Thus x divides q                    by DIVIDES_TRANS

   Therefore,
          (list_lcm (beta_horizontal n)) divides q      by list_lcm_is_least_common_multiple, Claim
       or                    (lcm_run n) divides q      by lcm_run_by_beta_horizontal, 0 < n
*)
val lcm_run_divides_property_alt = store_thm(
  "lcm_run_divides_property_alt",
  ``!m n. n <= 2 * m /\ m <= n ==> (lcm_run n) divides (binomial n m) * (lcm_run m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[lcm_run_0] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `q = (binomial n m) * (lcm_run m)` >>
  `!x. MEM x (beta_horizontal n) ==> x divides q` by
  (rpt strip_tac >>
  `?k. 0 < k /\ k <= n /\ (x = beta n k)` by rw[GSYM beta_horizontal_member] >>
  Cases_on `k <= m` >| [
    qabbrev_tac `p = (beta m k) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m k) divides lcm_run m` by rw[lcm_run_beta_divisor] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS],
    `x = beta n (n - k + 1)` by rw[Once beta_sym] >>
    `n - k + 1 <= m` by decide_tac >>
    qabbrev_tac `h = n - k + 1` >>
    qabbrev_tac `p = (beta m h) * (binomial n m)` >>
    `x divides p` by rw[beta_divides_beta_factor, Abbr`p`] >>
    `(beta m h) divides lcm_run m` by rw[lcm_run_beta_divisor, Abbr`h`] >>
    `p divides q` by metis_tac[DIVIDES_CANCEL, MULT_COMM, binomial_pos] >>
    metis_tac[DIVIDES_TRANS]
  ]) >>
  `(list_lcm (beta_horizontal n)) divides q` by metis_tac[list_lcm_is_least_common_multiple] >>
  metis_tac[lcm_run_by_beta_horizontal]);

(* This is the original lcm_run_divides_property to give lcm_run_upper_bound. *)

(* Theorem: lcm_run n <= 4 ** n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Base: n = 0.
         LHS = lcm_run 0 = 1               by lcm_run_0
         RHS = 4 ** 0 = 1                  by EXP
         Hence true.
      Step: n <> 0 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n m * lcm_run m.
         Then n = 2 * m                    by EVEN_HALF
           so m <= 2 * m = n               by arithmetic
         Note 0 < binomial n m             by binomial_pos, m <= n
          and 0 < lcm_run m                by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, m <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n m) * lcm_run m   by notation
           <= (binomial n m) * 4 ** m      by induction hypothesis, m < n
           <= 4 ** m * 4 ** m              by binomial_middle_upper_bound
            = 4 ** (m + m)                 by EXP_ADD
            = 4 ** n                       by TIMES2, n = 2 * m
         Hence lcm_run n <= 4 ** n.
   If ~EVEN n,
      Then ODD n                           by EVEN_ODD
      Base: n = 1.
         LHS = lcm_run 1 = 1               by lcm_run_1
         RHS = 4 ** 1 = 4                  by EXP
         Hence true.
      Step: n <> 1 /\ !m. m < n ==> lcm_run m <= 4 ** m ==> lcm_run n <= 4 ** n
         Let m = HALF n, c = binomial n (m + 1) * lcm_run (m + 1).
         Then n = 2 * m + 1                by ODD_HALF
          and 0 < m                        by n <> 1
          and m + 1 <= 2 * m + 1 = n       by arithmetic
          But m + 1 <> n                   by m <> 0
           so m + 1 < n                    by m + 1 <> n
         Note 0 < binomial n (m + 1)       by binomial_pos, m + 1 <= n
          and 0 < lcm_run (m + 1)          by lcm_run_pos
          ==> 0 < c                        by MULT_EQ_0
         Thus (lcm_run n) divides c        by lcm_run_divides_property, 0 < m + 1, m + 1 <= n
           or lcm_run n
           <= c                            by DIVIDES_LE, 0 < c
            = (binomial n (m + 1)) * lcm_run (m + 1)   by notation
           <= (binomial n (m + 1)) * 4 ** (m + 1)      by induction hypothesis, m + 1 < n
            = (binomial n m) * 4 ** (m + 1)            by binomial_sym, n - (m + 1) = m
           <= 4 ** m * 4 ** (m + 1)        by binomial_middle_upper_bound
            = 4 ** (m + (m + 1))           by EXP_ADD
            = 4 ** (2 * m + 1)             by arithmetic
            = 4 ** n                       by n = 2 * m + 1
         Hence lcm_run n <= 4 ** n.
*)
Theorem lcm_run_upper_bound[allow_rebind]:
  !n. lcm_run n <= 4 ** n
Proof
  completeInduct_on `n` >>
  Cases_on `EVEN n` >| [
    Cases_on `n = 0` >-
    rw[lcm_run_0] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    qabbrev_tac `c = binomial n m * lcm_run m` >>
    `m <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run m <= 4 ** m` by rw[] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** m` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** m = 4 ** n` by metis_tac[EXP_ADD, TIMES2] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    Cases_on `n = 1` >-
    rw[lcm_run_1] >>
    qabbrev_tac `m = HALF n` >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `0 < m` by rw[] >>
    qabbrev_tac `c = binomial n (m + 1) * lcm_run (m + 1)` >>
    `m + 1 <= n` by decide_tac >>
    `0 < c` by metis_tac[binomial_pos, lcm_run_pos, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
    `lcm_run n <= c` by rw[lcm_run_divides_property, DIVIDES_LE, Abbr`c`] >>
    `lcm_run (m + 1) <= 4 ** (m + 1)` by rw[] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `binomial n m <= 4 ** m` by metis_tac[binomial_middle_upper_bound] >>
    `c <= 4 ** m * 4 ** (m + 1)` by rw[LESS_MONO_MULT2, Abbr`c`] >>
    `4 ** m * 4 ** (m + 1) = 4 ** n` by metis_tac[EXP_ADD, ADD_ASSOC, TIMES2] >>
    decide_tac
  ]
QED

(* This is the original proof of the upper bound. *)

(* ------------------------------------------------------------------------- *)
(* LCM Lower Bound using Maximum                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: POSITIVE l ==> MAX_LIST l <= list_lcm l *)
(* Proof:
   If l = [],
      Note MAX_LIST [] = 0          by MAX_LIST_NIL
       and list_lcm [] = 1          by list_lcm_nil
      Hence true.
   If l <> [],
      Let x = MAX_LIST l.
      Then MEM x l                  by MAX_LIST_MEM
       and x divides (list_lcm l)   by list_lcm_is_common_multiple
       Now 0 < list_lcm l           by list_lcm_pos, EVERY_MEM
        so x <= list_lcm l          by DIVIDES_LE, 0 < list_lcm l
*)
val list_lcm_ge_max = store_thm(
  "list_lcm_ge_max",
  ``!l. POSITIVE l ==> MAX_LIST l <= list_lcm l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[MAX_LIST_NIL, list_lcm_nil] >>
  `MEM (MAX_LIST l) l` by rw[MAX_LIST_MEM] >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  rw[list_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)] *)
(* Proof:
   Note !k. MEM k (binomial_horizontal n) ==> 0 < k by binomial_horizontal_pos_alt [1]

    list_lcm [1 .. (n + 1)]
  = list_lcm (leibniz_vertical n)                by notation
  = list_lcm (leibniz_horizontal n)              by leibniz_lcm_property
  = (n + 1) * list_lcm (binomial_horizontal n)   by leibniz_horizontal_lcm_alt
  >= (n + 1) * MAX_LIST (binomial_horizontal n)  by list_lcm_ge_max, [1], LE_MULT_LCANCEL
  = (n + 1) * binomial n (HALF n)                by binomial_horizontal_max
*)
val lcm_lower_bound_by_list_lcm = store_thm(
  "lcm_lower_bound_by_list_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= list_lcm [1 .. (n + 1)]``,
  rpt strip_tac >>
  `MAX_LIST (binomial_horizontal n) <= list_lcm (binomial_horizontal n)` by
  (irule list_lcm_ge_max >>
  metis_tac[binomial_horizontal_pos_alt]) >>
  `list_lcm (leibniz_vertical n) = list_lcm (leibniz_horizontal n)` by rw[leibniz_lcm_property] >>
  `_ = (n + 1) * list_lcm (binomial_horizontal n)` by rw[leibniz_horizontal_lcm_alt] >>
  `n + 1 <> 0` by decide_tac >>
  metis_tac[LE_MULT_LCANCEL, binomial_horizontal_max]);

(* Theorem: FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s *)
(* Proof:
   If s = {},
      Note MAX_SET {} = 0          by MAX_SET_EMPTY
       and big_lcm {} = 1          by big_lcm_empty
      Hence true.
   If s <> {},
      Let x = MAX_SET s.
      Then x IN s                  by MAX_SET_IN_SET
       and x divides (big_lcm s)   by big_lcm_is_common_multiple
       Now 0 < big_lcm s           by big_lcm_positive
        so x <= big_lcm s          by DIVIDES_LE, 0 < big_lcm s
*)
val big_lcm_ge_max = store_thm(
  "big_lcm_ge_max",
  ``!s. FINITE s /\ (!x. x IN s ==> 0 < x) ==> MAX_SET s <= big_lcm s``,
  rpt strip_tac >>
  Cases_on `s = {}` >-
  rw[MAX_SET_EMPTY, big_lcm_empty] >>
  `(MAX_SET s) IN s` by rw[MAX_SET_IN_SET] >>
  `0 < big_lcm s` by rw[big_lcm_positive] >>
  rw[big_lcm_is_common_multiple, DIVIDES_LE]);

(* Theorem: (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Claim: MAX_SET (IMAGE (binomial n) (count (n + 1))) <= big_lcm (IMAGE (binomial n) count (n + 1))
   Proof: By big_lcm_ge_max, this is to show:
          (1) FINITE (IMAGE (binomial n) (count (n + 1)))
              This is true                                    by FINITE_COUNT, IMAGE_FINITE
          (2) !x. x IN IMAGE (binomial n) (count (n + 1)) ==> 0 < x
              This is true                                    by binomial_pos, IN_IMAGE, IN_COUNT

     big_lcm (natural (n + 1))
   = (n + 1) * big_lcm (IMAGE (binomial n) (count (n + 1)))   by big_lcm_natural_eqn
   >= (n + 1) * MAX_SET (IMAGE (binomial n) (count (n + 1)))  by claim, LE_MULT_LCANCEL
   = (n + 1) * binomial n (HALF n)                            by binomial_row_max
*)
val lcm_lower_bound_by_big_lcm = store_thm(
  "lcm_lower_bound_by_big_lcm",
  ``!n. (n + 1) * binomial n (HALF n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `MAX_SET (IMAGE (binomial n) (count (n + 1))) <=
       big_lcm (IMAGE (binomial n) (count (n + 1)))` by
  ((irule big_lcm_ge_max >> rpt conj_tac) >-
  metis_tac[binomial_pos, IN_IMAGE, IN_COUNT, DECIDE``x < n + 1 ==> x <= n``] >>
  rw[]
  ) >>
  metis_tac[big_lcm_natural_eqn, LE_MULT_LCANCEL, binomial_row_max, DECIDE``n + 1 <> 0``]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM function                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n] *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But list_lcm [1 .. 1] = 1          by list_lcm_sing
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= list_lcm [1 .. 1]    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= list_lcm [1 .. n]   by lcm_lower_bound_by_list_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b          by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]
*)
val lcm_lower_bound_by_list_lcm_stirling = store_thm(
  "lcm_lower_bound_by_list_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= list_lcm [1 .. n]``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[list_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= list_lcm [1 .. n]` by metis_tac[lcm_lower_bound_by_list_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* Theorem: big_lcm (natural n) <= big_lcm (natural (n + 1)) *)
(* Proof:
   Note FINITE (natural n)                    by natural_finite
    and 0 < big_lcm (natural n)               by big_lcm_positive, natural_element
       big_lcm (natural n)
    <= lcm (SUC n) (big_lcm (natural n))      by LCM_LE, 0 < SUC n, 0 < big_lcm (natural n)
     = big_lcm ((SUC n) INSERT (natural n))   by big_lcm_insert
     = big_lcm (natural (SUC n))              by natural_suc
     = big_lcm (natural (n + 1))              by ADD1
*)
val big_lcm_non_decreasing = store_thm(
  "big_lcm_non_decreasing",
  ``!n. big_lcm (natural n) <= big_lcm (natural (n + 1))``,
  rpt strip_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `0 < big_lcm (natural n)` by rw[big_lcm_positive, natural_element] >>
  `big_lcm (natural (n + 1)) = big_lcm (natural (SUC n))` by rw[ADD1] >>
  `_ = big_lcm ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = lcm (SUC n) (big_lcm (natural n))` by rw[big_lcm_insert] >>
  rw[LCM_LE]);

(* Theorem: Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
            !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n) *)
(* Proof:
   Note ODD n ==> n <> 0                  by EVEN_0, EVEN_ODD
   If n = 1,
      Note 1 <= pi                        by 0 < pi
        so 2 <= 2 * pi                    by LE_MULT_LCANCEL, 2 <> 0
        or 1 < 2 * pi                     by arithmetic
      Thus 1 DIV (2 * pi) = 0             by ONE_DIV, 1 < 2 * pi
       and SQRT (1 DIV (2 * pi)) = 0      by ZERO_EXP, 0 ** h, h <> 0
       But big_lcm (natural 1) = 1        by list_lcm_sing, natural_1
        so SQRT (1 DIV (2 * pi)) * 2 ** 1 <= big_lcm (natural 1)    by MULT
   If n <> 1,
      Then 0 < n - 1.
      Let m = n - 1, then n = m + 1       by arithmetic
      and n * binomial m (HALF m) <= big_lcm (natural n)   by lcm_lower_bound_by_big_lcm
      Now !a b c. (a DIV b) * c = (a * c) DIV b            by DIV_1, MULT_RIGHT_1, c = c DIV 1, b * 1 = b
      Note ODD n ==> EVEN m               by EVEN_ODD_SUC, ADD1
           n * binomial m (HALF m)
         = n * (2 ** n DIV SQRT (2 * pi * m))     by binomial_middle_by_stirling
         = (2 ** n DIV SQRT (2 * pi * m)) * n     by MULT_COMM
         = (2 ** n * n) DIV (SQRT (2 * pi * m))   by above
         = (n * 2 ** n) DIV (SQRT (2 * pi * m))   by MULT_COMM
         = (n DIV SQRT (2 * pi * m)) * 2 ** n     by above
         = (SQRT (n DIV (2 * pi)) * 2 ** n        by assumption, m = n - 1
      Hence SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)
*)
val lcm_lower_bound_by_big_lcm_stirling = store_thm(
  "lcm_lower_bound_by_big_lcm_stirling",
  ``Stirling /\ (!n c. n DIV (SQRT (c * (n - 1))) = SQRT (n DIV c)) ==>
   !n. ODD n ==> (SQRT (n DIV (2 * pi))) * (2 ** n) <= big_lcm (natural n)``,
  rpt strip_tac >>
  `!n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))` by prove_tac[binomial_middle_by_stirling] >>
  `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
  Cases_on `n = 1` >| [
    `1 <= pi` by decide_tac >>
    `1 < 2 * pi` by decide_tac >>
    `1 DIV (2 * pi) = 0` by rw[ONE_DIV] >>
    `SQRT (1 DIV (2 * pi)) * 2 ** 1 = 0` by rw[] >>
    rw[big_lcm_sing],
    `0 < n - 1 /\ (n = (n - 1) + 1)` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `n * binomial m (HALF m) <= big_lcm (natural n)` by metis_tac[lcm_lower_bound_by_big_lcm] >>
    `EVEN m` by metis_tac[EVEN_ODD_SUC, ADD1] >>
    `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
    `n * binomial m (HALF m) = n * (2 ** n DIV SQRT (2 * pi * m))` by rw[] >>
    `_ = (n DIV SQRT (2 * pi * m)) * 2 ** n` by metis_tac[MULT_COMM] >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Extra Theorems (not used)                                                 *)
(* ------------------------------------------------------------------------- *)

(*
This is GCD_CANCEL_MULT by coprime p n, and coprime p n ==> coprime (p ** k) n by coprime_exp.
Note prime_not_divides_coprime.
*)

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m) *)
(* Proof:
   Note m divides n ==> ?q. n = q * m     by divides_def

   Claim: coprime p q
   Proof: By contradiction, suppose gcd p q <> 1.
          Since (gcd p q) divides p       by GCD_IS_GREATEST_COMMON_DIVISOR
             so gcd p q = p               by prime_def, gcd p q <> 1.
             or p divides q               by divides_iff_gcd_fix
          Now, m <> 0 because
               If m = 0, p * m = 0        by MULT_0
               Then m divides n and ~((p * m) divides n) are contradictory.
          Thus p * m divides q * m        by DIVIDES_MULTIPLE_IFF, MULT_COMM, p divides q, m <> 0
          But q * m = n, contradicting ~((p * m) divides n).

      gcd (p * m) n
    = gcd (p * m) (q * m)                 by n = q * m
    = m * gcd p q                         by GCD_COMMON_FACTOR, MULT_COMM
    = m * 1                               by coprime p q, from Claim
    = m
*)
val gcd_prime_product_property = store_thm(
  "gcd_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==> (gcd (p * m) n = m)``,
  rpt strip_tac >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `m <> 0` by metis_tac[MULT_0] >>
  `coprime p q` by
  (spose_not_then strip_assume_tac >>
  `(gcd p q) divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  `gcd p q = p` by metis_tac[prime_def] >>
  `p divides q` by rw[divides_iff_gcd_fix] >>
  metis_tac[DIVIDES_MULTIPLE_IFF, MULT_COMM]) >>
  metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1]);

(* Theorem: prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n) *)
(* Proof:
   Note m <> 0                             by MULT_0, m divides n /\ ~((p * m) divides n)
   and   m * lcm (p * m) n
       = gcd (p * m) n * lcm (p * m) n     by gcd_prime_product_property
       = (p * m) * n                       by GCD_LCM
       = (m * p) * n                       by MULT_COMM
       = m * (p * n)                       by MULT_ASSOC
   Thus   lcm (p * m) n = p * n            by MULT_LEFT_CANCEL
*)
val lcm_prime_product_property = store_thm(
  "lcm_prime_product_property",
  ``!p m n. prime p /\ m divides n /\ ~((p * m) divides n) ==>(lcm (p * m) n = p * n)``,
  rpt strip_tac >>
  `m <> 0` by metis_tac[MULT_0] >>
  `m * lcm (p * m) n = gcd (p * m) n * lcm (p * m) n` by rw[gcd_prime_product_property] >>
  `_ = (p * m) * n` by rw[GCD_LCM] >>
  `_ = m * (p * n)` by metis_tac[MULT_COMM, MULT_ASSOC] >>
  metis_tac[MULT_LEFT_CANCEL]);

(* Theorem: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides list_lcm [] ==> p divides PROD_SET (set [])
      Note list_lcm [] = 1                  by list_lcm_nil
       and PROD_SET (set [])
         = PROD_SET {}                      by LIST_TO_SET
         = 1                                by PROD_SET_EMPTY
      Hence conclusion is alredy in predicate, thus true.
   Step: prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l) ==>
         prime p /\ p divides list_lcm (h::l) ==> p divides PROD_SET (set (h::l))
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)        by LIST_TO_SET
      This is to show: p divides PROD_SET (h INSERT set l)

      Let x = list_lcm l.
      Since p divides (lcm h x)             by given
         so p divides (gcd h x) * (lcm h x) by DIVIDES_MULTIPLE
         or p divides h * x                 by GCD_LCM
        ==> p divides h  or  p divides x    by P_EUCLIDES
      Case: p divides h.
      If h IN set l, or MEM h l,
         Then h divides x                                       by list_lcm_is_common_multiple
           so p divides x                                       by DIVIDES_TRANS
         Thus p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE, MULT_COMM
      Case: p divides x.
      If h IN set l, or MEM h l,
         Then p divides PROD_SET (set l)                        by induction hypothesis
           or p divides PROD_SET (h INSERT set l)               by ABSORPTION
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)  by PROD_SET_INSERT
           or p divides PROD_SET (h INSERT set l)               by DIVIDES_MULTIPLE
*)
val list_lcm_prime_factor = store_thm(
  "list_lcm_prime_factor",
  ``!p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[] >>
  qabbrev_tac `x = list_lcm l` >>
  `(gcd h x) * (lcm h x) = h * x` by rw[GCD_LCM] >>
  `p divides (h * x)` by metis_tac[DIVIDES_MULTIPLE] >>
  `p divides h \/ p divides x` by rw[P_EUCLIDES] >| [
    Cases_on `h IN set l` >| [
      `h divides x` by rw[list_lcm_is_common_multiple, Abbr`x`] >>
      `p divides x` by metis_tac[DIVIDES_TRANS] >>
      fs[ABSORPTION],
      rw[PROD_SET_INSERT] >>
      metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
    ],
    Cases_on `h IN set l` >-
    fs[ABSORPTION] >>
    rw[PROD_SET_INSERT] >>
    metis_tac[DIVIDES_MULTIPLE]
  ]);

(* Theorem: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x *)
(* Proof:
   By induction on l.
   Base: prime p /\ p divides PROD_SET (set []) ==> ?x. MEM x [] /\ p divides x
          p divides PROD_SET (set [])
      ==> p divides PROD_SET {}            by LIST_TO_SET
      ==> p divides 1                      by PROD_SET_EMPTY
      ==> p = 1                            by DIVIDES_ONE
      This contradicts with 1 < p          by ONE_LT_PRIME
   Step: prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x ==>
         !h. prime p /\ p divides PROD_SET (set (h::l)) ==> ?x. MEM x (h::l) /\ p divides x
      Note PROD_SET (set (h::l))
         = PROD_SET (h INSERT set l)                              by LIST_TO_SET
      This is to show: ?x. ((x = h) \/ MEM x l) /\ p divides x    by MEM
      If h IN set l, or MEM h l,
         Then h INSERT set l = set l                              by ABSORPTION
         Thus ?x. MEM x l /\ p divides x                          by induction hypothesis
      If ~(h IN set l),
         Then PROD_SET (h INSERT set l) = h * PROD_SET (set l)    by PROD_SET_INSERT
         Thus p divides h \/ p divides (PROD_SET (set l))         by P_EUCLIDES
         Case p divides h.
              Take x = h, the result is true.
         Case p divides PROD_SET (set l).
              Then ?x. MEM x l /\ p divides x                     by induction hypothesis
*)
val list_product_prime_factor = store_thm(
  "list_product_prime_factor",
  ``!p l. prime p /\ p divides PROD_SET (set l) ==> ?x. MEM x l /\ p divides x``,
  strip_tac >>
  Induct >| [
    rpt strip_tac >>
    `PROD_SET (set []) = 1` by rw[PROD_SET_EMPTY] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1` by decide_tac >>
    metis_tac[DIVIDES_ONE],
    rw[] >>
    Cases_on `h IN set l` >-
    metis_tac[ABSORPTION] >>
    fs[PROD_SET_INSERT] >>
    `p divides h \/ p divides (PROD_SET (set l))` by rw[P_EUCLIDES] >-
    metis_tac[] >>
    metis_tac[]
  ]);

(* Theorem: prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x *)
(* Proof: by list_lcm_prime_factor, list_product_prime_factor *)
val list_lcm_prime_factor_member = store_thm(
  "list_lcm_prime_factor_member",
  ``!p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x``,
  rw[list_lcm_prime_factor, list_product_prime_factor]);

(* ------------------------------------------------------------------------- *)
(* Count Helper Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   over f s t      = !x. x IN s ==> f x IN t
   s bij_eq t      = ?f. BIJ f s t
   s =b= t         = ?f. BIJ f s t
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Set Theorems:
   over_inj            |- !f s t. INJ f s t ==> over f s t
   over_surj           |- !f s t. SURJ f s t ==> over f s t
   over_bij            |- !f s t. BIJ f s t ==> over f s t
   SURJ_CARD_IMAGE_EQ  |- !f s t. FINITE t /\ over f s t ==>
                                  (SURJ f s t <=> CARD (IMAGE f s) = CARD t)
   FINITE_SURJ_IFF     |- !f s t. FINITE t ==>
                                  (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t)
   INJ_IMAGE_BIJ_IFF   |- !f s t. INJ f s t <=> BIJ f s (IMAGE f s) /\ over f s t
   INJ_IFF_BIJ_IMAGE   |- !f s t. over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s))
   INJ_IMAGE_IFF       |- !f s t. INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t
   FUNSET_ALT          |- !P Q. FUNSET P Q = {f | over f P Q}

   Bijective Equivalence:
   bij_eq_empty        |- !s t. s =b= t ==> (s = {} <=> t = {})
   bij_eq_refl         |- !s. s =b= s
   bij_eq_sym          |- !s t. s =b= t <=> t =b= s
   bij_eq_trans        |- !s t u. s =b= t /\ t =b= u ==> s =b= u
   bij_eq_equiv_on     |- !P. $=b= equiv_on P
   bij_eq_finite       |- !s t. s =b= t ==> (FINITE s <=> FINITE t)
   bij_eq_count        |- !s. FINITE s ==> s =b= count (CARD s)
   bij_eq_card         |- !s t. s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t
   bij_eq_card_eq      |- !s t. FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t)

   Alternate characterisation of maps:
   surj_preimage_not_empty
                       |- !f s t. SURJ f s t <=>
                                  over f s t /\ !y. y IN t ==> preimage f s y <> {}
   inj_preimage_empty_or_sing
                       |- !f s t. INJ f s t <=>
                                  over f s t /\ !y. y IN t ==> preimage f s y = {} \/
                                                               SING (preimage f s y)
   bij_preimage_sing   |- !f s t. BIJ f s t <=>
                                  over f s t /\ !y. y IN t ==> SING (preimage f s y)
   surj_iff_preimage_card_not_0
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (SURJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) <> 0)
   inj_iff_preimage_card_le_1
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (INJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) <= 1)
   bij_iff_preimage_card_eq_1
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (BIJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) = 1)
   finite_surj_inj_iff |- !f s t. FINITE s /\ SURJ f s t ==>
                                  (INJ f s t <=>
                                   !e. e IN IMAGE (preimage f s) t ==> CARD e = 1)
*)

(* Overload a function from domain to range.

   NOTE: this is FUNSET --Chun Tian
 *)
val _ = temp_overload_on("over", ``\f s t. !x. x IN s ==> f x IN t``);
(* not easy to make this a good infix operator! *)

(* Theorem: INJ f s t ==> over f s t *)
(* Proof: by INJ_DEF. *)
Theorem over_inj:
  !f s t. INJ f s t ==> over f s t
Proof
  simp[INJ_DEF]
QED

(* Theorem: SURJ f s t ==> over f s t *)
(* Proof: by SURJ_DEF. *)
Theorem over_surj:
  !f s t. SURJ f s t ==> over f s t
Proof
  simp[SURJ_DEF]
QED

(* Theorem: BIJ f s t ==> over f s t *)
(* Proof: by BIJ_DEF, INJ_DEF. *)
Theorem over_bij:
  !f s t. BIJ f s t ==> over f s t
Proof
  simp[BIJ_DEF, INJ_DEF]
QED

(* Theorem: FINITE t /\ over f s t ==>
            (SURJ f s t <=> CARD (IMAGE f s) = CARD t) *)
(* Proof:
   If part: SURJ f s t ==> CARD (IMAGE f s) = CARD t
      Note IMAGE f s = t           by IMAGE_SURJ
      Hence true.
   Only-if part: CARD (IMAGE f s) = CARD t ==> SURJ f s t
      By contradiction, suppose ~SURJ f s t.
      Then IMAGE f s <> t          by IMAGE_SURJ
       but IMAGE f s SUBSET t      by IMAGE_SUBSET_TARGET
        so IMAGE f s PSUBSET t     by PSUBSET_DEF
       ==> CARD (IMAGE f s) < CARD t
                                   by CARD_PSUBSET
      This contradicts CARD (IMAGE f s) = CARD t.
*)
Theorem SURJ_CARD_IMAGE_EQ:
  !f s t. FINITE t /\ over f s t ==>
          (SURJ f s t <=> CARD (IMAGE f s) = CARD t)
Proof
  rw[EQ_IMP_THM] >-
  fs[IMAGE_SURJ] >>
  spose_not_then strip_assume_tac >>
  `IMAGE f s <> t` by rw[GSYM IMAGE_SURJ] >>
  `IMAGE f s PSUBSET t` by fs[IMAGE_SUBSET_TARGET, PSUBSET_DEF] >>
  imp_res_tac CARD_PSUBSET >>
  decide_tac
QED

(* Theorem: FINITE t ==>
            (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t) *)
(* Proof:
   If part: true       by SURJ_DEF, IMAGE_SURJ
   Only-if part: true  by SURJ_CARD_IMAGE_EQ
*)
Theorem FINITE_SURJ_IFF:
  !f s t. FINITE t ==>
          (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t)
Proof
  metis_tac[SURJ_CARD_IMAGE_EQ, SURJ_DEF]
QED

(* Note: this cannot be proved:
g `!f s t. FINITE t /\ over f s t ==>
          (INJ f s t <=> CARD (IMAGE f s) = CARD t)`;
Take f = I, s = count m, t = count n, with m <= n.
Then INJ I (count m) (count n)
and IMAGE I (count m) = (count m)
so CARD (IMAGE f s) = m, CARD t = n, may not equal.
*)

(* INJ_IMAGE_BIJ |- !s f. (?t. INJ f s t) ==> BIJ f s (IMAGE f s) *)

(* Theorem: INJ f s t <=> (BIJ f s (IMAGE f s) /\ over f s t) *)
(* Proof:
   If part: INJ f s t ==> BIJ f s (IMAGE f s) /\ over f s t
      Note BIJ f s (IMAGE f s)     by INJ_IMAGE_BIJ
       and over f s t by INJ_DEF
   Only-if: BIJ f s (IMAGE f s) /\ over f s t ==> INJ f s t
      By INJ_DEF, this is to show:
      (1) x IN s ==> f x IN t, true by given
      (2) x IN s /\ y IN s /\ f x = f y ==> x = y
          Note f x IN (IMAGE f s)  by IN_IMAGE
           and f y IN (IMAGE f s)  by IN_IMAGE
            so f x = f y ==> x = y by BIJ_IS_INJ
*)
Theorem INJ_IMAGE_BIJ_IFF:
  !f s t. INJ f s t <=> (BIJ f s (IMAGE f s) /\ over f s t)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[INJ_IMAGE_BIJ] >-
  fs[INJ_DEF] >>
  rw[INJ_DEF] >>
  metis_tac[BIJ_IS_INJ, IN_IMAGE]
QED

(* Theorem: over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s)) *)
(* Proof: by INJ_IMAGE_BIJ_IFF. *)
Theorem INJ_IFF_BIJ_IMAGE:
  !f s t. over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s))
Proof
  metis_tac[INJ_IMAGE_BIJ_IFF]
QED

(*
INJ_IMAGE  |- !f s t. INJ f s t ==> INJ f s (IMAGE f s)
*)

(* Theorem: INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t *)
(* Proof:
   Let P = over f s t.
   If part: INJ f s t ==> INJ f s (IMAGE f s) /\ P
      Note INJ f s (IMAGE f s)     by INJ_IMAGE
       and P is true               by INJ_DEF
   Only-if part: INJ f s (IMAGE f s) /\ P ==> INJ f s t
      Note s SUBSET s              by SUBSET_REFL
       and (IMAGE f s) SUBSET t    by IMAGE_SUBSET_TARGET
      Thus INJ f s t               by INJ_SUBSET
*)
Theorem INJ_IMAGE_IFF:
  !f s t. INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[INJ_IMAGE] >-
  fs[INJ_DEF] >>
  `s SUBSET s` by rw[] >>
  `(IMAGE f s) SUBSET t` by fs[IMAGE_SUBSET_TARGET] >>
  metis_tac[INJ_SUBSET]
QED

(* pred_setTheory:
FUNSET |- !P Q. FUNSET P Q = (\f. over f P Q)
*)

(* Theorem: FUNSET P Q = {f | over f P Q} *)
(* Proof: by FUNSET, EXTENSION *)
Theorem FUNSET_ALT:
  !P Q. FUNSET P Q = {f | over f P Q}
Proof
  rw[FUNSET, EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Bijective Equivalence                                                     *)
(* ------------------------------------------------------------------------- *)

(* Overload bijectively equal. *)
val _ = overload_on("bij_eq", ``\s t. ?f. BIJ f s t``);
val _ = set_fixity "bij_eq" (Infix(NONASSOC, 450)); (* same as relation *)

val _ = overload_on ("=b=", ``$bij_eq``);
val _ = set_fixity "=b=" (Infix(NONASSOC, 450));

(*
> BIJ_SYM;
val it = |- !s t. s bij_eq t <=> t bij_eq s: thm
> BIJ_SYM;
val it = |- !s t. s =b= t <=> t =b= s: thm
> FINITE_BIJ_COUNT_CARD
val it = |- !s. FINITE s ==> count (CARD s) =b= s: thm
*)

(* Theorem: s =b= t ==> (s = {} <=> t = {}) *)
(* Proof: by BIJ_EMPTY. *)
Theorem bij_eq_empty:
  !s t. s =b= t ==> (s = {} <=> t = {})
Proof
  metis_tac[BIJ_EMPTY]
QED

(* Theorem: s =b= s *)
(* Proof: by BIJ_I_SAME *)
Theorem bij_eq_refl:
  !s. s =b= s
Proof
  metis_tac[BIJ_I_SAME]
QED

(* Theorem alias *)
Theorem bij_eq_sym = BIJ_SYM;
(* val bij_eq_sym = |- !s t. s =b= t <=> t =b= s: thm *)

Theorem bij_eq_trans = BIJ_TRANS;
(* val bij_eq_trans = |- !s t u. s =b= t /\ t =b= u ==> s =b= u: thm *)

(* Idea: bij_eq is an equivalence relation on any set of sets. *)

(* Theorem: $=b= equiv_on P *)
(* Proof:
   By equiv_on_def, this is to show:
   (1) s IN P ==> s =b= s, true    by bij_eq_refl
   (2) s IN P /\ t IN P ==> (t =b= s <=> s =b= t)
       This is true                by bij_eq_sym
   (3) s IN P /\ s' IN P /\ t IN P /\
       BIJ f s s' /\ BIJ f' s' t ==> s =b= t
       This is true                by bij_eq_trans
*)
Theorem bij_eq_equiv_on:
  !P. $=b= equiv_on P
Proof
  rw[equiv_on_def] >-
  simp[bij_eq_refl] >-
  simp[Once bij_eq_sym] >>
  metis_tac[bij_eq_trans]
QED

(* Theorem: s =b= t ==> (FINITE s <=> FINITE t) *)
(* Proof: by BIJ_FINITE_IFF *)
Theorem bij_eq_finite:
  !s t. s =b= t ==> (FINITE s <=> FINITE t)
Proof
  metis_tac[BIJ_FINITE_IFF]
QED

(* This is the iff version of:
pred_setTheory.FINITE_BIJ_CARD;
|- !f s t. FINITE s /\ BIJ f s t ==> CARD s = CARD t
*)

(* Theorem: FINITE s ==> s =b= (count (CARD s)) *)
(* Proof: by FINITE_BIJ_COUNT_CARD, BIJ_SYM *)
Theorem bij_eq_count:
  !s. FINITE s ==> s =b= (count (CARD s))
Proof
  metis_tac[FINITE_BIJ_COUNT_CARD, BIJ_SYM]
QED

(* Theorem: s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t *)
(* Proof: by FINITE_BIJ_CARD, BIJ_SYM. *)
Theorem bij_eq_card:
  !s t. s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t
Proof
  metis_tac[FINITE_BIJ_CARD, BIJ_SYM]
QED

(* Theorem: FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t) *)
(* Proof:
   If part: s =b= t ==> CARD s = CARD t
      This is true                 by FINITE_BIJ_CARD
   Only-if part: CARD s = CARD t ==> s =b= t
      Let n = CARD s = CARD t.
      Note ?f. BIJ f s (count n)   by bij_eq_count
       and ?g. BIJ g (count n) t   by FINITE_BIJ_COUNT_CARD
      Thus s =b= t                 by bij_eq_trans
*)
Theorem bij_eq_card_eq:
  !s t. FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[FINITE_BIJ_CARD] >>
  `?f. BIJ f s (count (CARD s))` by rw[bij_eq_count] >>
  `?g. BIJ g (count (CARD t)) t` by rw[FINITE_BIJ_COUNT_CARD] >>
  metis_tac[bij_eq_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Alternate characterisation of maps.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SURJ f s t <=>
            over f s t /\ (!y. y IN t ==> preimage f s y <> {}) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> preimage f s y <> {}.
   If part: SURJ f s t ==> P /\ Q
      P is true                by SURJ_DEF
      Q is true                by preimage_def, SURJ_DEF
   Only-if part: P /\ Q ==> SURJ f s t
      This is true             by preimage_def, SURJ_DEF
*)
Theorem surj_preimage_not_empty:
  !f s t. SURJ f s t <=>
          over f s t /\ (!y. y IN t ==> preimage f s y <> {})
Proof
  rw[SURJ_DEF, preimage_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: INJ f s t <=>
            over f s t /\
            (!y. y IN t ==> (preimage f s y = {} \/
                             SING (preimage f s y))) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> preimage f s y = {} \/ SING (preimage f s y).
   If part: INJ f s t ==> P /\ Q
      P is true                          by INJ_DEF
      For Q, if preimage f s y <> {},
      Then ?x. x IN preimage f s y       by MEMBER_NOT_EMPTY
        or ?x. x IN s /\ f x = y         by in_preimage
      Thus !z. z IN preimage f s y ==> z = x
                                         by in_preimage, INJ_DEF
        or SING (preimage f s y)         by SING_DEF, EXTENSION
   Only-if part: P /\ Q ==> INJ f s t
      By INJ_DEF, this is to show:
         !x y. x IN s /\ y IN s /\ f x = f y ==> x = y
      Let z = f x, then z IN t           by over f s t
        so x IN preimage f s z           by in_preimage
       and y IN preimage f s z           by in_preimage
      Thus preimage f s z <> {}          by MEMBER_NOT_EMPTY
        so SING (preimage f s z)         by implication
       ==> x = y                         by SING_ELEMENT
*)
Theorem inj_preimage_empty_or_sing:
  !f s t. INJ f s t <=>
          over f s t /\
          (!y. y IN t ==> (preimage f s y = {} \/
                           SING (preimage f s y)))
Proof
  rw[EQ_IMP_THM] >-
  fs[INJ_DEF] >-
 ((Cases_on `preimage f s y = {}` >> simp[]) >>
  `?x. x IN s /\ f x = y` by metis_tac[in_preimage, MEMBER_NOT_EMPTY] >>
  simp[SING_DEF] >>
  qexists_tac `x` >>
  rw[preimage_def, EXTENSION] >>
  metis_tac[INJ_DEF]) >>
  rw[INJ_DEF] >>
  qabbrev_tac `z = f x` >>
  `z IN t` by fs[Abbr`z`] >>
  `x IN preimage f s z` by fs[preimage_def] >>
  `y IN preimage f s z` by fs[preimage_def] >>
  metis_tac[MEMBER_NOT_EMPTY, SING_ELEMENT]
QED

(* Theorem: BIJ f s t <=>
           over f s t /\
           (!y. y IN t ==> SING (preimage f s y)) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> SING (preimage f s y).
   If part: BIJ f s t ==> P /\ Q
      P is true                          by BIJ_DEF, INJ_DEF
      For Q,
      Note INJ f s t /\ SURJ f s t       by BIJ_DEF
        so preimage f s y <> {}          by surj_preimage_not_empty
      Thus SING (preimage f s y)         by inj_preimage_empty_or_sing
   Only-if part: P /\ Q ==> BIJ f s t
      Note !y. y IN t ==> (preimage f s y) <> {}
                                         by SING_DEF, NOT_EMPTY_SING
        so SURJ f s t                    by surj_preimage_not_empty
       and INJ f s t                     by inj_preimage_empty_or_sing
      Thus BIJ f s t                     by BIJ_DEF
*)
Theorem bij_preimage_sing:
  !f s t. BIJ f s t <=>
          over f s t /\
          (!y. y IN t ==> SING (preimage f s y))
Proof
  rw[EQ_IMP_THM] >-
  fs[BIJ_DEF, INJ_DEF] >-
  metis_tac[BIJ_DEF, surj_preimage_not_empty, inj_preimage_empty_or_sing] >>
  `INJ f s t` by metis_tac[inj_preimage_empty_or_sing] >>
  `SURJ f s t` by metis_tac[SING_DEF, NOT_EMPTY_SING, surj_preimage_not_empty] >>
  simp[BIJ_DEF]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (SURJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <> 0) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 0 <=> preimage f s y = {}
                                         by CARD_EQ_0
   The result follows                    by surj_preimage_not_empty
*)
Theorem surj_iff_preimage_card_not_0:
  !f s t. FINITE s /\ over f s t ==>
          (SURJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <> 0)
Proof
  metis_tac[surj_preimage_not_empty, preimage_finite, CARD_EQ_0]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (INJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <= 1) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 0 <=> preimage f s y = {}
                                         by CARD_EQ_0
    and !y. CARD (preimage f s y) = 1 <=> SING (preimage f s y)
                                         by CARD_EQ_1
   The result follows                    by inj_preimage_empty_or_sing, LE_ONE
*)
Theorem inj_iff_preimage_card_le_1:
  !f s t. FINITE s /\ over f s t ==>
          (INJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <= 1)
Proof
  metis_tac[inj_preimage_empty_or_sing, preimage_finite, CARD_EQ_0, CARD_EQ_1, LE_ONE]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (BIJ f s t <=> !y. y IN t ==> CARD (preimage f s y) = 1) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 1 <=> SING (preimage f s y)
                                         by CARD_EQ_1
   The result follows                    by bij_preimage_sing
*)
Theorem bij_iff_preimage_card_eq_1:
  !f s t. FINITE s /\ over f s t ==>
          (BIJ f s t <=> !y. y IN t ==> CARD (preimage f s y) = 1)
Proof
  metis_tac[bij_preimage_sing, preimage_finite, CARD_EQ_1]
QED

(* Theorem: FINITE s /\ SURJ f s t ==>
            (INJ f s t <=> !e. e IN IMAGE (preimage f s) t ==> CARD e = 1) *)
(* Proof:
   If part: INJ f s t /\ x IN t ==> CARD (preimage f s x) = 1
      Note BIJ f s t                     by BIJ_DEF
       and over f s t                    by BIJ_DEF, INJ_DEF
        so CARD (preimage f s x) = 1     by bij_iff_preimage_card_eq_1
   Only-if part: !e. (?x. e = preimage f s x /\ x IN t) ==> CARD e = 1 ==> INJ f s t
      Note over f s t                                  by SURJ_DEF
       and !x. x IN t ==> ?y. y IN s /\ f y = x        by SURJ_DEF
      Thus !y. y IN t ==> CARD (preimage f s y) = 1    by IN_IMAGE
        so INJ f s t                                   by inj_iff_preimage_card_le_1
*)
Theorem finite_surj_inj_iff:
  !f s t. FINITE s /\ SURJ f s t ==>
      (INJ f s t <=> !e. e IN IMAGE (preimage f s) t ==> CARD e = 1)
Proof
  rw[EQ_IMP_THM] >-
  prove_tac[BIJ_DEF, INJ_DEF, bij_iff_preimage_card_eq_1] >>
  fs[SURJ_DEF] >>
  `!y. y IN t ==> CARD (preimage f s y) = 1` by metis_tac[] >>
  rw[inj_iff_preimage_card_le_1]
QED

(* ------------------------------------------------------------------------- *)
(* Necklace Theory Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Necklace:
   necklace_def      |- !n a. necklace n a =
                              {ls | LENGTH ls = n /\ set ls SUBSET count a}
   necklace_element  |- !n a ls. ls IN necklace n a <=>
                                 LENGTH ls = n /\ set ls SUBSET count a
   necklace_length   |- !n a ls. ls IN necklace n a ==> LENGTH ls = n
   necklace_colors   |- !n a ls. ls IN necklace n a ==> set ls SUBSET count a
   necklace_property |- !n a ls. ls IN necklace n a ==>
                                 LENGTH ls = n /\ set ls SUBSET count a
   necklace_0        |- !a. necklace 0 a = {[]}
   necklace_empty    |- !n. 0 < n ==> (necklace n 0 = {})
   necklace_not_nil  |- !n a ls. 0 < n /\ ls IN necklace n a ==> ls <> []
   necklace_suc      |- !n a. necklace (SUC n) a =
                              IMAGE (\(c,ls). c::ls) (count a CROSS necklace n a)
!  necklace_eqn      |- !n a. necklace n a =
                              if n = 0 then {[]}
                              else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a)
   necklace_1        |- !a. necklace 1 a = {[e] | e IN count a}
   necklace_finite   |- !n a. FINITE (necklace n a)
   necklace_card     |- !n a. CARD (necklace n a) = a ** n

   Mono-colored necklace:
   monocoloured_def  |- !n a. monocoloured n a =
                              {ls | ls IN necklace n a /\ (ls <> [] ==> SING (set ls))}
   monocoloured_element
                     |- !n a ls. ls IN monocoloured n a <=>
                                 ls IN necklace n a /\ (ls <> [] ==> SING (set ls))
   monocoloured_necklace   |- !n a ls. ls IN monocoloured n a ==> ls IN necklace n a
   monocoloured_subset     |- !n a. monocoloured n a SUBSET necklace n a
   monocoloured_finite     |- !n a. FINITE (monocoloured n a)
   monocoloured_0    |- !a. monocoloured 0 a = {[]}
   monocoloured_1    |- !a. monocoloured 1 a = necklace 1 a
   necklace_1_monocoloured
                     |- !a. necklace 1 a = monocoloured 1 a
   monocoloured_empty|- !n. 0 < n ==> monocoloured n 0 = {}
   monocoloured_mono |- !n. monocoloured n 1 = necklace n 1
   monocoloured_suc  |- !n a. 0 < n ==>
                              monocoloured (SUC n) a = IMAGE (\ls. HD ls::ls) (monocoloured n a)
   monocoloured_0_card   |- !a. CARD (monocoloured 0 a) = 1
   monocoloured_card     |- !n a. 0 < n ==> CARD (monocoloured n a) = a
!  monocoloured_eqn      |- !n a. monocoloured n a =
                                  if n = 0 then {[]}
                                  else IMAGE (\c. GENLIST (K c) n) (count a)
   monocoloured_card_eqn |- !n a. CARD (monocoloured n a) = if n = 0 then 1 else a

   Multi-colored necklace:
   multicoloured_def     |- !n a. multicoloured n a = necklace n a DIFF monocoloured n a
   multicoloured_element |- !n a ls. ls IN multicoloured n a <=>
                                     ls IN necklace n a /\ ls <> [] /\ ~SING (set ls)
   multicoloured_necklace|- !n a ls. ls IN multicoloured n a ==> ls IN necklace n a
   multicoloured_subset  |- !n a. multicoloured n a SUBSET necklace n a
   multicoloured_finite  |- !n a. FINITE (multicoloured n a)
   multicoloured_0       |- !a. multicoloured 0 a = {}
   multicoloured_1       |- !a. multicoloured 1 a = {}
   multicoloured_n_0     |- !n. multicoloured n 0 = {}
   multicoloured_n_1     |- !n. multicoloured n 1 = {}
   multicoloured_empty   |- !n. multicoloured n 0 = {} /\ multicoloured n 1 = {}
   multi_mono_disjoint   |- !n a. DISJOINT (multicoloured n a) (monocoloured n a)
   multi_mono_exhaust    |- !n a. necklace n a = multicoloured n a UNION monocoloured n a
   multicoloured_card    |- !n a. 0 < n ==> (CARD (multicoloured n a) = a ** n - a)
   multicoloured_card_eqn|- !n a. CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a
   multicoloured_nonempty|- !n a. 1 < n /\ 1 < a ==> multicoloured n a <> {}
   multicoloured_not_monocoloured
                         |- !n a ls. ls IN multicoloured n a ==> ls NOTIN monocoloured n a
   multicoloured_not_monocoloured_iff
                         |- !n a ls. ls IN necklace n a ==>
                                     (ls IN multicoloured n a <=> ls NOTIN monocoloured n a)
   multicoloured_or_monocoloured
                         |- !n a ls. ls IN necklace n a ==>
                                     ls IN multicoloured n a \/ ls IN monocoloured n a
*)


(* ------------------------------------------------------------------------- *)
(* Helper Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Necklace                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define necklaces as lists of length n, i.e. with n beads, in a colors. *)
Definition necklace_def[nocompute]:
    necklace n a = {ls | LENGTH ls = n /\ (set ls) SUBSET (count a) }
End
(* Note: use [nocompute] as this is not effective. *)

(* Theorem: ls IN necklace n a <=> (LENGTH ls = n /\ (set ls) SUBSET (count a)) *)
(* Proof: by necklace_def *)
Theorem necklace_element:
  !n a ls. ls IN necklace n a <=> (LENGTH ls = n /\ (set ls) SUBSET (count a))
Proof
  simp[necklace_def]
QED

(* Theorem: ls IN (necklace n a) ==> LENGTH ls = n *)
(* Proof: by necklace_def *)
Theorem necklace_length:
  !n a ls. ls IN (necklace n a) ==> LENGTH ls = n
Proof
  simp[necklace_def]
QED

(* Theorem: ls IN (necklace n a) ==> set ls SUBSET count a *)
(* Proof: by necklace_def *)
Theorem necklace_colors:
  !n a ls. ls IN (necklace n a) ==> set ls SUBSET count a
Proof
  simp[necklace_def]
QED

(* Idea: If ls in (necklace n a), LENGTH ls = n and colors in count a. *)

(* Theorem: ls IN (necklace n a) ==> LENGTH ls = n /\ set ls SUBSET count a *)
(* Proof: by necklace_def *)
Theorem necklace_property:
  !n a ls. ls IN (necklace n a) ==> LENGTH ls = n /\ set ls SUBSET count a
Proof
  simp[necklace_def]
QED

(* ------------------------------------------------------------------------- *)
(* Know the necklaces.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: zero-length necklaces of whatever colors is the set of NIL. *)

(* Theorem: necklace 0 a = {[]} *)
(* Proof:
     necklace 0 a
   = {ls | (LENGTH ls = 0) /\ (set ls) SUBSET (count a) }  by necklace_def
   = {ls | ls = [] /\ (set []) SUBSET (count a) }          by LENGTH_NIL
   = {ls | ls = [] /\ [] SUBSET (count a) }                by LIST_TO_SET
   = {[]}                                                  by EMPTY_SUBSET
*)
Theorem necklace_0:
  !a. necklace 0 a = {[]}
Proof
  rw[necklace_def, EXTENSION] >>
  metis_tac[LIST_TO_SET, EMPTY_SUBSET]
QED

(* Idea: necklaces with some length but 0 colors is EMPTY. *)

(* Theorem: 0 < n ==> (necklace n 0 = {}) *)
(* Proof:
     necklace n 0
   = {ls | LENGTH ls = n /\ (set ls) SUBSET (count 0) }  by necklace_def
   = {ls | LENGTH ls = n /\ (set ls) SUBSET {}           by COUNT_0
   = {ls | LENGTH ls = n /\ (set ls = {}) }              by SUBSET_EMPTY
   = {ls | LENGTH ls = n /\ (ls = []) }                  by LIST_TO_SET_EQ_EMPTY
   = {}                                                  by LENGTH_NIL, 0 < n
*)
Theorem necklace_empty:
  !n. 0 < n ==> (necklace n 0 = {})
Proof
  rw[necklace_def, EXTENSION]
QED

(* Idea: A necklace of length n <> 0 is non-NIL. *)

(* Theorem: 0 < n /\ ls IN (necklace n a) ==> ls <> [] *)
(* Proof:
   By contradiction, suppose ls = [].
   Then n = LENGTH ls         by necklace_element
          = LENGTH [] = 0     by LENGTH_NIL
   This contradicts 0 < n.
*)
Theorem necklace_not_nil:
  !n a ls. 0 < n /\ ls IN (necklace n a) ==> ls <> []
Proof
  rw[necklace_def] >>
  metis_tac[LENGTH_NON_NIL]
QED

(* ------------------------------------------------------------------------- *)
(* To show: (necklace n a) is FINITE.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: Relate (necklace (n+1) a) to (necklace n a) for induction. *)

(* Theorem: necklace (SUC n) a =
            IMAGE (\(c, ls). c :: ls) (count a CROSS necklace n a) *)
(* Proof:
   By necklace_def, EXTENSION, this is to show:
   (1) LENGTH x = SUC n /\ set x SUBSET count a ==>
       ?h t. (x = h::t) /\ h < a /\ (LENGTH t = n) /\ set t SUBSET count a
       Note SUC n <> 0                   by SUC_NOT_ZERO
         so ?h t. x = h::t               by list_CASES
       Take these h, t, true             by LENGTH, MEM
   (2) h < a /\ set t SUBSET count a ==> x < a ==> LENGTH (h::t) = SUC (LENGTH t)
       This is true                      by LENGTH
   (3) h < a /\ set t SUBSET count a ==> set (h::t) SUBSET count a
       Note set (h::t) c <=>
            (c = h) \/ set t c           by LIST_TO_SET_DEF
       If c = h, h < a
          ==> h IN count a               by IN_COUNT
       If set t c, set t SUBSET count a
          ==> c IN count a               by SUBSET_DEF
       Thus set (h::t) SUBSET count a    by SUBSET_DEF
*)
Theorem necklace_suc:
  !n a. necklace (SUC n) a =
        IMAGE (\(c, ls). c :: ls) (count a CROSS necklace n a)
Proof
  rw[necklace_def, EXTENSION] >>
  rw[pairTheory.EXISTS_PROD, EQ_IMP_THM] >| [
    `SUC n <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    qexists_tac `h` >>
    qexists_tac `t` >>
    fs[],
    simp[],
    fs[]
  ]
QED

(* Idea: display the necklaces. *)

(* Theorem: necklace n a =
            if n = 0 then {[]}
            else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a) *)
(* Proof: by necklace_0, necklace_suc. *)
Theorem necklace_eqn[compute]:
  !n a. necklace n a =
        if n = 0 then {[]}
        else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a)
Proof
  rw[necklace_0] >>
  metis_tac[necklace_suc, num_CASES, SUC_SUB1]
QED

(*
> EVAL ``necklace 3 2``;
= {[1; 1; 1]; [1; 1; 0]; [1; 0; 1]; [1; 0; 0]; [0; 1; 1]; [0; 1; 0]; [0; 0; 1]; [0; 0; 0]}
> EVAL ``necklace 2 3``;
= {[2; 2]; [2; 1]; [2; 0]; [1; 2]; [1; 1]; [1; 0]; [0; 2]; [0; 1]; [0; 0]}
*)

(* Idea: Unit-length necklaces are singletons from (count a). *)

(* Theorem: necklace 1 a = {[e] | e IN count a} *)
(* Proof:
   Let f = (\(c,ls). c::ls).
     necklace 1 a
   = necklace (SUC 0) a                       by ONE
   = IMAGE f ((count a) CROSS (necklace 0 a)) by necklace_suc
   = IMAGE f ((count a) CROSS {[]})           by necklace_0
   = {[e] | e IN count a}                     by EXTENSION
*)
Theorem necklace_1:
  !a. necklace 1 a = {[e] | e IN count a}
Proof
  rewrite_tac[ONE] >>
  rw[necklace_suc, necklace_0, pairTheory.EXISTS_PROD, EXTENSION]
QED

(* Idea: The set of (necklace n a) is finite. *)

(* Theorem: FINITE (necklace n a) *)
(* Proof:
   By induction on n.
   Base: FINITE (necklace 0 a)
      Note necklace 0 a = {[]}           by necklace_0
       and FINITE {[]}                   by FINITE_SING
   Step: FINITE (necklace n a) ==> FINITE (necklace (SUC n) a)
      Let f = (\(c, ls). c :: ls), b = count a, c = necklace n a.
      Note necklace (SUC n) a
         = IMAGE f (b CROSS c)           by necklace_suc
       and FINITE b                      by FINITE_COUNT
       and FINITE c                      by induction hypothesis
        so FINITE (b CROSS c)            by FINITE_CROSS
      Thus FINITE (necklace (SUC n) a)   by IMAGE_FINITE
*)
Theorem necklace_finite:
  !n a. FINITE (necklace n a)
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[necklace_0] >>
  simp[necklace_suc]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (necklace n a) = a^n.                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: size of (necklace n a) = a^n. *)

(* Theorem: CARD (necklace n a) = a ** n *)
(* Proof:
   By induction on n.
   Base: CARD (necklace 0 a) = a ** 0
        CARD (necklace 0 a)
      = CARD {[]}                            by necklace_0
      = 1                                    by CARD_SING
      = a ** 0                               by EXP_0
   Step: CARD (necklace n a) = a ** n ==>
         CARD (necklace (SUC n) a) = a ** SUC n
      Let f = (\(c, ls). c :: ls), b = count a, c = necklace n a.
      Note FINITE b                          by FINITE_COUNT
       and FINITE c                          by necklace_finite
       and FINITE (b CROSS c)                by FINITE_CROSS
      Also INJ f (b CROSS c) univ(:num list) by INJ_DEF, CONS_11
           CARD (necklace (SUC n) a)
         = CARD (IMAGE f (b CROSS c))        by necklace_suc
         = CARD (b CROSS c)                  by INJ_CARD_IMAGE_EQN
         = CARD b * CARD c                   by CARD_CROSS
         = a * CARD c                        by CARD_COUNT
         = a * a ** n                        by induction hypothesis
         = a ** SUC n                        by EXP
*)
Theorem necklace_card:
  !n a. CARD (necklace n a) = a ** n
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[necklace_0] >>
  qabbrev_tac `f = (\(c:num, ls:num list). c :: ls)` >>
  qabbrev_tac `b = count a` >>
  qabbrev_tac `c = necklace n a` >>
  `FINITE b` by rw[FINITE_COUNT, Abbr`b`] >>
  `FINITE c` by rw[necklace_finite, Abbr`c`] >>
  `necklace (SUC n) a = IMAGE f (b CROSS c)` by rw[necklace_suc, Abbr`f`, Abbr`b`, Abbr`c`] >>
  `INJ f (b CROSS c) univ(:num list)` by rw[INJ_DEF, pairTheory.FORALL_PROD, Abbr`f`] >>
  `FINITE (b CROSS c)` by rw[FINITE_CROSS] >>
  `CARD (necklace (SUC n) a) = CARD (b CROSS c)` by rw[INJ_CARD_IMAGE_EQN] >>
  `_ = CARD b * CARD c` by rw[CARD_CROSS] >>
  `_ = a * a ** n` by fs[Abbr`b`, Abbr`c`] >>
  simp[EXP]
QED

(* ------------------------------------------------------------------------- *)
(* Mono-colored necklace - necklace with a single color.                     *)
(* ------------------------------------------------------------------------- *)

(* Define mono-colored necklace *)
Definition monocoloured_def[nocompute]:
    monocoloured n a =
       {ls | ls IN necklace n a /\ (ls <> [] ==> SING (set ls)) }
End
(* Note: use [nocompute] as this is not effective. *)

(* Theorem: ls IN monocoloured n a <=>
            ls IN necklace n a /\ (ls <> [] ==> SING (set ls)) *)
(* Proof: by monocoloured_def *)
Theorem monocoloured_element:
  !n a ls. ls IN monocoloured n a <=>
           ls IN necklace n a /\ (ls <> [] ==> SING (set ls))
Proof
  simp[monocoloured_def]
QED

(* ------------------------------------------------------------------------- *)
(* Know the Mono-coloured necklaces.                                         *)
(* ------------------------------------------------------------------------- *)

(* Idea: A monocoloured necklace is indeed a necklace. *)

(* Theorem: ls IN monocoloured n a ==> ls IN necklace n a *)
(* Proof: by monocoloured_def *)
Theorem monocoloured_necklace:
  !n a ls. ls IN monocoloured n a ==> ls IN necklace n a
Proof
  simp[monocoloured_def]
QED

(* Idea: The monocoloured set is subset of necklace set. *)

(* Theorem: (monocoloured n a) SUBSET (necklace n a) *)
(* Proof: by monocoloured_necklace, SUBSET_DEF *)
Theorem monocoloured_subset:
  !n a. (monocoloured n a) SUBSET (necklace n a)
Proof
  simp[monocoloured_necklace, SUBSET_DEF]
QED

(* Idea: The monocoloured set is FINITE. *)

(* Theorem: FINITE (monocoloured n a) *)
(* Proof:
   Note (monocoloured n a) SUBSET (necklace n a)  by monocoloured_subset
    and FINITE (necklace n a)                     by necklace_finite
     so FINITE (monocoloured n a)                 by SUBSET_FINITE
*)
Theorem monocoloured_finite:
  !n a. FINITE (monocoloured n a)
Proof
  metis_tac[monocoloured_subset, necklace_finite, SUBSET_FINITE]
QED

(* Idea: Zero-length monocoloured set is singleton NIL. *)

(* Theorem: monocoloured 0 a = {[]} *)
(* Proof:
     monocoloured 0 a
   = {ls | ls IN necklace 0 a /\ (ls <> [] ==> SING (set ls)) }  by monocoloured_def
   = {ls | ls IN {[]} /\ (ls <> [] ==> SING (set ls)) }          by necklace_0
   = {[]}                                                        by IN_SING
*)
Theorem monocoloured_0:
  !a. monocoloured 0 a = {[]}
Proof
  rw[monocoloured_def, necklace_0, EXTENSION, EQ_IMP_THM]
QED

(* Idea: Unit-length monocoloured set are necklaces of length 1. *)

(* Theorem: monocoloured 1 a = necklace 1 a *)
(* Proof:
   By necklace_def, monocoloured_def, EXTENSION,
   this is to show:
      (LENGTH x = 1) /\ set x SUBSET count a /\ (x <> [] ==> SING (set x)) <=>
      (LENGTH x = 1) /\ set x SUBSET count a
   This is true         by SING_LIST_TO_SET
*)
Theorem monocoloured_1:
  !a. monocoloured 1 a = necklace 1 a
Proof
  rw[necklace_def, monocoloured_def, EXTENSION] >>
  metis_tac[SING_LIST_TO_SET]
QED

(* Idea: Unit-length necklaces are monocoloured. *)

(* Theorem: necklace 1 a = monocoloured 1 a *)
(* Proof: by monocoloured_1 *)
Theorem necklace_1_monocoloured:
  !a. necklace 1 a = monocoloured 1 a
Proof
  simp[monocoloured_1]
QED

(* Idea: Some non-NIL necklaces are monocoloured. *)

(* Theorem: 0 < n ==> monocoloured n 0 = {} *)
(* Proof:
   Note (monocoloured n 0) SUBSET (necklace n 0)   by monocoloured_subset
    but necklace n 0 = {}                          by necklace_empty
     so monocoloured n 0 = {}                      by SUBSET_EMPTY
*)
Theorem monocoloured_empty:
  !n. 0 < n ==> monocoloured n 0 = {}
Proof
  metis_tac[monocoloured_subset, necklace_empty, SUBSET_EMPTY]
QED

(* Idea: One-colour necklaces are monocoloured. *)

(* Theorem: monocoloured n 1 = necklace n 1 *)
(* Proof:
   By monocoloured_def, necklace_def, EXTENSION,
   this is to show:
        set x SUBSET count 1 /\ x <> [] ==> SING (set x)
   Note count 1 = {0}           by COUNT_1
    and set x <> {}             by LIST_TO_SET
     so set x = {0}             by SUBSET_SING_IFF
     or SING (set x)            by SING_DEF
*)
Theorem monocoloured_mono:
  !n. monocoloured n 1 = necklace n 1
Proof
  rw[monocoloured_def, necklace_def, EXTENSION, EQ_IMP_THM] >>
  fs[COUNT_1] >>
  `set x = {0}` by fs[SUBSET_SING_IFF] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (monocoloured n a) = a.                                     *)
(* ------------------------------------------------------------------------- *)

(* Idea: Relate (monocoloured (SUC n) a) to (monocoloured n a) for induction. *)

(* Theorem: 0 < n ==> (monocoloured (SUC n) a =
                      IMAGE (\ls. HD ls :: ls) (monocoloured n a)) *)
(* Proof:
   By monocoloured_def, necklace_def, EXTENSION, this is to show:
   (1) 0 < n /\ LENGTH x = SUC n /\ set x SUBSET count a /\ x <> [] ==> SING (set x) ==>
       ?ls. (x = HD ls::ls) /\ (LENGTH ls = n /\ set ls SUBSET count a) /\
            (ls <> [] ==> SING (set ls))
       Note SUC n <> 0                   by SUC_NOT_ZERO
         so x <> []                      by LENGTH_NIL
        ==> ?h t. x = h::t               by list_CASES
        and LENGTH t = n                 by LENGTH
        but t <> []                      by LENGTH_NON_NIL, 0 < n
         so ?k p. t = k::p               by list_CASES
       Thus x = h::k::p                  by above
        Now h IN set x                   by MEM
        and k IN set x                   by MEM, SUBSET_DEF
         so h = k                        by IN_SING, SING (set x)
       Let ls = t,
       then set ls SUBSET count a        by MEM, SUBSET_DEF
        and SING (set ls)                by LIST_TO_SET_DEF
   (2) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       LENGTH (HD ls::ls) = SUC (LENGTH ls)
       This is true                      by LENGTH
   (3) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       set (HD ls::ls) SUBSET count a
       Note ls <> []                     by LENGTH_NON_NIL
         so ?h t. ls = h::t              by list_CASES
       Also set (h::ls) x <=>
            (x = h) \/ set t x           by LIST_TO_SET_DEF
       Thus set (h::ls) SUBSET count a   by SUBSET_DEF
   (4) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       SING (set (HD ls::ls))
       Note ls <> []                     by LENGTH_NON_NIL
         so ?h t. ls = h::t              by list_CASES
       Also set (h::ls) x <=>
            (x = h) \/ set t x           by LIST_TO_SET_DEF
       Thus SING (set (h::ls))           by SUBSET_DEF
*)
Theorem monocoloured_suc:
  !n a. 0 < n ==> (monocoloured (SUC n) a =
                  IMAGE (\ls. HD ls :: ls) (monocoloured n a))
Proof
  rw[monocoloured_def, necklace_def, EXTENSION] >>
  rw[pairTheory.EXISTS_PROD, EQ_IMP_THM] >| [
    `SUC n <> 0` by decide_tac >>
    `x <> [] /\ ?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `LENGTH t = n` by fs[] >>
    `t <> []` by metis_tac[LENGTH_NON_NIL] >>
    `h IN set x` by fs[] >>
    `?k p. t = k::p` by metis_tac[list_CASES] >>
    `HD t IN set x` by rfs[SUBSET_DEF] >>
    `HD t = h` by metis_tac[SING_DEF, IN_SING] >>
    qexists_tac `t` >>
    fs[],
    simp[],
    `ls <> [] /\ ?h t. ls = h::t` by metis_tac[LENGTH_NON_NIL, list_CASES] >>
    fs[],
    `ls <> [] /\ ?h t. ls = h::t` by metis_tac[LENGTH_NON_NIL, list_CASES] >>
    fs[]
  ]
QED

(* Idea: size of (monocoloured 0 a) = 1. *)

(* Theorem: CARD (monocoloured 0 a) = 1 *)
(* Proof:
   Note monocoloured 0 a = {[]}        by monocoloured_0
     so CARD (monocoloured 0 a) = 1    by CARD_SING
*)
Theorem monocoloured_0_card:
  !a. CARD (monocoloured 0 a) = 1
Proof
  simp[monocoloured_0]
QED

(* Idea: size of (monocoloured n a) = a. *)

(* Theorem: 0 < n ==> CARD (monocoloured n a) = a *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> (CARD (monocoloured 0 a) = a)
      True by 0 < 0 = F.
   Step: 0 < n ==> CARD (monocoloured n a) = a ==>
         0 < SUC n ==> (CARD (monocoloured (SUC n) a) = a)
      If n = 0,
         CARD (monocoloured (SUC 0) a)
       = CARD (monocoloured 1 a)             by ONE
       = CARD (necklace 1 a)                 by monocoloured_1
       = a ** 1                              by necklace_card
       = a                                   by EXP_1
      If n <> 0, then 0 < n.
         Let f = (\ls. HD ls :: ls).
         Then INJ f (monocoloured n a)
                    univ(:num list)          by INJ_DEF, CONS_11
          and FINITE (monocoloured n a)      by monocoloured_finite
          CARD (monocoloured (SUC n) a)
        = CARD (IMAGE f (monocoloured n a))  by monocoloured_suc
        = CARD (monocoloured n a)            by INJ_CARD_IMAGE_EQN
        = a                                  by induction hypothesis
*)
Theorem monocoloured_card:
  !n a. 0 < n ==> CARD (monocoloured n a) = a
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  (Cases_on `n = 0` >> simp[]) >-
  simp[monocoloured_1, necklace_card] >>
  qabbrev_tac `f = \ls:num list. HD ls :: ls` >>
  `INJ f (monocoloured n a) univ(:num list)` by rw[INJ_DEF, Abbr`f`] >>
  `FINITE (monocoloured n a)` by rw[monocoloured_finite] >>
  `CARD (monocoloured (SUC n) a) =
    CARD (IMAGE f (monocoloured n a))` by rw[monocoloured_suc, Abbr`f`] >>
  `_ = CARD (monocoloured n a)` by rw[INJ_CARD_IMAGE_EQN] >>
  fs[]
QED

(* Theorem: monocoloured n a =
            if n = 0 then {[]} else IMAGE (\c. GENLIST (K c) n) (count a) *)
(* Proof:
   If n = 0, true                            by monocoloured_0
   If n <> 0, then 0 < n.
   By monocoloured_def, necklace_def, EXTENSION, this is to show:
   (1) 0 < LENGTH x /\ set x SUBSET count a /\ x <> [] ==> SING (set x) ==>
       ?c. (x = GENLIST (K c) (LENGTH x)) /\ c < a
       Note x <> []                          by LENGTH_NON_NIL
         so ?c. set x = {c}                  by SING_DEF
       Then c < a                            by SUBSET_DEF, IN_COUNT
        and x = GENLIST (K c) (LENGTH x)     by LIST_TO_SET_SING_IFF
   (2) c < a ==> LENGTH (GENLIST (K c) n) = n,
       This is true                          by LENGTH_GENLIST
   (3) c < a ==> set (GENLIST (K c) n) SUBSET count a
       Note set (GENLIST (K c) n) = {c}      by GENLIST_K_SET
         so c < a ==> {c} SUBSET (count a)   by SUBSET_DEF
   (4) c < a /\ GENLIST (K c) n <> [] ==> SING (set (GENLIST (K c) n))
       Note set (GENLIST (K c) n) = {c}      by GENLIST_K_SET
         so SING (set (GENLIST (K c) n))     by SING_DEF
*)
Theorem monocoloured_eqn[compute]:
  !n a. monocoloured n a =
        if n = 0 then {[]}
        else IMAGE (\c. GENLIST (K c) n) (count a)
Proof
  rw_tac bool_ss[] >-
  simp[monocoloured_0] >>
  `0 < n` by decide_tac >>
  rw[monocoloured_def, necklace_def, EXTENSION, EQ_IMP_THM] >| [
    `x <> []` by metis_tac[LENGTH_NON_NIL] >>
    `SING (set x) /\ ?c. set x = {c}` by rw[GSYM SING_DEF] >>
    `c < a` by fs[SUBSET_DEF] >>
    `?b. x = GENLIST (K b) (LENGTH x)` by metis_tac[LIST_TO_SET_SING_IFF] >>
    metis_tac[GENLIST_K_SET, IN_SING],
    simp[],
    rw[GENLIST_K_SET],
    rw[GENLIST_K_SET]
  ]
QED

(*
> EVAL ``monocoloured 2 3``; = {[2; 2]; [1; 1]; [0; 0]}: thm
> EVAL ``monocoloured 3 2``; = {[1; 1; 1]; [0; 0; 0]}: thm
*)

(* Slight improvement of a previous result. *)

(* Theorem: CARD (monocoloured n a) = if n = 0 then 1 else a *)
(* Proof:
   If n = 0,
        CARD (monocoloured 0 a)
      = CARD {[]}                  by monocoloured_eqn
      = 1                          by CARD_SING
   If n <> 0, then 0 < n.
      Let f = (\c:num. GENLIST (K c) n).
      Then INJ f (count a) univ(:num list)
                                   by INJ_DEF, GENLIST_K_SET, IN_SING
       and FINITE (count a)        by FINITE_COUNT
        CARD (monocoloured n a)
      = CARD (IMAGE f (count a))   by monocoloured_eqn
      = CARD (count a)             by INJ_CARD_IMAGE_EQN
      = a                          by CARD_COUNT
*)
Theorem monocoloured_card_eqn:
  !n a. CARD (monocoloured n a) = if n = 0 then 1 else a
Proof
  rw[monocoloured_eqn] >>
  qmatch_abbrev_tac `CARD (IMAGE f (count a)) = a` >>
  `INJ f (count a) univ(:num list)` by
  (rw[INJ_DEF, Abbr`f`] >>
  `0 < n` by decide_tac >>
  metis_tac[GENLIST_K_SET, IN_SING]) >>
  rw[INJ_CARD_IMAGE_EQN]
QED

(* ------------------------------------------------------------------------- *)
(* Multi-colored necklace                                                    *)
(* ------------------------------------------------------------------------- *)

(* Define multi-colored necklace *)
Definition multicoloured_def:
    multicoloured n a = (necklace n a) DIFF (monocoloured n a)
End
(* Note: EVAL can handle set DIFF. *)

(*
> EVAL ``multicoloured 3 2``;
= {[1; 1; 0]; [1; 0; 1]; [1; 0; 0]; [0; 1; 1]; [0; 1; 0]; [0; 0; 1]}: thm
> EVAL ``multicoloured 2 3``;
= {[2; 1]; [2; 0]; [1; 2]; [1; 0]; [0; 2]; [0; 1]}: thm
*)

(* Theorem: ls IN multicoloured n a <=>
            ls IN necklace n a /\ ls <> [] /\ ~SING (set ls) *)
(* Proof:
       ls IN multicoloured n a
   <=> ls IN (necklace n a) DIFF (monocoloured n a)          by multicoloured_def
   <=> ls IN (necklace n a) /\ ls NOTIN (monocoloured n a)   by IN_DIFF
   <=> ls IN (necklace n a) /\
       ~ls IN necklace n a /\ (ls <> [] ==> SING (set ls))   by monocoloured_def
   <=> ls IN (necklace n a) /\ ls <> [] /\ ~SING (set ls)    by logical equivalence

       t /\ ~(t /\ (p ==> q))
     = t /\ (~t \/  ~(p ==> q))
     = t /\ ~t \/ (t /\ ~(~p \/ q))
     = t /\ (p /\ ~q)
*)
Theorem multicoloured_element:
  !n a ls. ls IN multicoloured n a <=>
           ls IN necklace n a /\ ls <> [] /\ ~SING (set ls)
Proof
  (rw[multicoloured_def, monocoloured_def, EQ_IMP_THM] >> simp[])
QED

(* ------------------------------------------------------------------------- *)
(* Know the Multi-coloured necklaces.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: multicoloured is a necklace. *)

(* Theorem: ls IN multicoloured n a ==> ls IN necklace n a *)
(* Proof: by multicoloured_def *)
Theorem multicoloured_necklace:
  !n a ls. ls IN multicoloured n a ==> ls IN necklace n a
Proof
  simp[multicoloured_def]
QED

(* Idea: The multicoloured set is subset of necklace set. *)

(* Theorem: (multicoloured n a) SUBSET (necklace n a) *)
(* Proof:
   Note multicoloured n a
      = (necklace n a) DIFF (monocoloured n a)       by multicoloured_def
     so (multicoloured n a) SUBSET (necklace n a)    by DIFF_SUBSET
*)
Theorem multicoloured_subset:
  !n a. (multicoloured n a) SUBSET (necklace n a)
Proof
  simp[multicoloured_def]
QED

(* Idea: multicoloured set is FINITE. *)

(* Theorem: FINITE (multicoloured n a) *)
(* Proof:
   Note multicoloured n a
      = (necklace n a) DIFF (monocoloured n a)    by multicoloured_def
    and FINITE (necklace n a)                     by necklace_finite
     so FINITE (multicoloured n a)                by FINITE_DIFF
*)
Theorem multicoloured_finite:
  !n a. FINITE (multicoloured n a)
Proof
  simp[multicoloured_def, necklace_finite, FINITE_DIFF]
QED

(* Idea: (multicoloured 0 a) is EMPTY. *)

(* Theorem: multicoloured 0 a = {} *)
(* Proof:
     multicoloured 0 a
   = (necklace 0 a) DIFF (monocoloured 0 a)  by multicoloured_def
   = {[]} - {[]}                             by necklace_0, monocoloured_0
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_0:
  !a. multicoloured 0 a = {}
Proof
  simp[multicoloured_def, necklace_0, monocoloured_0]
QED

(* Idea: (mutlicoloured 1 a) is also EMPTY. *)

(* Theorem: multicoloured 1 a = {} *)
(* Proof:
     multicoloured 1 a
   = (necklace 1 a) DIFF (monocoloured 1 a)  by multicoloured_def
   = (necklace 1 a) DIFF (necklace 1 a)      by monocoloured_1
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_1:
  !a. multicoloured 1 a = {}
Proof
  simp[multicoloured_def, monocoloured_1]
QED

(* Idea: (multicoloured n 0) without color is EMPTY. *)

(* Theorem: multicoloured n 0 = {} *)
(* Proof:
   If n = 0,
      Then multicoloured 0 0 = {}              by multicoloured_0
   If n <> 0, then 0 < n.
       multicoloured n 0
     = (necklace n 0) DIFF (monocoloured n 0)  by multicoloured_def
     = {} DIFF (monocoloured n 0)              by necklace_empty
     = {}                                      by EMPTY_DIFF
*)
Theorem multicoloured_n_0:
  !n. multicoloured n 0 = {}
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[multicoloured_0] >>
  simp[multicoloured_def, necklace_empty]
QED

(* Idea: (multicoloured n 1) with one color is EMPTY. *)

(* Theorem: multicoloured n 1 = {} *)
(* Proof:
      multicoloured n 1
   = (necklace n 1) DIFF (monocoloured n 1)  by multicoloured_def
   = {necklace n 1} DIFF (necklace n 1)      by monocoloured_mono
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_n_1:
  !n. multicoloured n 1 = {}
Proof
  simp[multicoloured_def, monocoloured_mono]
QED

(* Theorem: multicoloured n 0 = {} /\ multicoloured n 1 = {} *)
(* Proof: by multicoloured_n_0, multicoloured_n_1. *)
Theorem multicoloured_empty:
  !n. multicoloured n 0 = {} /\ multicoloured n 1 = {}
Proof
  simp[multicoloured_n_0, multicoloured_n_1]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (multicoloured n a) = a^n - a.                              *)
(* ------------------------------------------------------------------------- *)

(* Idea: a multicoloured necklace is not monocoloured. *)

(* Theorem: DISJOINT (multicoloured n a) (monocoloured n a) *)
(* Proof:
   Let s = necklace n a, t = monocoloured n a.
   Then multicoloured n a = s DIFF t      by multicoloured_def
     so DISJOINT (multicoloured n a) t    by DISJOINT_DIFF
*)
Theorem multi_mono_disjoint:
  !n a. DISJOINT (multicoloured n a) (monocoloured n a)
Proof
  simp[multicoloured_def, DISJOINT_DIFF]
QED

(* Idea: a necklace is either monocoloured or multicolored. *)

(* Theorem: necklace n a = (multicoloured n a) UNION (monocoloured n a) *)
(* Proof:
   Let s = necklace n a, t = monocoloured n a.
   Then multicoloured n a = s DIFF t      by multicoloured_def
    Now t SUBSET s                        by monocoloured_subset
     so necklace n a = s
      = (multicoloured n a) UNION t       by UNION_DIFF
*)
Theorem multi_mono_exhaust:
  !n a. necklace n a = (multicoloured n a) UNION (monocoloured n a)
Proof
  simp[multicoloured_def, monocoloured_subset, UNION_DIFF]
QED

(* Idea: size of (multicoloured n a) = a^n - a. *)

(* Theorem: 0 < n ==> (CARD (multicoloured n a) = a ** n - a) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note t SUBSET s                 by monocoloured_subset
    and FINITE s                   by necklace_finite
        CARD (multicoloured n a)
      = CARD (s DIFF t)            by multicoloured_def
      = CARD s - CARD t            by SUBSET_DIFF_CARD, t SUBSET s
      = a ** n - CARD t            by necklace_card
      = a ** n - a                 by monocoloured_card, 0 < n
*)
Theorem multicoloured_card:
  !n a. 0 < n ==> (CARD (multicoloured n a) = a ** n - a)
Proof
  rpt strip_tac >>
  `(monocoloured n a) SUBSET (necklace n a)` by rw[monocoloured_subset] >>
  `FINITE (necklace n a)` by rw[necklace_finite] >>
  simp[multicoloured_def, SUBSET_DIFF_CARD, necklace_card, monocoloured_card]
QED

(* Theorem: CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a *)
(* Proof:
   If n = 0,
        CARD (multicoloured 0 a)
      = CARD {}                    by multicoloured_0
      = 0                          by CARD_EMPTY
   If n <> 0, then 0 < n.
        CARD (multicoloured 0 a)
      = a ** n - a                 by multicoloured_card
*)
Theorem multicoloured_card_eqn:
  !n a. CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[multicoloured_0] >>
  simp[multicoloured_card]
QED

(* Idea: (multicoloured n a) NOT empty when 1 < n /\ 1 < a. *)

(* Theorem: 1 < n /\ 1 < a ==> (multicoloured n a) <> {} *)
(* Proof:
   Let s = multicoloured n a.
   Then FINITE s               by multicoloured_finite
    and CARD s = a ** n - a    by multicoloured_card
   Note a < a ** n             by EXP_LT, 1 < a, 1 < n
   Thus CARD s <> 0,
     or s <> {}                by CARD_EMPTY
*)
Theorem multicoloured_nonempty:
  !n a. 1 < n /\ 1 < a ==> (multicoloured n a) <> {}
Proof
  rpt strip_tac >>
  qabbrev_tac `s = multicoloured n a` >>
  `FINITE s` by rw[multicoloured_finite, Abbr`s`] >>
  `CARD s = a ** n - a` by rw[multicoloured_card, Abbr`s`] >>
  `a < a ** n` by rw[EXP_LT] >>
  `CARD s <> 0` by decide_tac >>
  rfs[]
QED

(* ------------------------------------------------------------------------- *)

(* For revised necklace proof using GCD. *)

(* Idea: multicoloured lists are not monocoloured. *)

(* Theorem: ls IN multicoloured n a ==> ~(ls IN monocoloured n a) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note multicoloured n a = s DIFF t   by multicoloured_def
     so ls IN multicoloured n a
    ==> ls NOTIN t                     by IN_DIFF
*)
Theorem multicoloured_not_monocoloured:
  !n a ls. ls IN multicoloured n a ==> ~(ls IN monocoloured n a)
Proof
  simp[multicoloured_def]
QED

(* Theorem: ls IN necklace n a ==>
            (ls IN multicoloured n a <=> ~(ls IN monocoloured n a)) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note multicoloured n a = s DIFF t   by multicoloured_def
     so ls IN multicoloured n a
    <=> ls IN s /\ ls NOTIN t          by IN_DIFF
*)
Theorem multicoloured_not_monocoloured_iff:
  !n a ls. ls IN necklace n a ==>
           (ls IN multicoloured n a <=> ~(ls IN monocoloured n a))
Proof
  simp[multicoloured_def]
QED

(* Theorem: ls IN necklace n a ==>
            ls IN multicoloured n a \/ ls IN monocoloured n a *)
(* Proof: by multicoloured_def. *)
Theorem multicoloured_or_monocoloured:
  !n a ls. ls IN necklace n a ==>
           ls IN multicoloured n a \/ ls IN monocoloured n a
Proof
  simp[multicoloured_def]
QED

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
    rename [‘x SUBSET count (n + 1)’, ‘CARD x = k + 1’] >>
    Cases_on `x SUBSET count n` >> simp[] >>
    `n IN x` by
      (fs[SUBSET_DEF] >> rename [‘m IN x’, ‘~(m < n)’] >>
       `m < n + 1` by simp[] >>
       `m = n` by decide_tac >>
       fs[]) >>
    qexists_tac `x DELETE n` >>
    `FINITE x` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    rw[] >- (rw[EQ_IMP_THM] >> simp[]) >>
    `x DELETE n SUBSET (count (n + 1)) DELETE n` by rw[SUBSET_DELETE_BOTH] >>
    `count (n + 1) DELETE n = count n` by rw[EXTENSION] >>
    fs[],

    rename [‘s SUBSET count n’, ‘x SUBSET count (n + 1)’] >>
    `x = n INSERT s` by fs[EXTENSION] >>
    `x SUBSET (n INSERT count n)` by rw[SUBSET_INSERT_BOTH] >>
    rfs[count_add1],

    rename [‘s SUBSET count n’, ‘CARD x = CARD s + 1’] >>
    `x = n INSERT s` by fs[EXTENSION] >>
    `n NOTIN s` by metis_tac[SUBSET_DEF, COUNT_NOT_SELF] >>
    `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    rw[],

    metis_tac[COUNT_SUBSET, SUBSET_TRANS, DECIDE “n <= n + 1”]
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
  rename [‘s IN sub_count n k’, ‘x IN sub_count n (k + 1)’] >>
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
the Steinhaus-Johnson-Trotter algorithm, due to re-discovery by various people.
Outside mathematics, this method was known already to 17th-century English change ringers.
Equivalently, this algorithm finds a Hamiltonian cycle in the permutohedron.

Steinhaus-Johnson-Trotter algorithm
https://en.wikipedia.org/wiki/Steinhaus-Johnson-Trotter_algorithm

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
Theorem list_count_set_map_element:
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
   = (binomial n n) * FACT n   by arrange_formula
   = 1 * FACT n                by binomial_n_n
   = perm n                    by perm_eq_fact
*)
Theorem arrange_n_n:
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

val _ = export_theory ();
