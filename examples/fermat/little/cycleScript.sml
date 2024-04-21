(* ------------------------------------------------------------------------- *)
(* Cycle Theory -- simplifed to be valid for any n.                          *)
(* ------------------------------------------------------------------------- *)

(*

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
*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "cycle";

(* ------------------------------------------------------------------------- *)

(* open dependent theories *)
open arithmeticTheory gcdTheory pred_setTheory listTheory rich_listTheory
     combinatoricsTheory;

(* ------------------------------------------------------------------------- *)
(* Cycle Theory Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
!  rotate1 ls    = DROP 1 ls ++ TAKE 1 ls
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Cycle Theory:
   cycle_def     |- !n ls. cycle n ls = FUNPOW (\ls. rotate1 ls) n ls
   cycle_0       |- !ls. cycle 0 ls = ls
   cycle_1       |- !ls. cycle 1 ls = rotate1 ls
   cycle_suc     |- !n ls. cycle (SUC n) ls = cycle 1 (cycle n ls)
   cycle_add     |- !m n ls. cycle n (cycle m ls) = cycle (n + m) ls

   How cycle affects a list:
   cycle_nil           |- !n. cycle n [] = []
   cycle_eq_nil        |- !n ls. cycle n ls = [] <=> ls = []
   cycle_1_length      |- !ls. LENGTH (cycle 1 ls) = LENGTH ls
   cycle_same_length   |- !n ls. LENGTH (cycle n ls) = LENGTH ls
   cycle_1_set         |- !ls. set (cycle 1 ls) = set ls
   cycle_same_set      |- !n ls. set (cycle n ls) = set ls
   cycle_eq_drop_take  |- !n ls. n <= LENGTH ls ==> cycle n ls = DROP n ls ++ TAKE n ls
   cycle_head_to_element
                       |- !n ls. n < LENGTH ls ==> HD (cycle n ls) = EL n ls
   cycle_back          |- !ls. cycle (LENGTH ls) ls = ls
   cycle_back_multiple |- !n ls. cycle (n * LENGTH ls) ls = ls
   cycle_mod_length    |- !n ls. cycle n ls = cycle (n MOD LENGTH ls) ls
   cycle_addition      |- !m n ls. cycle m (cycle n ls) = cycle ((m + n) MOD LENGTH ls) ls
   cycle_inv           |- !n ls. n <= LENGTH ls ==> cycle (LENGTH ls - n) (cycle n ls) = ls
   cycle_1_fix         |- !n ls. cycle 1 ls = ls ==> cycle n ls = ls
   mono_has_cycle_1    |- !ls. (LENGTH ls = 1) ==> cycle 1 ls = ls
   sing_has_cycle_1    |- !ls. SING (set ls) ==> cycle 1 ls = ls
   cycle_1_eq          |- !h t. cycle 1 (h::t) = t ++ [h]
   cycle_1_neq         |- !h k t. k IN set t /\ k <> h ==> cycle 1 (h::t) <> h::t
   cycle_1_set_sing    |- !ls. ls <> [] /\ cycle 1 ls = ls ==> SING (set ls)
   cycle_1_iff_set_sing|- !ls. ls <> [] /\ cycle 1 ls = ls <=> SING (set ls)

   For revised necklace proof using GCD:
   cycle_multiple_back |- !m n ls. cycle n ls = ls ==> cycle (m * n) ls = ls
   cycle_gcd_back      |- !m n ls. cycle m ls = ls /\ cycle n ls = ls ==>
                                   cycle (gcd m n) ls = ls

   Relationship with rotate:
   cycle_alt     |- !n ls. cycle n ls = FUNPOW (rotate 1) n ls
   cycle_1_alt   |- !ls. cycle 1 ls = rotate 1 ls
   cycle_n_alt   |- !n ls. n <= LENGTH ls ==> cycle n ls = rotate n ls
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* remove overload of TWICE, SQ *)
val _ = clear_overloads_on "TWICE";
val _ = clear_overloads_on "SQ";

(* ------------------------------------------------------------------------- *)
(* Cycle Theory -- using FUNPOW of rotate once.                              *)
(* ------------------------------------------------------------------------- *)

(* Define cycle as action from Z[n] to (necklace n a). *)

(* Overload rotate of a list *)
val _ = temp_overload_on("rotate1", ``\ls. DROP 1 ls ++ TAKE 1 ls``);
(* Note: use temp_overload, as this is "rotate 1" in helperList. *)

(* Cycle as nth iterate of rotate *)
Definition cycle_def:
   cycle n ls = FUNPOW rotate1 n ls
End
(* Note: This is defined for all n, even n > LENGTH l.

Examples:

> EVAL ``cycle 0 [2;3;4;5]``; = [2; 3; 4; 5]
> EVAL ``cycle 1 [2;3;4;5]``; = [3; 4; 5; 2]
> EVAL ``cycle 2 [2;3;4;5]``; = [4; 5; 2; 3]
> EVAL ``cycle 3 [2;3;4;5]``; = [5; 2; 3; 4]
> EVAL ``cycle 4 [2;3;4;5]``; = [2; 3; 4; 5]
> EVAL ``cycle 7 [2;3;4;5]``; = [5; 2; 3; 4]
*)

(* ------------------------------------------------------------------------- *)
(* Properties of Cycles: additive.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cycle 0 ls = ls *)
(* Proof:
     cycle 0 ls
   = FUNPOW rotate1 0 ls   by cycle_def
   = ls                    by FUNPOW_0
*)
Theorem cycle_0:
  !ls. cycle 0 ls = ls
Proof
  simp[cycle_def]
QED

(* Theorem: cycle 1 ls = rotate1 ls  *)
(* Proof:
     cycle 1 ls
   = FUNPOW rotate1 1 ls      by cycle_def
   = rotate1 ls               by FUNPOW_1
*)
Theorem cycle_1:
  !ls. cycle 1 ls = rotate1 ls
Proof
  simp[cycle_def]
QED

(* Idea: cycle (n+1) of a list is cycle once more of cycle n list. *)

(* Theorem: cycle (SUC n) ls = cycle 1 (cycle n ls) *)
(* Proof:
     cycle (SUC n) ls
   = FUNPOW rotate1 (SUC n) ls       by cycle_def
   = rotate1 (FUNPOW rotate1) n ls)  by FUNPOW_SUC
   = rotate1 (cycle n ls)            by cycle_def
   = FUNPOW rotate1 1 (cycle n ls)   by FUNPOW_1
   = cycle 1 (cycle n ls)            by cycle_def
*)
Theorem cycle_suc:
  !n ls. cycle (SUC n) ls = cycle 1 (cycle n ls)
Proof
  simp[cycle_def, FUNPOW_SUC]
QED

(* Idea: cycle is additive. *)

(* Theorem: cycle n (cycle m ls) = cycle (n + m) ls  *)
(* Proof:
     cycle n (cycle m ls)
   = FUNPOW rotate1 n (FUNPOW rotate1 m ls)  by cycle_def
   = FUNPOW rotate1 (n + m) ls               by FUNPOW_ADD
   = cycle (n + m) ls                        by cycle_def
*)
Theorem cycle_add:
  !m n ls. cycle n (cycle m ls) = cycle (n + m) ls
Proof
  simp[cycle_def, FUNPOW_ADD]
QED

(* ------------------------------------------------------------------------- *)
(* How cycle affects a list.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cycle n [] = [] *)
(* Proof:
   By induction on n:
   Base: cycle 0 [] = [], true             by cycle_0
   Step: cycle n [] = [] ==> cycle (SUC n) [] = []
           cycle (SUC n) []
         = FUNPOW rotate1 (SUC n) []       by cycle_def
         = rotate1 (FUNPOW rotate1 n [])   by FUNPOW_SUC
         = rotate1 []                      by induction hypothesis
         = DROP 1 [] ++ TAKE 1 []          by notation
         = [] ++ []                        by DROP_nil, TAKE_nil
         = []                              by APPEND
*)
Theorem cycle_nil:
  !n. cycle n [] = []
Proof
  Induct >-
  simp[cycle_0] >>
  fs[cycle_def, FUNPOW_SUC]
QED

(* Idea: Only NIL will cycle to NIL. *)

(* Theorem: cycle n ls = [] <=> ls = [] *)
(* Proof:
   If part: cycle n ls = [] ==> ls = []
   By induction on n:
   Base: (cycle 0 ls = []) ==> ls = []
            ls
          = cycle 0 ls                         by cycle_0
          = []                                 by given
   Step: cycle n ls = [] ==> ls = []
         ==> (cycle (SUC n) ls = []) ==> ls = []
           cycle (SUC n) ls
         = FUNPOW (rotate1) (SUC n) ls         by cycle_def
         = rotate1 (FUNPOW (rotate1 n ls))     by FUNPOW_SUC
         = rotate1 (cycle n ls)                by cycle_def
         = DROP 1 (cycle n ls) ++ TAKE 1 (cycle n ls)
                                               by notation
         Thus cycle (SUC n) ls = []
          ==> DROP 1 (cycle n ls) = []
          and TAKE 1 (cycle n ls) = []         by APPEND_EQ_NIL
          ==> cycle n ls = []                  by DROP_EQ_NIL, TAKE_EQ_NIL, 1 <> 0
          ==> ls = []                          by inductive hypothesis
   Only-if part: cycle n [] = [], true         by cycle_nil
*)
Theorem cycle_eq_nil:
  !n ls. cycle n ls = [] <=> ls = []
Proof
  rw[EQ_IMP_THM] >| [
    Induct_on `n` >-
    simp[cycle_0] >>
    rw[cycle_def, FUNPOW_SUC],
    simp[cycle_nil]
  ]
QED

(* Idea: cycle keeps LENGTH unchanged. *)

(* Theorem: LENGTH (cycle 1 ls) = LENGTH ls *)
(* Proof:
   If ls = [],
     LENGTH (cycle 1 [])
   = LENGTH []                                 by cycle_0
   Otherwise ls = h::t.
     LENGTH (cycle 1 (h::t))
   = LENGTH (FUNPOW rotate1 1 (h::t))          by cycle_def
   = LENGTH (DROP 1 (h::t) ++ TAKE 1 (h::t))   by notation
   = LENGTH (DROP 1 (h::t)) +
     LENGTH (TAKE 1 (h::t))                    by LENGTH_APPEND
   = LENGTH t + LENGTH [h]                     by DROP, TAKE
   = LENGTH t + 1                              by LENGTH
   = LENGTH (h::t)                             by LENGTH
*)
Theorem cycle_1_length:
  !ls. LENGTH (cycle 1 ls) = LENGTH ls
Proof
  rw[cycle_def] >>
  Cases_on `ls` >-
  simp[] >>
  simp[]
QED

(* Idea: cycle keeps LENGTH (of necklace). *)

(* Theorem: LENGTH (cycle n ls) = LENGTH ls *)
(* Proof:
   By induction on n.
   Base: LENGTH (cycle 0 ls) = LENGTH ls
           LENGTH (cycle 0 ls)
         = LENGTH ls                     by cycle_0
   Step: LENGTH (cycle n ls) = LENGTH ls
         ==> LENGTH (cycle (SUC n) ls) = LENGTH ls
           LENGTH (cycle (SUC n) ls)
         = LENGTH (cycle 1 (cycle n ls)  by cycle_suc
         = LENGTH (cycle n ls)           by cycle_1_length
         = LENGTH ls                     by inductive hypothesis
*)
Theorem cycle_same_length:
  !n ls. LENGTH (cycle n ls) = LENGTH ls
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[cycle_0] >>
  rw[cycle_suc, cycle_1_length]
QED

(* Idea: cycle keep set unchanged. *)

(* Theorem: set (cycle 1 ls) = set ls *)
(* Proof:
   If ls = [],
     set (cycle 1 [])
   = set []                                 by cycle_0
   Otherwise ls = h::t.
     set (cycle 1 (h::t))
   = set (FUNPOW rotate1 1 (h::t))          by cycle_def
   = set (DROP 1 (h::t) ++ TAKE 1 (h::t))   by notation
   = set (DROP 1 (h::t)) UNION
     set (TAKE 1 (h::t))                    by LIST_TO_SET_APPEND
   = set t UNION set [h]                    by DROP, TAKE
   = set t UNION {h}                        by LIST_TO_SET_THM
   = set (h::t)                             by EXTENSION
*)
Theorem cycle_1_set:
  !ls. set (cycle 1 ls) = set ls
Proof
  rw[cycle_def] >>
  Cases_on `ls` >-
  simp[] >>
  simp[EXTENSION, DISJ_COMM]
QED

(* Idea: cycle keep set (of colors). *)

(* Theorem: set (cycle n ls) = set ls *)
(* Proof:
   By induction on n.
   Base: set (cycle 0 ls) = set ls
           set (cycle 0 ls)
         = set ls                        by cycle_0
   Step: set (cycle n ls) = set ls
         ==> set (cycle (SUC n) ls) = set ls
           set (cycle (SUC n) l))
         = set (cycle 1 (cycle n l)      by cycle_suc
         = set (cycle n l)               by cycle_1_set
         = set l                         by inductive hypothesis
*)
Theorem cycle_same_set:
  !n ls. set (cycle n ls) = set ls
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[cycle_0] >>
  rw[cycle_suc, cycle_1_set]
QED

(* ------------------------------------------------------------------------- *)
(* To show:  cycle x (cycle y ls) = cycle ((x + y) MOD n) ls, n = LENGTH ls. *)
(* This is required for Group Action.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: For n <= LENGTH ls, (cycle n ls) is the append of DROP and TAKE. *)

(* Theorem: n <= LENGTH ls ==> cycle n ls = DROP n ls ++ TAKE n ls *)
(* Proof:
   If ls = [],
      to show: n <= LENGTH [] ==> cycle n [] = DROP n [] ++ TAKE n []
      Note LENGTH [] = 0                    by LENGTH_NIL
        so n = 0                            by arithmetic
           cycle n []
         = []                               by cycle_nil
         = [] ++ []                         by APPEND_EQ_NIL
         = DROP n [] ++ TAKE n []           by DROP_nil, TAKE_nil
   If ls <> [].
     to show: n <= LENGTH ls /\ ls <> [] ==> cycle n ls = DROP n ls ++ TAKE n ls
     By induction on n.
     Base: 0 <= LENGTH ls ==> (cycle 0 ls = DROP 0 ls ++ TAKE 0 ls)
        cycle 0 ls
      = ls                                  by cycle_0
      = ls ++ []                            by APPEND_NIL
      = DROP 0 ls ++ TAKE 0 ls              by DROP_0, TAKE_0
     Step: ls <> [] /\ n <= LENGTH ls ==> cycle n ls = DROP n ls ++ TAKE n ls ==>
           SUC n <= LENGTH ls ==> (cycle (SUC n) ls = DROP (SUC n) ls ++ TAKE (SUC n) ls)
     Note DROP n ls <> []                   by DROP_EQ_NIL, n < LENGTH ls, [1]
        cycle (SUC n) ls
      = cycle 1 (cycle n ls)                by cycle_suc
      = cycle 1 (DROP n ls ++ TAKE n ls)    by inductive hypothesis
      = DROP 1 (DROP n ls ++ TAKE n ls) ++
        TAKE 1 (DROP n ls ++ TAKE n ls)     by cycle_def
      = DROP 1 (DROP n ls) ++ (TAKE n ls) ++
        TAKE 1 (DROP n ls)                  by DROP_1_APPEND, TAKE_1_APPEND, [1]
      = DROP (SUC n) ls ++ TAKE (SUC n) ls  by DROP_SUC, TAKE_SUC
*)
Theorem cycle_eq_drop_take:
  !n ls. n <= LENGTH ls ==> cycle n ls = DROP n ls ++ TAKE n ls
Proof
  rpt strip_tac >>
  Cases_on `ls = []` >-
  fs[cycle_0] >>
  Induct_on `n` >-
  rw[cycle_0] >>
  rw[cycle_suc] >>
  fs[cycle_def] >>
  rw[DROP_SUC, TAKE_SUC, DROP_1_APPEND, TAKE_1_APPEND, DROP_EQ_NIL]
QED

(* Idea: head of (cycle n ls) = element n ls. *)

(* Theorem: n < LENGTH ls ==> HD (cycle n ls) = EL n ls *)
(* Proof:
   By induction on ls, with !n.
   Base: !n. n < LENGTH [] ==> (HD (cycle n []) = EL n [])
      Note LENGTH [] = 0, and n < 0 = F, hence true.
   Step: !n. n < LENGTH ls ==> HD (cycle n ls) = EL n ls ==>
         !h n. n < LENGTH (h::ls) ==> (HD (cycle n (h::ls)) = EL n (h::ls))
      If n = 0,
           HD (cycle 0 (h::ls))
         = HD (h::ls)               by cycle_0
         = EL 0 (h::ls)             by EL
      If n <> 0, 0 < n.
         Note LENGTH (h::ls)
            = SUC (LENGTH ls)       by LENGTH
           so n - 1 < LENGTH ls     by n <> 0
         Let d = DROP (n - 1) ls,
             t = TAKE (n - 1) ls.
         Note LENGTH d
            = LENGTH ls - (n - 1)   by LENGTH_DROP
            <> 0                    by n - 1 < LENGTH ls
           so d <> []               by LENGTH_NIL
          and ?p q. d = p::q        by list_CASES

           HD (cycle n (h::ls))
         = HD (DROP n (h::ls) ++ TAKE n (h::ls))    by cycle_eq_drop_take
         = HD (DROP (n - 1) ls ++ h::t)             by DROP, TAKE, notation of t
         = HD (p::q ++ h::t)                        by above, d = p::q
         = p = HD (p::q ++ t) = HD (d ++ t)         by HD_APPEND twice, d = p::q
         = HD (DROP (n - 1) ls ++ TAKE (n - 1) ls)  by notations of d and t
         = HD (cycle (n - 1) ls)                    by cycle_eq_drop_take
         = EL (n - 1) ls                            by induction hypothesis
         = EL n (h::ls)                             by EL_TAIL
*)
Theorem cycle_head_to_element:
  !n ls. n < LENGTH ls ==> HD (cycle n ls) = EL n ls
Proof
  Induct_on `ls` >-
  simp[] >>
  fs[cycle_eq_drop_take] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[] >>
  `n - 1 < LENGTH ls` by decide_tac >>
  `LENGTH (DROP (n-1) ls) = LENGTH ls - (n - 1)` by rw[LENGTH_DROP] >>
  `LENGTH (DROP (n-1) ls) <> 0` by decide_tac >>
  `DROP (n-1) ls <> []` by fs[] >>
  `HD (DROP (n - 1) ls ++ h::TAKE (n - 1) ls) = EL (n-1) ls` by metis_tac[HD_APPEND, list_CASES] >>
  fs[EL_TAIL]
QED

(* Idea: cycle through length gives original. *)

(* Theorem: cycle (LENGTH ls) ls = ls. *)
(* Proof:
     cycle (LENGTH ls) ls
   = DROP (LENGTH ls) ls ++
     TAKE (LENGTH ls) ls       by cycle_eq_drop_take
   = [] ++ ls                  by DROP_LENGTH_NIL, TAKE_LENGTH_ID
   = ls                        by APPEND
*)
Theorem cycle_back:
  !ls. cycle (LENGTH ls) ls = ls
Proof
  rw[cycle_eq_drop_take, DROP_LENGTH_NIL]
QED

(* Theorem: cycle (n * LENGTH ls) ls = ls. *)
(* Proof:
   By induction on n.
   Base: cycle (0 * LENGTH ls) ls = ls
      cycle (0 * LENGTH ls) ls
    = cycle 0 ls                 by arithmetic
    = ls                         by cycle_0
   Step: cycle (n * LENGTH ls) ls = ls ==>
         cycle (SUC n * LENGTH ls) ls = ls
      cycle (SUC n * LENGTH ls) ls
    = cycle (LENGTH ls + n * LENGTH ls) ls          by MULT_SUC
    = cycle (LENGTH ls) (cycle (n * LENGTH ls) ls)  by cycle_add
    = cycle (LENGTH ls) ls                          by inductive hypothesis
    = ls                                            by cycle_back
*)
Theorem cycle_back_multiple:
  !n ls. cycle (n * LENGTH ls) ls = ls
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[cycle_0] >>
  `SUC n * LENGTH ls = LENGTH ls + n * LENGTH ls` by rw[MULT_SUC] >>
  metis_tac[cycle_add, cycle_back]
QED

(* Idea: cycle n ls = cycle k ls, where k = n MOD (LENGTH ls). *)

(* Theorem: cycle n ls = cycle (n MOD (LENGTH ls)) ls *)
(* Proof:
   If ls = [], true                            by cycle_nil
   Otherwise ls <> [].
   Let k = LENGTH ls, then 0 < k               by LENGTH_NON_NIL, ls <> []
     cycle n ls
   = cycle (n DIV k * k + n MOD k) ls          by DIVISION, 0 < k
   = cycle (n MOD k + n DIV k * k) ls          by arithmetic
   = cycle (n MOD k) (cycle (n DIV k * k) ls)  by cycle_add
   = cycle (n MOD k) ls                        by cycle_back_multiple
*)
Theorem cycle_mod_length:
  !n ls. cycle n ls = cycle (n MOD (LENGTH ls)) ls
Proof
  rpt strip_tac >>
  Cases_on `ls = []` >-
  simp[cycle_nil] >>
  qabbrev_tac `k = LENGTH ls` >>
  `0 < k` by rw[LENGTH_NON_NIL, Abbr`k`] >>
  `n = n DIV k * k + n MOD k` by rw[DIVISION] >>
  `_ = n MOD k + n DIV k * k` by decide_tac >>
  metis_tac[cycle_add, cycle_back_multiple]
QED

(* Idea: cycle m (cycle n ls) = cycle k ls, where k = (m + n) MOD LENGTH ls. *)

(* Theorem: cycle m (cycle n ls) = cycle ((m + n) MOD LENGTH ls) ls *)
(* Proof:
     cycle m (cycle n ls)
   = cycle (m + n) ls                  by cycle_add
   = cycle ((m + n) MOD LENGTH ls) ls  by cycle_mod_length
*)
Theorem cycle_addition:
  !m n ls. cycle m (cycle n ls) = cycle ((m + n) MOD LENGTH ls) ls
Proof
  metis_tac[cycle_add, cycle_mod_length]
QED

(* Idea: a cycle can be undone by another cycle. *)

(* Theorem: cycle m (cycle n ls) = ls  when  m + n = LENGTH ls. *)
(* Proof:
     cycle (LENGTH ls - n) (cycle n ls)
   = cycle (LENGTH ls - n + n) ls        by cycle_add
   = cycle (LENGTH ls) ls                by arithmetic
   = ls                                  by cycle_back
*)
Theorem cycle_inv:
  !n ls. n <= LENGTH ls ==> cycle (LENGTH ls - n) (cycle n ls) = ls
Proof
  rpt strip_tac >>
  `LENGTH ls - n + n = LENGTH ls` by decide_tac >>
  simp[cycle_add, cycle_back]
QED

(* ------------------------------------------------------------------------- *)
(* Some results related to: cycle 1 l = l.                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: cycle 1 ls = ls makes cycle trivial. *)

(* Theorem: cycle 1 ls = ls ==> cycle n ls = ls  *)
(* Proof:
   By induction on n:
   Base: cycle 0 ls = ls, true   by cycle_0
   Step: cycle n ls = ls ==> cycle (SUC n) ls = ls
      cycle (SUC n) ls
    = cycle 1 (cycle n ls)       by cycle_suc
    = cycle 1 ls                 by inductive hypothesis
    = ls                         by given
*)
Theorem cycle_1_fix:
  !n ls. cycle 1 ls = ls ==> cycle n ls = ls
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[cycle_0] >>
  simp[cycle_suc]
QED

(* Idea: a mono-list ls has cycle 1 ls = ls. *)

(* Theorem: LENGTH ls = 1 ==> cycle 1 ls = ls  *)
(* Proof:
   Note LENGTH ls <> 0, ls <> []         by LENGTH_NIL
     so ?h t.  ls = h::t                 by list_CASES
    and LENGTH ls = 1 ==> LENGTH t = 0   by LENGTH_APPEND, and h::t = [h] ++ t.
     so t = []                           by LENGTH_NIL
     cycle 1 ls
   = cycle 1 [h]                         by ls = [h]
   = DROP 1 [h] ++ TAKE 1 [h]            by cycle_def
   = [h]                                 by DROP, TAKE
   = ls                                  by ls = [h]
*)
Theorem mono_has_cycle_1:
  !ls. (LENGTH ls = 1) ==> cycle 1 ls = ls
Proof
  rpt strip_tac >>
  `?h t. ls = h::t` by metis_tac[LENGTH_NIL, list_CASES, DECIDE``1 <> 0``] >>
  `_ = [h] ++ t` by rw[] >>
  `LENGTH [h] = 1` by rw[] >>
  `LENGTH t = 0` by fs[] >>
  `t = []` by metis_tac[LENGTH_NIL] >>
  fs[cycle_def]
QED

(* Idea: a list with set singleton has cycle 1 ls = ls. *)

(* Theorem: SING (set ls) ==> cycle 1 ls = ls *)
(* Proof:
   If ls = [],
      cycle 1 [] = []                  by cycle_nil
   Otherwise, ls = h::t                by list_CASES
      cycle 1 (h::t)
    = FUNPOW rotate1 1 (h::t)          by cycle_def
    = rotate1 (h::t)                   by FUNPOW_1
    = DROP 1 (h::t) ++ TAKE 1 (h::t)   by notation
    = t ++ [h]                         by DROP, TAKE
    But SING (set (h::t))
    means set t = {h}                  by SING_INSERT
    Thus t ++ [h] = [h] ++ t           by MONOLIST_EQ
      or cycle 1 (h::t) = h::t
*)
Theorem sing_has_cycle_1:
  !ls. SING (set ls) ==> cycle 1 ls = ls
Proof
  rw[cycle_def] >>
  Cases_on `ls` >-
  simp[] >>
  fs[SING_INSERT] >>
  simp[MONOLIST_EQ]
QED

(* Theorem: cycle 1 (h::t) = t ++ [h] *)
(* Proof:
     cycle 1 (h::t)
   = rotate1 (h::t)                    by cycle_1
   = DROP 1 (h::t) ++ TAKE 1 (h::t)    by notation
   = t ++ [h]                          by DROP, TAKE
*)
Theorem cycle_1_eq:
  !h t. cycle 1 (h::t) = t ++ [h]
Proof
  simp[cycle_def]
QED

(* Idea: (t ++ [h] <> h::t) if (set t) has some element k <> h. *)

(* Theorem: k IN set t /\ k <> h ==> (cycle 1 (h::t) <> h::t) *)
(* Proof:
   Note k IN set t <=> MEM k t.
   By cycle_def, this is to show:
      MEM k t /\ k <> h ==> t ++ [h] <> h::t
   By induction on t.
   Base: MEM k [] ==> [] ++ [h] <> [h]
         Since MEM k [] = F, hence true   by MEM
   Step: MEM k t ==> t ++ [h] <> h::t ==>
         !h'. MEM k (h'::t) ==> h'::t ++ [h] <> h::h'::t
         Note MEM k (h'::t) ==>
              (k = h') \/ MEM k t
         If k = h',
              h'::t ++ [h]
            = k::t ++ [h] <> h::k::t      by APPEND
         If MEM k t
              h'::t ++ [h]
            = h'::(t ++ [h])              by APPEND
           <> h'::(h::t)                  by induction hypothesis
           still <> h::h'::t
*)
Theorem cycle_1_neq:
  !h k t. k IN set t /\ k <> h ==> (cycle 1 (h::t) <> h::t)
Proof
  rw[cycle_def] >>
  Induct_on `t` >>
  simp[]
QED

(* Idea: inverse of sing_has_cycle_1. *)

(* Theorem: cycle 1 ls = ls ==> SING (set ls)  *)
(* Proof:
   By contradiction, suppose ~SING (set ls).
   Note ?h t. ls = h::t            by list_CASES, ls <> []
   thus set t <> {h}               by ls = h::t
    ==> ?k. k IN set t /\ k <> h   by NON_MONO_TAIL_PROPERTY
        t ++ [h]
      = cycle 1 (h::t)             by cycle_1_eq
    ==> cycle 1 (h::t) <> h::t     by cycle_1_neq
   This contradicts cycle 1 ls = ls.
*)
Theorem cycle_1_set_sing:
  !ls. ls <> [] /\ cycle 1 ls = ls ==> SING (set ls)
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `?h t. ls = h::t` by metis_tac[list_CASES] >>
  fs[] >>
  `?k. k IN set t /\ k <> h` by rw[NON_MONO_TAIL_PROPERTY] >>
  metis_tac[cycle_1_eq, cycle_1_neq]
QED

(* Idea: a list has cycle 1 iff its set is a singleton. *)

(* Theorem: ls <> [] /\ cycle 1 ls = ls <=> SING (set ls) *)
(* Proof:
   If part: ls <> [] /\ cycle 1 ls = ls ==> SING (set ls)
      This is true               by cycle_1_set_sing
   Only-if part: SING (set ls) ==> ls <> [] /\ cycle 1 ls = ls
      Note ?c. set ls = {c}      by SING_DEF
       and {c} <> {}             by NOT_EMPTY_SING
        or ls <> []              by LIST_TO_SET, set [] = {}
       and cycle 1 ls = ls       by sing_has_cycle_1
*)
Theorem cycle_1_iff_set_sing:
  !ls. ls <> [] /\ cycle 1 ls = ls <=> SING (set ls)
Proof
  rw[EQ_IMP_THM] >-
  simp[cycle_1_set_sing] >-
  metis_tac[SING_DEF, NOT_EMPTY_SING, LIST_TO_SET] >>
  simp[sing_has_cycle_1]
QED

(* ------------------------------------------------------------------------- *)
(* For revised necklace proof using GCD.                                     *)
(* ------------------------------------------------------------------------- *)

(* Idea: if a value n can cycle back, multiples of n can also cycle back. *)

(* Theorem: cycle n ls = ls ==> cycle (m * n) ls = ls *)
(* Proof:
   By induction on m.
   Base: cycle (0 * n) ls = ls
      cycle (0 * n) ls
    = cycle 0 ls                   by arithmetic
    = ls                           by cycle_0
   Step: cycle (m * n) ls = ls ==>
         cycle (SUC m * n) ls = ls
      cycle (SUC m * n) ls
    = cycle (m * n + n) ls         by MULT_CLAUSES
    = cycle (m * n) (cycle n ls)   by cycle_add
    = cycle (m * n) ls             by given
    = ls                           by induction hypothesis
*)
Theorem cycle_multiple_back:
  !m n ls. cycle n ls = ls ==> cycle (m * n) ls = ls
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[cycle_0] >>
  metis_tac[MULT_CLAUSES, cycle_add]
QED

(* Idea: if two values m, n can cycle back, gcd(m,n) can also cycle back. *)

(* Theorem: cycle m ls = ls /\ cycle n ls = ls ==> cycle (gcd m n) ls = ls *)
(* Proof:
   If n = 0,
        cycle (gcd m 0) ls
      = cycle m ls           by GCD_0R
      = ls                   by given
   If n <> 0,
   Note ?p q. p * n = q * m + gcd m n       by LINEAR_GCD, n <> 0
        cycle (gcd m n) ls
      = cycle (gcd m n) (cycle m ls)        by given
      = cycle (gcd m n) (cycle (q * m) ls)  by cycle_multiple_back
      = cycle (gcd m n + q * m) ls          by cycle_add
      = cycle (q * m + gcd m n) ls          by arithmetic
      = cycle (p * n) ls                    by substitution
      = cycle n ls                          by cycle_multiple_back
      = ls                                  by given
*)
Theorem cycle_gcd_back:
  !m n ls. cycle m ls = ls /\ cycle n ls = ls ==> cycle (gcd m n) ls = ls
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[GCD_0R] >>
  `?p q. p * n = q * m + gcd m n` by rw[LINEAR_GCD] >>
  `cycle (gcd m n) ls = cycle (gcd m n) (cycle (q * m) ls)` by fs[cycle_multiple_back] >>
  metis_tac[cycle_add, ADD_COMM, cycle_multiple_back]
QED

(* ------------------------------------------------------------------------- *)
(* Relationship with rotate.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cycle n ls = FUNPOW (rotate 1) n ls *)
(* Proof:
   Note rotate1 = rotate 1   by rotate_def, FUN_EQ_THM
     cycle n ls
   = FUNPOW rotate1 n ls     by cycle_def
   = FUNPOW (rotate 1) n ls  by above
*)
Theorem cycle_alt:
  !n ls. cycle n ls = FUNPOW (rotate 1) n ls
Proof
  rw[cycle_def] >>
  `rotate1 = rotate 1` by rw[rotate_def, FUN_EQ_THM] >>
  simp[]
QED

(* Theorem: cycle 1 ls = rotate 1 ls *)
(* Proof:
     cycle 1 ls
   = FUNPOW (rotate 1) 1 ls   by cycle_alt
   = rotate 1 ls              by FUNPOW_1
*)
Theorem cycle_1_alt:
  !ls. cycle 1 ls = rotate 1 ls
Proof
  simp[cycle_alt]
QED

(* Theorem: n <= LENGTH ls ==> cycle n ls = rotate n ls *)
(* Proof:
     cycle n ls
   = DROP n ls ++ TAKE n ls   by cycle_eq_drop_take
   = rotate n ls              by rotate_def
*)
Theorem cycle_n_alt:
  !n ls. n <= LENGTH ls ==> cycle n ls = rotate n ls
Proof
  simp[rotate_def, cycle_eq_drop_take]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
