(* ------------------------------------------------------------------------- *)
(* Iteration Period Computation                                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "iterateCompute";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
open helperFunctionTheory;
open helperSetTheory;
open helperNumTheory;

(* arithmeticTheory -- load by default *)
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def *)

open iterationTheory;
open listTheory rich_listTheory listRangeTheory;
open helperListTheory; (* for listRangeINC_SNOC *)

(* val _ = load "helperTwosqTheory"; *)
open helperTwosqTheory; (* for WHILE_RULE_PRE_POST *)
open whileTheory; (* for WHILE definition *)


(* ------------------------------------------------------------------------- *)
(* Iteration Period Computation Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading: (! = temp)
!  iterate x f j  = FUNPOW f j x
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Iterative Search, by recursion with cutoff:
   iterate_search_def  |- !x j g f c b. iterate_search f g x c b j =
                                        if c <= j then b
                                        else if g x then x
                                        else iterate_search f g (f x) c b (j + 1)
   iterate_search_over |- !f g x c b j. c <= j ==> iterate_search f g x c b j = b
   iterate_search_exit |- !f g x c b j. j < c /\ g x ==> iterate_search f g x c b j = x
   iterate_search_next |- !f g x c b j. j < c /\ ~g x ==>
                          iterate_search f g x c b j =
                          iterate_search f g (f x) c b (j + 1)
   iterate_search_run  |- !f g x c b j k. 0 < k /\ j + k <= c /\
                          (!i. i < k ==> ~g (FUNPOW f i x)) ==>
                          iterate_search f g x c b j =
                          iterate_search f g (FUNPOW f k x) c b (j + k)
   iterate_search_done |- !f g x c b j n. 0 < n /\ j + n < c /\
                          (!i. i < n ==> ~g (FUNPOW f i x)) /\
                          g (FUNPOW f n x) ==> iterate_search f g x c b j = FUNPOW f n x
   iterate_search_thm  |- !f g x c b n. n < c /\ (!i. i < n ==> ~g (FUNPOW f i x)) /\
                          g (FUNPOW f n x) ==> iterate_search f g x c b 0 = FUNPOW f n x

   Iterative Loop, using WHILE construct:
   iterate_trace_def   |- !a b c. iterate_trace a b c = MAP (\j. iterate a b j) [0 .. c]
   iterate_trace_length|- !a b c. LENGTH (iterate_trace a b c) = 1 + c
   iterate_trace_non_nil
                       |- !a b c. iterate_trace a b c <> []
   iterate_trace_sing  |- !a b. iterate_trace a b 0 = [a]
   iterate_trace_0     |- !a b. iterate_trace a b 0 = [a]
   iterate_trace_suc   |- !a b c. iterate_trace a b (SUC c) = SNOC (iterate a b (SUC c)) (iterate_trace a b c)
   iterate_trace_head  |- !a b c. HD (iterate_trace a b c) = a
   iterate_trace_last  |- !a b c. LAST (iterate_trace a b c) = iterate a b c
   iterate_trace_element
                       |- !a b c j. j <= c ==> EL j (iterate_trace a b c) = iterate a b j
   iterate_trace_element_idx
                       |- !a b c ls j. ls = iterate_trace a b c /\ ALL_DISTINCT ls /\
                                       j <= c ==> findi (iterate a b j) ls = j
   iterate_trace_member|- !a b c ls x. ls = iterate_trace a b c /\ x <> iterate a b c /\
                               MEM x ls ==> MEM (b x) ls
   iterate_trace_member_iff
                       |- !a b c ls x. ls = iterate_trace a b c ==>
                              (MEM x ls <=> ?j. j <= c /\ (x = iterate a b j))
   iterate_trace_index |- !a b c ls x. ls = iterate_trace a b c /\ x <> iterate a b c /\
                              MEM x ls /\ ALL_DISTINCT ls ==>
                              (findi (b x) ls = 1 + findi x ls)
   iterate_trace_all_distinct
                       |- !s a b c p. FINITE s /\ b PERMUTES s /\ a IN s /\
                              p = iterate_period b a /\ c < p ==>
                              ALL_DISTINCT (iterate_trace a b c)
   iterate_while_hoare |- !s a b c p g n. FINITE s /\ b PERMUTES s /\ a IN s /\
                              p = iterate_period b a /\ n < c /\ c < p /\
                              ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
                              HOARE_SPEC {a} (WHILE g b) {iterate a b n}
   iterate_while_thm_1 |- !s a b c p g n. FINITE s /\ b PERMUTES s /\ a IN s /\
                              p = iterate_period b a /\ n < c /\ c < p /\
                              ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
                              WHILE g b a = iterate a b n
   iterate_while_hoare_0
                       |- !a b g. ~g a ==> HOARE_SPEC {a} (WHILE g b) {a}
   iterate_while_thm_0 |- !a b g. ~g a ==> WHILE g b a = a

   Direct from WHILE definition:
   iterate_while_eqn   |- !g b x k. (!j. j < k ==> g (FUNPOW b j x)) ==>
                                    WHILE g b x =
                                      if g (FUNPOW b k x) then WHILE g b (FUNPOW b (k + 1) x)
                                      else FUNPOW b k x
   iterate_while_thm   |- !g b x k. (!j. j < k ==> g (FUNPOW b j x)) /\ ~g (FUNPOW b k x) ==>
                                    WHILE g b x = FUNPOW b k x
   iterate_while_none  |- !g b x. ~g x ==> WHILE g b x = x
   skip_idx_while_thm  |- !ls f h k. h <= k /\ (!j. h <= j /\ j < k ==> f (EL j ls)) /\ ~f (EL k ls) ==>
                                     WHILE (\j. f (EL j ls)) SUC h = k
   skip_list_while_thm |- !ls g b h k. h <= k /\ (!j. h <= j /\ j < k ==> g (EL j ls)) /\ ~g (EL k ls) /\
                                       (!j. h + j <= k ==> EL (h + j) ls = FUNPOW b j (EL h ls)) ==>
                                       EL k ls = WHILE g b (EL h ls)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Iterative Search, by recursion with cutoff.                               *)
(* ------------------------------------------------------------------------- *)

(* Idea: recursion with cutoff c, starting count j. *)

(* The starting point is x:'a, iterating over function f:'a -> 'a,
   that is, f x <- x, until guard g:'a -> bool checks (g x) is true. *)
val iterate_search_def = tDefine "iterate_search" `
  iterate_search f g x c b j =
  if (c <= j) then b else if (g x) then x
  else iterate_search f g (f x) c b (j + 1)
`(WF_REL_TAC `measure (\(f,g,x,c,b,j). c - j)`);
(* Note: the bad b can be just x, as it is relevant only for the cutoff. *)

(* Idea: iteration goes on only for j < c; if not, game over. *)

(* Theorem: c <= j ==> iterate_search f g x c b j = b *)
(* Proof: by iterate_search_def *)
Theorem iterate_search_over:
  !f g x c b j. c <= j ==> iterate_search f g x c b j = b
Proof
  simp[Once iterate_search_def]
QED

(* Idea: iteration goes on for j < c, but exits when (g x). *)

(* Theorem: j < c /\ g x ==> iterate_search f g x c b j = x *)
(* Proof: by iterate_search_def *)
Theorem iterate_search_exit:
  !f g x c b j. j < c /\ g x ==> iterate_search f g x c b j = x
Proof
  simp[Once iterate_search_def]
QED

(* Idea: iteration goes on for one step when j < c and ~(g x). *)

(* Theorem: j < c /\ ~g x ==>
            iterate_search f g x c b j = iterate_search f g (f x) c b (j + 1) *)
(* Proof: by iterate_search_def *)
Theorem iterate_search_next:
  !f g x c b j. j < c /\ ~g x ==>
                iterate_search f g x c b j = iterate_search f g (f x) c b (j + 1)
Proof
  simp[Once iterate_search_def]
QED


(* Idea: iteration goes on for k more steps.
         Extend iterate_search_next by induction, with 0 < k. *)

(* Theorem: 0 < k /\ j + k <= c /\ (!i. i < k ==> ~g (FUNPOW f i x)) ==>
     iterate_search f g x c b j = iterate_search f g (FUNPOW f k x) c b (j + k) *)
(* Proof:
   By induction on k, starting from k = 1.
   Base: j + 1 <= c /\ (!i. i < 1 ==> ~g (FUNPOW f i x)) ==>
         (iterate_search f g x c b j = iterate_search f g (FUNPOW f 1 x) c b (j + 1))
     This simplifies, by FUNPOW_0, FUNPOW_1, to:
     j < c /\ ~g x ==> iterate_search f g x c b j = iterate_search f g (f x) c b (j + 1)
     which is true by iterate_search_next.
   Step: !k. 0 < k /\ j + (k + 1) <= c /\
          (!i. i < k ==> ~g (FUNPOW f i (f x))) ==>
          (iterate_search f g (f x) c b (j + 1) =
           iterate_search f g (FUNPOW f k (f x)) c b (j + (k + 1))) ==>
          0 < k /\ j + k <= c /\ (!i. i < k ==> ~g (FUNPOW f i x)) ==>
          iterate_search f g x c b j = iterate_search f g (FUNPOW f k x) c b (j + k)
     The case k = 1  has been covered.
     For k <> 1, 1 < k, so k = k - 1 + 1                by arithmetic
     Putting !k for the specific (k-1),
     Thus 0 < k - 1, j + (k-1 +1) <= c, and note
             !i. i < k ==> ~g (FUNPOW f i x)            by given
         <=> !i. i - 1 < k - 1 ==> ~g (FUNPOW f (i - 1 + 1) x)
         <=> !j. j < k - 1 ==> ~g (FUNPOW f (j + 1) x)
         <=> !j. j < k - 1 ==> ~g (FUNPOW f j (f x))    by FUNPOW
     Thus the induction assumption conditions are all satisfied,
          iterate_search f g x c b j
        = iterate_search f g (FUNPOW f (k - 1) (f x)) c b (j + k)
                                                        by induction hypothesis
        = iterate_search f g (FUNPOW f k x) c b (j + k) by FUNPOW, ADD1
 *)
Theorem iterate_search_run:
  !f g x c b j k. 0 < k /\ j + k <= c /\
                  (!i. i < k ==> ~g (FUNPOW f i x)) ==>
                  iterate_search f g x c b j =
                  iterate_search f g (FUNPOW f k x) c b (j + k)
Proof
  ho_match_mp_tac (theorem "iterate_search_ind") >>
  rw[] >>
  `~(c <= j)` by decide_tac >>
  `~g x` by metis_tac[FUNPOW_0] >>
  fs[] >>
  `iterate_search f g x c b j = iterate_search f g (f x) c b (j + 1)` by fs[iterate_search_next] >>
  (Cases_on `k = 1` >> simp[]) >>
  `0 < k - 1` by decide_tac >>
  last_x_assum (qspecl_then [`k-1`] strip_assume_tac) >>
  rfs[] >>
  `!i. i < k - 1 ==> ~g (FUNPOW f i (f x))` by
  (rpt strip_tac >>
  `~g (FUNPOW f (i + 1) x)` by fs[] >>
  metis_tac[FUNPOW, ADD1]) >>
  `k - 1 + 1 = k` by decide_tac >>
  metis_tac[FUNPOW, ADD1]
QED

(* Idea: iteration when k more steps becomes n, when now g (FUNPOW f n x). *)

(* Theorem: 0 < n /\ j + n < c /\
            (!i. i < n ==> ~g (FUNPOW f i x)) /\ g (FUNPOW f n x) ==>
            iterate_search f g x c b j = FUNPOW f n x *)
(* Proof:
     iterate_search f g x c b j
   = iterate_search f g (FUNPOW f n x) c b (j + n)   by iterate_search_run, j + n <= c
   = FUNPOW f n x                                    by iterate_search_exit, j + n < c
*)
Theorem iterate_search_done:
  !f g x c b j n. 0 < n /\ j + n < c /\
                  (!i. i < n ==> ~g (FUNPOW f i x)) /\ g (FUNPOW f n x) ==>
                  iterate_search f g x c b j = FUNPOW f n x
Proof
  metis_tac[iterate_search_run, iterate_search_exit, LESS_IMP_LESS_OR_EQ]
QED

(* Idea: the same result, but start with j = 0, and remove 0 < n. *)

(* Theorem: n < c /\ (!i. i < n ==> ~g (FUNPOW f i x)) /\
            g (FUNPOW f n x) ==> iterate_search f g x c b 0 = FUNPOW f n x *)
(* Proof:
   If n = 0, true     by iterate_search_exit
   If n <> 0, true    by iterate_search_done
*)
Theorem iterate_search_thm:
  !f g x c b n. n < c /\ (!i. i < n ==> ~g (FUNPOW f i x)) /\
                g (FUNPOW f n x) ==>
                iterate_search f g x c b 0 = FUNPOW f n x
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  fs[iterate_search_exit] >>
  simp[iterate_search_done]
QED

(* ------------------------------------------------------------------------- *)
(* Iterative Loop, using WHILE construct.                                    *)
(* ------------------------------------------------------------------------- *)

(* Define the iterate WHILE loop:
   with a guard g and a body b, both functions of x, of type alpha. *)
(* no need to define!
val iterate_while_def = Define`
    iterate_while (g:'a -> bool) (b:'a -> 'a) = WHILE g b
`;
*)

(* Overload FUNPOW f j x with index j as the last parameter. *)
val _ = temp_overload_on ("iterate", ``\x f j. FUNPOW f j x``);
(* FUNPOW f j x is pretty-printed as: f^{j}(x). *)
(* iterate x f j is pretty-printed as: (x)f^{j}. *)

(* for temporary overloading, otherwise all FUNPOW becomes iterate! *)

(* Define the trace of the iterate WHILE, starting with a, up to a cutoff c. *)
Definition iterate_trace_def:
    iterate_trace (a:'a) (b:'a -> 'a) (c:num) = MAP (iterate a b) [0 .. c]
End

(* Properties of iteration trace *)

(* Theorem: LENGTH (iterate_trace a b c) = 1 + c *)
(* Proof:
     LENGTH (iterate_trace a b c)
   = LENGTH (MAP (iterate a b) [0 .. c])   by iterate_trace_def
   = LENGTH [0 .. c]                       by LENGTH_MAP
   = 1 + c                                 by listRangeINC_LEN
*)
Theorem iterate_trace_length:
  !a b c. LENGTH (iterate_trace a b c) = 1 + c
Proof
  simp[iterate_trace_def, listRangeINC_LEN]
QED

(* Theorem: iterate_trace a b c <> [] *)
(* Proof:
   Let ls = iterate a b c.
   Note LENGTH ls = 1 + c        by iterate_trace_length
                  <> 0           by arithmetic
     so ls <> []                 by LENGTH_NIL
*)
Theorem iterate_trace_non_nil:
  !a b c. iterate_trace a b c <> []
Proof
  metis_tac[iterate_trace_length, LENGTH_NIL, DECIDE``1 + n <> 0``]
QED

(* Theorem: iterate_trace a b 0 = [a] *)
(* Proof:
     iterate_trace a b 0
   = MAP (iterate a b) [0 .. 0]  by iterate_trace_def
   = MAP (iterate a b) [0]       by listRangeINC_SING
   = [(iterate a b) 0]           by MAP_SING
   = [a]                         by FUNPOW_0
*)
Theorem iterate_trace_sing:
  !a b. iterate_trace a b 0 = [a]
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  `iterate_trace a b 0 = MAP f [0 .. 0]` by rw[iterate_trace_def, Abbr`f`] >>
  `_ = MAP f [0]` by rw[listRangeINC_SING] >>
  `_ = [f 0]` by rw[MAP_SING] >>
  simp[Abbr`f`]
QED

(* Theorem: iterate_trace a b 0 = [a] *)
(* Proof:
     iterate_trace a b 0
   = MAP (\j. FUNPOW b j a) [0 .. 0]           by iterate_trace_def
   = MAP (\j. FUNPOW b j a) [0]                by listRangeINC_SING
   = [FUNPOW b 0 a]                            by MAP_SING
   = [a]                                       by FUNPOW_0
*)
Theorem iterate_trace_0:
  !a b. iterate_trace a b 0 = [a]
Proof
  simp[iterate_trace_def]
QED
(* Note: this is the same as iterate_trace_sing. *)

(* Theorem: iterate_trace a b (SUC c) = SNOC (iterate a b (SUC c)) (iterate_trace a b c) *)
(* Proof:
   Let f = \j. FUNPOW b j a.
     iterate_trace a b (SUC c)
   = MAP f [0 .. (SUC c)]                      by iterate_trace_def
   = MAP f (SNOC (SUC c) [0 .. c])             by listRangeINC_SNOC, ADD1
   = SNOC (f (SUC c)) (MAP f [0 .. c])         by MAP_SNOC
   = SNOC (f (SUC c)) (iterate_trace a b c)    by iterate_trace_def
   = SNOC (FUNPOW b (SUC c) a) (iterate_trace a b c)
   = SNOC (iterate a b (SUC c)) (iterate_trace a b c)
                                               by notation
*)
Theorem iterate_trace_suc:
  !a b c. iterate_trace a b (SUC c) = SNOC (iterate a b (SUC c)) (iterate_trace a b c)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \j. FUNPOW b j a` >>
  `iterate_trace a b (SUC c) = MAP f [0 .. (SUC c)]` by simp[iterate_trace_def, Abbr`f`] >>
  `_ = MAP f (SNOC (SUC c) [0 .. c])` by fs[listRangeINC_SNOC, ADD1] >>
  `_ = SNOC (f (SUC c)) (MAP f [0 .. c])` by fs[MAP_SNOC] >>
  fs[iterate_trace_def, Abbr`f`]
QED

(* Theorem: HD (iterate_trace a b c) = a *)
(* Proof:
     HD (iterate_trace a b c)
   = HD (MAP (iterate a b) [0 .. c])          by iterate_trace_def
   = HD (MAP (iterate a b) (0::[1 .. c]))     by listRangeINC_CONS
   = HD ((iterate a b) 0 :: MAP (iterate a b) [1 .. c])
                                              by MAP
   = (iterate a b) 0                          by HD
   = a                                        by FUNPOW_0
*)
Theorem iterate_trace_head:
  !a b c. HD (iterate_trace a b c) = a
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  `HD (iterate_trace a b c) = HD (MAP f [0 .. c])` by rw[iterate_trace_def, Abbr`f`] >>
  `_ = HD (MAP f (0::[1 .. c]))` by rw[listRangeINC_CONS] >>
  `_ = HD (f 0 :: MAP f [1 .. c])` by rw[] >>
  simp[Abbr`f`]
QED

(* Theorem: LAST (iterate_trace a b c) = iterate a b c *)
(* Proof:
   If c = 0,
     LAST (iterate_trace a b 0)
   = LAST [a]                        by iterate_trace_sing
   = a                               by LAST_CONS
   = iterate a b 0                   by FUNPOW_0

   If c <> 0,
     LAST (iterate_trace a b c)
   = LAST (MAP (iterate a b) [0 .. c])               by iterate_trace_def
   = LAST (MAP (iterate a b) (SNOC c [0 .. (c-1)]))  by listRangeINC_SNOC
   = LAST (SNOC ((iterate a b) c) (MAP (iterate a b) [0 .. (c-1)]))
                                                     by MAP_SNOC
   = (iterate a b) c                                 by LAST_SNOC
   = iterate a b c                                   by function application
*)
Theorem iterate_trace_last:
  !a b c. LAST (iterate_trace a b c) = iterate a b c
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  Cases_on `c = 0` >-
  rw[iterate_trace_sing, Abbr`f`] >>
  `(c = c - 1 + 1) /\ (0 <= c)` by decide_tac >>
  `LAST (iterate_trace a b c) = LAST (MAP f [0 .. c])` by rw[iterate_trace_def, Abbr`f`] >>
  `_ = LAST (MAP f (SNOC c [0 .. (c-1)]))` by metis_tac[listRangeINC_SNOC] >>
  `_ = LAST (SNOC (f c) (MAP f [0 .. (c-1)]))` by rw[MAP_SNOC] >>
  `_ = f c` by rw[LAST_SNOC] >>
  simp[Abbr`f`]
QED

(* Theorem: j <= c ==> EL j (iterate_trace a b c) = iterate a b j *)
(* Proof:
   Note j <= c means j < c + 1.
     EL j (iterate_trace a b c)
   = EL j (MAP (iterate a b) [0 .. c])   by iterate_trace_def
   = (iterate a b) (EL j [0 .. c])       by EL_MAP, listRangeINC_LEN
   = (iterate a b) (0 + j)               by listRangeINC_EL
   = iterate a b j
*)
Theorem iterate_trace_element:
  !a b c j. j <= c ==> EL j (iterate_trace a b c) = iterate a b j
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  `EL j (iterate_trace a b c) = EL j (MAP f [0 .. c])` by rw[iterate_trace_def, Abbr`f`] >>
  `_ = f (EL j [0 .. c])` by rw[EL_MAP, listRangeINC_LEN] >>
  `_ = f j` by rw[listRangeINC_EL] >>
  simp[Abbr`f`]
QED

(* Theorem: ls = iterate_trace a b c /\ ALL_DISTINCT ls /\
            j <= c ==> findi (iterate a b j) ls = j *)
(* Proof:
   Note LENGTH ls = 1 + c          by iterate_trace_length
        findi (iterate a b j) ls
      = findi (EL j ls)            by iterate_trace_element
      = j                          by findi_EL, ALL_DISTINCT ls
*)
Theorem iterate_trace_element_idx:
  !a b c ls j. ls = iterate_trace a b c /\ ALL_DISTINCT ls /\
               j <= c ==> findi (iterate a b j) ls = j
Proof
  rpt strip_tac >>
  `LENGTH ls = 1 + c` by rw[iterate_trace_length] >>
  `iterate a b j = EL j ls` by rw[iterate_trace_element] >>
  rw[indexedListsTheory.findi_EL]
QED

(* Theorem: ls = iterate_trace a b c /\ x <> iterate a b c /\
            MEM x ls ==> MEM (b x) ls *)
(* Proof:
       MEM x ls
   <=> ?j. j < LENGTH ls /\ (x = EL j ls)    by MEM_EL
   <=> ?j. j < 1 + c /\ (x = EL j ls)        by iterate_trace_length
   <=> ?j. j < 1 + c /\ (x = iterate a b j)  by iterate_trace_element
   ==> j <> c since x <> LAST ls,            by iterate_trace_last
   ==> j < c, so j + 1 < 1 + c               by arithmetic
   ==> b x = iterate a b (j + 1)             by FUNPOW_SUC
   ==> b x = EL (j + 1) ls                   by iterate_trace_element
   ==> MEM (b x) ls                          by MEM_EL
*)
Theorem iterate_trace_member:
  !a b c ls x. ls = iterate_trace a b c /\ x <> iterate a b c /\
               MEM x ls ==> MEM (b x) ls
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  rfs[MEM_EL, iterate_trace_length, iterate_trace_element] >>
  `PRE (1 + c) = c` by decide_tac >>
  `ls <> []` by fs[iterate_trace_non_nil] >>
  `iterate a b c = LAST ls` by fs[iterate_trace_last] >>
  `_ = EL c ls` by metis_tac[LAST_EL, iterate_trace_length] >>
  `n <> c` by metis_tac[] >>
  `n + 1 < c + 1` by decide_tac >>
  qexists_tac `n + 1` >>
  simp[] >>
  `b (f n) = b (iterate a b n)` by fs[Abbr`f`] >>
  `_ = iterate a b (SUC n)` by fs[GSYM FUNPOW_SUC] >>
  `_ = EL (SUC n) ls` by rw[iterate_trace_element] >>
  simp[ADD1]
QED

(* Theorem: ls = iterate_trace a b c ==>
            (MEM x ls <=> ?j. j <= c /\ (x = iterate a b j)) *)
(* Proof:
       MEM x ls
   <=> ?j. j < LENGTH ls /\ (x = EL j ls)    by MEM_EL
   <=> ?j. j < 1 + c /\ (x = EL j ls)        by iterate_trace_length
   <=> ?j. j < 1 + c /\ (x = iterate a b j)  by iterate_trace_element
*)
Theorem iterate_trace_member_iff:
  !a b c ls x. ls = iterate_trace a b c ==>
               (MEM x ls <=> ?j. j <= c /\ (x = iterate a b j))
Proof
  rw[MEM_EL, iterate_trace_length] >>
  `!n c. n < c + 1 <=> n <= c` by decide_tac >>
  metis_tac[iterate_trace_element]
QED

(* Theorem: ls = iterate_trace a b c /\ x <> iterate a b c /\
            MEM x ls /\ ALL_DISTINCT ls ==> (findi (b x) ls = 1 + findi x ls) *)
(* Proof:
       MEM x ls
   <=> ?j. j < LENGTH ls /\ (x = EL j ls)    by MEM_EL
   <=> ?j. j < 1 + c /\ (x = EL j ls)        by iterate_trace_length
   Thus findi x ls = j                       by findi_EL
   Also j <> c since x <> LAST ls            by iterate_trace_last
    ==> j < c, so j + 1 < 1 + c              by arithmetic
        b x
      = iterate a b (j + 1)                  by FUNPOW_SUC
      = EL (j + 1) ls                        by iterate_trace_element
   Thus findi (b x) ls = 1 + j               by findi_EL, iterate_trace_length
                       = 1 + findi x ls      by above
indexedListsTheory.findi_EL
|- !l n. n < LENGTH l /\ ALL_DISTINCT l ==> (findi (EL n l) l = n)
*)
Theorem iterate_trace_index:
  !a b c ls x. ls = iterate_trace a b c /\ x <> iterate a b c /\
               MEM x ls /\ ALL_DISTINCT ls ==> (findi (b x) ls = 1 + findi x ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = iterate a b` >>
  rfs[MEM_EL, iterate_trace_length, iterate_trace_element] >>
  `f n = x` by fs[iterate_trace_element, Abbr`f`] >>
  `PRE (1 + c) = c` by decide_tac >>
  `ls <> []` by fs[iterate_trace_non_nil] >>
  `iterate a b c = LAST ls` by fs[iterate_trace_last] >>
  `_ = EL c ls` by metis_tac[LAST_EL, iterate_trace_length] >>
  `n <> c` by metis_tac[] >>
  `n + 1 < c + 1` by decide_tac >>
  `b (f n) = b (iterate a b n)` by fs[Abbr`f`] >>
  `_ = iterate a b (SUC n)` by fs[GSYM FUNPOW_SUC] >>
  `_ = EL (n + 1) ls` by rw[iterate_trace_element, ADD1] >>
  fs[iterate_trace_length, indexedListsTheory.findi_EL]
QED

(* Theorem: FINITE s /\ b PERMUTES s /\ a IN s /\
            p = iterate_period b a /\ c < p ==>
            ALL_DISTINCT (iterate_trace a b c) *)
(* Proof:
   Let ls = iterate_trace a b c.
   By EL_ALL_DISTINCT_EL_EQ, this is to show:
      n1 < LENGTH ls /\ n2 < LENGTH ls ==> (EL n1 ls = EL n2 ls) <=> (n1 = n2)
   The only-if part is trivial, so just do the if-part.

   Note LENGTH ls = 1 + c            by iterate_trace_length
    and c < p implies 1 + c <= p     by arithmetic
    ==> n1 < p and n2 < p            by n1, n2 < LENGTH ls
    Now EL n1 ls = iterate a b n1    by iterate_trace_element
    and EL n2 ls = iterate a b n2    by iterate_trace_element
    ==> n1 MOD p = n2 MOD p          by iterate_period_mod_eq
     or       n1 = n2                by LESS_MOD
*)
Theorem iterate_trace_all_distinct:
  !s a b c p. FINITE s /\ b PERMUTES s /\ a IN s /\
              p = iterate_period b a /\ c < p ==>
              ALL_DISTINCT (iterate_trace a b c)
Proof
  rewrite_tac[EL_ALL_DISTINCT_EL_EQ] >>
  rpt strip_tac >>
  qabbrev_tac `ls = iterate_trace a b c` >>
  `LENGTH ls = 1 + c` by fs[iterate_trace_length, Abbr`ls`] >>
  `n1 < p /\ n2 < p` by decide_tac >>
  `EL n1 ls = iterate a b n1` by fs[iterate_trace_element, Abbr`ls`] >>
  `EL n2 ls = iterate a b n2` by fs[iterate_trace_element, Abbr`ls`] >>
  metis_tac[iterate_period_mod_eq, LESS_MOD]
QED

(* Theorem: FINITE s /\ b PERMUTES s /\ a IN s /\
            p = iterate_period b a /\ c < p /\ n < c /\
            ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
            HOARE_SPEC {a} (WHILE g b) {iterate a b n} *)
(* Proof:
   Note 0 < p                      by iterate_period_pos
   Let ls = iterate_trace a b c.
   then LENGTH ls = 1 + c          by iterate_trace_length
    and ALL_DISTINCT ls            by iterate_trace_all_distinct

   By WHILE_RULE_PRE_POST,
   with Invariant x = MEM x ls /\ findi x ls <= n,
        Measure x = 1 + c - findi x ls.
        Guard x = g x, Cmd x = b x,
        Precond x = x IN {a}, Postcond x = x IN {iterate a b n}.
   this is to show:
   (1) MEM a ls           for (!x. Precond x ==> Invariant x)
       Note a = HD ls          by iterate_trace_head
        and ls <> []           by iterate_trace_non_nil
         so MEM a ls           by HEAD_MEM
   (2) findi a ls <= n    for (!x. Precond x ==> Invariant x)
       Note a = iterate a b 0  by FUNPOW_0
         so findi a ls = 0     by iterate_trace_element_idx
       and surely, 0 <= n      by arithmetic
   (3) MEM x ls /\ findi x ls <= n /\ g x ==>
       c + 1 < findi (b x) ls + (c + 1 - findi x ls)
       for (!x. Invariant x /\ Guard x ==> Measure (Cmd x) < Measure x)
       Let y = iterate a b c, which is LAST ls   by iterate_trace_last
       Then findi y ls = c     by iterate_trace_element_idx
        ==> x <> y             by c <= n and n < c are incompatible
       Thus findi (b x) ls
          = 1 + findi x ls     by iterate_trace_index, MEM x ls
       the inequality is true  by arithmetic
   (4) MEM x ls /\ findi x ls <= n /\ ~g x ==> x = iterate a b n
       for (!x. Invariant x /\ ~Guard x ==> Postcond x)
       Note ?j. j <= c /\ (x = iterate a b j)   by iterate_trace_member_iff, MEM x ls
         so findi x ls = j                      by iterate_trace_element_idx
       Thus ~(j < n)                            by ~g x, x = iterate a b j
         so j = n                               by j <= n, ~(j < n)
        and x = iterate a b j = iterate a b n.
   (5) HOARE_SPEC (\x. (MEM x ls /\ findi x ls <= n) /\ g x) b
                  (\x. MEM x ls /\ findi x ls <= n)
       for HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant
       By HOARE_SPEC_DEF, this is to show:
       MEM x ls /\ findi x ls <= n /\ g x ==> MEM (b x) ls /\ findi (b x) ls <= n

       Let y = iterate a b c, which is LAST ls   by iterate_trace_last
       Then findi y ls = c     by iterate_trace_element_idx
        ==> x <> y             by c <= n and n < c are incompatible
       Thus MEM (b x) ls       by iterate_trace_member, MEM x ls, x <> y
       Also findi (b x) ls
          = 1 + findi x ls     by iterate_trace_index, MEM x ls
       Note ?j. j <= c /\ (x = iterate a b j)   by iterate_trace_member_iff, MEM x ls
         so findi x ls = j                      by iterate_trace_element_idx
        But j <> n                              by ~g (iterate a b n)
         so j < n                               by j <= n, j <> n
       Thus findi (b x) ls <= n                 by arithmetic
*)
Theorem iterate_while_hoare:
  !s a b c p g n. FINITE s /\ b PERMUTES s /\ a IN s /\
                  p = iterate_period b a /\ n < c /\ c < p /\
                  (* guard g is true before n, but false for n, to exit. *)
                  ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
                  HOARE_SPEC {a} (WHILE g b) {iterate a b n}
Proof
  rpt strip_tac >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  qabbrev_tac `ls = iterate_trace a b c` >>
  `LENGTH ls = 1 + c` by rw[iterate_trace_length, Abbr`ls`] >>
  `ALL_DISTINCT ls` by metis_tac[iterate_trace_all_distinct] >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\x. MEM x ls /\ findi x ls <= n` >>
  qexists_tac `\x. 1 + c - findi x ls` >>
  rw[] >| [
    `a = HD ls` by rw[iterate_trace_head, Abbr`ls`] >>
    metis_tac[HEAD_MEM, iterate_trace_non_nil],
    `a = iterate a b 0` by simp[] >>
    `findi a ls = 0` by metis_tac[iterate_trace_element_idx, DECIDE``0 <= c``] >>
    decide_tac,
    qabbrev_tac `p = iterate_period b a` >>
    qabbrev_tac `y = iterate a b c` >>
    `findi y ls = c` by metis_tac[iterate_trace_element_idx, DECIDE``c <= c``] >>
    `x <> y` by metis_tac[NOT_LESS] >>
    `findi (b x) ls = 1 + findi x ls` by metis_tac[iterate_trace_index] >>
    decide_tac,
    qabbrev_tac `p = iterate_period b a` >>
    `?j. j <= c /\ (x = iterate a b j)` by metis_tac[iterate_trace_member_iff] >>
    `findi x ls = j` by metis_tac[iterate_trace_element_idx] >>
    `~(j < n)` by metis_tac[] >>
    `j = n` by decide_tac >>
    fs[],
    qabbrev_tac `p = iterate_period b a` >>
    qabbrev_tac `y = iterate a b c` >>
    `findi y ls = c` by metis_tac[iterate_trace_element_idx, DECIDE``c <= c``] >>
    simp[whileTheory.HOARE_SPEC_DEF] >>
    rpt strip_tac >| [
      `x <> y` by metis_tac[NOT_LESS] >>
      metis_tac[iterate_trace_member],
      `x <> y` by metis_tac[NOT_LESS] >>
      `findi (b x) ls = 1 + findi x ls` by metis_tac[iterate_trace_index] >>
      `?j. j <= c /\ (x = iterate a b j)` by metis_tac[iterate_trace_member_iff] >>
      `findi x ls = j` by metis_tac[iterate_trace_element_idx] >>
      `j <> n` by metis_tac[] >>
      `j < n` by decide_tac >>
      decide_tac
    ]
  ]
QED

(* Theorem: FINITE s /\ b PERMUTES s /\ a IN s /\
            p = iterate_period b a /\ n < c /\ c < p /\
            ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
            WHILE g b a = iterate a b n *)
(* Proof:
   Note HOARE_SPEC {a} (WHILE g b)
                   {iterate a b n}       by iterate_while_hoare
    Now a IN {a}                         by IN_SING
     so {a} a                            by set as function
    ==> {iterate a b n} ((WHILE g b) a)  by HOARE_SPEC_DEF
     or WHILE g b a IN {iterate a b n}   by set as function
   Thus WHILE g b a = iterate a b n      by IN_SING
> whileTheory.HOARE_SPEC_DEF;
val it = |- !P C Q. HOARE_SPEC P C Q <=> !s. P s ==> Q (C s): thm
Put C = (WHILE g b)
*)
Theorem iterate_while_thm_1:
  !s a b c p g n. FINITE s /\ b PERMUTES s /\ a IN s /\
                  p = iterate_period b a /\ n < c /\ c < p /\
                  ~g (iterate a b n) /\ (!j. j < n ==> g (iterate a b j)) ==>
                  WHILE g b a = iterate a b n
Proof
  rpt strip_tac >>
  `HOARE_SPEC {a} (WHILE g b) {iterate a b n}` by metis_tac[iterate_while_hoare] >>
  fs[whileTheory.HOARE_SPEC_DEF]
QED

(* This is another milestone. Now depreciated, see iterate_while_thm below. *)

(* Theorem: ~g a ==> HOARE_SPEC {a} (WHILE g b) {a} *)
(* Proof:
   By WHILE_RULE_PRE_POST,
   set Invariant as (\x. x = a),
   and Measure as any, e.g. (\x. 1).
   This is to show:
   (1) ~g a /\ g a ==> F, which is trivial.
   (2) ~g a ==> HOARE_SPEC (\x. (x = a) /\ g x) b (\x. x = a)
       This is also trival      by HOARE_SPEC_DEF
*)
Theorem iterate_while_hoare_0:
  !a b g. ~g a ==> HOARE_SPEC {a} (WHILE g b) {a}
Proof
  rpt strip_tac >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\x. x = a` >>
  qexists_tac `\x. 1` >>
  rw[] >>
  rw[whileTheory.HOARE_SPEC_DEF]
QED

(* Theorem: ~g a ==> WHILE g b a = a *)
(* Proof:
   Note HOARE_SPEC {a} (WHILE g b) {a}   by iterate_while_hoare_0
   Thus WHILE g b a = a                  by HOARE_SPEC_DEF
*)
Theorem iterate_while_thm_0:
  !a b g. ~g a ==> WHILE g b a = a
Proof
  rpt strip_tac >>
  `HOARE_SPEC {a} (WHILE g b) {a}` by rw[iterate_while_hoare_0] >>
  fs[whileTheory.HOARE_SPEC_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Direct from WHILE definition.                                             *)
(* ------------------------------------------------------------------------- *)

(* from whileTheory:

WHILE
|- !P g x. WHILE P g x = if P x then WHILE P g (g x) else x
WHILE |> ISPEC ``g:'a -> bool`` |> ISPEC ``b:'a -> 'a``;
val it = |- !x. WHILE g b x = if g x then WHILE g b (b x) else x: thm
WHILE |> ISPEC ``g:'a -> bool`` |> ISPEC ``b:'a -> 'a`` |> ISPEC ``FUNPOW b n x``;
|- WHILE g b (FUNPOW b n x) =
      if g (FUNPOW b n x) then WHILE g b (b (FUNPOW b n x)) else FUNPOW b n x: thm
*)


(* Theorem: (!j. j < k ==> g (FUNPOW b j x)) ==>
            (WHILE g b x =
                if g (FUNPOW b k x) then WHILE g b (FUNPOW b (k + 1) x) else FUNPOW b k x) *)
(* Proof:
   Note FUNPOW b (k + 1) x = b (FUNPOW b k x)                  by FUNPOW_SUC, ADD1
   By induction on k.
   Base: WHILE g b x =
         if g (FUNPOW b 0 x) then WHILE g b (b (FUNPOW b 0 x)) else FUNPOW b 0 x
         which simplifies to show:
         WHILE g b x = if g x then WHILE g b (b x) else x      by FUNPOW_0
         This is true                                          by WHILE
   Step: (!j. j < k ==> g (FUNPOW b j x)) ==>
         (WHILE g b x = if g (FUNPOW b k x) then WHILE g b (b (FUNPOW b k x)) else FUNPOW b k x)
     ==> (!j. j < SUC k ==> g (FUNPOW b j x)) ==>
         (WHILE g b x = if g (FUNPOW b (SUC k) x) then WHILE g b (b (FUNPOW b (SUC k) x)) else FUNPOW b (SUC k) x)
         Note !j. j < SUC k ==> g (FUNPOW b j x) means
              !j. j < k ==> g (FUNPOW b j x) and g (FUNPOW b k x)
           WHILE g b x
         = WHILE g b (b (FUNPOW b k x))           by induction hypothesis
         = WHILE g b (FUNPOW (SUC b) k x)         by FUNPOW_SUC
         = if g (FUNPOW b (SUC k) x) then WHILE g b (b (FUNPOW b (SUC k x)) else FUNPOW b (SUC k) x
                                                  by WHILE
*)
Theorem iterate_while_eqn:
  !g b x k. (!j. j < k ==> g (FUNPOW b j x)) ==>
            WHILE g b x =
               if g (FUNPOW b k x) then WHILE g b (FUNPOW b (k + 1) x)
               else FUNPOW b k x
Proof
  simp[FUNPOW_SUC, GSYM ADD1] >>
  ntac 3 strip_tac >>
  Induct >-
  rw[Once WHILE] >>
  rw[Once WHILE, FUNPOW_SUC]
QED

(* Theorem: (!j. j < k ==> g (FUNPOW b j x)) /\ ~g (FUNPOW b k x) ==>
            WHILE g b x = FUNPOW b k x *)
(* Proof: by iterate_while_eqn. *)
Theorem iterate_while_thm:
  !g b x k. (!j. j < k ==> g (FUNPOW b j x)) /\ ~g (FUNPOW b k x) ==>
            WHILE g b x = FUNPOW b k x
Proof
  metis_tac[iterate_while_eqn]
QED

(* Theorem: ~g x ==> WHILE g b x = x *)
(* Proof: by WHILE. *)
Theorem iterate_while_none:
  !g b x. ~g x ==> WHILE g b x = x
Proof
  rw[Once WHILE]
QED
(* This is the same as iterate_while_thm_0. *)

(*
It is not possible to prove the following, which would be nice;
WHILE g b x = FUNPOW b k x <=> (~g (FUNPOW b k x) /\ !j. j < k ==> g (FUNPOW b j x))

This is because WHILE is not known to terminate.
Those are pre-conditions for WHILE to terminate.
*)

(* Theorem: h <= k /\ (!j. h <= j /\ j < k ==> f (EL j ls)) /\ ~f (EL k ls) ==>
            WHILE (\j. f (EL j ls)) SUC h = k *)
(* Proof:
   Let g = \j. f (EL j ls),
       d = k - h.
   Then k = d + h = FUNPOW SUC d k             by FUNPOW_ADD1
   The goal is: WHILE g SUC h = FUNPOW SUC d h.
   By iterate_while_thm, this is to show:
   (1) !j. j < d ==> g (FUNPOW SUC j h)
       Note j + h <= h /\ j + k < d + h = k    by arithmetic
         so g (FUNPOW SUC j h) = g (j + h)     by FUNPOW_ADD1
                               = true          by assumption
   (2) ~g (FUNPOW SUC d h)
       Note g (FUNPOW SUC d h) = g (d + h)     by FUNPOW_ADD1
                               = g k = false   by given
*)
Theorem skip_idx_while_thm:
  !ls f h k. h <= k /\ (!j. h <= j /\ j < k ==> f (EL j ls)) /\ ~f (EL k ls) ==>
             WHILE (\j. f (EL j ls)) SUC h = k
Proof
  rpt strip_tac >>
  qabbrev_tac `g = \j. f (EL j ls)` >>
  `k = h + (k - h)` by decide_tac >>
  qabbrev_tac `d = k - h` >>
  `k = FUNPOW SUC d h` by simp[FUNPOW_ADD1] >>
  `WHILE g SUC h = FUNPOW SUC d h` suffices_by decide_tac >>
  irule iterate_while_thm >>
  fs[FUNPOW_ADD1]
QED

(* Theorem: h <= k /\ (!j. h <= j /\ j < k ==> g (EL j ls)) /\ ~g (EL k ls) /\
            (!j. h + j <= k ==> EL (h + j) ls = FUNPOW b j (EL h ls)) ==>
            EL k ls = WHILE g b (EL h ls) *)
(* Proof:
   Let t = EL h ls,
       d = k - h.
   Then k = h + d                              by arithmetic
        EL k ls
      = EL (h + d) ls                          by k = h + d
      = FUNPOW b d t                           by d <= d
   Thus ~g (FUNPOW b d t)
    and !j. j < d ==> g (FUNPOW b j t)         by h + j < k
   Thus WHILE g b (EL h ls)
      = FUNPOW b d t                           by iterate_while_thm
      = EL k ls                                by above
*)
Theorem skip_list_while_thm:
  !ls g b h k. h <= k /\ (!j. h <= j /\ j < k ==> g (EL j ls)) /\ ~g (EL k ls) /\
               (!j. h + j <= k ==> EL (h + j) ls = FUNPOW b j (EL h ls)) ==>
               EL k ls = WHILE g b (EL h ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `t = EL h ls` >>
  `k = h + (k - h)` by decide_tac >>
  qabbrev_tac `d = k - h` >>
  `EL k ls = FUNPOW b d t` by metis_tac[LESS_EQ_REFL] >>
  `!j. j < d ==> g (FUNPOW b j t)` by
  (rpt strip_tac >>
  `h <= h + j /\ h + j < k` by decide_tac >>
  metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  fs[iterate_while_thm]
QED



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
