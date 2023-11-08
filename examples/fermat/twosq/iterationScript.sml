(* ------------------------------------------------------------------------- *)
(* The Iteration Period                                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "iteration";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* open helperTwosqTheory; *)
open helperFunctionTheory;
open helperSetTheory;
open helperNumTheory;

(* arithmeticTheory -- load by default *)
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def *)


(* ------------------------------------------------------------------------- *)
(* Iteration Period Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Iteration Period:
   iterate_period_def  |- !f x. iterate_period f x =
                                case OLEAST k. 0 < k /\ FUNPOW f k x = x of
                                  NONE => 0
                                | SOME k => k
   iterate_period_property
                       |- !f x. FUNPOW f (iterate_period f x) x = x
   iterate_period_minimal
                       |- !f x n. 0 < n /\ n < iterate_period f x ==> FUNPOW f n x <> x
   iterate_period_thm  |- !f x n. 0 < n ==>
                          (iterate_period f x = n <=>
                           FUNPOW f n x = x /\ !m. 0 < m /\ m < n ==> FUNPOW f m x <> x)
   iterate_fix_0       |- !f x n. n < iterate_period f x /\ FUNPOW f n x = x ==> n = 0
   iterate_not_distinct|- !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
                            ?h k. FUNPOW f h x = FUNPOW f k x /\ h <> k
   iterate_period_exists
                       |- !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
                              ?n. 0 < n /\ n = iterate_period f x
   iterate_mod_period  |- !f s x n. FINITE s /\ f PERMUTES s /\ x IN s ==>
                                    FUNPOW f n x = FUNPOW f (n MOD iterate_period f x) x
   iterate_reduce      |- !f s x n. FINITE s /\ f PERMUTES s /\ x IN s ==>
                                ?m. FUNPOW f n x = FUNPOW f m x /\ m < iterate_period f x
   iterate_period_eq_0 |- !f x. iterate_period f x = 0 <=> !n. 0 < n ==> FUNPOW f n x <> x
   iterate_period_eq_1 |- !f x. iterate_period f x = 1 <=> f x = x
   iterate_period_eq_2 |- !f x. iterate_period f x = 2 <=> f x <> x /\ f (f x) = x
   iterate_period_multiple
                       |- !f x n. FUNPOW f n x = x <=> ?k. n = k * iterate_period f x
   iterate_period_mod  |- !f x n p. 0 < p /\ p = iterate_period f x ==>
                                    (FUNPOW f n x = x <=> n MOD p = 0)
   iterate_period_mod_eq
                       |- !f s p x i j. FINITE s /\ f PERMUTES s /\ x IN s /\
                                        p = iterate_period f x ==>
                                        (FUNPOW f i x = FUNPOW f j x <=> i MOD p = j MOD p)
   iterate_period_funpow_inj
                       |- !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\
                                    p = iterate_period f x ==>
                                    INJ (\j. FUNPOW f j x) (count p) s
   iterate_period_upper|- !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\
                                    p = iterate_period f x ==> p <= CARD s
   iterate_period_inv  |- !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
                                  iterate_period (LINV f s) x = iterate_period f x
   iterate_period_inv_alt
                       |- !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\
                                    p = iterate_period f x ==>
                                    iterate_period (LINV f s) x = p
   iterate_period_iterate
                       |- !f s x y j. FINITE s /\ f PERMUTES s /\ x IN s /\
                                      y = FUNPOW f j x ==>
                                      iterate_period f y = iterate_period f x
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Iteration Period                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define period = optional LEAST index for FUNPOW f k x to return to x. *)

Definition iterate_period_def[nocompute]:
    iterate_period (f:'a -> 'a) (x:'a) =
      case OLEAST k. 0 < k /\ FUNPOW f k x = x of
           NONE => 0
         | SOME k => k
End
(* use [nocompute] here since this is not computationally effective. *)

(* Theorem: FUNPOW f (iterate_period f x) x = x *)
(* Proof:
   If iterate_period f x k returns SOME k,
        FUNPOW f (iterate_period f x) x
      = FUNPOW f k x              by iterate_period_def
      = x                         by definition condition
   Otherwise iterate_period f x k returns NONE,
        FUNPOW f (iterate_period f x) x
      = FUNPOW f 0 x              by iterate_period_def
      = x                         by FUNPOW_0
*)
Theorem iterate_period_property:
  !f x. FUNPOW f (iterate_period f x) x = x
Proof
  rpt strip_tac >>
  simp[iterate_period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  simp[]
QED

(* Theorem: 0 < n /\ n < iterate_period f x ==> FUNPOW f n x <> x *)
(* Proof: by iterate_period_def, and definition of OLEAST. *)
Theorem iterate_period_minimal:
  !f x n. 0 < n /\ n < iterate_period f x ==> FUNPOW f n x <> x
Proof
  ntac 2 strip_tac >>
  simp[iterate_period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  metis_tac[DECIDE``~(0 < 0)``]
QED

(* Theorem: 0 < n ==> (iterate_period f x = n <=>
            FUNPOW f n x = x /\ !m. 0 < m /\ m < n ==> FUNPOW f m x <> x) *)
(* Proof:
   If part: iterate_period f x = n ==>
            FUNPOW f n x = x /\ !m. 0 < m /\ m < n ==> FUNPOW f m x <> x)
      This is to show:
      (1) FUNPOW f n x = x, true by iterate_period_property
      (2) !m. 0 < m /\ m < n ==> FUNPOW f m x <> x, true by iterate_period_minimal
   Only-if part: FUNPOW f n x = x /\ !m. 0 < m /\ m < n ==> FUNPOW f m x <> x) ==>
                 iterate_period f x = n
      Expanding by iterate_period_def, this is to show:
      (1) 0 < n /\ !n'. ~(0 < n') \/ FUNPOW f n' x <> x ==> 0 = n
          Putting n' = n, the assumption is contradictory.
      (2) 0 < n /\ 0 < n' /\ !m. m < n' ==> ~(0 < m) \/ FUNPOW f m x <> x ==> n' = n
          The assumptions implies ~(n' < n), and ~(n < n'), hence n' = n.
*)
Theorem iterate_period_thm:
  !f x n. 0 < n ==>
          (iterate_period f x = n <=>
           FUNPOW f n x = x /\ !m. 0 < m /\ m < n ==> FUNPOW f m x <> x)
Proof
  rw[EQ_IMP_THM] >-
  simp[iterate_period_property] >-
  simp[iterate_period_minimal] >>
  simp[iterate_period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  `~(n' < n) /\ ~(n < n')` by metis_tac[] >>
  decide_tac
QED

(* Theorem: n < iterate_period f x /\ FUNPOW f n x = x ==> n = 0 *)
(* Proof: by iterate_period_minimal, ~(0 < n), so n = 0. *)
Theorem iterate_fix_0:
  !f x n. n < iterate_period f x /\ FUNPOW f n x = x ==> n = 0
Proof
  metis_tac[iterate_period_minimal, NOT_ZERO]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==>
            ?h k. FUNPOW f h x = FUNPOW f k x /\ (h <> k) *)
(* Proof:
   By contradiction, suppose !h k. FUNPOW f h x = FUNPOW f k x ==> (h = k).
   Since s is FINITE, let c = CARD s.
   Let fun = (\n. FUNPOW f n x), t = count (SUC c).
   Then INJ fun t s since:
   (1) !n. fun n x IN s                        by INJ_DEF, FUNPOW_closure, x IN s
   (2) !h k. fun h x = fun k x ==> h = k       by assumption
   But c < SUC c
   and SUC c = CARD (count (SUC c)) = CARD t   by CARD_COUNT
   This contradicts the Pigeonhole Principle   by PHP
*)
Theorem iterate_not_distinct:
  !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
           ?h k. FUNPOW f h x = FUNPOW f k x /\ (h <> k)
Proof
  spose_not_then strip_assume_tac >>
  qabbrev_tac `c = CARD s` >>
  `INJ (\n. FUNPOW f n x) (count (SUC c)) s` by rw[INJ_DEF, FUNPOW_closure] >>
  `c < SUC c` by decide_tac >>
  metis_tac[CARD_COUNT, PHP]
QED

(* Unfortunately, this is too weak in this case.
Say the actual period is 3, so FUNPOW f 3 x = x.
That means h k can be 1, 4, or 1, 7, or 4, 61.
There is no guarantee that their difference is the period.
This is because the group is (Z, +), which is INFINITE.
Next one is stronger.
*)

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==>
            ?n. 0 < n /\ n = iterate_period f x *)
(* Proof:
   Note FINITE s /\ f PERMUTES s /\ x IN s
    ==> ?h k. FUNPOW f h x = FUNPOW f k x /\
              (h < k)                         by use of iterate_not_distinct
   Let n = (k - h), then 0 < n                by h < k
        FUNPOW f n x
      = FUNPOW f (k - h) x                    by n = k - h, above
      = FUNPOW (LINV f s) h (FUNPOW f k x)    by FUNPOW_SUB_LINV2, h <= k, x IN s
      = FUNPOW (LINV f s) h (FUNPOW f h x)    by FUNPOW f h x = FUNPOW f k x
      = x                                     by FUNPOW_EQ_LINV

   Let t = {n | 0 < n /\ FUNPOW f n x = x}, m = MIN_SET t.
   Thus n IN t, so t <> EMPTY                 by MEMBER_NOT_EMPTY
    and m IN t                                by MIN_SET_IN_SET, t <> EMPTY
    ==> 0 < m /\ (FUNPOW f m x = x)           by m IN t

   Claim: !j. 0 < j /\ j < m ==> (FUNPOW f j x <> x)
   Proof: By contradiction,
          suppose ?j. 0 < j /\ j < m /\ (FUNPOW f j x = x).
          Then j IN t, and m <= j             by MIN_SET_PROPERTY, t <> EMPTY
          This contradicts j < m.

   Thus m = iterate_period f x, and 0 < m.
*)
Theorem iterate_period_exists:
  !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
          ?n. 0 < n /\ n = iterate_period f x
Proof
  rpt strip_tac >>
  `?h k. FUNPOW f h x = FUNPOW f k x /\ (h < k)` by
  (`?h k. FUNPOW f h x = FUNPOW f k x /\ (h <> k)` by metis_tac[iterate_not_distinct] >>
  Cases_on `h < k` >-
  metis_tac[] >>
  `k < h` by decide_tac >>
  metis_tac[]
  ) >>
  `0 < k - h` by decide_tac >>
  qabbrev_tac `n = k - h` >>
  `FUNPOW f n x = FUNPOW f (k - h) x` by rw[Abbr`n`] >>
  `_ = FUNPOW (LINV f s) h (FUNPOW f k x)` by rw[FUNPOW_SUB_LINV2] >>
  `_ = FUNPOW (LINV f s) h (FUNPOW f h x)` by fs[] >>
  `_ = x` by rw[FUNPOW_EQ_LINV] >>
  qabbrev_tac `t = {n | 0 < n /\ FUNPOW f n x = x}` >>
  qabbrev_tac `m = MIN_SET t` >>
  `n IN t` by rw[Abbr`t`] >>
  `m IN t` by metis_tac[MIN_SET_IN_SET, MEMBER_NOT_EMPTY] >>
  `0 < m /\ (FUNPOW f m x = x)` by fs[Abbr`t`] >>
  `!j. 0 < j /\ j < m ==> (FUNPOW f j x <> x)` by
    (spose_not_then strip_assume_tac >>
  `j IN t` by rw[Abbr`t`] >>
  `m <= j` by metis_tac[MIN_SET_PROPERTY, MEMBER_NOT_EMPTY] >>
  decide_tac) >>
  metis_tac[iterate_period_thm]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==> 0 < iterate_period f x *)
(* Proof: by iterate_period_exists *)
Theorem iterate_period_pos:
  !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==> 0 < iterate_period f x
Proof
  metis_tac[iterate_period_exists]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==>
            FUNPOW f n x = FUNPOW f (n MOD iterate_period f x) x *)
(* Proof:
   Let p = iterate_period f x.
   Then 0 < p                      by iterate_period_pos
    and FUNPOW f p x = x           by iterate_period_property
        FUNPOW f n x
      = FUNPOW f (n MOD p) x       by FUNPOW_MOD, FUNPOW f p x = x
*)
Theorem iterate_mod_period:
  !f s x n. FINITE s /\ f PERMUTES s /\ x IN s ==>
            FUNPOW f n x = FUNPOW f (n MOD iterate_period f x) x
Proof
  rpt strip_tac >>
  qabbrev_tac `p = iterate_period f x` >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `FUNPOW f p x = x` by rw[iterate_period_property, Abbr`p`] >>
  simp[FUNPOW_MOD]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==>
            ?m. FUNPOW f n x = FUNPOW f m x /\ m < iterate_period f x *)
(* Proof:
   Let p = iterate_period f x.
   Then 0 < p                          by iterate_period_pos
   Let m = n MOD p, then m < p         by MOD_LESS
    and FUNPOW f n x = FUNPOW f m x    by iterate_mod_period
*)
Theorem iterate_reduce:
  !f s x n. FINITE s /\ f PERMUTES s /\ x IN s ==>
            ?m. FUNPOW f n x = FUNPOW f m x /\ m < iterate_period f x
Proof
  metis_tac[iterate_period_pos, iterate_mod_period, MOD_LESS]
QED

(* Theorem: iterate_period f x = 0 <=> !n. 0 < n ==> FUNPOW f n x <> x *)
(* Proof: by iterate_period_def *)
Theorem iterate_period_eq_0:
  !f x. iterate_period f x = 0 <=> !n. 0 < n ==> FUNPOW f n x <> x
Proof
  rw[iterate_period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  simp[] >>
  metis_tac[NOT_ZERO]
QED

(* Theorem: iterate_period f x = 1 <=> f x = x *)
(* Proof:
   Since 0 < 1,
       iterate_period f x = 1
   <=> (FUNPOW f 1 x = x) /\       by iterate_period_thm
       !m. 0 < m /\ m < 1 ==> FUNPOW f m x <> x)
   <=> f x = x /\ T                by FUNPOW_1
   <=> f x = x                     by simplification
*)
Theorem iterate_period_eq_1:
  !f x. iterate_period f x = 1 <=> f x = x
Proof
  rw[iterate_period_thm]
QED

(* Theorem: iterate_period f x = 2 <=> (f x <> x /\ f (f x) = x) *)
(* Proof:
   Since 0 < 2,
       iterate_period f x = 2
   <=> (FUNPOW f 2 x = x) /\       by iterate_period_thm
       !m. 0 < m /\ m < 2 ==> FUNPOW f m x <> x)
   <=> f (f x) = x /\ f x <> x     by FUNPOW_1, FUNPOW_2
*)
Theorem iterate_period_eq_2:
  !f x. iterate_period f x = 2 <=> (f x <> x /\ f (f x) = x)
Proof
  rw[iterate_period_thm, FUNPOW_2, EQ_IMP_THM] >-
  metis_tac[FUNPOW_1, DECIDE``0 < 1 /\ 1 < 2``] >>
  `m = 1` by decide_tac >>
  simp[]
QED

(* Theorem: FUNPOW f n x = x <=> ?k. n = k * (iterate_period f x) *)
(* Proof:
   Let p = iterate_period f x.
   When p = 0,
      If part: FUNPOW f n x = x ==> ?k. n = k * 0, that is: n = 0.
         By contradiction, suppose n <> 0.
         Then 0 < n, giving FUNPOW f n x <> x     by iterate_period_eq_0
         This contradicts FUNPOW f n x = x.
      Only-if part: n = 0 ==> FUNPOW f n x = x
         That is FUNPOW f 0 x = x, true           by FUNPOW_0
   When p <> 0, then 0 < p.
      Note FUNPOW f p x = x                       by iterate_period_property
      If part: FUNPOW f n x = x ==> ?k. n = k * p
         Let k = n DIV p, r = n MOD p.
         Then (n = k * p + r) /\ (r < p)          by DIVISION, 0 < p
         so n = FUNPOW f n x                      by given
              = FUNPOW f (r + k * p) x            by above
              = FUNPOW f r (FUNPOW f (k * p) x)   by FUNPOW_ADD
              = FUNPOW f r x                      by FUNPOW_MULTIPLE
         Thus r = 0                               by iterate_period_minimal
         so take k = n DIV p.
      Only-if part: n = k * p ==> FUNPOW f n x = x
         This is true                             by FUNPOW_MULTIPLE
*)
Theorem iterate_period_multiple:
  !f x n. FUNPOW f n x = x <=> ?k. n = k * (iterate_period f x)
Proof
  rpt strip_tac >>
  qabbrev_tac `p = iterate_period f x` >>
  Cases_on `p = 0` >| [
    rw[EQ_IMP_THM] >>
    metis_tac[iterate_period_eq_0, NOT_ZERO],
    `0 < p` by decide_tac >>
    `FUNPOW f p x = x` by rw[iterate_period_property, Abbr`p`] >>
    REVERSE (rw[EQ_IMP_THM]) >-
    rw[FUNPOW_MULTIPLE] >>
    qabbrev_tac `k = n DIV p` >>
    qabbrev_tac `r = n MOD p` >>
    `(n = k * p + r) /\ (r < p)` by rw[DIVISION, Abbr`k`, Abbr`r`] >>
    `FUNPOW f n x = FUNPOW f (r + k * p) x` by fs[] >>
    `_ = FUNPOW f r (FUNPOW f (k * p) x)` by rw[FUNPOW_ADD] >>
    `_ = FUNPOW f r x` by rw[FUNPOW_MULTIPLE] >>
    `~(0 < r)` by metis_tac[iterate_period_minimal] >>
    `r = 0` by decide_tac >>
    metis_tac[ADD_0]
  ]
QED

(* Theorem: 0 < p /\ p = iterate_period f x ==>
            (FUNPOW f n x = x <=> n MOD p = 0) *)
(* Proof:
       FUNPOW f n x = x
   <=> ?k. n = k * p               by iterate_period_multiple
   <=> n MOD p = 0                 by MOD_EQ_0_DIVISOR, 0 < p
*)
Theorem iterate_period_mod:
  !f x n p. 0 < p /\ p = iterate_period f x ==>
            (FUNPOW f n x = x <=> n MOD p = 0)
Proof
  simp[iterate_period_multiple, MOD_EQ_0_DIVISOR]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\ p = iterate_period f x ==>
            (FUNPOW f i x = FUNPOW f j x <=> i MOD p = j MOD p) *)
(* Proof:
   Note 0 < p                     by iterate_period_pos
    and FUNPOW f i x IN s         by FUNPOW_closure
    and FUNPOW f j x IN s         by FUNPOW_closure
   If i = j, the equivalence is trivial. Otherwise,

       FUNPOW f i x = FUNPOW f j x
   <=> x = FUNPOW (LINV f s) i (FUNPOW f j x)
    or FUNPOW (LINV f s) j (FUNPOW f i x) = x     by FUNPOW_LINV_INV
   <=> x = FUNPOW f (j - i) x   if i <= j
    or x = FUNPOW f (i - j) x   if j <= i         by FUNPOW_SUB_LINV2
   <=> (j - i) MOD p = 0 or (i - j) MOD p = 0     by iterate_period_mod
   <=> i MOD p = j MOD p                          by MOD_EQ, 0 < p
*)
Theorem iterate_period_mod_eq:
  !f s p x i j. FINITE s /\ f PERMUTES s /\ x IN s /\
                p = iterate_period f x ==>
                (FUNPOW f i x = FUNPOW f j x <=> i MOD p = j MOD p)
Proof
  rpt strip_tac >>
  ‘0 < p’ by metis_tac[iterate_period_pos] >>
  ‘(i = j) \/ (i < j) \/ (j < i)’ by decide_tac >-
  fs[]
  >- (‘i <= j’ by decide_tac >>
      ‘FUNPOW f j x IN s’ by rw[FUNPOW_closure] >>
      ‘FUNPOW f i x = FUNPOW f j x <=> (x = FUNPOW (LINV f s) i (FUNPOW f j x))’
        by metis_tac[FUNPOW_LINV_INV] >>
      ‘_ = (x = FUNPOW f (j - i) x)’ by fs[GSYM FUNPOW_SUB_LINV2] >>
      ‘_ = ((j - i) MOD p = 0)’ by metis_tac[iterate_period_mod] >>
      fs[MOD_EQ]) >>
  ‘j <= i’ by decide_tac >>
  ‘FUNPOW f i x IN s’ by rw[FUNPOW_closure] >>
  ‘FUNPOW f i x = FUNPOW f j x <=> (x = FUNPOW (LINV f s) j (FUNPOW f i x))’ by metis_tac[FUNPOW_LINV_INV] >>
  ‘_ = (x = FUNPOW f (i - j) x)’ by fs[GSYM FUNPOW_SUB_LINV2] >>
  ‘_ = ((i - j) MOD p = 0)’ by metis_tac[iterate_period_mod] >>
  fs[MOD_EQ]
QED

(* Another proof of the same theorem. *)
(* This is 'elementary' in the sense that LINV is not used, but same concept. *)

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\ p = iterate_period f x ==>
            (FUNPOW f i x = FUNPOW f j x <=> i MOD p = j MOD p) *)
(* Proof:
   Let h = i MOD p, k = j MOD p.
   Note 0 < p                           by iterate_period_pos
    and FUNPOW f i x = FUNPOW f h x     by iterate_mod_period
    and FUNPOW f j x = FUNPOW f k x     by iterate_mod_period
    and h < p, k < p                    by MOD_LESS, 0 < p
   Thus the goal is: FUNPOW f h x = FUNPOW f k x <=> h = k.
   The only-if part is trivial, so just do the if part.

   Let d = p - h, the difference        by h < p
   Then p = h + d = d + h               by arithmetic
        x = FUNPOW f p x                by iterate_period_property
          = FUNPOW f d (FUNPOW f h x)   by FUNPOW_ADD
          = FUNPOW f d (FUNPOW f k x)   by given
          = FUNPOW f (d + k) x          by FUNPOW_ADD
   Thus (d + k) MOD p = 0               by iterate_period_mod
     or p divides (d + k)               by DIVIDES_MOD_0, 0 < p
    But d + k < p + p = 2 * p           by arithmetic
    and 0 < d + k                       by arithmetic
   Also p divides p                     by DIVIDES_REFL
    ==> d + k = p                       by MULTIPLE_INTERVAL
     so k = p - d = h                   by arithmetic
*)
Theorem iterate_period_mod_eq[allow_rebind]:
  !f s p x i j. FINITE s /\ f PERMUTES s /\ x IN s /\
                p = iterate_period f x ==>
                (FUNPOW f i x = FUNPOW f j x <=> i MOD p = j MOD p)
Proof
  rpt strip_tac >>
  ‘0 < p’ by metis_tac[iterate_period_pos] >>
  qabbrev_tac ‘h = i MOD p’ >>
  qabbrev_tac ‘k = j MOD p’ >>
  ‘FUNPOW f h x = FUNPOW f k x <=> (h = k)’ suffices_by metis_tac[iterate_mod_period] >>
  simp[EQ_IMP_THM] >>
  strip_tac >>
  ‘h < p /\ k < p’ by rw[Abbr‘h’, Abbr‘k’] >>
  ‘p = p - h + h’ by decide_tac >>
  qabbrev_tac ‘d = p - h’ >>
  ‘x = FUNPOW f p x’ by metis_tac[iterate_period_property] >>
  ‘_ = FUNPOW f (d + k) x’ by rfs[FUNPOW_ADD] >>
  ‘p divides (d + k)’ by metis_tac[iterate_period_multiple, divides_def] >>
  ‘d + k < p + p’ by decide_tac >>
  ‘p - p < d + k’ by decide_tac >>
  ‘p divides p’ by fs[] >>
  ‘d + k = p’ by metis_tac[MULTIPLE_INTERVAL] >>
  decide_tac
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\ p = iterate_period f x ==>
            INJ (\j. FUNPOW f j x) (count p) s *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) j < p ==> FUNPOW f j x IN s, true    by FUNPOW_closure
   (2) j < p /\ j' < p /\ FUNPOW f j x = FUNPOW f j' x ==> j = j'
           FUNPOW f j x = FUNPOW f j' x
       ==>      j MOD p = j' MOD p          by iterate_period_mod_eq
       ==>            j = j'                by LESS_MOD, j < p, j' < p
*)
Theorem iterate_period_funpow_inj:
  !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\
            p = iterate_period f x ==>
            INJ (\j. FUNPOW f j x) (count p) s
Proof
  rw[INJ_DEF] >-
  fs[FUNPOW_closure] >>
  metis_tac[iterate_period_mod_eq, LESS_MOD]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\
            p = iterate_period f x ==> p <= CARD s *)
(* Proof:
   Note INJ (\j. FUNPOW f j x) (count p) s    by iterate_period_funpow_inj
    and FINITE (count p)                      by FINITE_COUNT
    and CARD (count p) = p                    by CARD_COUNT
    ==> p <= CARD s                           by INJ_CARD
*)
Theorem iterate_period_upper:
  !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\
            p = iterate_period f x ==> p <= CARD s
Proof
  metis_tac[iterate_period_funpow_inj, INJ_CARD, FINITE_COUNT, CARD_COUNT]
QED

(* Idea: period is unchanged for a permutation. *)

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s ==>
            iterate_period (LINV f s) x = iterate_period f x *)
(* Proof:
   Note LINV f s PERMUTES s             by LINV_permutes
   Let q = iterate_period (LINV f s) x
   Then 0 < q                           by iterate_period_pos
   By iterate_period_thm, this is to show:
   (1) FUNPOW f q x = x.
       Let y = FUNPOW f q x
       Then y IN s                      by FUNPOW_closure
         so x = FUNPOW (LINV f s) q y   by FUNPOW_LINV_INV
              = y                       by iterate_period_property
   (2) !m. 0 < m /\ m < q ==> FUNPOW f m x <> x
       Let y = FUNPOW f m x.
       Then y IN s                      by FUNPOW_closure
         so x = FUNPOW (LINV f s) m y   by FUNPOW_LINV_INV
        ==> FUNPOW f m x <> x           by iterate_period_minimal
*)
Theorem iterate_period_inv:
  !f s x. FINITE s /\ f PERMUTES s /\ x IN s ==>
          iterate_period (LINV f s) x = iterate_period f x
Proof
  rpt strip_tac >>
  `LINV f s PERMUTES s` by rw[LINV_permutes] >>
  qabbrev_tac `q = iterate_period (LINV f s) x` >>
  `0 < q` by metis_tac[iterate_period_pos] >>
  simp[iterate_period_thm] >>
  rpt strip_tac >| [
    qabbrev_tac `y = FUNPOW f q x` >>
    `y IN s` by rw[FUNPOW_closure, Abbr`y`] >>
    metis_tac[FUNPOW_LINV_INV, iterate_period_property],
    qabbrev_tac `y = FUNPOW f m x` >>
    `y IN s` by rw[FUNPOW_closure, Abbr`y`] >>
    metis_tac[FUNPOW_LINV_INV, iterate_period_minimal]
  ]
QED

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\ p = iterate_period f x ==>
            iterate_period (LINV f s) x = p *)
(* Proof: by iterate_period_inv. *)
Theorem iterate_period_inv_alt:
  !f s p x. FINITE s /\ f PERMUTES s /\ x IN s /\ p = iterate_period f x ==>
            iterate_period (LINV f s) x = p
Proof
  simp[iterate_period_inv]
QED

(* Idea: all elements in the orbit have the same period. *)

(* Theorem: FINITE s /\ f PERMUTES s /\ x IN s /\ y = FUNPOW f j x ==>
            iterate_period f y = iterate_period f x *)
(* Proof:
   Let p = iterate_period f x,
       q = iterate_period f y,
       k = j MOD p.
   Then y = FUNPOW f k x               by iterate_mod_period
   Note y IN s /\ FUNPOW f q x IN s    by FUNPOW_closure
    and 0 < p /\ 0 < q                 by iterate_period_pos, y IN s
    and k < p                          by MOD_LESS, 0 < p

   Step 1: show FUNPOW f p y = y
   Note p = k + p - k = p - k + k      by k < p
        FUNPOW f p y
      = FUNPOW f (k + p - k) y
      = FUNPOW f k (FUNPOW f (p - k) y)   by FUNPOW_ADD
      = FUNPOW f k (FUNPOW f (p - k) (FUNPOW f k x))
      = FUNPOW f k (FUNPOW f p x)         by FUNPOW_ADD
      = FUNPOW f k x                   by iterate_period_property
      = y
   Thus p MOD q = 0                    by iterate_period_mod
     or q divides p                    by DIVIDES_MOD_0, 0 < q

   Step 2: show FUNPOW f q x = x
        FUNPOW f k x
      = y                              by given
      = FUNPOW f q y                   by iterate_period_property
      = FUNPOW f q (FUNPOW f k x)
      = FUNPOW f k (FUNPOW f q x)      by FUNPOW_COMM
   Note (FUNPOW f k) PERMUTES s        by FUNPOW_permutes
    ==> FUNPOW f q x = x               by BIJ_DEF, INJ_DEF
   Thus q MOD p = 0                    by iterate_period_mod
     or p divides q                    by DIVIDES_MOD_0, 0 < q

   Thus p = q                          by DIVIDES_ANTISYM, [1][2]
*)
Theorem iterate_period_iterate:
  !f s x y j. FINITE s /\ f PERMUTES s /\ x IN s /\ y = FUNPOW f j x ==>
              iterate_period f y = iterate_period f x
Proof
  rpt strip_tac >>
  qabbrev_tac `p = iterate_period f x` >>
  qabbrev_tac `q = iterate_period f y` >>
  qabbrev_tac `k = j MOD p` >>
  `y = FUNPOW f k x` by metis_tac[iterate_mod_period] >>
  `y IN s` by rw[FUNPOW_closure] >>
  `0 < p /\ 0 < q` by metis_tac[iterate_period_pos] >>
  `k < p` by rw[Abbr`k`] >>
  `p = p - k + k` by decide_tac >>
  `FUNPOW f p y = FUNPOW f (k + p - k) y` by simp[] >>
  `_ = FUNPOW f k (FUNPOW f (p - k) y)` by rw[GSYM FUNPOW_ADD] >>
  `_ = FUNPOW f k (FUNPOW f p x)` by metis_tac[FUNPOW_ADD] >>
  `_ = y` by fs[iterate_period_property, Abbr`p`] >>
  `p MOD q = 0` by metis_tac[iterate_period_mod] >>
  `q divides p` by fs[DIVIDES_MOD_0] >>
  `FUNPOW f k x = y` by simp[] >>
  `_ = FUNPOW f q y` by rw[iterate_period_property, Abbr`q`] >>
  `_ = FUNPOW f q (FUNPOW f k x)` by rfs[] >>
  `_ = FUNPOW f k (FUNPOW f q x)` by rw[FUNPOW_COMM] >>
  `(FUNPOW f k) PERMUTES s` by rw[FUNPOW_permutes] >>
  `FUNPOW f q x IN s` by rw[FUNPOW_closure] >>
  `FUNPOW f q x = x` by metis_tac[BIJ_DEF, INJ_DEF] >>
  `q MOD p = 0` by metis_tac[iterate_period_mod] >>
  `p divides q` by fs[DIVIDES_MOD_0] >>
  simp[DIVIDES_ANTISYM]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
