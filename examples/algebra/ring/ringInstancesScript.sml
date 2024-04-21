(* ------------------------------------------------------------------------- *)
(* Applying Ring Theory: Ring Instances                                      *)
(* ------------------------------------------------------------------------- *)

(*

Ring Instances
===============
The important ones:

Z_n -- Arithmetic under Modulo n.

*)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open prim_recTheory pred_setTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory whileTheory primeTheory;

open monoidTheory groupTheory ringTheory;
open groupInstancesTheory;
open groupOrderTheory;
open groupMapTheory ringMapTheory;

(* ------------------------------------------------------------------------- *)
(* Ring Instances Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Ring Data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.
*)
(* Overloading:
   ordz n m  = order (ZN n).prod m

*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   The Trivial Ring (#1 = #0):
   trivial_ring_def       |- !z. trivial_ring z =
                                 <|carrier := {z};
                                       sum := <|carrier := {z}; id := z; op := (\x y. z)|>;
                                      prod := <|carrier := {z}; id := z; op := (\x y. z)|>
                                  |>
   trivial_ring           |- !z. FiniteRing (trivial_ring z)
   trivial_char           |- !z. char (trivial_ring z) = 1

   Arithmetic Modulo n:
   ZN_def                 |- !n. ZN n = <|carrier := count n; sum := add_mod n; prod := times_mod n|>
!  ZN_eval                |- !n. ((ZN n).carrier = count n) /\
                                 ((ZN n).sum = add_mod n) /\ ((ZN n).prod = times_mod n)
   ZN_property            |- !n. (!x. x IN (ZN n).carrier <=> x < n) /\ ((ZN n).sum.id = 0) /\
                                 ((ZN n).prod.id = if n = 1 then 0 else 1) /\
                                 (!x y. (ZN n).sum.op x y = (x + y) MOD n) /\
                                 (!x y. (ZN n).rr.op x y = (x * y) MOD n) /\
                                 FINITE (ZN n).carrier /\ (CARD (ZN n).carrier = n)
   ZN_ids                 |- !n. 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n)
   ZN_ids_alt             |- !n. 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1)
   ZN_finite              |- !n. FINITE (ZN n).carrier
   ZN_card                |- !n. CARD (ZN n).carrier = n
   ZN_ring                |- !n. 0 < n ==> Ring (ZN n)
   ZN_char                |- !n. 0 < n ==> (char (ZN n) = n)
   ZN_exp                 |- !n. 0 < n ==> !x k. (ZN n).prod.exp x k = x ** k MOD n
   ZN_num                 |- !n. 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n
   ZN_num_1               |- !n. (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n
   ZN_num_0               |- !n c. 0 < n ==> (ZN n).sum.exp 0 c = 0
   ZN_num_mod             |- !n c. 0 < n ==> (ZN n).sum.exp (ZN n).prod.id c = c MOD n
   ZN_finite_ring         |- !n. 0 < n ==> FiniteRing (ZN n)
   ZN_invertibles_group   |- !n. 0 < n ==> Group (Invertibles (ZN n).prod)
   ZN_invertibles_finite_group   |- !n. 0 < n ==> FiniteGroup (Invertibles (ZN n).prod)

   ZN Inverse:
   ZN_mult_inv_coprime      |- !n. 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n
   ZN_mult_inv_coprime_iff  |- !n. 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1
   ZN_coprime_invertible    |- !m n. 1 < m /\ coprime m n ==> n MOD m IN (Invertibles (ZN m).prod).carrier
   ZN_invertibles           |- !n. 1 < n ==> (Invertibles (ZN n).prod = Estar n)

   ZN Order:
   ZN_1_exp               |- !n k. (ZN 1).prod.exp n k = 0
   ZN_order_mod_1         |- !n. ordz 1 n = 1
   ZN_order_mod           |- !m n. 0 < m ==> (ordz m (n MOD m) = ordz m n)
   ZN_invertibles_order   |- !m n. 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n)
   ZN_order_0             |- !n. 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0)
   ZN_order_1             |- !n. 0 < n ==> (ordz n 1 = 1)
   ZN_order_eq_1          |- !m n. 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m))
   ZN_order_eq_1_alt      |- !m n. 1 < m ==> (ordz m n = 1 <=> n MOD m = 1)
   ZN_order_property      |- !m n. 0 < m ==> (n ** ordz m n MOD m = 1 MOD m)
   ZN_order_property_alt  |- !m n. 1 < m ==> (n ** ordz m n MOD m = 1)
   ZN_order_divisibility  |- !m n. 0 < m ==> m divides n ** ordz m n - 1
   ZN_coprime_euler_element         |- !m n. 1 < m /\ coprime m n ==> n MOD m IN Euler m
   ZN_coprime_order                 |- !m n. 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m)
   ZN_coprime_order_alt             |- !m n. 1 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1)
   ZN_coprime_order_divides_totient |- !m n. 0 < m /\ coprime m n ==> ordz m n divides totient m
   ZN_coprime_order_divides_phi     |- !m n. 0 < m /\ coprime m n ==> ordz m n divides phi m
   ZN_coprime_order_lt              |- !m n. 1 < m /\ coprime m n ==> ordz m n < m
   ZN_coprime_exp_mod               |- !m n. 0 < m /\ coprime m n ==> !k. n ** k MOD m = n ** (k MOD ordz m n) MOD m
   ZN_order_eq_1_by_prime_factors   |- !m n. 0 < m /\ coprime m n /\
                                       (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1)
   ZN_order_nonzero_iff   |- !m n. 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1))
   ZN_order_eq_0_iff      |- !m n. 1 < m ==> (ordz m n = 0 <=> !k. 0 < k ==> n ** k MOD m <> 1)
   ZN_order_nonzero       |- !m n. 0 < m ==> (ordz m n <> 0 <=> coprime m n)
   ZN_order_eq_0          |- !m n. 0 < m ==> ((ordz m n = 0) <=> gcd m n <> 1)
   ZN_not_coprime         |- !m n. 0 < m /\ gcd m n <> 1 ==> !k. 0 < k ==> n ** k MOD m <> 1
   ZN_order_gt_1_property |- !m n. 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p
   ZN_order_divides_exp   |- !m n k. 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> ordz m n divides k)
   ZN_order_divides_phi   |- !m n. 0 < m /\ 0 < ordz m n ==> ordz m n divides phi m
   ZN_order_upper         |- !m n. 0 < m ==> ordz m n <= phi m
   ZN_order_le            |- !m n. 0 < m ==> ordz m n <= m
   ZN_order_lt            |- !k n m. 0 < k /\ k < m ==> ordz k n < m
   ZN_order_minimal       |- !m n k. 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1
   ZN_coprime_order_gt_1  |- !m n. 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m
   ZN_order_with_coprime_1|- !m n. 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m
   ZN_order_with_coprime_2|- !m n k. 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==>
                                     1 < n /\ 1 < k
   ZN_order_eq_0_test     |- !m n. 1 < m ==>
                             ((ordz m n = 0) <=> !j. 0 < j /\ j < m ==> n ** j MOD m <> 1)
   ZN_order_divides_tops_index
                          |- !n j k. 1 < n /\ 0 < j /\ 1 < k ==>
                                     (k divides tops n j <=> ordz k n divides j)
   ZN_order_le_tops_index |- !n j k. 1 < n /\ 0 < j /\ 1 < k /\ k divides tops n j ==>
                                     ordz k n <= j

   ZN Order Candidate:
   ZN_order_test_propery  |- !m n k. 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
                            (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
                             !j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
                                 (ordz m n = k) \/ n ** j MOD m <> 1
   ZN_order_test_1        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k ==> n ** j MOD m <> 1)
   ZN_order_test_2        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              (n ** k MOD m = 1) /\
                              !j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1)
   ZN_order_test_3        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              k divides phi m /\ (n ** k MOD m = 1) /\
                              !j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1)
   ZN_order_test_4        |- !m n k. 1 < m ==> ((ordz m n = k) <=> (n ** k MOD m = 1) /\
                             !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1)

   ZN Homomorphism:
   ZN_to_ZN_element          |- !n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier
   ZN_to_ZN_sum_group_homo   |- !n m. 0 < n /\ m divides n ==>
                                      GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum
   ZN_to_ZN_prod_monoid_homo |- !n m. 0 < n /\ m divides n ==>
                                      MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod
   ZN_to_ZN_ring_homo        |- !n m. 0 < n /\ m divides n ==>
                                      RingHomo (\x. x MOD m) (ZN n) (ZN m)

   Ring from Sets:
   symdiff_set_inter_def  |- symdiff_set_inter =
                             <|carrier := univ(:'a -> bool); sum := symdiff_set; prod := set_inter|>
   symdiff_set_inter_ring |- Ring symdiff_set_inter
   symdiff_set_inter_char |- char symdiff_set_inter = 2
!  symdiff_eval           |- (symdiff_set.carrier = univ(:'a -> bool)) /\
                             (!x y. symdiff_set.op x y = x UNION y DIFF x INTER y) /\
                             (symdiff_set.id = {})

   Order Computation using a WHILE loop:
   compute_ordz_def      |- !m n. compute_ordz m n =
                                       if m = 0 then ordz 0 n
                                  else if m = 1 then 1
                                  else if coprime m n then WHILE (\i. (n ** i) MOD m <> 1) SUC 1
                                  else 0
   WHILE_RULE_PRE_POST   |- (!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
                            (!x. Precond x ==> Invariant x) /\
                            (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
                            HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
                            HOARE_SPEC Precond (WHILE Guard Cmd) Postcond
   compute_ordz_hoare    |- !m n. 1 < m /\ coprime m n ==>
                                  HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                                             (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                                             (\i. i = ordz m n)
   compute_ordz_by_while |- !m n. 1 < m /\ coprime m n ==> !j. 0 < j /\ j <= ordz m n ==>
                                  (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)

   Correctness of computing ordz m n:
   compute_ordz_0      |- !n. compute_ordz 0 n = ordz 0
   compute_ordz_1      |- !n. compute_ordz 1 n = 1
   compute_ordz_eqn    |- !m n. compute_ordz m n = ordz m n
!  ordz_eval           |- !m n. order (times_mod m) n = compute_ordz m n

*)
(* ------------------------------------------------------------------------- *)
(* The Trivial Ring = {|0|}.                                                 *)
(* ------------------------------------------------------------------------- *)

val trivial_ring_def = Define`
  (trivial_ring z) : 'a ring =
   <| carrier := {z};
      sum := <| carrier := {z};
                id := z;
                op := (\x y. z) |>;
      prod := <| carrier := {z};
                id := z;
                op := (\x y. z) |>
    |>
`;

(* Theorem: {|0|} is indeed a ring. *)
(* Proof: by definition, the field tables are:

   +    |0|          *  |0|
   ------------     -----------
   |0|  |0|         |0| |0|
*)
val trivial_ring = store_thm(
  "trivial_ring",
  ``!z. FiniteRing (trivial_ring z)``,
  rw_tac std_ss[FiniteRing_def] >| [
    rw_tac std_ss[trivial_ring_def, Ring_def, AbelianGroup_def, group_def_alt, IN_SING, RES_FORALL_THM, RES_EXISTS_THM] >>
    rw_tac std_ss[AbelianMonoid_def, Monoid_def, IN_SING],
    rw_tac std_ss[trivial_ring_def, FINITE_SING]
  ]);

(* Theorem: char (trivial_ring z) = 1 *)
(* Proof:
   By fiddling with properties of OLEAST.
   This is to show:
   (case OLEAST n. 0 < n /\ (FUNPOW (\y. z) n z = z) of NONE => 0 | SOME n => n) = 1
   If NONE, 0 = 1 is impossible, so SOME must be true, i.e. to show:
   ?n. 0 < n /\ (FUNPOW (\y. z) n z = z), and then that n must be 1.
   First part is simple:
   let n = 1, then FUNPOW (\y. z) 1 z = (\y. z) z = z   by FUNPOW
   Second part is to show:
   0 < n /\ (FUNPOW (\y. z) n z = z) /\ !m. m < n ==> ~(0 < m) \/ FUNPOW (\y. z) m z <> z ==> n = 1
   By contradiction, assume n <> 1,
   then 0 < n /\ n <> 1 ==> 1 < n,
   since 0 < 1, this means FUNPOW (\y. z) 1 z <> z,
   but FUNPOW (\y. z) 1 z = z by FUNPOW, hence a contradiction.
*)
Theorem trivial_char:
  !z. char (trivial_ring z) = 1
Proof
  strip_tac >>
  `FiniteRing (trivial_ring z)` by rw_tac std_ss[trivial_ring] >>
  rw[char_def] >>
  rw_tac std_ss[order_def, period_def, trivial_ring_def, monoid_exp_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `1 < n /\ 0 < 1` by decide_tac >>
  `FUNPOW (\y. z) 1 z <> z` by metis_tac[DECIDE “~(0 < 0)”] >>
  full_simp_tac (srw_ss()) []
QED

(* ------------------------------------------------------------------------- *)
(* Z_n, Arithmetic in Modulo n.                                              *)
(* ------------------------------------------------------------------------- *)

(* Integer Modulo Ring *)
val ZN_def = zDefine`
  ZN n : num ring =
    <| carrier := count n;
           sum := add_mod n;
          prod := times_mod n
     |>
`;
(*
Note: add_mod is defined in groupInstancesTheory.
times_mod is defined in monoidInstancesTheory.
*)
(* Use of zDefine to avoid incorporating into computeLib, by default. *)

(*
- type_of ``ZN n``;
> val it = ``:num ring`` : hol_type
*)

(* Theorem: Evaluation of ZN component fields. *)
(* Proof: by ZN_def *)
val ZN_eval = store_thm(
  "ZN_eval[compute]",
  ``!n. ((ZN n).carrier = count n) /\
       ((ZN n).sum = add_mod n) /\
       ((ZN n).prod = times_mod n)``,
  rw_tac std_ss[ZN_def]);
(* Put into computeLib, and later with ordz_eval for order computation. *)

(* Theorem: property of ZN Ring *)
(* Proof: by ZN_def, add_mod_def, times_mod_def. *)
val ZN_property = store_thm(
  "ZN_property",
  ``!n. (!x. x IN (ZN n).carrier <=> x < n) /\
       ((ZN n).sum.id = 0) /\
       ((ZN n).prod.id = if n = 1 then 0 else 1) /\
       (!x y. (ZN n).sum.op x y = (x + y) MOD n) /\
       (!x y. (ZN n).prod.op x y = (x * y) MOD n) /\
       FINITE (ZN n).carrier /\
       (CARD (ZN n).carrier = n)``,
  rw[ZN_def, add_mod_def, times_mod_def]);

(* Theorem: 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n) *)
(* Proof: by ZN_property *)
val ZN_ids = store_thm(
  "ZN_ids",
  ``!n. 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n)``,
  rw[ZN_property]);

(* Theorem: 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1) *)
(* Proof: by ZN_ids, ONE_MOD *)
val ZN_ids_alt = store_thm(
  "ZN_ids_alt",
  ``!n. 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1)``,
  rw[ZN_ids]);

(* Theorem: (ZN n).carrier is FINITE. *)
(* Proof: by ZN_ring and FINITE_COUNT. *)
val ZN_finite = store_thm(
  "ZN_finite",
  ``!n. FINITE (ZN n).carrier``,
  rw[ZN_def]);

(* Theorem: CARD (ZN n).carrier = n *)
(* Proof: by ZN_property. *)
val ZN_card = store_thm(
  "ZN_card",
  ``!n. CARD (ZN n).carrier = n``,
  rw[ZN_property]);

(* Theorem: For n > 0, (ZN n) is a Ring. *)
(* Proof: by checking definitions.
   For distribution: (x * (y + z) MOD n) MOD n = ((x * y) MOD n + (x * z) MOD n) MOD n
   LHS = (x * (y + z) MOD n) MOD n
       = (x MOD n * ((y + z) MOD n) MOD n        by LESS_MOD
       = (x * (y + z)) MOD n                     by MOD_TIMES2
       = (x * y + x * z) MOD n                   by LEFT_ADD_DISTRIB
       = ((x * y) MOD n + (x + y) MOD n) MOD n   by MOD_PLUS
       = RHS
*)
val ZN_ring = store_thm(
  "ZN_ring",
  ``!n. 0 < n ==> Ring (ZN n)``,
  rpt strip_tac >>
  `!x. x IN count n <=> x < n` by rw[] >>
  rw_tac std_ss[ZN_def, Ring_def] >-
  rw_tac std_ss[add_mod_abelian_group] >-
  rw_tac std_ss[times_mod_abelian_monoid] >-
  rw_tac std_ss[add_mod_def, count_def] >-
  rw_tac std_ss[times_mod_def] >>
  rw_tac std_ss[add_mod_def, times_mod_def] >>
  metis_tac[LEFT_ADD_DISTRIB, MOD_PLUS, MOD_TIMES2, LESS_MOD]);

(* Theorem: !m n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n) *)
(* Proof: by induction on m.
   Base case: !n. 0 < n /\ 0 <= n ==> (FUNPOW (\j. (j + 1) MOD n) 0 0 = 0 MOD n)
   By FUNPOW, !f x. FUNPOW f 0 x = x,
   hence this is true by 0 = 0 MOD n.
   Step case: !n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n) ==>
              !n. 0 < n /\ SUC m <= n ==> (FUNPOW (\j. (j + 1) MOD n) (SUC m) 0 = SUC m MOD n)
   By FUNPOW_SUC, !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
   hence  (FUNPOW (\j. (j + 1) MOD n) (SUC n) 0
         = (\j. (j + 1) MOD n) (FUNPOW (\j. (j + 1) MOD n) n  0)   by FUNPOW_SUC
         = (\j. (j + 1) MOD n) (m MOD n)                           by induction hypothesis
         = ((m MOD n) + 1) MOD n
         = (m + 1) MOD n    since m < n
         = SUC m MOD n      by ADD1
*)
val ZN_lemma1 = prove(
  ``!m n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n)``,
  Induct_on `m`  >-
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][FUNPOW_SUC, ADD1]);

(* Theorem: 0 < n ==> FUNPOW (\j. (j + 1) MOD n) n 0 = 0 *)
(* Proof:
   Put m = n in ZN_lemma1:
   FUNPOW (\j. (j + 1) MOD n) n 0 = n MOD n = 0  by DIVMOD_ID.
*)
val ZN_lemma2 = prove(
  ``!n. 0 < n ==> (FUNPOW (\j. (j + 1) MOD n) n 0 = 0)``,
  rw_tac std_ss[ZN_lemma1]);

(* Theorem: 0 < n ==> char (ZN n) = n *)
(* Proof:
   Depends on the "ZN_lemma":
    0 < m /\ n <= m ==> FUNPOW (\j. (j + 1) MOD m) n 0 = n MOD m
   which is proved by induction on n.
   This is to show:
   (case OLEAST n'. 0 < n' /\ (FUNPOW (\j. (1 + j) MOD n) n' 0 = 0) of NONE => 0 | SOME n => n) = n
   If SOME, n = n is trivial.
   If NONE, need to show impossible for 0 < n: 0 < n' /\ (FUNPOW (\j. (1 + j) MOD n) n' 0 = 0
   Since (FUNPOW (\j. (1 + j) MOD n) n' 0 = n MOD n' = 0  by by ZN_lemma1
   and 0 < n' /\ 0 < n ==> n MOD n' <> 0, a contradiction with n MOD n' = 0.
*)
Theorem ZN_char:
  !n. 0 < n ==> char (ZN n) = n
Proof
  rw_tac std_ss[char_def, order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  simp[Excl "lift_disj_eq", ZN_def, add_mod_def, times_mod_def,
       monoid_exp_def] >>
  rw[Excl "lift_disj_eq"] >| [ (* avoid srw_tac simplication *)
    qexists_tac `1` >> rw[],
    metis_tac[ZN_lemma2, DECIDE “~(0 < 0)”],
    rename [‘0 < m’] >> spose_not_then strip_assume_tac >>
    `1 < m` by decide_tac >>
    `FUNPOW (\j. 0) 1 0 = 0` by rw[] >>
    metis_tac[DECIDE “1 ≠ 0”],

    rename [‘m = n’, ‘n ≠ 1’] >>
    ‘FUNPOW (\j. (j + 1) MOD n) n 0 = 0’ by rw_tac std_ss[ZN_lemma2] >>
    ‘~(n < m)’ by metis_tac[DECIDE “~(0 < 0)”] >>
    ‘~(m < n)’ suffices_by decide_tac >>
    strip_tac >>
    full_simp_tac (srw_ss() ++ ARITH_ss) [ZN_lemma1]
  ]
QED

(* Better proof *)

(* Theorem: 0 < n ==> char (ZN n) = n *)
(* Proof:
   If n = 1, (ZN 1).carrier = count 1 = {0}
   this is to show: n = 1 iff (FUNPOW (\j. 0) n 0 = 0) /\ !m. 0 < m /\ m < n ==> FUNPOW (\j. 0) m 0 <> 0
   which is true, since FUNPOW (\j. 0) m 0 = 0 for all m, so to falsify 0 < m /\ m < n, n must be 1.
   If n <> 1, 1 < n,
   Ring (ZN n)    by ZN_ring
     (ZN n).sum.exp 1 n
   = FUNPOW (\j. (1 + j) MOD n) n 0   by monoid_exp_def
   = n MOD n = 0                      by ZN_lemma2
   Hence (ZN n).sum.exp 1 n = 0
   meaning  char (ZN n) n divides     by ring_char_divides
   Let m = char (ZN n),
   then m <= n                        by DIVIDES_LE
     (ZN n).sum.exp 1 m
   = FUNPOW (\j. (1 + j) MOD n) m 0   by monoid_exp_def
   = m MOD n                          by ZN_lemma1
   = 0                                by char_property
   But m MOD n = 0 means n divides m  by DIVIDES_MOD_0
   Therefore m = n                    by DIVIDES_ANTISYM
*)
Theorem ZN_char[allow_rebind]:
  !n. 0 < n ==> (char (ZN n) = n)
Proof
  rpt strip_tac >>
  ‘Ring (ZN n)’ by rw_tac std_ss [ZN_ring] >>
  ‘(ZN n).sum.id = 0’ by rw[ZN_def, add_mod_def] >>
  ‘(ZN n).sum.exp 1 n = 0’ by rw[ZN_lemma2, ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
  Cases_on ‘n = 1’ >| [
    ‘(ZN n).prod.id = 0’ by rw[ZN_def, times_mod_def] >>
    ‘(char (ZN n)) divides n’ by rw[GSYM ring_char_divides] >>
    metis_tac[DIVIDES_ONE],
    ‘(ZN n).prod.id = 1’ by rw[ZN_def, times_mod_def] >>
    ‘(ZN n).sum.exp 1 n = 0’ by rw[ZN_lemma2, ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
    ‘(char (ZN n)) divides n’ by rw[GSYM ring_char_divides] >>
    ‘(char (ZN n)) <= n’ by rw[DIVIDES_LE] >>
    qabbrev_tac ‘m = char (ZN n)’ >>
    ‘(ZN n).sum.exp 1 m = FUNPOW (\j. (j + 1) MOD n) m 0’ by rw[ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
    ‘_ = m MOD n’ by rw[ZN_lemma1] >>
    ‘n divides m’ by metis_tac[char_property, DIVIDES_MOD_0] >>
    metis_tac [DIVIDES_ANTISYM]
  ]
QED

(* Theorem: 0 < n ==> !x k. (ZN n).prod.exp x k = (x ** k) MOD n *)
(* Proof:
     (ZN n).prod.exp x k
   = (times_mod n).exp x k     by ZN_def
   = (x MOD n) ** k MOD n      by times_mod_exp, 0 < n
   = (x ** k) MOD n            by EXP_MOD, 0 < n
*)
val ZN_exp = store_thm(
  "ZN_exp",
  ``!n. 0 < n ==> !x k. (ZN n).prod.exp x k = (x ** k) MOD n``,
  rw[ZN_def, times_mod_exp]);

(* Theorem: 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n *)
(* Proof:
     (ZN n).sum.exp 1 k
   = (add_mod n).exp 1 k   by ZN_def
   = (1 * k) MOD n         by add_mod_exp, 0 < n
   = k MOD n               by MULT_LEFT_1
*)
val ZN_num = store_thm(
  "ZN_num",
  ``!n. 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n``,
  rw[ZN_def, add_mod_exp]);

(* Theorem: (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n *)
(* Proof:
   If n = 0,
        (ZN 0).sum.exp (ZN 0).prod.id 1
      = (ZN 0).sum.exp 1 1              by ZN_property, n <> 1
      = (ZN 0).sum 0 1                  by monoid_exp_def
      = 1 MOD 0                         by ZN_property
   If n = 1.
        (ZN 1).sum.exp (ZN 1).prod.id 1
      = (ZN 1).sum.exp 0 1              by ZN_property, n = 1
      = (ZN 1).sum 0 0                  by monoid_exp_def
      = 0 MOD 1 = 0                     by ZN_property
                = 1 MOD 1               by DIVMOD_ID, n <> 0
   Otherwise, 1 < n.
        (ZN n).sum.exp (ZN n).prod.id 1
      = (ZN n).sum.exp 1 1              by ZN_property, n <> 1
      = 1 MOD n                         by ZN_num, 0 < n
*)
val ZN_num_1 = store_thm(
  "ZN_num_1",
  ``!n. (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `(ZN 0).sum.exp (ZN 0).prod.id 1 = 1 MOD 0` by EVAL_TAC >>
    rw[],
    rw[ZN_num, ZN_property] >>
    EVAL_TAC
  ]);

(* Theorem: 0 < n ==> ((ZN n).sum.exp 0 c = 0) *)
(* Proof:
   By induction on c.
   Base: (ZN n).sum.exp 0 0 = 0
         (ZN n).sum.exp 0 0
       = (ZN n).sum.id          by monoid_exp_0
       = 0                      by ZN_property
   Step: (ZN n).sum.exp 0 c = 0 ==> (ZN n).sum.exp 0 (SUC c) = 0
         (ZN n).sum.exp 0 (SUC c)
       = (ZN n).sum.op 0 ((ZN n).sum.exp 0 c)
                                by monoid_exp_SUC
       = (ZN n).sum.op 0 0      by induction hypothesis
       = (ZN n).sum.id          by monoid_exp_0
       = 0                      by ZN_property
*)
val ZN_num_0 = store_thm(
  "ZN_num_0",
  ``!n c. 0 < n ==> ((ZN n).sum.exp 0 c = 0)``,
  strip_tac >>
  Induct >-
  rw[ZN_property] >>
  rw[ZN_property, monoid_exp_def]);

(* Theorem: 0 < n ==> ((ZN n).sum.exp (ZN n).prod.id c = c MOD n) *)
(* Proof:
   If n = 1,
        (ZN 1).sum.exp (ZN 1).prod.id c
      = (ZN 1).sum.exp 0 c            by ZN_property, n = 1
      = 0                             by ZN_num_0
      = c MOD 1                       by MOD_1
   If n <> 1,
        (ZN n).sum.exp (ZN n).prod.id c
      = (ZN n).sum.exp 1 c            by ZN_property, n <> 1
      = c MOD n                       by ZN_num, 0 < n.
*)
val ZN_num_mod = store_thm(
  "ZN_num_mod",
  ``!n c. 0 < n ==> ((ZN n).sum.exp (ZN n).prod.id c = c MOD n)``,
  rpt strip_tac >>
  rw[ZN_num, ZN_property] >>
  rw[ZN_num_0]);

(* Theorem: For n > 0, (ZN n) is a FINITE Ring. *)
(* Proof: by ZN_ring and ZN_finite. *)
val ZN_finite_ring = store_thm(
  "ZN_finite_ring",
  ``!n. 0 < n ==> FiniteRing (ZN n)``,
  rw_tac std_ss[ZN_ring, ZN_finite, FiniteRing_def]);

(* Theorem: FiniteGroup (Invertibles (ZN n).prod) *)
(* Proof:
   Note Ring (ZN n)                                by ZN_ring
     so Monoid (ZN n).prod                         by ring_mult_monoid
   Thus Group (Invertibles (ZN n).prod)            by monoid_invertibles_is_group
*)
val ZN_invertibles_group = store_thm(
  "ZN_invertibles_group",
  ``!n. 0 < n ==> Group (Invertibles (ZN n).prod)``,
  rw[ZN_ring, monoid_invertibles_is_group]);

(* Theorem: FiniteGroup (Invertibles (ZN n).prod) *)
(* Proof:
   By FiniteGroup_def, this is to show:
   (1) Group (Invertibles (ZN n).prod), true            by ZN_invertibles_group
   (2) FINITE (Invertibles (ZN n).prod).carrier
       Note Ring (ZN n)                                 by ZN_ring
       Since FINITE (ZN n).carrier                      by ZN_finite
       Hence FINITE (Invertibles (ZN n).prod).carrier   by Invertibles_subset, SUBSET_FINITE
*)
val ZN_invertibles_finite_group = store_thm(
  "ZN_invertibles_finite_group",
  ``!n. 0 < n ==> FiniteGroup (Invertibles (ZN n).prod)``,
  rw[FiniteGroup_def] >-
  rw[ZN_invertibles_group] >>
  metis_tac[ZN_finite, Invertibles_subset, SUBSET_FINITE, ZN_ring, ring_carriers]);

(* ------------------------------------------------------------------------- *)
(* ZN Inverse                                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n *)
(* Proof:
       (x * y) MOD n = 1
   ==> ?k. x * y = k * n + 1             by MOD_EQN
   Let d = gcd x n,
   Since d divides x                     by GCD_IS_GREATEST_COMMON_DIVISOR
      so d divides x * y                 by DIVIDES_MULT
    Also d divides n                     by GCD_IS_GREATEST_COMMON_DIVISOR
      so d divides k * n                 by DIVIDES_MULTIPLE
    Thus d divides gcd (k * n) (x * y)   by GCD_IS_GREATEST_COMMON_DIVISOR
     But gcd (k * n) (x * y)
       = gcd (k * n) (k * n + 1)         by above
       = 1                               by coprime_SUC
      so d divides 1, or d = 1           by DIVIDES_ONE
*)
val ZN_mult_inv_coprime = store_thm(
  "ZN_mult_inv_coprime",
  ``!n. 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n``,
  rpt strip_tac >>
  `?k. x * y = k * n + 1` by metis_tac[MOD_EQN] >>
  qabbrev_tac `d = gcd x n` >>
  `d divides x * y` by rw[DIVIDES_MULT, GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides k * n` by rw[DIVIDES_MULTIPLE, GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides gcd (k * n) (x * y)` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  metis_tac[coprime_SUC, DIVIDES_ONE]);

(* Theorem: 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1 *)
(* Proof:
   If part: coprime x n ==> ?y. (x * y) MOD n = 1
      This is true           by GCD_ONE_PROPERTY
   Only-if part: (x * y) MOD n = 1 ==> coprime x n
      This is true           by ZN_mult_inv_coprime, 0 < n
*)
val ZN_mult_inv_coprime_iff = store_thm(
  "ZN_mult_inv_coprime_iff",
  ``!n. 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[GCD_ONE_PROPERTY, GCD_SYM, MULT_COMM] >>
  metis_tac[ZN_mult_inv_coprime]);

(* Theorem: 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier *)
(* Proof:
   Expanding by Invertibles_def, ZN_def, this is to show:
   (1) n MOD m < m
       Since 1 < m ==> 0 < m, true    by MOD_LESS.
   (2) ?y. y < m /\ ((n MOD m * y) MOD m = 1) /\ ((y * n MOD m) MOD m = 1)
       Since  n MOD m < m             by MOD_LESS
       ?y. 0 < y /\ y < m /\ coprime n y /\
          ((y * (n MOD m)) MOD m = 1) by GCD_MOD_MULT_INV
       The result follows             by MULT_COMM
*)
Theorem ZN_coprime_invertible:
  !m n. 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier
Proof
  rpt strip_tac >>
  `0 < n /\ 0 < n MOD m` by metis_tac[MOD_NONZERO_WHEN_GCD_ONE] >>
  `0 < m` by decide_tac >>
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, ZN_def, times_mod_def,
                GSPECIFICATION, IN_COUNT] >>
  metis_tac[MOD_LESS, coprime_mod, GCD_MOD_MULT_INV, MULT_COMM]
QED

(* Same result with a different proof. *)

(* Theorem: 1 < m ==> coprime m n ==> n IN (Invertibles (ZN m).prod) *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) n MOD m < m
       True by MOD_LESS
   (2) ?y. y < m /\ ((n MOD m * y) MOD m = 1) /\ ((y * n MOD m) MOD m = 1)
       We have  n MOD m) < m          by MOD_LESS
           and  0 < (n MOD m)         by MOD_NONZERO_WHEN_GCD_ONE
          also  coprime m (n MOD m)   by coprime_mod
       Hence ?y. 0 < y /\ y < m /\
           (y * (n MOD m)) MOD m = 1  by GCD_MOD_MULT_INV
       and ((n MOD m) * y) MOD m = 1  by MULT_COMM
*)
Theorem ZN_coprime_invertible[allow_rebind]:
  !m n. 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier
Proof
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, ZN_def, times_mod_def,
                GSPECIFICATION, IN_COUNT]
  >- rw[] >>
  ‘0 < m’ by decide_tac >>
  ‘(n MOD m) < m’ by rw[] >>
  metis_tac[MOD_NONZERO_WHEN_GCD_ONE, GCD_MOD_MULT_INV, coprime_mod, MULT_COMM]
QED

(* Theorem: 1 < n ==> (Invertibles (ZN n).prod = Estar n) *)
(* Proof:
   Note 1 < n ==> 0 < n /\ n <> 1
    and (ZN n).prod.carrier = (ZN n).carrier         by ZN_ring, ring_carriers, 0 < n
   By Invertibles_def, Estar_def, this is to show:
   (1) monoid_invertibles (ZN n).prod = Euler n
       By monoid_invertibles_def, Euler_def, EXTENSION, ZN_property, this is to show:
          x < n /\ (?y. y < n /\ ((x * y) MOD n = 1)) <=> 0 < x /\ x < n /\ coprime n x
       That is:
       (1) (x * y) MOD n = 1 ==> 0 < x
           By contradiction, suppose x = 0.
           Then  0 MOD n = 1                         by MULT
             or        0 = 1                         by ZERO_MOD
           which is a contradiction.
       (2) (x * y) MOD n = 1 ==> coprime n x, true   by ZN_mult_inv_coprime
       (3) coprime n x ==> ?y. y IN (ZN n).prod.carrier /\ ((x * y) MOD n = 1)
           Note ?z. (x * z) MOD n = 1                by ZN_mult_inv_coprime_iff
           Let y = z MOD n.
           Then y < n                                by MOD_LESS
             so y IN (ZN n).prod.carrier             by ZN_property
               (x * y) MOD n
             = (x * (z MOD n)) MOD n                 by y = z MOD n
             = (x * z) MOD n                         by MOD_TIMES2, MOD_MOD
             = 1                                     by above
   (2) (ZN n).prod.op = (\i j. (i * j) MOD n), true  by FUN_EQ_THM, ZN_property
   (3) (ZN n).prod.id = 1, true                      by ZN_property, n <> 1
*)
val ZN_invertibles = store_thm(
  "ZN_invertibles",
  ``!n. 1 < n ==> (Invertibles (ZN n).prod = Estar n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `(ZN n).prod.carrier = (ZN n).carrier` by rw[ZN_ring, ring_carriers] >>
  rw[Invertibles_def, Estar_def] >| [
    rw[monoid_invertibles_def, Euler_def, EXTENSION, ZN_property] >>
    rw[EQ_IMP_THM] >| [
      spose_not_then strip_assume_tac >>
      `(x = 0) /\ (1 <> 0)` by decide_tac >>
      metis_tac[MULT, ZERO_MOD],
      metis_tac[ZN_mult_inv_coprime, coprime_sym],
      `?z. (x * z) MOD n = 1` by rw[GSYM ZN_mult_inv_coprime_iff, coprime_sym] >>
      qexists_tac `z MOD n` >>
      rpt strip_tac >-
      rw[MOD_LESS] >>
      metis_tac[MOD_TIMES2, MOD_MOD]
    ],
    rw[FUN_EQ_THM, ZN_property],
    rw[ZN_property]
  ]);

(* ------------------------------------------------------------------------- *)
(* ZN Order                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Overload for order of m in (ZN n).prod *)
val _ = overload_on("ordz", ``\n m. order (ZN n).prod m``);

(* Order for MOD 1:

I thought ordz m n is only defined for 1 < m,
as (x ** j) MOD 1 = 0 by MOD_1, or (x ** j) MOD 1 <> 1.
However, Ring (ZN 1) by ZN_ring.
In fact (ZN 1) = {0} is trivial ring, or 1 = 0.
Thus (x ** j = 1) MOD 1, and the least j is 1.

*)

(* Theorem: (ZN 1).prod.exp n k = 0 *)
(* Proof:
   By monoid_exp_def, ZN_property, this is to show:
      FUNPOW ((ZN 1).prod.op n) k 0 = 0
   Note (ZN 1).prod.op n = K 0         by ZN_property, FUN_EQ_THM
   Thus the goal is: FUNPOW (K 0) k 0 = 0

   By induction on k.
   Base: FUNPOW (K 0) 0 0 = 0, true    by FUNPOW
   Step: FUNPOW (K 0) k 0 = 0 ==> FUNPOW (K 0) (SUC k) 0 = 0
           FUNPOW (K 0) (SUC k) 0
         = FUNPOW (K 0) k ((K 0) 0)    by FUNPOW
         = FUNPOW (K 0) k 0            by K_THM
         = 0                           by induction hypothesis
*)
val ZN_1_exp = store_thm(
  "ZN_1_exp",
  ``!n k. (ZN 1).prod.exp n k = 0``,
  rw[monoid_exp_def, ZN_property] >>
  `(ZN 1).prod.op n = K 0` by rw[ZN_property, FUN_EQ_THM] >>
  rw[] >>
  Induct_on `k` >>
  rw[FUNPOW]);

(* Theorem: ordz 1 n = 1 *)
(* Proof:
   By order_def, period_def, and ZN_property, this is to show:
      (case OLEAST k. 0 < k /\ ((ZN 1).prod.exp n k = 0) of NONE => 0 | SOME k => k) = 1
   Note (ZN 1).prod.exp n k = 0   by ZN_1_exp
   The goal becomes: (case OLEAST k. 0 < k of NONE => 0 | SOME k => k) = 1
   or 0 < n /\ !m. m < n ==> (m = 0) ==> n = 1      by OLEAST_INTRO
   By contradiction, suppose n <> 1.
   Then 1 < n                                       by n <> 0, n <> 1
   By implication, 1 = 0, which is a contradiction.
*)
val ZN_order_mod_1 = store_thm(
  "ZN_order_mod_1",
  ``!n. ordz 1 n = 1``,
  rw[order_def, period_def, ZN_property] >>
  rw[ZN_1_exp] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  `1 < n /\ 1 <> 0` by decide_tac >>
  metis_tac[]);

(* Theorem: 0 < m ==> ordz m (n MOD m) = ordz m n *)
(* Proof:
   Since (ZN m).prod = times_mod m                                  by ZN_def
     and !k. (times_mod m).exp (n MOD m) k = (times_mod m).exp n k  by times_mod_exp, MOD_MOD
   Expanding by order_def, period_def, this is trivially true.
*)
val ZN_order_mod = store_thm(
  "ZN_order_mod",
  ``!m n. 0 < m ==> (ordz m (n MOD m) = ordz m n)``,
  rw[ZN_def, times_mod_exp, order_def, period_def]);

(* Theorem: 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n) *)
(* Proof:
        order (Invertibles (ZN m).prod) (n MOD m)
      = ordz m (n MOD m)          by Invertibles_order
      = ordz m n                  by ZN_order_mod, 0 < m
*)
val ZN_invertibles_order = store_thm(
  "ZN_invertibles_order",
  ``!m n. 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n)``,
  rw[Invertibles_order, ZN_order_mod]);

(*
> order_thm |> ISPEC ``(ZN n).prod`` |> SPEC ``0`` |> SPEC ``1``;
val it = |- 0 < 1 ==> ((ordz n 0 = 1) <=>
    ((ZN n).prod.exp 0 1 = (ZN n).prod.id) /\
    !m. 0 < m /\ m < 1 ==> (ZN n).prod.exp 0 m <> (ZN n).prod.id): thm
> order_eq_0 |> ISPEC ``(ZN n).prod`` |> SPEC ``0``;
val it = |- (ordz n 0 = 0) <=> !n'. 0 < n' ==> (ZN n).prod.exp 0 n' <> (ZN n).prod.id: thm
> monoid_order_eq_1 |> ISPEC ``(ZN n).prod``;
val it = |- Monoid (ZN n).prod ==> !x. x IN (ZN n).prod.carrier ==> ((ordz n x = 1) <=> (x = (ZN n).prod.id)): thm
*)

(* Theorem: 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0) *)
(* Proof:
   If n = 1,
      to show: 0 < n ==> ordz 1 0 = 1.
      Let g = (ZN 1).prod
      Then Monoid g        by ZN_ring, ring_mult_monoid, 0 < n
       and g.id = 0        by ZN_def, times_mod_def
      Note 0 IN g.carrier  by monoid_id_element
      Thus ordz 1 0 = 1    by monoid_order_eq_1
   If n <> 1,
      to show: 0 < n /\ n <> 1 ==> ordz 1 0 = 0.
      By order_eq_0, this is
      to show: !k. 0 < k ==> (ZN n).prod.exp 0 k <> (ZN n).prod.id
           or: !k. 0 < k ==> (0 ** k) MOD n <> 1      by ZN_property, ZN_exp
           or: 0 <> 1                                 by ZERO_EXP, 0 < k
      which is true.
*)
val ZN_order_0 = store_thm(
  "ZN_order_0",
  ``!n. 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0)``,
  rw[] >| [
    `(ZN 1).prod.id = 0` by rw[ZN_def, times_mod_def] >>
    `Monoid (ZN 1).prod` by rw[ZN_ring, ring_mult_monoid] >>
    metis_tac[monoid_order_eq_1, monoid_id_element],
    rw[order_eq_0, ZN_property, ZN_exp, ZERO_EXP]
  ]);

(* Theorem: 0 < n ==> (ordz n 1 = 1) *)
(* Proof:
   If n = 1,
      to show: ordz 1 1 = 1, true   by ZN_order_mod_1
   If n <> 1,
      Note Ring (ZN n)              by ZN_ring, 0 < n
        so Monoid (ZN n).prod       by ring_mult_monoid
       and (ZN n).prod.id = 1       by ZN_property, n <> 1
       ==> ordz n 1 = 1             by monoid_order_id
*)
val ZN_order_1 = store_thm(
  "ZN_order_1",
  ``!n. 0 < n ==> (ordz n 1 = 1)``,
  rpt strip_tac >>
  Cases_on `n = 1` >-
  rw[ZN_order_mod_1] >>
  `0 < n /\ n <> 1` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `Monoid (ZN n).prod` by rw[ring_mult_monoid] >>
  `(ZN n).prod.id = 1` by rw[ZN_property] >>
  metis_tac[monoid_order_id]);

(* Theorem: 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m)) *)
(* Proof:
   First, Ring (ZN m)                             by ZN_ring, 0 < m
      so  Monoid (ZN m).prod                      by ring_mult_monoid
     and  (ZN m).prod.carrier = (ZN m).carrier    by ring_carriers
    with  (ZN m).prod.id = 1 MOD m                by ZN_property

    Now,  n MOD m IN (ZN m).carrier               by ZN_property
     and  ordz m n = ordz m (n MOD m)             by ZN_order_mod, 1 < m
    Thus  n MOD m = 1 MOD m                       by monoid_order_eq_1
*)
val ZN_order_eq_1 = store_thm(
  "ZN_order_eq_1",
  ``!m n. 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m))``,
  rpt strip_tac >>
  `Ring (ZN m)` by rw[ZN_ring] >>
  `Monoid (ZN m).prod` by rw[] >>
  `ordz m n = ordz m (n MOD m)` by rw[ZN_order_mod] >>
  rw[monoid_order_eq_1, ZN_property]);

(* Theorem: 1 < m ==> ((ordz m n = 1) <=> (n MOD m = 1)) *)
(* Proof: ZN_order_eq_1, ONE_MOD *)
val ZN_order_eq_1_alt = store_thm(
  "ZN_order_eq_1_alt",
  ``!m n. 1 < m ==> ((ordz m n = 1) <=> (n MOD m = 1))``,
  rw[ZN_order_eq_1]);

(* Theorem: 0 < m ==> (n ** ordz m n MOD m = 1 MOD m) *)
(* Proof:
   Let k = ordz m n.
   To show: n ** k MOD m = 1
      n ** k MOD m
    = (ZN m).prod.exp n k        by ZN_exp, 0 < m
    = (ZN m).prod.id             by order_property
    = 1 MOD m                    by ZN_property
*)
val ZN_order_property = store_thm(
  "ZN_order_property",
  ``!m n. 0 < m ==> (n ** ordz m n MOD m = 1 MOD m)``,
  rw[order_property, ZN_property, GSYM ZN_exp]);

(* Theorem: 1 < m ==> (n ** ordz m n MOD m = 1) *)
(* Proof: by ZN_order_property, ONE_MOD *)
val ZN_order_property_alt = store_thm(
  "ZN_order_property_alt",
  ``!m n. 1 < m ==> (n ** ordz m n MOD m = 1)``,
  rw[ZN_order_property]);

(* Theorem: 0 < m ==> m divides (n ** ordz m n - 1) *)
(* Proof:
   If m = 1, true                   by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m            by 0 < m, m <> 1
   Let k = ordz m n, to show:  m divides n ** k - 1.
   Since n ** k MOD m = 1           by ZN_order_property, 0 < m
      or n ** k MOD m = 1 MOD m     by ONE_MOD, 1 < m
      so (n ** k - 1) MOD m = 0     by MOD_EQ_DIFF, 0 < m
   Hence m divides (n ** k - 1)     by DIVIDES_MOD_0, 0 < m
*)
val ZN_order_divisibility = store_thm(
  "ZN_order_divisibility",
  ``!m n. 0 < m ==> m divides (n ** ordz m n - 1)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[] >>
  rw[DIVIDES_MOD_0, MOD_EQ_DIFF, ONE_MOD, ZN_order_property]);

(* Theorem: 1 < m /\ coprime m n ==> (n MOD m) IN Euler m *)
(* Proof:
   By Euler_def, this is to show:
   (1) 0 < n MOD m.
       Note 0 < n                    by GCD_0, m <> 1
       Thus true                     by MOD_NONZERO_WHEN_GCD_ONE
   (2) coprime m (n MOD m), true     by MOD_WITH_GCD_ONE, 0 < m.
*)
val ZN_coprime_euler_element = store_thm(
  "ZN_coprime_euler_element",
  ``!m n. 1 < m /\ coprime m n ==> (n MOD m) IN Euler m``,
  rw[Euler_def] >| [
    `n <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
    rw[MOD_NONZERO_WHEN_GCD_ONE],
    rw[MOD_WITH_GCD_ONE]
  ]);

(* Theorem: 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m) *)
(* Proof:
   If m = 1,
      Then ordz 1 n = 1  > 0              by ZN_order_mod_1
       and n ** ordz m n MOD 1 = 1 MOD 1  by MOD_1
   If m <> 1,
      Then 1 < m                          by m <> 1, m <> 0
       and 1 MOD m = 1                    by ONE_MOD, 1 < m
      also (n MOD m) IN (Invertibles (ZN m).prod).carrier        by ZN_coprime_invertible, 1 < m
      Now, FiniteGroup (Invertibles (ZN m).prod)                 by ZN_invertibles_finite_group, 0 < m
       and order (Invertibles (ZN m).prod) (n MOD m) = ordz m n  by ZN_invertibles_order, 0 < m
       and (ZN m).prod.id = 1                                    by ZN_property, m <> 1
     Hence 0 < ordz m n                            by group_order_property
       and n ** (ordz m n) = (ZN m).prod.id = 1    by Invertibles_property, ZN_exp, EXP_MOD
*)
val ZN_coprime_order = store_thm(
  "ZN_coprime_order",
  ``!m n. 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m)``,
  ntac 3 strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  `FiniteGroup (Invertibles (ZN m).prod)` by rw[ZN_invertibles_finite_group] >>
  `(n MOD m) IN (Invertibles (ZN m).prod).carrier` by rw[ZN_coprime_invertible] >>
  `order (Invertibles (ZN m).prod) (n MOD m) = ordz m n` by rw[ZN_invertibles_order] >>
  `(ZN m).prod.id = 1` by rw[ZN_property] >>
  `1 MOD m = 1` by rw[] >>
  metis_tac[group_order_property, Invertibles_property, ZN_exp, EXP_MOD]);

(* This is slightly better than the next: ZN_coprime_order_alt *)

(* Theorem: 1 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** (ordz m n) = 1) *)
(* Proof: by ZN_coprime_order, ONE_MOD *)
val ZN_coprime_order_alt = store_thm(
  "ZN_coprime_order_alt",
  ``!m n. 1 < m /\ coprime m n ==> 0 < ordz m n /\ ((n ** (ordz m n)) MOD m = 1)``,
  rw[ZN_coprime_order]);

(* Theorem: 0 < m /\ coprime m n ==> (ordz m n) divides (totient m) *)
(* Proof:
   If m = 1,
      Then ordz 1 n = 1                 by ZN_order_mod_1
       and 1 divides (totient 1)        by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m                by 0 < m, m <> 1
   Let x = n MOD m
   Step 1: show x IN (Estar m).carrier, apply Euler_Fermat_thm
   Since coprime m n ==> ~(m divides n) by coprime_not_divides
      so x <> 0                         by DIVIDES_MOD_0
   hence 0 < x /\ x < m                 by MOD_LESS, 0 < m
     and coprime m x                    by coprime_mod, 0 < m
    Thus x IN (Estar m).carrier         by Estar_element
     ==> x ** (totient m) MOD m = 1     by Euler_Fermat_eqn (1)
   Step 2: show x IN (ZN m).prod.carrier, apply monoid_order_condition
    Now, Ring (ZN m)                    by ZN_ring, 0 < m
     ==> Monoid (ZN m).prod             by ring_mult_monoid
     and (ZN m).prod.id = 1             by ZN_property, m <> 1
   hence x IN (ZN m).prod.carrier       by ZN_property, MOD_LESS, 0 < m
    Thus ordz m x = ordz m n            by ZN_order_mod, 1 < m
   and (1) becomes
           (ZN m).prod.exp x (totient m) = (ZN m).prod.id  by ZN_exp
   Therefore   (ordz m n) divides (totient m)              by monoid_order_condition
*)
val ZN_coprime_order_divides_totient = store_thm(
  "ZN_coprime_order_divides_totient",
  ``!m n. 0 < m /\ coprime m n ==> (ordz m n) divides (totient m)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  qabbrev_tac `x = n MOD m` >>
  `x < m` by rw[Abbr`x`] >>
  `~(m divides n)` by rw[coprime_not_divides] >>
  `x <> 0` by rw[GSYM DIVIDES_MOD_0, Abbr`x`] >>
  `0 < x` by decide_tac >>
  `coprime m x` by metis_tac[coprime_mod] >>
  `x IN (Estar m).carrier` by rw[Estar_element] >>
  `x ** (totient m) MOD m = 1` by rw[Euler_Fermat_eqn] >>
  `Ring (ZN m)` by rw[ZN_ring] >>
  `Monoid (ZN m).prod` by rw[ring_mult_monoid] >>
  `m <> 1` by decide_tac >>
  `(ZN m).prod.id = 1` by rw[ZN_property] >>
  `x IN (ZN m).prod.carrier` by rw[ZN_property, MOD_LESS, Abbr`x`] >>
  metis_tac[monoid_order_condition, ZN_exp, ZN_order_mod]);

(* Theorem: 0 < m /\ coprime m n ==> (ordz m n) divides (phi m) *)
(* Proof:
   If m = 1, then ordz 1 n = 1       by ZN_order_mod_1
              and 1 divides (phi 1)  by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m             by 0 < m, m <> 1
                so phi m = totient m           by phi_eq_totient, 1 < m
              thus (ordz m n) divides (phi m)  by ZN_coprime_order_divides_totient
*)
val ZN_coprime_order_divides_phi = store_thm(
  "ZN_coprime_order_divides_phi",
  ``!m n. 0 < m /\ coprime m n ==> (ordz m n) divides (phi m)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  rw[ZN_coprime_order_divides_totient, phi_eq_totient]);

(* Theorem: 1 < m /\ coprime m n ==> ordz m n < m *)
(* Proof:
   Note ordz m n divides phi m   by ZN_coprime_order_divides_phi, 0 < m
    and 0 < phi m                by phi_pos, 0 < m
   Thus ordz m n <= phi m        by DIVIDES_LE, 0 < phi m
                  < m            by phi_lt, 1 < m
*)
val ZN_coprime_order_lt = store_thm(
  "ZN_coprime_order_lt",
  ``!m n. 1 < m /\ coprime m n ==> ordz m n < m``,
  rpt strip_tac >>
  `0 < phi m /\ phi m < m` by rw[phi_pos, phi_lt] >>
  `ordz m n <= phi m` by rw[ZN_coprime_order_divides_phi, DIVIDES_LE] >>
  decide_tac);

(* Theorem: 0 < m /\ coprime m n ==> !k. (n ** k) MOD m = (n ** (k MOD (ordz m n))) MOD m *)
(* Proof:
   If m = 1, true since ordz 1 n = 1    by ZN_order_mod_1
   If m <> 1, then 1 < m                by 0 < m, m <> 1
   Let z = ordz m n.
   Note 1 < m ==> 0 < m          by arithmetic
    and 0 < z                    by ZN_coprime_order_alt, 1 < m, coprime m n
   Let g = Invertibles (ZN m).prod, the Euler group.
   Then FiniteGroup g            by ZN_invertibles_finite_group, 0 < m
    ==> n MOD m IN g.carrier     by ZN_coprime_invertible, 1 < n, coprime m n
   Note z = ordz m n  by ZN_order_mod, 1 < m
          = order g (n MOD m)    by ZN_invertibles_order, 1 < m, coprime m n

    Let x = n MOD m
   Then x IN g.carrier                              by above
    and 0 < order g x                               by above, 0 < z
   Note !x k. g.exp x k = (ZN m).prod.exp x k       by Invertibles_property
    and !x k.(ZN m).prod.exp x k = (x ** k) MOD m   by ZN_exp

       (n ** k) MOD m
     = ((n MOD m) ** k) MOD m          by EXP_MOD, 0 < m
     = ((n MOD m) ** (k MOD z)) MOD m  by group_exp_mod_order, n MOD m IN g.carrier, 0 < z
     = ((n ** (k MOD z)) MOD m)        by EXP_MOD, 0 < m
*)
val ZN_coprime_exp_mod = store_thm(
  "ZN_coprime_exp_mod",
  ``!m n. 0 < m /\ coprime m n ==> !k. (n ** k) MOD m = (n ** (k MOD (ordz m n))) MOD m``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  qabbrev_tac `z = ordz m n` >>
  `0 < m` by decide_tac >>
  `0 < z` by rw[ZN_coprime_order_alt, Abbr`z`] >>
  qabbrev_tac `g = Invertibles (ZN m).prod` >>
  `FiniteGroup g` by rw[ZN_invertibles_finite_group, Abbr`g`] >>
  `n MOD m IN g.carrier` by rw[ZN_coprime_invertible, Abbr`g`] >>
  `z = ordz m n` by rw[ZN_order_mod, Abbr`z`] >>
  `_ = order g (n MOD m)` by rw[ZN_invertibles_order, Abbr`g`] >>
  `Group g` by rw[finite_group_is_group] >>
  `(n ** k) MOD m = ((n MOD m) ** k) MOD m` by metis_tac[EXP_MOD] >>
  `_ = ((n MOD m) ** (k MOD z)) MOD m` by metis_tac[group_exp_mod_order, Invertibles_property, ZN_exp] >>
  `_ = ((n ** (k MOD z)) MOD m)` by metis_tac[EXP_MOD] >>
  rw[]);

(* Theorem: 0 < m /\ coprime m n /\ (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1) *)
(* Proof:
   If m = 1, true since ordz 1 n = 1             by ZN_order_mod_1
   If m <> 1, then 1 < m                         by 0 < m, m <> 1
               and 1 MOD m = 1                   by ONE_MOD
   If n = 1, true                                by ZN_order_1
   If n <> 1,
      Since m <> 1, coprime m n ==> n <> 0       by GCD_0R
      Thus 0 < n and 1 < n                       by n <> 1

      Claim: !p. prime p /\ p divides n ==> (p MOD m = 1)
      Proof: prime p /\ p divides n
         ==> coprime m n ==> coprime m p         by coprime_prime_factor_coprime, GCD_SYM, 1 < m
         and ordz m p = 1                        by implication
         ==> p MOD m = 1                         by ZN_order_eq_1

      Thus n MOD m = 1                           by ALL_PRIME_FACTORS_MOD_EQ_1
       ==> ordz m p = 1                          by ZN_order_eq_1
*)
val ZN_order_eq_1_by_prime_factors = store_thm(
  "ZN_order_eq_1_by_prime_factors",
  ``!m n. 0 < m /\ coprime m n /\ (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  Cases_on `n = 1` >-
  rw[ZN_order_1] >>
  `n <> 0` by metis_tac[GCD_0R] >>
  `0 < n /\ 1 < n /\ 1 < m` by decide_tac >>
  `!p. prime p /\ p divides n ==> (p MOD m = 1)` by
  (rpt strip_tac >>
  `coprime m p` by metis_tac[coprime_prime_factor_coprime, GCD_SYM] >>
  metis_tac[ZN_order_eq_1, ONE_MOD]) >>
  `n MOD m = 1` by rw[ALL_PRIME_FACTORS_MOD_EQ_1] >>
  rw[ZN_order_eq_1]);

(*
> order_eq_0 |> ISPEC ``(ZN m).prod`` |> ISPEC ``n:num``;
val it = |- (ordz m n = 0) <=> !n'. 0 < n' ==> (ZN m).prod.exp n n' <> (ZN m).prod.id: thm
*)

(* Theorem: 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1)) *)
(* Proof:
   By order_eq_0,
      (ordz m n = 0) <=> !k. 0 < k ==> (ZN m).prod.exp n k <> (ZN m).prod.id
   or (ordz m n = 0) <=> !k. 0 < k ==> n ** k MOD m <> 1    by ZN_exp, ZN_ids_alt, 0 < m, 1 < m
   The result follows by taking negation of both sides.
*)
val ZN_order_nonzero_iff = store_thm(
  "ZN_order_nonzero_iff",
  ``!m n. 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1))``,
  rw[order_eq_0, ZN_exp, ZN_ids_alt]);

(* Theorem: 1 < m ==> ((ordz m n = 0) <=> (!k. 0 < k ==> n ** k MOD m <> 1)) *)
(* Proof: by ZN_order_nonzero_iff *)
val ZN_order_eq_0_iff = store_thm(
  "ZN_order_eq_0_iff",
  ``!m n. 1 < m ==> ((ordz m n = 0) <=> (!k. 0 < k ==> n ** k MOD m <> 1))``,
  metis_tac[ZN_order_nonzero_iff]);

(* Theorem: 0 < m ==> ((ordz m n <> 0) <=> coprime m n) *)
(* Proof:
   If m = 1, true since ordz 1 n = 1 <> 0        by ZN_order_mod_1
                    and coprime 1 n              by GCD_1
   If m <> 1, then 1 < m                         by 0 < m, m <> 1
               and 1 MOD m = 1                   by ONE_MOD
   If part: ordz m n <> 0 ==> coprime m n
      Let x = n MOD m.
      Then ordz m n = ordz m x     by ZN_order_mod, 0 < m
      Note Ring (ZN m)             by ZN_ring, 0 < m
        so Monoid (ZN m).prod      by ring_mult_monoid
       and (ZN m).prod.carrier = (ZN m).carrier   by ring_carriers
      Note x < n                   by MOD_LESS, 0 < m
      Thus x IN (ZN m).carrier     by ZN_property
       Now 0 < ordz m x            by 0 < ordz m n = ordz m x
       ==> x IN (Invertibles (ZN m).prod).carrier   by monoid_order_nonzero, Invertibles_carrier
        or x IN (Estar m).carrier                   by ZN_invertibles, 1 < m
     Hence coprime m x             by Estar_element
        or coprime m n             by coprime_mod_iff. 0 < m

   Only-if part: coprime m n ==> ordz m n <> 0
     This is true                  by ZN_coprime_order, 0 < m
*)
val ZN_order_nonzero = store_thm(
  "ZN_order_nonzero",
  ``!m n. 0 < m ==> ((ordz m n <> 0) <=> coprime m n)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `x = n MOD m` >>
    `ordz m n = ordz m x` by rw[ZN_order_mod, Abbr`x`] >>
    `Monoid (ZN m).prod` by rw[ZN_ring, ring_mult_monoid] >>
    `(ZN m).prod.carrier = (ZN m).carrier` by rw[ZN_ring, ring_carriers] >>
    `x IN (ZN m).carrier` by rw[ZN_property, MOD_LESS, Abbr`x`] >>
    `x IN (Invertibles (ZN m).prod).carrier` by rw[monoid_order_nonzero, Invertibles_carrier] >>
    `x IN (Estar m).carrier` by rw[GSYM ZN_invertibles] >>
    `coprime m x` by metis_tac[Estar_element] >>
    rw[Once coprime_mod_iff],
    metis_tac[ZN_coprime_order, NOT_ZERO_LT_ZERO]
  ]);

(* Theorem: 0 < m ==> ((ordz m n = 0) <=> ~(coprime m n)) *)
(* Proof: by ZN_order_nonzero *)
val ZN_order_eq_0 = store_thm(
  "ZN_order_eq_0",
  ``!m n. 0 < m ==> ((ordz m n = 0) <=> ~(coprime m n))``,
  metis_tac[ZN_order_nonzero]);

(* Theorem: 0 < m /\ ~coprime m n ==> !k. 0 < k ==> n ** k MOD m <> 1 *)
(* Proof:
   Note m <> 1                              by GCD_1
    and ~coprime m n ==> ordz m n = 0       by ZN_order_eq_0, 0 < m
    ==> !k. 0 < k ==> (n ** k) MOD m <> 1   by ZN_order_eq_0_iff, 1 < m
*)
val ZN_not_coprime = store_thm(
  "ZN_not_coprime",
  ``!m n. 0 < m /\ ~coprime m n ==> !k. 0 < k ==> n ** k MOD m <> 1``,
  rpt strip_tac >>
  `m <> 1` by metis_tac[GCD_1] >>
  `ordz m n = 0` by rw[ZN_order_eq_0] >>
  `1 < m` by decide_tac >>
  metis_tac[ZN_order_eq_0_iff]);

(* Note: "Since ord k n > 1, there must exist a prime divisor p of n such that ord k p > 1." *)

(* Theorem: 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p *)
(* Proof:
   By contradiction, suppose !p. prime p /\ p divides n /\ ~(1 < ordz m p).
   Note ordz m n <> 0          by 1 < ordz m n
    ==> coprime m n            by ZN_order_eq_0, 0 < m
    ==> ?p. prime p /\ p divides n /\ (ordz m p <> 1)
                               by ZN_order_eq_1_by_prime_factors, ordz m n <> 1
   Thus ordz m p = 0           by ~(1 < x) <=> (x = 0) \/ (x = 1)
    ==> p divides m            by ZN_order_eq_0, PRIME_GCD, coprime_sym
    ==> p divides 1            by GCD_PROPERTY, coprime m n
    ==> p = 1                  by DIVIDES_ONE
    ==> F                      by NOT_PRIME_1
*)
val ZN_order_gt_1_property = store_thm(
  "ZN_order_gt_1_property",
  ``!m n. 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p``,
  spose_not_then strip_assume_tac >>
  `coprime m n` by metis_tac[ZN_order_eq_0, DECIDE``1 < x ==> x <> 0``] >>
  `?p. prime p /\ p divides n /\ (ordz m p <> 1)` by metis_tac[ZN_order_eq_1_by_prime_factors, LESS_NOT_EQ] >>
  `ordz m p = 0` by metis_tac[DECIDE``~(1 < x) <=> (x = 0) \/ (x = 1)``] >>
  `p divides m` by metis_tac[ZN_order_eq_0, PRIME_GCD, coprime_sym] >>
  `p divides 1` by metis_tac[GCD_PROPERTY] >>
  metis_tac[DIVIDES_ONE, NOT_PRIME_1]);

(*
> group_order_divides_exp |> ISPEC ``Invertibles (ZN m).prod``;
val it = |- Group (Invertibles (ZN m).prod) ==>
            !x. x IN (Invertibles (ZN m).prod).carrier ==>
            !n. ((Invertibles (ZN m).prod).exp x n = (Invertibles (ZN m).prod).id) <=>
                 order (Invertibles (ZN m).prod) x divides n: thm
*)

(* Theorem: 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> (ordz m n) divides k) *)
(* Proof:
   Let g = Invertibles (ZN m).prod.
   Note g = Estar m           by ZN_invertibles
   Thus FiniteGroup g         by Estar_finite_group
    and Group g               by finite_group_is_group
    Let x = n MOD m.
   Then x < m                 by MOD_LESS, 0 < m

   If part: n ** k MOD m = 1 ==> (ordz m n) divides k
      Note x ** n MOD m = 1      by given
       ==> ordz m n <> 0         by ZN_order_nonzero_iff, 1 < m
       ==> coprime m n           by ZN_order_eq_0, 1 < m
       ==> coprime m x           by coprime_mod_iff, 0 < m
       Now 0 < x                 by GCD_0, coprime m x, 1 < m
      Thus x IN g.carrier        by Estar_element, 0 < x, x < m, coprime m x
      Note x ** k MOD m = 1      by EXP_MOD, n ** k MOD m = 1
        or (Invertibles (ZN m).prod).exp x n = (Invertibles (ZN m).prod).id  by Estar_exp, Estar_property
       ==> order (Invertibles (ZN m).prod) x divides k          by group_order_divides_exp
        or ordz m n divides k    by ZN_invertibles_order

   Only-if part: (ordz m n) divides k ==> n ** k MOD m = 1
      Note (ordz m n) divides k  by given
       ==> ordz m n <> 0         by ZERO_DIVIDES, 0 < k
       ==> coprime m n           by ZN_order_eq_0, 1 < m
       ==> coprime m x           by coprime_mod_iff, 0 < m
       Now 0 < x                 by GCD_0, coprime m x, 1 < m
      Thus x IN g.carrier        by Estar_element, 0 < x, x < m, coprime m x
      Note ordz m x = ordz m n   by ZN_order_mod, 1 < m
        or order (Invertibles (ZN n).prod) x divides k                 by ZN_invertibles_order, coprime m n
       ==> (Invertibles (ZN n).prod).exp x k = (Invertibles (ZN n).prod).id)  by group_order_divides_exp
        or x ** k MOD m = 1      by Estar_exp, Estar_property
        or n ** k MOD m = 1      by EXP_MOD, 0 < m
*)
val ZN_order_divides_exp = store_thm(
  "ZN_order_divides_exp",
  ``!m n k. 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> (ordz m n) divides k)``,
  rpt strip_tac >>
  `0 < m` by decide_tac >>
  qabbrev_tac `g = Invertibles (ZN m).prod` >>
  `g = Estar m` by rw[ZN_invertibles, Abbr`g`] >>
  `FiniteGroup g` by rw[Estar_finite_group] >>
  `Group g` by rw[finite_group_is_group] >>
  qabbrev_tac `x = n MOD m` >>
  `x < m` by rw[Abbr`x`] >>
  rewrite_tac[EQ_IMP_THM] >>
  rpt strip_tac >| [
    `ordz m n <> 0` by metis_tac[ZN_order_nonzero_iff] >>
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `coprime m x` by rw[GSYM coprime_mod_iff, Abbr`x`] >>
    `0 < x` by metis_tac[GCD_0, NOT_ZERO_LT_ZERO, DECIDE``1 < n ==> n <> 1``] >>
    `x IN g.carrier` by rw[Estar_element] >>
    `x ** k MOD m = 1` by rw[EXP_MOD, Abbr`x`] >>
    `order (Invertibles (ZN m).prod) x divides k` by rw[GSYM group_order_divides_exp, Estar_exp, Estar_property] >>
    metis_tac[ZN_invertibles_order],
    `ordz m n <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `coprime m x` by rw[GSYM coprime_mod_iff, Abbr`x`] >>
    `0 < x` by metis_tac[GCD_0, NOT_ZERO_LT_ZERO, DECIDE``1 < n ==> n <> 1``] >>
    `x IN g.carrier` by rw[Estar_element] >>
    `ordz m x = ordz m n` by rw[ZN_order_mod, Abbr`x`] >>
    `x ** k MOD m = 1` by metis_tac[group_order_divides_exp, ZN_invertibles_order, Estar_exp, Estar_property] >>
    rw[GSYM EXP_MOD, Abbr`x`]
  ]);

(* Theorem: 0 < m /\ 0 < ordz m n ==> (ordz m n) divides (phi m) *)
(* Proof:
   Note 0 < ordz m n ==> coprime m n    by ZN_order_nonzero, 0 < m
   Thus (ordz m n) divides (phi m)      by ZN_coprime_order_divides_phi, 0 < m
*)
val ZN_order_divides_phi = store_thm(
  "ZN_order_divides_phi",
  ``!m n. 0 < m /\ 0 < ordz m n ==> (ordz m n) divides (phi m)``,
  rpt strip_tac >>
  `coprime m n` by metis_tac[ZN_order_nonzero, NOT_ZERO_LT_ZERO] >>
  rw[ZN_coprime_order_divides_phi]);

(* Theorem: 0 < m ==> ordz m n <= phi m *)
(* Proof:
   If ordz m n = 0, then trivially true.
   Otherwise, 0 < ordz m n.
   Note ordz m n divides phi m       by ZN_order_divides_phi, 0 < m /\ 0 < ordz m n
    and 0 < phi m                    by phi_pos, 0 < m
     so ordz m n <= phi m            by DIVIDES_LE, 0 < phi m
*)
val ZN_order_upper = store_thm(
  "ZN_order_upper",
  ``!m n. 0 < m ==> ordz m n <= phi m``,
  rpt strip_tac >>
  Cases_on `ordz m n = 0` >-
  rw[] >>
  `ordz m n divides phi m` by rw[ZN_order_divides_phi] >>
  `0 < phi m` by rw[phi_pos] >>
  rw[DIVIDES_LE]);

(* Theorem: 0 < m ==> ordz m n <= m *)
(* Proof:
   Note ordz m n <= phi m            by ZN_order_upper, 0 < m
   Also phi m <= m                   by phi_le
   Thus ordz m n <= m                by LESS_EQ_TRANS
*)
val ZN_order_le = store_thm(
  "ZN_order_le",
  ``!m n. 0 < m ==> ordz m n <= m``,
  rpt strip_tac >>
  `ordz m n <= phi m` by rw[ZN_order_upper] >>
  `phi m <= m` by rw[phi_le] >>
  decide_tac);

(* Theorem: 0 < k /\ k < m ==> ordz k n < m *)
(* Proof:
   Note ordz k n <= k      by ZN_order_le, 0 < k
    and             k < m  by given
   Thus ordz k n < m       by LESS_EQ_LESS_TRANS
*)
val ZN_order_lt = store_thm(
  "ZN_order_lt",
  ``!k n m. 0 < k /\ k < m ==> ordz k n < m``,
  rpt strip_tac >>
  `ordz k n <= k` by rw[ZN_order_le] >>
  decide_tac);
(* Therefore, in the search for k such that m <= ordz k n, start with k = m *)

(*
val ZN_order_minimal =
  order_minimal |> ISPEC ``(ZN n).prod`` |> ADD_ASSUM ``1 < n`` |> DISCH_ALL
                |> SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [ZN_property, ZN_exp];

val ZN_order_minimal = |- 1 < n ==> !x n'. 0 < n' /\ n' < ordz n x ==> x ** n' MOD n <> 1: thm
*)

(* Theorem: 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1 *)
(* Proof:
   Note (ZN m).prod.exp n k <> (ZN m).prod.id    by order_minimal, 0 < k, k < ordz m n
    But (ZN m).prod.exp n k = n ** k MOD n       by ZN_exp, 0 < m
    and m <> 1  since !k. 0 < k /\ k < 1 = F     by ZN_order_mod_1, 0 < m
     so (ZN m).prod.id = 1                       by ZN_property, m <> 1
   Thus n ** k MOD m <> 1                        by above
*)
val ZN_order_minimal = store_thm(
  "ZN_order_minimal",
  ``!m n k. 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1``,
  metis_tac[order_minimal, ZN_order_mod_1, ZN_property, ZN_exp, DECIDE``(0 < k /\ k < 1) = F``]);

(* Theorem: 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m n *)
(* Proof:
   Let x = n MOD m.
   Then ordz m x = ordz m n             by ZN_order_mod, 0 < m
    and ordz m n <> 0                   by ZN_order_nonzero, coprime m n
    and ordz m n <> 1                   by ZN_order_eq_1_alt, 1 < m
   Thus ordz 1 < ordz m n               by arithmetic
*)
val ZN_coprime_order_gt_1 = store_thm(
  "ZN_coprime_order_gt_1",
  ``!m n. 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m n``,
  rpt strip_tac >>
  qabbrev_tac `x = n MOD m` >>
  `ordz m x = ordz m n` by rw[ZN_order_mod, Abbr`x`] >>
  `ordz m n <> 0` by rw[ZN_order_nonzero] >>
  `ordz m n <> 1` by rw[ZN_order_eq_1_alt, Abbr`x`] >>
  decide_tac);

(* Note: 1 < n MOD m cannot be replaced by 1 < n. A counterexample:
   1 < m /\ 1 < n /\ coprime m n ==> 1 < ordz m n
   1 < 7 /\ 1 < 43 /\ coprime 7 43, but ordz 7 43 = ordz 7 (43 MOD 7) = ordz 7 1 = 1.
*)

(* Theorem: 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m *)
(* Proof:
   Note m <> 0     by GCD_0, 1 < n
    and m <> 1     by ZN_order_mod_1, 1 < ordz m n
   Thus 1 < m
*)
val ZN_order_with_coprime_1 = store_thm(
  "ZN_order_with_coprime_1",
  ``!m n. 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m``,
  rpt strip_tac >>
  `m <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
  `m <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  decide_tac);

(* Theorem: 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==> 1 < n /\ 1 < k *)
(* Proof:
   Note k <> 1             by ZN_order_mod_1, 1 < ordz k m, 1 < m
    and n <> 1             by DIVIDES_ONE, m divides n, 1 < m
   also k <> 0 /\ n <> 0   by coprime_0L, coprime_0R
     so 1 < n /\ 1 < k     by both not 0, not 1.
*)
val ZN_order_with_coprime_2 = store_thm(
  "ZN_order_with_coprime_2",
  ``!m n k. 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==> 1 < n /\ 1 < k``,
  ntac 4 strip_tac >>
  `k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  `k <> 0 /\ n <> 0` by metis_tac[coprime_0L, coprime_0R] >>
  decide_tac);

(* Theorem: 1 < m ==> ((ordz m n = 0) <=> (!j. 0 < j /\ j < m ==> n ** j MOD m <> 1)) *)
(* Proof:
   If part: ordz m n = 0 ==> !j. 0 < j /\ j < m ==> n ** j MOD m <> 1
      Note !j. 0 < j ==> n ** j MOD m <> 1       by ZN_order_eq_0_iff
      Thus n ** j MOD m <> 1                     by just 0 < j
   Only-of part: !j. 0 < j /\ j < m ==> n ** j MOD m <> 1 ==> ordz m n = 0
      By contradiction, suppose ordz m n <> 0.
      Then coprime m n                           by ZN_order_eq_0
      Let k = ord z m.
      Then k < m                                 by ZN_order_lt, 0 < m, coprime m n
       and n ** k MOD m = 1                      by ZN_order_property_alt, 1 < m
      This contradicts n ** k MOD m <> 1         by implication
*)
val ZN_order_eq_0_test = store_thm(
  "ZN_order_eq_0_test",
  ``!m n. 1 < m ==> ((ordz m n = 0) <=> (!j. 0 < j /\ j < m ==> n ** j MOD m <> 1))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ZN_order_eq_0_iff] >>
  spose_not_then strip_assume_tac >>
  `0 < ordz m n /\ 0 < m` by decide_tac >>
  `coprime m n` by metis_tac[ZN_order_eq_0] >>
  `ordz m n < m` by rw[ZN_coprime_order_lt] >>
  metis_tac[ZN_order_property_alt]);

(* Theorem: 1 < n /\ 0 < j /\ 1 < k ==>
            (k divides (n ** j - 1) <=> (ordz k n) divides j) *)
(* Proof:
   Note 1 < n ** j                  by ONE_LT_EXP, 1 < n, 0 < j
       k divides (n ** j - 1)
   <=> (n ** j - 1) MOD k = 0       by DIVIDES_MOD_0, 0 < k
   <=> n ** j MOD k = 1 MOD k       by MOD_EQ, 1 < n ** j, 0 < k
                    = 1             by ONE_MOD, 1 < k
   <=> (ordz k n) divides j         by ZN_order_divides_exp, 0 < j, 1 < k
*)
val ZN_order_divides_tops_index = store_thm(
  "ZN_order_divides_tops_index",
  ``!n j k. 1 < n /\ 0 < j /\ 1 < k ==>
       (k divides (n ** j - 1) <=> (ordz k n) divides j)``,
  rpt strip_tac >>
  `1 < n ** j` by rw[ONE_LT_EXP] >>
  `k divides (n ** j - 1) <=> ((n ** j - 1) MOD k = 0)` by rw[DIVIDES_MOD_0] >>
  `_ = (n ** j MOD k = 1 MOD k)` by rw[MOD_EQ] >>
  `_ = (n ** j MOD k = 1)` by rw[ONE_MOD] >>
  `_ = (ordz k n) divides j` by rw[ZN_order_divides_exp] >>
  metis_tac[]);

(* Theorem: 1 < n /\ 0 < j /\ 1 < k /\ k divides (n ** j - 1) ==> (ordz k n) <= j *)
(* Proof:
   Note (ordz k n) divides j      by ZN_order_divides_tops_index
   Thus (ordz k n) <= j           by DIVIDES_LE, 0 < j
*)
val ZN_order_le_tops_index = store_thm(
  "ZN_order_le_tops_index",
  ``!n j k. 1 < n /\ 0 < j /\ 1 < k /\ k divides (n ** j - 1) ==> (ordz k n) <= j``,
  rw[GSYM ZN_order_divides_tops_index, DIVIDES_LE]);

(* ------------------------------------------------------------------------- *)
(* ZN Order Test                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
            (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
            !j. 0 < j /\ j < k /\ ~(j divides phi m) ==> (ordz m n = k) \/ n ** j MOD m <> 1 *)
(* Proof:
   By contradiction, suppose (ordz m n <> k) /\ (n ** j MOD m = 1).
   Let z = ordz m n.
   Then z divides j /\ z divides k        by ZN_order_divides_exp
     so z <= k                            by DIVIDES_LE, 0 < k
     or z < k                             by z <> k (from contradiction assumption)
   Also 0 < z                             by ZERO_DIVIDES, z divides j, 0 < j
    and z divides (phi m)                 by ZN_order_divides_phi, 0 < z
    Put j = z in implication gives: n ** z MOD m <> 1
    This contradicts n ** z MOD m = 1     by ZN_order_property_alt, 1 < m
*)
val ZN_order_test_propery = store_thm(
  "ZN_order_test_propery",
  ``!m n k. 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
   (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
   !j. 0 < j /\ j < k /\ ~(j divides phi m) ==> (ordz m n = k) \/ n ** j MOD m <> 1``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `z = ordz m n` >>
  `z divides j /\ z divides k` by rw[GSYM ZN_order_divides_exp, Abbr`z`] >>
  `z <= k` by rw[DIVIDES_LE] >>
  `z < k` by decide_tac >>
  `0 < z` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `z divides (phi m)` by rw[ZN_order_divides_phi, Abbr`z`] >>
  metis_tac[ZN_order_property_alt]);

(*
> order_thm |> GEN_ALL |> ISPEC ``(ZN m).prod`` |> ISPEC ``n:num`` |> ISPEC ``k:num``;
val it = |- 0 < k ==> ((ordz m n = k) <=>
    ((ZN m).prod.exp n k = (ZN m).prod.id) /\
    !m'. 0 < m' /\ m' < k ==> (ZN m).prod.exp n m' <> (ZN m).prod.id): thm
*)

(* Theorem: 1 < m /\ 0 < k ==>
            ((ordz m n = k) <=> ((n ** k) MOD m = 1) /\ !j. 0 < j /\ j < k ==> (n ** j) MOD m <> 1) *)
(* Proof:
   By order_thm, 0 < k ==>
   ((ordz m n = k) <=> ((ZN m).prod.exp n k = (ZN m).prod.id) /\
                       !j. 0 < j /\ j < k ==> (ZN m).prod.exp n j <> (ZN m).prod.id)
   Now (ZN m).prod.exp n k = (n ** k) MOD m    by ZN_exp, 0 < m
   and (ZN m).prod.id = 1                      by ZN_property, m <> 1
   Thus the result follows.
*)
val ZN_order_test_1 = store_thm(
  "ZN_order_test_1",
  ``!m n k. 1 < m /\ 0 < k ==>
   ((ordz m n = k) <=> ((n ** k) MOD m = 1) /\ !j. 0 < j /\ j < k ==> (n ** j) MOD m <> 1)``,
  metis_tac[order_thm, ZN_exp, ZN_ids_alt, DECIDE``1 < m ==> 0 < m``]);

(* Theorem: 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
            (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) *)
(* Proof:
   If part: ordz m n = k ==> (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)
      This is to show:
      (1) n ** (ordz m n) MOD m = 1, true   by ZN_order_property, 1 < m.
      (2) !j. 0 < j /\ j < (ordz m n) /\ j divides (phi m) ==> n ** j MOD m <> 1)
          This is true                      by ZN_order_minimal, 1 < m.
   Only-if part: (n ** k MOD m = 1) /\
                 !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) ==> ordz m n = k
      Note the conditions give:
      !j. 0 < j /\ j < k /\ ~(j divides phi m)
          ==> (ordz m n = k) \/ n ** j MOD m <> 1    by ZN_order_test_propery
      Combining both implications,
      !j. 0 < j /\ j < k  ==> n ** j MOD m <> 1
      Thus ordz m n = k                     by ZN_order_test_1
*)
val ZN_order_test_2 = store_thm(
  "ZN_order_test_2",
  ``!m n k. 1 < m /\ 0 < k ==>
     ((ordz m n = k) <=>
      (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)``,
  rw[EQ_IMP_THM] >-
  rw[ZN_order_property] >-
  rw[ZN_order_minimal] >>
  `!j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
       (ordz m n = k) \/ n ** j MOD m <> 1` by rw[ZN_order_test_propery] >>
  metis_tac[ZN_order_test_1]);

(* Theorem: 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
   (k divides phi m) /\ (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) *)
(* Proof:
   If part: ordz m n = k ==> (k divides phi m) /\
            (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)
      This is to show:
      (1) (ordz m n) divides phi m, true    by ZN_order_divides_phi, 1 < m.
      (2) n ** (ordz m n) MOD m = 1, true   by ZN_order_property, 1 < m.
      (3) !j. 0 < j /\ j < (ordz m n) /\ j divides (phi m) ==> n ** j MOD m <> 1)
          This is true                      by ZN_order_minimal, 1 < m.
   Only-if part: (k divides phi m) /\ (n ** k MOD m = 1) /\
                 !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) ==> ordz m n = k
      Note the conditions give:
      !j. 0 < j /\ j < k /\ ~(j divides phi m)
          ==> (ordz m n = k) \/ n ** j MOD m <> 1    by ZN_order_test_propery
      Combining both implications,
      !j. 0 < j /\ j < k  ==> n ** j MOD m <> 1
      Thus ordz m n = k                     by ZN_order_test_1
*)
val ZN_order_test_3 = store_thm(
  "ZN_order_test_3",
  ``!m n k. 1 < m /\ 0 < k ==>
     ((ordz m n = k) <=>
      (k divides phi m) /\ (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)``,
  rw[EQ_IMP_THM] >-
  rw[ZN_order_divides_phi] >-
  rw[ZN_order_property] >-
  rw[ZN_order_minimal] >>
  `!j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
       (ordz m n = k) \/ n ** j MOD m <> 1` by rw[ZN_order_test_propery] >>
  metis_tac[ZN_order_test_1]);

(* Theorem: 1 < m ==> (ordz m n = k <=> n ** k MOD m = 1 /\
           !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1) *)
(* Proof:
   If k = 0,
      Note n ** 0 MOD m
         = 1 MOD m                       by EXP_0
         = 1                             by ONE_MOD, 1 < m
      The result follows                 by ZN_order_eq_0_test
   If k <> 0, the result follows         by ZN_order_test_1
*)
val ZN_order_test_4 = store_thm(
  "ZN_order_test_4",
  ``!m n k. 1 < m ==> ((ordz m n = k) <=> ((n ** k MOD m = 1) /\
    !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1))``,
  rpt strip_tac >>
  (Cases_on `k = 0` >> simp[]) >| [
    `n ** 0 MOD m = 1` by rw[EXP_0] >>
    metis_tac[ZN_order_eq_0_test],
    rw[ZN_order_test_1]
  ]);

(* ------------------------------------------------------------------------- *)
(* ZN Homomorphism                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier *)
(* Proof:
   Expand by definitions, this is to show:
   x < n ==> x MOD m < m, true by MOD_LESS.
*)
val ZN_to_ZN_element = store_thm(
  "ZN_to_ZN_element",
  ``!n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier``,
  rw[ZN_def]);

(* Theorem: 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum *)
(* Proof:
   Note 0 < m                     by ZERO_DIVIDES, 0 < n
   Expand by definitions, this is to show:
      x < n /\ x' < n ==> (x + x') MOD n MOD m = (x MOD m + x' MOD m) MOD m
     (x + x') MOD n MOD m
   = (x + x') MOD m               by DIVIDES_MOD_MOD, 0 < n
   = (x MOD m + x' MOD m) MOD m   by MOD_PLUS, 0 < m
*)
val ZN_to_ZN_sum_group_homo = store_thm(
  "ZN_to_ZN_sum_group_homo",
  ``!n m. 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[ZN_def, GroupHomo_def, DIVIDES_MOD_MOD, MOD_PLUS]);

(* Theorem: 0 < n /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod *)
(* Proof:
   Note 0 < m                           by ZERO_DIVIDES, 0 < n
   Expand by definitions, this is to show:
   (1) x < n /\ x' < n ==> (x * x') MOD n MOD m = (x MOD m * x' MOD m) MOD m
         (x * x') MOD n MOD m
       = (x * x') MOD m                 by DIVIDES_MOD_MOD, 0 < n
       = (x MOD m * x' MOD m) MOD m     by MOD_TIMES2, 0 < m
   (2) 0 < m /\ m <> 1 ==> 1 < m, trivially true.
*)
val ZN_to_ZN_prod_monoid_homo = store_thm(
  "ZN_to_ZN_prod_monoid_homo",
  ``!n m. 0 < n /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[ZN_def, MonoidHomo_def, times_mod_def, DIVIDES_MOD_MOD] >>
  fs[DIVIDES_ONE]);

(* Theorem: 0 < n /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (ZN m) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier
       Note 0 < m                           by ZERO_DIVIDES, 0 < n
       Hence true                           by ZN_to_ZN_element, 0 < m.
   (2) GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum, true by ZN_to_ZN_sum_group_homo.
   (3) MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod, true by ZN_to_ZN_prod_monoid_homo.
*)
val ZN_to_ZN_ring_homo = store_thm(
  "ZN_to_ZN_ring_homo",
  ``!n m. 0 < n /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (ZN m)``,
  rw[RingHomo_def] >-
  metis_tac[ZN_to_ZN_element, ZERO_DIVIDES, NOT_ZERO] >-
  rw[ZN_to_ZN_sum_group_homo] >>
  rw[ZN_to_ZN_prod_monoid_homo]);

(* ------------------------------------------------------------------------- *)
(* A Ring from Sets.                                                         *)
(* ------------------------------------------------------------------------- *)

(* The Ring from Group (symdiff_set) and Monoid (set_inter). *)
val symdiff_set_inter_def = Define`
  symdiff_set_inter = <| carrier := UNIV;
                             sum := symdiff_set;
                            prod := set_inter |>
`;
(* Evaluation is given later in symdiff_eval. *)

(* Theorem: symdiff_set_inter is a Ring. *)
(* Proof: check definitions.
   For the distribution law:
   x INTER (y SYM z) = (x INTER y) SYM (x INTER z)
   first verify by Venn Diagram.
*)
Theorem symdiff_set_inter_ring:
  Ring symdiff_set_inter
Proof
  rw_tac std_ss[Ring_def, symdiff_set_inter_def] >>
  rw[symdiff_set_def, set_inter_def] >>
  rw[EXTENSION, symdiff_def] >>
  metis_tac[]
QED

(* Theorem: symdiff UNIV UNIV = EMPTY` *)
(* Proof: by definition. *)
val symdiff_univ_univ_eq_empty = store_thm(
  "symdiff_univ_univ_eq_empty",
  ``symdiff UNIV UNIV = EMPTY``,
  rw[symdiff_def]);

(* Note: symdiff_set_inter has carrier infinite, but characteristics 2. *)

(* Theorem: char symdiff_set_inter = 2 *)
(* Proof:
   By definition, and making use of FUNPOW_2.
   First to show:
   ?n. 0 < n /\ (FUNPOW (symdiff univ(:'a)) n {} = {})
   Put n = 2, and apply FUNPOW_2 and symdiff_def.
   Second to show:
   0 < n /\ FUNPOW (symdiff univ(:'a)) n {} = {} /\
   !m. m < n ==> ~(0 < m) \/ FUNPOW (symdiff univ(:'a)) m {} <> {} ==> n = 2
   By contradiction. Assume n <> 2, then n < 2 or 2 < n.
   If n < 2, then 0 < n < 2 means n = 1,
   but FUNPOW (symdiff univ(:'a)) 1 {} = symdiff univ(:'a) {} = univ(:'a) <> {}, a contradiction.
   If 2 < n, then FUNPOW (symdiff univ(:'a)) 2 {} <> {}, contradicting FUNPOW_2 and symdiff_def.
*)
Theorem symdiff_set_inter_char:
  char symdiff_set_inter = 2
Proof
  simp[char_def, order_def, period_def, symdiff_set_inter_def,
       monoid_exp_def, symdiff_set_def, set_inter_def] >>
  `FUNPOW (symdiff univ(:'a)) 2 {} = {}` by rw[FUNPOW_2, symdiff_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  `~(n < 2) /\ ~(2 < n)` suffices_by decide_tac >>
  spose_not_then strip_assume_tac >>
  ‘~(2 < n)’ by metis_tac[DECIDE “2 ≠ 0”] >> gs[] >>
  `n = 1` by decide_tac >>
  gs[symdiff_def]
QED

(* Theorem: evaluation for symdiff dields. *)
(* Proof: by definitions. *)
Theorem symdiff_eval[compute]:
  ((symdiff_set).carrier = UNIV) /\
  (!x y. (symdiff_set).op x y = (x UNION y) DIFF (x INTER y)) /\
  ((symdiff_set).id = EMPTY)
Proof
  rw_tac std_ss[symdiff_set_def, symdiff_def]
QED
(*
EVAL ``order (symdiff_set) EMPTY``;
> val it = |- order symdiff_set {} = 1 : thm
*)

(* ------------------------------------------------------------------------- *)
(* Order Computation using a WHILE loop                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A Small Example of WHILE loop invariant                                   *)
(* ------------------------------------------------------------------------- *)

(* Pseudocode: search through all indexes from 1.

Input: m, n with 1 < m, 0 < n
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

if ~(coprime m n) return 0    // initial check
// For coprime m n, search the least index j such that (n ** j = 1) (mod m).
// Search upwards for least index j
j <- 1                        // initial index
while ((n ** i) MOD m <> 1) j <- j + 1  // increment j
return j                      // the least index j.

*)

(* Compute ordz m n = order (ZN m).prod n = ordz m n *)
val compute_ordz_def = Define`
    compute_ordz m n =
         if m = 0 then ordz 0 n
    else if m = 1 then 1 (* ordz 1 n = 1 *)
    else if coprime m n then
         WHILE (\i. (n ** i) MOD m <> 1) SUC 1  (* i = 1, WHILE (n ** i (MOD m) <> 1) i <- SUC i) *)
    else 0  (* ordz m n = 0 when ~(coprime m n) *)
`;

(* Examples:
> EVAL ``compute_ordz 10 3``; --> 4
> EVAL ``compute_ordz 10 4``; --> 0
> EVAL ``compute_ordz 10 7``; --> 4
> EVAL ``compute_ordz 10 19``; --> 2

> EVAL ``phi 10``; --> 4

Indeed, (ordz m n) is a divisor of (phi m).
Since phi(10) = 4, ordz 10 n is a divisior of 4.

> EVAL ``compute_ordz 1 19``; --> 1;

> EVAL ``MAP (compute_ordz 7) [1 .. 6]``; = [1; 3; 6; 3; 6; 2]
> EVAL ``MAP (combin$C compute_ordz 10) [2 .. 13]``; = [0; 1; 0; 0; 0; 6; 0; 1; 0; 2; 0; 6]
  shows that, in decimals (base 10), 1/2 is finite, 1/3 has period 1, 1/7 has period 6,
                                     1/9 has period 1, 1/11 has period 2, 1/13 has period 6.
*)

(*
> EVAL ``WHILE (\i. i <= 4) SUC 1``;
val it = |- WHILE (\i. i <= 4) SUC 1 = 5: thm
*)

(*
For WHILE Guard Cmd,
we want to show:
   {Pre-condition} WHILE Guard Cmd {Post-condition}

> WHILE_RULE;
val it = |- !R B C. WF R /\ (!s. B s ==> R (C s) s) ==>
     HOARE_SPEC (\s. P s /\ B s) C P ==>
     HOARE_SPEC P (WHILE B C) (\s. P s /\ ~B s): thm

> HOARE_SPEC_DEF;
val it = |- !P C Q. HOARE_SPEC P C Q <=> !s. P s ==> Q (C s): thm
*)

(* Theorem: (!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
            (!x. Precond x ==> Invariant x) /\
            (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
            HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
            HOARE_SPEC Precond (WHILE Guard Cmd) Postcond *)
(* Proof:
   By HOARE_SPEC_DEF, change the goal to show:
      !s. Invariant s ==> Postcond (WHILE Guard Cmd s)
   By complete induction on (f s).
   After rewrite by WHILE, this is to show:
      Postcond (if Guard s then WHILE Guard Cmd (Cmd s) else s)
   If Guard s,
      With Invariant s,
       ==> Postcond (WHILE Guard Cmd (Cmd s))   by induction hypothesis
   If ~(Guard s),
      With Invariant s,
       ==> Postcond s                           by given
*)
val WHILE_RULE_PRE_POST = store_thm(
  "WHILE_RULE_PRE_POST",
  ``(!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
   (!x. Precond x ==> Invariant x) /\
   (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
   HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
   HOARE_SPEC Precond (WHILE Guard Cmd) Postcond``,
  simp[HOARE_SPEC_DEF] >>
  rpt strip_tac >>
  `!s. Invariant s ==> Postcond (WHILE Guard Cmd s)` suffices_by metis_tac[] >>
  Q.UNDISCH_THEN `Precond s` (K ALL_TAC) >>
  rpt strip_tac >>
  completeInduct_on `f s` >>
  rpt strip_tac >>
  fs[PULL_FORALL] >>
  first_x_assum (qspec_then `f` assume_tac) >>
  rfs[] >>
  ONCE_REWRITE_TAC[WHILE] >>
  Cases_on `Guard s` >>
  simp[]);
(* Michael's version:
val WHILE_RULE_PRE_POST = Q.store_thm(
  "WHILE_RULE_PRE_POST",
  `(!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
   (!x. Precond x ==> Invariant x) /\
   (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
   HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
   HOARE_SPEC Precond (WHILE Guard Cmd) Postcond`,
  simp[whileTheory.HOARE_SPEC_DEF] >>
  rpt strip_tac >>
  `!s. Invariant s ==> Postcond (WHILE Guard Cmd s)`
     suffices_by metis_tac[] >>
  Q.UNDISCH_THEN `Precond s` (K ALL_TAC) >>
  rpt strip_tac >>
  completeInduct_on `f s` >>
  rpt strip_tac >>
  fs[PULL_FORALL] >>
  first_x_assum (qspec_then `f` assume_tac) >>
  rfs[] >>
  ONCE_REWRITE_TAC[WHILE] >>
  Cases_on `Guard s` >> simp[]
)
*)

(* Theorem: 1 < m /\ coprime m n ==>
            HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                       (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                       (\i. i = ordz m n) *)
(* Proof:
   By WHILE_RULE_PRE_POST, this is to show:
      ?Invariant f. (!x. (\i. 0 < i /\ i <= ordz m n) x ==> Invariant x) /\
                    (!x. Invariant x /\ (\i. (n ** i) MOD m <> 1) x ==> f (SUC x) < f x) /\
                    (!x. Invariant x /\ ~(\i. (n ** i) MOD m <> 1) x ==> (\i. i = ordz m n) x) /\
                    HOARE_SPEC (\x. Invariant x /\ (\i. (n ** i) MOD m <> 1) x) SUC Invariant
   By looking at the first requirement, and peeking at the second,
   let Invariant = \i. 0 < i /\ i <= ordz m n, f = \i. ordz m n - i.
   This is to show:
   (1) 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> 0 < ordz m n - x
       If x = ordz m n, then this is true                  by ZN_coprime_order_alt
       Otherwise, x <> ordz m n, hence 0 < ordz m n - x    by arithmetic
   (2) 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m = 1 ==> x = ordz m n
       If x = ordz m n, then this is true trivially.
       Otherwise, x <> ordz m n,
       or x < ordz m n, and 0 < m, but n ** x MOD m = 1, contradicts  ZN_order_minimal.
   (3) 1 < m /\ coprime m n ==>
       HOARE_SPEC (\x. (0 < x /\ x <= ordz m n) /\ n ** x MOD m <> 1) SUC (\i. 0 < i /\ i <= ordz m n)
       By HOARE_SPEC_DEF, this is to show:
          1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> SUC x <= ordz m n
       or 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> x < ordz m n
       By contradiction, suppose x = ordz m n.
       Then n ** x MOD m = 1, a contradiction         by ZN_coprime_order_alt, 1 < m
*)
val compute_ordz_hoare = store_thm(
  "compute_ordz_hoare",
  ``!m n. 1 < m /\ coprime m n ==>
         HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                    (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                    (\i. i = ordz m n)``,
  rpt strip_tac >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\i. 0 < i /\ i <= ordz m n` >>
  qexists_tac `\i. ordz m n - i` >>
  rw[] >| [
    Cases_on `x = ordz m n` >| [
      rw[] >>
      rfs[ZN_coprime_order_alt],
      decide_tac
    ],
    Cases_on `x = ordz m n` >-
    simp[] >>
    rfs[] >>
    `x < ordz m n /\ 0 < m` by decide_tac >>
    metis_tac[ZN_order_minimal],
    rw[HOARE_SPEC_DEF] >>
    `x < ordz m n` suffices_by decide_tac >>
    spose_not_then strip_assume_tac >>
    `x = ordz m n` by decide_tac >>
    rw[] >>
    rfs[ZN_coprime_order_alt]
  ]);
(* Michael's version:
val compute_ordz_hoare = prove(
  ``1 < m /\ coprime m n ==>
    HOARE_SPEC
      (\i. 0 < i /\ i <= ordz m n)
               (WHILE (\i. (n ** i) MOD m <> 1) SUC)
      (\i. i = ordz m n)``,
  strip_tac >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\i. 0 < i /\ i <= ordz m n` >>
  qexists_tac `\i. ordz m n - i` >>
  rw[] >| [
    (* Case 1 *)
    reverse (Cases_on `x = ordz m n`) >- decide_tac >>
    rw[] >>
    rfs[ZN_coprime_order_alt],

    (* Case 2 *)
    Cases_on `x = ordz m n` >- simp[] >>
    rfs[] >>
    `x < ordz m n /\ 0 < m` by decide_tac >>
    metis_tac[ZN_order_minimal],

    (* Case 3 *)
    rw[HOARE_SPEC_DEF] >>
    `x < ordz m n` suffices_by decide_tac >>
    spose_not_then assume_tac >>
    `x = ordz m n` by decide_tac >> rw[] >>
    rfs[ZN_coprime_order_alt]
  ]);
*)

(*
val compute_ordz_hoare =
   |- 1 < m /\ coprime m n ==> HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
      (WHILE (\i. (n ** i) MOD m <> 1) SUC) (\i. i = ordz m n): thm

SIMP_RULE (srw_ss()) [HOARE_SPEC_DEF] compute_ordz_hoare;
val it = |- 1 < m /\ coprime m n ==>
            !i. 0 < i /\ i <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC i = ordz m n): thm
*)

(* Theorem: 1 < m /\ coprime m n ==>
            !j. 0 < j /\ j <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n) *)
(* Proof:
   By compute_ordz_hoare, we have the loop-invariant:
   HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
              (WHILE (\i. (n ** i) MOD m <> 1) SUC)
              (\i. i = ordz m n)
   Let Px = \i. 0 < i /\ i <= ordz m n                   be the pre-condition
       Cx = WHILE (\i. (n ** i) MOD m <> 1) SUC   be the command body
       Qx = \i. i = ordz m n                             be the post-condition
   ==> HOARE_SPEC Px Cx Qx                               by above
   Apply HOARE_SPEC_DEF, |- HOARE_SPEC P C Q <=> !s. P s ==> Q (C s)
   Thus !j. P j ==> Qx (Cx j)
     or !j. 0 < j /\ j <= ordz m n ==>
        (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)
*)
val compute_ordz_by_while = prove(
  ``!m n. 1 < m /\ coprime m n ==>
   !j. 0 < j /\ j <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)``,
  rpt strip_tac >>
  `HOARE_SPEC
      (\i. 0 < i /\ i <= ordz m n)
      (WHILE (\i. (n ** i) MOD m <> 1) SUC)
      (\i. i = ordz m n)` by rw[compute_ordz_hoare] >>
  fs[HOARE_SPEC_DEF]);

(* ------------------------------------------------------------------------- *)
(* Correctness of computing ordz m n.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: compute_ordz 0 n = ordz 0 n *)
(* Proof: by compute_ordz_def *)
val compute_ordz_0 = store_thm(
  "compute_ordz_0",
  ``!n. compute_ordz 0 n = ordz 0 n``,
  rw[compute_ordz_def]);

(* Theorem: compute_ordz 1 n = 1 *)
(* Proof: by compute_ordz_def *)
val compute_ordz_1 = store_thm(
  "compute_ordz_1",
  ``!n. compute_ordz 1 n = 1``,
  rw[compute_ordz_def]);

(* Theorem: compute_ordz m n = ordz m n *)
(* Proof:
   If m = 0,
      Then compute_ordz 0 n = ordz 0 n     by compute_ordz_0
   If m = 1,
      Then compute_ordz 1 n = 1            by compute_ordz_1
                            = ordz 1 n     by ZN_order_mod_1
   If m <> 0, m <> 1,
      Then 1 < m                           by arithmetic
      If ordz m n = 0,
         Then ~coprime m n                 by ZN_order_eq_0
              compute_ordz m n
            = 0                            by compute_ordz_def
            = ordz m n                     by ordz m n = 0
      If ordz m n <> 0,
         Then coprime m n                  by ZN_order_eq_0
          and 1 <= ordz m n                by arithmetic
              compute_ordz m n
            = WHILE (\i. (n ** i) MOD m <> 1) SUC 1   by compute_ordz_def
            = ordz m n                                       by compute_ordz_by_while, put j = 1.
*)
val compute_ordz_eqn = store_thm(
  "compute_ordz_eqn",
  ``!m n. compute_ordz m n = ordz m n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[compute_ordz_0] >>
  `0 < m` by decide_tac >>
  Cases_on `m = 1` >-
  rw[compute_ordz_1, ZN_order_mod_1] >>
  Cases_on `ordz m n = 0` >| [
    `~coprime m n` by rw[GSYM ZN_order_eq_0] >>
    rw[compute_ordz_def],
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `1 < m` by decide_tac >>
    rw[compute_ordz_def, compute_ordz_by_while]
  ]);

(* Theorem: order (times_mod m) n = compute_ordz m n *)
(* Proof: by compute_ordz_eqn *)
val ordz_eval = store_thm(
  "ordz_eval[compute]",
  ``!m n. order (times_mod m) n = compute_ordz m n``,
  rw[ZN_eval, compute_ordz_eqn]);
(* Put in computeLib for simplifier. *)

(*
> EVAL ``ordz 7 10``;
val it = |- ordz 7 10 = 6: thm
*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
