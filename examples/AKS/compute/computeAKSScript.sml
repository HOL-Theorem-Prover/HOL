(* ------------------------------------------------------------------------- *)
(* AKS Computations                                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computeAKS";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory primeTheory;

open ringTheory;

(* Get dependent theories local *)
open computeParamTheory computeOrderTheory;
open computeBasicTheory;

(* val _ = load "computeRingTheory"; *)
open computeRingTheory computePolyTheory;

open polyWeakTheory polyRingTheory;
open polyMonicTheory polyDivisionTheory;

(* ------------------------------------------------------------------------- *)
(* AKS Computations Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Introspective Computations in a Ring:
   unity_mod_intro_def    |- !r k n c. unity_mod_intro r k n c <=>
                             (unity_mod_exp r (unity_mod_monomial r k c) n = unity_mod_special r k n c)
   unity_mod_intro_range_def
                          |- (!r k n. unity_mod_intro_range r k n 0 <=> T) /\
                              !r k n m. unity_mod_intro_range r k n (SUC m) <=>
                                        unity_mod_intro r k n (SUC m) /\ unity_mod_intro_range r k n m
   unity_mod_intro_alt    |- !r. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
                             !c. unity_mod_intro r k n c <=> ((X + |c|) ** n == X ** n + |c|) (pm (unity k))

   Direct Computations using ZN Polynomials:
   ZN_poly_intro_def      |- !n k c. ZN_poly_intro n k c <=>
                                     (ZN_poly_monomial n k c **z n = ZN_very_special n k c)
   ZN_poly_intro_range_def|- (!n k. ZN_poly_intro_range n k 0 <=> T) /\
                              !n k m. ZN_poly_intro_range n k (SUC m) <=>
                                      ZN_poly_intro n k (SUC m) /\ ZN_poly_intro_range n k m
   ZN_poly_intro_alt      |- !n k. 1 < n /\ 0 < k ==>
                             !c. ZN_poly_intro n k c <=> unity_mod_intro (ZN n) k n c
   ZN_poly_intro_range_alt|- !n k. 1 < n /\ 0 < k ==>
                             !m. ZN_poly_intro_range n k m <=> unity_mod_intro_range (ZN n) k n m
   ZN_poly_intro_range_thm|- !n k m. ZN_poly_intro_range n k m <=> !c. 0 < c /\ c <= m ==> ZN_poly_intro n k c

   AKS Algorithm:
   aks_compute_def      |- !n. aks_compute n <=> power_free_check n /\
                               case aks_param n of
                                 nice j => j = n
                               | good k => unity_mod_intro_range (ZN n) k n (sqrt_compute (phi_compute k) * ulog n)
                               | bad => F

   aks_compute_alt_weak |- !n. aks_compute n <=> power_free n /\
                               case aks_param n of
                                 nice j => j = n
                               | good k => unity_mod_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
                               | bad => F

   AKS Algorithm with simple bound:
   aks0_def        |- !n. aks0 n <=> power_free_test n /\
                                     case param n of
                                       nice j => j = n
                                     | good k => unity_mod_intro_range (ZN n) k n k
                                     | bad => F
   aks0_alt        |- !n. aks0 n <=> power_free n /\
                                     case aks_param n of
                                       nice j => j = n
                                     | good k => unity_mod_intro_range (ZN n) k n k
                                     | bad => F
*)

(* ------------------------------------------------------------------------- *)
(* Introspective Computations in a Ring                                      *)
(* ------------------------------------------------------------------------- *)

(* Define polynomial introspective check for (X + c), MOD (unity k) *)
val unity_mod_intro_def = Define`
    unity_mod_intro (r:'a ring) k n (c:num) <=>
      (unity_mod_exp r (unity_mod_monomial r k c) n = unity_mod_special r k n c)
`;

(*
> EVAL ``unity_mod_intro (ZN 5) 3 5 1``; --> T
> EVAL ``unity_mod_intro (ZN 5) 3 5 2``; --> T
> EVAL ``unity_mod_intro (ZN 5) 3 5 3``; --> T
> EVAL ``unity_mod_intro (ZN 5) 3 5 4``; --> T
> EVAL ``unity_mod_intro (ZN 5) 3 5 5``; --> T

> EVAL ``unity_mod_intro (ZN 4) 3 4 1``; --> F
> EVAL ``unity_mod_intro (ZN 4) 3 4 2``; --> F
> EVAL ``unity_mod_intro (ZN 4) 3 4 3``; --> F
> EVAL ``unity_mod_intro (ZN 4) 3 4 4``; --> T

> EVAL ``unity_mod_intro (ZN 97) 59 97 1``; --> T   after a long time!
> EVAL ``unity_mod_intro (ZN 91) 59 91 1``; --> F   very long time!
*)

(* Define polynomial introspective check for all c: 1 .. m, (X + c), MOD (unity k) *)
(*
val unity_mod_intro_range_def = Define`
    unity_mod_intro_range (r:'a ring) k n m <=>
      if m = 0 then T
      else (unity_mod_intro_range r k n (m - 1)) /\ (unity_mod_intro r k n m)
      (* stack recursion, checks from 1 up to c *)
`;
*)
(*
val unity_mod_intro_range_def = Define`
    unity_mod_intro_range (r:'a ring) k n m <=>
      if m = 0 then T
      else (unity_mod_intro r k n m) /\ (unity_mod_intro_range r k n (m - 1))
      (* tail recursion, but checks from c down to 1 *)
`;
*)
(*
val unity_mod_intro_range_def = Define`
    (unity_mod_intro_range (r:'a ring) k n 0 <=> T) /\
    (unity_mod_intro_range (r:'a ring) k n (SUC m) <=>
        (unity_mod_intro_range r k n m) /\ (unity_mod_intro r k n (SUC m)))
`;
*)
val unity_mod_intro_range_def = Define`
    (unity_mod_intro_range (r:'a ring) k n 0 <=> T) /\
    (unity_mod_intro_range (r:'a ring) k n (SUC m) <=>
        (unity_mod_intro r k n (SUC m)) /\ (unity_mod_intro_range r k n m))
`;

(*
> EVAL ``unity_mod_intro_range (ZN 7) 3 7 5``; --> T
> EVAL ``unity_mod_intro_range (ZN 10) 3 10 5``; --> F
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
            !c. unity_mod_intro r k n c = ((X + |c|) ** n == X ** n + |c|) (pm (unity k)) *)
(* Proof:
   Note 0 < k                                    by 1 < k
   Let q = unity_mod_monomial r k c.
   Then LENGTH q = k                             by unity_mod_monomial_length
     so LENGTH (unity_mod_exp r q n)
      = LENGTH q = k                             by unity_mod_exp_length, by 0 < n
   Also LENGTH (unity_mod_special r k n c) = k   by unity_mod_special_length
    Now weak q                                   by unity_mod_monomial_weak
     so poly (chop q)                            by poly_chop_weak_poly
   also poly (X + |c|)                           by poly_X_add_c

   Let z = unity k.
   Then ulead z                                 by poly_unity_ulead, 0 < k

   For LHS of unity_mod_intro_def,
       chop (unity_mod_exp r q n)
     = (q ** n) % z                              by unity_mod_exp_eqn
     = ((chop q) ** n) % z                       by poly_exp_weak, weak_exp_weak
     = (((X + |c|) % z) ** n) % z                by unity_mod_monomial_chop
     = ((X + |c|) ** n) % z                      by poly_mod_exp
   For RHS of unity_mod_intro_def,
       chop (unity_mod_special r k n c)
     = (X ** n + |c|) % z                        by unity_mod_special_chop

       unity_mod_intro r k n c
   <=>        unity_mod_exp r q n = unity_mod_special r k n c         by unity_mod_intro_def
   <=> chop (unity_mod_exp r q n) = chop (unity_mod_special r k n c)  by poly_chop_eq_chop
   <=>       ((X + |c|) ** n) % z = (X ** n + |c|) % z                by above
   <=> ((X + |c|) ** n == X ** n + |c|) (pm z)                        by pmod_def_alt
*)
val unity_mod_intro_alt = store_thm(
  "unity_mod_intro_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
   !c. unity_mod_intro r k n c = ((X + |c|) ** n == X ** n + |c|) (pm (unity k))``,
  rpt strip_tac >>
  `0 < k` by decide_tac >>
  qabbrev_tac `q = unity_mod_monomial r k c` >>
  `LENGTH q = k` by rw[unity_mod_monomial_length, Abbr`q`] >>
  `LENGTH (unity_mod_exp r q n) = k` by rw[unity_mod_exp_length] >>
  `LENGTH (unity_mod_special r k n c) = k` by rw[unity_mod_special_length] >>
  `weak q` by rw[unity_mod_monomial_weak, Abbr`q`] >>
  `poly (chop q)` by rw[poly_chop_weak_poly] >>
  `poly (X + |c|)` by rw[] >>
  qabbrev_tac `z = unity k` >>
  `ulead z` by rw[poly_unity_ulead, Abbr`z`] >>
  `chop (unity_mod_exp r q n) = (q ** n) % z` by rw[unity_mod_exp_eqn, Abbr`z`] >>
  `_ = ((chop q) ** n) % z` by rw_tac std_ss[poly_exp_weak, weak_exp_weak] >>
  `_ = (((X + |c|) % z) ** n) % z` by rw_tac std_ss[unity_mod_monomial_chop, Abbr`z`, Abbr`q`] >>
  `_ = ((X + |c|) ** n) % z` by rw_tac std_ss[poly_mod_exp] >>
  `chop (unity_mod_special r k n c) = (X ** n + |c|) % z` by rw_tac std_ss[unity_mod_special_chop, Abbr`z`] >>
  metis_tac[unity_mod_intro_def, poly_chop_eq_chop, pmod_def_alt]);

(* Got it! A nice result. *)

(* ------------------------------------------------------------------------- *)
(* Direct Computations using ZN Polynomials                                  *)
(* ------------------------------------------------------------------------- *)

(* Define polynomial introspective check for (X + c), MOD (n, unity k) *)
(*
val ZN_poly_intro_def = Define`
    ZN_poly_intro (n:num) (k:num) (c:num) <=>
      (ZN_poly_exp n k (ZN_poly_monomial n k c) m = ZN_poly_special n k n c)
`;
*)
val ZN_poly_intro_def = Define`
    ZN_poly_intro (n:num) (k:num) (c:num) <=>
      ((ZN_poly_monomial n k c) **z n = ZN_poly_special n k n c)
`;

(*
> EVAL ``ZN_poly_intro 5 3 1``; --> T
> EVAL ``ZN_poly_intro 5 3 2``; --> T
> EVAL ``ZN_poly_intro 5 3 3``; --> T
> EVAL ``ZN_poly_intro 5 3 4``; --> T
> EVAL ``ZN_poly_intro 5 3 5``; --> T

> EVAL ``ZN_poly_intro 4 3 1``; --> F
> EVAL ``ZN_poly_intro 4 3 2``; --> F
> EVAL ``ZN_poly_intro 4 3 3``; --> F
> EVAL ``ZN_poly_intro 4 3 4``; --> T

> EVAL ``ZN_poly_intro 97 59 1``; --> T   after a long time!
> EVAL ``ZN_poly_intro 91 59 1``; --> F   very long time!
*)

(*
> time EVAL ``ZN_poly_intro 97 59 1``;
runtime: 10.2s,    gctime: 0.02760s,     systime: 0.16561s.
val it = |- ZN_poly_intro 97 59 1 <=> T: thm
> time EVAL ``ZN_poly_intro 91 59 1``;
runtime: 11.0s,    gctime: 0.02112s,     systime: 0.14379s.
val it = |- ZN_poly_intro 91 59 1 <=> F: thm

> time EVAL ``unity_mod_intro (ZN 97) 59 97 1``;
runtime: 12.5s,    gctime: 0.03019s,     systime: 0.17102s.
val it = |- unity_mod_intro (ZN 97) 59 97 1 <=> T: thm
> time EVAL ``unity_mod_intro (ZN 91) 59 91 1``;
runtime: 13.4s,    gctime: 0.02450s,     systime: 0.19787s.
val it = |- unity_mod_intro (ZN 91) 59 91 1 <=> F: thm

*)

(* Define polynomial introspective check for a range of constants c *)
val ZN_poly_intro_range_def = Define`
    (ZN_poly_intro_range (n:num) (k:num) 0 <=> T) /\
    (ZN_poly_intro_range (n:num) (k:num) (SUC m) <=>
     ZN_poly_intro n k (SUC m) /\ ZN_poly_intro_range n k m)
`;

(*
> EVAL ``ZN_poly_intro_range 5 3 4``;
val it = |- ZN_poly_intro_range 5 3 4 <=> T: thm
> EVAL ``ZN_poly_intro_range 4 3 4``;
val it = |- ZN_poly_intro_range 4 3 4 <=> F: thm
*)

(* Theorem: 1 < n /\ 0 < k ==> !c. ZN_poly_intro n k c = unity_mod_intro (ZN n) k n c *)
(* Proof:
   Note Ring (ZN n)                     by ZN_ring, 0 < n
   Let p = unity_mod_monomial (ZN n) k c.
   Then zweak p                         by unity_mod_monomial_weak
    and LENGTH p = k                    by unity_mod_monomial_length
    ==> p <> []                         by LENGTH_NIL, 0 < k

   Note ZN_poly_monomial n k c **z n
      = p **z n                         by ZN_poly_monomial_alt
      = unity_mod_exp (ZN n) p n        by ZN_poly_exp_alt, LENGTH p = k
    and ZN_poly_special n k n c
      = unity_mod_special (ZN n) k n c  by ZN_poly_special_alt

       ZN_poly_intro n k c
   <=> ZN_poly_monomial n k c **z n = ZN_poly_special n k n c    by ZN_poly_intro_def
   <=> unity_mod_exp p n = unity_mod_special (ZN n) k n c        by above
   <=> unity_mod_intro (ZN n) k n c                              by unity_mod_intro_def
*)
val ZN_poly_intro_alt = store_thm(
  "ZN_poly_intro_alt",
  ``!n k. 1 < n /\ 0 < k ==> !c. ZN_poly_intro n k c = unity_mod_intro (ZN n) k n c``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  qabbrev_tac `p = unity_mod_monomial (ZN n) k c` >>
  `zweak p` by rw[unity_mod_monomial_weak, Abbr`p`] >>
  `LENGTH p = k` by rw[unity_mod_monomial_length, Abbr`p`] >>
  `p <> []` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  metis_tac[ZN_poly_monomial_alt, ZN_poly_exp_alt, ZN_poly_special_alt, ZN_poly_intro_def, unity_mod_intro_def]);

(* Theorem: 1 < n /\ 0 < k ==> !m. ZN_poly_intro_range n k m = unity_mod_intro_range (ZN n) k n m *)
(* Proof:
   By induction on m.
   Base: ZN_poly_intro_range n k 0 <=> unity_mod_intro_range (ZN n) k n 0
      Note ZN_poly_intro_range n k 0 = T            by ZN_poly_intro_range_def
       and unity_mod_intro_range (ZN n) k n 0 = T   by unity_mod_intro_range_def
   Step: ZN_poly_intro_range n k m <=> unity_mod_intro_range (ZN n) k n m ==>
         ZN_poly_intro_range n k (SUC m) <=> unity_mod_intro_range (ZN n) k n (SUC m)

          ZN_poly_intro_range n k (SUC m)
      <=> ZN_poly_intro n k (SUC m) /\
             ZN_poly_intro_range n k m            by ZN_poly_intro_range_def
      <=> ZN_poly_intro n k (SUC m) /\
             unity_mod_intro_range (ZN n) k n m   by induction hypothesis
      <=> unity_mod_intro (ZN n) k n (SUC m) /\
             unity_mod_intro_range (ZN n) k n m   by ZN_poly_intro_alt, 1 < n, 0 < k
      <=> unity_mod_intro_range (ZN n) k n m      by unity_mod_intro_range_def
*)
val ZN_poly_intro_range_alt = store_thm(
  "ZN_poly_intro_range_alt",
  ``!n k. 1 < n /\ 0 < k ==> !m. ZN_poly_intro_range n k m = unity_mod_intro_range (ZN n) k n m``,
  ntac 3 strip_tac >>
  Induct >>
  rw[ZN_poly_intro_range_def, unity_mod_intro_range_def, ZN_poly_intro_alt]);

(* Theorem: ZN_poly_intro_range n k m = (!c. 0 < c /\ c <= m ==> ZN_poly_intro n k c) *)
(* Proof:
   By induction on m.
   Base: ZN_poly_intro_range n k 0 <=> !c. 0 < c /\ c <= 0 ==> ZN_poly_intro n k c
         LHS = ZN_poly_intro_range n k 0 = T     by ZN_poly_intro_range_def
         RHS = T, since no c for 0 < c <= 0.
   Step: ZN_poly_intro_range n k m <=> !c. 0 < c /\ c <= m ==> ZN_poly_intro n k c ==>
         ZN_poly_intro_range n k (SUC m) <=> !c. 0 < c /\ c <= SUC m ==> ZN_poly_intro n k c
         If ZN_poly_intro_range n k (SUC m),
            Then ZN_poly_intro n k (SUC m) /\
                     ZN_poly_intro_range n k m                     by ZN_poly_intro_range_def
              or ZN_poly_intro n k (SUC m) /\
                 !c. 0 < c /\ c <= m ==> ZN_poly_intro n k c       by induction hypothesis
              or !c. 0 < c /\ c <= SUC m ==> ZN_poly_intro n k c   by combining indexes
         If !c. 0 < c /\ c <= SUC m ==> ZN_poly_intro n k c,
            Then !c. 0 < c /\ c <= n ==> ZN_poly_intro n k c,
                     and (c = SUC m) ==> ZN_poly_intro n k c       by separating indexes
              or ZN_poly_intro_range n k m,
                     and (c = SUC m) ==> ZN_poly_intro n k c       by induction hypothesis
              or ZN_poly_intro_range n k m,
                     and ZN_poly_intro n k (SUC m)                 by substitution
              or ZN_poly_intro_range n k (SUC m)                   by ZN_poly_intro_range_def
*)
val ZN_poly_intro_range_thm = store_thm(
  "ZN_poly_intro_range_thm",
  ``!n k m. ZN_poly_intro_range n k m = (!c. 0 < c /\ c <= m ==> ZN_poly_intro n k c)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[ZN_poly_intro_range_def] >>
  rw[ZN_poly_intro_range_def, EQ_IMP_THM] >>
  Cases_on `c = SUC m` >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* AKS Algorithm -- original                                                 *)
(* ------------------------------------------------------------------------- *)

(* Express AKS algorithm in terms of possible results of AKS parameter. *)
val aks_compute_def = Define`
    aks_compute n <=> power_free_check n /\
       case aks_param n of     (* search for AKS parameter given n *)
         nice j => (j = n)     (* found j that will show n prime or composite directly *)
       | good k => unity_mod_intro_range (ZN n) k n ((sqrt_compute (phi_compute k)) * (ulog n))
                               (* found k with m <= ordz k n, where m = (ulog n) ** 2 *)
         (* !c. 0 < c /\ c <= SQRT (phi k) * (ulog n) ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
       | bad => F              (* impossible *)
`;
(* Note: power_free_check is computable. *)

(*
> EVAL ``aks_compute 2``; --> T
> EVAL ``aks_compute 3``; --> T
> EVAL ``aks_compute 4``; --> F
> EVAL ``aks_compute 5``; --> T
> EVAL ``aks_compute 6``; --> F
> EVAL ``aks_compute 7``; --> T
> EVAL ``aks_compute 8``; --> F
> EVAL ``aks_compute 9``; --> F
> EVAL ``aks_compute 10``; --> F
> EVAL ``aks_compute 11``; --> T
> EVAL ``aks_compute 12``; --> F
> EVAL ``aks_compute 13``; --> T
> EVAL ``aks_compute 31``; --> T (a long time)
> time EVAL ``aks_compute 31``;
runtime: 46.4s,    gctime: 0.08857s,     systime: 0.55679s.
val it = |- aks_compute 31 <=> T: thm
*)

(* Note: the following is a weak version.
The strong version is:
g `!n. aks_compute n = power_free n /\
       case aks_param n of
         nice j => (j = n)
       | good k => (n intro (X + |c|) in MOD (ZN n, (unity k)) for c = 1 to (SQRT (phi k)) * (ulog n)
       | bad => F`;
-- the strong version is: aks_compute_alt, see AKSclean,
*)

(* Theorem: aks_compute n <=> power_free n /\
            case aks_param n of
              nice j => (j = n)
            | good k => unity_mod_intro_range (ZN n) k n ((SQRT (phi k)) * ((LOG2 n) + 1))
            | bad => F *)
(* Proof: by aks_compute_def, power_free_check_eqn, sqrt_compute_eqn, phi_compute_eqn *)
val aks_compute_alt_weak = store_thm(
  "aks_compute_alt_weak",
  ``!n. aks_compute n <=> power_free n /\
       case aks_param n of
         nice j => (j = n)
       | good k => unity_mod_intro_range (ZN n) k n ((SQRT (phi k)) * (ulog n))
       | bad => F``,
  rw[aks_compute_def, power_free_check_eqn, sqrt_compute_eqn, phi_compute_eqn]);

(* ------------------------------------------------------------------------- *)
(* AKS Algorithm with simple bound                                           *)
(* ------------------------------------------------------------------------- *)

(* Express AKS algorithm in terms of possible results of AKS parameter. *)
val aks0_def = Define`
    aks0 n <=> power_free_test n /\
       case param n of         (* search for AKS parameter given n *)
         nice j => (j = n)     (* found j that will show n prime or composite directly *)
       | good k => unity_mod_intro_range (ZN n) k n k (* upper limit just use k *)
                               (* found k with m <= ordz k n, where m = (ulog n) ** 2 *)
          (* !c. 0 < c /\ c <= k ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
       | bad => F              (* impossible *)
`;
(* Note: power_free_test is not computable. *)

(* Theorem: aks0 n <=>
          power_free n /\
          case aks_param n of
            nice j => j = n
          | good k => unity_mod_intro_range (ZN n) k n k
          | bad => F *)
(* Proof: by aks0_def, param_eqn, power_free_test_eqn *)
val aks0_alt = store_thm(
  "aks0_alt",
  ``!n. aks0 n <=>
          power_free n /\
          case aks_param n of
            nice j => j = n
          | good k => unity_mod_intro_range (ZN n) k n k
          | bad => F``,
  rw[aks0_def, param_eqn, power_free_test_eqn]);

(* Correctness is proved in AKSclean:
   aks0_thm   |- !n. prime n <=> aks0 n
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
