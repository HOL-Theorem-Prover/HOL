(* ------------------------------------------------------------------------- *)
(* AKS Machine                                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSmachine";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "AKSimprovedTheory"; *)
open AKSimprovedTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperListTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

open logPowerTheory;
open computeAKSTheory;
open computeBasicTheory;
open computeOrderTheory;
open computePolyTheory;
open computeRingTheory;


(* ------------------------------------------------------------------------- *)
(* AKS Machine Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:

*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Fast Multiplication:
   mult_step_def    |- !r n m. mult_step m n r = if n = 0 then r
                               else mult_step (TWICE m) (HALF n) (if EVEN n then r else r + m)
   mult_fast_def    |- !m n. mult_fast m n = mult_step m n 0
   mult_step_0      |- !m r. mult_step m 0 r = r
   mult_step_1      |- !m r. mult_step m 1 r = r + m
   mult_step_2      |- !m r. mult_step m 2 r = r + TWICE m
   mult_step_even   |- !n. EVEN n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) r
   mult_step_odd    |- !n. ODD n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) (r + m)
   mult_step_eqn    |- !m n r. mult_step m n r = r + m * n
   mult_fast_0      |- !m. mult_fast m 0 = 0
   mult_fast_1      |- !m. mult_fast m 1 = m
   mult_fast_2      |- !m. mult_fast m 2 = TWICE m
   mult_fast_even   |- !n. EVEN n ==> !m. mult_fast m n = mult_fast (TWICE m) (HALF n)
   mult_fast_eqn    |- !m n. mult_fast m n = m * n

   Fast Modulo Multiplication:
   mult_mod_step_def   |- !r n m k. mult_mod_step m n k r = if k = 0 then (m * n) MOD 0
                                    else if n = 0 then r MOD k
                          else mult_mod_step (TWICE m MOD k) (HALF n) k (if EVEN n then r else (r + m) MOD k)
   mult_mod_fast_def   |- !m n k. mult_mod_fast m n k = mult_mod_step m n k 0
   mult_mod_step_0     |- !k. 0 < k ==> !m r. mult_mod_step m 0 k r = r MOD k
   mult_mod_step_1     |- !k. 0 < k ==> !m r. mult_mod_step m 1 k r = (r + m) MOD k
   mult_mod_step_2     |- !k. 0 < k ==> !m r. mult_mod_step m 2 k r = (r + TWICE m) MOD k
   mult_mod_step_even  |- !k. 0 < k ==> !n. EVEN n ==>
                          !m r. mult_mod_step m n k r = mult_mod_step (TWICE m MOD k) (HALF n) k r
   mult_mod_step_odd   |- !k. 0 < k ==> !n. ODD n ==>
                          !m r. mult_mod_step m n k r = mult_mod_step (TWICE m MOD k) (HALF n) k ((r + m) MOD k)
   mult_mod_step_eqn   |- !k. 0 < k ==> !m n r. mult_mod_step m n k r = (r + m * n) MOD k
   mult_mod_fast_0     |- !k. 0 < k ==> !m. mult_mod_fast m 0 k = 0
   mult_mod_fast_1     |- !k. 0 < k ==> !m. mult_mod_fast m 1 k = m MOD k
   mult_mod_fast_2     |- !k. 0 < k ==> !m. mult_mod_fast m 2 k = TWICE m MOD k
   mult_mod_fast_even  |- !k. 0 < k ==> !n. EVEN n ==>
                          !m. mult_mod_fast m n k = mult_mod_fast (TWICE m MOD k) (HALF n) k
   mult_mod_fast_eqn   |- !k. 0 < k ==> !m n. mult_mod_fast m n k = (m * n) MOD k

   Fast Polynomial Exponentiation:
   unity_mod_exp_step_def    |- !r q p n. unity_mod_exp_step r p n q = if n = 0 then q
         else unity_mod_exp_step r (unity_mod_sq r p) (HALF n) (if EVEN n then q else unity_mod_mult r p q)
   unity_mod_exp_fast_def    |- !r p n. unity_mod_exp_fast r p n = unity_mod_exp_step r p n |1|
   unity_mod_exp_step_0      |- !r p q. unity_mod_exp_step r p 0 q = q
   unity_mod_exp_step_1      |- !r p q. unity_mod_exp_step r p 1 q = unity_mod_mult r p q
   unity_mod_exp_step_2      |- !r p q. unity_mod_exp_step r p 2 q = unity_mod_mult r (unity_mod_sq r p) q
   unity_mod_exp_step_even   |- !r n. EVEN n ==>
         !p q. unity_mod_exp_step r p n q = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) q
   unity_mod_exp_step_odd    |- !r n. ODD n ==>
         !p q. unity_mod_exp_step r p n q = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) (unity_mod_mult r p q)
   unity_mod_exp_fast_0      |- !r p. unity_mod_exp_fast r p 0 = |1|
   unity_mod_exp_fast_1      |- !r. #1 <> #0 ==> !p. unity_mod_exp_fast r p 1 = #1 o p
   unity_mod_exp_fast_2      |- !r. #1 <> #0 ==> !p. unity_mod_exp_fast r p 2 = #1 o unity_mod_sq r p
   unity_mod_exp_fast_even   |- !r n. EVEN n ==>
                                !p. unity_mod_exp_fast r p n = unity_mod_exp_fast r (unity_mod_sq r p) (HALF n)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Fast Multiplication (Egyptian or Russian Peasant Method)                  *)
(* ------------------------------------------------------------------------- *)

(* Fast Multiplication -- iterative form *)
(* Pseudo-Code:
   m * n = r <- 0
           loop:
           if (n == 0) return r
           if (ODD n) r <- r + m
           n <- HALF n
           m <- TWICE m
           goto loop
*)

(* Define fast multiplication *)
val mult_step_def = Define`
    mult_step m n r = (* r = m * n *)
       if n = 0 then r else
       mult_step (TWICE m) (HALF n) (if EVEN n then r else (r + m))
`;
val mult_fast_def = Define`
    mult_fast m n = mult_step m n 0
`;

(*
EVAL ``mult_fast 2 10``; --> 20
EVAL ``mult_fast 3 10``; --> 30
EVAL ``mult_fast 3 8 = 3 * 8``; --> T
*)

(* Theorem: mult_step m 0 r = r *)
(* Proof: by mult_step_def *)
val mult_step_0 = store_thm(
  "mult_step_0",
  ``!m r. mult_step m 0 r = r``,
  rw[Once mult_step_def]);

(* Theorem: mult_step m 1 r = r + m *)
(* Proof: by mult_step_def *)
val mult_step_1 = store_thm(
  "mult_step_1",
  ``!m r. mult_step m 1 r = r + m``,
  rw[Once mult_step_def, Once mult_step_def]);

(* Theorem: mult_step m 2 r = r + TWICE m *)
(* Proof:
     mult_step m 2 r
   = mult_step (TWICE m) (HALF 2) r     by mult_step_def, EVEN 2
   = mult_step (TWICE m) 1 r            by arithmetic
   = r + TWICE m                        by mult_step_1
*)
val mult_step_2 = store_thm(
  "mult_step_2",
  ``!m r. mult_step m 2 r = r + TWICE m``,
  rw[Once mult_step_def, Once mult_step_def, Once mult_step_def]);

(* Theorem: EVEN n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) r *)
(* Proof:
   If n = 0, HALF 0 = 0      by HALF_EQ_0
      Thus LHS = r = RHS     by mult_step_def
   If n <> 0, true           by mult_step_def
*)
val mult_step_even = store_thm(
  "mult_step_even",
  ``!n. EVEN n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) r``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[mult_step_def, HALF_EQ_0] >>
  rw[Once mult_step_def]);

(* Theorem: ODD n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) (r + m) *)
(* Proof:
   Note ODD n ==> ~EVEN n     by ODD_EVEN
               and n <> 0     by EVEN
   The result follows         by mult_step_def
*)
val mult_step_odd = store_thm(
  "mult_step_odd",
  ``!n. ODD n ==> !m r. mult_step m n r = mult_step (TWICE m) (HALF n) (r + m)``,
  rpt strip_tac >>
  `~EVEN n /\ n <> 0` by metis_tac[ODD_EVEN, EVEN] >>
  rw[Once mult_step_def]);

(* Theorem: mult_step m n r = r + m * n *)
(* Proof:
   By complete induction on n.
   If n = 0,
        mult_step m 0 r
      = r                                     by mult_step_0
      = r + 0                                 by ADD_0
      = r + m * 0                             by MULT_0
   If n <> 0,
      then HALF n < n                         by HALF_LESS, 0 < n
   If EVEN n,
        mult_step m n r
      = mult_step (TWICE m) (HALF n) r        by mult_step_even
      = r + (TWICE m) * (HALF n)              by induction hypothesis, HALF n < n
      = r + m * n                             by MULT_EVEN
   If ~EVEN n,
      then ODD n                              by EVEN_ODD
        mult_step m n r
      = mult_step (TWICE m) (HALF n) (r + m)  by mult_step_odd
      = (r + m) + (TWICE m) * (HALF n)        by induction hypothesis, HALF n < n
      = r + (m + (TWICE m) * (HALF n))        by ADD_ASSOC
      = r + m * n                             by MULT_ODD
*)
val mult_step_eqn = store_thm(
  "mult_step_eqn",
  ``!m n r. mult_step m n r = r + m * n``,
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[mult_step_0] >>
  `HALF n < n` by rw[] >>
  Cases_on `EVEN n` >-
  rw[mult_step_even, MULT_EVEN] >>
  metis_tac[ODD_EVEN, mult_step_odd, ADD_ASSOC, MULT_ODD]);

(* Theorem: mult_fast m 0 = 0 *)
(* Proof: by mult_fast_def, mult_step_0 *)
val mult_fast_0 = store_thm(
  "mult_fast_0",
  ``!m. mult_fast m 0 = 0``,
  rw[mult_fast_def, mult_step_0]);

(* Theorem: mult_fast m 1 = m *)
(* Proof: by mult_fast_def, mult_step_1 *)
val mult_fast_1 = store_thm(
  "mult_fast_1",
  ``!m. mult_fast m 1 = m``,
  rw[mult_fast_def, mult_step_1]);

(* Theorem: mult_fast m 2 = TWICE m *)
(* Proof: by mult_fast_def, mult_step_2 *)
val mult_fast_2 = store_thm(
  "mult_fast_2",
  ``!m. mult_fast m 2 = TWICE m``,
  rw[mult_fast_def, mult_step_2]);

(* Theorem: EVEN n ==> !m. mult_fast m n = mult_fast (TWICE m) (HALF n) *)
(* Proof:
     mult_fast m n
   = mult_step m n 0                  by mult_fast_def
   = mult_step (TWICE m) (HALF n) 0   by mult_step_even, EVEN n
   = mult_fast (TWICE m) (HALF n)     by mult_fast_def
*)
val mult_fast_even = store_thm(
  "mult_fast_even",
  ``!n. EVEN n ==> !m. mult_fast m n = mult_fast (TWICE m) (HALF n)``,
  rw[mult_fast_def, mult_step_even]);

(* Theorem: mult_fast m n = m * n *)
(* Proof:
     mult_fast m n
   = mult_step m n 0    by mult_fast_def
   = 0 + m * n          by mult_step_eqn
   = m * n              by ADD
*)
val mult_fast_eqn = store_thm(
  "mult_fast_eqn",
  ``!m n. mult_fast m n = m * n``,
  rw[mult_fast_def, mult_step_eqn]);

(* ------------------------------------------------------------------------- *)
(* Fast Modulo Multiplication.                                               *)
(* ------------------------------------------------------------------------- *)

(* Fast Modulo Multiplication -- iterative form *)
(* Pseudo-Code:
   (m * n) MOD k = r <- 0
                   loop:
                   if (n == 0) return (r MOD k)
                   if (ODD n) r <- (r + m) MOD k
                   n <- HALF n
                   m <- (TWICE m) MOD k
                   goto loop
*)

(* Define fast modulo multiplication *)
val mult_mod_step_def = Define`
    mult_mod_step m n k r =
       if k = 0 then (m * n) MOD 0
       else if n = 0 then (r MOD k) else
       mult_mod_step ((TWICE m) MOD k) (HALF n) k (if EVEN n then r else ((r + m) MOD k))
`;
val mult_mod_fast_def = Define`
    mult_mod_fast m n k = mult_mod_step m n k 0
`;

(*
EVAL ``mult_mod_fast 2 10 3``; --> 20 MOD 3 = 2
EVAL ``mult_mod_fast 3 10 11``; --> 30 MOD 11 = 8
EVAL ``mult_mod_fast 3 8 5 = (3 * 8) MOD 5``; --> T
*)

(* Theorem: 0 < k ==> !m r. mult_mod_step m 0 k r = r MOD k *)
(* Proof: by mult_mod_step_def *)
val mult_mod_step_0 = store_thm(
  "mult_mod_step_0",
  ``!k. 0 < k ==> !m r. mult_mod_step m 0 k r = r MOD k``,
  rw[Once mult_mod_step_def]);

(* Theorem: 0 < k ==> !m r. mult_mod_step m 1 k r = (r + m) MOD k *)
(* Proof: by mult_mod_step_def *)
val mult_mod_step_1 = store_thm(
  "mult_mod_step_1",
  ``!k. 0 < k ==> !m r. mult_mod_step m 1 k r = (r + m) MOD k``,
  rw[Once mult_mod_step_def, Once mult_mod_step_def]);

(* Theorem: 0 < k ==> !m r. mult_mod_step m 2 k r = (r + TWICE m) MOD k *)
(* Proof:
     mult_mod_step m 2 k r
   = mult_mod_step (TWICE m) (HALF 2) k r  by mult_mod_step_def, EVEN 2
   = mult_mod_step (TWICE m) 1 k r         by arithmetic
   = (r + TWICE m) MOD k                   by mult_mod_step_1, 0 < k
*)
val mult_mod_step_2 = store_thm(
  "mult_mod_step_2",
  ``!k. 0 < k ==> !m r. mult_mod_step m 2 k r = (r + TWICE m) MOD k``,
  rw[Once mult_mod_step_def, Once mult_mod_step_def, Once mult_mod_step_def]);

(* Theorem: 0 < k ==> !n. EVEN n ==>
            !m r. mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k r *)
(* Proof:
   if n = 0, HALF 0 = 0            by HALF_EQ_0
      Thus LHS = r MOD k = RHS     by mult_mod_step_def
   If n <> 0, true                 by mult_mod_step_def
*)
val mult_mod_step_even = store_thm(
  "mult_mod_step_even",
  ``!k. 0 < k ==> !n. EVEN n ==>
   !m r. mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k r``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[mult_mod_step_def, HALF_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw[Once mult_mod_step_def]);

(* Theorem: 0 < k ==> !n. ODD n ==>
            !m r. mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k ((r + m) MOD k) *)
(* Proof:
   Note ODD n ==> ~EVEN n     by ODD_EVEN
               and m <> 0     by EVEN
   The result follows         by mult_mod_step_def
*)
val mult_mod_step_odd = store_thm(
  "mult_mod_step_odd",
  ``!k. 0 < k ==> !n. ODD n ==>
   !m r. mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k ((r + m) MOD k)``,
  rpt strip_tac >>
  `~EVEN n /\ n <> 0` by metis_tac[ODD_EVEN, EVEN] >>
  rw[Once mult_mod_step_def]);

(* Theorem: 0 < k ==> !m n r. mult_mod_step m n k r = (r + m * n) MOD k *)
(* Proof:
   By complete induction on n.
   if n = 0,
        mult_mod_step m 0 k r
      = r MOD k                               by mult_mod_step_0
      = (r + 0) MOD k                         by ADD_0
      = (r + m * 0) MOD k                     by MULT_0
   If n <> 0,
      then HALF n < n                         by HALF_LESS, 0 < n
   If EVEN n,
        mult_mod_step m n k r
      = mult_mod_step ((TWICE m) MOD k) (HALF n) r    by mult_mod_step_even
      = (r + ((TWICE m) MOD k) * (HALF n)) MOD k      by induction hypothesis, HALF n < n
      = (r + (TWICE m) * (HALF n)) MOD k              by MOD_PLUS, MOD_TIMES2, MOD_MOD, 0 < k
      = (r + m * n) MOD k                             by MULT_EVEN
   If ~EVEN n,
      then ODD n                                      by EVEN_ODD
        mult_mod_step m n k r
      = mult_mod_step ((TWICE m) MOD k) (HALF n) k ((r + m) MOD k)  by mult_mod_step_odd
      = ((r + m) + ((TWICE m) MOD k) * (HALF n)) MOD k              by induction hypothesis, HALF n < n
      = ((r + m) + (TWICE m) * (HALF n)) MOD k        by MOD_PLUS, MOD_TIMES2, MOD_MOD, 0 < k
      = (r + (m + (TWICE m) * (HALF n))) MOD k        by ADD_ASSOC
      = (r + m * n) MOD k                             by MULT_ODD
*)
val mult_mod_step_eqn = store_thm(
  "mult_mod_step_eqn",
  ``!k. 0 < k ==> !m n r. mult_mod_step m n k r = (r + m * n) MOD k``,
  ntac 2 strip_tac >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[mult_mod_step_0] >>
  `HALF n < n` by rw[] >>
  Cases_on `EVEN n` >| [
    `mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k r` by rw[mult_mod_step_even] >>
    `_ = (r + ((TWICE m) MOD k) * (HALF n)) MOD k` by rw[] >>
    `_ = (r + (TWICE m) * (HALF n)) MOD k` by rw[] >>
    `_ = (r + m * n) MOD k` by rw[GSYM MULT_EVEN] >>
    rw[],
    `ODD n` by rw[ODD_EVEN] >>
    `mult_mod_step m n k r = mult_mod_step ((TWICE m) MOD k) (HALF n) k ((r + m) MOD k)` by rw[mult_mod_step_odd] >>
    `_ = ((r + m) + ((TWICE m) MOD k) * (HALF n)) MOD k` by rw[] >>
    `_ = ((r + m) + (TWICE m) * (HALF n)) MOD k` by rw[] >>
    `_ = (r + (m + (TWICE m) * (HALF n))) MOD k` by rw[] >>
    `_ = (r + m * n) MOD k` by rw[GSYM MULT_ODD] >>
    rw[]
  ]);

(* Theorem: 0 < k ==> !m. mult_mod_fast m 0 k = 0 *)
(* Proof:
     mult_mod_fast m 0 k
   = mult_mod_step m 0 k 0     by mult_mod_fast_def
   = 0 MOD k                   by mult_mod_step_0, 0 < k
   = 0                         by ZERO_MOD, 0 < k
*)
val mult_mod_fast_0 = store_thm(
  "mult_mod_fast_0",
  ``!k. 0 < k ==> !m. mult_mod_fast m 0 k = 0``,
  rw[mult_mod_fast_def, mult_mod_step_0]);

(* Theorem: 0 < k ==> !m. mult_mod_fast m 1 k = m MOD k *)
(* Proof:
     mult_mod_fast m 1 k
   = mult_mod_step m 1 k 0     by mult_mod_fast_def
   = (0 + m) MOD k             by mult_mod_step_1, 0 < k
   = m MOD k                   by ADD
*)
val mult_mod_fast_1 = store_thm(
  "mult_mod_fast_1",
  ``!k. 0 < k ==> !m. mult_mod_fast m 1 k = m MOD k``,
  rw[mult_mod_fast_def, mult_mod_step_1]);

(* Theorem: 0 < k ==> !m. mult_mod_fast m 2 k = (TWICE m) MOD k *)
(* Proof:
     mult_mod_fast m 2 k
   = mult_mod_step m 2 k 0     by mult_mod_fast_def
   = (0 + TWICE m) MOD k       by mult_mod_step_2, 0 < k
   = (TWICE m) MOD k           by ADD
*)
val mult_mod_fast_2 = store_thm(
  "mult_mod_fast_2",
  ``!k. 0 < k ==> !m. mult_mod_fast m 2 k = (TWICE m) MOD k``,
  rw[mult_mod_fast_def, mult_mod_step_2]);

(* Theorem: 0 < k ==> !n. EVEN n ==>
            !n. mult_mod_fast m n k = mult_mod_fast ((TWICE m) MOD k) (HALF n) k *)
(* Proof:
     mult_mod_fast m n k
   = mult_mod_step m n k 0                          by mult_mod_fast_def
   = mult_mod_step ((TWICE m) MOD k) (HALF n) k 0   by mult_mod_step_even, EVEN n
   = mult_mod_fast ((TWICE m) MOD k) (HALF n) k     by mult_mod_fast_def
*)
val mult_mod_fast_even = store_thm(
  "mult_mod_fast_even",
  ``!k. 0 < k ==> !n. EVEN n ==>
   !m. mult_mod_fast m n k = mult_mod_fast ((TWICE m) MOD k) (HALF n) k``,
  rw[mult_mod_fast_def, mult_mod_step_even]);

(* Theorem: 0 < k ==> !m n. mult_mod_fast m n k = (m * n) MOD k *)
(* Proof:
     mult_mod_fast m n k
   = mult_mod_step m n k 0      by mult_mod_fast_def
   = (0 + m * n) MOD k          by mult_mod_step_eqn
   = (m * n) MOD k              by ADD
*)
val mult_mod_fast_eqn = store_thm(
  "mult_mod_fast_eqn",
  ``!k. 0 < k ==> !m n. mult_mod_fast m n k = (m * n) MOD k``,
  rw[mult_mod_fast_def, mult_mod_step_eqn]);

(* ------------------------------------------------------------------------- *)
(* Fast Polynomial Scalar Multiplication                                     *)
(* ------------------------------------------------------------------------- *)

(* Is this faster than direct MAP scalar multiply? *)

(* ------------------------------------------------------------------------- *)
(* Fast Polynomial Exponentiation                                            *)
(* ------------------------------------------------------------------------- *)

(* Fast Polynomial Exponentiation -- iterative form *)
(* Pseudo-Code:
   (p ** n) MOD z = q <- |1|
                    loop:
                    if (n == 0) return (q % z)
                    if (ODD n) r <- (q * p) % z
                    n <- HALF n
                    p <- (SQ p) % z
                    goto loop
*)

(* Define fast modulo exponentiation *)
val unity_mod_exp_step_def = Define`
    unity_mod_exp_step (r:'a ring) (p:'a poly) n (q:'a poly) =
       if n = 0 then q else
       unity_mod_exp_step r (unity_mod_sq r p) (HALF n) (if EVEN n then q else (unity_mod_mult r p q))
`;
val unity_mod_exp_fast_def = Define`
    unity_mod_exp_fast (r:'a ring) (p:'a poly) n = unity_mod_exp_step r p n |1|
`;

(*
EVAL ``unity_mod_exp_fast (ZN 7) [1;0;0;1] 3``; --> [1;1;3;3]
EVAL ``unity_mod_exp (ZN 7) [1;0;0;1] 3``; --> [1;1;3;3]

EVAL ``unity_mod_exp_fast (ZN 7) [1;1;0;0;0] 7``; --> [1; 0; 1; 0; 0]
EVAL ``unity_mod_exp (ZN 7) [1;1;0;0;0] 7``; --> [1; 0; 1; 0; 0]
*)

(* Theorem: unity_mod_exp_step r p 0 q = q *)
(* Proof: by unity_mod_exp_step_def *)
val unity_mod_exp_step_0 = store_thm(
  "unity_mod_exp_step_0",
  ``!r:'a ring. !p q. unity_mod_exp_step r p 0 q = q``,
  rw[Once unity_mod_exp_step_def]);

(* Theorem: unity_mod_exp_step r p 1 q = unity_mod_mult r p q *)
(* Proof: by unity_mod_exp_step_def *)
val unity_mod_exp_step_1 = store_thm(
  "unity_mod_exp_step_1",
  ``!r:'a ring. !p q. unity_mod_exp_step r p 1 q = unity_mod_mult r p q``,
  rw[Once unity_mod_exp_step_def, Once unity_mod_exp_step_def]);

(* Theorem: unity_mod_exp_step r p 2 q = unity_mod_mult r (unity_mod_sq r p) q *)
(* Proof:
     unity_mod_exp_step r p 2 q
   = unity_mod_exp_step r (unity_mod_sq r p) (HALF 2) q   by unity_mod_exp_step_def, EVEN 2
   = unity_mod_exp_step r (unity_mod_sq r p) 1 q          by arithmetic
   = unity_mod_mult r (unity_mod_sq r p) q                by unity_mod_exp_step_1
*)
val unity_mod_exp_step_2 = store_thm(
  "unity_mod_exp_step_2",
  ``!r:'a ring. !p q. unity_mod_exp_step r p 2 q = unity_mod_mult r (unity_mod_sq r p) q``,
  rw[Once unity_mod_exp_step_def, Once unity_mod_exp_step_def, Once unity_mod_exp_step_def]);

(* Theorem: EVEN n ==> !p q. unity_mod_exp_step r p n q = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) q *)
(* Proof:
   If n = 0, HALF 0 = 0      by HALF_EQ_0
      Thus LHS = q = RHS     by unity_mod_exp_step_def
   If n <> 0, true           by unity_mod_exp_step_def
*)
val unity_mod_exp_step_even = store_thm(
  "unity_mod_exp_step_even",
  ``!r:'a ring. !n. EVEN n ==>
   !p q. unity_mod_exp_step r p n q = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) q``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[unity_mod_exp_step_def, HALF_EQ_0] >>
  rw[Once unity_mod_exp_step_def]);

(* Theorem: ODD n ==> !p q. unity_mod_exp_step r p n q =
                      unity_mod_exp_step r (unity_mod_sq r p) (HALF n) (unity_mod_mult r p q) *)
(* Proof:
   Note ODD n ==> ~EVEN n     by ODD_EVEN
               and m <> 0     by EVEN
   The result follows         by unity_mod_exp_step_def
*)
val unity_mod_exp_step_odd = store_thm(
  "unity_mod_exp_step_odd",
  ``!r:'a ring. !n. ODD n ==>
   !p q. unity_mod_exp_step r p n q = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) (unity_mod_mult r p q)``,
  rpt strip_tac >>
  `~EVEN n /\ n <> 0` by metis_tac[ODD_EVEN, EVEN] >>
  rw[Once unity_mod_exp_step_def]);


(* Theorem: unity_mod_exp_fast r p 0 = |1| *)
(* Proof: by unity_mod_exp_fast_def, unity_mod_exp_step_0 *)
val unity_mod_exp_fast_0 = store_thm(
  "unity_mod_exp_fast_0",
  ``!r:'a ring. !p. unity_mod_exp_fast r p 0 = |1|``,
  rw[unity_mod_exp_fast_def, unity_mod_exp_step_0]);

(* Theorem: #1 <> #0 ==> !p. unity_mod_exp_fast r p 1 = #1 o p *)
(* Proof:
     unity_mod_exp_fast r p 1
   = unity_mod_exp_step r p 1 |1|   by unity_mod_exp_fast_def
   = unity_mod_mult r p |1|         by unity_mod_exp_step_1
   = #1 o p                         by unity_mod_mult_one, #1 <> #0
*)
val unity_mod_exp_fast_1 = store_thm(
  "unity_mod_exp_fast_1",
  ``!r:'a ring. #1 <> #0 ==> !p. unity_mod_exp_fast r p 1 = #1 o p``,
  rw[unity_mod_exp_fast_def, unity_mod_exp_step_1, unity_mod_mult_one]);

(* Theorem: #1 <> #0 ==> !p. unity_mod_exp_fast r p 2 = #1 o unity_mod_sq r p *)
(* Proof:
     unity_mod_exp_fast r p 2
   = unity_mod_exp_step r p 2 |1|                 by unity_mod_exp_fast_def
   = unity_mod_mult r (unity_mod_sq r p) |1|      by unity_mod_exp_step_2
   = #1 o unity_mod_mult r (unity_mod_sq r p)     by unity_mod_mult_one, #1 <> #0
*)
val unity_mod_exp_fast_2 = store_thm(
  "unity_mod_exp_fast_2",
  ``!r:'a ring. #1 <> #0 ==> !p. unity_mod_exp_fast r p 2 = #1 o unity_mod_sq r p``,
  rw[unity_mod_exp_fast_def, unity_mod_exp_step_2, unity_mod_mult_one]);

(* Theorem: EVEN n ==> !p. unity_mod_exp_fast r p n = unity_mod_exp_fast r (unity_mod_sq r p) (HALF n) *)
(* Proof:
     unity_mod_exp_fast r p n
   = unity_mod_exp_step r p n |1|                           by unity_mod_exp_fast_def
   = unity_mod_exp_step r (unity_mod_sq r p) (HALF n) |1|   by unity_mod_exp_step_even, EVEN n
   = unity_mod_exp_fast r (unity_mod_sq r p) (HALF n)       by unity_mod_exp_fast_def
*)
val unity_mod_exp_fast_even = store_thm(
  "unity_mod_exp_fast_even",
  ``!r:'a ring. !n. EVEN n ==>
   !p. unity_mod_exp_fast r p n = unity_mod_exp_fast r (unity_mod_sq r p) (HALF n)``,
  rw[unity_mod_exp_fast_def, unity_mod_exp_step_even]);


(* ------------------------------------------------------------------------- *)
(* The AKS Machine                                                           *)
(* ------------------------------------------------------------------------- *)

(*
Notes

There are two types of machines:
(1) Binary machine, with registers = list of binary cells.
(2) Polynomial machine, with registers = list of number cells = list of poly.

Binary machines are for numerical computations:
* ulog n
* gcd n m
* (x + y) MOD n
* (x * y) MOD n
* (x ** y) MOD n
* root n x
* phi n
* sqrt n

Polynomial machines are for polynomial computations:
* (p + q) MOD (unity k)
* (p * q) MOD (unity k)
* (p ** n) MOD (unity k)

Here I shall just concentrate on a Polynomial machine to perform the introspective check:
   (X + |c|) ** n == X ** n + |c|  in  MOD n, unity k

Note that the (MOD unity k) part is implicit: all polynomials in the machine has LENGTH = k.

Ingredients of Polynomial Machine:
* registers = (:num poly) list
* scalar = :num (for the exponent n)
* op codes with test-branches and call-return.
* stack = :num list, for return PC.
* pc = :num, a program-counter on TAPE.
* ticks = :num, a count-down clock.

Just like a Turing Machine, the Polynomial Machine operates on a Tape:
* Labels on a Tape points to various code sections.
* JUMP label will go to the label, no return.
* CALL label will go to the label, executes, return upon RETURN.
* Termination: either RETURN with empty stack, or ticks become 0.
* Results of RETURN are always in R0, parameters in R0, R1, etc.
*)


(* The AKS machine:

Concept:
* A machine can load a piece of relocatable code, itself can be a subroutine.
* Subroutines are "self-contained" through macro jump.
* Parameters for the machine are always in stack.
* Machine execution ends at a RETURN.
* RETURN gives the actual ticks and words used.
* The cells can grow (ALLOC) and shrink (DISCARD), but there is a MARK.
* scalar ALLOC initializes to 0, vector ALLOC initializes to [].
* For clean stacks, OP args are removed for unary, binary. (3rd arg is external)
* There are 3 'types': boolean, scalar, vector.
* flag is the boolean register. Test will set the flag: ZERO, ONE.
* Jump can be based on the flag: JTrue, JFalse, Jump.
* flag is used to indicate good (T) and nice (F) in AKS parameter search.
* can introduce CHAIN = if (false) RETURN to chain parts for AKS algorithm.

*)

(* Instructions *)
val _ = Datatype `ins =
        NEXT            (* no op *)
      | TRUE num        (* jump by offset if flag is true *)
      | FALSE num       (* jump by offset if flag is false *)
      | JUMP num        (* go forward by offset *)
      | BACK num        (* go back by offset *)
      | CALL num        (* call subroutine at offset *)
      | RETURN          (* return from subroutine call *)
        (* boolean ops *)
      | NEG             (* negate the flag *)
        (* scalar ops *)
      | sALLOC          (* obtain a scalar cell *)
      | sDUMP           (* release a scalar cell *)
      | sPUSH num       (* push scell[num] to stack *)
      | sPOP num        (* pop stack and put to scell[num] *)
      | sPUFF           (* pop stack and discard *)
      | sZERO           (* test if scalar is ZERO *)
      | sONE            (* test if scalar is ONE *)
      | sEVEN           (* test if scalar is EVEN *)
      | sEQ num         (* test if scalar == scell[num] *)
      | sINC            (* set n = INC n  for scalar *)
      | sDEC            (* set n = DEC n  for scalar (no negative) *)
      | sHALF           (* set n = HALF n  for scalar *)
      | sTWICE          (* set n = TWICE n  for scalar *)
      | sADD            (* set n = n + m for sstack: n m *)
      | sSUB            (* set n = n - m for sstack: n m (no neg) *)
      | sMULT           (* set n = n * m for sstack: n m *)
      | sDIV            (* set n = n DIV m for sstack: n m *)
      | sMOD            (* set n = n MOD m for sstack: n m *)
      | sHALVES num     (* set n = n >> r for r = scell[num] *)
        (* vector ops *)
      | vALLOC          (* obtain a vector cell *)
      | vDUMP           (* release a vector cell *)
      | vPUSH num       (* push vcell[num] to stack *)
      | vPOP num        (* pop stack and put to vcell[num] *)
      | vPUFF           (* pop stack and discard *)
      | vNULL           (* test if vector is NULL *)
      | vEQ num         (* test if vector == vcell[num] *)
      | vTURN           (* apply turn to vector *)
        (* both scalar and vector *)
      | vLSHIFT         (* head of vector to scalar, leave tail of vector *)
      | vRSHIFT         (* last of vector to scalar, leave front of vector *)
      | vCMULT num      (* multiply vector by scalar, MOD scell[num] *)
      | vPADD num       (* weak add the top two vectors in stack, MOD scell[num] *)
`;


(* Machine -- with CALL parameters. *)
val _ = Datatype `pm =
     <| (* registers *)
         flag : bool;              (* boolean flag *)
       sstack : num list;          (* scalar stack *)
       vstack : num list list;     (* vector stack *)
        (* memory *)
        scell : num list;          (* scalar cells *)
        vcell : num list list;     (* vector cells *)
        smark : num;               (* mark the end of allocated scalar cells *)
        vmark : num;               (* mark the end of allocated vector cells *)
        words : num;               (* count of memory allocations *)
       memory : num;               (* count-down from some given maximum value *)
       (* control *)
         code : ins list;          (* instruction codes *)
           pc : num;               (* program counter *)
       cstack : num list;          (* call stack *)
        ticks : num;               (* count of steps *)
        clock : num                (* count-down clock from some given maximum value *)
      |>
`;

(* Size of scalar register *)
val ssize_def = Define`
    ssize n (m: pm) = if n < LENGTH (m.scell) then ulog (EL n m.scell) else 0
`;

(* Size of top of scalar stack *)
val ssizet_def = Define`
    ssizet (m: pm) = if NULL m.sstack then 0 else ulog (HD m.sstack)
`;

(* Size of vector register *)
val vsize_def = Define`
    vsize n (m: pm) = if n < LENGTH (m.vcell) then LENGTH (EL n m.vcell) else 0
`;

(* Size of top of vector stack *)
val vsizet_def = Define`
    vsizet (m: pm) = if NULL m.vstack then 0 else LENGTH (HD m.vstack)
`;

(* Cost of each instruction *)
val cost_def = Define`
    cost (ins: ins) (m: pm) = case ins of
      NEXT     => 1 (* no op *)
    | TRUE  n1 => 1 (* jump by offset if flag is true *)
    | FALSE n2 => 1 (* jump by offset if flag is false *)
    | JUMP  n3 => 1 (* go forward by offset *)
    | BACK  n4 => 1 (* go back by offset *)
    | CALL  n5 => 4 (* call subroutine at offset *)
    | RETURN   => 4 (* return from subroutine call *)
      (* boolean ops *)
    | NEG      => 1 (* negate the flag *)
      (* scalar ops *)
    | sALLOC   => 1               (* obtain a scalar cell *)
    | sDUMP    => 1 + ssizet m    (* release a scalar cell *)
    | sPUSH s1 => 1 + ssize s1 m  (* push scell[num] to stack *)
    | sPOP  s2 => 1 + ssize s2 m  (* pop stack and put to scell[num] *)
    | sPUFF    => 1               (* pop stack and discard *)
    | sZERO    => 1 + ssizet m    (* test if scalar is ZERO *)
    | sONE     => 1 + ssizet m    (* test if scalar is ONE *)
    | sEVEN    => 1 + ssizet m    (* test if scalar is EVEN *)
    | sEQ   s3 => 1 + ssize s3 m  (* test if scalar == scell[num] *)
    | sINC     => 1 + ssizet m    (* set n = INC n  for scalar *)
    | sDEC     => 1 + ssizet m    (* set n = DEC n  for scalar *)
    | sHALF    => 1 + ssizet m    (* set n = HALF n  for scalar *)
    | sTWICE   => 1 + ssizet m    (* set n = TWICE n  for scalar *)
    | sADD     => 1 + 2 * ssizet m  (* set n = n + m for sstack: n m *)
    | sSUB     => 1 + 2 * ssizet m  (* set n = n - m for sstack: n m, no negative *)
    | sMULT    => 1 + 2 * ssizet m  (* set n = n * m for sstack: n m *)
    | sDIV     => 1 + 2 * ssizet m  (* set n = n DIV m for sstack: n m *)
    | sMOD     => 1 + 2 * ssizet m  (* set n = n MOD m for sstack: n m *)
    | sHALVES s4 => 1 + 2 * ssizet m + ssize s4 m (* set n = n >> r for r = scell[num] *)
      (* vector ops *)
    | vALLOC   => 1               (* obtain a vector cell *)
    | vDUMP    => 1 + vsizet m    (* release a vector cell *)
    | vPUSH v1 => 1 + vsize v1 m  (* push vcell[num] to stack *)
    | vPOP  v2 => 1 + vsize v2 m  (* pop stack and put to vcell[num] *)
    | vPUFF    => 1               (* pop stack and discard *)
    | vNULL    => 1 + vsizet m (* test if vector is NULL *)
    | vEQ   v3 => 1 + vsizet m + vsize v3 m  (* test if vector == vcell[num] *)
    | vTURN    => 1 + vsizet m    (* apply turn to vector *)
      (* both scalar and vector *)
    | vLSHIFT  => 1 + vsizet m    (* head of vector to scalar, leave tail of vector *)
    | vRSHIFT  => 1 + vsizet m    (* last of vector to scalar, leave front of vector *)
    | vCMULT n6 => 1 + (vsizet m) * (ssizet m) * (ssize n6 m)  (* multiply vector by scalar, MOD scell[num] *)
    | vPADD  n7 => 1 + 2 * (vsizet m) * (ssize n7 m) (* weak add the top two vectors in stack, MOD scell[num] *)
`;

(* Run a Polynomial Machine *)
val run_def = tDefine "run" `
   run (m: pm) =
      if m.clock = 0 then NONE (* abort: time out *)
      else if m.pc >= LENGTH m.code then NONE (* abort: no code *)
      else (* decode and execute *)
      let ins = EL m.pc m.code in
      let nclock = m.clock - cost ins m in
      let nticks = m.ticks + cost ins m in
      case ins of
        NEXT => (* no op *)
           run (m with <| pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | TRUE n1 =>  (* jump by offset if flag is true *)
           run (m with <| pc := m.pc + (if m.flag then n1 else 1); clock := nclock; ticks := nticks |>)
      | FALSE n2 =>  (* jump by offset if flag is false *)
           run (m with <| pc := m.pc + (if m.flag then 1 else n2); clock := nclock; ticks := nticks |>)
      | JUMP n3 => (* go forward by offset *)
           run (m with <| pc := m.pc + n3; clock := nclock; ticks := nticks |>)
      | BACK n4 => (* go back by offset *)
           if n4 > m.pc then NONE (* abort *)
           else run (m with <| pc := m.pc - n4; clock := nclock; ticks := nticks |>)
      | CALL n5 => (* call subroutine at offset *)
           run (m with <| cstack := (m.pc + 1) :: m.vmark :: m.smark :: m.cstack;
                          pc := m.pc + n5; smark := 0; vmark := 0;
                          clock := nclock; ticks := nticks |>)
      | RETURN => (* return from subroutine call *)
           (* sanity checks *)
           if (m.smark <> 0) then NONE (* abort: scalar memory leak *)
           else if (m.vmark <> 0) then NONE (* abort: vector memory leak *)
           else if NULL m.cstack then
                if (LENGTH m.sstack <> 1) then NONE (* abort: scalar stack leak *)
                else if (LENGTH m.vstack <> 1) then NONE (* abort: vector stack leak *)
                else SOME m (* halt *)
           else (* return to caller *)
              run (m with <| smark := EL 2 m.cstack; vmark := EL 1 m.cstack;
                                pc := HD m.cstack; cstack := DROP 3 m.cstack;
                             clock := nclock; ticks := nticks |>)
        (* boolean ops *)
      | NEG => (* negate the flag *)
           run (m with <| flag := ~(m.flag); pc updated_by SUC; clock := nclock; ticks := nticks |>)
        (* scalar ops *)
      | sALLOC => (* obtain a scalar cell *)
           if m.memory = 0 then NONE (* abort: no memory *)
           else run (m with <| scell := 0 :: m.scell; smark updated_by SUC;
                               memory updated_by PRE; words updated_by SUC;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sDUMP => (* release a scalar cell *)
           if m.smark = 0 then NONE (* abort: no more releases *)
           else run (m with <| scell := TL m.scell; smark updated_by PRE;
                               memory updated_by SUC; words updated_by PRE;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sPUSH s1 => (* push scell[num] to stack *)
           if s1 >= m.smark then NONE (* abort: inaccessible cell *)
           else run (m with <| sstack := EL s1 m.scell :: m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sPOP s2 => (* pop stack and put to scell[num] *)
           if s2 >= m.smark then NONE (* abort: inaccessible cell *)
           else run (m with <| scell := LUPDATE (HD m.sstack) s2 m.scell; sstack := TL m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sPUFF => (* pop stack and discard *)
           run (m with <| sstack := TL m.sstack; pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sZERO => (* test if scalar is ZERO *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| flag := (HD m.sstack = 0); pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sONE => (* test if scalar is ONE *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| flag := (HD m.sstack = 1); pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sEVEN =>  (* test if scalar is EVEN *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| flag := EVEN (HD m.sstack); pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sEQ s3 => (* test if scalar == scell[num] *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else if s3 >= m.smark then NONE (* abort: inaccessible cell *)
           else run (m with <| flag := (HD m.sstack = EL s3 m.scell);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sINC => (* set n = INC n  for scalar *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| sstack := SUC (HD m.sstack) :: TL m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sDEC => (* set n = DEC n  for scalar *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| sstack := PRE (HD m.sstack) :: TL m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sHALF => (* set n = HALF n  for scalar *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| sstack := HALF (HD m.sstack) :: TL m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sTWICE => (* set n = TWICE n  for scalar *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else run (m with <| sstack := 2 * (HD m.sstack) :: TL m.sstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sADD => (* set n = n + m  for sstack: n m *)
           if LENGTH m.sstack < 2 then NONE (* abort: need 2 scalars *)
           else run (m with <| sstack := ((HD m.sstack) + (EL 1 m.sstack)) :: TL (TL m.sstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sSUB => (* set n = n - m  for sstack: n m *)
           if LENGTH m.sstack < 2 then NONE (* abort: need 2 scalars *)
           else run (m with <| sstack := ((HD m.sstack) - (EL 1 m.sstack)) :: TL (TL m.sstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sMULT => (* set n = n * m  for sstack: n m *)
           if LENGTH m.sstack < 2 then NONE (* abort: need 2 scalars *)
           else run (m with <| sstack := ((HD m.sstack) * (EL 1 m.sstack)) :: TL (TL m.sstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sDIV => (* set n = n DIV m  for sstack: n m *)
           if LENGTH m.sstack < 2 then NONE (* abort: need 2 scalars *)
           else run (m with <| sstack := ((HD m.sstack) DIV (EL 1 m.sstack)) :: TL (TL m.sstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sMOD => (* set n = n MOD m  for sstack: n m *)
           if LENGTH m.sstack < 2 then NONE (* abort: need 2 scalars *)
           else run (m with <| sstack := ((HD m.sstack) MOD (EL 1 m.sstack)) :: TL (TL m.sstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | sHALVES s4 => (* set n = n MOD exp(2,r) = n >> r  for r = scell[num] *)
           if NULL m.sstack then NONE (* abort: no scalar *)
           else if s4 >= m.smark then NONE (* abort: inaccessible cell *)
           else let r = EL s4 m.scell in
           run (m with <| sstack := (FUNPOW HALF r (HD m.sstack)) :: TL m.sstack;
                          pc updated_by SUC; clock := nclock; ticks := nticks |>)
        (* vector ops *)
      | vPUSH v1 => (* push vcell[num] to stack *)
           if v1 >= m.vmark then NONE (* abort: inaccessible cell *)
           else run (m with <| vstack := EL v1 m.vcell :: m.vstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vPOP v2 =>  (* pop stack and put to vcell[num] *)
           if v2 >= m.vmark then NONE (* abort: inaccessible cell *)
           else run (m with <| vcell := LUPDATE (HD m.vstack) v2 m.vcell; vstack := TL m.vstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vNULL => (* test if vector is NULL *)
           if NULL m.vstack then NONE (* abort: no vector *)
           else run (m with <| flag := NULL (HD m.vstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vEQ v3 => (* test if vector == vcell[num] *)
           if NULL m.vstack then NONE (* abort: no vector *)
           else if v3 >= m.vmark then NONE (* abort: inaccessible cell *)
           else run (m with <| flag := (HD m.vstack = EL v3 m.vcell);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vTURN =>  (* apply turn to vector *)
           if NULL m.vstack then NONE (* abort: no vector *)
           else run (m with <| vstack := turn (HD m.vstack) :: (TL m.vstack);
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
        (* both scalar and vector *)
      | vLSHIFT => (* head of vector to scalar, leave tail of vector *)
           if NULL m.vstack then NONE (* abort: no vector *)
           else if NULL (HD (m.vstack)) then NONE (* abort: vector no head *)
           else run (m with <| sstack := HD (HD m.vstack) :: m.sstack;
                                   vstack := TL (HD m.vstack):: TL m.vstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vRSHIFT => (* last of vector to scalar, leave front of vector *)
           if NULL m.vstack then NONE (* abort: no vector *)
           else if NULL (HD (m.vstack)) then NONE (* abort: vector no last *)
           else run (m with <| sstack := LAST (HD m.vstack) :: m.sstack;
                                   vstack := FRONT (HD m.vstack) :: TL m.vstack;
                               pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vCMULT n6 => (* multiply vector by scalar, MOD scell[num] *)
           if n6 >= m.smark then NONE (* abort: inaccessible cell *)
           else if NULL m.sstack then NONE (* abort: no scalar *)
           else if NULL m.vstack then NONE (* abort: no vector *)
           else let n = EL n6 m.scell in
                let c = HD (m.sstack) in
              run (m with <| vstack := (MAP (\x. (x * c) MOD n) (HD m.vstack)) :: TL m.vstack;
                             pc updated_by SUC; clock := nclock; ticks := nticks |>)
      | vPADD n7 => (* weak add the top two vectors in stack, MOD scell[num] *)
           if n7 >= m.smark then NONE (* abort: inaccessible cell *)
           else if LENGTH m.vstack < 2 then NONE (* abort: no two vectors *)
           else let n = EL n7 m.scell in
                let v1 = EL 0 m.vstack in
                let v2 = EL 1 m.vstack in
              run (m with <| vstack := (MAP2 (\x y. (x + y) MOD n) v1 v2) :: TL m.vstack;
                             pc updated_by SUC; clock := nclock; ticks := nticks |>)
` (WF_REL_TAC `measure (\m. m.clock)` >> rw[cost_def]);
(* Note: use a measure that decreases on each run step *)

(* A Generic Machine *)
val Machine_def = Define`
    Machine = <| flag := F;
                 sstack := [0];
                 vstack := [[0]];
                 scell := [];
                 vcell := [];
                 smark := 0;
                 vmark := 0;
                 words := 0;
                 memory := 0;
                 code := [RETURN];
                 pc := 0;
                 cstack := [];
                 ticks := 0;
                 clock := 0
                |>
`;

(*
EVAL ``run (Machine with <| code := [NEXT; CALL 4; JUMP 2; NEXT; NEXT; RETURN]; clock := 15 |>)``;
*)

(* ------------------------------------------------------------------------- *)
(* Codes for GCD, Coprime, and Phi                                           *)
(* ------------------------------------------------------------------------- *)

(*
// Euclidean GCD
function gcd(n, m) {
   var r // the remainder
   while (m != 0) {
      r = (n % m) | 0   // update remainder
      n = m             // replace n
      m = r             // replace m
   }
   return n
}
*)
(* Machine code of GCD (Euclidean Algorithm) *)
val GCD_def = Define`
    GCD = (* sstack: n m, for (gcd n m) *)
   [ (* gcd: *)
    sALLOC;      (* 0: s0 = n *)
    sALLOC;      (*  1: s1 = m *)
    sALLOC;      (*  2: s2 = r *)
    sPOP 0;      (*  3: n <- n *)
    sPOP 1;      (*  4: m <- m *)
    (* start: *)
    sPUSH 1;     (*  5: scalar <- m *)
    sZERO;       (*  6: scalar == ZERO *)
    TRUE 9;      (*  7: if ZERO, goto end *)
    sPUSH 0;     (*  8: sstack: n m *)
    sMOD;        (*  9: scalar <- n MOD m *)
    sPOP 2;      (* 10: r <- scalar *)
    sPUSH 1;     (* 11: scalar <- m *)
    sPOP 0;      (* 12: n <- scalar, or n <- m  (discard n) *)
    sPUSH 2;     (* 13: scalar <- r *)
    sPOP 1;      (* 14: m <- scalar, or m <- r *)
    BACK 10;     (* 15: goto start *)
    (* end: *)
    sPUFF;       (* 16: discard scalar *)
    sPUSH 0;     (* 17: scalar <- n *)
    sDUMP;       (* 18: *)
    sDUMP;       (* 19: *)
    sDUMP;       (* 20: *)
    RETURN       (* 21: return scalar *)
   ]
`;

(*
EVAL ``run (Machine with <| code := GCD; sstack := [8; 12]; memory := 3; clock := 141 |>)``;   4
EVAL ``run (Machine with <| code := GCD; sstack := [8; 13]; memory := 3; clock := 214 |>)``;   1
*)

(*
// Check if two numbers are coprime
function coprime(n, m) {
   return gcd(n, m) == 1
}
*)
(* Machine code of COPRIME *)
val COPRIME_def = Define`
   COPRIME = (* sstack: n m, for (coprime n m) *)
   [(* coprime: *)
    CALL 3;    (* 0: scalar <- GCD n m *)
    sONE;      (* 1: flag <- scalar == 1 ? *)
    RETURN     (* 2: return flag *)
    (* gcd: *) (* 3: append GCD next *)
   ]
`;

(*
EVAL ``run (Machine with <| code := COPRIME ++ GCD; sstack := [8; 13]; memory := 3; clock := 223 |>)``;   T
*)



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
