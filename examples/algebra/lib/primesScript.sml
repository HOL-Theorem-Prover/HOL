(* ------------------------------------------------------------------------- *)
(* Primality Tests                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "primes";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

(* open dependent theories *)
(* val _ = load "logPowerTheory"; *)
open logPowerTheory; (* for SQRT *)
open helperNumTheory helperFunctionTheory;
open arithmeticTheory dividesTheory;


(* ------------------------------------------------------------------------- *)
(* Primality Tests Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(*

   Two Factors Properties:
   two_factors_property_1  |- !n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b
   two_factors_property_2  |- !n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n
   two_factors_property    |- !n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n

   Primality or Compositeness based on SQRT:
   prime_by_sqrt_factors  |- !p. prime p <=>
                                 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
   prime_factor_estimate  |- !n. 1 < n ==>
                                 (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)

   Primality Testing Algorithm:
   factor_seek_def     |- !q n c. factor_seek n c q =
                                  if c <= q then n
                                  else if 1 < q /\ (n MOD q = 0) then q
                                  else factor_seek n c (q + 1)
   prime_test_def      |- !n. prime_test n <=>
                              if n <= 1 then F else factor_seek n (1 + SQRT n) 2 = n
   factor_seek_bound   |- !n c q. 0 < n ==> factor_seek n c q <= n
   factor_seek_thm     |- !n c q. 1 < q /\ q <= c /\ c <= n ==>
                          (factor_seek n c q = n <=> !p. q <= p /\ p < c ==> ~(p divides n))
   prime_test_thm      |- !n. prime n <=> prime_test n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Two Factors Properties                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (n = a * b) /\ a < SQRT n ==> SQRT n <= b *)
(* Proof:
   If n = 0, then a = 0 or b = 0          by MULT_EQ_0
   But SQRT 0 = 0                         by SQRT_0
   so a <> 0, making b = 0, and SQRT n <= b true.
   If n <> 0, a <> 0 and b <> 0           by MULT_EQ_0
   By contradiction, suppose b < SQRT n.
   Then  n = a * b < a * SQRT n           by LT_MULT_LCANCEL, 0 < a.
    and a * SQRT n < SQRT n * SQRT n      by LT_MULT_RCANCEL, 0 < SQRT n.
   making  n < (SQRT n) ** 2              by LESS_TRANS, EXP_2
   This contradicts (SQRT n) ** 2 <= n    by SQRT_PROPERTY
*)
val two_factors_property_1 = store_thm(
  "two_factors_property_1",
  ``!n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT n = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `b < SQRT n` by decide_tac >>
    `0 < a /\ 0 < b /\ 0 < SQRT n` by decide_tac >>
    `n < a * SQRT n` by rw[] >>
    `a * SQRT n < SQRT n * SQRT n` by rw[] >>
    `n < (SQRT n) ** 2` by metis_tac[LESS_TRANS, EXP_2] >>
    `(SQRT n) ** 2 <= n` by rw[SQRT_PROPERTY] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) /\ SQRT n < a ==> b <= SQRT n *)
(* Proof:
   If n = 0, then a = 0 or b = 0             by MULT_EQ_0
   But SQRT 0 = 0                            by SQRT_0
   so a <> 0, making b = 0, and b <= SQRT n true.
   If n <> 0, a <> 0 and b <> 0              by MULT_EQ_0
   By contradiction, suppose SQRT n < b.
   Then SUC (SQRT n) ** 2
      = SUC (SQRT n) * SUC (SQRT n)          by EXP_2
      <= a * SUC (SQRT n)                    by LT_MULT_RCANCEL, 0 < SUC (SQRT n).
      <= a * b = n                           by LT_MULT_LCANCEL, 0 < a.
   Giving (SUC (SQRT n)) ** 2 <= n           by LESS_EQ_TRANS
   or SQRT ((SUC (SQRT n)) ** 2) <= SQRT n   by SQRT_LE
   or       SUC (SQRT n) <= SQRT n           by SQRT_OF_SQ
   which is a contradiction to !m. SUC m > m by LESS_SUC_REFL
 *)
val two_factors_property_2 = store_thm(
  "two_factors_property_2",
  ``!n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT 0 = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `SQRT n < b` by decide_tac >>
    `SUC (SQRT n) <= a /\ SUC (SQRT n) <= b` by decide_tac >>
    `SUC (SQRT n) * SUC (SQRT n) <= a * SUC (SQRT n)` by rw[] >>
    `a * SUC (SQRT n) <= n` by rw[] >>
    `SUC (SQRT n) ** 2  <= n` by metis_tac[LESS_EQ_TRANS, EXP_2] >>
    `SUC (SQRT n) <= SQRT n` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) ==> a <= SQRT n \/ b <= SQRT n *)
(* Proof:
   By contradiction, suppose SQRT n < a /\ SQRT n < b.
   Then (n = a * b) /\ SQRT n < a ==> b <= SQRT n  by two_factors_property_2
   which contradicts SQRT n < b.
 *)
val two_factors_property = store_thm(
  "two_factors_property",
  ``!n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `SQRT n < a` by decide_tac >>
  metis_tac[two_factors_property_2]);

(* ------------------------------------------------------------------------- *)
(* Primality or Compositeness based on SQRT                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) *)
(* Proof:
   If part: prime p ==> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
     First one: prime p ==> 1 < p  is true    by ONE_LT_PRIME
     Second one: by contradiction, suppose q divides p.
     But prime p /\ q divides p ==> (q = p) or (q = 1)  by prime_def
     Given 1 < q, q <> 1, hence q = p.
     This means p <= SQRT p, giving p = 0 or p = 1      by SQRT_GE_SELF
     which contradicts p <> 0 and p <> 1                by PRIME_POS, prime_def
   Only-if part: 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) ==> prime p
     By prime_def, this is to show:
     (1) p <> 1, true since 1 < p.
     (2) b divides p ==> (b = p) \/ (b = 1)
         By contradiction, suppose b <> p /\ b <> 1.
         b divides p ==> ?a. p = a * b     by divides_def
         which means a <= SQRT p \/ b <= SQRT p   by two_factors_property
         If a <= SQRT p,
         1 < p ==> p <> 0, so a <> 0  by MULT
         also b <> p ==> a <> 1       by MULT_LEFT_1
         so 1 < a, and a divides p    by prime_def, MULT_COMM
         The implication gives ~(a divides p), a contradiction.
         If b <= SQRT p,
         1 < p ==> p <> 0, so b <> 0  by MULT_0
         also b <> 1, so 1 < b, and b divides p.
         The implication gives ~(b divides p), a contradiction.
 *)
val prime_by_sqrt_factors = store_thm(
  "prime_by_sqrt_factors",
  ``!p. prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)``,
  rw[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
 (spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0 /\ q <> 1` by decide_tac >>
  `(q = p) /\ p <> 1` by metis_tac[prime_def] >>
  metis_tac[SQRT_GE_SELF]) >>
  rw[prime_def] >>
  spose_not_then strip_assume_tac >>
  `?a. p = a * b` by rw[GSYM divides_def] >>
  `a <= SQRT p \/ b <= SQRT p` by rw[two_factors_property] >| [
    `a <> 1` by metis_tac[MULT_LEFT_1] >>
    `p <> 0` by decide_tac >>
    `a <> 0` by metis_tac[MULT] >>
    `1 < a` by decide_tac >>
    metis_tac[divides_def, MULT_COMM],
    `p <> 0` by decide_tac >>
    `b <> 0` by metis_tac[MULT_0] >>
    `1 < b` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n) *)
(* Proof:
   If part ~prime n ==> ?p. prime p /\ p divides n /\ p <= SQRT n
   Given n <> 1, ?p. prime p /\ p divides n  by PRIME_FACTOR
   If p <= SQRT n, take this p.
   If ~(p <= SQRT n), SQRT n < p.
      Since p divides n, ?q. n = p * q       by divides_def, MULT_COMM
      Hence q <= SQRT n                      by two_factors_property_2
      Since prime p but ~prime n, q <> 1     by MULT_RIGHT_1
         so ?t. prime t /\ t divides q       by PRIME_FACTOR
      Since 1 < n, n <> 0, so q <> 0         by MULT_0
         so t divides q ==> t <= q           by DIVIDES_LE, 0 < q.
      Take t, then t divides n               by DIVIDES_TRANS
               and t <= SQRT n               by LESS_EQ_TRANS
    Only-if part: ?p. prime p /\ p divides n /\ p <= SQRT n ==> ~prime n
      By contradiction, assume prime n.
      Then p divides n ==> p = 1 or p = n    by prime_def
      But prime p ==> p <> 1, so p = n       by ONE_LT_PRIME
      Giving p <= SQRT p,
      thus forcing p = 0 or p = 1            by SQRT_GE_SELF
      Both are impossible for prime p.
*)
val prime_factor_estimate = store_thm(
  "prime_factor_estimate",
  ``!n. 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
    Cases_on `p <= SQRT n` >-
    metis_tac[] >>
    `SQRT n < p` by decide_tac >>
    `?q. n = q * p` by rw[GSYM divides_def] >>
    `_ = p * q` by rw[MULT_COMM] >>
    `q <= SQRT n` by metis_tac[two_factors_property_2] >>
    `q <> 1` by metis_tac[MULT_RIGHT_1] >>
    `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
    `n <> 0` by decide_tac >>
    `q <> 0` by metis_tac[MULT_0] >>
    `0 < q ` by decide_tac >>
    `t <= q` by rw[DIVIDES_LE] >>
    `q divides n` by metis_tac[divides_def] >>
    metis_tac[DIVIDES_TRANS, LESS_EQ_TRANS],
    spose_not_then strip_assume_tac >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1 /\ p <> 0` by decide_tac >>
    `p = n` by metis_tac[prime_def] >>
    metis_tac[SQRT_GE_SELF]
  ]);

(* ------------------------------------------------------------------------- *)
(* Primality Testing Algorithm                                               *)
(* ------------------------------------------------------------------------- *)

(* Seek the prime factor of number n, starting with q, up to cutoff c. *)
val factor_seek_def = tDefine "factor_seek" `
  factor_seek n c q =
    if c <= q then n
    else if 1 < q /\ (n MOD q = 0) then q
    else factor_seek n c (q + 1)
`(WF_REL_TAC `measure (\(n,c,q). c - q)` >> simp[]);
(* Use 1 < q so that, for prime n, it gives a result n for any initial q, including q = 1. *)

(* Primality test by seeking a factor exceeding (SQRT n). *)
val prime_test_def = Define`
    prime_test n =
       if n <= 1 then F
       else factor_seek n (1 + SQRT n) 2 = n
`;

(*
EVAL ``MAP prime_test [1 .. 15]``; = [F; T; T; F; T; F; T; F; F; F; T; F; T; F; F]: thm
*)

(* Theorem: 0 < n ==> factor_seek n c q <= n *)
(* Proof:
   By induction from factor_seek_def.
   If c <= q,
      Then factor_seek n c q = n, hence true    by factor_seek_def
   If q = 0,
      Then factor_seek n c 0 = 0, hence true    by factor_seek_def
   If n MOD q = 0,
      Then factor_seek n c q = q                by factor_seek_def
      Thus q divides n                          by DIVIDES_MOD_0, q <> 0
      hence q <= n                              by DIVIDES_LE, 0 < n
   Otherwise,
         factor_seek n c q
       = factor_seek n c (q + 1)                by factor_seek_def
      <= n                                      by induction hypothesis
*)
val factor_seek_bound = store_thm(
  "factor_seek_bound",
  ``!n c q. 0 < n ==> factor_seek n c q <= n``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >>
  `q divides n` by rw[DIVIDES_MOD_0] >>
  rw[DIVIDES_LE]);

(* Theorem: 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n))) *)
(* Proof:
   By induction from factor_seek_def, this is to show:
   (1) n MOD q = 0 ==> ?p. (q <= p /\ p < c) /\ p divides n
       Take p = q, then n MOD q = 0 ==> q divides n       by DIVIDES_MOD_0, 0 < q
   (2) n MOD q <> 0 ==> factor_seek n c (q + 1) = n <=>
                        !p. q <= p /\ p < c ==> ~(p divides n)
            factor_seek n c (q + 1) = n
        <=> !p. q + 1 <= p /\ p < c ==> ~(p divides n))   by induction hypothesis
         or !p.      q < p /\ p < c ==> ~(p divides n))
        But n MOD q <> 0 gives ~(q divides n)             by DIVIDES_MOD_0, 0 < q
       Thus !p.     q <= p /\ p < c ==> ~(p divides n))
*)
val factor_seek_thm = store_thm(
  "factor_seek_thm",
  ``!n c q. 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n)))``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >| [
    qexists_tac `q` >>
    rw[DIVIDES_MOD_0],
    rw[EQ_IMP_THM] >>
    spose_not_then strip_assume_tac >>
    `0 < q` by decide_tac >>
    `p <> q` by metis_tac[DIVIDES_MOD_0] >>
    `q + 1 <= p` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: prime n = prime_test n *)
(* Proof:
       prime n
   <=> 1 < n /\ !q. 1 < q /\ n <= SQRT n ==> ~(n divides p)     by prime_by_sqrt_factors
   <=> 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)          where c = 1 + SQRT n
   Under 1 < n,
   Note SQRT n <> 0         by SQRT_EQ_0, n <> 0
     so 1 < 1 + SQRT n = c, or 2 <= c.
   Also SQRT n <= n         by SQRT_LE_SELF
    but SQRT n <> n         by SQRT_EQ_SELF, 1 < n
     so SQRT n < n, or c <= n.
   Thus 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)
    <=> factor_seek n c q = n                              by factor_seek_thm
    <=> prime_test n                                       by prime_test_def
*)
val prime_test_thm = store_thm(
  "prime_test_thm",
  ``!n. prime n = prime_test n``,
  rw[prime_test_def, prime_by_sqrt_factors] >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    `!q. 2 <= q /\ q < c ==> ~(q divides n)` by fs[Abbr`c`] >>
    rw[factor_seek_thm],
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    fs[factor_seek_thm] >>
    `!p. 1 < p /\ p <= SQRT n ==> ~(p divides n)` by fs[Abbr`c`] >>
    rw[]
  ]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
