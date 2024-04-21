(* ------------------------------------------------------------------------- *)
(* Congruences from Number Theory                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "congruences";

(* ------------------------------------------------------------------------- *)

(* Purpose:
   subgroupTheory has finite_abelian_Fermat
   groupInstancesTheory has Z_star and mult_mod
   For Z_star p, show that MOD_MUL_INV can be evaluted by Fermat's Little Theorem.
   For mult_mod p, show that MOD_MULT_INV can be evaluted by Fermat's Little Theorem.
*)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory dividesTheory numberTheory combinatoricsTheory;

open groupTheory subgroupTheory groupInstancesTheory groupProductTheory;

(* ------------------------------------------------------------------------- *)
(* Congruences Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Definitions and Theorems (# are exported):

   Fermat's Little Theorem:
   fermat_little      |- !p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)
   fermat_little_alt  |- !p a. prime p ==> (a ** (p - 1) MOD p = if a MOD p = 0 then 0 else 1)
   fermat_little_thm  |- !p. prime p ==> !a. a ** p MOD p = a MOD p
   fermat_roots       |- !p. prime p ==> !x y z. (x ** p + y ** p = z ** p) ==> ((x + y) MOD p = z MOD p)

   Multiplicative Inverse by Fermat's Little Theorem:
   Zstar_inverse          |- !p. prime p ==> !a. 0 < a /\ a < p ==> ((Zstar p).inv a = a ** (p - 2) MOD p)
   Zstar_inverse_compute  |- !p a. (Zstar p).inv a =
                             if prime p /\ 0 < a /\ a < p then a ** (p - 2) MOD p else (Zstar p).inv a
   PRIME_2    |- prime 2
   PRIME_3    |- prime 3
   PRIME_5    |- prime 5
   PRIME_7    |- prime 7
   mult_mod_inverse          |- !p. prime p ==>
                                !a. 0 < a /\ a < p ==> ((mult_mod p).inv a = a ** (p - 2) MOD p)
   mult_mod_inverse_compute  |- !p a. (mult_mod p).inv a =
                                if prime p /\ 0 < a /\ a < p then a ** (p - 2) MOD p else (mult_mod p).inv a
*)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (by Zp finite abelian group)                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For prime p, 0 < a < p,  a**(p-1) = 1 (mod p) *)
(* Proof:
   Since 0 < a < p, a IN (Zstar p).carrier,
   and (Zstar p) is a FiniteAbelian Group, by Zstar_finite_abelian_group
   and CARD (Zstar p).carrier = (p-1)      by Zstar_property.
   this follows by finite_abelian_Fermat and Zstar_exp, which relates group_exp to EXP.

> finite_abelian_Fermat |> ISPEC ``(Zstar p)``;
val it = |- !a. FiniteAbelianGroup (Zstar p) /\ a IN (Zstar p).carrier ==>
                ((Zstar p).exp a (CARD (Zstar p).carrier) = (Zstar p).id): thm
*)
val fermat_little = store_thm(
  "fermat_little",
  ``!p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)``,
  rpt strip_tac >>
  `FiniteAbelianGroup (Zstar p)` by rw_tac std_ss[Zstar_finite_abelian_group] >>
  `a IN (Zstar p).carrier /\ ((Zstar p).id = 1)` by rw[Zstar_def, residue_def] >>
  `CARD (Zstar p).carrier = p - 1` by rw_tac std_ss[PRIME_POS, Zstar_property] >>
  metis_tac[finite_abelian_Fermat, Zstar_exp]);

(* Theorem: Fermat's Little Theorem for all a: (a**(p-1) MOD p = if (a MOD p = 0) then 0 else 1  when p is prime. *)
(* Proof: by cases of a, and restricted Fermat's Little Theorem. *)
val fermat_little_alt = store_thm(
  "fermat_little_alt",
  ``!p a. prime p ==> (a**(p-1) MOD p = if (a MOD p = 0) then 0 else 1)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  `a ** (p-1) MOD p = (a MOD p) ** (p-1) MOD p` by metis_tac[EXP_MOD] >>
  rw_tac std_ss[] >| [
    `0 < (p - 1)` by decide_tac >>
    `?k. (p - 1) = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
    rw[EXP],
    `0 < a MOD p` by decide_tac >>
    `a MOD p < p` by rw[MOD_LESS] >>
    metis_tac[fermat_little]
  ]);

(* Theorem: For prime p, a**p = a (mod p) *)
(* Proof: by fermat_little. *)
val fermat_little_thm = store_thm(
  "fermat_little_thm",
  ``!p. prime p ==> !a. a ** p MOD p = a MOD p``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `a ** p MOD p = (a MOD p) ** p MOD p` by rw_tac std_ss[MOD_EXP] >>
  Cases_on `a MOD p = 0` >-
  metis_tac[ZERO_MOD, ZERO_EXP, NOT_ZERO_LT_ZERO] >>
  `0 < a MOD p` by decide_tac >>
  `a MOD p < p` by rw_tac std_ss[MOD_LESS] >>
  `p = SUC (p-1)` by decide_tac >>
  `(a MOD p) ** p MOD p = ((a MOD p) * (a MOD p) ** (p-1)) MOD p` by metis_tac[EXP] >>
  `_ = ((a MOD p) * (a MOD p) ** (p-1) MOD p) MOD p` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = ((a MOD p) * 1) MOD p` by rw_tac std_ss[fermat_little] >>
  `_ = a MOD p` by rw_tac std_ss[MULT_RIGHT_1, MOD_MOD] >>
  rw_tac std_ss[]);

(* Theorem: For prime p > 2, x ** p + y ** p = z ** p ==> x + y = z (mod p) *)
(* Proof:
        x ** p + y ** p = z ** p
   ==>  x ** p + y ** p = z ** p   mod p
   ==>       x +      y = z        mod p   by Fermat's Little Theorem.
*)
val fermat_roots = store_thm(
  "fermat_roots",
  ``!p. prime p ==> !x y z. (x ** p + y ** p = z ** p) ==> ((x + y) MOD p = z MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `z ** p MOD p = (x ** p + y ** p) MOD p` by rw_tac std_ss[] >>
  `_ = (x ** p MOD p + y ** p MOD p) MOD p` by metis_tac[MOD_PLUS] >>
  `_ = (x MOD p + y MOD p) MOD p` by rw_tac std_ss[fermat_little_thm] >>
  `_ = (x + y) MOD p` by rw_tac std_ss[MOD_PLUS] >>
  metis_tac[fermat_little_thm]);

(* ------------------------------------------------------------------------- *)
(* Multiplicative Inverse by Fermat's Little Theorem                         *)
(* ------------------------------------------------------------------------- *)

(* There is already:
- Zstar_inv;
> val it = |- !p. prime p ==> !x. 0 < x /\ x < p ==> ((Zstar p).inv x = (Zstar p).exp x (order (Zstar p) x - 1)) : thm
*)

(* Theorem: For prime p, (Zstar p).inv a = a**(p-2) MOD p *)
(* Proof:
   a * (a ** (p-2) MOD p = a**(p-1) MOD p = 1   by  fermat_little.
   Hence (a ** (p-2) MOD p) is the multiplicative inverse by group_rinv_unique.
*)
val Zstar_inverse = store_thm(
  "Zstar_inverse",
  ``!p. prime p ==> !a. 0 < a /\ a < p ==> ((Zstar p).inv a = (a**(p-2)) MOD p)``,
  rpt strip_tac >>
  `a IN (Zstar p).carrier` by rw_tac std_ss[Zstar_element] >>
  `Group (Zstar p)` by rw_tac std_ss[Zstar_group] >>
  `(Zstar p).id = 1` by rw_tac std_ss[Zstar_property] >>
  `(Zstar p).exp a (p-2) = a**(p-2) MOD p` by rw_tac std_ss[Zstar_exp] >>
  `0 < p` by decide_tac >>
  `SUC (p-2) = p - 1` by decide_tac >>
  `(Zstar p).op a (a**(p-2) MOD p) = (a * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[Zstar_property] >>
  `_ = ((a MOD p) * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[LESS_MOD] >>
  `_ = (a * a**(p-2)) MOD p` by rw_tac std_ss[MOD_TIMES2] >>
  `_ = a ** (p-1) MOD p` by metis_tac[EXP] >>
  `_ = 1` by rw_tac std_ss[fermat_little] >>
  metis_tac[group_rinv_unique, group_exp_element]);

(* Theorem: As function, for prime p, (Zstar p).inv a = a**(p-2) MOD p *)
(* Proof: by Zstar_inverse. *)
val Zstar_inverse_compute = store_thm(
  "Zstar_inverse_compute",
  ``!p a. (Zstar p).inv a = if (prime p /\ 0 < a /\ a < p) then (a**(p-2) MOD p) else ((Zstar p).inv a)``,
  rw_tac std_ss[Zstar_inverse]);

(* Theorem: 2 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_2 = store_thm(
  "PRIME_2",
  ``prime 2``,
  rw_tac std_ss  [prime_def] >>
  `0 < 2` by decide_tac >>
  `0 < b /\ b <= 2` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  rw_tac arith_ss []);

(* Theorem: 3 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_3 = store_thm(
  "PRIME_3",
  ``prime 3``,
  rw_tac std_ss[prime_def] >>
  `b <= 3` by rw_tac std_ss[DIVIDES_LE] >>
  `(b=0) \/ (b=1) \/ (b=2) \/ (b=3)` by decide_tac >-
  fs[] >-
  fs[] >-
  full_simp_tac arith_ss [divides_def] >>
  metis_tac[]);

(* Theorem: 5 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_5 = store_thm(
  "PRIME_5",
  ``prime 5``,
  rw_tac std_ss[prime_def] >>
  `0 < 5` by decide_tac >>
  `0 < b /\ b <= 5` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `(b = 1) \/ (b = 2) \/ (b = 3) \/ (b = 4) \/ (b = 5)` by decide_tac >-
  rw_tac std_ss[] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >>
  rw_tac std_ss[]);

(* Theorem: 7 is prime. *)
(* Proof: by definition of prime. *)
val PRIME_7 = store_thm(
  "PRIME_7",
  ``prime 7``,
  rw_tac std_ss[prime_def] >>
  `0 < 7` by decide_tac >>
  `0 < b /\ b <= 7` by metis_tac[DIVIDES_LE, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `(b = 1) \/ (b = 2) \/ (b = 3) \/ (b = 4) \/ (b = 5) \/ (b = 6) \/ (b = 7)` by decide_tac >-
  rw_tac std_ss[] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >-
  full_simp_tac arith_ss [divides_def] >>
  rw_tac std_ss[]);

(* These computation uses Zstar_inv_compute of groupInstances.

- val _ = computeLib.add_persistent_funs ["PRIME_5"];
- EVAL ``prime 5``;
> val it = |- prime 5 <=> T : thm
- EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = 3 : thm
- EVAL ``(Zstar 5).id``;
> val it = |- (Zstar 5).id = 1 : thm
- EVAL ``(Zstar 5).op 2 3``;
> val it = |- (Zstar 5).op 2 3 = 1 : thm
- EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = 3 : thm
- EVAL ``(Zstar 5).inv 3``;
> val it = |- (Zstar 5).inv 3 = 2 : thm
*)


(*
val th = mk_thm([], ``MOD_MULT_INV 7 x = (x ** 5) MOD 7``);
val _ = save_thm("th", th);
val _ = computeLib.add_persistent_funs ["th"];

val _ = computeLib.add_persistent_funs [("Zstar5_inv", Zstar5_inv)];
EVAL ``(Zstar 5).op 2 3``;
> val it = |- (Zstar 5).op 2 3 = 1 : thm
EVAL ``(Zstar 5).inv 2``;
> val it = |- (Zstar 5).inv 2 = MOD_MUL_INV 5 2 : thm  (before)
> val it = |- (Zstar 5).inv 2 = 3 : thm
*)


(* There is already this in groupInstancesTheory:

- mult_mod_inv;
> val it = |- !p. prime p ==> !x. 0 < x /\ x < p ==> ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1)) : thm
*)

(* Theorem: For prime p, (mult_mod p).inv a = a**(p-2) MOD p *)
(* Proof:
   a * (a ** (p-2) MOD p = a**(p-1) MOD p = 1   by  fermat_little.
   Hence (a ** (p-2) MOD p) is the multiplicative inverse by group_rinv_unique.
*)
val mult_mod_inverse = store_thm(
  "mult_mod_inverse",
  ``!p. prime p ==> !a. 0 < a /\ a < p ==> ((mult_mod p).inv a = (a**(p-2)) MOD p)``,
  rpt strip_tac >>
  `a IN (mult_mod p).carrier` by rw_tac std_ss[mult_mod_property] >>
  `Group (mult_mod p)` by rw_tac std_ss[mult_mod_group] >>
  `(mult_mod p).exp a (p-2) = (a**(p-2) MOD p)` by rw_tac std_ss[mult_mod_exp] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  `SUC (p-2) = p - 1` by decide_tac >>
  `(mult_mod p).exp a (p-2) IN (mult_mod p).carrier` by rw_tac std_ss[group_exp_element] >>
  `(mult_mod p).op a (a**(p-2) MOD p) = (a * (a**(p-2) MOD p)) MOD p` by rw_tac std_ss[mult_mod_property] >>
  `_ = (a * a**(p-2)) MOD p` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = a ** (p-1) MOD p` by metis_tac[EXP] >>
  `_ = 1` by rw_tac std_ss[fermat_little] >>
  metis_tac[group_rinv_unique, mult_mod_property]);

(* Theorem: As function, for prime p, (mult_mod p).inv a = a**(p-2) MOD p *)
(* Proof: by mult_mod_inverse. *)
val mult_mod_inverse_compute = store_thm(
  "mult_mod_inverse_compute",
  ``!p a. (mult_mod p).inv a = if (prime p /\ 0 < a /\ a < p) then (a**(p-2) MOD p) else (mult_mod p).inv a``,
  rw_tac std_ss[mult_mod_inverse]);

(* These computation uses mult_mod_inv_compute of groupInstances.

- val _ = computeLib.add_persistent_funs ["PRIME_7"];
- EVAL ``prime 7``;
> val it = |- prime 7 <=> T : thm
- EVAL ``(mult_mod 7).id``;
> val it = |- (mult_mod 7).id = 1 : thm
- EVAL ``(mult_mod 7).op 5 3``;
> val it = |- (mult_mod 7).op 5 3 = 1 : thm
- EVAL ``(mult_mod 7).inv 5``;
> val it = |- (mult_mod 7).inv 5 = 3 : thm
- EVAL ``(mult_mod 7).inv 3``;
> val it = |- (mult_mod 7).inv 3 = 5 : thm
*)
(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
