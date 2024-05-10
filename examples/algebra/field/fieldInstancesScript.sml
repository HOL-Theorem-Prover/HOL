(* ------------------------------------------------------------------------- *)
(* Applying Field Theory: Field Instances                                    *)
(* ------------------------------------------------------------------------- *)

(*

Field Instances
===============
The important ones:

GF(p) -- Galois Field of order prime p.

*)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory numberTheory
     combinatoricsTheory;

(* declare new theory at start *)
val _ = new_theory "fieldInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open groupMapTheory ringMapTheory fieldMapTheory;
open groupInstancesTheory ringInstancesTheory;

(* ------------------------------------------------------------------------- *)
(* Field Instances Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Field is a special type of Ring, with data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.
*)
(* Definitions and Theorems (# are exported):

   The Trivial Field (GF 2):
   trivial_field_def |- !zero_elt one_elt. trivial_field zero_elt one_elt =
         <|carrier := {zero_elt; one_elt};
               sum :=  <|carrier := {zero_elt; one_elt};
                              id := zero_elt;
                              op := (\x y. if x = zero_elt then y else if y = zero_elt then x else zero_elt)|>;
              prod := <|carrier := {zero_elt; one_elt};
                             id := one_elt;
                             op := (\x y.  if x = zero_elt then zero_elt else if y = zero_elt then zero_elt else one_elt)|> |>
   trivial_field     |- !zero one. zero <> one ==> FiniteField (trivial_field zero one)

   Galois Field:
   GF_def           |- !p. GF p = <|carrier := {n | n < p};
                                        sum := add_mod p;
                                       prod := mult_mod p including 0|>
   GF_property      |- !p. ((GF p).carrier = count p) /\ ((GF p).sum = add_mod p) /\
                           ((GF p).prod = mult_mod p including 0) /\
                           ((GF p).sum.inv = (add_mod p).inv) /\
                           (((GF p).prod excluding 0).inv = (mult_mod p including 0 excluding 0).inv) /\
                           FINITE (GF p).carrier /\ (CARD (GF p).carrier = p)
   GF_element       |- !p x. x IN (GF p).carrier <=> x < p
   GF_zero          |- !p. (GF p).sum.id = 0
   GF_one           |- !p. (GF p).prod.id = 1
   GF_add           |- !p x y. (GF p).sum.op x y = (x + y) MOD p
   GF_mult          |- !p x y. (GF p).prod.op x y = (x * y) MOD p

   GF_sum_abelian_group      |- !n. 0 < n ==> AbelianGroup (GF n).sum
   GF_sum_group              |- !n. 0 < n ==> Group (GF n).sum
   GF_prod_abelian_monoid    |- !n. 1 < n ==> AbelianMonoid (GF n).prod
   GF_prod_monoid            |- !n. 1 < n ==> Monoid (GF n).prod
   GF_ring                   |- !n. 1 < n ==> Ring (GF n)
   GF_finite                 |- !n. FINITE (GF n).carrier
   GF_card                   |- !n. CARD (GF n).carrier = n
   GF_finite_ring            |- !n. 1 < n ==> FiniteRing (GF n)

   GF_field                  |- !p. prime p ==> Field (GF p)
   GF_finite_field           |- !p. prime p ==> FiniteField (GF p)
   GF_prime_char             |- !p. prime p ==> (char (GF p) = p)
   GF_char                   |- !n. 1 < n ==> (char (GF n) = n)

   Modulo Multiplication Field:
   ZN_field                  |- !p. prime p ==> Field (ZN p)
   ZN_field_iff              |- !n. prime n <=> Field (ZN n)
   ZN_finite_field           |- !p. prime p ==> FiniteField (ZN p)
   ZN_finite_field_iff       |- !p. prime p <=> FiniteField (ZN p)

   ZN and GF Theorems:
   ZN_to_GF_element          |- !n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (GF m).carrier
   ZN_to_GF_sum_group_homo   |- !n m. 0 < n /\ m divides n ==>
                                      GroupHomo (\x. x MOD m) (ZN n).sum (GF m).sum
   ZN_to_GF_prod_monoid_homo |- !n m. 0 < n /\ 1 < m /\ m divides n ==>
                                      MonoidHomo (\x. x MOD m) (ZN n).prod (GF m).prod
   ZN_to_GF_ring_homo        |- !n m. 0 < n /\ 1 < m /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (GF m)

   ZN_to_GF_ring_iso         |- !n. 1 < n ==> RingIso (\x. x MOD n) (ZN n) (GF n)
   GF_char_eq_ZN_char        |- !n. 1 < n ==> (char (GF n) = n)

   Multiplicative Inverse in Galois Field:
   GF_eval          |- !p. (!x. x IN (GF p).carrier <=> x < p) /\
                           (!x y. (GF p).sum.op x y = (x + y) MOD p) /\
                           (!x y. (GF p).prod.op x y = (x * y) MOD p) /\
                           ((GF p).sum.id = 0) /\ ((GF p).prod.id = 1)
   GF_mult_inv     |- !p. prime p ==> !x. 0 < x /\ x < p ==> (((GF p).prod excluding 0).inv x = (mult_mod p).inv x)
   GF_mult_inv_compute  |- !p x. ((GF p).prod excluding 0).inv x =
                            if prime p /\ 0 < x /\ x < p then (mult_mod p).inv x else ((GF p).prod excluding 0).inv x
   GF_sum_inv           |- !p. (GF p).sum.inv = (add_mod p).inv
   GF_prod_nonzero_inv  |- !p. ((GF p).prod excluding 0).inv = (mult_mod p).inv

*)
(* ------------------------------------------------------------------------- *)
(* The Trivial Field = GF(2) = {|0|, |1|}.                                   *)
(* ------------------------------------------------------------------------- *)

(* This is not OK!

val trivial_field_def = Define`
  (trivial_field (zero: 'a) (one: 'a)) : 'a field =
   <| carrier := {zero; one};
      sum := <| carrier := {zero; one};
                id := zero;
            (* inv := (\x. x); *)
                op := (\x y. if x = zero then y
                             else if y = zero then x
                             else zero) |>;
      prod := <| carrier := {zero; one};
                id := one;
            (* inv := (\x. x); *)
                op := (\x y. if x = zero then zero
                                else if y = zero then zero
                                else one) |>
    |>
`;
-- Why? *)

val trivial_field_def = Define`
  (trivial_field zero_elt one_elt) : 'a field =
   <| carrier := {zero_elt; one_elt};
      sum := <| carrier := {zero_elt; one_elt};
                id := zero_elt;
            (* inv := (\x. x); *)
                op := (\x y. if x = zero_elt then y
                             else if y = zero_elt then x
                             else zero_elt) |>;
      prod := <| carrier := {zero_elt; one_elt};
                id := one_elt;
            (* inv := (\x. x); *)
                op := (\x y. if x = zero_elt then zero_elt
                                else if y = zero_elt then zero_elt
                                else one_elt) |>
    |>
`;

(* Theorem: {|0|, |1|} is indeed a field. *)
(* Proof: by definition, the field tables are:

   +    |0| |1|          *  |0| |1|
   ------------         -----------
   |0|  |0| |1|         |0| |0| |0|
   |1|  |1| |0|         |1| |0| |1|

*)
val trivial_field = store_thm(
  "trivial_field",
  ``!zero one. zero <> one ==> FiniteField (trivial_field zero one)``,
  rw_tac std_ss[FiniteField_def] >| [
    `!x a b. x IN {a; b} <=> ((x = a) \/ (x = b))` by rw[] >>
    rw_tac std_ss[trivial_field_def, field_def_alt] >| [
      rw_tac std_ss[AbelianGroup_def, group_def_alt] >| [
        rw_tac std_ss[],
        rw_tac std_ss[],
        metis_tac[],
        metis_tac[]
      ],
      rw_tac std_ss[AbelianGroup_def, group_def_alt, excluding_def, IN_DIFF, IN_SING] >>
      metis_tac[],
      rw_tac std_ss[]
    ],
    rw[trivial_field_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* GF(p), Galois Field of order prime p.                                     *)
(* ------------------------------------------------------------------------- *)

(* Galois Field *)
val GF_def = zDefine`
  GF p :num field =
   <| carrier := { n | n < p };
          sum := add_mod p;
         prod := (mult_mod p including 0)
    |>
`;
(* Use of zDefine to avoid incorporating into computeLib, by default. *)

(*
- type_of ``GF p``;
> val it = ``:num field`` : hol_type
*)

(* Theorem: Evaluation of GF fields. *)
(* Proof: by GF_def. *)
val GF_eval = store_thm(
  "GF_eval",
  ``!p. (!x. x IN (GF p).carrier <=> x < p) /\
       (!x y. (GF p).sum.op x y = (x + y) MOD p) /\
       (!x y. (GF p).prod.op x y = (x * y) MOD p) /\
       ((GF p).sum.id = 0) /\
       ((GF p).prod.id = 1)``,
  rw[GF_def, add_mod_def, mult_mod_def, group_including_property]);

val _ = computeLib.add_persistent_funs ["GF_eval"];
(* Later, also GF_mult_inv in computeLib. *)

(* Theorem: properties of (GF p), including inverse:
            (((GF p).prod excluding 0).inv = ((mult_mod p) including 0 excluding 0).inv) *)
(* Proof: by definition. *)
val GF_property = store_thm(
  "GF_property",
  ``!p. ((GF p).carrier = count p) /\
       ((GF p).sum = add_mod p) /\
       ((GF p).prod = mult_mod p including 0) /\
       ((GF p).sum.inv = (add_mod p).inv) /\
       (((GF p).prod excluding 0).inv = ((mult_mod p) including 0 excluding 0).inv) /\
       FINITE (GF p).carrier /\ (CARD (GF p).carrier = p)``,
  rw_tac std_ss[GF_def, GSYM count_def, FINITE_COUNT, CARD_COUNT]);

(* Theorem: x IN (GF p).carrier iff x < p *)
(* Proof: by GF_def, i.e. (GF p).carrier = count p. *)
val GF_element = store_thm(
  "GF_element",
  ``!p x. x IN (GF p).carrier <=> x < p``,
  rw[GF_def]);

(* Theorem: (GF p) zero is 0. *)
(* Proof: by definitions. *)
val GF_zero = store_thm(
  "GF_zero",
  ``!p. (GF p).sum.id = 0``,
  rw_tac std_ss[GF_def, add_mod_def]);

(* Theorem: (GF p) one is 1. *)
(* Proof: by definitions. *)
val GF_one = store_thm(
  "GF_one",
  ``!p. (GF p).prod.id = 1``,
  rw_tac std_ss[GF_def, mult_mod_def, including_def]);

(* Theorem: field_add (GF p) x y = (x + y) MOD p *)
(* Proof: by definitions. *)
val GF_add = store_thm(
  "GF_add",
  ``!p x y. (GF p).sum.op x y = (x + y) MOD p``,
  rw_tac std_ss[GF_def, add_mod_def]);

(* Theorem: field_mult (GF p) x y = (x * y) MOD p *)
(* Proof: by definitions. *)
val GF_mult = store_thm(
  "GF_mult",
  ``!p x y. (GF p).prod.op x y = (x * y) MOD p``,
  rw_tac std_ss[GF_def, mult_mod_def, including_def]);

(* Theorem: !n. 0 < n ==> AbelianGroup (GF n).sum *)
(* Proof:
   By definitions, this is to show:
   (1) ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n
       True by MOD_ADD_ASSOC.
   (2) {x | x < n /\ ?y. y < n /\ ((x + y) MOD n = 0) /\ ((y + x) MOD n = 0)} = {i | i < n}
       This is to show: x < n ==> ?y. y < n /\ ((x + y) MOD n = 0) /\ ((y + x) MOD n = 0)
       If x = 0, take y = 0. Then 0 MOD n = 0   by ZERO_MOD
       If x <> 0, take y = (n - x) MOD n
       Then (n - x) < n, so that y < n          by arithmetic
            (x + y) MOD n
          = (x + (n - x) MOD n) MOD n
          = (x MOD n + (n - x) MOD n) MOD n     by LESS_MOD
          = (x + (n - x)) MOD n                 by MOD_PLUS
          = n MOD n                             by arithmetic
          = 0                                   by DIVMOD_ID
       Also (y + x) MOD n = (x + y) MOD n = 0   by ADD_COMM
   (3) (x + y) MOD n = (y + x) MOD n
       True by ADD_COMM.
*)
val GF_sum_abelian_group = store_thm(
  "GF_sum_abelian_group",
  ``!n. 0 < n ==> AbelianGroup (GF n).sum``,
  rw_tac std_ss[AbelianGroup_def, Group_def, Monoid_def, GF_def, add_mod_def, monoid_invertibles_def, GSPECIFICATION] >-
  rw[MOD_ADD_ASSOC] >-
 (rw[EXTENSION, EQ_IMP_THM] >>
  Cases_on `x = 0` >| [
    qexists_tac `0` >>
    rw[],
    qexists_tac `(n - x) MOD n` >>
    `n - x < n` by decide_tac >>
    `(x + (n - x) MOD n) MOD n = (x MOD n + (n - x) MOD n) MOD n` by rw[LESS_MOD] >>
    `_ = (x + (n - x)) MOD n ` by rw[MOD_PLUS] >>
    `_ = 0 ` by rw_tac arith_ss[DIVMOD_ID] >>
    metis_tac[LESS_MOD, ADD_COMM]
  ]) >>
  rw[ADD_COMM]);

(* Theorem: !n. 0 < n ==> Group (GF n).sum *)
(* Proof: by GF_sum_abelian_group. *)
val GF_sum_group = store_thm(
  "GF_sum_group",
  ``!n. 0 < n ==> Group (GF n).sum``,
  metis_tac[GF_sum_abelian_group, AbelianGroup_def]);

(* Theorem: !n. 1 < n ==> AbelianMonoid (GF n).prod *)
(* Proof:
   By definitions, this is to show:
   (1) (z * (x * y) MOD n) MOD n = (x * (y * z) MOD n) MOD n
         (z * (x * y) MOD n) MOD n
       = ((z MOD n) * (x * y) MOD n) MOD n   by MOD_TIMES2, MOD_MOD
       = (z * (x * y)) MOD n                 by MOD_TIMES2
       = ((x * y) * z) MOD n                 by MULT_COMM
       = (x * (y * z)) MOD n                 by MULT_ASSOC
       = (x * (y * z) MOD n) MOD n           by MOD_TIMES2, LESS_MOD
   (2) (0 * (x * y) MOD n) MOD n = (x * (y * 0) MOD n) MOD n
       True by MULT_CLAUSES.
   (3) (z * (x * 0) MOD n) MOD n = (x * (0 * z) MOD n) MOD n
       True by MULT_CLAUSES.
   (4) (0 * (x * 0) MOD n) MOD n = (x * (0 * 0) MOD n) MOD n
       True by MULT_CLAUSES.
   (5) (z * (0 * y) MOD n) MOD n = (0 * (y * z) MOD n) MOD n
       True by MULT_CLAUSES.
   (6) (0 * (0 * y) MOD n) MOD n = (0 * (y * 0) MOD n) MOD n
       True by MULT_CLAUSES.
   (7) (z * (0 * 0) MOD n) MOD n = (0 * (0 * z) MOD n) MOD n
       True by MULT_CLAUSES.
*)
val GF_prod_abelian_monoid = store_thm(
  "GF_prod_abelian_monoid",
  ``!n. 1 < n ==> AbelianMonoid (GF n).prod``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `0 MOD n = 0` by rw[] >>
  rw_tac arith_ss[AbelianMonoid_def, Monoid_def, GF_def, mult_mod_def, including_def, GSPECIFICATION, EXTENSION, SING_UNION, UNION_DEF, IN_SING] >| [
    `(z * (x * y) MOD n) MOD n = ((z MOD n) * (x * y) MOD n) MOD n` by metis_tac[MOD_TIMES2, MOD_MOD] >>
    `_ = (z * (x * y)) MOD n` by rw_tac std_ss[MOD_TIMES2] >>
    `_ = ((x * y) * z) MOD n` by rw_tac std_ss[MULT_COMM] >>
    `_ = (x * (y * z)) MOD n` by rw_tac std_ss[MULT_ASSOC] >>
    `_ = (x * (y * z) MOD n) MOD n` by metis_tac[MOD_TIMES2, LESS_MOD] >>
    rw_tac std_ss[],
    rw[],
    rw[],
    rw[],
    rw[],
    rw[],
    rw[]
  ]);

(* Theorem: !n. 1 < n ==> Monoid (GF n).prod *)
(* Proof: by GF_prod_abelian_monoid, AbelianMonoid_def. *)
val GF_prod_monoid = store_thm(
  "GF_prod_monoid",
  ``!n. 1 < n ==> Monoid (GF n).prod``,
  metis_tac[GF_prod_abelian_monoid, AbelianMonoid_def]);

(* Theorem: 1 < n ==> Ring (GF n) *)
(* Proof:
   By Ring_def, this is to show:
   (1) AbelianGroup (GF n).sum, true by GF_sum_abelian_group.
   (2) AbelianMonoid (GF n).prod, true by GF_prod_abelian_monoid.
   (3) (GF n).sum.carrier = (GF n).carrier, true by GF_def, add_mod_def.
   (4) (GF n).prod.carrier = (GF n).carrier, true by GF_def, mult_mod_def, including_def.
   (5) (GF n).prod.op x ((GF n).sum.op y z) = (GF n).sum.op ((GF n).prod.op x y) ((GF n).prod.op x z)
       This is to show: (x * (y + z) MOD n) MOD n = ((x * y) MOD n + (x * z) MOD n) MOD n
         (x * (y + z) MOD n) MOD n
       = ((x MOD n) * (y + z) MOD n) MOD n      by MOD_TIMES2, LESS_MOD
       = (x * (y + z)) MOD n                    by MOD_TIMES2
       = (x * y + x * z) MOD n                  by LEFT_ADD_DISTRIB
       = ((x * y) MOD n + (x * z) MOD n) MOD n  by MOD_PLUS

   Note: GF_field: |- !p. prime p ==> Field (GF p)  works for prime only.
*)
val GF_ring = store_thm(
  "GF_ring",
  ``!n. 1 < n ==> Ring (GF n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  rw_tac std_ss[Ring_def] >-
  rw[GF_sum_abelian_group] >-
  rw[GF_prod_abelian_monoid] >-
  rw[GF_def, add_mod_def] >-
  (rw[GF_def, mult_mod_def, including_def, EXTENSION] >> metis_tac[]) >>
  full_simp_tac (srw_ss())[GF_def, mult_mod_def, including_def] >>
  rw_tac std_ss[LEFT_ADD_DISTRIB]);

(* Theorem: FINITE (GF n).carrier *)
(* Proof: by GF_property *)
val GF_finite = store_thm(
  "GF_finite",
  ``!n. FINITE (GF n).carrier``,
  rw[GF_property]);

(* Theorem: CARD (GF n).carrier = n *)
(* Proof: by GF_property *)
val GF_card = store_thm(
  "GF_card",
  ``!n. CARD (GF n).carrier = n``,
  rw[GF_property]);

(* Theorem: 1 < n ==> FiniteRing (GF n) *)
(* Proof: by GF_ring, GF_finite, FiniteRing_def. *)
val GF_finite_ring = store_thm(
  "GF_finite_ring",
  ``!n. 1 < n ==> FiniteRing (GF n)``,
  rw[GF_ring, GF_finite, FiniteRing_def]);

(* Theorem: GF p is a field *)
(* Proof: check definitions.
   For distribution: (x * (y + z) MOD n) MOD n = ((x * y) MOD n + (x * z) MOD n) MOD n
   LHS = (x * (y + z) MOD n) MOD n
       = (x MOD n * ((y + z) MOD n) MOD n        by LESS_MOD
       = (x * (y + z)) MOD n                     by MOD_TIMES2
       = (x * y + x * z) MOD n                   by LEFT_ADD_DISTRIB
       = ((x * y) MOD n + (x + y) MOD n) MOD n   by MOD_PLUS
       = RHS
*)
val GF_field = store_thm(
  "GF_field",
  ``!p. prime p ==> Field (GF p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `(add_mod p).id = 0` by rw_tac std_ss[add_mod_def] >>
  `0 NOTIN (mult_mod p).carrier` by rw[mult_mod_def] >>
  rw_tac std_ss[field_def_alt, GF_def, GSPECIFICATION] >| [
    rw_tac std_ss[add_mod_abelian_group],
    rw_tac std_ss[mult_mod_abelian_group, GSYM group_including_excluding_abelian],
    rw_tac std_ss[add_mod_def],
    rw[mult_mod_def, including_def, EXTENSION, EQ_IMP_THM] >>
    rw_tac std_ss[],
    rw_tac std_ss[mult_mod_def, including_def],
    rw_tac std_ss[add_mod_def, mult_mod_def, including_def] >>
    metis_tac[LEFT_ADD_DISTRIB, MOD_PLUS, MOD_TIMES2, LESS_MOD]
  ]);

(* Theorem: GF p is a FINITE field *)
(* Proof: by GF_field and GF_finite. *)
val GF_finite_field = store_thm(
  "GF_finite_field",
  ``!p. prime p ==> FiniteField (GF p)``,
  rw_tac std_ss[FiniteField_def, GF_field, GF_property]);


(* TODO:

define: GF p = ZN p
- ZN_def;
> val it = |- !n. ZN n = <|carrier := count n; sum := add_mod n; prod := times_mod n|> : thm
i.e. use times_mod p instead of (mult_mod p including 0)

*)

(* Theorem: prime p ==> char (GF p) = p *)
(* Proof:
     Since FiniteRing (GF p)                              by GF_finite_ring
           (char (GF p)) divides (CARD (GF p).carrier)    by finite_ring_char_divides
       But CARD (GF p).carrier = p                        by GF_card
       and (GF p).sum.id = 0                              by GF_zero
       and (GF p).prod.id = 1                             by GF_one
        so char (GF p) <> 1                               by ring_char_eq_1
     Hence char (GF p) = p                                by prime_def
*)
val GF_prime_char = store_thm(
  "GF_prime_char",
  ``!p. prime p ==> (char (GF p) = p)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `FiniteRing (GF p)` by rw[GF_finite_ring] >>
  `(char (GF p)) divides (CARD (GF p).carrier)` by rw[finite_ring_char_divides] >>
  metis_tac[GF_card, GF_one, GF_zero, prime_def, ring_char_eq_1, FiniteRing_def, DECIDE``1 <> 0``]);

(* Theorem: 1 < n ==> (char (GF n) = n) *)
(* Proof:
   Since FiniteRing (GF n)    by GF_finite_ring, 1 < n.
     and (GF n).prod.id = 1   by GF_one
     and (GF n).sum.id = 0    by GF_zero
   This allows changing of goal, by finite_ring_char_alt, to show:
      ((GF n).sum.exp 1 n = 0) /\
      !m. 0 < m /\ m < n ==> (GF n).sum.exp 1 m <> 0
   By GF_def and other definitions, these will be:
    (1) FUNPOW (\j. (1 + j) MOD n) n 0 = 0
    (2) 0 < m /\ m < n ==> FUNPOW (\j. (1 + j) MOD n) m 0 <> 0
   Thus it is better to prove a lemma:
      !m. FUNPOW (\j. (1 + j) MOD n) m 0 = m MOD n
   By induction on m.
   Base case: FUNPOW (\j. (1 + j) MOD n) 0 0 = 0 MOD n
     LHS = FUNPOW (\j. (1 + j) MOD n) 0 0
         = 0                               by FUNPOW_0
         = 0 MOD n                         by ZERO_MOD, 0 < n.
         = RHS
   Step case: FUNPOW (\j. (1 + j) MOD n) m 0 = m MOD n ==>
              FUNPOW (\j. (1 + j) MOD n) (SUC m) 0 = SUC m MOD n
     LHS = FUNPOW (\j. (1 + j) MOD n) (SUC m) 0
         = (\j. (1 + j) MOD n) (FUNPOW (\j. (1 + j) MOD n) m 0)   by FUNPOW_SUC
         = (\j. (1 + j) MOD n) m MOD n                            by induction hypothesis
         = (1 + m MOD n) MOD n                                    by function application
         = (1 MOD n + m MOD n) MOD n                              by ONE_MOD, 1 < n.
         = (1 + m) MOD n                                          by MOD_PLUS
         = SUC m MOD n                                            by SUC_ONE_ADD
         = RHS
   With lemma proved, the cases are:
    (1) FUNPOW (\j. (1 + j) MOD n) n 0 = 0 MOD n = 0              by ZERO_MOD, 0 < n.
    (2) FUNPOW (\j. (1 + j) MOD n) m 0 = m MOD n = m <> 0         by LESS_MOD, m < n.
*)
val GF_char = store_thm(
  "GF_char",
  ``!n. 1 < n ==> (char (GF n) = n)``,
  rpt strip_tac >>
  `FiniteRing (GF n)` by rw[GF_finite_ring] >>
  `0 < n` by decide_tac >>
  `(GF n).prod.id = 1` by rw[GF_one] >>
  `(GF n).sum.id = 0` by rw[GF_zero] >>
  `((GF n).sum.exp 1 n = 0) /\ !m. 0 < m /\ m < n ==> (GF n).sum.exp 1 m <> 0` suffices_by metis_tac[finite_ring_char_alt] >>
  `!m. FUNPOW (\j. (1 + j) MOD n) m 0 = m MOD n` by
  (Induct_on `m` >-
  rw[] >>
  rw_tac std_ss[FUNPOW_SUC] >>
  metis_tac[SUC_ONE_ADD, ONE_MOD, MOD_PLUS]
  ) >>
  rw_tac std_ss[GF_def, add_mod_def, monoid_exp_def] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Modulo Multiplication Field.                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p ==> Field (ZN p) *)
(* Proof:
   By Field_def, this is to show:
   (1) Ring (ZN p),
       Since 0 < p     by PRIME_POS
       This is true    by ZN_ring
   (2) Group ((ZN p).prod excluding (ZN p).sum.id)
       Expand by group_def_alt, this is to show:
       (1) 1 < 1 ==> F
           This is F ==> F.
       (2) x <> 0 /\ x < p /\ y <> 0 /\ y < p ==> (x * y) MOD p <> 0
           True by EUCLID_LEMMA.
       (3) ((x * y) MOD p * z) MOD p = (x * (y * z) MOD p) MOD p
           True by MOD_MULT_ASSOC.
       (4) x <> 0 /\ x < p ==> ?y. (y < p /\ y <> 0) /\ ((y * x) MOD p = 1)
           True by MOD_MULT_INV_EXISTS, MULT_COMM.
*)
val ZN_field = store_thm(
  "ZN_field",
  ``!p. prime p ==> Field (ZN p)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < p` by decide_tac >>
  rw[Field_def] >-
  rw[ZN_ring] >>
  `Ring (ZN p)` by rw[ZN_ring] >>
  rw_tac std_ss[group_def_alt, ZN_property, ring_carriers, excluding_def, IN_DIFF, IN_SING] >-
  decide_tac >-
  rw[EUCLID_LEMMA] >-
  rw[MOD_MULT_ASSOC] >>
  metis_tac[MOD_MULT_INV_EXISTS, MULT_COMM, NOT_ZERO_LT_ZERO]);

(* Theorem: prime n <=> Field (ZN n) *)
(* Proof:
   If part: prime n ==> Field (ZN n)
      This is true                      by ZN_field
   Only-if part: Field (ZN n) ==> prime n
      Note (ZN n).carrier = count n     by ZN_eval
      Thus n <> 0                       by COUNT_0, field_carrier_nonempty
      Also FINITE (count n)             by FINITE_COUNT
      Thus FieldField (ZN n)            by FiniteField_def
       ==> prime (char (ZN n))          by finite_field_char
        or prime n                      by ZN_char, 0 < n
*)
val ZN_field_iff = store_thm(
  "ZN_field_iff",
  ``!n. prime n <=> Field (ZN n)``,
  rw[EQ_IMP_THM] >-
  rw[ZN_field] >>
  `(ZN n).carrier = count n` by rw[ZN_eval] >>
  `n <> 0` by metis_tac[field_carrier_nonempty, COUNT_0] >>
  `FiniteField (ZN n)` by rw[FiniteField_def] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[finite_field_char]);

(* Theorem: prime p ==> FiniteField (ZN p) *)
(* Proof:
   prime p ==> Field (ZN p)    by ZN_field
   With FINITE (ZN p).carrier  by ZN_finite
   This is true                by FiniteField_def
*)
val ZN_finite_field = store_thm(
  "ZN_finite_field",
  ``!p. prime p ==> FiniteField (ZN p)``,
  rw[FiniteField_def, ZN_field, ZN_finite]);

(* Another proof, not based on inverse. *)

(* Theorem: prime p ==> FiniteField (ZN p) *)
(* Proof:
   By finite_field_from_finite_ring, this is to show:
   (1) prime p ==> (if p = 1 then 0 else 1) <> 0
       Note p <> 1              by NOT_PRIME_1
        and 1 <> 0              by arithmetic
   (2) FiniteRing (ZN p)
       Note 0 < p               by PRIME_POS
        ==> FiniteRing (ZN p)   by ZN_finite_ring, 0 < p
   (3) !x y. x < p /\ y < p ==> (((x * y) MOD p = 0) <=> (x = 0) \/ (y = 0))
       If part: (x * y) MOD p = 0 ==> x = 0 \/ y = 0
          Note (x * y) MOD p = 0
           ==> (x MOD p = 0) \/ (y MOD p = 0)       by EUCLID_LEMMA
            or x = 0 \/ y = 0                       by LESS_MOD
       Only-if part: 0 < p ==> (0 * y) MOD p = 0 \/
                     0 < p ==> (x * 0) MOD p = 0
          Note 0 < p /\ 0 * y = 0 ==> 0 MOD p = 0   by MULT, ZERO_MOD
           and 0 < p /\ x * 0 = 0 ==> 0 MOD p = 0   by MULT_0, ZERO_MOD
*)
Theorem ZN_finite_field[allow_rebind]:
  !p. prime p ==> FiniteField (ZN p)
Proof
  rpt strip_tac >>
  (REVERSE (irule finite_field_from_finite_ring >> rpt conj_tac) >>
   simp[ZN_property])
  >- metis_tac[NOT_PRIME_1, ONE_NOT_ZERO]
  >- rw[ZN_finite_ring, PRIME_POS] >>
  rw[EQ_IMP_THM]
  >- metis_tac[EUCLID_LEMMA, LESS_MOD]
  >- rw[] >>
  rw[]
QED

(* Theorem: prime p <=> FiniteField (ZN p) *)
(* Proof:
   If part:
      prime p ==> FiniteField (ZN p)    by ZN_finite_field
   Only-if part:
          FiniteField (ZN p)
      ==> Field (ZN p)         by FiniteField_def
      ==> prime p              by ZN_field_iff
*)
val ZN_finite_field_iff = store_thm(
  "ZN_finite_field_iff",
  ``!p. prime p <=> FiniteField (ZN p)``,
  metis_tac[FiniteField_def, ZN_finite_field, ZN_field_iff]);

(* ------------------------------------------------------------------------- *)
(* ZN and GF Theorems                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (GF m).carrier *)
(* Proof:
   Expand by definitions, this is to show:
   x < n ==> x MOD m < m, true by MOD_LESS.
*)
val ZN_to_GF_element = store_thm(
  "ZN_to_GF_element",
  ``!n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (GF m).carrier``,
  rw[ZN_def, GF_def]);

(* Theorem: 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (GF m).sum *)
(* Proof:
   Note 0 < m                      by ZERO_DIVIDES, 0 < n
   Expand by definitions, this is to show:
      x < n /\ x' < n ==> (x + x') MOD n MOD m = (x MOD m + x' MOD m) MOD m
     (x + x') MOD n MOD m
   = (x + x') MOD m                by DIVIDES_MOD_MOD, 0 < n
   = (x MOD m + x' MOD m) MOD m    by MOD_PLUS, 0 < m
*)
val ZN_to_GF_sum_group_homo = store_thm(
  "ZN_to_GF_sum_group_homo",
  ``!n m. 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (GF m).sum``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[ZN_def, GF_def, GroupHomo_def, DIVIDES_MOD_MOD, MOD_PLUS]);

(* Theorem: 0 < n /\ 1 < m /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (GF m).prod *)
(* Proof:
   Expand by definitions, this is to show:
   (1) 1 < m /\ m divides 1 ==> F
       m divides 1 <=> m = 1   by DIVIDES_ONE
       but 1 < m means m <> 1, hence a contradiction.
   (2) x < n /\ x' < n ==> (x * x') MOD m = (x MOD m * x' MOD m) MOD m
       True by MOD_TIMES2.
   Another proof requires DIVIDES_MOD_MOD:
   (1) ~(1 < m) \/ m <> 1, trivally true.
   (2) x MOD m <> 0 /\ x MOD m < m \/ (x MOD m = 0), true by MOD_LESS.
   (3) x < n /\ x' < n ==> (x * x') MOD n MOD m = (x MOD m * x' MOD m) MOD m
       Since (x * x') MOD n MOD m = (x * x') MOD m  by DIVIDES_MOD_MOD, 0 < n
       True by MOD_TIMES2.
*)
val ZN_to_GF_prod_monoid_homo = store_thm(
  "ZN_to_GF_prod_monoid_homo",
  ``!n m. 0 < n /\ 1 < m /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (GF m).prod``,
  rw[ZN_def, GF_def, MonoidHomo_def, mult_mod_def, times_mod_def, DIVIDES_MOD_MOD, including_def]);

(* Theorem: 0 < n /\ 1 < m /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (GF m) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN (ZN n).carrier ==> x MOD m IN (GF m).carrier, true by ZN_to_GF_element.
   (2) GroupHomo (\x. x MOD m) (ZN n).sum (GF m).sum, true by ZN_to_GF_sum_group_homo.
   (3) MonoidHomo (\x. x MOD m) (ZN n).prod (GF m).prod, true by ZN_to_GF_prod_monoid_homo.
*)
val ZN_to_GF_ring_homo = store_thm(
  "ZN_to_GF_ring_homo",
  ``!n m. 0 < n /\ 1 < m /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (GF m)``,
  rw[RingHomo_def] >| [
    `0 < m` by decide_tac >>
    metis_tac[ZN_to_GF_element],
    rw[ZN_to_GF_sum_group_homo],
    rw[ZN_to_GF_prod_monoid_homo]
  ]);

(* Theorem: 1 < n ==> RingIso (\x. x MOD n) (ZN n) (GF n) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo (\x. x MOD n) (ZN n) (GF n)
       Since 1 < n ==> 0 < n,
         and n divides n   by DIVIDES_REFL
       Hence true          by ZN_to_GF_ring_homo
   (2) BIJ (\x. x MOD n) (ZN n).carrier (GF n).carrier
       Since (ZN n).carrier = count n      by ZN_def
         and (GF n).carrier = {x | x < n}  by GF_def
       After expanding by BIJ_DEF, INJ_DEF, SURJ_DEF,
       it comes down to show: x < n ==> ?x'. x' < n /\ (x' MOD n = x)
       Taking x' = x, this is true         by LESS_MOD
*)
val ZN_to_GF_ring_iso = store_thm(
  "ZN_to_GF_ring_iso",
  ``!n. 1 < n ==> RingIso (\x. x MOD n) (ZN n) (GF n)``,
  rw[RingIso_def] >| [
    `0 < n` by decide_tac >>
    `n divides n` by rw[DIVIDES_REFL] >>
    rw[ZN_to_GF_ring_homo],
    rw[ZN_def, GF_def] >>
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[LESS_MOD]
  ]);

(* Theorem: 1 < n ==> char (GF n) = n *)
(* Proof:
   Since Ring (ZN n)     by ZN_ring
     and Ring (GF n)     by GF_ring
    With RingIso (\x. x MOD n) (ZN n) (GF n)   by ZN_to_GF_ring_iso
         char (GF n)
       = char (ZN n)     by ring_iso_char_eq
       = n               by ZN_char
*)
val GF_char_eq_ZN_char = store_thm(
  "GF_char_eq_ZN_char",
  ``!n. 1 < n ==> (char (GF n) = n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `Ring (GF n)` by rw[GF_ring] >>
  metis_tac[ZN_to_GF_ring_iso, ring_iso_char_eq, ZN_char]);

(* ------------------------------------------------------------------------- *)
(* Multiplicative Inverse in Galois Field.                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p ==> !x. 0 < x /\ x < p ==> (((GF p).prod excluding 0).inv x = (mult_mod p).inv x) *)
(* Proof: by group homomorphism. *)
val GF_mult_inv = store_thm(
  "GF_mult_inv",
  ``!p. prime p ==> !x. 0 < x /\ x < p ==> (((GF p).prod excluding 0).inv x = (mult_mod p).inv x)``,
  rw_tac std_ss[GF_def] >>
  `0 NOTIN (mult_mod p).carrier` by rw_tac std_ss[mult_mod_property] >>
  `x IN (mult_mod p).carrier` by rw_tac std_ss[mult_mod_property, NOT_ZERO_LT_ZERO] >>
  `x IN (mult_mod p including 0 excluding 0).carrier` by rw_tac std_ss[group_including_excluding_property] >>
  `(mult_mod p including 0 excluding 0).op = (mult_mod p).op` by rw_tac std_ss[group_including_excluding_property] >>
  `Group (mult_mod p)` by rw_tac std_ss[mult_mod_group] >>
  `Group (mult_mod p including 0 excluding 0)` by rw_tac std_ss[GSYM group_including_excluding_group] >>
  `GroupHomo I (mult_mod p including 0 excluding 0) (mult_mod p)`
    by rw_tac std_ss[GroupHomo_def, group_including_excluding_property] >>
  `I ((mult_mod p including 0 excluding 0).inv x) = (mult_mod p).inv (I x)` by rw_tac std_ss[group_homo_inv] >>
  full_simp_tac std_ss[]);

(* Theorem: As a function, prime p ==> !x. 0 < x /\ x < p ==> (((GF p).prod excluding 0).inv x = (mult_mod p).inv x) *)
(* Proof: by GF_mult_inv *)
val GF_mult_inv_compute = store_thm(
  "GF_mult_inv_compute",
  ``!p x. ((GF p).prod excluding 0).inv x =
         if (prime p /\ 0 < x /\ x < p) then (mult_mod p).inv x else ((GF p).prod excluding 0).inv x``,
  rw_tac std_ss[GF_mult_inv]);

val _ = computeLib.add_persistent_funs ["GF_mult_inv_compute"];

(*
- EVAL ``(GF 7).sum.op 5 3``;
> val it = |- (GF 7).sum.op 5 3 = 1 : thm
- EVAL ``(GF 7).prod.op 5 3``;
> val it = |- (GF 7).prod.op 5 3 = 1 : thm
- EVAL ``((GF 7).prod excluding 0).op 5 3``;
> val it = |- ((GF 7).prod excluding 0).op 5 3 = 1 : thm
EVAL ``((GF 7).prod excluding 0).inv 5``;

How to know prime 7?
- val _ = computeLib.add_persistent_funs ["PRIME_7"];
- EVAL ``prime 7``;
> val it = |- prime 7 <=> T : thm

*)

(* ------------------------------------------------------------------------- *)
(* Better ways of GF inverse computation.                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (GF p).sum.inv = (add_mod p).inv *)
(* Proof: by GF_def. *)
val GF_sum_inv = store_thm(
  "GF_sum_inv",
  ``!p. (GF p).sum.inv = (add_mod p).inv``,
  rw_tac std_ss[GF_def]);

val _ = computeLib.add_persistent_funs ["GF_sum_inv"];

(* Theorem: (GF p excluding 0).prod.inv = (mult_mod p).inv *)
(* Proof: by GF_def and group_including_excluding_property. *)
val GF_prod_nonzero_inv = store_thm(
  "GF_prod_nonzero_inv",
  ``!p. ((GF p).prod excluding 0).inv = (mult_mod p).inv``,
  rw[GF_def, group_including_excluding_eqn]);

val _ = computeLib.add_persistent_funs["GF_prod_nonzero_inv"];


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
