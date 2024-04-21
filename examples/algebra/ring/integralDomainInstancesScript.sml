(* ------------------------------------------------------------------------- *)
(* Applying Integral Domain Theory: Integral Domain Instances                *)
(* ------------------------------------------------------------------------- *)

(*

Integral Domain Instances
=========================
The most important ones:

Z_p -- Arithmetic under Modulo prime p.
Z   -- Integer Arithmetic

*)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "integralDomainInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory numberTheory;

open monoidTheory groupTheory ringTheory integralDomainTheory;

(* val _ = load "groupInstancesTheory"; *)
open groupInstancesTheory;

(* ------------------------------------------------------------------------- *)
(* Integral Domain Instances Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Integral Domain is a special type of Ring, with data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.
*)
(* Definitions and Theorems (# are exported):

   The Trivial Integral Domain (GF 2):
   trivial_integal_domain_def |- !e0 e1. trivial_integal_domain e0 e1 =
         <|carrier := {e0; e1};
               sum :=  <|carrier := {e0; e1};
                              id := e0;
                              op := (\x y. if x = e0 then y else if y = e0 then x else e0)|>;
              prod := <|carrier := {e0; e1};
                             id := e1;
                             op := (\x y. if x = e0 then e0 else if y = e0 then e0 else e1)|> |>
   trivial_integral_domain    |- !e0 e1. e0 <> e1 ==> FiniteIntegralDomain (trivial_integal_domain e0 e1)

   Multiplication in Modulo of prime p:
   ZP_def                     |- !p. ZP p = <|carrier := count p; sum := add_mod p; prod := times_mod p|>
   ZP_integral_domain         |- !p. prime p ==> IntegralDomain (ZP p)
   ZP_finite                  |- !p. FINITE (ZP p).carrier
   ZP_finite_integral_domain  |- !p. prime p ==> FiniteIntegralDomain (ZP p)
*)
(* ------------------------------------------------------------------------- *)
(* The Trivial Integral Domain = GF(2) = {|0|, |1|}.                         *)
(* ------------------------------------------------------------------------- *)

val trivial_integal_domain_def = zDefine`
  (trivial_integal_domain e0 e1) : 'a ring =
   <| carrier := {e0; e1};
      sum := <| carrier := {e0; e1};
                id := e0;
                op := (\x y. if x = e0 then y
                             else if y = e0 then x
                             else e0) |>;
      prod := <| carrier := {e0; e1};
                id := e1;
                op := (\x y. if x = e0 then e0
                                else if y = e0 then e0
                                else e1) |>
    |>
`;

(* Theorem: {|0|, |1|} is indeed a integral domain. *)
(* Proof: by definition, the integral domain tables are:

   +    |0| |1|          *  |0| |1|
   ------------         -----------
   |0|  |0| |1|         |0| |0| |0|
   |1|  |1| |0|         |1| |0| |1|

*)
val trivial_integral_domain = store_thm(
  "trivial_integral_domain",
  ``!e0 e1. e0 <> e1 ==> FiniteIntegralDomain (trivial_integal_domain e0 e1)``,
  rw_tac std_ss[FiniteIntegralDomain_def] THENL [
    `!x a b. x IN {a; b} <=> ((x = a) \/ (x = b))` by rw[] THEN
    rw_tac std_ss[IntegralDomain_def, Ring_def] THENL [
      rw_tac std_ss[AbelianGroup_def, group_def_alt, trivial_integal_domain_def] THEN
      metis_tac[],
      rw_tac std_ss[AbelianMonoid_def, Monoid_def, trivial_integal_domain_def] THEN
      rw_tac std_ss[],
      rw_tac std_ss[trivial_integal_domain_def],
      rw_tac std_ss[trivial_integal_domain_def],
      (rw_tac std_ss[trivial_integal_domain_def] THEN metis_tac[]),
      rw_tac std_ss[trivial_integal_domain_def],
      rw_tac std_ss[trivial_integal_domain_def]
    ],
    rw[trivial_integal_domain_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Z_p - Multiplication in Modulo of prime p.                                *)
(* ------------------------------------------------------------------------- *)

(* Multiplication in Modulo of prime p *)
val ZP_def = zDefine`
  ZP p :num ring =
   <| carrier := count p;
          sum := add_mod p;
         prod := times_mod p
    |>
`;
(*
- type_of ``ZP p``;
> val it = ``:num ring`` : hol_type
*)

(* Theorem: ZP p is an integral domain for prime p. *)
(* Proof: check definitions.
   The no-zero divisor property is given by EUCLID_LEMMA for prime p.
*)
val ZP_integral_domain = store_thm(
  "ZP_integral_domain",
  ``!p. prime p ==> IntegralDomain (ZP p)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  rw_tac std_ss[IntegralDomain_def, Ring_def] >-
  rw_tac std_ss[ZP_def, add_mod_abelian_group] >-
  rw_tac std_ss[ZP_def, times_mod_abelian_monoid] >-
  rw_tac std_ss[ZP_def, add_mod_def, count_def] >-
  rw_tac std_ss[ZP_def, times_mod_def] >-
 (pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[ZP_def, add_mod_def, times_mod_def, count_def, GSPECIFICATION] >>
  metis_tac[LEFT_ADD_DISTRIB, MOD_PLUS, MOD_TIMES2, LESS_MOD, MOD_MOD]) >-
 (rw_tac std_ss[ZP_def, add_mod_def, times_mod_def] >>
  decide_tac) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[ZP_def, add_mod_def, times_mod_def, count_def, GSPECIFICATION] >>
  rw_tac std_ss[EUCLID_LEMMA, LESS_MOD]);

(* Theorem: (ZP p).carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val ZP_finite = store_thm(
  "ZP_finite",
  ``!p. FINITE (ZP p).carrier``,
  rw[ZP_def]);

(* Theorem: ZP p is a FINITE Integral Domain for prime p. *)
(* Proof: by ZP_integral_domain and ZP_finite. *)
val ZP_finite_integral_domain = store_thm(
  "ZP_finite_integral_domain",
  ``!p. prime p ==> FiniteIntegralDomain (ZP p)``,
  rw_tac std_ss[ZP_integral_domain, ZP_finite, FiniteIntegralDomain_def]);

(* ------------------------------------------------------------------------- *)
(* Integers Z is the prototype Integral Domain.                              *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
