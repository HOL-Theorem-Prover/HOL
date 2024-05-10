(* ------------------------------------------------------------------------- *)
(* Ring Theory -- Ideal and Quotient Ring.                                   *)
(* ------------------------------------------------------------------------- *)

(*

Ideal
=====
additive subgroup with multiplicative closure with all elements.

Quotient Ring
==============
R/I where I is an ideal.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "quotientRing";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory dividesTheory pred_setTheory numberTheory
     combinatoricsTheory;

open monoidTheory groupTheory ringTheory ringIdealTheory;
open groupMapTheory ringMapTheory;

open subgroupTheory;
open quotientGroupTheory;

(* ------------------------------------------------------------------------- *)
(* Quotient Ring Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   R/I     = CosetPartition r.sum i.sum
   gen x   = cogen r.sum i.sum x
   x + y   = ideal_coset_add r i x y
   x * y   = ideal_coset_mult r i x y
   r / i   = quotient_ring r i
*)
(* Definitions and Theorems (# are exported):

   Ideal Coset:
   ideal_coset_add_def      |- !r i x y. x + y = (gen x + gen y) o I
   ideal_coset_mult_def     |- !r i x y. x * y = (gen x * gen y) o I
   ideal_coset_element      |- !r i x. Ring r /\ i << r /\ x IN R ==>
                               !z. z IN x o I <=> ?y. y IN I /\ (z = x + y)

   Quotient Ring:
   quotient_ring_add_def    |- !r i. quotient_ring_add r i = <|carrier := R/I; id := I; op := $+ |>
   quotient_ring_mult_def   |- !r i. quotient_ring_mult r i = <|carrier := R/I; id := #1 o I; op := $* |>
   quotient_ring_def        |- !r i. r / i =
                                         <|carrier := R/I;
                                               sum := quotient_ring_add r i;
                                              prod := quotient_ring_mult r i
                                          |>
   quotient_ring_property   |- !r i. ((r / i).carrier = R/I) /\
                                     ((r / i).sum = quotient_ring_add r i) /\
                                     ((r / i).prod = quotient_ring_mult r i)
   ideal_cogen_property     |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)
   ideal_coset_property     |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)
   ideal_in_quotient_ring   |- !r i. Ring r /\ i << r ==> I IN R/I
   quotient_ring_has_ideal  |- !r i. Ring r /\ i << r ==> I IN R/I
   quotient_ring_element    |- !r i. Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I)
   ideal_coset_has_gen_diff |- !r i. Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I
   ideal_coset_add          |- !r i. Ring r /\ i << r ==>
                               !x y. x IN R /\ y IN R ==> (x o I + y o I = (x + y) o I)
   ideal_coset_mult         |- !r i. Ring r /\ i << r ==>
                               !x y. x IN R /\ y IN R ==> (x o I * y o I = (x * y) o I)
   ideal_coset_neg          |- !r i. Ring r /\ i << r ==> !x. x IN R ==> (x o I + -x o I = I)

   Quotient Ring Addition is a Abelian Group:
   quotient_ring_add_element  |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I
   quotient_ring_add_comm     |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> (x + y = y + x)
   quotient_ring_add_assoc    |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x + y + z = x + (y + z))
   quotient_ring_add_id       |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> (I + x = x)
   quotient_ring_add_inv      |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> ?y. y IN R/I /\ (y + x = I)
   quotient_ring_add_group    |- !r i. Ring r /\ i << r ==> Group (quotient_ring_add r i)
   quotient_ring_add_abelian_group  |- !r. Ring r /\ i << r ==> AbelianGroup (quotient_ring_add r i)

   Quotient Ring Multiplication is an Abelian Monoid:
   quotient_ring_mult_element |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I
   quotient_ring_mult_comm    |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> (x * y = y * x)
   quotient_ring_mult_assoc   |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * y * z = x * (y * z))
   quotient_ring_mult_id      |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> (#1 o I * x = x) /\ (x * #1 o I = x)
   quotient_ring_mult_monoid  |- !r i. Ring r /\ i << r ==> Monoid (quotient_ring_mult r i)
   quotient_ring_mult_abelian_monoid
                              |- !r. Ring r /\ i << r ==> AbelianMonoid (quotient_ring_mult r i)

   Quotient Ring is a Ring:
   quotient_ring_mult_ladd    |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==>
                                 (x * (y + z) = x * y + x * z)
   quotient_ring_ring         |- !r i. Ring r /\ i << r ==> Ring (r / i)
   quotient_ring_ring_sing    |- !r. Ring r ==> ((r / r).carrier = {R})
   quotient_ring_by_principal_ideal
                              |- !r. Ring r ==> !p. p IN R ==> Ring (r / <p>)

   Quotient Ring Homomorphism:
   quotient_ring_homo         |- !r i. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)
   quotient_ring_homo_surj    |- !r i. Ring r /\ i << r ==> SURJ (\x. x o I) R R/I
   quotient_ring_homo_kernel  |- !r i. Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I)

   Kernel of Ring Homomorphism:
   kernel_ideal_def           |- !f r s. kernel_ideal f r s =
                                 <|carrier := kernel f r.sum s.sum;
                                       sum := <|carrier := kernel f r.sum s.sum; op := $+; id := #0|>;
                                      prod := <|carrier := kernel f r.sum s.sum; op := $*; id := #1|>
                                  |>
   kernel_ideal_sum_eqn       |- !r s f. (kernel_ideal f r s).sum = kernel_group f r.sum s.sum
   kernel_ideal_element       |- !r r_ f x. x IN (kernel_ideal f r r_).carrier <=>
                                            x IN r.sum.carrier /\ (f x = #0_)
   ring_homo_kernel_ideal     |- !f r s. Ring r /\ Ring s /\ RingHomo f r s ==> kernel_ideal f r s << r
   quotient_ring_homo_kernel_ideal
                              |- !r i. Ring r /\ i << r ==>
                                       RingHomo (\x. x o I) r (r / i) /\ (kernel_ideal (\x. x o I) r (r / i) = i)

   First Isomorphism Theorem for Ring:
   kernel_ideal_gen_add_map    |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==>
                                   (f (gen ((gen x + gen y) o I)) = f (gen x) +_ f (gen y)))
   kernel_ideal_gen_mult_map   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==>
                                   (f (gen ((gen x * gen y) o I)) = f (gen x) *_ f (gen y)))
   kernel_ideal_gen_id_map     |- !r r_ f. (r ~r~ r_) f ==>
                                  (let i = kernel_ideal f r r_ in f (gen (#1 o I)) = #1_)
   kernel_ideal_quotient_element_eq
                               |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==> (gen x - gen y IN I <=> (x = y)))
   kernel_ideal_quotient_inj   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           INJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_surj  |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           SURJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_bij   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           BIJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_homo  |- !r s f. (r ~r~ s) f ==> (let i = kernel_ideal f r s in
                                          RingHomo (f o gen) (r / i) (ring_homo_image f r s))
   kernel_ideal_quotient_iso   |- !r s f. (r ~r~ s) f ==> (let i = kernel_ideal f r s in
                                          RingIso (f o gen) (r / i) (ring_homo_image f r s))
   ring_first_isomorphism_thm  |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           i << r /\ ring_homo_image f r r_ <= r_ /\
                                           RingIso (f o gen) (r / i) (ring_homo_image f r r_))
*)

(* ------------------------------------------------------------------------- *)
(* Ideal Coset.                                                              *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* Define carrier set of Quotient Ring (R/I) by overloading *)
val _ = overload_on ("R/I", ``CosetPartition r.sum i.sum``);

(* Define cogen operation of Quotient Ring (R/I) by overloading *)
val _ = overload_on ("gen", ``cogen r.sum i.sum``);

(* Define addition of ideal cosets *)
val ideal_coset_add_def = Define`
  ideal_coset_add (r:'a ring) (i:'a ring) x y = (gen x + gen y) o I
`;

(* Define multiplication of ideal cosets *)
val ideal_coset_mult_def = Define`
  ideal_coset_mult (r:'a ring) (i:'a ring) x y = (gen x * gen y) o I
`;

(* Overload operations *)
val _ = overload_on ("+", ``ideal_coset_add r i``);
val _ = overload_on ("*", ``ideal_coset_mult r i``);

(* Export simple definitions *)
val _ = export_rewrites ["ideal_coset_add_def", "ideal_coset_mult_def"];

(*
> in_coset |> ISPEC ``r.sum`` |> ISPEC ``i.sum.carrier`` |> ISPEC ``x``;
val it = |- x IN r.sum.carrier ==>
           !x'. x' IN x o i.sum.carrier <=> ?y. y IN i.sum.carrier /\ (x' = x + y): thm
*)

(* Theorem: Ring r /\ i << r /\ x IN R ==> !z. z IN x o I <=> ?y. y IN I /\ (z = x + y) *)
(* Proof:
     z IN x o I
   = z IN x * i.sum.carrier                  by notation
   = ?y. y IN i.sum.carrier /\ (z = x + y)   by in_coset
   = ?y. y IN I /\ (z = x + y)               by ring_carriers, ideal_carriers
*)
val ideal_coset_element = store_thm(
  "ideal_coset_element",
  ``!(r:'a ring) (i:'a ring) x. Ring r /\ i << r /\ x IN R ==>
   !z. z IN x o I <=> ?y. y IN I /\ (z = x + y)``,
  rw_tac std_ss[in_coset, ring_carriers, ideal_carriers]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define addition group in Quotient Ring (R/I) *)
val quotient_ring_add_def = Define `
  quotient_ring_add (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
            id := I; (* will show: I = #0 o I *)
            op := ideal_coset_add r i
     |>
`;

(* Define multiplication monoid in Quotient Ring (R/I) *)
val quotient_ring_mult_def = Define `
  quotient_ring_mult (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
            id := #1 o I;
            op := ideal_coset_mult r i
     |>
`;

(* Define Quotient Ring (R/I) *)
val quotient_ring_def = Define `
  quotient_ring (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
           sum := quotient_ring_add r i;
          prod := quotient_ring_mult r i
     |>
`;

(* set overloading for Quotient Ring. *)
val _ = overload_on ("/", ``quotient_ring``);

(* Theorem: Properties of quotient ring (r / i). *)
(* Proof: by quotient_ring_def *)
val quotient_ring_property = store_thm(
  "quotient_ring_property",
  ``!r:'a ring i:'a ring.
        ((r / i).carrier = R/I) /\
        ((r / i).sum = quotient_ring_add r i) /\
        ((r / i).prod = quotient_ring_mult r i)``,
  rw[quotient_ring_def]);

(* Theorem: Ring r /\ (i << r) ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x) *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I   by ideal_def
   and r.sum.carrier = R                 by ring_add_group
   Since x IN R/I,
     gen x IN r.sum.carrier              by cogen_element
     gen x o I
   = (cogen r.sum i.sum x) o I           by rewrite of gen
   = x                                   by coset_cogen_property, i.sum <= r.sum
*)
val ideal_cogen_property = store_thm(
  "ideal_cogen_property",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)``,
  metis_tac[ideal_def, ring_add_group, cogen_element, coset_cogen_property]);

(* Theorem: Ring r /\ (i << r) ==> !x. x IN R ==> gen (x o I) + I = x o I  *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I  by ideal_def
   and r.sum.carrier = R                by ring_add_group
   Hence x o I IN R/I                   by coset_partition_element
     gen (x o I) o I
   = gen (coset r.sum x I) o I          by ideal_coset rewrite
   = (coset r.sum x I)                  by coset_cogen_property
   = x o I                              by ideal_coset rewrite
*)
val ideal_coset_property = store_thm(
  "ideal_coset_property",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)``,
  metis_tac[ideal_def, ring_add_group, coset_partition_element, coset_cogen_property]);

(* Theorem: Ring r /\ i << r ==> #0 o I = I *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I     by ideal_def
   and   Group r.sum                       by ring_add_group
   This follows by coset_id_eq_subgroup.
*)
val ideal_coset_zero = store_thm(
  "ideal_coset_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> (#0 o I = I)``,
  metis_tac[ideal_def, coset_id_eq_subgroup, ring_add_group]);

(* Theorem: Ring r /\ i << r ==> I IN R/I *)
(* Proof:
   Since #0 IN R, #0 o I IN R/I by ideal_coset_property.
   Hence true by By ideal_coset_zero.
*)
val ideal_in_quotient_ring = store_thm(
  "ideal_in_quotient_ring",
  ``!r i:'a ring. Ring r /\ i << r ==> I IN R/I``,
  metis_tac[ideal_coset_property, ring_zero_element, ideal_coset_zero]);

(* Theorem alias *)
val quotient_ring_has_ideal = save_thm("quotient_ring_has_ideal", ideal_in_quotient_ring);


(*
ideal_coset_property  |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)
ideal_cogen_property  |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)

> coset_partition_element |> ISPEC ``r.sum`` |> ISPEC ``i.sum``;
val it = |- i.sum <= r.sum ==> !e. e IN R/I <=> ?a. a IN r.sum.carrier /\ (e = a o i.sum.carrier): thm

In textbook, this is written as: (x + I) + (y + I) = (x + y) + I
*)

(* Theorem: Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I) *)
(* Proof:
   If part: z IN R/I ==> ?x. x IN R /\ (z = x o I)
      Note gen z IN R /\ (gen z) o I = z    by ideal_cogen_property
      Take x = gen z, the result is true.
   Only-if part: x IN R /\ (z = x o I) ==> z IN R/I
      This is true                          by ideal_coset_property
*)
val quotient_ring_element = store_thm(
  "quotient_ring_element",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I)``,
  metis_tac[ideal_cogen_property, ideal_coset_property]);

(* Theorem: Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I *)
(* Proof:
   Note x o I IN R/I               by ideal_coset_property
    and gen (x o I) o I = x o I    by ideal_coset_property
   Thus gen (x o I) IN R           by ideal_cogen_property
   Thus gen (x o I) - x IN I       by ideal_coset_eq
*)
val ideal_coset_has_gen_diff = store_thm(
  "ideal_coset_has_gen_diff",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I``,
  rw_tac std_ss[ideal_coset_property, ideal_cogen_property, GSYM ideal_coset_eq]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I) + (y o I) = (x + y) o I) *)
(* Proof:
   Let t = gen (x o I) + gen (y o I).
   Note x o I IN R/I /\ y o I IN R/I           by ideal_coset_property
   Thus gen (x o I) IN R /\ gen (y o I) IN R   by ideal_cogen_property
    and t IN R /\ (x + y) IN R                 by ring_add_element

   Note (x o I) + (y o I) = t o I              by ideal_coset_add_def
    Now gen (x o I) - x IN I                   by ideal_coset_has_gen_diff
    and gen (y o I) - y IN I                   by ideal_coset_has_gen_diff

        t - (x + y)
      = (gen (x o I) + gen (y o I)) - (x + y)  by notation
      = (gen (x o I) - x) + (gen (y o I) - y)  by ring_add_pair_sub
   Thus t - (x + y) IN I                       by ideal_has_sum
     or t o I = (x + y) o I                    by ideal_coset_eq
*)
val ideal_coset_add = store_thm(
  "ideal_coset_add",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==>
   !x y. x IN R /\ y IN R ==> ((x o I) + (y o I) = (x + y) o I)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  qabbrev_tac `t = gen (x o I) + gen (y o I)` >>
  `x o I IN R/I /\ y o I IN R/I` by rw[ideal_coset_property] >>
  `gen (x o I) IN R /\ gen (y o I) IN R` by rw[ideal_cogen_property] >>
  `t IN R /\ x + y IN R` by rw[Abbr`t`] >>
  rw_tac std_ss[ideal_coset_eq] >>
  `t - (x + y) = (gen (x o I) - x) + (gen (y o I) - y)` by rw[ring_add_pair_sub, Abbr`t`] >>
  metis_tac[ideal_coset_has_gen_diff, ideal_has_sum]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I) * (y o I) = (x * y) o I) *)
(* Proof:
   Let t = gen (x o I) * gen (y o I).
   Note x o I IN R/I /\ y o I IN R/I           by ideal_coset_property
   Thus gen (x o I) IN R /\ gen (y o I) IN R   by ideal_cogen_property
    and t IN R /\ (x * y) IN R                 by ring_mult_element

   Note (x o I) * (y o I) = t o I              by ideal_coset_mult_def
    Now gen (x o I) - x IN I                   by ideal_coset_has_gen_diff
    and gen (y o I) - y IN I                   by ideal_coset_has_gen_diff

        t - (x * y)
      = (gen (x o I) * gen (y o I)) - (x * y)  by notation
      = (gen (x o I) - x) * gen (y o I) + x * (gen (y o I) - y)  by ring_mult_pair_diff
      = (gen (x o I) - x) * gen (y o I) + (gen (y o I) - y) * x  by ring_mult_comm
   Note (gen (x o I) - x) * gen (y o I) IN I   by ideal_has_multiple
    and           (gen (y o I) - y) * x IN I   by ideal_has_multiple
   Thus t - (x * y) IN I                       by ideal_has_sum
     or t o I = (x * y) o I                    by ideal_coset_eq
*)
val ideal_coset_mult = store_thm(
  "ideal_coset_mult",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==>
   !x y. x IN R /\ y IN R ==> ((x o I) * (y o I) = (x * y) o I)``,
  rw_tac std_ss[ideal_coset_mult_def] >>
  qabbrev_tac `t = gen (x o I) * gen (y o I)` >>
  `x o I IN R/I /\ y o I IN R/I` by rw[ideal_coset_property] >>
  `gen (x o I) IN R /\ gen (y o I) IN R` by rw[ideal_cogen_property] >>
  `t IN R /\ x * y IN R` by rw[Abbr`t`] >>
  rw_tac std_ss[ideal_coset_eq] >>
  `t - (x * y) = (gen (x o I) - x) * gen (y o I) + x * (gen (y o I) - y)` by rw_tac std_ss[ring_mult_pair_diff, Abbr`t`] >>
  `_ = (gen (x o I) - x) * gen (y o I) + (gen (y o I) - y) * x` by rw_tac std_ss[ring_mult_comm, ring_sub_element] >>
  metis_tac[ideal_coset_has_gen_diff, ideal_has_multiple, ideal_has_sum]);

(* Theorem: Ring r /\ i << r ==> !x. x IN R ==> (x o I + (-x) o I = I) *)
(* Proof:
   Note x IN R ==> -x IN R   by ring_neg_element
     x o I + (-x) o I
   = (x + (-x)) o I          by ideal_coset_add
   = #0 o I                  by ring_add_rneg
   = I                       by ideal_coset_zero
*)
val ideal_coset_neg = store_thm(
  "ideal_coset_neg",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !x. x IN R ==> (x o I + (-x) o I = I)``,
  rw_tac std_ss[ideal_coset_add, ideal_coset_zero, ring_neg_element, ring_add_rneg]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I).sum is an Abelian Group.                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Quotient Ring Add Closure]
   Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I            by ideal_def
   By Ring r, Group r.sum and r.sum.carrier = R   by ring_add_group
     x IN R/I ==> gen x IN r.sum.carrier          by cogen_element
     y IN R/I ==> gen y IN r.sum.carrier          by cogen_element
   Hence  gen x + gen y IN r.sum.carrier          by ring_add_element
      or  (gen x + gen y) o I IN R/I              by coset_partition_element, since i.sum <= r.sum.
*)
val quotient_ring_add_element = store_thm(
  "quotient_ring_add_element",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I``,
  rw[ideal_cogen_property, ideal_coset_property]);

(* Theorem: [Quotient Ring Add Commutative] Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y = y + x *)
(* Proof:
   First, gen x IN R and gen y IN R   by ideal_cogen_property
     x + y
   = (gen x + gen y) o I        by ideal_coset_add_def
   = (gen y + gen x) o I        by ring_add_comm
   = y + x                      by ideal_coset_add_def
*)
val quotient_ring_add_comm = store_thm(
  "quotient_ring_add_comm",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> (x + y = y + x)``,
  rw[ring_add_comm, ideal_cogen_property]);

(* Theorem: Ring r /\ i << r /\ x IN R/I /\ y IN R/I /\ z IN R/I ==> x + y + z = x + (y + z) *)
(* Proof:
   We have gen x IN R, gen y IN R and gen z IN R by ideal_cogen_property.
   Hence gen x + gen y IN R               by ring_add_element
     and gen ((gen x + gen y) o I) IN R   by ideal_coset_property, ideal_cogen_property
    Also gen y + gen z IN R               by ring_add_element
     and gen ((gen y + gen z) o I) IN R   by ideal_coset_property, ideal_cogen_property

   First, show: x + y + z = (gen x + gen y + gen z) o I
   i.e.   x + y + z = (gen ((gen x + gen y) o I) + gen z) o I = (gen x + gen y + gen z) o I
   By ideal_coset_eq, this is true if
         (gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I
   Now   gen ((gen x + gen y) o I) o I = (gen x + gen y) o I   by ideal_coset_property
   hence gen ((gen x + gen y) o I) - (gen x + gen y) IN I      by ideal_coset_eq
   or   (gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I   by ring_sub_pair_reduce
   Hence true.

   Next, show: x + (y + z) = (gen x + (gen y + gen z)) o I
   i.e. (gen x + gen ((gen y + gen z) o I)) o I = (gen x + (gen y + gen z)) o I
   By ideal_coset_eq, this is true if
        (gen x + gen ((gen y + gen z) o I)) - (gen x + (gen y + gen z)) IN I
   Now   gen ((gen y + gen z) o I) o I = (gen y + gen z) o I    by ideal_coset_property
   hence (gen ((gen y + gen z) o I)) - (gen y + gen z) IN I     by ideal_coset_eq
   or    (gen x + gen ((gen y + gen z) o I)) - (gen x + (gen y + gen z)) IN I  by ring_sub_pair_reduce, ring_add_comm
   Hence true.

   Combining,
     x + y + z
   = (gen x + gen y + gen z) o I     by 1st result
   = (gen x + (gen y + gen z)) o I   by ring_add_assoc
   = x + (y + z)                     by 2nd result
*)
val quotient_ring_add_assoc = store_thm(
  "quotient_ring_add_assoc",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x + y + z = x + (y + z))``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `(gen ((gen x + gen y) o I) + gen z) o I = (gen x + gen y + gen z) o I` by
  (`gen x + gen y IN R` by rw[] >>
  `gen ((gen x + gen y) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen x + gen y) o I) - (gen x + gen y) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `(gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I` by rw_tac std_ss[ring_sub_pair_reduce] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  `(gen x + gen ((gen y + gen z) o I)) o I = (gen x + (gen y + gen z)) o I` by
    (`gen y + gen z IN R` by rw[] >>
  `gen ((gen y + gen z) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen y + gen z) o I) - (gen y + gen z) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `gen x + gen ((gen y + gen z) o I) - (gen x + (gen y + gen z)) IN I` by metis_tac[ring_sub_pair_reduce, ring_add_comm] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  rw_tac std_ss[ring_add_assoc]);

(* Theorem: [Quotient Ring Add Identity] Ring r /\ i << r /\ x IN R/I ==> I + x = x *)
(* Proof:
   LHS = I + x = (gen I + gen x) o I        by ideal_coset_add_def
   RHS = x = gen x o I                      by ideal_cogen_property
   Since I IN R/I                           by ideal_in_quotient_ring
         I = gen I o I                      by ideal_cogen_property
   or gen I o I = I = #0 o I                by ideal_coset_zero
   Thus  gen I - #0 IN I                    by ideal_coset_eq
   But (gen I + gen x) - (#0 + gen x)
      = gen I - #0                          by ring_sub_pair_reduce
   Hence (gen I + gen x) - gen x IN I       by ring_add_lzero
   Thus LHS = RHS                           by ideal_coset_eq
*)
val quotient_ring_add_id = store_thm(
  "quotient_ring_add_id",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> (I + x = x)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `I IN R/I` by rw_tac std_ss[ideal_in_quotient_ring] >>
  `gen x IN R /\ gen I IN R /\ (gen x o I = x) /\ (gen I o I = I)` by rw_tac std_ss[ideal_cogen_property] >>
  `I = #0 o I` by rw_tac std_ss[ideal_coset_zero] >>
  `#0 IN R` by rw_tac std_ss[ring_zero_element] >>
  `(gen I + gen x) - gen x = gen I - #0` by metis_tac[ring_sub_pair_reduce, ring_add_lzero] >>
  metis_tac[ideal_coset_eq, ring_add_lzero, ring_add_element]);

(* Theorem: [Quotient Ring Add Inverse] Ring r /\ i << r /\ x IN R/I ==> ?y. y IN R/I /\ (y + x = I) *)
(* Proof:
   Since x IN R/I, gen x IN R        by ideal_cogen_property
            hence -gen x IN R        by ring_neg_element
              and -gen x o I IN R/I  by ideal_coset_property
   Let y = - gen x o I, then y IN R/I, and it remains to show that:
         y + x = I
   or   (- gen x o I) + x = I
   i.e. gen (-gen x o I) + gen x o I = I
   Since #0 o I = I               by coset_id_eq_subgroup
   this is to show: gen (-gen x o I) + gen x o I = #0 o I

   Now  gen (-gen x o I) IN R
    and (gen (-gen x o I) o I = (- gen x) o I)   by ideal_cogen_property
   Hence  gen (-gen x o I) - (- gen x) IN I      by ideal_coset_eq
     gen (-gen x o I) - (- gen x)
   = gen (-gen x o I) + gen x        by ring_sub_def, ring_neg_neg
   = gen (-gen x o I) + gen x - #0   by ring_sub_def, ring_neg_zero, ring_add_rzero, ring_add_element
   i.e. gen (-gen x o I) + gen x - #0 IN I
   Thus true by ideal_coset_eq.
*)
val quotient_ring_add_inv = store_thm(
  "quotient_ring_add_inv",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> ?y. y IN R/I /\ (y + x = I)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `gen x IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `- gen x IN R` by rw_tac std_ss[ring_neg_element] >>
  `- gen x o I IN R/I` by rw_tac std_ss[ideal_coset_property] >>
  qexists_tac `- gen x o I` >>
  rw_tac std_ss[] >>
  `gen (-gen x o I) IN R /\ (gen (-gen x o I) o I = (- gen x) o I)` by rw_tac std_ss[ideal_cogen_property] >>
  `gen (-gen x o I) - (- gen x) IN I` by metis_tac[ideal_coset_eq] >>
  `gen (-gen x o I) - (- gen x) = gen (-gen x o I) + gen x` by rw[] >>
  `_ = gen (-gen x o I) + gen x - #0` by rw[] >>
  `I = #0 o I` by rw_tac std_ss[ideal_coset_zero] >>
  metis_tac[ideal_coset_eq, ring_add_element, ring_zero_element]);

(* Theorem: quotient_ring_add is a Group. *)
(* Proof:
   Check for each group property:
   Closure: by quotient_ring_add_element
   Associative: by quotient_ring_add_assoc
   Identity: by quotient_ring_add_id, and ideal_in_quotient_ring
   Inverse: by quotient_ring_add_inv
*)
val quotient_ring_add_group = store_thm(
  "quotient_ring_add_group",
  ``!r i:'a ring. Ring r /\ (i << r) ==> Group (quotient_ring_add r i)``,
  rw_tac std_ss[group_def_alt, quotient_ring_add_def] >| [
    rw_tac std_ss[quotient_ring_add_element],
    rw_tac std_ss[quotient_ring_add_assoc],
    rw_tac std_ss[ideal_in_quotient_ring],
    rw_tac std_ss[quotient_ring_add_id],
    rw_tac std_ss[quotient_ring_add_inv]
  ]);

(* Theorem: quotient_ring_add is an Abelain Group. *)
(* Proof:
   By quotient_ring_add_group, and quotient_ring_add_comm.
*)
val quotient_ring_add_abelian_group = store_thm(
  "quotient_ring_add_abelian_group",
  ``!r:'a ring. Ring r /\ i << r ==> AbelianGroup (quotient_ring_add r i)``,
  rw_tac std_ss[AbelianGroup_def] >-
  rw_tac std_ss[quotient_ring_add_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[quotient_ring_add_def, quotient_ring_add_comm]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I).prod is an Abelian Monoid.                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Quotient Ring Mult Closure]
   Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I *)
(* Proof:
   Since   x * y = gen x * gen y o I
   and gen x IN R and gen y IN R    by ideal_cogen_property
   This is true by ideal_coset_property, ring_mult_element.
*)
val quotient_ring_mult_element = store_thm(
  "quotient_ring_mult_element",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I``,
  rw[ideal_cogen_property, ideal_coset_property]);

(* Theorem: [Quotient Ring Mult Commutative] Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y = y * x *)
(* Proof:
   We have gen x IN R and gen y IN R    by ideal_cogen_property
     x * y
   = (gen x * gen y) o I     by ideal_coset_mult_def
   = (gen y * gen x) o I     by ring_mult_comm
   = y * x                   by ideal_coset_mult_def
*)
val quotient_ring_mult_comm = store_thm(
  "quotient_ring_mult_comm",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> (x * y = y * x)``,
  rw[ideal_cogen_property, ring_mult_comm]);

(* Theorem: Ring r /\ i << r /\ x IN R/I /\ y IN R/I /\ z IN R/I ==> x * y * z = x * (y * z) *)
(* Proof:
   We have gen x IN R, gen y IN R and gen z IN R by ideal_cogen_property.
   Hence gen x * gen y IN R               by ring_mult_element
     and gen ((gen x * gen y) o I) IN R   by ideal_coset_property, ideal_cogen_property
    Also gen y * gen z IN R               by ring_mult_element
     and gen ((gen y * gen z) o I) IN R   by ideal_coset_property, ideal_cogen_property

   First, show: x * y * z = (gen x * gen y * gen z) o I
   i.e.   x * y * z = (gen ((gen x * gen y) o I) * gen z) o I = (gen x * gen y * gen z) o I
   By ideal_coset_eq, this is true if
         (gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I
   Now   gen ((gen x * gen y) o I) o I = (gen x * gen y) o I   by ideal_coset_property
   hence gen ((gen x * gen y) o I) - (gen x * gen y) IN I      by ideal_coset_eq
   and   gen ((gen x * gen y) o I) - (gen x * gen y) * gen z IN I   by ideal_product_property
   or   (gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I   by ring_mult_lsub
   Hence true.

   Next, show: x * (y * z) = (gen x * (gen y * gen z)) o I
   i.e. (gen x * gen ((gen y * gen z) o I)) o I = (gen x * (gen y * gen z)) o I
   By ideal_coset_eq, this is true if
        (gen x * gen ((gen y * gen z) o I)) - (gen x * (gen y * gen z)) IN I
   Now   gen ((gen y * gen z) o I) o I = (gen y * gen z) o I    by ideal_coset_property
   hence (gen ((gen y * gen z) o I)) - (gen y * gen z) IN I     by ideal_coset_eq
   and   gen x * (gen ((gen y * gen z) o I)) - (gen y * gen z) IN I  by ideal_product_property
   or    (gen x * gen ((gen y + gen z) o I)) - (gen x * (gen y * gen z)) IN I  by ring_mult_rsub
   Hence true.

   Combining,
     x * y * z
   = (gen x * gen y * gen z) o I     by 1st result
   = (gen x * (gen y * gen z)) o I   by ring_mut_assoc
   = x * (y * z)                     by 2nd result
*)
val quotient_ring_mult_assoc = store_thm(
  "quotient_ring_mult_assoc",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * y * z = x * (y * z))``,
  rw_tac std_ss[ideal_coset_mult_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `(gen ((gen x * gen y) o I) * gen z) o I = (gen x * gen y * gen z) o I` by
  (`gen x * gen y IN R` by rw[] >>
  `gen ((gen x * gen y) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen x * gen y) o I) - (gen x * gen y) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `(gen ((gen x * gen y) o I) - (gen x * gen y)) * gen z IN I` by rw_tac std_ss[ideal_product_property] >>
  `(gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I` by rw_tac std_ss[ring_mult_lsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  `(gen x * gen ((gen y * gen z) o I)) o I = (gen x * (gen y * gen z)) o I` by
    (`gen y * gen z IN R` by rw[] >>
  `gen ((gen y * gen z) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen y * gen z) o I) - (gen y * gen z) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `gen x * (gen ((gen y * gen z) o I) - (gen y * gen z)) IN I` by rw_tac std_ss[ideal_product_property] >>
  `gen x * gen ((gen y * gen z) o I) - (gen x * (gen y * gen z)) IN I` by rw_tac std_ss[ring_mult_rsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  rw_tac std_ss[ring_mult_assoc]);

(* Theorem: [Quotient Ring Mult Identity] Ring r /\ i << r ==> !x. x IN R/I ==> ((#1 o I) * x = x) /\ (x * (#1 o I) = x) *)
(* Proof:
   #1 IN R                            by ring_one_element
   #1 o I IN R/I                      by ideal_coset_property
   gen x IN R /\ gen (#1 o I) IN R    by ideal_cogen_property
   and x = gen x o I                  by ideal_cogen_property
   and gen (#1 o I) o I = #1 o I      by ideal_cogen_property
   or  gen (#1 o I) - #1 IN I         by ideal_coset_eq

   Hence this is to show:
        gen (#1 o I) * gen x o I = x = gen x o I
   and  gen x * gen (#1 o I) o I = x = gen x o I

   For the first case:
       gen (#1 o I) - #1 IN I
   ==> (gen (#1 o I) - #1) * gen x IN I        by ideal_product_property
   ==> gen (#1 o I) * gen x - #1 * gen x IN I  by ring_mult_lsub
   ==> gen (#1 o I) * gen x - gen x IN I       by ring_mult_lone
   Hence true by ideal_coset_eq.

   For the second case:
       gen (#1 o I) - #1 IN I
   ==> gen x * (gen (#1 o I) - #1) IN I        by ideal_product_property
   ==> gen x * gen (#1 o I) - gen x * #1 IN I  by ring_mult_rsub
   ==> gen x * gen (#1 o I) - gen x IN I       by ring_mult_rone
   Hence true by ideal_coset_eq.
*)
val quotient_ring_mult_id = store_thm(
  "quotient_ring_mult_id",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> ((#1 o I) * x = x) /\ (x * (#1 o I) = x)``,
  ntac 5 strip_tac >>
  `#1 IN R` by rw[] >>
  `#1 o I IN R/I` by rw_tac std_ss[ideal_coset_property] >>
  `gen x IN R /\ gen (#1 o I) IN R /\ (x = gen x o I) /\ (gen (#1 o I) o I = #1 o I)` by rw_tac std_ss[ideal_cogen_property] >>
  `gen (#1 o I) - #1 IN I` by metis_tac[ideal_coset_eq] >>
  rw_tac std_ss[ideal_coset_mult_def] >| [
    `(gen (#1 o I) - #1) * gen x IN I` by rw_tac std_ss[ideal_product_property] >>
    `gen (#1 o I) * gen x - #1 * gen x IN I` by rw_tac std_ss[ring_mult_lsub] >>
    `gen (#1 o I) * gen x - gen x IN I` by metis_tac[ring_mult_lone],
    `gen x * (gen (#1 o I) - #1) IN I` by rw_tac std_ss[ideal_product_property] >>
    `gen x * gen (#1 o I) - gen x * #1 IN I` by rw_tac std_ss[ring_mult_rsub] >>
    `gen x * gen (#1 o I) - gen x IN I` by metis_tac[ring_mult_rone]
  ] >>
  metis_tac[ideal_coset_eq, ring_mult_element]);

(* Theorem: quotient_ring_mult is a Monoid. *)
(* Proof:
   Check for each monoid property:
   Closure: by quotient_ring_mult_element
   Associative: by quotient_ring_mult_assoc
   Identity: by quotient_ring_mult_id, and ideal_coset_property, ring_one_element
*)
val quotient_ring_mult_monoid = store_thm(
  "quotient_ring_mult_monoid",
  ``!r i:'a ring. Ring r /\ (i << r) ==> Monoid (quotient_ring_mult r i)``,
  rw_tac std_ss[Monoid_def, quotient_ring_mult_def] >| [
    rw_tac std_ss[quotient_ring_mult_element],
    rw_tac std_ss[quotient_ring_mult_assoc],
    rw_tac std_ss[ideal_coset_property, ring_one_element],
    rw_tac std_ss[quotient_ring_mult_id],
    rw_tac std_ss[quotient_ring_mult_id]
  ]);

(* Theorem: quotient_ring_mult is an Abelain Monoid. *)
(* Proof:
   By quotient_ring_mult_monoid, and quotient_ring_mult_comm.
*)
val quotient_ring_mult_abelian_monoid = store_thm(
  "quotient_ring_mult_abelian_monoid",
  ``!r:'a ring. Ring r /\ i << r ==> AbelianMonoid (quotient_ring_mult r i)``,
  rw_tac std_ss[AbelianMonoid_def] >-
  rw_tac std_ss[quotient_ring_mult_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[quotient_ring_mult_def, quotient_ring_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I) is a Ring.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ i << r ==> x * (y + z) = x * y + x * z *)
(* Proof:
   We have gen x IN R, gen y IN R, gen z IN R        by ideal_cogen_property
   Thus    gen y + gen z IN R                        by ring_add_element
   and     gen x * gen y IN R /\ gen x * gen z IN R  by ring_mult_element

   First, show that: (gen x * gen ((gen y + gen z) o I)) o I = (gen x * (gen y + gen z)) o I
   Let t = gen y + gen z, t IN R  by ring_add_element
   Hence t o I IN R/I             by coset_partition_element
   and gen (t o I) IN R           by cogen_element
   Now the goal reduces to: (gen x * gen (t o I)) o I = (gen x * t) o I
   Since gen (t o I) o I = t o I  by ideal_cogen_property
         gen (t o I) - t IN I     by ideal_coset_eq
   hence gen x * (gen (t o I) - t) IN I         by ideal_product_property
      or gen x * gen (t o I) - gen x * t IN I   by ring_mult_rsub
   Hence true by ideal_coset_eq, ring_mult_element.

   Next, show that: (gen ((gen x * gen y) o I) + gen ((gen x * gen z) o I)) o I = (gen x * gen y + gen x * gen z) o I
   Let p = gen x * gen y, p IN R  by ring_mult_element
   Let q = gen x * gen z, q IN R  by ring_mult_element
   Hence gen (p o I) IN R         by ideal_cogen_property
   and   gen (q o I) IN R         by ideal_cogen_property
   Now the goal reduces to: gen (p o I) + gen (q o I) o I = p + q o I
     gen (p o I) + gen (q o I) - (p + q)
   = (gen (p o I) - p) + (gen (q o I) - q)      by ring_add_pair_sub
   Since      gen (p o I) o I = p o I           by ideal_cogen_property
              gen (p o I) - p IN I              by ideal_coset_eq
   Similarly, gen (q o I) o I = q o I           by ideal_cogen_property
              gen (q o I) - q IN I              by ideal_coset_eq
   Now by subgroup_property,
     Group i.sum /\ (!x y. x IN I /\ y IN I ==> (i.sum.op x y = x + y))
   Thus gen (p o I) + gen (q o I) - (p + q) IN I by group_op_element.
   Hence true by ideal_coset_eq, ring_add_element.

   Combining,
     gen x * gen (gen y + gen z o I) o I
   = (gen x * (gen y + gen z)) o I                          by 1st result
   = (gen x * gen y + gen x * gen z) o I                    by ring_mult_radd
   = gen (gen x * gen y o I) + gen (gen x * gen z o I) o I  by 2nd result
*)
val quotient_ring_mult_ladd = store_thm(
  "quotient_ring_mult_ladd",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * (y + z) = x * y + x * z)``,
  rw_tac std_ss[ideal_coset_add_def, ideal_coset_mult_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `gen y + gen z IN R /\ gen x * gen y IN R /\ gen x * gen z IN R` by rw[] >>
  `(gen x * gen ((gen y + gen z) o I)) o I = (gen x * (gen y + gen z)) o I` by
  (qabbrev_tac `t = gen y + gen z` >>
  `gen (t o I) IN R /\ (gen (t o I) o I = t o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (t o I) - t IN I` by metis_tac[ideal_coset_eq] >>
  `gen x * (gen (t o I) - t) IN I` by rw_tac std_ss[ideal_product_property] >>
  `gen x * gen (t o I) - gen x * t IN I` by rw_tac std_ss[ring_mult_rsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  `(gen ((gen x * gen y) o I) + gen ((gen x * gen z) o I)) o I = (gen x * gen y + gen x * gen z) o I` by
    (qabbrev_tac `p = gen x * gen y` >>
  qabbrev_tac `q = gen x * gen z` >>
  `gen (p o I) IN R /\ (gen (p o I) o I = p o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (q o I) IN R /\ (gen (q o I) o I = q o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (p o I) - p IN I` by metis_tac[ideal_coset_eq] >>
  `gen (q o I) - q IN I` by metis_tac[ideal_coset_eq] >>
  `gen (p o I) + gen (q o I) - (p + q) = (gen (p o I) - p) + (gen (q o I) - q)` by rw_tac std_ss[ring_add_pair_sub] >>
  `gen (p o I) + gen (q o I) - (p + q) IN I` by metis_tac[ideal_property] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  rw_tac std_ss[ring_mult_radd]);

(* Theorem: Ring r /\ i << r ==> Ring (r/i) *)
(* Proof:
   Check for each ring property:
   Abelian Sum group: by quotient_ring_add_abelian_group
   Abelian Prod monoid: by quotient_ring_mult_abelian_monoid
   Distribution of sum over product: by quotient_ring_mult_ladd.
*)
val quotient_ring_ring = store_thm(
  "quotient_ring_ring",
  ``!r i:'a ring. Ring r /\ i << r ==> Ring (r / i)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, quotient_ring_def] >| [
    rw_tac std_ss[quotient_ring_add_abelian_group],
    rw_tac std_ss[quotient_ring_mult_abelian_monoid],
    rw_tac std_ss[quotient_ring_add_def],
    rw_tac std_ss[quotient_ring_mult_def],
    rw_tac std_ss[quotient_ring_add_def, quotient_ring_mult_def, quotient_ring_mult_ladd]
  ]);

(* Theorem: (r/r).carrier = {R} *)
(* Proof: by defintions, this is to show:
   (1) x'' IN x /\ !x''. (x'' IN x ==> x'' IN R /\ x'' IN x' o R) ==> x'' IN R
       True by implication.
   (2) x'' IN R /\ !x''. (x'' IN R /\ x'' IN x' o R ==> x'' IN x) ==> x'' IN x
       Since (x'' - x') IN R      by ring_sub_element
       and x'' = x'' - x' + x'    by ring_sub_add
               = x' + (x'' - x')  by ring_add_comm
       True by coset_def
   (3) !x'. (x' IN x ==> x' IN R) /\ (x' IN R ==> x' IN x) ==> ?x'. x' IN R /\ !x''. x'' IN x ==> x'' IN x' o R
       Let x' = #0, then #0 IN R         by ring_zero_element
       and !x''. x'' IN x ==> x'' IN R   by given implication
       Since r << r                      by ideal_refl
          x' o R = #0 o R = R            by ideal_coset_zero
       Hence true.
*)
val quotient_ring_ring_sing = store_thm(
  "quotient_ring_ring_sing",
  ``!r:'a ring. Ring r ==> ((r/r).carrier = {R})``,
  rw[quotient_ring_def, CosetPartition_def, partition_def, inCoset_def, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    metis_tac[],
    `!y z. y IN R /\ z IN R ==> (z = y + (z - y))` by metis_tac[ring_sub_add, ring_add_comm, ring_sub_element] >>
    `!x z. x IN R ==> (z IN x o R <=> ?y. y IN R /\ (z = x + y))` by (rw[coset_def] >> metis_tac[]) >>
    metis_tac[ring_sub_element],
    `#0 IN R /\ (#0 o R = R)` by rw[ideal_coset_zero, ideal_refl] >>
    metis_tac[]
  ]);
(* Michael's proof:
val quotient_ring_ring_sing = store_thm(
  "quotient_ring_ring_sing",
  ``!r:'a ring. Ring r ==> ((r/r).carrier = {R})``,
  rw[quotient_ring_def, CosetPartition_def, partition_def, inCoset_def, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    metis_tac[],
    qcase_tac `y o R` >>
    qcase_tac `_ IN R' ⇒ _` >>
    qcase_tac `z IN R'` >>
    `z = z - y + y` by rw[ring_sub_add] >>
    `_ = y + (z - y)` by rw[ring_add_comm] >>
    `!z. z IN y o R <=> ?y'. y' IN R /\ (z = y + y')` by rw[coset_def] >| [
      metis_tac[],
      metis_tac[ring_sub_element]
    ],
    `#0 IN R` by rw[] >>
    `#0 o R = R` by rw[ideal_coset_zero, ideal_refl] >>
    metis_tac[]
  ]);
*)

(* ------------------------------------------------------------------------- *)
(* Quotient Ring by Principal Ideal                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring (r / <p>) *)
(* Proof:
   by quotient_ring_ring, principal_ideal_ideal.
*)
val quotient_ring_by_principal_ideal = store_thm(
  "quotient_ring_by_principal_ideal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> Ring (r / <p>)``,
  rw[quotient_ring_ring, principal_ideal_ideal]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring Homomorphism                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Ring homomorphism to Quotient Ring] The map: x -> x o I is a homomorphism from R to (R/I). *)
(* Proof:
   This is to show:
   (1) Ring r /\ i << r /\ x IN R ==> x o I IN R/I
       True by ideal_coset_property
   (2) same as (1)
   (3) Ring r /\ i << r /\ x IN R /\ x' IN R ==> (x + x') o I = x o I + x' o I
       By ideal_coset_add_def, this is to show: (x + x') o I = (gen (x o I) + gen (x' o I)) o I
       Now   gen (x o I) IN R /\ gen (x o I) o I = x o I      by ideal_cogen_property, ideal_coset_property
       and   gen (x' o I) IN R /\ gen (x' o I) o I = x' o I   by ideal_cogen_property, ideal_coset_property
       Hence   gen (x o I) - x IN I     by ideal_coset_eq
       and     gen (x' o I) - x' IN I   by ideal_coset_eq
       But     gen (x o I) + gen (x' o I) - (x + x')
             = (gen (x o I) - x) + (gen (x' o I) - x')        by ring_add_pair_sub
       By ideal_property, each component is IN I.
       Hence true by ideal_coset_eq.
   (4) same as (1)
   (5) Ring r /\ i << r /\ x IN R /\ x' IN R ==> (x * x') o I = x o I * x' o I
       By ideal_coset_mult_def, this is to show: (x * x') o I = (gen (x o I) * gen (x' o I)) o I
       gen (x o I) * gen (x' o I) - (x * x')
       = (gen (x o I) - x) * (gen (x' o I) - x') +  (gen (x o I) - x) * x' + x * (gen (x' o I) - x')
             in I               in I                    in I           in R  in R  in I
       By ideal_product_property and ideal_property, each component is IN I.
       Hence true by ideal_coset_eq.
*)
val quotient_ring_homo = store_thm(
  "quotient_ring_homo",
  ``!r i:'a ring. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)``,
  rw_tac std_ss[RingHomo_def, GroupHomo_def, MonoidHomo_def, quotient_ring_def, quotient_ring_add_def, quotient_ring_mult_def, ring_add_group, ring_mult_monoid] >-
  rw_tac std_ss[ideal_coset_property] >-
  rw_tac std_ss[ideal_coset_property] >-
 (rw_tac std_ss[ideal_coset_add_def] >>
  `gen (x o I) - x IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x' o I) - x' IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x o I) IN R /\ gen (x' o I) IN R` by metis_tac[ideal_cogen_property, ideal_coset_property] >>
  `gen (x o I) + gen (x' o I) - (x + x') = (gen (x o I) - x) + (gen (x' o I) - x')`
    by rw_tac std_ss[ring_add_pair_sub] >>
  `gen (x o I) + gen (x' o I) - (x + x') IN I` by metis_tac[ideal_property] >>
  metis_tac[ideal_coset_eq, ring_add_element]) >-
  rw_tac std_ss[ideal_coset_property] >>
  rw_tac std_ss[ideal_coset_mult_def] >>
  `gen (x o I) IN R /\ gen (x' o I) IN R` by metis_tac[ideal_cogen_property, ideal_coset_property] >>
  `gen (x o I) * gen (x' o I) - (x * x') =
   (gen (x o I) - x) * (gen (x' o I) - x') + (gen (x o I) - x) * x' + x * (gen (x' o I) - x')`
     by rw_tac std_ss[ring_mult_pair_sub] >>
  `gen (x o I) - x IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x' o I) - x' IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x o I) * gen (x' o I) - x * x' IN I` by metis_tac[ideal_property, ideal_product_property] >>
  metis_tac[ideal_coset_eq, ring_mult_element]);

(* Theorem: The quotient ring homomorphism is surjective. *)
(* Proof: by SURJ_DEF, this is to show:
   (1) x IN R ==> x o I IN R/I
       True by ideal_coset_property
   (2) x IN R/I ==> ?x'. x' IN R /\ (x' o I = x)
       Since  i.sum <= r.sum   by ideal_def
       r.sum.carrier = R       by Ring_def
       i.sum.carrier = I       by ideal_def
       True by coset_partition_element.
*)
val quotient_ring_homo_surj = store_thm(
  "quotient_ring_homo_surj",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> SURJ (\x. x o I) R R/I``,
  rw[SURJ_DEF] >| [
    rw[ideal_coset_property],
    `i.sum <= r.sum` by metis_tac[ideal_def] >>
    `r.sum.carrier = R` by rw[] >>
    `i.sum.carrier = I` by metis_tac[ideal_def] >>
    metis_tac[coset_partition_element]
  ]);

(* Theorem: In the ring homomorphism x -> x o I, its kernel = I *)
(* Proof:
   This is to show: {x | x IN R /\ (x o I = I)} = I
   If x IN R /\ (x o I = I),
      Since I = #0 o I       by ideal_coset_zero
      we have x o I = #0 o I
      or  x - #0 IN I        by ideal_coset_eq
      i.e. x IN I            by ring_sub_zero
   If x IN I
      then x IN R            by ideal_element_property
      and since x - #0 IN I  by ring_sub_zero
      x o I = #0 o I         by ideal_coset_eq
            = I              by ideal_coset_zero
*)
val quotient_ring_homo_kernel = store_thm(
  "quotient_ring_homo_kernel",
  ``!r i:'a ring. Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I)``,
  rw_tac std_ss[kernel_def, preimage_def, quotient_ring_def, quotient_ring_add_def, ring_add_group] >>
  `#0 o I = I` by rw_tac std_ss[ideal_coset_zero] >>
  rw[Once EXTENSION, EQ_IMP_THM] >| [
    metis_tac[ideal_coset_eq, ring_zero_element, ring_sub_zero],
    metis_tac[ideal_element_property],
    metis_tac[ideal_coset_eq, ring_sub_zero, ideal_element_property, ring_zero_element]
  ]);

(* ------------------------------------------------------------------------- *)
(* Kernel of Ring Homomorphism.                                              *)
(* ------------------------------------------------------------------------- *)

(* Define the Kernel Ideal of a ring homomorphism. *)
val kernel_ideal_def = Define`
  kernel_ideal f (r:'a ring) (s:'b ring) =
    <| carrier := kernel f r.sum s.sum;  (* e.g. s = r / i *)
           sum := <| carrier := kernel f r.sum s.sum; op := r.sum.op; id := r.sum.id |>;
          prod := <| carrier := kernel f r.sum s.sum; op := r.prod.op; id := r.prod.id |>
     |>`;

(* Theorem: (kernel_ideal f r s).sum = kernel_group f r.sum s.sum *)
(* Proof: kernel_ideal_def, kernel_group_def *)
val kernel_ideal_sum_eqn = store_thm(
  "kernel_ideal_sum_eqn",
  ``!(r:'a ring) (s:'b ring) f. (kernel_ideal f r s).sum = kernel_group f r.sum s.sum``,
  rw_tac std_ss[kernel_ideal_def, kernel_group_def]);

(* Theorem: x IN (kernel_ideal f r r_).carrier <=> x IN r.sum.carrier /\ (f x = #0_) *)
(* Proof:
       x IN (kernel_ideal f r r_).carrier
   <=> x IN kernel f r.sum r_.sum           by kernel_ideal_def
   <=> x IN preimage f r.sum.carrier #0_    by kernel_def
   <=> x IN r.sum.carrier /\ (f x = #0_)    by in_preimage
*)
val kernel_ideal_element = store_thm(
  "kernel_ideal_element",
  ``!(r:'a ring) (r_:'b ring) f x.
     x IN (kernel_ideal f r r_).carrier <=> x IN r.sum.carrier /\ (f x = #0_)``,
  rw_tac std_ss[kernel_ideal_def, kernel_def, in_preimage]);

(*
CONJ_ASM1_TAC      A ==> B /\ C  to A ==> B,  A /\ B ==> C
CONJ_ASM2_TAC      A ==> B /\ C  to A ==> C,  A /\ C ==> B
*)

(* Theorem: If f is a Ring homomorphism, kernel_ideal is an ideal. *)
(* Proof:
   Ring r, s ==> Group r.sum /\ Group s.sum     by ring_add_group
   RingHomo f r s ==> GroupHomo f r.sum s.sum   by RingHomo_def
   This is to show:
   (1) <|carrier := kernel f r.sum s.sum; op := $+; id := #0|> <= r.sum
       This splits into two:
       the first one is: Group <|carrier := kernel f r.sum s.sum; op := $+; id := #0|>
       This reduces to 7 subgoals:
       1. x IN R /\ y IN R ==> x + y IN R     true by ring_add_element
       2. f x = s.sum.id /\ f y = s.sum.id ==> f (x + y) = s.sum.id
          Since   f (x + y) = s.sum.op (f x) (f y))   by GroupHomo_def
          Hence true by group_id_id.
       3. x IN R /\ y IN R /\ z IN R ==> x + y + z = x + (y + z)   true by ring_add_assoc
       4. #0 IN R     true by ring_zero_element
       5. f #0 = s.sum.id
          Since  f (x + y) = s.sum.op (f x) (f y))   by GroupHomo_def, RingHomo_def, ring_add_group
          Using group_id_id,  f #0 = f (#0 + #0) = s.sum.op (f #0) (f #0)
          Hence f #0 = s.sum.id      by group_id_fix
       6. x IN R ==> #0 + x = x      true by ring_add_lzero
       7. x IN R /\ f x = s.sum.id ==> ?y. (y IN R /\ (f y = s.sum.id)) /\ (y + x = #0)
          x IN R ==> -x IN R         by ring_neg_element
          Let y = -x, then y IN R, and y + x = #0   by ring_add_lneg
          f y = s.sum.op ((f y) s.sum.id)      by group_rid
              = s.sum.op ((f y) (f x))         by given
              = f (y + x)                      by GroupHomo_def
              = f #0                           by above
              = s.sum.id                       by 5.
       The second is: kernel f r.sum s.sum SUBSET R
       True by kernel_def.
   (2) x IN kernel f r.sum s.sum /\ y IN R ==> x * y IN kernel f r.sum s.sum
       This reduces to 2 subgoals:
       1. x IN kernel f r.sum s.sum /\ y IN R ==> x * y IN R
          Since   kernel f r.sum s.sum SUBSET R  by (2)
          This is true by ring_mult_element and SUBSET_DEF.
       2. x IN kernel f r.sum s.sum /\ y IN R ==> f (x * y) = s.sum.id
          Since x IN kernel f r.sum s.sum, f x = s.sum.id    by kernel_def
          f (x * y) = s.prod.op (s.sum.id) (f y)             by MonoidHomo_def
                    = s.sum.id                               by ring_mult_lzero
   (3) x IN kernel f r.sum s.sum /\ y IN R ==> y * x IN kernel f r.sum s.sum
       Since kernel f r.sum s.sum SUBSET R     by kernel_def
       x IN R                                  by SUBSET_DEF
       Hence this follows from (2) by ring_mult_comm.
*)
val ring_homo_kernel_ideal = store_thm(
  "ring_homo_kernel_ideal",
  ``!f (r:'a ring) (s:'b ring). Ring r /\ Ring s /\ RingHomo f r s ==> kernel_ideal f r s << r``,
  rpt strip_tac >>
  `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
  `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
  `Group r.sum /\ Group s.sum /\ (r.sum.carrier = R) /\ (s.sum.carrier = s.carrier)` by rw_tac std_ss[ring_add_group] >>
  `Monoid r.prod /\ Monoid s.prod /\ (r.prod.carrier = R) /\ (s.prod.carrier = s.carrier)` by rw_tac std_ss[ring_mult_monoid] >>
  rw_tac std_ss[kernel_ideal_def, ideal_def] >| [
    rw_tac std_ss[Subgroup_def] >| [
      rw_tac std_ss[group_def_alt, kernel_def, preimage_def, GSPECIFICATION] >-
      rw_tac std_ss[ring_add_element] >-
      metis_tac[GroupHomo_def, group_id_id] >-
      rw_tac std_ss[ring_add_assoc] >-
      rw_tac std_ss[ring_zero_element] >-
      metis_tac[GroupHomo_def, group_id_id, group_id_fix, ring_zero_element] >-
      rw_tac std_ss[ring_add_lzero] >>
      `-x IN R /\ (-x + x = #0)` by rw_tac std_ss[ring_neg_element, ring_add_lneg] >>
      qexists_tac `-x` >>
      rw_tac std_ss[] >>
      metis_tac[GroupHomo_def, group_id_id, group_id_fix, ring_zero_element, ring_add_lneg, group_rid],
      rw[kernel_def, preimage_def, SUBSET_DEF]
    ],
    `kernel f r.sum s.sum SUBSET R` by rw[kernel_def, preimage_def, SUBSET_DEF] >>
    rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >-
    metis_tac[SUBSET_DEF, ring_mult_element] >>
    `x IN R` by metis_tac[SUBSET_DEF] >>
    `!x. x IN kernel f r.sum s.sum ==> (f x = s.sum.id)` by rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >>
    metis_tac[MonoidHomo_def, ring_mult_monoid, ring_mult_lzero],
    `kernel f r.sum s.sum SUBSET R` by rw[kernel_def, preimage_def, SUBSET_DEF] >>
    rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >-
    metis_tac[SUBSET_DEF, ring_mult_element] >>
    `x IN R` by metis_tac[SUBSET_DEF] >>
    `!x. x IN kernel f r.sum s.sum ==> (f x = s.sum.id)` by rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >>
    metis_tac[MonoidHomo_def, ring_mult_monoid, ring_mult_rzero]
  ]);

(* Theorem: Any ideal will induce a ring homomorphism f from r to (r / i) such that kernel_ideal f = i *)
(* Proof:
   We have shown: Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)   by quotient_ring_homo
   And we have: Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I  by quotient_ring_homo_kernel
   The remaining cases are:
   (1) <|carrier := kernel (\x. x o I) r.sum (r / i).sum; op := $+; id := #0|> = i.sum
       kernel (\x. x o I) r.sum (r / i).sum = I    by quotient_ring_homo_kernel
       i.sum.carrier = I                           by ideal_def
       i.sum.op = r.sum.op                         by ideal_ops
       i.sum.id = #0                               by subgroup_id
       Hence true by monoid_component_equality.
   (2) <|carrier := kernel (\x. x o I) r.sum (r / i).sum; op := $*; id := #1|> = i.prod
       kernel (\x. x o I) r.sum (r / i).sum = I    by quotient_ring_homo_kernel
       i.prod.carrier = I                          by ideal_def
       i.prod.op = r.prod.op                       by ideal_def
       i.prod.id = #1                              by ideal_def

*)
val quotient_ring_homo_kernel_ideal = store_thm(
  "quotient_ring_homo_kernel_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i) /\ (kernel_ideal (\x. x o I) r (r / i) = i)``,
  rw_tac std_ss[quotient_ring_homo] >>
  rw_tac std_ss[kernel_ideal_def] >>
  `kernel (\x. x o I) r.sum (r / i).sum = I` by rw_tac std_ss[quotient_ring_homo_kernel] >>
  rw_tac std_ss[ring_component_equality] >| [
    `i.sum <= r.sum /\ (i.sum.carrier = I) /\ (i.sum.op = r.sum.op)` by metis_tac[ideal_def, ideal_ops] >>
    `i.sum.id = #0` by rw_tac std_ss[subgroup_id],
    `(i.prod.carrier = I) /\ (i.prod.op = r.prod.op) /\ (i.prod.id = #1)` by metis_tac[ideal_def]
  ] >>
  rw_tac std_ss[monoid_component_equality]);

(* ------------------------------------------------------------------------- *)
(* First Isomorphism Theorem for Ring.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x + gen y) o I)) = (f (gen x)) +_ (f (gen y))) *)
(* Proof:
   Let t = gen x + gen y.
   The goal becomes: f (gen (t o I)) = f (gen x) +_ f (gen y)
   Note i << r                           by ring_homo_kernel_ideal
    ==> gen x IN R /\ gen y IN R         by ideal_cogen_property
     so t IN R                           by ring_add_element
    ==> t o I IN R/I                     by ideal_coset_property, t IN R
     so gen (t o I) IN R                 by ideal_cogen_property
   Thus f (gen (t o I)) IN R_            by ring_homo_element
    and f (gen x) IN R_                  by ring_homo_element
    and f (gen y) IN R_                  by ring_homo_element
     so (f (gen x) +_ f (gen y)) IN R_   by ring_add_element

   Note gen (t o I) - t IN I             by ideal_coset_has_gen_diff

        f (gen (t o I)) -_ (f (gen x) +_ f (gen y))
      = f (gen (t o I)) -_ (f t)         by ring_homo_add
      = f (gen (t o I) - t)              by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (t o I)) = f (gen x) +_ f (gen y)   by ring_sub_eq_zero
*)
val kernel_ideal_gen_add_map = store_thm(
  "kernel_ideal_gen_add_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x + gen y) o I)) = (f (gen x)) +_ (f (gen y)))``,
  rw_tac std_ss[] >>
  qabbrev_tac `t = gen x + gen y` >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `t IN R` by rw[Abbr`t`] >>
  `t o I IN R/I` by rw[ideal_coset_property] >>
  `gen (t o I) IN R` by rw[ideal_cogen_property] >>
  `f (gen (t o I)) IN R_ /\ f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `(f (gen x) +_ f (gen y)) IN R_` by rw[] >>
  `gen (t o I) - t IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (t o I)) -_ (f (gen x) +_ f (gen y)) = f (gen (t o I)) -_ f t` by metis_tac[ring_homo_add] >>
  `_ = f (gen (t o I) - t)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x * gen y) o I)) = (f (gen x)) *_ (f (gen y))) *)
(* Proof:
   Let t = gen x * gen y.
   The goal becomes: f (gen (t o I)) = f (gen x) *_ f (gen y)
   Note i << r                           by ring_homo_kernel_ideal
    ==> gen x IN R /\ gen y IN R         by ideal_cogen_property
     so t IN R                           by ring_add_element
    ==> t o I IN R/I                     by ideal_coset_property, t IN R
     so gen (t o I) IN R                 by ideal_cogen_property
   Thus f (gen (t o I)) IN R_            by ring_homo_element
    and f (gen x) IN R_                  by ring_homo_element
    and f (gen y) IN R_                  by ring_homo_element
     so (f (gen x) *_ f (gen y)) IN R_   by ring_mult_element

   Note gen (t o I) - t IN I             by ideal_coset_has_gen_diff

        f (gen (t o I)) -_ (f (gen x) *_ f (gen y))
      = f (gen (t o I)) -_ (f t)         by ring_homo_mult
      = f (gen (t o I) - t)              by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (t o I)) = f (gen x) *_ f (gen y)   by ring_sub_eq_zero
*)
val kernel_ideal_gen_mult_map = store_thm(
  "kernel_ideal_gen_mult_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x * gen y) o I)) = (f (gen x)) *_ (f (gen y)))``,
  rw_tac std_ss[] >>
  qabbrev_tac `t = gen x * gen y` >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `t IN R` by rw[Abbr`t`] >>
  `t o I IN R/I` by rw[ideal_coset_property] >>
  `gen (t o I) IN R` by rw[ideal_cogen_property] >>
  `f (gen (t o I)) IN R_ /\ f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `(f (gen x) *_ f (gen y)) IN R_` by rw[] >>
  `gen (t o I) - t IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (t o I)) -_ (f (gen x) *_ f (gen y)) = f (gen (t o I)) -_ f t` by metis_tac[ring_homo_mult] >>
  `_ = f (gen (t o I) - t)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen (#1 o I)) = #1_) *)
(* Proof:
   Note i << r                           by ring_homo_kernel_ideal
    and #1 IN R /\ #1_ IN R_             by ring_add_element
    ==> #1 o I IN R/I                    by ideal_coset_property, #1 IN R
     so gen (#1 o I) IN R                by ideal_cogen_property
   Thus f (gen (#1 o I)) IN R_           by ring_homo_element

   Note gen (#1 o I) - #1 IN I           by ideal_coset_has_gen_diff

        f (gen (#1 o I)) -_ #1_
      = f (gen (#1 o I)) -_ (f #1)       by ring_homo_ids
      = f (gen (#1 o I) - #1)            by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (#1 o I)) = #1_           by ring_sub_eq_zero
*)
val kernel_ideal_gen_id_map = store_thm(
  "kernel_ideal_gen_id_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in f (gen (#1 o I)) = #1_``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `#1 IN R /\ #1_ IN R_` by rw[] >>
  `#1 o I IN R/I` by rw[ideal_coset_property] >>
  `gen (#1 o I) IN R` by rw[ideal_cogen_property] >>
  `gen (#1 o I) - #1 IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (#1 o I)) IN R_` by metis_tac[ring_homo_element] >>
  `f (gen (#1 o I)) -_ #1_ = f (gen (#1 o I)) -_ f #1` by metis_tac[ring_homo_ids] >>
  `_ = f (gen (#1 o I) - #1)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> ((gen x - gen y) IN I <=> (x = y)) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                          by ring_homo_kernel_ideal, (r ~r~ s) f
    ==> gen x IN R /\ (gen x o I = x)   by ideal_cogen_property
    and gen y IN R /\ (gen y o I = y)   by ideal_cogen_property
   If part: (gen x - gen y) IN I ==> (x = y)
      By EXTENSION, this is to show:
      (1) z IN x ==> z IN y
          Note z IN (gen x) o I                by above
           ==> ?u. u IN I /\ (z = gen x + u)   by ideal_coset_element
            so u IN R                          by ideal_element_property
               z = gen x + u
                 = gen x + #0 + u                    by ring_add_rzero
                 = gen x + (-(gen y) + gen y) + u    by ring_add_lneg
                 = (gen x - gen y) + gen y + u       by ring_add_assoc
                 = gen y + (gen x - gen y) + u       by ring_add_comm
                 = gen y + ((gen x - gen y) + u)     by ring_add_assoc, ring_sub_element
           Now (gen x - gen y) + u IN I              by ideal_has_sum
          Thus z IN y                                by ideal_coset_element
      (2) z IN y ==> z IN x
          Note z IN (gen y) o I                by above
           ==> ?v. v IN I /\ (z = gen y + v)   by ideal_coset_element
            so v IN R                          by ideal_element_property
               z = gen x + u
                 = gen y + #0 + v                    by ring_add_rzero
                 = gen y + (-(gen x) + gen x) + v    by ring_add_lneg
                 = (gen y - gen x) + gen x + v       by ring_add_assoc
                 = gen x + (gen y - gen x) + v       by ring_add_comm
                 = gen x + ((gen y - gen x) + v)     by ring_add_assoc, ring_sub_element
                 = gen x + (-(gen x - gen y) + v)    by ring_neg_sub
           Now -(gen x - gen y) IN I                 by ideal_has_neg
            so -(gen x - gen y) + v IN I             by ideal_has_sum
           Thus z IN x                               by ideal_coset_element
   Only-if part: (x = y) ==> (gen x - gen y) IN I
      Note gen x - gen y = gen x - gen x       by x = y
                         = #0                  by ring_sub_eq_zero
       and #0 IN I                             by ideal_has_zero
*)
val kernel_ideal_quotient_element_eq = store_thm(
  "kernel_ideal_quotient_element_eq",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
   !x y. x IN R/I /\ y IN R/I ==> ((gen x - gen y) IN I <=> (x = y))``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ (gen x o I = x)` by rw[ideal_cogen_property] >>
  `gen y IN R /\ (gen y o I = y)` by rw[ideal_cogen_property] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?u. u IN I /\ (x' = gen x + u)` by rw[GSYM ideal_coset_element] >>
      `_ = gen x + #0 + u` by rw[] >>
      `_ = gen x + (-(gen y) + gen y) + u` by rw[] >>
      `_ = (gen x - gen y) + gen y + u` by rw[ring_add_assoc] >>
      `_ = gen y + (gen x - gen y) + u` by rw[ring_add_comm] >>
      `_ = gen y + ((gen x - gen y) + u)` by prove_tac[ring_add_assoc, ring_sub_element, ideal_element_property] >>
      metis_tac[ideal_coset_element, ideal_has_sum],
      `?v. v IN I /\ (x' = gen y + v)` by rw[GSYM ideal_coset_element] >>
      `_ = gen y + #0 + v` by rw[] >>
      `_ = gen y + (-(gen x) + gen x) + v` by rw[] >>
      `_ = (gen y - gen x) + gen x + v` by rw[ring_add_assoc] >>
      `_ = gen x + (gen y - gen x) + v` by rw[ring_add_comm] >>
      `_ = gen x + ((gen y - gen x) + v)` by prove_tac[ring_add_assoc, ring_sub_element, ideal_element_property] >>
      `_ = gen x + (-(gen x - gen y) + v)` by rw[ring_neg_sub] >>
      metis_tac[ideal_coset_element, ideal_has_sum, ideal_has_neg]
    ],
    `gen x - gen x = #0` by rw[] >>
    metis_tac[ideal_has_zero]
  ]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in INJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                         by ring_homo_kernel_ideal, (r ~r~ r_) f
   By INJ_DEF, this is to show:
   (1) x IN R/I ==> f (gen x) IN IMAGE f R
       Note gen x IN R                 by ideal_cogen_property
       Thus f (gen x) IN IMAGE f R     by IN_IMAGE
   (2) x IN R/I /\ y IN R/I /\ (f (gen x) = f (gen y)) ==> (x = y)
       Note gen x IN R /\ gen y IN R   by ideal_cogen_property
       Thus gen x - gen y IN R         by ring_sub_element
       also r.sum.carrier = R          by ring_carriers
       Note f (gen x) IN R_            by ring_homo_element
        and f (gen y) IN R_            by ring_homo_element
            f (gen x - gen y)
          = f (gen x) -_ f (gen y)     by ring_homo_sub
          = f (gen x) -_ f (gen x)     by f (gen x) = f (gen y)
          = #0_                        by ring_sub_eq_zero
       Thus (gen x - gen y) IN I       by kernel_ideal_element
        ==> x = y                      by kernel_ideal_quotient_element_eq
*)
val kernel_ideal_quotient_inj = store_thm(
  "kernel_ideal_quotient_inj",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
     let i = kernel_ideal f r r_ in INJ (f o gen) R/I (IMAGE f R)``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  rw_tac std_ss[INJ_DEF] >-
  rw[ideal_cogen_property] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `gen x - gen y IN R /\ (r.sum.carrier = R)` by rw[] >>
  `f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `f (gen x - gen y) = #0_` by metis_tac[ring_homo_sub, ring_sub_eq_zero] >>
  `(gen x - gen y) IN I` by rw[kernel_ideal_element, Abbr`i`] >>
  metis_tac[kernel_ideal_quotient_element_eq]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in SURJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                         by ring_homo_kernel_ideal, (r ~r~ r_) f
   By SURJ_DEF, this is to show:
   (1) x IN R/I ==> f (gen x) IN IMAGE f R
       Note gen x IN R                 by ideal_cogen_property
       Thus f (gen x) IN IMAGE f R     by IN_IMAGE
   (2) x IN IMAGE f R ==> ?y. y IN R/I /\ (f (gen y) = x)
       Note ?z. (x = f z) /\ z IN R    by IN_IMAGE
       Thus z o I IN R/I               by ideal_coset_property
        ==> gen (z o I) IN R           by ideal_cogen_property
       Note gen (z o I) - z IN I       by ideal_coset_has_gen_diff, z IN R
        ==> #0_ = f (gen (z o I) - z)       by kernel_ideal_element
                = f (gen (z o I)) -_ f z    by ring_homo_sub
        ==> f (gen (z o I)) = f z           by ring_sub_eq_zero, ring_homo_element
       Take y = z o I, the result follows.
*)
val kernel_ideal_quotient_surj = store_thm(
  "kernel_ideal_quotient_surj",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
     let i = kernel_ideal f r r_ in SURJ (f o gen) R/I (IMAGE f R)``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  rw_tac std_ss[SURJ_DEF] >-
  rw[ideal_cogen_property] >>
  `?z. (x = f z) /\ z IN R` by rw[GSYM IN_IMAGE] >>
  `z o I IN R/I` by rw[ideal_coset_property] >>
  `gen (z o I) IN R` by rw[ideal_cogen_property] >>
  `gen (z o I) - z IN I` by rw[ideal_coset_has_gen_diff] >>
  `#0_ = f (gen (z o I) - z)` by metis_tac[kernel_ideal_element] >>
  `_ = f (gen (z o I)) -_ f z` by rw[ring_homo_sub] >>
  prove_tac[ring_sub_eq_zero, ring_homo_element]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in BIJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (f o gen) R/I (IMAGE f R)
       This is true by kernel_ideal_quotient_inj
   (2) SURJ (f o gen) R/I (IMAGE f R)
       This is true by kernel_ideal_quotient_surj
*)
val kernel_ideal_quotient_bij = store_thm(
  "kernel_ideal_quotient_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
    let i = kernel_ideal f r r_ in BIJ (f o gen) R/I (IMAGE f R)``,
  metis_tac[BIJ_DEF, kernel_ideal_quotient_inj, kernel_ideal_quotient_surj]);

(* Theorem: (r ~r~ s) f ==>
            let i = kernel_ideal f r s in RingHomo (f o gen) (r / i) (ring_homo_image f r s) *)
(* Proof:
   Let i = kernel_ideal f r s, r_ = ring_homo_image f r s.
   The goal is to show: RingHomo (f o gen) (r / i) r_
   Note Ring r_              by ring_homo_image_ring, by (r ~r~ s) f
    and i << r               by ring_homo_kernel_ideal, by (r ~r~ s) f
    ==> Ring (r / i)         by quotient_ring_ring, i << r

   Claim: !x. x IN (r / i).carrier ==> f (gen x) IN R_
   Proof: By quotient_ring_def, ring_homo_image_def, this is to show:
          !x. x IN R/I ==> ?z. (f (gen x) = f z) /\ z IN R
          Note x IN R/I ==> gen x IN R           by ideal_cogen_property
          Take z = gen x, the result is true.

   By RingHomo_def, this is to show:
   (1) x IN (r / i).carrier ==> f (gen x) IN R_, true by Claim.
   (2) GroupHomo (f o gen) (r / i).sum r_.sum
       By GroupHomo_def, ring_carriers, this is to show:
          x IN (r / i).carrier /\ y IN (r / i).carrier ==>
          f (gen ((r / i).sum.op x y)) = f (gen x) +_ f (gen y)
       By quotient_ring_def, quotient_ring_add_def, ring_homo_image_def, homo_image_def,
       the goal is:
           x IN R/I /\ y IN R/I ==> f (gen ((gen x + gen y) o I)) = s.sum.op (f (gen x)) (f (gen y))
       This is true by kernel_ideal_gen_add_map.
   (3) MonoidHomo (f o gen) (r / i).prod r_.prod
       By MonoidHomo_def, ring_carriers, this is to show:
       (1) x IN (r / i).carrier /\ y IN (r / i).carrier ==>
           f (gen ((r / i).prod.op x y)) = f (gen x) *_ f (gen y)
           By quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def,
           the goal is:
               x IN R/I /\ y IN R/I ==> f (gen ((gen x * gen y) o I)) = s.prod.op (f (gen x)) (f (gen y))
           This is true by kernel_ideal_gen_mult_map.
       (2) f (gen (r / i).prod.id) = #1_
           By quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def,
           the goal is: f (gen (#1 o I)) = s.prod.id
           This is true by kernel_ideal_gen_id_map.
*)
val kernel_ideal_quotient_homo = store_thm(
  "kernel_ideal_quotient_homo",
  ``!(r:'a ring) (s:'b ring) f. (r ~r~ s) f ==>
   let i = kernel_ideal f r s in RingHomo (f o gen) (r / i) (ring_homo_image f r s)``,
  rw_tac std_ss[] >>
  qabbrev_tac `r_ = ring_homo_image f r s` >>
  `Ring r_` by rw[ring_homo_image_ring, Abbr`r_`] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `Ring (r / i)` by rw[quotient_ring_ring] >>
  `!x. x IN (r / i).carrier ==> f (gen x) IN R_` by
  (fs[quotient_ring_def, ring_homo_image_def, Abbr`r_`] >>
  metis_tac[ideal_cogen_property]) >>
  rw_tac std_ss[RingHomo_def] >| [
    rw_tac std_ss[GroupHomo_def, ring_carriers] >>
    fs[quotient_ring_def, quotient_ring_add_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
    metis_tac[kernel_ideal_gen_add_map],
    rw_tac std_ss[MonoidHomo_def, ring_carriers] >| [
      fs[quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
      metis_tac[kernel_ideal_gen_mult_map],
      fs[quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
      metis_tac[kernel_ideal_gen_id_map]
    ]
  ]);

(* Theorem: (r ~r~ s) f ==> let i = kernel_ideal f r s in
            RingIso (f o gen) (r / i) (ring_homo_image f r s) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo (f o gen) (r / i) (ring_homo_image f r s)
       This is true by kernel_ideal_quotient_homo
   (2) BIJ (f o gen) (r / i).carrier (ring_homo_image f r s).carrier
       Note (r / i).carrier = R/I                         by quotient_ring_def
        and (ring_homo_image f r s).carrier = IMAGE f R   by ring_homo_image_def
       Hence true by kernel_ideal_quotient_bij
*)
val kernel_ideal_quotient_iso = store_thm(
  "kernel_ideal_quotient_iso",
  ``!(r:'a ring) (s:'b ring) f. (r ~r~ s) f ==> let i = kernel_ideal f r s in
         RingIso (f o gen) (r / i) (ring_homo_image f r s)``,
  rw_tac std_ss[RingIso_def] >-
  metis_tac[kernel_ideal_quotient_homo] >>
  `(r / i).carrier = R/I` by rw[quotient_ring_def] >>
  `(ring_homo_image f r s).carrier = IMAGE f R` by rw[ring_homo_image_def] >>
  metis_tac[kernel_ideal_quotient_bij]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            (i << r) /\ (ring_homo_image f r r_ <= r_) /\
            RingIso (f o gen) (r / i) (ring_homo_image f r r_) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   This is to show:
   (1) i << r, true by ring_homo_kernel_ideal
   (2) ring_homo_image f r r_ <= r_, true by ring_homo_image_subring
   (3) RingIso (f o gen) (r / i) (ring_homo_image f r r_)
       This is true by kernel_ideal_quotient_iso
*)
val ring_first_isomorphism_thm = store_thm(
  "ring_first_isomorphism_thm",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    (i << r) /\ (ring_homo_image f r r_ <= r_) /\ RingIso (f o gen) (r / i) (ring_homo_image f r r_)``,
  rw_tac std_ss[ring_homo_image_subring] >-
  rw_tac std_ss[ring_homo_kernel_ideal, Abbr`i`] >>
  metis_tac[kernel_ideal_quotient_iso]);

(* This is a significant milestone theorem! *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
