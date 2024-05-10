(* ------------------------------------------------------------------------- *)
(* Ideals in Ring                                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringIdeal";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory gcdsetTheory numberTheory
     combinatoricsTheory;

open ringTheory;
open groupTheory;
open monoidTheory;
open groupMapTheory ringMapTheory;

open ringUnitTheory;
open subgroupTheory quotientGroupTheory;

(* ------------------------------------------------------------------------- *)
(* Ideals in Ring Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   I       = i.carrier
   J       = j.carrier
   i << r  = ideal i r
   x o I   = coset r.sum x i.carrier
   x * R   = coset r.prod x r.carrier
   x === y = ideal_congruence r i x y
   <p>     = principal_ideal r p
   <q>     = principal_ideal r q
   <#0>    = principal_ideal r #0
   i + j   = ideal_sum r i j
   maxi    = ideal_maximal r
   atom    = irreducible r
*)
(* Definitions and Theorems (# are exported):

   Ring Ideals:
   ideal_def    |- !i r. i << r <=>
                    i.sum <= r.sum /\ (i.sum.carrier = I) /\
                    (i.prod.carrier = I) /\ (i.prod.op = $* ) /\ (i.prod.id = #1) /\
                    !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I
   ideal_has_subgroup      |- !r i. i << r ==> i.sum <= r.sum
   ideal_carriers          |- !r i. i << r ==> (i.sum.carrier = I) /\ (i.prod.carrier = I)
   ideal_product_property  |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I
   ideal_element           |- !r i. i << r ==> !x. x IN I ==> x IN r.sum.carrier
   ideal_ops               |- !r i. i << r ==> (i.sum.op = $+) /\ (i.prod.op = $* )

   Ideal Theorems:
   ideal_element_property  |- !r i. Ring r /\ i << r ==> !x. x IN I ==> x IN R
   ideal_property          |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I
   ideal_has_zero          |- !r i. Ring r /\ i << r ==> #0 IN I
   ideal_has_neg           |- !r i. Ring r /\ i << r ==> !x. x IN I ==> -x IN I
   ideal_has_sum           |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I
   ideal_has_diff          |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x - y IN I
   ideal_has_product       |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x * y IN I
   ideal_has_multiple      |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I
   ideal_zero              |- !r i. Ring r /\ i << r ==> (i.sum.id = #0)
   ideal_eq_ideal          |- !r i j. Ring r /\ i << r /\ j << r ==> ((i = j) <=> (I = J))
   ideal_sub_ideal         |- !r i j. Ring r /\ i << r /\ j << r ==> (i << j <=> I SUBSET J)
   ideal_sub_itself        |- !r i. Ring r /\ i << r ==> i << i
   ideal_refl              |- !r. Ring r ==> r << r
   ideal_antisym           |- !r i. i << r /\ r << i ==> (i = r)
   ideal_has_one           |- !r i. Ring r /\ i << r /\ #1 IN I ==> (I = R)
   ideal_with_one          |- !r. Ring r ==> !i. i << r /\ #1 IN I <=> (i = r)
   ideal_with_unit         |- !r i. Ring r /\ i << r ==> !x. x IN I /\ unit x ==> (i = r)

   Ideal Cosets:
   ideal_coset_of_element  |- !r i. Ring r /\ i << r ==> !x. x IN I ==> (x o I = I)
   ideal_coset_eq_carrier  |- !r i. Ring r /\ i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I
   ideal_coset_eq          |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I)

   Ideal induces congruence in Ring:
#  ideal_congruence_def    |- !r i x y. x === y <=> x - y IN I
   ideal_congruence_refl   |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x === x
   ideal_congruence_sym    |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> (x === y <=> y === x)
   ideal_congruence_trans  |- !r i. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> x === y /\ y === z ==> x === z
   ideal_congruence_equiv  |- !r i. Ring r /\ i << r ==> $=== equiv_on R
   ideal_congruence_iff_inCoset  |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x === y <=> inCoset r.sum i.sum x y)
   ideal_coset_eq_congruence     |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y)
   ideal_congruence_mult         |- !r i. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> x === y ==> z * x === z * y
   ideal_congruence_elements     |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN R ==> (y IN I <=> x === y)

   Principal Ideal:
   principal_ideal_def      |- !r p.  <p> =  <|carrier := p * R;
                                                   sum := <|carrier := p * R; op := $+; id := #0|>;
                                                  prod := <|carrier := p * R; op := $*; id := #1|>
                                              |>
   principal_ideal_property |- !r p. (<p>.carrier = p * R) /\ (<p>.sum.carrier = p * R) /\
                                     (<p>.prod.carrier = p * R) /\ (<p>.sum.op = $+) /\
                                     (<p>.prod.op = $* ) /\ (<p>.sum.id = #0) /\ (<p>.prod.id = #1)
   principal_ideal_element              |- !p x. x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z)
   principal_ideal_has_element          |- !r. Ring r ==> !p. p IN R ==> p IN <p>.carrier
   principal_ideal_group                |- !r. Ring r ==> !p. p IN R ==> Group <p>.sum
   principal_ideal_subgroup             |- !r. Ring r ==> !p. p IN R ==> <p>.sum <= r.sum
   principal_ideal_subgroup_normal      |- !r. Ring r ==> !p. p IN R ==> <p>.sum << r.sum
   principal_ideal_ideal                |- !r. Ring r ==> !p. p IN R ==> <p> << r
   principal_ideal_has_principal_ideal  |- !r. Ring r ==> !p q. p IN R /\ q IN <p>.carrier ==> <q> << <p>
   principal_ideal_eq_principal_ideal   |- !r. Ring r ==> !p q u. p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> (<p> = <q>)
   ideal_has_principal_ideal            |- !r i. Ring r /\ i << r ==> !p. p IN R ==> (p IN I <=> <p> << i)

   Trivial Ideal:
   zero_ideal_sing          |- !r. Ring r ==> (<#0>.carrier = {#0})
   zero_ideal_ideal         |- !r. Ring r ==> <#0> << r
   ideal_carrier_sing       |- !r i. Ring r /\ i << r ==> (SING I <=> (i = <#0>))

   Sum of Ideals:
   ideal_sum_def            |- !r i j. i + j =
                                <|carrier := {x + y | x IN I /\ y IN J};
                                      sum := <|carrier := {x + y | x IN I /\ y IN J}; op := $+; id := #0|>;
                                     prod := <|carrier := {x + y | x IN I /\ y IN J}; op := $*; id := #1|>
                                 |>
   ideal_sum_element         |- !i j x. x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z)
   ideal_sum_comm            |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j = j + i)
   ideal_sum_group           |- !r i j. Ring r /\ i << r /\ j << r ==> Group (i + j).sum
   ideal_subgroup_ideal_sum  |- !r i j. Ring r /\ i << r /\ j << r ==> i.sum <= (i + j).sum
   ideal_sum_subgroup        |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j).sum <= r.sum
   ideal_sum_has_ideal       |- !r i j. Ring r /\ i << r /\ j << r ==> i << (i + j)
   ideal_sum_has_ideal_comm  |- !r i j. Ring r /\ i << r /\ j << r ==> j << (i + j)
   ideal_sum_ideal           |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j) << r
   ideal_sum_sub_ideal       |- !r i j. Ring r /\ i << r /\ j << r ==> ((i + j) << j <=> i << j)

   principal_ideal_sum_eq_ideal     |- !r i. Ring r /\ i << r ==> !p. p IN I ==> (<p> + i = i)
   principal_ideal_sum_equal_ideal  |- !r i. Ring r /\ i << r ==> !p. p IN I <=> p IN R /\ (<p> + i = i)

   Maximal Ideals:
   ideal_maximal_def     |- !r i. maxi i <=> i << r /\ !j. i << j /\ j << r ==> (i = j) \/ (j = r)

   Irreducibles:
   irreducible_def       |- !r z. atom z <=> z IN R+ /\ z NOTIN R* /\ !x y. x IN R /\ y IN R /\ (z = x * y) ==> unit x \/ unit y
   irreducible_element   |- !r p. atom p ==> p IN R

   Principal Ideal Ring:
   PrincipalIdealRing_def             |- !r. PrincipalIdealRing r <=> Ring r /\ !i. i << r ==> ?p. p IN R /\ (<p> = i)
   principal_ideal_ring_ideal_maximal |- !r. PrincipalIdealRing r ==> !p. atom p ==> maxi <p>

   Euclidean Ring:
   EuclideanRing_def     |- !r f. EuclideanRing r f <=> Ring r /\ (!x. (f x = 0) <=> (x = #0)) /\
                            !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y
   euclid_ring_ring      |- !r f. EuclideanRing r f ==> Ring r
   euclid_ring_map       |- !r f. EuclideanRing r f ==> !x. (f x = 0) <=> (x = #0)
   euclid_ring_property  |- !r f. EuclideanRing r f ==> !x y. x IN R /\ y IN R /\ y <> #0 ==>
                                                     ?q t. q IN R /\ t IN R /\ (x = y * q + t) /\ f t < f y
   ideal_gen_exists      |- !r i. Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0)) ==>
                            ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z
   ideal_gen_def         |- !r i f. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0)) ==>
                            ideal_gen r i f IN I /\ ideal_gen r i f <> #0 /\
                            !z. z IN I /\ z <> #0 ==> f (ideal_gen r i f) <= f z
   ideal_gen_minimal     |- !r i. Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0)) ==>
                            !z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))
   euclid_ring_principal_ideal_ring   |- !r f. EuclideanRing r f ==> PrincipalIdealRing r

   Ideal under Ring Homomorphism:
   homo_ideal_def           |- !f r i. homo_ideal f r s i =
                               <|carrier := IMAGE f I;
                                    sum := <|carrier := IMAGE f I; op := s.sum.op; id := f #0|>;
                                   prod := <|carrier := IMAGE f I; op := s.prod.op; id := f #1|>
                                |>
   ring_homo_ideal_group    |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> Group (homo_ideal f r s i).sum
   ring_homo_ideal_subgroup |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> (homo_ideal f r s i).sum <= s.sum
   ring_homo_ideal_ideal    |- !r s f. Ring r /\ Ring s /\ RingHomo f r s /\ SURJ f R s.carrier ==>
                               !i. i << r ==> homo_ideal f r s i << s
*)

(* ------------------------------------------------------------------------- *)
(* Ring Ideals                                                               *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* An Ideal i (structurally a ring: carrier, sum, prod) of a ring r satisfies 2 conditions:
   (1) sum part is subgroup: i.sum is a subgroup of r.sum
   (2) prod part is absorption: !x IN I, y IN R, x * y IN I
   (3) !x IN I, y IN R, y * x IN I
*)
val ideal_def = Define `
  ideal (i:'a ring) (r:'a ring) <=>
    i.sum <= r.sum /\
    (i.sum.carrier = I) /\
    (i.prod.carrier = I) /\
    (i.prod.op = r.prod.op) /\
    (i.prod.id = #1) /\
    (!x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I)
`;
(*
- ideal_def;
> val ideal_def = |- !i r. ideal i r <=>
         i.sum <= r.sum /\ (i.sum.carrier = I) /\
         (i.prod.carrier = I) /\ (i.prod.op = $* ) /\ (i.prod.id = #1) /\
         !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I : thm
*)
(* set overloading *)
val _ = overload_on ("<<", ``ideal``);
val _ = set_fixity "<<" (Infixl 650); (* higher than * or / *)

(* Theorem: Ideal add_group is a subgroup. *)
val ideal_has_subgroup = save_thm("ideal_has_subgroup",
    ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val ideal_has_subgroup = |- !r i. i << r ==> i.sum <= r.sum : thm *)

(* Theorem: Ideal carriers are I. *)
val ideal_carriers = save_thm("ideal_carriers",
    CONJ (ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1)
         (ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCT1)
         |> DISCH_ALL |> GEN_ALL);
(* > val ideal_carriers = |- !r i. i << r ==> (i.sum.carrier = I) /\ (i.prod.carrier = I) : thm *)

(* Theorem: Ideal is multiplicative closed with all elements. *)
val ideal_product_property = save_thm("ideal_product_property",
    ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCTS |> last |> DISCH_ALL |> GEN_ALL);
(* > val ideal_product_property = |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I : thm *)

(* Theorem: i << r ==> !x. x IN I ==> x IN r.sum.carrier *)
(* Proof:
   i.sum <= r.sum /\ i.sum.carrier = I    by ideal_def
   x IN i.sum.carrier ==> x IN r.sum.carrier  by subgroup_element
   hence true.
*)
val ideal_element = store_thm(
  "ideal_element",
  ``!r i:'a ring. i << r ==> !x. x IN I ==> x IN r.sum.carrier``,
  metis_tac[ideal_def, subgroup_element]);

(* Theorem: i << r ==> (i.sum.op = r.sum.op) /\ (i.prod.op = r.prod.op *)
(* Proof:
   i << r ==> i.sum <= r.sum          by ideal_def
          ==> i.sum.op = r.sum.op     by Subgroup_def
   i << r ==> i.prod.op = r.prod.op   by ideal_def
*)
val ideal_ops = store_thm(
  "ideal_ops",
  ``!r i:'a ring. i << r ==> (i.sum.op = r.sum.op) /\ (i.prod.op = r.prod.op)``,
  rw[ideal_def, Subgroup_def]);

(* ------------------------------------------------------------------------- *)
(* Ideal Theorems                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ i << r ==> !x. x IN I ==> x IN R *)
(* Proof:
   x IN I ==> x IN r.sum.carrier    by ideal_element
   r.sum.carrier = R                by ring_add_group
   hence true.
*)
val ideal_element_property = store_thm(
  "ideal_element_property",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> x IN R ``,
  metis_tac[ideal_element, ring_add_group]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I *)
(* Proof:
   For the first one, x + y IN I
     It is because i.sum <= r.sum /\ (i.sum.carrier = I)  by ideal_def
     Hence Group i.sum /\ (i.sum.op x y = x + y)          by subgroup_property
     Since x, y IN I, x, y IN R                           by ideal_element_property
     Hence true by group_op_element.
   For the second one, x * y IN I
     It is because y IN I ==> y IN R by ideal_element_property
     Hence true by ideal_product_property.
*)
val ideal_property = store_thm(
  "ideal_property",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I``,
  rpt strip_tac >| [
    `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
    `Group i.sum /\ (i.sum.op x y = x + y)` by metis_tac[subgroup_property] >>
    metis_tac[group_op_element, ideal_element_property],
    metis_tac[ideal_product_property, ideal_element_property]
  ]);

(* Theorem: i << r ==> #0 IN I *)
(* Proof:
   i.sum <= r.sum /\ (i.sum.carrier = I)   by ideal_def
   i.sum.id = #0                           by subgroup_id
   hence true by Subgroup_def, group_id_element.
*)
val ideal_has_zero = store_thm(
  "ideal_has_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> #0 IN I``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  metis_tac[subgroup_id, Subgroup_def, group_id_element]);

(* Theorem: i << r ==> !x. x IN I <=> -x IN I *)
(* Proof:
   i.sum <= r.sum /\ (i.sum.carrier = I)   by ideal_def
   hence true by Subgroup_def, group_inv_element.
*)
val ideal_has_neg = store_thm(
  "ideal_has_neg",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> -x IN I``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  metis_tac[subgroup_inv, Subgroup_def, group_inv_element]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x + y) IN I *)
(* Proof: by ideal_property. *)
val ideal_has_sum = store_thm(
  "ideal_has_sum",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x + y) IN I``,
  rw[ideal_property]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x - y) IN I *)
(* Proof: by ideal_has_neg, ideal_has_sum. *)
val ideal_has_diff = store_thm(
  "ideal_has_diff",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x - y) IN I``,
  rw[ideal_has_neg, ideal_has_sum]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x * y) IN I *)
(* Proof: by ideal_property. *)
val ideal_has_product = store_thm(
  "ideal_has_product",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x * y) IN I``,
  rw[ideal_property]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I *)
(* Proof: by ideal_product_property. *)
val ideal_has_multiple = store_thm(
  "ideal_has_multiple",
  ``!r i:'a ring. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I``,
  rw[ideal_product_property]);

(* Theorem: i << r ==> i.sum.id = #0 *)
(* Proof:
       i << r
   ==> i.sum <= r.sum        by ideal_def
   ==> i.sum.id = #0         by subgroup_id
*)
val ideal_zero = store_thm(
  "ideal_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> (i.sum.id = #0)``,
  rw[ideal_def, subgroup_id]);

(* Theorem: i << r /\ j << r ==> ((i = j) <=> (I = J)) *)
(* Proof:
   If part: i = j ==> I = J, true by I = i.carrier, J = j.carrier.
   Only-if part: I = J ==> i = j
   By ring_component_equality, this is to show:
   (1) I = J ==> i.sum = j.sum
       True by monoid_component_equality, ideal_def, ideal_ops, ideal_zero.
   (2) I = J ==> i.prod = j.prod
       True by monoid_component_equality, ideal_def, ideal_ops.
*)
val ideal_eq_ideal = store_thm(
  "ideal_eq_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i = j) <=> (I = J))``,
  rw[ring_component_equality, EQ_IMP_THM] >>
  metis_tac[monoid_component_equality, ideal_def, ideal_ops, ideal_zero]);

(* Theorem: i << r /\ j << r ==> ((i << j) <=> (I <= J)) *)
(* Proof:
   After expanding by definitions, this is to show:
   (1) x IN I /\ y IN J /\ I SUBSET J ==> x * y IN I, true by SUBSET_DEF, and y IN J ==> y IN R.
   (2) x IN I /\ y IN J /\ I SUBSET J ==> y * x IN I, true by SUBSET_DEF, and x IN I ==> x IN R.
*)
val ideal_sub_ideal = store_thm(
  "ideal_sub_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i << j) <=> (I SUBSET J))``,
  rw[ideal_def, Subgroup_def] >>
  `r.sum.carrier = R` by rw[ring_add_group] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: i << r ==> i << i *)
(* Proof:
   i << i iff I SUBSET I    by ideal_sub_ideal
          iff T             by SUBSET_REFL
*)
val ideal_sub_itself = store_thm(
  "ideal_sub_itself",
  ``!r i:'a ring. Ring r /\ i << r ==> i << i``,
  metis_tac[ideal_sub_ideal, SUBSET_REFL]);

(* Theorem: r << r *)
(* Proof: by definition, this is to show:
   (1) r.sum <= r.sum, true by subgroup_refl.
   (2) r.prod.carrier = R, true by ring_mult_monoid.
   (3) x IN R /\ y IN R ==> x * y IN R, true by ring_mult_element.
   (4) x IN R /\ y IN R ==> y * x IN R, true by ring_mult_element.
*)
val ideal_refl = store_thm(
  "ideal_refl",
  ``!r:'a ring. Ring r ==> r << r``,
  rw[ideal_def, subgroup_refl]);

(* Theorem: i << r /\ #1 IN I ==> i = r *)
(* Proof:
   By ring_component_equality, this is to show:
   (1) i << r /\ r << i ==> I = R
       i << r ==> i.sum.carrier = I SUBSET R = r.sum.carrier   by ideal_def, Subgroup_def
       r << i ==> r.sum.carrier = R SUBSET I = i.sum.carrier   by ideal_def, Subgroup_def
       Hence true by SUBSET_ANTISYM.
   (2) i << r /\ r << i ==> i.sum = r.sum
       i << r ==> i.sum <= r.sum    by ideal_def
       r << i ==> r.sum <= i.sum    by ideal_def
       Hence true by subgroup_antisym.
   (3) i << r /\ r << i ==> i.prod = r.prod
       By monoid_component_equality, this is to show:
       (a)  << r /\ r << i ==> i.prod.carrier = r.prod.carrier,
           i.e. I = R     by ideal_def
           so apply (1).
       (b) i << r ==> i.prod.op = $*, true by ideal_def.
       (c) i << r ==> i.prod.id = #1, true by ideal_def.
*)
val ideal_antisym = store_thm(
  "ideal_antisym",
  ``!(r:'a ring) (i:'a ring). i << r /\ r << i ==> (i = r)``,
  rw[ring_component_equality] >-
  metis_tac[ideal_def, Subgroup_def, SUBSET_ANTISYM] >-
  metis_tac[ideal_def, subgroup_antisym] >>
  rw[monoid_component_equality] >>
  metis_tac[ideal_def, Subgroup_def, SUBSET_ANTISYM]);

(* Theorem: i << r /\ #1 IN I ==> I = R *)
(* Proof:
   First, i << r ==> I SUBSET R, by Subgroup_def.
   Now, !z. #1 IN I /\ z IN R ==> #1 * z = z IN I by ideal_def.
   Hence R SUBSET I, or I = R by SUBSET_ANTISYM.
*)
val ideal_has_one = store_thm(
  "ideal_has_one",
  ``!r i:'a ring. Ring r /\ i << r /\ #1 IN I ==> (I = R)``,
  rw[ideal_def] >>
  `I SUBSET R` by metis_tac[Subgroup_def, Ring_def] >>
  `!y. y IN R ==> (#1 * y = y)` by rw[] >>
  `R SUBSET I` by metis_tac[SUBSET_DEF] >>
  rw[SUBSET_ANTISYM]);

(* Theorem: i << r /\ #1 IN I <=> i = r *)
(* Proof:
   If part: i << r /\ #1 IN I ==> i = r
   By ring_component_equality, this is to show:
   (1) i << r /\ #1 IN I ==> I = R, true by ideal_has_one.
   (2) i << r /\ #1 IN I ==> i.sum = r.sum
       By monoid_component_equality, this is to show:
       (a) i.sum.carrier = R, i.e. I = R, given by (1)
       (b) i.sum.op = $+, true by ideal_ops.
       (c) i.sum.id = #0, true by i.sum <= r.sum, and subgroup_id.
   (3) i << r /\ #1 IN I ==> i.prod = r.prod
       By monoid_component_equality, this is to show:
       (a) i.prod.carrier = r.prod.carrier, i.e. I = R, given by (1)
       (b) i.prod.op = $*, true by ideal_ops.
       (c) i.prod.id = #1, true by ideal_def.
   Only-if part: Ring i ==> i << i
   True by ideal_refl.
*)
val ideal_with_one = store_thm(
  "ideal_with_one",
  ``!r:'a ring. Ring r ==> !i. i << r /\ #1 IN I <=> (i = r)``,
  rw[EQ_IMP_THM] >| [
    rw[ring_component_equality] >| [
      rw[ideal_has_one],
      rw[monoid_component_equality] >| [
        metis_tac[ideal_carriers, ideal_has_one],
        rw[ideal_ops],
        metis_tac[ideal_def, subgroup_id]
      ],
      rw[monoid_component_equality] >| [
        metis_tac[ideal_def, ring_mult_monoid, ideal_has_one],
        rw[ideal_ops],
        metis_tac[ideal_def]
      ]
    ],
    rw[ideal_refl]
  ]);

(* Theorem: i << r /\ x IN I /\ unit x ==> i = r *)
(* Proof:
   x IN I ==> x IN R        by ideal_element_property
   unit x ==> |/ x IN R     by ring_unit_inv_element
   So x * |/x IN I          by ideal_has_multiple
   But x * |/x = #1         by ring_unit_rinv
   i.e. #1 IN I, hence follows by ideal_with_one.
*)
val ideal_with_unit = store_thm(
  "ideal_with_unit",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I /\ unit x ==> (i = r)``,
  rpt strip_tac >>
  `x IN R` by metis_tac[ideal_element_property] >>
  `|/x IN R` by rw[ring_unit_inv_element] >>
  `x * |/x = #1` by rw[ring_unit_rinv] >>
  `#1 IN I` by metis_tac[ideal_has_multiple] >>
  metis_tac[ideal_with_one]);

(* ------------------------------------------------------------------------- *)
(* Ideal Cosets                                                              *)
(* ------------------------------------------------------------------------- *)

(* Define (left) coset of ideal with an element a in R by overloading *)
val _ = overload_on ("o", ``coset r.sum``);

(* Theorem: i << r ==> !x. x IN I ==> x o I = I *)
(* Proof: by coset_def, this is to show:
   (1) x IN I /\ z IN I ==> x + z IN I
       True by ideal_property.
   (2) x IN I /\ x' IN I ==> ?z. (x' = x + z) /\ z IN I
       Let z = x' + (-x)
       -x IN I         by ideal_has_neg
       hence z IN I    by ideal_property
       and x + z
         = x + (x' + -x)
         = x + (-x + x')  by ring_add_comm
         = x'             by ring_add_lneg_assoc
*)
val ideal_coset_of_element = store_thm(
  "ideal_coset_of_element",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> (x o I = I)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[ideal_property] >>
  qexists_tac `x' + -x` >>
  `-x IN I` by rw[ideal_has_neg] >>
  metis_tac[ring_add_lneg_assoc, ring_add_comm, ideal_element_property, ideal_property]);

(* Theorem: i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I *)
(* Proof:
   If part: x IN R /\ x o I = I ==> x IN I
     x o I = IMAGE (\z. x + z) I   by coset_def
     Since #0 IN I                 by ideal_has_zero
     x + #0 IN IMAGE (\z. x + z) I
     i.e. x + #0 IN I
     or x IN I                     by ring_add_rzero
   Only if part: x IN I ==> x IN R /\ (x o I = I)
     x IN R     by ideal_element_property
     x o I = I  by ideal_coset_of_element.
*)
val ideal_coset_eq_carrier = store_thm(
  "ideal_coset_eq_carrier",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I``,
  rw[EQ_IMP_THM] >| [
    `x o I = IMAGE (\z. x + z) I` by rw[GSYM coset_def] >>
    `#0 IN I` by rw[ideal_has_zero] >>
    `x + #0 IN IMAGE (\z. x + z) I` by rw[] >>
    metis_tac[ring_add_rzero, ideal_element_property],
    metis_tac[ideal_element_property],
    rw[ideal_coset_of_element]
  ]);

(* Theorem: Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I) *)
(* Proof:
   Since i << r, i.sum <= r.sum by ideal_def
   Also r.sum.carrier = R       by ring_add_group
   Hence by subgroup_coset_eq, this is to show:
            - y + x IN I
   or        x + -y IN I        by ring_add_comm, ring_neg_element
   or        x - y  IN I        by ring_sub_def
*)
val ideal_coset_eq = store_thm(
  "ideal_coset_eq",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I)``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  `r.sum.carrier = R` by rw[] >>
  metis_tac[subgroup_coset_eq, ring_add_comm, ring_neg_element, ring_sub_def]);

(* ------------------------------------------------------------------------- *)
(* Ideal induces congruence in Ring.                                         *)
(* ------------------------------------------------------------------------- *)

(* Define congruence by ideal in Ring *)
val ideal_congruence_def = Define `
  ideal_congruence (r:'a ring) (i:'a ring) (x:'a) (y:'a) <=> x - y IN i.carrier
`;

(* set overloading *)
val _ = overload_on ("===", ``ideal_congruence r i``);
val _ = set_fixity "===" (Infix(NONASSOC, 450));

(* export definiton *)
val _ = export_rewrites ["ideal_congruence_def"];

(* Theorem: x === x *)
(* Proof:
   x - x = #0            by ring_sub_eq_zero
   hence true            by ideal_has_zero
*)
val ideal_congruence_refl = store_thm(
  "ideal_congruence_refl",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R ==> x === x``,
  rw[ideal_has_zero]);

(* Theorem: x === y <=> y === x *)
(* Proof:
   x - y = - (y - x)    by ring_neg_sub
   hence true           by ideal_had_neg
*)
val ideal_congruence_sym = store_thm(
  "ideal_congruence_sym",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> (x === y <=> y === x)``,
  rw_tac std_ss[ideal_congruence_def] >>
  metis_tac[ring_neg_sub, ideal_has_neg]);

(* Theorem: x === y /\ y === z ==> x === z *)
(* Proof:
   x - z = (x - y) + (y - z)   by ring_sub_def, ring_add_assoc, ring_add_lneg, ring_add_lzero
   hence true                  by ideal_has_sum
*)
val ideal_congruence_trans = store_thm(
  "ideal_congruence_trans",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x === y /\ y === z ==> x === z)``,
  rw_tac std_ss[ideal_congruence_def] >>
  `(x - y) + (y - z) = x + (-y + (y + -z))` by rw[ring_add_assoc] >>
  `_ = x + (-y + y + -z)` by rw[ring_add_assoc] >>
  `_ = x - z` by rw[] >>
  metis_tac[ideal_has_sum]);

(* Theorem: === is an equivalence relation on R. *)
(* Proof: by reflexive, symmetric and transitive of === on R. *)
val ideal_congruence_equiv = store_thm(
  "ideal_congruence_equiv",
  ``!r i:'a ring. Ring r /\ i << r ==> $=== equiv_on R``,
  rw_tac std_ss[equiv_on_def] >-
  rw[ideal_congruence_refl] >-
  rw[ideal_congruence_sym] >>
  metis_tac[ideal_congruence_trans]);

(* Theorem: Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y) *)
(* Proof: by ideal_congruence_def, ideal_coset_eq. *)
val ideal_coset_eq_congruence = store_thm(
  "ideal_coset_eq_congruence",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y)``,
  rw[ideal_coset_eq]);

(* Characterization: x === y iff x, y in the same coset, element of (r/i) *)

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x === y) <=> inCoset r.sum i.sum x y *)
(* Proof: by definitions, this is to show:
   (1) x IN I /\ y IN I /\ x + -y IN I ==> ?z. (y = x + z) /\ z IN I
       Let z = -x + y,
       then z IN I   by ideal_has_neg, ideal_has_sum
       and y = x + (-x + y)   by ring_add_lneg_assoc
   (2) x IN I /\ z IN I ==> x + -(x + z) IN I
         x + -(x + z)
       = x + (-x + -z)   by ring_neg_add
       = -z              by ring_add_lneg_assoc
       hence true        by ideal_has_neg
*)
val ideal_congruence_iff_inCoset = store_thm(
  "ideal_congruence_iff_inCoset",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> ((x === y) <=> inCoset r.sum i.sum x y)``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  rw[inCoset_def, coset_def, EQ_IMP_THM] >| [
    qexists_tac `-x + y` >>
    metis_tac[ring_add_lneg_assoc, ideal_has_neg, ideal_has_sum],
    `!y. y IN R ==> -y IN R` by rw[] >>
    metis_tac[ring_neg_add, ring_add_lneg_assoc, ideal_has_neg]
  ]);

(* Theorem: x === y ==> z * x === z * y  *)
(* Proof:
       x === y
   ==> x - y IN R          by ideal_congruence_def
   ==> z * (x - y) IN R    by ideal_def
   ==> z * x - z * y IN R  by ring_mult_rsub, ideal_element_property
   ==> z * x === z * y     by ideal_congruence_def
*)
val ideal_congruence_mult = store_thm(
  "ideal_congruence_mult",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x === y) ==> (z * x === z * y))``,
  rw_tac std_ss[ideal_congruence_def] >>
  `z * (x - y) IN I` by metis_tac[ideal_def] >>
  metis_tac[ring_mult_rsub, ideal_element_property]);

(* Theorem: i << r /\ x IN I /\ y IN R ==> y IN I <=> x === y *)
(* Proof:
   If part: y IN I ==> x === y
       x IN I /\ y IN I
   ==> x - y IN I             by ideal_has_diff
   ==> x === y                by ideal_congruence_def
   Only-if part: x === y ==> y IN I
       x === y
   ==> y === x                by ideal_congruence_sym
   ==> y - x IN I             by ideal_congruence_def
   ==> (y - x) + x IN I       by ideal_has_sum
   ==> y IN I                 by ring_sub_add
*)
val ideal_congruence_elements = store_thm(
  "ideal_congruence_elements",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN R ==> (y IN I <=> x === y)``,
  rpt strip_tac >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  rw_tac std_ss[ideal_congruence_def, EQ_IMP_THM] >-
  rw[ideal_has_diff] >>
  `x + -y IN I` by metis_tac[ring_sub_def] >>
  `x + -y - x IN I` by rw[ideal_has_diff] >>
  `-y IN I` by metis_tac[ring_add_sub_comm, ring_neg_element] >>
  metis_tac[ideal_has_neg, ring_neg_neg]);

(* ------------------------------------------------------------------------- *)
(* Principal Ideal = Ideal generated by a Ring element                       *)
(* ------------------------------------------------------------------------- *)

(* Multiples of a Ring element p *)
(* val element_multiple_def = Define `element_multiple (r:'a ring) (p:'a) = {p * x | x IN R}`; *)

(* use overloading *)
val _ = overload_on ("*", ``coset r.prod``);

(* Integer Ring Ideals are multiples *)
val principal_ideal_def = Define `
  principal_ideal (r:'a ring) (p:'a) =
    <| carrier := p * R;
           sum := <| carrier := p * R; op := r.sum.op; id := r.sum.id |>;
          prod := <| carrier := p * R; op := r.prod.op; id := r.prod.id |>
     |>
`;
(* Note: <p>.prod is only type-compatible with monoid, it is not a monoid: prod.id may not be in carrier. *)

(* set overloading *)
val _ = overload_on ("<p>", ``principal_ideal r p``);
val _ = overload_on ("<q>", ``principal_ideal r q``);

(*
- principal_ideal_def;
> val it = |- !r p. <p> = <|carrier := p * R;
                                sum := <|carrier := p * R; op := $+; id := #0|>;
                               prod := <|carrier := p * R; op := $*; id := #1|>
                           |> : thm
*)

(* Theorem: Properties of principal ideal. *)
(* Proof: by definition. *)
val principal_ideal_property = store_thm(
  "principal_ideal_property",
  ``!(r:'a ring) (p:'a).
     (<p>.carrier = p * R) /\ (<p>.sum.carrier = p * R) /\ (<p>.prod.carrier = p * R) /\
     (<p>.sum.op = r.sum.op) /\ (<p>.prod.op = r.prod.op) /\
     (<p>.sum.id = #0) /\ (<p>.prod.id = #1)``,
  rw[principal_ideal_def]);

(* Theorem: x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z) *)
(* Proof: by definitions. *)
val principal_ideal_element = store_thm(
  "principal_ideal_element",
  ``!p x:'a. x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z)``,
  rw[principal_ideal_def, coset_def] >>
  metis_tac[]);

(* Theorem: p IN <p>.carrier *)
(* Proof:
   By principal_ideal_element, this is to show:
   ?x. (p = p * x) /\ x IN R
   Let x = #1,
   then #1 IN R      by ring_one_element
   and  p = p * #1   by ring_mult_rone
   hence true.
*)
val principal_ideal_has_element = store_thm(
  "principal_ideal_has_element",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p IN <p>.carrier``,
  metis_tac[principal_ideal_element, ring_one_element, ring_mult_rone]);

(* Theorem: Group <p>.sum *)
(* Proof:
   First, <p>.carrier = p * R     by principal_ideal_property
   and !x. x IN p * R ==> x IN R  by coset_def
   Check group axioms:
   (1) x IN p * R /\ y IN p * R ==> x + y IN p * R
       Let x = p * u, y = p * v,  u IN R and v IN R
       x + y = p * u + p * v
             = p * (u + v)        by ring_mult_radd
       Hence in p * R.
   (2) x IN p * R /\ y IN p * R /\ z IN p * R ==> x + y + z = x + (y + z)
       True by ring_add_assoc.
   (3) #0 IN p * R
       Since #0 = p * #0          by ring_mult_rzero
       and #0 IN R                by ring_zero_element
       Hence true.
   (4) x IN p * R ==> #0 + x = x
       True by ring_add_lzero.
   (5) x IN p * R ==> ?y. y IN p * R /\ (y + x = #0)
       Let x = p * u, u IN R      by principal_ideal_element
       Let y = p * (-u), -u IN R  by ring_neg_element
       Hence y IN p * R, and
          y + x
       = p * -u + p * u
       = - (p * u) + p * u        by ring_neg_mult
       = #0                       by ring_add_lneg
*)
val principal_ideal_group = store_thm(
  "principal_ideal_group",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> Group <p>.sum``,
  ntac 4 strip_tac >>
  `<p>.carrier = p * R` by rw[principal_ideal_property] >>
  (`!x. x IN p * R ==> x IN R` by (rw[coset_def] >> rw[])) >>
  rw_tac std_ss[principal_ideal_def, group_def_alt, GSPECIFICATION] >| [
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `?v. v IN R /\ (y = p * v)` by metis_tac[principal_ideal_element] >>
    `x + y = p * (u + v)` by rw[ring_mult_radd] >>
    metis_tac[principal_ideal_element, ring_add_element],
    rw[ring_add_assoc],
    metis_tac[principal_ideal_element, ring_zero_element, ring_mult_rzero],
    rw[],
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    qexists_tac `p * (-u)` >>
    `p * -u = - x` by metis_tac[ring_neg_mult] >>
    `p * -u + x = #0` by metis_tac[ring_add_lneg] >>
    metis_tac[principal_ideal_element, ring_neg_element]
  ]);

(* Theorem: <p>.sum <= r.sum *)
(* Proof: for a subgroup:
   (1) Group <p>.sum,
       true by principal_ideal_group
   (2) <p>.sum SUBSET r.sum.carrier,
       i.e. to show: p * R SUBSET R
         or to show: p IN R /\ z IN R ==> p * z IN R
       true by ring_mult_element.
*)
val principal_ideal_subgroup = store_thm(
  "principal_ideal_subgroup",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p>.sum <= r.sum``,
  rw[Subgroup_def, principal_ideal_group, principal_ideal_def] >>
  rw[coset_def, SUBSET_DEF] >>
  rw[]);

(* Theorem: <p>.sum << r.sum *)
(* Proof: for a normal subgroup:
   (1) <p>.sum <= r.sum,
       true by principal_ideal_subgroup
   (2) p IN R /\ a IN R ==> IMAGE (\z. a + z) <p>.sum.carrier = IMAGE (\z. z + a) <p>.sum.carrier
       true ring_add_comm and EXTENSION.
*)
val principal_ideal_subgroup_normal = store_thm(
  "principal_ideal_subgroup_normal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p>.sum << r.sum``,
  rw[normal_subgroup_alt, coset_def, right_coset_def] >| [
    rw[principal_ideal_subgroup],
    rw[principal_ideal_def, coset_def, EXTENSION] >>
    `!x. x IN R ==> (a + p * x = p * x + a)` by rw[ring_add_comm] >>
    metis_tac[]
  ]);

(* Theorem: <p> is an ideal: <p> << r. *)
(* Proof: by ideal_def
   (1) <p>.sum <= r.sum
       True by principal_ideal_subgroup.
   (2) x IN p * R /\ y IN R ==> x * y IN p * R
       x = p * u   for some u IN R
       x * y = (p * u) * y
             = p * (u * y)     by ring_mult_assoc
       Hence x * y IN p * R.
   (3) x IN p * R /\ y IN R ==> y * x IN p * R
       Use above and y * x = x * y   by ring_mult_comm
*)
val principal_ideal_ideal = store_thm(
  "principal_ideal_ideal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p> << r``,
  rpt strip_tac >>
  `<p>.carrier = p * R` by metis_tac[principal_ideal_property] >>
  rw[ideal_def, principal_ideal_def, principal_ideal_subgroup] >| [
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `x * y = p * (u * y)` by rw[ring_mult_assoc] >>
    metis_tac[principal_ideal_element, ring_mult_element],
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `y * (p * u) = p * u  * y` by rw[ring_mult_comm] >>
    `_ = p * (u * y)` by rw[ring_mult_assoc] >>
    metis_tac[principal_ideal_element, ring_mult_element]
  ]);

(* Theorem: A principal ideal has all ideals of its elements:
            p IN R /\ q IN <p>.carrier ==> <q> << <p> *)
(* Proof:
   First, q IN R    by principal_ideal_element, ring_mult_element
   thus  <p> << r   by principal_ideal_ideal
   and   <q> << r   by principal_ideal_ideal
   By ideal_def, this is to show:
   (1) <q>.sum <= <p>.sum
       By Subgroup_def, this is to show:
       (a) Group <q>.sum, true by ideal_has_subgroup and Subgroup_def.
       (b) Group <p>.sum, true by ideal_has_subgroup and Subgroup_def.
       (c) <q>.sum.carrier SUBSET <p>.sum.carrier,
           or, x IN <q>.sum.carrier ==> x IN <p>.sum.carrier
           Since q IN <p>.carrier,
               q = p * z   for some z IN R, by principal_ideal_def
           x = q * k       for some k IN R, by principal_ideal_def
             = p * (z * k) by ring_mult_assoc
           hence x IN <p>.carrier.
       (d) <q>.sum.op = <p>.sum.op, true by ideal_ops.
   (2) <q>.sum.carrier = <q>.carrier, true by ideal_carriers.
   (3) <q>.prod.carrier = <q>.carrier, true by ideal_carriers.
   (4) <q>.prod.op = <p>.prod.op, true by ideal_ops.
   (5) <q>.prod.id = <p>.prod.id, true by ideal_def.
   (6) x IN <q>.carrier /\ y IN <q>.carrier ==> <p>.prod.op x y IN <q>.carrier, true by ideal_product_property.
       y IN <q>.carrier ==> y IN R    by ideal_element_property
       <p>.prod.op = r.prod.op        by ideal_ops
       Hence true by ideal_product_property.
   (7) Similar to (6), also by ideal_product_property
*)
val principal_ideal_has_principal_ideal = store_thm(
  "principal_ideal_has_principal_ideal",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN <p>.carrier ==> (<q> << <p>)``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `q IN R` by metis_tac[principal_ideal_element, ring_mult_element] >>
  `<q> << r` by rw[principal_ideal_ideal] >>
  rw[ideal_def] >| [
    rw[Subgroup_def] >-
    metis_tac[ideal_has_subgroup, Subgroup_def] >-
    metis_tac[ideal_has_subgroup, Subgroup_def] >-
   (`<q>.carrier SUBSET <p>.carrier` suffices_by metis_tac[ideal_carriers] >>
    `?z. z IN R /\ (q = p * z)` by metis_tac[principal_ideal_element] >>
    rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
    qexists_tac `z * z'` >>
    rw[ring_mult_assoc]) >>
    metis_tac[ideal_ops],
    metis_tac[ideal_carriers],
    metis_tac[ideal_carriers],
    metis_tac[ideal_ops],
    metis_tac[ideal_def],
    metis_tac[ideal_element_property, ideal_ops, ideal_product_property],
    metis_tac[ideal_element_property, ideal_ops, ideal_product_property]
  ]);

(* Theorem: if elements are associates, their principal ideals are equal.
            p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> <p> = <q>  *)
(* Proof:
   First, <p> << r     by principal_ideal_ideal
      and <q> << r     by principal_ideal_ideal
      and u IN R       by ring_unit_element
   By ideal_eq_ideal, only need to show: <p>.carrier = <q>.carrier
   Let x IN <p>.carrier,
   i.e. x = p * z      for some z
          = q * u * z  given p = q * u
          = q * (u * z)
   Hence x IN <q>.carrier. Thus <p>.carrier SUBSET <q>.carrier.
   But u has |/u IN R    by ring_unit_inv_element
     p * |/u
   = q * u * |/u         given p = q * u
   = q * (u * |/u)       by ring_mult_assoc
   = q * #1              by ring_unit_rinv
   = q                   by ring_mult_rone
   Hence using the same argument gives <q>.carrier SUBSET <p>.carrier.
   or <p>.carrier = <q>.carrier    by SUBSET_ANTISYM
*)
val principal_ideal_eq_principal_ideal = store_thm(
  "principal_ideal_eq_principal_ideal",
  ``!r:'a ring. Ring r ==> !p q u. p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> (<p> = <q>)``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `<q> << r` by rw[principal_ideal_ideal] >>
  `u IN R` by rw[ring_unit_element] >>
  `<p>.carrier = <q>.carrier` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `u * z` >>
    rw[ring_mult_assoc],
    `|/u IN R` by rw[ring_unit_inv_element] >>
    qexists_tac `|/u * z` >>
    `q * u * ( |/ u * z) = q * (u * |/ u * z)` by rw[ring_mult_assoc] >>
    rw[ring_unit_rinv]
  ]);
(* Note: the converse can be proved only in integral domain. *)

(* Theorem: i << r /\ p IN R ==> (p IN I <=> <p> << i) *)
(* Proof:
   First, <p> << r    by principal_ideal_ideal
   If part: p IN I ==> <p> << i
   By ideal_def, this is to show:
   (1) <p>.sum <= i.sum
       By Subgroup_def, this is to show:
       (a) Group <p>.sum, true by ideal_has_subgroup, Subgroup_def
       (b) Group i.sum, true by ideal_has_subgroup, Subgroup_def
       (c) <p>.carrier SUBSET I
           By principal_ideal_def, this is to show:
           p IN I /\ z IN R ==> p * z IN I, true by ideal_product_property
   (2) <p>.prod.id = i.prod.id
       <p>.prod.id = r.prod.id    by ideal_def
       i.prod.id = r.prod.id      by ideal_def
       Hence true.
   (3) x IN <p>.carrier /\ y IN I ==> x * y IN <p>.carrier
       Since y IN I ==> y IN R    by ideal_element_property
       This is true by ideal_product_property.
   (4) x IN <p>.carrier /\ y IN I ==> y * x IN <p>.carrier
       Since y IN I ==> y IN R    by ideal_element_property
       This is also true by ideal_product_property.
   Only-if part: p IN R /\ <p> << i ==> p IN I
     p IN <p>.carrier           by principal_ideal_has_element
     hence p IN i.sum.carrier   by ideal_element
     or p IN I since i.sum.carrier = I   by ideal_carriers.
*)
val ideal_has_principal_ideal = store_thm(
  "ideal_has_principal_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> !p. p IN R ==> (p IN I <=> (<p> << i))``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  rw[EQ_IMP_THM] >| [
    `!j. j << r ==> (j.sum.carrier = J)` by metis_tac[ideal_carriers] >>
    `!j. j << r ==> (j.prod.carrier = J)` by metis_tac[ideal_carriers] >>
    `!j. j << r ==> (j.sum.op = r.sum.op)` by metis_tac[ideal_ops] >>
    `!j. j << r ==> (j.prod.op = r.prod.op)` by metis_tac[ideal_ops] >>
    rw[ideal_def] >| [
      `Group <p>.sum` by metis_tac[ideal_has_subgroup, Subgroup_def] >>
      `Group i.sum` by metis_tac[ideal_has_subgroup, Subgroup_def] >>
      rw[Subgroup_def] >>
      rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
      rw[ideal_product_property],
      metis_tac[ideal_def],
      metis_tac[ideal_element_property, ideal_product_property],
      metis_tac[ideal_element_property, ideal_product_property]
    ],
    metis_tac[principal_ideal_has_element, ideal_element, ideal_carriers]
  ]);

(* ------------------------------------------------------------------------- *)
(* Trivial Ideal                                                             *)
(* ------------------------------------------------------------------------- *)

(* use overloading for ring ideal zero *)
val _ = overload_on ("<#0>", ``principal_ideal r #0``);

(* Theorem: <#0>.carrier = {#0} *)
(* Proof: by definitions, this is to show:
   (1) z IN R ==> #0 * z = #0, true by ring_mult_lzero.
   (2) ?z. (#0 = #0 * z) /\ z IN R, let z = #0, true by ring_mult_zero_zero.
*)
val zero_ideal_sing = store_thm(
  "zero_ideal_sing",
  ``!r:'a ring. Ring r ==> (<#0>.carrier = {#0})``,
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >>
  metis_tac[ring_mult_zero_zero, ring_zero_element]);

(* Theorem: <#0> << r *)
(* Proof:
   Since #0 IN R    by ring_zero_element
   This follows     by principal_ideal_ideal.
*)
val zero_ideal_ideal = store_thm(
  "zero_ideal_ideal",
  ``!r:'a ring. Ring r ==> <#0> << r``,
  rw[principal_ideal_ideal]);

(* Theorem: SING I <=> i = <#0> *)
(* Proof: This is to show:
   (1) i << r /\ SING I ==> i = <#0>
       Since #0 IN I      by ideal_has_zero
       I = {#0}           by SING_DEF, IN_SING
         = <#0>.carrier   by zero_ideal_sing
       but <#0> << r      by zero_ideal_ideal
       hence i = <#0>     by ideal_eq_ideal
   (2) SING <#0>.carrier
       Since <#0>.carrier = {#0}   by zero_ideal_sing
       hence true                  by SING_DEF
*)
val ideal_carrier_sing = store_thm(
  "ideal_carrier_sing",
  ``!r i:'a ring. Ring r /\ i << r ==> (SING I <=> (i = <#0>))``,
  rw[EQ_IMP_THM] >| [
    `#0 IN I` by rw[ideal_has_zero] >>
    `I = {#0}` by metis_tac[SING_DEF, IN_SING] >>
    metis_tac[ideal_eq_ideal, zero_ideal_ideal, zero_ideal_sing],
    rw[zero_ideal_sing]
  ]);

(* ------------------------------------------------------------------------- *)
(* Sum of Ideals                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define sum of ideals *)
val ideal_sum_def = Define `
  ideal_sum (r:'a ring) (i:'a ring) (j:'a ring) =
      <| carrier := {x + y | x IN I /\ y IN J};
             sum := <| carrier := {x + y | x IN I /\ y IN J}; op := r.sum.op; id := r.sum.id |>;
            prod := <| carrier := {x + y | x IN I /\ y IN J}; op := r.prod.op; id := r.prod.id |>
       |>
`;
val _ = overload_on ("+", ``ideal_sum r``);

(* Theorem: x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z) *)
(* Proof: by definition. *)
val ideal_sum_element = store_thm(
  "ideal_sum_element",
  ``!(i:'a ring) (j:'a ring) x. x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z)``,
  rw[ideal_sum_def] >>
  metis_tac[]);

(* Theorem: i << r /\ j << r ==> i + j = j + i *)
(* Proof:
   By ideal_sum_def, this is to show:
   {x + y | x IN I /\ y IN J} = {x + y | x IN J /\ y IN I}
   Since !z. z IN I ==> z IN R    by ideal_element_property
   This is true by ring_add_comm.
*)
val ideal_sum_comm = store_thm(
  "ideal_sum_comm",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j = j + i)``,
  rw[ideal_sum_def, EXTENSION] >>
  metis_tac[ideal_element_property, ring_add_comm]);

(* Theorem: i << r /\ j << r ==>  Group (i + j).sum *)
(* Proof: by group definition, this is to show:
   for x = x' + y', y = x'' + y'', z = x''' + y''', x, y, z in (i + j).sum,
   Note !z. z IN I ==> z IN R /\ z IN J ==> z IN R     by ideal_element_property
   (1) ?x y. x IN I /\ y IN J /\ (x' + y' + (x'' + y'') = x + y)
       x' + y' + (x'' + y'') = (x' + x'') + (y' + y'')      by ring_add_assoc, ring_add_comm
       Let x = x' + x'', y = y' + y'', then x IN I, y IN J  by ideal_property
   (2) x' + y' + (x'' + y'') + (x''' + y''') = x' + y' + (x'' + y'' + (x''' + y'''))
       True by ring_add_assoc.
   (3) ?x y. x IN I /\ y IN J /\ (#0 = x + y)
       Let x = #0, y = #0, and #0 IN I, #0 IN J by ideal_has_zero.
       True by ring_add_zero_zero.
   (4) #0 + (x' + y) = x' + y
       True by ring_add_lzero.
   (5) x' IN J /\ y IN J ==> ?y'. (?x y. x IN I /\ y IN J /\ (y' = x + y)) /\ (y' + (x' + y) = #0)
       Let y' = -(x' + y) = -x' + -y   by ring_neg_add
       -x' IN I and -y IN J            by ideal_has_neg
       Hence true by ring_add_lneg.
*)
val ideal_sum_group = store_thm(
  "ideal_sum_group",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> Group (i + j).sum``,
  rpt strip_tac >>
  (`!z. z IN {x + y | x IN I /\ y IN J} <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[] >> metis_tac[])) >>
  `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
  rw_tac std_ss[ideal_sum_def, group_def_alt] >| [
    `x' + y' + (x'' + y'') = x' + (y' + x'' + y'')` by rw[ring_add_assoc] >>
    `_ = x' + (x'' + y' + y'')` by rw[ring_add_comm] >>
    `_ = (x' + x'') + (y' + y'')` by rw[ring_add_assoc] >>
    `x' + x'' IN I /\ y' + y'' IN J` by rw[ideal_property] >>
    metis_tac[],
    rw[ring_add_assoc],
    `#0 IN I /\ #0 IN J` by rw[ideal_has_zero] >>
    metis_tac[ring_add_zero_zero],
    rw[],
    `-(x' + y) = -x' + -y` by rw[ring_neg_add] >>
    `-x' IN I /\ -y IN J` by rw[ideal_has_neg] >>
    qexists_tac `-(x' + y)` >>
    rw[] >>
    metis_tac[]
  ]);

(* Theorem: i << r /\ j << r ==> i.sum <= (i + j).sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group i.sum,
       Since i.sum << r.sum   by ideal_def, true by Subgroup_def.
   (2) i << r /\ j << r ==> Group (i + j).sum
       True by ideal_sum_group.
   (3) i.sum.carrier SUBSET (i + j).sum.carrier
       i.e. x IN I ==> ?y. y IN J /\ x = x + y,
       so take y = #0, and #0 IN J by ideal_has_zero.
   (4) x IN I /\ y IN I ==> i.sum.op x y = (i + j).sum.op x y
       True by ideal_ops.
*)
val ideal_subgroup_ideal_sum = store_thm(
  "ideal_subgroup_ideal_sum",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> i.sum <= (i + j).sum``,
  rw[Subgroup_def] >| [
    metis_tac[ideal_def, Subgroup_def],
    rw[ideal_sum_group],
    rw[ideal_sum_def, SUBSET_DEF] >>
    metis_tac[ideal_def, ideal_has_zero, ring_add_rzero, ideal_element_property],
    rw[ideal_sum_def] >>
    metis_tac[ideal_ops]
  ]);

(* Theorem: i << r /\ j << r ==> (i + j).sum <= r.sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group (i + j).sum,
       True by ideal_sum_group.
   (2) (i + j).sum.carrier SUBSET R
       By ideal_sum_def, and SUBSET_DEF, this is to show:
       x' IN I /\ y IN J ==> x' + y IN R
       But x' IN R /\ y IN R   by ideal_element_property
       hence true by ring_add_element.
   (3) x IN (i + j).sum.carrier /\ y IN (i + j).sum.carrier ==> (i + j).sum.op x y = x + y
       True by ideal_sum_def.
*)
val ideal_sum_subgroup = store_thm(
  "ideal_sum_subgroup",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j).sum <= r.sum``,
  rw[Subgroup_def] >| [
    rw[ideal_sum_group],
    rw[ideal_sum_def, SUBSET_DEF] >>
    metis_tac[ideal_element_property, ring_add_element],
    rw[ideal_sum_def]
  ]);

(* Theorem: i << r /\ j << r ==> i << i + j *)
(* Proof: by definition, this is to show:
   (1) i.sum <= (i + j).sum, true by ideal_subgroup_ideal_sum.
   (2) i.sum.carrier = I, true by ideal_def.
   (3) i.prod.carrier = I, true by ideal_def.
   (4) i.prod.op = (i + j).prod.op, true by ideal_sum_def, ideal_ops.
   (5) i.prod.id = (i + j).prod.id, true by ideal_sum_def, ideal_def.
   (6) x IN I /\ y IN (i + j).carrier ==> (i + j).prod.op x y IN I
       i.e. x * y IN I
       Since y IN (i + j).carrier, y IN R  by ideal_element_property, ring_add_element
       Hence x * y IN I by ideal_def.
   (7) x IN I /\ y IN (i + j).carrier ==> (i + j).prod.op y x IN I
       i.e. y * x IN I
       By same reasoning above, apply ring_mult_comm.
*)
val ideal_sum_has_ideal = store_thm(
  "ideal_sum_has_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> i << (i + j)``,
  rpt strip_tac >>
  rw[ideal_def] >-
  rw[ideal_subgroup_ideal_sum] >-
  metis_tac[ideal_def] >-
  metis_tac[ideal_def] >-
 (rw[ideal_sum_def] >>
  metis_tac[ideal_ops]) >-
 (rw[ideal_sum_def] >>
  metis_tac[ideal_def]) >-
 (rw[ideal_sum_def] >>
  (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
  metis_tac[ideal_element_property, ring_add_element, ideal_def]) >>
  rw[ideal_sum_def] >>
  (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
  metis_tac[ideal_element_property, ring_add_element, ring_mult_comm, ideal_def]);

(* Theorem: i << r /\ j << r ==> j << i + j *)
(* Proof: by ideal_sum_has_ideal and ideal_sum_comm. *)
val ideal_sum_has_ideal_comm = store_thm(
  "ideal_sum_has_ideal_comm",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> j << (i + j)``,
  metis_tac[ideal_sum_has_ideal, ideal_sum_comm]);

(* Theorem: i << r /\ j << r ==> i + j << r *)
(* Proof: by definition, this is to show:
   (1) (i + j).sum <= r.sum, true by ideal_sum_subgroup.
   (2) (i + j).sum.carrier = (i + j).carrier, true by ideal_sum_def.
   (3) (i + j).prod.carrier = (i + j).carrier, true by ideal_sum_def.
   (4) (i + j).prod.op = $*, true by ideal_sum_def.
   (5) (i + j).prod.id = #1, true by ideal_sum_def.
   (6) x IN (i + j).carrier /\ y IN R ==> x * y IN (i + j).carrier
       Since x = p + q    with p IN I and q IN J
       x * y = (p + q) * y
             = p * y + q * y           by ring_mult_ladd
       But p * y IN I and q * y IN J   by ideal_def
       hence x * y IN (i + j).carrier.
   (7) x IN (i + j).carrier /\ y IN R ==> y * x IN (i + j).carrier
       Same reasoning above, using ring_mult_radd.
*)
val ideal_sum_ideal = store_thm(
  "ideal_sum_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j) << r``,
  rpt strip_tac >>
  rw[ideal_def] >| [
    rw[ideal_sum_subgroup],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
    `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
    `?p q. p IN I /\ q IN J /\ (x = p + q)` by metis_tac[] >>
    `x * y = (p + q) * y` by rw[] >>
    `_ = p * y + q * y` by rw[ring_mult_ladd] >>
    `p * y IN I /\ q * y IN J` by metis_tac[ideal_def] >>
    metis_tac[],
    (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
    `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
    `?p q. p IN I /\ q IN J /\ (x = p + q)` by metis_tac[] >>
    `y * x = y * (p + q)` by rw[] >>
    `_ = y * p + y * q` by rw[ring_mult_radd] >>
    `y * p IN I /\ y * q IN J` by metis_tac[ideal_def] >>
    metis_tac[]
  ]);

(* Theorem: i << r /\ j << r ==> (i + j << j <=> i << j) *)
(* Proof:
   By ideal_sub_ideal, this is to show:
   (i + j).carrier SUBSET J <=> I SUBSET J
   Expand by ideal_sum_element, this is to show:
   (1) x IN I /\ !x. (?y z. y IN I /\ z IN J /\ (x = y + z)) ==> x IN J ==> x IN J ==> x IN J
       x IN I ==> x IN R                      by ideal_element_property
       j << r ==> #0 IN J                     by ideal_has_zero
       x = x + #0                             by ring_add_rzero
       Hence x IN (i + j).carrier             by ideal_sum_element
       and x IN J                             by given implication
   (2) y IN I /\ z IN J /\ !x. x IN I ==> x IN J ==> y + z IN J
       y IN I ==> y IN J                      by implication
       Hence y + z IN J                       by ideal_property
*)
val ideal_sum_sub_ideal = store_thm(
  "ideal_sum_sub_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i + j) << j <=> i << j)``,
  rpt strip_tac >>
  `(i + j) << r` by rw[ideal_sum_ideal] >>
  `(i + j).carrier SUBSET J <=> I SUBSET J` suffices_by metis_tac[ideal_sub_ideal] >>
  rw[ideal_sum_element, SUBSET_DEF, EQ_IMP_THM] >| [
    `x IN R /\ #0 IN J` by metis_tac[ideal_element_property, ideal_has_zero] >>
    `x = x + #0` by rw[] >>
    metis_tac[],
    rw[ideal_property]
  ]);

(* Theorem: i << r /\ p IN I ==> <p> + i = i *)
(* Proof:
   Since i << r,
         p IN I ==> p IN R    by ideal_element_property
   thus  <p> << r             by principal_ideal_ideal
   and   <p> + i << r         by ideal_sum_ideal
   By ideal_eq_ideal, only need to show:
     (<p> + i).carrier = I
   By ideal_sum_def, need to show:
   (1) x' IN <p>.carrier /\ y IN I ==> x' + y IN I
       Since ?z. z IN R /\ (x' = p * z)  by principal_ideal_element
       x' IN I by ideal_product_property (or ideal_def)
       thus x' + y IN I by ideal_property.
   (2) p IN I /\ x IN I ==> ?x' y. (x = x' + y) /\ x' IN <p>.carrier /\ y IN I
       Since x = #0 + x      by ring_add_lzero
       and #0 IN <p>.carrier by principal_ideal_ideal, ideal_has_zero
       Let x' = #0, y = x, hence true.
*)
val principal_ideal_sum_eq_ideal = store_thm(
  "principal_ideal_sum_eq_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> !p. p IN I ==> (<p> + i = i)``,
  rpt strip_tac >>
  `<p> << r` by metis_tac[principal_ideal_ideal, ideal_element_property] >>
  `(<p> + i) << r` by rw[ideal_sum_ideal] >>
  `(<p> + i).carrier = I` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[ideal_sum_def, EXTENSION, EQ_IMP_THM] >| [
    `?z. z IN R /\ (x' = p * z)` by metis_tac[principal_ideal_element] >>
    metis_tac[ideal_def, ideal_property],
    `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
    `x = #0 + x` by rw[] >>
    metis_tac[principal_ideal_ideal, ideal_has_zero]
  ]);

(* Theorem: i << r /\ p IN I <=> p IN R /\ (<p> + i = i) *)
(* Proof:
   If part: i << r /\ p IN I ==> p IN R /\ (<p> + i = i)
     the part: p IN I ==> p IN R, true by ideal_element_property.
     the part: p IN I ==> <p> + i = i, true by principal_ideal_sum_eq_ideal.
   Only-if part: i << r /\ p IN R /\ (<p> + i = i) ==> p IN I
     Since <p> << r                  by principal_ideal_ideal
     <p> << (<p> + i)                by ideal_sum_has_ideal
         p IN <p>.carrier            by principal_ideal_has_element
     ==> p IN (<p> + i).sum.carrier  by ideal_element
     or  p IN (<p> + i).carrier      by ideal_carriers
     ==> p IN I                      by given: <p> + i = i
*)
val principal_ideal_sum_equal_ideal = store_thm(
  "principal_ideal_sum_equal_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> (!p. p IN I <=> p IN R /\ (<p> + i = i))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ideal_element_property] >-
  rw[principal_ideal_sum_eq_ideal] >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `<p> << (<p> + i)` by rw[ideal_sum_has_ideal] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `p IN (<p> + i).carrier` by metis_tac[ideal_element, ideal_carriers] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Maximal Ideals                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define maximal ideal *)
val ideal_maximal_def = Define `
  ideal_maximal (r:'a ring) (i:'a ring) <=>
    (i << r) /\
    (!j:'a ring. i << j /\ j << r ==> (i = j) \/ (j = r))
`;

(* use overloading *)
val _ = overload_on ("maxi", ``ideal_maximal r``);

(* ------------------------------------------------------------------------- *)
(* Irreduicables in Ring                                                     *)
(* ------------------------------------------------------------------------- *)

(* A ring element is irreducible if it is non-zero and non-unit, and its only factors are trivial. *)
val irreducible_def = Define`
  irreducible (r:'a ring) (z:'a) <=>
    (z IN R+) /\ ~(unit z) /\
    (!x y. x IN R /\ y IN R /\ (z = x * y) ==> (unit x) \/ (unit y))
`;

(* use overloading *)
val _ = overload_on ("atom", ``irreducible r``);

(*
- irreducible_def;
> val it = |- !r z. atom z <=> z IN R+ /\ z NOTIN R* /\ !x y. x IN R /\ y IN R /\ (z = x * y) ==> unit x \/ unit y : thm
*)

(* Theorem: atom p ==> p IN R *)
(* Proof:
   atom p ==> p IN R+       by irreducible_def
          ==> p IN R        by ring_nonzero_element
*)
val irreducible_element = store_thm(
  "irreducible_element",
  ``!r:'a ring. !p. atom p ==> p IN R``,
  rw[irreducible_def, ring_nonzero_element]);

(* ------------------------------------------------------------------------- *)
(* Principal Ideal Ring                                                      *)
(* ------------------------------------------------------------------------- *)

(* A principal ideal ring = a ring with all ideals being principal ideals. *)
val PrincipalIdealRing_def = Define`
  PrincipalIdealRing (r:'a ring) <=>
    (Ring r) /\
    (!(i:'a ring). i << r ==> ?p. p IN R /\ (<p> = i))
`;
(*
> val PrincipalIdealRing_def = |- !r. PrincipalIdealRing r <=> Ring r /\ !i. i << r ==> ?p. p IN R /\ (<p> = i)
*)

(* Theorem: For a principal ideal ring, an irreducible element generates a maximal ideal *)
(* Proof:
   By definitions, this is to show:
   (1) p IN R+ ==>  <p> << r,
       p IN R+ ==> p IN R           by ring_nonzero_element
       Hence true                   by principal_ideal_ideal.
   (2) <p> << j /\ j << r ==> (<p> = j) \/ (j = r)
      Since r is a principal ring, ?q. q IN R /\ (<q> = j).
      p IN R+ ==> p IN R            by ring_nonzero_element
      p IN <p>.carrier              by principal_ideal_has_element
      p IN <q>.carrier              by ideal_element
      so ?u. u IN R /\ (p = q * u)  by principal_ideal_element
      hence unit q or unit u        by ideal_maximal_def
      If unit q,
        Since q IN <q>.carrier      by principal_ideal_has_element
         unit q IN <q>.carrier
        hence <q> = j = r           by ideal_with_unit
      If unit u,
        <p> = <q>                   by principal_ideal_eq_principal_ideal.
*)
val principal_ideal_ring_ideal_maximal = store_thm(
  "principal_ideal_ring_ideal_maximal",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> maxi <p>``,
  rw[PrincipalIdealRing_def, irreducible_def, ideal_maximal_def] >-
  rw[principal_ideal_ideal, ring_nonzero_element] >>
  `?q. q IN R /\ (<q> = j)` by rw[] >>
  `p IN R` by rw[ring_nonzero_element] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `p IN <q>.carrier` by metis_tac[ideal_element, principal_ideal_property] >>
  `?u. u IN R /\ (p = q * u)` by metis_tac[principal_ideal_element] >>
  `unit q \/ unit u` by rw[] >-
  metis_tac[principal_ideal_has_element, ideal_with_unit] >>
  metis_tac[principal_ideal_eq_principal_ideal]);

(* ------------------------------------------------------------------------- *)
(* Euclidean Ring                                                            *)
(* ------------------------------------------------------------------------- *)

(* A Euclidean Ring is a ring with a norm function f for division algorithm. *)
val EuclideanRing_def = Define`
  EuclideanRing (r:'a ring) (f:'a -> num) <=>
    (Ring r) /\
    (!x. (f x = 0) <=> (x = #0)) /\
    (!x y:'a. x IN R /\ y IN R /\ y <> #0 ==>
     ?q t:'a. q IN R /\ t IN R /\ (x = q * y + t) /\ f(t) < f(y))
`;

(* Theorem: EuclideanRing r ==> Ring r *)
val euclid_ring_ring = save_thm("euclid_ring_ring",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                   |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_ring = |- !r f. EuclideanRing r f ==> Ring r : thm *)

(* Theorem: EuclideanRing r ==> !x. (f x = 0) <=> (x = #0) *)
val euclid_ring_map = save_thm("euclid_ring_map",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                   |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_map = |- !r f. EuclideanRing r f ==> !x. (f x = 0) <=> (x = #0) : thm *)

(* Theorem: EuclideanRing property:
            !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y  *)
(* Proof: by EuclideanRing_def. *)
(*
val euclid_ring_property = store_thm(
  "euclid_ring_property",
  ``!r:'a ring. !f. EuclideanRing r f ==>
   !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = y * q + t) /\ f t < f y``,
  rw[EuclideanRing_def]); -- Note: not by metis_tac!
*)
val euclid_ring_property = save_thm("euclid_ring_property",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                      |> UNDISCH_ALL |> CONJUNCTS |> last |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_property = |- !r f.  EuclideanRing r f ==> !x y. x IN R /\ y IN R /\ y <> #0 ==>
                                ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y : thm *)

(* Theorem: ideal generator exists:
            Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0))
            ==> ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ f z < f p ==> z = #0        *)
(* Proof:
   Since #0 IN R,            by ring_zero_element
   <#0> << r                 by principal_ideal_ideal
   Since <#0>.carrier = {#0} by zero_ideal_sing
   i.carrier <> {#0}         by ideal_eq_ideal
   Since #0 IN I,            by ideal_has_zero
   there is x IN I, x <> #0  by ONE_ELEMENT_SING
   and f x <> 0              by condition on f
   Thus f x IN s, where s = IMAGE f I DELETE 0
   Let p IN I such that f p = MIN_SET s
   then for any z IN s,
   z IN I /\ z <> #0         by IN_IMAGE
   and  f p <= f z           by MIN_SET_LEM
*)
val ideal_gen_exists = store_thm(
  "ideal_gen_exists",
  ``!r i:'a ring. Ring r /\ i << r /\ i <> <#0> ==> !f:'a -> num. (!x. (f x = 0) <=> (x = #0))
    ==> ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z``,
  rpt strip_tac >>
  `<#0> << r` by rw[principal_ideal_ideal] >>
  `i.carrier <> {#0}` by metis_tac[ideal_eq_ideal, zero_ideal_sing] >>
  `?x. x IN I /\ x <> #0` by metis_tac[ONE_ELEMENT_SING, ideal_has_zero, MEMBER_NOT_EMPTY] >>
  `f x IN (IMAGE f I)` by rw[] >>
  `f x <> 0` by rw[] >>
  `IMAGE f I DELETE 0 <> {}` by metis_tac[IN_DELETE, MEMBER_NOT_EMPTY] >>
  qabbrev_tac `s = IMAGE f I DELETE 0` >>
  `MIN_SET s IN s /\ !x. x IN s ==> MIN_SET s <= x` by metis_tac[MIN_SET_LEM] >>
  `?p. p IN I /\ p <> #0 /\ (f p = MIN_SET s)` by metis_tac[IN_IMAGE, IN_DELETE] >>
  metis_tac[IN_IMAGE, IN_DELETE]);

(* Apply Skolemization *)
val lemma = prove(
  ``!r i f. ?p. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0))
       ==> p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z``,
  metis_tac[ideal_gen_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define ideal generator *)
(*
- SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma;
> val it = |- ?f. !r i f'.
           Ring r /\ i << r /\ i <> <#0> /\ (!x. (f' x = 0) <=> (x = #0)) ==>
           f r i f' IN I /\ f r i f' <> #0 /\ !z. z IN I /\ z <> #0 ==> f' (f r i f') <= f' z : thm
*)
val ideal_gen_def = new_specification(
    "ideal_gen_def",
    ["ideal_gen"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma
    |> CONV_RULE (RENAME_VARS_CONV ["h", "r", "i", "f"])); (* replace f r i f' by h r i f *)
(* val ideal_gen_def = |- !r i f. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0)) ==>
        ideal_gen r i f IN I /\ ideal_gen r i f <> #0 /\ !z. z IN I /\ z <> #0 ==> f (ideal_gen r i f) <= f z : thm *)

(* Theorem: property of ideal generator:
            !z. z IN I ==> (f z < f (ideal_gen r i f) <=> z = #0) *)
(* Proof:
   If part: f z < f (ideal_gen r i f) ==> z = #0
     By contradicton, assume z <> #0,
     then f (ideal_gen r i f) <= f z   by ideal_gen_def
     which contradicts f z < f (ideal_gen r i f).
   Only-if part: z = #0 ==> f z < f (ideal_gen r i f)
     (ideal_gen r i f) <> #0           by ideal_gen_def
     hence f (ideal_gen r i f) <> 0    by given f: f x = 0 <=> x = #0
     Since f #0 = 0                    by given f above
     This is true.
*)
val ideal_gen_minimal = store_thm(
  "ideal_gen_minimal",
  ``!r i:'a ring. Ring r /\ i << r /\ i <> <#0> ==> !f:'a -> num. (!x. (f x = 0) <=> (x = #0))
   ==> !z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))``,
  rw[ideal_gen_def, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `f (ideal_gen r i f) <= f z` by metis_tac[ideal_gen_def] >>
    decide_tac,
    `(ideal_gen r i f) <> #0` by metis_tac[ideal_gen_def] >>
    `f (ideal_gen r i f) <> 0 /\ (f #0 = 0)` by metis_tac[] >>
    decide_tac
  ]);

(* Theorem: EuclideanRing f r ==> PrincipalIdealRing r *)
(* Proof:
   First,
   EuclideanRing r f ==> Ring r by EuclideanRing_def
   By PrincipalIdealRing_def, this is to show:
     !i. i << r ==> ?p. p IN R /\ (<p> = i)
   If i = <#0>, it is generated by #0.
   If i <> <#0>,
   Let p = ideal_gen r i f
   Then p IN I /\ p <> #0       by ideal_gen_def
   and for any x IN I, x IN R   by ideal_element_property
   By EuclideanRing_Def,
   there exists y IN R, t IN R
   such that  x = y * p + t     with (f t) < (f p)
   or  x = p * y + t            by ring_mult_comm
   Since p * y IN I             by ideal_product_property
   t = x - p * y IN I           by ideal_has_diff
   Thus t = #0                  by ideal_gen_minimal
   or x = p * y,
   so x IN <p>.carrier          by principal_ideal_element
   i.e. I SUBSET <p>.carrier    by SUBSET_DEF
   On the other hand,
   p IN I ==> <p> << i          by ideal_has_principal_ideal
   so !x IN <p>.carrier ==> x IN I   by ideal_element
   i.e. <p>.carrier SUBSET I    by SUBSET_DEF
   so <p>.carrier = I           by SUBSET_ANTISYM
   Hence <p> = i                by ideal_eq_ideal.
*)
val euclid_ring_principal_ideal_ring = store_thm(
  "euclid_ring_principal_ideal_ring",
  ``!r:'a ring. !f. EuclideanRing r f ==> PrincipalIdealRing r``,
  rw[EuclideanRing_def, PrincipalIdealRing_def] >>
  Cases_on `i = <#0>` >-
  metis_tac[ring_zero_element] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  `ideal_gen r i f IN I /\ ideal_gen r i f <> #0` by metis_tac[ideal_gen_def] >>
  `!z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))` by rw[ideal_gen_minimal] >>
  qabbrev_tac `p = ideal_gen r i f` >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  qexists_tac `p` >>
  rw[] >>
  `<p>.carrier = I` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[ideal_product_property] >>
  `?q t. q IN R /\ t IN R /\ (x = q * p + t) /\ f t < f p` by rw[] >>
  `x = p * q + t` by rw[ring_mult_comm] >>
  `p * q IN I` by metis_tac[ideal_product_property] >>
  `t = x - p * q` by metis_tac[ring_sub_eq_add] >>
  `t IN I` by rw[ideal_has_diff] >>
  `t = #0` by metis_tac[ideal_gen_minimal] >>
  `x = p * q` by rw[] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Ideal under Ring Homomorphism                                             *)
(* ------------------------------------------------------------------------- *)

(* Homomorphic image of ideal *)
(*
val homo_ideal_def = Define`
  homo_ideal (f:'a -> 'b) (r:'a ring) (i:'a ring) =
    <| carrier := IMAGE f I;
           sum := <| carrier := IMAGE f I; op := image_op i.sum f; id := f #0 |>;
          prod := <| carrier := IMAGE f I; op := image_op i.prod f; id := f #1 |>
     |>
`;
*)
val homo_ideal_def = Define`
  homo_ideal (f:'a -> 'b) (r:'a ring) (s:'b ring) (i:'a ring) =
    <| carrier := IMAGE f I;
           sum := <| carrier := IMAGE f I; op := s.sum.op; id := f #0 |>;
          prod := <| carrier := IMAGE f I; op := s.prod.op; id := f #1 |>
     |>
`;

(* Theorem: RingHomo f r s /\ i << r ==> Group (homo_ideal f r s i).sum *)
(* Proof: checking group axioms:
   (1) x IN IMAGE f I /\ y IN IMAGE f I ==> s.sum.op x y IN IMAGE f I
       Let p = CHOICE (preimage f I x),
           q = CHOICE (preimage f I y)
       then p IN I /\ f p = x    by preimage_choice_property
        and q IN I /\ f q = y    by preimage_choice_property
       Since  p + q IN I         by ideal_property
         f (p + q) IN IMAGE f I
       but f (p + q)
       = s.sum.op (f p) (f q)    by RingHomo_def and GroupHomo_def.
   (2) x IN IMAGE f I /\ y IN IMAGE f I /\ z IN IMAGE f I ==> s.sum.op (s.sum.op x y) z = s.sum.op x (s.sum.op y z)
       Let p = CHOICE (preimage f I x)
       Let q = CHOICE (preimage f I y)
       Let t = CHOICE (preimage f I z)
       Then p IN I /\ (f p = x)    by preimage_choice_property
            q IN I /\ (f q = y)    by preimage_choice_property
            t IN I /\ (f t = z)    by preimage_choice_property
       Since !z. z IN I ==> z IN R   by ideal_element_property
       and   !z. z IN R ==> f z IN s.carrier by RingHomo_def
       This is true by ring_add_assoc.
   (3) f #0 IN IMAGE f I
       Since #O IN I    by ideal_has_zero, this is true.
   (4) s.sum.op (f #0) x = x
       Let p = CHOICE (preimage f I x)
       then p IN I /\ f p = x    by preimage_choice_property
         s.sum.op (f #0) x
       = f (#0 + p)              by RingHomo_def, GroupHomo_def
       = f p = x                 by ring_add_lzero
   (5) ?y. y IN IMAGE f I /\ (s.sum.op y x = f #0)
       Let p = CHOICE (preimage f I x)
       Then   p IN I /\ (f p = x)       by preimage_choice_property
       Hence    -p IN I                 by ideal_has_neg
       and  f (-p) IN IMAGE f I
       Let y = f (-p), then
         s.sum.op y x
       = s.sum.op (f (-p)) (f p)
       = f (-p + p)                     by RingHomo_def, GroupHomo_def
       = f #0                           by ring_add_lneg
*)
val ring_homo_ideal_group = store_thm(
  "ring_homo_ideal_group",
  ``!(r:'a ring) (s:'b ring) f.  Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> Group (homo_ideal f r s i).sum``,
  rpt strip_tac >>
  `r.sum.carrier = R` by rw[] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  `i.sum.carrier = I` by metis_tac[ideal_def] >>
  `i.sum.op = r.sum.op` by metis_tac[ideal_ops] >>
  `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
  `!x y. x IN R /\ y IN R ==> (f (x + y) = s.sum.op (f x) (f y))` by metis_tac[GroupHomo_def] >>
  `!z. z IN R ==> f z IN s.carrier` by metis_tac[RingHomo_def] >>
  `s.sum.id = f #0` by rw[ring_homo_zero] >>
  rw_tac std_ss[homo_ideal_def, group_def_alt] >| [
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    qabbrev_tac `q = CHOICE (preimage f I y)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `q IN I /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
    `p + q IN I` by rw[ideal_property] >>
    `f (p + q) IN IMAGE f I` by rw[] >>
    metis_tac[],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    qabbrev_tac `q = CHOICE (preimage f I y)` >>
    qabbrev_tac `t = CHOICE (preimage f I z)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `q IN I /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
    `t IN I /\ (f t = z)` by rw[preimage_choice_property, Abbr`t`] >>
    rw[ring_add_assoc],
    rw[ideal_has_zero],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    metis_tac[ring_add_lzero],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `-p IN I` by rw[ideal_has_neg] >>
    `f (-p) IN IMAGE f I` by rw[] >>
    qexists_tac `f (-p)` >>
    metis_tac[ring_add_lneg]
  ]);

(* Theorem: RingHomo f r s /\ i << r ==> (homo_ideal f r s i).sum <= s.sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group (homo_ideal f r s i).sum
       True by ring_homo_ideal_group.
   (2) (homo_ideal f r s i).sum.carrier SUBSET s.carrier
       i.e. to show: IMAGE f I SUBSET s.carrier
       Since !x. x IN I ==> x IN R            by ideal_element_property
       and   !x. x IN R ==> f x IN s.carrier  by RingHomo_def
       This is true by SUBSET_DEF.
   (3) (homo_ideal f r s i).sum.op = s.sum.op
*)
val ring_homo_ideal_subgroup = store_thm(
  "ring_homo_ideal_subgroup",
  ``!(r:'a ring) (s:'b ring) f.  Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> (homo_ideal f r s i).sum <= s.sum``,
  rw[Subgroup_def] >| [
    rw[ring_homo_ideal_group],
    rw[homo_ideal_def] >>
    rw[SUBSET_DEF] >>
    metis_tac[ideal_element_property, RingHomo_def],
    rw[homo_ideal_def]
  ]);

(* Theorem: Ring homomorphic image of an ideal is still an ideal of the target ring, if the map is surjective.
            RingHomo f r s /\ SURJ f R s.carrier ==> !i. i << r ==> (homo_ideal f r s i) << s  *)
(* Proof: by ideal_def, this is to show:
   (1) (homo_ideal f r s i).sum <= s.sum
       True by ring_homo_ideal_subgroup.
   (2) (homo_ideal f r s i).sum.carrier = (homo_ideal f r s i).carrier
       True by homo_ideal_def.
   (3) (homo_ideal f r s i).prod.carrier = (homo_ideal f r s i).carrier
       True by homo_ideal_def.
   (4) (homo_ideal f r s i).prod.op = s.prod.op
       True by homo_ideal_def.
   (5) (homo_ideal f r s i).prod.id = s.prod.id
       True by homo_ideal_def, ring_homo_one.
   -- so far, no need for surjective, but the next two require surjective.
   (6) x IN (homo_ideal f r s i).carrier /\ y IN s.carrier ==> s.prod.op x y IN (homo_ideal f r s i).carrier
       or, by homo_ideal_def, this is to show:
       x IN IMAGE f I /\ y IN s.carrier ==> s.prod.op x y IN IMAGE f I
       y IN s.carrier = IMAGE f R   by IMAGE_SURJ, due to SURJ f R s.carrier
       Let p = CHOICE (preimage f I x),
           q = CHOICE (preimage f R y)
       Then  p IN I /\ (f p = x)   by preimage_choice_property
             q IN R /\ (f q = y)   by preimage_choice_property
         s.prod.op x y
       = s.prod.op (f p) (f q)
       = f (p * q)                 by RingHomo_def, MonoidHomo_def
       Since  p * q IN I           by ideal_def
       f (p * q) IN IMAGE f I, hence true
   (7) x IN (homo_ideal f r s i).carrier /\ y IN s.carrier ==> s.prod.op y x IN (homo_ideal f r s i).carrier
       Same as (7), apply ring_mult_comm.
*)
val ring_homo_ideal_ideal = store_thm(
  "ring_homo_ideal_ideal",
  ``!(r:'a ring) (s:'b ring) f. Ring r /\ Ring s /\ RingHomo f r s /\ SURJ f R s.carrier ==>
     !i. i << r ==> (homo_ideal f r s i) << s``,
  rpt strip_tac >>
  `r.prod.carrier = R` by metis_tac[Ring_def] >>
  `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
  `!x y. x IN R /\ y IN R ==> (f (x * y) = s.prod.op (f x) (f y))` by metis_tac[MonoidHomo_def] >>
  `!z. z IN R ==> f z IN s.carrier` by metis_tac[RingHomo_def] >>
  `(homo_ideal f r s i).carrier = IMAGE f I` by rw[homo_ideal_def] >>
  `IMAGE f R = s.carrier` by rw[GSYM IMAGE_SURJ] >>
  rw_tac std_ss[ideal_def] >-
  rw[ring_homo_ideal_subgroup] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def, ring_homo_one] >-
 (`y IN IMAGE f R` by metis_tac[] >>
  qabbrev_tac `p = CHOICE (preimage f I x)` >>
  qabbrev_tac `q = CHOICE (preimage f R y)` >>
  `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
  `q IN R /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
  `s.prod.op x y = f (p * q)` by metis_tac[ideal_element_property] >>
  `p * q IN I` by metis_tac[ideal_def] >>
  metis_tac[IN_IMAGE]) >>
  `y IN IMAGE f R` by metis_tac[] >>
  qabbrev_tac `p = CHOICE (preimage f I x)` >>
  qabbrev_tac `q = CHOICE (preimage f R y)` >>
  `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
  `q IN R /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
  `s.prod.op y x = f (q * p)` by metis_tac[ideal_element_property] >>
  `q * p IN I` by metis_tac[ideal_def] >>
  metis_tac[IN_IMAGE]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
