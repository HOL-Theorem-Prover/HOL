(* ------------------------------------------------------------------------- *)
(* Cyclic Group                                                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupCyclic";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "subgroupTheory"; *) *)
(* val _ = load "groupOrderTheory"; *)
open monoidTheory monoidOrderTheory;
open groupTheory subgroupTheory groupOrderTheory;
open groupMapTheory;

(* val _ = load "groupInstancesTheory"; *)
open groupInstancesTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory;

(* val _ = load "helperFunctionTheory"; *)
open helperFunctionTheory;

(* val _ = load "GaussTheory"; *)
open GaussTheory;
open EulerTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* Cyclic Group Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
*)
(* Definitions and Theorems (# are exported):

   Helper Theroems:

   Cyclic Group has a generator:
   cyclic_def              |- !g. cyclic g <=> Group g /\ ?z. z IN G /\ !x. x IN G ==> ?n. x = z ** n
   cyclic_gen_def          |- !g. cyclic g ==> cyclic_gen g IN G /\
                                           !x. x IN G ==> ?n. x = cyclic_gen g ** n
#  cyclic_group            |- !g. cyclic g ==> Group g
   cyclic_element          |- !g. cyclic g ==> !x. x IN G ==> ?n. x = cyclic_gen g ** n
   cyclic_gen_element      |- !g. cyclic g ==> cyclic_gen g IN G
   cyclic_generated_group  |- !g. FiniteGroup g ==> !x. x IN G ==> cyclic (gen x)
   cyclic_gen_order        |- !g. cyclic g /\ FINITE G ==> (ord (cyclic_gen g) = CARD G)
   cyclic_gen_power_order  |- !g. cyclic g /\ FINITE G ==> !n. 0 < n /\ (CARD G MOD n = 0) ==>
                                              (ord (cyclic_gen g ** (CARD G DIV n)) = n)

   cyclic_generated_by_gen         |- !g. cyclic g /\ FINITE G ==> (g = gen (cyclic_gen g))
   cyclic_element_by_gen           |- !g. cyclic g /\ FINITE G ==>
                                      !x. x IN G ==> ?n. n < CARD G /\ (x = cyclic_gen g ** n)
   cyclic_element_in_generated     |- !g. cyclic g /\ FINITE G ==>
                                      !x. x IN G ==> x IN (Gen (cyclic_gen g ** (CARD G DIV ord x)))
   cyclic_finite_has_order_divisor |- !g. cyclic g /\ FINITE G ==>
                                      !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n)

   Cyclic Group Properties:
   cyclic_finite_alt           |- !g. FiniteGroup g ==> (cyclic g <=> ?z. z IN G /\ (ord z = CARD G))
   cyclic_group_comm           |- !g. cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x)
   cyclic_group_abelian        |- !g. cyclic g ==> AbelianGroup g

   Cyclic Subgroups:
   cyclic_subgroup_cyclic      |- !g h. cyclic g /\ h <= g ==> cyclic h
   cyclic_subgroup_condition   |- !g. cyclic g /\ FINITE G ==>
                                  !n. (?h. h <= g /\ (CARD H = n)) <=> n divides CARD G

   Cyclic Group Examples:
   cyclic_uroots_has_primitive |- !g. FINITE G /\ cyclic g ==>
                                  !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)
   cyclic_uroots_cyclic        |- !g. cyclic g ==> !n. cyclic (uroots n)
   add_mod_order_1             |- !n. 1 < n ==> (order (add_mod n) 1 = n)
   add_mod_cylic               |- !n. 0 < n ==> cyclic (add_mod n)

   Cyclic Generators:
   cyclic_generators_def       |- !g. cyclic_generators g = {z | z IN G /\ (ord z = CARD G)}
   cyclic_generators_element   |- !g z. z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G)
   cyclic_generators_subset    |- !g. cyclic_generators g SUBSET G
   cyclic_generators_finite    |- !g. FINITE G ==> FINITE (cyclic_generators g)
   cyclic_generators_nonempty  |- !g. cyclic g /\ FINITE G ==> cyclic_generators g <> {}
   cyclic_generators_coprimes_bij |- !g. cyclic g /\ FINITE G ==>
                          BIJ (\j. cyclic_gen g ** j) (coprimes (CARD G)) (cyclic_generators g)
   cyclic_generators_card      |- !g. cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G))
   cyclic_generators_gen_cofactor_eq_orders  |- !g. cyclic g /\ FINITE G ==> !n. n divides CARD G ==>
                          (cyclic_generators (Generated g (cyclic_gen g ** (CARD G DIV n))) = orders g n)
   cyclic_orders_card          |- !g. cyclic g /\ FINITE G ==>
                                  !n. CARD (orders g n) = if n divides CARD G then phi n else 0

   Partition by order equality:
   eq_order_def            |- !g x y. eq_order g x y <=> (ord x = ord y)
   eq_order_equiv          |- !g. eq_order g equiv_on G
   cyclic_orders_nonempty  |- !g. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {}
   cyclic_eq_order_partition         |- !g. cyclic g /\ FINITE G ==>
                                        (partition (eq_order g) G = {orders g n | n | n divides CARD G})
   cyclic_eq_order_partition_alt     |- !g. cyclic g /\ FINITE G ==>
                                        (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)})
   cyclic_eq_order_partition_by_card |- !g. cyclic g /\ FINITE G ==>
                                        (IMAGE CARD (partition (eq_order g) G) = IMAGE phi (divisors (CARD G)))

   eq_order_is_feq_order           |- !g. eq_order g = feq ord
   orders_is_feq_class_order       |- !g. orders g = feq_class ord G
   cyclic_image_ord_is_divisors    |- !g. cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G))
   cyclic_orders_partition         |- !g. cyclic g /\ FINITE G ==>
                                          (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G)))

   Finite Cyclic Group Existence:
   finite_cyclic_group_existence   |- !n. 0 < n ==> ?g. cyclic g /\ (CARD g.carrier = n)

   Cyclic Group index relative to a generator:
   cyclic_index_exists             |- !g x. cyclic g /\ x IN G ==>
                                      ?n. (x = cyclic_gen g ** n) /\ (FINITE G ==> n < CARD G)
   cyclic_index_def                |- !g x. cyclic g /\ x IN G ==>
                                      (x = cyclic_gen g ** cyclic_index g x) /\
                                      (FINITE G ==> cyclic_index g x < CARD G)
   finite_cyclic_index_property    |- !g. cyclic g /\ FINITE G ==>
                                      !n. n < CARD G ==> (cyclic_index g (cyclic_gen g ** n) = n)
   finite_cyclic_index_unique      |- !g x. cyclic g /\ FINITE G /\ x IN G ==>
                                      !n. n < CARD G ==> ((x = cyclic_gen g ** n) <=> (n = cyclic_index g x))
   finite_cyclic_index_add         |- !g x y. cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
                                      (cyclic_index g (x * y) =
                                         (cyclic_index g x + cyclic_index g y) MOD CARD G)

   Finite Cyclic Group Uniqueness:
   finite_cyclic_group_homo          |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
   finite_cyclic_group_bij           |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier
   finite_cyclic_group_iso           |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
   finite_cyclic_group_uniqueness    |- !g1 g2. cyclic g1 /\ cyclic g2 /\
      FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      ?f. GroupIso f g1 g2
   finite_cyclic_group_add_mod_homo  |- !g. cyclic g /\ FINITE G ==>
      GroupHomo (\n. cyclic_gen g ** n) (add_mod (CARD G)) g
   finite_cyclic_group_add_mod_bij   |- !g. cyclic g /\ FINITE G ==>
      BIJ (\n. cyclic_gen g ** n) (add_mod (CARD G)).carrier G
   finite_cyclic_group_add_mod_iso   |- !g. cyclic g /\ FINITE G ==>
      GroupIso (\n. cyclic_gen g ** n) (add_mod (CARD G)) g

   Isomorphism between Cyclic Groups:
   cyclic_iso_gen     |- !g h f. cyclic g /\ cyclic h /\ FINITE G /\ GroupIso f g h ==>
                                 f (cyclic_gen g) IN cyclic_generators h
*)

(* ------------------------------------------------------------------------- *)
(* Cyclic Group has a generator.                                             *)
(* ------------------------------------------------------------------------- *)

(* Define Cyclic Group *)
val cyclic_def = Define`
  cyclic (g:'a group) <=> Group g /\ ?z. z IN G /\ (!x. x IN G ==> ?n. x = z ** n)
`;

(* Apply Skolemization *)
val lemma = prove(
  ``!(g:'a group). ?z. cyclic g ==> z IN G /\ !x. x IN G ==> ?n. x = z ** n``,
  metis_tac[cyclic_def]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define cyclic generator *)
(*
- SIMP_RULE bool_ss [SKOLEM_THM] lemma;
> val it = |- ?f. !g. cyclic g ==> f g IN G /\ !x. x IN G ==> ?n. x = f g ** n: thm
*)
val cyclic_gen_def = new_specification(
    "cyclic_gen_def",
    ["cyclic_gen"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
> val cyclic_gen_def = |-
  !g. cyclic g ==> cyclic_gen g IN G /\ !x. x IN G ==> ?n. x = cyclic_gen g ** n: thm
*)

(* Theorem: cyclic g ==> Group g *)
(* Proof: by cyclic_def *)
val cyclic_group = store_thm(
  "cyclic_group",
  ``!g:'a group. cyclic g ==> Group g``,
  rw[cyclic_def]);

(* export simple result *)
val _ = export_rewrites ["cyclic_group"];

(* Theorem: cyclic g ==> !x. x IN G ==> ?n. x = (cyclic_gen g) ** n *)
(* Proof: by cyclic_gen_def. *)
val cyclic_element = store_thm(
  "cyclic_element",
  ``!g:'a group. cyclic g ==> (!x. x IN G ==> ?n. x = (cyclic_gen g) ** n)``,
  rw[cyclic_gen_def]);

(* Theorem cyclic g ==> (cyclic_gen g) IN G *)
(* Proof: by cyclic_gen_def. *)
val cyclic_gen_element = store_thm(
  "cyclic_gen_element",
  ``!g:'a group. cyclic g ==> (cyclic_gen g) IN G``,
  rw[cyclic_gen_def]);

(* Theorem: FiniteGroup g ==> !x. x IN G ==> cyclic (gen x) *)
(* Proof:
   By cyclic_def, this is to show:
   (1) x IN G ==> Group (gen x)
       True by generated_group.
   (2) ?z. z IN (Gen x) /\ !x'. x' IN (Gen x) ==> ?n. x' = (gen x).exp z n
       x IN (Gen x)   by generated_gen_element
       Let z = x, the assertion is true by generated_element
*)
val cyclic_generated_group = store_thm(
  "cyclic_generated_group",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> cyclic (gen x)``,
  rpt strip_tac >>
  `Group g /\ FINITE G` by metis_tac[FiniteGroup_def] >>
  rw[cyclic_def] >-
  rw[generated_group] >>
  `x IN (Gen x)` by rw[generated_gen_element] >>
  metis_tac[generated_subgroup, generated_element, subgroup_exp, subgroup_element]);

(* Theorem: cyclic g /\ FINITE G ==> ord (cyclic_gen g) = CARD G *)
(* Proof:
   Let z = cyclic_gen g.
   !x. x IN G ==> ?n. x = z ** n     by cyclic_element
              ==> x IN (Gen z)       by generated_element
   Hence G SUBSET (Gen z)            by SUBSET_DEF
   But (gen z) <= g                  by generated_subgroup
   So  (Gen z) SUBSET G              by Subgroup_def
   Hence (Gen z) = G                 by SUBSET_ANTISYM
   or ord z = CARD (Gen z)           by generated_group_card, group_order_pos
            = CARD G                 by above
*)
val cyclic_gen_order = store_thm(
  "cyclic_gen_order",
  ``!g:'a group. cyclic g /\ FINITE G ==> (ord (cyclic_gen g) = CARD G)``,
  rpt strip_tac >>
  `Group g /\ cyclic_gen g IN G /\ !x. x IN G ==> ?n. x = cyclic_gen g ** n` by rw[cyclic_gen_def] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  `G SUBSET (Gen (cyclic_gen g))` by rw[generated_element, SUBSET_DEF] >>
  `(Gen (cyclic_gen g)) SUBSET G` by metis_tac[generated_subgroup, Subgroup_def] >>
  metis_tac[generated_group_card, group_order_pos, SUBSET_ANTISYM]);

(* Theorem: cyclic g /\ FINITE G ==>
           !n. 0 < n /\ ((CARD G) MOD n = 0) ==> (ord (cyclic_gen g ** (CARD G DIV n)) = n) *)
(* Proof:
   First, Group g                           by cyclic_group
   Therefore  FiniteGroup g                 by FiniteGroup_def
   Let t = (cyclic_gen g) ** m, where m = (CARD G) DIV n.
   Since (cyclic_gen g) IN G                by cyclic_gen_element
      so t IN G                             by group_exp_element
   Since ord (cyclic_gen g) = CARD G        by cyclic_gen_order
      so ord t * gcd (CARD G) m = CARD G    by group_order_power

     But CARD G
       = m * n + ((CARD G) MOD n)           by DIVISION
       = m * n                              since (CARD G) MOD n = 0
       = n * m                              by MULT_COMM
      so gcd (CARD G) m = m                 by GCD_MULTIPLE_ALT

     But CARD G <> 0                        by group_carrier_nonempty, CARD_EQ_0
      so m = (CARD G) DIV n <> 0            by GCD_EQ_0
   Therefore  ord t * m = n * m
          or  ord t = n                     by MULT_RIGHT_CANCEL
*)
val cyclic_gen_power_order = store_thm(
  "cyclic_gen_power_order",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. 0 < n /\ ((CARD G) MOD n = 0) ==> (ord (cyclic_gen g ** (CARD G DIV n)) = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  qabbrev_tac `m = (CARD G) DIV n` >>
  qabbrev_tac `t = (cyclic_gen g) ** m` >>
  `(cyclic_gen g) IN G` by rw[cyclic_gen_element] >>
  `t IN G` by rw[Abbr`t`] >>
  `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  `ord t * gcd (CARD G) m = CARD G` by metis_tac[group_order_power] >>
  `CARD G = m * n + ((CARD G) MOD n)` by rw[DIVISION, Abbr`m`] >>
  `_ = n * m` by rw[MULT_COMM] >>
  `gcd (CARD G) m = m` by metis_tac[GCD_MULTIPLE_ALT] >>
  `m <> 0` by metis_tac[group_carrier_nonempty, CARD_EQ_0, GCD_EQ_0] >>
  metis_tac[MULT_RIGHT_CANCEL]);

(* Theorem: cyclic g ==> (g = (gen (cyclic_gen g))) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
   Let z = cyclic_gen g.
   Then z IN G                    by cyclic_gen_element
    and (Gen z) SUBSET G          by generated_subset
   Now, show: G SUBSET (Gen z)
     or show: x IN G ==> x IN (Gen z)   by SUBSET_DEF
       Since cyclic g and x IN G,
             ?j. x = z ** j       by cyclic_gen_def
       hence x IN x IN (Gen z)    by generated_element

   Thus (Gen z) SUBSET G
    and G SUBSET (Gen z)
    ==> G = Gen z                 by SUBSET_ANTISYM
   also (gen z).op = $*
    and (gen z).id = #e           by generated_property
   Therefore g = (gen z)          by monoid_component_equality
*)
val cyclic_generated_by_gen = store_thm(
  "cyclic_generated_by_gen",
  ``!g:'a group. cyclic g ==> (g = (gen (cyclic_gen g)))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `(Gen z) SUBSET G` by rw[generated_subset] >>
  `G SUBSET (Gen z)` by metis_tac[SUBSET_DEF, cyclic_gen_def, generated_element] >>
  `G = Gen z` by rw[SUBSET_ANTISYM] >>
  metis_tac[monoid_component_equality, generated_property]);

(* Theorem: cyclic g /\ FINITE G ==> !x. x IN G ==>
            ?n. n < CARD G /\ (x = (cyclic_gen g) ** n) *)
(* Proof:
   Since cyclic g ==> Group g    by cyclic_group
      so FiniteGroup g           by FiniteGroup_def
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                   by cyclic_gen_element
    and 0 < m                    by finite_group_card_pos
   also ord z = m                by cyclic_gen_order
    Now ?k. x = z ** k           by cyclic_element
   Since k MOD m < m             by MOD_LESS
     and z ** k = z (k MOD m)    by group_exp_mod, 0 < m
   Just take n = k MOD m.
*)
val cyclic_element_by_gen = store_thm(
  "cyclic_element_by_gen",
  ``!g:'a group. cyclic g /\ FINITE G ==> !x. x IN G ==>
     ?n. n < CARD G /\ (x = (cyclic_gen g) ** n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `?k. x = z ** k` by rw[cyclic_element, Abbr`z`] >>
  qexists_tac `k MOD m` >>
  metis_tac[group_exp_mod, MOD_LESS]);

(* Theorem: cyclic g /\ FINITE G ==> !x. x IN G ==>
            x IN (Gen ((cyclic_gen g) ** ((CARD G) DIV (ord x)))) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos
   Let n = ord x, k = m DIV n, y = z ** k.
   To show: x IN (Gen y)
   Note n divides m               by group_order_divides
   Since x IN G,
         ?t. x = z ** t           by cyclic_element
     But x ** n = #e              by order_property
      or (z ** t) ** n = #e       by x = z ** t
      or  z ** (t * n) = #e       by group_exp_mult
    Thus m divides (t * n)        by group_order_divides_exp, m = ord z
      so k divides t              by dividend_divides_divisor_multiple, n divides m
   Hence ?s. t = s * k            by divides_def
     and x = z ** t
           = z ** (s * k)         by t = s * k
           = z ** (k * s)         by MULT_COMM
           = (z ** k) ** s        by group_exp_mult
           = y ** s               by y = z ** k
   Therefore x IN (Gen y)         by generated_element
*)
val cyclic_element_in_generated = store_thm(
  "cyclic_element_in_generated",
  ``!g:'a group. cyclic g /\ FINITE G ==> !x. x IN G ==>
        x IN (Gen ((cyclic_gen g) ** ((CARD G) DIV (ord x))))``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G /\ (ord z = m)` by rw[GSYM cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  qabbrev_tac `y = z ** k` >>
  `n divides m` by rw[group_order_divides, Abbr`n`, Abbr`m`] >>
  `?t. x = z ** t` by rw[cyclic_element, Abbr`z`] >>
  `x ** n = #e` by rw[order_property, Abbr`n`] >>
  `z ** (t * n) = #e` by rw[group_exp_mult] >>
  `m divides (t * n)` by rw[GSYM group_order_divides_exp] >>
  `k divides t` by rw[GSYM dividend_divides_divisor_multiple, Abbr`k`] >>
  `?s. t = s * k` by rw[GSYM divides_def] >>
  `x = y ** s` by metis_tac[group_exp_mult, MULT_COMM] >>
  metis_tac[generated_element]);

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n) *)
(* Proof:
   Note cyclic g ==> Group g                    by cyclic_group
    and Group g /\ FINITE G ==> FiniteGroup g   by FiniteGroup_def
      Let z = cyclic_gen g, m = CARD G.
      Note 0 < m                                by finite_group_card_pos
      Then z IN G                               by cyclic_gen_element
       and ord z = m                            by cyclic_gen_order
      Let x = z ** (m DIV n),
      Then x IN G                               by group_exp_element
       and ord x = n                            by group_order_exp_cofactor, 0 < m
*)
val cyclic_finite_has_order_divisor = store_thm(
  "cyclic_finite_has_order_divisor",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> ?x. x IN G /\ (ord x = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  qabbrev_tac `x = z ** (m DIV n)` >>
  metis_tac[group_order_exp_cofactor, group_exp_element]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group Properties                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteGroup g ==> cyclic g <=> ?z. z IN G /\ (ord z = CARD G) *)
(* Proof:
   If part: cyclic g ==> ?z. z IN G /\ (ord z = CARD G)
     Let z = cyclic_gen g.
     cyclic g ==> z IN G                          by cyclic_gen_element
     cyclic g /\ FINITE G ==>  (ord z = CARD G)   by cyclic_gen_order
   Only-if part: ?z. z IN G /\ (ord z = CARD G) ==> cyclic g
     Note 0 < CARD G                      by finite_group_card_pos
     (Gen z) SUBSET G                     by generated_subset
     CARD (Gen z) = ord z                 by generated_group_card
     (Gen z) = G                          by SUBSET_EQ_CARD
     Thus !x. x IN G ==> ?n. x = z ** n   by generated_element
*)
val cyclic_finite_alt = store_thm(
  "cyclic_finite_alt",
  ``!g:'a group. FiniteGroup g ==> (cyclic g <=> (?z. z IN G /\ (ord z = CARD G)))``,
  rpt strip_tac >>
  `Group g /\ FINITE G` by metis_tac[FiniteGroup_def] >>
  rw[EQ_IMP_THM] >-
  metis_tac[cyclic_gen_element, cyclic_gen_order] >>
  rw[cyclic_def] >>
  qexists_tac `z` >>
  rw[] >>
  `(Gen z) SUBSET G` by metis_tac[generated_subset] >>
  `CARD (Gen z) = ord z` by rw[generated_group_card, finite_group_card_pos] >>
  `Gen z = G` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  metis_tac[generated_element]);

(* Theorem: cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x) *)
(* Proof:
   Let z = cyclic_gen g.
   x IN G ==> ?n. x = z ** n     by cyclic_element
   y IN G ==> ?m. y = z ** m     by cyclic_element
     x * y
   = (z ** n) * (z ** m)
   = z ** (n + m)                by group_exp_add
   = z ** (m + n)                by ADD_COMM
   = (z ** m) * (z ** n)         by group_exp_add
   = y * x
*)
val cyclic_group_comm = store_thm(
  "cyclic_group_comm",
  ``!g:'a group. cyclic g ==> !x y. x IN G /\ y IN G ==> (x * y = y * x)``,
  metis_tac[cyclic_group, cyclic_gen_def, cyclic_element, group_exp_add, ADD_COMM]);;

(* Theorem: cyclic g ==> AbelianGroup g *)
(* Proof: by cyclic_group_comm, cyclic_group, AbelianGroup_def *)
val cyclic_group_abelian = store_thm(
  "cyclic_group_abelian",
  ``!g:'a group. cyclic g ==> AbelianGroup g``,
  rw[cyclic_group_comm, AbelianGroup_def]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Subgroups                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g /\ h <= g ==> cyclic h *)
(* Proof:
   Let z = cyclic_gen g.
   h <= g <=> Group h /\ Group g /\ H SUBSET G     by Subgroup_def
   Hence H <> {}                                   by group_carrier_nonempty
   and #e IN H                                     by group_id_element, subgroup_id
   If H = {#e},
      !x. x IN H ==> x = #e, #e ** 1 = #e          by group_exp_1, IN_SING
      Hence cyclic h                               by cyclic_def
   If H <> {#e}, there is an x IN H and x <> #e    by ONE_ELEMENT_SING
   !x. x IN H ==> x IN G                           by SUBSET_DEF
              ==> ?n. x = z ** n                   by cyclic_element
   Let m = MIN_SET {n | 0 < n /\ z ** n IN H}
   Let s = z ** m, s IN H                          by group_exp_element
   Then for any x IN H, ?n. x = z ** n             by above
   Now n = q * m + r                               by DIVISION
   x = z ** n
     = z ** (q * m + r)
     = z ** q * m  * z ** r                        by group_comm_op_exp
     = (z ** m) ** q * z ** r                      by group_exp_mult, MULT_COMM
     = s ** q * z ** r
   Hence z ** r = |/ (s ** q) * x                  by group_rsolve
   or z ** r IN H                                  by group_op_element, group_exp_element
   But 0 <= r < m, and m is minimum.
   Hence r = 0, or z ** r = #e                     by group_exp_0
   Therefore for any x IN H, ?q. x = s ** q.
   Result follows by cyclic_def.
*)
val cyclic_subgroup_cyclic = store_thm(
  "cyclic_subgroup_cyclic",
  ``!g h:'a group. cyclic g /\ h <= g ==> cyclic h``,
  rpt strip_tac >>
  `Group g /\ (cyclic_gen g) IN G` by rw[cyclic_gen_def] >>
  `Group h /\ (h.op = g.op) /\ !x. x IN H ==> x IN G` by metis_tac[Subgroup_def, SUBSET_DEF] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `H <> {}` by rw[group_carrier_nonempty] >>
  `#e IN H` by metis_tac[subgroup_id, group_id_element] >>
  `!x. x IN H ==> ?n. x = z ** n` by rw[cyclic_element, Abbr`z`] >>
  `!x. x IN H ==> !n. h.exp x n = x ** n` by rw[subgroup_exp] >>
  `!x. x IN H ==> (h.inv x = |/ x)` by rw[subgroup_inv] >>
  rw[cyclic_def] >>
  Cases_on `H = {#e}` >-
  rw[] >>
  `?x. x IN H /\ x <> #e` by metis_tac[ONE_ELEMENT_SING] >>
  `?n. x = z ** n` by rw[] >>
  `n <> 0` by metis_tac[group_exp_0] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `s = {n | 0 < n /\ z ** n IN H}` >>
  `n IN s` by rw[Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `MIN_SET s IN s /\ !n. n IN s ==> MIN_SET s <= n` by metis_tac[MIN_SET_LEM] >>
  qabbrev_tac `m = MIN_SET s` >>
  `!n. n IN s <=> 0 < n /\ z ** n IN H` by rw[Abbr`s`] >>
  `0 < m /\ z ** m IN H` by metis_tac[] >>
  qexists_tac `z ** m` >>
  rw[] >>
  `?n'. x' = z ** n'` by rw[] >>
  `?q r. ?r q. (n' = q * m + r) /\ r < m` by rw[DA] >>
  `x' = z ** (q * m + r)` by rw[] >>
  `_ = z ** (q * m) * z ** r` by rw[group_exp_add] >>
  `_ = z ** (m * q) * z ** r` by metis_tac[MULT_COMM] >>
  `_ = (z ** m) ** q * z ** r` by metis_tac[group_exp_mult] >>
  `(z ** m) ** q IN H` by metis_tac[group_exp_element] >>
  Cases_on `r = 0` >-
  metis_tac[group_exp_0, group_rid] >>
  `0 < r` by decide_tac >>
  `|/ ((z ** m) ** q) IN H` by metis_tac[group_inv_element] >>
  `z ** r IN H` by metis_tac[group_rsolve, group_exp_element, group_op_element] >>
  `m <= r` by metis_tac[] >>
  `~(r < m)` by decide_tac);

(* Theorem: cyclic g /\ FINITE G ==> !n. (?h. h <= g /\ (CARD H = n)) <=> (n divides (CARD G)) *)
(* Proof:
   If part: h <= g ==> CARD H divides CARD G
      True by Lagrange_thm.
   Only-if part: n divides CARD G ==> ?h. h <= g /\ (CARD H = n)
      Let z = cyclic_gen g, m = CARD G.
      Then z IN G          by cyclic_gen_element
       and (ord z = m)     by cyclic_gen_order
      Since n divides m,
            ?k. m = k * n  by divides_def
       Thus k divides m    by divides_def, MULT_COMM
        and gcd k m = k    by divides_iff_gcd_fix
       Note Group g        by cyclic_group
        and FiniteGroup g  by FiniteGroup_def, FINITE G.
       Let x = z ** k,
       Then x IN G                    by group_exp_element
        and n * k
          = m                         by MULT_COMM, m = k * n
          = ord (z ** k) * gcd m k    by group_order_power
          = ord x * gcd k m           by GCD_SYM
          = ord x * k                 by above
       Since 0 < m, m <> 0            by finite_group_card_pos
          so k <> 0 and n <> 0        by MULT_EQ_0
        thus ord x = n                by EQ_MULT_RCANCEL, k <> 0
        Take h = gen x,
        then h <= g                   by generated_subgroup
         and CARD (Gen x)
           = ord x = n                by generated_group_card
*)
val cyclic_subgroup_condition = store_thm(
  "cyclic_subgroup_condition",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. (?h. h <= g /\ (CARD H = n)) <=> (n divides (CARD G))``,
  rw[EQ_IMP_THM] >-
  rw[Lagrange_thm] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `?k. m = k * n` by rw[GSYM divides_def] >>
  `k divides m` by metis_tac[divides_def, MULT_COMM] >>
  `gcd k m = k` by rw[GSYM divides_iff_gcd_fix] >>
  qabbrev_tac `x = z ** k` >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  `ord x * k = n * k` by metis_tac[group_order_power, GCD_SYM, MULT_COMM] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `m <> 0` by decide_tac >>
  `k <> 0 /\ n <> 0` by metis_tac[MULT_EQ_0] >>
  `ord x = n` by metis_tac[EQ_MULT_RCANCEL] >>
  `x IN G` by rw[Abbr`x`] >>
  qexists_tac `gen x` >>
  metis_tac[generated_subgroup, generated_group_card, NOT_ZERO_LT_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group Examples                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE G /\ cyclic g ==>
            !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)  *)
(* Proof:
       cyclic g
   ==> AbelianGroup g       by cyclic_group_abelian
   ==> (uroots n) <= g      by group_uroots_subgroup
   ==> cyclic (uroots n)    by cyclic_subgroup_cyclic
   ==> (cyclic_gen (uroots n)) IN (uroots n).carrier
                            by cyclic_gen_element
   ==> ord (cyclic_gen (uroots n)) = CARD (uroots n)
                            by cyclic_gen_order, subgroup_order
*)
val cyclic_uroots_has_primitive = store_thm(
  "cyclic_uroots_has_primitive",
  ``!g:'a group. FINITE G /\ cyclic g ==>
     !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `AbelianGroup g` by rw[cyclic_group_abelian] >>
  `(uroots n) <= g` by rw[group_uroots_subgroup] >>
  `cyclic (uroots n)` by metis_tac[cyclic_subgroup_cyclic] >>
  `(cyclic_gen (uroots n)) IN (uroots n).carrier` by rw[cyclic_gen_element] >>
  metis_tac[cyclic_gen_order, subgroup_order, Subgroup_def, SUBSET_FINITE]);

(* This cyclic_uroots_has_primitive, originally for the next one, is not used. *)

(* Theorem: cyclic g ==> cyclic (uroots n) *)
(* Proof:
   Note AbelianGroup g           by cyclic_group_abelian
    and (uroots n) <= g          by group_uroots_subgroup
   Thus cyclic (uroots n)        by cyclic_subgroup_cyclic
*)
val cyclic_uroots_cyclic = store_thm(
  "cyclic_uroots_cyclic",
  ``!g:'a group. cyclic g ==> !n. cyclic (uroots n)``,
  rpt strip_tac >>
  `AbelianGroup g` by rw[cyclic_group_abelian] >>
  `(uroots n) <= g` by rw[group_uroots_subgroup] >>
  metis_tac[cyclic_subgroup_cyclic]);

(* Theorem: 1 < n ==> (order (add_mod n) 1 = n) *)
(* Proof:
   Since 1 IN (add_mod n).carrier             by add_mod_element, 1 < n
     and !m. (add_mod n).exp 1 m = m MOD n    by add_mod_exp, 0 < n
   Therefore,
         (add_mod n).exp 1 n = n MOD n = 0    by DIVMOD_ID, 0 < n
     and !m. 0 < m /\ m < n,
         (add_mod n).exp 1 m = m <> 0         by NOT_ZERO_LT_ZERO, 0 < n
     Now (add_mod n).id = 0                   by add_mod_property
      so order (add_mod n) 1 = n              by group_order_thm
*)
val add_mod_order_1 = store_thm(
  "add_mod_order_1",
  ``!n. 1 < n ==> (order (add_mod n) 1 = n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `!m. (add_mod n).exp 1 m = m MOD n` by rw[add_mod_exp] >>
  `1 IN (add_mod n).carrier` by rw[add_mod_element] >>
  `(add_mod n).exp 1 n = 0` by rw[] >>
  `!m. 0 < m /\ m < n ==> (add_mod n).exp 1 m <> 0` by rw[NOT_ZERO_LT_ZERO] >>
  metis_tac[group_order_thm, add_mod_property]);

(* Theorem: 0 < n ==> cyclic (add_mod n) *)
(* Proof:
   Note Group (add_mod n)                  by add_mod_group
    and FiniteGroup (add_mod n)            by add_mod_finite_group
    and (add_mod n).id = 0                 by add_mod_property
    and CARD (add_mod n).carrier = n       by add_mod_property
   If n = 1,
      Since order (add_mod 1) 0 = 1        by group_order_id
        and 0 IN (add_mod 1).carrier       by group_id_element
        and CARD (add_mod 1).carrier = 1   by above
       Thus cyclic (add_mod 1)             by cyclic_finite_alt
   If n <> 1, 1 < n.
      Since 1 IN (add_mod n).carrier       by add_mod_element, 1 < n
        and order (add_mod n) 1 = n        by add_mod_order_1, 1 < n
       Thus cyclic (add_mod n)             by cyclic_finite_alt
*)
val add_mod_cylic = store_thm(
  "add_mod_cylic",
  ``!n. 0 < n ==> cyclic (add_mod n)``,
  rpt strip_tac >>
  `Group (add_mod n)` by rw[add_mod_group] >>
  `FiniteGroup (add_mod n)` by rw[add_mod_finite_group] >>
  `((add_mod n).id = 0) /\ (CARD (add_mod n).carrier = n)` by rw[add_mod_property] >>
  Cases_on `n = 1` >-
  metis_tac[cyclic_finite_alt, group_order_id, group_id_element] >>
  `1 < n` by decide_tac >>
  metis_tac[cyclic_finite_alt, add_mod_order_1, add_mod_element]);

(* ------------------------------------------------------------------------- *)
(* Order of elements in a Cyclic Group                                       *)
(* ------------------------------------------------------------------------- *)

(*
From FiniteField theory, knowing that F* is cyclic, we can prove stronger results:
(1) Let G be cyclic with |G| = n, so it has a generator z with (order z = n).
(2) All elements in G are known: 1, g, g^2, ...., g^(n-1).
(3) Thus all their orders are known: n/gcd(0,n), n/gcd(1,n), n/gcd(2,n), ..., n/gcd(n-1,n).
(4) Counting, CARD (order_eq k) = phi k.
(5) As a result, n = SUM (phi k), over k | n.
*)

(* ------------------------------------------------------------------------- *)
(* Cyclic Generators                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define the set of generators for cyclic group *)
val cyclic_generators_def = Define `
    cyclic_generators (g:'a group) = {z | z IN G /\ (ord z = CARD G)}
`;

(* Theorem: z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G) *)
(* Proof: by cyclic_generators_def *)
val cyclic_generators_element = store_thm(
  "cyclic_generators_element",
  ``!g:'a group. !z. z IN cyclic_generators g <=> z IN G /\ (ord z = CARD G)``,
  rw[cyclic_generators_def]);

(* Theorem: (cyclic_generators g) SUBSET G *)
(* Proof: by cyclic_generators_def, SUBSET_DEF *)
val cyclic_generators_subset = store_thm(
  "cyclic_generators_subset",
  ``!g:'a group. (cyclic_generators g) SUBSET G``,
  rw[cyclic_generators_def, SUBSET_DEF]);

(* Theorem: FINITE G ==> FINITE (cyclic_generators g) *)
(* Proof: by cyclic_generators_subset, SUBSET_FINITE *)
val cyclic_generators_finite = store_thm(
  "cyclic_generators_finite",
  ``!g:'a group. FINITE G ==> FINITE (cyclic_generators g)``,
  metis_tac[cyclic_generators_subset, SUBSET_FINITE]);

(* Theorem: cyclic g /\ FINITE G ==> (cyclic_generators g) <> {} *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
    Then z IN G                        by cyclic_gen_element
     and ord z = m                     by cyclic_gen_order, FINITE G
   Hence z IN cyclic_generators g      by cyclic_generators_element
      or (cyclic_generators g) <> {}   by MEMBER_NOT_EMPTY
*)
val cyclic_generators_nonempty = store_thm(
  "cyclic_generators_nonempty",
  ``!g:'a group. cyclic g /\ FINITE G ==> (cyclic_generators g) <> {}``,
  metis_tac[cyclic_generators_element, cyclic_gen_element, cyclic_gen_order, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            BIJ (\j. (cyclic_gen g) ** j) (coprimes (CARD G)) (cyclic_generators g) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos
   Expanding by BIJ_DEF, INJ_DEF, and SURJ_DEF, this is to show:
   (1) z IN G /\ (ord z = m) /\ j IN coprimes m ==> z ** j IN cyclic_generators g
       Since z ** j IN G                    by group_exp_element
         and coprime j m                    by coprimes_element
          so ord (z ** j) = m               by group_order_power_eq_order
       Hence z ** j IN cyclic_generators g  by cyclic_generators_element
   (2) z IN G /\ (ord z = m) /\ j IN coprimes m /\ j' IN coprimes m /\ z ** j = z ** j' ==> j = j'
       If m = 1,
          then coprimes 1 = {1}                  by coprimes_1
          hence j = 1 = j'                       by IN_SING
       If m <> 1, 1 < m.
          then j IN coprimes m ==> j < m         by coprimes_element_less
           and j' IN coprimes m ==> j' < m       by coprimes_element_less
          Therefore j = j'                       by group_exp_equal
   (3) same as (1)
   (4) z IN G /\ (ord z = m) /\ x IN cyclic_generators g ==> ?j. j IN coprimes m /\ (z ** j = x)
       Since x IN cyclic_generators g
         ==> x IN G /\ (ord x = m)               by cyclic_generators_element
        Also ?k. k < m /\ (x = z ** k)           by cyclic_element_by_gen
        If m = 1,
           then ord x = 1 ==> x = #e             by group_order_eq_1
           then ord z = 1 ==> z = #e             by group_order_eq_1
           Take j = 1,
           and 1 IN (coprimes 1)                 by coprimes_1, IN_SING
           with z ** 1 = x                       by group_exp_1
        If m <> 1,
           then x <> #e                          by group_order_eq_1
           thus k <> 0                           by group_exp_0
             so 0 < k, and k < m ==> k <= m      by LESS_IMP_LESS_OR_EQ
           Also ord (z ** k) = m ==> coprime k m by group_order_power_eq_order
           Take j = k, and j IN coprimes m       by coprimes_element
*)
val cyclic_generators_coprimes_bij = store_thm(
  "cyclic_generators_coprimes_bij",
  ``!g:'a group. cyclic g /\ FINITE G ==>
      BIJ (\j. (cyclic_gen g) ** j) (coprimes (CARD G)) (cyclic_generators g)``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    qabbrev_tac `m = ord z` >>
    `coprime j m` by metis_tac[coprimes_element] >>
    `z ** j IN G` by rw[] >>
    `ord (z ** j) = m` by metis_tac[group_order_power_eq_order] >>
    metis_tac[cyclic_generators_element],
    qabbrev_tac `m = ord z` >>
    Cases_on `m = 1` >-
    metis_tac[coprimes_1, IN_SING] >>
    `1 < m` by decide_tac >>
    metis_tac[coprimes_element_less, group_exp_equal],
    qabbrev_tac `m = ord z` >>
    `coprime j m` by metis_tac[coprimes_element] >>
    `z ** j IN G` by rw[] >>
    `ord (z ** j) = m` by metis_tac[group_order_power_eq_order] >>
    metis_tac[cyclic_generators_element],
    qabbrev_tac `m = ord z` >>
    `x IN G /\ (ord x = m)` by metis_tac[cyclic_generators_element] >>
    `?k. k < m /\ (x = z ** k)` by metis_tac[cyclic_element_by_gen] >>
    Cases_on `m = 1` >-
    metis_tac[group_order_eq_1, coprimes_1, IN_SING, group_exp_1] >>
    `x <> #e` by metis_tac[group_order_eq_1] >>
    `k <> 0` by metis_tac[group_exp_0] >>
    `0 < k /\ k <= m` by decide_tac >>
    metis_tac[group_order_power_eq_order, coprimes_element]
  ]);

(* Theorem: cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G)) *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
    Then z IN G                        by cyclic_gen_element
     and ord z = m                     by cyclic_gen_order
     Now BIJ (\j. z ** j) (coprimes m) (cyclic_generators g)   by cyclic_generators_coprimes_bij
   Since FINITE (coprimes m)           by coprimes_finite
     and FINITE (cyclic_generators g)  by cyclic_generators_finite
   Hence CARD (cyclic_generators g)
       = CARD (coprimes m)             by FINITE_BIJ_CARD_EQ
       = phi m                         by phi_def
*)
val cyclic_generators_card = store_thm(
  "cyclic_generators_card",
  ``!g:'a group. cyclic g /\ FINITE G ==> (CARD (cyclic_generators g) = phi (CARD G))``,
  rpt strip_tac >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `BIJ (\j. z ** j) (coprimes m) (cyclic_generators g)` by rw[cyclic_generators_coprimes_bij, Abbr`z`, Abbr`m`] >>
  `FINITE (coprimes m)` by rw[coprimes_finite] >>
  `FINITE (cyclic_generators g)` by rw[cyclic_generators_finite] >>
  metis_tac[phi_def, FINITE_BIJ_CARD_EQ]);

(*
Goolge: order of elements in a cyclic group.

Pattern of orders of elements in a cyclic group
http://math.stackexchange.com/questions/158281/pattern-of-orders-of-elements-in-a-cyclic-group

The number of elements of order d, where d is a divisor of n, is φ(d).

Let G be a cyclic group of order n, and let a in G be a generator. Let d be a divisor of n.

Certainly, a^{n/d} is an element of G of order d (in other words, <a^{n/d}> is a subgroup of G of order d).
If a^{t} in G is an element of order d, then (a^{t})^{d} = e, hence n ∣ td, and thus (n/d) ∣ t.
This shows that a^{t} in <a^{n/d}>, and thus <a^{t}> = <a^{n/d}> (since they are both subgroups of order d).
Thus, there is exactly one subgroup, let's call it H_{d}, of G of order d, for each divisor d of n,
and all of these subgroups are themselves cyclic.

Any cyclic group of order d has ϕ(d) generators, i.e. there are ϕ(d) elements of order d in H_{d},
and hence there are ϕ(d) elements of order d in G. Here, ϕ is Euler's phi function.

This can be checked to make sense via the identity: n = SUM ϕ(d), over d | n.
*)

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides (CARD G) ==>
            (cyclic_generators (Generated g ((cyclic_gen g) ** ((CARD G) DIV n))) = orders g n) *)
(* Proof:
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
    and 0 < m                     by finite_group_card_pos

   Let k = m DIV n, y = z ** k, h = Generated g y.
   Then y IN G                    by group_exp_element
    and h <= g                    by generated_subgroup, y IN G

   Expanding by cyclic_generators_def, orders_def, this is to show:
   (1) h <= g /\ x IN H ==> x IN G
       True by Subgroup_def, SUBSET_DEF.
   (2) h <= g /\ order h x = CARD H ==> ord x = n
       Note ord x = CARD H      by subgroup_order
                  = ord y       by generated_group_card, group_order_pos
                  = n           by group_order_exp_cofactor
   (3) h <= g /\ x IN G /\ (ord x) divides m ==> x IN H
       True by cyclic_element_in_generated.
   (4) h <= g /\ x IN G ==> order h x = CARD H
       Note x IN H              by cyclic_element_in_generated
        and (ord x) divides m   by group_order_divides
            order h x
          = ord x               by subgroup_order, x IN H
          = ord (z ** k)        by group_order_exp_cofactor, (ord x) divides m = ord z
          = ord y               by y = z ** k
          = CARD H              by generated_group_card, group_order_pos
*)
val cyclic_generators_gen_cofactor_eq_orders = store_thm(
  "cyclic_generators_gen_cofactor_eq_orders",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides (CARD G) ==>
   (cyclic_generators (Generated g ((cyclic_gen g) ** ((CARD G) DIV n))) = orders g n)``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `k = m DIV n` >>
  qabbrev_tac `y = z ** k` >>
  qabbrev_tac `h = Generated g y` >>
  `y IN G` by rw[Abbr`y`, Abbr`z`] >>
  `h <= g` by rw[generated_subgroup, Abbr`h`] >>
  rw[cyclic_generators_def, orders_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[Subgroup_def, SUBSET_DEF] >-
  metis_tac[subgroup_order, generated_group_card, group_order_exp_cofactor, group_order_pos] >-
  metis_tac[cyclic_element_in_generated] >>
  qabbrev_tac `m = ord z` >>
  qabbrev_tac `n = ord x` >>
  `x IN H` by metis_tac[cyclic_element_in_generated] >>
  `order h x = n` by rw[subgroup_order, Abbr`n`] >>
  `ord y = n` by rw[group_order_exp_cofactor, Abbr`m`, Abbr`y`, Abbr`k`] >>
  `CARD H = ord y` by rw[generated_group_card, group_order_pos, Abbr`h`] >>
  decide_tac);

(* Theorem: cyclic g /\ FINITE G ==>
            !n. CARD (orders g n) = if (n divides CARD G) then phi n else 0 *)
(* Proof:
   Let m = CARD G.
   Note 0 < m                     by finite_group_card_pos
   Since cyclic g ==> Group g     by cyclic_group
      so FiniteGroup g            by FiniteGroup_def, FINITE G
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                    by cyclic_gen_element
    and ord z = m                 by cyclic_gen_order
   If n divides m, to show: CARD (orders g n) = phi n
      Let k = m DIV n, y = z ** k, h = Generated g y.
      Then y IN G                 by group_exp_element
       and ord y = n              by group_order_exp_cofactor
      also h <= g                 by generated_subgroup
       and CARD H = n             by generated_group_card, group_order_pos
      Also cyclic h               by cyclic_subgroup_cyclic
       and FINITE H               by finite_subgroup_carrier_finite
      Hence CARD (orders g n)
          = CARD (cyclic_generators h)  by cyclic_generators_gen_cofactor_eq_orders
          = phi n                       by cyclic_generators_card, FINITE H

   If ~(n divides m), to show: CARD (orders g n) = 0
      By contradiction, suppose CARD (orders g n) <> 0.
      Since FINITE (orders g n)       by orders_finite
         so orders g n <> {}          by CARD_EQ_0
       Thus ?x. x IN orders g n       by MEMBER_NOT_EMPTY
         or x IN G /\ (ord x = n)     by orders_element
        Now (ord x) divides m         by group_order_divides
        which contradicts ~(n divides m).
*)
val cyclic_orders_card = store_thm(
  "cyclic_orders_card",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. CARD (orders g n) = if (n divides CARD G) then phi n else 0``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  Cases_on `n divides m` >| [
    simp[] >>
    qabbrev_tac `k = m DIV n` >>
    qabbrev_tac `y = z ** k` >>
    qabbrev_tac `h = Generated g y` >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by metis_tac[group_order_exp_cofactor] >>
    `h <= g` by rw[generated_subgroup, Abbr`h`] >>
    `CARD H = n` by rw[generated_group_card, group_order_pos, Abbr`h`] >>
    `cyclic h` by metis_tac[cyclic_subgroup_cyclic] >>
    `FINITE H` by metis_tac[finite_subgroup_carrier_finite] >>
    metis_tac[cyclic_generators_gen_cofactor_eq_orders, cyclic_generators_card],
    simp[] >>
    spose_not_then strip_assume_tac >>
    `FINITE (orders g n)` by rw[orders_finite] >>
    `orders g n <> {}` by rw[GSYM CARD_EQ_0] >>
    metis_tac[MEMBER_NOT_EMPTY, orders_element, group_order_divides]
  ]);

(* ------------------------------------------------------------------------- *)
(* Partition by order equality                                               *)
(* ------------------------------------------------------------------------- *)

(* Define a relation: eq_order *)
val eq_order_def = Define `
    eq_order (g:'a group) x y <=> (ord x = ord y)
`;

(* Theorem: (eq_order g) equiv_on G *)
(* Proof: by eq_order_def, equiv_on_def *)
val eq_order_equiv = store_thm(
  "eq_order_equiv",
  ``!g:'a group. (eq_order g) equiv_on G``,
  rw[eq_order_def, equiv_on_def]);

(* Theorem: cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {} *)
(* Proof:
   Let z = cyclic_gen g, m = CARD G.
   Note 0 < m               by finite_group_card_pos
   Then z IN G              by cyclic_gen_element
    and ord z = m           by cyclic_gen_order
   Let x = z ** (m DIV n)
   Then x IN G              by group_exp_element
    and ord x = n           by group_order_exp_cofactor
     so x IN (orders g n)   by orders_element
   Thus orders g n <> {}    by MEMBER_NOT_EMPTY
*)
val cyclic_orders_nonempty = store_thm(
  "cyclic_orders_nonempty",
  ``!g:'a group. cyclic g /\ FINITE G ==> !n. n divides CARD G ==> orders g n <> {}``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `z = cyclic_gen g` >>
  qabbrev_tac `m = CARD G` >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  `z IN G` by rw[cyclic_gen_element, Abbr`z`] >>
  `ord z = m` by rw[cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  qabbrev_tac `x = z ** (m DIV n)` >>
  `x IN G` by rw[Abbr`x`] >>
  `ord x = n` by metis_tac[group_order_exp_cofactor] >>
  metis_tac[orders_element, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            (partition (eq_order g) G = {orders g n | n | n divides (CARD G)}) *)
(* Proof:
   Expanding by partition_def, eq_order_def, orders_def, this is to show:
   (1) x' IN G /\ ... ==> ?n. ... (ord x' = n) ... /\ n divides CARD G
       Let n = ord x',
       Result is true since n divides CARD G   by group_order_divides
   (2) n divides CARD G /\ ... (ord x'' = n) ... ==> ?x'. x' IN G /\ ... (ord x' = ord x'') ...
       Since n divides CARD G
         ==> (orders g n) <> {}            by cyclic_orders_nonempty
         ==> ?z. z IN G /\ (ord z = n)     by orders_element, , MEMBER_NOT_EMPTY
       Let x' = z, then the result follows.
*)
val cyclic_eq_order_partition = store_thm(
  "cyclic_eq_order_partition",
  ``!g:'a group. cyclic g /\ FINITE G ==>
     (partition (eq_order g) G = {orders g n | n | n divides (CARD G)})``,
  rpt strip_tac >>
  `Group g ` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  rw[partition_def, eq_order_def, orders_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[group_order_divides] >>
  metis_tac[orders_element, cyclic_orders_nonempty, MEMBER_NOT_EMPTY]);

(* Theorem: cyclic g /\ FINITE G ==>
            (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)}) *)
(* Proof:
   Note Group g            by cyclic_group
     so FiniteGroup g      by FiniteGroup_def
    ==> 0 < CARD G         by finite_group_card_pos, FiniteGroup g
        partition (eq_order g) G
      = {orders g n | n | n divides (CARD G)}      by cyclic_eq_order_partition
      = {orders g n | n | n IN divisors (CARD G)}  by divisors_element_alt, 0 < CARD G
*)
val cyclic_eq_order_partition_alt = store_thm(
  "cyclic_eq_order_partition_alt",
  ``!g:'a group. cyclic g /\ FINITE G ==>
                (partition (eq_order g) G = {orders g n | n | n IN divisors (CARD G)})``,
  rpt strip_tac >>
  `0 < CARD G` by metis_tac[finite_group_card_pos, cyclic_group, FiniteGroup_def] >>
  rw[cyclic_eq_order_partition, divisors_element_alt]);

(* We have shown: in a finite cyclic group G,
   For each divisor d | |G|, there are phi(d) elements of order d.
   Since each element must have some order in a finite group,
   the sum of phi(d) over all divisors d will count all elements in the group,
   that is,  n = SUM phi(d), over d | n.
*)

(* Theorem: cyclic g /\ FINITE G ==>
            (IMAGE CARD (partition (eq_order g) g.carrier) = IMAGE phi (divisors (CARD G))) *)
(* Proof:
   Since cyclic g ==> Group g       by cyclic_group
      so FiniteGroup g              by FiniteGroup_def
   Let z = cyclic_gen g, m = CARD G.
   Then z IN G                      by cyclic_gen_element
    and ord z = m                   by cyclic_gen_order
    and 0 < m                       by finite_group_card_pos

   Apply partition_def, eq_order_def, to show:
   (1) ?x''. (CARD s = phi x'') /\ x'' IN divisors m
       Note s = orders g n         by orders_def
       Let n = ord x'', y = z ** (m DIV n).
       Then n divides m             by group_order_divides
        and y IN G                  by group_exp_element
        and ord y = n               by group_order_exp_cofactor
       Since 0 < m, n IN divisors m by divisors_element_alt
       hence CARD s = phi n         by cyclic_orders_card
       So take x'' = n.
   (2) x' IN divisors m ==> ?x''. (phi x' = CARD x'') /\ ?x. x IN orders g x'
       Let n = x', y = z ** (m DIV n).
       Since n IN divisors m,
         ==> n <= m /\ n divides m  by divisors_element
         Let s = orders g n,
        Then CARD s = phi n         by cyclic_orders_card
         and y IN G                 by group_exp_element
         and ord y = n              by group_order_exp_cofactor
          so y IN orders g n        by orders_element
       So take x'' = y.
*)
val cyclic_eq_order_partition_by_card = store_thm(
  "cyclic_eq_order_partition_by_card",
  ``!g:'a group. cyclic g /\ FINITE G ==>
      (IMAGE CARD (partition (eq_order g) g.carrier) = IMAGE phi (divisors (CARD G)))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  qabbrev_tac `m = CARD G` >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G /\ (ord z = m)` by rw[cyclic_gen_element, cyclic_gen_order, Abbr`z`, Abbr`m`] >>
  `0 < m` by rw[finite_group_card_pos, Abbr`m`] >>
  rw[partition_def, eq_order_def, EXTENSION, EQ_IMP_THM] >| [
    qabbrev_tac `m = ord z` >>
    qabbrev_tac `n = ord x''` >>
    (`x' = orders g n` by (rw[orders_def, EXTENSION] >> metis_tac[])) >>
    qabbrev_tac `y = z ** (m DIV n)` >>
    `n divides m` by metis_tac[group_order_divides] >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by rw[group_order_exp_cofactor, Abbr`y`, Abbr`m`] >>
    metis_tac[cyclic_orders_card, divisors_element_alt],
    qabbrev_tac `m = ord z` >>
    qabbrev_tac `n = x'` >>
    qabbrev_tac `y = z ** (m DIV n)` >>
    `n <= m /\ n divides m` by metis_tac[divisors_element] >>
    `y IN G` by rw[Abbr`y`] >>
    `ord y = n` by rw[group_order_exp_cofactor, Abbr`y`, Abbr`m`] >>
    metis_tac[cyclic_orders_card, orders_element]
  ]);

(* Theorem: eq_order g = feq ord *)
(* Proof:
       eq_order g x y
   <=> ord x = ord y   by eq_order_def
   <=> feq ord x y     by feq_def
   Hence true by FUN_EQ_THM.
*)
val eq_order_is_feq_order = store_thm(
  "eq_order_is_feq_order",
  ``!g:'a group. eq_order g = feq ord``,
  rw[eq_order_def, FUN_EQ_THM, fequiv_def]);

(* Theorem: orders g = feq_class ord G *)
(* Proof:
     orders g n
   = {x | x IN G /\ (ord x = n)}   by orders_def
   = feq_class ord G n             by feq_class_def
   Hence true by FUN_EQ_THM.
*)
Theorem orders_is_feq_class_order:
  !g:'a group. orders g = feq_class ord G
Proof
  rw[orders_def, in_preimage, EXTENSION, Once FUN_EQ_THM]
QED

(* Theorem: cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G)) *)
(* Proof:
   Note cyclic g ==> Group g                    by cyclic_group
    and Group g /\ FINITE G ==> FiniteGroup g   by FiniteGroup_def
   If part: x IN G ==> ord x <= CARD G /\ (ord x) divides (CARD G)
      Since FiniteGroup g ==> 0 < CARD G        by finite_group_card_pos
       also ==> (ord x) divides (CARD G)        by group_order_divides
      Hence ord x IN divisors (CARD G)          by divisors_element_alt, 0 < CARD G
   Only-if part: n <= CARD G /\ n divides CARD G ==> ?x. x IN G /\ (ord x = n)
      True by cyclic_finite_has_order_divisor.
*)
Theorem cyclic_image_ord_is_divisors:
  !g:'a group. cyclic g /\ FINITE G ==> (IMAGE ord G = divisors (CARD G))
Proof
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def] >>
  `0 < CARD G` by simp[finite_group_card_pos] >>
  rw[EXTENSION, divisors_element_alt, EQ_IMP_THM] >-
  rw[group_order_divides] >>
  metis_tac[cyclic_finite_has_order_divisor]
QED

(* Theorem: cyclic g /\ FINITE G ==> (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G))) *)
(* Proof:
   Since cyclic g /\ FINITE G
     ==> FiniteGroup g              by FiniteGroup_def, cyclic_group
      so 0 < CARD G                 by finite_group_card_pos
    Then partition (eq_order g) G
       = {orders g n | n | n divides CARD G}  by cyclic_eq_order_partition
       = IMAGE (orders g) (divisors (CARD G)) by divisors_element_alt, 0 < CARD G
*)
Theorem cyclic_orders_partition:
  !g:'a group. cyclic g /\ FINITE G ==>
       (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G)))
Proof
  rpt strip_tac >>
  `FiniteGroup g` by metis_tac[FiniteGroup_def, cyclic_group] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `partition (eq_order g) G = {orders g n | n | n divides CARD G}` by rw[cyclic_eq_order_partition] >>
  rw[divisors_element_alt, EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Finite Cyclic Group Existence.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> ?g:num group. cyclic g /\ (CARD g.carrier = n)  *)
(* Proof:
   Let g = add_mod n.
   Then cyclic (add_mod n)        by add_mod_cylic
    and CARD g.carrier = n        by add_mod_card
*)
val finite_cyclic_group_existence = store_thm(
  "finite_cyclic_group_existence",
  ``!n. 0 < n ==> ?g:num group. cyclic g /\ (CARD g.carrier = n)``,
  rpt strip_tac >>
  qexists_tac `add_mod n` >>
  rpt strip_tac >-
  rw[add_mod_cylic] >>
  rw[add_mod_card]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Group index relative to a generator.                               *)
(* ------------------------------------------------------------------------- *)

(* Extract cyclic index w.r.t a generator *)

(* Theorem: cyclic g /\ x IN G ==> ?n. (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G) *)
(* Proof:
   Note Group g                          by cyclic_def
    and cyclic_gen g IN G /\
        ?k. x = (cyclic_gen g) ** k      by cyclic_gen_def
   If FINITE G,
      Then FiniteGroup g                 by FiniteGroup_def
        so 0 < CARD G                    by finite_group_card_pos
       and ord (cyclic_gen g) = CARD G   by cyclic_gen_order
      Take n = k MOD (CARD G).
      Then (cyclic_gen g) ** n
         = (cyclic_gen g) ** k           by group_exp_mod, 0 < CARD G
         = x                             by above
       and n < CARD G                    by MOD_LESS, 0 < CARD G
   If INFINITE G,
      Take n = k, the result follows.
*)
val cyclic_index_exists = store_thm(
  "cyclic_index_exists",
  ``!(g:'a group) x. cyclic g /\ x IN G ==> ?n. (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `cyclic_gen g IN G /\ ?n. x = (cyclic_gen g) ** n` by rw[cyclic_gen_def] >>
  Cases_on `FINITE G` >| [
    rw[] >>
    `FiniteGroup g` by rw[FiniteGroup_def] >>
    `0 < CARD G` by rw[finite_group_card_pos] >>
    `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
    qexists_tac `n MOD (CARD G)` >>
    rw[Once group_exp_mod],
    metis_tac[]
  ]);

(* Apply Skolemization *)
val lemma = prove(
  ``!(g:'a group) x. ?n. cyclic g /\ x IN G ==> (x = (cyclic_gen g) ** n) /\ (FINITE G ==> n < CARD G)``,
  metis_tac[cyclic_index_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define cyclic generator *)
(*
- SIMP_RULE (bool_ss) [SKOLEM_THM] lemma;
> val it =
   |- ?f. !g x. cyclic g /\ x IN G ==> x = cyclic_gen g ** f g x /\ (FINITE G ==> f g x < CARD G): thm
*)
val cyclic_index_def = new_specification(
    "cyclic_index_def",
    ["cyclic_index"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
val cyclic_index_def =
   |- !g x. cyclic g /\ x IN G ==> x = cyclic_gen g ** cyclic_index g x /\
            (FINITE G ==> cyclic_index g x < CARD G): thm
*)

(* Theorem: cyclic g /\ FINITE G ==>
            !n. n < CARD G ==> (cyclic_index g (cyclic_gen g ** n) = n) *)
(* Proof:
   Note Group g                           by cyclic_group
    ==> FiniteGroup g                     by FiniteGroup_def
    Let x = (cyclic_gen g) ** n.
   Note cyclic_gen g IN G                 by cyclic_gen_def
   Then x IN G                            by group_exp_element
   Thus (x = (cyclic_gen g) ** (cyclic_index g x)) /\
        cyclic_index g x < CARD G         by cyclic_index_def
    Now ord (cyclic_gen g) = CARD G       by cyclic_gen_order
    and 0 < CARD G                        by finite_group_card_pos
   Thus n = cyclic_index g x              by group_exp_equal
*)
val finite_cyclic_index_property = store_thm(
  "finite_cyclic_index_property",
  ``!g:'a group. cyclic g /\ FINITE G ==>
   !n. n < CARD G ==> (cyclic_index g ((cyclic_gen g) ** n) = n)``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  qabbrev_tac `x = (cyclic_gen g) ** n` >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `x IN G` by rw[Abbr`x`] >>
  `(x = (cyclic_gen g) ** (cyclic_index g x)) /\ cyclic_index g x < CARD G` by fs[cyclic_index_def] >>
  `ord (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  metis_tac[group_exp_equal, finite_group_card_pos]);

(* Theorem: cyclic g /\ FINITE G /\ x IN G ==>
            !n. n < CARD G ==> ((x = (cyclic_gen g) ** n) <=> (n = cyclic_index g x)) *)
(* Proof:
   If part: (x = (cyclic_gen g) ** n) ==> (n = cyclic_index g x)
      This is true by finite_cyclic_index_property.
   Only-if part: (n = cyclic_index g x) ==> (x = (cyclic_gen g) ** n)
      This is true by cyclic_index_def
*)
val finite_cyclic_index_unique = store_thm(
  "finite_cyclic_index_unique",
  ``!g:'a group x. cyclic g /\ FINITE G /\ x IN G ==>
   !n. n < CARD G ==> ((x = (cyclic_gen g) ** n) <=> (n = cyclic_index g x))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  rw[cyclic_index_def, EQ_IMP_THM] >>
  rw[finite_cyclic_index_property]);

(* Theorem: cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
            (cyclic_index g (x * y) = ((cyclic_index g x) + (cyclic_index g y)) MOD (CARD G)) *)
(* Proof:
   Note Group g                 by cyclic_group
     so FiniteGroup g           by FiniteGroup_def
    and x * y IN G              by group_op_element
   Let z = cyclic_gen g.
   Then z IN G                  by cyclic_gen_def
    and ord z = CARD G          by cyclic_gen_order
   Note 0 < CARD G              by finite_group_card_pos
   Let h = cyclic_index g x, k = cyclic_index g y.
       z ** ((h + k) MOD CARD G)
     = z ** (h + k)             by group_exp_mod
     = (z ** h) * (z ** k)      by group_exp_add
     = x * y                    by cyclic_index_def
   Note (h + k) MOD (CARD G) < CARD G                   by MOD_LESS
   Thus (h + k) MOD (CARD G) = cyclic_index g (x * y)   by finite_cyclic_index_unique
*)
val finite_cyclic_index_add = store_thm(
  "finite_cyclic_index_add",
  ``!g:'a group x y. cyclic g /\ FINITE G /\ x IN G /\ y IN G ==>
    (cyclic_index g (x * y) = ((cyclic_index g x) + (cyclic_index g y)) MOD (CARD G))``,
  rpt strip_tac >>
  `Group g` by rw[] >>
  `FiniteGroup g` by rw[FiniteGroup_def] >>
  `x * y IN G` by rw[] >>
  qabbrev_tac `z = cyclic_gen g` >>
  `z IN G` by rw[cyclic_gen_def, Abbr`z`] >>
  `ord z = CARD G` by rw[cyclic_gen_order, Abbr`z`] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  qabbrev_tac `h = cyclic_index g x` >>
  qabbrev_tac `k = cyclic_index g y` >>
  `z ** ((h + k) MOD CARD G) = z ** (h + k)` by metis_tac[group_exp_mod] >>
  `_ = (z ** h) * (z ** k)` by rw[] >>
  `_ = x * y` by metis_tac[cyclic_index_def] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `(h + k) MOD (CARD G) < CARD G` by rw[] >>
  metis_tac[finite_cyclic_index_unique]);

(* ------------------------------------------------------------------------- *)
(* Finite Cyclic Group Uniqueness.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2 *)
(* Proof:
   Note Group g2                                     by cyclic_group
    and FiniteGroup g2                               by FiniteGroup_def
   Note cyclic_gen g2 IN g2.carrier                  by cyclic_gen_def
    and order g2 (cyclic_gen g2) = CARD g2.carrier   by cyclic_gen_order

   By GroupHomo_def, this is to show:
   (1) x IN g1.carrier ==> g2.exp (cyclic_gen g2) (cyclic_index g1 x) IN g2.carrier
       This is true           by group_exp_element
   (2) x IN g1.carrier /\ x' IN g1.carrier ==>
         g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x')) =
         g2.op (g2.exp (cyclic_gen g2) (cyclic_index g1 x)) (g2.exp (cyclic_gen g2) (cyclic_index g1 x'))

         g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x'))
       = g2.exp (cyclic_gen g2) (((cyclic_index g1 x) +
                                  (cyclic_index g1 x')) MOD (CARD g1.carrier)) by finite_cyclic_index_add
       = g2.exp (cyclic_gen g2) ((cyclic_index g1 x) + (cyclic_index g1 x'))   by group_exp_mod, group_order_pos
       = g2.op (g2.exp (cyclic_gen g2) (cyclic_index g1 x))
               (g2.exp (cyclic_gen g2) (cyclic_index g1 x'))                   by group_exp_add
*)
val finite_cyclic_group_homo = store_thm(
  "finite_cyclic_group_homo",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2``,
  rpt strip_tac >>
  `Group g2 /\ FiniteGroup g2` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g2 IN g2.carrier` by rw[cyclic_gen_def] >>
  `order g2 (cyclic_gen g2) = CARD g2.carrier` by rw[cyclic_gen_order] >>
  rw[GroupHomo_def] >>
  `g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.op x x')) =
    g2.exp (cyclic_gen g2) (((cyclic_index g1 x) + (cyclic_index g1 x')) MOD (CARD g1.carrier))` by rw[finite_cyclic_index_add] >>
  `_ = g2.exp (cyclic_gen g2) ((cyclic_index g1 x) + (cyclic_index g1 x'))` by metis_tac[group_exp_mod, group_order_pos] >>
  rw[group_exp_add]);

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier *)
(* Proof:
   Note Group g2                                     by cyclic_group
    and FiniteGroup g2                               by FiniteGroup_def
   Note cyclic_gen g2 IN g2.carrier                  by cyclic_gen_def
    and order g2 (cyclic_gen g2) = CARD g2.carrier   by cyclic_gen_order

   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN g1.carrier ==> g2.exp (cyclic_gen g2) (cyclic_index g1 x) IN g2.carrier
       This is true           by group_exp_element
   (2) x IN g1.carrier /\ x' IN g1.carrier /\
       g2.exp (cyclic_gen g2) (cyclic_index g1 x) = g2.exp (cyclic_gen g2) (cyclic_index g1 x') ==> x = x'
       Note cyclic_index g1 x < CARD g2.carrier           by cyclic_index_def
        and cyclic_index g1 x' < CARD g2.carrier          by cyclic_index_def
       Thus cyclic_index g1 x = cyclic_index g1 x'        by group_exp_equal, group_order_ps
            x
          = g1.exp (cyclic_gen g1) (cyclic_index g1 x)    by finite_cyclic_index_unique
          = g1.exp (cyclic_gen g1) (cyclic_index g1 x')   by above
          = x'                                            by finite_cyclic_index_unique
   (3) x IN g2.carrier ==> ?x'. x' IN g1.carrier /\ g2.exp (cyclic_gen g2) (cyclic_index g1 x') = x
       Note Group g1                                      by cyclic_group
        and FiniteGroup g1                                by FiniteGroup_def
       Note cyclic_gen g1 IN g2.carrier                   by cyclic_gen_def
        and order g1 (cyclic_gen g1) = CARD g1.carrier    by cyclic_gen_order
        and cyclic_index g2 x < CARD g2.carrier           by cyclic_index_def

        Let x' = g1.exp (cyclic_gen g1) (cyclic_index g2 x).
       Then g1.exp (cyclic_gen g1) (cyclic_index g2 x) IN g1.carrier    by group_exp_element
        and g2.exp (cyclic_gen g2) (cyclic_index g1 (g1.exp (cyclic_gen g1) (cyclic_index g2 x)))
           = g2.exp (cyclic_gen g2) (cyclic_index g2 x)    by finite_cyclic_index_property
           = x                                             by cyclic_index_def
*)
val finite_cyclic_group_bij = store_thm(
  "finite_cyclic_group_bij",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier``,
  rpt strip_tac >>
  `Group g2 /\ FiniteGroup g2` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g2 IN g2.carrier` by rw[cyclic_gen_def] >>
  `order g2 (cyclic_gen g2) = CARD g2.carrier` by rw[cyclic_gen_order] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    `cyclic_index g1 x < CARD g2.carrier /\ cyclic_index g1 x' < CARD g2.carrier` by metis_tac[cyclic_index_def] >>
    `cyclic_index g1 x = cyclic_index g1 x'` by metis_tac[group_exp_equal, group_order_pos] >>
    metis_tac[finite_cyclic_index_unique],
    `Group g1 /\ FiniteGroup g1` by rw[FiniteGroup_def, cyclic_group] >>
    `cyclic_gen g1 IN g1.carrier` by rw[cyclic_gen_def] >>
    `order g1 (cyclic_gen g1) = CARD g1.carrier` by rw[cyclic_gen_order] >>
    qexists_tac `g1.exp (cyclic_gen g1) (cyclic_index g2 x)` >>
    rw[] >>
    `cyclic_index g2 x < CARD g2.carrier` by rw[cyclic_index_def] >>
    `cyclic_index g1 (g1.exp (cyclic_gen g1) (cyclic_index g2 x)) = cyclic_index g2 x` by fs[finite_cyclic_index_property] >>
    rw[cyclic_index_def]
  ]);

(* Theorem: cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2 *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2
       This is true by finite_cyclic_group_homo
   (2) BIJ (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1.carrier g2.carrier
       This is true by finite_cyclic_group_bij
*)
val finite_cyclic_group_iso = store_thm(
  "finite_cyclic_group_iso",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\
   FINITE g1.carrier /\ FINITE g2.carrier /\ (CARD g1.carrier = CARD g2.carrier) ==>
      GroupIso (\x. g2.exp (cyclic_gen g2) (cyclic_index g1 x)) g1 g2``,
  rw[GroupIso_def] >-
  rw[finite_cyclic_group_homo] >>
  rw[finite_cyclic_group_bij]);

(* Theorem: cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
            (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2 *)
(* Proof:
   Let f = \x. g2.exp (cyclic_gen g2) (cyclic_index g1 x).
   The result follows by finite_cyclic_group_iso
*)
val finite_cyclic_group_uniqueness = store_thm(
  "finite_cyclic_group_uniqueness",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
        (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2``,
  metis_tac[finite_cyclic_group_iso]);

(* This completes the classification of finite cyclic groups. *)

(* Another proof of uniqueness *)

(* Theorem: cyclic g /\ FINITE G ==> GroupHomo (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g *)
(* Proof:
   Note Group g                             by cyclic_group
    and FiniteGroup g                       by FiniteGroup_def
    and cyclic_gen g IN G                   by cyclic_gen_def
    and order g (cyclic_gen g) = CARD G     by cyclic_gen_order
   By GroupHomo_def, this is to show:
   (1) (cyclic_gen g) ** n IN G, true       by group_exp_element
   (2) n < CARD G /\ n' < CARD G ==>
       cyclic_gen g ** ((n + n') MOD CARD G) = cyclic_gen g ** n * cyclic_gen g ** n'
       Note cyclic_gen g ** ((n + n') MOD CARD G)
          = cyclic_gen g ** (n + n')                 by group_exp_mod, 0 < CARD G
          = cyclic_gen g ** n * cyclic_gen g ** n'   by group_exp_add
*)
val finite_cyclic_group_add_mod_homo = store_thm(
  "finite_cyclic_group_add_mod_homo",
  ``!g:'a group. cyclic g /\ FINITE G ==> GroupHomo (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g``,
  rpt strip_tac >>
  `Group g /\ FiniteGroup g` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `order g (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  rw[GroupHomo_def] >>
  `0 < CARD G` by decide_tac >>
  `cyclic_gen g ** ((n + n') MOD CARD G) = cyclic_gen g ** (n + n')` by metis_tac[group_exp_mod] >>
  rw[]);

(* Theorem: cyclic g /\ FINITE G ==> BIJ (\n. (cyclic_gen g) ** n) (add_mod (CARD G)).carrier G *)
(* Proof:
   Note Group g                             by cyclic_group
    and FiniteGroup g                       by FiniteGroup_def
    and cyclic_gen g IN G                   by cyclic_gen_def
    and order g (cyclic_gen g) = CARD G     by cyclic_gen_order
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) (cyclic_gen g) ** n IN G, true       by group_exp_element
   (2) n < CARD G /\ n' < CARD G /\ cyclic_gen g ** n = cyclic_gen g ** n' ==> n = n'
       This is true                         by finite_cyclic_index_property
   (3) x IN G ==> ?n. n < CARD G /\ (cyclic_gen g ** n = x)
       This is true                         by cyclic_index_def
*)
val finite_cyclic_group_add_mod_bij = store_thm(
  "finite_cyclic_group_add_mod_bij",
  ``!g:'a group. cyclic g /\ FINITE G ==> BIJ (\n. (cyclic_gen g) ** n) (add_mod (CARD G)).carrier G``,
  rpt strip_tac >>
  `Group g /\ FiniteGroup g` by rw[FiniteGroup_def, cyclic_group] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_def] >>
  `order g (cyclic_gen g) = CARD G` by rw[cyclic_gen_order] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  metis_tac[finite_cyclic_index_property] >>
  metis_tac[cyclic_index_def]);

(* Theorem: cyclic g /\ FINITE G ==> GroupIso (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo (\n. cyclic_gen g ** n) (add_mod (CARD G)) g
       This is true by finite_cyclic_group_add_mod_homo
   (2) BIJ (\n. cyclic_gen g ** n) (add_mod (CARD G)).carrier G
       This is true by finite_cyclic_group_add_mod_bij
*)
val finite_cyclic_group_add_mod_iso = store_thm(
  "finite_cyclic_group_add_mod_iso",
  ``!g:'a group. cyclic g /\ FINITE G ==> GroupIso (\n. (cyclic_gen g) ** n) (add_mod (CARD G)) g``,
  rw_tac std_ss[GroupIso_def] >-
  rw[finite_cyclic_group_add_mod_homo] >>
  rw[finite_cyclic_group_add_mod_bij]);

(* Theorem: cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
            (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2 *)
(* Proof:
   Note Group g1                             by cyclic_group
     so FiniteGroup g1                       by FiniteGroup_def
    ==> 0 < CARD g1.carrier                  by finite_group_card_pos
   Thus Group (add_mod (CARD g1.carrier))    by add_mod_group, 0 < CARD g1.carrier
   Let f1 = (\n. g1.exp (cyclic_gen g1) n),
       f2 = (\n. g2.exp (cyclic_gen g2) n).
    Now GroupIso f1 (add_mod (CARD g1.carrier)) g1    by finite_cyclic_group_add_mod_iso
    and GroupIso f2 (add_mod (CARD g2.carrier)) g2    by finite_cyclic_group_add_mod_iso
   Thus GroupIso (LINV f1 (add_mod (CARD g1.carrier)).carrier) g1 (add_mod (CARD g1.carrier))
                                                      by group_iso_sym
     or ?f. GroupIso f g1 g2                          by group_iso_trans
*)
val finite_cyclic_group_uniqueness = store_thm(
  "finite_cyclic_group_uniqueness",
  ``!g1:'a group g2:'b group. cyclic g1 /\ cyclic g2 /\ FINITE g1.carrier /\ FINITE g2.carrier /\
        (CARD g1.carrier = CARD g2.carrier) ==> ?f. GroupIso f g1 g2``,
  rpt strip_tac >>
  `Group g1 /\ FiniteGroup g1` by rw[cyclic_group, FiniteGroup_def] >>
  `0 < CARD g1.carrier` by rw[finite_group_card_pos] >>
  `Group (add_mod (CARD g1.carrier))` by rw[add_mod_group] >>
  `GroupIso (\n. g1.exp (cyclic_gen g1) n) (add_mod (CARD g1.carrier)) g1` by rw[finite_cyclic_group_add_mod_iso] >>
  `GroupIso (\n. g2.exp (cyclic_gen g2) n) (add_mod (CARD g2.carrier)) g2` by rw[finite_cyclic_group_add_mod_iso] >>
  metis_tac[group_iso_sym, group_iso_trans]);

(* ------------------------------------------------------------------------- *)
(* Isomorphism between Cyclic Groups                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: cyclic g /\ cyclic h /\ FINITE G /\
            GroupIso f g h ==> f (cyclic_gen g) IN (cyclic_generators h) *)
(* Proof:
   Note Group g /\ Group h          by cyclic_group
    and cyclic_gen g IN G           by cyclic_gen_element
   By cyclic_generators_element, this is to show:
   (1) f (cyclic_gen g) IN h.carrier, true by group_iso_element
   (2) order h (f (cyclic_gen g)) = CARD h.carrier
        order h (f (cyclic_gen g))
      = ord (cyclic_gen g)          by group_iso_order
      = CARD G                      by cyclic_gen_order, FINITE G
      = CARD h.carrier              by group_iso_card_eq
*)
val cyclic_iso_gen = store_thm(
  "cyclic_iso_gen",
  ``!(g:'a group) (h:'b group) f. cyclic g /\ cyclic h /\ FINITE G /\
        GroupIso f g h ==> f (cyclic_gen g) IN (cyclic_generators h)``,
  rpt strip_tac >>
  `Group g /\ Group h` by rw[] >>
  `cyclic_gen g IN G` by rw[cyclic_gen_element] >>
  rw[cyclic_generators_element] >-
  metis_tac[group_iso_element] >>
  `order h (f (cyclic_gen g)) = ord (cyclic_gen g)` by rw[group_iso_order] >>
  `_ = CARD G` by rw[cyclic_gen_order] >>
  metis_tac[group_iso_card_eq]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
