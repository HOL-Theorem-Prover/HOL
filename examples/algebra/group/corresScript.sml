(* ------------------------------------------------------------------------- *)
(* Group Correspondence Theory                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* ------------------------------------------------------------------------- *)

open pred_setTheory arithmeticTheory numberTheory combinatoricsTheory;

open groupTheory subgroupTheory;

open quotientGroupTheory groupMapTheory;

val _ = new_theory "corres";

(* ------------------------------------------------------------------------- *)
(* Group Correspondence Documentation                                        *)
(* ------------------------------------------------------------------------- *)
(* Notes:

   Author: Yiming Xu
   Editor: Joseph Chan
   Date: March 2018
   Summary: This makes use of the HOL4 Group and Subgroup Libraries
            to formalise the Correspondence Theorem of Group Theory.
   Reference: page 62 in Algebra (2nd Edition) by Michael Artin, ISBN: 0132413779.
*)
(* Overload:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   SURJ_IMAGE_PREIMAGE     |- !f a b. s SUBSET b /\ SURJ f a b ==> IMAGE f (PREIMAGE f s INTER a) = s
   count_formula           |- !g h. FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD (g / h).carrier
   iso_group_same_card     |- !g h. FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier
   Subgroup_subgroup       |- !g h. h <= g ==> subgroup h g
   Subgroup_homo_homo      |- !g h k f. h <= g /\ GroupHomo f g k ==> GroupHomo f h k

   Lemma 1:
   image_subgroup_subgroup |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==>
                                          homo_image f h g2 <= g2
   Lemma 2:
   preimage_group_def          |- !f g1 g2 h. preimage_group f g1 g2 h =
                                              <|carrier := PREIMAGE f h INTER g1.carrier;
                                                     op := g1.op;
                                                     id := g1.id|>
   preimage_group_property     |- !f g1 g2 h x. x IN PREIMAGE f h INTER g1.carrier ==>
                                                x IN g1.carrier /\ f x IN h
   preimage_group_group        |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
                                              Group (preimage_group f g1 g2 h.carrier)
   preimage_subgroup_subgroup  |- !f g1 g2 h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
                                              preimage_group f g1 g2 h.carrier <= g1

   Lemma 3:
   preimage_subgroup_kernel    |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
                                               kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier

   Lemma 4:
   normal_preimage_normal      |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
                                               h2 << g2 ==> preimage_group f g1 g2 h2.carrier << g1
   normal_surj_normal          |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
                                               SURJ f g1.carrier g2.carrier ==>
                                               preimage_group f g1 g2 h2.carrier << g1 ==> h2 << g2
   normal_iff_preimage_normal  |- !f g1 g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
                                               SURJ f g1.carrier g2.carrier ==>
                                               (h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1)

   Lemma 5:
   image_preimage_group    |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier ==>
                                          IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier
   subset_preimage_image   |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==>
                                          H SUBSET PREIMAGE f (IMAGE f H) INTER g1.carrier
   preimage_image_subset   |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET H ==>
                                          PREIMAGE f (IMAGE f H) INTER g1.carrier SUBSET H
   bij_corres              |- !f g1 g2 h1 h2. Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\
                                              GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
                                              kernel f g1 g2 SUBSET h1.carrier ==>
                               IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
                               PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier

   Lemma 6:
   homo_count_formula      |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
                               CARD (preimage_group f g1 g2 h.carrier).carrier =
                                 CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *
                                 CARD (preimage_group f g1 g2 h.carrier /
                                       kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
   image_iso_preimage_quotient     |- !f g1 g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
      GroupIso (\z. coset (preimage_group f g1 g2 h.carrier)
              (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
              (kernel f (preimage_group f g1 g2 h.carrier) g2))
        (homo_image f (preimage_group f g1 g2 h.carrier) g2)
        (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2)
   finite_homo_image       |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
                              FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier
   image_preimage_quotient_same_card   |- !f g1 g2 h.
      FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
      CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
      CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
   homo_restrict_same_kernel    |- !f g1 g2 h. H SUBSET g1.carrier /\ GroupHomo f g1 g2 /\
                                               kernel f g1 g2 SUBSET H ==> kernel f g1 g2 = kernel f h g2
   preimage_cardinality    |- !f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\
                                          SURJ f g1.carrier g2.carrier ==>
      CARD (preimage_group f g1 g2 h.carrier).carrier = CARD h.carrier * CARD (kernel f g1 g2)

   Correspondence Theorem:
   corres_thm    |- !f g1 g2 h1 h2. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\
                                    SURJ f g1.carrier g2.carrier /\ h1 <= g1 /\
                                    kernel f g1 g2 SUBSET h1.carrier /\ h2 <= g2 ==>
                     homo_image f h1 g2 <= g2 /\
                     preimage_group f g1 g2 h2.carrier <= g1 /\
                     kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier /\
                     (h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1) /\
                     IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
                     PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
                     (FiniteGroup g1 ==>
                         CARD (preimage_group f g1 g2 h2.carrier).carrier =
                         CARD h2.carrier * CARD (kernel f g1 g2))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* set tight equality *)
val _ = ParseExtras.tight_equality();

(* Firstly we prove a useful fact for set-theoric function to be used later. *)

(* lemma 0 (SURJ_IMAGE_PREIMAGE):
   Let f be a surjective function from set a to set b, let s be a subset of b, then f(f^{-1}(s) = s. *)
(* Theorem: s SUBSET b /\ SURJ f a b ==> (IMAGE f (PREIMAGE f s INTER a) = s) *)
(* Proof:
          f(f^{-1}(s)) = s
     <=>  x IN f(f^{-1}(s)) iff x IN s                                       definition of equality of sets
     <=>  ?y. y IN f^{-1}(s) /\ f(y) = x iff x IN s                          definition of image
     <=>  ?y. f(y) IN s /\ f(y) = x iff x IN s                               definition of preimage
     <=>  ?y. x IN s /\ f(y) = x iff x IN s                                  substitute ``f(y)`` by ``x``
     <=>  x IN s /\ !y. f(y) = x iff x IN s                                  FOL
     <=>  x IN s /\ T iff x IN s                                             definition of surjectiveness
     <=>  x IN s iff x IN s                                                  FOL
     <=>  T                                                                  FOL
*)

Theorem SURJ_IMAGE_PREIMAGE:
  !f a b. s SUBSET b /\  SURJ f a b ==> (IMAGE f(PREIMAGE f s INTER a) = s)
Proof
  rpt strip_tac >> simp[EXTENSION, PREIMAGE_def] >> strip_tac >> fs[SURJ_DEF] >>
  eq_tac >> rpt strip_tac >> metis_tac[SUBSET_DEF]
QED

(* Add some facts about cardinal arithmetic of groups. *)

(* count_formula:
   Let g be a group and h be a normal subgroup of g. Then CARD g = CARD h * CARD g / h. *)
(* Theorem: FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD ((g / h).carrier) *)
(* Proof:
   Note h <= g                   by normal_subgroup_def
    and FINITE G                 by FiniteGroup_def
        CARD G
      = CARD H * CARD (CosetPartition g h)    by Lagrange_identity
      = CARD H * CARD ((g / h).carrier)       by quotient_group_def
*)
val count_formula = store_thm(
  "count_formula",
  ``!g:'a group h. FiniteGroup g /\ h << g ==> CARD G = CARD H * CARD ((g / h).carrier)``,
  rpt strip_tac >>
  `(g / h).carrier = CosetPartition g h` by simp[quotient_group_def] >>
  fs[FiniteGroup_def, normal_subgroup_def] >>
  rw[Lagrange_identity]);

(* iso_group_same_card: If two groups g and h are isomorphic, then CARD g = CARD h. *)
(* Theorem:  FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier *)
(* Proof:
   Note BIJ f G h.carrier          by group_iso_bij
   Thus CARD G = CARD h.carrier    by FINITE_BIJ_CARD, FINITE G
*)
val iso_group_same_card = store_thm(
  "iso_group_same_card",
  ``!f g:'a group h. FINITE G /\ GroupIso f g h ==> CARD G = CARD h.carrier``,
  rpt strip_tac >>
  `BIJ f G h.carrier` by fs[group_iso_bij] >>
  metis_tac[FINITE_BIJ_CARD]);

(* lemma 1' (Subgroup_subgroup):
   The definition "Subgroup_def" implies the definition "subgroup_def" *)
(* Theorem: h <= g ==> subgroup h g *)
(* Proof: by subgroup_homomorphism *)
val Subgroup_subgroup = store_thm(
  "Subgroup_subgroup",
  ``!g:'a group h. h <= g ==> subgroup h g``,
  rw[subgroup_homomorphism]);

(* Theorem: h <= g /\ GroupHomo f g k ==> GroupHomo f h k *)
(* Proof:
   Note subgroup h g          by Subgroup_subgroup
   Thus GroupHomo f h k       by subgroup_homo_homo
*)
val Subgroup_homo_homo = store_thm(
  "Subgroup_homo_homo",
  ``!g:'a group h k f. h <= g /\ GroupHomo f g k ==> GroupHomo f h k``,
  rpt strip_tac >>
  `subgroup h g` by metis_tac[Subgroup_subgroup] >>
  metis_tac[subgroup_homo_homo]);

(* ------------------------------------------------------------------------- *)
(* Lemma 1                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 1 (image_subgroup_subgroup) :
   For a group homomorphism f from a group g1 to a group g2,
   the image of any subgroup h of g1 under f is a subgroup of g2. *)
(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==> homo_image f h g2 <= g2 *)
(* Proof:
   Note subgroup h g1             by Subgroup_subgroup, h <= g1
    ==> GroupHomo f h g2          by subgroup_homo_homo
    and Group h                   by subgroup_groups
   Thus homo_image f h g2 <= g2   by homo_image_subgroup
*)
val image_subgroup_subgroup = store_thm(
  "image_subgroup_subgroup",
  ``!g1:'a group g2 h f. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g1 ==> homo_image f h g2 <= g2``,
  rpt strip_tac >>
  `subgroup h g1` by fs[Subgroup_subgroup] >>
  `GroupHomo f h g2` by metis_tac[subgroup_homo_homo] >>
  `Group h` by metis_tac[subgroup_groups] >>
  metis_tac[homo_image_subgroup]);

(* This is Lemma 1 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 2                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 2 (preimage_subgroup_subgroup):
   For a group homomorphism f from a group g1 to a group g2,
       the preimage of any subgroup of g2 under f is a subgroup of g1. *)

(* ------------------------------------------------------------------------- *)
(* Preimage Group of Group Homomorphism.                                     *)
(* ------------------------------------------------------------------------- *)
val preimage_group_def = Define `
    preimage_group (f:'a -> 'b) (g1:'a group) (g2:'b group) (h:'b -> bool) =
    <| carrier := PREIMAGE f h INTER g1.carrier;
            op := g1.op;
            id := g1.id
     |>
`;
(* This is subset_group g1 (PREIMAGE f h INTER g1.carrier) *)


(* Theorem: x IN (PREIMAGE f h) INTER g1.carrier ==> x IN g1.carrier /\ f x IN h *)
(* Proof: by definitions. *)
val preimage_group_property = store_thm(
    "preimage_group_property",
    ``!(f:'a -> 'b) (g1:'a group) (g2:'b group) (h:'b -> bool) x.
       x IN (PREIMAGE f h) INTER g1.carrier ==> x IN g1.carrier /\ f x IN h``,
    rpt strip_tac >> fs[INTER_DEF, PREIMAGE_def]);

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
            Group (preimage_group f g1 g2 h.carrier) *)
(* Proof:
   By group_def_alt and other definitions, this is to show:
   (1) f (g1.op x y) IN h.carrier
         f (g1.op x y)
       = g2.op (f x) (f y)      by GroupHomo_def
       = h.op (f x) (f y)       by Subgroup_def
       which is IN h.carrier    by Subgroup_def, Group h
   (2) g1.op (g1.op x y) z = g1.op x (g1.op y z)
       This is true             by group_assoc
   (3) f g1.id IN h.carrier
         f g1.id
       = g2.id                  by group_homo_id
       = h.id                   by subgroup_id
       which is IN h.carrier    by group_id_element, Group h
   (4) ?y. (f y IN h.carrier /\ y IN g1.carrier) /\ g1.op y x = g1.id
       Let y = g1.inv x.
       Then f y = g2.inv (f x)  by group_homo_inv
                = h.inv (f x)   by subgroup_inv
                IN h.carrier    by group_inv_element
        and   y IN g1.carrier   by group_inv_element
        and g1.op y x = g1.id   by group_inv_thm
*)
val preimage_group_group = store_thm(
    "preimage_group_group",
 ``!f g1:'a group g2:'b group h. Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==> Group (preimage_group f g1 g2 h.carrier)``,
    rpt strip_tac >> rw_tac std_ss[group_def_alt] >> fs[preimage_group_def, preimage_group_property] >>
    fs[PREIMAGE_def]
    >- (fs[GroupHomo_def] >>
       ` g2.op (f x) (f y) = h.op (f x) (f y)` by fs[Subgroup_def] >>
       `Group h` by fs[Subgroup_def] >>
       `h.op (f x) (f y) IN h.carrier` by fs[group_def_alt] >> rw[])

    >- fs[group_def_alt]
    >- (`f g1.id = g2.id` by metis_tac[group_homo_id] >>
        `h.id = g2.id` by fs[subgroup_id] >> fs[Subgroup_def] >> fs[group_def_alt])
    >- (qexists_tac `g1.inv x` >> rpt strip_tac
        >-
      ( `f (g1.inv x) = g2.inv (f x)` by fs[group_homo_inv] >>
       `g2.inv (f x) = h.inv (f x)` by fs[subgroup_inv] >>
       `Group h` by fs[Subgroup_def] >> fs[group_inv_element])
        >- (`Group h` by fs[Subgroup_def] >>
           `h.inv (f x) IN h.carrier` by fs[group_inv_element] >> rw[])
        >- fs[group_inv_thm]));

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
            preimage_group f g1 g2 h.carrier <= g1 *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (preimage_group f g1 g2 h.carrier), true        by preimage_group_group
   (2) (preimage_group f g1 g2 h.carrier).carrier
        SUBSET g1.carrier, true                              by preimage_group_def
   (3) (preimage_group f g1 g2 h.carrier).op = g1.op, true   by preimage_group_def
*)
Theorem preimage_subgroup_subgroup:
  !f g1:'a group g2:'b group h.
    Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ h <= g2 ==>
    preimage_group f g1 g2 h.carrier <= g1
Proof
  rpt strip_tac >> simp[Subgroup_def] >> rpt strip_tac
  >- metis_tac[preimage_group_group] >>
  rw[preimage_group_def]
QED

(* This is Lemma 2 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 3                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 3 (preimage_subgroup_kernel):
   For a group homomorphism f from a group g to a group 'g,
   the preimage of any subgroup 'h of 'g under f contains the kernel of f. *)

(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
             (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier*)
(* Proof:
        k SUBSET f^{-1}('h)
    <=> !x. x IN k ==> x IN f^{-1}('h)                                 by definition of set inclusion
    <=> !x. x IN g /\ f(x) = #e ==> x IN g /\ f(x) IN 'h               by definition of kernel, preimage
    <=> !x. x IN g /\ f(x) = #e ==> x IN g /\ #e IN 'h                 substitute ``f(x)`` by ``#e``
    <=> T                                                              by definition of subgroup
*)
val preimage_subgroup_kernel = store_thm(
    "preimage_subgroup_kernel",
    ``!f g1:'a group g2 h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
             (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier``,
    rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >> rw[PREIMAGE_def] >>
    `h2.id = g2.id` by metis_tac[subgroup_id] >> `Group h2` by metis_tac[Subgroup_def] >>
    `h2.id IN h2.carrier` by metis_tac[group_id_element] >> metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Lemma 4                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 4 (normal_iff_preimage_normal):
   For a group homomorphism f from a group g to a group 'g, if 'h is a subgroup of 'g,
   then 'h is a normal subgroup of 'g iff PREIM f 'h is a normal subgroup of g. *)
(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
            (h2 << g2 ==> (preimage_group f g1 g2 h2.carrier) << g1) *)
(* Proof:
       'h is a normal subgroup of 'g ==> f^{-1}('h) is a normal subgroup of g.
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ y IN f^{-1}('h) ==> x * y * x^{-1} IN f^{-1}('h)) by definition of normal subgroup
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ f(y) IN 'h ==> f(x * y * x^{-1}) IN 'h            by definition of preimage
   <=> (!'x 'y. 'x IN 'g /\ 'y IN 'h ==> 'x * 'y * 'x^{-1} IN 'h)
       ==> (!x y. x IN g /\ f(y) IN 'h ==> f(x) * f(y) * (f(x))^{-1} IN 'h    by definition of homomorphism
                                                                                 f(x^{-1}) = (f(x))^{-1}
   <=> T                                                                      by FOL

       f^{-1}('h) is a normal subgroup of g ==> 'h is a normal subgroup of 'g.
   <=> (!a b. a IN g /\ b IN f^{-1}('h) ==> a * b * a^{-1} IN f^{-1}('h))
        ==> (!x y. x IN 'g /\ y IN 'h ==> x * y * x^{-1} IN 'h)               by definition of normal subgroup
   <=> (!a b. a IN g /\ f(b) IN 'h ==> f(a) * f(b) * (f(a))^{-1} IN 'h)
        ==> (!x y. x IN 'g /\ y IN 'h ==> x * y * x^{-1} IN 'h)               by definition of preimage
   Now !x y. ?x' y'. x' IN g /\ y' IN g /\ f(x') = x /\ f(y') = y             by definition of surjectiveness
   <=> (!a b. a IN g /\ f(b) IN 'h ==> f(a) * f(b) * (f(a))^{-1} IN 'h)
        ==> (!f(x') f(y'). f(x') IN 'g /\ f(y') IN 'h ==> f(x') * f(y') * (f(x))^{-1} IN 'h)
                             by substitute ``x`` by ``f(x')`` and substitute ``y`` by ``f(y')``
   <=> T                                                                      by condition satisfied
*)
val normal_preimage_normal = store_thm(
    "normal_preimage_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 ==>
    (h2 << g2 ==> (preimage_group f g1 g2 h2.carrier) << g1)``,
    rpt strip_tac >>
    fs[normal_subgroup_def] >> rpt strip_tac >>
    simp[preimage_subgroup_subgroup] >>
    fs[preimage_group_def] >> fs[PREIMAGE_def] >>
    `f (g1.op (g1.op a z) (g1.inv a)) = g2.op (g2.op (f a) (f z)) (f (g1.inv a))` by fs[GroupHomo_def] >>
    `f (g1.inv a) = g2.inv (f a)` by fs[group_homo_inv] >>
    `f (g1.op (g1.op a z) (g1.inv a)) = g2.op (g2.op (f a) (f z)) (g2.inv (f a))` by rw[] >>
    `(f a) IN g2.carrier` by metis_tac[group_homo_element] >>
    metis_tac[]);

(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            ((preimage_group f g1 g2 h2.carrier) << g1 ==> (h2 << g2)) *)
(* Proof:
   By normal_subgroup_def and preimage_group_def, this is to show:
      a IN g2.carrier /\ z IN h2.carrier ==>
           g2.op (g2.op a z) (g2.inv a) IN h2.carrier
   Let a1 = CHOICE (preimage f g1.carrier a),
   and z1 = CHOICE (preimage f g1.carrier a),
   Then f a1 = a /\ f z1 = z          by preimage_choice_property.
    and f (g1.op (g1.op a1 z1) (g1.inv a1))
      = g2.op (g2.op a z) (g2.inv a)  by GroupHomo_def, group_homo_inv
   Thus g2.op (g2.op a z) (g2.inv a) IN h2.carrier    by GroupHomo_def
*)
val normal_surj_normal = store_thm(
    "normal_surj_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==> ((preimage_group f g1 g2 h2.carrier) << g1 ==> (h2 << g2))``,
    rpt strip_tac >> fs[normal_subgroup_def] >> rpt strip_tac >> fs[preimage_group_def] >> fs[PREIMAGE_def] >>
    `IMAGE f g1.carrier = g2.carrier` by fs[IMAGE_SURJ] >>
    `h2.carrier SUBSET g2.carrier` by fs[Subgroup_def] >>
    `a IN IMAGE f g1.carrier` by metis_tac[] >>
    `z IN IMAGE f g1.carrier` by metis_tac[SUBSET_DEF] >>
    `CHOICE (preimage f g1.carrier a) IN g1.carrier /\ f (CHOICE (preimage f g1.carrier a)) = a` by metis_tac[preimage_choice_property] >>
    `CHOICE (preimage f g1.carrier z) IN g1.carrier /\ f (CHOICE (preimage f g1.carrier z)) = z` by metis_tac[preimage_choice_property] >>
    `f (CHOICE (preimage f g1.carrier z)) IN h2.carrier` by metis_tac[] >>
    `f (g1.op (g1.op (CHOICE (preimage f g1.carrier a)) (CHOICE (preimage f g1.carrier z))) (g1.inv (CHOICE (preimage f g1.carrier a)))) IN h2.carrier` by metis_tac[] >>
    `(f (g1.inv (CHOICE (preimage f g1.carrier a)))) = (g2.inv (f (CHOICE (preimage f g1.carrier a))))` by fs[group_homo_inv] >>
    `f (g1.op (g1.op (CHOICE (preimage f g1.carrier a)) (CHOICE (preimage f g1.carrier z))) (g1.inv (CHOICE (preimage f g1.carrier a)))) = g2.op (g2.op (f (CHOICE (preimage f g1.carrier a))) (f (CHOICE (preimage f g1.carrier z)))) (f (g1.inv (CHOICE (preimage f g1.carrier a))))` by fs[GroupHomo_def] >>
    `_ = g2.op (g2.op (f (CHOICE (preimage f g1.carrier a))) (f (CHOICE (preimage f g1.carrier z)))) (g2.inv (f (CHOICE (preimage f g1.carrier a))))` by rw[] >>
    `_ = g2.op (g2.op a z) (g2.inv a)` by rw[] >> metis_tac[]);


(* Theorem: Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) *)
(* Proof:
   If part: h2 << g2 ==> preimage_group f g1 g2 h2.carrier << g1
      This is true                    by normal_preimage_normal
   Only-if part: preimage_group f g1 g2 h2.carrier << g1 ==> h2 << g2
      This is true                    by normal_surj_normal
*)
val normal_iff_preimage_normal = store_thm(
    "normal_iff_preimage_normal",
    ``!f:'a -> 'b g1:'a group g2:'b group h2. Group g1 /\ Group g2 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
    (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1)``,
    rpt strip_tac >> eq_tac >- metis_tac[normal_preimage_normal] >> metis_tac[normal_surj_normal]);

(* This is Lemma 4 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 5                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 5 (bij_corres):
    Let g, 'g are groups and f is a surjective group homomorphism from g to 'g.
    Let h be a subgroup of g contains the kernel of f, and let 'h be any subgroup of 'g,
    then f (PREIM f 'h) = 'h and PREIM f (f h) = h. *)
(* Proof:
   only need to prove f^{-1}(f(h)) is a subset of h,
   the other three follows from IMAGE_PREIMAGE, PREIMAGE_IMAGE, SURJ_IMAGE_PREIMAGE respectively.

          f^{-1}(f(h)) SUBSET h
      <=> !x. x IN f^{-1}(f(h)) ==> x IN h                               by definition of set inclusion
      <=> !x. f(x) IN f(h) ==> x IN h                                    by definition of preimage
      <=> !x. f(x) IN 'g /\ ?x'. x' IN h /\ f(x') = f(x) ==> x IN h      by definition of image
     Note f(x'^{-1} * x) = f(x'^{-1}) * f(x)                             by definition of homomorphism
                         = f(x')^{-1} * f(x)                             by (previous thm)
                   = f(x)^{-1} * f(x)                                    substitute ``f(x')`` by ``f(x)``
                   = #e                                                  by definition of inverse
      so x'^{-1} * x IN k                                                by definition of kernel
      so x'^{-1} * x IN h                                                by definition of subset
      so ?y. y IN h /\ x'^{-1} * x = y                                   by definition of element
      so ?y. y IN h /\ x = x' * y                                        by left cancellation
      so x IN h                                                          by closure of group
*)


(* Theorem: Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier *)
(* Proof: by SURJ_IMAGE_PREIMAGE *)
val image_preimage_group = store_thm(
  "image_preimage_group",
  ``!f g1:'a group g2 h.
      Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
        IMAGE f (PREIMAGE f h.carrier INTER g1.carrier) = h.carrier``,
  rpt strip_tac >>
  `h.carrier SUBSET g2.carrier` by metis_tac[Subgroup_def] >>
  metis_tac[SURJ_IMAGE_PREIMAGE]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==>
            h.carrier SUBSET PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier *)
(* Proof: by PREIMAGE_IMAGE *)
val subset_preimage_image = store_thm(
    "subset_preimage_image",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 ==> h.carrier SUBSET PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier``,
    rpt strip_tac >> `h.carrier SUBSET g1.carrier` by metis_tac[Subgroup_def] >> fs[PREIMAGE_IMAGE]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\
            SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h.carrier ==>
            PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier SUBSET h.carrier *)
(* Proof:
   By SUBSET_DEF, PREIMAGE_def, this is to show:
      (!x. x IN g1.carrier /\ f x = g2.id ==> x IN H) /\ h <= g1 /\
      x' IN H /\ x IN g1.carrier /\ f x = f x' ==> x IN H

   Let y = g1.op x (g1.inv x').
   Note x' IN g1.carrier                 by subgroup_element
   Thus (g1.inv x') in g1.carrier        by group_inv_element
     or y IN g1.carrier                  by group_op_element
        f y
      = f (g1.op x (g1.inv x'))
      = g2.op (f x) f (g1.inv x')        by GroupHomo_def
      = g2.op (f x') f (g1.inv x')       by given, f x = f x'
      = f (g1.op x' (g1.inv x'))         by GroupHomo_def
      = f (g1.id)                        by group_rinv
      = g2.id                            by group_homo_id
   Thus y IN H                           by implication
    ==> h.op y x' IN H                   by group_op_element, h <= g1
    But h.op y x'
      = g1.op y x'                       by subgroup_op
      = g1.op (g1.op x (g1.inv x')) x'   by definition of y
      = g1.op x (g1.op (g1.inv x') x')   by group_assoc
      = g1.op x g1.id                    by group_linv
      = x                                by group_rid
     or x IN H
*)
val preimage_image_subset = store_thm(
    "preimage_image_subset",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g1 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h.carrier ==> PREIMAGE f (IMAGE f h.carrier) INTER g1.carrier SUBSET h.carrier``,
    rpt strip_tac >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[PREIMAGE_def] >>
    `H SUBSET g1.carrier` by fs[Subgroup_def] >>
    `x' IN g1.carrier` by fs[SUBSET_DEF] >>
    `g1.op x (g1.inv x') IN g1.carrier` by fs[group_def_alt] >>
    `(f x) IN g2.carrier` by fs[GroupHomo_def] >>
    `(f x') IN g2.carrier` by fs[GroupHomo_def] >>
    `g2.inv (f x') = f (g1.inv x')` by rw_tac std_ss[group_homo_inv] >>
    `g2.op (f x) (g2.inv (f x)) = g2.id` by fs[group_div_cancel] >>
    `g2.op (f x) (g2.inv (f x')) = g2.id` by metis_tac[] >>
    `g2.op (f x) (g2.inv (f x')) = g2.op (f x) (f (g1.inv x'))` by metis_tac[] >>
    `_ = f (g1.op x (g1.inv x'))` by fs[GroupHomo_def] >>
    `g1.inv x' IN g1.carrier` by fs[group_inv_element] >>
    `g1.op x (g1.inv x') IN g1.carrier` by fs[group_def_alt] >>
    `f (g1.op x (g1.inv x')) = g2.id` by metis_tac[] >>
    `g1.op x (g1.inv x') IN H` by metis_tac[] >>
    `Group h` by metis_tac[Subgroup_def] >>
    `g1.inv x' = h.inv x'` by metis_tac[subgroup_inv] >>
    `g1.op x (g1.inv x') = h.op x (g1.inv x')` by metis_tac[Subgroup_def] >>
    `_ = h.op x (h.inv x')` by metis_tac[] >>
    `h.op (h.op x (h.inv x')) x' IN H` by metis_tac[group_def_alt] >>
    `h.op (h.op x (h.inv x')) x' = g1.op (g1.op x (h.inv x')) x'` by fs[Subgroup_def] >>
    `_ = g1.op (g1.op x (g1.inv x')) x'` by metis_tac[subgroup_inv] >>
    `_ = g1.op x (g1.op (g1.inv x') x')` by metis_tac[group_assoc] >>
    `g1.op (g1.inv x') x' = g1.id` by metis_tac[group_linv] >>
    `h.op (h.op x (h.inv x')) x' = g1.op x g1.id` by metis_tac[] >>
    `g1.op x g1.id = x` by metis_tac[group_id] >> metis_tac[]);

(* Theorem: Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
            SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h1.carrier ==>
            IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
            PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier *)
(* Proof:
   This is to show:
   (1) IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier
       This is true                       by image_preimage_group
   (2) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
       By SUBSET_ANTISYM, need to show:
       (1) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier SUBSET h1.carrier
           This is true                   by preimage_image_subset
       (2) h1.carrier SUBSET PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier
           This is true                   by subset_preimage_image
*)
Theorem bij_corres:
  !f g1:'a group g2 h1 h2.
    Group g1 /\ Group g2 /\ h1 <= g1 /\ h2 <= g2 /\ GroupHomo f g1 g2 /\
    SURJ f g1.carrier g2.carrier /\ kernel f g1 g2 SUBSET h1.carrier ==>
    IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
    PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
Proof
  rpt strip_tac
  >- metis_tac[image_preimage_group] >>
  irule SUBSET_ANTISYM >> rpt conj_tac
  >- metis_tac[preimage_image_subset] >>
  metis_tac[subset_preimage_image]
QED

(* This is Lemma 5 *)

(* ------------------------------------------------------------------------- *)
(* Lemma 6                                                                   *)
(* ------------------------------------------------------------------------- *)

(* lemma 6 (preimage_cardinality):
   If g, 'g are groups and f is a group homomorphism from g to 'g and 'h is a subgroup of 'g,
   then the cardinality of the preimage of 'h is
    the cardinality of 'h times the cardinality of the kernel of f. *)
(* Proof:
   Note f restrict to f^{-1}('h) is a group homomorphism
        from the group f^{-1}('h) to the group 'h. by previous thm
        (maybe we need to give another name to the restricted f, all in f'.)
   so k is also the kernel of f'.
   by the first isomorphism thm, Iso 'h f^{-1}('h) / k
   by iso_group_same_card, CARD 'h = CARD f^{-1}('h) / k
   by counting_formula, CARD f^{-1}('h) = CARD f^{-1}('h) / k * CARD k
   substitute CARD f^{-1}('h) by CARD 'h, the result follows.
*)

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            CARD (preimage_group f g1 g2 h.carrier).carrier =
              (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) *
               CARD (preimage_group f g1 g2 h.carrier /
                     kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Let t = preimage_group f g1 g2 h.carrier, k = kernel_group f t g2.
   Note Group g1             by finite_group_is_group
    and t <= g1              by preimage_subgroup_subgroup
    ==> GroupHomo f t g2     by Subgroup_homo_homo
   Also Group t              by preimage_group_group
   Thus k << t               by kernel_group_normal
    and FiniteGroup t        by finite_subgroup_finite_group
   Thus CARD t.carrier = (CARD k.carrier) * CARD (t / k).carrier
                             by count_formula
*)
val homo_count_formula = store_thm(
    "homo_count_formula",
    ``!f g1 g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==> CARD (preimage_group f g1 g2 h.carrier).carrier = (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) * CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier``,
    rpt strip_tac >>
    `Group g1` by metis_tac[finite_group_is_group] >>
    `preimage_group f g1 g2 h.carrier <= g1` by metis_tac[preimage_subgroup_subgroup] >>
    `GroupHomo f (preimage_group f g1 g2 h.carrier) g2` by metis_tac[Subgroup_homo_homo] >>
    `Group (preimage_group f g1 g2 h.carrier)` by metis_tac[preimage_group_group] >>
    `kernel_group f (preimage_group f g1 g2 h.carrier) g2 << (preimage_group f g1 g2 h.carrier)` by metis_tac[kernel_group_normal] >>
    `FiniteGroup (preimage_group f g1 g2 h.carrier)` by metis_tac[finite_subgroup_finite_group] >>
    metis_tac[count_formula]);

(* Theorem: Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            GroupIso (\z. coset (preimage_group f g1 g2 h.carrier)
                          (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
                          (kernel f (preimage_group f g1 g2 h.carrier) g2))
               (homo_image f (preimage_group f g1 g2 h.carrier) g2)
               (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2) *)
(* Proof:
   Note Group (preimage_group f g1 g2 h.carrier)             by preimage_group_group
    and (preimage_group f g1 g2 h.carrier) <= g1             by preimage_subgroup_subgroup
   also GroupHomo f (preimage_group f g1 g2 h.carrier) g2    by Subgroup_homo_homo
   The result follows                                        by group_first_isomorphism_thm
*)
val image_iso_preimage_quotient = store_thm(
    "image_iso_preimage_quotient",
    ``!f g1:'a group g2 h. Group g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    GroupIso
         (λz.
             coset (preimage_group f g1 g2 h.carrier)
               (CHOICE
                  (preimage f (preimage_group f g1 g2 h.carrier).carrier
                     z))
               (kernel f (preimage_group f g1 g2 h.carrier) g2))
         (homo_image f (preimage_group f g1 g2 h.carrier) g2)
         (preimage_group f g1 g2 h.carrier /
          kernel_group f (preimage_group f g1 g2 h.carrier) g2)``,
    rpt strip_tac >>
    `Group (preimage_group f g1 g2 h.carrier)` by metis_tac[preimage_group_group] >>
    `(preimage_group f g1 g2 h.carrier) <= g1` by metis_tac[preimage_subgroup_subgroup] >>
    `GroupHomo f (preimage_group f g1 g2 h.carrier) g2` by metis_tac[Subgroup_homo_homo] >>
    imp_res_tac group_first_isomorphism_thm);

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
            FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Note FINITE g1.carrier                                  by FiniteGroup_def
   Thus FINITE (PREIMAGE f h.carrier INTER g1.carrier)     by FINITE_INTER
      = FINITE (preimage_group f g1 g2 h.carrier).carrier  by preimage_group_def
    ==> FINITE (IMAGE f (preimage_group f g1 g2 h.carrier).carrier)          by IMAGE_FINITE
      = FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier  by homo_image_def
*)
Theorem finite_homo_image:
  !f g1:'a group g2 h.
    FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier
Proof
  rpt strip_tac >>
  fs[homo_image_def] >>
  irule IMAGE_FINITE >>
  fs[preimage_group_def] >>
  irule FINITE_INTER >>
  metis_tac[FiniteGroup_def]
QED

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
    CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier *)
(* Proof:
   Let map = \z. coset (preimage_group f g1 g2 h.carrier)
                 (CHOICE (preimage f (preimage_group f g1 g2 h.carrier).carrier z))
                 (kernel f (preimage_group f g1 g2 h.carrier) g2)
       t1 = homo_image f (preimage_group f g1 g2 h.carrier) g2
       t2 = preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2
   Then GroupIso map t1 t2                   by image_iso_preimage_quotient
   Note FINITE t1.carrier                    by finite_homo_image, FiniteGroup g1
   Thus CARD t1.carrier = CARD t2.carrier    by iso_group_same_card
*)
Theorem image_preimage_quotient_same_card:
  !f g1:'a group g2 h.
    FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 ==>
    CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
    CARD
      (preimage_group f g1 g2 h.carrier /
       kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier
Proof
  rpt strip_tac >>
  `Group g1` by metis_tac[finite_group_is_group] >>
  imp_res_tac image_iso_preimage_quotient >>
  `FINITE (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier` by metis_tac[finite_homo_image] >>
  metis_tac[iso_group_same_card]
QED

(* Theorem: H SUBSET g1.carrier /\
            GroupHomo f g1 g2 /\ (kernel f g1 g2) SUBSET H ==> kernel f g1 g2 = kernel f h g2 *)
(* Proof:
   By kernel_def, preimage_def, this is to show:
      {x | x IN g1.carrier /\ f x = g2.id} SUBSET H ==>
      {x | x IN g1.carrier /\ f x = g2.id} = {x | x IN H /\ f x = g2.id}
   Since each is the other's SUBSET, they are equal by SET_EQ_SUBSET.
*)
val homo_restrict_same_kernel = store_thm(
  "homo_restrict_same_kernel",
  ``!f g1:'a group g2 h:'a group. H SUBSET g1.carrier /\
          GroupHomo f g1 g2 /\ (kernel f g1 g2) SUBSET H ==> kernel f g1 g2 = kernel f h g2``,
  rpt strip_tac >>
  fs[kernel_def] >>
  fs[preimage_def] >>
  fs[SET_EQ_SUBSET] >>
  rpt strip_tac >-
  fs[SUBSET_DEF] >>
  fs[SUBSET_DEF]);

(* Theorem: FiniteGroup g1 /\ Group g2 /\ h <= g2 /\
            GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==>
            CARD ((preimage_group f g1 g2 h.carrier).carrier) = CARD h.carrier * CARD (kernel f g1 g2) *)
(* Proof:
   Let t1 = preimage_group f g1 g2 h.carrier,
       t2 = kernel_group f t1 g2.
   Note Group g1                  by finite_group_is_group
        CARD t1.carrier
      = CARD t2.carrier * CARD ((t1 / t2).carrier)   by homo_count_formula

   Let k = kernel f g1 g2.
   Then k SUBSET (PREIMAGE f h.carrier ∩ g1.carrier)    by preimage_subgroup_kernel
    and k SUBSET t1.carrier                             by preimage_group_def
    and t1.carrier SUBSET g1.carrier                    by preimage_group_def
   Note t2.carrier
      = (kernel_group f t1).carrier                     by notation
      = kernel f t1 g2                                  by kernel_group_def
      = kernel f g1 g2 = k                              by homo_restrict_same_kernel
        CARD t1.carrier
      = CARD k * CARD ((t1 / t2.carrier))               by above
      = CARD k * CARD (homo_image f t1).carrier         by image_preimage_quotient_same_card
      = CARD k * CARD (IMAGE f t1.carrier)              by homo_image_def
      = CARD k * CARD (IMAGE f (PREIMAGE f h.carrier INTER g1.carrier)) by preimage_group_def
      = CARD k * CARD h.carrier                         by image_preimage_group
      = CARD h.carrier * CARD k                         by MULT_COMM
*)
val preimage_cardinality = store_thm(
    "preimage_cardinality",
    ``!f g1:'a group g2 h. FiniteGroup g1 /\ Group g2 /\ h <= g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier ==> CARD ((preimage_group f g1 g2 h.carrier).carrier) = CARD h.carrier * CARD (kernel f g1 g2)``,
    rpt strip_tac >>
    `Group g1` by fs[finite_group_is_group] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier = (CARD (kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier) * CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by metis_tac[homo_count_formula] >>
    `(kernel f g1 g2) SUBSET (PREIMAGE f h.carrier ∩ g1.carrier)` by metis_tac[preimage_subgroup_kernel] >>
    `(kernel f g1 g2) SUBSET (preimage_group f g1 g2 h.carrier).carrier` by fs[preimage_group_def] >>
    `(preimage_group f g1 g2 h.carrier).carrier SUBSET g1.carrier` by fs[preimage_group_def] >>
    `kernel f (preimage_group f g1 g2 h.carrier) g2 = kernel f g1 g2` by fs[homo_restrict_same_kernel] >>
    `(kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier = kernel f (preimage_group f g1 g2 h.carrier) g2` by fs[kernel_group_def] >>
    ` _ = kernel f g1 g2` by rw[] >>
    ` CARD (preimage_group f g1 g2 h.carrier).carrier =
      CARD (kernel f g1 g2) *
      CARD (preimage_group f g1 g2 h.carrier /
            kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by rw[] >>
    `CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier =
     CARD (preimage_group f g1 g2 h.carrier / kernel_group f (preimage_group f g1 g2 h.carrier) g2).carrier` by fs[image_preimage_quotient_same_card] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier =
       CARD (kernel f g1 g2) * CARD (homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier` by rw[] >>
    `(homo_image f (preimage_group f g1 g2 h.carrier) g2).carrier = IMAGE f (preimage_group f g1 g2 h.carrier).carrier` by fs[homo_image_def] >>
    `_ = IMAGE f (PREIMAGE f h.carrier INTER g1.carrier)` by fs[preimage_group_def] >>
    `_ = h.carrier` by metis_tac[image_preimage_group] >>
    `CARD (preimage_group f g1 g2 h.carrier).carrier =
     CARD (kernel f g1 g2) * CARD h.carrier` by fs[] >>
    `CARD (kernel f g1 g2) * CARD h.carrier = CARD h.carrier * CARD (kernel f g1 g2)` by metis_tac[MULT_COMM] >>
    metis_tac[]);

(* This is Lemma 6 *)

(* ------------------------------------------------------------------------- *)
(* Correspondence Theorem                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem:
   Let f be a surjective group homomorphism from group g to group 'g with kernel k.
   There is a bijective correspondence between subgroups of 'g and subgroups of g that contains k.
   The correspondence is defined as follows:
   a subgroup h of g that contains k |-> its image f h in 'g,
   a subgroup 'h of 'g |-> its inverse image f^{-1} 'h in g.
   If h and 'h are corresponding subgroups, then h is normal in g iff 'h is normal in 'g.
   If h and 'h are corresponding subgroups, then | h | = | 'h | | k |.
*)

(* Theorem: Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
            h1 <= g1 /\ (kernel f g1 g2) SUBSET h1.carrier /\ h2 <= g2 ==>
            homo_image f h1 g2 <= g2 /\
            preimage_group f g1 g2 h2.carrier <= g1 /\
            (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier /\
            (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) /\
            IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
            PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
            (FiniteGroup g1 ==>
              CARD (preimage_group f g1 g2 h2.carrier).carrier = CARD h2.carrier * CARD (kernel f g1 g2)) *)
(* Proof:
   Directly by lemma 1, 2, 3 and 4.
   Specifically, to show:
   (1) homo_image f h1 g2 <= g2, true                 by image_subgroup_subgroup
   (2) preimage_group f g1 g2 h2.carrier <= g1, true  by preimage_subgroup_subgroup
   (3) kernel f g1 g2 SUBSET PREIMAGE f h2.carrier INTER g1.carrier
       This is true                                   by preimage_subgroup_kernel
   (4) h2 << g2 <=> preimage_group f g1 g2 h2.carrier << g1
       This is true                                   by normal_iff_preimage_normal
   (5) IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier
       This is true                                   by bij_corres
   (6) PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier
       This is true                                   by bij_corres
   (7) CARD (preimage_group f g1 g2 h2.carrier).carrier =
       CARD h2.carrier * CARD (kernel f g1 g2)
       This is true                                   by preimage_cardinality
*)
val corres_thm = store_thm(
   "corres_thm",
   ``!f g1:'a group g2:'b group h1 h2.
   Group g1 /\ Group g2 /\ GroupHomo f g1 g2 /\ SURJ f g1.carrier g2.carrier /\
   h1 <= g1 /\ (kernel f g1 g2) SUBSET h1.carrier /\ h2 <= g2 ==>
   homo_image f h1 g2 <= g2 /\
   preimage_group f g1 g2 h2.carrier <= g1 /\
   (kernel f g1 g2) SUBSET (PREIMAGE f h2.carrier) INTER g1.carrier /\
   (h2 << g2 <=> (preimage_group f g1 g2 h2.carrier) << g1) /\
   IMAGE f (PREIMAGE f h2.carrier INTER g1.carrier) = h2.carrier /\
   PREIMAGE f (IMAGE f h1.carrier) INTER g1.carrier = h1.carrier /\
   (FiniteGroup g1 ==> CARD (preimage_group f g1 g2 h2.carrier).carrier = CARD h2.carrier * CARD (kernel f g1 g2))``,
   rpt strip_tac >-
   metis_tac[image_subgroup_subgroup] >- metis_tac[preimage_subgroup_subgroup] >-
   metis_tac[preimage_subgroup_kernel] >- metis_tac[normal_iff_preimage_normal] >-
   metis_tac[bij_corres] >- metis_tac[bij_corres] >- metis_tac[preimage_cardinality]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
