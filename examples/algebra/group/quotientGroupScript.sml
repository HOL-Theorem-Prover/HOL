(* ------------------------------------------------------------------------- *)
(* Group Theory -- Normal subgroup and Quotient Groups.                      *)
(* ------------------------------------------------------------------------- *)

(*

Normal Subgroup
===============
left Coset = right Coset

Quotient Group
==============
G/N where N is a normal subgroup.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "quotientGroup";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory numberTheory combinatoricsTheory;

open monoidTheory;

(* val _ = load "subgroupTheory"; *)
open groupTheory subgroupTheory;
open groupMapTheory;

(* ------------------------------------------------------------------------- *)
(* Quotient Group Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   x / y    = group_div g x y
   h << g   = normal_subgroup h g
   h == g   = group_equiv g h
   x o y    = coset_op g h x y
   g / h    = quotient_group g h
*)
(* Definitions and Theorems (# are exported):

   Group element division:
#  group_div_def      |- !g x y. x / y = x * |/ y
#  group_div_element  |- !g. Group g ==> !x y. x IN G /\ y IN G ==> x / y IN G
#  group_div_cancel   |- !g. Group g ==> !x. x IN G ==> (x / x = #e)
   group_div_pair     |- !g. Group g ==> !x1 y1 x2 y2. x1 IN G /\ y1 IN G /\ x2 IN G /\ y2 IN G ==>
                         (x1 * y1 / (x2 * y2) = x1 * (y1 / y2) / x1 * (x1 / x2))
   group_div_lsame    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (z * x / (z * y) = z * (x / y) / z)
   group_div_rsame    |- !g. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x * z / (y * z) = x / y)

   Normal Subgroup:
   normal_subgroup_def       |- !h g. h << g <=> h <= g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H
   normal_subgroup_subgroup  |- !h g. h << g ==> h <= g
   normal_subgroup_property  |- !h g. h << g ==> !a z. a IN G /\ z IN H ==> a * z / a IN H
   normal_subgroup_groups    |- !g h. h << g ==> h <= g /\ Group h /\ Group g
   normal_subgroup_refl      |- !g. Group g ==> g << g
   normal_subgroup_antisym   |- !g h. h << g /\ g << h ==> (h = g)
   normal_subgroup_alt       |- !g h. h << g <=> h <= g /\ !a. a IN G ==> (a * H = H * a)
   normal_subgroup_coset_eq  |- !g h. h << g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> x / y IN H)

   Equivalence induced by Normal Subgroup:
   group_equiv_def               |- !g h x y. x == y <=> x / y IN H
   group_normal_equiv_reflexive  |- !g h. h << g ==> !z. z IN G ==> z == z
   group_normal_equiv_symmetric  |- !g h. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> y == x)
   group_normal_equiv_transitive |- !g h. h << g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> x == y /\ y == z ==> x == z
   group_normal_equiv            |- !g h. h << g ==> $== equiv_on G
   group_normal_equiv_property   |- !h g. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> x IN y * H)

   Binary operation for cosets:
   cogen_def       |- !g h e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G /\ (e = cogen g h e * H)
   cogen_element   |- !h g e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G
   coset_cogen_property   |- !h g e. h <= g /\ e IN CosetPartition g h ==> (e = cogen g h e * H)
   coset_op_def           |- !g h x y. x o y = cogen g h x * cogen g h y * H
   cogen_of_subgroup      |- !g h. h <= g ==> (cogen g h H * H = H
   cogen_coset_element    |- !g h. h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G
   normal_cogen_property  |- !g h. h << g ==> !x. x IN G ==> x / cogen g h (x * H) IN H
   normal_coset_property1 |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * b * H = a * b * H)
   normal_coset_property2 |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (a * cogen g h (b * H) * H = a * b * H)
   normal_coset_property  |- !g h. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H)

   Quotient Group:
   quotient_group_def  |- !g h. g / h = <|carrier := CosetPartition g h; op := $o; id := H|>
   quotient_group_closure    |- !g h. h <= g ==>
      !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h
   quotient_group_assoc     |- !g h. h << g ==>
      !x y z. x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> ((x o y) o z = x o y o z)
   quotient_group_id        |- !g h. h << g ==> H IN CosetPartition g h /\ !x. x IN CosetPartition g h ==> (H o x = x)
   quotient_group_inv       |- !g h. h << g ==> !x. x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)
   quotient_group_group     |- !g h. h << g ==> Group (g / h)

   Group Homomorphism by left_coset via normal subgroup:
   normal_subgroup_coset_homo  |- !g h. h << g ==> GroupHomo (left_coset g H) g (g / h)
   normal_coset_op_property    |- !g h. h << g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==>
         (x o y = CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y) * H)
   coset_homo_group_iso_quotient_group |- !g h. h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)

   Kernel Group of Group Homomorphism:
   kernel_def             |- !f g h. kernel f g h = preimage f G h.id
   kernel_group_def       |- !f g h. kernel_group f g h = <|carrier := kernel f g h; id := #e; op := $* |>
#  kernel_property        |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)
   kernel_element         |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)
   kernel_group_group     |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h)
   kernel_group_subgroup  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> kernel_group f g h <= g
   kernel_group_normal    |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> kernel_group f g h << g
   kernel_quotient_group  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (g / kernel_group f g h)

   Homomorphic Image and Kernel:
   homo_image_def            |- !f g h. homo_image f g h = <|carrier := IMAGE f G; op := h.op; id := h.id|>
   homo_image_monoid         |- !g h f. Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h)
   homo_image_group          |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h)
   homo_image_subgroup       |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> homo_image f g h <= h
   group_homo_image_surj_property  |- !g h f. Group g /\ Group h /\
                                              SURJ f G h.carrier ==> GroupIso I h (homo_image f g h)
   monoid_homo_homo_image_monoid   |- !g h f. Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h)
   group_homo_homo_image_group     |- !g h f. Group g /\ MonoidHomo f g h ==> Group (homo_image f g h)

   First Isomorphic Theorem for Group:
   homo_image_homo_quotient_kernel    |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      GroupHomo (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   homo_image_to_quotient_kernel_bij  |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      BIJ (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h).carrier (g / kernel_group f g h).carrier
   homo_image_iso_quotient_kernel     |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      GroupIso (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   group_first_isomorphism_thm        |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
      kernel_group f g h << g /\ homo_image f g h <= h /\
      GroupIso (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h) /\
      (SURJ f G h.carrier ==> GroupIso I h (homo_image f g h))
*)

(* ------------------------------------------------------------------------- *)
(* Group element division.                                                   *)
(* ------------------------------------------------------------------------- *)
(* Define group division *)
val group_div_def = Define `
  group_div (g:'a group) (x:'a) (y:'a)  = x * |/ y
`;

(* set overloading *)
val _ = overload_on ("/", ``group_div g``);
val _ = set_fixity "/" (Infixl 600); (* same as "*" in arithmeticScript.sml *)

(* export simple defintion *)
val _ = export_rewrites ["group_div_def"];

(* Theorem: x / y IN G *)
(* Proof:
   x / y = x * |/y  by group_div_def
   and |/y IN G     by group_inv_element
   hence true       by group_op_element
*)
val group_div_element = store_thm(
  "group_div_element",
  ``!g:'a group. Group g ==> !x y. x IN G /\ y IN G ==> x / y IN G``,
  rw[group_div_def]);

val _ = export_rewrites ["group_div_element"];

(* Theorem: x / x = #e *)
(* Proof:
   x / x = x * |/x   by group_div_def
         = #e        by group_rinv
*)
val group_div_cancel = store_thm(
  "group_div_cancel",
  ``!g:'a group. Group g ==> !x. x IN G ==> (x / x = #e)``,
  rw[group_div_def]);

val _ = export_rewrites ["group_div_cancel"];

(* Theorem: (x1 * y1) / (x2 * y2) = x1 * (y1 / y2) / x1 * (x1 / x2) *)
(* Proof:
     (x1 * y1) / (x2 * y2)
   = (x1 * y1) * |/ (x2 * y2)                    by group_div_def
   = (x1 * y1) * ( |/ y2 * |/ x2)                by group_inv_op
   = x1 * (y1 * ( |/ y2 * |/ x2))                by group_assoc
   = x1 * (y1 * |/ y2 * |/ x2)                   by group_assoc
   = x1 * (y1 * |/ y2 * ( |/ x1 * x1 * |/ x2))   by group_linv, group_lid
   = x1 * (y1 * |/ y2 * ( |/ x1 * (x1 * |/ x2))) by group_assoc
   = x1 * (y1 / y2) * |/ x1 * (x1 / x2)          by group_assoc
   = x1 * (y1 / y2) / x1 * (x1 / x2)             by group_div_def
*)
val group_div_pair = store_thm(
  "group_div_pair",
  ``!g:'a group. Group g ==> !x1 y1 x2 y2. x1 IN G /\ y1 IN G /\ x2 IN G /\ y2 IN G ==>
    ((x1 * y1) / (x2 * y2) = (x1 * (y1 / y2) / x1) * (x1 / x2))``,
  rw_tac std_ss[group_div_def] >>
  `|/ x1 IN G /\ |/ y1 IN G /\ |/ x2 IN G /\ |/ y2 IN G` by rw[group_assoc] >>
  `(x1 * y1) * |/ (x2 * y2) = x1 * y1 * ( |/ y2 * |/ x2)` by rw[group_inv_op] >>
  `_ = x1 * (y1 * |/ y2 * |/ x2)` by rw[group_assoc] >>
  `_ = x1 * (y1 * |/ y2 * ( |/ x1 * x1 * |/ x2))` by rw_tac std_ss[group_linv, group_lid] >>
  `_ = (x1 * (y1 * |/ y2) * |/ x1) * (x1 * |/ x2)` by rw[group_assoc] >>
  rw_tac std_ss[]);

(* Theorem: (z * x) / (z * y) = z * (x / y) / z  *)
(* Proof:
     (z * x) / (z * y)
   = z * (x / y) / z * (z / z)    by group_div_pair
   = z * (x / y) / z * #e         by group_div_cancel
   = z * (x / y) / z              by group_rid
*)
val group_div_lsame = store_thm(
  "group_div_lsame",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((z * x) / (z * y) = z * (x / y) / z)``,
  rw[group_assoc, group_div_pair]);

(* Theorem: (x * z) / (y * z) = x / y  *)
(* Proof:
     (x * z) / (y * z)
   = x * (z / z) / x * (x / y)   by group_div_pair
   = x * #e / x * (x / y)        by group_div_cancel
   = x / x * (x / y)             by group_rid
   = #e * (x / y)                by group_div_cancel
   = x / y                       by group_lid
*)
val group_div_rsame = store_thm(
  "group_div_rsame",
  ``!g:'a group. Group g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> ((x * z) / (y * z) = x / y)``,
  rw[group_assoc, group_div_pair]);

(* ------------------------------------------------------------------------- *)
(* Normal Subgroup                                                           *)
(* ------------------------------------------------------------------------- *)

(* A Normal Subgroup: for all x IN H, for all a IN G, a * x / a IN H
   i.e. A subgroup, H, of a group, G, is called a normal subgroup if it is invariant under conjugation. *)
val normal_subgroup_def = Define `
  normal_subgroup (h:'a group) (g:'a group) <=>
    h <= g /\ (!a z. a IN G /\ z IN H ==> a * z / a IN H)
`;

(* set overloading *)
val _ = overload_on ("<<", ``normal_subgroup``);
val _ = set_fixity "<<" (Infixl 650); (* higher than * or / *)

(* Theorem: Normal subgroup is a subgroup. *)
val normal_subgroup_subgroup = save_thm("normal_subgroup_subgroup",
    normal_subgroup_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val normal_subgroup_subgroup = |- !h g. h << g ==> h <= g : thm *)

(* Theorem: Normal subgroup is invariant under conjugation. *)
val normal_subgroup_property = save_thm("normal_subgroup_property",
    normal_subgroup_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val normal_subgroup_property = |- !h g. h << g ==> !a z. a IN G /\ z IN H ==> a * z / a IN H : thm *)

(* Theorem: h << g ==> h <= g /\ Group h /\ Group g *)
(* Proof: by normal_subgroup_def and subgroup_property. *)
val normal_subgroup_groups = store_thm(
  "normal_subgroup_groups",
  ``!g h:'a group. h << g ==> h <= g /\ Group h /\ Group g``,
  metis_tac[normal_subgroup_def, subgroup_property]);

(* Theorem: g << g *)
(* Proof: by definition, this is to show:
   g <= g,
   True by subgroup_refl
*)
val normal_subgroup_refl = store_thm(
  "normal_subgroup_refl",
  ``!g:'a group. Group g ==> g << g``,
  rw[normal_subgroup_def, subgroup_refl]);

(* Theorem: h << g /\ g << h ==> h = g *)
(* Proof: by definition, this is to show:
   h <= g /\ g <= h ==> h = g,
   True by subgroup_antisym.
*)
val normal_subgroup_antisym = store_thm(
  "normal_subgroup_antisym",
  ``!(g:'a group) (h:'a group). h << g /\ g << h ==> (h = g)``,
  rw[normal_subgroup_def, subgroup_antisym]);

(* Note: Subgroup normality is not transitive:
see: http://groupprops.subwiki.org/wiki/Normality_is_not_transitive

D4 = <a, x | a^4 = x^2 = e, x a x = |/a >
Let H1 = <x>, H2 = <a^2 x>, K = <x, a^2>
Then H1 << K, H2 << K, K << D4, but neither H1 << D4 nor H2 << D4.

i.e. <s> << <r^2, s> << <r, s>=D4, but <s> is not normal in D4.

or
In S4 and its following subgroup A={(12)(34)} and B={(12)(34),(13)(42),(23)(41),e}
Try to show A is normal in B and B is normal in S4 but A is not normal in G.

*)

(* Property of Normal Subgroup: a subgroup with left coset = right coset. *)
(* Theorem: h << g <=> h <= g /\ aH = Ha  for all a in G. *)
(* Proof:
   If-part:
     h << g ==> !a. a IN G ==> (IMAGE (\z. z * a) H = IMAGE (\z. a * z) H)
   This essentially boils down to 2 cases:
   case 1. h <= g /\ a IN G /\ z IN H ==> ?z'. (z * a = a * z') /\ z' IN H
      By group property, z' = |/a * z * a, need to show that z' IN H
      This is because, a IN G ==> |/a IN G,
      hence |/a * z * |/( |/ a) IN H    by by conjugate property
         or |/a * z * a        IN H    by group_inv_inv
   case 2. h <= g /\ a IN G /\ z IN H ==> ?z'. (a * z = z' * a) /\ z' IN H
      By group property, z' = a * z / a, need to show z' IN H
      This is because a IN G, hence true by conjugate property.
   Only-if part:
      h <= g /\ !a. a IN G ==> (IMAGE (\z. z * a) H = IMAGE (\z. a * z) H) ==> a * z * |/ a IN H
      Since a * z IN right image, there is z' such that z' * a = a * z and z' IN H
      i.e. z' = a * z * |/a IN H,
              = a * z / a   IN H.
*)
val normal_subgroup_alt = store_thm(
  "normal_subgroup_alt",
  ``!g h:'a group. h << g <=> h <= g /\ (!a. a IN G ==> (a * H = H * a))``,
  rw_tac std_ss[normal_subgroup_def, coset_def, right_coset_def, EQ_IMP_THM] >| [
    rw[EXTENSION] >>
    `Group h /\ Group g` by metis_tac[subgroup_property] >>
    `|/a IN G` by rw[] >>
    rw_tac std_ss[EQ_IMP_THM] >| [
      qexists_tac `a * z / a` >>
      `z IN G` by metis_tac[subgroup_element] >>
      rw[group_rinv_assoc],
      qexists_tac `|/a * z * a` >>
      `z IN G` by metis_tac[subgroup_element] >>
      rw[group_assoc, group_linv_assoc] >>
      `|/ a * (z * a) = |/a * z * a` by rw[group_assoc] >>
      metis_tac[group_inv_inv, group_div_def]
    ],
    full_simp_tac std_ss [IMAGE_DEF, EXTENSION, GSPECIFICATION] >>
    `?z'. (a * z = z' * a) /\ z' IN H` by metis_tac[] >>
    metis_tac[group_rinv_assoc, group_div_def, Subgroup_def, SUBSET_DEF]
  ]);

(* Theorem: x * H = y * H ==> x / y IN H  if  H is a normal subgroup *)
(* Proof:
   By subgroup_coset_eq, |/y * x IN H
   i.e. y * ( |/y * x) * |/ y    IN H  by normal_subgroup_property
     or x * |/ y                 IN H  by group_assoc, group_rinv, group_lid
     or x / y                    IN H  by group_div_def
*)
val normal_subgroup_coset_eq = store_thm(
  "normal_subgroup_coset_eq",
  ``!g h:'a group. h << g ==> !x y. x IN G /\ y IN G ==> ((x * H = y * H) <=> x / y IN H)``,
  rw_tac std_ss[normal_subgroup_def, group_div_def] >>
  `|/y * x IN H <=> x * |/ y IN H` suffices_by rw_tac std_ss[subgroup_coset_eq] >>
  `Group h /\ Group g` by metis_tac[subgroup_property] >>
  `y * ( |/y * x) * |/ y = y * |/y * x * |/ y` by rw[group_assoc] >>
  `_ = x * |/ y` by rw_tac std_ss[group_rinv, group_lid] >>
  `|/ x * (x * |/ y) * x = |/ x * x * |/ y * x` by rw[group_assoc] >>
  `_ = |/ y * x` by rw_tac std_ss[group_linv, group_lid, group_inv_element] >>
  metis_tac[group_inv_element, group_inv_inv]);

(* ------------------------------------------------------------------------- *)
(* Equivalence induced by Normal Subgroup                                    *)
(* ------------------------------------------------------------------------- *)

(* Two group elements x y are equivalent if  x / y = x * |/y in normal subgroup. *)

(* Define group element equivalence by normal subgroup. *)
val group_equiv_def = Define `
  group_equiv (g:'a group) (h:'a group) x y  <=> x / y IN H
`;

(* set overloading *)
val _ = overload_on ("==", ``group_equiv g h``);
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [== is reflexive] h << g ==> z == z   for z IN G. *)
(* Proof:
   z == z  iff z / z         IN H  by group_equiv_def
           iff z * |/z = #e  IN H  by group_div_def, group_rinv
   which is true since h <= g, and Group h.
   or: since h << g, h.id = #e     by subgroup_id
   hence   z * |/z = z * #e * |/z  IN H   by normal_subgroup_property.
*)
val group_normal_equiv_reflexive = store_thm(
  "group_normal_equiv_reflexive",
  ``!g h:'a group. h << g ==> !z. z IN G ==> z == z``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  metis_tac[group_id_element, subgroup_id, group_rid, Subgroup_def]);

(* Theorem: [== is symmetric] h << g ==> x == y <=> y == x   for x, y IN G. *)
(* Proof:
   x == y  iff x / y         IN H    by group_equiv_def
           iff x * |/ y      IN H    by group_div_def
           iff |/ (x * |/ y) IN H    by group_inv_element
           iff y * |/ x      IN H    by group_inv_op, group_inv_inv
           if  y / x         IN H    by group_div_def
           iff y == x                by group_equiv_def
*)
val group_normal_equiv_symmetric = store_thm(
  "group_normal_equiv_symmetric",
  ``!g h:'a group. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> y == x)``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  `Group h /\ Group g` by metis_tac[Subgroup_def] >>
  `|/ ( x * |/ y) = y * |/ x` by rw[group_inv_inv, group_inv_op] >>
  `|/ ( y * |/ x) = x * |/ y` by rw[group_inv_inv, group_inv_op] >>
  metis_tac[group_inv_element, subgroup_inv]);

(* Theorem: [== is transitive] h << g ==> x == y /\ y == z ==> x == z   for x, y, z IN G. *)
(* Proof:
   x == y  iff x * |/ y  IN H        by group_equiv_def, group_div_def
   y == z  iff y * |/ z  IN H        by by group_equiv_def, group_div_def
   Together,
      (x * |/ y) * (y * |/ z) IN H   by group_op_element
   or  x * |/ z               IN H   by group_assoc, group_linv
   i..e. x == z                      by by group_equiv_def, group_div_def
*)
val group_normal_equiv_transitive = store_thm(
  "group_normal_equiv_transitive",
  ``!g h:'a group. h << g ==> !x y z. x IN G /\ y IN G /\ z IN G ==> (x == y /\ y == z ==> x == z)``,
  rw_tac std_ss[normal_subgroup_def, group_equiv_def, group_div_def] >>
  `Group h /\ Group g` by metis_tac[Subgroup_def] >>
  `(x * |/ y) * (y * |/ z) = (x * |/ y) * y * |/ z` by rw[group_assoc] >>
  `_ = x * |/ z` by rw_tac std_ss[group_linv, group_rid, group_assoc, group_inv_element] >>
  metis_tac[group_op_element, subgroup_property]);

(* Theorem: [== is an equivalence relation] h << g ==> $== equiv_on G. *)
(* Proof: by group_normal_equiv_reflexive, group_normal_equiv_symmetric, group_normal_equiv_transitive. *)
val group_normal_equiv = store_thm(
  "group_normal_equiv",
  ``!g h:'a group. h << g ==> $== equiv_on G``,
  rw_tac std_ss[equiv_on_def] >| [
    rw_tac std_ss[group_normal_equiv_reflexive],
    rw_tac std_ss[group_normal_equiv_symmetric],
    metis_tac[group_normal_equiv_transitive]
  ]);

(* ------------------------------------------------------------------------- *)
(* Normal Equivalence Classes are Cosets of Normal Subgroup.                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: for x, y in G, x == y  iff x IN y * H, the coset of y with normal subgroup. *)
(* Proof:
   x == y  iff   x / y IN H                 by group_equiv_def
           iff   x * |/ y  IN H             by group_div_def
           iff   x * |/ y = z,  where z IN H
           iff   x = z * y
           iff   x IN IMAGE (\z. z * y) H   by IMAGE definition
           iff   x IN IMAGE (\z. y * z) H   by normal_subgroup_alt
           iff   x IN yH                    by coset definition
*)
val group_normal_equiv_property = store_thm(
  "group_normal_equiv_property",
  ``!h g:'a group. h << g ==> !x y. x IN G /\ y IN G ==> (x == y <=> x IN y * H)``,
  rw_tac std_ss[group_equiv_def] >>
  `x / y IN H <=> x IN H * y` suffices_by metis_tac[normal_subgroup_alt] >>
  rw_tac std_ss[group_div_def, right_coset_def, IN_IMAGE] >>
  `x * |/ y IN H <=> ?z. z IN H /\ (z = x * |/ y)` by rw_tac std_ss[] >>
  metis_tac[group_lsolve, normal_subgroup_subgroup, Subgroup_def, SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* The map to set of costes and the induced binary operation.                *)
(* Aim: coset g H is a homomorphism: G -> Group of {a * H | a IN G}    *)
(* ------------------------------------------------------------------------- *)

(* from subgroupTheory:

- inCoset_def;
> val it = |- !g h a b. inCoset g h a b <=> b IN a * H : thm

- inCoset_equiv_on_carrier;
> val it = |- !g h. h <= g ==> inCoset g h equiv_on G : thm

- CosetPartition_def;
> val it = |- !g h. CosetPartition g h = partition (inCoset g h) G : thm

- coset_partition_element;
> val it = |- !g h. h <= g ==> !e. e IN CosetPartition g h ==> ?a. a IN G /\ (e = a * H) : thm

- GroupHomo_def;
> val it = |- !f g h. GroupHomo f g h <=> (!x. x IN G ==> f x IN H) /\
                                          !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)) : thm
- type_of ``a * H``;
> val it = ``:'a -> bool`` : hol_type

*)

(* Existence of coset generator: e IN CosetPartition g h ==> ?a. a IN G /\ (e = a * H) *)
val lemma = prove(
  ``!g h e. ?a. h <= g /\ e IN CosetPartition g h ==> a IN G /\ (e = a * H)``,
  metis_tac[coset_partition_element]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define coset generator *)
val cogen_def = new_specification(
    "cogen_def",
    ["cogen"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val cogen_def = |- !g h e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G /\ (e = (cogen g h e) * H) : thm *)

(* Theorem: h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G *)
val cogen_element = save_thm("cogen_element",
    cogen_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val cogen_element = |- !h g e. h <= g /\ e IN CosetPartition g h ==> cogen g h e IN G : thm *)

(* Theorem: h <= g /\ e IN CosetPartition g h ==> (cogen g h e) * H = e *)
val coset_cogen_property = save_thm("coset_cogen_property",
    cogen_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val coset_cogen_property = |- !h g e. h <= g /\ e IN CosetPartition g h ==> (e = (cogen g h e) * H) : thm *)

(* Define coset multiplication *)
val coset_op_def = Define `
  coset_op (g:'a group) (h:'a group) (x:'a -> bool) (y:'a -> bool) = ((cogen g h x) * (cogen g h y)) * H
`;

(* set overloading *)
val _ = overload_on ("o", ``coset_op g h``);

(* Theorem: h <= g ==> cogen g h H * H = H *)
(* Proof:
   Since H = #e * H          by coset_id_eq_subgroup
   H IN CosetPartition g h   by coset_partition_element
   hence cogen g h H * H = H by cogen_def
*)
val cogen_of_subgroup = store_thm(
  "cogen_of_subgroup",
  ``!g h:'a group. h <= g ==> (cogen g h H * H = H)``,
  rpt strip_tac >>
  `#e * H = H` by rw_tac std_ss[coset_id_eq_subgroup] >>
  `Group g` by metis_tac[Subgroup_def] >>
  `H IN CosetPartition g h` by metis_tac[coset_partition_element, group_id_element] >>
  rw_tac std_ss[cogen_def]);

(* Theorem: h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G *)
(* Proof:
   Since x * H  IN CosetPartition g h   by coset_partition_element
   cogen g h (x * H) IN G               by cogen_def
*)
val cogen_coset_element = store_thm(
  "cogen_coset_element",
  ``!g h:'a group. h <= g ==> !x. x IN G ==> cogen g h (x * H) IN G``,
  metis_tac[cogen_def, coset_partition_element]);

(* Theorem: x / cogen g h (x * H) IN H if H is a normal subgroup. *)
(* Proof:
   Since x * H IN CosetPartition g h  by coset_partition_element
         cogen g h (x * H) IN G /\
         ((cogen g h (x * H)) * H = x * H)  by cogen_def
   hence x / cogen g h (x * H) IN H   by normal_subgroup_coset_eq
*)
val normal_cogen_property = store_thm(
  "normal_cogen_property",
  ``!g h:'a group. h << g ==> !x. x IN G ==> x / cogen g h (x * H) IN H``,
  rpt strip_tac >>
  `h <= g` by rw_tac std_ss[normal_subgroup_subgroup] >>
  `x * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  `cogen g h (x * H) IN G /\ ((cogen g h (x * H)) * H = x * H)` by rw_tac std_ss[cogen_def] >>
  metis_tac[normal_subgroup_coset_eq]);

(* Theorem: h << g ==> cogen g h (a * H) * b * H = a * b * H  *)
(* Proof:
   By normal_subgroup_coset_eq, and reversing the equality,
   this is to show: (a * b) / (cogen g h (a * H) * b) IN H
   but  (a * b) / (cogen g h (a * H) * b) = a / cogen g h (a * H)  by group_div_rsame
   and  a / cogen g h (a * H) IN H    by normal_cogen_property.
*)
val normal_coset_property1 = store_thm(
  "normal_coset_property1",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * b * H = a * b * H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h (a * H) IN G` by rw_tac std_ss[cogen_coset_element] >>
  `a / cogen g h (a * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `(a * b) / (cogen g h (a * H) * b) = a / cogen g h (a * H)` by rw_tac std_ss[group_div_rsame] >>
  metis_tac[normal_subgroup_coset_eq, group_op_element]);

(* Theorem: h << g ==> a * cogen g h (b * H) * H = a * b * H  *)
(* Proof:
   By normal_subgroup_coset_eq, and reversing the equality,
   this is to show: (a * b) / (a * cogen g h (b * H)) IN H
   but (a * b) / (a * cogen g h (b * H)) = a * (b / cogen g h (b * H)) / a  by group_div_lsame
   and  b / cogen g h (b * H) IN H          by normal_cogen_property
   hence a * b / cogen g h (b * H) / a IN H by normal_subgroup_property
*)
val normal_coset_property2 = store_thm(
  "normal_coset_property2",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (a * cogen g h (b * H) * H = a * b * H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h (b * H) IN G` by rw_tac std_ss[cogen_coset_element] >>
  `b / cogen g h (b * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `a * b / (a * cogen g h (b * H)) = a * (b / cogen g h (b * H)) / a` by rw_tac std_ss[group_div_lsame] >>
  `a * b / (a * cogen g h (b * H)) IN H` by rw_tac std_ss[normal_subgroup_property] >>
  metis_tac[normal_subgroup_coset_eq, group_op_element]);

(* Theorem: h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H) *)
(* Proof:
   h << g ==> h <= g                  by normal_subgroup_subgroup
   a IN G ==> cogen g h (a * H) IN G  by cogen_coset_element, h <= g
   b IN G ==> cogen g h (b * H) IN G  by cogen_coset_element, h <= g
     cogen g h (a * H) * cogen g h (b * H) * H
   = a * cogen g h (b * H) * H        by normal_coset_property1, h << g
   = a * b * H                        by normal_coset_property2, h << g
*)
val normal_coset_property = store_thm(
  "normal_coset_property",
  ``!g h:'a group. h << g ==> !a b. a IN G /\ b IN G ==> (cogen g h (a * H) * cogen g h (b * H) * H = a * b * H)``,
  rw_tac std_ss[normal_subgroup_subgroup, cogen_coset_element, normal_coset_property1, normal_coset_property2]);

(* ------------------------------------------------------------------------- *)
(* Quotient Group                                                            *)
(* ------------------------------------------------------------------------- *)
(* Define the quotient group, the group divided by a normal subgroup. *)
val quotient_group_def = Define`
  quotient_group (g:'a group) (h:'a group) =
    <| carrier := (CosetPartition g h);
            op := coset_op g h;
            id := H
     |>
`;

(* set overloading *)
val _ = overload_on ("/", ``quotient_group``);
val _ = set_fixity "/" (Infixl 600); (* same as "*" in arithmeticScript.sml *)

(*
- type_of ``(g:'a group) / (h:'a group)``;
> val it = ``:('a -> bool) group`` : hol_type
- type_of ``coset g H``;
> val it = ``:'a -> 'a -> bool`` : hol_type
*)

(* Theorem: [Quotient Group Closure]
   h << g ==> x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h *)
(* Proof:
   x o y = cogen g h x * cogen g h y * H    by coset_op_def
   Since cogen g h x IN G    by cogen_def
     and cogen g h y IN G    by cogen_def
   hence cogen g h x * cogen g h y IN G   by group_op_element
      or (cogen g h x * cogen g h y IN G) * H IN CosetPartition g h   by coset_partition_element.

*)
val quotient_group_closure = store_thm(
  "quotient_group_closure",
  ``!g h:'a group. h <= g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h``,
  rw_tac std_ss[coset_op_def] >>
  `cogen g h x IN G /\ cogen g h y IN G` by rw_tac std_ss[cogen_def] >>
  metis_tac[group_op_element, coset_partition_element, Subgroup_def]);

(* Theorem: [Quotient Group Associativity]
   h << g ==> x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> (x o y) o z = x o (y o z)  *)
(* Proof:
   By coset_op_def,
     (x o y) o z
   = cogen g h (cogen g h x * cogen g h y * H) * cogen g h z * H     by coset_op_def
   = ((cogen g h x * cogen g h y) * cogen g h z) * H                 by normal_coset_property1
   = (cogen g h x * (cogen g h y * cogen g h z)) * H                 by group_assoc
   = cogen g h x * cogen g h (cogen g h y * cogen g h z * H) * H     by normal_coset_property2
   = x o (y o z)                                                     by coset_op_def

   Since cogen g h x IN G    by cogen_def
     and cogen g h y IN G    by cogen_def
     and cogen g h z IN G    by cogen_def
   Let t = cogen g h x * cogen g h y  IN G
       t * H   IN CosetPartition g h
       cogen g h (t * H)  IN G /\ (cogen g h (t * H)) * H = t * H
   For h << g, this implies t / cogen g h (t * H)  IN H   by normal_cogen_property

*)
val quotient_group_assoc = store_thm(
  "quotient_group_assoc",
  ``!g h:'a group. h << g ==> !x y z. x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h
      ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  rw[group_assoc, normal_coset_property1, normal_coset_property2, cogen_coset_element, cogen_def]);

(* Theorem: [Quotient Group Identity]
   h << g ==> H IN CosetPartition g h /\ !x. x INCosetPartition g h ==> H o x = x *)
(* Proof:
   Since  #e * H = H                by coset_id_eq_subgroup
   hence  H IN CosetPartition g h   by coset_partition_element, group_id_element
   Since  cogen g h x IN G and x = cogen g h x * H     by cogen_def
   By normal_coset_property1,
       cogen g h (#e * H) * cogen g h x * H = #e * cogen g h x * H
   or  cogen g h H * cogen g h x * H = cogen g h x * H   by group_lid
   Hence
       H o x = cogen g h H * cogen g h x * H    by coset_op_def
             = cogen g h x * H                  by above
             = x
*)
val quotient_group_id = store_thm(
  "quotient_group_id",
  ``!g h:'a group. h << g ==> H IN CosetPartition g h /\ !x. x IN CosetPartition g h ==> (H o x = x)``,
  ntac 3 strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_def, Subgroup_def] >>
  `#e * H = H` by rw_tac std_ss[coset_id_eq_subgroup] >>
  `#e IN G` by rw_tac std_ss[group_id_element] >>
  rw_tac std_ss[coset_op_def] >| [
    metis_tac[coset_partition_element],
    `cogen g h x IN G /\ (cogen g h x * H = x)` by rw_tac std_ss[cogen_def] >>
    `cogen g h (#e * H) * cogen g h x * H = #e * cogen g h x * H` by rw_tac std_ss[normal_coset_property1] >>
    metis_tac[group_lid]
  ]);

(* Theorem: [Quotient Group Inverse]
   h << g ==> x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H) *)
(* Proof:
   Since x IN CosetPartition g h,
       cogen g h x IN G /\ (cogen g h x * H = x)                     by cogen_def
   and |/ (cogen g h x) IN G /\ |/ (cogen g h x) * cogen g h x = #e  by group_inv_element, group_linv
   hence  |/ (cogen g h x) * H IN CosetPartition g h                 by coset_partition_element
   Let y = |/ (cogen g h x) * H, then
   y o x = cogen g h ( |/ (cogen g h x) * H) * cogen g h x * H
         = |/ (cogen g h x) * H o cogen g h x * H                    by normal_coset_property1
         = ( |/ (cogen g h x) * cogen g h x) * H                     by coset_op_def
         = #e * H = H                                                by coset_id_eq_subgroup
*)
val quotient_group_inv = store_thm(
  "quotient_group_inv",
  ``!g h:'a group. h << g ==> !x. x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)``,
  rpt strip_tac >>
  `h <= g /\ Group g` by metis_tac[normal_subgroup_groups] >>
  `cogen g h x IN G /\ (cogen g h x * H = x)` by rw_tac std_ss[cogen_def] >>
  `|/ (cogen g h x) IN G /\ ( |/ (cogen g h x) * cogen g h x = #e)` by rw[] >>
  `|/ (cogen g h x) * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  metis_tac[coset_op_def, normal_coset_property1, coset_id_eq_subgroup]);

(* Theorem: quotient_group is a group for normal subgroup
   i.e. h << g ==> Group (quotient_group g h)               *)
(* Proof:
   This is to prove:
   (1) x IN CosetPartition g h /\ y IN CosetPartition g h ==> x o y IN CosetPartition g h
       true by quotient_group_closure.
   (2) x IN CosetPartition g h /\ y IN CosetPartition g h /\ z IN CosetPartition g h ==> (x o y) o z = x o y o z
       true by quotient_group_assoc.
   (3) H IN CosetPartition g h
       true by quotient_group_id.
   (4) x IN CosetPartition g h ==> H o x = x
       true by quotient_group_id.
   (5) x IN CosetPartition g h ==> ?y. y IN CosetPartition g h /\ (y o x = H)
       true by quotient_group_inv.
*)
val quotient_group_group = store_thm(
  "quotient_group_group",
  ``!g h:'a group. h << g ==> Group (quotient_group g h)``,
  rpt strip_tac >>
  `h <= g /\ Group h /\ Group g` by metis_tac[normal_subgroup_groups] >>
  rw_tac std_ss[group_def_alt, quotient_group_def] >| [
    rw_tac std_ss[quotient_group_closure],
    rw_tac std_ss[quotient_group_assoc],
    rw_tac std_ss[quotient_group_id],
    rw_tac std_ss[quotient_group_id],
    rw_tac std_ss[quotient_group_inv]
  ]);

(* ------------------------------------------------------------------------- *)
(* Group Homomorphism by left_coset via normal subgroup.                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: A normal subgroup induces a natural homomorphism to its quotient group, i.e.
            h << g ==> GroupHomo (left_coset g H) g (g / h) *)
(* Proof:
   After expanding by quotient_group_def, this is to show 2 things:
   (1) h << g /\ x IN G ==> x * H IN CosetPartition g h
       This is true by coset_partition_element, and normal_subgroup_subgroup.
   (2) h << g /\ x IN G /\ y IN G ==> (x * y) * H = x * H o y * H
       This is to show:
       (x * y) * H = (cogen g h (x * H) * cogen g h (y * H)) * H
       Since x * H IN CosetPartition g h    by coset_partition_element
             y * H IN CosetPartition g h    by coset_partition_element
       hence cogen g h (x * H) IN G         by cogen_def
             cogen g h (y * H) IN G         by cogen_def
       By normal_subgroup_coset_eq, this is to show:
             (x * y) / (cogen g h (x * H) * cogen g h (y * H)) IN H
       But  (x * y) / (cogen g h (x * H) * cogen g h (y * H))
          = x * (y / cogen g h (y * H)) / x * (x / cogen g h (x * H)  by group_div_pair

       Since      x / cogen g h (x * H) IN H    by normal_cogen_property
       and    z = y / cogen g h (y * H) IN H    by normal_cogen_property
       so     x * z * / x  IN H  since z IN H   by normal_subgroup_property
       hence their product is IN H              by group_op_element
*)
val normal_subgroup_coset_homo = store_thm(
  "normal_subgroup_coset_homo",
  ``!g h:'a group. h << g ==> GroupHomo (left_coset g H) g (g / h)``,
  rw_tac std_ss[GroupHomo_def, quotient_group_def, left_coset_def] >-
  metis_tac[coset_partition_element, normal_subgroup_subgroup] >>
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H` by metis_tac[normal_subgroup_def] >>
  `Group h /\ Group g /\ !x y. x IN H /\ y IN H ==> (h.op x y = x * y)` by metis_tac[subgroup_property] >>
  `x * H IN CosetPartition g h /\ y * H IN CosetPartition g h` by metis_tac[coset_partition_element] >>
  `cogen g h (x * H) IN G /\ cogen g h (y * H) IN G` by rw_tac std_ss[cogen_def] >>
  `(x * y) / (cogen g h (x * H) * cogen g h (y * H)) IN H`
     suffices_by rw_tac std_ss[normal_subgroup_coset_eq, group_op_element] >>
  rw_tac std_ss[group_div_pair] >>
  `x / cogen g h (x * H) IN H /\ y / cogen g h (y * H) IN H` by rw_tac std_ss[normal_cogen_property] >>
  `x * (y / cogen g h (y * H)) / x IN H` by rw_tac std_ss[normal_subgroup_property] >>
  metis_tac[group_op_element]);

(* Theorem: x o y = (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) * H *)
(* Proof:
   This is to show:
   cogen g h x * cogen g h y * H = CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y) * H
   By normal_subgroup_coset_eq, need to show:
      (cogen g h x * cogen g h y) / (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) IN H
   i.e.  (cogen g h x) * ((cogen g h y) / CHOICE (preimage (left_coset g H) G y)) / (cogen g h x) *
         ((cogen g h x) / CHOICE (preimage (left_coset g H) G x))   IN H    by group_div_pair
   Since  x = (cogen g h x) * H                by cogen_def
          x = (CHOICE (preimage (left_coset g H) G x)) * H   by preimage_choice_property
          (cogen g h x) / (CHOICE (preimage (left_coset g H) G x)) IN H    by normal_subgroup_coset_eq
   Similarly,
          y = (cogen g h y) * H                by cogen_def
          y = (CHOICE (preimage (left_coset g H) G y)) * H   by preimage_def
          (cogen g h y) / (CHOICE (preimage (left_coset g H) G y)) IN H    by normal_subgroup_coset_eq
   Hence (cogen g h x) * ((cogen g h y) / (CHOICE (preimage (left_coset g H) G y))) / (cogen g h x)   by normal_subgroup_property
   and the whole product is thus in H                by group_op_element, as h <= g ==> Group h.
*)
val normal_coset_op_property = store_thm(
  "normal_coset_op_property",
  ``!g h:'a group. h << g ==> !x y. x IN CosetPartition g h /\ y IN CosetPartition g h ==>
     (x o y = (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) * H)``,
  rw_tac std_ss[coset_op_def] >>
  `h <= g /\ Group g /\ !a z. a IN G /\ z IN H ==> a * z / a IN H` by metis_tac[normal_subgroup_def, subgroup_property] >>
  `cogen g h x IN G /\ ((cogen g h x) * H = x)` by rw_tac std_ss[cogen_def] >>
  `cogen g h y IN G /\ ((cogen g h y) * H = y)` by rw_tac std_ss[cogen_def] >>
  `x IN IMAGE (left_coset g H) G` by metis_tac[coset_partition_element, left_coset_def, IN_IMAGE] >>
  `y IN IMAGE (left_coset g H) G` by metis_tac[coset_partition_element, left_coset_def, IN_IMAGE] >>
  `CHOICE (preimage (left_coset g H) G x) IN G /\ (x = (CHOICE (preimage (left_coset g H) G x)) * H)` by metis_tac[preimage_choice_property, left_coset_def] >>
  `CHOICE (preimage (left_coset g H) G y) IN G /\ (y = (CHOICE (preimage (left_coset g H) G y)) * H)` by metis_tac[preimage_choice_property, left_coset_def] >>
  `(cogen g h x) / CHOICE (preimage (left_coset g H) G x) IN H` by metis_tac[normal_subgroup_coset_eq] >>
  `(cogen g h y) / CHOICE (preimage (left_coset g H) G y) IN H` by metis_tac[normal_subgroup_coset_eq] >>
  `(cogen g h x * cogen g h y) / (CHOICE (preimage (left_coset g H) G x) * CHOICE (preimage (left_coset g H) G y)) IN H` suffices_by rw_tac std_ss[normal_subgroup_coset_eq, group_op_element] >>
  rw_tac std_ss[group_div_pair] >>
  prove_tac[group_op_element, subgroup_property]);
(* This theorem does not help to prove identity below, but helps to prove isomorphism. *)

(* Theorem: h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)  *)
(* Proof:
   This is to show:
   (1) h << g ==> GroupHomo I (homo_group g (left_coset g H)) (g / h)
       This is to show:
       (1.1) x IN IMAGE (left_coset g H) G ==> x IN CosetPartition g h
             true by subgroup_coset_in_partition.
       (1.2) x IN IMAGE (left_coset g H) G /\ y IN IMAGE (left_coset g H) G ==> image_op g (left_coset g H) x y = x o y
             Since x IN CosetPartition g h    by subgroup_coset_in_partition
                   y IN CosetPartition g h    by subgroup_coset_in_partition
             hence true by normal_coset_op_property, image_op_def, left_coset_def.
   (2) h << g ==> BIJ I (homo_group g (left_coset g H)).carrier (g / h).carrier
       This is to show: BIJ I (IMAGE (left_coset g H) G) (CosetPartition g h)
       Since h <= g  by normal_subgroup_def
       this is true by BIJ and subgroup_coset_in_partition.
*)
val coset_homo_group_iso_quotient_group = store_thm(
  "coset_homo_group_iso_quotient_group",
  ``!g h:'a group. h << g ==> GroupIso I (homo_group g (left_coset g H)) (g / h)``,
  rw_tac std_ss[GroupIso_def] >| [
    `h <= g` by metis_tac[normal_subgroup_def] >>
    rw_tac std_ss[GroupHomo_def, homo_monoid_def, quotient_group_def] >| [
      rw_tac std_ss[GSYM subgroup_coset_in_partition],
      `x IN CosetPartition g h` by rw_tac std_ss[GSYM subgroup_coset_in_partition] >>
      `y IN CosetPartition g h` by rw_tac std_ss[GSYM subgroup_coset_in_partition] >>
      rw_tac std_ss[image_op_def, left_coset_def, normal_coset_op_property]
    ],
    `h <= g` by metis_tac[normal_subgroup_def] >>
    rw_tac std_ss[homo_monoid_def, quotient_group_def] >>
    rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, subgroup_coset_in_partition]
  ]);

(* ------------------------------------------------------------------------- *)
(* Kernel Group of Group Homomorphism.                                       *)
(* ------------------------------------------------------------------------- *)

(* Define kernel of a mapping: the preimage of identity. *)
val kernel_def = Define`
  kernel f (g:'a group) (h:'b group) = preimage f G h.id
`;

(* Convert kernel to a group structure *)
val kernel_group_def = Define`
  kernel_group f (g:'a group) (h:'b group) =
    <| carrier := kernel f g h;
            id := g.id;
            op := g.op
     |>`;

(* Theorem: !x. x IN kernel f g h <=> x IN G /\ f x = h.id *)
(* Proof: by definition. *)
val kernel_property = store_thm(
  "kernel_property",
  ``!(g:'a group) (h:'b group). !f x. x IN kernel f g h <=> x IN G /\ (f x = h.id)``,
  simp_tac std_ss [kernel_def, preimage_def] >>
  rw[]);

(* export trivial truth. *)
val _ = export_rewrites ["kernel_property"];

(* Theorem alias *)
val kernel_element = save_thm("kernel_element", kernel_property);
(*
val kernel_element = |- !g h f x. x IN kernel f g h <=> x IN G /\ (f x = h.id): thm
*)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h) *)
(* Proof:
   This is to show:
   (1) x IN kernel f g h /\ y IN kernel f g h ==> x * y IN kernel f g h
   By kernel property, x IN G and y IN G.
   f (x * y) = (f x) o (f y)      by GroupHomo_def
             = h.id o h.id        by kernel_property
             = h.id               by group_id_id
   Since x * y IN G               by group_op_element
   Hence x * y IN kernel f g h    by preimage_of_image
   (2) x IN kernel f g h /\ y IN kernel f g h /\ z IN kernel f g h ==> x * y * z = x * (y * z)
   By kernel_property, x IN G, y IN G and z IN G,
   Hence x * y * z = x * (y * z)  by group_assoc
   (3) #e IN kernel f g h
   Since #e IN G                  by group_id_element
   and f #e = h.id                by group_homo_id
   Hence #e IN kernel f g h       by preimage_of_image
   (4) x IN kernel f g h ==> #e * x = x
   By kernel property, x IN G.
   Hence #e * x = x               by group_lid
   (5) x IN kernel f g h ==> ?y. y IN kernel f g h /\ (y * x = #e)
   By kernel property, x IN G.
   Also, |/ x IN G                by group_inv_element
   Let y = |/ x, then y * x = #e  by group_linv
   Now f ( |/ x) = h.inv (f x))   by group_homo_inv
                = h.inv (h.id)    by kernel_property
                = h.id            by group_inv_id
   Hence |/ x IN kernel f g h     by preimage_of_image
*)
val kernel_group_group = store_thm(
  "kernel_group_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (kernel_group f g h)``,
  rw_tac std_ss[GroupHomo_def] >>
  rw_tac std_ss[group_def_alt, kernel_group_def] >| [
    `x IN G /\ y IN G` by metis_tac[kernel_property] >>
    `x * y IN G` by rw[] >>
    `f (x * y) = h.id` by metis_tac[kernel_property, group_id_id] >>
    metis_tac[kernel_def, preimage_of_image],
    `x IN G /\ y IN G /\ z IN G` by metis_tac[kernel_property] >>
    rw[group_assoc],
    `#e IN G` by rw[] >>
    `f #e = h.id` by rw_tac std_ss[group_homo_id, GroupHomo_def] >>
    metis_tac[kernel_def, preimage_of_image],
    `x IN G` by metis_tac[kernel_property] >>
    rw[],
    `x IN G` by metis_tac[kernel_property] >>
    qexists_tac `|/ x` >>
    rw[] >>
    `|/x IN G` by rw[] >>
    `f ( |/ x) = h.inv (f x)` by rw_tac std_ss[group_homo_inv, GroupHomo_def] >>
    `_ = h.inv h.id` by metis_tac[kernel_property] >>
    `_ = h.id` by rw[] >>
    metis_tac[kernel_def, preimage_of_image]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) <= g *)
(* Proof: by Subgroup_def.
   (1) Group (kernel_group f g h)
   True by kernel_group_group.
   (2) (kernel_group f g h).carrier SUBSET G
   True by kernel_group_def, kernel_def, preimage_subset.
   (3) x IN (kernel_group f g h).carrier /\ y IN (kernel_group f g h).carrier ==> (kernel_group f g h).op x y = x * y
   True by kernel_group_def.
*)
val kernel_group_subgroup = store_thm(
  "kernel_group_subgroup",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) <= g``,
  rw_tac std_ss[Subgroup_def] >| [
    rw_tac std_ss[kernel_group_group],
    rw[kernel_group_def, kernel_def, preimage_subset],
    full_simp_tac (srw_ss()) [kernel_group_def]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) << g *)
(* Proof: by normal_subgroup_def.
   With kernel_group_subgroup, it needs to show further:
   a IN G /\ z IN kernel f g h ==> a * z * |/ a IN kernel f g h
   By kernel_property, z IN G /\ f z = h.id
   Hence a * z * |/ a IN G              by group_op_element, group_inv_element.
     f (a * z * |/ a)
   = h.op (f (a * z)) f ( |/ a)         by GroupHomo_def
   = h.op (h.op (f a) (f z)) f ( |/ a)  by GroupHomo_def
   = h.op (h.op (f a) h.id) (h.inv f a) by group_homo_inv
   = h.op (f a) (h.inv f a)             by group_rid
   = h.id                               by group_rinv
   Hence a * z * |/ a IN kernel f g h   by preimage_of_image
*)
val kernel_group_normal = store_thm(
  "kernel_group_normal",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (kernel_group f g h) << g``,
  rw_tac std_ss[normal_subgroup_def, kernel_group_subgroup, kernel_group_def] >>
  `z IN G /\ (f z = h.id)` by metis_tac[kernel_property] >>
  `|/ a IN G /\ a * z IN G /\ a * z * |/ a IN G` by rw[] >>
  `f (a * z * |/ a) = h.id` by metis_tac[group_rid, group_rinv, group_homo_inv, GroupHomo_def] >>
  metis_tac[kernel_property, group_div_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (g / (kernel_group f g h)) *)
(* Proof:
   By kernel_group_normal, kernel_group f g h << g.
   By quotient_group_group, Group (g / (kernel_group f g h))
*)
val kernel_quotient_group = store_thm(
  "kernel_quotient_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (g / kernel_group f g h)``,
  rw[kernel_group_normal, quotient_group_group]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image and Kernel.                                             *)
(* ------------------------------------------------------------------------- *)

(* Proved in groupTheory,
- group_homo_group;
> val it = |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> Group (homo_group g f) : thm
- homo_monoid_def;
> val it = |- !g f. homo_group g f = <|carrier := IMAGE f G; op := image_op g f; id := f #e|> : thm
*)

(* Define the homomorphic image of a group via homomorphism. *)
val homo_image_def = Define`
  homo_image f (g:'a group) (h:'b group) =
    <| carrier := IMAGE f G;
            op := h.op;
            id := h.id
     |>
`;

(* Theorem: Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h) *)
(* Proof: by definition.
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
   By IN_IMAGE, there are a IN G with f a = x, and b IN G with f b = y.
   Then h.op x y = h.op (f a) (f b) = f (a * b)                        by GroupHomo_def
   Since a * b IN G  by group_op_element, hence f (a * b) IN IMAGE f G by IN_IMAGE.
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
   By IN_IMAGE, there are a IN G with f a = x, b IN G with f b = y, and c IN G with f c = z.
   Hence x, y, z IN h.carrier      by MonoidHomo_def, thus true by monoid_assoc.
   (3) h.id IN IMAGE f G
   Since #e IN G               by monoid_id_element
   and f #e = h.id             by MonoidHomo_def
   Hence h.id IN IMAGE f G     by IN_IMAGE
   (4) h.op h.id x = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by MonoidHomo_def
   Hence h.op h.id x = x       by monoid_lid
   (5) h.op x h.id = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by MonoidHomo_def
   Hence h.op x h.id = x      by monoid_rid
*)
val homo_image_monoid = store_thm(
  "homo_image_monoid",
  ``!(g:'a monoid) (h:'b monoid). !f. Monoid g /\ Monoid h /\ MonoidHomo f g h ==> Monoid (homo_image f g h)``,
  rw_tac std_ss[MonoidHomo_def] >>
  `!x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[homo_image_def, Monoid_def] >| [
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `a * b IN G` by rw[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    metis_tac[IN_IMAGE],
    `x IN h.carrier` by metis_tac[] >>
    `y IN h.carrier` by metis_tac[] >>
    `z IN h.carrier` by metis_tac[] >>
    rw[monoid_assoc],
    metis_tac[monoid_id_element, IN_IMAGE],
    `x IN h.carrier` by metis_tac[] >>
    rw[],
    `x IN h.carrier` by metis_tac[] >>
    rw[]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h) *)
(* Proof: by definition.
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
   By IN_IMAGE, there are a IN G with f a = x, and b IN G with f b = y.
   Then h.op x y = h.op (f a) (f b) = f (a * b)   by GroupHomo_def
   Since a * b IN G  by group_op_element, hence f (a * b) IN IMAGE f G by IN_IMAGE.
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
   By IN_IMAGE, there are a IN G with f a = x, b IN G with f b = y, and c IN G with f c = z.
   Hence x, y, z IN h.carrier  by GroupHomo_def, thus true by group_assoc.
   (3) h.id IN IMAGE f G
   Since #e IN G               by group_id_element
   and f #e = h.id             by group_homo_id
   Hence h.id IN IMAGE f G     by IN_IMAGE
   (4) h.op h.id x = x
   By IN_IMAGE, there are a IN G with f a = x.
   Hence x IN h.carrier        by GroupHomo_def
   Hence h.op h.id x = x       by group_lid

   Since GroupHomo f g h /\           by given
         f #e = h.id                  by group_homo_id
     ==> MonoidHomo h g h             by GroupHomo_def, MonoidHomo_def
   Hence Monoid (homo_image f g h)    by homo_image_monoid
   With Group_def and other definitions, this is to show:
         x IN IMAGE f G ==> ?y. y IN IMAGE f G /\ (h.op y x = h.id)
   By IN_IMAGE, there is a IN G with f a = x.
   Hence |/ a IN G                    by group_inv_element
   Let y = f ( |/ a), y IN IMAGE f G  by IN_IMAGE
   h.op y x = h.op (f ( |/ a)) (f a)
            = f ( |/a * a)            by GroupHomo_def
            = f #e                    by group_linv
            = h.id                    by group_homo_id
   h.op x y = h.op (f a) (f ( |/ a))
            = f (a * |/a )            by GroupHomo_def
            = f #e                    by group_rinv
            = h.id                    by group_homo_id
*)
val homo_image_group = store_thm(
  "homo_image_group",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> Group (homo_image f g h)``,
  rpt strip_tac >>
  `f #e = h.id` by rw_tac std_ss[group_homo_id] >>
  `MonoidHomo f g h` by prove_tac[GroupHomo_def, MonoidHomo_def] >>
  `Monoid (homo_image f g h)` by rw[homo_image_monoid] >>
  rw_tac std_ss[Group_def, monoid_invertibles_def, homo_image_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  `?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  `|/ a IN G` by rw[] >>
  `( |/ a * a = #e) /\ (a * |/ a = #e)` by rw[] >>
  `f ( |/ a) IN IMAGE f G` by metis_tac[GroupHomo_def, IN_IMAGE] >>
  metis_tac[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> (homo_image f g h) <= h *)
(* Proof: by Subgroup_def.
   (1) Group (homo_image f g h)
   True by homo_image_group.
   (2) (homo_image f g h).carrier SUBSET h.carrier
   (homo_image f g h).carrier = IMAGE f G    by homo_image_def
   For all x IN IMAGE f G, ?a. a IN G /\ (f a = x)   by IN_IMAGE
   Hence x IN h.carrier by GroupHomo_def, hence true by SUBSET_DEF.
   (3) x IN (homo_image f g h).carrier /\ y IN (homo_image f g h).carrier ==> (homo_image f g h).op x y = h.op x y
   True by homo_image_def.
*)
val homo_image_subgroup = store_thm(
  "homo_image_subgroup",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==> (homo_image f g h) <= h``,
  rw_tac std_ss[Subgroup_def] >| [
    rw_tac std_ss[homo_image_group],
    rw[homo_image_def, SUBSET_DEF] >>
    metis_tac[GroupHomo_def],
    rw_tac std_ss[homo_image_def]
  ]);

(* Theorem: Group g /\ Group h /\ SURJ f G h.carrier ==> GroupIso I h (homo_image f g h) *)
(* Proof:
   After expanding by GroupIso_def, GroupHomo_def, and homo_image_def, this is to show:
   (1) x IN h.carrier ==> x IN IMAGE f G
       Note x IN h.carrier ==> ?z. z IN G /\ f z = x    by SURJ_DEF
        and z IN G ==> f z = x IN IMAGE f G             by IN_IMAGE
   (2) x IN IMAGE f G ==> x IN h.carrier
       Note x IN IMAGE f G ==> ?z. z IN G /\ f z = x    by IN_IMAGE
        and z IN G ==> f z = x IN h.carrier             by SURJ_DEF
*)
val group_homo_image_surj_property = store_thm(
  "group_homo_image_surj_property",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\
     SURJ f G h.carrier ==> GroupIso I h (homo_image f g h)``,
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF, GroupIso_def, GroupHomo_def, homo_image_def] >>
  metis_tac[IN_IMAGE]);

(* Theorem: Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h) *)
(* Proof:
   Note MonoidHomo f g h
    ==> !x. x IN G ==> f x IN h.carrier                             by MonoidHomo_def
    and !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))   by MonoidHomo_def
    and f #e = h.id                                                 by MonoidHomo_def
   Also !x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)              by IN_IMAGE

   Expand by homo_image_def, Monoid_def, this is to show:
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> h.op x y IN IMAGE f G
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
        and ?b. b IN G /\ (f b = y)             by y IN IMAGE f G
       also a * b IN G                          by monoid_op_element
        Now h.op x y = f (a * b)                by above
         so h.op x y IN IMAGE f G               by IN_IMAGE
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> h.op (h.op x y) z = h.op x (h.op y z)
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
        and ?b. b IN G /\ (f b = y)             by y IN IMAGE f G
        and ?c. c IN G /\ (f c = z)             by z IN IMAGE f G
        Now h.op (h.op x y) z = f ((a * b) * c) by a * b IN G, and above
        and h.op x (h.op y z) = f (a * (b * c)) by b * c IN G, and above
      Since a * b * c = a * (b * c)             by monoid_assoc
       thus h.op (h.op x y) z = h.op x (h.op y z)
   (3) h.id IN IMAGE f G
       Note h.id = f #e                         by above
        Now #e IN G                             by monoid_id_element
         so h.id IN IMAGE f G                   by IN_IMAGE
   (4) x IN IMAGE f G ==> h.op h.id x = x
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
            h.op h.id x
          = f (#e * a)                          by monoid_id_element, and above
          = f a                                 by monoid_lid
          = x
   (5) x IN IMAGE f G ==> h.op x h.id = x
       Note ?a. a IN G /\ (f a = x)             by x IN IMAGE f G
            h.op x h.id
          = f (a * #e)                          by monoid_id_element, and above
          = f a                                 by monoid_rid
          = x
*)
val monoid_homo_homo_image_monoid = store_thm(
  "monoid_homo_homo_image_monoid",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h ==> Monoid (homo_image f g h)``,
  rw_tac std_ss[MonoidHomo_def] >>
  `!x. x IN IMAGE f G ==> ?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[homo_image_def, Monoid_def] >| [
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `a * b IN G` by rw[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    metis_tac[IN_IMAGE],
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `?b. b IN G /\ (f b = y)` by rw_tac std_ss[] >>
    `?c. c IN G /\ (f c = z)` by rw_tac std_ss[] >>
    `h.op x y = f (a * b)` by rw_tac std_ss[] >>
    `h.op y z = f (b * c)` by rw_tac std_ss[] >>
    `a * b IN G /\ b * c IN G` by rw[] >>
    `h.op (h.op x y) z = f ((a * b) * c)` by metis_tac[] >>
    `h.op x (h.op y z) = f (a * (b * c))` by metis_tac[] >>
    `a * b * c = a * (b * c)` by rw[monoid_assoc] >>
    metis_tac[],
    metis_tac[monoid_id_element, IN_IMAGE],
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `h.op h.id x = f (#e * a)` by rw_tac std_ss[monoid_id_element] >>
    metis_tac[monoid_lid],
    `x IN h.carrier` by metis_tac[] >>
    `?a. a IN G /\ (f a = x)` by rw_tac std_ss[] >>
    `h.op x h.id = f (a * #e)` by rw_tac std_ss[monoid_id_element] >>
    metis_tac[monoid_rid]
  ]);

(*
GroupHomo_def is weaker than MonoidHomo_def.
May need to define  GroupHomo = MonoidHomo, making f #e = h.id mandatory.
Better keep GroupHomo, just use MonoidHomo if necessary.
*)

(* Theorem: Group g /\ MonoidHomo f g h ==> Group (homo_image f g h) *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (homo_image f g h), true   by monoid_homo_homo_image_monoid
   (2) monoid_invertibles (homo_image f g h) = (homo_image f g h).carrier
       By monoid_invertibles_def, homo_image_def, this is to show:
       x IN IMAGE f G ==> ?y. y IN IMAGE f G /\ (h.op x y = h.id) /\ (h.op y x = h.id)

       Note ?a. a IN G /\ (f a = x)      by x IN IMAGE f G
      Hence |/ a IN G                    by group_inv_element
        Let y = f ( |/ a).
       Then y IN IMAGE f G               by IN_IMAGE
            h.op y x
          = h.op (f ( |/ a)) (f a)
          = f ( |/a * a)                 by MonoidHomo_def
          = f #e                         by group_linv
          = h.id                         by MonoidHomo_def
            h.op x y
          = h.op (f a) (f ( |/ a))
          = f (a * |/a )                 by MonoidHomo_def
          = f #e                         by group_rinv
          = h.id                         by MonoidHomo_def
*)
val group_homo_homo_image_group = store_thm(
  "group_homo_homo_image_group",
  ``!(g:'a group) (h:'b group) f. Group g /\ MonoidHomo f g h ==> Group (homo_image f g h)``,
  rpt strip_tac >>
  `Monoid (homo_image f g h)` by rw[monoid_homo_homo_image_monoid] >>
  rw_tac std_ss[Group_def, monoid_invertibles_def, homo_image_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  `?a. a IN G /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  `|/ a IN G` by rw[] >>
  `( |/ a * a = #e) /\ (a * |/ a = #e)` by rw[] >>
  `f ( |/ a) IN IMAGE f G` by metis_tac[IN_IMAGE] >>
  metis_tac[MonoidHomo_def]);

(* ------------------------------------------------------------------------- *)
(* First Isomorphic Theorem for Group.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==>
            GroupHomo (\z. (CHOICE (preimage f G z)) * (kernel f g h) ) (homo_image f g h) (g / (kernel_group f g h)) *)
(* Proof: by GroupHomo_def, homo_image_def and quotient_group_def.
   This is to show:
   (1) !z. z IN IMAGE f G ==> CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   Since (kernel_group f g h) <= g  by kernel_group_subgroup
   Hence CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h) by coset_partition_element
   and
   (2) !z. z IN IMAGE f G /\ z' IN IMAGE f G ==>
   CHOICE (preimage f G (h.op z z')) * kernel f g h =
   coset_op g (kernel_group f g h) (CHOICE (preimage f G z) * kernel f g h) (CHOICE (preimage f G z') * kernel f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   After expanding by coset_op_def, this is to show:
   CHOICE (preimage f G (h.op z z')) * kernel f g h =
   cogen g (kernel_group f g h) (CHOICE (preimage f G z) * kernel f g h) *
   cogen g (kernel_group f g h) (CHOICE (preimage f G z') * kernel f g h) * kernel f g h
   Now, (kernel_group f g h) << g    by kernel_group_normal
   Let x = CHOICE (preimage f G z
       x' = CHOICE (preimage f G z'
       y = CHOICE (preimage f G (h.op z z'))
       k = kernel_group f g h
       s = kernel f g h
   This is to show: y * s = cogen g k (x * s) * cogen g k (x' * s) * s
   This can be done via normal_coset_property, but first:
   x IN G /\ x' IN G /\ (f x = z) /\ (f x' = z')   by preimage_choice_property
   x * s IN CosetPartition g k    by coset_partition_element
   x' * s IN CosetPartition g k   by coset_partition_element
   Hence
   cogen g k (x * s) * cogen g k (x' * s) * s = x * x' * s  by normal_coset_property
   It remains to show: y * s = x * x' * s
   i.e. to show: y / (x * x') IN s   since k << g  if we know y IN G and x * x' IN G
   But h.op z z' = f (x * x')    by GroupHomo_def
   Hence x * x' IN G /\ f (x * x') IN IMAGE f G   by group_op_element, IN_IMAGE
   and f y = h.op z z' = f (x * x') by preimage_choice_property
   Hence we just need to show: y / (x * x') IN s  where s = kernel f g h
   An element is in kernel if it maps to h.id, so compute:
     f (y / (x * x'))
   = f (y * |/ (x * x'))          by group_div_def
   = h.op (f y) f ( |/ (x * x'))   by GroupHomo_def
   = h.op (f y) h.inv f (x * x')  by group_homo_inv
   = h.op (f y) h.inv (f y)       by above
   = h.id                         by group_rinv
*)
val homo_image_homo_quotient_kernel = store_thm(
  "homo_image_homo_quotient_kernel",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            GroupHomo (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h) (g / (kernel_group f g h))``,
  rw_tac std_ss[homo_image_def, quotient_group_def] >>
  `(kernel_group f g h).carrier = kernel f g h` by rw_tac std_ss[kernel_group_def] >>
  rw_tac std_ss[GroupHomo_def] >| [
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    rw_tac std_ss[coset_op_def] >>
    `(kernel_group f g h) << g /\ (kernel_group f g h) <= g` by rw_tac std_ss[kernel_group_normal, normal_subgroup_subgroup] >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `x' = CHOICE (preimage f G z')` >>
    qabbrev_tac `y = CHOICE (preimage f G (h.op z z'))` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `x IN G /\ x' IN G /\ (f x = z) /\ (f x' = z')` by rw_tac std_ss[preimage_choice_property, Abbr`x`, Abbr`x'`] >>
    `x * s IN CosetPartition g k /\ x' * s IN CosetPartition g k` by metis_tac[coset_partition_element] >>
    `cogen g k (x * s) * cogen g k (x' * s) * s = x * x' * s` by rw_tac std_ss[normal_coset_property] >>
    full_simp_tac std_ss [] >>
    `h.op z z' = f (x * x')` by metis_tac[GroupHomo_def] >>
    `x * x' IN G /\ f (x * x') IN IMAGE f G` by rw[] >>
    `y IN G /\ (f y = h.op z z')` by metis_tac[preimage_choice_property] >>
    `y / (x * x') IN s` suffices_by rw_tac std_ss[normal_subgroup_coset_eq] >>
    `|/ (x * x') IN G` by rw[] >>
    `f y IN h.carrier` by metis_tac[GroupHomo_def] >>
    `f (y / (x * x')) = f (y * |/ (x * x'))` by rw_tac std_ss[group_div_def] >>
    `_ = h.op (f y) (f ( |/ (x * x')))` by metis_tac[GroupHomo_def] >>
    `_ = h.op (f y) (h.inv (h.op z z'))` by metis_tac[group_homo_inv] >>
    `_ = h.id` by metis_tac[group_rinv] >>
    metis_tac[kernel_property, group_div_element]
  ]);

(* Theorem:  BIJ (\z. CHOICE (preimage f G z) * kernel f g h)
             (homo_image f g h).carrier (g / kernel_group f g h).carrier *)
(* Proof:
   This is to prove:
   (1) z IN IMAGE f G ==> CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h)
   z IN IMAGE f G ==> CHOICE (preimage f G z) IN G   by preimage_choice_property
   Since (kernel_group f g h) <= g  by kernel_group_subgroup
   Hence CHOICE (preimage f G z) * kernel f g h IN CosetPartition g (kernel_group f g h) by coset_partition_element
   (2) z IN IMAGE f G /\ z' IN IMAGE f G /\ CHOICE (preimage f G z) * kernel f g h = CHOICE (preimage f G z') * kernel f g h ==> z = z'
   Let x = CHOICE (preimage f G z)
       x' = CHOICE (preimage f G z'), then
   z IN IMAGE f G ==> x IN G /\ f x = z  by preimage_choice_property
   z' IN IMAGE f G ==> x' IN G /\ f x' = z'  by preimage_choice_property
   x IN G ==> z = f x IN H, x' IN G ==> z' = f x' IN H   by GroupHomo_def
   Given  x * kernel f g h = x' * kernel f g h
   Since (kernel_group f g h) << g      by kernel_group_normal
   this gives  x / x' IN kernel f g h   by normal_subgroup_coset_eq
   Hence    f (x / x') = h.id           by kernel_property
   i.e. h.id = f (x / x')
             = f (x * |/ x')            by group_div_def
             = h.op (f x) (f ( |/ x'))   by GroupHomo_def
             = h.op (f x) h.inv (f x')  by group_homo_inv
             = h.op z h.inv z'          by above
   Hence z = z'  by group_linv_unique, group_inv_inv
   (3) same as (1).
   (4) x IN CosetPartition g (kernel_group f g h) ==> ?z. z IN IMAGE f G /\ (CHOICE (preimage f G z) * kernel f g h = x)
   Note (kernel_group f g h) << g          by kernel_group_normal
   and (kernel_group f g h) <= g           by normal_subgroup_subgroup
   Since x IN CosetPartition g (kernel_group f g h),
   ?a. a IN G /\ (x = a * kernel f g h)    by coset_partition_element
   Let z = f a, then z IN IMAGE f G    by IN_IMAGE,
   and CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)  by preimage_choice_property
   Thus, this is to prove:
   CHOICE (preimage f G z) * kernel f g h = x = a * kernel f g h
   Since kernel f g h << g, this is true if  CHOICE (preimage f G z) / a IN kernel f g h
   or need to show: f (CHOICE (preimage f G z) / a) = h.id  by normal_subgroup_coset_eq
   By computation,
     f (CHOICE (preimage f G z) / a)
   = f (CHOICE (preimage f G z) * |/ a)             by group_div_def
   = h.op (f (CHOICE (preimage f G z)) (f ( |/ a))   by GroupHomo_def
   = h.op z (h.inv z)                               by group_homo_inv
   = h.id                                           by group_linv
*)
val homo_image_to_quotient_kernel_bij = store_thm(
  "homo_image_to_quotient_kernel_bij",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            BIJ (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h).carrier (g / (kernel_group f g h)).carrier``,
  rw_tac std_ss[homo_image_def, quotient_group_def] >>
  `(kernel_group f g h).carrier = kernel f g h` by rw_tac std_ss[kernel_group_def] >>
  rw_tac std_ss[BIJ_DEF, SURJ_DEF, INJ_DEF] >| [
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    `CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)` by rw_tac std_ss[preimage_choice_property] >>
    `CHOICE (preimage f G z') IN G /\ (f (CHOICE (preimage f G z')) = z')` by rw_tac std_ss[preimage_choice_property] >>
    `(kernel_group f g h) << g` by rw_tac std_ss[kernel_group_normal] >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `x' = CHOICE (preimage f G z')` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `|/ x' IN G` by rw[] >>
    `f ( |/ x') = h.inv z'` by rw_tac std_ss[group_homo_inv] >>
    `z IN h.carrier /\ z' IN h.carrier /\ h.inv z' IN h.carrier` by metis_tac[GroupHomo_def] >>
    `x / x' IN s` by metis_tac[normal_subgroup_coset_eq] >>
    `h.id = f (x / x')` by metis_tac[kernel_property] >>
    `_ = f (x * |/ x')` by rw_tac std_ss[group_div_def] >>
    `_ = h.op (f x) (h.inv (f x'))` by metis_tac[GroupHomo_def] >>
    metis_tac[group_linv_unique, group_inv_inv],
    metis_tac[preimage_choice_property, kernel_group_subgroup, coset_partition_element],
    `(kernel_group f g h) << g /\ (kernel_group f g h) <= g` by rw_tac std_ss[kernel_group_normal, normal_subgroup_subgroup] >>
    `?a. a IN G /\ (x = a * kernel f g h)` by metis_tac[coset_partition_element] >>
    qexists_tac `f a` >>
    rw[] >>
    qabbrev_tac `z = f a` >>
    qabbrev_tac `x = CHOICE (preimage f G z)` >>
    qabbrev_tac `k = kernel_group f g h` >>
    qabbrev_tac `s = kernel f g h` >>
    `x IN G /\ (f x = z) /\ z IN h.carrier` by metis_tac[preimage_choice_property, IN_IMAGE, GroupHomo_def] >>
    `x / a IN s` suffices_by metis_tac[normal_subgroup_coset_eq] >>
    `|/a IN G` by rw[] >>
    `f (x * |/ a) = h.op (f x) (f ( |/ a))` by metis_tac[GroupHomo_def] >>
    `_ = h.op z (h.inv z)` by metis_tac[group_homo_inv] >>
    `_ = h.id` by metis_tac[group_rinv] >>
    metis_tac[kernel_property, group_div_def, group_div_element]
  ]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==>
            GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) ) (homo_image f g h) (g / (kernel_group f g h)) *)
(* Proof: by GroupIso_def.
   (1) GroupHomo (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h) (g / kernel_group f g h)
   True by homo_image_homo_quotient_kernel.
   (2) BIJ (\z. CHOICE (preimage f G z) * kernel f g h) (homo_image f g h).carrier (g / kernel_group f g h).carrier
   True by homo_image_to_quotient_kernel_bij.
*)
val homo_image_iso_quotient_kernel = store_thm(
  "homo_image_iso_quotient_kernel",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
            GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                     (homo_image f g h) (g / (kernel_group f g h))``,
  rw[GroupIso_def, homo_image_homo_quotient_kernel, homo_image_to_quotient_kernel_bij]);

(* Theorem [First Isomorphism Theorem for Groups]
   Let G and H be groups, and let f: G -> H be a homomorphism. Then:
   (a) The kernel of f is a normal subgroup of G,
   (b) The image of f is a subgroup of H, and
   (c) The image of f is isomorphic to the quotient group G / ker(f).
   In particular, (d) if f is surjective then H is isomorphic to G / ker(f).
*)
(* Proof:
   (a) by kernel_group_normal
   (b) by homo_image_subgroup
   (c) by homo_image_iso_quotient_kernel
   (d) by group_homo_image_surj_property
*)
val group_first_isomorphism_thm = store_thm(
  "group_first_isomorphism_thm",
  ``!(g:'a group) (h:'b group). !f. Group g /\ Group h /\ GroupHomo f g h ==>
      (kernel_group f g h) << g /\
      (homo_image f g h) <= h /\
      GroupIso (\z. (CHOICE (preimage f G z)) * (kernel f g h) )
                    (homo_image f g h) (g / (kernel_group f g h)) /\
      (SURJ f G h.carrier ==> GroupIso I h (homo_image f g h))``,
  rw[kernel_group_normal, homo_image_subgroup, homo_image_iso_quotient_kernel, group_homo_image_surj_property]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
