(* ------------------------------------------------------------------------- *)
(* Group Maps                                                                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupMap";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory gcdsetTheory numberTheory combinatoricsTheory;

open monoidTheory;

(* val _ = load "groupTheory"; *)
open groupTheory;

(* ------------------------------------------------------------------------- *)
(* Group Maps Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   homo_group g f   = homo_monoid g f
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups:
   GroupHomo_def   |- !f g h. GroupHomo f g h <=> (!x. x IN G ==> f x IN h.carrier) /\
                                                   !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   GroupIso_def    |- !f g h. GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
   GroupEndo_def   |- !f g. GroupEndo f g <=> GroupHomo f g g
   GroupAuto_def   |- !f g. GroupAuto f g <=> GroupIso f g g
   subgroup_def    |- !h g. subgroup h g <=> GroupHomo I h g

   Group Homomorphisms:
   group_homo_id       |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)
   group_homo_element  |- !f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier
   group_homo_inv      |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/ x) = h.inv (f x))
   group_homo_cong     |- !g h. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
                                (GroupHomo f1 g h <=> GroupHomo f2 g h)
   group_homo_I_refl   |- !g. GroupHomo I g g
   group_homo_trans    |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_sym      |- !g h f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
   group_homo_compose  |- !g h k f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
   group_homo_is_monoid_homo
                       |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h
   group_homo_monoid_homo
                       |- !f g h. GroupHomo f g h /\ f #e = h.id <=> MonoidHomo f g h
   group_homo_exp      |- !g h f. Group g /\ Group h /\ GroupHomo f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n

   Group Isomorphisms:
   group_iso_property  |- !f g h. GroupIso f g h <=>
                                  GroupHomo f g h /\ !y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)
   group_iso_id        |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
   group_iso_element   |- !f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier
   group_iso_I_refl    |- !g. GroupIso I g g
   group_iso_trans     |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_sym       |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_compose   |- !g h k f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k
   group_iso_is_monoid_iso
                       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h
   group_iso_monoid_iso|- !f g h. GroupIso f g h /\ f #e = h.id <=> MonoidIso f g h
   group_iso_exp       |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n
   group_iso_order     |- !g h f. Group g /\ Group h /\ GroupIso f g h ==>
                          !x. x IN G ==> (order h (f x) = ord x)
   group_iso_linv_iso  |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g
   group_iso_bij       |- !g h f. GroupIso f g h ==> BIJ f G h.carrier
   group_iso_group     |- !g h f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h
   group_iso_card_eq   |- !g h f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)

   Group Automorphisms:
   group_auto_id       |- !f g. Group g /\ GroupAuto f g ==> (f #e = #e)
   group_auto_element  |- !f g. GroupAuto f g ==> !x. x IN G ==> f x IN G
   group_auto_compose  |- !g f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g
   group_auto_is_monoid_auto
                       |- !g f. Group g /\ GroupAuto f g ==> MonoidAuto f g
   group_auto_exp      |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> !n. f (x ** n) = f x ** n
   group_auto_order    |- !g f. Group g /\ GroupAuto f g ==>
                          !x. x IN G ==> (ord (f x) = ord x)
   group_auto_I        |- !g. GroupAuto I g
   group_auto_linv_auto|- !g f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g
   group_auto_bij      |- !g f. GroupAuto f g ==> f PERMUTES G

   Subgroups:
   subgroup_eqn             |- !g h. subgroup h g <=> H SUBSET G /\
                               !x y. x IN H /\ y IN H ==> (h.op x y = x * y)
   subgroup_subset          |- !g h. subgroup h g ==> H SUBSET G
   subgroup_homo_homo       |- !g h k f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k
   subgroup_reflexive       |- !g. subgroup g g
   subgroup_transitive      |- !g h k. subgroup g h /\ subgroup h k ==> subgroup g k
   subgroup_I_antisym       |- !g h. subgroup h g /\ subgroup g h ==> GroupIso I h g
   subgroup_carrier_antisym |- !g h. subgroup h g /\ G SUBSET H ==> GroupIso I h g
   subgroup_is_submoniod    |- !g h. Group g /\ Group h /\ subgroup h g ==> submonoid h g
   subgroup_order_eqn       |- !g h. Group g /\ Group h /\ subgroup h g ==>
                               !x. x IN H ==> (order h x = ord x)

   Homomorphic Image of a Group:
   homo_group_closure |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> x o y IN fG
   homo_group_assoc   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o y o z)
   homo_group_id      |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\
                         !x. x IN fG ==> (#i o x = x) /\ (x o #i = x)
   homo_group_inv     |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==>
                         !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)
   homo_group_group   |- !g f. Group g /\ GroupHomo f g (homo_group g f) ==> Group (homo_group g f)
   homo_group_comm    |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                         !x y. x IN fG /\ y IN fG ==> (x o y = y o x)
   homo_group_abelian_group  |- !g f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
                                      AbelianGroup (homo_group g f)
   homo_group_by_inj         |- !g f. Group g /\ INJ f G univ(:'b) ==> GroupHomo f g (homo_group g f)

   Injective Image of Group:
   group_inj_image_group           |- !g f. Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
   group_inj_image_abelian_group   |- !g f. AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f)
   group_inj_image_excluding_group
                               |- !g f e. Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          Group (monoid_inj_image g f excluding f e)
   group_inj_image_excluding_abelian_group
                               |- !g f e. AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
                                          AbelianGroup (monoid_inj_image g f excluding f e)
   group_inj_image_group_homo  |- !g f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subgroups.  *)
(* ------------------------------------------------------------------------- *)

(* A function f from g to h is a homomorphism if group properties are preserved. *)
(* For group, no need to ensure that identity is preserved, see group_homo_id.   *)

val GroupHomo_def = Define`
  GroupHomo (f:'a -> 'b) (g:'a group) (h:'b group) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)))
    (* no requirement for: f #e = h.id *)
`;

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val GroupIso_def = Define`
  GroupIso f g h <=> GroupHomo f g h /\ BIJ f G h.carrier
`;

(* A group homomorphism from g to g is an endomorphism. *)
val GroupEndo_def = Define `GroupEndo f g <=> GroupHomo f g g`;

(* A group isomorphism from g to g is an automorphism. *)
val GroupAuto_def = Define `GroupAuto f g <=> GroupIso f g g`;

(* A subgroup h of g if identity is a homomorphism from h to g *)
val subgroup_def = Define `subgroup h g <=> GroupHomo I h g`;

(* ------------------------------------------------------------------------- *)
(* Group Homomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id *)
(* Proof:
   Since #e IN G                     by group_id_element,
   f (#e * #e) = h.op (f #e) (f #e)  by GroupHomo_def
   f #e = h.op (f #e) (f #e)         by group_id_id
   ==> f #e = h.id                   by group_id_fix
*)
val group_homo_id = store_thm(
  "group_homo_id",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id)``,
  rw_tac std_ss[GroupHomo_def] >>
  `#e IN G` by rw[] >>
  metis_tac[group_id_fix, group_id_id]);

(* Theorem: GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupHomo_def *)
val group_homo_element = store_thm(
  "group_homo_element",
  ``!f g h. GroupHomo f g h ==> !x. x IN G ==> f x IN h.carrier``,
  rw_tac std_ss[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> f ( |/x) = h.inv (f x) *)
(* Proof:
   Since |/x IN G                      by group_inv_element
   f ( |/x * x) = h.op (f |/x) (f x)   by GroupHomo_def
   f (#e) = h.op (f |/x) (f x)         by group_linv
     h.id = h.op (f |/x) (f x)         by group_homo_id
   ==> f |/x = h.inv (f x)             by group_linv_unique
*)
val group_homo_inv = store_thm(
  "group_homo_inv",
  ``!f g h. Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> (f ( |/x) = h.inv (f x))``,
  rpt strip_tac >>
  `|/x IN G` by rw_tac std_ss[group_inv_element] >>
  `f x IN h.carrier /\ f ( |/x) IN h.carrier` by metis_tac[GroupHomo_def] >>
  `h.op (f ( |/x)) (f x) = f ( |/x * x)` by metis_tac[GroupHomo_def] >>
  metis_tac[group_linv_unique, group_homo_id, group_linv]);

(* Theorem: Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==> (GroupHomo f1 g h = GroupHomo f2 g h) *)
(* Proof: by GroupHomo_def, group_op_element *)
val group_homo_cong = store_thm(
  "group_homo_cong",
  ``!(g:'a group) (h:'b group) f1 f2. Group g /\ Group h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
          (GroupHomo f1 g h = GroupHomo f2 g h)``,
  rw_tac std_ss[GroupHomo_def, EQ_IMP_THM] >-
  metis_tac[group_op_element] >>
  metis_tac[group_op_element]);

(* Theorem: GroupHomo I g g *)
(* Proof: by GroupHomo_def. *)
val group_homo_I_refl = store_thm(
  "group_homo_I_refl",
  ``!g:'a group. GroupHomo I g g``,
  rw[GroupHomo_def]);

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo f2 o f1 g k *)
(* Proof: true by GroupHomo_def. *)
val group_homo_trans = store_thm(
  "group_homo_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw[GroupHomo_def]);

(* Theorem: Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g *)
(* Proof:
   Note BIJ f G h.carrier
    ==> BIJ (LINV f G) h.carrier G     by BIJ_LINV_BIJ
   By GroupHomo_def, this is to show:
   (1) x IN h.carrier ==> LINV f G x IN G
       With BIJ (LINV f G) h.carrier G
        ==> INJ (LINV f G) h.carrier G           by BIJ_DEF
        ==> x IN h.carrier ==> LINV f G x IN G   by INJ_DEF
   (2) x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       With x IN h.carrier
        ==> ?x1. (x = f x1) /\ x1 IN G           by BIJ_DEF, SURJ_DEF
       With y IN h.carrier
        ==> ?y1. (y = f y1) /\ y1 IN G           by BIJ_DEF, SURJ_DEF
        and x1 * y1 IN G                         by group_op_element
            LINV f G (h.op x y)
          = LINV f G (f (x1 * y1))                  by GroupHomo_def
          = x1 * y1                                 by BIJ_LINV_THM, x1 * y1 IN G
          = (LINV f G (f x1)) * (LINV f G (f y1))   by BIJ_LINV_THM, x1 IN G, y1 IN G
          = (LINV f G x) * (LINV f G y)             by x = f x1, y = f y1.
*)
val group_homo_sym = store_thm(
  "group_homo_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g``,
  rpt strip_tac >>
  `BIJ (LINV f G) h.carrier G` by rw[BIJ_LINV_BIJ] >>
  fs[GroupHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >>
  `?x1. (x = f x1) /\ x1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `?y1. (y = f y1) /\ y1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `g.op x1 y1 IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]);

Theorem group_homo_sym_any:
  Group g /\ GroupHomo f g h /\
  (!x. x IN h.carrier ==> i x IN g.carrier /\ f (i x) = x) /\
  (!x. x IN g.carrier ==> i (f x) = x)
  ==>
  GroupHomo i h g
Proof
  rpt strip_tac \\ fs[GroupHomo_def]
  \\ rpt strip_tac
  \\ `h.op x y = f (g.op (i x) (i y))` by metis_tac[]
  \\ pop_assum SUBST1_TAC
  \\ first_assum irule
  \\ PROVE_TAC[group_def_alt]
QED

(* Theorem: GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k *)
(* Proof: by GroupHomo_def *)
val group_homo_compose = store_thm(
  "group_homo_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k``,
  rw_tac std_ss[GroupHomo_def]);
(* This is the same as group_homo_trans. *)

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h *)
(* Proof:
   By MonoidHomo_def, this is to show:
   (1) x IN G ==> f x IN h.carrier, true                           by GroupHomo_def
   (2) x IN G /\ y IN G ==> f (x * y) = h.op (f x) (f y), true     by GroupHomo_def
   (3) Group g /\ Group h /\ GroupHomo f g h ==> f #e = h.id, true by group_homo_id
*)
val group_homo_is_monoid_homo = store_thm(
  "group_homo_is_monoid_homo",
  ``!g:'a group h f. Group g /\ Group h /\ GroupHomo f g h ==> MonoidHomo f g h``,
  rw[MonoidHomo_def] >-
  fs[GroupHomo_def] >-
  fs[GroupHomo_def] >>
  fs[group_homo_id]);

(* Theorem: (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h *)
(* Proof: by MonoidHomo_def, GroupHomo_def. *)
Theorem group_homo_monoid_homo:
  !f g h. (GroupHomo f g h /\ f #e = h.id) <=> MonoidHomo f g h
Proof
  simp[MonoidHomo_def, GroupHomo_def] >>
  rw[EQ_IMP_THM]
QED

(* Theorem: Group g /\ Group h /\ GroupHomo f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidHomo f g h   by group_homo_is_monoid_homo
    The result follows     by monoid_homo_exp
*)
val group_homo_exp = store_thm(
  "group_homo_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupHomo f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_homo_is_monoid_homo, monoid_homo_exp]);

(* ------------------------------------------------------------------------- *)
(* Group Isomorphisms                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GroupIso f g h <=> GroupIHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) BIJ f G H /\ y IN H ==> ?!x. x IN G /\ (f x = y)
       true by INJ_DEF and SURJ_DEF.
   (2) !y. y IN H /\ GroupHomo f g h ==> ?!x. x IN G /\ (f x = y) ==> BIJ f G H
       true by INJ_DEF and SURJ_DEF, and
       x IN G /\ GroupHomo f g h ==> f x IN H  by GroupHomo_def
*)
val group_iso_property = store_thm(
  "group_iso_property",
  ``!f g h. GroupIso f g h <=> GroupHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y))``,
  rw[GroupIso_def, EQ_IMP_THM] >-
  metis_tac[BIJ_THM] >>
  rw[BIJ_THM] >>
  metis_tac[GroupHomo_def]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> f #e = h.id *)
(* Proof:
   Since Group g, Group h ==> Monoid g, Monoid h   by group_is_monoid
   and GroupIso = WeakIso, GroupHomo = WeakHomo,
   this follows by monoid_iso_id.
*)
val group_iso_id = store_thm(
  "group_iso_id",
  ``!f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)``,
  rw[monoid_weak_iso_id, group_is_monoid, GroupIso_def, GroupHomo_def, WeakIso_def, WeakHomo_def]);
(* However,
   this result is worse than (proved earlier):
- group_homo_id;
> val it = |- !f g h. Group g /\ Group h /\ GroupHomo f g h ==> (f #e = h.id) : thm
*)

(* Theorem: GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by GroupIso_def, group_homo_element *)
val group_iso_element = store_thm(
  "group_iso_element",
  ``!f g h. GroupIso f g h ==> !x. x IN G ==> f x IN h.carrier``,
  metis_tac[GroupIso_def, group_homo_element]);

(* Theorem: GroupIso I g g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo I g g, true by group_homo_I_refl
   (2) BIJ I R R, true by BIJ_I_SAME
*)
val group_iso_I_refl = store_thm(
  "group_iso_I_refl",
  ``!g:'a group. GroupIso I g g``,
  rw[GroupIso_def, group_homo_I_refl, BIJ_I_SAME]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g
       True by group_homo_trans.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE.
*)
val group_iso_trans = store_thm(
  "group_iso_trans",
  ``!(g:'a group) (h:'b group) (k:'c group).
    !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw[GroupIso_def] >-
  metis_tac[group_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Group g ==> !f. GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f g h /\ BIJ f G h.carrier ==> GroupHomo (LINV f G) h g
       True by group_homo_sym.
   (2) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_sym = store_thm(
  "group_iso_sym",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw[GroupIso_def, group_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k *)
(* Proof:
   By GroupIso_def, this is to show:
   (1) GroupHomo f1 g h /\ GroupHomo f2 h k ==> GroupHomo (f2 o f1) g k
       True by group_homo_compose.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE
*)
val group_iso_compose = store_thm(
  "group_iso_compose",
  ``!(g:'a group) (h:'b group) (k:'c group).
   !f1 f2. GroupIso f1 g h /\ GroupIso f2 h k ==> GroupIso (f2 o f1) g k``,
  rw_tac std_ss[GroupIso_def] >-
  metis_tac[group_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as group_iso_trans. *)

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h *)
(* Proof: by GroupIso_def, MonoidIso_def, group_homo_is_monoid_homo *)
val group_iso_is_monoid_iso = store_thm(
  "group_iso_is_monoid_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==> MonoidIso f g h``,
  rw[GroupIso_def, MonoidIso_def] >>
  rw[group_homo_is_monoid_homo]);

(* Theorem: (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h *)
(* Proof:
       MonioidIso f g h
   <=> MonoidHomo f g h /\ BIJ f G h.carrier                 by MonoidIso_def
   <=> GroupHomo f g h /\ f #e = h.id /\ BIJ f G h.carrier   by group_homo_monoid_homo
   <=> GroupIso f g h /\ f #e = h.id                         by GroupIso_def
*)
Theorem group_iso_monoid_iso:
  !f g h. (GroupIso f g h /\ f #e = h.id) <=> MonoidIso f g h
Proof
  simp[MonoidIso_def, GroupIso_def] >>
  metis_tac[group_homo_monoid_homo]
QED

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidIso f g h    by group_iso_is_monoid_iso
    The result follows     by monoid_iso_exp
*)
val group_iso_exp = store_thm(
  "group_iso_exp",
  ``!g:'a group h:'b group f. Group g /\ Group h /\ GroupIso f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_exp]);

(* Theorem: Group g /\ Group h /\ GroupIso f g h ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                    by group_is_monoid
    and MonoidIso f h g                         by group_iso_is_monoid_iso
   Thus !x. x IN H ==> (order h (f x) = ord x)  by monoid_iso_order
*)
val group_iso_order = store_thm(
  "group_iso_order",
  ``!(g:'a group) (h:'b group) f. Group g /\ Group h /\ GroupIso f g h ==>
    !x. x IN G ==> (order h (f x) = ord x)``,
  rw[group_is_monoid, group_iso_is_monoid_iso, monoid_iso_order]);

(* Theorem: Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g *)
(* Proof:
   By GroupIso_def, GroupHomo_def, this is to show:
   (1) BIJ f G h.carrier /\ x IN h.carrier ==> LINV f G x IN G
       True by BIJ_LINV_ELEMENT
   (2) BIJ f G h.carrier /\ x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       Let x' = LINV f G x, y' = LINV f G y.
       Then x' IN G /\ y' IN G        by BIJ_LINV_ELEMENT
         so x' * y' IN G              by group_op_element
        ==> f (x' * y') = h.op (f x') (f y')    by GroupHomo_def
                        = h.op x y              by BIJ_LINV_THM
       Thus LINV f G (h.op x y)
          = LINV f G (f (x' * y'))    by above
          = x' * y'                   by BIJ_LINV_THM
   (3) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val group_iso_linv_iso = store_thm(
  "group_iso_linv_iso",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h ==> GroupIso (LINV f G) h g``,
  rw_tac std_ss[GroupIso_def, GroupHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
 (qabbrev_tac `x' = LINV f G x` >>
  qabbrev_tac `y' = LINV f G y` >>
  metis_tac[BIJ_LINV_THM, BIJ_LINV_ELEMENT, group_op_element]) >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as group_iso_sym. *)

(* Theorem: GroupIso f g h ==> BIJ f G h.carrier *)
(* Proof: by GroupIso_def *)
val group_iso_bij = store_thm(
  "group_iso_bij",
  ``!(g:'a group) (h:'b group) f. GroupIso f g h ==> BIJ f G h.carrier``,
  rw_tac std_ss[GroupIso_def]);

(* Note: read the discussion in group_iso_id for the condition: f #e = h.id:
   group_iso_id  |- !f g h. Group g /\ Group h /\ GroupIso f g h ==> (f #e = h.id)
*)
(* Theorem: Group g /\ GroupIso f g h /\ f #e = h.id ==> Group h  *)
(* Proof:
   This is to show:
   (1) x IN h.carrier /\ y IN h.carrier ==> h.op x y IN h.carrier
       Group g ==> Monoid g               by group_is_monoid
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             h.op x y = f (x' * y')       by GroupHomo_def
       As                  x' * y' IN G   by group_op_element
       hence f (x' * y') IN h.carrier     by GroupHomo_def
   (2) x IN h.carrier /\ y IN h.carrier /\ z IN h.carrier ==> h.op (h.op x y) z = h.op x (h.op y z)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
             ?y'. y' IN G /\ (f y' = y)   by group_iso_property
             ?z'. z' IN G /\ (f z' = z)   by group_iso_property
       as     x' * y' IN G                by group_op_element
       and f (x' * y') IN h.carrier       by GroupHomo_def
       ?!t. t IN G /\ f t = f (x' * y')   by group_iso_property
       i.e.  t = x' * y'                  by uniqueness
       hence h.op (h.op x y) z = f (x' * y' * z')
                                          by GroupHomo_def
       Similary,
       as     y' * z' IN G                by group_op_element
       and f (y' * z') IN h.carrier       by GroupHomo_def
       ?!s. s IN G /\ f s = f (y' * z')   by group_iso_property
       i.e.  s = y' * z'                  by uniqueness
       and   h.op x (h.op y z) = f (x' * (y' * z'))
                                          by GroupHomo_def
       hence true                         by group_assoc.
   (3) h.id IN h.carrier
       Since #e IN G                      by group_id_element
            (f #e) = h.id IN h.carrier    by GroupHomo_def
   (4) x IN h.carrier ==> h.op h.id x = x
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       h.id IN h.carrier                  by group_id_element
       ?!e. e IN G /\ f e = h.id = f #e   by group_iso_property
       i.e. e = #e                        by uniqueness
       hence h.op h.id x = f (e * x')     by GroupHomo_def
                         = f (#e * x')
                         = f x'           by group_lid
                         = x
   (5) x IN h.carrier ==> ?y. y IN h.carrier /\ (h.op y x = h.id)
       Since ?x'. x' IN G /\ (f x' = x)   by group_iso_property
       so      |/ x' IN G                 by group_inv_element
       and  f ( |/ x') IN h.carrier       by GroupHomo_def
       Let y = f ( |/ x')
       then h.op y x = f ( |/ x' * x')    by GroupHomo_def
                     = f #e               by group_linv
                     = h.id
*)
val group_iso_group = store_thm(
  "group_iso_group",
  ``!(g:'a group) (h:'b group) f. Group g /\ GroupIso f g h /\ (f #e = h.id) ==> Group h``,
  rw[group_iso_property] >>
  `(!x. x IN G ==> f x IN h.carrier) /\ !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))`
    by metis_tac[GroupHomo_def] >>
  rw[group_def_alt] >| [
    metis_tac[group_op_element],
    `?x'. x' IN G /\ (f x' = x)` by metis_tac[] >>
    `?y'. y' IN G /\ (f y' = y)` by metis_tac[] >>
    `?z'. z' IN G /\ (f z' = z)` by metis_tac[] >>
    `?t. t IN G /\ (t = x' * y')` by metis_tac[group_op_element] >>
    `h.op (h.op x y) z = f (x' * y' * z')` by metis_tac[] >>
    `?s. s IN G /\ (s = y' * z')` by metis_tac[group_op_element] >>
    `h.op x (h.op y z) = f (x' * (y' * z'))` by metis_tac[] >>
    `x' * y' * z' = x' * (y' * z')` by rw[group_assoc] >>
    metis_tac[],
    metis_tac[group_id_element, GroupHomo_def],
    metis_tac[group_lid, group_id_element],
    metis_tac[group_linv, group_inv_element]
  ]);

(* Theorem: GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier) *)
(* Proof: by GroupIso_def, FINITE_BIJ_CARD. *)
val group_iso_card_eq = store_thm(
  "group_iso_card_eq",
  ``!g:'a group h:'b group f. GroupIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)``,
  metis_tac[GroupIso_def, FINITE_BIJ_CARD]);

(* ------------------------------------------------------------------------- *)
(* Group Automorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ GroupAuto f g ==> (f #e = #e) *)
(* Proof: by GroupAuto_def, group_iso_id *)
val group_auto_id = store_thm(
  "group_auto_id",
  ``!f g. Group g /\ GroupAuto f g ==> (f #e = #e)``,
  rw_tac std_ss[GroupAuto_def, group_iso_id]);

(* Theorem: GroupAuto f g ==> !x. x IN G ==> f x IN G *)
(* Proof: by GroupAuto_def, group_iso_element *)
val group_auto_element = store_thm(
  "group_auto_element",
  ``!f g. GroupAuto f g ==> !x. x IN G ==> f x IN G``,
  metis_tac[GroupAuto_def, group_iso_element]);

(* Theorem: GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g *)
(* Proof: by GroupAuto_def, group_iso_compose *)
val group_auto_compose = store_thm(
  "group_auto_compose",
  ``!(g:'a group). !f1 f2. GroupAuto f1 g /\ GroupAuto f2 g ==> GroupAuto (f1 o f2) g``,
  metis_tac[GroupAuto_def, group_iso_compose]);

(* Theorem: Group g /\ GroupAuto f g ==> MonoidAuto f g *)
(* Proof: by GroupAuto_def, MonoidAuto_def, group_iso_is_monoid_iso *)
val group_auto_is_monoid_auto = store_thm(
  "group_auto_is_monoid_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> MonoidAuto f g``,
  rw[GroupAuto_def, MonoidAuto_def] >>
  rw[group_iso_is_monoid_iso]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n *)
(* Proof:
   Note Monoid g           by group_is_monoid
    and MonoidAuto f g     by group_auto_is_monoid_auto
    The result follows     by monoid_auto_exp
*)
val group_auto_exp = store_thm(
  "group_auto_exp",
  ``!g:'a group f. Group g /\ GroupAuto f g ==>
   !x. x IN G ==> !n. f (x ** n) = (f x) ** n``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_exp]);

(* Theorem: Group g /\ GroupAuto f g ==> !x. x IN G ==> (order h (f x) = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and MonoidAuto f h                        by group_auto_is_monoid_auto
   Thus !x. x IN H ==> (ord (f x) = ord x)    by monoid_auto_order
*)
val group_auto_order = store_thm(
  "group_auto_order",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==>
    !x. x IN G ==> (ord (f x) = ord x)``,
  rw[group_is_monoid, group_auto_is_monoid_auto, monoid_auto_order]);

(* Theorem: GroupAuto I g *)
(* Proof:
       GroupAuto I g
   <=> GroupIso I g g                 by GroupAuto_def
   <=> GroupHomo I g g /\ BIJ f G G   by GroupIso_def
   <=> T /\ BIJ f G G                 by GroupHomo_def, I_THM
   <=> T /\ T                         by BIJ_I_SAME
*)
val group_auto_I = store_thm(
  "group_auto_I",
  ``!(g:'a group). GroupAuto I g``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def, GroupHomo_def, BIJ_I_SAME]);

(* Theorem: Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g *)
(* Proof:
       GroupAuto I g
   ==> GroupIso I g g                by GroupAuto_def
   ==> GroupIso (LINV f G) g         by group_iso_linv_iso
   ==> GroupAuto (LINV f G) g        by GroupAuto_def
*)
val group_auto_linv_auto = store_thm(
  "group_auto_linv_auto",
  ``!(g:'a group) f. Group g /\ GroupAuto f g ==> GroupAuto (LINV f G) g``,
  rw_tac std_ss[GroupAuto_def, group_iso_linv_iso]);

(* Theorem: GroupAuto f g ==> f PERMUTES G *)
(* Proof: by GroupAuto_def, GroupIso_def *)
val group_auto_bij = store_thm(
  "group_auto_bij",
  ``!g:'a group. !f. GroupAuto f g ==> f PERMUTES G``,
  rw_tac std_ss[GroupAuto_def, GroupIso_def]);

(* ------------------------------------------------------------------------- *)
(* Subgroups                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: subgroup h g <=> H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) *)
(* Proof:
       subgroup h g
   <=> GroupHomo I h g                                              by subgroup_def
   <=> (!x. x IN H ==> I x IN G) /\
       (!x y. x IN H /\ y IN H ==> (I (h.op x y) = (I x) * (I y)))  by GroupHomo_def
   <=> (!x. x IN H ==> x IN G) /\
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by I_THM
   <=> H SUBSET G
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))              by SUBSET_DEF
*)
val subgroup_eqn = store_thm(
  "subgroup_eqn",
  ``!(g:'a group) (h:'a group). subgroup h g <=>
     H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y))``,
  rw_tac std_ss[subgroup_def, GroupHomo_def, SUBSET_DEF]);

(* Theorem: subgroup h g ==> H SUBSET G *)
(* Proof: by subgroup_eqn *)
val subgroup_subset = store_thm(
  "subgroup_subset",
  ``!(g:'a group) (h:'a group). subgroup h g ==> H SUBSET G``,
  rw_tac std_ss[subgroup_eqn]);

(* Theorem: subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k *)
(* Proof:
   Note H SUBSET G              by subgroup_subset
     or !x. x IN H ==> x IN G   by SUBSET_DEF
   By GroupHomo_def, this is to show:
   (1) x IN H ==> f x IN k.carrier
       True                     by GroupHomo_def, GroupHomo f g k
   (2) x IN H /\ y IN H /\ f (h.op x y) = k.op (f x) (f y)
       Note x IN H ==> x IN G   by above
        and y IN H ==> y IN G   by above
         f (h.op x y)
       = f (x * y)              by subgroup_eqn
       = k.op (f x) (f y)       by GroupHomo_def
*)
val subgroup_homo_homo = store_thm(
  "subgroup_homo_homo",
  ``!(g:'a group) (h:'a group) (k:'b group) f. subgroup h g /\ GroupHomo f g k ==> GroupHomo f h k``,
  rw_tac std_ss[subgroup_def, GroupHomo_def]);

(* Theorem: subgroup g g *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g g, true by group_homo_I_refl.
*)
val subgroup_reflexive = store_thm(
  "subgroup_reflexive",
  ``!g:'a group. subgroup g g``,
  rw[subgroup_def, group_homo_I_refl]);

(* Theorem: subgroup g h /\ subgroup h k ==> subgroup g k *)
(* Proof:
   By subgroup_def, this is to show:
   GroupHomo I g h /\ GroupHomo I h k ==> GroupHomo I g k
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by group_homo_trans
*)
val subgroup_transitive = store_thm(
  "subgroup_transitive",
  ``!(g h k):'a group. subgroup g h /\ subgroup h k ==> subgroup g k``,
  prove_tac[subgroup_def, combinTheory.I_o_ID, group_homo_trans]);

(* Theorem: subgroup h g /\ subgroup g h ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ GroupHomo I g h ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by subgroup_subset, subgroup g h
*)
val subgroup_I_antisym = store_thm(
  "subgroup_I_antisym",
  ``!(g:'a monoid) h. subgroup h g /\ subgroup g h ==> GroupIso I h g``,
  rw_tac std_ss[subgroup_def, GroupIso_def] >>
  fs[GroupHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subgroup h g /\ G SUBSET H ==> GroupIso I h g *)
(* Proof:
   By subgroup_def, GroupIso_def, this is to show:
      GroupHomo I h g /\ G SUBSET H ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by subgroup_subset, subgroup h g
   (2) x IN G ==> x IN H, true    by G SUBSET H, given
*)
val subgroup_carrier_antisym = store_thm(
  "subgroup_carrier_antisym",
  ``!(g:'a group) h. subgroup h g /\ G SUBSET H ==> GroupIso I h g``,
  rpt (stripDup[subgroup_def]) >>
  rw_tac std_ss[GroupIso_def] >>
  `H SUBSET G` by rw[subgroup_subset] >>
  fs[GroupHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: Group g /\ Group h /\ subgroup h g ==> submonoid h g *)
(* Proof:
   By subgroup_def, submonoid_def, this is to show:
      Group g /\ Group h /\ GroupHomo I h g ==> MonoidHomo I h g
   This is true by group_homo_is_monoid_homo
*)
val subgroup_is_submoniod = store_thm(
  "subgroup_is_submoniod",
  ``!g:'a group h. Group g /\ Group h /\ subgroup h g ==> submonoid h g``,
  rw[subgroup_def, submonoid_def] >>
  rw[group_homo_is_monoid_homo]);

(* Theorem: Group g /\ Group h /\ subgroup h g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note Monoid g /\ Monoid h                  by group_is_monoid
    and submonoid h g                         by subgroup_is_submoniod
   Thus !x. x IN H ==> (order h x = ord x)    by submonoid_order_eqn
*)
val subgroup_order_eqn = store_thm(
  "subgroup_order_eqn",
  ``!g:'a group h. Group g /\ Group h /\ subgroup h g ==>
   !x. x IN H ==> (order h x = ord x)``,
  rw[group_is_monoid, subgroup_is_submoniod, submonoid_order_eqn]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of a Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* For those same as monoids, use overloading  *)
val _ = overload_on ("homo_group", ``homo_monoid``);

(* Theorem: [Closure] Group g /\ GroupHomo f g (homo_group g f) ==> x IN fG /\ y IN fG ==> x o y IN fG *)
(* Proof:
   x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))  by homo_monoid_property
   Since   CHOICE (preimage f G x) IN G    by preimage_choice_property
           CHOICE (preimage f G y) IN G    by preimage_choice_property
   hence   CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G      by group_op_element
   so    f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) IN fG   by GroupHomo_def
*)
val homo_group_closure = store_thm(
  "homo_group_closure",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
     !x y. x IN fG /\ y IN fG ==> x o y IN fG``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_def, image_op_def] >>
  rw_tac std_ss[preimage_choice_property, group_op_element]);

(* Theorem: [Associative] Group g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = x o (y o z) *)
(* Proof:
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
           CHOICE (preimage f G z) IN G /\ z = f (CHOICE (preimage f G z))   by preimage_choice_property
     (x o y) o z
   = (f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))) o f (CHOICE (preimage f G z))   by expanding x, y, z
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)) o f (CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z))             by homo_monoid_property
   = f (CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z)))           by group_assoc
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y) * CHOICE (preimage f G z))         by homo_monoid_property
   = f (CHOICE (preimage f G x)) o (f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G z)))   by homo_monoid_property
   = x o (y o z)                                                                                 by contracting x, y, z
*)
val homo_group_assoc = store_thm(
  "homo_group_assoc",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
   !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==>
     (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw_tac std_ss[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G z) IN G /\ (f (CHOICE (preimage f G z)) = z)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) IN G` by rw[] >>
  `CHOICE (preimage f G y) * CHOICE (preimage f G z) IN G` by rw[] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) * CHOICE (preimage f G z) =
   CHOICE (preimage f G x) * (CHOICE (preimage f G y) * CHOICE (preimage f G z))` by rw[group_assoc] >>
  metis_tac[]);

(* Theorem: [Identity] Group g /\ GroupHomo f g (homo_group g f) ==> #i IN fG /\ #i o x = x /\ x o #i = x. *)
(* Proof:
   By homo_monoid_property, #i = f #e, and #i IN fG.
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   hence  #i o x
        = (f #e) o  f (preimage f G x)
        = f (#e * preimage f G x)       by homo_group_property
        = f (preimage f G x)            by group_lid
        = x
   similarly for x o #i = x             by group_rid
*)
val homo_group_id = store_thm(
  "homo_group_id",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_group g f) ==>
      #i IN fG /\ (!x. x IN fG ==> (#i o x = x) /\ (x o #i = x))``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >| [
    rw[],
    metis_tac[group_lid, group_id_element, preimage_choice_property],
    metis_tac[group_rid, group_id_element, preimage_choice_property]
  ]);

(* Theorem: [Inverse] Group g /\ GroupHomo f g (homo_monoid g f) ==> x IN fG ==> ?z. z IN fG /\ z o x = #i. *)
(* Proof:
   x IN fG ==> CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   Choose z = f ( |/ (preimage f G x)),
   then   z IN fG since |/ CHOICE (preimage f G x) IN G,
   and    z o x = f ( |/ (CHOICE (preimage f G x))) o f (CHOICE (preimage f G x))
                = f ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x))    by homo_monoid_property
                = f #e                                                           by group_lid
                = #i                                                             by homo_monoid_id
*)
val homo_group_inv = store_thm(
  "homo_group_inv",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ GroupHomo f g (homo_monoid g f) ==>
     !x. x IN fG ==> ?z. z IN fG /\ (z o x = #i)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `|/ (CHOICE (preimage f G x)) IN G /\ ( |/ (CHOICE (preimage f G x)) * CHOICE (preimage f G x) = #e)` by rw[] >>
  qexists_tac `f ( |/ (CHOICE (preimage f G x)))` >>
  metis_tac[]);

(* Theorem: [Commutative] AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
            x IN fG /\ y IN fG ==> (x o y = y o x) *)
(* Proof:
   Note AbelianGroup g ==> Group g and
        !x y. x IN G /\ y IN G ==> (x * y = y * x)          by AbelianGroup_def
   By GroupHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
           CHOICE (preimage f G y) IN G /\ y = f (CHOICE (preimage f G y))   by preimage_choice_property
     x o y
   = f (CHOICE (preimage f G x)) o f (CHOICE (preimage f G y))   by expanding x, y
   = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))       by homo_monoid_property
   = f (CHOICE (preimage f G y) * CHOICE (preimage f G x))       by AbelianGroup_def, above
   = f (CHOICE (preimage f G y)) o f (CHOICE (preimage f G x))   by homo_monoid_property
   = y o x                                                       by contracting x, y
*)
val homo_group_comm = store_thm(
  "homo_group_comm",
  ``!(g:'a group) (f:'a -> 'b). AbelianGroup g /\ GroupHomo f g (homo_group g f) ==>
   !x y. x IN fG /\ y IN fG ==> (x o y = y o x)``,
  rw_tac std_ss[AbelianGroup_def, GroupHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  `CHOICE (preimage f G x) IN G /\ (f (CHOICE (preimage f G x)) = x)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G y) IN G /\ (f (CHOICE (preimage f G y)) = y)` by metis_tac[preimage_choice_property] >>
  `CHOICE (preimage f G x) * CHOICE (preimage f G y) = CHOICE (preimage f G y) * CHOICE (preimage f G x)` by rw[] >>
  metis_tac[]);

(* Theorem: Homomorphic image of a group is a group.
            Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f) *)
(* Proof:
   This is to show each of these:
   (1) x IN fG /\ y IN fG ==> x o y IN fG    true by homo_group_closure
   (2) x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = (x o y) o z    true by homo_group_assoc
   (3) #i IN fG, true by homo_group_id
   (4) x IN fG ==> #i o x = x, true by homo_group_id
   (5) x IN fG ==> ?y. y IN fG /\ (y o x = #i), true by homo_group_inv
*)
val homo_group_group = store_thm(
  "homo_group_group",
  ``!(g:'a group) f. Group g /\ GroupHomo f g (homo_monoid g f) ==> Group (homo_monoid g f)``,
  rpt strip_tac >>
  rw[group_def_alt] >| [
    rw[homo_group_closure],
    rw[homo_group_assoc],
    rw[homo_group_id],
    rw[homo_group_id],
    rw[homo_group_inv]
  ]);

(* Theorem: Homomorphic image of an Abelian group is an Abelian group.
            AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f) *)
(* Proof:
   Note AbelianGroup g ==> Group g                  by AbelianGroup_def
   By AbelianGroup_def, this is to show:
   (1) Group (homo_group g f), true                 by homo_group_group, Group g
   (2) x IN fG /\ y IN fG ==> x o y = y o x, true   by homo_group_comm, AbelianGroup g
*)
val homo_group_abelian_group = store_thm(
  "homo_group_abelian_group",
  ``!(g:'a group) f. AbelianGroup g /\ GroupHomo f g (homo_group g f) ==> AbelianGroup (homo_monoid g f)``,
  metis_tac[homo_group_group, AbelianGroup_def, homo_group_comm]);

(* Theorem: Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f) *)
(* Proof:
   By GroupHomo_def, homo_monoid_property, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true                 by IN_IMAGE
   (2) x IN G /\ y IN G ==> f (x * y) = f x o f y, true  by homo_monoid_op_inj
*)
val homo_group_by_inj = store_thm(
  "homo_group_by_inj",
  ``!(g:'a group) (f:'a -> 'b). Group g /\ INJ f G UNIV ==> GroupHomo f g (homo_group g f)``,
  rw_tac std_ss[GroupHomo_def, homo_monoid_property] >-
  rw[] >>
  rw[homo_monoid_op_inj]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Group.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Group g, and an injective function f,
   then the image (f G) is a Group, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a group injective image for an injective f, with LINV f G. *)
(* Since a group is a monoid, group injective image = monoid injective image *)

(* Theorem: Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f) *)
(* Proof:
   By Group_def, this is to show:
   (1) Group g ==> Monoid (monoid_inj_image g f)
       Group g ==> Monoid g                            by group_is_monoid
               ==> Monoid (monoid_inj_image g f)       by monoid_inj_image_monoid
   (2) monoid_invertibles (monoid_inj_image g f) = (monoid_inj_image g f).carrier
       By monoid_invertibles_def, monoid_inj_image_def, this is to show:
       z IN G ==> ?y. (?x. (y = f x) /\ x IN G) /\
                  (f (t (f z) * t y) = f #e) /\ (f (t y * t (f z)) = f #e)
                                                       where t = LINV f G
      Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)   by INJ_IMAGE_BIJ_ALT
        so !x. x IN G ==> t (f x) = x
       and !x. x IN (IMAGE f G) ==> f (t x) = x        by BIJ_LINV_THM
      Also z IN G ==> |/ z IN G                        by group_inv_element
       Put x = |/ z, and y = f x
      Then  f (t (f z) * t y)
          = f (t (f z) * t (f ( |/ z)))                by y = f ( |/ z)
          = f (z * |/ z)                               by !y. t (f y) = y
          = f #e                                       by group_inv_thm
        and f (t y * t (f z))
          = f (t (f ( |/ z)) * t (f z))                by y = f ( |/ z)
          = f ( |/ z * z)                              by !y. t (f y) = y
          = f #e                                       by group_inv_thm
*)
Theorem group_inj_image_group:
  !(g:'a group) (f:'a -> 'b). Group g /\ INJ f G univ(:'b) ==> Group (monoid_inj_image g f)
Proof
  rpt strip_tac >>
  rw_tac std_ss[Group_def] >-
  rw[monoid_inj_image_monoid] >>
  rw[monoid_invertibles_def, monoid_inj_image_def, EXTENSION, EQ_IMP_THM] >>
  `g.inv x' IN G` by rw[] >>
  qexists_tac `f (g.inv x')` >>
  `BIJ f G (IMAGE f G)` by rw[INJ_IMAGE_BIJ_ALT] >>
  imp_res_tac BIJ_LINV_THM >>
  metis_tac[group_inv_thm]
QED

(* Theorem: AbelianGroup g /\ INJ f G univ(:'b) ==> AbelianGroup (monoid_inj_image g f) *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group g ==> Group (monoid_inj_image g f)
       True by group_inj_image_group.
   (2) (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       By monoid_inj_image_def, this is to show:
       x' IN G /\ x'' IN G /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
       ==> f (t (f x') * t (f x'')) = f (t (f x'') * t (f x'))  where t = LINV f G
       Note INJ f G univ(:'b) ==> BIJ f G (IMAGE f G)  by INJ_IMAGE_BIJ_ALT
         so !x. x IN G ==> t (f x) = x
        and !x. x IN (IMAGE f G) ==> f (t x) = x       by BIJ_LINV_THM
         f (t (f x') * t (f x''))
       = f (x' * x'')                                  by !y. t (f y) = y
       = f (x'' * x')                                  by commutativity condition
       = f (t (f x'') * t (f x'))                      by !y. t (f y) = y
*)
Theorem group_inj_image_abelian_group:
  !(g:'a group) (f:'a -> 'b). AbelianGroup g /\ INJ f G univ(:'b) ==>
       AbelianGroup (monoid_inj_image g f)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_inj_image_def] >>
  metis_tac[INJ_IMAGE_BIJ_ALT, BIJ_LINV_THM]
QED

(* Theorem: Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G
            ==> Group (monoid_inj_image g f excluding f e) *)
(* Proof:
   Let h = g excluding e.
   Then H = h.carrier = G DIFF {e}             by excluding_def
    and h.op = g.op /\ h.id = g.id             by excluding_def
    and IMAGE f H = IMAGE f G DIFF {f e}       by IMAGE_DIFF
    and H SUBSET G                             by DIFF_SUBSET
   Let t = LINV f G.
   Then !x. x IN H ==> t (f x) = x             by LINV_SUBSET

   By group_def_alt, monoid_inj_image_def, excluding_def, this is to show:
   (1) x IN IMAGE f H /\ y IN IMAGE f H ==> f (t x * t y) IN IMAGE f H
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
            ?b. (y = f b) /\ b IN H            by IN_IMAGE
       Hence  f (t x * t y)
            = f (t (f a) * t (f b))            by x = f a, y = f b
            = f (a * b)                        by !y. t (f y) = y
       Since a * b IN H                        by group_op_element
       hence f (a * b) IN IMAGE f H            by IN_IMAGE
   (2) x IN IMAGE f H /\ y IN IMAGE f H /\ z IN IMAGE f H ==> f (t x * t y * t z) = f (t x * (t y * t z))
       Note ?a. (x = f a) /\ a IN G            by IN_IMAGE
            ?b. (y = f b) /\ b IN G            by IN_IMAGE
            ?c. (z = f c) /\ c IN G            by IN_IMAGE
       Hence  (t x * t y) * t z
            = (t (f a) * t (f b)) * t (f c)    by x = f a, y = f b, z = f c
            = (a * b) * c                      by !y. t (f y) = y
            = a * (b * c)                      by group_assoc
            = t (f a) * (t (f b) * t (f c))    by !y. t (f y) = y
            = t x * (t y * t z)                by x = f a, y = f b, z = f c
       or   f ((t x * t y) * t z) = f (t x * (t y * t z))
   (3) f #e IN IMAGE f H
       Since #e IN H                           by group_id_element
       f #e IN IMAGE f H                       by IN_IMAGE
   (4) x IN IMAGE f H ==> f (t (f #e) * t x) = x
       Note #e IN H                            by group_id_element
        and ?a. (x = f a) /\ a IN H            by IN_IMAGE
       Hence f (t (f #e) * t x)
           = f (#e * t x)                      by !y. t (f y) = y
           = f (#e * t (f a))                  by x = f a
           = f (#e * a)                        by !y. t (f y) = y
           = f a                               by group_id
           = x                                 by x = f a
   (5) x IN IMAGE f H ==> ?y. y IN IMAGE f H /\ f (t y * t x) = f #e
       Note ?a. (x = f a) /\ a IN H            by IN_IMAGE
        and b = (h.inv a) IN H                 by group_inv_element
       Let y = f b.
       Then y IN IMAGE f H                     by IN_IMAGE
        and f (t y * t x)
          = f (t y * t (f a))                  by x = f a
          = f (t (f b)) * t (f a))             by y = f b
          = f (b * a)                          by !y. t (f y) = y
          = f #e                               by group_linv
*)
Theorem group_inj_image_excluding_group:
  !(g:'a group) (f:'a -> 'b) e.
      Group (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      Group (monoid_inj_image g f excluding f e)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  qabbrev_tac `Q = IMAGE f G DIFF {f e}` >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  rw_tac std_ss[group_def_alt, monoid_inj_image_def, excluding_def] >| [
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_op_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN H` by rw[GSYM IN_IMAGE] >>
    `?c. (z = f c) /\ c IN H` by rw[GSYM IN_IMAGE] >>
    metis_tac[group_assoc, group_op_element],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    metis_tac[group_id_element, group_id, IN_IMAGE],
    `Q = IMAGE f H` by fs[IMAGE_DIFF, Abbr`Q`] >>
    `?a. (x = f a) /\ a IN H` by rw[GSYM IN_IMAGE] >>
    `h.inv a IN H` by rw[group_inv_element] >>
    `f (h.inv a) IN Q` by rw[] >>
    metis_tac[group_linv]
  ]
QED

(* Theorem: AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
            AbelianGroup (monoid_inj_image g f excluding f e) *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Group (monoid_inj_image g f excluding f e)
       True by group_inj_image_excluding_group.
   (2) x IN IMAGE f H /\ y IN IMAGE f H ==> (monoid_inj_image g f).op x y = (monoid_inj_image g f).op y x
       where H = G DIFF {e}
       Note H SUBSET G                                     by DIFF_SUBSET
         so !x. x IN H ==> LINV f G (f x) = x              by LINV_SUBSET
        and (monoid_inj_image g f excluding f e).carrier
          = (IMAGE f G) DIFF {f e}                         by monoid_inj_image_def, excluding_def
          = IMAGE f (G DIFF {e})                           by IMAGE_DIFF
          = IMAGE f H                                      by notation
       By monoid_inj_image_def, excluding_def, this is to show:
          f (t x * t y) = f (t y * t x)                    where t = LINV f G
       Note ?a. x = f a /\ a IN H                          by IN_IMAGE
            ?b. y = f b /\ b IN H                          by IN_IMAGE
         f (t x * t y)
       = f (t (f a) * t (f b))                             by x = f a, y = f b
       = f (a * b)                                         by !y. t (f y) = y
       = f (b * a)                                         by commutativity condition
       = f (t (f b) * t (f a))                             by !y. t (f y) = y
       = f (t y * t x)                                     by y = f b, x = f a
*)
Theorem group_inj_image_excluding_abelian_group:
  !(g:'a group) (f:'a -> 'b) e.
      AbelianGroup (g excluding e) /\ INJ f G univ(:'b) /\ e IN G ==>
      AbelianGroup (monoid_inj_image g f excluding f e)
Proof
  rw[AbelianGroup_def] >-
  rw[group_inj_image_excluding_group] >>
  qabbrev_tac `h = g excluding e` >>
  `h.carrier = G DIFF {e} /\ h.op = g.op /\ h.id = g.id` by rw[excluding_def, Abbr`h`] >>
  `H SUBSET G` by fs[] >>
  imp_res_tac LINV_SUBSET >>
  `(monoid_inj_image g f excluding f e).carrier = IMAGE f G DIFF {f e}` by rw[monoid_inj_image_def, excluding_def] >>
  `_ = IMAGE f H` by rw[IMAGE_DIFF] >>
  simp[monoid_inj_image_def, excluding_def] >>
  metis_tac[IN_IMAGE]
QED

(* Theorem: INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f) *)
(* Proof:
   Let s = IMAGE f G.
   Then BIJ f G s                              by INJ_IMAGE_BIJ_ALT
     so INJ f G s                              by BIJ_DEF

   By GroupHomo_def, monoid_inj_image_def, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem group_inj_image_group_homo:
  !(g:'a group) f. INJ f G univ(:'b) ==> GroupHomo f g (monoid_inj_image g f)
Proof
  rw[GroupHomo_def, monoid_inj_image_def] >>
  qabbrev_tac `s = IMAGE f G` >>
  `BIJ f G s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f G s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
