(* ------------------------------------------------------------------------- *)
(* Monoid Maps                                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoidMap";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* val _ = load "monoidOrderTheory"; *)
open monoidTheory monoidOrderTheory;

(* open dependent theories *)
open pred_setTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- from monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- from monoidTheory *) *)
open helperNumTheory helperSetTheory;


(* ------------------------------------------------------------------------- *)
(* Monoid Maps Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   H      = h.carrier
   o      = binary operation of homo_monoid: (homo_monoid g f).op
   #i     = identity of homo_monoid: (homo_monoid g f).id
   fG     = carrier of homo_monoid: (homo_monoid g f).carrier
*)
(* Definitions and Theorems (# are exported):

   Homomorphism, isomorphism, endomorphism, automorphism and submonoid:
   MonoidHomo_def   |- !f g h. MonoidHomo f g h <=>
                               (!x. x IN G ==> f x IN h.carrier) /\ (f #e = h.id) /\
                               !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   MonoidIso_def    |- !f g h. MonoidIso f g h <=> MonoidHomo f g h /\ BIJ f G h.carrier
   MonoidEndo_def   |- !f g. MonoidEndo f g <=> MonoidHomo f g g
   MonoidAuto_def   |- !f g. MonoidAuto f g <=> MonoidIso f g g
   submonoid_def    |- !h g. submonoid h g <=> MonoidHomo I h g

   Monoid Homomorphisms:
   monoid_homo_id       |- !f g h. MonoidHomo f g h ==> (f #e = h.id)
   monoid_homo_element  |- !f g h. MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier
   monoid_homo_cong     |- !g h f1 f2. Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
                                       (MonoidHomo f1 g h <=> MonoidHomo f2 g h)
   monoid_homo_I_refl   |- !g. MonoidHomo I g g
   monoid_homo_trans    |- !g h k f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
   monoid_homo_sym      |- !g h f. Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g
   monoid_homo_compose  |- !g h k f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
   monoid_homo_exp      |- !g h f. Monoid g /\ MonoidHomo f g h ==>
                           !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n

   Monoid Isomorphisms:
   monoid_iso_property  |- !f g h. MonoidIso f g h <=>
                                   MonoidHomo f g h /\ !y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)
   monoid_iso_id        |- !f g h. MonoidIso f g h ==> (f #e = h.id)
   monoid_iso_element   |- !f g h. MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier
   monoid_iso_monoid    |- !g h f. Monoid g /\ MonoidIso f g h ==> Monoid h
   monoid_iso_I_refl    |- !g. MonoidIso I g g
   monoid_iso_trans     |- !g h k f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k
   monoid_iso_sym       |- !g h f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g
   monoid_iso_compose   |- !g h k f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k
   monoid_iso_exp       |- !g h f. Monoid g /\ MonoidIso f g h ==>
                           !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n
   monoid_iso_linv_iso  |- !g h f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g
   monoid_iso_bij       |- !g h f. MonoidIso f g h ==> BIJ f G h.carrier
   monoid_iso_eq_id     |- !g h f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
                           !x. x IN G ==> ((f x = h.id) <=> (x = #e))
   monoid_iso_order     |- !g h f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
                           !x. x IN G ==> (order h (f x) = ord x)
   monoid_iso_card_eq   |- !g h f. MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)

   Monoid Automorphisms:
   monoid_auto_id       |- !f g. MonoidAuto f g ==> (f #e = #e)
   monoid_auto_element  |- !f g. MonoidAuto f g ==> !x. x IN G ==> f x IN G
   monoid_auto_compose  |- !g f1 f2. MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g
   monoid_auto_exp      |- !g f. Monoid g /\ MonoidAuto f g ==>
                           !x. x IN G ==> !n. f (x ** n) = f x ** n
   monoid_auto_I        |- !g. MonoidAuto I g
   monoid_auto_linv_auto|- !g f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g
   monoid_auto_bij      |- !g f. MonoidAuto f g ==> f PERMUTES G
   monoid_auto_order    |- !g f. Monoid g /\ MonoidAuto f g ==>
                           !x. x IN G ==> (ord (f x) = ord x)

   Submonoids:
   submonoid_eqn               |- !g h. submonoid h g <=> H SUBSET G /\
                                        (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e)
   submonoid_subset            |- !g h. submonoid h g ==> H SUBSET G
   submonoid_homo_homo         |- !g h k f. submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k
   submonoid_refl              |- !g. submonoid g g
   submonoid_trans             |- !g h k. submonoid g h /\ submonoid h k ==> submonoid g k
   submonoid_I_antisym         |- !g h. submonoid h g /\ submonoid g h ==> MonoidIso I h g
   submonoid_carrier_antisym   |- !g h. submonoid h g /\ G SUBSET H ==> MonoidIso I h g
   submonoid_order_eqn         |- !g h. Monoid g /\ Monoid h /\ submonoid h g ==>
                                  !x. x IN H ==> (order h x = ord x)

   Homomorphic Image of Monoid:
   image_op_def         |- !g f x y. image_op g f x y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y))
   image_op_inj         |- !g f. INJ f G univ(:'b) ==>
                           !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (x * y))
   homo_monoid_def      |- !g f. homo_monoid g f = <|carrier := IMAGE f G; op := image_op g f; id := f #e|>
   homo_monoid_property |- !g f. (fG = IMAGE f G) /\
                                 (!x y. x IN fG /\ y IN fG ==>
                                       (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))) /\
                                 (#i = f #e)
   homo_monoid_element  |- !g f x. x IN G ==> f x IN fG
   homo_monoid_id       |- !g f. f #e = #i
   homo_monoid_op_inj   |- !g f. INJ f G univ(:'b) ==> !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   homo_monoid_I        |- !g. MonoidIso I (homo_group g I) g

   homo_monoid_closure         |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y. x IN fG /\ y IN fG ==> x o y IN fG
   homo_monoid_assoc           |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o y o z)
   homo_monoid_id_property     |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> #i IN fG /\
                                  !x. x IN fG ==> (#i o x = x) /\ (x o #i = x)
   homo_monoid_comm            |- !g f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                  !x y. x IN fG /\ y IN fG ==> (x o y = y o x)
   homo_monoid_monoid          |- !g f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f)
   homo_monoid_abelian_monoid  |- !g f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
                                        AbelianMonoid (homo_monoid g f)
   homo_monoid_by_inj          |- !g f. Monoid g /\ INJ f G univ(:'b) ==> MonoidHomo f g (homo_monoid g f)

   Weaker form of Homomorphic of Monoid and image of identity:
   WeakHomo_def        |- !f g h. WeakHomo f g h <=>
                           (!x. x IN G ==> f x IN h.carrier) /\
                            !x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))
   WeakIso_def         |- !f g h. WeakIso f g h <=> WeakHomo f g h /\ BIJ f G h.carrier
   monoid_weak_iso_id  |- !f g h. Monoid g /\ Monoid h /\ WeakIso f g h ==> (f #e = h.id)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphism, isomorphism, endomorphism, automorphism and submonoid.      *)
(* ------------------------------------------------------------------------- *)

(* val _ = overload_on ("H", ``h.carrier``);

- type_of ``H``;
> val it = ``:'a -> bool`` : hol_type

then MonoidIso f g h = MonoidHomo f g h /\ BIJ f G H
will make MonoidIso apply only for f: 'a -> 'a.

will need val _ = overload_on ("H", ``(h:'b monoid).carrier``);
*)

(* A function f from g to h is a homomorphism if monoid properties are preserved. *)
(* For monoids, need to ensure that identity is preserved, too. See: monoid_weak_iso_id. *)
val MonoidHomo_def = Define`
  MonoidHomo (f:'a -> 'b) (g:'a monoid) (h:'b monoid) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))) /\
    (f #e = h.id)
`;
(*
If MonoidHomo_def uses the condition: !x y. f (x * y) = h.op (f x) (f y)
this will mean a corresponding change in GroupHomo_def, but then
in quotientGroup <<normal_subgroup_coset_homo>> will give a goal:
h <= g ==> x * y * H = (x * H) o (y * H) with no qualification on x, y!
*)

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val MonoidIso_def = Define`
  MonoidIso f g h <=> MonoidHomo f g h /\ BIJ f G h.carrier
`;

(* A monoid homomorphism from g to g is an endomorphism. *)
val MonoidEndo_def = Define `MonoidEndo f g <=> MonoidHomo f g g`;

(* A monoid isomorphism from g to g is an automorphism. *)
val MonoidAuto_def = Define `MonoidAuto f g <=> MonoidIso f g g`;

(* A submonoid h of g if identity is a homomorphism from h to g *)
val submonoid_def = Define `submonoid h g <=> MonoidHomo I h g`;

(* ------------------------------------------------------------------------- *)
(* Monoid Homomorphisms                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidHomo f g h ==> (f #e = h.id) *)
(* Proof: by MonoidHomo_def. *)
val monoid_homo_id = store_thm(
  "monoid_homo_id",
  ``!f g h. MonoidHomo f g h ==> (f #e = h.id)``,
  rw[MonoidHomo_def]);

(* Theorem: MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by MonoidHomo_def *)
val monoid_homo_element = store_thm(
  "monoid_homo_element",
  ``!f g h. MonoidHomo f g h ==> !x. x IN G ==> f x IN h.carrier``,
  rw_tac std_ss[MonoidHomo_def]);

(* Theorem: Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==> (MonoidHomo f1 g h = MonoidHomo f2 g h) *)
(* Proof: by MonoidHomo_def, monoid_op_element, monoid_id_element *)
val monoid_homo_cong = store_thm(
  "monoid_homo_cong",
  ``!g h f1 f2. Monoid g /\ Monoid h /\ (!x. x IN G ==> (f1 x = f2 x)) ==>
               (MonoidHomo f1 g h = MonoidHomo f2 g h)``,
  rw_tac std_ss[MonoidHomo_def, EQ_IMP_THM] >-
  metis_tac[monoid_op_element] >-
  metis_tac[monoid_id_element] >-
  metis_tac[monoid_op_element] >>
  metis_tac[monoid_id_element]);

(* Theorem: MonoidHomo I g g *)
(* Proof: by MonoidHomo_def. *)
val monoid_homo_I_refl = store_thm(
  "monoid_homo_I_refl",
  ``!g:'a monoid. MonoidHomo I g g``,
  rw[MonoidHomo_def]);

(* Theorem: MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo f2 o f1 g k *)
(* Proof: true by MonoidHomo_def. *)
val monoid_homo_trans = store_thm(
  "monoid_homo_trans",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
    !f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k``,
  rw[MonoidHomo_def]);

(* Theorem: Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g *)
(* Proof:
   Note BIJ f G h.carrier
    ==> BIJ (LINV f G) h.carrier G     by BIJ_LINV_BIJ
   By MonoidHomo_def, this is to show:
   (1) x IN h.carrier ==> LINV f G x IN G
       With BIJ (LINV f G) h.carrier G
        ==> INJ (LINV f G) h.carrier G           by BIJ_DEF
        ==> x IN h.carrier ==> LINV f G x IN G   by INJ_DEF
   (2) x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       With x IN h.carrier
        ==> ?x1. (x = f x1) /\ x1 IN G           by BIJ_DEF, SURJ_DEF
       With y IN h.carrier
        ==> ?y1. (y = f y1) /\ y1 IN G           by BIJ_DEF, SURJ_DEF
        and x1 * y1 IN G                         by monoid_op_element
            LINV f G (h.op x y)
          = LINV f G (f (x1 * y1))                  by MonoidHomo_def
          = x1 * y1                                 by BIJ_LINV_THM, x1 * y1 IN G
          = (LINV f G (f x1)) * (LINV f G (f y1))   by BIJ_LINV_THM, x1 IN G, y1 IN G
          = (LINV f G x) * (LINV f G y)             by x = f x1, y = f y1.
   (3) LINV f G h.id = #e
       Since #e IN G                   by monoid_id_element
         LINV f G h.id
       = LINV f G (f #e)               by MonoidHomo_def
       = #e                            by BIJ_LINV_THM
*)
val monoid_homo_sym = store_thm(
  "monoid_homo_sym",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h /\ BIJ f G h.carrier ==>
        MonoidHomo (LINV f G) h g``,
  rpt strip_tac >>
  `BIJ (LINV f G) h.carrier G` by rw[BIJ_LINV_BIJ] >>
  fs[MonoidHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >-
 (`?x1. (x = f x1) /\ x1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `?y1. (y = f y1) /\ y1 IN G` by metis_tac[BIJ_DEF, SURJ_DEF] >>
  `g.op x1 y1 IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]) >>
  `#e IN G` by rw[] >>
  metis_tac[BIJ_LINV_THM]);

Theorem monoid_homo_sym_any:
  Monoid g /\ MonoidHomo f g h /\
  (!x. x IN h.carrier ==> i x IN g.carrier /\ f (i x) = x) /\
  (!x. x IN g.carrier ==> i (f x) = x)
  ==>
  MonoidHomo i h g
Proof
  rpt strip_tac >> fs[MonoidHomo_def]
  \\ metis_tac[Monoid_def]
QED

(* Theorem: MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k *)
(* Proof: by MonoidHomo_def *)
val monoid_homo_compose = store_thm(
  "monoid_homo_compose",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
   !f1 f2. MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k``,
  rw_tac std_ss[MonoidHomo_def]);
(* This is the same as monoid_homo_trans *)

(* Theorem: Monoid g /\ MonoidHomo f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof:
   By induction on n.
   Base: f (x ** 0) = h.exp (f x) 0
         f (x ** 0)
       = f #e                by monoid_exp_0
       = h.id                by monoid_homo_id
       = h.exp (f x) 0       by monoid_exp_0
   Step: f (x ** SUC n) = h.exp (f x) (SUC n)
       Note x ** n IN G               by monoid_exp_element
         f (x ** SUC n)
       = f (x * x ** n)               by monoid_exp_SUC
       = h.op (f x) (f (x ** n))      by MonoidHomo_def
       = h.op (f x) (h.exp (f x) n)   by induction hypothesis
       = h.exp (f x) (SUC n)          by monoid_exp_SUC
*)
val monoid_homo_exp = store_thm(
  "monoid_homo_exp",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidHomo f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[monoid_exp_0, monoid_homo_id] >>
  fs[monoid_exp_SUC, MonoidHomo_def]);

(* ------------------------------------------------------------------------- *)
(* Monoid Isomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidIso f g h <=> MonoidHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y)) *)
(* Proof:
   This is to prove:
   (1) BIJ f G H /\ y IN H ==> ?!x. x IN G /\ (f x = y)
       true by INJ_DEF and SURJ_DEF.
   (2) !y. y IN H /\ MonoidHomo f g h ==> ?!x. x IN G /\ (f x = y) ==> BIJ f G H
       true by INJ_DEF and SURJ_DEF, and
       x IN G /\ GroupHomo f g h ==> f x IN H  by MonoidHomo_def
*)
val monoid_iso_property = store_thm(
  "monoid_iso_property",
  ``!f g h. MonoidIso f g h <=> MonoidHomo f g h /\ (!y. y IN h.carrier ==> ?!x. x IN G /\ (f x = y))``,
  rw_tac std_ss[MonoidIso_def, EQ_IMP_THM] >-
  metis_tac[BIJ_THM] >>
  rw[BIJ_THM] >>
  metis_tac[MonoidHomo_def]);

(* Note: all these proofs so far do not require the condition: f #e = h.id in MonoidHomo_def,
   but evetually it should, as this is included in definitions of all resources. *)

(* Theorem: MonoidIso f g h ==> (f #e = h.id) *)
(* Proof: by MonoidIso_def, monoid_homo_id. *)
val monoid_iso_id = store_thm(
  "monoid_iso_id",
  ``!f g h. MonoidIso f g h ==> (f #e = h.id)``,
  rw_tac std_ss[MonoidIso_def, monoid_homo_id]);

(* Theorem: MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier *)
(* Proof: by MonoidIso_def, monoid_homo_element *)
val monoid_iso_element = store_thm(
  "monoid_iso_element",
  ``!f g h. MonoidIso f g h ==> !x. x IN G ==> f x IN h.carrier``,
  metis_tac[MonoidIso_def, monoid_homo_element]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> Monoid h  *)
(* Proof:
   This is to show:
   (1) x IN h.carrier /\ y IN h.carrier ==> h.op x y IN h.carrier
       Since ?x'. x' IN G /\ (f x' = x)   by monoid_iso_property
             ?y'. y' IN G /\ (f y' = y)   by monoid_iso_property
             h.op x y = f (x' * y')       by MonoidHomo_def
       As                  x' * y' IN G   by monoid_op_element
       hence f (x' * y') IN h.carrier     by MonoidHomo_def
   (2) x IN h.carrier /\ y IN h.carrier /\ z IN h.carrier ==> h.op (h.op x y) z = h.op x (h.op y z)
       Since ?x'. x' IN G /\ (f x' = x)   by monoid_iso_property
             ?y'. y' IN G /\ (f y' = y)   by monoid_iso_property
             ?z'. z' IN G /\ (f z' = z)   by monoid_iso_property
       as     x' * y' IN G                by monoid_op_element
       and f (x' * y') IN h.carrier       by MonoidHomo_def
       ?!t. t IN G /\ f t = f (x' * y')   by monoid_iso_property
       i.e.  t = x' * y'                  by uniqueness
       hence h.op (h.op x y) z = f (x' * y' * z')     by MonoidHomo_def
       Similary,
       as     y' * z' IN G                by monoid_op_element
       and f (y' * z') IN h.carrier       by MonoidHomo_def
       ?!s. s IN G /\ f s = f (y' * z')   by monoid_iso_property
       i.e.  s = y' * z'                  by uniqueness
       and   h.op x (h.op y z) = f (x' * (y' * z'))   by MonoidHomo_def
       hence true by monoid_assoc.
   (3) h.id IN h.carrier
       Since #e IN G                     by monoid_id_element
            (f #e) = h.id IN h.carrier   by MonoidHomo_def
   (4) x IN h.carrier ==> h.op h.id x = x
       Since ?x'. x' IN G /\ (f x' = x)  by monoid_iso_property
       h.id IN h.carrier                 by monoid_id_element
       ?!e. e IN G /\ f e = h.id = f #e  by monoid_iso_property
       i.e. e = #e                       by uniqueness
       hence h.op h.id x = f (e * x')    by MonoidHomo_def
                         = f (#e * x')
                         = f x'          by monoid_lid
                         = x
   (5) x IN h.carrier ==> h.op x h.id = x
       Since ?x'. x' IN G /\ (f x' = x)  by monoid_iso_property
       h.id IN h.carrier                 by monoid_id_element
       ?!e. e IN G /\ f e = h.id = f #e  by monoid_iso_property
       i.e. e = #e                       by uniqueness
       hence h.op x h.id = f (x' * e)    by MonoidHomo_def
                         = f (x' * #e)
                         = f x'          by monoid_rid
                         = x
*)
val monoid_iso_monoid = store_thm(
  "monoid_iso_monoid",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> Monoid h``,
  rw[monoid_iso_property] >>
  `(!x. x IN G ==> f x IN h.carrier) /\
     (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y))) /\
     (f #e = h.id)` by metis_tac[MonoidHomo_def] >>
  rw_tac std_ss[Monoid_def] >-
  metis_tac[monoid_op_element] >-
 (`?x'. x' IN G /\ (f x' = x)` by metis_tac[] >>
  `?y'. y' IN G /\ (f y' = y)` by metis_tac[] >>
  `?z'. z' IN G /\ (f z' = z)` by metis_tac[] >>
  `?t. t IN G /\ (t = x' * y')` by metis_tac[monoid_op_element] >>
  `h.op (h.op x y) z = f (x' * y' * z')` by metis_tac[] >>
  `?s. s IN G /\ (s = y' * z')` by metis_tac[monoid_op_element] >>
  `h.op x (h.op y z) = f (x' * (y' * z'))` by metis_tac[] >>
  `x' * y' * z' = x' * (y' * z')` by rw[monoid_assoc] >>
  metis_tac[]) >-
  metis_tac[monoid_id_element, MonoidHomo_def] >-
  metis_tac[monoid_lid, monoid_id_element] >>
  metis_tac[monoid_rid, monoid_id_element]);

(* Theorem: MonoidIso I g g *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo I g g, true by monoid_homo_I_refl
   (2) BIJ I R R, true by BIJ_I_SAME
*)
val monoid_iso_I_refl = store_thm(
  "monoid_iso_I_refl",
  ``!g:'a monoid. MonoidIso I g g``,
  rw[MonoidIso_def, monoid_homo_I_refl, BIJ_I_SAME]);

(* Theorem: MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
       True by monoid_homo_trans.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE.
*)
val monoid_iso_trans = store_thm(
  "monoid_iso_trans",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
    !f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k``,
  rw[MonoidIso_def] >-
  metis_tac[monoid_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f g h /\ BIJ f G h.carrier ==> MonoidHomo (LINV f G) h g
       True by monoid_homo_sym.
   (2) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val monoid_iso_sym = store_thm(
  "monoid_iso_sym",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g``,
  rw[MonoidIso_def, monoid_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo f1 g h /\ MonoidHomo f2 h k ==> MonoidHomo (f2 o f1) g k
       True by monoid_homo_compose.
   (2) BIJ f1 G h.carrier /\ BIJ f2 h.carrier k.carrier ==> BIJ (f2 o f1) G k.carrier
       True by BIJ_COMPOSE
*)
val monoid_iso_compose = store_thm(
  "monoid_iso_compose",
  ``!(g:'a monoid) (h:'b monoid) (k:'c monoid).
   !f1 f2. MonoidIso f1 g h /\ MonoidIso f2 h k ==> MonoidIso (f2 o f1) g k``,
  rw_tac std_ss[MonoidIso_def] >-
  metis_tac[monoid_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as monoid_iso_trans. *)

(* Theorem: Monoid g /\ MonoidIso f g h ==> !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n *)
(* Proof: by MonoidIso_def, monoid_homo_exp *)
val monoid_iso_exp = store_thm(
  "monoid_iso_exp",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==>
   !x. x IN G ==> !n. f (x ** n) = h.exp (f x) n``,
  rw[MonoidIso_def, monoid_homo_exp]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g *)
(* Proof:
   By MonoidIso_def, MonoidHomo_def, this is to show:
   (1) BIJ f G h.carrier /\ x IN h.carrier ==> LINV f G x IN G
       True by BIJ_LINV_ELEMENT
   (2) BIJ f G h.carrier /\ x IN h.carrier /\ y IN h.carrier ==> LINV f G (h.op x y) = LINV f G x * LINV f G y
       Let x' = LINV f G x, y' = LINV f G y.
       Then x' IN G /\ y' IN G        by BIJ_LINV_ELEMENT
         so x' * y' IN G              by monoid_op_element
        ==> f (x' * y') = h.op (f x') (f y')    by MonoidHomo_def
                        = h.op x y              by BIJ_LINV_THM
       Thus LINV f G (h.op x y)
          = LINV f G (f (x' * y'))    by above
          = x' * y'                   by BIJ_LINV_THM
   (3) BIJ f G h.carrier ==> LINV f G h.id = #e
       Note #e IN G                   by monoid_id_element
        and f #e = h.id               by MonoidHomo_def
        ==> LINV f G h.id = #e        by BIJ_LINV_THM
   (4) BIJ f G h.carrier ==> BIJ (LINV f G) h.carrier G
       True by BIJ_LINV_BIJ
*)
val monoid_iso_linv_iso = store_thm(
  "monoid_iso_linv_iso",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ MonoidIso f g h ==> MonoidIso (LINV f G) h g``,
  rw_tac std_ss[MonoidIso_def, MonoidHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
 (qabbrev_tac `x' = LINV f G x` >>
  qabbrev_tac `y' = LINV f G y` >>
  metis_tac[BIJ_LINV_THM, BIJ_LINV_ELEMENT, monoid_op_element]) >-
  metis_tac[BIJ_LINV_THM, monoid_id_element] >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as monoid_iso_sym, just a direct proof. *)

(* Theorem: MonoidIso f g h ==> BIJ f G h.carrier *)
(* Proof: by MonoidIso_def *)
val monoid_iso_bij = store_thm(
  "monoid_iso_bij",
  ``!(g:'a monoid) (h:'b monoid) f. MonoidIso f g h ==> BIJ f G h.carrier``,
  rw_tac std_ss[MonoidIso_def]);

(* Theorem: Monoid g /\ Monoid h /\ MonoidIso f g h ==>
            !x. x IN G ==> ((f x = h.id) <=> (x = #e)) *)
(* Proof:
   Note MonoidHomo f g h /\ BIJ f G h.carrier   by MonoidIso_def
   If part: x IN G /\ f x = h.id ==> x = #e
      By monoid_id_unique, this is to show:
      (1) !y. y IN G ==> y * x = y
          Let z = y * x.
          Then z IN G               by monoid_op_element
          f z = h.op (f y) (f x)    by MonoidHomo_def
              = h.op (f y) h.id     by f x = h.id
              = f y                 by monoid_homo_element, monoid_id
          Thus z = y                by BIJ_DEF, INJ_DEF
      (2) !y. y IN G ==> x * y = y
          Let z = x * y.
          Then z IN G               by monoid_op_element
          f z = h.op (f x) (f y)    by MonoidHomo_def
              = h.op h.id (f y)     by f x = h.id
              = f y                 by monoid_homo_element, monoid_id
          Thus z = y                by BIJ_DEF, INJ_DEF

   Only-if part: f #e = h.id, true  by monoid_homo_id
*)
val monoid_iso_eq_id = store_thm(
  "monoid_iso_eq_id",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
   !x. x IN G ==> ((f x = h.id) <=> (x = #e))``,
  rw[MonoidIso_def] >>
  rw[EQ_IMP_THM] >| [
    rw[GSYM monoid_id_unique] >| [
      qabbrev_tac `z = x' * x` >>
      `z IN G` by rw[Abbr`z`] >>
      `f z = h.op (f x') (f x)` by fs[MonoidHomo_def, Abbr`z`] >>
      `_ = f x'` by metis_tac[monoid_homo_element, monoid_id] >>
      metis_tac[BIJ_DEF, INJ_DEF],
      qabbrev_tac `z = x * x'` >>
      `z IN G` by rw[Abbr`z`] >>
      `f z = h.op (f x) (f x')` by fs[MonoidHomo_def, Abbr`z`] >>
      `_ = f x'` by metis_tac[monoid_homo_element, monoid_id] >>
      metis_tac[BIJ_DEF, INJ_DEF]
    ],
    rw[monoid_homo_id]
  ]);

(* Theorem: Monoid g /\ Monoid h /\ MonoidIso f g h ==> !x. x IN G ==> (order h (f x) = ord x)` *)
(* Proof:
   Let n = ord x, y = f x.
   If n = 0, to show: order h y = 0.
      By contradiction, suppose order h y <> 0.
      Let m = order h y.
      Note h.id = h.exp y m          by order_property
                = f (x ** m)         by monoid_iso_exp
      Thus x ** m = #e               by monoid_iso_eq_id, monoid_exp_element
       But x ** m <> #e              by order_eq_0, ord x = 0
      This is a contradiction.

   If n <> 0, to show: order h y = n.
      Note ord x = n
       ==> (x ** n = #e) /\
           !m. 0 < m /\ m < n ==> x ** m <> #e    by order_thm, 0 < n
      Note h.exp y n = f (x ** n)    by monoid_iso_exp
                     = f #e          by x ** n = #e
                     = h.id          by monoid_iso_id, [1]
      Claim: !m. 0 < m /\ m < n ==> h.exp y m <> h.id
      Proof: By contradiction, suppose h.exp y m = h.id.
             Then f (x ** m) = h.exp y m    by monoid_iso_exp
                             = h.id         by above
               or     x ** m = #e           by monoid_iso_eq_id, monoid_exp_element
             But !m. 0 < m /\ m < n ==> x ** m <> #e   by above
             This is a contradiction.

      Thus by [1] and claim, order h y = n  by order_thm
*)
val monoid_iso_order = store_thm(
  "monoid_iso_order",
  ``!(g:'a monoid) (h:'b monoid) f. Monoid g /\ Monoid h /\ MonoidIso f g h ==>
   !x. x IN G ==> (order h (f x) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `y = f x` >>
  Cases_on `n = 0` >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = order h y` >>
    `0 < m` by decide_tac >>
    `h.exp y m = h.id` by metis_tac[order_property] >>
    `f (x ** m) = h.id` by metis_tac[monoid_iso_exp] >>
    `x ** m = #e` by metis_tac[monoid_iso_eq_id, monoid_exp_element] >>
    metis_tac[order_eq_0],
    `0 < n` by decide_tac >>
    `(x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e` by metis_tac[order_thm] >>
    `h.exp y n = h.id` by metis_tac[monoid_iso_exp, monoid_iso_id] >>
    `!m. 0 < m /\ m < n ==> h.exp y m <> h.id` by
  (spose_not_then strip_assume_tac >>
    `f (x ** m) = h.id` by metis_tac[monoid_iso_exp] >>
    `x ** m = #e` by metis_tac[monoid_iso_eq_id, monoid_exp_element] >>
    metis_tac[]) >>
    metis_tac[order_thm]
  ]);

(* Theorem: MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier) *)
(* Proof: by MonoidIso_def, FINITE_BIJ_CARD. *)
val monoid_iso_card_eq = store_thm(
  "monoid_iso_card_eq",
  ``!g:'a monoid h:'b monoid f. MonoidIso f g h /\ FINITE G ==> (CARD G = CARD h.carrier)``,
  metis_tac[MonoidIso_def, FINITE_BIJ_CARD]);

(* ------------------------------------------------------------------------- *)
(* Monoid Automorphisms                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MonoidAuto f g ==> (f #e = #e) *)
(* Proof: by MonoidAuto_def, monoid_iso_id. *)
val monoid_auto_id = store_thm(
  "monoid_auto_id",
  ``!f g. MonoidAuto f g ==> (f #e = #e)``,
  rw_tac std_ss[MonoidAuto_def, monoid_iso_id]);

(* Theorem: MonoidAuto f g ==> !x. x IN G ==> f x IN G *)
(* Proof: by MonoidAuto_def, monoid_iso_element *)
val monoid_auto_element = store_thm(
  "monoid_auto_element",
  ``!f g. MonoidAuto f g ==> !x. x IN G ==> f x IN G``,
  metis_tac[MonoidAuto_def, monoid_iso_element]);

(* Theorem: MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g *)
(* Proof: by MonoidAuto_def, monoid_iso_compose *)
val monoid_auto_compose = store_thm(
  "monoid_auto_compose",
  ``!(g:'a monoid). !f1 f2. MonoidAuto f1 g /\ MonoidAuto f2 g ==> MonoidAuto (f1 o f2) g``,
  metis_tac[MonoidAuto_def, monoid_iso_compose]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n *)
(* Proof: by MonoidAuto_def, monoid_iso_exp *)
val monoid_auto_exp = store_thm(
  "monoid_auto_exp",
  ``!f g. Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> !n. f (x ** n) = (f x) ** n``,
  rw[MonoidAuto_def, monoid_iso_exp]);

(* Theorem: MonoidAuto I g *)
(* Proof:
       MonoidAuto I g
   <=> MonoidIso I g g                by MonoidAuto_def
   <=> MonoidHomo I g g /\ BIJ f G G  by MonoidIso_def
   <=> T /\ BIJ f G G                 by MonoidHomo_def, I_THM
   <=> T /\ T                         by BIJ_I_SAME
*)
val monoid_auto_I = store_thm(
  "monoid_auto_I",
  ``!(g:'a monoid). MonoidAuto I g``,
  rw_tac std_ss[MonoidAuto_def, MonoidIso_def, MonoidHomo_def, BIJ_I_SAME]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g *)
(* Proof:
       MonoidAuto I g
   ==> MonoidIso I g g                by MonoidAuto_def
   ==> MonoidIso (LINV f G) g         by monoid_iso_linv_iso
   ==> MonoidAuto (LINV f G) g        by MonoidAuto_def
*)
val monoid_auto_linv_auto = store_thm(
  "monoid_auto_linv_auto",
  ``!(g:'a monoid) f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (LINV f G) g``,
  rw_tac std_ss[MonoidAuto_def, monoid_iso_linv_iso]);

(* Theorem: MonoidAuto f g ==> f PERMUTES G *)
(* Proof: by MonoidAuto_def, MonoidIso_def *)
val monoid_auto_bij = store_thm(
  "monoid_auto_bij",
  ``!g:'a monoid. !f. MonoidAuto f g ==> f PERMUTES G``,
  rw_tac std_ss[MonoidAuto_def, MonoidIso_def]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> (ord (f x) = ord x) *)
(* Proof: by MonoidAuto_def, monoid_iso_order. *)
val monoid_auto_order = store_thm(
  "monoid_auto_order",
  ``!(g:'a monoid) f. Monoid g /\ MonoidAuto f g ==> !x. x IN G ==> (ord (f x) = ord x)``,
  rw[MonoidAuto_def, monoid_iso_order]);

(* ------------------------------------------------------------------------- *)
(* Submonoids.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Use H to denote h.carrier *)
val _ = overload_on ("H", ``(h:'a monoid).carrier``);

(* Theorem: submonoid h g ==> H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e) *)
(* Proof:
       submonoid h g
   <=> MonoidHomo I h g           by submonoid_def
   <=> (!x. x IN H ==> I x IN G) /\
       (!x y. x IN H /\ y IN H ==> (I (h.op x y) = (I x) * (I y))) /\
       (h.id = I #e)              by MonoidHomo_def
   <=> (!x. x IN H ==> x IN G) /\
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\
       (h.id = #e)                by I_THM
   <=> H SUBSET G
       (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\
       (h.id = #e)                by SUBSET_DEF
*)
val submonoid_eqn = store_thm(
  "submonoid_eqn",
  ``!(g:'a monoid) (h:'a monoid). submonoid h g <=>
     H SUBSET G /\ (!x y. x IN H /\ y IN H ==> (h.op x y = x * y)) /\ (h.id = #e)``,
  rw_tac std_ss[submonoid_def, MonoidHomo_def, SUBSET_DEF]);

(* Theorem: submonoid h g ==> H SUBSET G *)
(* Proof: by submonoid_eqn *)
val submonoid_subset = store_thm(
  "submonoid_subset",
  ``!(g:'a monoid) (h:'a monoid). submonoid h g ==> H SUBSET G``,
  rw_tac std_ss[submonoid_eqn]);

(* Theorem: submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k *)
(* Proof:
   Note H SUBSET G              by submonoid_subset
     or !x. x IN H ==> x IN G   by SUBSET_DEF
   By MonoidHomo_def, this is to show:
   (1) x IN H ==> f x IN k.carrier
       True                     by MonoidHomo_def, MonoidHomo f g k
   (2) x IN H /\ y IN H /\ f (h.op x y) = k.op (f x) (f y)
       Note x IN H ==> x IN G   by above
        and y IN H ==> y IN G   by above
         f (h.op x y)
       = f (x * y)              by submonoid_eqn
       = k.op (f x) (f y)       by MonoidHomo_def
   (3) f h.id = k.id
         f (h.id)
       = f #e                   by submonoid_eqn
       = k.id                   by MonoidHomo_def
*)
val submonoid_homo_homo = store_thm(
  "submonoid_homo_homo",
  ``!(g:'a monoid) (h:'a monoid) (k:'b monoid) f. submonoid h g /\ MonoidHomo f g k ==> MonoidHomo f h k``,
  rw_tac std_ss[submonoid_def, MonoidHomo_def]);

(* Theorem: submonoid g g *)
(* Proof:
   By submonoid_def, this is to show:
   MonoidHomo I g g, true by monoid_homo_I_refl.
*)
val submonoid_refl = store_thm(
  "submonoid_refl",
  ``!g:'a monoid. submonoid g g``,
  rw[submonoid_def, monoid_homo_I_refl]);

(* Theorem: submonoid g h /\ submonoid h k ==> submonoid g k *)
(* Proof:
   By submonoid_def, this is to show:
   MonoidHomo I g h /\ MonoidHomo I h k ==> MonoidHomo I g k
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by monoid_homo_trans
*)
val submonoid_trans = store_thm(
  "submonoid_trans",
  ``!(g h k):'a monoid. submonoid g h /\ submonoid h k ==> submonoid g k``,
  prove_tac[submonoid_def, combinTheory.I_o_ID, monoid_homo_trans]);

(* Theorem: submonoid h g /\ submonoid g h ==> MonoidIso I h g *)
(* Proof:
   By submonoid_def, MonoidIso_def, this is to show:
      MonoidHomo I h g /\ MonoidHomo I g h ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by submonoid_subset, submonoid h g
   (2) x IN G ==> x IN H, true    by submonoid_subset, submonoid g h
*)
val submonoid_I_antisym = store_thm(
  "submonoid_I_antisym",
  ``!(g:'a monoid) h. submonoid h g /\ submonoid g h ==> MonoidIso I h g``,
  rw_tac std_ss[submonoid_def, MonoidIso_def] >>
  fs[MonoidHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: submonoid h g /\ G SUBSET H ==> MonoidIso I h g *)
(* Proof:
   By submonoid_def, MonoidIso_def, this is to show:
      MonoidHomo I h g /\ G SUBSET H ==> BIJ I H G
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN H ==> x IN G, true    by submonoid_subset, submonoid h g
   (2) x IN G ==> x IN H, true    by G SUBSET H, given
*)
val submonoid_carrier_antisym = store_thm(
  "submonoid_carrier_antisym",
  ``!(g:'a monoid) h. submonoid h g /\ G SUBSET H ==> MonoidIso I h g``,
  rpt (stripDup[submonoid_def]) >>
  rw_tac std_ss[MonoidIso_def] >>
  `H SUBSET G` by rw[submonoid_subset] >>
  fs[MonoidHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: Monoid g /\ Monoid h /\ submonoid h g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   Note MonoidHomo I h g          by submonoid_def
   If ord x = 0, to show: order h x = 0.
      By contradiction, suppose order h x <> 0.
      Let n = order h x.
      Then 0 < n                  by n <> 0
       and h.exp x n = h.id       by order_property
        or    x ** n = #e         by monoid_homo_exp, monoid_homo_id, I_THM
       But    x ** n <> #e        by order_eq_0, ord x = 0
      This is a contradiction.
   If ord x <> 0, to show: order h x = ord x.
      Note 0 < ord x              by ord x <> 0
      By order_thm, this is to show:
      (1) h.exp x (ord x) = h.id
            h.exp x (ord x)
          = I (h.exp x (ord x))   by I_THM
          = (I x) ** ord x        by monoid_homo_exp
          = x ** ord x            by I_THM
          = #e                    by order_property
          = I (h.id)              by monoid_homo_id
          = h.id                  by I_THM
      (2) 0 < m /\ m < ord x ==> h.exp x m <> h.id
          By contradiction, suppose h.exp x m = h.id
            h.exp x m
          = I (h.exp x m)         by I_THM
          = (I x) ** m            by monoid_homo_exp
          = x ** m                by I_THM
            h.id = I (h.id)       by I_THM
                 = #e             by monoid_homo_id
         Thus x ** m = #e         by h.exp x m = h.id
          But x ** m <> #e        by order_thm
          This is a contradiction.
*)
val submonoid_order_eqn = store_thm(
  "submonoid_order_eqn",
  ``!(g:'a monoid) h. Monoid g /\ Monoid h /\ submonoid h g ==>
   !x. x IN H ==> (order h x = ord x)``,
  rw[submonoid_def] >>
  `!x. I x = x` by rw[] >>
  Cases_on `ord x = 0` >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `n = order h x` >>
    `0 < n` by decide_tac >>
    `h.exp x n = h.id` by rw[order_property, Abbr`n`] >>
    `x ** n = #e` by metis_tac[monoid_homo_exp, monoid_homo_id] >>
    metis_tac[order_eq_0],
    `0 < ord x` by decide_tac >>
    rw[order_thm] >-
    metis_tac[monoid_homo_exp, order_property, monoid_homo_id] >>
    spose_not_then strip_assume_tac >>
    `x ** m = #e` by metis_tac[monoid_homo_exp, monoid_homo_id] >>
    metis_tac[order_thm]
  ]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of Monoid.                                              *)
(* ------------------------------------------------------------------------- *)

(* Define an operation on images *)
val image_op_def = Define`
   image_op (g:'a monoid) (f:'a -> 'b) x y =  f (CHOICE (preimage f G x) * CHOICE (preimage f G y))
`;

(* Theorem: INJ f G univ(:'b) ==> !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (x * y)) *)
(* Proof:
   Note x = CHOICE (preimage f G (f x))    by preimage_inj_choice
    and y = CHOICE (preimage f G (f y))    by preimage_inj_choice
     image_op g f (f x) (f y)
   = f (CHOICE (preimage f G (f x)) * CHOICE (preimage f G (f y))   by image_op_def
   = f (x * y)                             by above
*)
val image_op_inj = store_thm(
  "image_op_inj",
  ``!g:'a monoid f. INJ f G univ(:'b) ==>
    !x y. x IN G /\ y IN G ==> (image_op g f (f x) (f y) = f (g.op x y))``,
  rw[image_op_def, preimage_inj_choice]);

(* Define the homomorphic image of a monoid. *)
val homo_monoid_def = Define`
  homo_monoid (g:'a monoid) (f:'a -> 'b) =
    <| carrier := IMAGE f G;
            op := image_op g f;
            id := f #e
     |>
`;

(* set overloading *)
val _ = overload_on ("o", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).op``);
val _ = overload_on ("#i", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).id``);
val _ = overload_on ("fG", ``(homo_monoid (g:'a monoid) (f:'a -> 'b)).carrier``);

(* Theorem: Properties of homo_monoid. *)
(* Proof: by homo_monoid_def and image_op_def. *)
val homo_monoid_property = store_thm(
  "homo_monoid_property",
  ``!(g:'a monoid) (f:'a -> 'b). (fG = IMAGE f G) /\
      (!x y. x IN fG /\ y IN fG  ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))) /\
      (#i = f #e)``,
  rw[homo_monoid_def, image_op_def]);

(* Theorem: !x. x IN G ==> f x IN fG *)
(* Proof: by homo_monoid_def, IN_IMAGE *)
val homo_monoid_element = store_thm(
  "homo_monoid_element",
  ``!(g:'a monoid) (f:'a -> 'b). !x. x IN G ==> f x IN fG``,
  rw[homo_monoid_def]);

(* Theorem: f #e = #i *)
(* Proof: by homo_monoid_def *)
val homo_monoid_id = store_thm(
  "homo_monoid_id",
  ``!(g:'a monoid) (f:'a -> 'b). f #e = #i``,
  rw[homo_monoid_def]);

(* Theorem: INJ f G univ(:'b) ==>
            !x y. x IN G /\ y IN G  ==> (f (x * y) = (f x) o (f y)) *)
(* Proof:
   Note x = CHOICE (preimage f G (f x))    by preimage_inj_choice
    and y = CHOICE (preimage f G (f y))    by preimage_inj_choice
     f (x * y)
   = f (CHOICE (preimage f G (f x)) * CHOICE (preimage f G (f y))   by above
   = (f x) o (f y)                         by homo_monoid_property
*)
val homo_monoid_op_inj = store_thm(
  "homo_monoid_op_inj",
  ``!(g:'a monoid) (f:'a -> 'b). INJ f G univ(:'b) ==>
   !x y. x IN G /\ y IN G  ==> (f (x * y) = (f x) o (f y))``,
  rw[homo_monoid_property, preimage_inj_choice]);

(* Theorem: MonoidIso I (homo_monoid g I) g *)
(* Proof:
   Note IMAGE I G = G         by IMAGE_I
    and INJ I G univ(:'a)     by INJ_I
    and !x. I x = x           by I_THM
   By MonoidIso_def, this is to show:
   (1) MonoidHomo I (homo_monoid g I) g
       By MonoidHomo_def, homo_monoid_def, this is to show:
          x IN G /\ y IN G ==> image_op g I x y = x * y
       This is true           by image_op_inj
   (2) BIJ I (homo_group g I).carrier G
         (homo_group g I).carrier
       = IMAGE I G            by homo_monoid_property
       = G                    by above, IMAGE_I
       This is true           by BIJ_I_SAME
*)
val homo_monoid_I = store_thm(
  "homo_monoid_I",
  ``!g:'a monoid. MonoidIso I (homo_monoid g I) g``,
  rpt strip_tac >>
  `IMAGE I G = G` by rw[] >>
  `INJ I G univ(:'a)` by rw[INJ_I] >>
  `!x. I x = x` by rw[] >>
  rw_tac std_ss[MonoidIso_def] >| [
    rw_tac std_ss[MonoidHomo_def, homo_monoid_def] >>
    metis_tac[image_op_inj],
    rw[homo_monoid_property, BIJ_I_SAME]
  ]);

(* Theorem: [Closure] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> x IN fG /\ y IN fG ==> x o y IN fG *)
(* Proof:
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y).
   Then a IN G /\ x = f a      by preimage_choice_property
        b IN G /\ y = f b      by preimage_choice_property
        x o y
      = (f a) o (f b)
      = f (a * b)              by homo_monoid_property
   Note a * b IN G             by monoid_op_element
   so   f (a * b) IN fG        by homo_monoid_element
*)
val homo_monoid_closure = store_thm(
  "homo_monoid_closure",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
     !x y. x IN fG /\ y IN fG ==> x o y IN fG``,
  rw_tac std_ss[homo_monoid_property] >>
  rw[preimage_choice_property]);

(* Theorem: [Associative] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
            x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = x o (y o z) *)
(* Proof:
   By MonoidHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y),
       c = CHOICE (preimage f G z).
   Then a IN G /\ x = f a      by preimage_choice_property
        b IN G /\ y = f b      by preimage_choice_property
        c IN G /\ z = f c      by preimage_choice_property
     (x o y) o z
   = ((f a) o (f b)) o (f c)   by expanding x, y, z
   = f (a * b) o (f c)         by homo_monoid_property
   = f (a * b * c)             by homo_monoid_property
   = f (a * (b * c))           by monoid_assoc
   = (f a) o f (b * c)         by homo_monoid_property
   = (f a) o ((f b) o (f c))   by homo_monoid_property
   = x o (y o z)               by contracting x, y, z
*)
val homo_monoid_assoc = store_thm(
  "homo_monoid_assoc",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
   !x y z. x IN fG /\ y IN fG /\ z IN fG ==> ((x o y) o z = x o (y o z))``,
  rw_tac std_ss[MonoidHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  qabbrev_tac `a = CHOICE (preimage f G x)` >>
  qabbrev_tac `b = CHOICE (preimage f G y)` >>
  qabbrev_tac `c = CHOICE (preimage f G z)` >>
  `a IN G /\ (f a = x)` by metis_tac[preimage_choice_property] >>
  `b IN G /\ (f b = y)` by metis_tac[preimage_choice_property] >>
  `c IN G /\ (f c = z)` by metis_tac[preimage_choice_property] >>
  `a * b IN G /\ b * c IN G ` by rw[] >>
  `a * b * c = a * (b * c)` by rw[monoid_assoc] >>
  metis_tac[]);

(* Theorem: [Identity] Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> #i IN fG /\ #i o x = x /\ x o #i = x. *)
(* Proof:
   By homo_monoid_property, #i = f #e, and #i IN fG.
   Since   CHOICE (preimage f G x) IN G /\ x = f (CHOICE (preimage f G x))   by preimage_choice_property
   hence  #i o x
        = (f #e) o f (preimage f G x)
        = f (#e * preimage f G x)       by homo_monoid_property
        = f (preimage f G x)            by monoid_lid
        = x
   similarly for x o #i = x             by monoid_rid
*)
val homo_monoid_id_property = store_thm(
  "homo_monoid_id_property",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ MonoidHomo f g (homo_monoid g f) ==>
      #i IN fG /\ (!x. x IN fG ==> (#i o x = x) /\ (x o #i = x))``,
  rw[MonoidHomo_def, homo_monoid_property] >-
  metis_tac[monoid_lid, monoid_id_element, preimage_choice_property] >>
  metis_tac[monoid_rid, monoid_id_element, preimage_choice_property]);

(* Theorem: [Commutative] AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
            x IN fG /\ y IN fG ==> (x o y = y o x) *)
(* Proof:
   Note AbelianMonoid g ==> Monoid g and
        !x y. x IN G /\ y IN G ==> (x * y = y * x)          by AbelianMonoid_def
   By MonoidHomo_def,
      !x. x IN G ==> f x IN fG
      !x y. x IN G /\ y IN G ==> (f (x * y) = f x o f y)
   Let a = CHOICE (preimage f G x),
       b = CHOICE (preimage f G y).
   Then a IN G /\ x = f a     by preimage_choice_property
        b IN G /\ y = f b     by preimage_choice_property
     x o y
   = (f a) o (f b)            by expanding x, y
   = f (a * b)                by homo_monoid_property
   = f (b * a)                by AbelianMonoid_def, above
   = (f b) o (f a)            by homo_monoid_property
   = y o x                    by contracting x, y
*)
val homo_monoid_comm = store_thm(
  "homo_monoid_comm",
  ``!(g:'a monoid) (f:'a -> 'b). AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==>
   !x y. x IN fG /\ y IN fG ==> (x o y = y o x)``,
  rw_tac std_ss[AbelianMonoid_def, MonoidHomo_def] >>
  `(fG = IMAGE f G) /\ !x y. x IN fG /\ y IN fG ==> (x o y = f (CHOICE (preimage f G x) * CHOICE (preimage f G y)))` by rw[homo_monoid_property] >>
  qabbrev_tac `a = CHOICE (preimage f G x)` >>
  qabbrev_tac `b = CHOICE (preimage f G y)` >>
  `a IN G /\ (f a = x)` by metis_tac[preimage_choice_property] >>
  `b IN G /\ (f b = y)` by metis_tac[preimage_choice_property] >>
  `a * b = b * a` by rw[] >>
  metis_tac[]);

(* Theorem: Homomorphic image of a monoid is a monoid.
            Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f) *)
(* Proof:
   This is to show each of these:
   (1) x IN fG /\ y IN fG ==> x o y IN fG    true by homo_monoid_closure
   (2) x IN fG /\ y IN fG /\ z IN fG ==> (x o y) o z = (x o y) o z    true by homo_monoid_assoc
   (3) #i IN fG, true by homo_monoid_id_property
   (4) x IN fG ==> #i o x = x, true by homo_monoid_id_property
   (5) x IN fG ==> x o #i = x, true by homo_monoid_id_property
*)
val homo_monoid_monoid = store_thm(
  "homo_monoid_monoid",
  ``!(g:'a monoid) f. Monoid g /\ MonoidHomo f g (homo_monoid g f) ==> Monoid (homo_monoid g f)``,
  rpt strip_tac >>
  rw_tac std_ss[Monoid_def] >| [
    rw[homo_monoid_closure],
    rw[homo_monoid_assoc],
    rw[homo_monoid_id_property],
    rw[homo_monoid_id_property],
    rw[homo_monoid_id_property]
  ]);

(* Theorem: Homomorphic image of an Abelian monoid is an Abelian monoid.
            AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==> AbelianMonoid (homo_monoid g f) *)
(* Proof:
   Note AbelianMonoid g ==> Monoid g               by AbelianMonoid_def
   By AbelianMonoid_def, this is to show:
   (1) Monoid (homo_monoid g f), true               by homo_monoid_monoid, Monoid g
   (2) x IN fG /\ y IN fG ==> x o y = y o x, true   by homo_monoid_comm, AbelianMonoid g
*)
val homo_monoid_abelian_monoid = store_thm(
  "homo_monoid_abelian_monoid",
  ``!(g:'a monoid) f. AbelianMonoid g /\ MonoidHomo f g (homo_monoid g f) ==> AbelianMonoid (homo_monoid g f)``,
  metis_tac[homo_monoid_monoid, AbelianMonoid_def, homo_monoid_comm]);

(* Theorem: Monoid g /\ INJ f G UNIV ==> MonoidHomo f g (homo_monoid g f) *)
(* Proof:
   By MonoidHomo_def, homo_monoid_property, this is to show:
   (1) x IN G ==> f x IN IMAGE f G, true                 by IN_IMAGE
   (2) x IN G /\ y IN G ==> f (x * y) = f x o f y, true  by homo_monoid_op_inj
*)
val homo_monoid_by_inj = store_thm(
  "homo_monoid_by_inj",
  ``!(g:'a monoid) (f:'a -> 'b). Monoid g /\ INJ f G UNIV ==> MonoidHomo f g (homo_monoid g f)``,
  rw_tac std_ss[MonoidHomo_def, homo_monoid_property] >-
  rw[] >>
  rw[homo_monoid_op_inj]);

(* ------------------------------------------------------------------------- *)
(* Weaker form of Homomorphic of Monoid and image of identity.               *)
(* ------------------------------------------------------------------------- *)

(* Let us take out the image of identity requirement *)
val WeakHomo_def = Define`
  WeakHomo (f:'a -> 'b) (g:'a monoid) (h:'b monoid) <=>
    (!x. x IN G ==> f x IN h.carrier) /\
    (!x y. x IN G /\ y IN G ==> (f (x * y) = h.op (f x) (f y)))
    (* no requirement for: f #e = h.id *)
`;

(* A function f from g to h is an isomorphism if f is a bijective homomorphism. *)
val WeakIso_def = Define`
  WeakIso f g h <=> WeakHomo f g h /\ BIJ f G h.carrier
`;

(* Then the best we can prove about monoid identities is the following:
            Monoid g /\ Monoid h /\ WeakIso f g h ==> f #e = h.id
   which is NOT:
            Monoid g /\ Monoid h /\ WeakHomo f g h ==> f #e = h.id
*)

(* Theorem: Monoid g /\ Monoid h /\ WeakIso f g h ==> f #e = h.id *)
(* Proof:
   By monoid_id_unique:
   |- !g. Monoid g ==> !e. e IN G ==> ((!x. x IN G ==> (x * e = x) /\ (e * x = x)) <=> (e = #e)) : thm
   Hence this is to show: !x. x IN h.carrier ==> (h.op x (f #e) = x) /\ (h.op (f #e) x = x)
   Note that WeakIso f g h = WeakHomo f g h /\ BIJ f G h.carrier.
   (1) x IN h.carrier /\ f #e IN h.carrier ==> h.op x (f #e) = x
       Since  x = f y     for some y IN G, by BIJ_THM
       h.op x (f #e) = h.op (f y) (f #e)
                     = f (y * #e)     by WeakHomo_def
                     = f y = x        by monoid_rid
   (2) x IN h.carrier /\ f #e IN h.carrier ==> h.op (f #e) x = x
       Similar to above,
       h.op (f #e) x = h.op (f #e) (f y) = f (#e * y) = f y = x  by monoid_lid.
*)
val monoid_weak_iso_id = store_thm(
  "monoid_weak_iso_id",
  ``!f g h. Monoid g /\ Monoid h /\ WeakIso f g h ==> (f #e = h.id)``,
  rw_tac std_ss[WeakIso_def] >>
  `#e IN G /\ f #e IN h.carrier` by metis_tac[WeakHomo_def, monoid_id_element] >>
  `!x. x IN h.carrier ==> (h.op x (f #e) = x) /\ (h.op (f #e) x = x)` suffices_by rw_tac std_ss[monoid_id_unique] >>
  rpt strip_tac>| [
    `?y. y IN G /\ (f y = x)` by metis_tac[BIJ_THM] >>
    metis_tac[WeakHomo_def, monoid_rid],
    `?y. y IN G /\ (f y = x)` by metis_tac[BIJ_THM] >>
    metis_tac[WeakHomo_def, monoid_lid]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
