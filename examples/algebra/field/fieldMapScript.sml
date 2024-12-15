(* ------------------------------------------------------------------------ *)
(* Field Maps                                                               *)
(* ------------------------------------------------------------------------ *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldMap";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     numberTheory combinatoricsTheory;

open monoidTheory groupTheory ringTheory fieldTheory fieldOrderTheory;

(* ------------------------------------------------------------------------- *)
(* Field Maps Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (r ~~~ r_) f  = Field r /\ Field r_ /\ FieldHomo f r r_
   (r === r_) f  = Field r /\ Field r_ /\ FieldIso f r r_
   (r ~^~ r_) f  = FiniteField r /\ FiniteField r_ /\ FieldHomo f r r_
   (r =^= r_) f  = FiniteField r /\ FiniteField r_ /\ FieldIso f r r_
   f_*           = (r_:'b field).prod excluding r_.sum.id
   F_*           = f_*.carrier
   s <<= r       = Field r /\ Field s /\ subfield s r
   homo_field    = homo_ring
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subfields:
   FieldHomo_def  |- !f r s. FieldHomo f r s <=> RingHomo f r s
   FieldIso_def   |- !f g h. FieldIso f g h <=> FieldHomo f g h /\ BIJ f R s.carrier
   FieldEndo_def  |- !f g. FieldEndo f g <=> FieldHomo f g g
   FieldAuto_def  |- !f g. FieldAuto f g <=> FieldIso f g g
   subfield_def   |- !h g. subfield h g <=> FieldHomo I h g

   Field Homomorphisms:
#  field_homo_zero      |- !r r_ f. (r ~~~ r_) f ==> (f #0 = #0_)
#  field_homo_one       |- !r r_ f. (r ~~~ r_) f ==> (f #1 = #1_)
#  field_homo_ids       |- !r r_ f. (r ~~~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
#  field_homo_element   |- !r r_ f. FieldHomo f r r_ ==> !x. x IN R ==> f x IN R_
   field_homo_eq_ring_homo |- !r r_ f. FieldHomo f r r_ <=> RingHomo f r r_
   field_homo_is_ring_homo |- !r r_ f. (r ~~~ r_) f ==> (r ~r~ r_) f
   field_homo_property  |- !r r_ f. Field r /\ FieldHomo f r r_ ==> !x y. x IN R /\ y IN R ==>
                                    (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   field_homo_cong      |- !r r_ f1 f2. Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                        (FieldHomo f1 r r_ <=> FieldHomo f2 r r_)
   field_homo_add       |- !r r_ f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   field_homo_mult      |- !r r_ f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   field_homo_neg       |- !r r_ f. (r ~~~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   field_homo_sub       |- !r r_ f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   field_homo_num       |- !r r_ f. (r ~~~ r_) f ==> !n. f (##n) = ##_ #1_ n
   field_homo_exp       |- !r r_ f. (r ~~~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   field_homo_unit      |- !r r_ f. (r ~~~ r_) f ==> !x. unit x ==> unit_ (f x)
   field_homo_I_refl    |- !r. FieldHomo I r r
   field_homo_trans     |- !r s t f1 f2. FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t
   field_homo_sym       |- !r r_ f. (r ~~~ r_) f /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r
   field_homo_compose   |- !r s t f1 f2. FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t
   field_homo_linv_homo |- !r r_ f. (r ~~~ r_) f /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r
   field_homo_eq_zero   |- !r r_ f. (r ~~~ r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   field_homo_inv       |- !r r_ f. (r ~~~ r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x))
   field_homo_mult_group_homo |- !r r_ f. (r ~~~ r_) f ==> GroupHomo f f* f_*
   field_homo_map_inj   |- !r r_ f. (r ~~~ r_) f ==> INJ f R R_

   Field Isomorphisms:
   field_iso_zero      |- !r r_ f. (r === r_) f ==> (f #0 = #0_)
   field_iso_one       |- !r r_ f. (r === r_) f ==> (f #1 = #1_)
#  field_iso_ids       |- !r r_ f. (r === r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
   field_iso_element   |- !r r_ f. FieldIso f r r_ ==> !x. x IN R ==> f x IN R_
   field_iso_eq_ring_iso  |- !r r_ f. FieldIso f r r_ <=> RingIso f r r_
   field_iso_is_ring_iso  |- !r r_ f. (r === r_) f ==> (r =r= r_) f
   field_iso_property  |- !r r_ f. Field r /\ FieldIso f r r_ ==> !x y. x IN R /\ y IN R ==>
                                   (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   field_iso_cong      |- !r r_ f1 f2. Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                       (FieldIso f1 r r_ <=> FieldIso f2 r r_)
   field_iso_add       |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   field_iso_mult      |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   field_iso_neg       |- !r r_ f. (r === r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   field_iso_sub       |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   field_iso_num       |- !r r_ f. (r === r_) f ==> !n. f (##n) = ##_ #1_ n
   field_iso_exp       |- !r r_ f. (r === r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   field_iso_unit      |- !r r_ f. (r === r_) f ==> !x. unit x ==> unit_ (f x)
   field_iso_I_refl    |- !r. FieldIso I r r
   field_iso_trans     |- !r s t f1 f2. FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t
   field_iso_sym       |- !r r_ f. (r === r_) f ==> FieldIso (LINV f R) r_ r
   field_iso_compose   |- !r s t f1 f2. FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t
   field_iso_linv_iso  |- !r r_ f. (r === r_) f ==> FieldIso (LINV f R) r_ r
   field_iso_bij       |- !r r_ f. (r === r_) f ==> BIJ f R R_
   field_iso_card_eq   |- !r r_ f. FieldIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)
   field_iso_char_eq   |- !r r_ f. (r === r_) f ==> (char r_ = char r)
   field_iso_eq_zero   |- !r r_ f. (r === r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   field_iso_nonzero   |- !r r_ f. (r === r_) f ==> !x. x IN R+ ==> f x IN R+_
   field_iso_inv       |- !r r_ f. (r === r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x))
   field_iso_eq_one    |- !r r_ f. (r === r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))
   field_iso_inverse_element
                       |- !r r_ f. (r === r_) f ==> !y. y IN R_ ==> LINV f R y IN R /\ (y = f (LINV f R y))
   field_iso_inverse   |- !r r_ f. (r === r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)
   field_iso_element_unique
                       |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))

   field_iso_iso       |- !r s t f1 f2. Field r /\ Field s /\ FieldIso f1 r s /\ FieldIso f2 r t ==>
                                        FieldIso (f2 o LINV f1 R) s t
   field_iso_eq        |- !r s t f. Field r /\ Field s /\ Field t /\ FieldIso f r s /\ FieldIso f r t ==>
                                    FieldIso I s t
   field_iso_I_iso     |- !r s. (r === s) I ==> FieldIso I s r
   field_iso_I_iso_iff |- !r s. Field r /\ Field s ==> (FieldIso I r s <=> FieldIso I s r)
   field_iso_inverse_nonzero
                       |- !r r_ f. (r === r_) f ==> !y. y IN R+_ ==> ?x. x IN R+ /\ (y = f x)
   field_iso_order     |- !r r_ f. (r === r_) f ==> !x. x IN R ==> (forder_ (f x) = forder x)
   field_iso_orders    |- !r r_ f. (r === r_) f ==> !n. IMAGE f (orders f* n) = orders f_* n

   Field Automorphisms:
   field_iso_zero      |- !r f. Field r /\ FieldAuto f r ==> (f #0 = #0)
   field_auto_one      |- !r f. Field r /\ FieldAuto f r ==> (f #1 = #1)
   field_auto_ids      |- !r f. Field r /\ FieldAuto f r ==> (f #0 = #0) /\ (f #1 = #1)
   field_auto_element  |- !r f. FieldAuto f r ==> !x. x IN R ==> f x IN R
   field_auto_eq_ring_auto |- !r f. FieldAuto f r <=> RingAuto f r
   field_auto_cong     |- !r f1 f2. Field r /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                    (FieldAuto f1 r <=> FieldAuto f2 r)
   field_auto_compose    |- !r f1 f2. FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2) r
   field_auto_I          |- !r. FieldAuto I r
   field_auto_linv_auto  |- !r f. Field r /\ FieldAuto f r ==> FieldAuto (LINV f R)
   field_auto_bij        |- !r f. Field r /\ FieldAuto f r ==> f PERMUTES R
   field_auto_order      |- !r f. Field r /\ FieldAuto f r ==>
                            !x. x IN R ==> forder (f x) = forder x
   field_auto_orders     |- !r f. Field r /\ FieldAuto f r ==>
                            !n. IMAGE f (orders f* n) = orders f* n

   Subfields:
   subfield_alt             |- !r s. s <<= r <=> Field r /\ Field s /\ FieldHomo I s r
   subfield_eq_subring      |- !r s. subfield s r <=> subring s r
   subfield_is_subring      |- !r s. s <<= r ==> s <= r
   subfield_element         |- !r s. subfield s r ==> !x. x IN B ==> x IN R
   subfield_carrier_subset  |- !r s. subfield s r ==> B SUBSET R
   subfield_carrier_finite  |- !r s. FiniteField r /\ subfield s r ==> FINITE B
   subfield_finite_field    |- !r s. FiniteField r /\ s <<= r ==> FiniteField s
   subfield_refl            |- !r. subfield r r
   subfield_trans           |- !r s t. subfield r s /\ subfield s t ==> subfield r t
   subfield_I_antisym       |- !r s. subfield s r /\ subfield r s ==> FieldIso I s r
   subfield_carrier_antisym |- !r s. subfield s r /\ R SUBSET B ==> FieldIso I s r
   subfield_by_subring      |- !r s. s <<= r <=> Field r /\ Field s /\ subring s r
   subfield_by_subgroup_submonoid   |- !r s. s <<= r <=> Field r /\ Field s /\
                                             subgroup s.sum r.sum /\ submonoid s.prod r.prod
   subfield_homo_homo       |- !r s r_ f. subfield s r /\ FieldHomo f r r_ ==> FieldHomo f s r_
   subfield_iso_I_subfield  |- !r s. s <<= r ==> !t. Field t /\ FieldIso I t s ==> t <<= r

   Subfield Theorems:
   subfield_zero            |- !r s. s <<= r ==> (s.sum.id = #0)
   subfield_one             |- !r s. s <<= r ==> (s.prod.id = #1)
   subfield_ids             |- !r s. s <<= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)
   subfield_element_alt     |- !r s. s <<= r ==> !x. x IN B ==> x IN R
   subfield_nonzero_element |- !r s. s <<= r ==> !x. x IN B* ==> x IN R+
   subfield_property        |- !r s. Field s /\ subfield s r ==> !x y. x IN B /\ y IN B ==>
                                     (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)
   subfield_add             |- !r s. s <<= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)
   subfield_mult            |- !r s. s <<= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)
   subfield_neg             |- !r s. s <<= r ==> !x. x IN B ==> (s.sum.inv x = -x)
   subfield_sub             |- !r s. s <<= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)
   subfield_num             |- !r s. s <<= r ==> !n. s.sum.exp s.prod.id n = ##n
   subfield_exp             |- !r s. s <<= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n
   subfield_unit            |- !r s. s <<= r ==> !x. Unit s x ==> unit x
   subfield_inv             |- !r s. s <<= r ==> !x. x IN B /\ x <> #0 ==> |/ x IN B
   subfield_char            |- !r s. s <<= r ==> (char s = char r)
   subfield_order           |- !r s. s <<= r ==> !x. x IN B ==> (order s* x = forder x)
   subfield_orders_subset   |- !r s. s <<= r ==> !n. orders s* n SUBSET orders f* n
   subfield_property_alt    |- !r s. s <<= r ==> (!x. x IN B ==> x IN R) /\
                                     (s.sum.id = #0) /\ (s.prod.id = #1) /\
                                     (!x y. x IN B /\ y IN B ==>
                                     (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)) /\
                                     !n. s.sum.exp s.prod.id n = ##n
   subfield_field_iso_compose  |- !r s r_ f. subfield s r /\ FieldIso f r r_ ==> FieldHomo f s r_
   field_homo_iso_homo         |- !f1 f2 f3 f g. FieldHomo f f1 f2 /\ FieldIso g f2 f3 ==>
                                                 FieldHomo (g o f) f1 f3

   Homomorphic Image of Field:
   homo_field_field     |- !r f. Field r /\ FieldHomo f r (homo_field r f) /\ f #1 <> f #0 ==>
                                 Field (homo_field r f)
   homo_field_by_inj    |- !r f. Field r /\ INJ f R univ(:'b) ==> FieldHomo f r (homo_field r f)

   Homomorphic Image between Fields:
   ring_homo_image_field     |- !r r_ f. (r ~~~ r_) f ==> Field (ring_homo_image f r r_)
   field_homo_subfield       |- !r r_ f. (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_
   field_homo_map_image_bij  |- !r r_ f. (r ~~~ r_) f ==> BIJ f R (ring_homo_image f r r_).carrier
   field_homo_image_homo     |- !r r_ f. (r ~~~ r_) f ==> FieldHomo f r (ring_homo_image f r r_)
   field_homo_image_iso      |- !r r_ f. (r ~~~ r_) f ==> FieldIso f r (ring_homo_image f r r_)

   field_homo_subfield_homo  |- !r s r_ f. (r ~~~ r_) f /\ s <<= r ==> (s ~~~ ring_homo_image f s r_) f
   field_iso_subfield_iso    |- !r s r_ f. (r === r_) f /\ s <<= r ==> (s === ring_homo_image f s r_) f
   ring_homo_image_subfield       |- !r r_ f. (r ~~~ r_) f ==> ring_homo_image f r r_ <<= r_
   field_homo_ring_homo_subfield  |- !r r_ f. (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_
   field_iso_ring_homo_subfield   |- !r r_ f. (r === r_) f ==> subfield (ring_homo_image f r r_) r_
   subfield_field_iso_ring_homo_subfield
                                  |- !r s r_ f. s <<= r /\ (r === r_) f ==> ring_homo_image f s r_ <<= r_

   Subset Field:
   subset_field_def       |- !r s. subset_field r s =
                                   <|carrier := s;
                                         sum := <|carrier := s; op := $+; id := #0|>;
                                        prod := <|carrier := s; op := $*; id := #1|>
                                    |>
   subset_field_property  |- !r s. ((subset_field r s).carrier = s) /\
                                   ((subset_field r s).sum.carrier = s) /\
                                   ((subset_field r s).prod.carrier = s) /\
                                   ((subset_field r s).sum.op = $+) /\
                                   ((subset_field r s).sum.id = #0) /\
                                   ((subset_field r s).prod.op = $* ) /\
                                   ((subset_field r s).prod.id = #1)
   subset_field_sum_eq_subset_group_sum    |- !r s. (subset_field r s).sum = subset_group r.sum s
   subset_field_prod_eq_subset_group_prod  |- !r s. (subset_field r s).prod = subset_group r.prod s
   subset_field_sum_exp   |- !r s x. x IN s ==> !n. (subset_field r s).sum.exp x n = r.sum.exp x n
   subset_field_prod_exp  |- !r s x. x IN s ==> !n. (subset_field r s).prod.exp x n = x ** n
   subset_field_sum_num   |- !r s. #1 IN s ==> !n. (subset_field r s).sum.exp (subset_field r s).prod.id n = ##n
   subset_field_order     |- !r s x. x IN s ==> (order ((subset_field r s).prod excluding #0) x = forder x)
   subset_field_char      |- !r s. #1 IN s ==> (char (subset_field r s) = char r)

   Relation to Subset Group:
   subring_add_subset_group_subgroup    |- !r s. s <= r ==> subset_group r.sum s.sum.carrier <= r.sum
   subring_mult_subset_group_submonoid  |- !r s. s <= r ==> subset_group r.prod s.prod.carrier << r.prod
   subfield_add_subset_group_subgroup   |- !r s. s <<= r ==> subset_group r.sum s.sum.carrier <= r.sum
   subfield_mult_subset_group_submonoid |- !r s. s <<= r ==> subset_group r.prod s.prod.carrier << r.prod
   subfield_mult_subset_group_subgroup  |- !r s. s <<= r ==> subset_group f* (s.prod.carrier DIFF {#0}) <= f*
   field_subset_group_subgroup          |- !r. Field r ==> subset_group f* R+ <= f*
   field_subset_group_self              |- !r. Field r ==> (subset_group f* R+ = f* )

   Injective Image of Field:
   field_inj_image_field  |- !r f. Field r /\ INJ f R univ(:'b) ==> Field (ring_inj_image r f)
   field_inj_image_prod_nonzero_monoid
                          |- !r f. Field r /\ INJ f R univ(:'b) ==> Monoid ((ring_inj_image r f).prod excluding f #0)
   field_inj_image_prod_nonzero_group
                          |- !r f. Field r /\ INJ f R univ(:'b) ==> Group ((ring_inj_image r f).prod excluding f #0)
   field_inj_image_field_homo    |- !r f. Field r /\ INJ f R univ(:'b) ==> FieldHomo f r (ring_inj_image r f)
   field_inj_image_finite_field  |- !r f. FiniteField r /\ INJ f R univ(:'b) ==> FiniteField (ring_inj_image r f)


*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subfields.  *)
(* ------------------------------------------------------------------------- *)

(* A function f from r to s is a homomorphism if field properties are preserved. *)
(*
val FieldHomo_def = Define`
  FieldHomo f (r:'a field) (s:'b field) =
     (!x. x IN r.carrier ==> f x IN s.carrier) /\
     GroupHomo f (r.sum) (s.sum) /\
     GroupHomo f f* (s.prod excluding s.sum.id)
`;
*)

(* Actually, a field homomorphism is just a ring homomorphism. *)
val FieldHomo_def = Define`
  FieldHomo f (r:'a field) (s:'b field) <=> RingHomo f r s
`;

(* A function f from r to s is an isomorphism if f is a bijective homomorphism. *)
val FieldIso_def = Define`
  FieldIso f r s <=> FieldHomo f r s /\ BIJ f R s.carrier
`;

(* A field homomorphism from r to r is an endomorphism. *)
val FieldEndo_def = Define `FieldEndo f r <=> FieldHomo f r r`;

(* A field isomorphism from r to r is an automorphism. *)
val FieldAuto_def = Define `FieldAuto f r <=> FieldIso f r r`;

(* A subfield s of r if identity is a homomorphism from s to r *)
val subfield_def = Define `subfield s r <=> FieldHomo I s r`;

(* Overloads for Homomorphism and Isomorphisms with map *)
val _ = overload_on("~~~", ``\(r:'a field) (r_:'b field) f. Field r /\ Field r_ /\ FieldHomo f r r_``);
val _ = overload_on("===", ``\(r:'a field) (r_:'b field) f. Field r /\ Field r_ /\ FieldIso f r r_``);
val _ = overload_on("~^~", ``\(r:'a field) (r_:'b field) f. FiniteField r /\ FiniteField r_ /\ FieldHomo f r r_``);
val _ = overload_on("=^=", ``\(r:'a field) (r_:'b field) f. FiniteField r /\ FiniteField r_ /\ FieldIso f r r_``);
(* make infix operators *)
val _ = set_fixity "~~~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "===" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "~^~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "=^=" (Infix(NONASSOC, 450)); (* same as relation *)

(* Overloads for Field of type 'b *)
val _ = overload_on("f_*", ``(r_:'b field).prod excluding r_.sum.id``);
val _ = overload_on("F_*", ``f_*.carrier``);

(* ------------------------------------------------------------------------- *)
(* Field Homomorphisms                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~~~ r_) f ==> (f #0 = #0_) *)
(* Proof:by FieldHomo_def, ring_homo_zero. *)
val field_homo_zero = store_thm(
  "field_homo_zero",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> (f #0 = #0_)``,
  rw[FieldHomo_def, ring_homo_zero]);

(* Theorem: (r ~~~ r_) f ==> (f #1 = #1_) *)
(* Proof:by FieldHomo_def, ring_homo_one. *)
Theorem field_homo_one:
  !(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> (f #1 = #1_)
Proof rw[FieldHomo_def, ring_homo_one]
QED

(* Theorem: (r ~~~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by field_homo_zero, field_homo_one. *)
Theorem field_homo_ids[simp]:
  !(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
Proof rw_tac std_ss[field_homo_zero, field_homo_one]
QED

(* Theorem: FieldHomo f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by FieldHomo_def, ring_homo_element. *)
val field_homo_element = store_thm(
  "field_homo_element",
  ``!(r:'a field) (r_:'b field) f.
     FieldHomo f r r_ ==> !x. x IN R ==> f x IN R_``,
  metis_tac[FieldHomo_def, ring_homo_element]);

(* Theorem: FieldHomo f r r_ <=> RingHomo f r r_ *)
(* Proof: by FieldHomo_def *)
val field_homo_eq_ring_homo = store_thm(
  "field_homo_eq_ring_homo",
  ``!(r:'a field) (r_:'b field) f. FieldHomo f r r_ <=> RingHomo f r r_``,
  rw[FieldHomo_def]);

(* Theorem: (r ~~~ r_) f ==> (r ~r~ r_) f *)
(* Proof: by FieldHomo_def, field_is_ring *)
val field_homo_is_ring_homo = store_thm(
  "field_homo_is_ring_homo",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> (r ~r~ r_) f``,
  rw_tac std_ss[FieldHomo_def, field_is_ring]);

(* Theorem: Field r /\ FieldHomo f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by FieldHomo_def, ring_homo_property. *)
val field_homo_property = store_thm(
  "field_homo_property",
  ``!(r:'a field) (r_:'b field) f. Field r /\ FieldHomo f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[FieldHomo_def, ring_homo_property]);

(* Theorem: Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (FieldHomo f1 r r_ = FieldHomo f2 r r_) *)
(* Proof: by FieldHomo_def, field_is_ring, ring_homo_cong. *)
val field_homo_cong = store_thm(
  "field_homo_cong",
  ``!(r:'a field) (r_:'b field) f1 f2. Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                 (FieldHomo f1 r r_ = FieldHomo f2 r r_)``,
  metis_tac[FieldHomo_def, field_is_ring, ring_homo_cong]);

(* Theorem: (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by FieldHomo_def, ring_homo_add. *)
val field_homo_add = store_thm(
  "field_homo_add",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[FieldHomo_def, ring_homo_add]);

(* Theorem: (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by FieldHomo_def, ring_homo_mult. *)
val field_homo_mult = store_thm(
  "field_homo_mult",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[FieldHomo_def, ring_homo_mult]);

(* Theorem: (r ~~~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof: by FieldHomo_def and ring_homo_neg. *)
val field_homo_neg = store_thm(
  "field_homo_neg",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[FieldHomo_def, ring_homo_neg]);

(* Theorem: (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y)) *)
(* Proof: by FieldHomo_def, ring_homo_sub. *)
val field_homo_sub = store_thm(
  "field_homo_sub",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y))``,
  rw[FieldHomo_def, ring_homo_sub]);

(* Theorem: (r ~~~ r_) f ==> !n. f ##n = ##_ #1_ n *)
(* Proof: by FieldHomo_def and ring_homo_num. *)
val field_homo_num = store_thm(
  "field_homo_num",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !n. f ##n = ##_ #1_ n``,
  rw[FieldHomo_def, ring_homo_num]);

(* Theorem: (r ~~~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof: by FieldHomo_def and ring_homo_exp. *)
val field_homo_exp = store_thm(
  "field_homo_exp",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rw[FieldHomo_def, ring_homo_exp]);

(* Theorem: (r ~~~ r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof: by field_homo_is_ring_homo, ring_homo_unit *)
val field_homo_unit = store_thm(
  "field_homo_unit",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x. unit x ==> unit_ (f x)``,
  metis_tac[field_homo_is_ring_homo, ring_homo_unit]);

(* Theorem: FieldHomo I r r *)
(* Proof: by FieldHomo_def, ring_homo_I_refl. *)
val field_homo_I_refl = store_thm(
  "field_homo_I_refl",
  ``!r:'a field. FieldHomo I r r``,
  rw[FieldHomo_def, ring_homo_I_refl]);

(* Theorem: FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo f2 o f1 r t *)
(* Proof: by FieldHomo_def, and ring_homo_trans. *)
val field_homo_trans = store_thm(
  "field_homo_trans",
  ``!(r:'a field) (s:'b field) (t:'c field). !f1 f2. FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t``,
  metis_tac[FieldHomo_def, ring_homo_trans]);

(* Theorem: (r ~~~ r_) f /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r *)
(* Proof:
       FieldHomo f r r_
   <=> RingHomo f r r_             by FieldHomo_def
   ==> RingHomo (LINV f R) r_ r    by ring_homo_sym, BIJ f R R_
   <=> FieldHomo (LINV f R) r_ r   by FieldHomo_def
*)
val field_homo_sym = store_thm(
  "field_homo_sym",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r``,
  rw[FieldHomo_def, ring_homo_sym]);

(* Theorem: FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t *)
(* Proof: by FieldHomo_def, ring_homo_compose *)
val field_homo_compose = store_thm(
  "field_homo_compose",
  ``!(r:'a field) (s:'b field) (t:'c field).
   !f1 f2. FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t``,
  metis_tac[FieldHomo_def, ring_homo_compose]);
(* This is the same as field_homo_trans. *)

(* Theorem: Field r /\ Field r_ /\ FieldHomo f r r_ /\ ==> FieldHomo (LINV f R) r_ r *)
(* Proof:
   Note Ring r /\ Ring r_           by field_is_ring
    and RingHomo f r r_             by field_homo_eq_ring_homo
   Thus RingHomo (LINV f R) r_ r    by ring_homo_linv_homo
     or FieldHomo (LINV f R) r_ r   by field_homo_eq_ring_homo
*)
val field_homo_linv_homo = store_thm(
  "field_homo_linv_homo",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r``,
  rw_tac std_ss[field_homo_eq_ring_homo, field_is_ring, ring_homo_linv_homo]);
(* This is the same as field_homo_sym. *)

(* Theorem: (r ~~~ r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof:
   Note that: FieldHomo f r r_ <=> RingHomo f r r_      by FieldHomo_def
   If part: (f x = #0_) ==> (x = #0)
   By contradiction, assume x <> #0.
   Then x IN R+                                  by field_nonzero_eq
   Thus |/ x IN R                                by field_inv_element
   and f ( |/ x) IN s.carrier                    by field_homo_element
   Therefore
   #1_ = f (#1)                                  by field_homo_one
       = f (x * |/ x)                            by field_mult_rinv
       = (f x) *_ (f ( |/ x))                    by field_homo_property
       = #0_ *_ (f ( |/ x))                      by given, f x = #0_
       = #0_                                     by field_mult_lzero
   But Field s ==> #1_ <> #0_                    by field_one_ne_zero
   Hence a contradiction.
   Only-if part: (x = #0) ==> (f x = #0_), true  by field_homo_zero.
*)
val field_homo_eq_zero = store_thm(
  "field_homo_eq_zero",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  rw_tac std_ss[field_homo_zero, EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `|/ x IN R` by rw[] >>
  `f ( |/ x) IN R_` by metis_tac[field_homo_element] >>
  `#1_ = f #1` by rw[field_homo_one] >>
  `_ = f (x * |/ x)` by rw[] >>
  `_ = (f x) *_ (f ( |/ x))` by rw[field_homo_property] >>
  `_ = #0_` by rw[] >>
  metis_tac[field_one_ne_zero]);

(* Theorem: (r ~~~ r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
   x IN R+ ==> |/ x IN R+        by field_inv_nonzero
   hence x IN R /\ |/ x IN R     by field_nonzero_element
   and f x and f ( |/ x) IN R_   by field_homo_element
   and f x IN R+_ /\
       f ( |/ x) IN R+_          by field_homo_eq_zero, field_nonzero_eq
   Therefore
     f ( |/ x) *_ (f x)
   = f ( |/ x * x)               by field_homo_property
   = f #1                        by field_mult_linv
   = #1_                         by field_homo_one
   Hence |/_ (f x) = f ( |/ x)   by field_linv_unique
*)
val field_homo_inv = store_thm(
  "field_homo_inv",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x))``,
  rpt strip_tac >>
  `|/ x IN R+` by rw[field_inv_nonzero] >>
  `x IN R /\ |/ x IN R` by rw[field_nonzero_element] >>
  `f x IN R_ /\ f ( |/ x) IN R_` by metis_tac[field_homo_element] >>
  `f x IN R+_ /\ f ( |/ x) IN R+_` by metis_tac[field_homo_eq_zero, field_nonzero_eq] >>
  `f ( |/ x) *_ (f x) = f ( |/ x * x)` by rw[field_homo_property] >>
  `_ = f #1` by rw[] >>
  `_ = #1_` by rw[field_homo_one] >>
  rw[GSYM field_linv_unique]);

(* Theorem: (r ~~~ r_) f ==> GroupHomo f f* f_* *)
(* Proof:
   By GroupHomo_def, this is to show:
   (1) x IN R /\ FieldHomo f r r_ ==> f x IN R_, true                            by ring_homo_element
   (2) x IN R /\ x <> #0 /\ FieldHomo f r r_ ==> f x <> #0_, true                by field_homo_eq_zero
   (3) x IN R /\ y IN R /\ FieldHomo f r r_ ==> f (x * y) = (f x) *_ (f y), true by ring_homo_property
*)
val field_homo_mult_group_homo = store_thm(
  "field_homo_mult_group_homo",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> GroupHomo f f* f_*``,
  rw[FieldHomo_def, GroupHomo_def, excluding_def] >-
  metis_tac[ring_homo_element, field_is_ring] >-
  metis_tac[field_homo_eq_zero, FieldHomo_def] >>
  rw[ring_homo_property]);

(* Theorem: (r ~~~ r_) f ==> INJ f R R_ *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN R ==> f x IN R_, true     by field_homo_element
   (2) x IN R /\ y IN R /\ f x = f y ==> x = y
       Note f x IN R_ and f y IN R_   by field_homo_element
         f (x - y)
       = (f x) -_ (f y)               by field_homo_sub
       = #0_                          by field_sub_eq, f x = f y
       Hence x - y = #0               by field_homo_eq_zero
          or x = y                    by field_sub_eq_zero
*)
val field_homo_map_inj = store_thm(
  "field_homo_map_inj",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> INJ f R R_``,
  rw[INJ_DEF] >-
  metis_tac[field_homo_element] >>
  `f x IN R_ /\ f y IN R_` by metis_tac[field_homo_element] >>
  `f (x - y) = (f x) -_ (f y)` by rw[field_homo_sub] >>
  `_ = #0_` by rw[] >>
  metis_tac[field_homo_eq_zero, field_sub_eq_zero, field_sub_element]);

(* ------------------------------------------------------------------------- *)
(* Field Isomorphisms                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r === r_) f ==> (f #0 = #0_) *)
(* Proof: by FieldIso_def, field_homo_zero. *)
val field_iso_zero = store_thm(
  "field_iso_zero",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (f #0 = #0_)``,
  rw[FieldIso_def, field_homo_zero]);

(* Theorem: (r === r_) f ==> (f #1 = #1_) *)
(* Proof: by FieldIso_def, field_homo_one. *)
val field_iso_one = store_thm(
  "field_iso_one",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (f #1 = #1_)``,
  rw[FieldIso_def, field_homo_one]);

(* Theorem: (r === r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by field_iso_zero, field_iso_one *)
val field_iso_ids = store_thm(
  "field_iso_ids",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)``,
  rw_tac std_ss[field_iso_zero, field_iso_one]);

(* export simple result *)
val _ = export_rewrites ["field_iso_ids"];

(* Theorem: FieldIso f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by FieldIso_def, field_homo_element. *)
val field_iso_element = store_thm(
  "field_iso_element",
  ``!(r:'a field) (r_:'b field) f. FieldIso f r r_ ==> !x. x IN R ==> f x IN R_``,
  metis_tac[FieldIso_def, field_homo_element]);

(* Theorem: FieldIso f r r_ <=> RingIso f r r_ *)
(* Proof:
       FieldIso f r r_
   <=> FieldHomo f r r_ /\ BIJ f R R_    by FieldIso_def
   <=> RingHomo f r r_ /\ BIJ f R R_     by FieldHomo_def
   <=> RingIso f r r_                    by RingIso_def
*)
val field_iso_eq_ring_iso = store_thm(
  "field_iso_eq_ring_iso",
  ``!(r:'a field) (r_:'b field) f. FieldIso f r r_ <=> RingIso f r r_``,
  rw[FieldIso_def, FieldHomo_def, RingIso_def]);

(* Theorem: (r === r_) f ==> (r =r= r_) f *)
(* Proof:
   Note Field r ==> Ring r                 by field_is_ring
    and Field r_ ==> Ring r_               by field_is_ring
    and FieldIso f r r_ = RingIso f r r_   by field_iso_eq_ring_iso
   Thus (r =r= r_) f                       by notation
*)
val field_iso_is_ring_iso = store_thm(
  "field_iso_is_ring_iso",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (r =r= r_) f``,
  rw[field_iso_eq_ring_iso]);

(* Theorem: Field r /\ FieldIso f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by FieldIso_def, field_homo_property. *)
val field_iso_property = store_thm(
  "field_iso_property",
  ``!(r:'a field) (r_:'b field) f. Field r /\ FieldIso f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[FieldIso_def, field_homo_property]);

(* Theorem: Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (FieldIso f1 r r_ <=> FieldIso f2 r r_) *)
(* Proof:
   Note Field r ==> Ring r                                                   by field_is_ring
    and Field r_ ==> Ring r_                                                 by field_is_ring
     so RingIso f1 r r_ <=> RingIso f2 r r_                                  by ring_iso_cong
     or RingHomo f1 r r_ /\ BIJ f R R_ <=> RingHomo f2 r r_ /\ BIJ f R R_    by RingIso_def
     or FieldHomo f1 r r_ /\ BIJ f R R_ <=> FieldHomo f2 r r_ /\ BIJ f R R_  by FieldHomo_def
     or FieldIso f1 r r_ <=> FieldIso f2 r r_                                by FieldIso_def
*)
val field_iso_cong = store_thm(
  "field_iso_cong",
  ``!(r:'a field) (r_:'b field) f1 f2. Field r /\ Field r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
        (FieldIso f1 r r_ <=> FieldIso f2 r r_)``,
  metis_tac[FieldIso_def, FieldHomo_def, RingIso_def, ring_iso_cong, field_is_ring]);

(* Theorem: (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by FieldIso_def, field_homo_add. *)
val field_iso_add = store_thm(
  "field_iso_add",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[FieldIso_def, field_homo_add]);

(* Theorem: (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by FieldIso_def, field_homo_mult. *)
val field_iso_mult = store_thm(
  "field_iso_mult",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[FieldIso_def, field_homo_mult]);

(* Theorem: (r === r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof: by FieldIso_def, field_homo_neg *)
val field_iso_neg = store_thm(
  "field_iso_neg",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[FieldIso_def, field_homo_neg]);

(* Theorem: (r === r_) f ==> !n. f (##n) = ##_ #1_ n *)
(* Proof: by FieldIso_def, field_homo_num *)
val field_iso_num = store_thm(
  "field_iso_num",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !n. f (##n) = ##_ #1_ n``,
  rw[FieldIso_def, field_homo_num]);

(* Theorem: (r === r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof: by FieldIso_def, field_homo_exp *)
val field_iso_exp = store_thm(
  "field_iso_exp",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rw[FieldIso_def, field_homo_exp]);

(* Theorem: (r === r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_unit *)
val field_iso_unit = store_thm(
  "field_iso_unit",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. unit x ==> unit_ (f x)``,
  metis_tac[FieldIso_def, field_homo_unit]);

(* Theorem: FieldIso I r r *)
(* Proof:
   By FieldIso_def, FieldHomo_def, this is to show:
   RingHomo I r r /\ BIJ I R R, true by ring_iso_I_refl.
*)
val field_iso_I_refl = store_thm(
  "field_iso_I_refl",
  ``!r:'a field. FieldIso I r r``,
  rw[FieldIso_def, field_homo_I_refl, BIJ_I_SAME]);

(* Theorem: FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t
       True by field_homo_trans.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE.
*)
val field_iso_trans = store_thm(
  "field_iso_trans",
  ``!(r:'a field) (s:'b field) (t:'c field). !f1 f2. FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t``,
  rw[FieldIso_def] >-
  metis_tac[field_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: (r === r_) f ==> FieldIso (LINV f R) r_ r *)
(* Proof:
       FieldIso f r r_
   <=> FieldHomo f r r_ /\ BIJ f R R_                     by FieldIso_def
   <=> FieldHomo f r r_ /\ BIJ (LINV f R) R_ R            by BIJ_LINV_BIJ
   <=> FieldHomo (LINV f R) r_ r /\ BIJ (LINV f R) R_ R   by field_homo_sym
   <=> FieldIso (LINV f R) r_ r                           by FieldIso_def
   Or,
   By FieldIso_def, this is to show:
   (1) FieldHomo f r r_ /\ BIJ f R R_ ==> FieldHomo (LINV f R) r_ r, true by field_homo_sym
   (2) BIJ f R R_ ==> BIJ (LINV f R) R_ R, true                           by BIJ_LINV_BIJ
*)
val field_iso_sym = store_thm(
  "field_iso_sym",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> FieldIso (LINV f R) r_ r``,
  rw[FieldIso_def, field_homo_sym, BIJ_LINV_BIJ]);

(* Theorem: FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo f1 r s /\ FieldHomo f2 s t ==> FieldHomo (f2 o f1) r t
       True by field_homo_compose.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE
*)
val field_iso_compose = store_thm(
  "field_iso_compose",
  ``!(r:'a field) (s:'b field) (t:'c field).
   !f1 f2. FieldIso f1 r s /\ FieldIso f2 s t ==> FieldIso (f2 o f1) r t``,
  rw_tac std_ss[FieldIso_def] >-
  metis_tac[field_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as field_iso_trans. *)

(* Theorem: (r === r_) f ==> FieldIso (LINV f R) r_ r *)
(* Proof:
   Note Ring r /\ Ring r_          by field_is_ring
    and RingIso f r r_             by field_iso_eq_ring_iso
   Thus RingIso (LINV f R) r_ r    by ring_iso_linv_iso
     or FieldIso (LINV f R) r_ r   by field_iso_eq_ring_iso
*)
val field_iso_linv_iso = store_thm(
  "field_iso_linv_iso",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> FieldIso (LINV f R) r_ r``,
  rw_tac std_ss[field_iso_eq_ring_iso, field_is_ring, ring_iso_linv_iso]);
(* This is the same as field_iso_sym. *)

(* Theorem: (r === r_) f ==> BIJ f R R_ *)
(* Proof: by FieldIso_def *)
val field_iso_bij = store_thm(
  "field_iso_bij",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> BIJ f R R_``,
  rw_tac std_ss[FieldIso_def]);

(* Theorem: FieldIso f r r_ /\ FINITE R ==> (CARD R = CARD R_) *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_card_eq *)
val field_iso_card_eq = store_thm(
  "field_iso_card_eq",
  ``!(r:'a field) (r_:'b field). !f. FieldIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_card_eq]);

(* Theorem: (r === r_) f ==> (char r_ = char r) *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_char_eq *)
val field_iso_char_eq = store_thm(
  "field_iso_char_eq",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (char r_ = char r)``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_char_eq, field_is_ring]);

(* Theorem: (r === r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_eq_zero *)
val field_iso_eq_zero = store_thm(
  "field_iso_eq_zero",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  metis_tac[field_iso_is_ring_iso, ring_iso_eq_zero]);

(* Theorem: (r === r_) f ==> !x. x IN R+ ==> !x. x IN R+ ==> (f x) IN R+_ *)
(* Proof: by field_iso_is_ring_iso, ring_iso_nonzero *)
val field_iso_nonzero = store_thm(
  "field_iso_nonzero",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R+ ==> (f x) IN R+_``,
  metis_tac[field_iso_is_ring_iso, ring_iso_nonzero]);

(* Theorem: (r === r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
   Note x IN R+ ==> unit x        by field_nonzero_unit
    and (r =r= r_) f              by field_iso_is_ring_iso
   The result follows             by ring_iso_inv
   or simply                      by FieldIso_def, field_homo_inv
*)
val field_iso_inv = store_thm(
  "field_iso_inv",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R+ ==> (f ( |/ x) = |/_ (f x))``,
  rw[FieldIso_def, field_homo_inv]);

(* Theorem: (r === r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1)) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_eq_one *)
val field_iso_eq_one = store_thm(
  "field_iso_eq_one",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))``,
  metis_tac[field_iso_is_ring_iso, ring_iso_eq_one]);

(* Theorem: (r === r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y)) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_inverse_element *)
val field_iso_inverse_element = store_thm(
  "field_iso_inverse_element",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y))``,
  metis_tac[field_iso_is_ring_iso, ring_iso_inverse_element]);

(* Theorem: (r === r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x) *)
(* Proof: by field_iso_inverse_element *)
val field_iso_inverse = store_thm(
  "field_iso_inverse",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)``,
  metis_tac[field_iso_inverse_element]);

(* Theorem: (r === r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y)) *)
(* Proof:
   Note INJ R R_                   by FieldIso_def, BIJ_DEF
   Hence (f x = f y) <=> (x = y)   by INJ_DEF
*)
val field_iso_element_unique = store_thm(
  "field_iso_element_unique",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))``,
  prove_tac[FieldIso_def, BIJ_DEF, INJ_DEF]);

(* Theorem: Field r /\ Field s /\ FieldIso f1 r s /\ FieldIso f2 r t ==> FieldIso (f2 o (LINV f1 R)) s t *)
(* Proof:
       FieldIso f1 r s /\ FieldIso f2 r t
   ==> FieldIso (LINV f R) s r /\ FieldIso f2 r t      by field_iso_sym
   ==> FieldIso (f2 o (LINV f1 R)) s t                 by field_iso_trans
*)
val field_iso_iso = store_thm(
  "field_iso_iso",
  ``!(r:'a field) (s:'b field) (t:'c field) f1 f2.
   Field r /\ Field s /\ FieldIso f1 r s /\ FieldIso f2 r t ==> FieldIso (f2 o (LINV f1 R)) s t``,
  metis_tac[field_iso_sym, field_iso_trans]);

(* Theorem: Field r /\ Field s /\ FieldIso f s r /\ FieldIso f t r ==> FieldIso I s t *)
(* Proof:
   Note FieldIso f r s
    ==> FieldIso (LINV f R) s r        by field_iso_sym
   With FieldIso f r t
    ==> FieldIso (f o LINV f R) s t    by field_iso_trans

   Claim: !x. x IN s.carrier ==> ((f o LINV f R) x = I x)
   Proof: By FUN_EQ_THM, this is to show:
          x IN s.carrier ==> f (LINV f R x) = x
          Since BIJ s.carrier R        by FieldIso_def
             so f (LINV f R x) = x     by BIJ_LINV_THM

   Hence FieldIso I s t                by field_iso_cong
*)
val field_iso_eq = store_thm(
  "field_iso_eq",
  ``!r:'a field (s t):'b field f.
   Field r /\ Field s /\ Field t /\ FieldIso f r s /\ FieldIso f r t ==> FieldIso I s t``,
  rpt strip_tac >>
  `FieldIso (LINV f R) s r` by rw[field_iso_sym] >>
  `FieldIso (f o LINV f R) s t` by metis_tac[field_iso_trans] >>
  `!x. x IN s.carrier ==> ((f o LINV f R) x = I x)` by
  (rw[FUN_EQ_THM] >>
  metis_tac[FieldIso_def, BIJ_LINV_THM]) >>
  metis_tac[field_iso_cong]);

(* Note:
FieldIso I s t ==> s = t cannot be proved,
due to ring_component_equality eventually leads to monoid_component_equality,
that demands things like: $* = f.op, which is not possible for arbitrary arguments.
*)

(* Theorem: Field r /\ Field s /\ FieldIso I r s ==> FieldIso I s r *)
(* Proof:
   Note FieldIso I r s
    ==> FieldIso (LINV I R) s r       by field_iso_sym

   Claim: !x. x IN B ==> ((LINV I R) x = I x)
   Proof: Note BIJ I R B                 by FieldIso_def
           ==> INJ I R B /\ SURJ I R B   by BIJ_DEF
         Hence ?y. y IN R /\ (x = I y)   by SURJ_DEF
           and (LINV I R) (I y) = y      by LINV_DEF
           But x = I y = y               by I_THM
          Thus (LINV I R) x = x = I x

   Hence  FieldIso I s r                 by field_iso_cong, Claim
*)
val field_iso_I_iso = store_thm(
  "field_iso_I_iso",
  ``!(r s):'a field. Field r /\ Field s /\ FieldIso I r s ==> FieldIso I s r``,
  rpt strip_tac >>
  `FieldIso (LINV I R) s r` by rw[field_iso_sym] >>
  `!x. x IN B ==> ((LINV I R) x = I x)` by
  (rpt strip_tac >>
  `INJ I R B /\ SURJ I R B` by metis_tac[FieldIso_def, BIJ_DEF] >>
  `?y. y IN R /\ (x = I y)` by metis_tac[SURJ_DEF] >>
  `(LINV I R) (I y) = y` by metis_tac[LINV_DEF] >>
  rw[]) >>
  metis_tac[field_iso_cong]);

(* Theorem: Field r /\ Field s ==> (FieldIso I r s <=> FieldIso I s r) *)
(* Proof: by field_iso_I_iso *)
val field_iso_I_iso_iff = store_thm(
  "field_iso_I_iso_iff",
  ``!(r s):'a field. Field r /\ Field s ==> (FieldIso I r s <=> FieldIso I s r)``,
  metis_tac[field_iso_I_iso]);

(* Theorem: (r === r_) f ==> !y. y IN R+_ ==> ?x. x IN R+ /\ (y = f x) *)
(* Proof:
   Note y IN R+_ ==> y IN R_ /\ y <> #0_   by field_nonzero_eq
   Thus ?x. x IN R /\ (y = f x)            by field_iso_inverse
    But y <> #0_ ==> x <> #0               by field_iso_eq_zero
   Thus x IN R+                            by field_nonzero_eq
   So take this x.
*)
val field_iso_inverse_nonzero = store_thm(
  "field_iso_inverse_nonzero",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !y. y IN R+_ ==> ?x. x IN R+ /\ (y = f x)``,
  metis_tac[field_nonzero_eq, field_iso_inverse, field_iso_eq_zero]);

(* Theorem: (r === r_) f ==> !x. x IN R ==> (forder_ (f x) = forder x) *)
(* Proof:
   Let n = forder x, y = f x.
   This is to show: forder_ y = n

   If n = 0,
      By contradiction, suppose forder_ y <> 0.
      Let m = forder_ y.
      Then 0 < m                       by m <> 0
      Now    y **_ m = #1_             by field_order_eqn
       or f (x ** m) = #1_             by field_iso_exp
      ==>     x ** m = #1              by field_iso_eq_one, field_exp_element
      But !n. 0 < n ==> x ** n <> #1   by field_order_0
      This is a contradiction.
   If n <> 0,
      Then 0 < n                                 by n <> 0
        so (x ** n = #1) /\
           !m. 0 < m /\ m < n ==> x ** m <> #1   by field_order_thm, 0 < n [1]
      Thus y **_ n = #1_               by field_iso_exp, field_iso_ids

      Claim: !m. 0 < m /\ m < n ==> y **_ m <> #1_
      Proof: By contradiction, suppose y ** m = #1_ .
             Then f (x ** m) = #1_     by field_iso_exp
               or     x ** m = #1      by field_iso_eq_one, field_exp_element
             This contradicts the implication [1].

      Then forder_ y = n               by field_order_thm
*)
val field_iso_order = store_thm(
  "field_iso_order",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !x. x IN R ==> (forder_ (f x) = forder x)``,
  rpt strip_tac >>
  qabbrev_tac `n = forder x` >>
  qabbrev_tac `y = f x` >>
  Cases_on `n = 0` >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = forder_ y` >>
    `0 < m` by decide_tac >>
    `y **_ m = #1_` by metis_tac[field_order_eqn] >>
    `f (x ** m) = #1_` by metis_tac[field_iso_exp] >>
    `x ** m = #1` by metis_tac[field_iso_eq_one, field_exp_element] >>
    metis_tac[field_order_0],
    `0 < n` by decide_tac >>
    `(x ** n = #1) /\ !m. 0 < m /\ m < n ==> x ** m <> #1` by metis_tac[field_order_thm] >>
    `y **_ n = #1_` by metis_tac[field_iso_exp, field_iso_ids] >>
    `!m. 0 < m /\ m < n ==> y **_ m <> #1_` by
  (spose_not_then strip_assume_tac >>
    `f (x ** m) = #1_` by metis_tac[field_iso_exp] >>
    `x ** m = #1` by metis_tac[field_iso_eq_one, field_exp_element] >>
    metis_tac[]) >>
    metis_tac[field_order_thm]
  ]);

(* Theorem: (r === r_) f ==> !n. IMAGE f (orders f* n) = orders f_* n *)
(* Proof:
     IMAGE f (orders f* n)
   = IMAGE f {x | x IN F* /\ (forder x = n)}          by orders_def
   = {f x| (f x) IN (IMAGE f F* ) /\ (forder x = n)}  by IN_IMAGE
   = {f x| (f x) IN F_* /\ (forder x = n)}            by field_iso_nonzero
   = {f x| (f x) IN F_* /\ (forder_ (f x) = n)}       by field_iso_order
   = orders f_* n                                     by orders_def
*)
val field_iso_orders = store_thm(
  "field_iso_orders",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !n. IMAGE f (orders f* n) = orders f_* n``,
  rw[orders_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[field_iso_nonzero, field_mult_carrier] >-
  metis_tac[field_iso_order, field_nonzero_element_alt] >>
  `?y. y IN F* /\ (x = f y)` by metis_tac[field_iso_inverse_nonzero, field_mult_carrier] >>
  metis_tac[field_iso_order, field_nonzero_element_alt]);

(* ------------------------------------------------------------------------- *)
(* Field Automorphisms.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r /\ FieldAuto f r ==> (f #0 = #0) *)
(* Proof: by FieldAuto_def, field_iso_zero. *)
val field_auto_zero = store_thm(
  "field_auto_zero",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> (f #0 = #0)``,
  rw_tac std_ss[FieldAuto_def, field_iso_zero]);

(* Theorem: (r === r_) f ==> (f #1 = #1_) *)
(* Proof: by FieldIso_def, field_homo_one. *)
val field_auto_one = store_thm(
  "field_auto_one",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> (f #1 = #1)``,
  rw[FieldAuto_def, field_iso_one]);

(* Theorem: Field r /\ FieldAuto f r ==> (f #0 = #0) /\ (f #1 = #1) *)
(* Proof: by field_auto_zero, field_auto_one *)
val field_auto_ids = store_thm(
  "field_auto_ids",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> (f #0 = #0) /\ (f #1 = #1)``,
  rw_tac std_ss[field_auto_zero, field_auto_one]);

(* Theorem: FieldAuto f r ==> !x. x IN R ==> f x IN R *)
(* Proof: by FieldAuto_def, field_iso_elemen. *)
val field_auto_element = store_thm(
  "field_auto_element",
  ``!(r:'a field) f. FieldAuto f r ==> !x. x IN R ==> f x IN R``,
  metis_tac[FieldAuto_def, field_iso_element]);

(* Theorem: FieldAuto f r = RingAuto f r *)
(* Proof:
     FieldAuto f r
   = FieldIso f r r     by FieldAuto_def
   = RingIso f r r      by field_iso_eq_ring_iso
   = RingAuto f r       by RingAuto_def
*)
val field_auto_eq_ring_auto = store_thm(
  "field_auto_eq_ring_auto",
  ``!(r:'a field) f. FieldAuto f r = RingAuto f r``,
  rw_tac std_ss[FieldAuto_def, RingAuto_def, field_iso_eq_ring_iso]);

(* Theorem: Field r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (FieldAuto f1 r <=> FieldAuto f2 r) *)
(* Proof: by FieldAuto_def, field_iso_cong. *)
val field_auto_cong = store_thm(
  "field_auto_cong",
  ``!(r:'a field) f1 f2. Field r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (FieldAuto f1 r <=> FieldAuto f2 r)``,
  rw_tac std_ss[FieldAuto_def, field_iso_cong]);

(* Theorem: FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2) r *)
(* Proof: by FieldAuto_def, field_iso_compose *)
val field_auto_compose = store_thm(
  "field_auto_compose",
  ``!(r:'a field). !f1 f2. FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2) r``,
  metis_tac[FieldAuto_def, field_iso_compose]);

(* Theorem: FieldAuto I r *)
(* Proof: by FieldAuto_def, field_iso_I_refl *)
val field_auto_I = store_thm(
  "field_auto_I",
  ``!(r:'a field). FieldAuto I r``,
  rw_tac std_ss[FieldAuto_def, field_iso_I_refl]);

(* Theorem: Field r /\ FieldAuto f r ==> FieldAuto (LINV f R) r *)
(* Proof:
       FieldAuto f r
   ==> FieldIso f r r                by FieldAuto_def
   ==> FieldIso (LINV f R) r         by field_iso_linv_iso
   ==> FieldAuto (LINV f R) r        by FieldAuto_def
*)
val field_auto_linv_auto = store_thm(
  "field_auto_linv_auto",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> FieldAuto (LINV f R) r``,
  rw_tac std_ss[FieldAuto_def, field_iso_linv_iso]);

(* Theorem: Field r /\ FieldAuto f r ==> f PERMUTES R *)
(* Proof: by FieldAuto_def, field_iso_bij *)
val field_auto_bij = store_thm(
  "field_auto_bij",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> f PERMUTES R``,
  rw_tac std_ss[FieldAuto_def, field_iso_bij]);

(* Theorem: Field r /\ FieldAuto f r ==> !x. x IN R ==> (forder (f x) = forder x) *)
(* Proof: by FieldAuto_def, field_iso_order *)
val field_auto_order = store_thm(
  "field_auto_order",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> !x. x IN R ==> (forder (f x) = forder x)``,
  rw[FieldAuto_def, field_iso_order]);

(* Theorem: Field r /\ FieldAuto f r ==> !n. IMAGE f (orders f* n) = orders f* n *)
(* Proof: by FieldAuto_def, field_iso_orders *)
val field_auto_orders = store_thm(
  "field_auto_orders",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> !n. IMAGE f (orders f* n) = orders f* n``,
  rw[FieldAuto_def, field_iso_orders]);

(* ------------------------------------------------------------------------- *)
(* Subfields                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload on subfield situation *)
val _ = overload_on("<<=", ``\s r:'a field. Field r /\ Field s /\ subfield s r``);
val _ = set_fixity "<<=" (Infixl 500); (* same as + in arithmeticScript.sml *)

(* Theorem: s <<= r <=> Field r /\ Field s /\ FieldHomo I s r *)
(* Proof: by subfield_def *)
val subfield_alt = store_thm(
  "subfield_alt",
  ``!(r s):'a field. s <<= r <=> Field r /\ Field s /\ FieldHomo I s r``,
  rw_tac std_ss[subfield_def]);

(* Theorem: subfield s r <=> subring s r *)
(* Proof:
        subfield s r
    <=> FieldHomo I s r       by subfield_def
    <=> RingHomo I s r        by FieldHomo_def
    <=> subring s r           by subring_def
*)
val subfield_eq_subring = store_thm(
  "subfield_eq_subring",
  ``!(r s):'a field. subfield s r <=> subring s r``,
  rw[subfield_def, subring_def, FieldHomo_def]);

(* Theorem: s <<= r ==> s <= r *)
(* Proof:
   Note Field r ==> Ring r            by field_is_ring
        Field s ==> Ring s            by field_is_ring
        subfield s r <=> subring s r  by subfield_eq_subring
*)
val subfield_is_subring = store_thm(
  "subfield_is_subring",
  ``!(r s):'a field. s <<= r ==> s <= r``,
  rw[subfield_eq_subring]);

(* Theorem: subfield s r ==> !x. x IN B ==> x IN R *)
(* Proof: by subfield_eq_subring, subring_element *)
val subfield_element = store_thm(
  "subfield_element",
  ``!(r s):'a field. subfield s r ==> !x. x IN B ==> x IN R``,
  metis_tac[subfield_eq_subring, subring_element]);

(* Theorem: subfield s r ==> B SUBSET R *)
(* Proof: by subfield_element, SUBSET_DEF. *)
val subfield_carrier_subset = store_thm(
  "subfield_carrier_subset",
  ``!(r s):'a field. subfield s r ==> B SUBSET R``,
  metis_tac[subfield_element, SUBSET_DEF]);

(* Theorem: FiniteField r /\ subfield s r ==> FINITE B *)
(* Proof:
   Since FiniteField r ==> FiniteRing r  by finite_field_is_finite_ring
     and subfield s r ==> subring s r    by subfield_eq_subring
   Hence FINITE B                        by subring_carrier_finite
*)
val subfield_carrier_finite = store_thm(
  "subfield_carrier_finite",
  ``!(r s):'a field. FiniteField r /\ subfield s r ==> FINITE B``,
  metis_tac[finite_field_is_finite_ring, subfield_eq_subring, subring_carrier_finite]);

(* Theorem: FiniteField r /\ s <<= r ==> FiniteField s *)
(* Proof:
   Since FINITE B        by subfield_carrier_finite
   Hence FiniteField s   by FiniteField_def
*)
val subfield_finite_field = store_thm(
  "subfield_finite_field",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> FiniteField s``,
  metis_tac[FiniteField_def, subfield_carrier_finite]);;

(* Theorem: subfield r r *)
(* Proof:
   By subfield_def, this is to show:
   FieldHomo I r r, true by field_homo_I_refl.
*)
val subfield_refl = store_thm(
  "subfield_refl",
  ``!r:'a field. subfield r r``,
  rw[subfield_def, field_homo_I_refl]);

(* Theorem: subfield r s /\ subfield s t ==> subfield r t *)
(* Proof:
   By subfield_def, this is to show:
   FieldHomo I r s /\ FieldHomo I s t ==> FieldHomo I r t
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by field_homo_trans
*)
val subfield_trans = store_thm(
  "subfield_trans",
  ``!r s t:'a field. subfield r s /\ subfield s t ==> subfield r t``,
  prove_tac[subfield_def, combinTheory.I_o_ID, field_homo_trans]);

(* Theorem: subfield s r /\ subfield r s ==> FieldIso I s r *)
(* Proof:
   By subfield_def, FieldIso_def, this is to show:
      FieldHomo I s r /\ FiedldHomo I r s ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subfield_carrier_subset, subfield s r
   (2) x IN R ==> x IN B, true    by subfield_carrier_subset, subfield r s
*)
val subfield_I_antisym = store_thm(
  "subfield_I_antisym",
  ``!(r:'a field) s. subfield s r /\ subfield r s ==> FieldIso I s r``,
  rw_tac std_ss[subfield_def, FieldIso_def] >>
  fs[FieldHomo_def, RingHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subfield s r /\ R SUBSET B ==> FieldIso I s r *)
(* Proof:
   By subfield_def, FieldIso_def, this is to show:
      RingHomo I s r /\ R SUBSET B ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subring_carrier_subset, subring s r
   (2) x IN R ==> x IN B, true    by R SUBSET B, given
*)
val subfield_carrier_antisym = store_thm(
  "subfield_carrier_antisym",
  ``!(r:'a field) s. subfield s r /\ R SUBSET B ==> FieldIso I s r``,
  rpt (stripDup[subfield_def]) >>
  rw_tac std_ss[FieldIso_def] >>
  `B SUBSET R` by rw[subfield_carrier_subset] >>
  fs[FieldHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: s <<= r <=> Field r /\ Field s /\ subring s r *)
(* Proof: by subfield_eq_subring *)
val subfield_by_subring = store_thm(
  "subfield_by_subring",
  ``!(r:'a field) (s:'a field). s <<= r <=> Field r /\ Field s /\ subring s r``,
  rw_tac std_ss[subfield_eq_subring]);

(* Theorem: s <<= r <=> Field r /\ Field s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod *)
(* Proof:
   If part: s <<= r ==> Field r /\ Field s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod
      Note s <= r                    by subfield_is_subring
        so subgroup s.sum r.sum      by subring_sum_subgroup
       and submonoid s.prod r.prod   by subring_prod_submonoid
   Only-if part: Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod ==> s <= r
      Note subgroup s.sum r.sum
       ==> s.sum.carrier SUBSET r.sum.carrier   by subgroup_subset
       ==> B SUBSET R                           by field_carriers
       ==> !x. x IN B ==> I x IN R              by SUBSET_DEF, I_THM
       and subgroup s.sum r.sum ==> GroupHomo I s.sum r.sum         by subgroup_def
       and submonoid s.prod r.prod ==> MonoidHomo I s.prod r.prod   by submonoid_def
      Thus RingHomo I s r            by RingHomo_def
        or s <= r                    by subring_def
        or s <<= r                   by subfield_eq_subring
*)
val subfield_by_subgroup_submonoid = store_thm(
  "subfield_by_subgroup_submonoid",
  ``!(r:'a field) (s:'a field). s <<= r <=>
     Field r /\ Field s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod``,
  rw[EQ_IMP_THM] >-
  rw[subfield_is_subring, subring_sum_subgroup] >-
  rw[subfield_is_subring, subring_prod_submonoid] >>
  rw_tac std_ss[subfield_eq_subring, subring_def, RingHomo_def] >-
  metis_tac[subgroup_subset, field_carriers, SUBSET_DEF] >-
  fs[subgroup_def] >>
  fs[submonoid_def]);

(* Theorem: subfield s r /\ FieldHomo f r r_ ==> FieldHomo f s r_ *)
(* Proof:
   Note subfield s r = subring s r             by subfield_eq_subring
   Thus RingHomo f r r_ ==> RingHomo f s r_    by subring_homo_homo
     or FieldHomo f r r_ ==> FieldHomo f s r_  by field_homo_eq_ring_homo
*)
val subfield_homo_homo = store_thm(
  "subfield_homo_homo",
  ``!(r:'a field) (s:'a field) (r_:'b field) f. subfield s r /\ FieldHomo f r r_ ==> FieldHomo f s r_``,
  metis_tac[subring_homo_homo, subfield_eq_subring, field_homo_eq_ring_homo]);

(* Theorem: s <<= r ==> !t:'a field. Field t /\ FieldIso I t s ==> t <<= r *)
(* Proof:
   Note FieldHomo I s r         by subfield_def
   With FieldIso I t s          by given
    ==> FieldHomo I t s         by FieldIso_def
    ==> FieldHomo (I o I) t r   by field_homo_trans
    Now !x. x IN s.carrier ==> ((f o I) x = f x)   by I_THM
     so FieldHomo I t r         by field_homo_cong
     or t <<= r                 by notation
*)
val subfield_iso_I_subfield = store_thm(
  "subfield_iso_I_subfield",
  ``!(r s):'a field. s <<= r ==> !t:'a field. Field t /\ FieldIso I t s ==> t <<= r``,
  rw[subfield_def] >>
  `FieldHomo (I o I) t r` by prove_tac[field_homo_trans, FieldIso_def] >>
  `!x. x IN t.carrier ==> ((I o I) x = I x)` by rw[] >>
  metis_tac[field_homo_cong]);

(* ------------------------------------------------------------------------- *)
(* Subfield Theorems                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s <<= r ==> (s.sum.id = #0) *)
(* Proof: by subfield_is_subring, subring_zero *)
val subfield_zero = store_thm(
  "subfield_zero",
  ``!(r s):'a field. s <<= r ==> (s.sum.id = #0)``,
  rw[subfield_is_subring, subring_zero]);

(* Theorem: s <<= r ==> (s.prod.id = #1) *)
(* Proof: by subfield_is_subring, subring_one *)
val subfield_one = store_thm(
  "subfield_one",
  ``!(r s):'a field. s <<= r ==> (s.prod.id = #1)``,
  rw[subfield_is_subring, subring_one]);

(* Theorem: s <<= r ==> (s.sum.id = #0) /\ (s.prod.id = #1) *)
(* Proof: by subfield_is_subring, subring_ids *)
val subfield_ids = store_thm(
  "subfield_ids",
  ``!(r s):'a field. s <<= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)``,
  rw[subfield_is_subring, subring_ids]);

(* Theorem: s <<= r ==> !x. x IN B ==> x IN R *)
(* Proof: by subfield_is_subring, subring_element_alt. *)
val subfield_element_alt = store_thm(
  "subfield_element_alt",
  ``!(r s):'a field. s <<= r ==> !x. x IN B ==> x IN R``,
  metis_tac[subfield_is_subring, subring_element_alt]);

(* Theorem: s <<= r ==> !x. x IN B* ==> x IN R+ *)
(* Proof:
       x IN B*
   <=> x IN B /\ x <> s.sum.id     by field_nonzero_eq, field_mult_carrier
   <=> x IN B /\ x <> #0           by subfield_zero
   ==> x IN R /\ x <> #0           by subfield_element
   <=> x IN R+                     by field_nonzero_eq
*)
val subfield_nonzero_element = store_thm(
  "subfield_nonzero_element",
  ``!(r:'a field) s. s <<= r ==> !x. x IN B* ==> x IN R+``,
  metis_tac[subfield_element, field_nonzero_eq, subfield_zero, field_mult_carrier]);

(* Theorem: subfield preserves sum and product. *)
(* Proof: by field_is_ring, subfield_eq_subring, subring_property. *)
val subfield_property = store_thm(
  "subfield_property",
  ``!(r s):'a field. Field s /\ subfield s r ==>
     !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)``,
  metis_tac[field_is_ring, subfield_eq_subring, subring_property]);

(* Theorem: s <<= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) *)
(* Proof: by subfield_is_subring, subring_add. *)
val subfield_add = store_thm(
  "subfield_add",
  ``!(r s):'a field. s <<= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)``,
  rw[subfield_is_subring, subring_add]);

(* Theorem: s <<= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y) *)
(* Proof: by subfield_is_subring, subring_mult. *)
val subfield_mult = store_thm(
  "subfield_mult",
  ``!(r s):'a field. s <<= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)``,
  rw[subfield_is_subring, subring_mult]);

(* Theorem: s <<= r ==> !x. x IN B ==> (s.sum.inv x = -x) *)
(* Proof: by subfield_is_subring, subring_neg. *)
val subfield_neg = store_thm(
  "subfield_neg",
  ``!(r s):'a field. s <<= r ==> !x. x IN B ==> (s.sum.inv x = -x)``,
  rw[subfield_is_subring, subring_neg]);

(* Theorem: s <<= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y) *)
(* Proof: by subfield_is_subring, subring_sub. *)
val subfield_sub = store_thm(
  "subfield_sub",
  ``!(r s):'a field. s <<= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)``,
  rw[subfield_is_subring, subring_sub]);

(* Theorem: s <<= r ==> !n. s.sum.exp s.prod.id n = ##n *)
(* Proof: by subfield_is_subring, subring_num. *)
val subfield_num = store_thm(
  "subfield_num",
  ``!(r s):'a field. s <<= r ==> !n. s.sum.exp s.prod.id n = ##n``,
  rw[subfield_is_subring, subring_num]);

(* Theorem: s <<= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n *)
(* Proof: by subfield_is_subring, subring_exp *)
val subfield_exp = store_thm(
  "subfield_exp",
  ``!(r s):'a field. s <<= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n``,
  rw[subfield_is_subring, subring_exp]);

(* Theorem: s <<= r ==> !x. Unit s x ==> unit x *)
(* Proof: by subfield_is_subring, subring_unit *)
val subfield_unit = store_thm(
  "subfield_unit",
  ``!r:'a field s. s <<= r ==> !x. Unit s x ==> unit x``,
  metis_tac[subfield_is_subring, subring_unit]);

(* Theorem: s <<= r ==> !x. x IN B /\ x <> #0 ==> |/ x IN B *)
(* Proof:
   Note x <> s.sum.id           by subfield_zero
    ==> x IN ring_nonzero s     by field_nonzero_eq
    Now FieldHomo I s r                              by subfield_def
    ==> I ((Invertibles s.prod).inv x) = |/ (I x)    by field_homo_inv
     or (Invertibles s.prod).inv x = |/ x            by I_THM
    But (Invertibles s.prod).inv x IN B              by field_inv_element
*)
val subfield_inv = store_thm(
  "subfield_inv",
  ``!(r s):'a field. s <<= r ==> !x. x IN B /\ x <> #0 ==> |/ x IN B``,
  rpt strip_tac >>
  `x IN ring_nonzero s` by metis_tac[subfield_zero, field_nonzero_eq] >>
  `FieldHomo I s r` by rw[GSYM subfield_def] >>
  `(Invertibles s.prod).inv x = |/ x` by metis_tac[field_homo_inv, combinTheory.I_THM] >>
  metis_tac[field_inv_element]);

(* Theorem: s <<= r ==> (char s = char r) *)
(* Proof: by subfield_eq_subring, subring_char *)
val subfield_char = store_thm(
  "subfield_char",
  ``!(r s):'a field. s <<= r ==> (char s = char r)``,
  rw[subfield_eq_subring, subring_char]);

(* Theorem: s <<= r ==> !x. x IN B ==> (order s* x = forder x) *)
(* Proof:
   Note s*.id = f*.id
    <=> s.prod.id = #1                       by excluding_def
    <=> T                                    by subfield_ids
   Also !k.
        s*.exp x k = f*.exp x k
    <=> s.prod.exp x k = x ** k              by field_nonzero_exp
    <=> T                                    by subfield_exp
   The result follows by order_def, period_def.
*)
val subfield_order = store_thm(
  "subfield_order",
  ``!(r:'a field) s. s <<= r ==> !x. x IN B ==> (order s* x = forder x)``,
  rpt strip_tac >>
  `s*.id = f*.id` by rw[excluding_def, subfield_ids] >>
  `!k. s*.exp x k = f*.exp x k` by rw[field_nonzero_exp, subfield_exp] >>
  rw[order_def, period_def]);

(* Theorem: s <<= r ==> !n. (orders s* n) SUBSET (orders f* n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
       x IN orders s* n ==> x IN orders f* n
       x IN orders s* n
   <=> x IN ring_nonzero s /\ (order B* x = n)      by field_orders_element_property
   <=> x IN B /\ x <> s.sum.id /\ (order B* x = n)  by field_nonzero_eq
   ==> x IN B /\ x <> s.sum.id /\ forder x          by subfield_order
   <=> x IN B /\ x <> #0 /\ forder x = n            by subfield_ids
   ==> x IN R /\ x <> #0 /\ forder x = n            by subfield_element
   <=> x IN R+ /\ forder x = n                      by field_nonzero_eq
   <=> x IN orders f* n                             by field_orders_element_property
*)
val subfield_orders_subset = store_thm(
  "subfield_orders_subset",
  ``!(r:'a field) s. s <<= r ==> !n. (orders s* n) SUBSET (orders f* n)``,
  rw[SUBSET_DEF] >>
  metis_tac[subfield_order, field_orders_element_property, subfield_element, field_nonzero_eq, subfield_ids]);

(* Theorem: Properties of subfield: s <<= r ==>
            (!x. x IN B ==> x IN R) /\
            (s.sum.id = #0) /\ (s.prod.id = #1) /\
            (!x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)) /\
            (!n. s.sum.exp s.prod.id n = ##n) *)
(* Proof:
   To show for each property:
   (1) x IN s.carrier ==> x IN R, true by field_homo_element.
   (2) s.sum.id = #0, true by field_homo_zero.
   (3) s.prod.id = #1, true by field_homo_one.
   (4) x IN s.carrier /\ y IN s.carrier ==> s.sum.op x y = x + y, true by field_homo_property.
   (5) x IN s.carrier /\ y IN s.carrier ==> s.prod.op x y = x * y, true by field_homo_property.
   (6) s.sum.exp s.prod.id n = ##n, true by field_homo_num.
*)
val subfield_property_alt = store_thm(
  "subfield_property_alt",
  ``!(r s):'a field. s <<= r ==>
    (!x. x IN B ==> x IN R) /\
    (s.sum.id = #0) /\ (s.prod.id = #1) /\
    (!x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)) /\
    (!n. s.sum.exp s.prod.id n = ##n)``,
  ntac 2 strip_tac >>
  `!x. I x = x` by rw[] >>
  rw[subfield_def] >| [
    metis_tac[field_homo_element],
    metis_tac[field_homo_zero],
    metis_tac[field_homo_one],
    metis_tac[field_homo_property],
    metis_tac[field_homo_property],
    metis_tac[field_homo_num]
  ]);

(* Theorem: subfield s r /\ FieldIso f r r_ ==> FieldHomo f s r_ *)
(* Proof:
   Note subfield s r ==> FieldHomo I s r        by subfield_def
    and FieldIso f r r_  ==> FieldHomo f r r_   by FieldIso_def
   Thus FieldHomo (f o I) s r_                  by field_homo_compose
     or FieldHomo f s r_                        by I_o_ID
*)
val subfield_field_iso_compose = store_thm(
  "subfield_field_iso_compose",
  ``!(r:'a field) (s:'a field) (r_:'b field) f. subfield s r /\ FieldIso f r r_ ==> FieldHomo f s r_``,
  rpt strip_tac >>
  `FieldHomo I s r` by rw[GSYM subfield_def] >>
  `FieldHomo f r r_` by metis_tac[FieldIso_def] >>
  prove_tac[field_homo_compose, combinTheory.I_o_ID]);

(* Theorem: FieldHomo f f1 f2 /\ FieldIso g f2 f3 ==> FieldHomo (g o f) f1 f3 *)
(* Proof:
   Note FieldHomo g f2 f3          by FieldIso_def
     so FieldHomo (g o f) f1 f3    by field_homo_compose
*)
val field_homo_iso_homo = store_thm(
  "field_homo_iso_homo",
  ``!(f1:'a field) (f2:'b field) (f3:'c field) f g.
     FieldHomo f f1 f2 /\ FieldIso g f2 f3 ==> FieldHomo (g o f) f1 f3``,
  metis_tac[field_homo_compose, FieldIso_def]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of Field.                                               *)
(* ------------------------------------------------------------------------- *)

(* Overload homomorphic image of a field. *)
val _ = overload_on("homo_field", ``homo_ring``);

(* Theorem: Field r /\ FieldHomo f r (homo_field r f) /\ f #1 <> f #0 ==> Field (homo_field r f) *)
(* Proof:
   Note Field r ==> Ring r                      by field_is_ring
    and !s. FieldHomo f r s = RingHomo f r s    by FieldHomo_def
   By field_def_by_inv, this is to show:
   (1) Ring (homo_field r f), true              by homo_ring_ring
   (2) (homo_field r f).prod.id <> (homo_field r f).sum.id
       Note (homo_field r f).prod.id = f #1     by homo_ring_property, homo_monoid_def
        and (homo_field r f).sum.id = f #0      by homo_ring_property, homo_monoid_def
       thus true                                by given f #1 <> f #0.
   (3) x IN fR /\ x <> (homo_field r f).sum.id ==>
       ?y. y IN fR /\ ((homo_field r f).prod.op x y = (homo_field r f).prod.id)
       Note (homo_field r f).prod.carrier = fR  by homo_ring_property, homo_monoid_property
        and (homo_field r f).sum.id = f #0      by homo_ring_property, homo_monoid_property
        Now ?a. x = f a /\ a IN R               by homo_ring_property, IN_IMAGE
        and a <> #0                             by x <> (homo_ring r f).sum.id
       Thus a IN R+                             by field_nonzero_eq
        and |/ a IN R /\ (a * |/ a = #1)        by field_inv_element, field_mult_rinv
       Note MonoidHomo f r.prod (homo_field r f).prod   by RingHomo_def
        Let y = f ( |/ a).
       Then y IN (homo_field r f).prod.carrier  by MonoidHomo_def
         or y IN fR                             by above
            (homo_field r f).prod.op x y
          = (homo_field r f).prod.op (f a) (f ( |/ a))    by expanding x, y
          = f (a * |/ a)                        by MonoidHomo_def, field_carriers
          = f #1                                by field_mult_rinv
          = (homo_field r f).prod.id            by MonoidHomo_def
*)
val homo_field_field = store_thm(
  "homo_field_field",
  ``!(r:'a field) f. Field r /\ FieldHomo f r (homo_field r f) /\ f #1 <> f #0 ==> Field (homo_field r f)``,
  rw_tac std_ss[FieldHomo_def] >>
  rw_tac std_ss[field_def_by_inv] >-
  rw[homo_ring_ring] >-
  rw[homo_ring_property, homo_monoid_def] >>
  `(homo_field r f).prod.carrier = fR` by rw[homo_ring_property, homo_monoid_property] >>
  `(homo_field r f).sum.id = f #0` by rw[homo_ring_property, homo_monoid_property] >>
  `?a. (x = f a) /\ a IN R /\ a <> #0` by metis_tac[homo_ring_property, IN_IMAGE] >>
  `a IN R+` by rw[field_nonzero_eq] >>
  `|/ a IN R /\ (a * |/ a = #1)` by rw[] >>
  `MonoidHomo f r.prod (homo_field r f).prod` by metis_tac[RingHomo_def] >>
  metis_tac[MonoidHomo_def, field_carriers]);

(* Theorem: Field r /\ INJ f R UNIV ==> FieldHomo f r (homo_field r f) *)
(* Proof: by FieldHomo_def, homo_ring_by_inj. *)
val homo_field_by_inj = store_thm(
  "homo_field_by_inj",
  ``!(r:'a field) (f:'a -> 'b). Field r /\ INJ f R UNIV ==> FieldHomo f r (homo_field r f)``,
  rw[FieldHomo_def, homo_ring_by_inj]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image between Fields.                                         *)
(* ------------------------------------------------------------------------- *)

(* Try not to do this: overloading for field *)
(* val _ = overload_on ("field_homo_image", ``ring_homo_image``); *)

(* Theorem: (r ~~~ r_) f ==> Field (ring_homo_image f r r_) *)
(* Proof:
   By field_def_by_inv, this is to show:
   (1) Ring (ring_homo_image f r r_)
       Since Field r ==> Ring r                   by field_is_ring
             Field r_ ==> Ring r_                 by field_is_ring
             FieldHomo f r r_ <=> RingHomo f r r_ by FieldHomo_def
       Hence true                                 by ring_homo_image_ring
   (2) (ring_homo_image f r r_).prod.id <> (ring_homo_image f r r_).sum.id
       True by ring_homo_image_def, homo_image_def.
   (3) x' IN R /\ f x' <> #0_ ==>  ?y. (?x. (y = f x) /\ x IN R) /\ (f x' *_ y = #1_)
       f x' <> #0_ ==> x' <> #0               by field_homo_zero
       Let x = |/x IN R                       by field_inv_element, field_nonzero_eq
       Let y = f ( |/x)
       Then this is to show:
       (a) f ( |/ x') <> s.sum.id
           x' <> #0 ==> |/ x' <> #0           by field_inv_nonzero
           Hence f ( |/ x') <> s.sum.id       by field_homo_eq_zero
       (b) f x' *_ f ( |/ x') = #1_
             f x' *_ f ( |/ x')
           = f (x' * |/ x'))                  by field_homo_property
           = f #1                             by field_mult_rinv
           = #1_                              by field_homo_one
*)
Theorem ring_homo_image_field:
  !(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> Field (ring_homo_image f r r_)
Proof
  rpt strip_tac >>
  rw[field_def_by_inv] (* 3 *)
  >- rw[ring_homo_image_ring, GSYM FieldHomo_def]
  >- rw[ring_homo_image_def, homo_image_def] >>
  fs[ring_homo_image_def, homo_image_def, ring_nonzero_def] >>
  rename [‘FieldHomo f r r_’, ‘x = f x'’] >>
  ‘x' <> #0’ by metis_tac[field_homo_zero] >>
  ‘x' IN R+’ by rw[field_nonzero_eq] >>
  ‘|/ x' IN R /\ |/ x' IN R+’ by rw[field_nonzero_eq] >>
  ‘|/ x' <> #0’ by metis_tac[field_nonzero_eq] >>
  simp[PULL_EXISTS] >> qexists_tac ‘|/ x'’ >> rw[] >>
  ‘f x' *_ f ( |/ x') = f (x' * |/ x')’ by rw[field_homo_property] >>
  rw[]
QED

(* Theorem: (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_ *)
(* Proof:
   By subfield_def, this is to show: FieldHomo I (ring_homo_image f r r_) r_
   Expanding by definitions, it all comes down to: x' IN R ==> f x' IN R_
   which is true by field_homo_element.
*)
val field_homo_subfield = store_thm(
  "field_homo_subfield",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_``,
  rw[subfield_def] >>
  `!x. x IN R ==> f x IN R_` by metis_tac[field_homo_element] >>
  rw_tac std_ss[FieldHomo_def, RingHomo_def] >-
  fs[ring_homo_image_def] >-
 (rw[GroupHomo_def, ring_homo_image_def, homo_image_def] >>
  rw[]) >>
  rw[MonoidHomo_def, ring_homo_image_def, homo_image_def] >>
  rw[]);

(* This is similar to: homo_ring_subring *)

(* Theorem: (r ~~~ r_) f ==> BIJ f R (ring_homo_image f r r_).carrier *)
(* Proof:
   Note (r ~~~ r_) f ==> INJ f R R_                       by field_homo_map_inj
   Since (ring_homo_image f r r_).carrier = IMAGE f R     by ring_homo_image_def
   Hence true                                             by INJ_IMAGE_BIJ
*)
val field_homo_map_image_bij = store_thm(
  "field_homo_map_image_bij",
  ``!(r:'a field) (r_:'b field). !f. (r ~~~ r_) f ==> BIJ f R (ring_homo_image f r r_).carrier``,
  rpt strip_tac >>
  `INJ f R R_` by rw[field_homo_map_inj] >>
  `(ring_homo_image f r r_).carrier = IMAGE f R` by rw[ring_homo_image_def] >>
  metis_tac[INJ_IMAGE_BIJ]);

(* Theorem: (r ~~~ r_) f ==> FieldHomo f r (ring_homo_image f r r_ *)
(* Proof:
   By FieldHomo_def and RingHomo_def, this is to show:
   (1) x IN R ==> f x IN (ring_homo_image f r r_).carrier
       True by ring_homo_image_def.
   (2) GroupHomo f r.sum (ring_homo_image f r r_).sum
       Expanding by definitions, this is to show: f (x + y) = f x +_ f y
       True by field_homo_property.
   (3) MonoidHomo f r.prod (ring_homo_image f r r_).prod
       Expanding by definitions, this is to show: f (x * y) = f x *_ f y
       True by field_homo_property.
*)
val field_homo_image_homo = store_thm(
  "field_homo_image_homo",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> FieldHomo f r (ring_homo_image f r r_)``,
  rpt strip_tac >>
  rw_tac std_ss[FieldHomo_def, RingHomo_def] >-
  rw[ring_homo_image_def] >-
  rw[GroupHomo_def, ring_homo_image_def, homo_image_def, field_homo_property] >>
  rw[MonoidHomo_def, ring_homo_image_def, homo_image_def, field_homo_property]);

(* Theorem: (r ~~~ r_) f ==> FieldIso f r (ring_homo_image f r r_) *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo f r (ring_homo_image f r r_), true by field_homo_image_homo
   (2) BIJ f R (ring_homo_image f r r_).carrier, true by field_homo_map_image_bij.
*)
val field_homo_image_iso = store_thm(
  "field_homo_image_iso",
  ``!(r:'a field) (r_:'b field). !f. (r ~~~ r_) f ==> FieldIso f r (ring_homo_image f r r_)``,
  rw[FieldIso_def, field_homo_image_homo, field_homo_map_image_bij]);

(* Theorem: (r ~~~ r_) f /\ s <<= r ==> (s ~~~ (ring_homo_image f s r_)) f *)
(* Proof:
   Note FieldHomo f s r_     by subfield_homo_homo
   This is to show:
   (1) Field (ring_homo_image f s r_), true   by ring_homo_image_field
   (2) FieldHomo f s (ring_homo_image f s r_)
       Note s <= r             by subfield_is_subring
       Thus RingHomo f s r_    by FieldHomo_def
        ==> RingHomo f s (ring_homo_image f s r_)  by ring_homo_image_homo
         or FieldHomo f s (ring_homo_image f s r_) by FieldHomo_def
*)
val field_homo_subfield_homo = store_thm(
  "field_homo_subfield_homo",
  ``!(r:'a field) (s:'a field) (r_:'b field) f.
      (r ~~~ r_) f /\ s <<= r ==> (s ~~~ (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `FieldHomo f s r_` by metis_tac[subfield_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_field] >>
  `s <= r` by rw[subfield_is_subring] >>
  `RingHomo f s r_` by rw[GSYM FieldHomo_def] >>
  `RingHomo f s (ring_homo_image f s r_)` by rw[ring_homo_image_homo] >>
  metis_tac[FieldHomo_def]);

(* Theorem: (r === r_) f /\ s <<= r ==> (s === (ring_homo_image f s r_)) f *)
(* Proof:
   Note FieldHomo f r r_ /\ INJ f R R_    by FieldIso_def
    ==> FieldHomo f s r_                  by subfield_homo_homo
   This is to show:
   (1) Field (ring_homo_image f s r_), true  by ring_homo_image_field
   (2) FieldIso f s (ring_homo_image f s r_)
       Note INJ f R R_                             by BIJ_DEF
        ==> INJ f B R_                             by INJ_SUBSET, subfield_carrier_subset, SUBSET_REFL
       Note RingHomo f s r_                        by FieldHomo_def
       Thus RingIso f s (ring_homo_image f s r_)   by ring_homo_image_iso
         or FieldIso f s (ring_homo_image f s r_)  by field_iso_eq_ring_iso
*)
val field_iso_subfield_iso = store_thm(
  "field_iso_subfield_iso",
  ``!(r:'a field) (s:'a field) (r_:'b field) f.
      (r === r_) f /\ s <<= r ==> (s === (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `FieldHomo f r r_ /\ BIJ f R R_` by metis_tac[FieldIso_def] >>
  `FieldHomo f s r_` by metis_tac[subfield_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_field] >>
  `INJ f B R_` by metis_tac[BIJ_DEF, INJ_SUBSET, subfield_carrier_subset, SUBSET_REFL] >>
  `s <= r` by rw[subfield_is_subring] >>
  `RingHomo f s r_` by rw[GSYM FieldHomo_def] >>
  `RingIso f s (ring_homo_image f s r_)` by rw[ring_homo_image_iso] >>
  rw[field_iso_eq_ring_iso]);

(* have:
ring_homo_image_is_subring |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_
field_homo_subfield        |- !r r_ f. (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_
*)

(* Theorem: (r ~~~ r_) f ==> ring_homo_image f r r_ <<= r_ *)
(* Proof:
   Note Field (ring_homo_image f r r_)   by ring_homo_image_field, (r ~~~ r_) f
    and (r ~r~ r_) f                     by field_homo_eq_ring_homo, field_is_ring
    ==> (ring_homo_image f r r_) <= r_   by ring_homo_image_subring, (r ~r~ r_) f
   Thus (ring_homo_image f r r_) <<= r_  by subfield_eq_subring
*)
val ring_homo_image_subfield = store_thm(
  "ring_homo_image_subfield",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> ring_homo_image f r r_ <<= r_``,
  ntac 4 strip_tac >>
  `Field (ring_homo_image f r r_)` by rw[ring_homo_image_field] >>
  `(r ~r~ r_) f` by rw[GSYM field_homo_eq_ring_homo] >>
  `(ring_homo_image f r r_) <= r_` by rw[ring_homo_image_subring] >>
  rw[subfield_eq_subring]);

(* Theorem alias *)
val field_homo_ring_homo_subfield = save_thm("field_homo_ring_homo_subfield", field_homo_subfield);
(*
val field_homo_ring_homo_subfield = |- !r r_ f. (r ~~~ r_) f ==> subfield (ring_homo_image f r r_) r_: thm
*)

(* Theorem: (r === r_) f ==> subfield (ring_homo_image f r r_) r_ *)
(* Proof:
   Note FieldIso f r r_ ==> FieldHomo f r r_   by FieldIso_def
   Thus subring (ring_homo_image f r r_) r_    by field_homo_ring_homo_subfield
*)
val field_iso_ring_homo_subfield = store_thm(
  "field_iso_ring_homo_subfield",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> subfield (ring_homo_image f r r_) r_``,
  rw_tac std_ss[field_homo_ring_homo_subfield, FieldIso_def]);

(* Theorem: s <<= r /\ (r === r_) f ==> (ring_homo_image f s r_) <<= r_ *)
(* Proof:
   Note FieldHomo f s r_                   by subfield_field_iso_compose
   Thus (s ~~~ r_) f                       by notation, Field s
    ==> (ring_homo_image f s r_) <<= r_    by ring_homo_image_subfield
*)
val subfield_field_iso_ring_homo_subfield = store_thm(
  "subfield_field_iso_ring_homo_subfield",
  ``!(r:'a field) (s:'a field) (r_:'b field) f.
     s <<= r /\ (r === r_) f ==> (ring_homo_image f s r_) <<= r_``,
  metis_tac[ring_homo_image_subfield, subfield_field_iso_compose]);

(* ------------------------------------------------------------------------- *)
(* Subset Field (to be subfield)                                             *)
(* ------------------------------------------------------------------------- *)

(* Define the subset field: takes a subset and gives a field candidate *)
val subset_field_def = Define`
    subset_field (r:'a field) (s:'a -> bool) =
    <| carrier := s;
           sum := <| carrier := s; op := r.sum.op; id := #0 |>;
          prod := <| carrier := s; op := r.prod.op; id := #1 |>
     |>
`;
(* Note: s DELETE #0 = s DIFF {#0}  by DELETE_DEF *)
(* Note: x INSERT s = {x} UNION s   by INSERT_SING_UNION *)

(* Theorem: properties of subset_field *)
(* Proof: by subset_field_def *)
val subset_field_property = store_thm(
  "subset_field_property",
  ``!(r:'a field) s.
     ((subset_field r s).carrier = s) /\
     ((subset_field r s).sum.carrier = s) /\
     ((subset_field r s).prod.carrier = s) /\
     ((subset_field r s).sum.op = r.sum.op) /\
     ((subset_field r s).sum.id = #0) /\
     ((subset_field r s).prod.op = r.prod.op) /\
     ((subset_field r s).prod.id = #1)``,
  rw_tac std_ss[subset_field_def]);

(* Theorem: (subset_field r s).sum = subset_group r.sum s *)
(* Proof: by subset_field_def, subset_group_def *)
val subset_field_sum_eq_subset_group_sum = store_thm(
  "subset_field_sum_eq_subset_group_sum",
  ``!(r:'a field) s. (subset_field r s).sum = subset_group r.sum s``,
  rw[subset_field_def, subset_group_def]);

(* Theorem: (subset_field r s).prod = subset_group r.prod s *)
(* Proof: by subset_field_def, subset_group_def *)
val subset_field_prod_eq_subset_group_prod = store_thm(
  "subset_field_prod_eq_subset_group_prod",
  ``!(r:'a field) s. (subset_field r s).prod = subset_group r.prod s``,
  rw[subset_field_def, subset_group_def]);

(* Theorem: x IN s ==> !n. (subset_field r s).sum.exp x n = r.sum.exp x n *)
(* Proof:
   By induction on n.
   Base: (subset_field r s).sum.exp x 0 = r.sum.exp x 0
          (subset_field r s).sum.exp x 0
        = (subset_field r s).sum.id       by group_exp_0
        = #0                              by subset_field_property
        = r.sum.exp x 0                   by group_exp_0
   Step: x IN s /\ (subset_field r s).sum.exp x n = r.sum.exp x n ==>
         (subset_field r s).sum.exp x (SUC n) = r.sum.exp x (SUC n)
          (subset_field r s).sum.exp x (SUC n)
        = (subset_field r s).sum.op x ((subset_field r s).sum.exp x n)   by group_exp_SUC
        = x + ((subset_field r s).sum.exp x n)                           by subset_field_property
        = x + r.sum.exp x n               by induction hypothesis
        = r.sum.exp x (SUC n)             by group_exp_SUC
*)
val subset_field_sum_exp = store_thm(
  "subset_field_sum_exp",
  ``!(r:'a field) s. !x. x IN s ==> !n. (subset_field r s).sum.exp x n = r.sum.exp x n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[subset_field_property] >>
  rw[subset_field_property]);

(* Theorem: x IN s ==> !n. (subset_field r s).prod.exp x n = x ** n *)
(* Proof:
   By induction on n.
   Base: (subset_field r s).prod.exp x 0 = x ** 0
          (subset_field r s).prod.exp x 0
        = (subset_field r s).prod.id   by group_exp_0
        = #1                           by subset_field_property
        = x ** 0                       by field_exp_0
   Step: x IN s /\ (subset_field r s).prod.exp x n = x ** n ==>
         (subset_field r s).prod.exp x (SUC n) = x ** SUC n
          (subset_field r s).prod.exp x (SUC n)
        = (subset_field r s).prod.op x ((subset_field r s).prod.exp x n)   by group_exp_SUC
        = x * ((subset_field r s).prod.exp x n)                            by subset_field_property
        = x * (x ** n)                 by induction hypothesis
        = x ** SUC n                   by field_exp_SUC
*)
val subset_field_prod_exp = store_thm(
  "subset_field_prod_exp",
  ``!(r:'a field) s. !x. x IN s ==> !n. (subset_field r s).prod.exp x n = x ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[subset_field_property] >>
  rw[subset_field_property]);

(* Theorem: #1 IN s ==> !n. (subset_field r s).sum.exp (subset_field r s).prod.id n = ##n *)
(* Proof: by subset_field_sum_exp, subset_field_property *)
val subset_field_sum_num = store_thm(
  "subset_field_sum_num",
  ``!(r:'a field) s. #1 IN s ==> !n. (subset_field r s).sum.exp (subset_field r s).prod.id n = ##n``,
  rw_tac std_ss[subset_field_sum_exp, subset_field_property]);

(* Theorem: x IN s ==> (order ((subset_field r s).prod excluding #0) x = forder x) *)
(* Proof:
   Let g = (subset_field r s).prod excluding #0.
   Note !k. g.exp x k = f*.exp x k    by group_excluding_exp, subset_field_prod_exp
    and g.id = f*.id                  by excluding_def, subset_field_property
   Thus order g x = forder x          by order_def, period_def
*)
val subset_field_order = store_thm(
  "subset_field_order",
  ``!(r:'a field) s. !x. x IN s ==> (order ((subset_field r s).prod excluding #0) x = forder x)``,
  rw[order_def, period_def] >>
  qabbrev_tac `g = (subset_field r s).prod excluding #0` >>
  `!k. g.exp x k = f*.exp x k` by rw[group_excluding_exp, subset_field_prod_exp, Abbr`g`] >>
  `#e = f*.id` by rw[excluding_def, subset_field_property, Abbr`g`] >>
  rw[]);

(* Theorem: #1 IN s ==> (char (subset_field r s) = char r) *)
(* Proof:
     char (subset_field r s)
   = order (subset_field r s).sum (subset_field r s).prod.id   by char_def
   = order (subset_field r s).sum #1                           by subset_field_property
   = order (subset_group r.sum s) #1      by subset_field_sum_eq_subset_group_sum
   = order r.sum #1                       by subset_group_order, #1 IN s
   = char r                               by char_def
*)
val subset_field_char = store_thm(
  "subset_field_char",
  ``!(r:'a field) s. #1 IN s ==> (char (subset_field r s) = char r)``,
  rw[char_def, subset_field_property] >>
  rw[subset_field_sum_eq_subset_group_sum] >>
  rw[subset_group_order]);

(* Note:
Given a subset s of field elements, to make (subset_field r s) a field
will take some effort: the elements must be chosen so that addition is
closed, as well as closure for multiplication.

Thus a subgroup_field is better: at least multiplication is closed.
However, to ensure addition is also closed, we need to appeal to the
roots of the Master polynomial.
see: ffMasterTheory.subgroup_field_element_iff_master_root

Therefore, subgroup_field is defined and investigated in ffMaster.
*)

(* ------------------------------------------------------------------------- *)
(* Relation to Subset Group                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s <= r ==> (subset_group r.sum s.sum.carrier) <= r.sum *)
(* Proof:
   By subset_group_subgroup, this is to show:
   (1) !x y. x IN s.sum.carrier /\ y IN s.sum.carrier ==> x + -y IN s.sum.carrier
       Note s.sum.carrier = B       by ring_carriers
        and -y = s.sum.inv y        by subring_neg
         so x + -y
          = s.sum.op x (-y)         by subring_add, ring_neg_element
        which is IN B               by ring_add_element
   (2) Group r.sum, true            by ring_add_group
   (3) s.sum.carrier <> {}, true    by ring_carrier_nonempty
   (4) s.sum.carrier SUBSET r.sum.carrier
       Note s.sum.carrier = B       by ring_carriers
        and r.sum.carrier = R       by ring_carriers
        and B SUBSET R              by subring_carrier_subset
*)
val subring_add_subset_group_subgroup = store_thm(
  "subring_add_subset_group_subgroup",
  ``!(r:'a ring) s. s <= r ==> (subset_group r.sum s.sum.carrier) <= r.sum``,
  rpt strip_tac >>
  (irule subset_group_subgroup >> rpt conj_tac) >-
  metis_tac[ring_neg_element, ring_add_element, ring_carriers, subring_neg, subring_add] >-
  rw[ring_add_group] >-
  rw[ring_carrier_nonempty] >>
  rw[subring_carrier_subset]);

(* Theorem: s <= r ==> (subset_group r.prod s.prod.carrier) << r.prod *)
(* Proof:
   By subset_group_submonoid, this is to show:
   (1) !x y. x IN s.prod.carrier /\ y IN s.prod.carrier ==> x * y IN s.prod.carrier
       Note s.prod.carrier = B      by ring_carriers
         so x * y
          = s.prod.op x y           by subring_mult
        which is IN B               by ring_mult_element
   (2) Monoid r.prod, true          by ring_mult_monoid
   (3) #1 IN s.prod.carrier, true   by subring_one, ring_one_element, ring_carriers
   (4) s.prod.carrier SUBSET r.prod.carrier
       Note s.prod.carrier = B      by ring_carriers
        and r.prod.carrier = R      by ring_carriers
        and B SUBSET R              by subring_carrier_subset
*)
val subring_mult_subset_group_submonoid = store_thm(
  "subring_mult_subset_group_submonoid",
  ``!(r:'a ring) s. s <= r ==> Submonoid (subset_group r.prod s.prod.carrier) r.prod``,
  rpt strip_tac >>
  (irule subset_group_submonoid >> rpt conj_tac) >-
  metis_tac[ring_mult_element, ring_carriers, subring_mult] >-
  rw[ring_mult_monoid] >-
  metis_tac[subring_one, ring_one_element, ring_carriers] >>
  rw[subring_carrier_subset]);

(* Theorem: s <<= r ==> (subset_group r.sum s.sum.carrier) <= r.sum *)
(* Proof: by subfield_is_subring, subring_add_subset_group_subgroup *)
val subfield_add_subset_group_subgroup = store_thm(
  "subfield_add_subset_group_subgroup",
  ``!(r:'a field) s. s <<= r ==> (subset_group r.sum s.sum.carrier) <= r.sum``,
  metis_tac[subfield_is_subring, subring_add_subset_group_subgroup]);

(* Theorem: s <<= r ==> (subset_group r.prod s.prod.carrier) << r.prod *)
(* Proof: by subfield_is_subring, subring_mult_subset_group_submonoid *)
val subfield_mult_subset_group_submonoid = store_thm(
  "subfield_mult_subset_group_submonoid",
  ``!(r:'a field) s. s <<= r ==> Submonoid (subset_group r.prod s.prod.carrier) r.prod``,
  metis_tac[subfield_is_subring, subring_mult_subset_group_submonoid]);

(*
> field_homo_inv |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring`` |> ISPEC ``I``;
val it = |- (s ~~~ r) I ==> !x. x IN ring_nonzero s ==> (I ((Invertibles s.prod).inv x) = |/ (I x)): thm
*)

(* Theorem: s <<= r ==> (subset_group f* (s.prod.carrier DIFF {#0})) <= f* *)
(* Proof:
   By subset_group_subgroup, this is to show:
   (1) x IN s.prod.carrier DIFF {#0} /\ y IN s.prod.carrier DIFF {#0} ==>
       f*.op x (f*.inv y) IN s.prod.carrier DIFF {#0}
       After simplifying by group_excluding_property, field_carriers, IN_DIFF, IN_SING,
       this is to show:
       (a) x IN B /\ x <> #0 /\ y IN B /\ y <> #0 ==> x * (f*.inv y) IN B
           Note y IN R+               by subfield_element, field_nonzero_eq
           Thus f*.inv y = |/ y       by field_mult_inv
            ==> |/ y IN B             by subfield_inv
                x * |/ y
              = s.prod.op x ( |/ y)   by subfield_property
                IN B                  by field_mult_element
       (b) x IN B /\ x <> #0 /\ y IN B /\ y <> #0 ==>==> x * (f*.inv y) <> #0
           Note x IN R+               by subfield_element, field_nonzero_eq
            and y IN R+               by subfield_element, field_nonzero_eq
           Thus f*.inv y = |/ y       by field_mult_inv
            and |/ y IN R+            by field_inv_nonzero
            ==> x * |/ y IN R+        by field_mult_nonzero
             or x * |/ y <> #0        by field_nonzero_eq
   (2) Group f*, true                 by field_mult_group
   (3) s.prod.carrier DIFF {#0} <> {}
       Note #1 IN B                   by subfield_ids, field_one_element
        But #1 <> #0                  by field_one_ne_zero
        ==> #1 IN B DIFF {#0}         by DELETE_DEF, IN_DELETE
         or #1 IN s.prod.carrier DIFF {#0}   by field_carriers
         or s.prod.carrier DIFF {#0} <> {}   by MEMBER_NOT_EMPTY
   (4) s.prod.carrier DIFF {#0} SUBSET F*
       By field_carriers, SUBSET_DEF, IN_DIFF, IN_SING,
       this is to show: x IN B /\ x <> #0 ==> x IN F*
       Note x IN R                    by subfield_element
        ==> x IN R+                   by field_nonzero_eq
         or x IN F*                   by field_mult_carrier
*)
val subfield_mult_subset_group_subgroup = store_thm(
  "subfield_mult_subset_group_subgroup",
  ``!(r:'a field) s. s <<= r ==> (subset_group f* (s.prod.carrier DIFF {#0})) <= f*``,
  rpt strip_tac >>
  (irule subset_group_subgroup >> rpt conj_tac) >| [
    rw_tac std_ss[group_excluding_property, field_carriers, IN_DIFF, IN_SING] >| [
      `y IN R+` by metis_tac[subfield_element, field_nonzero_eq] >>
      rw_tac std_ss[field_mult_inv] >>
      `|/ y IN B` by rw[subfield_inv] >>
      metis_tac[subfield_property, field_mult_element],
      `y IN R+` by metis_tac[subfield_element, field_nonzero_eq] >>
      rw_tac std_ss[field_mult_inv] >>
      `x IN R+` by metis_tac[subfield_element, field_nonzero_eq] >>
      `|/ y IN R+` by rw[field_inv_nonzero] >>
      metis_tac[field_mult_nonzero, field_nonzero_eq]
    ],
    rw[field_mult_group],
    `#1 IN B DIFF {#0}` by metis_tac[DELETE_DEF, IN_DELETE, field_one_ne_zero, subfield_ids, field_one_element] >>
    metis_tac[field_carriers, MEMBER_NOT_EMPTY],
    rw_tac std_ss[field_carriers, SUBSET_DEF, IN_DIFF, IN_SING] >>
    metis_tac[subfield_element, field_mult_carrier, field_nonzero_eq]
  ]);

(* Theorem: Field r ==> (subset_group f* R+ <= f* ) *)
(* Proof:
   By subset_group_subgroup, this is to show:
   (1) R+ SUBSET F*, true                    by field_nonzero_subset, field_mult_carrier
   (2) R+ <> {}, true                        by field_nonzero_carrier_nonempty
   (3) Group f*, true                        by field_mult_group
   (4) !x y. x IN R+ /\ y IN R+ ==> f*.op x (f*.inv y) IN R+
       Note f*.op x (f*.inv y) = x * |/ y    by field_nonzero_mult_property, field_mult_inv
       Thus x * |/ y IN R+                   by field_mult_nonzero, field_inv_nonzero
*)
val field_subset_group_subgroup = store_thm(
  "field_subset_group_subgroup",
  ``!r:'a field. Field r ==> (subset_group f* R+ <= f* )``,
  rpt strip_tac >>
  (REVERSE (irule subset_group_subgroup >> rpt conj_tac)) >-
  rw[field_nonzero_subset, field_mult_carrier] >-
  rw[field_nonzero_carrier_nonempty] >-
  rw[field_mult_group] >>
  rw[field_nonzero_mult_property, field_mult_inv]);

(* Theorem: Field r ==> (subset_group f* R+ = f* ) *)
(* Proof:
   Note subset_group f* R+ <= f*             by field_subset_group_subgroup
    and (subset_group f* R+).carrier = R+    by subset_group_property
    ==> subset_group f* R+ = f*              by subgroup_eq_carrier, field_mult_carrier
*)
val field_subset_group_self = store_thm(
  "field_subset_group_self",
  ``!r:'a field. Field r ==> (subset_group f* R+ = f* )``,
  rpt strip_tac >>
  `subset_group f* R+ <= f*` by rw[field_subset_group_subgroup] >>
  `(subset_group f* R+).carrier = R+` by rw[subset_group_property] >>
  metis_tac[subgroup_eq_carrier, field_mult_carrier]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Field.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Field r, and an injective function f,
   then the image (f R) is a Field, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Since a field is a ring, field injective image = ring injective image *)

(* Theorem: Field r /\ INJ f R univ(:'b) ==> Field (ring_inj_image r f) *)
(* Proof:
   By Field_def, this is to show:
   (1) Ring (ring_inj_image r f)
           Field r
       ==> Ring r                              by field_is_ring
       ==> Ring (ring_inj_image r f)           by ring_inj_image_ring

   (2) Group ((ring_inj_image r f).prod excluding (ring_inj_image r f).sum.id)
       Note (ring_inj_image r f).prod
          = monoid_inj_image r.prod f          by ring_inj_image_alt, [1]
        and (ring_inj_image r f).sum.id
         = (monoid_inj_image r.sum f).id       by ring_inj_image_alt
         = f #0                                by monoid_inj_image_def, [2]
       Hence goal is: Group (monoid_inj_image r.prod f excluding f #0).
           Field r
       ==> Group f*                            by Field_def
         = Group (r.prod excluding #0)         by notation
       ==> Group (monoid_inj_image r.prod f excluding f #0)
                                               by group_inj_image_excluding_group

       This is interesting:
       Note F* = R+                            by field_mult_carrier
        and R+ SUBSET R, thus F* SUBSET R      by field_nonzero_subset
         so INJ f F* univ(:'b)                 by INJ_SUBSET
           Field r
       ==> Group f*                            by Field_def
       ==> Group (monoid_inj_image f* f)       by group_inj_image_group
         = Group (monoid_inj_image (r.prod excluding #0) f)
                                               by notation
      However, showing the following not possible with HOL4 functions:
         monoid_inj_image (r.prod excluding #0) f
       = (monoid_inj_image r.prod f) excluding f #0
*)
Theorem field_inj_image_field:
  !(r:'a field) (f:'a -> 'b). Field r /\ INJ f R univ(:'b) ==> Field (ring_inj_image r f)
Proof
  rpt strip_tac >>
  rw[Field_def] >-
  rw[ring_inj_image_ring] >>
  `(ring_inj_image r f).sum.id = f #0` by rw[ring_inj_image_alt, monoid_inj_image_def] >>
  simp[ring_inj_image_alt] >>
  `Group f*` by metis_tac[Field_def] >>
  simp[group_inj_image_excluding_group]
QED

(* The following will be applied to finite fields, for existence and extension. *)

(* Theorem: Field r /\ INJ f R univ(:'b) ==> Monoid ((ring_inj_image r f).prod excluding (f #0)) *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                                    by INJ_IMAGE_BIJ_ALT
     so INJ f R s                                    by BIJ_DEF
   Note !x. x IN R ==> f x IN s                      by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R               by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)          by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)          by BIJ_LINV_THM
    and !x. x IN R ==> ((f x = f #0) <=> (x = #0))   by INJ_DEF, field_zero_element

   Let xx = LINV f R x, yy = LINV f R y, zz = LINV f R z.
   By Monoid_def, ring_inj_image_def, excluding_def, this is to show:
   (1) x IN s /\ y IN s ==> f (xx * yy) IN , true    by field_mult_element
   (2) x IN s /\ y IN s /\ x <> f #0 /\ y <> f #0 ==> f (xx * yy) <> f #0
       Since xx <> #0 /\ yy <> #0, hence true        by field_mult_eq_zero
   (3) x IN s /\ y IN s /\ z IN s ==> f (LINV f R (f (xx * yy)) * zz) = f (xx * LINV f R (f (yy * zz)))
       Since LINV f R (f (xx * yy)) = xx * yy        by field_mult_element
         and LINV f R (f (yy * zz)) = yy * zz        by field_mult_element
       The result follows                            by field_mult_assoc
   (4) f #1 IN s, true                               by field_one_element
   (5) f #1 <> f #0, true since #1 <> #0             by field_one_ne_zero
   (6) x IN s ==> f (LINV f R (f #1) * xx) = x, true by field_mult_lone
   (7) x IN s ==> f (xx * LINV f R (f #1)) = x, true by field_mult_rone
*)
Theorem field_inj_image_prod_nonzero_monoid:
  !(r:'a field) f. Field r /\ INJ f R univ(:'b) ==> Monoid ((ring_inj_image r f).prod excluding (f #0))
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN R ==> ((f x = f #0) <=> (x = #0))` by metis_tac[INJ_DEF, field_zero_element] >>
  rw_tac std_ss[Monoid_def, ring_inj_image_def, excluding_def, IN_DIFF, IN_SING] >-
  rw[] >-
 (`LINV f R x <> #0 /\ LINV f R y <> #0` by metis_tac[] >>
  rw[field_mult_eq_zero]) >-
 (qabbrev_tac `xx = LINV f R x` >>
  qabbrev_tac `yy = LINV f R y` >>
  qabbrev_tac `zz = LINV f R z` >>
  `LINV f R (f (xx * yy)) = xx * yy` by metis_tac[field_mult_element] >>
  `LINV f R (f (yy * zz)) = yy * zz` by metis_tac[field_mult_element] >>
  metis_tac[field_mult_assoc]) >-
  rw[] >-
  metis_tac[field_one_element, field_one_ne_zero] >-
  rw[] >>
  rw[]
QED

(* Theorem: Field r /\ INJ f R univ(:'b) ==> Group ((ring_inj_image r f).prod excluding (f #0)) *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                                    by INJ_IMAGE_BIJ_ALT
     so INJ f R s                                    by BIJ_DEF
   Note !x. x IN R ==> f x IN s                      by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R               by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)          by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)          by BIJ_LINV_THM
    and !x. x IN R ==> ((f x = f #0) <=> (x = #0))   by INJ_DEF, field_zero_element

   Let xx = LINV f R x.
   By Group_def, this is to show:
   (1) Monoid ((ring_inj_image r f).prod excluding f #0), true by field_inj_image_prod_nonzero_monoid
   (2) monoid_invertibles ((ring_inj_image r f).prod excluding f #0) = ((ring_inj_image r f).prod excluding f #0).carrier
       By monoid_invertibles_def, ring_inj_image_def, excluding_def, this is to show:
       x IN s /\ x <> f #0 ==>
         ?y. (y IN s /\ y <> f #0) /\ (f (xx * LINV f R y) = f #1) /\ (f (LINV f R y * xx) = f #1)
       Since xx IN R /\ xx <> #0               by above
          so |/ xx IN R /\ |/ xx <> #0         by field_inv_nonzero, field_nonzero_eq
       Let y = f ( |/ xx).
       Then y IN s /\ y <> f #0                by above
        and LINV f R y = |/ xx                 by above, BIJ_LINV_THM
       Note xx IN R+                           by field_nonzero_eq
         so f (xx * |/ xx) = f #1              by field_mult_rinv
        and f ( |/ xx * xx) = f #1             by field_mult_linv
*)
Theorem field_inj_image_prod_nonzero_group:
  !(r:'a field) f. Field r /\ INJ f R univ(:'b) ==> Group ((ring_inj_image r f).prod excluding (f #0))
Proof
  rw[Group_def] >-
  rw[field_inj_image_prod_nonzero_monoid] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN R ==> ((f x = f #0) <=> (x = #0))` by metis_tac[INJ_DEF, field_zero_element] >>
  rw_tac std_ss[monoid_invertibles_def, ring_inj_image_def, excluding_def, GSPECIFICATION, EXTENSION, IN_DIFF, IN_SING, EQ_IMP_THM] >>
  qabbrev_tac `xx = LINV f R x` >>
  `xx IN R /\ xx <> #0` by metis_tac[] >>
  `|/ xx IN R /\ |/ xx <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
  qexists_tac `f ( |/ xx)` >>
  rw[field_nonzero_eq, field_mult_rinv, field_mult_linv]
QED

(* Theorem: Field r /\ INJ f R univ(:'b) ==> FieldHomo f r (ring_inj_image r f) *)
(* Proof: by ring_inj_image_ring_homo, field_is_ring *)
Theorem field_inj_image_field_homo:
  !(r:'a field) f. Field r /\ INJ f R univ(:'b) ==> FieldHomo f r (ring_inj_image r f)
Proof
  rw[ring_inj_image_ring_homo, FieldHomo_def]
QED

(* Theorem: FiniteField r /\ INJ f R univ(:'b) ==> FiniteField (ring_inj_image r f) *)
(* Proof:
   Note Field r /\ FINITE R                        by FiniteField_def
    ==> Field (ring_inj_image r f)                 by field_inj_image_field
   Also (ring_inj_image r f).carrier = IMAGE f R   by ring_inj_image_carrier
     so FINITE ((ring_inj_image r f).carrier)      by IMAGE_FINITE
     or FiniteField (ring_inj_image r f)           by FiniteField_def
*)
Theorem field_inj_image_finite_field:
  !(r:'a field) f. FiniteField r /\ INJ f R univ(:'b) ==> FiniteField (ring_inj_image r f)
Proof
  metis_tac[FiniteField_def, field_inj_image_field, ring_inj_image_carrier, IMAGE_FINITE]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
