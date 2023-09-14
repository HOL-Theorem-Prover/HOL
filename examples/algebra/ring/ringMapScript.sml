(* ------------------------------------------------------------------------- *)
(* Ring Maps                                                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringMap";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* val _ = load "groupOrderTheory"; (* loads monoidTheory implicitly *) *)
open monoidTheory groupTheory;
open monoidOrderTheory groupOrderTheory;

(* val _ = load "ringUnitTheory"; *)
open ringTheory ringUnitTheory;

(* val _ = load "subgroupTheory"; *)
open submonoidTheory subgroupTheory;
open monoidMapTheory groupMapTheory;

(* val _ = load "quotientGroupTheory"; *)
open quotientGroupTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory;

(* Get arithmetic for Ring characteristics *)
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* Ring Maps Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (r ~r~ r_) f  = Ring r /\ Ring r_ /\ RingHomo f r r_
   (r =r= r_) f  = Ring r /\ Ring r_ /\ RingIso f r r_
   R_            = (r_:'b ring).carrier
   R+_           = ring_nonzero (r_:'b ring)
   #0_           = (r_:'b ring).sum.id
   #1_           = (r_:'b ring).prod.id
   +_            = (r_:'b ring).sum.op
   *_            = (r_:'b ring).prod.op
   -_            = ring_sub (r_:'b ring)
   neg_          = (r_:'b ring).sum.inv
   ##_           = (r_:'b ring).sum.exp
   **_           = (r_:'b ring).prod.exp
   unit_ x       = x IN (Invertibles (r_:'b ring).prod).carrier
   Unit r x      = x IN (Invertibles r.prod).carrier
   |/_           = (Invertibles (r_:'b ring ).prod).inv
   Inv r         = (Invertibles r.prod).inv
   -_            = neg_

   B            = s.carrier
   s <= r       = Ring r /\ Ring s /\ subring s r
   fR           = (homo_ring r f).carrier
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subrings:
   RingHomo_def        |- !f r s. RingHomo f r s <=> (!x. x IN R ==> f x IN s.carrier) /\
                                  GroupHom f r.sum s.sum /\ MonoidHomo f r.prod s.prod
   RingIso_def         |- !f r s. RingIso f r s <=> RingHomo f r s /\ BIJ f R s.carrier
   RingEndo_def        |- !f r. RingEndo f r <=> RingHomo f r r
   RingAuto_def        |- !f r. RingAuto f r <=> RingIso f r r
   subring_def         |- !s r. subring s r <=> RingHomo I s r

   Ring Homomorphisms:
#  ring_homo_zero      |- !r r_ f. (r ~r~ r_) f ==> (f #0 = #0_)
#  ring_homo_one       |- !r r_ f. (r ~r~ r_) f ==> (f #1 = #1_)
#  ring_homo_ids       |- !r r_ f. (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
#  ring_homo_element   |- !r r_ f. RingHomo f r r_ ==> !x. x IN R ==> f x IN R_
   ring_homo_property  |- !r r_ f. Ring r /\ RingHomo f r r_ ==> !x y. x IN R /\ y IN R ==>
                                   (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   ring_homo_cong      |- !r r_ f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                       (RingHomo f1 r r_ <=> RingHomo f2 r r_)
   ring_homo_add       |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   ring_homo_mult      |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   ring_homo_neg       |- !r r_ f. (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   ring_homo_sub       |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   ring_homo_num       |- !r r_ f. (r ~r~ r_) f ==> !n. f (##n) = ##_ #1_ n
   ring_homo_exp       |- !r r_ f. (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   ring_homo_char_divides  |- !r r_ f. (r ~r~ r_) f ==> char r_ divides char r
   ring_homo_I_refl    |- !r. RingHomo I r r
   ring_homo_trans     |- !r s t f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
   ring_homo_sym       |- !r r_ f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r
   ring_homo_compose   |- !r s t f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
   ring_homo_linv_homo |- !r r_ f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r
   ring_homo_eq_zero   |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   ring_homo_one_eq_zero       |- !r r_ f. (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_)
   ring_homo_sum_num_property  |- !r r_ f. (r ~r~ r_) f ==>
                                  !c. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_
   ring_homo_num_nonzero       |- !r r_ f. (r ~r~ r_) f ==>
                                  !c. 0 < c /\ c < char r_ ==> ##c <> #0 /\ f (##c) <> #0_
   ring_homo_unit              |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x)
   ring_homo_unit_nonzero      |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> f x <> #0_
   ring_homo_unit_inv_element  |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_
   ring_homo_unit_inv_nonzero  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> |/_ (f x) <> #0_
   ring_homo_unit_inv          |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> ( |/_ (f x) = f ( |/ x))
   ring_homo_inv               |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))

   Ring Isomorphisms:
   ring_iso_zero       |- !r r_ f. (r =r= r_) f ==> (f #0 = #0_)
   ring_iso_one        |- !r r_ f. (r =r= r_) f ==> (f #1 = #1_)
#  ring_iso_ids        |- !r r_ f. (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
   ring_iso_element    |- !r r_ f. RingIso f r r_ ==> !x. x IN R ==> f x IN R_
   ring_iso_property   |- !r r_ f. Ring r /\ RingIso f r r_ ==> !x y. x IN R /\ y IN R ==>
                                   (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   ring_iso_cong       |- !r r_ f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                       (RingIso f1 r r_ <=> RingIso f2 r r_)
   ring_iso_add        |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   ring_iso_mult       |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   ring_iso_neg        |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   ring_iso_sub        |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   ring_iso_num        |- !r r_ f. (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n
   ring_iso_exp        |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   ring_iso_I_refl     |- !r. RingIso I r r
   ring_iso_trans      |- !r s t f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t
   ring_iso_sym        |- !r r_ f. (r =r= r_) f ==> RingIso (LINV f R) r_ r
   ring_iso_compose    |- !r s t f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t
   ring_iso_linv_iso   |- !r r_ f. (r =r= r_) f ==> RingIso (LINV f R) r_ r
   ring_iso_eq_zero    |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   ring_iso_card_eq    |- !r r_ f. RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)
   ring_iso_char_eq    |- !r r_ f. (r =r= r_) f ==> (char r_ = char r)
   ring_iso_bij        |- !r r_ f. (r =r= r_) f ==> BIJ f R R_
   ring_iso_unit       |- !r r_ f. (r =r= r_) f ==> !x. unit x ==> unit_ (f x)
   ring_iso_nonzero    |- !r r_ f. (r =r= r_) f ==> !x. x IN R+ ==> f x IN R+_
   ring_iso_inv        |- !r r_ f. (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))
   ring_iso_eq_one     |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))
   ring_iso_inverse_element
                       |- !r r_ f. (r =r= r_) f ==> !y. y IN R_ ==> LINV f R y IN R /\ (y = f (LINV f R y))
   ring_iso_inverse    |- !r r_ f. (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)
   ring_iso_element_unique
                       |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))

   Ring Automorphisms:
   ring_auto_zero      |- !r f. Ring r /\ RingAuto f r ==> (f #0 = #0)
   ring_auto_one       |- !r f. Ring r /\ RingAuto f r ==> (f #1 = #1)
   ring_auto_ids       |- !r f. Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1)
   ring_auto_element   |- !r f. RingAuto f r ==> !x. x IN R ==> f x IN R
   ring_auto_cong      |- !r f1 f2. Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                    (RingAuto f1 r <=> RingAuto f2 r)
   ring_auto_compose   |- !r f1 f2. RingAuto f1 r /\ RingAuto f2 r ==> RingAuto (f1 o f2) r
   ring_auto_I         |- !r. RingAuto I r
   ring_auto_linv_auto |- !r f. Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r
   ring_auto_bij       |- !r f. Ring r /\ RingAuto f r ==> f PERMUTES R

   Subrings:
   subring_element         |- !r s. subring s r ==> !x. x IN B ==> x IN R
   subring_carrier_subset  |- !r s. subring s r ==> B SUBSET R
   subring_carrier_finite  |- !r s. FiniteRing r /\ subring s r ==> FINITE B
   subring_finite_ring     |- !r s. FiniteRing r /\ s <= r ==> FiniteRing s
   subring_refl            |- !r. subring r r
   subring_trans           |- !r s t. subring r s /\ subring s t ==> subring r t
   subring_I_antisym       |- !r s. subring s r /\ subring r s ==> RingIso I s r
   subring_carrier_antisym |- !r s. subring s r /\ R SUBSET B ==> RingIso I s r
   subring_sum_subgroup    |- !r s. subring s r ==> subgroup s.sum r.sum
   subring_prod_submonoid  |- !r s. subring s r ==> submonoid s.prod r.prod
   subring_by_subgroup_submonoid |- !r s. s <= r <=>
                              Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod
   subring_homo_homo       |- !r s r_ f. subring s r /\ RingHomo f r r_ ==> RingHomo f s r_

   Subring Theorems:
#  subring_zero          |- !r s. s <= r ==> (s.sum.id = #0)
#  subring_one           |- !r s. s <= r ==> (s.prod.id = #1)
   subring_ids           |- !r s. s <= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)
#  subring_element_alt   |- !r s. s <= r ==> !x. x IN B ==> x IN R
   subring_property      |- !r s. Ring s /\ subring s r ==> !x y. x IN B /\ y IN B ==>
                                  (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)
   subring_add           |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)
   subring_mult          |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)
   subring_neg           |- !r s. s <= r ==> !x. x IN B ==> (s.sum.inv x = -x)
   subring_sub           |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)
   subring_num           |- !r s. s <= r ==> !n. s.sum.exp s.prod.id n = ##n
   subring_exp           |- !r s. s <= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n
   subring_char_divides  |- !r s. s <= r ==> (char r) divides (char s)
   subring_char          |- !r s. s <= r ==> (char s = char r)
   subring_unit          |- !r s. s <= r ==> !x. Unit s x ==> unit x
   subring_unit_nonzero  |- !r s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0
   subring_unit_inv_element |- !r s. s <= r ==> !x. Unit s x ==> Inv s x IN B
   subring_unit_inv_nonzero |- !r s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> Inv s x <> #0
   subring_unit_inv         |- !r s. s <= r ==> !x. Unit s x ==> Inv s x = |/ x
   subring_ring_iso_compose |- !r s r_ f. subring s r /\ RingIso f r r_ ==> RingHomo f s r_

   Homomorphic Image of Ring:
   homo_ring_def       |- !r f. homo_ring r f =
                          <|carrier := IMAGE f R; sum := homo_group r.sum f; prod := homo_group r.prod f|>
   homo_ring_property  |- !r f. (fR = IMAGE f R) /\ ((homo_ring r f).sum = homo_group r.sum f) /\
                                ((homo_ring r f).prod = homo_group r.prod f)
   homo_ring_ring      |- !r f. Ring r /\ RingHomo f r (homo_ring r f) ==> Ring (homo_ring r f)
   homo_ring_subring   |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> subring (homo_ring r f) s
   homo_ring_by_inj    |- !r f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (homo_ring r f)

   Homomorphic Image between Rings:
   ring_homo_image_def    |- !f r r_. ring_homo_image f r r_ =
                                     <|carrier := IMAGE f R;
                                           sum := homo_image f r.sum r_.sum;
                                          prod := homo_image f r.prod r_.prod
                                      |>
   ring_homo_image_carrier          |- !r r_ f. (ring_homo_image f r r_).carrier = IMAGE f R
   ring_homo_image_ring             |- !r r_ f. (r ~r~ r_) f ==> Ring (ring_homo_image f r r_)
   ring_homo_image_subring_subring  |- !r r_ f. (r ~r~ r_) f ==>
                                       !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_
   ring_homo_image_is_subring       |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_
   ring_homo_image_subring          |- !r r_ f. (r ~r~ r_) f ==> ring_homo_image f r r_ <= r_
   ring_homo_image_homo             |- !r r_ f. (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_)
   ring_homo_image_bij              |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                                BIJ f R (ring_homo_image f r r_).carrier
   ring_homo_image_iso              |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                                RingIso f r (ring_homo_image f r r_)
   ring_homo_image_surj_property    |- !r r_ f. Ring r /\ Ring r_ /\ SURJ f R R_ ==>
                                                RingIso I r_ (ring_homo_image f r r_)

   ring_homo_subring_homo       |- !r s r_ f. (r ~r~ r_) f /\ s <= r ==> (s ~r~ ring_homo_image f s r_) f
   ring_iso_subring_iso         |- !r s r_ f. (r =r= r_) f /\ s <= r ==> (s =r= ring_homo_image f s r_) f
   ring_homo_ring_homo_subring  |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_
   ring_iso_ring_homo_subring   |- !r r_ f. (r =r= r_) f ==> subring (ring_homo_image f r r_) r_
   subring_ring_iso_ring_homo_subring
                                |- !r s r_ f. s <= r /\ (r =r= r_) f ==> ring_homo_image f s r_ <= r_

   Injective Image of Ring:
   ring_inj_image_def           |- !r f. Ring r ==> ring_inj_image r f =
      <|carrier := IMAGE f R;
            sum := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x + LINV f R y)); id := f #0|>;
           prod := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x * LINV f R y)); id := f #1|>
       |>
   ring_inj_image_carrier       |- !r f. (ring_inj_image r f).carrier = IMAGE f R
   ring_inj_image_alt           |- !f r. Ring r ==> ring_inj_image r f =
                                         <|carrier := IMAGE f R;
                                               sum := monoid_inj_image r.sum f;
                                              prod := monoid_inj_image r.prod f
                                          |>
   ring_inj_image_ring          |- !r f. Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f)
   ring_inj_image_sum_monoid    |- !r f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum
   ring_inj_image_sum_group     |- !r f. Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum
   ring_inj_image_sum_abelian_group
                                |- !r f. Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum
   ring_inj_image_prod_monoid   |- !r f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod
   ring_inj_image_prod_abelian_monoid
                                |- !r f. Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod
   ring_inj_image_sum_group_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum
   ring_inj_image_prod_monoid_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod
   ring_inj_image_ring_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subrings.   *)
(* ------------------------------------------------------------------------- *)

(* A function f from r to s is a homomorphism if ring properties are preserved. *)
val RingHomo_def = Define`
  RingHomo f (r:'a ring) (s:'b ring) <=>
     (!x. x IN r.carrier ==> f x IN s.carrier) /\
     GroupHomo f (r.sum) (s.sum) /\
     MonoidHomo f (r.prod) (s.prod)
`;

(* A function f from r to s is an isomorphism if f is a bijective homomorphism. *)
val RingIso_def = Define `
  RingIso f r s <=> RingHomo f r s /\ BIJ f r.carrier s.carrier
`;

(* A ring homomorphism from r to r is an endomorphism. *)
val RingEndo_def = Define `RingEndo f r <=> RingHomo f r r`;

(* A ring isomorphism from r to r is an automorphism. *)
val RingAuto_def = Define `RingAuto f r <=> RingIso f r r`;

(* A subring s of r if identity is a homomorphism from s to r *)
val subring_def = Define `subring s r <=> RingHomo I s r`;

(* Overloads for Homomorphism and Isomorphisms with map *)
val _ = overload_on("~r~", ``\(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ RingHomo f r r_``);
val _ = overload_on("=r=", ``\(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ RingIso f r r_``);
(* make infix operators *)
val _ = set_fixity "~r~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "=r=" (Infix(NONASSOC, 450)); (* same as relation *)

(* Overloads for Ring of type 'b *)
val _ = overload_on("R_", ``(r_:'b ring).carrier``);
val _ = overload_on("R+_", ``ring_nonzero (r_:'b ring)``);
val _ = overload_on("#0_", ``(r_:'b ring).sum.id``);
val _ = overload_on("#1_", ``(r_:'b ring).prod.id``);
val _ = overload_on("+_", ``(r_:'b ring).sum.op``);
val _ = overload_on("*_", ``(r_:'b ring).prod.op``);
val _ = overload_on("-_", ``ring_sub (r_:'b ring)``);
val _ = overload_on("neg_", ``(r_:'b ring).sum.inv``); (* unary negation *)
val _ = overload_on("##_", ``(r_:'b ring).sum.exp``);
val _ = overload_on("**_", ``(r_:'b ring).prod.exp``);
val _ = overload_on("unit_", ``\x. x IN (Invertibles (r_:'b ring).prod).carrier``);
val _ = overload_on("|/_", ``(Invertibles (r_:'b ring).prod).inv``);
val _ = overload_on("Unit", ``\r x. x IN (Invertibles r.prod).carrier``); (* for any type *)
val _ = overload_on("Inv", ``\r. (Invertibles r.prod).inv``); (* for any type *)
(* make infix operators *)
val _ = set_fixity "+_" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity "-_" (Infixl 500); (* same as - in arithmeticScript.sml *)
val _ = set_fixity "*_" (Infixl 600); (* same as * in arithmeticScript.sml *)
val _ = set_fixity "**_" (Infixr 700); (* same as EXP in arithmeticScript.sml, infix right *)
(* 900 for numeric_negate *)
(* make unary symbolic *)
val _ = overload_on("-_", ``neg_``); (* becomes $-_ *)

(* ------------------------------------------------------------------------- *)
(* Ring Homomorphisms.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f ==> (f #0 = #0_) *)
(* Proof:
   Ring r ==> Group r.sum                        by ring_add_group
   Ring r_ ==> Group r_.sum                      by ring_add_group
   RingHomo f r r_ ==> GroupHomo f r.sum r_.sum  by RingHomo_def
   Hence true by group_homo_id.
*)
val ring_homo_zero = store_thm(
  "ring_homo_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #0 = #0_)``,
  rw_tac std_ss[ring_add_group, RingHomo_def, group_homo_id]);

(* Theorem: (r ~r~ r_) f ==> (f #1 = #1_) *)
(* Proof:
   Ring r ==> Monoid r.prod                         by ring_mult_monoid
   Ring r_ ==> Monoid r_.prod                       by ring_mult_monoid
   RingHomo f r r_ ==> MonoidHomo f r.prod r_.prod  by RingHomo_def
   Hence true by MonoidHomo_def.
*)
val ring_homo_one = store_thm(
  "ring_homo_one",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #1 = #1_)``,
  rw_tac std_ss[ring_mult_monoid, RingHomo_def, MonoidHomo_def]);

(* Theorem: (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by ring_homo_zero, ring_homo_one *)
val ring_homo_ids = store_thm(
  "ring_homo_ids",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)``,
  rw_tac std_ss[ring_homo_zero, ring_homo_one]);

(* export simple result *)
val _ = export_rewrites ["ring_homo_ids"];

(* Theorem: RingHomo f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by RingHomo_def *)
val ring_homo_element = store_thm(
  "ring_homo_element",
  ``!(r:'a ring) (r_:'b ring) f. RingHomo f r r_ ==> !x. x IN R ==> f x IN R_``,
  rw[RingHomo_def]);

(* Theorem: Ring r /\ RingHomo f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by definitions. *)
val ring_homo_property = store_thm(
  "ring_homo_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingHomo f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[RingHomo_def, GroupHomo_def, MonoidHomo_def]);

(* Theorem: Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingHomo f1 r r_ = RingHomo f2 r r_) *)
(* Proof: by RingHomo_def, ring_add_group, group_homo_cong, ring_mult_monoid, monoid_homo_cong *)
val ring_homo_cong = store_thm(
  "ring_homo_cong",
  ``!(r:'a ring) (r_:'b ring) f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                (RingHomo f1 r r_ = RingHomo f2 r r_)``,
  rw_tac std_ss[RingHomo_def, EQ_IMP_THM] >-
  metis_tac[ring_add_group, group_homo_cong] >-
  metis_tac[ring_mult_monoid, monoid_homo_cong] >-
  metis_tac[ring_add_group, group_homo_cong] >>
  metis_tac[ring_mult_monoid, monoid_homo_cong]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by ring_homo_property. *)
val ring_homo_add = store_thm(
  "ring_homo_add",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by ring_homo_property. *)
val ring_homo_mult = store_thm(
  "ring_homo_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof:
   Ring r ==> Group r.sum                          by ring_add_group
   Ring r_ ==> Group r_.sum                        by ring_add_group
   RingHomo f r r_ ==> GroupHomo f r.sum r_.sum    by RingHomo_def
   Hence true                                      by group_homo_inv
*)
val ring_homo_neg = store_thm(
  "ring_homo_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[ring_add_group, RingHomo_def, group_homo_inv]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y)) *)
(* Proof:
       f (x - y)
     = f (x + -y)              by ring_sub_def
     = (f x) +_ f (- y)        by ring_homo_add, ring_neg_element
     = (f x) +_ ($-_ (f y))    by ring_homo_neg
     = (f x) -_ (f y)          by ring_sub_def
*)
val ring_homo_sub = store_thm(
  "ring_homo_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y))``,
  metis_tac[ring_sub_def, ring_homo_add, ring_homo_neg, ring_neg_element]);

(* Theorem: (r ~r~ r_) f ==> !n. f ##n = ##_ #1_ n *)
(* Proof:
   By induction on n.
   Base case: f (##0) = ##_ #1_ 0
     f (## 0)
   = f #0          by ring_num_0
   = #1_           by ring_homo_zero
   = ##_ #1_ 0     by ring_num_0
   Step case: f (##n) = ##_ #1_ n ==> f (##(SUC n)) = ##_ #1_ (SUC n)
     f (##(SUC n))
   = f (#1 + ##n)          by ring_num_SUC
   = (f #1) +_ (f ##n)     by ring_homo_property
   = #1_ +_ (f ##n)        by ring_homo_one
   = #1_ +_ (##_ #1_ n)    by induction hypothesis
   = ##_ #1_ (SUC n)       by ring_num_SUC
*)
val ring_homo_num = store_thm(
  "ring_homo_num",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !n. f ##n = ##_ #1_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f (##(SUC n)) = f (#1 + ##n)` by rw[] >>
  `_ = (f #1) +_ (f ##n)` by rw[ring_homo_property] >>
  `_ = #1_ +_ (f ##n)` by metis_tac[ring_homo_one] >>
  rw[]);

(* Theorem: (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof:
   By induction on n.
   Base case: f (x ** 0) = f x **_ 0
     f (x ** 0)
   = f #1          by ring_exp_0
   = #1_           by ring_homo_one
   = f x **_ 0     by ring_exp_0
   Step case: f (x ** n) = f x **_ n ==> f (x ** SUC n) = (f x) **_ SUC n
     f (x ** SUC n)
   = f (x * x ** n)              by ring_exp_SUC
   = (f x) *_ (f (x ** n))       by ring_homo_property
   = (f x) *_ (f x **_ n)        by induction hypothesis
   = (f x) **_ SUC n             by ring_exp_SUC
*)
val ring_homo_exp = store_thm(
  "ring_homo_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f (x ** SUC n) = f (x * x ** n)` by rw[] >>
  `_ = (f x) *_ (f (x ** n))` by rw[ring_homo_property] >>
  rw[]);

(* Theorem: If two rings r and s have a ring homomorphism, then (char s) divides (char f).
            (r ~r~ r_) f ==> (char r_) divides (char r) *)
(* Proof:
   Let n = char r, m = char r_. This is to show: m divides n.
   If n = 0, result is true by ALL_DIVIDES_0.
   If n <> 0, 0 < n.
   then  ##n = #0           by char_property
   so  f ##n = f #0
   or ##_ #1_ n = #0_       by ring_homo_num, ring_homo_zero
   and result follows       by ring_char_divides.
*)
val ring_homo_char_divides = store_thm(
  "ring_homo_char_divides",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (char r_) divides (char r)``,
  rpt strip_tac >>
  Cases_on `char r = 0` >-
  rw_tac std_ss[ALL_DIVIDES_0] >>
  `0 < char r` by decide_tac >>
  metis_tac[char_property, ring_homo_num, ring_homo_zero, ring_char_divides]);

(* Theorem: RingHomo I r r *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo I r.sum r.sum, true by group_homo_I_refl
   (2) GroupHomo I f* f*, true by group_homo_I_refl
*)
val ring_homo_I_refl = store_thm(
  "ring_homo_I_refl",
  ``!r:'a ring. RingHomo I r r``,
  rw_tac std_ss[RingHomo_def, group_homo_I_refl, monoid_homo_I_refl]);

(* Theorem: RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo f2 o f1 r t *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo f1 r.sum s.sum /\ GroupHomo f2 s.sum t.sum ==>  GroupHomo (f2 o f1) r.sum t.sum
       True by group_homo_trans.
   (2) MonoidHomo f1 r.prod s.prod /\ MonoidHomo f2 s.prod t.pro ==> MonoidHomo (f2 o f1) r.prod t.prod
       True by monoid_homo_trans.
*)
val ring_homo_trans = store_thm(
  "ring_homo_trans",
  ``!(r:'a ring) (s:'b ring) (t:'c ring). !f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t``,
  rw_tac std_ss[RingHomo_def] >| [
    metis_tac[group_homo_trans],
    metis_tac[monoid_homo_trans]
  ]);

(* Theorem: (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r *)
(* Proof:
   Note BIJ f R R_
    ==> BIJ (LINV f R) R_ R                  by BIJ_LINV_BIJ
   By RingHomo_def, this is to show:
   (1) x IN R_ ==> LINV f R x IN R
       With BIJ (LINV f R) R_ R
        ==> INJ (LINV f R) R_ R              by BIJ_DEF
        ==> x IN R_ ==> LINV f R x IN R      by INJ_DEF
   (2) GroupHomo f r.sum r_.sum /\ BIJ f R R_ ==> GroupHomo (LINV f R) r_.sum r.sum
       Since Ring r
         ==> Group r.sum /\ (r.sum.carrier = R)      by ring_add_group
         and Ring r_ ==> r_.sum.carrier = R_         by ring_add_group
       Hence GroupHomo (LINV f R) r_.sum r.sum       by group_homo_sym
   (3) MonoidHomo f r.prod r_.prod /\ BIJ f R R_ ==> MonoidHomo (LINV f R) r_.prod r.prod
       Since Ring r
         ==> Group r.prod /\ (r.prod.carrier = R)    by ring_mult_monoid
         and Ring r_ ==> r_.prod.carrier = R_        by ring_mult_monoid
       Hence MonoidHomo (LINV f R) r_.prod r.prod    by monoid_homo_sym
*)
val ring_homo_sym = store_thm(
  "ring_homo_sym",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r``,
  rpt strip_tac >>
  `BIJ (LINV f R) R_ R` by rw[BIJ_LINV_BIJ] >>
  fs[RingHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >-
 (`Group r.sum /\ (r.sum.carrier = R)` by rw[ring_add_group] >>
  `r_.sum.carrier = R_` by rw[ring_add_group] >>
  metis_tac[group_homo_sym]) >>
  `Monoid r.prod /\ (r.prod.carrier = R)` by rw[ring_mult_monoid] >>
  `r_.prod.carrier = R_` by rw[ring_mult_monoid] >>
  metis_tac[monoid_homo_sym]);

Theorem ring_homo_sym_any:
  Ring r /\ Ring s /\ RingHomo f r s /\
  (!x. x IN s.carrier ==> i x IN r.carrier /\ f (i x) = x) /\
  (!x. x IN r.carrier ==> i (f x) = x)
  ==>
  RingHomo i s r
Proof
  rpt strip_tac
  \\ fs[RingHomo_def]
  \\ conj_tac
  >- (
    irule group_homo_sym_any
    \\ conj_tac >- metis_tac[Ring_def, AbelianGroup_def]
    \\ qexists_tac`f`
    \\ metis_tac[ring_carriers] )
  \\ irule monoid_homo_sym_any
  \\ conj_tac >- metis_tac[Ring_def, AbelianMonoid_def]
  \\ qexists_tac`f`
  \\ metis_tac[ring_carriers]
QED

(* Theorem: RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo f1 r.sum s.sum /\ GroupHomo f2 s.sum t.sum ==> GroupHomo (f2 o f1) r.sum t.sum
       True by group_homo_compose.
   (2) MonoidHomo f1 r.prod s.prod /\ MonoidHomo f2 s.prod t.prod ==> MonoidHomo (f2 o f1) r.prod t.prod
       True by monoid_homo_compose
*)
val ring_homo_compose = store_thm(
  "ring_homo_compose",
  ``!(r:'a ring) (s:'b ring) (t:'c ring).
   !f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[group_homo_compose] >>
  metis_tac[monoid_homo_compose]);
(* This is the same as ring_homo_trans *)

(* Theorem: (r ~r~ r_) f /\  /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, RingHomo_def, this is to show:
   (1) BIJ f R R_ /\ x IN R_ ==> LINV f R x IN R
       True by BIJ_LINV_ELEMENT
   (2) BIJ f R R_ /\ GroupHomo (LINV f R) r_.sum r.sum
       Note Group r.sum                            by ring_add_group
        and R = r.sum.carrier                      by ring_carriers
        and R_ = r_.sum.carrier                    by ring_carriers
        ==> GroupIso f r.sum r_.sum                by GroupIso_def, BIJ f R R_
       Thus GroupHomo (LINV f R) r_.sum r.sum      by group_iso_linv_iso
   (3) BIJ f R R_ /\ MonoidHomo (LINV f R) r_.prod r.prod
       Note Monoid r.prod                          by ring_mult_monoid
        and R = r.prod.carrier                     by ring_carriers
        and R_ = r_.prod.carrier                   by ring_carriers
        ==> MonoidIso f r.prod r_.prod             by MonoidIso_def, BIJ f R R_
       Thus MonoidHomo (LINV f R) r_.prod r.prod   by monoid_iso_linv_iso
*)
val ring_homo_linv_homo = store_thm(
  "ring_homo_linv_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
  metis_tac[group_iso_linv_iso, ring_add_group, ring_carriers, GroupIso_def] >>
  metis_tac[monoid_iso_linv_iso, ring_mult_monoid, ring_carriers, MonoidIso_def]);
(* This is the same as ring_homo_sym, direct proof. *)

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof:
   If part: f x = #0_ ==> x = #0
      Note f #0 = #0_      by ring_homo_zero
       and #0 IN R         by ring_zero_element
      Thus x = #0          by INJ_DEF, x IN R
   Only-if part: x = #0 ==> f x = #0_
      True                 by ring_homo_zero
*)
val ring_homo_eq_zero = store_thm(
  "ring_homo_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  metis_tac[ring_homo_zero, INJ_DEF, ring_zero_element]);

(* Theorem: (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_) *)
(* Proof:
   Since f #1 = #1_     by ring_homo_one
     and f #0 = #0_     by ring_homo_zero
   Hence #1_ = #0_
*)
val ring_homo_one_eq_zero = store_thm(
  "ring_homo_one_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_)``,
  metis_tac[ring_homo_one, ring_homo_zero]);

(* Theorem: (r ~r~ r_) f ==> !c:num. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_ *)
(* Proof:
   This is to show:
   (1) ##c <> #0
       By contradiction.
       Suppose ##c = #0.
          Then (char r) divides c   by ring_char_divides
            or (char r) <= c        by DIVIDES_LE, 0 < c.
           But 0 < c means c <> 0
         Hence char r <> 0          by ZERO_DIVIDES
            or 0 < char r
           Now (char r_) divides (char r)   by ring_homo_char_divides
            so (char r_) <= (char r)        by DIVIDES_LE, 0 < char r.
            or c < char r                   by c < char r_
       This is a contradiction with (char r) <= c.
   (2) ##_ #1_ c <> #0_
       By contradiction.
       Suppose ##_ #1_ c = #0_.
          Then (char r_) divides c          by ring_char_divides
            so (char r_) <= c               by DIVIDES_LE, 0 < c.
       This is a contradiction with given c < (char r_).
*)
val ring_homo_sum_num_property = store_thm(
  "ring_homo_sum_num_property",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c:num. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_``,
  rpt strip_tac >| [
    `(char r) divides c` by rw[GSYM ring_char_divides] >>
    `(char r) <= c` by rw[DIVIDES_LE] >>
    `c <> 0` by decide_tac >>
    `char r <> 0` by metis_tac[ZERO_DIVIDES] >>
    `0 < char r` by decide_tac >>
    `(char r_) divides (char r)` by metis_tac[ring_homo_char_divides] >>
    `(char r_) <= (char r)` by rw[DIVIDES_LE] >>
    decide_tac,
    `(char r_) divides c` by rw[GSYM ring_char_divides] >>
    `(char r_) <= c` by rw[DIVIDES_LE] >>
    decide_tac
  ]);

(* Theorem: (r ~r~ r_) f ==> !c:num. 0 < c /\ c < char r_ ==>  ##c <> #0 /\ f (##c) <> #0_ *)
(* Proof:
   Given 0 < c /\ c < char r_,
         ##c <> #0 /\ ##_ #1_ c <> #0_   by ring_homo_sum_num_property
     f (##c)
   = ##_ #1_ c      by ring_homo_num
   <> #0_           by above
*)
val ring_homo_num_nonzero = store_thm(
  "ring_homo_num_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c:num. 0 < c /\ c < char r_ ==>  ##c <> #0 /\ f (##c) <> #0_``,
  metis_tac[ring_homo_num, ring_homo_sum_num_property]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     #1_
   = f #1                      by ring_homo_one
   = f (x * |/ x)              by ring_unit_rinv
   = (f x) *_ (f ( |/ x))      by ring_homo_property
   Hence true                  by ring_unit_property
*)
val ring_homo_unit = store_thm(
  "ring_homo_unit",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x)``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `#1_ = f #1` by rw[ring_homo_one] >>
  `_ = f (x * |/ x)` by rw[ring_unit_rinv] >>
  `_ = (f x) *_ (f ( |/ x))` by rw[ring_homo_property] >>
  metis_tac[ring_unit_property]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> (f x) <> #0_ *)
(* Proof:
   By contradiction. Suppose (f x) = #0_.
   Since unit x ==> f x IN (Invertibles r_.prod).carrier   by ring_homo_unit
   But this contradicts the given #1_ <> #0_               by ring_unit_zero
*)
val ring_homo_unit_nonzero = store_thm(
  "ring_homo_unit_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> (f x) <> #0_``,
  metis_tac[ring_homo_unit, ring_unit_zero]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) = f ( |/ x) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     (f x) *_ (f ( |/ x))
   = f (x * |/ x)              by ring_homo_property
   = f #1                      by ring_unit_rinv
   = #1_                       by ring_homo_one
   Since unit_ (f x)           by ring_homo_unit
   Hence |/_ (f x) = f ( |/x)  by ring_unit_rinv_unique
*)
val ring_homo_unit_inv = store_thm(
  "ring_homo_unit_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) = f ( |/ x)``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `(f x) *_ (f ( |/ x)) = f (x * |/x)` by rw[ring_homo_property] >>
  `_ = f #1` by rw[ring_unit_rinv] >>
  `_ = #1_` by rw[ring_homo_one] >>
  metis_tac[ring_homo_unit, ring_unit_rinv_unique]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_ *)
(* Proof:
   Note unit_ (f x)        by ring_homo_unit
   Thus |/_ (f x) IN R_    by ring_unit_inv_element
*)
val ring_homo_unit_inv_element = store_thm(
  "ring_homo_unit_inv_element",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_``,
  metis_tac[ring_homo_unit, ring_unit_inv_element]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> |/_ (f x) <> #0_ *)
(* Proof:
   Note unit_ (f x)        by ring_homo_unit
   Thus |/_ (f x) <> #0_   by ring_unit_inv_nonzero
*)
val ring_homo_unit_inv_nonzero = store_thm(
  "ring_homo_unit_inv_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !x. unit x ==> |/_ (f x) <> #0_``,
  metis_tac[ring_homo_unit, ring_unit_inv_nonzero]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     #1_
   = f #1                                 by ring_homo_one
   = f (x * |/ x)                         by ring_unit_rinv
   = (f x) *_ (f ( |/ x))                 by ring_homo_property
   Since unit_ (f x)                      by ring_homo_unit
   Hence f ( |/ x) = |/_ (f x)            by ring_unit_rinv_unique
*)
val ring_homo_inv = store_thm(
  "ring_homo_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `#1_ = f #1` by rw[ring_homo_one] >>
  `_ = f (x * |/ x)` by rw[ring_unit_rinv] >>
  `_ = (f x) *_ (f ( |/ x))` by rw[ring_homo_property] >>
  `unit_ (f x)` by metis_tac[ring_homo_unit] >>
  rw[ring_unit_rinv_unique]);

(* ------------------------------------------------------------------------- *)
(* Ring Isomorphisms.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==> (f #0 = #0_) *)
(* Proof: by RingIso_def, ring_homo_zero *)
val ring_iso_zero = store_thm(
  "ring_iso_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #0 = #0_)``,
  rw[RingIso_def]);

(* Theorem: (r =r= r_) f ==> (f #1 = #1_) *)
(* Proof: by RingIso_def, ring_homo_zero *)
val ring_iso_one = store_thm(
  "ring_iso_one",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #1 = #1_)``,
  rw[RingIso_def]);

(* Theorem: (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by ring_iso_zero, ring_iso_one. *)
val ring_iso_ids = store_thm(
  "ring_iso_ids",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)``,
  rw_tac std_ss[ring_iso_zero, ring_iso_one]);

(* export simple result *)
val _ = export_rewrites ["ring_iso_ids"];

(* Theorem: RingIso f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by RingIso_def, ring_homo_element *)
val ring_iso_element = store_thm(
  "ring_iso_element",
  ``!(r:'a ring) (r_:'b ring) f. RingIso f r r_ ==> !x. x IN R ==> f x IN R_``,
  metis_tac[RingIso_def, ring_homo_element]);

(* Theorem: Ring r /\ RingIso f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_property *)
val ring_iso_property = store_thm(
  "ring_iso_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingIso f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[RingIso_def, ring_homo_property]);

(* Theorem: Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingIso f1 r r_ <=> RingIso f2 r r_) *)
(* Proof:
   If part: RingIso f1 r r_ ==> RingIso f2 r r_
      By RingIso_def, RingHomo_def, this is to show:
      (1) x IN R ==> f2 x IN R_, true         by implication, given x IN R ==> f1 x IN R_
      (2) GroupHomo f2 r.sum r_.sum, true     by GroupHomo_def, ring_carriers, ring_add_element
      (3) MonoidHomo f2 r.prod r_.prod, true  by MonoidHomo_def, ring_carriers, ring_mult_element, ring_one_element
      (4) BIJ f R R_ ==> BIJ f2 R R_, true    by BIJ_DEF, INJ_DEF, SURJ_DEF
   Only-if part: RingIso f2 r r_ ==> RingIso f1 r r_
      By RingIso_def, RingHomo_def, this is to show:
      (1) x IN R_ ==> f1 x IN R, true trivially, given x IN R_ ==> f1 x IN R
      (2) GroupHomo f1 r_.sum r.sum, true     by GroupHomo_def
      (3) MonoidHomo f1 r_.prod r.prod, true  by MonoidHomo_def
      (4) BIJ f2 R R_ ==> BIJ f1 R R), true   by BIJ_DEF, INJ_DEF, SURJ_DEF
*)
val ring_iso_cong = store_thm(
  "ring_iso_cong",
  ``!(r:'a ring) (r_:'b ring) f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
        (RingIso f1 r r_ <=> RingIso f2 r r_)``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    fs[RingIso_def, RingHomo_def] >>
    rpt strip_tac >-
    metis_tac[] >-
   (fs[GroupHomo_def] >>
    metis_tac[ring_carriers, ring_add_element]) >-
   (fs[MonoidHomo_def] >>
    metis_tac[ring_carriers, ring_mult_element, ring_one_element]) >>
    fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[],
    fs[RingIso_def, RingHomo_def] >>
    rpt strip_tac >-
    fs[GroupHomo_def] >-
    fs[MonoidHomo_def] >>
    fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[]
  ]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_add *)
val ring_iso_add = store_thm(
  "ring_iso_add",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[RingIso_def, ring_homo_add]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_mult *)
val ring_iso_mult = store_thm(
  "ring_iso_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[RingIso_def, ring_homo_mult]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof: by RingIso_def, ring_homo_neg *)
val ring_iso_neg = store_thm(
  "ring_iso_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[RingIso_def, ring_homo_neg]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_sub *)
val ring_iso_sub = store_thm(
  "ring_iso_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y))``,
  rw[RingIso_def, ring_homo_sub]);

(* Theorem: (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n *)
(* Proof: by RingIso_def, ring_homo_num *)
val ring_iso_num = store_thm(
  "ring_iso_num",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n``,
  rw[RingIso_def, ring_homo_num]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof: by RingIso_def, ring_homo_exp *)
val ring_iso_exp = store_thm(
  "ring_iso_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rw[RingIso_def, ring_homo_exp]);

(* Theorem: RingIso I r r *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo I r r, true by ring_homo_I_refl
   (2) BIJ I R R, true      by BIJ_I_SAME
*)
val ring_iso_I_refl = store_thm(
  "ring_iso_I_refl",
  ``!r:'a ring. RingIso I r r``,
  rw[RingIso_def, ring_homo_I_refl, BIJ_I_SAME]);

(* Theorem: RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
       True by ring_homo_trans.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE.
*)
val ring_iso_trans = store_thm(
  "ring_iso_trans",
  ``!(r:'a ring) (s:'b ring) (t:'c ring). !f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t``,
  rw[RingIso_def] >-
  metis_tac[ring_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as ring_iso_trans. *)

(* Theorem: (r =r= r_) f ==> RingIso (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f r r_ /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r, true  by ring_homo_sym
   (2) BIJ f R R_ ==> BIJ (LINV f R) R_ R, true                          by BIJ_LINV_BIJ
*)
val ring_iso_sym = store_thm(
  "ring_iso_sym",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> RingIso (LINV f R) r_ r``,
  rw[RingIso_def, ring_homo_sym, BIJ_LINV_BIJ]);

Theorem ring_iso_sym_any:
  Ring r /\ Ring s /\ RingIso f r s /\
  (!x. x IN s.carrier ==> i x IN r.carrier /\ f (i x) = x) /\
  (!x. x IN r.carrier ==> i (f x) = x)
  ==>
  RingIso i s r
Proof
  rpt strip_tac \\ fs[RingIso_def]
  \\ conj_tac >- metis_tac[ring_homo_sym_any]
  \\ simp[BIJ_IFF_INV]
  \\ qexists_tac`f`
  \\ metis_tac[BIJ_DEF, INJ_DEF]
QED

(* Theorem: RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
       True by ring_homo_compose.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE
*)
val ring_iso_compose = store_thm(
  "ring_iso_compose",
  ``!(r:'a ring) (s:'b ring) (t:'c ring).
   !f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t``,
  rw_tac std_ss[RingIso_def] >-
  metis_tac[ring_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Ring r /\ Ring r_ /\ RingIso f r r_ ==> RingIso (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, RingHomo_def, this is to show:
   (1) BIJ f R R_ /\ x IN R_ ==> LINV f R x IN R
       True by BIJ_LINV_ELEMENT
   (2) BIJ f R R_ /\ GroupHomo (LINV f R) r_.sum r.sum
       Note Group r.sum                            by ring_add_group
        and R = r.sum.carrier                      by ring_carriers
        and R_ = r_.sum.carrier                    by ring_carriers
        ==> GroupIso f r.sum r_.sum                by GroupIso_def
       Thus GroupHomo (LINV f R) r_.sum r.sum      by group_iso_linv_iso
   (3) BIJ f R R_ /\ MonoidHomo (LINV f R) r_.prod r.prod
       Note Monoid r.prod                          by ring_mult_monoid
        and R = r.prod.carrier                     by ring_carriers
        and R_ = r_.prod.carrier                   by ring_carriers
        ==> MonoidIso f r.prod r_.prod             by MonoidIso_def
       Thus MonoidHomo (LINV f R) r_.prod r.prod   by monoid_iso_linv_iso
   (4) BIJ f R R_ ==> BIJ (LINV f R) R_ R
       True by BIJ_LINV_BIJ
*)
val ring_iso_linv_iso = store_thm(
  "ring_iso_linv_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> RingIso (LINV f R) r_ r``,
  rw_tac std_ss[RingIso_def, RingHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
  metis_tac[group_iso_linv_iso, ring_add_group, ring_carriers, GroupIso_def] >-
  metis_tac[monoid_iso_linv_iso, ring_mult_monoid, ring_carriers, MonoidIso_def] >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as ring_iso_sym, direct proof. *)

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof: by ring_homo_eq_zero, RingIso_def, BIJ_DEF *)
val ring_iso_eq_zero = store_thm(
  "ring_iso_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  rw_tac std_ss[ring_homo_eq_zero, RingIso_def, BIJ_DEF]);

(* Theorem: RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_ *)
(* Proof:
   Since BIJ f R R_               by RingIso_def
      so FINITE R ==> FINITE R_   by BIJ_FINITE
    thus CARD R = CARD R_         by FINITE_BIJ_CARD_EQ
*)
val ring_iso_card_eq = store_thm(
  "ring_iso_card_eq",
  ``!(r:'a ring) (r_:'b ring) f. RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)``,
  metis_tac[RingIso_def, BIJ_FINITE, FINITE_BIJ_CARD_EQ]);

(* Theorem: (r =r= r_) f ==> (char r_ = char r) *)
(* Proof:
   Note RingIso (LINV f R) r_ r     by ring_iso_sym
   Thus (char r_) divides (char r)  by RingIso_def, ring_homo_char_divides,
    and (char r) divides (char r_)  by RingIso_def, ring_homo_char_divides
    ==> char r_ = char r            by DIVIDES_ANTISYM
*)
val ring_iso_char_eq = store_thm(
  "ring_iso_char_eq",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (char r_ = char r)``,
  metis_tac[ring_iso_sym, DIVIDES_ANTISYM, RingIso_def, ring_homo_char_divides]);

(* Theorem: (r =r= r_) f ==> BIJ f R R_ *)
(* Proof: by RingIso_def *)
val ring_iso_bij = store_thm(
  "ring_iso_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> BIJ f R R_``,
  rw_tac std_ss[RingIso_def]);

(* Theorem: (r =r= r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof:
   Note RingIso f r r_ ==> RingHomo f r r_   by RingIso_def
   Thus !x. unit x ==> unit_ (f x)           by ring_homo_unit
*)
val ring_iso_unit = store_thm(
  "ring_iso_unit",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. unit x ==> unit_ (f x)``,
  metis_tac[ring_homo_unit, RingIso_def]);

(* Theorem: (r =r= r_) f ==> !x. x IN R+ ==> !x. x IN R+ ==> (f x) IN R+_ *)
(* Proof:
   Note (r === r_) f
      = Ring r /\ Ring r_ /\ RingIso f r r_     by notation
   Note x IN R+ <=> x IN R /\ x <> #0           by ring_nonzero_eq
    But x IN R ==> f x IN R_                    by ring_iso_element
    and x <> #0 ==> f x <> #0_                  by ring_iso_eq_zero
     so (f x) IN R+_                            by ring_nonzero_eq
*)
val ring_iso_nonzero = store_thm(
  "ring_iso_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R+ ==> (f x) IN R+_``,
  metis_tac[ring_nonzero_eq, ring_iso_element, ring_iso_eq_zero]);

(* Theorem: (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
   Note (r =r= r_) f
     = Ring r /\ Ring r_ /\ RingIso f r r_     by notation
   ==> Ring r /\ Ring r_ /\ RingdHomo f r r_   by RingIso_def
   ==> f ( |/ x) = |/_ (f x)                   by ring_homo_inv, unit x
*)
val ring_iso_inv = store_thm(
  "ring_iso_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))``,
  rw[RingIso_def, ring_homo_inv]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1)) *)
(* Proof:
   If part: f x = #1_ ==> x = #1
      Note INJ R R_         by RingIso_def, BIJ_DEF
     Since f x = f #1       by ring_iso_one
        so   x = #1         by INJ_DEF
   Only-if part: x = #1 ==> f x = #1_
      True by ring_iso_one
*)
val ring_iso_eq_one = store_thm(
  "ring_iso_eq_one",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))``,
  prove_tac[ring_iso_one, RingIso_def, BIJ_DEF, INJ_DEF, ring_one_element]);

(* Theorem: (r =r= r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y)) *)
(* Proof: by RingIso_def, BIJ_DEF, BIJ_LINV_ELEMENT, BIJ_LINV_INV *)
val ring_iso_inverse_element = store_thm(
  "ring_iso_inverse_element",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y))``,
  metis_tac[RingIso_def, BIJ_DEF, BIJ_LINV_ELEMENT, BIJ_LINV_INV]);

(* Theorem: (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x) *)
(* Proof: by ring_iso_inverse_element *)
val ring_iso_inverse = store_thm(
  "ring_iso_inverse",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)``,
  metis_tac[ring_iso_inverse_element]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y)) *)
(* Proof:
   Note INJ R R_                   by RingIso_def, BIJ_DEF
   Hence (f x = f y) <=> (x = y)   by INJ_DEF
*)
val ring_iso_element_unique = store_thm(
  "ring_iso_element_unique",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))``,
  prove_tac[RingIso_def, BIJ_DEF, INJ_DEF]);

(* ------------------------------------------------------------------------- *)
(* Ring Automorphisms.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ RingAuto f r ==> (f #0 = #0) *)
(* Proof: by RingAuto_def, ring_iso_zero *)
val ring_auto_zero = store_thm(
  "ring_auto_zero",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #0 = #0)``,
  rw_tac std_ss[RingAuto_def, ring_iso_zero]);

(* Theorem: Ring r /\ RingAuto f r ==> (f #1 = #1) *)
(* Proof: by RingAuto_def, ring_iso_one *)
val ring_auto_one = store_thm(
  "ring_auto_one",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #1 = #1)``,
  rw_tac std_ss[RingAuto_def, ring_iso_one]);

(* Theorem: Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1) *)
(* Proof: by ring_auto_zero, ring_auto_one. *)
val ring_auto_ids = store_thm(
  "ring_auto_ids",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1)``,
  rw_tac std_ss[ring_auto_zero, ring_auto_one]);

(* Theorem: RingAuto f r ==> !x. x IN R ==> f x IN R *)
(* Proof: by RingAuto_def, ring_iso_element *)
val ring_auto_element = store_thm(
  "ring_auto_element",
  ``!(r:'a ring) f. RingAuto f r ==> !x. x IN R ==> f x IN R``,
  metis_tac[RingAuto_def, ring_iso_element]);

(* Theorem: Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingAuto f1 r <=> RingAuto f2 r) *)
(* Proof: by RingAuto_def, ring_iso_cong. *)
val ring_auto_cong = store_thm(
  "ring_auto_cong",
  ``!(r:'a ring) f1 f2. Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingAuto f1 r <=> RingAuto f2 r)``,
  rw_tac std_ss[RingAuto_def, ring_iso_cong]);

(* Theorem: RingAuto I r *)
(* Proof: by RingAuto_def, ring_iso_I_refl. *)
val ring_auto_I = store_thm(
  "ring_auto_I",
  ``!(r:'a ring). RingAuto I r``,
  rw_tac std_ss[RingAuto_def, ring_iso_I_refl]);

(* Theorem: Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r *)
(* Proof:
       RingAuto f r
   ==> RingIso f r r                by RingAuto_def
   ==> RingIso (LINV f R) r         by ring_iso_linv_iso
   ==> RingAuto (LINV f R) r        by RingAuto_def
*)
val ring_auto_linv_auto = store_thm(
  "ring_auto_linv_auto",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r``,
  rw_tac std_ss[RingAuto_def, ring_iso_linv_iso]);


(* Theorem: Ring r /\ RingAuto f r ==> f PERMUTES R *)
(* Proof: by RingAuto_def, ring_iso_bij *)
val ring_auto_bij = store_thm(
  "ring_auto_bij",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> f PERMUTES R``,
  rw_tac std_ss[RingAuto_def, ring_iso_bij]);

(* ------------------------------------------------------------------------- *)
(* Subrings.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload on s.carrier, base carrier *)
val _ = overload_on("B", ``(s:'a ring).carrier``);

(* Overload on subring situation *)
val _ = overload_on("<=", ``\(s r):'a ring. Ring r /\ Ring s /\ subring s r``);

(* Theorem: subring s r ==> !x. x IN B ==> x IN R *)
(* Proof: by subring_def, RingHomo_def *)
val subring_element = store_thm(
  "subring_element",
  ``!(r s):'a ring. subring s r ==> !x. x IN B ==> x IN R``,
  rw_tac std_ss[subring_def, RingHomo_def]);

(* Theorem: subring s r ==> B SUBSET R *)
(* Proof: by subring_element, SUBSET_DEF *)
val subring_carrier_subset = store_thm(
  "subring_carrier_subset",
  ``!(r s):'a ring. subring s r ==> B SUBSET R``,
  metis_tac[subring_element, SUBSET_DEF]);

(* Theorem: FiniteRing r /\ subring s r ==> FINITE B *)
(* Proof:
   Since FiniteRing r ==> FINITE R    by FiniteRing_def
     and subring s r ==> B SUBSET R   by subring_carrier_subset
   Hence FINITE B                     by SUBSET_FINITE
*)
val subring_carrier_finite = store_thm(
  "subring_carrier_finite",
  ``!(r s):'a ring. FiniteRing r /\ subring s r ==> FINITE B``,
  metis_tac[FiniteRing_def, subring_carrier_subset, SUBSET_FINITE]);

(* Theorem: FiniteRing r /\ s <= r ==> FiniteRing s *)
(* Proof:
   Since FINITE B       by subring_carrier_finite
   Hence FiniteRing s   by FiniteRing_def
*)
val subring_finite_ring = store_thm(
  "subring_finite_ring",
  ``!(r s):'a ring. FiniteRing r /\ s <= r ==> FiniteRing s``,
  metis_tac[FiniteRing_def, subring_carrier_finite]);

(* Theorem: subring r r *)
(* Proof:
   By subring_def, this is to show:
   RingHomo I r r, true by ring_homo_I_refl.
*)
val subring_refl = store_thm(
  "subring_refl",
  ``!r:'a ring. subring r r``,
  rw[subring_def, ring_homo_I_refl]);

(* Theorem: subring r s /\ subring s t ==> subring r t *)
(* Proof:
   By subring_def, this is to show:
   RingHomo I r s /\ RingHomo I s t ==> RingHomo I r t
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by ring_homo_trans
*)
val subring_trans = store_thm(
  "subring_trans",
  ``!(r s t):'a ring. subring r s /\ subring s t ==> subring r t``,
  prove_tac[subring_def, combinTheory.I_o_ID, ring_homo_trans]);

(* Theorem: subring s r /\ subring r s ==> RingIso I s r *)
(* Proof:
   By subring_def, RingIso_def, this is to show:
      RingHomo I s r /\ RingHomo I r s ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subring_carrier_subset, subring s r
   (2) x IN R ==> x IN B, true    by subring_carrier_subset, subring r s
*)
val subring_I_antisym = store_thm(
  "subring_I_antisym",
  ``!(r:'a ring) s. subring s r /\ subring r s ==> RingIso I s r``,
  rw_tac std_ss[subring_def, RingIso_def] >>
  fs[RingHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subring s r /\ R SUBSET B ==> RingIso I s r *)
(* Proof:
   By subring_def, RingIso_def, this is to show:
      RingHomo I s r /\ R SUBSET B ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subring_carrier_subset, subring s r
   (2) x IN R ==> x IN B, true    by R SUBSET B, given
*)
val subring_carrier_antisym = store_thm(
  "subring_carrier_antisym",
  ``!(r:'a ring) s. subring s r /\ R SUBSET B ==> RingIso I s r``,
  rpt (stripDup[subring_def]) >>
  rw_tac std_ss[RingIso_def] >>
  `B SUBSET R` by rw[subring_carrier_subset] >>
  fs[RingHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subring s r ==> subgroup s.sum r.sum *)
(* Proof:
        subring s r
    <=> RingHomo I s r            by subring_def
    ==> GroupHomo I s.sum r.sum   by RingHomo_def
    ==> subgroup s.rum r.sum      by subgroup_def
*)
val subring_sum_subgroup = store_thm(
  "subring_sum_subgroup",
  ``!(r:'a ring) (s:'a ring). subring s r ==> subgroup s.sum r.sum``,
  rw_tac std_ss[subring_def, RingHomo_def, subgroup_def]);

(* Theorem: subring s r ==> submonoid s.prod r.prod *)
(* Proof:
        subring s r
    <=> RingHomo I s r               by subring_def
    ==> MonoidHomo I s.prod r.prod   by RingHomo_def
    ==> submonoid s.prod r.prod      by submonoid_def
*)
val subring_prod_submonoid = store_thm(
  "subring_prod_submonoid",
  ``!(r:'a ring) (s:'a ring). subring s r ==> submonoid s.prod r.prod``,
  rw_tac std_ss[subring_def, RingHomo_def, submonoid_def]);

(* Theorem: s <= r <=> Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod *)
(* Proof:
   If part: s <= r ==> Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod
      Note subgroup s.sum r.sum      by subring_sum_subgroup
       and submonoid s.prod r.prod   by subring_prod_submonoid
   Only-if part: Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod ==> s <= r
      Note subgroup s.sum r.sum
       ==> s.sum.carrier SUBSET r.sum.carrier   by subgroup_subset
       ==> B SUBSET R                           by ring_carriers
       ==> !x. x IN B ==> I x IN R              by SUBSET_DEF, I_THM
       and subgroup s.sum r.sum ==> GroupHomo I s.sum r.sum         by subgroup_def
       and submonoid s.prod r.prod ==> MonoidHomo I s.prod r.prod   by submonoid_def
      Thus RingHomo I s r            by RingHomo_def
        or s <= r                    by subring_def
*)
val subring_by_subgroup_submonoid = store_thm(
  "subring_by_subgroup_submonoid",
  ``!(r:'a ring) (s:'a ring). s <= r <=>
     Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod``,
  rw[EQ_IMP_THM] >-
  rw[subring_sum_subgroup] >-
  rw[subring_prod_submonoid] >>
  rw_tac std_ss[subring_def, RingHomo_def] >-
  metis_tac[subgroup_subset, ring_carriers, SUBSET_DEF] >-
  fs[subgroup_def] >>
  fs[submonoid_def]);

(* Theorem: subring s r /\ RingHomo f r r_ ==> RingHomo f s r_ *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) subring s r /\ x IN B ==> f x IN R_, true          by subring_element
   (2) subring s r /\ GroupHomo f r.sum r_.sum ==> GroupHomo f s.sum r_.sum
       Note subgroup s.sum r.sum                          by subring_sum_subgroup
       Thus GroupHomo f s.sum r_.sum                      by subgroup_homo_homo
   (3) subring s r /\ MonoidHomo f r.prod r_.prod ==> MonoidHomo f s.prod r_.prod
       Note submonoid s.prod r.prod                       by subring_prod_submonoid
       Thus MonoidHomo f s.prod r_.prod                   by submonoid_homo_homo
*)
val subring_homo_homo = store_thm(
  "subring_homo_homo",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. subring s r /\ RingHomo f r r_ ==> RingHomo f s r_``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[subring_element] >-
  metis_tac[subring_sum_subgroup, subgroup_homo_homo] >>
  metis_tac[subring_prod_submonoid, submonoid_homo_homo]);

(* ------------------------------------------------------------------------- *)
(* Subring Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: I x = x *)
val i_thm = combinTheory.I_THM;

(* Theorem: (f o g) x = f (g x) *)
val o_thm = combinTheory.o_THM;

(* Theorem: s <= r ==> s.sum.id = #0 *)
(* Proof: by subring_def, ring_homo_zero. *)
val subring_zero = store_thm(
  "subring_zero",
  ``!(r s):'a ring. s <= r ==> (s.sum.id = #0)``,
  metis_tac[subring_def, ring_homo_zero, i_thm]);

(* Theorem: s <= r ==> s.prod.id = #1 *)
(* Proof: by subring_def, ring_homo_one. *)
val subring_one = store_thm(
  "subring_one",
  ``!(r s):'a ring. s <= r ==> (s.prod.id = #1)``,
  metis_tac[subring_def, ring_homo_one, i_thm]);

(* export simple results *)
val _ = export_rewrites["subring_zero", "subring_one"];

(* Theorem: s <= r ==> s.sum.id = #0 /\ s.prod.id = #1 *)
(* Proof: by subring_zero, subring_one. *)
val subring_ids = store_thm(
  "subring_ids",
  ``!(r s):'a ring. s <= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)``,
  rw[]);

(* Theorem: s <= r ==> !x. x IN B ==> x IN R *)
(* Proof: by subring_def, ring_homo_element. *)
val subring_element_alt = store_thm(
  "subring_element_alt",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> x IN R``,
  metis_tac[subring_def, ring_homo_element, i_thm]);

(* Theorem: subring preserves sum and product. *)
(* Proof: by subring_def, ring_homo_property. *)
val subring_property = store_thm(
  "subring_property",
  ``!(r s):'a ring. Ring s /\ subring s r ==>
     !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)``,
  metis_tac[subring_def, ring_homo_property, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) *)
(* Proof: by subring_def, ring_homo_add. *)
val subring_add = store_thm(
  "subring_add",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)``,
  metis_tac[subring_def, ring_homo_add, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y) *)
(* Proof: by subring_def, ring_homo_mult. *)
val subring_mult = store_thm(
  "subring_mult",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)``,
  metis_tac[subring_def, ring_homo_mult, i_thm]);

(* Theorem: s <= r ==> !x. x IN B ==> (s.sum.inv x = -x) *)
(* Proof: by subring_def, ring_homo_neg. *)
val subring_neg = store_thm(
  "subring_neg",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> (s.sum.inv x = -x)``,
  metis_tac[subring_def, ring_homo_neg, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y) *)
(* Proof: by subring_def, ring_homo_sub. *)
val subring_sub = store_thm(
  "subring_sub",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)``,
  metis_tac[subring_def, ring_homo_sub, i_thm]);

(* Theorem: s <= r ==> !n. s.sum.exp s.prod.id n = ##n *)
(* Proof: by subring_def, ring_homo_num. *)
val subring_num = store_thm(
  "subring_num",
  ``!(r s):'a ring. s <= r ==> !n. s.sum.exp s.prod.id n = ##n``,
  metis_tac[subring_def, ring_homo_num, i_thm]);

(* Theorem: s <= r ==> !n. s.sum.exp s.prod.id n = ##n *)
(* Proof: by subring_def, ring_homo_exp. *)
val subring_exp = store_thm(
  "subring_exp",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n``,
  metis_tac[subring_def, ring_homo_exp, i_thm]);

(* Theorem: s <= r ==> (char r) (char s) divides *)
(* Proof: by subring_def, ring_homo_char_divides. *)
val subring_char_divides = store_thm(
  "subring_char_divides",
  ``!(r s):'a ring. s <= r ==> (char r) divides (char s)``,
  metis_tac[subring_def, ring_homo_char_divides, i_thm]);

(* Note: This seems wrong, but
   ring_homo_char_divides |- !r s. Ring r /\ Ring s ==> !f. RingHomo f r s ==> (char s) divides (char r)
   subring_def |- !s r. subring s r <=> RingHomo I s r
   So for subring s r, it is really (char r) divides (char s).
*)

(* Note:
There is no such theorem: m divides n ==> subring (ZN m) (ZN n)
This is because (ZN m) is (mod m), but (ZN n) is (mod n), totally different operations.
This means: (GF p) a subring of (ZN n), where prime p divides n, is not true!
*)

(* Theorem: s <= r ==> (char s = char r) *)
(* Proof:
     char s
   = order s.sum s.prod.id              by char_def
   = case OLEAST k. period r.sum #1 k
       of NONE => 0 | SOME k => k       by order_def
   = case OLEAST k. 0 < k /\ (s.sum.exp s.prod.id k = s.sum.id)
       of NONE => 0 | SOME k => k       by period_def
   = case OLEAST k. 0 < k /\ (##k = #0)
       of NONE => 0 | SOME k => k       by subring_num, subring_ids
   = order r.sum #1                     by order_def, period_def
   = char r                             by char_def
*)
val subring_char = store_thm(
  "subring_char",
  ``!(r s):'a ring. s <= r ==> (char s = char r)``,
  rw[char_def, order_def, period_def, subring_exp] >>
  metis_tac[subring_num, subring_ids]);

(* Theorem: s <= r ==> !x. Unit s x ==> unit x *)
(* Proof:
   Note s <= r ==> RingHomo I s r   by subring_def
   Thus Unit s x = unit (I x)       by ring_homo_unit
                 = unit x           by I_THM
*)
val subring_unit = store_thm(
  "subring_unit",
  ``!(r:'a ring) s. s <= r ==> !x. Unit s x ==> unit x``,
  metis_tac[ring_homo_unit, subring_def, combinTheory.I_THM]);

(* Theorem: s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0 *)
(* Proof:
   Note s <= r ==> RingHomo I s r   by subring_def
   Thus Unit s x <> s.prod.id       by ring_homo_unit_nonzero
     or          <> I #0 = #0       by I_THM
*)
val subring_unit_nonzero = store_thm(
  "subring_unit_nonzero",
  ``!(r:'a ring) s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0``,
  metis_tac[ring_homo_unit_nonzero, subring_def, combinTheory.I_THM]);

(* Theorem: s <= r ==> !x. Unit s x ==> (Inv s x) IN s.carrier *)
(* Proof:
   Note Unit s x                by subring_unit
   Thus (Inv s x) IN s.carrier  by ring_unit_inv_element

   Note:
> ring_homo_unit_inv_element |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f ==> !x. Unit s x ==> |/ (f x) IN R: thm
   This is not what we want to prove.
*)
val subring_unit_inv_element = store_thm(
  "subring_unit_inv_element",
  ``!(r s):'a ring. s <= r ==> !x. Unit s x ==> (Inv s x) IN s.carrier``,
  rw[subring_unit, ring_unit_inv_element]);

(* Theorem: s <= r /\ #1 <> #0 ==> !x. Unit s x ==> (Inv s x) <> #0 *)
(* Proof:
   Note Unit s x                        by subring_unit
   Thus (Inv s x) <> s.prod.id          by subring_unit_inv_nonzero
    and s.sum.id = #0, s.prod.id = #1   by subring_ids

   Note:
> ring_homo_unit_inv_nonzero |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f /\ #1 <> #0 ==> !x. Unit s x ==> |/ (f x) <> #0
   This is not what we want to prove.
*)
val subring_unit_inv_nonzero = store_thm(
  "subring_unit_inv_nonzero",
  ``!(r s):'a ring. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> (Inv s x) <> #0``,
  metis_tac[subring_unit, ring_unit_inv_nonzero, subring_ids]);

(* Theorem: s <= r ==> !x. Unit s x ==> (Inv s x = |/ x) *)
(* Proof:
   Let z = Inv s x.
   Note x IN s.carrier        by ring_unit_element
    and z IN s.carrier        by ring_unit_inv_element
   Thus x IN R /\ z IN R      by subring_element
   Also unit x                by subring_unit
        x * z
      = s.prod.op x z         by subring_mult
      = s.prod.id             by ring_unit_rinv
      = #1                    by subring_one
   Hence z = |/x              by ring_unit_rinv_unique
*)
Theorem subring_unit_inv:
  !(r s):'a ring. s <= r ==> !x. Unit s x ==> (Inv s x = |/ x)
Proof
  metis_tac[ring_homo_unit_inv, subring_def, combinTheory.I_THM]
QED

(* Theorem: subring s r /\ RingIso f r r_ ==> RingHomo f s r_ *)
(* Proof:
   Note subring s r ==> RingHomo I s r         by subring_def
    and RingIso f r r_  ==> RingHomo f r r_    by RingIso_def
   Thus RingHomo (f o I) s r_                  by ring_homo_compose
     or RingHomo f s r_                        by I_o_ID
*)
val subring_ring_iso_compose = store_thm(
  "subring_ring_iso_compose",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. subring s r /\ RingIso f r r_ ==> RingHomo f s r_``,
  rpt strip_tac >>
  `RingHomo I s r` by rw[GSYM subring_def] >>
  `RingHomo f r r_` by metis_tac[RingIso_def] >>
  prove_tac[ring_homo_compose, combinTheory.I_o_ID]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of Ring.                                                *)
(* ------------------------------------------------------------------------- *)

(* Define the homomorphic image of a ring. *)
val homo_ring_def = Define`
  homo_ring (r:'a ring) (f:'a -> 'b) =
    <| carrier := IMAGE f R;
           sum := homo_group (r.sum) f;
          prod := homo_monoid (r.prod) f
     |>
`;

(* set overloading *)
val _ = overload_on ("fR", ``(homo_ring (r:'a ring) (f:'a -> 'b)).carrier``);

(* Theorem: Properties of homo_ring. *)
(* Proof: by homo_ring_def. *)
val homo_ring_property = store_thm(
  "homo_ring_property",
  ``!(r:'a ring) (f:'a -> 'b). (fR = IMAGE f R) /\
      ((homo_ring r f).sum = homo_group (r.sum) f) /\
      ((homo_ring r f).prod = homo_monoid (r.prod) f)``,
  rw_tac std_ss[homo_ring_def]);

(* Theorem: Homomorphic image of a Ring is a Ring. *)
(* Proof:
   This is to show each of these:
   (1) GroupHomo f r.sum (homo_ring r f).sum ==> AbelianGroup (homo_ring r f).sum
       Note AbelianGroup r.sum                           by Ring_def
        and (homo_ring r f).sum = homo_group r.sum f     by homo_ring_property
       Thus GroupHomo f r.sum (homo_group r.sum f)       by above
        ==> AbelianGroup (homo_group r.sum f)            by homo_group_abelian_group
         or AbelianGroup (homo_ring r f).sum             by above
   (2) MonoidHomo f r.prod (homo_ring r f).prod ==> AbelianMonoid (homo_ring r f).prod
       Note AbelianMonoid r.prod                         by Ring_def
        and (homo_ring r f).prod = homo_group r.prod f   by homo_ring_property
       Thus MonoidHomo f r.prod (homo_group r.prod f)    by above
        ==> AbelianMonoid (homo_group r.prod f)          by homo_monoid_abelian_monoid
         or AbelianMonoid (homo_ring r f).prod           by above
   (3) (homo_ring r f).sum.carrier = fR
            (homo_ring r f).sum.carrier
          = (homo_group r.sum f).carrier                 by homo_ring_property
          = IMAGE f r.sum.carrier                        by homo_monoid_property
          = IMAGE f R = fR                               by ring_carriers
   (4) (homo_ring r f).prod.carrier = fR
            (homo_ring r f).prod.carrier
          = (homo_group r.prod f).carrier                by homo_ring_property
          = IMAGE f r.prod.carrier                       by homo_monoid_property
          = IMAGE f R = fR                               by ring_carriers
   (5) x IN fR /\ y IN fR /\ z IN fR ==>
        (homo_ring r f).prod.op x ((homo_ring r f).sum.op y z) =
        (homo_ring r f).sum.op ((homo_ring r f).prod.op x y) ((homo_ring r f).prod.op x z)
       Note ?a. x = f a /\ a IN R                        by homo_ring_property, IN_IMAGE
        and ?b. y = f b /\ b IN R                        by homo_ring_property, IN_IMAGE
        and ?c. z = f c /\ c IN R                        by homo_ring_property, IN_IMAGE
        (homo_ring r f).prod.op x ((homo_ring r f).sum.op y z)
      = (homo_ring r f).prod.op x (f (b + c))            by GroupHomo_def, ring_carriers
      = f (a * (b + c))                                  by MonoidHomo_def, ring_carriers
      = f (a * b + a * c)                                by ring_mult_radd
      = (homo_ring r f).sum.op (a * b) (a * c)           by MonoidHomo_def, ring_carriers
      = (homo_ring r f).sum.op ((homo_ring r f).prod.op x y)
                               ((homo_ring r f).prod.op x z)  by GroupHomo_def, ring_carriers
*)
val homo_ring_ring = store_thm(
  "homo_ring_ring",
  ``!(r:'a ring) f. Ring r /\ RingHomo f r (homo_ring r f) ==> Ring (homo_ring r f)``,
  rw_tac std_ss[RingHomo_def] >>
  rw_tac std_ss[Ring_def] >| [
    fs[homo_ring_property] >>
    `AbelianGroup r.sum` by metis_tac[Ring_def] >>
    rw[homo_group_abelian_group],
    fs[homo_ring_property] >>
    `AbelianMonoid r.prod` by metis_tac[Ring_def] >>
    rw[homo_monoid_abelian_monoid],
    fs[homo_ring_property] >>
    rw[homo_monoid_property, ring_carriers],
    fs[homo_ring_property] >>
    rw[homo_monoid_property, ring_carriers],
    fs[homo_ring_property] >>
    `x' * (x'' + x''') = x' * x'' + x' * x'''` by rw[ring_mult_radd] >>
    `x'' + x''' IN R /\ x' * x'' IN R /\ x' * x''' IN R` by rw[] >>
    fs[GroupHomo_def, MonoidHomo_def] >>
    metis_tac[ring_carriers]
  ]);

(* Theorem: Homomorphic image of a Ring is a subring of the target ring. *)
(* Proof:
   This is to show each of these:
   (1) RingHomo f r s /\ x IN fR ==> x IN s.carrier
           x IN fR
       ==> x IN IMAGE f R       by homo_ring_property
       ==> ?z. x = f x, x IN R  by IN_IMAGE
       ==> f x IN s.carrier     by RingHomo_def
   (2) RingHomo f r s ==> GroupHomo I (homo_ring r f).sum s.sum
       RingHomo f r s ==> GroupHomo f r.sum s.sum  by RingHomo_def
       hence this is to show: GroupHomo f r.sum s.sum ==> GroupHomo I (homo_ring r f).sum s.sum
       Expand by definitions, need to show:
       (2.1) x IN IMAGE f r.sum.carrier /\ (!x. x IN r.sum.carrier ==> f x IN s.sum.carrier) ==> x IN s.sum.carrier
             True by IN_IMAGE.
       (2.2) x IN IMAGE f r.sum.carrier /\ y IN IMAGE f r.sum.carrier /\ ... ==>
             f (CHOICE (preimage f r.sum.carrier x) + CHOICE (preimage f r.sum.carrier y)) = s.sum.op x y
             True by preimage_choice_property.
   (3) RingHomo f r s ==> MonoidHomo I (homo_ring r f).prod s.prod
       RingHomo f r s ==> MonoidHomo f r.prod s.prod   by RingHomo_def
       hence this is to show: MonoidHomo f r.prod s.prod ==> MonoidHomo I (homo_ring r f).prod s.prod
       Expand by definitions, need to show:
       (3.1) x IN IMAGE f r.prod.carrier /\ (!x. x IN r.prod.carrier ==> f x IN s.prod.carrier) ==> x IN s.prod.carrier
             True by IN_IMAGE.
       (3.2) x IN IMAGE f r.prod.carrier /\ y IN IMAGE f r.prod.carrier /\ ... ==>
             f (CHOICE (preimage f r.prod.carrier x) * CHOICE (preimage f r.prod.carrier y)) = s.prod.op x y
             True by preimage_choice_property.
*)
val homo_ring_subring = store_thm(
  "homo_ring_subring",
  ``!(r:'a ring) (s:'b ring) f. Ring r /\ Ring s /\ RingHomo f r s ==> subring (homo_ring r f) s``,
  rpt strip_tac >>
  rw_tac std_ss[subring_def, RingHomo_def] >| [
    metis_tac[homo_ring_property, IN_IMAGE, RingHomo_def],
    `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
    pop_assum mp_tac >>
    rw_tac std_ss[GroupHomo_def, homo_ring_property, homo_monoid_property] >| [
      metis_tac[IN_IMAGE],
      metis_tac[preimage_choice_property]
    ],
    `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
    pop_assum mp_tac >>
    rw_tac std_ss[MonoidHomo_def, homo_ring_property, homo_monoid_property] >| [
      metis_tac[IN_IMAGE],
      metis_tac[preimage_choice_property]
    ]
  ]);

(* Theorem: Ring r /\ INJ f R UNIV ==> RingHomo f r (homo_ring r f) *)
(* Proof:
   By RingHomo_def, homo_ring_property, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true                by IN_IMAGE
   (2) GroupHomo f r.sum (homo_group r.sum f), true     by homo_group_by_inj
   (3) MonoidHomo f r.prod (homo_group r.prod f), true  by homo_monoid_by_inj
*)
val homo_ring_by_inj = store_thm(
  "homo_ring_by_inj",
  ``!(r:'a ring) (f:'a -> 'b). Ring r /\ INJ f R UNIV ==> RingHomo f r (homo_ring r f)``,
  rw_tac std_ss[RingHomo_def, homo_ring_property] >-
  rw[] >-
  rw[homo_group_by_inj] >>
  rw[homo_monoid_by_inj]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image between Rings.                                          *)
(* ------------------------------------------------------------------------- *)

(* Define homomorphism image of Ring *)
val ring_homo_image_def = Define`
  ring_homo_image f (r:'a ring) (r_:'b ring) =
     <| carrier := IMAGE f R;
            sum := homo_image f r.sum r_.sum;
           prod := homo_image f r.prod r_.prod
      |>
`;
(*
We have these (based on image_op):
- homo_ring_def;
> val it = |- !r f. homo_ring r f = <|carrier := IMAGE f R;
                                          sum := homo_group r.sum f;
                                         prod := homo_group r.prod f
                                     |> : thm
- homo_monoid_def;
> val it = |- !g f. homo_group g f = <|carrier := IMAGE f G;
                                            op := image_op g f;
                                            id := f #e
                                      |> : thm
We also have (based on real op):
- homo_image_def;
> val it = |- !f g h. homo_image f g h = <|carrier := IMAGE f G;
                                                op := h.op;
                                                id := h.id
                                          |> : thm
So ring_homo_image is based on homo_image.
*)

(* Theorem: (ring_homo_image f r r_).carrier = IMAGE f R *)
(* Proof: by ring_homo_image_def *)
val ring_homo_image_carrier = store_thm(
  "ring_homo_image_carrier",
  ``!(r:'a ring) (r_:'b ring) f. (ring_homo_image f r r_).carrier = IMAGE f R``,
  rw_tac std_ss[ring_homo_image_def]);

(* Theorem: (r ~r~ r_) f ==> Ring (ring_homo_image f r r_) *)
(* Proof:
   By ring_homo_image_def, Ring_def, this is to show:
   (1) AbelianGroup (homo_image f r.sum r_.sum)
       Ring r ==> Group r.sum /\ !x y. x IN R /\ y IN R ==> (x + y = y + x)         by ring_add_group
       Ring r_ ==> Group r_.sum /\ !x y. x IN R_ /\ y IN R_ ==> (x +_ y = y +_ x)   by ring_add_group
       Thus Group (homo_image f r.sum r_.sum)                                       by homo_image_group
       And  !x' x''. x' IN R /\ x'' IN R ==> f x' +_ f x'' = f x'' +_ f x'          by commutative properties
       Hence AbelianGroup (homo_image f r.sum r_.sum)                               by AbelianGroup_def
   (2) AbelianMonoid (homo_image f r.prod r_.prod)
       Ring r ==> Monoid r.prod /\ !x y. x IN R /\ y IN R ==> (x * y = y * x)       by ring_mult_monoid
       Ring s ==> Monoid r_.prod /\ !x y. x IN R_ /\ y IN R_ ==> (x *_ y = y *_ x)  by ring_mult_monoid
       Thus Monoid (homo_image f r.prod r_.prod)                                    by homo_image_monoid
       And  !x' x''. x' IN R /\ x'' IN R ==> f x' *_ f x'' = f x'' *_ f x'          by commutative properties
       Hence AbelianMonoid (homo_image f r.prod r_.prod)                            by AbelianMonoid_def
   (3) (homo_image f r.sum r_.sum).carrier = IMAGE f R
       True by ring_add_group, homo_image_def.
   (4) (homo_image f r.prod r_.prod).carrier = IMAGE f R
       True by ring_mult_monoid, homo_image_def
   (5) x IN IMAGE f R /\ y IN IMAGE f R /\ z IN IMAGE f R ==> x *_ (y +_ z) = x *_ y +_ x *_ z
       By IN_IMAGE, there are a IN R with f a = x, hence x = f a IN R_
                              b IN R with f b = y, hence y = f b IN R_
                          and c IN R with f c = z, hence z = f c IN R_
       Hence true by ring_mult_radd.
*)
val ring_homo_image_ring = store_thm(
  "ring_homo_image_ring",
  ``!(r:'a ring) (r_:'b ring). !f. (r ~r~ r_) f ==> Ring (ring_homo_image f r r_)``,
  rw_tac std_ss[RingHomo_def] >>
  `!x. x IN IMAGE f R ==> ?a. a IN R /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[ring_homo_image_def, Ring_def] >| [
    `Group r.sum /\ !x y. x IN R /\ y IN R ==> (x + y = y + x)` by rw[ring_add_group] >>
    `Group r_.sum /\ !x y. x IN R_ /\ y IN R_ ==> (x +_ y = y +_ x)` by rw[ring_add_group] >>
    `Group (homo_image f r.sum r_.sum)` by rw[homo_image_group] >>
    rw[AbelianGroup_def, homo_image_def] >>
    metis_tac[],
    `Monoid r.prod /\ !x y. x IN R /\ y IN R ==> (x * y = y * x)` by rw[ring_mult_monoid] >>
    `Monoid r_.prod /\ !x y. x IN R_ /\ y IN R_ ==> (x *_ y = y *_ x)` by rw[ring_mult_monoid] >>
    `Monoid (homo_image f r.prod r_.prod)` by rw[homo_image_monoid] >>
    rw[AbelianMonoid_def, homo_image_def] >>
    metis_tac[],
    rw[homo_image_def],
    rw[homo_image_def],
    rw[homo_image_def] >>
    `x IN R_ /\ y IN R_ /\ z IN R_` by metis_tac[] >>
    rw[]
  ]);

(* Theorem: (r ~r~ r_) f ==> !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_ *)
(* Proof:
   Note RingHomo I s r               by subring_def
   By RingHomo_def, this is to show:
   (1) x IN (ring_homo_image f s r_).carrier ==> x IN R_
           x IN (ring_homo_image f s r_).carrier
       ==> x IN IMAGE f B            by ring_homo_image_def
       ==> ?y. y IN B /\ (f y = x)   by IN_IMAGE
       ==> ?y. y IN R /\ (f y = x)   by RingHomo_def, RingHomo I s r
       ==> x IN IMAGE f R            by IN_IMAGE
       ==> x IN R_                   by notation
   (2) GroupHomo I (ring_homo_image f s r_).sum r_.sum
       By GroupHomo_def, ring_homo_image_def, homo_image_def, this is to show:
          y IN B ==> f y IN R_, true by RingHomo_def
   (3) MonoidHomo I (ring_homo_image f s r_).prod r_.prod
       By MonoidHomo_def, ring_homo_image_def, homo_image_def, this is to show:
          y IN B ==> f y IN R_, true by RingHomo_def
*)
val ring_homo_image_subring_subring = store_thm(
  "ring_homo_image_subring_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_``,
  rw[subring_def] >>
  rw_tac std_ss[RingHomo_def] >| [
    fs[ring_homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM],
    rw[GroupHomo_def, ring_homo_image_def, homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM],
    rw[MonoidHomo_def, ring_homo_image_def, homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM]
  ]);

(* Theorem: (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_ *)
(* Proof:
   Note subring r r                           by subring_refl
   Thus subring (ring_homo_image f r r_) r_   by ring_homo_image_subring_subring
*)
val ring_homo_image_is_subring = store_thm(
  "ring_homo_image_is_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_``,
  metis_tac[ring_homo_image_subring_subring, subring_refl]);

(* Theorem: (r ~r~ r_) f ==> (ring_homo_image f r r_) <= r_ *)
(* Proof: by ring_homo_image_ring, ring_homo_image_is_subring  *)
val ring_homo_image_subring = store_thm(
  "ring_homo_image_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (ring_homo_image f r r_) <= r_``,
  rw_tac std_ss[ring_homo_image_ring, ring_homo_image_is_subring]);

(* Theorem: (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN R ==> f x IN (ring_homo_image f r r_).carrier
       True by ring_homo_image_def.
   (2) GroupHomo f r.sum (ring_homo_image f r r_).sum
       Expanding by definitions, this is to show: f (x + y) = f x +_ f y
       True by ring_homo_property.
   (3) MonoidHomo f r.prod (ring_homo_image f r r_).prod
       Expanding by definitions, this is to show: f (x * y) = f x *_ f y
       True by ring_homo_property.
*)
val ring_homo_image_homo = store_thm(
  "ring_homo_image_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_)``,
  rpt strip_tac >>
  rw_tac std_ss[RingHomo_def] >-
  rw[ring_homo_image_def] >-
  rw[GroupHomo_def, ring_homo_image_def, homo_image_def, ring_homo_property] >>
  rw[MonoidHomo_def, ring_homo_image_def, homo_image_def, ring_homo_property]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> BIJ f R (ring_homo_image f r r_).carrier *)
(* Proof:
   Since (ring_homo_image f r r_).carrier = IMAGE f R     by ring_homo_image_def
   Hence true given INJ f R R_                            by INJ_IMAGE_BIJ
*)
val ring_homo_image_bij = store_thm(
  "ring_homo_image_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> BIJ f R (ring_homo_image f r r_).carrier``,
  rpt strip_tac >>
  `(ring_homo_image f r r_).carrier = IMAGE f R` by rw[ring_homo_image_def] >>
  metis_tac[INJ_IMAGE_BIJ]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> RingIso f r (ring_homo_image f r r_) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f r r_ ==> RingHomo f r (ring_homo_image f r s), true by ring_homo_image_homo
   (2) RingHomo f r r_ /\ INJ f R R_ ==>
       BIJ f R (ring_homo_image f r r_).carrier, true by ring_homo_image_bij.
*)
val ring_homo_image_iso = store_thm(
  "ring_homo_image_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> RingIso f r (ring_homo_image f r r_)``,
  rw[RingIso_def, ring_homo_image_homo, ring_homo_image_bij]);

(* This turns RingHomo to RingIso, for the same function. *)

(* Theorem: Ring r /\ Ring r_ /\ SURJ f R R_ ==> RingIso I r_ (ring_homo_image f r r_) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo I r_ (ring_homo_image f r r_)
       After expanding by definitions and ring_carriers,
       the goal is: SURJ f R R_ /\ x IN R_ ==> x IN IMAGE f R
       This is true by SURJ_DEF, IN_IMAGE.
   (2) SURJ f R R_ ==> BIJ I R_ (ring_homo_image f r r_).carrier
       After expanding by definitions and ring_carriers, this is to show:
       (1) SURJ f R R_ ==> INJ I R_ (IMAGE f R)
           By INJ_DEF, this is true by SURJ_DEF, IN_IMAGE.
       (2) SURJ f R R_ ==> SURJ I R_ (IMAGE f R)
           By SURJ_DEF, this is true by SURJ_DEF, IN_IMAGE.
*)
val ring_homo_image_surj_property = store_thm(
  "ring_homo_image_surj_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ SURJ f R R_ ==> RingIso I r_ (ring_homo_image f r r_)``,
  rw_tac std_ss[RingIso_def] >| [
    rw_tac std_ss[RingHomo_def, GroupHomo_def, MonoidHomo_def, ring_homo_image_def, homo_image_def, ring_carriers] >>
    metis_tac[SURJ_DEF, IN_IMAGE],
    rw_tac std_ss[BIJ_DEF, ring_homo_image_def, homo_image_def, ring_carriers] >| [
      rw_tac std_ss[INJ_DEF] >>
      metis_tac[SURJ_DEF, IN_IMAGE],
      rewrite_tac[SURJ_DEF, combinTheory.I_THM] >>
      metis_tac[SURJ_DEF, IN_IMAGE]
    ]
  ]);

(* Theorem: (r ~r~ r_) f /\ s <= r ==> (s ~r~ (ring_homo_image f s r_)) f *)
(* Proof:
   Note RingHomo f s r_                              by subring_homo_homo
   This is to show:
   (1) Ring (ring_homo_image f s r_), true           by ring_homo_image_ring
   (2) RingHomo f s (ring_homo_image f s r_), true   by ring_homo_image_homo
*)
val ring_homo_subring_homo = store_thm(
  "ring_homo_subring_homo",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ s <= r ==> (s ~r~ (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `RingHomo f s r_` by metis_tac[subring_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_ring] >>
  rw[ring_homo_image_homo]);

(* Theorem: (r =r= r_) f /\ s <= r ==> (s =r= (ring_homo_image f s r_)) f *)
(* Proof:
   Note RingHomo f r r_ /\ INJ f R R_    by RingIso_def
    ==> RingHomo f s r_                  by subring_homo_homo
   This is to show:
   (1) Ring (ring_homo_image f s r_), true  by ring_homo_image_ring
   (2) RingIso f s (ring_homo_image f s r_)
       Note INJ f R R_                             by BIJ_DEF
        ==> INJ f B R_                             by INJ_SUBSET, subring_carrier_subset, SUBSET_REFL
       Thus RingIso f s (ring_homo_image f s r_)   by ring_homo_image_iso
*)
val ring_iso_subring_iso = store_thm(
  "ring_iso_subring_iso",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. (r =r= r_) f /\ s <= r ==> (s =r= (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `RingHomo f r r_ /\ BIJ f R R_` by metis_tac[RingIso_def] >>
  `RingHomo f s r_` by metis_tac[subring_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_ring] >>
  `INJ f B R_` by metis_tac[BIJ_DEF, INJ_SUBSET, subring_carrier_subset, SUBSET_REFL] >>
  rw[ring_homo_image_iso]);

(* Theorem alias *)
val ring_homo_ring_homo_subring = save_thm("ring_homo_ring_homo_subring", ring_homo_image_is_subring);
(*
val ring_homo_ring_homo_subring = |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_: thm
*)

(* Theorem: (r =r= r_) f ==> subring (ring_homo_image f r r_) r_ *)
(* Proof:
   Note RingIso f r r_ ==> RingHomo f r r_   by RingIso_def
   Thus subring (ring_homo_image f r r_) r_  by ring_homo_ring_homo_subring
*)
val ring_iso_ring_homo_subring = store_thm(
  "ring_iso_ring_homo_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> subring (ring_homo_image f r r_) r_``,
  rw_tac std_ss[ring_homo_ring_homo_subring, RingIso_def]);

(* Theorem: s <= r /\ (r =r= r_) f ==> (ring_homo_image f s r_) <= r_ *)
(* Proof:
   Note RingHomo f s r_                    by subring_ring_iso_compose
   Thus (s ~r~ r_) f                       by notation, Ring s
    ==> (ring_homo_image f s r_) <= r_     by ring_homo_image_subring
*)
val subring_ring_iso_ring_homo_subring = store_thm(
  "subring_ring_iso_ring_homo_subring",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. s <= r /\ (r =r= r_) f ==> (ring_homo_image f s r_) <= r_``,
  metis_tac[ring_homo_image_subring, subring_ring_iso_compose]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Ring.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Ring r, and an injective function f,
   then the image (f R) is a Ring, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a ring injective image for an injective f, with LINV f R. *)
Definition ring_inj_image_def:
   ring_inj_image (r:'a ring) (f:'a -> 'b) =
       <| carrier := IMAGE f R;
              sum := <| carrier := IMAGE f R; op := (\x y. f ((LINV f R x) + LINV f R y)); id := f #0 |>;
             prod := <| carrier := IMAGE f R; op := (\x y. f ((LINV f R x) * LINV f R y)); id := f #1 |>
        |>
End

(* Theorem: (ring_inj_image r f).carrier = IMAGE f R *)
(* Proof: by ring_inj_image_def *)
Theorem ring_inj_image_carrier:
  !(r:'a ring) f. (ring_inj_image r f).carrier = IMAGE f R
Proof
  simp[ring_inj_image_def]
QED

(* Alternative definitaion the image of ring injection, so that LINV f R makes sense. *)

(* Theorem: equivalent definition of ring_inj_image r f. *)
(* Proof:
   By ring_inj_image_def, monoid_inj_image_def, and component_equality of types,
   this is to show:
   (1) IMAGE f R = IMAGE f r.sum.carrier, true         by ring_carriers
   (2) (\x y. f (LINV f r.sum.carrier x + LINV f r.sum.carrier y)) =
       (\x y. f (LINV f R x + LINV f R y)), true       by ring_carriers
   (3) IMAGE f R = IMAGE f r.prod.carrier, true        by ring_carriers
   (4) (\x y. f (LINV f r.prod.carrier x * LINV f r.prod.carrier y)) =
       (\x y. f (LINV f R x * LINV f R y)), true       by ring_carriers
*)
Theorem ring_inj_image_alt:
  !(r:'a ring) (f:'a -> 'b).  Ring r ==>
     ring_inj_image r f = <| carrier := IMAGE f R;
                                 sum := monoid_inj_image r.sum f;
                                prod := monoid_inj_image r.prod f
                           |>
Proof
  simp[ring_inj_image_def, monoid_inj_image_def, ring_component_equality, monoid_component_equality]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f) *)
(* Proof:
   By Ring_def and ring_inj_image_alt, this is to show:
   (1) AbelianGroup (monoid_inj_image r.sum f)
           Ring r
       ==> AbelianGroup (r.sum)                        by ring_add_abelian_group
       ==> AbelianGroup (monoid_inj_image r.sum f)     by group_inj_image_abelian_group
   (2) AbelianMonoid (monoid_inj_image r.prod f)
           Ring r
       ==> AbelianMonoid (r.prod)                      by ring_mult_abelian_monoid
       ==> AbelianMonoid (monoid_inj_image r.prod f)   by monoid_inj_image_abelian_monoid
   (3) (monoid_inj_image r.sum f).carrier = IMAGE f R
         (monoid_inj_image r.sum f).carrier
       = IMAGE f r.sum.carrier                         by monoid_inj_image_def
       = IMAGE f R                                     by ring_carriers
   (4) (monoid_inj_image r.prod f).carrier = IMAGE f R
         (monoid_inj_image r.prod f).carrier
       = IMAGE f r.prod.carrier                        by monoid_inj_image_def
       = IMAGE f R                                     by ring_carriers
   (5) x IN IMAGE f R /\ y IN IMAGE f R /\ z IN IMAGE f R ==>
       f (t x * t (f (t y + t z))) = f (t (f (t x * t y)) + t (f (t x * t z)))
       by monoid_inj_image_def, ring_carriers, where t = LINV f R.
       Note INJ f R univ(:'b) ==> BIJ f R (IMAGE f R)  by INJ_IMAGE_BIJ_ALT
         so !x. x IN R ==> t (f x) = x
        and !x. x IN (IMAGE f R) ==> f (t x) = x       by BIJ_LINV_THM
       Note ?a. (x = f a) /\ a IN R                    by IN_IMAGE
            ?b. (y = f b) /\ b IN R                    by IN_IMAGE
            ?c. (z = f c) /\ c IN R                    by IN_IMAGE
       LHS = f (t x * t (f (t y + t z)))
           = f (t (f a) * t (f (t (f b) + t (f c))))   by x = f a, y = f b, z = f c
           = f (a * t (f (b + c)))                     by !y. t (f y) = y
           = f (a * (b + c))                           by !y. t (f y) = y, ring_add_element
       RHS = f (t (f (t x * t y)) + t (f (t x * t z)))
           = f (t (f (t (f a) * t (f b))) + t (f (t (f a) * t (f b))))   by x = f a, y = f b, z = f c
           = f (t (f (a * b)) + t (f (a * b)))         by !y. t (f y) = y
           = f (a * b + a * c)                         by !y. t (f y) = y, ring_mult_element
           = f (a * (b + c))                           by ring_mult_ladd
           = LHS
*)
Theorem ring_inj_image_ring:
  !(r:'a ring) (f:'a -> 'b).
    Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f)
Proof
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, ring_inj_image_alt] >-
  rw[ring_add_abelian_group, group_inj_image_abelian_group] >-
  rw[ring_mult_abelian_monoid, monoid_inj_image_abelian_monoid] >-
  rw[monoid_inj_image_def] >-
  rw[monoid_inj_image_def] >>
  rw_tac std_ss[monoid_inj_image_def, ring_carriers] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  `BIJ f R (IMAGE f R)` by rw[INJ_IMAGE_BIJ_ALT] >>
  imp_res_tac BIJ_LINV_THM >>
  rpt strip_tac >>
  `?a. (x = f a) /\ a IN R` by rw[GSYM IN_IMAGE] >>
  `?b. (y = f b) /\ b IN R` by rw[GSYM IN_IMAGE] >>
  `?c. (z = f c) /\ c IN R` by rw[GSYM IN_IMAGE] >>
  rw[ring_mult_ladd, Abbr`t`]
QED

(* The following will be applied to finite fields, for existence and extension. *)

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF
   Note !x. x IN R ==> f x IN s                by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R         by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)    by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)    by BIJ_LINV_THM

   Let xx = LINV f R x, yy = LINV f R y, zz = LINV f R z.
   By Monoid_def, ring_inj_image_def, this is to show:
   (1) x IN s /\ y IN s ==> f (xx + yy) IN s, true by ring_add_element
   (2) x IN s /\ y IN s /\ z IN s ==> f (LINV f R (f (xx + yy)) + zz) = f (xx + LINV f R (f (yy + zz)))
       Since LINV f R (f (xx + yy)) = xx + yy  by ring_add_element
         and LINV f R (f (yy + zz)) = yy + zz  by ring_add_element
       The result follows                      by ring_add_assoc
   (3) f #0 IN s, true                         by ring_zero_element
   (4) x IN s ==> f (LINV f R (f #0) + xx) = x
       Since LINV f R (f #0) = #0              by ring_zero_element
       f (#0 + xx) = f xx = x                  by ring_add_lzero
   (5) x IN s ==> f (xx + LINV f R (f #0)) = x
       Since LINV f R (f #0) = #0              by ring_zero_element
       f (xx + #0) = f xx = x                  by ring_add_rzero
*)
Theorem ring_inj_image_sum_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw_tac std_ss[Monoid_def, ring_inj_image_def] >-
  rw[] >-
 (qabbrev_tac `xx = LINV f R x` >>
  qabbrev_tac `yy = LINV f R y` >>
  qabbrev_tac `zz = LINV f R z` >>
  `LINV f R (f (xx + yy)) = xx + yy` by metis_tac[ring_add_element] >>
  `LINV f R (f (yy + zz)) = yy + zz` by metis_tac[ring_add_element] >>
  rw[ring_add_assoc, Abbr`xx`, Abbr`yy`, Abbr`zz`]) >-
  rw[] >-
  rw[] >>
  rw[]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (ring_inj_image r f).sum, true     by ring_inj_image_sum_monoid
   (2) monoid_invertibles (ring_inj_image r f).sum = (ring_inj_image r f).sum.carrier
      Let xx = LINV f R x.
       By ring_inj_image_def, monoid_invertibles_def, this is to show:
       x IN IMAGE f R ==> ?y. y IN IMAGE f R /\ (f (xx + LINV f R y) = f #0) /\ (f (LINV f R y + xx) = f #0)
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
      Since -xx IN R                             by ring_neg_element
       Take y = f (-xx).
       Then y = f (-xx) IN s                     by above
        and LINV f R y = LINV f R (-xx) = -xx    by above
       Also f (xx + -xx) = f #0                  by ring_add_rneg
        and f (-xx + xx) = f #0                  by ring_add_lneg
*)
Theorem ring_inj_image_sum_group:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum
Proof
  rw[Group_def] >-
  rw[ring_inj_image_sum_monoid] >>
  rw_tac std_ss[ring_inj_image_def, monoid_invertibles_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  qabbrev_tac `xx = LINV f R x` >>
  `-xx IN R` by rw[Abbr`xx`] >>
  metis_tac[ring_add_lneg, ring_add_rneg, ring_zero_element]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group (ring_inj_image r f).sum, true      by ring_inj_image_sum_group
   (2) x' IN R /\ x'' IN R ==>
       f (LINV f R (f x') + LINV f R (f x'')) = f (LINV f R (f x'') + LINV f R (f x'))
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
       The result follows                        by ring_add_comm
*)
Theorem ring_inj_image_sum_abelian_group:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum
Proof
  rw[AbelianGroup_def] >-
  rw[ring_inj_image_sum_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw[ring_add_comm]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF
   Note !x. x IN R ==> f x IN s                by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R         by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)    by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)    by BIJ_LINV_THM

   Let xx = LINV f R x, yy = LINV f R y, zz = LINV f R z.
   By Monoid_def, ring_inj_image_def, this is to show:
   (1) x IN s /\ y IN s ==> f (xx * yy) IN s, true by ring_mult_element
   (2) x IN s /\ y IN s /\ z IN s ==> f (LINV f R (f (xx * yy)) * zz) = f (xx * LINV f R (f (yy * zz)))
       Since LINV f R (f (xx * yy)) = xx * yy  by ring_mult_element
         and LINV f R (f (yy * zz)) = yy * zz  by ring_mult_element
       The result follows                      by ring_mult_assoc
   (3) f #1 IN s, true                         by ring_one_element
   (4) x IN s ==> f (LINV f R (f #1) * xx) = x
       Since LINV f R (f #1) = #1              by ring_one_element
       f (#1 * xx) = f xx = x                  by ring_mult_lone
   (5) x IN s ==> f (xx * LINV f R (f #1)) = x
       Since LINV f R (f #1) = #1              by ring_one_element
       f (xx * #1) = f xx = x                  by ring_mult_rone
*)
Theorem ring_inj_image_prod_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw_tac std_ss[Monoid_def, ring_inj_image_def] >-
  rw[] >-
 (qabbrev_tac `xx = LINV f R x` >>
  qabbrev_tac `yy = LINV f R y` >>
  qabbrev_tac `zz = LINV f R z` >>
  `LINV f R (f (xx * yy)) = xx * yy` by metis_tac[ring_mult_element] >>
  `LINV f R (f (yy * zz)) = yy * zz` by metis_tac[ring_mult_element] >>
  rw[ring_mult_assoc, Abbr`xx`, Abbr`yy`, Abbr`zz`]) >-
  rw[] >-
  rw[] >>
  rw[]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Monoid (ring_inj_image r f).prod, true    by ring_inj_image_prod_monoid
   (2) x' IN R /\ x'' IN R ==>
       f (LINV f R (f x') * LINV f R (f x'')) = f (LINV f R (f x'') * LINV f R (f x'))
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
       The result follows                        by ring_mult_comm
*)
Theorem ring_inj_image_prod_abelian_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod
Proof
  rw[AbelianMonoid_def] >-
  rw[ring_inj_image_prod_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw[ring_mult_comm]
QED


(* Theorem: Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum *)
(* Proof:
   Note R = r.prod.carrier                     by ring_carriers
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF

   By GroupHomo_def, ring_inj_image_def, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x + y) = f (LINV f R (f x) + LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem ring_inj_image_sum_group_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum
Proof
  rw[GroupHomo_def, ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod *)
(* Proof:
   Note R = r.prod.carrier                     by ring_carriers
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF

   By MonoidHomo_def, ring_inj_image_def, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem ring_inj_image_prod_monoid_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod
Proof
  rw[MonoidHomo_def, ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN R ==> f x IN (ring_inj_image r f).carrier
       Note (ring_inj_image r f).carrier = IMAGE f R       by ring_inj_image_carrier
       Thus f x IN IMAGE f R                               by INJ_DEF, IN_IMAGE
   (2) GroupHomo f r.sum (ring_inj_image r f).sum, true    by ring_inj_image_sum_group_homo
   (3) MonoidHomo f r.prod (ring_inj_image r f).prod, true by ring_inj_image_prod_monoid_homo
*)
Theorem ring_inj_image_ring_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f)
Proof
  rw_tac std_ss[RingHomo_def] >-
  rw[ring_inj_image_carrier, INJ_DEF] >-
  rw[ring_inj_image_sum_group_homo] >>
  rw[ring_inj_image_prod_monoid_homo]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
