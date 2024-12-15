(* ------------------------------------------------------------------------- *)
(* Polynomial Quotient Ring by a Modulus                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyModuloRing";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory;

open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory;

open polyFieldTheory;

val _ = intLib.deprecate_int ();
val _ = hide "Z";

(* ------------------------------------------------------------------------- *)
(* Polynomial Quotient Ring by a Modulus Documentation                       *)
(* ------------------------------------------------------------------------- *)
(* Data type:

   Overloads:
   PolyModRing r z  = poly_mod_ring r z
   Rz               = (PolyModRing r z).carrier
   #0z              = (PolyModRing r z).sum.id
   #1z              = (PolyModRing r z).prod.id
   p +z q           = (PolyModRing r z).sum.op p q
   p *z q           = (PolyModRing r z).prod.op p q
   p -z q           = ring_sub (PolyModRing r z) p q
   negz p           = (PolyModRing r z).sum.inv p
   |/z              = (Invertibles (PolyModRing r z).prod).inv p
   x ##z n          = (PolyModRing r z).sum.exp x n
   x **z n          = (PolyModRing r z).prod.exp x n
   $-z p            = negz p
*)
(* Definitions and Theorems (# are exported):

   Polynomial Modulo Ring:
   poly_remainders_def       |- !r z. poly_remainders r z =
                                {p | poly p /\ if deg z = 0 then p = |0| else deg p < deg z}
   poly_remainders_property  |- !r z p. p IN poly_remainders r z <=>
                                (poly p /\ if deg z = 0 then p = |0| else deg p < deg z)
   poly_mod_ring_def         |- !r z. poly_mod_ring r z =
        <|carrier := poly_remainders r z;
              sum := <|carrier := poly_remainders r z; op := (\x y. (x + y) % z); id := |0||>;
             prod := <|carrier := poly_remainders r z; op := (\x y. (x * y) % z); id := if deg z = 0 then |0| else |1||>
         |>
   poly_mod_ring_property  |- !r z. (!p. p IN Rz <=> poly p /\ if deg z = 0 then p = |0| else deg p < deg z) /\
                                    (!p q. p IN Rz /\ q IN Rz ==> (p +z q = (p + q) % z)) /\
                                    (!p q. p IN Rz /\ q IN Rz ==> (p *z q = (p * q) % z)) /\
                                    ((PolyModRing r z).sum.carrier = Rz) /\
                                    ((PolyModRing r z).prod.carrier = Rz) /\
                                    (#0z = |0|) /\ (#1z = if deg z = 0 then |0| else |1|)
   poly_mod_ring_element   |- !r z p. p IN Rz <=> poly p /\ if deg z = 0 then p = |0| else deg p < deg z
   poly_mod_ring_carriers  |- !r z. ((PolyModRing r z).sum.carrier = Rz) /\ ((PolyModRing r z).prod.carrier = Rz)
   poly_mod_ring_ids       |- !r z. (#0z = |0|) /\ (#1z = if deg z = 0 then |0| else |1|)
   poly_mod_ring_sum_abelian_group   |- !r. Ring r ==> !z. ulead z ==> AbelianGroup (PolyModRing r z).sum
   poly_mod_ring_prod_abelian_monoid |- !r. Ring r ==> !z. ulead z ==> AbelianMonoid (PolyModRing r z).prod
   poly_mod_ring_ring      |- !r. Ring r ==> !z. ulead z ==> Ring (PolyModRing r z)
   poly_mod_ring_add       |- !r p q z. p IN Rz /\ q IN Rz ==> (p +z q = (p + q) % z)
   poly_mod_ring_mult      |- !r p q z. p IN Rz /\ q IN Rz ==> (p *z q = (p * q) % z)
   poly_mod_ring_neg       |- !r. Ring r ==> !z. ulead z ==> !p. p IN Rz ==> ($-z p = -p % z)
   poly_mod_ring_sub       |- !r. Ring r ==> !z. ulead z ==> !p q. p IN Rz /\ q IN Rz ==> (p -z q = (p - q) % z)

   Polynomial Modulo Ring isomorphic to Quotient Ring by Principal Ideal:
   poly_ideal_coset  |- !r. Ring r ==> !z. poly z ==> !x. x IN Rz ==>
         coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier IN
           (PolyRing r / principal_ideal (PolyRing r) z).carrier
   poly_ideal_coset_eq  |- !r. Ring r ==> !z. ulead z ==>
       !p q. poly p /\ poly q ==>
       ((coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier =
         coset (PolyRing r).sum q (principal_ideal (PolyRing r) z).carrier) <=> (p == q) (pm z))
   poly_ideal_cogen_property |- !r. Ring r ==> !z. ulead z ==>
       !p q. poly p /\ poly q ==>
         (q = cogen (PolyRing r).sum (principal_ideal (PolyRing r) z).sum
              (coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier)) ==> (p == q) (pm z)
   poly_mod_sum_group_homo_quotient_ring
                                |- !r. Ring r ==> !z. ulead z ==>
       GroupHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
                 (PolyModRing r z).sum
                 (PolyRing r / principal_ideal (PolyRing r) z).sum
   poly_mod_prod_monoid_homo_quotient_ring
                                |- !r. Ring r ==> !z. ulead z ==>
       MonoidHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
                  (PolyModRing r z).prod
                  (PolyRing r / principal_ideal (PolyRing r) z).prod
   poly_mod_ring_homo_quotient_ring |- !r. Ring r ==> !z. ulead z ==>
       RingHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
                (PolyModRing r z)
                (PolyRing r / principal_ideal (PolyRing r) z)
   poly_mod_ring_iso_quotient_ring  |- !r. Ring r ==> !z. ulead z ==>
       RingIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
               (PolyModRing r z)
               (PolyRing r / principal_ideal (PolyRing r) z)

   Cardinality of Polynomial Modulo Ring:
   poly_mod_ring_carrier_alt |- !r z. Rz = {p | poly p /\ (p = [] \/ deg p < deg z)}
   poly_mod_ring_finite      |- !r z. FiniteRing r ==> FINITE Rz
   poly_mod_ring_card        |- !r z. FiniteRing r ==> (CARD Rz = CARD R ** deg z)

   Polynomial Modulo Theorems:
   poly_mod_prod_nonzero_id         |- !r z. ((PolyModRing r z).prod excluding |0|).id =
                                             if deg z = 0 then |0| else |1|
   poly_mod_ring_prod_finite        |- !r z. FiniteRing r /\ ulead z ==>
                                           FINITE ((PolyModRing r z).prod excluding |0|).carrier
   poly_mod_ring_nonzero_element    |- !r z. Ring r /\ 0 < deg z ==>
                                       !p. p IN ((PolyModRing r z).prod excluding |0|).carrier <=>
                                           poly p /\ p <> |0| /\ deg p < deg z

   Exponentiation in Polynomial Ring:
   poly_mod_exp_alt  |- !r. Ring r ==> !p z. poly p /\ ulead z ==>
                        !n. ((PolyModRing r z).prod excluding |0|).exp p n = p ** n % z
   poly_mod_ring_exp |- !r z. Ring r /\ ulead z ==>
                        !p. p IN Rz ==> !n. p **z n = p ** n % z

   Polynomial Theorems when coefficient is field:
   poly_field_mod_ring_sum_abelian_group
                             |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                    AbelianGroup (PolyModRing r z).sum
   poly_field_mod_ring_prod_abelian_monoid
                             |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                    AbelianMonoid (PolyModRing r z).prod
   poly_field_mod_ring_ring  |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                    Ring (PolyModRing r z)
   poly_field_mod_ring_neg   |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                !p. p IN Rz ==> ($-z p = -p % z)
   poly_field_mod_ring_sub   |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                !p q. p IN Rz /\ q IN Rz ==> (p -z q = (p - q) % z)
   poly_field_ideal_coset    |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
        !x. x IN Rz ==> coset (PolyRing r).sum x
                        (principal_ideal (PolyRing r) z).carrier IN
                            (PolyRing r / principal_ideal (PolyRing r) z).carrier
   poly_field_ideal_coset_eq |- !r. Field r ==> !z. poly z ==>
        !p q. poly p /\ poly q ==>
              ((coset (PolyRing r).sum p
                      (principal_ideal (PolyRing r) z).carrier =
                coset (PolyRing r).sum q
                      (principal_ideal (PolyRing r) z).carrier) <=> (p == q) (pm z))
   poly_field_ideal_cogen_property
                       |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
        !p q. poly p /\ poly q ==>
              (q = cogen (PolyRing r).sum
                     (principal_ideal (PolyRing r) z).sum
                     (coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier)) ==>
              (p == q) (pm z)
   poly_field_mod_sum_group_homo_quotient_ring
                       |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
              GroupHomo (\x. coset (PolyRing r).sum x
                                   (principal_ideal (PolyRing r) z).carrier)
                        (PolyModRing r z).sum
                        (PolyRing r / principal_ideal (PolyRing r) z).sum
   poly_field_mod_prod_monoid_homo_quotient_ring
                       |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
              MonoidHomo (\x. coset (PolyRing r).sum x
                                    (principal_ideal (PolyRing r) z).carrier)
                         (PolyModRing r z).prod
                         (PolyRing r / principal_ideal (PolyRing r) z).prod
   poly_field_mod_ring_homo_quotient_ring
                       |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
              RingHomo (\x. coset (PolyRing r).sum x
                                  (principal_ideal (PolyRing r) z).carrier)
                       (PolyModRing r z)
                       (PolyRing r / principal_ideal (PolyRing r) z)
   poly_field_mod_ring_iso_quotient_ring
                       |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
              RingIso (\x. coset (PolyRing r).sum x
                           (principal_ideal (PolyRing r) z).carrier)
                      (PolyModRing r z)
                      (PolyRing r / principal_ideal (PolyRing r) z)
   poly_field_mod_exp_alt    |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                !n. ((PolyModRing r z).prod excluding |0|).exp p n = p ** n % z
   poly_field_mod_ring_exp   |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                !p. p IN Rz ==> !n. p **z n = p ** n % z

*)
(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Ring                                                    *)
(* ------------------------------------------------------------------------- *)

(* Define the set of polynomial remainders modulo z *)
val poly_remainders_def = Define`
    poly_remainders (r:'a  ring) (z:'a poly) =
       {p | poly p /\ (if deg z = 0 then p = |0| else deg p < deg z) }
`;

(* Theorem: properties of poly_remainders r z *)
(* Proof: by poly_remainders_def. *)
val poly_remainders_property = store_thm(
  "poly_remainders_property",
  ``!r:'a ring z:'a poly p. p IN poly_remainders r z <=>
      (poly p /\ (if deg z = 0 then p = |0| else deg p < deg z))``,
  rw[poly_remainders_def]);

(* Modulo Ring by division of a polynomial *)
val poly_mod_ring_def = Define`
  poly_mod_ring (r:'a ring) (z:'a poly) =
    <| carrier := poly_remainders r z;
           sum := <| carrier := poly_remainders r z;
                          op := (\(x:'a poly) (y:'a poly). (x + y) % z);
                          id := |0| |>;
          prod := <| carrier := poly_remainders r z;
                          op := (\(x:'a poly) (y:'a poly). (x * y) % z);
                          id := if deg z = 0 then |0| else |1| |>
     |>
`;
(* Note: need to use (r:'a ring) due to x % y = poly_mod r x y *)
(* Note: when deg z = 0, poly_remainders r z = {|0|}, so prod.id = |0| to be an element. *)

(* overload on R[x]/z *)
val _ = overload_on ("PolyModRing", ``\r z. poly_mod_ring r z``);

(* Overloads for elements of (PolyModRing r z) *)
val _ = overload_on("Rz", ``(PolyModRing r z).carrier``);
(* val _ = overload_on("R+z", ``ring_nonzero (PolyModRing r z)``); *)
val _ = overload_on("#0z", ``(PolyModRing r z).sum.id``);
val _ = overload_on("#1z", ``(PolyModRing r z).prod.id``);
val _ = overload_on("+z", ``(PolyModRing r z).sum.op``);
val _ = overload_on("*z", ``(PolyModRing r z).prod.op``);
val _ = overload_on("-z", ``ring_sub (PolyModRing r z)``);
val _ = overload_on("negz", ``(PolyModRing r z).sum.inv``); (* unary negation *)
val _ = overload_on("|/z", ``(Invertibles (PolyModRing r z).prod).inv``);
val _ = overload_on("##z", ``(PolyModRing r z).sum.exp``);
val _ = overload_on("**z", ``(PolyModRing r z).prod.exp``);

(* make infix operators *)
val _ = set_fixity "+z" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity "-z" (Infixl 500); (* same as - in arithmeticScript.sml *)
val _ = set_fixity "*z" (Infixl 600); (* same as * in arithmeticScript.sml *)
val _ = set_fixity "**z" (Infixr 700); (* same as EXP in arithmeticScript.sml, infix right *)
(* 900 for numeric_negate *)
(* make unary symbolic *)
val _ = overload_on("-z", ``negz``); (* becomes $-z *)

(* Theorem: properties of PolyModRing r z *)
(* Proof: by poly_mod_ring_def, poly_remainders_def. *)
val poly_mod_ring_property = store_thm(
  "poly_mod_ring_property",
  ``!(r:'a ring) (z:'a poly).
     (!p. p IN Rz <=> poly p /\ if deg z = 0 then p = |0| else deg p < deg z) /\
     (!p q. p IN Rz /\ q IN Rz ==> (p +z q = (p + q) % z)) /\
     (!p q. p IN Rz /\ q IN Rz ==> (p *z q = (p * q) % z)) /\
     ((PolyModRing r z).sum.carrier = Rz) /\
     ((PolyModRing r z).prod.carrier = Rz) /\
     (#0z = |0|) /\ (#1z = if deg z = 0 then |0| else |1|)``,
  rw[poly_mod_ring_def, poly_remainders_def]);

(* Theorem: p IN Rz <=> poly p /\ if deg z = 0 then p = |0| else deg p < deg z *)
(* Proof: by poly_mod_ring_property. *)
val poly_mod_ring_element = store_thm(
  "poly_mod_ring_element",
  ``!(r:'a ring) (z:'a poly). !p. p IN Rz <=>
        poly p /\ if deg z = 0 then p = |0| else deg p < deg z``,
  rw[poly_mod_ring_property]);

(* Theorem: ((PolyModRing r z).sum.carrier = Rz) /\ ((PolyModRing r z).prod.carrier = Rz) *)
(* Proof: by poly_mod_ring_property. *)
val poly_mod_ring_carriers = store_thm(
  "poly_mod_ring_carriers",
  ``!(r:'a ring) (z:'a poly). ((PolyModRing r z).sum.carrier = Rz) /\
                             ((PolyModRing r z).prod.carrier = Rz)``,
  rw[poly_mod_ring_property]);

(* Theorem: (#0z = |0|) /\ (#1z = if deg z = 0 then |0| else |1|) *)
(* Proof: by poly_mod_ring_property. *)
val poly_mod_ring_ids = store_thm(
  "poly_mod_ring_ids",
  ``!(r:'a ring) (z:'a poly). (#0z = |0|) /\ (#1z = if deg z = 0 then |0| else |1|)``,
  rw[poly_mod_ring_property]);

(* Theorem: p IN Rz /\ q IN Rz ==> (p +z q = (p + q) % z) *)
(* Proof: by poly_mod_ring_property *)
val poly_mod_ring_add = store_thm(
  "poly_mod_ring_add",
  ``!r:'a ring. !p q z. p IN Rz /\ q IN Rz ==> (p +z q = (p + q) % z)``,
  rw[poly_mod_ring_property]);

(* Theorem: p IN Rz /\ q IN Rz ==> (p *z q = (p * q) % z) *)
(* Proof: by poly_mod_ring_property *)
val poly_mod_ring_mult = store_thm(
  "poly_mod_ring_mult",
  ``!r:'a ring. !p q z. p IN Rz /\ q IN Rz ==> (p *z q = (p * q) % z)``,
  rw[poly_mod_ring_property]);

(* Theorem: Ring r ==> !z. ulead z ==> AbelianGroup (PolyModRing r z).sum *)
(* Proof:
   If deg z = 0,
   poly_remainders r z = {|0|}             by poly_remainders_def
   By group definition, this is to show:
   (1) poly (( |0| + |0|) % z), true       by poly_mod_zero
   (2) ( |0| + |0|) % z = |0|, true        by poly_mod_zero
   (3) (( |0| + |0|) % z + |0|) % z = ( |0| + ( |0| + |0|) % z) % z
                               true        by poly_mod_zero
   (4) poly |0|, true                      by poly_zero_poly
   (5) ( |0| + |0|) % z = |0|, true        by poly_mod_zero

   Otherwise 0 < deg z.
   poly_remainders r z = {p | poly p /\ deg p < deg z}   by poly_remainders_def
   By group definition, this is to show:
   (1) poly ((x + y) % z), true         by poly_add_poly, poly_mod_poly
   (2) deg ((x + y) % z) < deg z, true  by poly_division, 0 < deg z
   (3) ((x + y) % z + z') % z = (x + (y + z') % z) % z, true by poly_mod_add_assoc
   (4) poly |0|, true              by poly_zero_poly
   (5) deg |0| < deg z, true       by poly_deg_zero
   (6) (|0| + x) % z = x, true     by poly_add_lzero, poly_mod_less
   (7) poly x /\ deg x < deg z ==> ?y. (poly y /\ deg y < deg z) /\ ((y + x) % z = |0|)
       Take y = (-x) % z, then
         (y + x) % z
       = ((-x) % z + x) % z
       = ((-x) % z + x % z ) % z   by poly_mod_add
       = (- (x % z) + x % z) % z   by poly_mod_neg
       = |0| % z                   by poly_add_lneg
       = |0|                       by poly_zero_mod
   (8) (x + y) % z = (y + x) % z, true by poly_add_comm
*)
val poly_mod_ring_sum_abelian_group = store_thm(
  "poly_mod_ring_sum_abelian_group",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> AbelianGroup (PolyModRing r z).sum``,
  rpt strip_tac >>
  Cases_on `deg z = 0` >-
  (rw_tac std_ss[AbelianGroup_def, group_def_alt, poly_mod_ring_def, poly_remainders_def, GSPECIFICATION] >> rw[poly_mod_of_zero]) >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, poly_mod_ring_def, poly_remainders_def, GSPECIFICATION] >-
  rw[] >-
  rw[poly_division] >-
  rw[poly_mod_add_assoc] >-
  rw[] >-
  rw[] >-
  rw[poly_mod_less] >-
 (qexists_tac `(-x) % z` >>
  `poly (x % z) /\ poly (-x % z)` by rw[] >>
  `(-x) % z = - (x % z)` by rw[poly_mod_neg] >>
  `(-x % z + x) % z = ((-x % z) % z + x % z) % z` by rw_tac std_ss[poly_mod_add] >>
  `_ = (- (x % z) + x % z) % z` by rw_tac std_ss[poly_mod_neg, poly_mod_mod] >>
  `_ = |0| % z` by rw_tac std_ss[poly_add_lneg] >>
  rw[poly_deg_neg, poly_division]) >>
  rw[poly_add_comm]);

(* Theorem: Ring r ==> !z. ulead z ==> AbelianMonoid (PolyModRing r z).prod *)
(* Proof:
   If deg z = 0,
   poly_remainders r z = {|0|}             by poly_remainders_def
   By monoid definition, this is to show:
   (1) poly (( |0| * |0|) % z), true       by poly_mod_zero
   (2) ( |0| * |0|) % z = |0|, true        by poly_mod_zero
   (3) (( |0| * |0|) % z * |0|) % z = ( |0| * ( |0| * |0|) % z) % z
                               true        by poly_mod_zero
   (4) poly |0|, true                      by poly_zero_poly
   (5) ( |0| * |0|) % z = |0|, true        by poly_mod_zero

   Otherwise 0 < deg z.
   poly_remainders r z = {p | poly p /\ deg p < deg z}   by poly_remainders_def

   By monoid definition, this is to show:
   (1) poly ((x * y) % z), true        by poly_mod_poly
   (2) deg ((x * y) % z) < deg z, true by poly_division, 0 < deg z
   (3) ((x * y) % z * z') % z = (x * (y * z') % z) % z, true by poly_mod_mult_assoc
   (4) poly |1|, true                  by poly_one_poly
   (5) deg |1| < deg z, true           by poly_deg_one
   (6) (|1| * x) % z = x, true by      poly_mult_lone
   (7) (x * |1|) % z = x, true         by poly_mult_rone
   (8) (x * y) % z = (y * x) % z, true by poly_mult_comm
*)
val poly_mod_ring_prod_abelian_monoid = store_thm(
  "poly_mod_ring_prod_abelian_monoid",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> AbelianMonoid (PolyModRing r z).prod``,
  rpt strip_tac >>
  Cases_on `deg z = 0` >-
  (rw_tac std_ss[AbelianMonoid_def, Monoid_def, poly_mod_ring_def, poly_remainders_def, GSPECIFICATION] >> rw[poly_mod_of_zero]) >>
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, poly_mod_ring_def, poly_remainders_def, GSPECIFICATION] >-
  rw[] >-
  rw[poly_division] >-
  rw[poly_mod_mult_assoc] >-
  rw[] >-
  rw[] >-
  rw[poly_mod_less] >-
  rw[poly_mod_less] >>
  rw[poly_mult_comm]);

(* Theorem: Ring r ==> !z. ulead z ==> Ring (PolyModRing r z) *)
(* Proof:
   By Ring_def, this is to show:
   (1) AbelianGroup (PolyModRing r z).sum, true   by poly_mod_ring_sum_abelian_group
   (2) AbelianMonoid (PolyModRing r z).prod, true by poly_mod_ring_prod_abelian_monoid
   (3) (PolyModRing r z).sum.carrier = Rz, true   by poly_mod_ring_def
   (4) (PolyModRing r z).prod.carrier = Rz, true  by poly_mod_ring_def
   (5) x IN Rz /\ y IN Rz /\ z' IN Rz ==>
       (x * (y + z') % z) % z = ((x * y) % z + (x * z') % z) % z
       If deg z = 0,
          ( |0| * ( |0| + |0|) % z) % z = (( |0| * |0|) % z + ( |0| * |0|) % z) % z
                                            by poly_mod_by_const
       If deg z <> 0,
         (x * (y + z') % z) % z
       = (x % z * (y + z') % z) % z         by poly_mod_mult, poly_mod_mod
       = (x * (y + z')) % z                 by poly_mod_mult
       = (x * y + x * z') % z               by poly_mult_radd
       = ((x * y) % z + (x * z') % z) % z   by poly_mod_add
*)
val poly_mod_ring_ring = store_thm(
  "poly_mod_ring_ring",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> Ring (PolyModRing r z)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def] >-
  rw[poly_mod_ring_sum_abelian_group] >-
  rw[poly_mod_ring_prod_abelian_monoid] >-
  rw[poly_mod_ring_def] >-
  rw[poly_mod_ring_def] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[poly_mod_ring_def, poly_remainders_def, GSPECIFICATION] >-
  simp[poly_mod_by_const] >>
  `poly (y + z') /\ poly ((y + z') % z) /\ poly (x * y) /\ poly (x * z')` by rw[] >>
  `(x * (y + z') % z) % z = ((x % z) * (y + z') % z) % z` by rw_tac std_ss[poly_mod_mult, poly_mod_mod] >>
  `_ = (x * (y + z')) % z` by rw_tac std_ss[poly_mod_mult] >>
  rw_tac std_ss[poly_mult_radd, poly_mod_add]);

(* This is a milestone theorem. *)

(* Theorem: Ring r ==> !z. ulead z ==> !p. p IN Rz ==> ($-z p = (-p) % z) *)
(* Proof:
   Note Ring (PolyModRing r z)      by poly_mod_ring_ring
    Let q = $-z p
   Then q IN Rz                     by ring_neg_element
    and q +z p = #0z                by ring_add_lneg
               = |0|                by poly_mod_ring_ids

   If deg z = 0,
      Then q = |0|                  by poly_mod_ring_element
       and -p % z = |0|             by poly_mod_by_const
      Hence true.
   Otherwise 0 < deg z.
    Now poly p /\ deg p < deg z     by poly_mod_ring_element
    and poly q /\ deg q < deg z     by poly_mod_ring_element
   Also deg (q + p) <= MAX (deg q) (deg p)   by poly_deg_add
    and MAX (deg q) (deg p) < deg z          by MAX_LESS
   thus deg (q + p) < deg z

   Hence (q + p) % z = q + p        by poly_mod_less
     and p % z = p                  by poly_mod_less
   Since |0| = q +z p
             = (q + p) % z          by poly_mod_ring_add
             = q + p                by poly_mod_less
    Thus   q = - p                  by poly_add_eq_zero
             = - (p % z)            by above, poly_mod_less
             = (-p) % z             by poly_mod_neg
*)
val poly_mod_ring_neg = store_thm(
  "poly_mod_ring_neg",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> !p. p IN Rz ==> ($-z p = (-p) % z)``,
  rpt strip_tac >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `($-z p) +z p = |0|` by rw[ring_add_lneg, poly_mod_ring_ids] >>
  qabbrev_tac `q = $-z p` >>
  `q IN Rz` by rw[Abbr`q`] >>
  Cases_on `deg z = 0` >-
  metis_tac[poly_mod_ring_element, poly_mod_by_const, poly_neg_poly] >>
  `poly p /\ deg p < deg z` by metis_tac[poly_mod_ring_element] >>
  `poly q /\ deg q < deg z` by metis_tac[poly_mod_ring_element] >>
  `deg (q + p) <= MAX (deg q) (deg p)` by rw[poly_deg_add] >>
  `MAX (deg q) (deg p) < deg z` by rw[MAX_LESS] >>
  `deg (q + p) < deg z` by decide_tac >>
  `(q + p) % z = q + p` by rw[poly_mod_less] >>
  `p % z = p` by rw[poly_mod_less] >>
  `q + p = |0|` by metis_tac[poly_mod_ring_add] >>
  `- (p % z) = (-p) % z` by rw[poly_mod_neg] >>
  metis_tac[poly_add_eq_zero]);

(* Theorem: Ring r ==> !z. ulead z ==> !p q. p IN Rz /\ q IN Rz ==> (p -z q = (p - q) % z) *)
(* Proof:
   Note Ring (PolyModRing r z)      by poly_mod_ring_ring
   Then $-z q IN Rz                 by ring_neg_element
   If deg z = 0,
      Then p -z q = |0|             by poly_mod_ring_element, ring_sub_element
       and (p - q) % z = |0|        by poly_mod_by_const, poly_mod_ring_element
      Hence true.
   Otherwise 0 < deg z.
   Note poly p /\ deg p < deg z     by poly_mod_ring_element
    and poly q /\ deg q < deg z     by poly_mod_ring_element
     so poly -q                     by poly_neg_poly

     p -z q
   = p +z ($-z q)                   by ring_sub_def
   = (p + ($-z q)) % z              by poly_mod_ring_add
   = (p + (-q) % z) % z             by poly_mod_ring_neg
   = (p % z + (-q) % z) % z         by poly_mod_less
   = (p + -q) % z                   by poly_mod_add
   = (p - q) % z                    by poly_sub_def
*)
val poly_mod_ring_sub = store_thm(
  "poly_mod_ring_sub",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> !p q. p IN Rz /\ q IN Rz ==> (p -z q = (p - q) % z)``,
  rpt strip_tac >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `$-z q IN Rz` by rw[] >>
  Cases_on `deg z = 0` >| [
    `p -z q = |0|` by metis_tac[poly_mod_ring_element, ring_sub_element] >>
    metis_tac[poly_mod_by_const, poly_sub_poly, poly_mod_ring_element],
    `poly p /\ deg p < deg z` by metis_tac[poly_mod_ring_element] >>
    `poly (-q)` by metis_tac[poly_mod_ring_element, poly_neg_poly] >>
    rw_tac std_ss[ring_sub_def, poly_mod_ring_add, poly_mod_ring_neg, poly_mod_less, poly_mod_add, poly_sub_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Ring isomorphic to Quotient Ring by Principal Ideal     *)
(* ------------------------------------------------------------------------- *)

(* Idea (some abuse in notation):
   Given Ring r and poly z IN R[X], let I = principal_ideal R[X] z.
   Then !x. x IN R[X] ==> x o I IN (R[X] / I).
*)
(* Theorem: x IN Rz ==> coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier IN
                        (PolyRing r / principal_ideal (PolyRing r) z).carrier *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z.
   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal
   Let x o I = coset RX.sum x I.carrier.
    ==> x o I IN CosetPartition RX.sum I.sum   by ideal_coset_property
    ==> x o I IN (RX / I).carrier              by quotient_ring_def
*)
val poly_ideal_coset = store_thm(
  "poly_ideal_coset",
  ``!r:'a ring. Ring r ==> !z. poly z ==> !x. x IN Rz ==>
   coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier IN
   (PolyRing r / principal_ideal (PolyRing r) z).carrier``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw[poly_add_mult_ring] >>
  `z IN (PolyRing r).carrier` by metis_tac[poly_ring_property] >>
  `(principal_ideal (PolyRing r) z) << (PolyRing r)` by rw[principal_ideal_ideal] >>
  `!x. x IN Rz ==> poly x` by rw[poly_mod_ring_element] >>
  `x IN (PolyRing r).carrier` by rw[GSYM poly_ring_property] >>
  rw[ideal_coset_property, quotient_ring_def]);

(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z.
   Then !p q. poly p /\ poly q ==> (p o I = q o I) <=> (p == q) (pm z).
*)
(* Theorem: coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier =
            coset (PolyRing r).sum q (principal_ideal (PolyRing r) z).carrier <=> p == q (pm z) *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z.
   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal
   Let p o I = coset RX.sum p I.carrier,
   and q o I = coset RX.sum q I.carrier.
       p o I = q o I
   <=> p - q IN I.carrier             by ideal_coset_eq, poly_ring_def
   <=> ?t. poly t /\ (p - q = z * t)  by principal_ideal_element, poly_ring_property
   <=> (p - q) % z = |0|              by poly_mod_eq_zero, poly_mult_comm
   <=> (p == q) (pm z)                by poly_mod_eq_alt
*)
val poly_ideal_coset_eq = store_thm(
  "poly_ideal_coset_eq",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> !p q. poly p /\ poly q ==>
     ((coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier =
       coset (PolyRing r).sum q (principal_ideal (PolyRing r) z).carrier) <=> (p == q) (pm z))``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `z IN rx.carrier` by metis_tac[poly_ring_property] >>
  `zz << rx` by rw[principal_ideal_ideal, Abbr`zz`] >>
  `poly (p - q)` by rw[] >>
  `!x. poly x <=> x IN rx.carrier` by rw[GSYM poly_ring_property, Abbr`rx`] >>
  `!x y:'a poly. rx.sum.op x y = x + y` by rw[poly_ring_def] >>
  `!x:'a poly. rx.sum.inv x = -x` by rw[poly_ring_def] >>
  `(coset rx.sum p Z = coset rx.sum q Z) <=> ring_sub rx p q IN Z` by metis_tac[ideal_coset_eq] >>
  `_ = (p - q IN Z)` by metis_tac[ring_sub_def, poly_sub_def] >>
  `_ = ?t. poly t /\ (p - q = z * t)` by metis_tac[principal_ideal_element] >>
  `_ = ((p - q) % z = |0|)` by metis_tac[poly_mod_eq_zero, poly_mult_comm] >>
  `_ = (p == q) (pm z)` by metis_tac[poly_mod_eq_alt] >>
  simp[]);

(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z.
   Then !p q. poly p /\ poly q ==>
              (q = cogen R[X] I (p o I)) ==> (p == q) (pm z).
*)
(* Theorem: q = cogen (PolyRing r).sum
               (principal_ideal (PolyRing r) z).sum
               (coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier  ==> (p == q) (pm z) *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z.
   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal
   Let p o I = coset RX.sum p I.carrier,
   and q o I = coset RX.sum q I.carrier,
   where q = cogen RX.sum I.sum (p o I)     by given
   Note zz.sum <= rx.sum    by ideal_has_subgroup
    and p IN rx.sum.carrier by poly_ring_property
    ==> p o I IN CosetPartition RX.sum I.sum
                            by coset_partition_element, ideal_carriers
   Then p o I = q o I       by ideal_cogen_property
   Thus (p == q) (pm z)     by poly_ideal_coset_eq
*)
val poly_ideal_cogen_property = store_thm(
  "poly_ideal_cogen_property",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> !p q. poly p /\ poly q ==>
   ((q = cogen (PolyRing r).sum
               (principal_ideal (PolyRing r) z).sum
               (coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier)) ==> (p == q) (pm z))``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `z IN rx.carrier` by metis_tac[poly_ring_property] >>
  `zz << rx` by rw[principal_ideal_ideal, Abbr`zz`] >>
  `coset rx.sum p Z IN CosetPartition rx.sum zz.sum` by
  (`zz.sum <= rx.sum` by rw[ideal_has_subgroup] >>
  `p IN rx.sum.carrier` by fs[poly_ring_property, Abbr`rx`] >>
  metis_tac[coset_partition_element, ideal_carriers]) >>
  `coset rx.sum q Z = coset rx.sum p Z` by metis_tac[ideal_cogen_property] >>
  metis_tac[poly_ideal_coset_eq]);

(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z = <z>.
   Then GroupHomo (\x. x o I) (PolyModRing r z).sum (R[X] / I).sum
*)
(* Theorem: (PolyModRing r z).sum has a homomorphism to (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)).sum *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z,
       RM = PolyModRing r z.
       and for any p, p o I = coset RX.sum p I.carrier.
   The goal is: GroupHomo (\x. x o I) RM.sum (RX / I).sum

   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal

   By GroupHomo_def, this is to show:
   (1) x IN RM.sum.carrier ==> x o I IN (RX / I).sum.carrier
           x IN RM.sum.carrier
       ==> poly x                                   by poly_mod_ring_property
       ==> x IN RX.carrier                          by poly_ring_property
       ==> x o I IN (CosetPartition rx.sum zz.sum)  by ideal_coset_property
       ==> x o I IN (RX / I).sum.carrier            by quotient_ring_def, quotient_ring_add_def
   (2) x IN RM.sum.carrier /\ x' IN RM.sum.carrier ==>
      (x +z x') o I = (RX / I).sum.op (x o I) (x' o I)
      Expand by quotient_ring_def, quotient_ring_add_def, poly_ring_def,
      Let y = (cogen RX.sum I.sum (x o I)),
          y' = (cogen RX.sum I.sum (x o I)),
      this is to show: (x +z x') o I = (RX.sum.op y y') o I
      Note I.sum <= RX.sum              by ideal_has_subgroup
       and RX.sum.carrier = RX.carrier  by ring_carriers
       and I.sum.carrier = I.carrier    by ideal_carriers
       Now poly x /\ poly x'            by poly_mod_ring_property
       and poly y /\ poly y'            by cogen_coset_element, poly_ring_property, poly_mod_ring_property
      Note x +z x' = (x + x') % z       by poly_mod_ring_property, poly_ring_def
       and poly (RX.sum.op y y')        by poly_add_poly
      The goal becomes:
          ((x + x') % z == (y + y')) (pm z)
                                        by poly_ideal_coset_eq, poly_add_poly, poly_mod_poly
      Note (x == y) (pm z)                     by poly_ideal_cogen_property
       and (x' == y') (pm z)                   by poly_ideal_cogen_property
      Thus (x + x' == y + y') (pm z)           by pmod_add
       and (x + x' == (x + x') % z) (pm z)     by pmod_mod
       ==> ((x + x') % z == y + y') (pm z)     by poly_mod_transitive
*)
val poly_mod_sum_group_homo_quotient_ring = store_thm(
  "poly_mod_sum_group_homo_quotient_ring",
  ``!r:'a ring. Ring r ==> !z. ulead z ==>
       GroupHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
               (PolyModRing r z).sum
               (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)).sum``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `zz << rx` by metis_tac[principal_ideal_ideal, poly_ring_property] >>
  rw_tac std_ss[GroupHomo_def] >| [
    `x IN rx.carrier` by fs[GSYM poly_ring_property, poly_mod_ring_property, Abbr`rx`] >>
    `(coset rx.sum x Z) IN (CosetPartition rx.sum zz.sum)` by metis_tac[ideal_coset_property] >>
    rw[quotient_ring_def, quotient_ring_add_def],
    rw[quotient_ring_def, quotient_ring_add_def, poly_ring_def] >>
    qabbrev_tac `y = (cogen rx.sum zz.sum (coset rx.sum x Z))` >>
    qabbrev_tac `y' = (cogen rx.sum zz.sum (coset rx.sum x' Z))` >>
    `zz.sum <= rx.sum` by rw[ideal_has_subgroup] >>
    `rx.sum.carrier = rx.carrier` by rw[ring_carriers] >>
    `zz.sum.carrier = Z` by metis_tac[ideal_carriers] >>
    `poly x /\ poly x'` by fs[poly_mod_ring_property] >>
    `poly y /\ poly y'` by metis_tac[cogen_coset_element, poly_ring_property, poly_mod_ring_property] >>
    `x +z x' = (x + x') % z` by rw[GSYM poly_mod_ring_property, poly_ring_def] >>
    `poly (rx.sum.op y y')` by metis_tac[poly_add_poly] >>
    `((x + x') % z == (y + y')) (pm z)` suffices_by metis_tac[poly_ideal_coset_eq, poly_add_poly, poly_mod_poly] >>
    `(x == y) (pm z)` by rw[poly_ideal_cogen_property] >>
    `(x' == y') (pm z)` by rw[poly_ideal_cogen_property] >>
    `(x + x' == y + y') (pm z)` by rw[pmod_add] >>
    `((x + x') % z == x + x') (pm z)` by rw[pmod_mod] >>
    metis_tac[poly_mod_transitive]
  ]);


(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z = <z>.
   Then MonoidHomo (\x. x o I) (PolyModRing r z).prod (R[X] / I).prod
*)
(* Theorem: (PolyModRing r z).prod has a homomorphism to (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)).prod *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z,
       RM = PolyModRing r z.
       and for any p, p o I = coset RX.sum p I.carrier.
   The goal is: MonoidHomo (\x. x o I) RM.prod (RX / I).prod

   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal

   By MonoidHomo_def, this is to show:
   (1) x IN RM.prod.carrier ==> x o I IN (RX / I).prod.carrier
           x IN RM.sum.carrier
       ==> poly x                                   by poly_mod_ring_property
       ==> x IN RX.carrier                          by poly_ring_property
       ==> x o I IN (CosetPartition rx.sum zz.sum)  by ideal_coset_property
       ==> x o I IN (RX / I).prod.carrier           by quotient_ring_def, quotient_ring_mult_def
   (2) x IN RM.prod.carrier /\ x' IN RM.prod.carrier ==>
      (x *z x') o I = (RX / I).prod.op (x o I) (x' o I)
      Expand by quotient_ring_def, quotient_ring_mult_def, poly_ring_def,
      Let y = (cogen rx.sum zz.sum (x o I)),
          y' = (cogen rx.sum zz.sum (x o I)),
      this is to show: (x *z x') o I = (rx.prod.op y y') o I

      Note I.sum <= RX.sum              by ideal_has_subgroup
       and RX.sum.carrier = RX.carrier  by ring_carriers
       and I.sum.carrier = I.carrier    by ideal_carriers
       Now poly x /\ poly x'            by poly_mod_ring_property
       and poly y /\ poly y'            by cogen_coset_element, poly_ring_property, poly_mod_ring_property
      Note x *z x' = (x * x') % z       by poly_mod_ring_property, poly_ring_property
       and poly (RX.prod.op y y')       by poly_mult_poly
      The goal becomes:
          ((x * x') % z == (y * y')) (pm z)
                                        by poly_ideal_coset_eq, poly_mult_poly, poly_mod_poly
      Note (x == y) (pm z)                     by poly_ideal_cogen_property
       and (x' == y') (pm z)                   by poly_ideal_cogen_property
      Thus (x * x' == y * y') (pm z)           by pmod_mult
       and (x * x' == (x * x') % z) (pm z)     by pmod_mod
       ==> ((x * x') % z == y * y') (pm z)     by poly_mod_transitive

   (3) |1| o I = (RX / I).prod.id
      Expand by quotient_ring_def, quotient_ring_mult_def, poly_ring_def,
      this is to show: #1z o I = RX.prod.id o I

      Note RX.prod.id = |1|      by poly_ring_property
      If deg z = 0,
         Then #1z = |0|                 by poly_mod_ring_ids, deg z = 0
         goal is: ( |0| == |1|) (pm z)  by poly_ideal_coset_eq
         that is: (|0| - |1|) % z = |0| by poly_mod_eq_alt
         This is true                   by poly_mod_by_const
      If deg z <> 0,
         Then #1z = |1|                 by poly_mod_ring_ids, deg z <> 0
         goal is: ( |1| == |1|) (pm z)  by poly_ideal_coset_eq
         This is true trivially.
*)
val poly_mod_prod_monoid_homo_quotient_ring = store_thm(
  "poly_mod_prod_monoid_homo_quotient_ring",
  ``!r:'a ring. Ring r ==> !z. ulead z ==>
       MonoidHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
               (PolyModRing r z).prod
               (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)).prod``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `zz << rx` by metis_tac[principal_ideal_ideal, poly_ring_property] >>
  rw_tac std_ss[MonoidHomo_def] >| [
    `x IN rx.carrier` by fs[GSYM poly_ring_property, poly_mod_ring_property, Abbr`rx`] >>
    `(coset rx.sum x Z) IN (CosetPartition rx.sum zz.sum)` by metis_tac[ideal_coset_property] >>
    rw[quotient_ring_def, quotient_ring_mult_def],
    rw[quotient_ring_def, quotient_ring_mult_def, poly_ring_def] >>
    qabbrev_tac `y = (cogen rx.sum zz.sum (coset rx.sum x Z))` >>
    qabbrev_tac `y' = (cogen rx.sum zz.sum (coset rx.sum x' Z))` >>
    `zz.sum <= rx.sum` by rw[ideal_has_subgroup] >>
    `rx.sum.carrier = rx.carrier` by rw[ring_carriers] >>
    `zz.sum.carrier = Z` by metis_tac[ideal_carriers] >>
    `poly x /\ poly x'` by fs[poly_mod_ring_property] >>
    `poly y /\ poly y'` by metis_tac[cogen_coset_element, poly_ring_property, poly_mod_ring_property] >>
    `x *z x' = (x * x') % z` by metis_tac[poly_mod_ring_property, poly_ring_property] >>
    `poly (rx.prod.op y y')` by metis_tac[poly_mult_poly] >>
    `((x * x') % z == (y * y')) (pm z)` suffices_by metis_tac[poly_ideal_coset_eq, poly_mult_poly, poly_mod_poly] >>
    `(x == y) (pm z)` by rw[poly_ideal_cogen_property] >>
    `(x' == y') (pm z)` by rw[poly_ideal_cogen_property] >>
    `(x * x' == y * y') (pm z)` by rw[pmod_mult] >>
    `((x * x') % z == x * x') (pm z)` by rw[pmod_mod] >>
    metis_tac[poly_mod_transitive],
    rw[quotient_ring_def, quotient_ring_mult_def, poly_ring_def] >>
    `rx.prod.id = |1|` by rw[poly_ring_property, Abbr`rx`] >>
    `poly |0| /\ poly |1|` by rw[] >>
    Cases_on `deg z = 0` >| [
      `#1z = |0|` by metis_tac[poly_mod_ring_ids] >>
      `( |0| == |1|) (pm z)` suffices_by metis_tac[poly_ideal_coset_eq] >>
      rw[poly_mod_eq_alt, poly_mod_by_const],
      `#1z = |1|` by metis_tac[poly_mod_ring_ids] >>
      metis_tac[poly_ideal_coset_eq, poly_one_poly]
    ]
  ]);

(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z = <z>.
   Then RingHomo (\x. x + I) (PolyModRing r z) (R[X] / I).
*)
(* Theorem: (PolyModRing r z) has a homomorphism to (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)) *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z,
       RM = PolyModRing r z.
       and for any p, p o I = coset RX.sum p I.carrier.
   The goal is: RingHomo (\x. x o I) RM (RX / I)

   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal

   By RingHomo_def, this is to show:
   (1) x IN RM.carrier ==> x o I IN (RX / I).carrier
           x IN RM.carrier
       ==> poly x                                   by poly_mod_ring_property
       ==> x IN RX.carrier                          by poly_ring_property
       ==> x o I IN (CosetPartition rx.sum zz.sum)  by ideal_coset_property
       ==> x o I IN (RX / I).carrier                by quotient_ring_def
   (2) GroupHomo (\x. x o I) RM.sum (RX / I).sum
       This is true                  by poly_mod_sum_group_homo_quotient_ring
   (3) MonoidHomo (\x. coset rx.sum x Z) (PolyModRing r z).prod (rx / zz).prod
       This is true                  by poly_mod_prod_monoid_homo_quotient_ring
*)
val poly_mod_ring_homo_quotient_ring = store_thm(
  "poly_mod_ring_homo_quotient_ring",
  ``!r:'a ring. Ring r ==> !z. ulead z ==>
       RingHomo (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
               (PolyModRing r z)
               (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z))``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `zz << rx` by metis_tac[principal_ideal_ideal, poly_ring_property] >>
  rw_tac std_ss[RingHomo_def] >| [
    `x IN rx.carrier` by fs[GSYM poly_ring_property, poly_mod_ring_property, Abbr`rx`] >>
    `(coset rx.sum x Z) IN (CosetPartition rx.sum zz.sum)` by metis_tac[ideal_coset_property] >>
    rw[quotient_ring_def],
    metis_tac[poly_mod_sum_group_homo_quotient_ring],
    metis_tac[poly_mod_prod_monoid_homo_quotient_ring]
  ]);


(* Idea (some abuse in notation):
   Given Ring r and ulead z IN R[X], let I = principal_ideal R[X] z = <z>.
   Then RingIso (\x. x + I) (PolyModRing r z) (R[X] / I).
*)
(* Theorem: (PolyModRing r z) is isomorphic to (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z)) *)
(* Proof:
   Let RX = PolyRing r,
        I = principal_ideal RX z,
       RM = PolyModRing r z.
       and for any p, p o I = coset RX.sum p I.carrier.
   The goal is: RingIso (\x. x o I) RM (RX / I)

   Note Ring RX             by poly_add_mult_ring
    and z IN RX.carrier     by poly_ring_property
    ==> I << RX             by principal_ideal_ideal

   By RingIso_def, this is to show:
   (1) RingHomo (\x. x o I) RM (RX / I)
       True by  poly_mod_ring_homo_quotient_ring.
   (2) BIJ (\x. x o I) RM.carrier (RX / I).carrier
       Expand by BIJ_DEF, SURJ_DEF and INJ_DEF,
       this is to show:
       (1) x IN RM.carrier ==> x o I IN (RX / I).carrier
           This is true                  by poly_ideal_coset
       (2) x IN RM.carrier /\ x' IN RM.case /\ x o I = x' o I ==> x = x'
           If deg z = 0
              Then x = |0| and x' = |0|  by poly_mod_ring_property
              so x = x'
           Otherwise 0 < deg z,
              Then poly x /\ deg x < deg z     by poly_mod_ring_property
               and poly x' /\ deg x' < deg z   by poly_mod_ring_property
               ==> (x == x') (pm z)            by poly_ideal_coset_eq
               ==> x % z = x' % z              by pmod_def_alt
               ==>     x = x'                  by poly_mod_less
       (3) x IN RM.carrier ==> x o I IN (RX / I).carrier, same as (1)
       (4) x IN (RX / I).carrier ==> ?y. y IN RM.carrier /\ y o I = x
           Let p = gen x, put y = p % z.
               x IN (RX / I).carrier
           ==> x IN IN CosetPartition RX.sum I.sum   by poly_mod_ring_property
           ==> p IN RX.carrier /\ p o I = x    by ideal_cogen_property
           Thus poly p                         by poly_ring_property
             so poly (p % z)                   by poly_mod_poly
           If deg z = 0,
              Then p % z = |0|                 by poly_mod_by_const
                so (p % z) IN RM.carrier       by poly_mod_ring_property, deg z = 0
              and the goal becomes: |0| o I = p o I
              That is: (|0| == p) (pm z)       by poly_ideal_coset_eq
              or need: (|0| - p) % z = |0|     by poly_mod_eq_alt
              This is true                     by poly_mod_by_const
           If deg z <> 0,
              Then deg (p % z) < deg z         by poly_division_all, deg z <> 0
                so (p % z) IN RM.carrier       by poly_mod_ring_property, deg z <> 0
              and the goal becomes: (p % z) o I = p o I
              That is: (p % z == p) (pm z)     by poly_ideal_coset_eq
              or need: (p % z) % z = p % z     by pmod_def_alt
              This is true since p % z = p     by poly_mod_less, deg (p % z) < deg p
*)
val poly_mod_ring_iso_quotient_ring = store_thm(
  "poly_mod_ring_iso_quotient_ring",
  ``!r:'a ring. Ring r ==> !z. ulead z ==>
       RingIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
               (PolyModRing r z)
               (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z))``,
  rpt strip_tac >>
  qabbrev_tac `rx = (PolyRing r)` >>
  qabbrev_tac `zz = (principal_ideal rx z)` >>
  qabbrev_tac `Z = zz.carrier` >>
  `Ring rx` by rw[poly_add_mult_ring, Abbr`rx`] >>
  `zz << rx` by metis_tac[principal_ideal_ideal, poly_ring_property] >>
  rw_tac std_ss[RingIso_def] >-
  metis_tac[poly_mod_ring_homo_quotient_ring] >>
  rw[BIJ_DEF, SURJ_DEF, INJ_DEF] >-
  rw[poly_ideal_coset, Abbr`rx`, Abbr`zz`, Abbr`Z`] >-
 (Cases_on `deg z = 0` >-
  fs[poly_mod_ring_property] >>
  fs[poly_mod_ring_property] >>
  `(x == x') (pm z)` by rw[GSYM poly_ideal_coset_eq] >>
  `x % z = x' % z` by rw[GSYM pmod_def_alt] >>
  metis_tac[poly_mod_less]) >-
  rw[poly_ideal_coset, Abbr`rx`, Abbr`zz`, Abbr`Z`] >>
  qabbrev_tac `p = cogen rx.sum zz.sum x` >>
  qexists_tac `p % z` >>
  `p IN rx.carrier /\ (coset rx.sum p Z = x)` by metis_tac[ideal_cogen_property, quotient_ring_property] >>
  `poly p /\ poly (p % z)` by rw[poly_ring_property] >>
  Cases_on `deg z = 0` >| [
    `poly |0| /\ poly ( |0| - p)` by rw[] >>
    metis_tac[poly_mod_ring_property, poly_ideal_coset_eq, poly_mod_eq_alt, poly_mod_by_const],
    `deg (p % z) < deg z` by rw[poly_division] >>
    metis_tac[poly_mod_ring_property, poly_ideal_coset_eq, pmod_mod]
  ]);

(* This isomorphism between
        (PolyModRing r z) and (PolyRing r / principal_ideal (PolyRing r) z)
        is a major milestone!
*)

(* ------------------------------------------------------------------------- *)
(* Cardinality of Polynomial Modulo Ring                                     *)
(* ------------------------------------------------------------------------- *)

(* Given a ring R, form its polynomial ring R[x].
   Pick a polynomial z with 0 < deg z for modulo,
   CARD Rz = CARD R ** (deg z)
   If R = (ZN n),
     CARD (ZN n).carrier
   = CARD count n                by ZN_def
   = n                           by CARD_COUNT
   = char (ZN n)                 by ZN_ring_char
*)
(* Example of a ring with CARD R <> char r:
   The symdiff_inter_set, CARD R = CARD univ(:'a -> bool), char r = 2.

   Any example of a finite ring with CARD R <> char r ?
   Yes, char (R[x]) = char r, but CARD (R[x].carrier ) <> CARD R.
*)

(* Theorem: Rz = {p | poly p /\ ((p = []) \/ deg p < deg z)} *)
(* Proof:
     Rz
   = (PolyModRing r z).carrier            by notation
   = { p | poly p /\ if deg z = 0 then p = |0| else deg p < deg z }
                                          by poly_mod_ring_def, poly_remainders_def
   = { p | poly p /\ ((p = []) \/ deg p < deg z) }
                                          by EXTENSION, poly_deg_zero
*)
val poly_mod_ring_carrier_alt = store_thm(
  "poly_mod_ring_carrier_alt",
  ``!r:'a ring z:'a poly. Rz = {p | poly p /\ ((p = []) \/ deg p < deg z)}``,
  rw[poly_mod_ring_def, poly_remainders_def, EXTENSION] >>
  rw[EQ_IMP_THM] >>
  rw[]);

(* Theorem: FiniteRing r ==> FINITE Rz *)
(* Proof:
   FiniteRing r ==> Ring r /\ FINITE R     by FiniteRing_def
   and #0 IN R                             by ring_zero_element
   Let s = {p | weak p /\ (LENGTH p = deg z)},
       t = {p | poly p /\ ((p = []) \/ deg p < deg z)}.
   Note BIJ chop s t      by weak_poly_poly_bij
    Now FINITE s          by weak_poly_finite
     so FINITE t          by FINITE_BIJ
     or FINITE Rz         by poly_mod_ring_carrier_alt
*)
val poly_mod_ring_finite = store_thm(
  "poly_mod_ring_finite",
  ``!r:'a ring z:'a poly. FiniteRing r ==> FINITE Rz``,
  rw[FiniteRing_def] >>
  `#0 IN R` by rw[] >>
  metis_tac[weak_poly_poly_bij, weak_poly_finite, FINITE_BIJ, poly_mod_ring_carrier_alt]);

(* Theorem: FiniteRing r ==> CARD Rz = (CARD R) ** (deg z)  *)
(* Proof:
     CARD Rz
   = CARD { p | poly p /\ ((p = []) \/ deg p < deg z) }    by poly_mod_ring_carrier_alt
   = CARD { p | weak p /\ (LENGTH p = deg z) }             by weak_poly_poly_bij, weak_poly_finite, FINITE_BIJ
   = CARD R ** (deg z)                                     by weak_poly_card
*)
val poly_mod_ring_card = store_thm(
  "poly_mod_ring_card",
  ``!r:'a ring z. FiniteRing r ==> (CARD Rz = (CARD R) ** (deg z))``,
  rw[FiniteRing_def] >>
  `#0 IN R` by rw[] >>
  metis_tac[poly_mod_ring_carrier_alt, weak_poly_poly_bij, weak_poly_finite, FINITE_BIJ, weak_poly_card]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Theorems                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ((PolyModRing r z).prod excluding |0|).id =
            if deg z = 0 then |0| else |1| *)
(* Proof: by poly_mod_ring_def, excluding_def *)
val poly_mod_prod_nonzero_id = store_thm(
  "poly_mod_prod_nonzero_id",
  ``!(r:'a ring) z. ((PolyModRing r z).prod excluding |0|).id =
       if deg z = 0 then |0| else |1|``,
  rw_tac std_ss[poly_mod_ring_def, excluding_def]);

(* Theorem: ulead z ==> FINITE ((PolyModRing r z).prod excluding |0|).carrier *)
(* Proof:
    Since  Ring (PolyModRing r z)                                         by poly_mod_ring_ring
       so  ((PolyModRing r z).prod.carrier = (PolyModRing r z).carrier)   by ring_mult_monoid
     Now,  ((PolyModRing r z).prod excluding |0|).carrier SUBSET (PolyModRing r z).prod.carrier
                                                                          by excluding_def, DIFF_SUBSET
    Since  FINITE (PolyModRing r z).carrier                               by poly_mod_ring_finite
    Hence  FINITE ((PolyModRing r z).prod excluding |0|).carrier          by SUBSET_FINITE
*)
val poly_mod_ring_prod_finite = store_thm(
  "poly_mod_ring_prod_finite",
  ``!r:'a ring z. FiniteRing r /\ ulead z ==>
                 FINITE ((PolyModRing r z).prod excluding |0|).carrier``,
  rpt strip_tac >>
  `Ring r` by metis_tac[FiniteRing_def] >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `(PolyModRing r z).prod.carrier = (PolyModRing r z).carrier` by rw[ring_mult_monoid] >>
  `((PolyModRing r z).prod excluding |0|).carrier SUBSET (PolyModRing r z).prod.carrier` by rw[excluding_def] >>
  `FINITE (PolyModRing r z).carrier` by rw[poly_mod_ring_finite] >>
  metis_tac[SUBSET_FINITE]);

(* Theorem: Ring r /\ 0 < deg z ==>
            !p. p IN ((PolyModRing r z).prod excluding |0|).carrier <=>
                (poly p /\ p <> |0| /\ deg p < deg z) *)
(* Proof: by poly_mod_ring_property, excluding_def. *)
val poly_mod_ring_nonzero_element = store_thm(
  "poly_mod_ring_nonzero_element",
  ``!r:'a ring z. Ring r /\ 0 < deg z ==>
   !p. p IN ((PolyModRing r z).prod excluding |0|).carrier <=>
           (poly p /\ p <> |0| /\ deg p < deg z)``,
  rw[poly_mod_ring_property, excluding_def] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Exponentiation in Polynomial Ring                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ ulead z ==>
            !n. ((PolyModRing r z).prod excluding |0|).exp p n = (p ** n) % z *)
(* Proof:
   Expand by poly_mod_ring_def, poly_remainders_def, monoid_exp_def, excluding_def.
   If deg z = 0,
   This is to show: FUNPOW (\y. (p * y) % z) n |0| = FUNPOW ($* p) n |1| % z
   By induction on n.
   Base case: FUNPOW (\y. (p * y) % z) 0 |0| = FUNPOW ($* p) 0 |1| % z
     LHS = FUNPOW (\y. (p * y) % z) 0 |0|
         = |0|                              by FUNPOW_0
         = |1| % z                          by poly_mod_by_const
         = (FUNPOW ($* p) |1|) % z          by FUNPOW_0
         = RHS
   Step case: FUNPOW (\y. (p * y) % z) n |0| = FUNPOW ($* p) n |1| % z ==>
              FUNPOW (\y. (p * y) % z) (SUC n) |0| = FUNPOW ($* p) (SUC n) |1| % z
    Note !j. poly (FUNPOW ($* p) j |1|)     by poly_exp_poly, poly_mult_monoid, monoid_exp_def
    LHS = FUNPOW (\y. (p * y) % z) (SUC n) |0|
        = (p * FUNPOW (\y. (p * y) % z) n |0|) % z   by FUNPOW_SUC
        = (p * FUNPOW ($* p) n |1| % z) % z          by induction hypothesis
        = |0|                                        by poly_mod_by_const, j = n
        = FUNPOW ($* p) (SUC n) |1| % z              by poly_mod_by_const, j = SUC n
        = RHS

   If deg z <> 0,
   This is to show: FUNPOW (\y. (p * y) % z) n |1| = FUNPOW ($* p) n |1| % z
   By induction on n.
   Base case: FUNPOW (\y. (p * y) % z) 0 |1| = FUNPOW ($* p) 0 |1| % z
     LHS = FUNPOW (\y. (p * y) % z) 0 |1|
         = |1|                              by FUNPOW_0
         = |1| % z                          by poly_mod_one
         = (FUNPOW ($* p) |0|) % z          by FUNPOW_0
         = RHS
   Step case: FUNPOW (\y. (p * y) % z) n |1| = FUNPOW ($* p) n |1| % z ==>
              FUNPOW (\y. (p * y) % z) (SUC n) |1| = FUNPOW ($* p) (SUC n) |1| % z
    Note !j. poly (FUNPOW ($* p) j |1|)     by poly_exp_poly, poly_mult_monoid, monoid_exp_def
    LHS = FUNPOW (\y. (p * y) % z) (SUC n) |1|
        = (p * FUNPOW (\y. (p * y) % z) n |1|) % z   by FUNPOW_SUC
        = (p * FUNPOW ($* p) n |1| % z) % z          by induction hypothesis
        = (p % z * FUNPOW ($* p) n |1| % z % z) % z  by poly_mod_mult
        = (p % z * FUNPOW ($* p) n |1| % z) % z      by poly_mod_mod
        = (p * FUNPOW ($* p) n |1|) % z % z          by poly_mod_mult
        = (p * FUNPOW ($* p) n |1|) % z              by poly_mod_mod
        = FUNPOW ($* p) (SUC n) |1| % z              by FUNPOW_SUC
        = RHS
*)
val poly_mod_exp_alt = store_thm(
  "poly_mod_exp_alt",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==>
   !n. ((PolyModRing r z).prod excluding |0|).exp p n = (p ** n) % z``,
  rw[poly_mod_ring_def, poly_remainders_def, monoid_exp_def, excluding_def] >>
  (Cases_on `deg z = 0` >> simp[]) >| [
    Induct_on `n` >-
    rw[poly_mod_by_const] >>
    rw_tac std_ss[FUNPOW_SUC] >>
    `!n. poly (FUNPOW ($* p) n |1|)` by metis_tac[poly_exp_poly, poly_mult_monoid, monoid_exp_def] >>
    rw[poly_mod_by_const],
    Induct_on `n` >-
    rw[] >>
    rw_tac std_ss[FUNPOW_SUC] >>
    `!n. poly (FUNPOW ($* p) n |1|)` by metis_tac[poly_exp_poly, poly_mult_monoid, monoid_exp_def] >>
    metis_tac[poly_mod_mult, poly_mod_mod, poly_mod_poly]
  ]);

(* Theorem: Ring r /\ ulead z ==> !p. p IN Rz ==> !n. p **z n = (p ** n) % z *)
(* Proof:
   By induction on n.
   Base: p **z 0 = p ** 0 % z
       If deg z = 0,
         p **z 0
       = #1z                           by ring_exp_0
       = |0|                           by poly_mod_ring_ids, deg z = 0
       = (p ** 0) % z                  by poly_mod_by_const

       If deg z <> 0,
         p **z 0
       = #1z                           by ring_exp_0
       = |1|                           by poly_mod_ring_ids, deg z <> 0
       = |1| % z                       by poly_mod_one
       = (p ** 0) % z                  by poly_exp_0
   Step: p **z n = p ** n % z ==> p **z SUC n = p ** SUC n % z
      Note Ring (PolyModRing r z)      by poly_mod_ring_ring
        so p **z n IN Rz               by ring_exp_element
      If deg z = 0,
       Then p = |0|                    by poly_mod_ring_element, deg z = 0
         |0| **z SUC n
       = |0| *z ( |0| **z n)           by ring_exp_SUC
       = (|0| * ( |0| **z n)) % z      by poly_mod_ring_mult
       = |0|                           by poly_mod_by_const
       = (p ** SUC n) % z              by poly_mod_by_const

      If deg z <> 0,
       Now poly p /\ deg p < deg z     by poly_mod_ring_element, deg z <> 0
       and poly (p **z n) /\ deg (p **z n) < deg z
                                       by poly_mod_ring_element, deg z <> 0
         p **z SUC n
       = p *z (p **z n)                by ring_exp_SUC
       = (p * (p **z n)) % z           by poly_mod_ring_mult
       = (p * ((p ** n) % z)) % z      by induction hypothesis
       = ((p % z) * (p ** n) % z) % z  by poly_mod_less
       = (p * p ** n) % z              by poly_mod_mult
       = (p ** SUC n) % z              by poly_exp_SUC
*)
val poly_mod_ring_exp = store_thm(
  "poly_mod_ring_exp",
  ``!r:'a ring z:'a poly. Ring r /\ ulead z ==> !p. p IN Rz ==> !n. p **z n = (p ** n) % z``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[poly_mod_ring_ids, poly_mod_by_const] >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `(p **z n) IN Rz` by rw[ring_exp_element] >>
  Cases_on `deg z = 0` >| [
    `p = |0|` by metis_tac[poly_mod_ring_element] >>
    rw[poly_mod_ring_mult, poly_mod_by_const],
    `poly p /\ deg p < deg z` by metis_tac[poly_mod_ring_element] >>
    `poly (p **z n) /\ deg (p **z n) < deg z` by metis_tac[poly_mod_ring_element] >>
    rw_tac std_ss[ring_exp_SUC, poly_mod_ring_mult, poly_mod_less, poly_mod_mult, poly_exp_poly, poly_exp_SUC]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Theorems when coefficient is field rather than ring.           *)
(* ------------------------------------------------------------------------- *)

(* Note: from polyFieldTheory, exported:
poly_field_unit_lead
|- !r. Field r ==> !p. poly p /\ p <> |0| ==> unit (lead p)
*)

val poly_field_mod_ring_sum_abelian_group = store_thm("poly_field_mod_ring_sum_abelian_group",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> AbelianGroup (PolyModRing r z).sum``,
  rw[poly_mod_ring_sum_abelian_group]);

val poly_field_mod_ring_prod_abelian_monoid = store_thm("poly_field_mod_ring_prod_abelian_monoid",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> AbelianMonoid (PolyModRing r z).prod``,
  rw[poly_mod_ring_prod_abelian_monoid]);

val poly_field_mod_ring_ring = store_thm("poly_field_mod_ring_ring",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> Ring (PolyModRing r z)``,
  rw[poly_mod_ring_ring]);

val poly_field_mod_ring_neg = store_thm("poly_field_mod_ring_neg",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> !p. p IN Rz ==> ($-z p = (-p) % z)``,
  rw[poly_mod_ring_neg]);

val poly_field_mod_ring_sub = store_thm("poly_field_mod_ring_sub",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==>
    !p q. p IN Rz /\ q IN Rz ==> (p -z q = (p - q) % z)``,
  rw[poly_mod_ring_sub]);

val poly_field_ideal_coset = store_thm("poly_field_ideal_coset",
  ``!r:'a field. Field r ==> !z. poly z ==>
    !x. x IN Rz ==> coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier IN
                          (PolyRing r / principal_ideal (PolyRing r) z).carrier``,
  rw[poly_ideal_coset]);

val poly_field_ideal_coset_eq = store_thm("poly_field_ideal_coset_eq",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==>
    !p q. poly p /\ poly q ==>
     ((coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier =
       coset (PolyRing r).sum q (principal_ideal (PolyRing r) z).carrier) <=> (p == q) (pm z))``,
  rw[poly_ideal_coset_eq]);

val poly_field_ideal_cogen_property = store_thm("poly_field_ideal_cogen_property",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==>
    !p q. poly p /\ poly q ==>
   ((q = cogen (PolyRing r).sum
               (principal_ideal (PolyRing r) z).sum
               (coset (PolyRing r).sum p (principal_ideal (PolyRing r) z).carrier)) ==> (p == q) (pm z))``,
  rw[poly_ideal_cogen_property]);

Theorem poly_field_mod_sum_group_homo_quotient_ring:
  !r:'a field.
    Field r ==> !z. poly z /\ z <> |0| ==>
    GroupHomo
      (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
      (PolyModRing r z).sum
      (PolyRing r / principal_ideal (PolyRing r) z).sum
Proof
  rw[poly_mod_sum_group_homo_quotient_ring]
QED

Theorem poly_field_mod_prod_monoid_homo_quotient_ring:
  !r:'a field.
    Field r ==>
    !z. poly z /\ z <> |0| ==>
        MonoidHomo
         (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
         (PolyModRing r z).prod
         (PolyRing r / principal_ideal (PolyRing r) z).prod
Proof
  rw[poly_mod_prod_monoid_homo_quotient_ring]
QED

Theorem poly_field_mod_ring_homo_quotient_ring:
  !r:'a field.
    Field r ==>
    !z. poly z /\ z <> |0| ==>
        RingHomo
         (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
         (PolyModRing r z)
         (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z))
Proof
  rw[poly_mod_ring_homo_quotient_ring]
QED

Theorem poly_field_mod_ring_iso_quotient_ring:
  !r:'a field.
    Field r ==>
    !z. poly z /\ z <> |0| ==>
        RingIso
         (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
         (PolyModRing r z)
         (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) z))
Proof
  rw[poly_mod_ring_iso_quotient_ring]
QED

val poly_field_mod_exp_alt = store_thm("poly_field_mod_exp_alt",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
    !n. ((PolyModRing r z).prod excluding |0|).exp p n = (p ** n) % z``,
  rw[poly_mod_exp_alt]);

val poly_field_mod_ring_exp = store_thm("poly_field_mod_ring_exp",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==>
    !p. p IN Rz ==> !n. p **z n = (p ** n) % z``,
  rw[poly_mod_ring_exp]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
