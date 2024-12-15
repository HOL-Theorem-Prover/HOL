(* ------------------------------------------------------------------------- *)
(* Polynomial with coefficients from a Field  (Part 3)                       *)
(* To show: Polynomial Ring Modulo Irreducible forms a Finite Field.         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyFieldModulo";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyDivisionTheory polyFieldDivisionTheory;
open polyModuloRingTheory polyRingModuloTheory;
open polyDividesTheory;
open polyEvalTheory;
open polyBinomialTheory;

open polyIrreducibleTheory;
open polyRootTheory;
open polyMonicTheory;

open polyProductTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open fieldMapTheory;
open fieldIdealTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Field Polynomial Modulo Documentation                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   RRz              = (PolyRing (PolyModRing r z)).carrier
   zeropz p         = zero_poly (PolyModRing r z) p
   weakz  p         = Weak (PolyModRing r z) p
   polyz  p         = Poly (PolyModRing r z) p
   chopz  p         = poly_chop (PolyModRing r z) p
   negz   p         = weak_neg (PolyModRing r z) p
   -z p             = poly_neg (PolyModRing r z) p
   p ||z q          = weak_add (PolyModRing r z) p q
   p +z q           = poly_add (PolyModRing r z) p q
   p -z q           = poly_sub (PolyModRing r z) p q
   c oz p           = weak_cmult (PolyModRing r z) c p
   c *z p           = poly_cmult (PolyModRing r z) c p
   p oz q           = weak_mult (PolyModRing r z) p q
   p *z q           = poly_mult (PolyModRing r z) p q
   p >>z n          = poly_shift (PolyModRing r z) p n
   ##z n            = poly_num (PolyModRing r z) n
   p **z n          = poly_exp (PolyModRing r z) p n
   degz p           = poly_deg (PolyModRing r z) p
   leadz p          = poly_lead (PolyModRing r z) p
   p 'z k           = poly_coeff (PolyModRing r z) p k
   |0|z             = poly_zero (PolyModRing r z)
   |1|z             = poly_one (PolyModRing r z)
   |c|z             = poly_num (PolyModRing r z) c
   |X|              = |1|z >>z 1
   unityz n         = Unity (PolyModRing r z) n
   masterz n        = Master (PolyModRing r z) n
   monicz p         = Monic (PolyModRing r z) p
   unitz x          = Unit (PolyModRing r z) x
   uleadz p         = Ulead (PolyModRing r z) p
   pmonicz p        = Pmonic (PolyModRing r z) p
   upolyz p         = p IN (Invertibles (PolyRing (PolyModRing r z)).prod).carrier
   ipolyz p         = IPoly (PolyModRing r z) p
   evalz p x        = poly_eval (PolyModRing r z) p x
   rootz p x        = poly_root (PolyModRing r z) p x
   rootsz p         = poly_roots (PolyModRing r z) p
   factorz c        = poly_factor (PolyModRing r z) c
   forderz x        = order ((PolyModRing r z).prod excluding |0|)
   p pdividesz q    = poly_divides (PolyModRing r z) p q
   pprime p         = ring_prime (PolyRing r) p
   norm p           = if p = |0| then 0 else SUC (deg p)
   up e             = if e = #0 then |0| else [e]
   lift p           = poly_lift r p
   ||0||            = (PolyRing (PolyRing r)).sum.id
   p |+| q          = (PolyRing (PolyModRing r z)).sum.op p q
   p |*| q          = (PolyRing (PolyModRing r z)).prod.op p q
   PolyModConst r z = poly_mod_const r z
   RCz              = (PolyModConst r z).carrier
*)
(* Definitions and Theorems (# are exported):

   Polynomial Ring F[x] is a Euclidean Ring:
   poly_ring_euclid_ring           |- !r. Field r ==> EuclideanRing (PolyRing r) (\p. norm p)
   poly_norm_eq_length             |- !p. norm p = LENGTH p
   poly_ring_euclid_ring_alt       |- !r. Field r ==> EuclideanRing (PolyRing r) LENGTH
   poly_ring_principal_ideal_ring  |- !r. Field r ==> PrincipalIdealRing (PolyRing r)
   poly_irreducible_ideal_maximal  |- !r. Field r ==> !p. ipoly p ==>
                                          ideal_maximal (PolyRing r) (principal_ideal (PolyRing r) p)
   poly_irreducible_ideal_property |- !r. Ring r ==> !p. ipoly p ==>
                                          |1| NOTIN (principal_ideal (PolyRing r) p).carrier
   poly_irreducible_quotient_field |- !r. Field r ==> !p. ipoly p ==>
                                          Field (PolyRing r / principal_ideal (PolyRing r) p)

   Irreducible Polynomials are Primes:
   poly_mod_zero_eq_divides        |- !r z p. Ring r /\ ulead z /\ poly p ==>
                                                     (ring_divides (PolyRing r) z p <=> p % z = |0|)
   poly_field_mod_zero_eq_divides  |- !r z p. Field r /\ poly z /\ z <> |0| /\ poly p ==>
                                                      (ring_divides (PolyRing r) z p <=> (p % z = |0|))
   poly_mod_prime_product          |- !r z. Ring r /\ ulead z ==>
                                          (pprime z <=> !x y. poly x /\ poly y /\
                                            ((x * y) % z = |0|) ==> (x % z = |0|) \/ (y % z = |0|))
   poly_field_mod_prime_product    |- !r z. Field r /\ poly z /\ z <> |0| ==>
                                          (pprime z <=> !x y. poly x /\ poly y /\
                                            ((x * y) % z = |0|) ==> (x % z = |0|) \/ (y % z = |0|))
   poly_prime_divides              |- !r z. Ring r /\ ulead z ==>
                                          (pprime z <=> !x y. poly x /\ poly y /\
                                            z pdivides x * y ==> z pdivides x \/ z pdivides y)
   poly_prime_divides_product      |- !r. Ring r ==> !p q. poly p /\ poly q ==>
                                      !t. poly t /\ pprime t /\ t pdivides p * q ==> t pdivides p \/ t pdivides q
   poly_monic_prime_power_divides_product
                                   |- !r. Ring r /\ #1 <> #0 ==> !p q. poly p /\ poly q ==>
                                      !t. monic t /\ pprime t /\ ~(t pdivides q) ==>
                                      !n. t ** n pdivides p * q ==> t ** n pdivides p

   poly_irreducible_prime          |- !r. Field r ==> !p. ipoly p ==> pprime p
   poly_X_add_c_pprime             |- !r. Field r ==> !c. pprime (X + |c|)
   poly_X_sub_c_pprime             |- !r. Field r ==> !c. pprime (X - |c|)
   poly_X_add_c_divides_product    |- !r. Field r ==> !c p q. poly p /\ poly q /\
                                                      ((p * q) % (X + |c|) = |0|) ==>
                                                      (p % (X + |c|) = |0|) \/ (q % (X + |c|) = |0|)
   poly_X_sub_c_divides_product    |- !r. Field r ==> !c p q. poly p /\ poly q /\
                                                      ((p * q) % (X - |c|) = |0|) ==>
                                                      (p % (X - |c|) = |0|) \/ (q % (X - |c|) = |0|)

   poly_mod_mult_eq_zero           |- !r. Field r ==> !x y z. poly x /\ poly y /\ ipoly z ==>
                                                 (((x * y) % z = |0|) <=> (x % z = |0|) \/ (y % z = |0|))
   poly_mod_zero_deg_le            |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                                                 (p % q = |0|) ==> deg q <= deg p
   poly_field_mod_deg_less_eq_zero |- !r z. Field r /\ pmonic z ==>
                                      !x. poly x /\ deg x < deg z /\ (x % z = |0|) ==> (x = |0|)

   More Properties of Irreducible Polynomials:
   poly_irreducible_divides_exp      |- !r. Field r ==> !z. monic z /\ ipoly z ==> !p n. poly p /\
                                                            z pdivides p ** n ==> z pdivides p
   poly_irreducible_mult_divides     |- !r. Field r ==> !x y p. monic x /\ ipoly x /\ poly y /\ poly p /\
                                            x pdivides p /\ y pdivides p /\ ~(x pdivides y) ==> x * y pdivides p
   poly_irreducible_not_divides_one  |- !r. Field r ==> !p. ipoly p ==> ~(p pdivides |1|)
   poly_monic_divides_irreducible    |- !r. Field r ==> !p q. monic p /\ 0 < deg p /\
                                            monic q /\ ipoly q /\ p pdivides q ==> (p = q)
   poly_irreducible_divides_prod_set |- !r. Field r ==> !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
                                        !e. monic e /\ ipoly e ==> (e IN s <=> e pdivides PPROD s)
   poly_distinct_irreducibles_divides_exp      |- !r. Field r ==>
                                      !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
                                      !p n. poly p /\ PPROD s pdivides p ** n ==> PPROD s pdivides p
   poly_distinct_irreducibles_mod_exp_eq_zero  |- !r. Field r ==>
                                      !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
                                      !p n. poly p /\ (p ** n == |0|) (pm (PPROD s)) ==> (p == |0|) (pm (PPROD s))
   poly_distinct_irreducibles_mod_exp_char_eq  |- !r. FiniteField r ==>
                                      !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
               !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (PPROD s)) ==> (p == q) (pm (PPROD s))

   Quotient Field and Polynomial Ring modulo Irreducible Polynomial:
   poly_quotient_field_iso_poly_mod |- !r. Field r ==> !p. ipoly p ==>
      FieldIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) p).carrier)
               (PolyModRing r p)
               (PolyRing r / principal_ideal (PolyRing r) p)
   poly_mod_ring_prod_monoid        |- !r. Field r ==> !p. ipoly p ==>
                                           Monoid ((PolyModRing r p).prod excluding |0|)

   Polynomial Ring Modulo irreducible gives Finite Field:

   Polynomial GCD and Inverse:
   poly_linear_eq_const_property  |- !r. Ring r ==> !p q a b c.
                                         pmonic p /\ poly q /\ poly a /\ poly b /\ c IN R /\ c <> #0 /\
                                         (a * p + b * q = [c]) ==> ((b * q) % p = [c])
   poly_linear_eq_const_property1 |- !r. Ring r ==> !p q a b c.
                                         pmonic p /\ poly q /\ poly a /\ poly b /\ c IN R /\ c <> #0 /\
                                         (a * p + b * q = [c]) ==> b % p <> |0|
   poly_linear_eq_const_property2 |- !r. Field r ==> !p q a b c.
                                         pmonic p /\ poly q /\ poly a /\ poly b /\ c IN R /\ c <> #0 /\
                                         (a * p + b * q = [c]) ==> ((q * ( |/ c * b % p)) % p = |1|)
   poly_mod_prod_inv          |- !r. Field r ==> !p. ipoly p ==>
                                 !x. poly x /\ deg x < deg p /\ x <> |0| ==>
                                 ?y. ((poly y /\ deg y < deg p) /\ y <> |0|) /\ ((x * y) % p = |1|)
   poly_mod_prod_group        |- !r. Field r ==> !p. ipoly p ==>
                                     Group ((PolyModRing r p).prod excluding |0|)
   poly_mod_prod_finite_group |- !r. FiniteField r ==> !p. ipoly p ==>
                                     FiniteGroup ((PolyModRing r p).prod excluding |0|)
   poly_mod_irreducible_ring  |- !r. Field r ==> !p. ipoly p ==> Ring (PolyModRing r p)
   poly_mod_irreducible_field |- !r. Field r ==> !p. ipoly p ==> Field (PolyModRing r p)
   poly_mod_irreducible_finite_field  |- !r. FiniteField r ==> !p. ipoly p ==> FiniteField (PolyModRing r p)
   poly_mod_irreducible_field_card    |- !r. FiniteField r ==> !z. ipoly z ==> (CARD Rz = CARD R ** deg z)
   poly_mod_field_exp       |- !r. Field r ==> !z. ipoly z ==> !p. poly p ==> !n. (p % z) **z n = p ** n % z
   poly_mod_one_sum_n       |- !r z. Ring r /\ pmonic z ==> !n. ##z |1| n = chop [##n]
   poly_mod_ring_monic_ring |- !r. Ring r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z)
   poly_mod_ring_monic_alt  |- !r. Field r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z)
   poly_mod_ring_char       |- !r. Ring r ==> !p. pmonic p ==> (char (PolyModRing r p) = char r)
   poly_mod_ring_char_alt   |- !r. Field r ==> !z. monic z /\ 0 < deg z ==> (char (PolyModRing r z) = char r)
   poly_mod_prod_nonzero_abelian_group        |- !r. Field r ==> !p. monic p /\ ipoly p ==>
                                                     AbelianGroup ((PolyModRing r p).prod excluding |0|)
   poly_mod_prod_nonzero_finite_abelian_group |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                                     FiniteAbelianGroup ((PolyModRing r p).prod excluding |0|)

   Constant Polynomials of Quotient Field:

   Lifting of Elements from Field r to (PolyRing r):
   up_zero      |- !r. up #0 = |0|
   up_one       |- !r. #1 <> #0 ==> (up #1 = |1|)
   up_alt       |- !r x. up x = chop [x]
   up_poly      |- !r x. x IN R ==> poly (up x)
   up_add       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x + y) = up x + up y)
   up_mult      |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x * y) = up x * up y)
   up_neg       |- !r. Ring r ==> !x. x IN R ==> (up (-x) = -up x)
   up_sub       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x - y) = up x - up y)
   up_num       |- !r n. up (##n) = chop [##n]
   up_exp       |- !r. Ring r /\ #1 <> #0 ==> !x. x IN R ==> !n. up (x ** n) = up x ** n
   up_eq_zero   |- !r x. (up x = |0|) <=> (x = #0)
   up_nonzero   |- !r x. x IN R+ ==> up x <> |0|
   up_eq_one    |- !r. Ring r /\ #1 <> #0 ==> !x. (up x = |1|) <=> (x = #1)
   up_eq        |- !r x y. (up x = up y) <=> (x = y)
   up_deg       |- !r x. x IN R ==> (deg (up x) = 0)

   Lifting Polynomial from F[x] to (F[x] mod z)[y]:
#  poly_lift_def            |- !r p. lift p = MAP up p
   zero_poly_lift_zero      |- !r. ||0|| = []
   poly_lift_zero           |- !r. lift |0| = ||0||
   poly_lift_of_zero        |- !r. lift [] = []
   poly_lift_one            |- !r. #1 <> #0 ==> (lift |1| = [|1|])
   poly_lift_const          |- !r c. c IN R /\ c <> #0 ==> (lift [c] = [[c]])
   poly_lift_cons           |- !r h t. lift (h::t) = (if h = #0 then |0| else [h])::lift t
   poly_lift_eq_zero        |- !r p. (lift p = ||0||) <=> (p = |0|)
   poly_lift_eq_one         |- !r. Ring r /\ #1 <> #0 ==> !p. (lift p = [|1|]) <=> (p = |1|)
   poly_lift_eq_zero_poly   |- !r p. zero_poly (PolyRing r) (lift p) <=> zerop p
   poly_lift_zero_poly      |- !r p. zerop p <=> zero_poly (PolyRing r) (lift p)
   poly_lift_chop           |- !r p. lift (chop p) = poly_chop (PolyRing r) (lift p)
   poly_lift_poly           |- !r p. poly p ==> Poly (PolyRing r) (lift p)
   poly_lift_deg            |- !r p. poly_deg (PolyRing r) (lift p) = deg p
   poly_eval_lift_poly_by_X |- !r. Ring r ==> !p. poly p ==> (poly_eval (PolyRing r) (lift p) X = p)
   poly_eval_lift_poly_poly |- !r. Ring r ==> !p q. poly p /\ poly q ==> poly (poly_eval (PolyRing r) (lift p) q)
   poly_lift_sub_eq_zero    |- !r. Ring r ==> !p q. poly p /\ poly q /\ (lift (p - q) = ||0||) ==> (p = q)

   Lifting of Elements from Field r to (PolyModRing r z):
   up_element   |- !r x z. x IN R /\ 0 < deg z ==> up x IN Rz
   up_mod       |- !r z. Ring r /\ pmonic z ==> !x. x IN R ==> (up x = up x % z)
   up_mod_add   |- !r z. Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x + y) = up x +z up y)
   up_mod_mult  |- !r z. Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x * y) = up x *z up y)
   up_mod_neg   |- !r z. Ring r /\ pmonic z ==> !x. x IN R  ==> (up (-x) = $-z (up x))
   up_mod_sub   |- !r z. Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x - y) = up x -z up y)
   up_num_mod   |- !r z. Ring r /\ pmonic z ==> !n. up (##n) = ##z #1z n
   up_mod_exp   |- !r z. Ring r /\ pmonic z ==> !x. x IN R ==> !n. up (x ** n) = up x **z n
   up_mod_inv   |- !r z. Field r /\ ipoly z ==> !x. x IN R+ ==> (up ( |/ x) = |/z (up x))

   Lifting of Polynomials to (PolyModRing r z):
   poly_mod_poly_zero         |- !r z. |0|z = ||0||
   poly_mod_poly_one          |- !r z. #1 <> #0 /\ 0 < deg z ==> ( |1|z = [|1|])
   poly_mod_lift_eq_zero_poly |- !r z p. zeropz (lift p) <=> zerop p
   poly_mod_lift_eq_zero      |- !r z p. (lift p = |0|z) <=> (p = |0|)
   poly_mod_lift_deg          |- !r p. degz (lift p) = deg p
   poly_mod_lift_lead         |- !r z. Ring r /\ pmonic z ==> !p. leadz (lift p) = up (lead p)
   poly_mod_lift_coeff        |- !r z. Ring r /\ pmonic z ==> !p k. lift p 'z k = up (p ' k)
   poly_mod_lift_unit         |- !r z. Ring r /\ pmonic z ==> !x. unit x ==> unitz (up x)
   poly_mod_lift_weak         |- !r z p. weak p /\ 0 < deg z ==> weakz (lift p)
   poly_mod_lift_poly         |- !r z. Ring r /\ 0 < deg z ==> !p. poly p ==> polyz (lift p)
   poly_mod_lift_pmonic       |- !r z. Ring r /\ pmonic z ==> !p. pmonic p ==> pmonicz (lift p)
   poly_mod_lift_monic        |- !r z. Ring r /\ pmonic z ==> !p. monic p ==> monicz (lift p)
   poly_mod_lift_monic_iff    |- !r z. Ring r /\ pmonic z ==> !p. poly p ==> (monic p <=> monicz (lift p))
   poly_mod_lift_chop         |- !r. Ring r ==> !p z. lift (chop p) = chopz (lift p)
   poly_mod_lift_weak_add     |- !r z. Ring r /\ pmonic z ==>
                                 !p q. weak p /\ weak q ==> (lift (p || q) = lift p ||z lift q)
   poly_mod_lift_poly_add     |- !r z. Ring r /\ pmonic z ==>
                                 !p q. poly p /\ poly q ==> (lift (p + q) = lift p +z lift q)
   poly_mod_lift_weak_neg     |- !r z. Ring r /\ pmonic z ==> !p. weak p ==> (lift (neg p) = negz (lift p))
   poly_mod_lift_poly_neg     |- !r z. Ring r /\ pmonic z ==> !p. poly p ==> (lift (-p) = $-z (lift p))
   poly_mod_lift_poly_sub     |- !r z. Ring r /\ pmonic z ==>
                                 !p q. poly p /\ poly q ==> (lift (p - q) = lift p -z lift q)
   poly_mod_lift_weak_cmult   |- !r z. Ring r /\ pmonic z ==>
                                 !p c. weak p /\ c IN R ==> (lift (c o p) = up c oz lift p)
   poly_mod_lift_poly_cmult   |- !r z. Ring r /\ pmonic z ==>
                                 !p c. poly p /\ c IN R ==> (lift (c * p) = up c *z lift p)
   poly_mod_lift_poly_shift   |- !r z. Ring r /\ pmonic z ==> !p n. lift (p >> n) = lift p >>z n
   poly_mod_lift_element      |- !r z. Ring r /\ pmonic z ==> !p. poly p ==> lift p IN RRz
   poly_mod_lift_zero         |- !r z. |0|z = lift |0|
   poly_mod_ring_zero         |- !r z. |0|z = ||0||
   poly_mod_lift_one          |- !r z. 0 < deg z ==> ( |1|z = lift |1|)
   poly_mod_lift_X            |- !r z. Ring r /\ pmonic z ==> lift X = |X|
   poly_mod_lift_weak_mult    |- !r z. Ring r /\ pmonic z ==>
                                 !p q. weak p /\ weak q ==> (lift (p o q) = lift p oz lift q)
   poly_mod_lift_poly_mult    |- !r z. Ring r /\ pmonic z ==>
                                 !p q. poly p /\ poly q ==> (lift (p * q) = lift p *z lift q)
   poly_mod_lift_poly_exp     |- !r z. Ring r /\ pmonic z ==>
                                 !p. poly p ==> !n. lift (p ** n) = lift p **z n
   poly_mod_lift_unity        |- !r z. Ring r /\ pmonic z ==> !n. lift (unity n) = unityz n
   poly_mod_lift_poly_divides |- !r z. Ring r /\ pmonic z ==>
                                 !p q. poly p /\ poly q /\ p pdivides q ==> lift p pdividesz lift q
   poly_mod_lift_mod_poly     |- !r. Ring r ==> !p z. poly p /\ pmonic z ==> polyz (lift (p % z))
   poly_mod_lift_poly_divides_iff
                              |- !r z. Ring r /\ pmonic z ==> !p q. pmonic p /\ poly q ==>
                                     (p pdivides q <=> lift p pdividesz lift q)
   poly_mod_lift_poly_mod     |- !r z. Ring r /\ pmonic z ==>
                                 !p q t. poly p /\ poly q /\ pmonic t ==>
                                     ((p == q) (pm t) <=> (lift p == lift q) (pmod (PolyModRing r z) (lift t)))

   Polynomial Lifting Theorems:
   poly_peval_alt             |- !r. Ring r ==> !p q. poly p /\ poly q ==>
                                     (peval p q = poly_eval (PolyRing r) (lift p) q)
   poly_mod_eval_lift_by_poly_eval_lift
                              |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                                     (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z)
   poly_mod_eval_lift_by_poly_eval_lift_alt
                              |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
                                     (evalz (lift p) (q % z) = poly_eval (PolyRing r) (lift p) q % z)
   poly_mod_lift_root_by_mod_peval
                              |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                                     (rootz (lift p) q <=> (peval p q % z = |0|))
   poly_mod_lift_root_by_mod_peval_alt
                              |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
                                     (rootz (lift p) (q % z) <=> (peval p q % z = |0|))

   Polynomial Root X:
   poly_field_mod_eval_lift_by_poly_eval_lift
                              |- !r z. Field r /\ poly z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                                     (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z)
   poly_field_mod_lift_root_by_mod_peval
                              |- !r z. Field r /\ poly z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                                     (rootz (lift p) q <=> (peval p q % z = |0|))
   poly_field_mod_lift_has_root_X
                              |- !r z. Field r /\ poly z /\ 1 < deg z ==> rootz (lift z) X
   poly_field_mod_lift_has_root_X_alt
                              |- !r z. Field r /\ poly z /\ 1 < deg z ==> (peval z X % z = |0|)

   poly_irreducible_lift_has_root_X
                              |- !r z. Field r /\ ipoly z /\ 1 < deg z ==> rootz (lift z) X
   poly_mod_eq_gives_root_X   |- !r z. Ring r /\ ulead z /\ 1 < deg z ==>
                                 !p q. poly p /\ poly q /\ (p % z = q % z) ==> rootz (lift (p - q)) X
   poly_mod_lift_root_X_exp   |- !r z. Ring r /\ pmonic z ==> !p. poly p ==>
                                 !n. rootz (lift p) (X ** n % z) <=> (peval p (X ** n) % z = |0|)

   Polynomial Order:
   poly_zero_order       |- !r z. Ring r /\ pmonic z ==> (forderz |0| = 0)
   poly_X_order_nonzero  |- !r z. FiniteField r /\ ipoly z /\ 1 < deg z ==> 0 < forderz X
   poly_X_order_gt_1     |- !r z. FiniteField r /\ ipoly z /\ 1 < deg z ==> 1 < forderz X
   poly_order_eq_poly_mod_order
                         |- !r z p. Field r /\ ipoly z /\ poly p ==> (forderz p = forderz (p % z))
   poly_order_divides    |- !r z. Field r /\ ipoly z ==>
                            !p. poly p /\ p % z <> |0| ==> !k. (p ** k == |1|) (pm z) ==> forderz p divides k
   poly_X_order_divides  |- !r z. Field r /\ monic z /\ ipoly z /\ z <> unity 1 ==>
                            !k. 0 < k /\ (X ** k == |1|) (pm z) ==> forderz X divides k
   poly_order_eq_1       |- !r z. Field r /\ monic z /\ ipoly z ==>
                            !p. poly p /\ (forderz p = 1) ==> ((p % z = |0|) \/ (p % z = |1|))
   poly_mod_field_exp_eq_0
                         |- !r z. Field r /\ ipoly z /\ 1 < deg z ==>
                            !m n. m < forderz X /\ n < forderz X ==> ((X ** m == X ** n) (pm z) <=> (m = n))
   poly_mod_field_exp_eq_1
                         |- !r z. Field r /\ monic z /\ ipoly z /\ z <> X ==>
                            !m n. m < forderz X /\ n < forderz X ==> ((X ** m == X ** n) (pm z) <=> (m = n))
   poly_mod_field_exp_eq_condition
                         |- !r z. Field r /\ ipoly z ==>
                            !p. poly p /\ p <> |0| /\ deg p < deg z ==>
                            !m n. m < forderz p /\ n < forderz p ==> ((p ** m == p ** n) (pm z) <=> (m = n))

   Product of Monomials:
   poly_prod_set_image_X_add_c_deg     |- !r. Ring r /\ #1 <> #0 ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                                              (deg (PPROD (IMAGE (\c. X + |c|) s)) = CARD s)
   poly_prod_set_image_X_sub_c_deg     |- !r. Ring r /\ #1 <> #0 ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                                              (deg (PPIMAGE (\c. X - |c|) s) = CARD s)
   poly_prod_set_image_X_add_c_factor  |- !r. Ring r /\ #1 <> #0 ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                                          !n. n < char r /\ n IN s ==>
                                              (PPROD (IMAGE (\c. X + |c|) s) % (X + |n|) = |0|)
   poly_prod_set_image_X_sub_c_factor  |- !r. Ring r /\ #1 <> #0 ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                                          !n. n < char r /\ n IN s ==>
                                              (PPIMAGE (\c. X - |c|) s % (X - |n|) = |0|)
   poly_X_add_c_image_poly_subset      |- !r. Ring r ==>
                                          !s. IMAGE (\c. X + |c|) s SUBSET (PolyRing r).carrier
   poly_X_sub_c_image_poly_subset      |- !r. Ring r ==>
                                          !s. IMAGE (\c. X - |c|) s SUBSET (PolyRing r).carrier
   poly_prod_set_image_X_add_c_divides |- !r. Field r ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                     !n. n < char r ==> (PPIMAGE (\c. X + |c|) s % (X + |n|) = |0|) ==> n IN s
   poly_prod_set_image_X_sub_c_divides |- !r. Field r ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                     !n. n < char r ==> (PPIMAGE (\c. X - |c|) s % (X - |n|) = |0|) ==> n IN s
   poly_prod_set_image_X_add_c_property|- !r. Field r ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                     !n. n < char r ==> (n IN s <=> (PPIMAGE (\c. X + |c|) s % (X + |n|) = |0|))
   poly_prod_set_image_X_sub_c_property|- !r. Field r ==>
                                          !s. FINITE s /\ MAX_SET s < char r ==>
                     !n. n < char r ==> (n IN s <=> (PPIMAGE (\c. X - |c|) s % (X - |n|) = |0|))
   poly_prod_set_image_X_add_c_inj     |- !r. Field r ==> !n. n < char r ==>
                                              INJ (\s. PPIMAGE (\c. X + |c|) s)
                                                  (PPOW (natural n)) (PolyRing r).carrier
   poly_prod_set_image_X_sub_c_inj     |- !r. Field r ==> !n. n < char r ==>
                                              INJ (\s. PPIMAGE (\c. X - |c|) s)
                                                  (PPOW (natural n)) (PolyRing r).carrier

   Factor and Root of Lifting Polynomial:
   poly_mod_lift_root_factor  |- !r. Field r ==> !z. ipoly z ==>
                                 !p x. poly p /\ p <> |0| /\ poly x /\ deg x < deg z /\ rootz (lift p) x ==>
                                 ?q. polyz q /\ (degz q = PRE (deg p)) /\ (lift p = q |*| factorz x)
   poly_irreducible_has_field_with_root |- !r. Field r ==> !z. ipoly z /\ 1 < deg z ==>
                                           ?s. Field s /\ (s = PolyModRing r z) /\ rootz (lift z) X

   Isomorphism between Field elements and Constant Polynomials:
   poly_mod_const_def           |- !r z. PolyModConst r z =
                                  <|carrier := IMAGE (\e. up e) R;
                                        sum := <|carrier := IMAGE (\e. up e) R; op := $+z; id := #0z|>;
                                       prod := <|carrier := IMAGE (\e. up e) R; op := $*z; id := #1z|>
                                   |>
   poly_mod_const_property      |- !r z. (!p. p IN RCz <=> ?c. c IN R /\ (p = up c)) /\
                                         ((PolyModConst r z).sum.op = $+z) /\
                                         ((PolyModConst r z).prod.op = $*z) /\
                                         ((PolyModConst r z).sum.carrier = RCz) /\
                                         ((PolyModConst r z).prod.carrier = RCz) /\
                                         ((PolyModConst r z).sum.id = #0z) /\
                                         ((PolyModConst r z).prod.id = #1z)
   poly_mod_const_element       |- !r z p. p IN RCz <=> ?c. c IN R /\ (p = up c)
   poly_mod_const_carriers      |- !r z. ((PolyModConst r z).sum.carrier = RCz) /\
                                         ((PolyModConst r z).prod.carrier = RCz)
   poly_mod_const_ids           |- !r z. ((PolyModConst r z).sum.id = #0z) /\
                                         ((PolyModConst r z).prod.id = #1z)
   poly_mod_const_element_const |- !r z x. x IN RCz ==> poly x /\ (deg x = 0)
   up_bij                       |- !r z. BIJ up R RCz

   Constant Polynomials Zero and One:
   poly_mod_const_one_eq_zero   |- !r z. Ring r /\ 0 < deg z ==> ((#1 = #0) <=> (#1z = #0z))
   poly_mod_const_zero          |- !r z. #0z = up #0
   poly_mod_const_one           |- !r z. Ring r /\ 0 < deg z ==> (#1z = up #1)
   poly_mod_const_zero_element  |- !r z. Ring r ==> #0z IN RCz
   poly_mod_const_one_element   |- !r z. Ring r ==> #1z IN RCz

   Constant Polynomials Addition:
   poly_mod_const_add           |- !r p q z. (PolyModConst r z).sum.op p q = p +z q
   poly_mod_const_add_element   |- !r z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x +z y IN RCz
   poly_mod_const_add_comm      |- !r z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x +z y = y +z x)
   poly_mod_const_add_assoc     |- !r z. Ring r /\ pmonic z ==>
                                   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x +z y +z t = x +z (y +z t))
   poly_mod_const_add_lzero     |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (#0z +z x = x)
   poly_mod_const_add_rzero     |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z #0z = x)
   poly_mod_const_neg_element   |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> $-z x IN RCz
   poly_mod_const_add_lneg      |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> ($-z x +z x = #0z)
   poly_mod_const_add_rneg      |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z $-z x = #0z)

   Constant Polynomials Multiplication:
   poly_mod_const_mult          |- !r p q z. (PolyModConst r z).prod.op p q = p *z q
   poly_mod_const_mult_element  |- !r z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x *z y IN RCz
   poly_mod_const_mult_comm     |- !r z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x *z y = y *z x)
   poly_mod_const_mult_assoc    |- !r z. Ring r /\ pmonic z ==>
                                   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z y *z t = x *z (y *z t))
   poly_mod_const_mult_lone     |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (#1z *z x = x)
   poly_mod_const_mult_rone     |- !r z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x *z #1z = x)
   poly_mod_const_inv_element   |- !r. Field r ==> !z. ipoly z ==>
                                   !x. x IN RCz /\ x <> #0z ==> |/z x IN RCz /\ |/z x <> #0z
   poly_mod_const_mult_linv     |- !r. Field r ==> !z. ipoly z ==>
                                   !x. x IN RCz /\ x <> #0z ==> ( |/z x *z x = #1z)
   poly_mod_const_mult_rinv     |- !r. Field r ==> !z. ipoly z ==>
                                   !x. x IN RCz /\ x <> #0z ==> (x *z |/z x = #1z)

   Constant Polynomials Distribution Law:
   poly_mod_const_mult_ladd     |- !r z. Ring r /\ pmonic z ==>
                                   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> ((x +z y) *z t = x *z t +z y *z t)
   poly_mod_const_mult_radd     |- !r z. Ring r /\ pmonic z ==>
                                   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z (y +z t) = x *z y +z x *z t)

   Constant Polynomials as Field:
   poly_mod_const_sum_abelian_group   |- !r z. Ring r /\ pmonic z ==> AbelianGroup (PolyModConst r z).sum
   poly_mod_const_prod_abelian_monoid |- !r z. Ring r /\ pmonic z ==> AbelianMonoid (PolyModConst r z).prod
   poly_mod_const_ring                |- !r z. Ring r /\ pmonic z ==> Ring (PolyModConst r z)
   poly_mod_const_field               |- !r z. Field r /\ ipoly z ==> Field (PolyModConst r z)
   poly_mod_const_finite_field        |- !r z. FiniteField r /\ ipoly z ==> FiniteField (PolyModConst r z)

   Constant Polynomials as Subfield:
   poly_mod_const_subring_poly_mod      |- !r z. Ring r /\ pmonic z ==>
                                               subring (PolyModConst r z) (PolyModRing r z)
   poly_mod_const_subfield_poly_mod     |- !r z. Field r/\ ipoly z ==>
                                               subfield (PolyModConst r z) (PolyModRing r z)
   poly_mod_const_subfield_poly_mod_alt |- !r z. Field r /\ ipoly z ==>
                                               (PolyModConst r z) <<= (PolyModRing r z)

   Constant Polynomials as isomorphic Field:
   poly_mod_const_homo_ring      |- !r z. Ring r /\ pmonic z ==> RingHomo up r (PolyModConst r z)
   poly_mod_const_iso_ring       |- !r z. Ring r /\ pmonic z ==> RingIso up r (PolyModConst r z)
   poly_mod_const_homo_field     |- !r z. Field r /\ pmonic z ==> FieldHomo up r (PolyModConst r z)
   poly_mod_const_homo_field_alt |- !r z. Field r /\ ipoly z ==> FieldHomo (\e. up e) r (PolyModConst r z)
   poly_mod_const_iso_field      |- !r z. Field r /\ pmonic z ==> FieldIso up r (PolyModConst r z)
   poly_mod_const_iso_field_alt  |- !r z. Field r /\ ipoly z ==> FieldIso (\e. up e) r (PolyModConst r z)

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo forms a Finite Field                                    *)
(* ------------------------------------------------------------------------- *)

(* Overloads for polynomials of (PolyModRing r z) *)
val _ = overload_on("RRz", ``(PolyRing (PolyModRing r z)).carrier``);
val _ = overload_on("zeropz", ``zero_poly (PolyModRing r z)``);
val _ = overload_on("weakz", ``Weak (PolyModRing r z)``);
val _ = overload_on("polyz", ``Poly (PolyModRing r z)``);
val _ = overload_on("chopz", ``poly_chop (PolyModRing r z)``);
val _ = overload_on("negz", ``weak_neg (PolyModRing r z)``);
val _ = overload_on("-z", ``poly_neg (PolyModRing r z)``);
val _ = overload_on("||z", ``weak_add (PolyModRing r z)``);
val _ = overload_on("+z", ``poly_add (PolyModRing r z)``);
val _ = overload_on("-z", ``poly_sub (PolyModRing r z)``);
val _ = overload_on("oz", ``weak_cmult (PolyModRing r z)``);
val _ = overload_on("*z", ``poly_cmult (PolyModRing r z)``);
val _ = overload_on("oz", ``weak_mult (PolyModRing r z)``);
val _ = overload_on("*z", ``poly_mult (PolyModRing r z)``);
val _ = overload_on(">>z", ``poly_shift (PolyModRing r z)``);
val _ = overload_on("##z", ``poly_num (PolyModRing r z)``);
val _ = overload_on("**z", ``poly_exp (PolyModRing r z)``);
val _ = overload_on("degz", ``poly_deg (PolyModRing r z)``);
val _ = overload_on("leadz", ``poly_lead (PolyModRing r z)``);
val _ = overload_on("'z", ``poly_coeff (PolyModRing r z)``);
(* val _ = overload_on("pz", ``MAP (f:'a -> 'b) (p:'a poly)``); *)
(* val _ = overload_on("qz", ``MAP (f:'a -> 'b) (q:'a poly)``); *)
val _ = overload_on("|0|z", ``poly_zero (PolyModRing r z)``);
val _ = overload_on("|1|z", ``poly_one (PolyModRing r z)``);
val _ = overload_on("|c|z", ``poly_num (PolyModRing r z) (c:num)``);
val _ = overload_on("|X|", ``>>z |1|z 1``); (* before infix, will be |1|z >>z 1 after infix *)
val _ = overload_on("unityz", ``Unity (PolyModRing r z)``);
val _ = overload_on("masterz", ``Master (PolyModRing r z)``);
val _ = overload_on("monicz", ``Monic (PolyModRing r z)``);
val _ = overload_on("unitz", ``Unit (PolyModRing r z)``);
val _ = overload_on("uleadz", ``Ulead (PolyModRing r z)``);
val _ = overload_on("pmonicz", ``Pmonic (PolyModRing r z)``);
val _ = overload_on("upolyz", ``\p. p IN (Invertibles (PolyRing (PolyModRing r z)).prod).carrier``);
val _ = overload_on("ipolyz", ``IPoly (PolyModRing r z)``);
val _ = overload_on("evalz", ``poly_eval (PolyModRing r z)``);
val _ = overload_on("rootz", ``poly_root (PolyModRing r z)``);
val _ = overload_on("rootsz", ``poly_roots (PolyModRing r z)``);
val _ = overload_on("factorz", ``poly_factor (PolyModRing r z)``);
val _ = overload_on("forderz", ``order ((PolyModRing r z).prod excluding |0|)``);

(* make infix operators *)
val _ = set_fixity "||z" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity "oz" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity ">>z" (Infixr 700); (* same as EXP in arithmeticScript.sml, infix right *)
val _ = set_fixity "'z" (Infixl 2000); (* same as ' for function application *)

(* other polynomial overloads *)
val _ = overload_on("pdividesz", ``poly_divides (PolyModRing r z)``);
(* make infix operators *)
val _ = set_fixity "pdividesz" (Infix(NONASSOC, 450)); (* same as relation *)

(*
We have:
- polyDivisionTheory.poly_mod_ring_ring;
> val it = |- !r. Ring r ==> !z. ulead z ==> Ring (PolyModRing r z) : thm
- polyDivisionTheory.poly_mod_ring_iso_quotient_ring;
> val it = |- !r. Ring r ==> !z. ulead z ==>
           RingIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) z).carrier)
                   (PolyModRing r z)
                   (PolyRing r / principal_ideal (PolyRing r) z) : thm
- polyFieldModuloTheory.poly_irreducible_quotient_field;
> val it = |- !r. Field r ==> !p. ipoly p ==> Field (PolyRing r / principal_ideal (PolyRing r) p) : thm
- polyDivisionTheory.poly_mod_ring_card;
> val it = |- !r. FiniteRing r ==> !z. poly z /\ 0 < deg z ==> (CARD (PolyModRing r z).carrier = CARD R ** deg z) : thm

We still need:
Field (PolyModRing r z)
FiniteField (PolyModRing r z)
*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring F[x] is a Euclidean Ring                                  *)
(* ------------------------------------------------------------------------- *)

(* Define norm for Polynomial Ring *)
val _ = overload_on ("norm", ``\p. if p = |0| then 0 else SUC (deg p)``);

(* Theorem: F[x] ring is a Euclidean ring, with norm f p = if (p = |0|) then 0 else SUC(deg p) *)
(* Proof:
   By EuclideanRing_def, this is to show:
   (1) Field r ==> Ring (PolyRing r)
       True by poly_ring_ring, field_is_ring.
   (2) (norm p = 0) <=> (p = |0|)
       which is trivial since only p = |0| is compared.
   (3) poly x /\ poly p /\ p <> |0| ==>
       ?q t. poly q /\ poly t /\ (x = q * p + t) /\ norm t < SUC (deg p)
       If (deg p = 0),
       Since p <> |0|,
       ?h. h IN R /\ h <> #0 /\ (p = [h])    by poly_deg_eq_zero
       i.e. h IN R+                          by field_nonzero_eq
       |/h IN R for Field r,                 by field_inv_element
       Take q = |/h * x, t = |0|
       Then SUC (deg p) = SUC 0 = 1 > 0, and
         q * p + t
       = ( |/h * x) * [h] + #0
       = [h] * ( |/h * x) + #0            by poly_mult_comm
       = [h] * ( |/h * x)                 by poly_add_rzero
       = h * ( |/h * x)                   by poly_mult_lconst
       = h * |/h * x                      by poly_cmult_cmult
       = #1 * x                           by field_mult_rinv
       = x                                by poly_cmult_lone
       If (deg p > 0), by poly_field_division_eqn
       ?q t. poly q /\ poly t /\ (x = q * p + t) /\ deg t < deg p
       Take q = q, t = t,
       Then SUC (deg p) > SUC (deg t)     by LESS_MONO_EQ
*)
val poly_ring_euclid_ring = store_thm(
  "poly_ring_euclid_ring",
  ``!r:'a field. Field r ==> EuclideanRing (PolyRing r) norm``,
  rw_tac std_ss[EuclideanRing_def] >-
  rw[poly_ring_ring] >-
  rw[] >>
  `!z. z IN (PolyRing r).carrier <=> poly z` by rw[poly_ring_property] >>
  `|0| = []` by rw[] >>
  Cases_on `deg p = 0` >| [
    `?h. h IN R /\ h <> #0 /\ (p = [h])` by metis_tac[poly_deg_eq_zero] >>
    `h IN R+` by rw[field_nonzero_eq] >>
    `|/h IN R /\ (h * |/h = #1)` by rw[] >>
    `Ring r` by rw[] >>
    `poly ( |/h * x)` by metis_tac[poly_cmult_poly] >>
    qexists_tac `|/h * x` >>
    qexists_tac `|0|` >>
    rw[] >>
    metis_tac[poly_mult_comm, poly_mult_lconst, poly_cmult_cmult, poly_cmult_lone],
    `0 < deg p` by decide_tac >>
    `?q t. poly q /\ poly t /\ (x = q * p + t) /\ deg t < deg p` by metis_tac[poly_field_division_eqn] >>
    `Ring r` by rw[] >>
    qexists_tac `q` >>
    qexists_tac `t` >>
    rw[]
  ]);

(* The use of norm is suitable from a polynomial structural viewpoint.
   The following simple version depends on polynomial representation.
*)

(* Theorem: norm p = LENGTH p *)
(* Proof:
   Note |0| = []             by poly_zero
   If p = [],
      Then LENGTH p = 0      by LENGTH_EQ_0
       and norm [] = 0       by notation
      Hence true.
   If p <> [],
      Then LENGTH p <> 0     by LENGTH_EQ_0
      norm p
    = SUC (deg p)            by notation
    = SUC (PRE (LENGTH p))   by poly_deg_def
    = LENGTH p               by arithmetic, LENGTH p <> 0
*)
val poly_norm_eq_length = store_thm(
  "poly_norm_eq_length",
  ``!p. norm p = LENGTH p``,
  metis_tac[poly_deg_def, LENGTH_EQ_0, SUC_PRE, NOT_ZERO_LT_ZERO, poly_zero]);

(* Theorem: Field r ==> EuclideanRing (PolyRing r) LENGTH *)
(* Proof:
     Field r
   ==> EuclideanRing (PolyRing r) norm    by poly_ring_euclid_ring
   ==> EuclideanRing (PolyRing r) LENGTH  by poly_norm_eq_length, FUN_EQ_THM
*)
val poly_ring_euclid_ring_alt = store_thm(
  "poly_ring_euclid_ring_alt",
  ``!r:'a field. Field r ==> EuclideanRing (PolyRing r) LENGTH``,
  rpt strip_tac >>
  `EuclideanRing (PolyRing r) norm` by rw[poly_ring_euclid_ring] >>
  `norm = LENGTH` by rw[poly_norm_eq_length, FUN_EQ_THM] >>
  prove_tac[]);

(* Theorem: F[x] ring is a Principal Ideal ring *)
(* Proof: by poly_ring_euclid_ring, euclid_ring_principal_ideal_ring *)
val poly_ring_principal_ideal_ring = store_thm(
  "poly_ring_principal_ideal_ring",
  ``!r:'a field. Field r ==> PrincipalIdealRing (PolyRing r)``,
  metis_tac[poly_ring_euclid_ring, euclid_ring_principal_ideal_ring]);

(* Theorem: In F[x] ring, an irreducible polynomial generates a maximal ideal. *)
(* Proof:
   Since Field r ==> PrincipalIdealRing (PolyRing r)    by poly_ring_principal_ideal_ring
   This follows from principal_ideal_ring_ideal_maximal.
*)
val poly_irreducible_ideal_maximal = store_thm(
  "poly_irreducible_ideal_maximal",
  ``!r:'a field. Field r ==> !p. ipoly p ==> ideal_maximal (PolyRing r) (principal_ideal (PolyRing r) p)``,
  rw[poly_ring_principal_ideal_ring, principal_ideal_ring_ideal_maximal]);

(* Theorem: Ring r /\ ipoly p ==> |1| NOTIN (principal_ideal (PolyRing r) p).carrier *)
(* Proof:
   From definitions, this is to show:
   |1| = p * z /\ z IN (PolyRing r).carrier /\
   p IN ring_nonzero (PolyRing r) /\ p NOTIN (Invertibles (PolyRing r).prod).carrier ==> F
       p IN ring_nonzero (PolyRing r)
   ==> p IN (PolyRing r).carrier          by ring_nonzero_element
   Hence poly p /\ poly z                 by poly_ring_element
   and   z * p = |1|                      by poly_mult_comm
   Hence p IN (Invertibles (PolyRing r).prod).carrier   by Invertibles_def, monoid_invertibles_def
   a contradiction.
*)
val poly_irreducible_ideal_property = store_thm(
  "poly_irreducible_ideal_property",
  ``!r:'a ring. Ring r ==> !p. ipoly p ==> |1| NOTIN (principal_ideal (PolyRing r) p).carrier``,
  rw_tac std_ss[irreducible_def, principal_ideal_def, coset_def, IN_IMAGE] >>
  spose_not_then strip_assume_tac >>
  `p IN (PolyRing r).carrier` by rw[ring_nonzero_element] >>
  `poly p /\ poly z` by rw[GSYM poly_ring_element] >>
  `z * p = |1|` by rw[poly_mult_comm] >>
  `!x. x IN (Invertibles (PolyRing r).prod).carrier <=>
        x IN (PolyRing r).prod.carrier /\
        ?y. y IN (PolyRing r).prod.carrier /\
        (x * y = |1|) /\ (y * x = |1|)` by rw[Invertibles_def, monoid_invertibles_def] >>
  metis_tac[poly_ring_property]);

(* Theorem: In F[x] ring, an irreducible polynomial gives a quotient field. *)
(* Proof:
   Ring (PolyRing r)    by poly_ring_ring
   ideal_maximal (PolyRing r) (principal_ideal (PolyRing r) p)   by poly_irreducible_ideal_maximal
   (principal_ideal (PolyRing r) p) << (PolyRing r)              by ideal_maximal_def
   Since |1| not in (principal_ideal (PolyRing r) p).carrier     by poly_irreducible_ideal_property
   (principal_ideal (PolyRing r) p) <> (PolyRing r)              by ideal_with_one
   Hence Field (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) p))  by quotient_field_by_maximal_ideal.
*)
val poly_irreducible_quotient_field = store_thm(
  "poly_irreducible_quotient_field",
  ``!r:'a field. Field r ==> !p. ipoly p ==>
   Field (quotient_ring (PolyRing r) (principal_ideal (PolyRing r) p))``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw[poly_ring_ring] >>
  `ideal_maximal (PolyRing r) (principal_ideal (PolyRing r) p)` by rw[poly_irreducible_ideal_maximal] >>
  `(principal_ideal (PolyRing r) p) << (PolyRing r)` by metis_tac[ideal_maximal_def] >>
  `|1| NOTIN (principal_ideal (PolyRing r) p).carrier` by rw[poly_irreducible_ideal_property] >>
  `(principal_ideal (PolyRing r) p) <> (PolyRing r)` by metis_tac[ideal_with_one] >>
  rw[quotient_field_by_maximal_ideal]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Irreducible Polynomials are Primes                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload ring_prime (PolyRing r) *)
val _ = overload_on("pprime", ``ring_prime (PolyRing r)``);

(*
- ring_divides_def |> ISPEC ``(PolyRing (r:'a ring))``;
> val it = |- !q p. ring_divides (PolyRing r) q p <=> ?s. s IN (PolyRing r).carrier /\ (p = s * q) : thm
*)

(* Theorem: ring_divides (PolyRing r) z p <=> p % z = |0| *)
(* Proof:
       ring_divides (PolyRing r) z p
   <=> ?q. q IN (PolyRing r).carrier /\ p = q * z     by ring_divides_def
   <=> poly q /\ p = q * z                            by poly_ring_property
   <=> p % z = |0|                                    by poly_mod_eq_zero
*)
val poly_mod_zero_eq_divides = store_thm(
  "poly_mod_zero_eq_divides",
  ``!r:'a ring z p. Ring r /\ ulead z /\ poly p ==>
            (ring_divides (PolyRing r) z p <=> (p % z = |0|))``,
  rw_tac std_ss[ring_divides_def, poly_mod_eq_zero, poly_ring_property]);

(* Theorem: ring_divides (PolyRing r) z p <=> p % z = |0| *)
(* Proof:
       ring_divides (PolyRing r) z p
   <=> ?q. q IN (PolyRing r).carrier /\ p = q * z     by ring_divides_def
   <=> poly q /\ p = q * z                            by poly_ring_property
   <=> p % z = |0|                                    by poly_field_mod_eq_zero
   Another proof:
       Note ulead z    by poly_field_poly_ulead
       Hence true      by poly_mod_zero_eq_divides
*)
val poly_field_mod_zero_eq_divides = store_thm(
  "poly_field_mod_zero_eq_divides",
  ``!r:'a field z p. Field r /\ poly z /\ z <> |0| /\ poly p ==>
                (ring_divides (PolyRing r) z p <=> (p % z = |0|))``,
  rw_tac std_ss[poly_mod_zero_eq_divides, poly_field_poly_ulead, field_is_ring]);

(* Theorem: pprime z <=> !x y. poly x /\ poly y /\ (x * y) % z = |0| ==> (x % z = |0|) \/ (y % z = |0| *)
(* Proof: by ring_prime_def and poly_mod_zero_eq_divides. *)
val poly_mod_prime_product = store_thm(
  "poly_mod_prime_product",
  ``!r:'a ring z. Ring r /\ ulead z ==>
     (pprime z <=> (!x y. poly x /\ poly y /\ ((x * y) % z = |0|) ==> (x % z = |0|) \/ (y % z = |0|)))``,
  metis_tac[ring_prime_def, poly_ring_element, poly_mod_zero_eq_divides, poly_mult_poly]);

(*
- ring_prime_def |> ISPEC ``(PolyRing (r:'a ring))``;
> val it = |- !p. pprime p <=>
           !a b. a IN (PolyRing r).carrier /\ b IN (PolyRing r).carrier /\ ring_divides (PolyRing r) p (a * b) ==>
                 ring_divides (PolyRing r) p a \/ ring_divides (PolyRing r) p b : thm
*)

(* Theorem: pprime z <=> !x y. poly x /\ poly y /\ (x * y) % z = |0| ==> (x % z = |0|) \/ (y % z = |0| *)
(* Proof:
   By ring_prime_def and poly_field_mod_zero_eq_divides.
   Another proof:
       Note ulead z    by poly_field_poly_ulead
       Hence true      by poly_mod_prime_product
*)
val poly_field_mod_prime_product = store_thm(
  "poly_field_mod_prime_product",
  ``!r:'a field z. Field r /\ poly z /\ z <> |0| ==>
     (pprime z <=> (!x y. poly x /\ poly y /\ ((x * y) % z = |0|) ==> (x % z = |0|) \/ (y % z = |0|)))``,
  rw_tac std_ss[poly_mod_prime_product, poly_field_poly_ulead, field_is_ring]);

(* Theorem: (pprime z <=> !x y. poly x /\ poly y /\ z pdivides (x * y) ==> z pdivides x \/ z pdivides y) *)
(* Proof: by poly_mod_prime_product, poly_divides_alt. *)
val poly_prime_divides = store_thm(
  "poly_prime_divides",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   (pprime z <=> !x y. poly x /\ poly y /\ z pdivides (x * y) ==> z pdivides x \/ z pdivides y)``,
  metis_tac[poly_mod_prime_product, poly_divides_alt, poly_mult_poly]);

(* Theorem: poly t /\ pprime t /\ t pdivides (p * q) ==> (t pdivides p) \/ (t pdivides q) *)
(* Proof: by ring_prime_def, poly_divides_is_ring_divides. *)
val poly_prime_divides_product = store_thm(
  "poly_prime_divides_product",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ pprime t /\ t pdivides (p * q) ==> (t pdivides p) \/ (t pdivides q)``,
  rw[ring_prime_def, poly_ring_element] >>
  metis_tac[poly_divides_is_ring_divides, poly_mult_poly]);

(* Theorem: monic t /\ pprime t /\ ~(t pdivides q) ==>
            !n. t ** n pdivides (p * q) ==> t ** n pdivides p *)
(* Proof:
   By induction on n.
   Base case: t ** 0 pdivides p * q /\ ~(t pdivides q) ==> t ** 0 pdivides p
     Since t ** 0 = |1|                 by poly_exp_0
       and !p. |1| pdivides p           by poly_one_divides_all
       hence true.
   Step case: t ** n pdivides p * q /\ ~(t pdivides q) ==> t ** n pdivides p ==>
              t ** SUC n pdivides p * q /\ ~(t pdivides q) ==> t ** SUC n pdivides p
     To apply poly_monic_mult_lcancel later, need 0 < deg (t ** n)
     Since monic (t ** n)               by poly_monic_exp_monic
     If deg (t ** n) = 0,
        then t ** n = |1|               by poly_monic_deg_0
        which reduces to show:
        t pdivides p * q /\ ~(t pdivides q) ==> t pdivides p
                                   true by poly_prime_divides_product
     If deg (t ** n) <> 0, 0 < deg (t ** n).
     Since t ** n pdivides t ** SUC n
           t ** n pdivides (p * q)      by poly_divides_transitive
     Thus  t ** n pdivides p            by induction hypothesis
     ?s. poly s /\ p = s * (t ** n)     by poly_divides_def
     and p * q = q * s * (t ** n)       by poly_mult_comm, poly_mult_assoc
     But t ** SUC n pdivides (p * q)
     ?a. poly a /\ (a * t ** SUC n = q * s * t ** n)  by poly_divides_def
     so   a * t = q * s                 by poly_monic_mult_rcancel
     or   t pdivides (q * s)
     By pprime t, t pdivides s          by poly_prime_divides_product, ~(t pdivides q)
     So ?b. poly b /\ s = b * t         by poly_divides_def
     Hence p = (b * t) * t ** n
             = b * (t ** SUC n)         by poly_mult_assoc, poly_exp_suc
       or t ** SUC n pdivides p         by poly_divides_def
*)
val poly_monic_prime_power_divides_product = store_thm(
  "poly_monic_prime_power_divides_product",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. poly p /\ poly q ==>
   !t. monic t /\ pprime t /\ ~(t pdivides q) ==>
   !n. t ** n pdivides (p * q) ==> t ** n pdivides p``,
  rpt strip_tac >>
  `poly t` by rw[] >>
  Induct_on `n` >-
  rw[poly_one_divides_all] >>
  rw[poly_exp_suc] >>
  Cases_on `deg (t ** n) = 0` >| [
    `t ** n = |1|` by rw[GSYM poly_monic_deg_0] >>
    metis_tac[poly_prime_divides_product, poly_mult_lone],
    `0 < deg (t ** n)` by decide_tac >>
    `poly (t ** n) /\ monic (t ** n)` by rw[] >>
    `t ** n pdivides p` by metis_tac[poly_mult_divides, poly_mult_poly] >>
    `?s. poly s /\ (p = s * (t ** n))` by rw[GSYM poly_divides_def] >>
    `p * q = (t ** n * s) * q` by rw[poly_mult_comm] >>
    `_ = t ** n * (s * q)` by rw[poly_mult_assoc] >>
    `?a. poly a /\ (p * q = a * (t ** n * t))` by rw[GSYM poly_divides_def] >>
    `_ = (t ** n * t) * a` by rw[poly_mult_comm] >>
    `_ = t ** n * (a * t)` by rw[poly_mult_assoc, poly_mult_comm] >>
    `poly (s * q) /\ poly (a * t)` by rw[] >>
    `s * q = a * t` by metis_tac[poly_monic_mult_lcancel] >>
    `t pdivides s * q` by metis_tac[poly_divides_def] >>
    `t pdivides s` by metis_tac[poly_prime_divides_product] >>
    `?b. poly b /\ (s = b * t)` by rw[GSYM poly_divides_def] >>
    `p = b * (t * t ** n)` by rw[poly_mult_assoc] >>
    `_ = b * (t ** n * t)` by rw[poly_mult_comm] >>
    metis_tac[poly_divides_def]
  ]);

(* Theorem: Field r ==> !p. ipoly p ==> pprime p *)
(* Proof:
   Since  Field ==> PrincipalIdealRing (PolyRing r)    by poly_ring_principal_ideal_ring
   Hence  !p. ipoly p ==> pprime p                     by principal_ideal_ring_irreducible_is_prime
*)
val poly_irreducible_prime = store_thm(
  "poly_irreducible_prime",
  ``!r:'a field. Field r ==> !p. ipoly p ==> pprime p``,
  rw[poly_ring_principal_ideal_ring, principal_ideal_ring_irreducible_is_prime]);

(* Theorem: pprime (X + |c|) *)
(* Proof: by poly_X_add_c_irreducible, poly_irreducible_prime. *)
val poly_X_add_c_pprime = store_thm(
  "poly_X_add_c_pprime",
  ``!r:'a field. Field r ==> !c:num. pprime (X + |c|)``,
  rw[poly_X_add_c_irreducible, poly_irreducible_prime]);

(* Theorem: pprime (X - |c|) *)
(* Proof: by poly_X_sub_c_irreducible, poly_irreducible_prime. *)
val poly_X_sub_c_pprime = store_thm(
  "poly_X_sub_c_pprime",
  ``!r:'a field. Field r ==> !c:num. pprime (X - |c|)``,
  rw[poly_X_sub_c_irreducible, poly_irreducible_prime]);

(* Theorem: (X + |c|) divides p * q ==> (X + |c|) divides p or (X + |c|) divides q *)
(* Proof:
   Since pmonic (X + |c|)     by poly_pmonic_X_add_c
     and pprime (X + |c|)     by poly_X_add_c_pprime
    This follows              by poly_mod_prime_product.
*)
val poly_X_add_c_divides_product = store_thm(
  "poly_X_add_c_divides_product",
  ``!r:'a field. Field r ==> !(c:num) p q. poly p /\ poly q /\ ((p * q) % (X + |c|) = |0|) ==>
           ((p % (X + |c|) = |0|) \/ ((q % (X + |c|) = |0|)))``,
  rpt strip_tac >>
  `pmonic (X + |c|)` by rw[poly_pmonic_X_add_c] >>
  `pprime (X + |c|)` by rw[poly_X_add_c_pprime] >>
  metis_tac[poly_mod_prime_product, field_is_ring]);

(* Theorem: (X - |c|) divides p * q ==> (X - |c|) divides p or (X - |c|) divides q *)
(* Proof:
   Since pmonic (X - |c|)     by poly_pmonic_X_sub_c
     and pprime (X - |c|)     by poly_X_sub_c_pprime
    This follows              by poly_mod_prime_product.
*)
val poly_X_sub_c_divides_product = store_thm(
  "poly_X_sub_c_divides_product",
  ``!r:'a field. Field r ==> !(c:num) p q. poly p /\ poly q /\ ((p * q) % (X - |c|) = |0|) ==>
           ((p % (X - |c|) = |0|) \/ ((q % (X - |c|) = |0|)))``,
  rpt strip_tac >>
  `pmonic (X - |c|)` by rw[poly_pmonic_X_sub_c] >>
  `pprime (X - |c|)` by rw[poly_X_sub_c_pprime] >>
  metis_tac[poly_mod_prime_product, field_is_ring]);

(* Theorem: Field r /\ poly x /\ poly y /\ ipoly z ==> (x * y) % z = |0| <=> x % z = |0| \/ y % z = |0|  *)
(* Proof:
   Note ipoly z ==> pprime z      by poly_irreducible_prime
    and ipoly z ==> pmonic z      by poly_irreducible_pmonic
   If part: (x * y) % z = |0| ==> x % z = |0| \/ y % z = |0|
      True by poly_mod_prime_product.
   Only-if part: x % z = |0| \/ y % z = |0| ==> (x * y) % z = |0|
      If x % z = |0|,
        (x * y) % z
      = (x % z * y % z) % z       by poly_mod_mult
      = |0| % z                   by poly_mult_lzero, poly_mod_poly
      = |0|                       by poly_zero_mod
      Similarly for y % z = |0|   by poly_mult_rzero.
*)
val poly_mod_mult_eq_zero = store_thm(
  "poly_mod_mult_eq_zero",
  ``!r:'a field. Field r ==> !x y z. poly x /\ poly y /\ ipoly z ==>
      (((x * y) % z = |0|) <=> (x % z = |0|) \/ (y % z = |0|))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pprime z` by rw[poly_irreducible_prime] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    metis_tac[poly_mod_prime_product],
    rw_tac std_ss[poly_mod_mult, poly_mult_lzero, poly_mod_poly, poly_zero_mod],
    rw_tac std_ss[poly_mod_mult, poly_mult_rzero, poly_mod_poly, poly_zero_mod]
  ]);

(*
- ring_divides_le |> ISPEC ``PolyRing (r:'a ring)``;
> val it = |- !f. EuclideanRing (PolyRing r) f /\ ring_ordering (PolyRing r) f ==>
              !p q. p IN (PolyRing r).carrier /\ q IN (PolyRing r).carrier /\
               p <> |0| /\ ring_divides (PolyRing r) q p ==> f q <= f p : thm
*)

(* Theorem: poly p /\ poly q /\ p <> |0| /\ q <> |0| /\ (p % q = |0|) ==> deg q <= deg p *)
(* Proof:
   Let f = norm
   Field r ==> EuclideanRing (PolyRing r) f   by poly_ring_euclid_ring
   Claim: ring_ordering (PolyRing r) f        by proving on-the-fly
   which is to show: (if p' = [] then 0 else SUC (deg p'))
                   <= if p' * b = [] then 0 else SUC (deg (p' * b))
   If p' = [], p' * b = []                    by poly_mult_lzero, LHS = 0 = RHS.
   If p' <> [], p' * b <> []                  by poly_mult_eq_zero, since b <> []
   to show: SUC (deg p')) <= SUC (deg (p' * b))
   or to show:     deg p' <= deg (p' * b)
   which is true by poly_deg_mult_nonzero: deg (p' * b) = deg p' + deg b
   Also, p % q = |0|
   means ring_divides (PolyRing r) q p        by poly_field_mod_zero_eq_divides
   hence f q <= f p                           by ring_divides_le
   Now   0 < deg q means q <> |0|             by poly_deg_zero
   Hence f q <= f p means SUC (deg q) <= SUC (deg p), or deg q <= deg p.
*)
val poly_mod_zero_deg_le = store_thm(
  "poly_mod_zero_deg_le",
  ``!r:'a field. Field r ==>
   !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\ (p % q = |0|) ==> deg q <= deg p``,
  rpt strip_tac >>
  qabbrev_tac `f = norm` >>
  `EuclideanRing (PolyRing r) f` by rw[poly_ring_euclid_ring, Abbr`f`] >>
  `ring_ordering (PolyRing r) f` by
  (rw[ring_ordering_def, poly_ring_element, Abbr`f`] >>
  Cases_on `p' = []` >-
  rw[] >>
  `p' * b <> []` by metis_tac[poly_mult_eq_zero, poly_zero] >>
  rw[] >>
  `deg (p' * b) = deg p' + deg b` by rw[poly_deg_mult_nonzero] >>
  decide_tac
  ) >>
  `ring_divides (PolyRing r) q p` by rw[poly_field_mod_zero_eq_divides] >>
  `f q <= f p` by metis_tac[ring_divides_le, poly_ring_element] >>
  `SUC (deg q) <= SUC (deg p)` by metis_tac[] >>
  decide_tac);

(* Theorem: pmonic z ==> deg x < deg z /\ x % z = |0| ==> x = |0| *)
(* Proof:
       x % z = |0|
   ==> ?q. poly q /\ x = q * z     by poly_mod_eq_zero
   If q = |0|, then x = |0|        by poly_mult_lzero
   If q <> |0|,
   Since 0 < deg z, z <> |0|       by poly_deg_zero
   and deg x = deg q + deg z       by poly_deg_mult_nonzero
   which contradicts deg x < deg z by given
*)
val poly_field_mod_deg_less_eq_zero = store_thm(
  "poly_field_mod_deg_less_eq_zero",
  ``!r:'a field z. Field r /\ pmonic z ==>
   !x. poly x /\ deg x < deg z /\ (x % z = |0|) ==> (x = |0|)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `?q. poly q /\ (x = q * z)` by rw[GSYM poly_mod_eq_zero] >>
  Cases_on `q = |0|` >-
  rw[] >>
  `deg z <> 0` by decide_tac >>
  `z <> |0|` by metis_tac[poly_deg_zero] >>
  `deg x = deg q + deg z` by rw[poly_deg_mult_nonzero] >>
  `~(deg x < deg z)` by decide_tac);

(* ------------------------------------------------------------------------- *)
(* More Properties of Irreducible Polynomials                                *)
(* ------------------------------------------------------------------------- *)

(* These irreducible polynomial theorems depends on poly_prime_divides *)

(* Theorem: monic z /\ ipoly z ==>
            !p n. poly p /\ z pdivides (p ** n) ==> z pdivides p *)
(* Proof:
   By induction on n.
   Base case: z pdivides p ** 0 ==> z pdivides p
      Note z pdivides |1|     by poly_exp_0
        so z = |1|            by poly_monic_divides_one
       and |1| pdivides p     by poly_one_divides_all
   Step case: z pdivides p ** n ==> z pdivides p ==>
              z pdivides p ** SUC n ==> z pdivides p
      If n = 0,
          then SUC 0 = 1       by ONE
           and p ** 1 = p      by poly_exp_1
         Hence z pdivides p    by given: z pdivides p ** 1
      If n <> 0, 0 < n.
          then p ** SUC n = p * p ** n    by poly_exp_SUC
           Now pmonic z                   by poly_monic_irreducible_property
           and pprime z                   by poly_irreducible_prime
         Hence z pdivides p or
               z pdivides p ** n          by poly_prime_divides
         First case is trivial.
         Second case gives z pdivides p   by induction hypothesis
*)
val poly_irreducible_divides_exp = store_thm(
  "poly_irreducible_divides_exp",
  ``!r:'a field. Field r ==> !z. monic z /\ ipoly z ==>
   !p n. poly p /\ z pdivides (p ** n) ==> z pdivides p``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  Induct_on `n` >-
  rw[poly_one_divides_all, poly_monic_divides_one] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[poly_exp_1, ONE] >>
  `0 < n` by decide_tac >>
  `p ** SUC n = p * p ** n` by rw[poly_exp_SUC] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  `pprime z` by rw[poly_irreducible_prime] >>
  metis_tac[poly_prime_divides, poly_exp_poly]);

(* Theorem: monic x /\ ipoly x /\ poly y /\ poly p /\
            x pdivides p /\ y pdivides p /\ ~(x pdivides y) ==> (x * y) pdivides p *)
(* Proof:
   Since y pdivides p,
         ?s. poly s /\ (p = s * y)      by poly_divides_def
     Now x pdivides p,
      or x pdivides (s * x)
   Since pprime x                       by poly_irreducible_prime
         x pdivides s or x pdivides x   by poly_prime_divides
     But ~(x pdivides y),
      so x pdivides s,
      or ?t. poly t /\ (s = t * x)      by poly_divides_def
   Hence p = (t * x) * y
           = t * (x * y)                by poly_mult_assoc
      or (x * y) pdivides p             by poly_divides_def
*)
val poly_irreducible_mult_divides = store_thm(
  "poly_irreducible_mult_divides",
  ``!r:'a field. Field r ==> !x y p. monic x /\ ipoly x /\ poly y /\ poly p /\
    x pdivides p /\ y pdivides p /\ ~(x pdivides y) ==> (x * y) pdivides p``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `?s. poly s /\ (p = s * y)` by rw[GSYM poly_divides_def] >>
  `pprime x` by rw[poly_irreducible_prime] >>
  `pmonic x` by rw[poly_monic_irreducible_property] >>
  `x pdivides s` by metis_tac[poly_prime_divides] >>
  `?t. poly t /\ (s = t * x)` by rw[GSYM poly_divides_def] >>
  `p = t * (x * y)` by rw[poly_mult_assoc] >>
  metis_tac[poly_divides_def, poly_mult_poly]);

(* Note: In Z_4[x], (2x + 1)*(2x + 1) = 1 *)

(* Theorem: ipoly p ==> ~(p pdivides |1|) *)
(* Proof:
   By contradiction, assume p pdivides |1|.
   Then ?q. poly q /\ ( |1| = q * p)     by poly_divides_def
   Given ipoly p
     ==> poly p                         by poly_irreducible_poly
     and 0 < deg p                      by poly_irreducible_deg_nonzero
   Since |1| <> |0|                     by poly_one_ne_poly_zero
      so p <> |0| and q <> |0|          by poly_mult_zero
    thus 0 = deg q + deg p              by poly_deg_mult_nonzero, poly_deg_one
      or deg p = 0 and deg q = 0        by ADD_EQ_0
   which contradicts 0 < deg p.
*)
val poly_irreducible_not_divides_one = store_thm(
  "poly_irreducible_not_divides_one",
  ``!r:'a field. Field r ==> !p. ipoly p ==> ~(p pdivides |1|)``,
  rpt strip_tac >>
  `?q. poly q /\ ( |1| = q * p)` by rw[GSYM poly_divides_def] >>
  `Ring r /\ |1| <> |0|` by rw[] >>
  `poly p /\ 0 < deg p` by rw[poly_irreducible_poly, poly_irreducible_deg_nonzero] >>
  `p <> |0| /\ q <> |0|` by metis_tac[poly_mult_zero] >>
  `0 = deg q + deg p` by metis_tac[poly_deg_mult_nonzero, poly_deg_one] >>
  `(deg p = 0) /\ (deg q = 0)` by decide_tac >>
  decide_tac);

(* Theorem: !p q. monic p /\ 0 < deg p /\ monic q /\ ipoly q /\ p pdivides q ==> (p = q) *)
(* Proof:
   Since p pdivides q,
         ?s. poly s /\ (q = s * p)       by poly_divides_def
     Now pmonic q                        by poly_monic_irreducible_property
     and pprime q                        by poly_irreducible_prime
   Since q pdivides q                    by poly_divides_reflexive
      so q pdivides s or q pdivides p    by poly_prime_divides
   If q pdivides s,
      ?t. poly t /\ (s = t * q)          by poly_divides_def
      |1| * q = q                        by poly_mult_lone
              = (t * q) * p              by q = s * p, s = t * q
              = t * (q * p)              by poly_mult_assoc
              = t * (p * q)              by poly_mult_comm
              = t * p * q                by poly_mult_assoc
      so  |1| = t * p                    by poly_monic_mult_rcancel
      but p <> |0|                       by poly_monic_nonzero
      and t <> |0|                       by poly_mult_lzero
       so 0 = deg t + deg p              by poly_deg_mult_nonzero, poly_deg_one
       or deg t = 0 and deg p = 0        by ADD_EQ_0
      which contradicts 0 < deg p.
   If q pdivides p,
      Given monic p and monic q,
      and p pdivides q,
      This means p = q                   by poly_monic_divides_antisymmetric
*)
val poly_monic_divides_irreducible = store_thm(
  "poly_monic_divides_irreducible",
  ``!r:'a field. Field r ==> !p q. monic p /\ 0 < deg p /\ monic q /\ ipoly q /\ p pdivides q ==> (p = q)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0 /\ |1| <> |0|` by rw[] >>
  `poly |1| /\ poly p /\ poly q` by rw[] >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `pmonic q` by rw[poly_monic_irreducible_property] >>
  `pprime q` by rw[poly_irreducible_prime] >>
  `q pdivides s \/ q pdivides p` by metis_tac[poly_prime_divides, poly_divides_reflexive] >| [
    `?t. poly t /\ (s = t * q)` by rw[GSYM poly_divides_def] >>
    `|1| * q = (t * q) * p` by rw[] >>
    `_ = t * p * q` by rw[poly_mult_assoc, poly_mult_comm] >>
    `poly (t * p)` by rw[] >>
    `|1| = t * p` by metis_tac[poly_monic_mult_rcancel] >>
    `p <> |0|` by metis_tac[poly_monic_nonzero] >>
    `t <> |0|` by metis_tac[poly_mult_lzero] >>
    `0 = deg t + deg p` by metis_tac[poly_deg_mult_nonzero, poly_deg_one] >>
    `deg p = 0` by decide_tac >>
    `deg p <> 0` by decide_tac,
    metis_tac[poly_monic_divides_antisymmetric]
  ]);

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
            !e. monic e /\ ipoly e ==> (e IN s <=> e pdivides PPROD s) *)
(* Proof: by finite induction on s.
   Base case: e IN {} <=> e pdivides PPROD {}
      First, e IN {} = F                        by MEMBER_NOT_EMPTY
      Since PPROD {} = |1|                      by poly_prod_set_empty
        and e pdivides |1| = F                  by poly_irreducible_not_divides_one
   Step case: e' IN e INSERT s <=> e' pdivides PPROD (e INSERT s)
      Note !z. z IN s ==> monic z /\ ipoly z    by IN_INSERT
       and !z. z IN s ==> poly z                by poly_monic_poly
      thus s SUBSET (PolyRing r).carrier        by poly_ring_property, SUBSET_DEF
     Hence PPROD (e INSERT s)
         = e * PPROD (s DELETE e)               by poly_prod_set_thm
         = e * PPROD s                          by DELETE_NON_ELEMENT
     Since e IN (e INSERT s)                    by COMPONENT
           monic e /\ ipoly e                   by implication
        so poly e                               by poly_monic_poly
       and poly (PPROD s)                       by poly_prod_set_poly
    If part: e' IN e INSERT s ==> e' pdivides e * PPROD s
       Since e' IN e INSERT s,
            (e' = e) \/ (e' IN s)               by IN_INSERT
       If e' = e,
          Since e pdivides e * PPROD s          by poly_divides_def, poly_mult_comm
             so e' pdivides e * PPROD s.
       If e' IN s,
          Since e' pdivides PPROD s             by induction hypothesis
             so e' pdivides e * PPROD s         by poly_divides_multiple
    Only-if part: e' pdivides e * PPROD s ==> e' IN e INSERT s
         That is: e' pdivides e * PPROD s ==> (e' = e) \/ (e' IN s)            by IN_INSERT
              or: e' pdivides e * PPROD s ==> (e' = e) \/ e' pdivides PPROD s  by induction hypothesis
       If e' = e, this is trivial.
       If e' <> e,
          Since pmonic e'                       by poly_monic_irreducible_property
            and pprime e'                       by poly_irreducible_prime
            but ~(e' pdivides e)                by poly_monic_divides_irreducible
             so e' pdivides (PPROD s)           by poly_prime_divides
*)
val poly_irreducible_divides_prod_set = store_thm(
  "poly_irreducible_divides_prod_set",
  ``!r:'a field. Field r ==> !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
   !e. monic e /\ ipoly e ==> (e IN s <=> e pdivides PPROD s)``,
  ntac 2 strip_tac >>
  `Ring r` by rw[] >>
  `!s. FINITE s ==> (!z. z IN s ==> monic z /\ ipoly z) ==>
   !e. monic e /\ ipoly e ==> (e IN s <=> e pdivides PPROD s)` suffices_by metis_tac[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY, poly_prod_set_empty, poly_irreducible_not_divides_one] >>
  `!z. z IN s ==> monic z /\ ipoly z` by rw[] >>
  `!z. z IN s ==> poly z` by rw[] >>
  `s SUBSET (PolyRing r).carrier` by metis_tac[poly_ring_property, SUBSET_DEF] >>
  `PPROD (e INSERT s) = e * PPROD (s DELETE e)` by rw[poly_prod_set_thm] >>
  `_ = e * PPROD s` by metis_tac[DELETE_NON_ELEMENT] >>
  `e IN (e INSERT s)` by rw[] >>
  `poly e /\ poly (PPROD s)` by rw[poly_prod_set_poly] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `(e' = e) \/ (e' IN s)` by metis_tac[IN_INSERT] >-
    metis_tac[poly_divides_def, poly_mult_comm] >>
    metis_tac[poly_divides_multiple],
    rw[] >>
    Cases_on `e' = e` >-
    rw[] >>
    `pmonic e'` by rw[poly_monic_irreducible_property] >>
    `pprime e'` by rw[poly_irreducible_prime] >>
    metis_tac[poly_prime_divides, poly_monic_divides_irreducible]
  ]);

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
            !p n. poly p /\ 0 < n /\ (PPROD s) pdivides (p ** n) ==> (PPROD s) pdivides p *)
(* Proof: by finite induction on s.
   Base case: PPROD {} pdivides p ** n ==> PPROD {} pdivides p
      Since PPROD {} = |1|            by poly_prod_set_empty
        and |1| pdivides p            by poly_one_divides_all
      hence true.
   Step case: PPROD (e INSERT s) pdivides p ** n ==> PPROD (e INSERT s) pdivides p
      Since !z. z IN s ==> monic z /\ ipoly z    by IN_INSERT
        and !z. z IN s ==> poly z                by poly_monic_poly
         so s SUBSET (PolyRing r).carrier        by poly_ring_property, SUBSET_DEF
      hence PPROD (e INSERT s)
          = e * PPROD (s DELETE e)    by poly_prod_set_thm
          = e * PPROD s               by DELETE_NON_ELEMENT
        But e IN (e INSERT s)         by COMPONENT
         so monic e /\ ipoly e        by implication
        and poly e                    by poly_monic_poly
        and poly (PPROD s)            by poly_prod_set_poly
      Therefore,
            e pdivides p ** n, and
            PPROD s pdivides p ** n   by poly_mult_divides
        Now e pdivides p              by poly_irreducible_divides_exp
        and PPROD s pdivides p        by induction hypothesis
      Since ~(e IN s),
            ~(e pdivides PPROD s)     by poly_irreducible_divides_prod_set
      Hence (e * PPROD s) pdivides p  by poly_irreducible_mult_divides
*)
val poly_distinct_irreducibles_divides_exp = store_thm(
  "poly_distinct_irreducibles_divides_exp",
  ``!r:'a field. Field r ==> !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
   !p n. poly p /\ (PPROD s) pdivides (p ** n) ==> (PPROD s) pdivides p``,
  ntac 2 strip_tac >>
  `Ring r` by rw[] >>
  `!s. FINITE s ==> (!z. z IN s ==> (monic z /\ ipoly z)) ==>
   !p n. poly p /\ (PPROD s) pdivides (p ** n) ==> (PPROD s) pdivides p` suffices_by metis_tac[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[poly_prod_set_empty, poly_one_divides_all] >>
  `!z. z IN s ==> monic z /\ ipoly z` by rw[] >>
  `!z. z IN s ==> poly z` by rw[] >>
  `s SUBSET (PolyRing r).carrier` by metis_tac[poly_ring_property, SUBSET_DEF] >>
  `PPROD (e INSERT s) = e * PPROD (s DELETE e)` by rw[poly_prod_set_thm] >>
  `_ = e * PPROD s` by metis_tac[DELETE_NON_ELEMENT] >>
  `e IN (e INSERT s)` by rw[] >>
  `poly e /\ poly (PPROD s) /\ poly (p ** n)` by rw[poly_prod_set_poly] >>
  `e pdivides p ** n /\ PPROD s pdivides p ** n` by metis_tac[poly_mult_divides] >>
  `e pdivides p` by metis_tac[poly_irreducible_divides_exp] >>
  `PPROD s pdivides p` by metis_tac[] >>
  `~(e pdivides PPROD s)` by rw[GSYM poly_irreducible_divides_prod_set] >>
  metis_tac[poly_irreducible_mult_divides]);

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
            !p n. poly p /\ (p ** n == |0|) (pm (PPROD s)) ==> (p == |0|) (pm (PPROD s)) *)
(* Proof:
   Since !z. z IN s ==> (monic z /\ ipoly z)
   Hence ulead (PPROD s)                      by poly_monic_prod_set_ulead
     and poly (p ** n)                        by poly_exp_poly
   Given (p ** n == |0|) (pm (PPROD s)),
         PPROD s pdivides p ** n              by poly_divides_pmod_eq_zero
    then PPROD s pdivides p                   by poly_distinct_irreducibles_divides_exp
      or (p == |0|) (pm (PPROD s))            by poly_divides_pmod_eq_zero
*)
val poly_distinct_irreducibles_mod_exp_eq_zero = store_thm(
  "poly_distinct_irreducibles_mod_exp_eq_zero",
  ``!r:'a field. Field r ==> !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) ==>
   !p n. poly p /\ (p ** n == |0|) (pm (PPROD s)) ==> (p == |0|) (pm (PPROD s))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `ulead (PPROD s) /\ poly (p ** n)` by rw[poly_monic_prod_set_ulead] >>
  metis_tac[poly_distinct_irreducibles_divides_exp, poly_divides_pmod_eq_zero]);

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) /\ s <> {} ==>
           !p q. poly p /\ poly q /\
                 (p ** (char r) == q ** (char r)) (pm (PPROD s)) ==> (p == q) (pm (PPROD s)) *)
(* Proof:
   Since FiniteField r ==> Field r             by FiniteField_def
                       ==> prime (char r)      by finite_field_char
   Let m = char r, z = PPROD s.
   Then 0 < m                                  by PRIME_POS
   Given !z. z IN s ==> monic z /\ ipoly z
    thus ulead z                               by poly_monic_prod_set_ulead
   Given (p ** m == q ** m) (pm z),
         (p ** m - q ** m == |0|) (pm z)       by poly_pmod_sub_eq_zero
      or ((p - q) ** m == |0|) (pm z)          by poly_freshman_thm_sub
   Hence (p - q == |0|) (pm z)                 by poly_distinct_irreducibles_mod_exp_eq_zero
      or (p == q) (pm z)                       by poly_pmod_sub_eq_zero
*)
val poly_distinct_irreducibles_mod_exp_char_eq = store_thm(
  "poly_distinct_irreducibles_mod_exp_char_eq",
  ``!r:'a field. FiniteField r ==> !s. FINITE s /\ (!z. z IN s ==> monic z /\ ipoly z) /\ s <> {} ==>
   !p q. poly p /\ poly q /\ (p ** (char r) == q ** (char r)) (pm (PPROD s)) ==> (p == q) (pm (PPROD s))``,
  rpt (stripDup[FiniteField_def]) >>
  `prime (char r)` by rw[finite_field_char] >>
  `0 < char r` by rw[PRIME_POS] >>
  `Ring r` by rw[] >>
  `ulead (PPROD s)` by rw[poly_monic_prod_set_ulead] >>
  qabbrev_tac `m = char r` >>
  qabbrev_tac `z = PPROD s` >>
  `(p ** m - q ** m == |0|) (pm z)` by rw[GSYM poly_pmod_sub_eq_zero] >>
  `((p - q) ** m == |0|) (pm z)` by metis_tac[poly_freshman_thm_sub] >>
  `(p - q == |0|) (pm z)` by metis_tac[poly_distinct_irreducibles_mod_exp_eq_zero, poly_sub_poly] >>
  rw[poly_pmod_sub_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Quotient Field and Polynomial Ring modulo Irreducible Polynomial.         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r /\ ipoly p ==>
                FieldIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) p).carrier)
                         (PolyModRing r p)
                         (PolyRing r / principal_ideal (PolyRing r) p) *)
(* Proof:
   Note ipoly p ==> pmonic p   by poly_irreducible_pmonic
   Hence true                  by poly_mod_ring_iso_quotient_ring, field_iso_eq_ring_iso
*)
val poly_quotient_field_iso_poly_mod = store_thm(
  "poly_quotient_field_iso_poly_mod",
  ``!r:'a field. Field r ==> !p. ipoly p ==>
       FieldIso (\x. coset (PolyRing r).sum x (principal_ideal (PolyRing r) p).carrier)
                (PolyModRing r p)
                (PolyRing r / principal_ideal (PolyRing r) p)``,
  rw[poly_irreducible_pmonic, poly_mod_ring_iso_quotient_ring, field_iso_eq_ring_iso]);

(* Theorem: Field r ==> ipoly p ==> Monoid ((PolyModRing r p).prod excluding |0|) *)
(* Proof:
   Note ipoly p ==> pmonic p                         by poly_irreducible_pmonic
   Expanding by definitions, this is to show:
   (1) poly x /\ poly y ==> poly ((x * y) % p)
       True by poly_mult_poly, poly_mod_poly
   (2) poly x /\ poly y ==> deg ((x * y) % p) < deg p
       True by poly_mult_poly, poly_division due to pmonic p.
   (3) x <> |0| /\ y <> |0| ==> (x * y) % p <> |0|
       By contradiction, suppose (x * y) % p = |0|
       Since ipoly p ==> pprime p                    by poly_irreducible_prime
       Hence (x % p = |0|) \/ (y % p = |0|)          by poly_mod_prime_product
       But deg x < deg p and deg y < deg p,
       so x = |0| or y = |0|                         by poly_mod_less
       This contradicts x <> |0| and y <> |0|.
   (4) ((x * y) % p * z) % p = (x * (y * z) % p) % p
       True by poly_mod_mult_assoc.
   (5) poly |1|
       True by poly_one_poly.
   (6) deg |1| < deg p
       True since deg |1| = 0 by poly_deg_one, and given 0 < deg p.
   (7) |1| <> |0|
       True by poly_field_one_ne_zero.
   (8) ( |1| * x) % p = x
       True by poly_mult_lone, poly_mod_less.
   (9) (x * |1|) % p = x
       True by poly_mult_rone, poly_mod_less.
*)
val poly_mod_ring_prod_monoid = store_thm(
  "poly_mod_ring_prod_monoid",
  ``!r:'a field. Field r ==> !p. ipoly p ==> Monoid ((PolyModRing r p).prod excluding |0|)``,
  rpt strip_tac >>
  `Ring r /\ pmonic p` by rw[poly_irreducible_pmonic] >>
  `deg p <> 0` by decide_tac >>
  rw_tac std_ss[Monoid_def, excluding_def, poly_mod_ring_def, poly_remainders_def, IN_DIFF, IN_SING, GSPECIFICATION] >-
  rw[] >-
  rw[poly_division] >-
 (`x * y <> |0|` by metis_tac[poly_mult_eq_zero] >>
  spose_not_then strip_assume_tac >>
  `pprime p` by rw[poly_irreducible_prime] >>
  `(x % p = |0|) \/ (y % p = |0|)` by metis_tac[poly_mod_prime_product] >-
  metis_tac[poly_mod_less] >>
  metis_tac[poly_mod_less]) >-
  rw_tac std_ss[poly_mod_mult_assoc] >-
  rw[] >-
  rw[] >-
  rw[] >-
  rw[poly_mod_less] >>
  rw[poly_mod_less]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring Modulo irreducible gives Finite Field.                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Polynomial GCD and Inverse                                                *)
(* ------------------------------------------------------------------------- *)

(*
> ring_gcd_linear;
val it = |- !r f. EuclideanRing r f ==>
            !p q. p IN R /\ q IN R ==> ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q): thm
> ring_irreducible_gcd;
val it = |- !r f. EuclideanRing r f ==>
            !p. p IN R /\ atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q: thm
*)

(*
> poly_ring_euclid_ring;
val it = |- !r. Field r ==> EuclideanRing (PolyRing r) (\p. if p = |0| then 0 else SUC (deg p)): thm

> ring_irreducible_gcd |> ISPEC ``PolyRing r``;
val it = |- !f. EuclideanRing (PolyRing r) f ==>
     !p. p IN (PolyRing r).carrier /\ ipoly p ==>
       !q. q IN (PolyRing r).carrier ==>
         upoly (ring_gcd (PolyRing r) f p q) \/ ring_divides (PolyRing r) p q: thm

> ring_gcd_linear |> ISPEC ``PolyRing r``;
val it = |- !f. EuclideanRing (PolyRing r) f ==>
     !p q. p IN (PolyRing r).carrier /\ q IN (PolyRing r).carrier ==>
       ?a b. a IN (PolyRing r).carrier /\ b IN (PolyRing r).carrier /\
       (ring_gcd (PolyRing r) f p q = a * p + b * q): thm
*)

(* Theorem: a * p + b * q = [c] ==> (b * q) % p = [c] *)
(* Proof:
   Note pmonic p = poly p /\ 0 < deg p /\ unit (lead p)
   [c] = [c] % p                           by poly_mod_less
       = (a * p + b * q) % p               by substitution
       = ((a * p) % p + (b * q) % p) % p   by poly_mod_add
       = ( |0| + (b * q) % p) % p          by poly_mod_multiple
       = ((b * q) % p) % p                 by poly_add_lzero
       = (b * q) % p                       by poly_mod_mod
*)
val poly_linear_eq_const_property = store_thm(
  "poly_linear_eq_const_property",
  ``!r:'a ring. Ring r ==> !p q a b c. pmonic p /\ poly q /\ poly a /\ poly b /\
       c IN R /\ c <> #0 /\ (a * p + b * q = [c]) ==> ((b * q) % p = [c])``,
  rpt strip_tac >>
  `[c] = [c] % p` by rw[poly_mod_less] >>
  `_ = ((a * p) % p + (b * q) % p) % p` by rw[GSYM poly_mod_add] >>
  rw[poly_mod_multiple, poly_mod_mod]);

(* Theorem: a * p + b * q = [c] ==> b % p <> |0| *)
(* Proof:
   By contradiction, assume b % p = |0|.
   Since (b * q) % p = [c]                        by poly_linear_eq_const_property
   and   (b * q) % p = ((b % p) * (q % p)) % p    by poly_mod_mult
   b % p = |0| ==> |0| = [c]                      by poly_zero_mod
   But |0| = []                                   by poly_zero
   Hence this is a contradiction.
*)
val poly_linear_eq_const_property1 = store_thm(
  "poly_linear_eq_const_property1",
  ``!r:'a ring. Ring r ==> !p q a b c. pmonic p /\ poly q /\ poly a /\ poly b /\
       c IN R /\ c <> #0 /\ (a * p + b * q = [c]) ==> b % p <> |0|``,
  spose_not_then strip_assume_tac >>
  `((b % p) * (q % p)) % p = (b * q) % p` by rw[poly_mod_mult] >>
  `_ = [c]` by metis_tac[poly_linear_eq_const_property] >>
  `[c] = ( |0| * q % p) % p` by metis_tac[] >>
  `_ = |0|` by rw[poly_mod_less] >>
  metis_tac[poly_zero, NOT_CONS_NIL]);

(* Theorem: a * p + b * q = [c] ==> (q * ( |/ c * b % p)) % p = |1| *)
(* Proof:
   Since (b * q) % p = [c]                       by poly_linear_eq_const_property
   and   (b * q) % p = ((b % p) * (q % p)) % p   by poly_mod_mult
     (q * ( |/ c * b % p)) % p
   = (q % p * ( |/ c * b % p) % p) % p           by poly_mod_mult
   = (q % p * ( |/ c * b) % p) % p               by poly_mod_cmult
   = (q * ( |/ c * b)) % p                       by poly_mod_mult
   = (( |/ c * b) * q) % p                       by poly_mult_comm
   = ( |/ c * (b * q)) % p                       by poly_cmult_mult
   = ( |/ c * (b * q) % p) % p                   by poly_mod_cmult
   = ( |/ c * [c]) % p                           by above
   = ([|/ c * c]) % p                            by poly_cmult_const_nonzero
   = [#1] % p                                    by field_mult_linv
   = |1| % p                                     by poly_one
   = |1|                                         by poly_mod_less
*)
val poly_linear_eq_const_property2 = store_thm(
  "poly_linear_eq_const_property2",
  ``!r:'a field. Field r ==> !p q a b c. pmonic p /\ poly q /\ poly a /\ poly b /\
       c IN R /\ c <> #0 /\ (a * p + b * q = [c]) ==> ((q * ( |/ c * b % p)) % p = |1|)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `|/ c IN R /\ |/ c <> #0` by metis_tac[field_inv_element, field_inv_nonzero, field_nonzero_eq] >>
  `( |/ c * c = #1) /\ (#1 <> #0)` by rw[field_mult_linv, field_nonzero_eq] >>
  `(b * q) % p = [c]` by metis_tac[poly_linear_eq_const_property] >>
  `(q * ( |/ c * b % p)) % p = (q % p * ( |/ c * b % p) % p) % p` by rw[poly_mod_mult] >>
  `_ = (q % p * ( |/ c * b) % p) % p` by rw[poly_mod_cmult] >>
  `_ = (q * ( |/ c * b)) % p` by rw[poly_mod_mult] >>
  `_ = (( |/ c * b) * q) % p` by rw_tac std_ss[poly_mult_comm, poly_cmult_poly, field_is_ring] >>
  `_ = ( |/ c * (b * q)) % p` by rw[poly_cmult_mult] >>
  `_ = ( |/ c * (b * q) % p) % p` by rw_tac std_ss[poly_mod_cmult, poly_mult_poly, field_is_ring] >>
  `_ = ([|/ c * c]) % p` by rw[poly_cmult_const_nonzero] >>
  rw[poly_one, poly_mod_less]);

(* Theorem: Field r /\ ipoly p ==>
            !x. poly x /\ deg x < deg p /\ x <> |0| ==>
            ?y. ((poly y /\ deg y < deg p) /\ y <> |0|) /\ ((x * y) % p = |1|) *)
(* Proof:
   Note ipoly p ==> pmonic p                      by poly_irreducible_pmonic
   Field r ==> EuclideanRing (PolyRing r) norm    by poly_ring_euclid_ring
   Hence by ring_gcd_linear,
         ?a b. poly a /\ poly b /\ ring_gcd (PolyRing r) norm p x = a * p + b * x
   Since deg x < deg p /\ x <> |0|, x cannot be a multiple of p,
         or ~ (ring_divides (PolyRing r) p x)     by poly_mod_less, poly_field_mod_zero_eq_divides
   Hence upoly (ring_gcd (PolyRing r) norm p x)   by ring_irreducible_gcd
     But Field r ==> upoly is constant            by poly_field_units
     So  [u] = (b * x) % p for some u in R        by poly_deg_eq_zero
     Take ( |/ u)*(b % p) as the inverse for x, apply poly_mult_comm.
  This requires to show:
  (1) poly ( |/ u * b % p)                        by poly_cmult_poly
  (2) deg ( |/ u * b % p) < deg p                 by poly_field_deg_cmult
  (3) |/ u * (b % p) <> |0|
      Since [u] = a * p + b * x
      ==> b % p <> |0|                            by poly_linear_eq_const_property1
      This is true                                by poly_field_cmult_eq_zero
  (4) (x * ( |/ u * b % p)) % p = |1|
      Since [u] = a * p + b * x
      ==> (x * ( |/ u * b % p)) % p = |1|         by poly_linear_eq_const_property2
*)
val poly_mod_prod_inv = store_thm(
  "poly_mod_prod_inv",
  ``!r:'a field. Field r ==> !p. ipoly p ==>
            !x. poly x /\ deg x < deg p /\ x <> |0| ==>
            ?y. ((poly y /\ deg y < deg p) /\ y <> |0|) /\ ((x * y) % p = |1|)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pmonic p` by rw[poly_irreducible_pmonic] >>
  `EuclideanRing (PolyRing r) norm` by rw[poly_ring_euclid_ring] >>
  `?a b. poly a /\ poly b /\ (ring_gcd (PolyRing r) norm p x = a * p + b * x)` by prove_tac[ring_gcd_linear, poly_ring_element] >>
  `x % p = x` by rw[poly_mod_less] >>
  `p <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO] >>
  `~ (ring_divides (PolyRing r) p x)` by metis_tac[poly_field_mod_zero_eq_divides] >>
  `upoly (ring_gcd (PolyRing r) norm p x)` by metis_tac[ring_irreducible_gcd, poly_ring_element] >>
  `poly (ring_gcd (PolyRing r) norm p x)` by metis_tac[ring_gcd_element, poly_ring_element] >>
  qabbrev_tac `d = ring_gcd (PolyRing r) norm p x` >>
  qabbrev_tac `f = norm` >>
  `d <> |0| /\ (deg d = 0)` by metis_tac[poly_field_units] >>
  `?u. u IN R /\ u <> #0 /\ (d = [u])` by metis_tac[poly_deg_eq_zero] >>
  `|/ u IN R /\ |/ u <> #0` by metis_tac[field_inv_element, field_inv_nonzero, field_nonzero_eq] >>
  qexists_tac `|/u * (b % p)` >>
  `deg (b % p) < deg p` by rw[poly_deg_mod_less] >>
  `poly (b % p)` by rw[poly_mod_poly] >>
  rw_tac std_ss[poly_cmult_poly, poly_field_deg_cmult] >-
  metis_tac[poly_field_cmult_eq_zero, poly_linear_eq_const_property1] >>
  prove_tac[poly_linear_eq_const_property2]);

(* Theorem: Field r /\ ipoly p ==> Group ((PolyModRing r p).prod excluding |0|) *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid ((PolyModRing r p).prod excluding |0|)
       True by poly_mod_ring_prod_monoid.
   (2) poly x /\ deg x < deg p /\ x <> |0| ==>
       ?y. ((poly y /\ deg y < deg p) /\ y <> |0|) /\ ((x * y) % p = |1|) /\ ((y * x) % p = |1|)
       True by poly_mod_prod_inv, poly_mult_comm.
*)
val poly_mod_prod_group = store_thm(
  "poly_mod_prod_group",
  ``!r:'a field. Field r ==> !p. ipoly p ==> Group ((PolyModRing r p).prod excluding |0|)``,
  rw_tac std_ss[Group_def] >-
  rw_tac std_ss[poly_mod_ring_prod_monoid] >>
  rw_tac std_ss[monoid_invertibles_def, poly_mod_ring_def, poly_remainders_def, excluding_def, IN_DIFF, IN_SING, EXTENSION, GSPECIFICATION] >>
  rw_tac std_ss[EQ_IMP_THM] >>
  `?y. ((poly y /\ deg y < deg p) /\ y <> |0|) /\ ((x * y) % p = |1|)` by rw[poly_mod_prod_inv] >>
  metis_tac[poly_mult_comm, field_is_ring]);

(* Theorem: FiniteField r ==> !p. ipoly p ==>
            FiniteGroup ((PolyModRing r p).prod excluding |0|) *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R    by FiniteField_def
   Hence Ring r /\ FiniteRing r             by field_is_ring, FiniteRing_def
    Note ipoly p ==> pmonic p               by poly_irreducible_pmonic
    With Group ((PolyModRing r p).prod excluding |0|)          by poly_mod_prod_group
     and FINITE ((PolyModRing r p).prod excluding |0|).carrier by poly_mod_ring_prod_finite
   Hence FiniteGroup ((PolyModRing r p).prod excluding |0|)    by FiniteGroup_def
*)
val poly_mod_prod_finite_group = store_thm(
  "poly_mod_prod_finite_group",
  ``!r:'a field. FiniteField r ==> !p. ipoly p ==>
     FiniteGroup ((PolyModRing r p).prod excluding |0|)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by metis_tac[FiniteRing_def] >>
  `pmonic p` by rw[poly_irreducible_pmonic] >>
  `Group ((PolyModRing r p).prod excluding |0|)` by rw[poly_mod_prod_group] >>
  `FINITE ((PolyModRing r p).prod excluding |0|).carrier` by rw[poly_mod_ring_prod_finite] >>
  metis_tac[FiniteGroup_def]);

(* Theorem: Field r /\ ipoly p ==> Ring (PolyModRing r p) *)
(* Proof:
   Since ipoly p ==> pmonic p   by poly_irreducible_pmonic
   and   Field r ==> Ring r     by field_is_ring
   Hence true                   by poly_mod_ring_ring, ulead p
*)
val poly_mod_irreducible_ring = store_thm(
  "poly_mod_irreducible_ring",
  ``!r:'a field. Field r ==> !p. ipoly p ==> Ring (PolyModRing r p)``,
  rw[poly_irreducible_pmonic, poly_mod_ring_ring]);

(* Theorem: Field r /\ ipoly p ==> Field (PolyModRing r p) *)
(* Proof:
   By Field_def, this is to show:
   (1) Ring (PolyModRing r p)
       True by poly_mod_irreducible_ring.
   (2) Group ((PolyModRing r p).prod excluding (PolyModRing r p).sum.id)
       Since (PolyModRing r p).sum.id = |0|   by poly_mod_ring_def
       True by poly_mod_prod_group.
*)
val poly_mod_irreducible_field = store_thm(
  "poly_mod_irreducible_field",
  ``!r:'a field. Field r ==> !p. ipoly p ==> Field (PolyModRing r p)``,
  rpt strip_tac >>
  rw[Field_def] >-
  rw[poly_mod_irreducible_ring] >>
  `(PolyModRing r p).sum.id = |0|` by rw_tac std_ss[poly_mod_ring_def] >>
  rw_tac std_ss[poly_mod_prod_group]);

(* Theorem: FiniteField r /\ ipoly p ==> FiniteField (PolyModRing r p) *)
(* Proof:
   By FiniteField_def, this is to show:
   (1) Field (PolyModRing r p)
       True by poly_mod_irreducible_field.
   (2) FINITE (PolyModRing r p).carrier
       Since poly p /\ 0 < deg p  by poly_irreducible_pmonic
       True by poly_mod_ring_finite.
*)
val poly_mod_irreducible_finite_field = store_thm(
  "poly_mod_irreducible_finite_field",
  ``!r:'a field. FiniteField r ==> !p. ipoly p ==> FiniteField (PolyModRing r p)``,
  rw[FiniteField_def] >-
  rw[poly_mod_irreducible_field] >>
  rw[poly_mod_ring_finite, poly_irreducible_pmonic, FiniteRing_def]);

(* Theorem: FiniteField r /\ ipoly z ==> (CARD Rz = CARD R ** deg z) *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R      by FiniteField_def
   Note ipoly z ==> pmonic z                  by poly_irreducible_pmonic
   The result follows                         by poly_mod_ring_card
*)
val poly_mod_irreducible_field_card = store_thm(
  "poly_mod_irreducible_field_card",
  ``!r:'a field. FiniteField r ==> !z. ipoly z ==> (CARD Rz = (CARD R) ** (deg z))``,
  rw[poly_mod_ring_card, poly_irreducible_pmonic, FiniteField_def, FiniteRing_def]);

(* Theorem: Field r /\ ipoly z /\ poly p ==> !n. (p % z) **z n = p ** n % z *)
(* Proof:
   Note pmonic z                              by poly_irreducible_pmonic
    and poly (p % z)                          by poly_mod_poly
    and deg (p % z) < deg                     by poly_deg_mod_less]
     so (p % z) IN (PolyModRing r z).carrier  by poly_mod_ring_property
   Also Field (PolyModRing r z)               by poly_mod_irreducible_field
   By induction on n.
   Base: (p % z) **z 0 = p ** 0 % z
          (p % z) **z 0
        = #1z                                 by field_exp_0
        = |1|                                 by poly_mod_ring_property
        = |1| % z                             by poly_mod_one, pmonic z
        = (p ** 0) % z                        by poly_exp_0

   Step: (p % z) **z n = p ** n % z ==> (p % z) **z SUC n = p ** SUC n % z
          (p % z) **z SUC n
        = (p % z) *z ((p % z) **z n)          by field_exp_SUC
        = (p % z) *z ((p ** n) % z)           by induction hypothesis
        = (p % z * ((p ** n) % z)) % z        by poly_mod_ring_property
        = (p * (p ** n)) % z                  by poly_mod_mult, poly_mod_mod
        = (p ** SUC n) % z                    by poly_exp_SUC
*)
val poly_mod_field_exp = store_thm(
  "poly_mod_field_exp",
  ``!r:'a field. Field r ==> !z. ipoly z ==> !p. poly p ==> !n. (p % z) **z n = p ** n % z``,
  rpt strip_tac >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  `poly (p % z) /\ deg (p % z) < deg z` by rw[poly_deg_mod_less] >>
  `(p % z) IN Rz` by rw[poly_mod_ring_property] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  Induct_on `n` >-
  rw[poly_mod_ring_property, poly_mod_one] >>
  rw[poly_exp_SUC, field_exp_SUC, poly_mod_ring_property] >>
  `Ring r /\ poly (p ** n)` by rw[] >>
  metis_tac[poly_mod_mult, poly_mod_mod, poly_mod_poly]);

(* Theorem: Ring r /\ pmonic z ==> !n. ##z |1| n = chop [##n] *)
(* Proof:
   Note Ring (PolyModRing r z)     by poly_mod_ring_ring, pmonic p
   If #1 = #0,
   Then R = {#0}                   by ring_one_eq_zero
   Hence LHS = ##z |1| n
             = ##z |0| n           by poly_one_eq_poly_zero
             = #0z                 by ring_add_group, group_id_exp
             = |0|                 by poly_mod_ring_property
         RHS = chop [##n]
             = chop [#0]           by IN_SING, ring_num_element
             = |0|                 by poly_chop_const_zero
   If #1 <> #0, by induction on n.
   Base: ##z |1| 0 = chop [##0]
     LHS = ##z |1| 0
         = #0z                     by poly_add_group, group_exp_0
         = |0|                     by poly_mod_ring_property
         = chop [##0] = RHS        by poly_chop_zero, ring_num_0, poly_chop_const_zero
   Step: ##z |1| n = chop [##n] ==>
         ##z |1| (SUC n) = chop [##(SUC n)]
       ##z |1| (SUC n)
     = ( |1| + ##z |1| n) % p              by group_exp_SUC, poly_mod_ring_property
     = ( |1| + chop [##n]) % p             by induction hypothesis
     = ([#1] + chop [##n]) % p             by poly_one, #1 <> #0
     = (chop([#1] || [##n])) % p           by poly_chop_add_comm, poly_is_weak
     = chop([#1 + ##n]) % p                by weak_add_def
     = chop [##(SUC n)] % p                by ring_num_SUC
     If ##(SUC n) = #0,
          chop [##(SUC n)]
        = chop [#0] = |0|                  by poly_chop_const_zero
        and |0| % p = |0|                  by poly_zero_mod
     If ##(SUC n) <> #0,
          chop [##(SUC n)]
        = [##(SUC n)]                      by poly_chop_const_nonzero
        and [##(SUC n)] % p = [##(SUC n)]  by poly_mod_const
*)
val poly_mod_one_sum_n = store_thm(
  "poly_mod_one_sum_n",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !n. ##z |1| n = chop [##n]``,
  rpt strip_tac >>
  `Ring (PolyModRing r z)` by rw_tac std_ss[poly_mod_ring_ring] >>
  Cases_on `#1 = #0` >| [
    `R = {#0}` by metis_tac[ring_one_eq_zero] >>
    metis_tac[IN_SING, ring_num_element, poly_chop_const_zero, poly_one, poly_zero, ring_add_group, group_id_exp, poly_mod_ring_property],
    Induct_on `n` >-
    rw[poly_mod_ring_property] >>
    rw[poly_mod_ring_property] >-
    metis_tac[ring_add_rzero, ring_one_element] >-
    rw_tac std_ss[poly_mod_one, poly_one_alt] >-
   (rw_tac std_ss[poly_add_def, poly_chop_def, weak_add_def, poly_is_weak, poly_one_poly, poly_one, zero_poly_def] >>
    metis_tac[poly_zero_mod, poly_zero]) >>
    rw_tac std_ss[poly_add_def, poly_chop_def, weak_add_def, poly_is_weak, poly_one_poly, poly_one, zero_poly_def] >>
    metis_tac[ring_one_element, ring_num_element, ring_add_element, poly_mod_const]
  ]);

(* Theorem: Ring r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z) *)
(* Proof: by poly_monic_pmonic, poly_mod_ring_ring *)
val poly_mod_ring_monic_ring = store_thm(
  "poly_mod_ring_monic_ring",
  ``!r:'a ring. Ring r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z)``,
  rw_tac std_ss[poly_monic_pmonic, poly_mod_ring_ring]);

(* Theorem: Field r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z) *)
(* Proof: by field_is_ring, poly_mod_ring_monic_ring *)
val poly_mod_ring_monic_alt = store_thm(
  "poly_mod_ring_monic_alt",
  ``!r:'a field. Field r ==> !z. monic z /\ 0 < deg z ==> Ring (PolyModRing r z)``,
  rw_tac std_ss[field_is_ring, poly_mod_ring_monic_ring]);

(* Theorem: Ring r /\ pmonic z ==> (char (PolyModRing r z) = char r) *)
(* Proof:
   Let s = (PolyModRing r z),
   Then Ring s                     by poly_mod_ring_ring, ulead p
     ##z |1| (char r)
   = chop [##(char r)]             by poly_mod_one_sum_n
   = chop [#0]                     by char_property
   = |0|                           by poly_chop_const_zero
   Since #0z = |0| /\ #1z = |1|    by poly_mod_ring_property, deg z <> 0
   Hence (char s) divides (char r) by ring_char_divides,
   Also,
     |0|
   = #0z                           by poly_mod_ring_property, deg z <> 0
   = ##z |1| (char s)              by char_property
   = chop [#(char s)]              by poly_mod_one_sum_n
   ==> ## char s) = #0             by poly_chop_const_eq_zero
   Hence (char r) divides (char s) by ring_char_divides
   Therefore  (char s) = (char r)  by DIVIDES_ANTISYM
*)
val poly_mod_ring_char = store_thm(
  "poly_mod_ring_char",
  ``!r:'a ring z. Ring r /\ pmonic z ==> (char (PolyModRing r z) = char r)``,
  rpt strip_tac >>
  `deg z <> 0` by decide_tac >>
  qabbrev_tac `s = PolyModRing r z` >>
  `Ring s` by rw_tac std_ss[poly_mod_ring_ring, Abbr`s`] >>
  `##z |1| (char r) = chop[##(char r)]` by rw_tac std_ss[poly_mod_one_sum_n, Abbr`s`] >>
  `_ = |0|` by rw[char_property] >>
  `(#0z = |0|) /\ (#1z = |1|)` by rw[poly_mod_ring_property] >>
  `(char s) divides (char r)` by rw_tac std_ss[GSYM ring_char_divides, Abbr`s`] >>
  `|0| = ##z |1| (char s)` by metis_tac[char_property, poly_mod_ring_property, Abbr`s`] >>
  `_ = chop [##(char s)]` by rw_tac std_ss[poly_mod_one_sum_n, Abbr`s`] >>
  `##(char s) = #0` by rw_tac std_ss[GSYM poly_chop_const_eq_zero, ring_num_element, Abbr`s`] >>
  `(char r) divides (char s)` by rw_tac std_ss[GSYM ring_char_divides] >>
  rw_tac std_ss[DIVIDES_ANTISYM]);

(* Theorem: Field r ==> !z. monic z /\ 0 < deg z ==> (char (PolyModRing r z) = char r) *)
(* Proof: by field_is_ring, poly_monic_pmonic, poly_mod_ring_char *)
val poly_mod_ring_char_alt = store_thm(
  "poly_mod_ring_char_alt",
  ``!r:'a field. Field r ==> !z. monic z /\ 0 < deg z ==> (char (PolyModRing r z) = char r)``,
  rw_tac std_ss[field_is_ring, poly_monic_pmonic, poly_mod_ring_char]);

(* Theorem: Field r /\ monic p /\ ipoly p ==> AbelianGroup ((PolyModRing r p).prod excluding |0|) *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group ((PolyModRing r p).prod excluding |0|)
       True by poly_mod_prod_group.
   (2) poly x /\ poly y ==> (x * y) % p = (y * x) % p
       True by poly_mult_comm.
*)
val poly_mod_prod_nonzero_abelian_group = store_thm(
  "poly_mod_prod_nonzero_abelian_group",
  ``!r:'a field. Field r ==>
   !p. monic p /\ ipoly p ==> AbelianGroup ((PolyModRing r p).prod excluding |0|)``,
  rw_tac std_ss[AbelianGroup_def] >-
  rw[poly_mod_prod_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[poly_mod_ring_def, poly_remainders_def, excluding_def, poly_mult_comm]);

(* Theorem: FiniteField r /\ monic p /\ ipoly p ==> FiniteAbelianGroup ((PolyModRing r p).prod excluding |0|) *)
(* Proof:
   FiniteField r /\ monic z /\ ipoly p ==>
   FiniteField (PolyModRing r p)                                      by poly_mod_irreducible_finite_field
   Hence FiniteGroup ((PolyModRing r p).prod excluding |0|)           by finite_field_alt
   Also  AbelianGroup ((PolyModRing r p).prod excluding |0|)          by poly_mod_prod_nonzero_abelian_group
   Hence FiniteAbelianGroup ((PolyModRing r p).prod excluding |0|)    by FiniteGroup_def
*)
val poly_mod_prod_nonzero_finite_abelian_group = store_thm(
  "poly_mod_prod_nonzero_finite_abelian_group",
  ``!r:'a field. FiniteField r ==>
   !p. monic p /\ ipoly p ==> FiniteAbelianGroup ((PolyModRing r p).prod excluding |0|)``,
  rpt strip_tac >>
  `FiniteField (PolyModRing r p)` by rw[poly_mod_irreducible_finite_field] >>
  `(PolyModRing r p).sum.id = |0|` by rw[poly_mod_ring_property] >>
  `FiniteGroup ((PolyModRing r p).prod excluding |0|)` by metis_tac[finite_field_alt] >>
  `AbelianGroup ((PolyModRing r p).prod excluding |0|)` by metis_tac[poly_mod_prod_nonzero_abelian_group, FiniteField_def] >>
  metis_tac[FiniteAbelianGroup_def, FiniteGroup_def]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials of Quotient Field                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Lifting of Elements from Field r to (PolyRing r)                          *)
(* ------------------------------------------------------------------------- *)

(* Name the element function involved in lifting polynomials *)
val _ = overload_on("up", ``\e. if e = #0 then |0| else [e]``);

(* Theorem: up #0 = |0| *)
(* Proof: by notation. *)
val up_zero = store_thm(
  "up_zero",
  ``!r:'a ring. up #0 = |0|``,
  rw[]);

(* Theorem: #1 <> #0 ==> (up #1 = |1|) *)
(* Proof: by notation. *)
val up_one = store_thm(
  "up_one",
  ``!r:'a ring. #1 <> #0 ==> (up #1 = |1|)``,
  rw[poly_one]);

(* Theorem: up x = chop [x] *)
(* Proof:
   If x = #0,
      Note zerop [#0]  by zero_poly_element_zero
        chop [#0]
      = []             by poly_chop_def
      = up #0          by notation
   If x <> #0,
      Note ~zerop [#0]  by zero_poly_def
        chop [x]
      = [x]::chop []    by poly_chop_def
      = [x]             by poly_chop_of_zero
      = up x            by notation
*)
val up_alt = store_thm(
  "up_alt",
  ``!r:'a ring. !x. up x = chop [x]``,
  rw[]);

(* Note: However, up is not chop; this only shows: up = \x. chop[x] *)
(* Note: up is a function from 'a to 'a poly; but chop is a function from 'a poly to 'a poly. *)

(* Theorem: x IN R ==> poly (up x) *)
(* Proof:
   If x = #0,
      up #0 = |0|         by notation
      so poly |0|         by poly_zero_poly
   If x <> #0,
      up x = [x]          by notation
      so poly [x]         by poly_nonzero_element_poly
*)
val up_poly = store_thm(
  "up_poly",
  ``!r:'a ring. !x. x IN R ==> poly (up x)``,
  metis_tac[poly_zero_poly, poly_nonzero_element_poly]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==> (up (x + y) = (up x) + (up y)) *)
(* Proof:
   Note (x + y) IN R        by ring_add_element
     up (x + y)
   = chop [x + y]           by up_alt
   = chop [x] + chop [y]    by poly_add_const_const
   = (up x) + (up y)        by up_alt
*)
val up_add = store_thm(
  "up_add",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x + y) = (up x) + (up y))``,
  rw_tac std_ss[up_alt, poly_add_const_const, ring_add_element]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==> (up (x * y) = (up x) * (up y)) *)
(* Proof:
   Note (x * y) IN R        by ring_mult_element
     up (x * y)
   = chop [x * y]           by up_alt
   = chop [x] * chop [y]    by poly_mult_const_const
   = (up x) * (up y)        by up_alt
*)
val up_mult = store_thm(
  "up_mult",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x * y) = (up x) * (up y))``,
  rw_tac std_ss[up_alt, poly_mult_const_const, ring_mult_element]);

(* Theorem: Ring r ==> !x. x IN R ==> (up (-x) = - (up x)) *)
(* Proof:
   Note -x IN R       by ring_neg_element
     up (-x)
   = chop [-x]        by up_alt
   = - chop [x]       by poly_neg_const
   = - (up x)         by up_alt
*)
val up_neg = store_thm(
  "up_neg",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (up (-x) = - (up x))``,
  (rw[up_alt] >> rw[up_alt]));

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==> (up (x - y) = (up x) - (up y)) *)
(* Proof:
   Note -y IN R              by ring_neg_element
     up (x - y)
   = up (x + -y)             by ring_sub_def
   = chop [x + -y]           by up_alt, ring_add_element
   = chop [x] + chop [-y]    by poly_add_const_const
   = (up x) + (up (-y))      by up_alt
   = (up x) + - (up y)       by up_neg
   = (up x) - (up y)         by poly_sub_def
*)
val up_sub = store_thm(
  "up_sub",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (up (x - y) = (up x) - (up y))``,
  rpt strip_tac >>
  `-y IN R` by rw[] >>
  `up (x - y) = up (x + -y)` by rw[ring_sub_def] >>
  `_ = chop [x + -y]` by rw[up_alt] >>
  `_ = chop [x] + chop [-y]` by rw[poly_add_const_const] >>
  `_ = (up x) + (up (-y))` by rw_tac std_ss[up_alt] >>
  rw_tac std_ss[up_neg, poly_sub_def]);

(* Theorem: up ##n = chop [##n] *)
(* Proof: by up_alt *)
val up_num = store_thm(
  "up_num",
  ``!r:'a ring. !n. up ##n = chop [##n]``,
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. x IN R ==> !n. up (x ** n) = (up x) ** n *)
(* Proof:
   By induction on n.
   Base: up (x ** 0) = up x ** 0
         up (x ** 0)
       = up #1                  by ring_exp_0
       = |1|                    by up_one
       = (up x) ** 0            by poly_exp_0
   Step: up (x ** n) = up x ** n ==> up (x ** SUC n) = up x ** SUC n
         Note poly (up x)       by up_poly

         up (x ** SUC n)
       = up (x * x ** n)        by ring_exp_SUC
       = (up x) * up (x ** n)   by up_mult
       = (up x) * (up x) ** n   by induction hypothesis
       = (up x) ** SUC n        by poly_exp_SUC
*)
val up_exp = store_thm(
  "up_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. x IN R ==> !n. up (x ** n) = (up x) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  metis_tac[ring_exp_0, up_one, poly_exp_0] >>
  `poly (up x)` by rw[up_poly] >>
  `up (x ** SUC n) = up (x * x ** n)` by rw[] >>
  rw[up_mult]);

(* Theorem: (up x = |0|) <=> (x = #0) *)
(* Proof:
   If part: up x = |0| ==> x = #0
      By contradiction, suppose x <> #0.
      Then up x = [x]      by notation
       But |0| = []        by poly_zero
       and [x] <> []       by NOT_NIL_CONS
       ==> up x <> |0|, a contradiction.
   Only-if part: x = #0 ==> up x = |0|
      True by up_zero
*)
val up_eq_zero = store_thm(
  "up_eq_zero",
  ``!r:'a ring. !x. (up x = |0|) <=> (x = #0)``,
  metis_tac[up_zero, poly_zero, NOT_NIL_CONS]);

(* Theorem: x IN R+ ==> up x <> |0| *)
(* Proof:
   Note x IN R+ ==> x IN R /\ x <> #0   by ring_nonzero_eq
     so up x <> |0|                     by up_eq_zero
*)
val up_nonzero = store_thm(
  "up_nonzero",
  ``!r:'a ring. !x. x IN R+ ==> up x <> |0|``,
  rw[ring_nonzero_eq, up_eq_zero]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. (up x = |1|) <=> (x = #1) *)
(* Proof:
   If part: up x = |1| ==> x = #1
      Since |1| <> |0|    by poly_one_ne_poly_zero
         so x <> #0       by up_eq_zero
        Now up x = [x]    by notation
        and  |1| = [#1]   by poly_one_alt
         so    x = #1     by NOT_EQ_LIST

   Only-if part: x = #1 ==> up x = |1|
      True by up_one
*)
val up_eq_one = store_thm(
  "up_eq_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. (up x = |1|) <=> (x = #1)``,
  rw_tac std_ss[poly_one_alt, EQ_IMP_THM] >>
  `|1| <> |0|` by rw_tac std_ss[GSYM poly_one_ne_poly_zero] >>
  `x <> #0` by metis_tac[up_eq_zero] >>
  `[x] = [#1]` by metis_tac[poly_one_alt] >>
  rw[]);

(* Theorem: (up x = up y) <=> (x = y) *)
(* Proof:
   If part: (up x = up y) ==> (x = y)
      If x = #0,
         up #0 = |0|      by up_zero
               = up y     by given
      Thus y = #0         by up_eq_zero
      If x <> #0,
         Then y <> #0     by up_eq_zero
           up x = up y
      ==>   [x] = [y]     by notation
      ==>     x = y       by NOT_EQ_LIST

   Only-if part: (x = y) ==> (up x = up y)
      This is trivially true.
*)
val up_eq = store_thm(
  "up_eq",
  ``!r:'a ring. !x y. (up x = up y) <=> (x = y)``,
  rw_tac std_ss[poly_zero, EQ_IMP_THM]);

(* Theorem: x IN R ==> (deg (up x) = 0) *)
(* Proof:
   If x = #0,
      Then deg (up #0) = deg |0|    by up_zero
                       = 0          by poly_deg_zero
   If x <> #0,
      Then deg (up x) = deg [x]     by notation
                      = 0           by poly_deg_const
*)
val up_deg = store_thm(
  "up_deg",
  ``!(r:'a ring) x. x IN R ==> (deg (up x) = 0)``,
  rw_tac std_ss[poly_deg_zero, poly_deg_const]);

(* ------------------------------------------------------------------------- *)
(* Lifting Polynomial from F[x] to (F[x] mod z)[y]                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Lift of Polynomials                                                       *)
(* ------------------------------------------------------------------------- *)

(* overload lift of polynomial negation *)
(* val _ = overload_on("|~|", ``(PolyRing (PolyModRing r z)).sum.inv``); *)
(* This is now $-z *)

(* overload lift of polynomial shift *)
(* val _ = overload_on("|>>|", ``poly_shift (PolyModRing r z)``); *)
(* val _ = set_fixity "|>>|" (Infixr 700); (* R-associative *) *)
(* val _ = add_infix("|>>|", 700, HOLgrammars.RIGHT); *)
(* This is now >>z *)

(* overload lift of X *)
(* val _ = overload_on("|X|", ``(lift |1|) |>>| 1``); *)
(* This is now |X| *)

(* Lifting a polynomial *)
val poly_lift_def = Define`
  poly_lift (r:'a ring) (p:'a poly) = MAP up p
`;
val _ = overload_on ("lift", ``poly_lift r``);

(* poly_lift_def:
val it = |- !r p. lift p = MAP (\e. up e) p: thm
*)

(* export simple definition *)
val _ = export_rewrites ["poly_lift_def"];

(* overload on lifted |0| *)
val _ = overload_on ("||0||", ``(PolyRing (PolyRing r)).sum.id``);

(* Theorem: ||0|| = [] *)
(* Proof: by poly_zero. *)
val zero_poly_lift_zero = store_thm(
  "zero_poly_lift_zero",
  ``!r:'a ring. ||0|| = []``,
  rw[]);

(* Theorem: lift |0| = ||0|| *)
(* Proof: by poly_lift_def. *)
val poly_lift_zero = store_thm(
  "poly_lift_zero",
  ``!r:'a ring. lift |0| = ||0||``,
  rw[]);

(* Theorem: lift [] = [] *)
(* Proof: by poly_lift_zero, poly_zero. *)
val poly_lift_of_zero = store_thm(
  "poly_lift_of_zero",
  ``!r:'a ring. lift [] = []``,
  rw[]);

(* Theorem: #1 <> #0 ==> (lift |1| = [|1|]) *)
(* Proof:
     lift |1|
   = lift [#1]        by poly_one_alt
   = MAP up [#1]      by poly_lift_def
   = [[#1]]           by MAP
   = [|1|]            by poly_one_alt
*)
val poly_lift_one = store_thm(
  "poly_lift_one",
  ``!r:'a ring. #1 <> #0 ==> (lift |1| = [|1|])``,
  rw[poly_one_alt]);

(* Theorem: c IN R /\ c <> #0 ==> (lift [c] = [[c]]) *)
(* Proof:
      lift [c]
    = MAP up [c]     by poly_lift_def
    = [[c]]          by MAP
*)
val poly_lift_const = store_thm(
  "poly_lift_const",
  ``!r:'a ring. !c. c IN R /\ c <> #0 ==> (lift [c] = [[c]])``,
  rw[]);

(* Theorem: lift (h::t) = (if h = #0 then |0| else [h])::lift t *)
(* Proof: by poly_lift_def. *)
val poly_lift_cons = store_thm(
  "poly_lift_cons",
  ``!r:'a ring. !h t. lift (h::t) = (if h = #0 then |0| else [h])::lift t``,
  rw[]);

(* Theorem: lift p = ||0|| <=> p = |0| *)
(* Proof:
   If part: lift p = ||0|| <=> p = |0|
     Assume p <> |0|, i.e. p <> []    by poly_zero
     Then p = h::t, and lift p <> []  by MAP
     Contradicting p = ||0|| = []     by zero_poly_lift_zero
   Only-if part: p = |0| ==> lift p = ||0||
     True by poly_lift_zero.
*)
val poly_lift_eq_zero = store_thm(
  "poly_lift_eq_zero",
  ``!r:'a ring. !p. (lift p = ||0||) <=> (p = |0|)``,
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p. (lift p = [|1|]) <=> (p = |1|) *)
(* Proof:
   If part: lift p = [|1|] ==> p = |1|
      Since |1| <> |0|                      by poly_one_ne_poly_zero
         so [|1|] <> [|0|] = ||0||
       thus p <> |0|                        by poly_lift_eq_zero
         or p <> []                         by poly_zero
         or ?h t. p = h::t                  by list_CASES
       and lift p = up h::lift t            by poly_lift_cons
       By equality of lists,
          up h = |1| /\ lift t = [] = |0|   by poly_zero
       so h = #1 /\ t = |0|                 by up_eq_one, poly_lift_eq_zero
       or p = h::t = [#1] = |1|             by poly_one_alt

   Only-if part: p = |1| ==> lift p = [|1|]
      True by poly_lift_one
*)
val poly_lift_eq_one = store_thm(
  "poly_lift_eq_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. (lift p = [|1|]) <=> (p = |1|)``,
  rw_tac std_ss[poly_lift_one, EQ_IMP_THM] >>
  `|1| <> |0|` by rw_tac std_ss[GSYM poly_one_ne_poly_zero] >>
  `[|1|] <> ||0||` by rw[] >>
  `p <> |0|` by metis_tac[poly_lift_eq_zero] >>
  `?h t. p = h::t` by metis_tac[list_CASES, poly_zero] >>
  `lift p = up h::lift t` by rw[GSYM poly_lift_cons] >>
  qabbrev_tac `uh = up h` >>
  qabbrev_tac `lt = lift t` >>
  `[|1|] = uh::lt` by metis_tac[] >>
  `(uh = |1|) /\ (lt = [])` by rw[] >>
  `h = #1` by metis_tac[up_eq_one] >>
  `t = []` by rw[zero_poly_lift_zero, GSYM poly_lift_eq_zero, Abbr`lt`] >>
  rw[poly_one]);

(* Theorem: zerop (lift p) <=> zerop p *)
(* Proof: by induction on p.
   Base case: zero_poly (PolyRing r) (lift []) <=> zerop []
     True by poly_lift_of_zero.
   Step case: zero_poly (PolyRing r) (lift p) <=> zerop p ==>
              !h. zero_poly (PolyRing r) (lift (h::p)) <=> zerop (h::p)
       (PolyRing r) (lift (h::p))
     = (PolyRing r) ((if h = #0 then |0| else [h])::lift p)  by poly_lift_cons
     If h = #0, true by induction hypothesis, zero_poly_of_zero.
     if h <> #0, both sides are F by zero_poly_cons.
*)
val poly_lift_eq_zero_poly = store_thm(
  "poly_lift_eq_zero_poly",
  ``!r:'a ring. !p. zero_poly (PolyRing r) (lift p) <=> (zerop p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_lift_cons, zero_poly_cons, poly_zero]);

(* The following is the reverse of above *)

(* Theorem: zerop p <=> zero_poly (PolyRing r) (lift p) *)
(* Proof:
   By induction on p.
   Base case: zerop [] <=> zero_poly (PolyRing r) (lift [])
        zerop [] <=> T                    by zero_poly_of_zero
        zero_poly (PolyRing r) (lift [])
      = zero_poly (PolyRing r) []         by poly_lift_of_zero
        <=> T                             by zero_poly_of_zero
   Step case: zerop p <=> zero_poly (PolyRing r) (lift p) ==>
              !h. zerop (h::p) <=> zero_poly (PolyRing r) (lift (h::p))
         zerop (h::p)
     <=> h = #0 /\ zerop p                                                by zero_poly_cons
     <=> h = #0 /\ zero_poly (PolyRing r) (lift p)                        by induction hypothesis
     <=> zero_poly (PolyRing r) (if h = #0 then |0| else [h])::(lift p)   by zero_poly_cons
     <=> zero_poly (PolyRing r) (lift (h::p))                             by poly_lift_cons
*)
val poly_lift_zero_poly = store_thm(
  "poly_lift_zero_poly",
  ``!r:'a ring. !p. zerop p <=> zero_poly (PolyRing r) (lift p)``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[]);

(* Theorem: lift (chop p) = poly_chop (PolyRing r) (lift p) *)
(* Proof:
   By induction on p.
   Base case: lift (chop []) = poly_chop (PolyRing r) (lift [])
          lift (chop [])
        = lift []                                 by poly_chop_of_zero
        = []                                      by poly_lift_of_zero
        = poly_chop (PolyRing r) []               by poly_chop_of_zero
        = poly_chop (PolyRing r) (lift [])        by poly_lift_of_zero
   Step case: lift (chop p) = poly_chop (PolyRing r) (lift p) ==>
              lift (chop (h::p)) = poly_chop (PolyRing r) (lift (h::p))
        If zerop (h::p),
           poly_zero (PolyRing r) (lift (h::p))   by poly_lift_zero_poly
           lift (chop (h::p))
         = lift []                                by poly_chop_cons, zerop (h::p)
         = []                                     by poly_lift_of_zero
         = poly_chop (PolyRing r) (lift (h::p))   by poly_chop_cons, poly_lift_cons
        If ~zerop (h::p),
           ~poly_zero (PolyRing r) (lift (h::p))  by poly_lift_zero_poly
        If h <> #0,
          lift (chop (h::p))
        = lift (h::chop p)                        by poly_chop_cons, ~zerop (h::p)
        = [h] :: lift (chop p)                    by poly_lift_cons, h <> #0
        = [h] :: poly_chop (PolyRing r) (lift p)  by induction hypothesis
        = poly_chop (PolyRing r) (lift (h::p))    by poly_chop_cons, poly_lift_cons
        If h = #0, ~zerop p
          lift (chop (h::p))
        = lift (h::chop p)                        by poly_chop_cons, ~zerop (h::p)
        = [] :: lift (chop p)                     by poly_lift_cons, h = #0
        = [] :: poly_chop (PolyRing r) (lift p)   by induction hypothesis
        = poly_chop (PolyRing r) (lift (#0::p))   by poly_chop_cons, poly_lift_cons
*)
val poly_lift_chop = store_thm(
  "poly_lift_chop",
  ``!r:'a ring. !p. lift (chop p) = poly_chop (PolyRing r) (lift p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `zerop (h::p)` >| [
    `zero_poly (PolyRing r) (lift (h::p))` by rw[GSYM poly_lift_zero_poly] >>
    metis_tac[poly_chop_cons, poly_lift_cons, poly_lift_of_zero],
    `~zero_poly (PolyRing r) (lift (h::p))` by rw[GSYM poly_lift_zero_poly] >>
    metis_tac[poly_chop_cons, poly_lift_cons, poly_lift_zero]
  ]);

(* Theorem: poly p ==> Poly (PolyRing r) (lift p) *)
(* Proof: by induction on p.
   Base case: poly [] ==> Poly (PolyRing r) (lift [])
     Since lift [] = []                        by poly_lift_of_zero
     Hence true by zero_poly_poly.
   Step case: poly p ==> Poly (PolyRing r) (lift p) ==>
              !h. poly (h::p) ==> Poly (PolyRing r) (lift (h::p)
     Expanding by definitions,
     if h = #0, to show: []::lift p IN (PolyRing (PolyRing r)).carrier
       Since poly p and ~zerop (#0::p), p <> [].
       Hence lift p <> [],                     by poly_lift_eq_zero
       and  ~zerop (#0::p) ==> ~zerop p        by zero_poly_cons
       Thus ~zerop (lift p)                    by poly_lift_eq_zero_poly
       Hence true                              by poly_cons_poly
     if h <> #0, to show: [h]::lift p IN (PolyRing (PolyRing r)).carrier
       poly [h]                                by poly_nonzero_element_poly
       ~zerop (h::p) ==>
       ~zero_poly (PolyRing r) (lift (h::p))   by poly_lift_eq_zero_poly
       Hence true                              by poly_cons_poly, poly_lift_cons
*)
val poly_lift_poly = store_thm(
  "poly_lift_poly",
  ``!r:'a ring. !p. poly p ==> Poly (PolyRing r) (lift p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly, poly_lift_cons, poly_ring_property] >| [
    `poly p` by rw[poly_ring_property] >>
    `Poly (PolyRing r) ([]::lift p)` suffices_by rw[GSYM poly_ring_property] >>
    `[] IN (PolyRing r).carrier` by rw[poly_ring_element] >>
    rw_tac std_ss[poly_cons_poly] >>
    full_simp_tac std_ss[zero_poly_cons, poly_zero] >>
    rw[poly_lift_eq_zero_poly],
    `poly [h]` by rw[] >>
    `~zero_poly (PolyRing r) (lift (h::p))` by metis_tac[poly_lift_eq_zero_poly] >>
    full_simp_tac std_ss[poly_lift_cons, poly_cons_poly, poly_ring_element] >>
    rw[]
  ]);

(* Theorem: poly_deg (PolyRing r) (lift p) = deg p *)
(* Proof:
   By poly_deg_def, this is to show:
   (1) p <> [] ==> 0 = PRE (LENGTH p), which is F.
       This contradicts MAP f [] = [], by MAP.
   (2) lift [] <> [] ==> PRE (LENGTH (lift [])) = 0, which is F.
       This contradicts MAP f [] = [], by MAP.
   (3) p <> [] ==> PRE (LENGTH (MAP (\e. if e = #0 then |0| else [e]) p)) = PRE (LENGTH p)
       True by LENGTH_MAP.
*)
val poly_lift_deg = store_thm(
  "poly_lift_deg",
  ``!(r:'a ring) p. poly_deg (PolyRing r) (lift p) = deg p``,
  rw[poly_deg_def, poly_lift_def]);

(* Theorem: Ring r ==> !p. poly p ==> poly_eval (PolyRing r) (lift p) X = p *)
(* Proof: by induction on p.
   Base case: poly [] ==> (poly_eval (PolyRing r) (lift []) X = [])
       poly_eval (PolyRing r) (lift []) X
     = poly_eval (PolyRing r) [] X                   by poly_lift_of_zero
     = []                                            by poly_eval_of_zero
   Step case: poly_eval (PolyRing r) (left p) X = p ==>
              !h. poly (h::p) ==> (poly_eval (PolyRing r) (lift (h::p)) X = h::p)
     poly (h::p) ==> h IN R /\ poly p             by poly_cons_poly
     If h = #0, p <> |0|
       (poly_eval (PolyRing r) (lift (h::p)) X
     = (poly_eval (PolyRing r) ( |0|::lift p) X      by poly_lift_cons
     = |0| + poly_eval (PolyRing r) (left p) X * X   by poly_eval_cons
     = |0| + p * X                                   by induction hypothesis
     = |0| + p >> 1                                  by poly_mult_X
     = p >> 1                                        by poly_add_lzero
     = #0::p                                         by poly_shift_1
     If h <> #0,
       (poly_eval (PolyRing r) (lift (h::p)) X
     = (poly_eval (PolyRing r) ([h] :: lift p) X     by poly_lift_cons
     = [h] + poly_eval (PolyRing r) (left p) X * X   by poly_eval_cons
     = [h] + p * X                                   by induction hypothesis
     = [h] + p >> 1                                  by poly_mult_X
     = h::p                                          by poly_cons_eq_add_shift
*)
val poly_eval_lift_poly_by_X = store_thm(
  "poly_eval_lift_poly_by_X",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (poly_eval (PolyRing r) (lift p) X = p)``,
  rpt strip_tac >>
  `poly X` by rw[] >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly, poly_eval_cons, poly_lift_cons] >| [
    `p <> |0|` by metis_tac[zero_poly_cons, zero_poly_of_zero, poly_zero] >>
    rw[poly_mult_X, poly_shift_1],
    rw[poly_mult_X, poly_cons_eq_add_shift]
  ]);

(* Theorem: poly (poly_eval (PolyRing r) (lift p) q) *)
(* Proof:
   Since Ring (PolyRing r)                                           by poly_add_mult_ring
     and q IN (PolyRing r).carrier                                   by poly_ring_property
    also Poly (PolyRing r) (lift p)                                  by poly_lift_poly
   Hence poly_eval (PolyRing r) (lift p) q IN (PolyRing r).carrier   by poly_eval_element
      or poly (poly_eval (PolyRing r) (lift p) q)                    by poly_ring_property
*)
val poly_eval_lift_poly_poly = store_thm(
  "poly_eval_lift_poly_poly",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> poly (poly_eval (PolyRing r) (lift p) q)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw[poly_add_mult_ring] >>
  `q IN (PolyRing r).carrier` by rw[GSYM poly_ring_property] >>
  `Poly (PolyRing r) (lift p)` by rw[poly_lift_poly] >>
  `poly_eval (PolyRing r) (lift p) q IN (PolyRing r).carrier` by rw[poly_eval_element] >>
  rw[poly_ring_property]);

(* Theorem: lift (p - q) = ||0|| ==> p = q *)
(* Proof:
       lift (p - q) = ||0||
   <=> (p - q) = |0|          by poly_lift_eq_zero
   <=> p = q                  by poly_sub_eq_zero
*)
val poly_lift_sub_eq_zero = store_thm(
  "poly_lift_sub_eq_zero",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (lift (p - q) = ||0||) ==> (p = q)``,
  metis_tac[poly_lift_eq_zero, poly_sub_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Lifting of Elements from Field r to (PolyModRing r z)                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN R /\ 0 < deg z ==> (up x) IN Rz *)
(* Proof:
   If x = #0,
      up #0 = |0|          by notation
      Now poly |0|         by poly_zero_poly
      and deg |0| = 0      by poly_deg_zero
      so (up #0) IN Rz     by poly_mod_ring_element
   If x <> #0,
      up x = [x]           by notation
      Now poly [x]         by poly_nonzero_element_poly
      and deg [x] = 0      by poly_deg_const
      so (up x) IN Rz      by poly_mod_ring_element
*)
val up_element = store_thm(
  "up_element",
  ``!r:'a ring. !x z. x IN R /\ 0 < deg z ==> (up x) IN Rz``,
  rw[Once poly_mod_ring_element]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN R ==> (up x = (up x) % z) *)
(* Proof:
   If x = #0,
        (up #0) % z
      = |0| % z          by notation
      = |0|              by poly_zero_mod
      = up #0            by notation
   If x <> #0,
        (up x) % z
      = [x] % z          by notation
      = [x]              by poly_mod_const, x <> #0
      = up x             by notation
*)
val up_mod = store_thm(
  "up_mod",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN R ==> (up x = (up x) % z)``,
  metis_tac[poly_zero_mod, poly_mod_const]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x + y) = (up x) +z (up y)) *)
(* Proof:
   Note (x + y) IN R        by ring_add_element
    and (up x) IN Rz        by up_element
    and (up y) IN Rz        by up_element
     up (x + y)
   = up (x + y) % z         by up_mod
   = ((up x) + (up y)) % z  by up_add
   = (up x) +z (up y)       by poly_mod_ring_add
*)
val up_mod_add = store_thm(
  "up_mod_add",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y. x IN R /\ y IN R ==> (up (x + y) = (up x) +z (up y))``,
  rpt strip_tac >>
  `(up x) IN Rz /\ (up y) IN Rz` by rw_tac std_ss[up_element] >>
  `up (x + y) = up (x + y) % z` by rw_tac std_ss[up_mod, ring_add_element] >>
  metis_tac[up_add, poly_mod_ring_add]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x * y) = (up x) *z (up y)) *)
(* Proof:
   Note (x * y) IN R        by ring_mult_element
    and (up x) IN Rz        by up_element
    and (up y) IN Rz        by up_element
     up (x * y)
   = up (x * y) % z         by up_mod
   = ((up x) * (up y)) % z  by up_mult
   = (up x) *z (up y)       by poly_mod_ring_mult
*)
val up_mod_mult = store_thm(
  "up_mod_mult",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y. x IN R /\ y IN R ==> (up (x * y) = (up x) *z (up y))``,
  rpt strip_tac >>
  `(up x) IN Rz /\ (up y) IN Rz` by rw_tac std_ss[up_element] >>
  `up (x * y) = up (x * y) % z` by rw_tac std_ss[up_mod, ring_mult_element] >>
  metis_tac[up_mult, poly_mod_ring_mult]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN R ==> (up (-x) = $-z (up x)) *)
(* Proof:
   Note -x IN R        by ring_neg_element
    and (up x) IN Rz   by up_element
     up (-x)
   = up (-x) % z       by up_mod
   = (- (up x)) % z    by up_neg
   = $-z (up x)        by poly_mod_ring_neg
*)
val up_mod_neg = store_thm(
  "up_mod_neg",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN R ==> (up (-x) = $-z (up x))``,
  rpt strip_tac >>
  `-x IN R` by rw[] >>
  `(up x) IN Rz` by rw[up_element] >>
  metis_tac[up_mod, up_neg, poly_mod_ring_neg]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN R /\ y IN R ==> (up (x - y) = (up x) -z (up y)) *)
(* Proof:
   Note (x - y) IN R        by ring_sub_element
    and (up x) IN Rz        by up_element
    and (up y) IN Rz        by up_element
     up (x - y)
   = up (x - y) % z         by up_mod
   = ((up x) - (up y)) % z  by up_sub
   = (up x) -z (up y)       by poly_mod_ring_sub
*)
val up_mod_sub = store_thm(
  "up_mod_sub",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y. x IN R /\ y IN R ==> (up (x - y) = (up x) -z (up y))``,
  rpt strip_tac >>
  `(x - y) IN R` by rw[] >>
  `(up x) IN Rz /\ (up y) IN Rz` by metis_tac[up_element] >>
  metis_tac[up_mod, up_sub, poly_mod_ring_sub]);

(* Theorem: Ring r /\ pmonic z ==> !n. up ##n = ##z #1z n *)
(* Proof:
   Note #1 <> #0                 by poly_deg_pos_ring_one_ne_zero, 0 < deg z
    and Ring (PolyModRing r z)   by poly_mod_ring_ring
   By induction on n.
   Base: up (##0) = ##z #1z 0
         up (##0)
       = up (#0)                 by ring_num_0
       = |0|                     by up_zero
       = #0z                     by poly_mod_ring_ids
       = ##z #1z 0               by ring_num_0
   Step: up (##n) = ##z #1z n ==> up (##(SUC n)) = ##z #1z (SUC n)
         up (##(SUC n))
       = up (#1 + ##n)           by ring_num_SUC, Ring r
       = (up #1) +z (up (##n))   by up_mod_add
       = (up #1) +z (##z #1z n)  by induction hypothesis
       = |1| +z (##z #1z n)      by up_one, #1 <> #0
       = #1z +z (##z #1z n)      by poly_mod_ring_ids
       = ##z #1z (SUC n)         by ring_num_SUC, Ring (PolyModRing r z)
*)
val up_num_mod = store_thm(
  "up_num_mod",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !n. up ##n = ##z #1z n``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  Induct_on `n` >-
  rw[poly_mod_ring_ids] >>
  `up (##(SUC n)) = up (#1 + ##n)` by rw[ring_num_SUC] >>
  `_ = (up #1) +z (up (##n))` by rw[up_mod_add] >>
  `_ = (up #1) +z (##z #1z n)` by rw[] >>
  `_ = |1| +z (##z #1z n)` by rw[up_one] >>
  `_ = #1z +z (##z #1z n)` by rw[poly_mod_ring_ids] >>
  `_ = ##z #1z (SUC n)` by rw_tac std_ss[ring_num_SUC] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN R ==> !n. up (x ** n) = (up x) **z n *)
(* Proof:
   Note #1 <> #0            by poly_deg_pos_ring_one_ne_zero, 0 < deg z
   Note (x ** n) IN R       by ring_exp_element
    and (up x) IN Rz        by up_element
     up (x ** n)
   = up (x ** n) % z        by up_mod
   = ((up x) ** n) % z      by up_exp
   = (up x) **z n           by poly_mod_ring_exp
*)
val up_mod_exp = store_thm(
  "up_mod_exp",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x. x IN R ==> !n. up (x ** n) = (up x) **z n``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `x ** n IN R` by rw[] >>
  `(up x) IN Rz` by rw[up_element] >>
  `up (x ** n) = up (x ** n) % z` by rw[up_mod] >>
  `_ = ((up x) ** n) % z` by rw[up_exp] >>
  rw[poly_mod_ring_exp]);

(* Theorem: Field r /\ ipoly z ==> !x. x IN R+ ==> (up ( |/ x) = |/z (up x)) *)
(* Proof:
   Note x IN R+ ==> |/ x IN R+      by field_inv_nonzero
     so x IN R /\ x <> #0           by field_nonzero_eq
    and |/ x IN R /\ |/ x <> #0     by field_nonzero_eq
   Also pmonic z                    by poly_irreducible_pmonic
   Note Field (PolyModRing r z)     by poly_mod_irreducible_field
    and |0| = #0z                   by poly_mod_ring_ids
   Thus (up x) IN Rz /\ (up x) <> #0z        by up_element, up_nonzero
    and up ( |/ x) IN Rz /\ up ( |/ x) <> #0z  by up_element, up_nonzero

        up ( |/ x) *z (up x)
      = up ( |/x * x)               by up_mod_mult
      = up #1                       by ring_mult_linv
      = |1|                         by up_one
      = #1z                         by poly_mod_ring_ids
   Therefore up ( |/ x) = |/z (up x) by field_linv_unique
*)
val up_mod_inv = store_thm(
  "up_mod_inv",
  ``!r:'a field z. Field r /\ ipoly z ==> !x. x IN R+ ==> (up ( |/ x) = |/z (up x))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `x IN R /\ x <> #0` by metis_tac[field_nonzero_eq] >>
  `|/ x IN R /\ |/ x <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `(up x) IN Rz /\ up ( |/ x) IN Rz` by metis_tac[up_element] >>
  `(up x) <> #0z /\ up ( |/ x) <> #0z` by metis_tac[up_eq_zero, poly_mod_ring_ids] >>
  `up ( |/ x) *z (up x) = up ( |/x * x)` by rw[up_mod_mult, field_inv_element] >>
  `_ = up #1` by rw[] >>
  `_ = #1z` by rw[up_one, poly_mod_ring_ids] >>
  metis_tac[field_linv_unique, field_nonzero_eq]);

(* ------------------------------------------------------------------------- *)
(* Lifting of Polynomials to (PolyModRing r z)                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: |0|z = ||0|| *)
(* Proof: by poly_zero, zero_poly_lift_zero *)
val poly_mod_poly_zero = store_thm(
  "poly_mod_poly_zero",
  ``!r:'a ring. !z:'a poly. |0|z = ||0||``,
  rw[]);

(* Theorem: #1 <> #0 /\ 0 < deg z ==> ( |1|z = [|1|]) *)
(* Proof:
     |1|z
   = [#1z]            by poly_one, #1 <> #0
   = [|1|]            by poly_mod_ring_ids, 0 < deg z
*)
val poly_mod_poly_one = store_thm(
  "poly_mod_poly_one",
  ``!r:'a ring. !z:'a poly. #1 <> #0 /\ 0 < deg z ==> ( |1|z = [|1|])``,
  rw[poly_mod_ring_ids, poly_one]);

(* Theorem: !p. zeropz (lift p) <=> zerop p *)
(* Proof: by induction on p.
   Base case: zeropz (lift []) <=> zerop []
     True by poly_lift_of_zero.
   Step case: zeropz (lift p) <=> zerop p ==> !h. zeropz (lift (h::p)) <=> zerop (h::p)
       (PolyModRing r z) (lift (h::p))
     = (PolyModRing r z) ((if h = #0 then |0| else [h])::lift p)  by poly_lift_cons
     If h = #0, true by induction hypothesis, zero_poly_of_zero.
     if h <> #0, both sides are F by zero_poly_cons.
*)
val poly_mod_lift_eq_zero_poly = store_thm(
  "poly_mod_lift_eq_zero_poly",
  ``!r:'a ring. !z. !p. zero_poly (PolyModRing r z) (lift p) <=> zerop p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_lift_cons, zero_poly_cons, poly_zero, poly_mod_ring_property]);

(* Theorem: (lift p = |0|z) <=> (p = |0|) *)
(* Proof:
   Note lift p = ||0|| <=> p = |0|      by poly_lift_eq_zero
    and |0|z = ||0||                    by poly_mod_poly_zero
    The result follows.
*)
val poly_mod_lift_eq_zero = store_thm(
  "poly_mod_lift_eq_zero",
  ``!r:'a ring z:'a poly p. (lift p = |0|z) <=> (p = |0|)``,
  rw[poly_lift_eq_zero, poly_mod_poly_zero]);

(* Theorem: degz (lift p) = deg p *)
(* Proof:
   Split p according to poly_deg_def.
   If p = [],
        degz (lift []])
      = degz (MAP up [])        by notation
      = degz []                 by MAP
      = 0                       by poly_deg_def
      = deg |0|                 by poly_deg_zero
   If p <> [],
      Then lift p <> []         by poly_lift_eq_zero, poly_zero
        degz (lift p)
      = PRE (LENGTH (lift p))   by poly_deg_def, lift p <> []
      = PRE (LENGTH (MAP up p)) by poly_lift_def
      = PRE (LENGTH p)          by LENGTH_MAP
      = deg p                   by poly_deg_def, p <> []
*)
val poly_mod_lift_deg= store_thm(
  "poly_mod_lift_deg",
  ``!r:'a ring. !p. degz (lift p) = deg p``,
  rw[poly_deg_def]);

(* Theorem: Ring r /\ pmonic z ==> !p. leadz (lift p) = up (lead p) *)
(* Proof:
   Split cases of p for poly_lead_alt,
   If p = |0|,
        leadz (lift |0|)
      = leadz ||0||           by poly_lift_zero
      = #0z                   by poly_lead_zero
      = |1|                   by poly_mod_ring_ids
      = up #0                 by up_zero
   If p <> |0|,
      Then p <> []            by poly_zero
       and lift p <> ||0||    by poly_lift_eq_zero
        leadz (lift p)
      = LAST (lift p)         by poly_lead_alt, lift p <> ||0||
      = LAST (MAP up p)       by poly_lift_def
      = up (LAST p)           by LAST_MAP
      = up (lead p)           by poly_lead_alt, p <> |0|
*)
val poly_mod_lift_lead = store_thm(
  "poly_mod_lift_lead",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. leadz (lift p) = up (lead p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[poly_mod_ring_ids] >>
  `p <> []` by metis_tac[poly_zero] >>
  `lift p <> ||0||` by rw[poly_lift_eq_zero] >>
  `leadz (lift p) = LAST (lift p)` by metis_tac[poly_lead_alt, poly_zero] >>
  `_ = LAST (MAP up p)` by rw[poly_lift_def] >>
  `_ = up (LAST p)` by rw[LAST_MAP] >>
  rw[poly_lead_alt]);

(* Theorem: Ring r /\ pmonic z ==> !x. unit x ==> unitz (up x) *)
(* Proof:
   Note Ring (PolyModRing r z)                 by poly_mod_ring_ring, pmonic z
    and x IN R /\ ?y. y IN R /\ (x * y = #1)   by ring_unit_property, unit x
   Note #1 <> #0                               by poly_deg_pos_ring_one_ne_zero, 0 < deg z
   Thus x <> #0 /\ y <> #0                     by ring_mult_lzero, ring_mult_rzero
   By ring_unit_property, this is to show:
   (1) [x] IN Rz, true                         by poly_mod_ring_element
   (2) ?v. v IN Rz /\ [x] *z v = #1z
       Let v = [y],
       Then [y] IN Rz                          by poly_mod_ring_element
           [x] *z [y]
       <=> ([x] * [y]) % z = |1|               by poly_mod_ring_property
       <=> [x * y] % z = |1|                   by poly_mult_const_const, poly_chop_const_nonzero
       <=> [#1] % z = |1|                      by x * y = #1
       <=> |1| % z = |1|                       by poly_one_alt, #1 <> #0
       <=> T                                   by poly_mod_one
*)
val poly_mod_lift_unit = store_thm(
  "poly_mod_lift_unit",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. unit x ==> unitz (up x)``,
  rpt strip_tac >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `x IN R /\ ?y. y IN R /\ (x * y = #1)` by metis_tac[ring_unit_property] >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `x <> #0 /\ y <> #0` by metis_tac[ring_mult_lzero, ring_mult_rzero] >>
  rw_tac std_ss[ring_unit_property] >-
  rw[poly_mod_ring_element] >>
  qexists_tac `[y]` >>
  rw[poly_mod_ring_element, poly_mod_ring_property] >>
  rw[poly_mod_ring_property] >>
  `[x] * [y] = [x * y]` by metis_tac[poly_mult_const_const, poly_chop_const_nonzero, ring_mult_element] >>
  `_ = |1|` by rw[poly_one_alt] >>
  simp[]);

(* Theorem: Ring r /\ pmonic z ==> !p k. lift p 'z k = up (p ' k) *)
(* Proof:
   Let s = PolyModRing r z.
   Split cases of p for poly_coeff_nonzero.
   If p = |0|,
        (lift p) 'z k
      = poly_coeff s (lift |0|) k      by notation
      = poly_coeff s ||0|| k           by poly_lift_zero
      = #0z                            by poly_coeff_zero
      = |0|                            by poly_mod_ring_ids, poly_zero
      = up #0                          by up_zero
      = up ( |0| ' k)                  by poly_coeff_zero
   If p <> |0|,
      Then p <> []                     by poly_zero
       and lift p <> []                by poly_lift_eq_zero, poly_zero
       and degz (lift p) = deg p       by poly_mod_lift_deg
       If deg p < k,
          (lift p) 'z k
        = #0z                          by poly_coeff_nonzero
        = |0|                          by poly_mod_ring_ids, poly_zero
        = up #0                        by up_zero
        = up (p ' k)                   by poly_coeff_nonzero
       If ~(deg p < k),
          Note deg p = PRE (LENGTH p)  by poly_deg_nonzero, p <> |0|
           and LENGTH p <> 0           by LENGTH_NIL, p <> []
          thus k < LENGTH p            by ~(deg p < k

          (lift p) 'z k
        = EL k (lift p)                by poly_coeff_nonzero, lift p <> []
        = EL k (MAP up p)              by poly_lift_def
        = up (EL k p)                  by EL_MAP, k < LENGTH p
        = up (p ' k)                   by poly_coeff_nonzero, p <> []
*)
val poly_mod_lift_coeff = store_thm(
  "poly_mod_lift_coeff",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p k. poly_coeff (PolyModRing r z) (lift p) k = up (p ' k)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[poly_lift_zero, up_zero, poly_mod_ring_ids] >>
  `p <> []` by metis_tac[poly_zero] >>
  `lift p <> ||0||` by rw[poly_lift_eq_zero] >>
  `degz (lift p) = deg p` by rw[poly_mod_lift_deg] >>
  qabbrev_tac `s = PolyModRing r z` >>
  Cases_on `deg p < k` >| [
    `poly_coeff s (lift p) k = #0z` by rw[poly_coeff_nonzero] >>
    `_ = |0|` by rw[poly_mod_ring_ids, poly_zero] >>
    `_ = up #0` by rw[up_zero] >>
    `_ = up (p ' k)` by rw[poly_coeff_nonzero] >>
    rw[],
    `deg p = PRE (LENGTH p)` by rw[poly_deg_nonzero] >>
    `LENGTH p <> 0` by metis_tac[LENGTH_NIL] >>
    `k < LENGTH p` by decide_tac >>
    `poly_coeff s (lift p) k = EL k (lift p)` by rw[poly_coeff_nonzero] >>
    `_ = EL k (MAP up p)` by rw[poly_lift_def] >>
    `_ = up (EL k p)` by rw[EL_MAP] >>
    `_ = up (p ' k)` by rw[poly_coeff_nonzero] >>
    rw[]
  ]);

(* Theorem: weak p /\ 0 < deg z ==> weakz (lift p) *)
(* Proof:
   Let f = (\e. if e = #0 then [] else [e])
   Note !x. x IN R
    ==> f x = [] or f x = [x]             by comparing x with #0
    If x = #0, f x = [],
    ==> poly (f x) /\ deg (f x) < deg z   by zero_poly_poly, poly_deg_of_zero
    If x <> #0, f x = [x],
    ==> poly (f x) /\ deg (f x) < deg z   by poly_nonzero_element_poly, poly_deg_const

       weak p
   <=> EVERY (\x. x IN R) p                              by weak_def_alt
   <=> EVERY (\x. poly x /\ deg x < deg z) (MAP f p)     by EVERY_MONOTONIC_MAP
   <=> weakz p                                           by weak_def_alt
*)
val poly_mod_lift_weak = store_thm(
  "poly_mod_lift_weak",
  ``!r:'a ring z p. weak p /\ 0 < deg z ==> weakz (lift p)``,
  rw[weak_def_alt, poly_mod_ring_element] >>
  qabbrev_tac `f = (\e. if e = #0 then [] else [e])` >>
  `!x. x IN R ==> poly (f x) /\ deg (f x) < deg z` by rw[Abbr`f`] >>
  qabbrev_tac `PP = \x. x IN R` >>
  qabbrev_tac `QQ = \x. poly x /\ deg x < deg z` >>
  `!x. PP x ==> (QQ o f) x` by rw[Abbr`PP`, Abbr`QQ`] >>
  metis_tac[EVERY_MONOTONIC_MAP]);

(* Theorem: Ring r /\ 0 < deg z ==> !p. poly p ==> polyz (lift p) *)
(* Proof:
   Consider cases of p for poly_def_alt.
   If p = |0|,
      Then lift |0| = ||0||           by poly_lift_zero
       and polyz ||0||                by poly_zero_poly
   If p <> |0|,
      or p <> []                      by poly_zero
      Then poly p
       ==> weak p /\ LAST p <> #0     by poly_def_alt, p <> |0|
      Note weak p ==> weakz (lift p)  by poly_mod_lift_weak, 0 < deg z
       and LAST (lift p)
         = LAST (MAP up p)            by poly_lift_def
         = up (LAST p)                by LAST_MAP, p <> []
       Now up (LAST p) <> |0|         by up_eq_zero
        or LAST (lift p) <> #0z       by poly_mod_ring_id
     Hence polyz (lift p)             by poly_def_alt
*)
val poly_mod_lift_poly = store_thm(
  "poly_mod_lift_poly",
  ``!r:'a ring z. Ring r /\ 0 < deg z ==> !p. poly p ==> polyz (lift p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `weak p /\ LAST p <> #0` by metis_tac[poly_def_alt] >>
  `weakz (lift p)` by rw[poly_mod_lift_weak] >>
  `p <> []` by metis_tac[poly_zero] >>
  `LAST (lift p) = up (LAST p)` by rw[poly_lift_def, LAST_MAP] >>
  `LAST (lift p) <> #0z` by metis_tac[up_eq_zero, poly_mod_ring_ids] >>
  rw[poly_def_alt]);

(* Theorem: Ring r /\ pmonic z ==> !p. ulead p ==> Ulead (PolyModRing r z) (lift p) *)
(* Proof:
   This is to show:
   (1) poly p ==> polyz (lift p), true           by poly_mod_lift_poly
   (2) unit (lead p) ==> unitz (leadz (lift p))
       Note leadz (lift p) = up (lead p)         by poly_mod_lift_lead
       Hence true                                by poly_mod_lift_unit
*)
val poly_mod_lift_ulead = store_thm(
  "poly_mod_lift_ulead",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. ulead p ==> Ulead (PolyModRing r z) (lift p)``,
  rpt strip_tac >-
  rw[poly_mod_lift_poly] >>
  metis_tac[poly_mod_lift_lead, poly_mod_lift_unit]);

(* Theorem: Ring r /\ pmonic z ==> !p. pmonic p ==> Pmonic (PolyModRing r z) (lift p) *)
(* Proof:
   This is to show:
   (1) poly p ==> polyz (lift p), true           by poly_mod_lift_poly
   (2) unit (lead p) ==> unitz (leadz (lift p))
       Note leadz (lift p) = up (lead p)         by poly_mod_lift_lead
       Hence true                                by poly_mod_lift_unit
   (3) 0 < deg p ==> 0 < degz (lift p), true     by poly_mod_lift_deg
*)
val poly_mod_lift_pmonic = store_thm(
  "poly_mod_lift_pmonic",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. pmonic p ==> Pmonic (PolyModRing r z) (lift p)``,
  rpt strip_tac >-
  rw[poly_mod_lift_poly] >-
  metis_tac[poly_mod_lift_lead, poly_mod_lift_unit] >>
  rw[poly_mod_lift_deg]);

(* Theorem: Ring r /\ pmonic z ==> !p. monic p ==> monicz (lift p) *)
(* Proof:
   Note #1 <> #0                 by poly_deg_pos_ring_one_ne_zero, 0 < deg z
   By poly_monic_def, this is to show:
   (1) poly p ==> polyz (lift p)
       This is true              by poly_mod_lift_poly, 0 < deg z
   (2) lead p = #1 ==> leadz (lift p) = #1z
         leadz (lift p)
       = up (lead p)             by poly_mod_lift_lead
       = up #1                   by poly_monic_lead
       = |1|                     by up_one, #1 <> #0
       = #1z                     by poly_mod_ring_ids, 0 < deg z
*)
val poly_mod_lift_monic = store_thm(
  "poly_mod_lift_monic",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. monic p ==> monicz (lift p)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  metis_tac[poly_monic_def, poly_mod_lift_poly, poly_mod_lift_lead, up_one, poly_mod_ring_ids, NOT_ZERO]);

(* Theorem: Ring r /\ pmonic z ==> !p. poly p ==> (monic p <=> monicz (lift p)) *)
(* Proof:
   Note #1 <> #0                          by poly_deg_pos_ring_one_ne_zero, 0 < deg z
   If part: monic p ==> monicz (lift p)
      This is true                        by poly_mod_lift_monic, #1 <> #0
   Only-if part: monicz (lift p) ==> monic p
      Note lead (lift p) = up (lead p)    by poly_mod_lift_lead
        so up (lead p) = #1z              by poly_monic_lead
        or up (lead p) = |1|              by poly_mod_ring_ids, 0 < deg z
       ==>      lead p = #1               by up_eq_one, #1 <> #0
     Hence monic p                        by poly_monic_def
*)
val poly_mod_lift_monic_iff = store_thm(
  "poly_mod_lift_monic_iff",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. poly p ==> (monic p <=> monicz (lift p))``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_mod_lift_monic] >>
  metis_tac[poly_mod_lift_lead, poly_monic_def, up_eq_one, poly_mod_ring_ids, NOT_ZERO]);

(* Theorem: Ring r ==> !p z. lift (chop p) = chopz (lift p) *)
(* Proof:
   By induction on p.
   Base: lift (chop []) = chopz (lift [])
          lift (chop [])
        = lift []                 by poly_chop_of_zero
        = []                      by poly_lift_of_zero
        = chopz []                by poly_chop_of_zero
        = chopz (lift [])         by poly_lift_of_zero
   Step: lift (chop p) = chopz (lift p) ==> !h. lift (chop (h::p)) = chopz (lift (h::p))
        If zerop (h::p),
           zeropz (lift (h::p))   by poly_mod_lift_eq_zero_poly
           lift (chop (h::p))
         = lift []                by poly_chop_cons, zerop (h::p)
         = []                     by poly_lift_of_zero
         = chopz (lift (h::p))    by poly_chop_cons, poly_lift_cons
        If ~zerop (h::p),
           ~zeropz (lift (h::p))  by poly_mod_lift_eq_zero_poly
        If h <> #0,
          lift (chop (h::p))
        = lift (h::chop p)        by poly_chop_cons, ~zerop (h::p)
        = [h] :: lift (chop p)    by poly_lift_cons, h <> #0
        = [h] :: chopz (lift p)   by induction hypothesis
        = chopz (lift (h::p))     by poly_chop_cons, poly_lift_cons
        If h = #0, ~zerop p
          lift (chop (h::p))
        = lift (h::chop p)        by poly_chop_cons, ~zerop (h::p)
        = [] :: lift (chop p)     by poly_lift_cons, h = #0
        = [] :: chopz (lift p)    by induction hypothesis
        = chopz (lift (#0::p))    by poly_chop_cons, poly_lift_cons
*)
val poly_mod_lift_chop = store_thm(
  "poly_mod_lift_chop",
  ``!r:'a ring. Ring r ==> !p (z:'a poly). lift (chop p) = chopz (lift p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `zerop (h::p)` >| [
    `zeropz (lift (h::p))` by rw[poly_mod_lift_eq_zero_poly] >>
    metis_tac[poly_chop_cons, poly_lift_cons, poly_lift_of_zero],
    `~zeropz (lift (h::p))` by rw[poly_mod_lift_eq_zero_poly] >>
    metis_tac[poly_chop_cons, poly_lift_cons, poly_lift_zero]
  ]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. weak p /\ weak q ==> (lift (p || q) = (lift p) ||z (lift q)) *)
(* Proof:
   By induction on p.
   Base: lift ([] || q) = lift [] ||z lift q
       LHS = lift ([] || q)
           = lift q                    by weak_add_of_lzero
       RHS = lift [] ||z lift q
           = [] ||z lift q             by poly_lift_of_zero
           = lift q                    by weak_add_of_lzero
   Step: weak (h::p) /\ weak q /\ 0 < deg z ==> (lift ((h::p) || q) = lift (h::p) ||z lift q)
        By induction on q.
        Base: weak [] ==> (lift ((h::p) || []) = lift (h::p) ||z lift [])
           LHS = lift ((h::p) || [])
               = lift (h::p)                    by weak_add_of_rzero
           RHS = lift (h::p) ||z lift []
               = lift (h::p) ||z []             by poly_lift_of_zero
               = lift (h::p)                    by weak_add_of_rzero
        Step: weak (h'::q) ==> (lift ((h::p) || (h'::q)) = lift (h::p) ||z lift (h'::q))
           Note weak (h::p) ==> h IN R /\ weak p          by weak_cons
            and weak (h'::q) ==> h' IN R /\ weak q        by weak_cons
             lift ((h::p) || (h'::q))
           = lift (h + h' :: (p || q))                    by weak_add_cons
           = up (h + h') :: lift (p || q)                 by poly_lift_cons
           = up (h + h') :: (lift p) ||z (lift q)         by induction hypothesis
           = (up h) +z (up h') :: (lift p) ||z (lift q)   by up_mod_add
           = (up h:: lift p) ||z (up h':: lift q)         by weak_add_cons
           = lift (h::p) ||z lift (h'::q)                 by poly_lift_cons
*)
val poly_mod_lift_weak_add = store_thm(
  "poly_mod_lift_weak_add",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. weak p /\ weak q ==> (lift (p || q) = (lift p) ||z (lift q))``,
  ntac 4 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Induct_on `q` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `lift ((h::p) || (h'::q)) = lift (h + h' :: (p || q))` by rw[] >>
  `_ = up (h + h') :: lift (p || q)` by rw[poly_lift_cons] >>
  `_ = up (h + h') :: (lift p) ||z (lift q)` by rw[] >>
  `_ = (up h) +z (up h') :: (lift p) ||z (lift q)` by rw[up_mod_add] >>
  `_ = (up h:: lift p) ||z (up h':: lift q)` by rw[] >>
  `_ = lift (h::p) ||z lift (h'::q)` by rw[poly_lift_cons] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. poly p /\ poly q ==> (lift (p + q) = (lift p) +z (lift q)) *)
(* Proof:
     lift (p + q)
   = lift (chop (p || q))            by poly_add_def
   = chopz (lift (p || q))           by poly_mod_lift_chop
   = chopz ((lift p) ||z (lift q))   by poly_mod_lift_weak_add
   = (lift p) +z (lift q)            by poly_add_def
*)
val poly_mod_lift_poly_add = store_thm(
  "poly_mod_lift_poly_add",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. poly p /\ poly q ==> (lift (p + q) = (lift p) +z (lift q))``,
  metis_tac[poly_mod_lift_chop, poly_mod_lift_weak_add, poly_is_weak, poly_add_def]);

(* Theorem: Ring r /\ pmonic z ==> !p. weak p ==> (lift (neg p) = negz (lift p)) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (lift (neg []) = negz (lift []))
        lift (neg [])
      = lift []                      by weak_neg_of_zero
      = []                           by poly_lift_of_zero
      = negz []                      by weak_neg_of_zero
      = negz (lift [])               by poly_lift_of_zero
   Step: weak p ==> (lift (neg p) = negz (lift p)) ==>
        !h. weak (h::p) ==> (lift (neg (h::p)) = negz (lift (h::p)))
     Note h IN R /\ weak p           by weak_cons
       lift (neg (h::p))
     = MAP up (neg (h::p))           by poly_lift_def
     = MAP up (-h::neg p)            by weak_neg_def
     = up (-h) :: MAP up (neg p)     by MAP
     = up (-h) :: lift (neg p)       by poly_lift_def
     = up (-h) :: negz (lift p)      by induction hypothesis
     = $-z (up h) :: negz (lift p)   by up_mod_neg
     = negz (up h:: lift p)          by weak_neg_def
     = negz (lift (h::p))            by poly_lift_cons
*)
val poly_mod_lift_weak_neg = store_thm(
  "poly_mod_lift_weak_neg",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. weak p ==> (lift (neg p) = negz (lift p))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `lift (neg (h::p)) = MAP up (neg (h::p))` by rw_tac std_ss[poly_lift_def] >>
  `_ = MAP up (-h::neg p)` by rw_tac std_ss[weak_neg_def] >>
  `_ = up (-h) :: MAP up (neg p)` by rw[] >>
  `_ = up (-h) :: lift (neg p)` by rw_tac std_ss[GSYM poly_lift_def] >>
  `_ = up (-h) :: negz (lift p)` by rw[] >>
  `_ = $-z (up h) :: negz (lift p)` by rw[up_mod_neg] >>
  `_ = negz (up h:: lift p)` by rw[weak_neg_def] >>
  `_ = negz (lift (h::p))` by rw[poly_lift_cons] >>
  rw[]);

(* Note:
poly_mod_lift_poly  |- !r z. Ring r /\ pmonic z ==> !p. poly p ==> polyz (lift p)
poly_lift_mod_poly  |- !r. Ring r ==> !p z. poly p /\ pmonic z ==> polyz (lift p)
*)

(* Theorem: Ring r /\ pmonic z ==> !p. poly p ==> (lift (- p) = $-z (lift p)) *)
(* Proof:
   Note poly p ==> polyz (lift p)   by poly_mod_lift_poly
    and Ring (PolyModRing r z)      by poly_mod_ring_ring

     lift (-p)
   = lift (neg p)    by poly_neg_def
   = negz (lift p)   by poly_mod_lift_weak_neg
   = $-z (lift p)    by poly_neg_def, polyz (lift p)
*)
val poly_mod_lift_poly_neg = store_thm(
  "poly_mod_lift_poly_neg",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. poly p ==> (lift (- p) = $-z (lift p))``,
  rpt strip_tac >>
  `polyz (lift p)` by rw[poly_mod_lift_poly] >>
  `lift (-p) = lift (neg p)` by rw[poly_neg_def] >>
  `_ = negz (lift p)` by rw[poly_mod_lift_weak_neg] >>
  `_ = $-z (lift p)` by rw[poly_mod_ring_ring, poly_neg_def] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. poly p /\ poly q ==> (lift (p - q) = (lift p) -z (lift q)) *)
(* Proof:
   Note poly (-q)                 by poly_neg_poly
     lift (p - q)
   = lift (p + -q)                by poly_sub_def
   = (lift p) +z (lift (-q))      by poly_mod_lift_poly_add
   = (lift p) +z ($-z (lift q))   by poly_mod_lift_poly_neg
   = (lift p) -z (lift q)         by poly_sub_def
*)
val poly_mod_lift_poly_sub = store_thm(
  "poly_mod_lift_poly_sub",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. poly p /\ poly q ==> (lift (p - q) = (lift p) -z (lift q))``,
  rpt strip_tac >>
  `lift (p - q) = lift (p + -q)` by rw[poly_sub_def] >>
  `_ = (lift p) +z (lift (-q))` by rw[poly_mod_lift_poly_add] >>
  `_ = (lift p) +z ($-z (lift q))` by rw_tac std_ss[GSYM poly_mod_lift_poly_neg] >>
  `_ = (lift p) -z (lift q)` by rw_tac std_ss[poly_sub_def] >>
  rw_tac std_ss[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p c. weak p /\ c IN R ==> (lift (c o p) = (up c) oz (lift p)) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (lift (c o []) = up c oz lift [])
        lift (c o [])
      = lift []                by weak_cmult_of_zero
      = |0|                    by poly_lift_of_zero
      = (up c) oz |0|          by weak_cmult_zero
      = (up c) oz (lift [])    by poly_lift_of_zero
   Step: weak p ==> (lift (c o p) = up c oz lift p) ==>
         !h. weak (h::p) ==> (lift (c o (h::p)) = up c oz lift (h::p))
      Note weak (h::p) ==> h IN R /\ weak p      by weak_cons
        lift (c o (h::p))
      = lift (c * h :: c o p)                    by weak_cmult_cons
      = up (c * h) :: lift (c o p)               by poly_lift_cons
      = up (c * h) :: (up c) oz (lift p)         by induction hypothesis
      = (up c) *z (up h) :: (up c) oz (lift p)   by up_mod_mult
      = (up c) oz (up h :: lift p)               by weak_cmult_cons
      = up c oz lift (h::p)                      by poly_lift_cons
*)
val poly_mod_lift_weak_cmult = store_thm(
  "poly_mod_lift_weak_cmult",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p c. weak p /\ c IN R ==> (lift (c o p) = (up c) oz (lift p))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  `h IN R /\ weak p` by metis_tac[weak_cons] >>
  `lift (c o (h::p)) = lift (c * h :: c o p)` by rw[weak_cmult_cons] >>
  `_ = up (c * h) :: lift (c o p)` by rw[poly_lift_cons] >>
  `_ = up (c * h) :: (up c) oz (lift p)` by rw[] >>
  `_ = (up c) *z (up h) :: (up c) oz (lift p)` by rw[up_mod_mult] >>
  `_ = (up c) oz (up h :: lift p)` by rw[weak_cmult_cons] >>
  `_ = up c oz lift (h::p)` by rw[poly_lift_cons] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p c. poly p /\ c IN R ==> (lift (c * p) = (up c) *z (lift p)) *)
(* Proof:
   Note weak p                    by poly_is_weak
     lift (c * p)
   = lift (chop (c o p))          by poly_cmult_def
   = chopz (lift (c o p))         by poly_mod_lift_chop
   = chopz ((up c) oz (lift p))   by poly_mod_lift_weak_cmult
   = (up c) *z (lift p)           by poly_cmult_def
*)
val poly_mod_lift_poly_cmult = store_thm(
  "poly_mod_lift_poly_cmult",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p c. poly p /\ c IN R ==> (lift (c * p) = (up c) *z (lift p))``,
  rpt strip_tac >>
  `lift (c * p) = lift (chop (c o p))` by rw_tac std_ss[poly_cmult_def] >>
  `_ = chopz (lift (c o p))` by rw[poly_mod_lift_chop] >>
  `_ = chopz ((up c) oz (lift p))` by metis_tac[poly_mod_lift_weak_cmult, poly_is_weak] >>
  `_ = (up c) *z (lift p)` by rw_tac std_ss[poly_cmult_def] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==> !p n. lift (p >> n) = (lift p) >>z n *)
(* Proof:
   Split cases for poly_shift_suc.
   If p = |0|,
        lift ( |0| >> n)
      = lift |0|                by poly_shift_zero
      = ||0||                   by poly_lift_zero
      = ( ||0||) >>z n          by poly_shift_zero
      = (lift |0|) >>z n        by poly_lift_zero
   If p <> |0|,
   By induction on n.
   Base: lift (p >> 0) = lift p >>z 0
        lift (p >> 0)
      = lift p                  by shift_0
      = (lift p) >>z 0          by shift_0
   Step: lift (p >> n) = lift p >>z n ==> lift (p >> SUC n) = lift p >>z SUC n
      Note p <> |0|
       ==> lift p <> ||0||      by poly_lift_eq_zero
        lift (p >> SUC n)
      = lift (#0:: p >> n)      by poly_shift_suc
      = up #0 :: lift (p >> n)  by poly_lift_cons
      = up #0 :: lift p >>z n   by induction hypothesis
      = |0| :: lift p >>z n     by up_zero
      = (lift p) >>z (SUC n)    by poly_shift_suc
*)
val poly_mod_lift_poly_shift = store_thm(
  "poly_mod_lift_poly_shift",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p n. lift (p >> n) = (lift p) >>z n``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Induct_on `n` >-
  rw[] >>
  `lift p <> ||0||` by rw[poly_lift_eq_zero] >>
  `lift (p >> SUC n) = lift (#0:: p >> n)` by rw[poly_shift_suc] >>
  `_ = up #0 :: lift (p >> n)` by rw[poly_lift_cons] >>
  `_ = up #0 :: lift p >>z n` by rw[] >>
  `_ = |0| :: lift p >>z n` by rw[up_zero] >>
  `_ = (lift p) >>z (SUC n)` by metis_tac[poly_shift_suc, poly_mod_ring_ids, poly_zero] >>
  rw[]);

(* Theorem: poly p ==> (lift p) IN RRz *)
(* Proof:
   Since Ring (PolyModRing r z)     by poly_mod_ring_ring, pmonic z
     and polyz (lift p)             by poly_mod_lift_poly, pmonic z
   Hence (lift p) IN RRz            by poly_ring_property
*)
val poly_mod_lift_element = store_thm(
  "poly_mod_lift_element",
  ``!(r:'a ring) z. Ring r /\ pmonic z ==> !p. poly p ==> (lift p) IN RRz``,
  rw[poly_mod_ring_ring, poly_mod_lift_poly, GSYM poly_ring_property]);

(* Theorem: |0|z = lift |0| *)
(* Proof:
     |0|z
   = []                       by poly_zero |> GEN_ALL |> SPEC ``t:'a ring``;
   = lift []                  by poly_lift_of_zero
   = lift |0|                 by poly_zero
*)
val poly_mod_lift_zero = store_thm(
  "poly_mod_lift_zero",
  ``!(r:'a ring) (z:'a poly). |0|z = lift |0|``,
  rw[]);

(* Theorem: |0|z = ||0|| *)
(* Proof:
     |0|z
   = lift |0|                 by poly_mod_lift_zero
   = ||0||                    by poly_lift_zero
*)
val poly_mod_ring_zero = store_thm(
  "poly_mod_ring_zero",
  ``!(r:'a ring) (z:'a poly). |0|z = ||0||``,
  rw[]);

(* Note:
   ||0|| = (PolyRing (PolyRing r)).sum.id
   ||1|| is not defined, no use for (PolyRing (PolyRing r)).prod.id
   See lifting above.
*)

(* Theorem: |1|z = lift |1| *)
(* Proof:
   Note (PolyModRing r z).sum.id = |0|      by poly_mod_ring_ids
        (PolyModRing r z).prod.id = |1|     by poly_mod_ring_ids, 0 < deg z
   If #1 = #0, |1| = |0|                    by poly_one_eq_poly_zero
     |1|z
   = []                                     by poly_one |> GEN_ALL |> SPEC ``t:'a ring``
   = lift []                                by poly_lift_of_zero
   = lift |0|                               by poly_zero
   = lift |1|                               by above
   If #1 <> #0, |1| <> |0|                  by poly_one_eq_poly_zero
     |1|z
   = [(PolyModRing r z).prod.id]            by poly_one |> GEN_ALL |> SPEC ``t:'a ring``
   = [|1|]                                  by poly_mod_ring_ids, 0 < deg z
   = lift |1|                               by poly_lift_cons, poly_lift_of_zero
*)
val poly_mod_lift_one = store_thm(
  "poly_mod_lift_one",
  ``!(r:'a ring) (z:'a poly). 0 < deg z ==> ( |1|z = lift |1|)``,
  rw[poly_one, poly_mod_ring_ids] >-
  metis_tac[poly_one_ne_zero] >>
  metis_tac[]);

(* Theorem: Ring r /\ pmonic z ==> (lift X = |X|) *)
(* Proof:
    lift X
  = lift ( |1| >> 1)     by notation
  = (lift |1|) >>z 1     by poly_mod_lift_poly_shift, pmonic z
  = |1|z >>z 1           by poly_mod_lift_one
  = |X|                  by notation
*)
val poly_mod_lift_X = store_thm(
  "poly_mod_lift_X",
  ``!r:'a ring z. Ring r /\ pmonic z ==> (lift X = |X|)``,
  rw_tac std_ss[poly_mod_lift_poly_shift, poly_mod_lift_one]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. weak p /\ weak q ==> (lift (p o q) = (lift p) oz (lift q)) *)
(* Proof:
   By induction on p.
   Base: lift ([] o q) = lift [] oz lift q
        lift ([] o q)
      = lift []                        by weak_mult_of_lzero
      = ||0||                          by poly_lift_zero
      = ||0|| oz lift q                by weak_mult_of_lzero
      = lift [] oz lift q              by poly_lift_zero
   Step: !q. weak p /\ weak q ==> (lift (p o q) = lift p oz lift q) ==>
         !h q. weak (h::p) /\ weak q ==> (lift ((h::p) o q) = lift (h::p) oz lift q)
      Note weak (h::p) ==> h IN R /\ weak p    by weak_cons
       and weak (h o q)                by weak_cmult_weak
       and weak (p o q)                by weak_mult_weak
       and weak (p o q >> 1)           by poly_shift_weak

        lift ((h::p) o q)
      = lift (h o q || p o q >> 1)     by weak_mult_cons
      = (lift (h o q)) ||z (lift (p o q >> 1))               by poly_mod_lift_weak_add
      = ((up h) oz (lift q)) ||z (lift (p o q >> 1))         by poly_mod_lift_weak_cmult
      = ((up h) oz (lift q)) ||z (lift (p o q) >>z 1)        by poly_mod_lift_poly_shift
      = ((up h) oz (lift q)) ||z ((lift p oz lift q) >>z 1)  by induction hypothesis
      = (up h:: lift p) oz (lift q)    by weak_mult_cons
      = (lift (h::p)) oz (lift q)      by poly_lift_cons
*)
val poly_mod_lift_weak_mult = store_thm(
  "poly_mod_lift_weak_mult",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. weak p /\ weak q ==> (lift (p o q) = (lift p) oz (lift q))``,
  ntac 4 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h o q)` by rw[] >>
  `weak (p o q)` by rw[] >>
  `weak (p o q >> 1)` by rw[] >>
  `lift ((h::p) o q) = lift (h o q || p o q >> 1)` by rw[weak_mult_cons] >>
  `_ = (lift (h o q)) ||z (lift (p o q >> 1))` by rw[poly_mod_lift_weak_add] >>
  `_ = ((up h) oz (lift q)) ||z (lift (p o q >> 1))` by metis_tac[poly_mod_lift_weak_cmult] >>
  `_ = ((up h) oz (lift q)) ||z (lift (p o q) >>z 1)` by metis_tac[poly_mod_lift_poly_shift] >>
  `_ = ((up h) oz (lift q)) ||z ((lift p oz lift q) >>z 1)` by rw[] >>
  `_ = (up h:: lift p) oz (lift q)` by rw[weak_mult_cons] >>
  `_ = (lift (h::p)) oz (lift q)` by rw[poly_lift_cons] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. poly p /\ poly q ==> (lift (p * q) = (lift p) *z (lift q)) *)
(* Proof:
   Note weak p, weak q              by poly_is_weak
     lift (p * q)
   = lift (chop (p o q))            by poly_mult_def
   = chopz (lift (p o q))           by poly_mod_lift_chop
   = chopz ((lift p) oz (lift q))   by poly_mod_lift_weak_mult
   = (lift p) *z (lift q)           by poly_mult_def
*)
val poly_mod_lift_poly_mult = store_thm(
  "poly_mod_lift_poly_mult",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. poly p /\ poly q ==> (lift (p * q) = (lift p) *z (lift q))``,
  rpt strip_tac >>
  `lift (p * q) = lift (chop (p o q))` by rw_tac std_ss[poly_mult_def] >>
  `_ = chopz (lift (p o q))` by rw[poly_mod_lift_chop] >>
  `_ = chopz ((lift p) oz (lift q))` by metis_tac[poly_mod_lift_weak_mult, poly_is_weak] >>
  `_ = (lift p) *z (lift q)` by rw_tac std_ss[poly_mult_def] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==> !p. poly p ==> !n. lift (p ** n) = (lift p) **z n *)
(* Proof:
   Note #1 <> #0                     by poly_deg_pos_ring_one_ne_zero, 0 < deg z
   By induction on n.
   Base: lift (p ** 0) = lift p **z 0
         lift (p ** 0)
       = lift |1|                    by poly_exp_0
       = [|1|]                       by poly_lift_one
       = [#1z]                       by poly_mod_ring_ids
       = (lift p) **z 0              by poly_exp_0, poly_one_alt
   Step: lift (p ** n) = lift p **z n ==> lift (p ** SUC n) = lift p **z SUC n
      Note polyz (lift p)            by poly_mod_lift_poly
        lift (p ** SUC n)
      = lift (p * p ** n)            by poly_exp_SUC
      = (lift p) *z (lift (p ** n))  by poly_mod_lift_poly_mult
      = (lift p) *z (lift p **z n)   by induction hypothesis
      = lift p **z SUC n             by poly_exp_SUC
*)
val poly_mod_lift_poly_exp = store_thm(
  "poly_mod_lift_poly_exp",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. poly p ==> !n. lift (p ** n) = (lift p) **z n``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  Induct_on `n` >-
  rw[poly_lift_one, poly_mod_ring_ids, poly_one_alt] >>
  `lift (p ** SUC n) = lift (p * p ** n)` by rw[poly_exp_SUC] >>
  `_ = (lift p) *z (lift (p ** n))` by rw[poly_mod_lift_poly_mult] >>
  `_ = (lift p) *z (lift p **z n)` by rw[] >>
  `_ = lift p **z SUC n` by rw[poly_exp_SUC] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==> !n. lift (unity n) = unityz n *)
(* Proof:
     lift (unity n)
   = lift (X ** n - |1|)             by notation
   = lift (X ** n) -z (lift |1|)     by poly_mod_lift_poly_sub, pmonic z
   = lift (X ** n) -z |1|z           by poly_mod_lift_one
   = (lift X) **z n -z (lift |1|)    by poly_mod_lift_poly_exp
   = ( |X| **z n) -z |1|z            by poly_mod_lift_X
   = unityz n                        by notation
*)
val poly_mod_lift_unity = store_thm(
  "poly_mod_lift_unity",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !n. lift (unity n) = unityz n``,
  rpt strip_tac >>
  `lift (unity n) = lift (X ** n) -z (lift |1|)` by rw[poly_mod_lift_poly_sub] >>
  `_ = lift (X ** n) -z |1|z` by rw[poly_mod_lift_one] >>
  `_ = (lift X) **z n -z |1|z` by rw[GSYM poly_mod_lift_poly_exp] >>
  `_ = ( |X| **z n) -z |1|z` by rw[GSYM poly_mod_lift_X] >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==>
            !p q. poly p /\ poly q /\ p pdivides q ==> (lift p) pdividesz (lift q) *)
(* Proof:
         p pdivides q
     <=> !t. poly t /\ (q = t * p)      by poly_divides_def
     Now poly p ==> polyz (lift p)      by poly_mod_lift_poly
     and poly q ==> polyz (lift q)      by poly_mod_lift_poly
     and poly t ==> polyz (lift t)      by poly_mod_lift_poly
    Also lift q
       = lift (t * p)                   by above
       = (lift t) *z (lift p)           by poly_mod_lift_poly_mult
   Hence (lift p) pdividesz (lift q)    by poly_divides_def
*)
val poly_mod_lift_poly_divides = store_thm(
  "poly_mod_lift_poly_divides",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. poly p /\ poly q /\ p pdivides q ==> (lift p) pdividesz (lift q)``,
  metis_tac[poly_divides_def, poly_mod_lift_poly, poly_mod_lift_poly_mult]);

(* Theorem: poly p /\ pmonic z ==> polyz (lift (p % z)) *)
(* Proof
   poly p ==> poly (p % z)  by poly_mod_poly
   polyz (lift (p % z))     by poly_mod_lift_poly
*)
val poly_mod_lift_mod_poly = store_thm(
  "poly_mod_lift_mod_poly",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ pmonic z ==> polyz (lift (p % z))``,
  rw[poly_mod_lift_poly]);

(*
poly_mod_unique |> ISPEC ``PolyModRing r z``;
poly_divides_alt |> ISPEC ``PolyModRing r z``;
*)

(* Theorem: Ring r /\ pmonic z ==>
      !p q. pmonic p /\ poly q ==> (p pdivides q <=> lift p pdividesz lift q) *)
(* Proof:
   If part: p pdivides q ==> lift p pdividesz lift q
      This is true                                    by poly_mod_lift_poly_divides
   Only-if part: lift p pdividesz lift q ==> p pdivides q
      Note ?s t. poly s /\ poly t /\
                 (q = s * p + t) /\ deg t < deg p     by poly_division_eqn, pmonic p
       ==> lift q = (lift s *z lift p) +z (lift t)    by poly_mod_lift_poly_add, poly_mod_lift_poly_mult
      Let rz = PolyModRing r z.
      Note Ring rz                                    by poly_mod_ring_ring
       and polyz (lift p) /\ polyz (lift q) /\
           polyz (lift s) /\ polyz (lift t)           by poly_mod_lift_poly
       and degz (lift t) = deg t /\
           degz (lift p) = deg p                      by poly_mod_lift_deg
       and leadz (lift p) = up (lead p)               by poly_mod_lift_lead
       and Unit rz (leadz (lift p))                   by poly_mod_lift_unit
           lift t
         = poly_mod rz (lift q) (lift p)              by poly_mod_unique
         = |0|z                                       by poly_divides_alt
      Thus t = |0|                                    by poly_mod_lift_eq_zero
       ==> q = s * p                                  by t = |0|
       ==> p pdivides q                               by poly_divides_def
*)
val poly_mod_lift_poly_divides_iff = store_thm(
  "poly_mod_lift_poly_divides_iff",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !p q. pmonic p /\ poly q ==> (p pdivides q <=> lift p pdividesz lift q)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_mod_lift_poly_divides] >>
  `?s t. poly s /\ poly t /\ (q = s * p + t) /\ deg t < deg p` by rw[poly_division_eqn] >>
  `lift q = (lift s *z lift p) +z (lift t)` by prove_tac[poly_mod_lift_poly_add, poly_mod_lift_poly_mult, poly_mult_poly] >>
  `Ring (PolyModRing r z)` by rw[poly_mod_ring_ring] >>
  `polyz (lift p) /\ polyz (lift q) /\ polyz (lift s) /\ polyz (lift t)` by rw[poly_mod_lift_poly] >>
  `(degz (lift t) = deg t) /\ (degz (lift p) = deg p)` by rw[poly_mod_lift_deg] >>
  `leadz (lift p) = up (lead p)` by rw[poly_mod_lift_lead] >>
  `unitz (leadz (lift p))` by metis_tac[poly_mod_lift_unit] >>
  `lift t = poly_mod (PolyModRing r z) (lift q) (lift p)` by metis_tac[poly_mod_unique] >>
  `_ = |0|z` by metis_tac[poly_divides_alt] >>
  `t = |0|` by metis_tac[poly_mod_lift_eq_zero] >>
  `q = s * p` by rw[] >>
  metis_tac[poly_divides_def]);

(* Theorem: Ring r /\ pmonic z ==> !p q t. poly p /\ poly q /\ pmonic t ==>
            ((p == q) (pm t) <=> (lift p == lift q) (pmod (PolyModRing r z) (lift t))) *)
(* Proof:
   Let rz = PolyModRing r z.
   Then Ring rz                               by poly_mod_ring_ring
    and pmonicz (lift t)                      by poly_mod_lift_pmonic
    and polyz (lift p) /\ polyz (lift q)      by poly_mod_lift_poly

      (p == q) (pm t)
  <=> t pdivides p - q                        by poly_divides_sub
  <=> lift t pdividesz lift (p - q)           by poly_mod_lift_poly_divides_iff
  <=> lift t pdividesz (lift p -z lift q)     by poly_mod_lift_poly_sub
  <=> (lift p == lift q) (pmod rz (lift t))   by poly_divides_sub
*)
val poly_mod_lift_poly_mod = store_thm(
  "poly_mod_lift_poly_mod",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p q t. poly p /\ poly q /\ pmonic t ==>
      ((p == q) (pm t) <=> (lift p == lift q) (pmod (PolyModRing r z) (lift t)))``,
  rpt strip_tac >>
  qabbrev_tac `rz = PolyModRing r z` >>
  `Ring rz` by rw[poly_mod_ring_ring, Abbr`rz`] >>
  `pmonicz (lift t)` by rw[poly_mod_lift_pmonic, Abbr`rz`] >>
  `polyz (lift p) /\ polyz (lift q)` by rw[poly_mod_lift_poly] >>
  `(p == q) (pm t) <=> t pdivides p - q` by rw[poly_divides_sub] >>
  `_ = (lift t pdividesz lift (p - q))` by rw[poly_mod_lift_poly_divides_iff] >>
  `_ = (lift t pdividesz (lift p -z lift q))` by rw[GSYM poly_mod_lift_poly_sub] >>
  `_ = (lift p == lift q) (pmod rz (lift t))` by metis_tac[poly_divides_sub] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Lifting Theorems                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: peval p q = poly_eval (PolyRing r) (lift p) q *)
(* Proof: by induction on p.
   Base case: poly [] ==> peval [] q = poly_eval (PolyRing r) (lift []) q
     LHS = peval [] q = |0|              by poly_peval_of_zero
     RHS = poly_eval (PolyRing r) (lift []) q
         = poly_eval (PolyRing r) [] q   by poly_lift_of_zero
         = |0| = LHS                     by poly_eval_of_zero
   Step case: poly p ==> peval p q = poly_eval (PolyRing r) (lift p) q ==>
         !h. poly (h::p) ==> peval (h::p) q = poly_eval (PolyRing r) (lift (h::p)) q
     poly (h::p) ==> h IN R /\ poly p                             by poly_cons_poly
     If h = #0,
     LHS = peval (#0::p) q
         = #0 * |1| + peval p q * q                               by poly_peval_cons
         = #0 * |1| + (poly_eval (PolyRing r) (lift p) q) * q     by induction hypothesis
         = |0| + (poly_eval (PolyRing r) (lift p) q) * q          by poly_cmult_lzero
         = (poly_eval (PolyRing r) (lift p) q) * q                by poly_add_lzero
     RHS = poly_eval (PolyRing r) (lift (#0::p)) q
         = poly_eval (PolyRing r) ( |0|::lift p) q                by poly_lift_cons
         = |0| * |1| + (poly_eval (PolyRing r) (lift p) q) * q    by poly_eval_cons
         = |0| + (poly_eval (PolyRing r) (lift p) q) * q          by poly_mult_lzero
         = (poly_eval (PolyRing r) (lift p) q) * q = LHS          by poly_add_lzero
     If h <> #0
     LHS = peval (h::p) q
         = h * |1| + peval p q * q                                by poly_peval_cons
         = h * |1| + (poly_eval (PolyRing r) (lift p) q) * q      by induction hypothesis
         = [h] + (poly_eval (PolyRing r) (lift p) q) * q          by poly_cmult_one, h <> #0
     RHS = poly_eval (PolyRing r) (lift (h::p)) q
         = poly_eval (PolyRing r) ([h]::lift p) q                 by poly_lift_cons
         = [h] * |1| + (poly_eval (PolyRing r) (lift p) q) * q    by poly_eval_cons
         = [h] + (poly_eval (PolyRing r) (lift p) q) * q = LHS    by poly_mult_rone
*)
val poly_peval_alt = store_thm(
  "poly_peval_alt",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (peval p q = poly_eval (PolyRing r) (lift p) q)``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[]);

(* Theorem: Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
            evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z *)
(* Proof: by induction on p.
   Base case: poly [] ==> (evalz (lift []) q = poly_eval (PolyRing r) (lift []) q % z)
   LHS = evalz (lift []) q
       = evalz [] q           by poly_lift_of_zero
       = #0z                  by poly_eval_of_zero
       = |0|                  by poly_mod_ring_ids
   RHS = poly_eval (PolyRing r) (lift []) q % z
       = poly_eval (PolyRing r) [] q % z    by poly_lift_of_zero
       = |0| % z              by poly_eval_of_zero
       = |0| = LHS            by poly_zero_mod
   Step case: !h. poly (h::p) ==> (evalz (lift (h::p)) q = poly_eval (PolyRing r) (lift (h::p)) q % z)
     poly (h::p) ==> h IN R /\ poly p                     by poly_cons_poly
     lift (h::p) = (if h = #0 then |0| else [h])::lift p  by poly_lift_cons
     If h = #0,
    LHS = evalz (lift (#0::p)) q
        = evalz ( |0|::lift p) q  by poly_lift_cons
        = |0| +z ((evalz (lift p) q) *z q              by poly_eval_cons
        = |0| +z ((poly_eval (PolyRing r) (lift p) q) % z) *z q
                                                       by induction hypothesis
        = ( |0| + ((poly_eval (PolyRing r) (lift p) q % z) * q) % z) % z   by poly_mod_ring_property
        = ( |0| + ((t % z) * q) % z) % z               where t = poly_eval (PolyRing r) (lift p) q
        = (((t % z) * q) % z) % z                      by poly_add_lzero
        = ((t % z) * q) % z                            by poly_mod_mod
        = (t % z) * (q % z) % z                        by poly_mod_mult, poly_mod_mod
        = (t * q) % z                                  by poly_mod_mult
    RHS = poly_eval (PolyRing r) (lift (#0::p)) q % z
        = poly_eval (PolyRing r) ( |0|::lift p) q % z  by poly_lift_cons
        = ( |0| + poly_eval (PolyRing r) (lift p) q * q) % z  by poly_eval_cons
        = ( |0| + t * q) % z                           by t above
        = (t * q) % z = LHS                            by poly_add_lzero

     If h <> #0,
    LHS = evalz (lift (h::p)) q
        = evalz ([h]::lift p) q  by poly_lift_cons
        = [h] +z (evalz (lift p) q) *z q               by poly_eval_cons
        = [h] +z ((poly_eval (PolyRing r) (lift p) q) % z) *z q
                                                       by induction hypothesis
        = ([h] + ((poly_eval (PolyRing r) (lift p) q % z) * q) % z) % z   by poly_mod_ring_property
        = ([h] + ((t % z) * q) % z) % z                where t = poly_eval (PolyRing r) (lift p) q
        = ([h] + (t % z) * (q % z) % z) % z            by poly_mod_mult, poly_mod_mod
        = ([h] + (t * q) % z) % z                      by poly_mod_mult
        = ([h] % z + (t * q) % z) % z                  by poly_mod_add, poly_mod_mod
        = ([h] + t * q) % z                            by poly_mod_add
    RHS = poly_eval (PolyRing r) (lift (h::p)) q % z
        = poly_eval (PolyRing r) ([h]::lift p) q % z   by poly_lift_cons
        = ([h] + poly_eval (PolyRing r) (lift p) q * q) % z  by poly_eval_cons
        = ([h] + t * q) % z = LHS                      by t above
*)
val poly_mod_eval_lift_by_poly_eval_lift = store_thm(
  "poly_mod_eval_lift_by_poly_eval_lift",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
     (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z)``,
  rpt strip_tac >>
  Induct_on `p` >| [
    rw[poly_mod_ring_ids] >>
    metis_tac[poly_zero_mod, poly_zero],
    rw_tac std_ss[poly_cons_poly] >>
    `!s t. poly s /\ poly t ==> ((s + ((t % z) * q) % z) % z = (s + t * q) % z)` by
  (rpt strip_tac >>
    `poly (t * q)` by rw[] >>
    `!u. poly u ==> poly (u % z)` by rw[] >>
    `(s + ((t % z) * q) % z) % z = (s + ((t % z) * (q % z)) % z) % z` by metis_tac[poly_mod_mult, poly_mod_mod] >>
    `_ = (s + (t * q) % z) % z` by rw[GSYM poly_mod_mult] >>
    `_ = (s % z + (t * q) % z) % z` by metis_tac[poly_mod_add, poly_mod_mod] >>
    `_ = (s + t * q) % z` by rw[GSYM poly_mod_add] >>
    rw[]) >>
    qabbrev_tac `t = poly_eval (PolyRing r) (lift p) q` >>
    `poly t` by rw[poly_eval_lift_poly_poly, Abbr`t`] >>
    rw_tac std_ss[poly_eval_cons, poly_mod_ring_property, poly_lift_cons] >| [
      `poly |0| /\ deg |0| < deg z` by rw[] >>
      `poly (t % z) /\ deg (t % z) < deg z` by rw[poly_mod_poly, poly_deg_mod_less] >>
      `|0| IN Rz` by rw[poly_mod_ring_property] >>
      `(t % z) IN Rz` by rw[poly_mod_ring_property] >>
      `(t % z) *z q = ((t % z) * q) % z` by rw[poly_mod_ring_property] >>
      `(t % z * q) % z IN Rz` by rw[poly_mod_ring_property, poly_deg_mod_less] >>
      `|0| +z (t % z) *z q = ( |0| + ((t % z) * q) % z) % z` by rw[poly_mod_ring_property] >>
      `poly ((t % z * q) % z) /\ deg ((t % z * q) % z) < deg z` by rw[poly_deg_mod_less] >>
      metis_tac[poly_mod_ring_property],
      `poly [h] /\ deg [h] < deg z` by rw[] >>
      `poly (t % z) /\ deg (t % z) < deg z` by rw[poly_mod_poly, poly_deg_mod_less] >>
      `poly ((t % z * q) % z) /\ deg ((t % z * q) % z) < deg z` by rw[poly_deg_mod_less] >>
      metis_tac[poly_mod_ring_property, NOT_ZERO]
    ]
  ]);

(* Another version with evalz (lift p) (q % z) rather than evalz (lift p) q *)

(*
poly_mod_eval_lift_by_poly_eval_lift;
val it = |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z): thm
*)

(* Theorem: Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
            (evalz (lift p) (q % z) = poly_eval (PolyRing r) (lift p) q % z) *)
(* Proof:
   Let t = q % z
   Then deg t < deg z           by poly_deg_mod_less
    and poly_eval (PolyRing r) (lift p) t % z
      = peval p t % z           by poly_peval_alt
      = (peval p (q % z)) % z   by t = q % z
      = (peval p q) % z         by poly_peval_mod
      = poly_eval (PolyRing r) (lift p) q % z
                                by poly_peval_alt
   The result follows           by poly_mod_eval_lift_by_poly_eval_lift
*)
val poly_mod_eval_lift_by_poly_eval_lift_alt = store_thm(
  "poly_mod_eval_lift_by_poly_eval_lift_alt",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
         (evalz (lift p) (q % z) = poly_eval (PolyRing r) (lift p) q % z)``,
  rpt strip_tac >>
  `poly (q % z) /\ deg (q % z) < deg z` by rw[poly_deg_mod_less] >>
  `(peval p (q % z)) % z = (peval p q) % z` by rw[poly_peval_mod] >>
  rw[poly_mod_eval_lift_by_poly_eval_lift, GSYM poly_peval_alt]);

(* Theorem: Ring r /\ pmonic z ==> !p q z. poly p /\ poly q /\ deg q < deg z ==>
            (rootz (lift p) q <=> (peval p q % z = |0|)) *)
(* Proof:
       rootz (lift p) q
   <=> evalz (lift p) q = |0|                         by poly_root_def
   <=> poly_eval (PolyRing r) (lift p) q % z = |0|    by poly_mod_eval_lift_by_poly_eval_lift
   <=> (peval p q) % z = |0|                          by poly_peval_alt
*)
val poly_mod_lift_root_by_mod_peval = store_thm(
  "poly_mod_lift_root_by_mod_peval",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
               (rootz (lift p) q <=> (peval p q % z = |0|))``,
  rpt strip_tac >>
  `|0| = #0z` by rw[poly_mod_ring_ids] >>
  `rootz (lift p) q <=> (evalz (lift p) q = |0|)` by rw[GSYM poly_root_def] >>
  `_ = ((poly_eval (PolyRing r) (lift p) q) % z = |0|)` by metis_tac[poly_mod_eval_lift_by_poly_eval_lift] >>
  rw[GSYM poly_peval_alt]);

(* Another version with q % z rather than q *)

(*
poly_mod_lift_root_by_mod_peval;
val it = |- !r z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
                (rootz (lift p) q <=> (peval p q % z = |0|)): thm
*)

(* Theorem: Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
            (rootz (lift p) (q % z) <=> (peval p q % z = |0|)) *)
(* Proof:
   Let t = q % z
   Then deg t < deg z           by poly_deg_mod_less
    and (peval p t) % z
      = (peval p (q % z)) % z   by t = q % z
      = (peval p q) % z         by poly_peval_mod
   The result follows           by poly_mod_lift_root_by_mod_peval
*)
val poly_mod_lift_root_by_mod_peval_alt = store_thm(
  "poly_mod_lift_root_by_mod_peval_alt",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p q. poly p /\ poly q ==>
               (rootz (lift p) (q % z) <=> (peval p q % z = |0|))``,
  rpt strip_tac >>
  `poly (q % z) /\ deg (q % z) < deg z` by rw[poly_deg_mod_less] >>
  `(peval p (q % z)) % z = (peval p q) % z` by rw[poly_peval_mod] >>
  rw[poly_mod_lift_root_by_mod_peval]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Root X                                                         *)
(* ------------------------------------------------------------------------- *)

(* These are better *)

(* Theorem: Field r /\ poly z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
            (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z) *)
(* Proof:
   Note 0 < deg z          by deg q < deq z
     so pmonic z           by poly_field_poly_pmonic
   The result follows      by poly_mod_eval_lift_by_poly_eval_lift
*)
val poly_field_mod_eval_lift_by_poly_eval_lift = store_thm(
  "poly_field_mod_eval_lift_by_poly_eval_lift",
  ``!r:'a field z. Field r /\ poly z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
     (evalz (lift p) q = poly_eval (PolyRing r) (lift p) q % z)``,
  rw[poly_mod_eval_lift_by_poly_eval_lift]);

(* Theorem: Field r /\ poly z ==> !p q z. poly p /\ poly q /\ deg q < deg z ==>
            (rootz (lift p) q <=> (peval p q % z = |0|)) *)
(* Proof:
   Note 0 < deg z        by deg q < deq z
     so pmonic z         by poly_field_poly_pmonic
   The result follows    by poly_mod_lift_root_by_mod_peval
*)
val poly_field_mod_lift_root_by_mod_peval = store_thm(
  "poly_field_mod_lift_root_by_mod_peval",
  ``!r:'a field z. Field r /\ poly z ==> !p q. poly p /\ poly q /\ deg q < deg z ==>
               (rootz (lift p) q <=> (peval p q % z = |0|))``,
  rw[poly_mod_lift_root_by_mod_peval]);

(* Theorem: Field r /\ poly z /\ 1 < deg z ==> rootz (lift z) X *)
(* Proof:
   By poly_root_def, this is to show:
   evalz (lift z) X = #0z

     evalz (lift z) X
   = (poly_eval (PolyRing r z) (lift z) X) % z    by poly_field_mod_eval_lift_by_poly_eval_lift
   = z % z                                        by poly_eval_lift_poly_by_X
   = |0|                                          by poly_div_mod_id
   = #0z                                          by poly_mod_ring_ids
*)
val poly_field_mod_lift_has_root_X = store_thm(
  "poly_field_mod_lift_has_root_X",
  ``!r:'a field z. Field r /\ poly z /\ 1 < deg z ==> rootz (lift z) X``,
  rw[poly_root_def, poly_field_mod_eval_lift_by_poly_eval_lift, poly_eval_lift_poly_by_X,
     poly_div_mod_id, poly_mod_ring_property]);

(* Theorem: Field r /\ poly z /\ 1 < deg z ==> ((peval z X) % z = |0|) *)
(* Proof:
   Note rootz (lift z) X        by poly_field_mod_lift_has_root_X
     so (peval z X) % z = |0|   by poly_field_mod_lift_root_by_mod_peval
*)
val poly_field_mod_lift_has_root_X_alt = store_thm(
  "poly_field_mod_lift_has_root_X_alt",
  ``!(r:'a field) z. Field r /\ poly z /\ 1 < deg z ==> ((peval z X) % z = |0|)``,
  rw[poly_field_mod_lift_has_root_X, GSYM poly_field_mod_lift_root_by_mod_peval]);

(* Theorem: Field r /\ ipoly z /\ 1 < deg z ==> rootz (lift z) X *)
(* Proof: by poly_irreducible_pmonic, poly_field_mod_lift_has_root_X *)
val poly_irreducible_lift_has_root_X = store_thm(
  "poly_irreducible_lift_has_root_X",
  ``!(r:'a field) z. Field r /\ ipoly z /\ 1 < deg z ==> rootz (lift z) X``,
  rw[poly_irreducible_pmonic, poly_field_mod_lift_has_root_X]);

(* Theorem: ulead z /\ 1 < deg z ==> !p q. (p % z = q % z) ==> rootz (lift (p - q)) X *)
(* Proof:
   Let d = p - q
       p % z = q % z
   ==> d % z = |0|       by poly_mod_eq
   Hence d = t * z       for some poly t
      or (lift d) = (lift q) * (lift z)
   Since (lift z) has root X by poly_peval_by_X, poly_div_mod_id
         (lift d) also has X as root.
*)
val poly_mod_eq_gives_root_X = store_thm(
  "poly_mod_eq_gives_root_X",
  ``!r:'a ring z. Ring r /\ ulead z /\ 1 < deg z ==>
    !p q. poly p /\ poly q /\ (p % z = q % z) ==> rootz (lift (p - q)) X``,
  rpt strip_tac >>
  `0 < deg z` by decide_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `?d. (d = p - q) /\ poly d` by rw[] >>
  `d % z = |0|` by rw[GSYM poly_mod_eq] >>
  `?t. poly t /\ (d = t * z)` by rw[GSYM poly_mod_eq_zero] >>
  `(peval d X) % z = ((peval t X) * (peval z X)) % z` by rw[poly_peval_mult] >>
  `_ = (((peval t X) % z) * ((peval z X) % z)) % z` by rw[GSYM poly_mod_mult] >>
  `_ = ((t % z) * (z % z)) % z` by rw[poly_peval_by_X] >>
  `_ = ((t % z) * |0|) % z` by metis_tac[poly_div_mod_id] >>
  `_ = |0|` by rw_tac std_ss[poly_mult_rzero, poly_zero_mod, poly_mod_poly] >>
  `poly X /\ (deg X = 1)` by rw[] >>
  metis_tac[poly_mod_lift_root_by_mod_peval]);
(* compare:
poly_field_mod_lift_has_root_X
|- !r z. Field r /\ poly z /\ 1 < deg z ==> rootz (lift z) X
*)

(* Theorem: !n. rootz (lift p) (X ** n % z) <=> (peval p (X ** n) % z = |0|) *)
(* Proof:
   Since poly (X ** n % z)              by poly_X, poly_exp_poly, poly_mod_poly
     and deg (X ** n % z) < deg z       by poly_deg_mod_less
       rootz (lift p) (X ** n % z)
   <=> peval p (X ** n % z) % z = |0|   by poly_mod_lift_root_by_mod_peval
   <=> peval p (X ** n) % z = |0|       by poly_peval_mod
*)
val poly_mod_lift_root_X_exp = store_thm(
  "poly_mod_lift_root_X_exp",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !p. poly p ==>
    !n. rootz (lift p) (X ** n % z) <=> (peval p (X ** n) % z = |0|)``,
  rpt strip_tac >>
  `poly (X ** n % z)` by rw[] >>
  `deg (X ** n % z) < deg z` by rw[poly_deg_mod_less] >>
  rw[poly_mod_lift_root_by_mod_peval, poly_peval_mod]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Order                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: pmonic z ==> (forderz |0| = 0) *)
(* Proof:
   Note #1 <> #0              by poly_deg_pos_ring_one_ne_zero, 0 < deg z
    and ((PolyModRing r z).prod excluding |0|).id = \1|
                              by poly_mod_prod_nonzero_id, 0 < deg
   By order_eq_0, poly_mod_exp_alt,
   this is to show: 0 < n ==> |0| ** n % z <> |1|
   Since n <> 0               by 0 < n
         |0| ** n % z
       = |0| % z              by poly_zero_exp
       = |0|                  by poly_zero_mod
       <> |1|                 by poly_one_eq_poly_zero, #1 <> #0.
*)
val poly_zero_order = store_thm(
  "poly_zero_order",
  ``!r:'a ring z. Ring r /\ pmonic z ==> (forderz |0| = 0)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `poly |0| /\ |0| <> |1|` by metis_tac[poly_zero_poly, GSYM poly_one_eq_poly_zero] >>
  rw_tac std_ss[order_eq_0, poly_mod_prod_nonzero_id, poly_mod_exp_alt] >>
  metis_tac[poly_zero_exp, poly_zero_mod, NOT_ZERO]);

(*
When z = x ** k - |1|, and k = prime, then order ((PolyModRing r z).prod excluding |0|) X = k.
This is because X is a root of (lift h), and x ** k - |1| = q * h   by (z % h = |0|)
Hence peval (x ** k - |1|) X = peval (q * h) X = peval q X * peval h X = |0|
or X is an k-th root of unity, so (order ((PolyModRing r z).prod excluding |0|) X) divides k.
If k is prime, (order ((PolyModRing r z).prod excluding |0|) X) = 1 or k.
But (order ((PolyModRing r z).prod excluding |0|) X) = 1 ==> X = |1|, which is false.
Hence (order ((PolyModRing r z).prod excluding |0|) X) = k.
*)

(* Theorem: FiniteField r /\ ipoly z /\ 1 < deg z ==> 0 < forderz X *)
(* Proof:
   Since  FiniteField (PolyModRing r z)                        by poly_mod_irreducible_finite_field
      so  FiniteGroup ((PolyModRing r z).prod excluding |0|)   by finite_field_alt, poly_mod_ring_property
     Now  X IN (PolyModRing r z).carrier                       by poly_mod_ring_property, poly_X, poly_deg_X
      As  X <> |0|                                             by poly_lead_zero
          X IN ((PolyModRing r z).prod excluding |0|).carrier  by poly_mod_ring_property, excluding_def
    Hence 0 < order ((PolyModRing r z).prod excluding |0|) X   by group_order_pos
*)
val poly_X_order_nonzero = store_thm(
  "poly_X_order_nonzero",
  ``!(r:'a field) z. FiniteField r /\ ipoly z /\ 1 < deg z ==> 0 < forderz X``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0 ` by rw[] >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `FiniteGroup ((PolyModRing r z).prod excluding |0|)` by metis_tac[finite_field_alt, poly_mod_ring_property] >>
  `X IN Rz` by rw[poly_mod_ring_property] >>
  `X IN ((PolyModRing r z).prod excluding |0|).carrier` by rw[poly_mod_ring_property, excluding_def] >>
  rw[group_order_pos]);

(* Theorem: FiniteField r /\ ipoly z /\ 1 < deg z ==> 1 < forderz X *)
(* Proof:
   Since  FiniteField (PolyModRing r z)                        by poly_mod_irreducible_finite_field
      so  FiniteGroup ((PolyModRing r z).prod excluding |0|)   by finite_field_alt, poly_mod_ring_property
     Now  X IN (PolyModRing r z).carrier                       by poly_mod_ring_property, poly_X, poly_deg_X
      As  X <> |0|                                             by poly_lead_zero
          X IN ((PolyModRing r z).prod excluding |0|).carrier  by poly_mod_ring_property, excluding_def
    Hence 0 < forderz X                                        by group_order_pos
    Now, ((PolyModRing r z).prod excluding |0|).id = |1|       by poly_mod_prod_nonzero_id, deg z <> 0
      But X <> |1|                                             by poly_deg_one
       so forderz X <> 1                                       by group_order_eq_1
    Hence 1 < forderz X
*)
val poly_X_order_gt_1 = store_thm(
  "poly_X_order_gt_1",
  ``!(r:'a field) z. FiniteField r /\ ipoly z /\ 1 < deg z ==> 1 < forderz X``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0 ` by rw[] >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `FiniteGroup ((PolyModRing r z).prod excluding |0|)` by metis_tac[finite_field_alt, poly_mod_ring_property] >>
  `X IN Rz` by rw[poly_mod_ring_property] >>
  `X IN ((PolyModRing r z).prod excluding |0|).carrier` by rw[poly_mod_ring_property, excluding_def] >>
  `0 < forderz X` by rw[group_order_pos] >>
  `X <> |1|` by metis_tac[poly_eq_deg_eq, poly_deg_X, poly_deg_one, poly_X, poly_one_poly, DECIDE``0 <> 1``] >>
  `deg z <> 0` by decide_tac >>
  `forderz X <> 1` by metis_tac[group_order_eq_1, poly_mod_prod_nonzero_id, FiniteGroup_def] >>
  decide_tac);

(* Theorem: Field r /\ poly p /\ ipoly z ==> (forderz p = forderz (p % z)) *)
(* Proof:
   First, ((PolyModRing r z).prod excluding |0|).id = |1|   by poly_mod_prod_nonzero_id

   Expand by order_def, period_def, this is to show:
       case OLEAST k. 0 < k /\ (((PolyModRing r z).prod excluding |0|).exp p k = |1|) of ... =
       case OLEAST k. 0 < k /\ (((PolyModRing r z).prod excluding |0|).exp (p % z) k = |1| of ...

   Since
   !k. ((PolyModRing r z).prod excluding |0|).exp p k = (p ** k) % z               by poly_mod_exp_alt
   !k. ((PolyModRing r z).prod excluding |0|).exp (p % z) k = ((p % z) ** k) % z   by poly_mod_exp_alt
   !k. (p ** k) % z = ((p % z) ** k) % z                                           by poly_mod_exp
   The result follows.
*)
val poly_order_eq_poly_mod_order = store_thm(
  "poly_order_eq_poly_mod_order",
  ``!r:'a field z p. Field r /\ ipoly z /\ poly p ==> (forderz p = forderz (p % z))``,
  rpt strip_tac >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  rw[order_def, period_def, poly_mod_exp_alt, poly_mod_exp]);

(* Theorem: poly p /\ ipoly z /\ p % z <> |0| ==> !k. (p ** k == |1|) (pm z) ==> (forderz p) divides k *)
(* Proof:
   Let h = forderz p
         = forderz (p % z)                                   by poly_order_eq_poly_mod_order
   First, #0z = |0|                                          by poly_mod_ring_property
     and  ((PolyModRing r z).prod excluding |0|).id = |1|    by poly_mod_prod_nonzero_id
     Now, Group ((PolyModRing r z).prod excluding |0|)       by poly_mod_prod_group
   Since  deg (p % z) < deg z                                by poly_deg_mod_less
     and  p % z <> |0|                                       by given
          p % z IN ((PolyModRing r z).prod excluding |0|).carrier   by poly_mod_ring_property, excluding_def
   Given  (p ** k == |1|) (pm z)
   means  (p ** k) % z = |1| % z        by pmod_def_alt
                       = |1|            by poly_deg_one, poly_mod_less
   Hence  ((PolyModRing r z).prod excluding |0|).exp (p % z) k
         = (p % z) ** k % z             by poly_mod_exp_alt
         = (p ** k) % z                 by poly_mod_exp
         = |1|                          by above

   Therefore   divides h k              by group_order_condition
*)
val poly_order_divides = store_thm(
  "poly_order_divides",
  ``!r:'a field z. Field r /\ ipoly z ==>
   !p. poly p /\ p % z <> |0| ==> !k. (p ** k == |1|) (pm z) ==> (forderz p) divides k``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  qabbrev_tac `h = forderz p` >>
  `forderz (p % z) = h` by rw_tac std_ss[poly_order_eq_poly_mod_order, Abbr`h`] >>
  `#0z = |0|` by metis_tac[poly_mod_ring_property] >>
  `((PolyModRing r z).prod excluding |0|).id = |1|` by rw[poly_mod_prod_nonzero_id] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[poly_mod_prod_group] >>
  (`p % z IN ((PolyModRing r z).prod excluding |0|).carrier` by (rw[poly_mod_ring_property, excluding_def, poly_deg_mod_less] >> metis_tac[poly_zero])) >>
  `(p ** k) % z = |1|` by metis_tac[pmod_def_alt, poly_one_poly, poly_deg_one, poly_mod_less] >>
  `((PolyModRing r z).prod excluding |0|).exp (p % z) k = ((p % z) ** k) % z` by rw[poly_mod_exp_alt] >>
  `_ = (p ** k) % z` by rw[GSYM poly_mod_exp] >>
  `_ = |1|` by rw[] >>
  metis_tac[group_order_condition]);

(* Theorem: monic z /\ ipoly z /\ z <> unity 1 ==>
            !k. 0 < k /\ (X ** k == |1|) (pm z) ==> (forderz X) divides k *)
(* Proof:
   First, 0 < deg z                      by poly_irreducible_deg_nonzero
   Hence  pmonic z                       by notation
   Show z <> X
      Since 0 < k                        by given
        and pmonic X                     by poly_deg_X, poly_monic_X
      Given (X ** k == |1|) (pm z),
      This is X ** k % z = |1|           by pmod_def_alt
      But  X ** k % X = |0|              by poly_mod_exp, poly_div_mod_id
      If z = X, this means |0| = |1|
      which is not possible for Field    by poly_one_eq_poly_zero
   With z <> X, and z <> unity 1         by given
   We claim: X % z <> |0|
             If deg z = 1, z = factor c  by poly_monic_deg1_factor
             and X % z = c * |1|         by poly_factor_divides_X
             This equals |0| when c = #0 by poly_cmult_lzero
             but this makes z = X        by poly_sub_rzero
             which contradicts z <> X.
             If 1 < deg z, X % z = X     by poly_mod_less
             and X <> |0| as they differ in degree.
   Hence X % z <> |0|,
   and the result follows by poly_order_divides.
*)
val poly_X_order_divides = store_thm(
  "poly_X_order_divides",
  ``!r:'a field z. Field r /\ monic z /\ ipoly z /\ z <> unity 1 ==>
   !k. 0 < k /\ (X ** k == |1|) (pm z) ==> (forderz X) divides k``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  `poly X` by rw[] >>
  `k <> 0` by decide_tac >>
  `pmonic X` by rw[] >>
  `X ** k % z = |1|` by metis_tac[pmod_def_alt, poly_one_poly, poly_deg_one, poly_mod_less] >>
  `X ** k % X = |0|` by metis_tac[poly_mod_exp, poly_div_mod_id, poly_zero_exp, poly_zero_mod] >>
  `z <> X` by metis_tac[poly_one_eq_poly_zero] >>
  `X % z <> |0|` by
  (Cases_on `deg z = 1` >| [
    `?c. c IN R /\ (z = factor c)` by rw[poly_monic_deg1_factor] >>
    `c <> #0` by metis_tac[poly_factor_alt, poly_cmult_lzero, poly_sub_rzero, poly_one_poly] >>
    rw[poly_factor_divides_X],
    `1 < deg z` by decide_tac >>
    rw[poly_mod_less]
  ]) >>
  rw[poly_order_divides]);

(* Theorem: Field r /\ monic z /\ ipoly z ==>
            !p. poly p /\ (forderz p = 1) ==> ((p % z = |0|) \/ (p % z = |1|)) *)
(* Proof:
   By contradiction, suppose p % z <> |0| /\ p % z <> |1|.
   Note 0 < deg z             by poly_irreducible_deg_nonzero
     so pmonic z              by monic z
    ==> deg (p % z) < deg z   by poly_deg_mod_less, pmonic z
   Also forderz (p % z) = 1   by poly_order_eq_poly_mod_order, forderz p = 1.

    Now Group ((PolyModRing r z).prod excluding |0|)             by poly_mod_prod_group
    and p % z IN ((PolyModRing r z).prod excluding |0|).carrier  by poly_mod_ring_property, excluding_def, p % z <> |0|
    and ((PolyModRing r z).prod excluding |0|).id = |1|          by poly_mod_prod_nonzero_id
   Thus p % z = |1|           by group_order_eq_1
   This contradicts p % z <> |1|.
*)
val poly_order_eq_1 = store_thm(
  "poly_order_eq_1",
  ``!r:'a field z. Field r /\ monic z /\ ipoly z ==>
   !p. poly p /\ (forderz p = 1) ==> ((p % z = |0|) \/ (p % z = |1|))``,
  spose_not_then strip_assume_tac >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  `deg (p % z) < deg z` by rw[poly_deg_mod_less] >>
  `forderz (p % z) = 1` by rw[GSYM poly_order_eq_poly_mod_order] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[poly_mod_prod_group] >>
  (`p % z IN ((PolyModRing r z).prod excluding |0|).carrier` by (rw[poly_mod_ring_property, excluding_def] >> metis_tac[poly_zero])) >>
  `((PolyModRing r z).prod excluding |0|).id = |1|` by rw[poly_mod_prod_nonzero_id] >>
  metis_tac[group_order_eq_1]);

(* Theorem: Field r /\ ipoly z /\ 1 < deg z ==>
            !m n. m < forderz X /\ n < forderz X ==> (X ** m == X ** n) (pm z) <=> (m = n) *)
(* Proof:
   Let k = forderz X
   If part: (X ** m == X ** n) (pm z) ==> (m = n)
     Since Field (PolyModRing r z                        by poly_mod_irreducible_field
       and Group ((PolyModRing r z).prod excluding |0|)  by field_mult_group
     It is easy to show: X IN ((PolyModRing r z).prod excluding |0|).carrier
       Since by excluding_def, IN_DIFF, IN_SING, this is to show:
       (1) X IN (PolyModRing r z).prod.carrier
           Since poly X and (deg X = 1)                  by poly_X, poly_deg_X
           This is true by poly_mod_ring_property
       (2) X <> |0|
           This is true by since X = |1| >> 1.
     Note pmonic z                  by poly_irreducible_pmonic
     Therefore !n. ((PolyModRing r z).prod excluding |0|).exp X n = (X ** n) % z  by poly_mod_exp_alt
     Since (X ** m == X ** n) (pm z) means X ** m % z = X ** n % z                by pmod_def_alt
     Thus   ((PolyModRing r z).prod excluding |0|).exp X m
          = ((PolyModRing r z).prod excluding |0|).exp X n        by above
     With  (PolyModRing r z).sum.id = |0|                         by poly_mod_ring_property
     we conclude m = n                                            by group_order_unique
   Only-if part: (m = n) ==> (X ** m == X ** n) (pm z)
     This is true by poly_mod_reflexive.
*)
val poly_mod_field_exp_eq_0 = store_thm(
  "poly_mod_field_exp_eq_0",
  ``!r:'a field z. Field r /\ ipoly z /\ 1 < deg z ==>
     !m n. m < forderz X /\ n < forderz X ==> ((X ** m == X ** n) (pm z) <=> (m = n))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `k = forderz X` >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `(PolyModRing r z).sum.id = |0|` by metis_tac[poly_mod_ring_property] >>
    `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
    `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[field_mult_group] >>
    `X IN ((PolyModRing r z).prod excluding |0|).carrier` by
  (rw_tac std_ss[excluding_def, IN_DIFF, IN_SING] >-
    rw[poly_mod_ring_property] >>
    rw[]
    ) >>
    `pmonic z` by rw[poly_irreducible_pmonic] >>
    `!n. ((PolyModRing r z).prod excluding |0|).exp X n = (X ** n) % z` by rw[poly_mod_exp_alt] >>
    metis_tac[group_order_unique, pmod_def_alt],
    rw[]
  ]);

(* Next is an improvement of the previous version, but require monic z. *)

(* Theorem: Field r /\ monic z /\ ipoly z /\ z <> X ==>
            !m n. m < forderz X /\ n < forderz X ==> (X ** m == X ** n) (pm z) <=> (m = n) *)
(* Proof:
   Let k = forderz X
   If part: (X ** m == X ** n) (pm z) ==> (m = n)
     Since Field (PolyModRing r z                        by poly_mod_irreducible_field
       and Group ((PolyModRing r z).prod excluding |0|)  by field_mult_group
     It is easy to show: X IN ((PolyModRing r z).prod excluding |0|).carrier
       Since by excluding_def, IN_DIFF, IN_SING, this is to show:
       (1) X IN (PolyModRing r z).prod.carrier
           Since poly X and (deg X = 1)   by poly_X, poly_deg_X
           This is true by poly_mod_ring_property, 0 < deg z
       (2) X <> |0|
           This is true by since X = |1| >> 1.
     Note deg z <> 0                by poly_monic_deg1_factor
     Thus 1 < deg z                 by poly_irreducible_deg_nonzero
      and pmonic z                  by notation
     Therefore !n. ((PolyModRing r z).prod excluding |0|).exp X n = (X ** n) % z  by poly_mod_exp_alt
     Since (X ** m == X ** n) (pm z) means X ** m % z = X ** n % z                by pmod_def_alt
     Thus  forderz X = forderz (X % z)       by above
     With  #0z = |0|                         by poly_mod_ring_ids
     we conclude m = n                       by group_order_unique
   Only-if part: (m = n) ==> (X ** m == X ** n) (pm z)
     This is true by poly_mod_reflexive.
*)
val poly_mod_field_exp_eq_1 = store_thm(
  "poly_mod_field_exp_eq_1",
  ``!r:'a field z. Field r /\ monic z /\ ipoly z /\ z <> X ==>
     !m n. m < forderz X /\ n < forderz X ==> ((X ** m == X ** n) (pm z) <=> (m = n))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `k = forderz X` >>
  `(PolyModRing r z).sum.id = |0|` by metis_tac[poly_mod_ring_ids] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[field_mult_group] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  `X % z IN ((PolyModRing r z).prod excluding |0|).carrier` by
  (rw_tac std_ss[excluding_def, IN_DIFF, IN_SING] >| [
    `deg (X % z) < deg z` by rw[poly_deg_mod_less] >>
    `poly (X % z)` by rw[] >>
    metis_tac[poly_mod_ring_property, NOT_ZERO],
    Cases_on `deg z = 1` >| [
      `?c. c IN R /\ (z = factor c)` by rw[poly_monic_deg1_factor] >>
      `c <> #0` by metis_tac[poly_factor_alt, poly_cmult_lzero, poly_sub_rzero, poly_X, poly_one_poly] >>
      rw[poly_factor_divides_X],
      `1 < deg z` by decide_tac >>
      rw[poly_mod_less]
    ]
  ]) >>
  `!n. ((PolyModRing r z).prod excluding |0|).exp (X % z) n = (X ** n) % z` by rw[poly_mod_exp_alt, GSYM poly_mod_exp] >>
  `forderz X = forderz (X % z)` by rw[GSYM poly_order_eq_poly_mod_order] >>
  metis_tac[group_order_unique, pmod_def_alt]);

(*
poly_mod_field_exp_eq_1
val it = |- !r. Field r ==>
     !z. monic z /\ ipoly z /\ z <> X ==>
       !m n. m < forderz X /\ n < forderz X ==> ((X ** m == X ** n) (pm z) <=> (m = n)): thm
*)

(* Theorem: Field r /\ ipoly z ==>
            !p. poly p /\ p <> |0| /\ deg p < deg z ==>
            !m n. m < forderz p /\ n < forderz p ==> ((p ** m == p ** n) (pm z) <=> (m = n)) *)
(* Proof:
   If part: (p ** m == p ** n) (pm z) ==> (m = n)
      By pmod_def_alt, this is to show: p ** m % z = p ** n % z ==> m = n
      Note FiniteGroup ((PolyModRing r z).prod excluding |0|)    by poly_mod_prod_finite_group
       and p IN ((PolyModRing r z).prod excluding |0|).carrier   by poly_mod_ring_nonzero_element, 0 < deg z
      also pmonic z                                              by poly_irreducible_pmonic
     Let k = forderz t
     Then ((PolyModRing r z).prod excluding |0|).exp p m
        = ((PolyModRing r z).prod excluding |0|).exp p n         by poly_mod_exp_alt
       or m MOD k = n MOD k                                      by group_exp_eq_condition, pmonic z, 0 < k
       or       m = n                                            by LESS_MOD, m < k and n < k.
   Only-if part: m = n ==> (p ** m == p ** n) (pm z) is trivially true.
*)
val poly_mod_field_exp_eq_condition = store_thm(
  "poly_mod_field_exp_eq_condition",
  ``!r:'a field z. Field r /\ ipoly z ==>
   !p. poly p /\ p <> |0| /\ deg p < deg z ==>
   !m n. m < forderz p /\ n < forderz p ==> ((p ** m == p ** n) (pm z) <=> (m = n))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  rw[pmod_def_alt, EQ_IMP_THM] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by rw[poly_mod_prod_group] >>
  `p IN ((PolyModRing r z).prod excluding |0|).carrier` by rw[poly_mod_ring_nonzero_element] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  `0 < forderz p` by decide_tac >>
  metis_tac[poly_mod_exp_alt, group_exp_eq_condition, LESS_MOD]);

(* ------------------------------------------------------------------------- *)
(* Product of Monomials.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The following proof amounts to an application of poly_monic_prod_set_monomials_deg. *)

val _ = temp_overload_on ("|e|", ``###e``);

(* Theorem: FINITE s /\ MAX_SET s < char r ==> deg (PPROD (IMAGE (\c. X + |c|) s)) = CARD s *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: deg (PPROD (IMAGE (\c. X + |c|) {})) = CARD {}
     LHS = deg (PPROD (IMAGE (\c. X + |c|) {}))
         = deg |1|                   by poly_prod_set_empty
         = 0                         by poly_deg_one
         = CARD {}                   by CARD_EMPTY
         = RHS
   Step case: e NOTIN s ==> deg (PPROD (IMAGE (\c. X + |c|) (e INSERT s))) = CARD (e INSERT s)
     Note that monic (X + |e|)                                    by poly_monic_X_add_c
          and  monic (PPROD (IMAGE (\c. X + |c|) s))              by poly_monic_prod_set_monic
          and  (X + |e|) NOTIN (IMAGE (\c. X + |c|) s)            by poly_X_add_c_image_property
     LHS = deg (PPROD (IMAGE (\c. X + |c|) (e INSERT s)))
         = deg (PPROD ((X + |e|) INSERT IMAGE (\c. X + |c|) s))   by IMAGE_INSERT
         = deg ((X + |e|) * PPROD (IMAGE (\c. X + |c|) s) DELETE (X + |e|))  by poly_prod_set_thm
         = deg ((X + |e|) * PPROD (IMAGE (\c. X + |c|) s))        by DELETE_NON_ELEMENT
         = deg (X + |e|) + deg (PPROD (IMAGE (\c. X + |c|) s))    by poly_monic_deg_mult
         = deg (X + |e|) + CARD s                                 by induction hypothesis
         = 1 + CARD s                                             by poly_deg_X_add_c
         = SUC(CARD s)                                            by SUC_ONE_ADD
         = CARD (e INSERT s)                                      by CARD_INSERT
         = RHS
*)
val poly_prod_set_image_X_add_c_deg = store_thm(
  "poly_prod_set_image_X_add_c_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
    (deg (PPROD (IMAGE (\c:num. X + |c|) s)) = CARD s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> MAX_SET s < char r ==> (deg (PPROD (IMAGE (\c:num. X + |c|) s)) = CARD s)` suffices_by metis_tac[] >>
  Induct_on `FINITE` >>
  rw_tac std_ss[] >-
  rw[poly_prod_set_empty] >>
  `monic (X + |e|)` by rw[poly_monic_X_add_c] >>
  `!p. p IN (IMAGE (\c:num. X + |c|) s) <=> ?c. (p = X + |c|) /\ c IN s` by rw[] >>
  `!p. p IN (IMAGE (\c:num. X + |c|) s) ==> monic p` by metis_tac[poly_monic_X_add_c] >>
  `(e INSERT s) <> {}` by rw[] >>
  `!c. c IN (e INSERT s) ==> c <= MAX_SET (e INSERT s)` by rw[MAX_SET_DEF] >>
  `e < char r` by metis_tac[COMPONENT, LESS_EQ_LESS_TRANS] >>
  `MAX_SET s <= MAX_SET (e INSERT s)` by rw[MAX_SET_THM] >>
  `MAX_SET s < char r` by decide_tac >>
  `X + |e| NOTIN IMAGE (\c. X + |c|) s` by metis_tac[poly_X_add_c_image_property] >>
  `monic (PPROD (IMAGE (\c. X + |c|) s))` by rw[poly_monic_prod_set_monic] >>
  `(IMAGE (\c. X + |c|) s) SUBSET (PolyRing r).carrier` by metis_tac[poly_monic_poly, poly_ring_element, SUBSET_DEF] >>
  `!p. p IN (IMAGE (\c. X + |c|) s) ==> poly p` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `deg (PPROD (IMAGE (\c. X + |c|) (e INSERT s)))
    = deg (PPROD ((X + |e|) INSERT IMAGE (\c. X + |c|) s))` by rw[IMAGE_INSERT] >>
  `_ = deg ((X + |e|) * PPROD ((IMAGE (\c. X + |c|) s) DELETE (X + |e|)))` by rw[GSYM poly_prod_set_thm] >>
  `_ = deg ((X + |e|) * PPROD (IMAGE (\c. X + |c|) s))` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = deg (X + |e|) + deg (PPROD (IMAGE (\c. X + |c|) s))` by rw[poly_monic_deg_mult] >>
  `_ = deg (X + |e|) + CARD s` by rw[] >>
  `_ = 1 + CARD s` by rw[poly_deg_X_add_c] >>
  `_ = SUC(CARD s)` by rw[SUC_ONE_ADD] >>
  `_ = CARD (e INSERT s)` by rw[CARD_INSERT] >>
  rw[]);

(* Theorem: FINITE s /\ MAX_SET s < char r ==> deg (PPROD (IMAGE (\c. X - |c|) s)) = CARD s *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: deg (PPROD (IMAGE (\c. X - |c|) {})) = CARD {}
     LHS = deg (PPROD (IMAGE (\c. X - |c|) {}))
         = deg |1|                   by poly_prod_set_empty
         = 0                         by poly_deg_one
         = CARD {}                   by CARD_EMPTY
         = RHS
   Step case: e NOTIN s ==> deg (PPROD (IMAGE (\c. X - |c|) (e INSERT s))) = CARD (e INSERT s)
     Note that monic (X - |e|)                                    by poly_monic_X_sub_c
          and  monic (PPROD (IMAGE (\c. X - |c|) s))              by poly_monic_prod_set_monic
          and  (X - |e|) NOTIN (IMAGE (\c. X - |c|) s)            by poly_X_sub_c_image_property
     LHS = deg (PPROD (IMAGE (\c. X - |c|) (e INSERT s)))
         = deg (PPROD ((X - |e|) INSERT IMAGE (\c. X - |c|) s))   by IMAGE_INSERT
         = deg ((X - |e|) * PPROD (IMAGE (\c. X - |c|) s) DELETE (X + |e|))  by poly_prod_set_thm
         = deg ((X - |e|) * PPROD (IMAGE (\c. X - |c|) s))        by DELETE_NON_ELEMENT
         = deg (X - |e|) + deg (PPROD (IMAGE (\c. X - |c|) s))    by poly_monic_deg_mult
         = deg (X - |e|) + CARD s                                 by induction hypothesis
         = 1 + CARD s                                             by poly_deg_X_sub_c
         = SUC(CARD s)                                            by SUC_ONE_ADD
         = CARD (e INSERT s)                                      by CARD_INSERT
         = RHS
*)
val poly_prod_set_image_X_sub_c_deg = store_thm(
  "poly_prod_set_image_X_sub_c_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
    (deg (PPROD (IMAGE (\c:num. X - |c|) s)) = CARD s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> MAX_SET s < char r ==> (deg (PPROD (IMAGE (\c:num. X - |c|) s)) = CARD s)` suffices_by metis_tac[] >>
  Induct_on `FINITE` >>
  rw_tac std_ss[] >-
  rw[poly_prod_set_empty] >>
  `monic (X - |e|)` by rw[poly_monic_X_sub_c] >>
  `!p. p IN (IMAGE (\c:num. X - |c|) s) <=> ?c. (p = X - |c|) /\ c IN s` by rw[] >>
  `!p. p IN (IMAGE (\c:num. X - |c|) s) ==> monic p` by metis_tac[poly_monic_X_sub_c] >>
  `(e INSERT s) <> {}` by rw[] >>
  `!c. c IN (e INSERT s) ==> c <= MAX_SET (e INSERT s)` by rw[MAX_SET_DEF] >>
  `e < char r` by metis_tac[COMPONENT, LESS_EQ_LESS_TRANS] >>
  `MAX_SET s <= MAX_SET (e INSERT s)` by rw[MAX_SET_THM] >>
  `MAX_SET s < char r` by decide_tac >>
  `X - |e| NOTIN IMAGE (\c. X - |c|) s` by metis_tac[poly_X_sub_c_image_property] >>
  `monic (PPROD (IMAGE (\c. X - |c|) s))` by rw[poly_monic_prod_set_monic] >>
  `(IMAGE (\c. X - |c|) s) SUBSET (PolyRing r).carrier` by metis_tac[poly_monic_poly, poly_ring_element, SUBSET_DEF] >>
  `!p. p IN (IMAGE (\c. X - |c|) s) ==> poly p` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `deg (PPROD (IMAGE (\c. X - |c|) (e INSERT s)))
    = deg (PPROD ((X - |e|) INSERT IMAGE (\c. X - |c|) s))` by rw[IMAGE_INSERT] >>
  `_ = deg ((X - |e|) * PPROD ((IMAGE (\c. X - |c|) s) DELETE (X - |e|)))` by rw[GSYM poly_prod_set_thm] >>
  `_ = deg ((X - |e|) * PPROD (IMAGE (\c. X - |c|) s))` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = deg (X - |e|) + deg (PPROD (IMAGE (\c. X - |c|) s))` by rw[poly_monic_deg_mult] >>
  `_ = deg (X - |e|) + CARD s` by rw[] >>
  `_ = 1 + CARD s` by rw[poly_deg_X_sub_c] >>
  `_ = SUC(CARD s)` by rw[SUC_ONE_ADD] >>
  `_ = CARD (e INSERT s)` by rw[CARD_INSERT] >>
  rw[]);

(* Theorem: A factor divides the poly_prod_set of monomials.
            !n. n < char r ==>
            (n IN s ==> ((PPROD (IMAGE (\c:num. X + |c|) s)) % (X + |n|) = |0|) *)
(* Proof:
   Let f = (\c:num. X + |c|), this is to show:
       n < char r ==> n IN s ==> (PPROD (IMAGE f s) % (X + |n|) = |0|)
   Let p = f n = X + |n|,
   n IN s ==> p IN (IMAGE f s)                 by poly_X_add_c_image_property
     PPROD (IMAGE f s)
   = PPROD (p INSERT (IMAGE f s))              by ABSORPTION
   = p * PPROD ((IMAGE f s) DELETE p)          by poly_prod_set_thm
   Since pmonic p                              by poly_pmonic_X_add_c, #1 <> #0
     and poly (PPROD ((IMAGE f s) DELETE p))   by poly_prod_set_poly
         PPROD (IMAGE f s) % p = |0|           by poly_mod_eq_zero, poly_mult_comm
*)
val poly_prod_set_image_X_add_c_factor = store_thm(
  "poly_prod_set_image_X_add_c_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r /\ n IN s ==>
       ((PPROD (IMAGE (\c:num. X + |c|) s)) % (X + |n|) = |0|)``,
  rpt strip_tac >>
  qabbrev_tac `f = \c:num. X + |c|` >>
  qabbrev_tac `p = X + |n|` >>
  `p IN (IMAGE f s)` by rw[GSYM poly_X_add_c_image_property, Abbr`f`, Abbr`p`] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `FINITE ((IMAGE f s) DELETE p)` by rw[] >>
  `(IMAGE f s) SUBSET (PolyRing r).carrier` by (rw[poly_X_add_c_image_element, poly_ring_element, SUBSET_DEF, Abbr`f`] >- rw[]) >>
  `!x. x IN (IMAGE f s) ==> poly x` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `poly p` by rw[poly_X_add_c, Abbr`p`] >>
  `PPROD (IMAGE f s) = PPROD (p INSERT (IMAGE f s))` by metis_tac[ABSORPTION] >>
  `_ = p * PPROD ((IMAGE f s) DELETE p)` by rw[poly_prod_set_thm] >>
  `pmonic p` by rw[poly_pmonic_X_add_c, Abbr`p`] >>
  `((IMAGE f s) DELETE p) SUBSET (PolyRing r).carrier` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
  `!x. x IN ((IMAGE f s) DELETE p) ==> poly x` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `poly (PPROD ((IMAGE f s) DELETE p))` by rw[poly_prod_set_poly] >>
  `poly (PPROD (IMAGE f s))` by rw[poly_prod_set_poly, Abbr`f`] >>
  metis_tac[poly_mod_eq_zero, poly_mult_comm]);

(* Theorem: A factor divides the poly_prod_set of monomials.
            !n. n < char r ==>
            (n IN s ==> ((PPROD (IMAGE (\c:num. X - |c|) s)) % (X - |n|) = |0|) *)
(* Proof:
   Let f = (\c:num. X - |c|), this is to show:
       n < char r ==> n IN s ==> (PPROD (IMAGE f s) % (X - |n|) = |0|)
   Let p = f n = X - |n|,
   n IN s ==> p IN (IMAGE f s)                 by poly_X_sub_c_image_property
     PPROD (IMAGE f s)
   = PPROD (p INSERT (IMAGE f s))              by ABSORPTION
   = p * PPROD ((IMAGE f s) DELETE p)          by poly_prod_set_thm
   Since pmonic p                              by poly_pmonic_X_sub_c, #1 <> #0
     and poly (PPROD ((IMAGE f s) DELETE p))   by poly_prod_set_poly
         PPROD (IMAGE f s) % p = |0|           by poly_mod_eq_zero, poly_mult_comm
*)
val poly_prod_set_image_X_sub_c_factor = store_thm(
  "poly_prod_set_image_X_sub_c_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r /\ n IN s ==>
       ((PPROD (IMAGE (\c:num. X - |c|) s)) % (X - |n|) = |0|)``,
  rpt strip_tac >>
  qabbrev_tac `f = \c:num. X - |c|` >>
  qabbrev_tac `p = X - |n|` >>
  `p IN (IMAGE f s)` by rw[GSYM poly_X_sub_c_image_property, Abbr`f`, Abbr`p`] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `FINITE ((IMAGE f s) DELETE p)` by rw[] >>
  `(IMAGE f s) SUBSET (PolyRing r).carrier` by (rw[poly_X_sub_c_image_element, poly_ring_element, SUBSET_DEF, Abbr`f`] >- rw[]) >>
  `!x. x IN (IMAGE f s) ==> poly x` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `poly p` by rw[poly_X_sub_c, Abbr`p`] >>
  `PPROD (IMAGE f s) = PPROD (p INSERT (IMAGE f s))` by metis_tac[ABSORPTION] >>
  `_ = p * PPROD ((IMAGE f s) DELETE p)` by rw[poly_prod_set_thm] >>
  `pmonic p` by rw[poly_pmonic_X_sub_c, Abbr`p`] >>
  `((IMAGE f s) DELETE p) SUBSET (PolyRing r).carrier` by metis_tac[DELETE_SUBSET, SUBSET_TRANS] >>
  `!x. x IN ((IMAGE f s) DELETE p) ==> poly x` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `poly (PPROD ((IMAGE f s) DELETE p))` by rw[poly_prod_set_poly] >>
  `poly (PPROD (IMAGE f s))` by rw[poly_prod_set_poly, Abbr`f`] >>
  metis_tac[poly_mod_eq_zero, poly_mult_comm]);

(* Theorem: (IMAGE (\c:num. X + |c|) s) SUBSET (PolyRing r).carrier *)
(* Proof: by poly_X_add_c_image_element and poly_ring_element. *)
val poly_X_add_c_image_poly_subset = store_thm(
  "poly_X_add_c_image_poly_subset",
  ``!r:'a ring. Ring r ==> !s. (IMAGE (\c:num. X + |c|) s) SUBSET (PolyRing r).carrier``,
  rw[poly_X_add_c_image_element, poly_ring_element, SUBSET_DEF] >>
  rw[]);

(* Theorem: (IMAGE (\c:num. X - |c|) s) SUBSET (PolyRing r).carrier *)
(* Proof: by poly_X_sub_c_image_element and poly_ring_element. *)
val poly_X_sub_c_image_poly_subset = store_thm(
  "poly_X_sub_c_image_poly_subset",
  ``!r:'a ring. Ring r ==> !s. (IMAGE (\c:num. X - |c|) s) SUBSET (PolyRing r).carrier``,
  rw[poly_X_sub_c_image_element, poly_ring_element, SUBSET_DEF] >>
  rw[]);

(* Theorem: What divides the poly_prod_set of monomials must be a factor.
            FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
            (((PPROD (IMAGE (\c:num. X + |c|) s)) % (X + |n|) = |0|) ==> n IN s) *)
(* Proof:
   Let f = (\c:num. X + |c|), this is to show:
       n < char r ==> (PPROD (IMAGE f s) % (X + |n|) = |0|) ==> n IN s
   Let p = f n = X + |n|,
   Need to use: p IN (IMAGE f s) ==> n IN s      by poly_X_add_c_image_property
   Change goal: PPROD (IMAGE f s) % p = |0| ==> p IN IMAGE f s
   Use complete induction on (CARD s).
   If s = {},
      IMAGE f {} = {}      by IMAGE_EMPTY
      and p IN IMAGE f {}  is impossible.
      But  PPROD (IMAGE f {}) % p
         = PPROD {} % p            by IMAGE_EMPTY
         = |1| % p                 by poly_prod_set_empty
         = |1|                     by poly_mod_const, poly_one
      and  |1| <> |0|.
   If s <> {},
      Let c = CHOICE s, t = REST s,
      then s = c INSERT t                        by CHOICE_INSERT_REST
        PPROD (IMAGE f s)
      = PPROD (IMAGE f (c INSERT t))             by CHOICE_INSERT_REST above
      = PPROD ((X + |c|) INSERT (IMAGE f t))     by IMAGE_INSERT
      = (X + |c|) * PPROD ((IMAGE f t) DELETE (X + |c|))  by poly_prod_set_thm
      = (X + |c|) * PPROD (IMAGE f t)            by DELETE_NON_ELEMENT
      Given (PPROD (IMAGE f s)) % p = |0|,
            (X + |c|) % p = |0|
         or PPROD (IMAGE f t) % p = |0|          by poly_X_add_c_divides_product
      If (X + |c|) % p = |0|,
         X + |c| = p                             by poly_X_add_c_factor
         Since (X + |c|) IN IMAGE f s            by IN_IMAGE, CHOICE_DEF
         Hence p IN IMAGE f s.
      If PPROD (IMAGE f t) % p = |0|,
         Since deg (PPROD (IMAGE f t)) = CARD t  by poly_prod_set_image_X_add_c_deg
           and CARD t < CARD s                   by CARD_REST
          Thus p IN (IMAGE f t)                  by induction hypothesis
          Hence p IN (IMAGE f s)                 by REST_SUBSET, IMAGE_SUBSET, SUBSET_DEF
*)
val poly_prod_set_image_X_add_c_divides = store_thm(
  "poly_prod_set_image_X_add_c_divides",
  ``!r:'a field. Field r ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
    (((PPROD (IMAGE (\c:num. X + |c|) s)) % (X + |n|) = |0|) ==> n IN s)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `f = \c:num. X + |c|` >>
  qabbrev_tac `p = X + |n|` >>
  `p IN (IMAGE f s)` suffices_by rw[GSYM poly_X_add_c_image_property, Abbr`f`, Abbr`p`] >>
  `pmonic p` by rw[poly_pmonic_X_add_c, Abbr`p`] >>
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw_tac std_ss[] >>
  Cases_on `s = {}` >| [
    rw[] >>
    `PPROD (IMAGE f {}) = |1|` by rw[poly_prod_set_empty] >>
    `|1| % p = |1|` by rw[poly_mod_const] >>
    metis_tac[poly_one_ne_poly_zero],
    `?c t. (c = CHOICE s) /\ (t = REST s) /\ (s = c INSERT t)` by rw[CHOICE_INSERT_REST] >>
    `c NOTIN t` by metis_tac[CHOICE_NOT_IN_REST] >>
    `c < char r` by metis_tac[CHOICE_DEF, MAX_SET_LESS] >>
    `FINITE t` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
    `MAX_SET t < char r` by metis_tac[REST_SUBSET, SUBSET_MAX_SET, LESS_EQ_LESS_TRANS] >>
    `(X + |c|) NOTIN (IMAGE f t)` by rw[GSYM poly_X_add_c_image_property, Abbr`f`] >>
    `(IMAGE f t) SUBSET (PolyRing r).carrier` by (rw[poly_X_add_c_image_element, poly_ring_element, SUBSET_DEF, Abbr`f`] >- rw[]) >>
    `!p. p IN (IMAGE f t) ==> poly p` by metis_tac[poly_ring_element, SUBSET_DEF] >>
    `PPROD (IMAGE f s) = PPROD (IMAGE f (c INSERT t))` by rw[] >>
    `_ = PPROD ((X + |c|) INSERT (IMAGE f t))` by rw[IMAGE_INSERT] >>
    `_ = (X + |c|) * PPROD ((IMAGE f t) DELETE (X + |c|))` by rw[poly_prod_set_thm] >>
    `_ = (X + |c|) * PPROD (IMAGE f t)` by metis_tac[DELETE_NON_ELEMENT] >>
    `poly (X + |c|)` by rw[poly_X_add_c] >>
    `poly (PPROD (IMAGE f t))` by rw[poly_prod_set_poly, Abbr`f`] >>
    `((X + |c|) % p = |0|) \/ (PPROD (IMAGE f t) % p = |0|)` by metis_tac[poly_X_add_c_divides_product] >-
    metis_tac[poly_X_add_c_factor, IN_IMAGE, CHOICE_DEF] >>
    `CARD t < CARD s` by rw[CARD_REST] >>
    `deg (PPROD (IMAGE f t)) = CARD t` by rw[poly_prod_set_image_X_add_c_deg, Abbr`f`] >>
    `p IN (IMAGE f t)` by rw[] >>
    metis_tac[REST_SUBSET, IMAGE_SUBSET, SUBSET_DEF]
  ]);

(* Theorem: What divides the poly_prod_set of monomials must be a factor.
            FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
            (((PPROD (IMAGE (\c:num. X - |c|) s)) % (X - |n|) = |0|) ==> n IN s) *)
(* Proof:
   Let f = (\c:num. X - |c|), this is to show:
       n < char r ==> (PPROD (IMAGE f s) % (X - |n|) = |0|) ==> n IN s
   Let p = f n = X - |n|,
   Need to use: p IN (IMAGE f s) ==> n IN s      by poly_X_sub_c_image_property
   Change goal: PPROD (IMAGE f s) % p = |0| ==> p IN IMAGE f s
   Use complete induction on (CARD s).
   If s = {},
      IMAGE f {} = {}      by IMAGE_EMPTY
      and p IN IMAGE f {}  is impossible.
      But  PPROD (IMAGE f {}) % p
         = PPROD {} % p            by IMAGE_EMPTY
         = |1| % p                 by poly_prod_set_empty
         = |1|                     by poly_mod_const, poly_one
      and  |1| <> |0|.
   If s <> {},
      Let c = CHOICE s, t = REST s,
      then s = c INSERT t                        by CHOICE_INSERT_REST
        PPROD (IMAGE f s)
      = PPROD (IMAGE f (c INSERT t))             by CHOICE_INSERT_REST above
      = PPROD ((X + |c|) INSERT (IMAGE f t))     by IMAGE_INSERT
      = (X + |c|) * PPROD ((IMAGE f t) DELETE (X + |c|))  by poly_prod_set_thm
      = (X + |c|) * PPROD (IMAGE f t)            by DELETE_NON_ELEMENT
      Given (PPROD (IMAGE f s)) % p = |0|,
            (X + |c|) % p = |0|
         or PPROD (IMAGE f t) % p = |0|          by poly_X_sub_c_divides_product
      If (X - |c|) % p = |0|,
         X - |c| = p                             by poly_X_sub_c_factor
         Since (X - |c|) IN IMAGE f s            by IN_IMAGE, CHOICE_DEF
         Hence p IN IMAGE f s.
      If PPROD (IMAGE f t) % p = |0|,
         Since deg (PPROD (IMAGE f t)) = CARD t  by poly_prod_set_image_X_sub_c_deg
           and CARD t < CARD s                   by CARD_REST
          Thus p IN (IMAGE f t)                  by induction hypothesis
          Hence p IN (IMAGE f s)                 by REST_SUBSET, IMAGE_SUBSET, SUBSET_DEF
*)
val poly_prod_set_image_X_sub_c_divides = store_thm(
  "poly_prod_set_image_X_sub_c_divides",
  ``!r:'a field. Field r ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
    (((PPROD (IMAGE (\c:num. X - |c|) s)) % (X - |n|) = |0|) ==> n IN s)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `f = \c:num. X - |c|` >>
  qabbrev_tac `p = X - |n|` >>
  `p IN (IMAGE f s)` suffices_by rw[GSYM poly_X_sub_c_image_property, Abbr`f`, Abbr`p`] >>
  `pmonic p` by rw[poly_pmonic_X_sub_c, Abbr`p`] >>
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw_tac std_ss[] >>
  Cases_on `s = {}` >| [
    rw[] >>
    `PPROD (IMAGE f {}) = |1|` by rw[poly_prod_set_empty] >>
    `|1| % p = |1|` by rw[poly_mod_const] >>
    metis_tac[poly_one_ne_poly_zero],
    `?c t. (c = CHOICE s) /\ (t = REST s) /\ (s = c INSERT t)` by rw[CHOICE_INSERT_REST] >>
    `c NOTIN t` by metis_tac[CHOICE_NOT_IN_REST] >>
    `c < char r` by metis_tac[CHOICE_DEF, MAX_SET_LESS] >>
    `FINITE t` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
    `MAX_SET t < char r` by metis_tac[REST_SUBSET, SUBSET_MAX_SET, LESS_EQ_LESS_TRANS] >>
    `(X - |c|) NOTIN (IMAGE f t)` by rw[GSYM poly_X_sub_c_image_property, Abbr`f`] >>
    `(IMAGE f t) SUBSET (PolyRing r).carrier` by (rw[poly_X_sub_c_image_element, poly_ring_element, SUBSET_DEF, Abbr`f`] >- rw[]) >>
    `!p. p IN (IMAGE f t) ==> poly p` by metis_tac[poly_ring_element, SUBSET_DEF] >>
    `PPROD (IMAGE f s) = PPROD (IMAGE f (c INSERT t))` by rw[] >>
    `_ = PPROD ((X - |c|) INSERT (IMAGE f t))` by rw[IMAGE_INSERT] >>
    `_ = (X - |c|) * PPROD ((IMAGE f t) DELETE (X - |c|))` by rw[poly_prod_set_thm] >>
    `_ = (X - |c|) * PPROD (IMAGE f t)` by metis_tac[DELETE_NON_ELEMENT] >>
    `poly (X - |c|)` by rw[poly_X_sub_c] >>
    `poly (PPROD (IMAGE f t))` by rw[poly_prod_set_poly, Abbr`f`] >>
    `((X - |c|) % p = |0|) \/ (PPROD (IMAGE f t) % p = |0|)` by metis_tac[poly_X_sub_c_divides_product] >-
    metis_tac[poly_X_sub_c_factor, IN_IMAGE, CHOICE_DEF] >>
    `CARD t < CARD s` by rw[CARD_REST] >>
    `deg (PPROD (IMAGE f t)) = CARD t` by rw[poly_prod_set_image_X_sub_c_deg, Abbr`f`] >>
    `p IN (IMAGE f t)` by rw[] >>
    metis_tac[REST_SUBSET, IMAGE_SUBSET, SUBSET_DEF]
  ]);

(* Theorem: A factor divides only its poly_prod_set of monomials.
            Field r ==> !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
            (n IN s <=> (PPROD (IMAGE (\c. X + |c|) s) % (X + |n|) = |0|)) *)
(* Proof:
   If part: by poly_prod_set_image_X_add_c_factor.
   Only-if part: by poly_prod_set_image_X_add_c_divides.
*)
val poly_prod_set_image_X_add_c_property = store_thm(
  "poly_prod_set_image_X_add_c_property",
  ``!r:'a field. Field r ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
   (n IN s <=> (PPROD (IMAGE (\c. X + |c|) s) % (X + |n|) = |0|))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  metis_tac[poly_prod_set_image_X_add_c_factor, poly_prod_set_image_X_add_c_divides]);

(* Theorem: A factor divides only its poly_prod_set of monomials.
            Field r ==> !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
            (n IN s <=> (PPROD (IMAGE (\c. X - |c|) s) % (X - |n|) = |0|)) *)
(* Proof:
   If part: by poly_prod_set_image_X_sub_c_factor.
   Only-if part: by poly_prod_set_image_X_sub_c_divides.
*)
val poly_prod_set_image_X_sub_c_property = store_thm(
  "poly_prod_set_image_X_sub_c_property",
  ``!r:'a field. Field r ==>
   !s. FINITE s /\ MAX_SET s < char r ==> !n. n < char r ==>
   (n IN s <=> (PPROD (IMAGE (\c. X - |c|) s) % (X - |n|) = |0|))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  metis_tac[poly_prod_set_image_X_sub_c_factor, poly_prod_set_image_X_sub_c_divides]);

(* Theorem: The poly_prod_set map of monomials from PowerSet of counts to Polynomials is Injective.
            FiniteField r /\ n < char r ==>
            INJ (\s. PPROD (IMAGE (\c:num. X + |c|) s))
                (PPOW (IMAGE SUC (count n))) (PolyRing r).carrier
*)
(* Proof:
   Let f = (\c:num. X + |c|).
   By INJ_DEF, this is to show:
   (1) s IN POW (IMAGE SUC (count n)) ==> PPROD (IMAGE f s) IN (PolyRing r).carrier
           s IN POW (IMAGE SUC (count n))
       ==> s SUBSET (IMAGE SUC (count n))               by IN_POW
       Since FINITE (IMAGE f s)                         by IMAGE_FINITE
         and (IMAGE f s) SUBSET (PolyRing r).carrier    by poly_X_add_c_image_poly_subset
       Hence PPROD (IMAGE f s) IN (PolyRing r).carrier  by poly_prod_set_property
   (2) s IN POW (IMAGE SUC (count n)) /\
       s' IN POW (IMAGE SUC (count n)) /\
       PPROD (IMAGE f s') = PPROD (IMAGE f s) ==> s' = s
       First prove that: equality implies subsets:
       !s t. FINITE s /\ MAX_SET s < char r /\ FINITE t /\ MAX_SET t < char r /\
          (PPROD (IMAGE f s) = PPROD (IMAGE f t)) ==> s SUBSET t
       Expand by r SUBSET_DEF, this is to show: x IN s ==> x IN t
       Since x IN s ==> x < char r      by MAX_SET_LESS
        Also x IN s ==> (PPROD (IMAGE f s'')) % (X + ###x) = |0|  by poly_prod_set_image_X_add_c_property
        Thus            (PPROD (IMAGE f t)) % (X + ###x) = |0|    by given equality
       Hence x IN t, or assetion is proved                        by poly_prod_set_image_X_add_c_property
       Now, s IN POW (IMAGE SUC (count n)) ==> s SUBSET (IMAGE SUC (count n))     by IN_POW
            s' IN POW (IMAGE SUC (count n)) ==> s' SUBSET (IMAGE SUC (count n))   by IN_POW
       Also FINITE s and FINITE s'                        by FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE
        and MAX_SET s <= n, MAX_SET s' <= n               by MAX_SET_IMAGE_SUC_COUNT, SUBSET_MAX_SET
         so MAX_SET s < char r and MAX_SET s' < char r    by LESS_EQ_LESS_TRANS
       Applying the lemma, s SUBSET s' and s' SUBSET s    by equality implies subset
       Therefore s = s'                                   by SUBSET_ANTISYM
*)

Theorem poly_prod_set_image_X_add_c_inj:
  !r:'a field.
      Field r ==> !n. n < char r ==>
      INJ (\s. PPROD (IMAGE (\c:num. X + |c|) s))
          (PPOW (IMAGE SUC (count n)))
          (PolyRing r).carrier
Proof
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `f = \c:num. X + |c|` >>
  rw_tac std_ss[INJ_DEF, IN_PPOW, IN_DIFF, IN_SING] >| [
    rename [‘s ≠ natural n’, ‘s ∈ POW (natural n)’] >>
    `s SUBSET (IMAGE SUC (count n))` by rw[GSYM IN_POW] >>
    `FINITE (IMAGE f s)`
       by metis_tac[IMAGE_FINITE, SUBSET_FINITE, FINITE_COUNT] >>
    `(IMAGE f s) SUBSET (PolyRing r).carrier`
       by rw[poly_X_add_c_image_poly_subset, Abbr`f`] >>
    rw[poly_prod_set_property],
    rename [‘PPIMAGE f s1 = PPIMAGE f s2’] >>
    ‘!s t. FINITE s /\ MAX_SET s < char r /\ FINITE t /\ MAX_SET t < char r /\
             (PPROD (IMAGE f s) = PPROD (IMAGE f t)) ==> s SUBSET t’
     by (rw_tac std_ss[SUBSET_DEF, Abbr`f`] >>
         qabbrev_tac `f = \c:num. X + |c|` >>
         `x < char r` by metis_tac[MAX_SET_LESS] >>
         `(PPROD (IMAGE f s)) % (X + ###x) = |0|`
           by rw[GSYM poly_prod_set_image_X_add_c_property, Abbr`f`] >>
         `(PPROD (IMAGE f t)) % (X + ###x) = |0|` by metis_tac[] >>
         rev_full_simp_tac std_ss [GSYM poly_prod_set_image_X_add_c_property,
                                   Abbr`f`]) >>
    `s1 ⊆ IMAGE SUC (count n) /\ s2 ⊆ (IMAGE SUC (count n))`
      by rw[GSYM IN_POW] >>
    `FINITE (IMAGE SUC (count n))` by rw[] >>
    `MAX_SET (IMAGE SUC (count n)) = n` by rw[MAX_SET_IMAGE_SUC_COUNT] >>
    `FINITE s1 ∧ FINITE s2` by metis_tac[SUBSET_FINITE] >>
    `MAX_SET s1 < char r ∧ MAX_SET s2 < char r`
      by metis_tac[SUBSET_MAX_SET, LESS_EQ_LESS_TRANS] >>
    metis_tac[SUBSET_ANTISYM]
  ]
QED

(* Theorem: The poly_prod_set map of monomials from PowerSet of counts to Polynomials is Injective.
            FiniteField r /\ n < char r ==>
            INJ (\s. PPROD (IMAGE (\c:num. X - |c|) s))
                (PPOW (IMAGE SUC (count n))) (PolyRing r).carrier
*)
(* Proof:
   Let f = (\c:num. X - |c|).
   By INJ_DEF, this is to show:
   (1) s IN POW (IMAGE SUC (count n)) ==> PPROD (IMAGE f s) IN (PolyRing r).carrier
           s IN POW (IMAGE SUC (count n))
       ==> s SUBSET (IMAGE SUC (count n))               by IN_POW
       Since FINITE (IMAGE f s)                         by IMAGE_FINITE
         and (IMAGE f s) SUBSET (PolyRing r).carrier    by poly_X_sub_c_image_poly_subset
       Hence PPROD (IMAGE f s) IN (PolyRing r).carrier  by poly_prod_set_property
   (2) s IN POW (IMAGE SUC (count n)) /\
       s' IN POW (IMAGE SUC (count n)) /\
       PPROD (IMAGE f s') = PPROD (IMAGE f s) ==> s' = s
       First prove that: equality implies subsets:
       !s t. FINITE s /\ MAX_SET s < char r /\ FINITE t /\ MAX_SET t < char r /\
          (PPROD (IMAGE f s) = PPROD (IMAGE f t)) ==> s SUBSET t
       Expand by r SUBSET_DEF, this is to show: x IN s ==> x IN t
       Since x IN s ==> x < char r      by MAX_SET_LESS
        Also x IN s ==> (PPROD (IMAGE f s'')) % (X - ###x) = |0|  by poly_prod_set_image_X_sub_c_property
        Thus            (PPROD (IMAGE f t)) % (X - ###x) = |0|    by given equality
       Hence x IN t, or assetion is proved                        by poly_prod_set_image_X_sub_c_property
       Now, s IN POW (IMAGE SUC (count n)) ==> s SUBSET (IMAGE SUC (count n))     by IN_POW
            s' IN POW (IMAGE SUC (count n)) ==> s' SUBSET (IMAGE SUC (count n))   by IN_POW
       Also FINITE s and FINITE s'                        by FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE
        and MAX_SET s <= n, MAX_SET s' <= n               by MAX_SET_IMAGE_SUC_COUNT, SUBSET_MAX_SET
         so MAX_SET s < char r and MAX_SET s' < char r    by LESS_EQ_LESS_TRANS
       Applying the lemma, s SUBSET s' and s' SUBSET s    by equality implies subset
       Therefore s = s'                                   by SUBSET_ANTISYM
*)
Theorem poly_prod_set_image_X_sub_c_inj:
  !r:'a field. Field r ==> !n. n < char r ==>
   INJ (\s. PPROD (IMAGE (\c:num. X - |c|) s)) (PPOW (IMAGE SUC (count n))) (PolyRing r).carrier
Proof
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `f = \c:num. X - |c|` >>
  rw_tac std_ss[INJ_DEF, IN_PPOW, IN_DIFF, IN_SING] >| [
    rename1 ‘s <> natural n’ >>
    `s SUBSET (IMAGE SUC (count n))` by rw[GSYM IN_POW] >>
    `FINITE (IMAGE f s)` by metis_tac[IMAGE_FINITE, SUBSET_FINITE, FINITE_COUNT] >>
    `(IMAGE f s) SUBSET (PolyRing r).carrier` by rw[poly_X_sub_c_image_poly_subset, Abbr`f`] >>
    rw[poly_prod_set_property],
    rename1 ‘s IN POW (natural n)’ >>
    `!s t. FINITE s /\ MAX_SET s < char r /\ FINITE t /\ MAX_SET t < char r /\
             (PPROD (IMAGE f s) = PPROD (IMAGE f t)) ==> s SUBSET t` by
  (rw_tac std_ss[SUBSET_DEF, Abbr`f`] >>
    qabbrev_tac `f = \c:num. X - |c|` >>
    `x < char r` by metis_tac[MAX_SET_LESS] >>
    `(PPROD (IMAGE f s'')) % (X - ###x) = |0|` by rw[GSYM poly_prod_set_image_X_sub_c_property, Abbr`f`] >>
    `(PPROD (IMAGE f t)) % (X - ###x) = |0|` by metis_tac[] >>
    rev_full_simp_tac std_ss [GSYM poly_prod_set_image_X_sub_c_property, Abbr`f`]) >>
    `s SUBSET (IMAGE SUC (count n)) /\ s' SUBSET (IMAGE SUC (count n))` by rw[GSYM IN_POW] >>
    `FINITE (IMAGE SUC (count n))` by rw[] >>
    `MAX_SET (IMAGE SUC (count n)) = n` by rw[MAX_SET_IMAGE_SUC_COUNT] >>
    `FINITE s /\ FINITE s'` by metis_tac[SUBSET_FINITE] >>
    `MAX_SET s < char r /\ MAX_SET s' < char r` by metis_tac[SUBSET_MAX_SET, LESS_EQ_LESS_TRANS] >>
    `s SUBSET s' /\ s' SUBSET s` by metis_tac[] >>
    rw[SUBSET_ANTISYM]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Factor and Root of Lifting Polynomial                                     *)
(* ------------------------------------------------------------------------- *)

(* Transform: poly_field_mod_lift_has_root_X to factor form:
poly_field_mod_lift_has_root_X
|- !r. Field r ==> !z. poly z /\ 1 < deg z ==> rootz (lift z) X

poly_root_thm
|- !r. Field r ==> !p x. poly p /\ x IN R ==> (root p x <=> (p % factor x = |0|))
> poly_root_thm |> ISPEC ``(PolyModRing r z)``;
val it = |- Ring (PolyModRing r z) /\ #1z <> #0z ==> !p x. polyz p /\ x IN Rz ==>
    (rootz p x <=> (poly_mod (PolyModRing r z) p (factorz x) = (PolyRing (PolyModRing r z)).sum.id)): thm
*)

(* poly_lift_zero  |- !r. lift |0| = ||0|| *)

(* overload on lifted |0| -- in polyFieldModulo *)
(* val _ = overload_on ("||0||", ``(PolyRing (PolyRing r)).sum.id``); *)
(* want: (PolyRing (PolyModRing r)).sum.id, will be lift |0| = ||0|| *)

(* overload on lifted |1| -- don't do this *)
(* val _ = overload_on("||1||", ``(PolyRing (PolyRing r)).prod.id``); *)
(* want: (PolyRing (PolyModRing r)).prod.id, will be lift |1| *)
(* ||1|| is not defined, no use for (PolyRing (PolyRing r)).prod.id  <-- why no use? *)

(* overload lift of polynomial addition *)
val _ = overload_on("|+|", ``(PolyRing (PolyModRing r z)).sum.op``);
val _ = set_fixity "|+|" (Infix(NONASSOC, 599)); (* not 600, L-associative *)
(* This is not +z *)

(* overload lift of polynomial multiplication *)
val _ = overload_on("|*|", ``(PolyRing (PolyModRing r z)).prod.op``);
val _ = set_fixity "|*|" (Infix(NONASSOC, 599)); (* not 600, L-associative *)
(* This is not *z *)

(* overload lift of poly *)
(* val _ = overload_on("lift_poly", ``Poly (PolyModRing r z)``); *)
(* This is now polyz *)

(* overload lift of deg *)
(* val _ = overload_on("lift_deg", ``poly_deg (PolyModRing r z)``); *)
(* This is now degz *)

(* overload lift of factor *)
(* val _ = overload_on("lift_factor", ``poly_factor (PolyModRing r z)``); *)
(* This is now factorz *)

(* overload lift of poly_root *)
(* val _ = overload_on("lift_root", ``\p q. poly_root (PolyModRing r z) (lift p) q``); *)
(* I have rootz = poly_root (PolyModRing r z) *)

(* Don't do this! *)
(* val poly_mod_ring_property = save_thm("poly_mod_ring_property", poly_mod_ring_property); *)

(* (PolyRing (PolyModRing r z)).carrier
Does this consists only of lift p, or more than that?
More. (PolyModRing r z) is Finite, (PolyRing (PolyModRing r z)) is infinite.
*)

(*
> poly_root_factor_eqn |> ISPEC ``(PolyModRing r z)``;
val it =  |- Ring (PolyModRing r z) ==>
   !p x. Poly (PolyModRing r z) p /\
     p <> (PolyRing (PolyModRing r z)).sum.id /\
     x IN (PolyModRing r z).carrier /\
     poly_root (PolyModRing r z) p x ==>
     ?q. Poly (PolyModRing r z) q /\
       (poly_deg (PolyModRing r z) q =
        PRE (poly_deg (PolyModRing r z) p)) /\ (p = q |*| lift_factor x): thm
*)

(* Theorem: Field r ==> !z. ipoly z ==>
            !p x. poly p /\ p <> |0| /\ poly x /\ deg x < deg z /\ rootz (lift p) x ==>
            ?q. polyz q /\ (degz q = PRE (deg p)) /\ (lift p = q |*| (factorz x)) *)
(* Proof:
   Since Field (PolyModRing r z)          by poly_mod_irreducible_field, ipoly z
     and pmonic z                         by poly_irreducible_pmonic
    also polyz (lift p)                   by poly_mod_lift_poly, pmonic z
     and lift p <> ||0||                  by poly_lift_eq_zero
    Note (PolyRing (PolyModRing r z)).sum.id = ||0||  by poly_mod_ring_zero
     Now x IN Rz                          by poly_mod_ring_property, deg x < deg z
     and degz (lift p) = deg p            by poly_mod_lift_deg, Ring r
   Since Ring (PolyModRing r z) /\ #1z <> #0z     by field_is_ring, field_one_ne_zero
   Hence polyz q exists with result       by poly_root_factor_eqn, poly_mod_ring_zero
*)
val poly_mod_lift_root_factor = store_thm(
  "poly_mod_lift_root_factor",
  ``!r:'a field. Field r ==> !z. ipoly z ==>
   !p x. poly p /\ p <> |0| /\ poly x /\ deg x < deg z /\ rootz (lift p) x ==>
   ?q. polyz q /\ (degz q = PRE (deg p)) /\ (lift p = q |*| (factorz x))``,
  rpt strip_tac >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  `polyz (lift p)` by rw[poly_mod_lift_poly] >>
  `lift p <> ||0||` by metis_tac[poly_lift_eq_zero] >>
  `(PolyRing (PolyModRing r z)).sum.id = ||0||` by rw[] >>
  `x IN Rz` by rw[poly_mod_ring_property] >>
  `degz (lift p) = deg p` by rw[poly_mod_lift_deg] >>
  `Ring (PolyModRing r z) /\ #1z <> #0z` by rw[] >>
  metis_tac[poly_root_factor_eqn, poly_mod_ring_zero]);

(* Theorem: Field r ==> !z. ipoly z /\ 1 < deg z ==>
            ?s:'a poly field. Field s /\ (s = PolyModRing r z) /\ rootz (lift z) X *)
(* Proof:
   Let s = (PolyModRing r z)
   Then Field s              by poly_mod_irreducible_field
   and poly z                by poly_irreducible_poly
   Hence rootz (lift z) X    by poly_field_mod_lift_has_root_X
*)
val poly_irreducible_has_field_with_root = store_thm(
  "poly_irreducible_has_field_with_root",
  ``!r:'a field. Field r ==> !z. ipoly z /\ 1 < deg z ==>
    ?s:'a poly field. Field s /\ (s = PolyModRing r z) /\ rootz (lift z) X``,
  rpt strip_tac >>
  qexists_tac `(PolyModRing r z)` >>
  rw_tac std_ss[poly_mod_irreducible_field] >>
  `poly z` by rw[poly_irreducible_poly] >>
  rw[poly_field_mod_lift_has_root_X]);

(* ------------------------------------------------------------------------- *)
(* Isomorphism between Field elements and Constant Polynomials               *)
(* ------------------------------------------------------------------------- *)

(* Note:
So far, I have not really captured the idea that a Ring r is embedded within its (PolyRing r), or (PolyModRing r z).
The following (PolyConst r) is to capture that idea by the basic up function: relating an element with its constant polynomial.
Aim is to show: Ring r ==> Ring (PolyConst r), and RingIso up r (PolyConst r).
and Field r ==> Field (PolyConst r), and FieldIso up r (PolyConst r).

This is essential because later, when X is an element in (PolyModRing r z),
and when we say: ipoly p now has root X,
what we mean is: p IN (PolyModRing r z) cannot be factorised, so ipoly p, thus no root in Field r.
But (lift p) in (PolyRing (PolyModRing r z)) has a root X, where (lift p = MAP up p).
*)

(* Define the ring of constant polynomials *)
val poly_mod_const_def = Define`
    poly_mod_const (r:'a ring) (z:'a poly) =
    <| carrier := IMAGE up R;
           sum := <|carrier := IMAGE up R; op := $+z; id := #0z |>;
          prod := <|carrier := IMAGE up R; op := $*z; id := #1z |>
     |>
`;

(* overload on constant polynomials of R[x]/z *)
val _ = overload_on ("PolyModConst", ``\r z. poly_mod_const r z``);

(* Overload carrier of PolyModConst r z *)
val _ = overload_on("RCz", ``(PolyModConst r z).carrier``);

(* Theorem: properties of PolyModConst r z *)
(* Proof: by poly_mod_const_def. *)
val poly_mod_const_property = store_thm(
  "poly_mod_const_property",
  ``!(r:'a ring) (z:'a poly).
     (!p. p IN RCz <=> ?c. c IN R /\ (p = up c)) /\
     ((PolyModConst r z).sum.op = $+z) /\
     ((PolyModConst r z).prod.op = $*z) /\
     ((PolyModConst r z).sum.carrier = RCz) /\
     ((PolyModConst r z).prod.carrier = RCz) /\
     ((PolyModConst r z).sum.id = #0z) /\
     ((PolyModConst r z).prod.id = #1z)``,
  rw_tac std_ss[poly_mod_const_def] >>
  (rw_tac std_ss[IN_IMAGE, EQ_IMP_THM] >> metis_tac[]));

(* Theorem: p IN RCz <=> ?c. c IN R /\ (p = up c) *)
(* Proof: by poly_mod_ring_property. *)
val poly_mod_const_element = store_thm(
  "poly_mod_const_element",
  ``!(r:'a ring) (z:'a poly). !p. p IN RCz <=> ?c. c IN R /\ (p = up c)``,
  rw_tac std_ss[poly_mod_const_property]);

(* Theorem: ((PolyModConst r z).sum.carrier = RCz) /\ ((PolyModConst r z).prod.carrier = RCz) *)
(* Proof: by poly_mod_const_property. *)
val poly_mod_const_carriers = store_thm(
  "poly_mod_const_carriers",
  ``!(r:'a ring) (z:'a poly). ((PolyModConst r z).sum.carrier = RCz) /\
                              ((PolyModConst r z).prod.carrier = RCz)``,
  rw_tac std_ss[poly_mod_const_property]);

(* Theorem: ((PolyModConst r z).sum.id = #0z) /\ ((PolyModConst r z).prod.id = #1z) *)
(* Proof: by poly_mod_const_property. *)
val poly_mod_const_ids = store_thm(
  "poly_mod_const_ids",
  ``!(r:'a ring) (z:'a poly). ((PolyModConst r z).sum.id = #0z) /\ ((PolyModConst r z).prod.id = #1z)``,
  rw_tac std_ss[poly_mod_const_property]);

(* Theorem: x IN RCz ==> poly x /\ (deg x = 0) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
   Thus poly x                      by up_poly
    and deg x = 0                   by up_deg
*)
val poly_mod_const_element_const = store_thm(
  "poly_mod_const_element_const",
  ``!r:'a ring. !(z:'a poly) x. x IN RCz ==> poly x /\ (deg x = 0)``,
  metis_tac[poly_mod_const_element, up_poly, up_deg]);

(* Theorem: BIJ up R RCz *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) e IN R ==> up e IN RCz, true                by poly_mod_const_element
   (2) up e = up e' ==> e = e', true               by up_eq
   (3) same as (1).
   (4) x IN RCz ==> ?e. e IN R /\ (up e = x), true by poly_mod_const_element
*)
val up_bij = store_thm(
  "up_bij",
  ``!r:'a ring. !z:'a poly. BIJ up R RCz``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  metis_tac[poly_mod_const_element] >-
  metis_tac[up_eq] >-
  metis_tac[poly_mod_const_element] >>
  metis_tac[poly_mod_const_element]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials Zero and One                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ 0 < deg z ==> (#1 = #0) <=> (#1z = #0z) *)
(* Proof:
        #1 = #0
   <=> |1| = |0|     by poly_one_eq_poly_zero
   <=> #1z = #0z     by poly_mod_ring_ids, 0 < deg z
*)
val poly_mod_const_one_eq_zero = store_thm(
  "poly_mod_const_one_eq_zero",
  ``!(r:'a ring) (z:'a poly). Ring r /\ 0 < deg z ==> ((#1 = #0) <=> (#1z = #0z))``,
  metis_tac[poly_one_eq_poly_zero, poly_mod_ring_ids, NOT_ZERO]);

(* Theorem: #0z = up #0 *)
(* Proof:
   #0z = |0|     by poly_mod_ring_ids
       = up #0   by up_zero
*)
val poly_mod_const_zero = store_thm(
  "poly_mod_const_zero",
  ``!(r:'a ring) (z:'a poly). #0z = up #0``,
  rw_tac std_ss[poly_mod_ring_ids, up_zero]);

(* Theorem: Ring r /\ 0 < deg z ==> (#1z = up #1) *)
(* Proof:
   If #1 = #0,
      Then #1z = #0z     by poly_mod_const_one_eq_zero, 0 < deg z
               = up #0   by poly_mod_const_zero
               = up #1   by #1 = #0
   If #1 <> #0
      Then #1z = |1|     by poly_mod_ring_ids, 0 < deg z
               = up #1   by up_one, #1 <> #0
*)
val poly_mod_const_one = store_thm(
  "poly_mod_const_one",
  ``!(r:'a ring) (z:'a poly). Ring r /\ 0 < deg z ==> (#1z = up #1)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_mod_const_one_eq_zero, poly_mod_const_zero] >>
  metis_tac[poly_mod_ring_ids, up_one, NOT_ZERO]);

(* Theorem: Ring r ==> #0z IN RCz *)
(* Proof:
   Since #0z = up #0   by poly_mod_const_zero
   Hence #0z IN RCz    by poly_mod_const_element, ring_zero_element
*)
val poly_mod_const_zero_element = store_thm(
  "poly_mod_const_zero_element",
  ``!(r:'a ring) (z:'a poly). Ring r ==> #0z IN RCz``,
  metis_tac[poly_mod_const_zero, poly_mod_const_element, ring_zero_element]);

(* Theorem: Ring r ==> #1z IN RCz *)
(* Proof:
   If deg z = 0,
      Then #1z = #0z    by poly_mod_ring_ids, deg z = 0
       and #0z IN RCz   by poly_mod_const_zero_element
   If deg z <> 0,
   Then #1z = up #1     by poly_mod_const_one, 0 < deg z
   Hence #1z IN RCz     by poly_mod_const_element, ring_one_element
*)
val poly_mod_const_one_element = store_thm(
  "poly_mod_const_one_element",
  ``!(r:'a ring) (z:'a poly). Ring r ==> #1z IN RCz``,
  rpt strip_tac >>
  Cases_on `deg z = 0` >| [
    `#1z = #0z` by rw[poly_mod_ring_ids] >>
    metis_tac[poly_mod_const_zero_element],
    metis_tac[poly_mod_const_one, poly_mod_const_element, ring_one_element, NOT_ZERO]
  ]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials Addition                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (PolyModConst r z).sum.op p q = p +z q *)
(* Proof: by poly_mod_const_property *)
val poly_mod_const_add = store_thm(
  "poly_mod_const_add",
  ``!r:'a ring. !p q z. (PolyModConst r z).sum.op p q = p +z q``,
  rw_tac std_ss[poly_mod_const_property]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x +z y IN RCz *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
        x +z y
      = (up u) +z (up v)
      = up (u + v)                  by up_mod_add
    Now u + v IN R                  by ring_add_element
     so up (u + v) IN RCz           by poly_mod_const_element
*)
val poly_mod_const_add_element = store_thm(
  "poly_mod_const_add_element",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x +z y IN RCz``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  `x +z y = up (u + v)` by rw[up_mod_add] >>
  `u + v IN R` by rw[] >>
  metis_tac[poly_mod_const_element]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x +z y = y +z x) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
        x +z y
      = (up u) +z (up v)
      = up (u + v)                  by up_mod_add
      = up (v + u)                  by ring_add_comm
      = (up v) +z (up u)            by up_mod_add
      = y +z x
*)
val poly_mod_const_add_comm = store_thm(
  "poly_mod_const_add_comm",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x +z y = y +z x)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  metis_tac[up_mod_add, ring_add_comm]);

(* Theorem: Ring r /\ pmonic z ==>
            !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x +z y +z t = x +z (y +z t)) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
    and ?w. w IN R /\ (t = up w)    by poly_mod_const_element
        x +z y +z t
      = (up u) +z (up v) +z (up w)
      = up (u + v) +z (up w)           by up_mod_add
      = up (u + v + w)                 by up_mod_add, ring_add_element
      = up (u + (v + w))               by ring_add_assoc
      = (up u) +z up (v + w)           by up_mod_add, ring_add_element
      = (up u) +z ((up v) +z (up w))   by up_mod_add
      = x +z (y +z t)
*)
val poly_mod_const_add_assoc = store_thm(
  "poly_mod_const_add_assoc",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x +z y +z t = x +z (y +z t))``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  `?w. w IN R /\ (t = up w)` by metis_tac[poly_mod_const_element] >>
  `x +z y = up (u + v)` by rw[up_mod_add] >>
  `up (u + v) +z t = up (u + v + w)` by rw[up_mod_add] >>
  `_ = up (u + (v + w))` by rw[ring_add_assoc] >>
  `_ = x +z up (v + w)` by rw[up_mod_add] >>
  `up (v + w) = y +z t` by rw[up_mod_add] >>
  rw_tac std_ss[]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (#0z +z x = x) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and #0z = up #0                 by poly_mod_const_zero
        #0z +z x
      = (up #0) +z (up u)
      = up (#0 + u)                 by up_mod_add
      = up u                        by ring_add_lzero
      = x
*)
val poly_mod_const_add_lzero = store_thm(
  "poly_mod_const_add_lzero",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (#0z +z x = x)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `#0z = up #0` by rw[poly_mod_const_zero] >>
  metis_tac[up_mod_add, ring_zero_element, ring_add_lzero]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z #0z = x) *)
(* Proof:
   Note #0z IN RCz        by poly_mod_const_zero_element
        x +z #0z
      = #0z +z x          by poly_mod_const_add_comm
      = x                 by poly_mod_const_add_lzero
*)
val poly_mod_const_add_rzero = store_thm(
  "poly_mod_const_add_rzero",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z #0z = x)``,
  metis_tac[poly_mod_const_add_lzero, poly_mod_const_zero_element, poly_mod_const_add_comm]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> ($-z x) IN RCz *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
        $-z x
      = $-z (up u)
      = up (-u)                     by up_mod_neg
    Now -u IN R                     by ring_neg_element
     so $-z x IN RCz                by poly_mod_const_element
*)
val poly_mod_const_neg_element = store_thm(
  "poly_mod_const_neg_element",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> ($-z x) IN RCz``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `$-z x = up (-u)` by rw[up_mod_neg] >>
  metis_tac[poly_mod_const_element, ring_neg_element]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (($-z x) +z x = #0z) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and $-z x = up (-u)             by up_mod_neg
        ($-z x) +z x
      = (up (-u)) +z (up u)
      = up (-u + u)                 by up_mod_add, ring_neg_element
      = up #0                       by ring_add_lneg
      = #0z                         by poly_mod_const_zero
*)
val poly_mod_const_add_lneg = store_thm(
  "poly_mod_const_add_lneg",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (($-z x) +z x = #0z)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `$-z x = up (-u)` by rw[up_mod_neg] >>
  `-u IN R` by rw[] >>
  metis_tac[up_mod_add, ring_add_lneg, poly_mod_const_zero]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z ($-z x) = #0z) *)
(* Proof:
   Note $-z x IN RCz      by poly_mod_const_neg_element
        x +z ($-z x)
      = ($-z x) +z x      by poly_mod_const_add_comm
      = #0z               by poly_mod_const_add_lneg
*)
val poly_mod_const_add_rneg = store_thm(
  "poly_mod_const_add_rneg",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x +z ($-z x) = #0z)``,
  metis_tac[poly_mod_const_add_lneg, poly_mod_const_neg_element, poly_mod_const_add_comm]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials Multiplication                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (PolyModConst r z).prod.op p q = p *z q *)
(* Proof: by poly_mod_const_property *)
val poly_mod_const_mult = store_thm(
  "poly_mod_const_mult",
  ``!r:'a ring. !p q z. (PolyModConst r z).prod.op p q = p *z q``,
  rw_tac std_ss[poly_mod_const_property]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x *z y IN RCz *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
        x *z y
      = (up u) *z (up v)
      = up (u * v)                  by up_mod_mult
    Now u * v IN R                  by ring_mult_element
     so up (u * v) IN RCz           by poly_mod_const_element
*)
val poly_mod_const_mult_element = store_thm(
  "poly_mod_const_mult_element",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> x *z y IN RCz``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  `x *z y = up (u * v)` by rw[up_mod_mult] >>
  `u * v IN R` by rw[] >>
  metis_tac[poly_mod_const_element]);

(* Theorem: Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x *z y = y *z x) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
        x *z y
      = (up u) *z (up v)
      = up (u * v)                  by up_mod_mult
      = up (v * u)                  by ring_mult_comm
      = (up v) *z (up u)            by up_mod_mult
      = y *z x
*)
val poly_mod_const_mult_comm = store_thm(
  "poly_mod_const_mult_comm",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x y. x IN RCz /\ y IN RCz ==> (x *z y = y *z x)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  metis_tac[up_mod_mult, ring_mult_comm]);

(* Theorem: Ring r /\ pmonic z ==>
            !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z y *z t = x *z (y *z t)) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
    and ?w. w IN R /\ (t = up w)    by poly_mod_const_element
        x *z y *z t
      = (up u) *z (up v) *z (up w)
      = up (u * v) *z (up w)           by up_mod_mult
      = up (u * v * w)                 by up_mod_mult, ring_mult_element
      = up (u * (v * w))               by ring_mult_assoc
      = (up u) *z up (v * w)           by up_mod_mult, ring_mult_element
      = (up u) *z ((up v) *z (up w))   by up_mod_mult
      = x *z (y *z t)
*)
val poly_mod_const_mult_assoc = store_thm(
  "poly_mod_const_mult_assoc",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z y *z t = x *z (y *z t))``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  `?w. w IN R /\ (t = up w)` by metis_tac[poly_mod_const_element] >>
  `x *z y = up (u * v)` by rw[up_mod_mult] >>
  `up (u * v) *z t = up (u * v * w)` by rw[up_mod_mult] >>
  `_ = up (u * (v * w))` by rw[ring_mult_assoc] >>
  `_ = x *z up (v * w)` by rw[up_mod_mult] >>
  `up (v * w) = y *z t` by rw[up_mod_mult] >>
  rw_tac std_ss[]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (#1z *z x = x) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and #1z = up #1                 by poly_mod_const_one
        #1z *z x
      = (up #1) *z (up u)
      = up (#1 * u)                 by up_mod_mult
      = up u                        by ring_mult_lone
      = x
*)
val poly_mod_const_mult_lone = store_thm(
  "poly_mod_const_mult_lone",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (#1z *z x = x)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `#1z = up #1` by rw[poly_mod_const_one] >>
  metis_tac[up_mod_mult, ring_one_element, ring_mult_lone]);

(* Theorem: Ring r /\ pmonic z ==> !x. x IN RCz ==> (x *z #1z = x) *)
(* Proof:
   Note #1z IN RCz        by poly_mod_const_one_element
        x *z #1z
      = #1z +z x          by poly_mod_const_mult_comm
      = x                 by poly_mod_const_mult_lone
*)
val poly_mod_const_mult_rone = store_thm(
  "poly_mod_const_mult_rone",
  ``!r:'a ring z. Ring r /\ pmonic z ==> !x. x IN RCz ==> (x *z #1z = x)``,
  metis_tac[poly_mod_const_mult_lone, poly_mod_const_one_element, poly_mod_const_mult_comm]);

(* Theorem: Field r /\ ipoly z ==>
            !x. x IN RCz /\ x <> #0z ==> ( |/z x) IN RCz /\ ( |/z x) <> #0z *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and x <> #0z ==> u <> #0        by up_eq_zero, poly_mod_ring_ids
   thus u IN R+                     by field_nonzero_eq
        |/z x
      = |/z (up u)
      = up ( |/ u)                  by up_mod_inv, u IN R+
    Now |/ u IN R                   by field_inv_element
     so |/z x IN RCz                by poly_mod_const_element
   Also |/ u IN R+                  by field_inv_nonzero
     so |/ u <> #0                  by field_nonzero_eq
     or |/z x <> #0z                by up_eq_zero, poly_mod_ring_ids
*)
val poly_mod_const_inv_element = store_thm(
  "poly_mod_const_inv_element",
  ``!r:'a field. Field r ==> !z. ipoly z ==>
   !x. x IN RCz /\ x <> #0z ==> ( |/z x) IN RCz /\ ( |/z x) <> #0z``,
  ntac 6 strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `u IN R+` by metis_tac[up_eq_zero, poly_mod_ring_ids, field_nonzero_eq] >>
  `|/ u IN R+` by rw[field_inv_nonzero] >>
  `|/ u IN R /\ |/ u <> #0` by metis_tac[field_nonzero_eq] >>
  `|/z x = up ( |/ u)` by rw[up_mod_inv] >>
  metis_tac[poly_mod_const_element, up_eq_zero, poly_mod_ring_ids]);

(* Theorem: Field r ==> !z. monic z /\ ipoly z ==>
            !x. x IN RCz /\ x <> #0z ==> (( |/z x) *z x = #1z) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and x <> #0z ==> u <> #0        by up_eq_zero, poly_mod_ring_ids
   thus u IN R+                     by field_nonzero_eq
    and |/z x = up ( |/ u)          by up_mod_inv, u IN R+
    Now pmonic z                    by poly_irreducible_pmonic
        ( |/z x) *z x
      = (up ( |/ u) *z (up u)
      = up ( |/ u * u)              by up_mod_mult, field_inv_element
      = up #1                       by field_mult_linv
      = #1z                         by poly_mod_const_one
*)
val poly_mod_const_mult_linv = store_thm(
  "poly_mod_const_mult_linv",
  ``!r:'a field. Field r ==> !z. ipoly z ==>
   !x. x IN RCz /\ x <> #0z ==> (( |/z x) *z x = #1z)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `u IN R+` by metis_tac[up_eq_zero, poly_mod_ring_ids, field_nonzero_eq] >>
  `|/z x = up ( |/ u)` by rw[up_mod_inv] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  metis_tac[up_mod_mult, field_inv_element, field_mult_linv, poly_mod_const_one]);

(* Theorem: Field r /\ ipoly z ==>
            !x. x IN RCz /\ x <> #0z ==> (x *z ( |/z x) = #1z) *)
(* Proof:
   Note |/z c IN RCz      by poly_mod_const_inv_element
    Now pmonic z          by poly_irreducible_pmonic
        x *z ( |/z x)
      = ( |/z x) *z x     by poly_mod_const_mult_comm
      = #1z               by poly_mod_const_mult_linv
*)
val poly_mod_const_mult_rinv = store_thm(
  "poly_mod_const_mult_rinv",
  ``!r:'a ring. Field r ==> !z. ipoly z ==>
   !x. x IN RCz /\ x <> #0z ==> (x *z ( |/z x) = #1z)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  metis_tac[poly_mod_const_mult_linv, poly_mod_const_inv_element, poly_mod_const_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials Distribution Law                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ pmonic z ==>
            !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> ((x +z y) *z t = x *z t +z y *z t) *)
(* Proof:
   Note ?u. u IN R /\ (x = up u)    by poly_mod_const_element
    and ?v. v IN R /\ (y = up v)    by poly_mod_const_element
    and ?w. w IN R /\ (t = up w)    by poly_mod_const_element
        (x +z y) *z t
      = ((up u) +z (up v)) *z (up w))
      = up (u + v) *z (up w)           by up_mod_add
      = up ((u + v) * w))              by up_mod_mult
      = up (u * w + v * w)             by ring_mult_ladd
      = up (u * w) +z up (v * w)       by up_mod_add, ring_mult_element
      = ((up u) *z (up w)) +z ((up v) * (up w))   by up_mod_mult
      = x *z t +z y *z t
*)
val poly_mod_const_mult_ladd = store_thm(
  "poly_mod_const_mult_ladd",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> ((x +z y) *z t = x *z t +z y *z t)``,
  rpt strip_tac >>
  `?u. u IN R /\ (x = up u)` by metis_tac[poly_mod_const_element] >>
  `?v. v IN R /\ (y = up v)` by metis_tac[poly_mod_const_element] >>
  `?w. w IN R /\ (t = up w)` by metis_tac[poly_mod_const_element] >>
  `x +z y = up (u + v)` by rw[up_mod_add] >>
  `x *z t = up (u * w)` by rw[up_mod_mult] >>
  `y *z t = up (v * w)` by rw[up_mod_mult] >>
  `up (u + v) *z t = up ((u + v) * w)` by rw[up_mod_mult] >>
  `_ = up (u * w + v * w)` by rw[ring_mult_ladd] >>
  `_ = up (u * w) +z up (v * w)` by rw[up_mod_add] >>
  rw_tac std_ss[]);

(* Theorem: Ring r /\ pmonic z ==>
            !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z (y +z t) = x *z y +z x *z t) *)
(* Proof:
   Note y +z t IN RCz       by poly_mod_const_add_element
        x *z (y +z t)
      = (y +z t) *z x       by poly_mod_const_mult_comm
      = y *z x +z t *z x    by poly_mod_const_mult_ladd
      = x *z y +z x *z t    by poly_mod_const_mult_comm
*)
val poly_mod_const_mult_radd = store_thm(
  "poly_mod_const_mult_radd",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !x y t. x IN RCz /\ y IN RCz /\ t IN RCz ==> (x *z (y +z t) = x *z y +z x *z t)``,
  rpt strip_tac >>
  `y +z t IN RCz` by rw[poly_mod_const_add_element] >>
  `x *z (y +z t) = (y +z t) *z x` by rw_tac std_ss[poly_mod_const_mult_comm] >>
  `_ = y *z x +z t *z x` by rw[poly_mod_const_mult_ladd] >>
  rw[poly_mod_const_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials as Field                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ pmonic z ==> AbelianGroup (PolyModConst r z).sum *)
(* Proof:
   By group definition, this is to show:
   (1) x IN RCz /\ y IN RCz ==> x +z y IN RCz, true       by poly_mod_const_add_element
   (2) x IN RCz /\ y IN RCz /\ z' IN RCz ==>
       x +z y +z z' = x +z (y +z z'), true                by poly_mod_const_add_assoc
   (3) #0z IN RCz, true                                   by poly_mod_const_zero_element
   (4) #0z +z x = x, true                                 by poly_mod_const_add_lzero
   (5) ?y. y IN RCz /\ (y +z x = #0z)
       Let y = $-z x.
       Then y IN RCz                                      by poly_mod_const_neg_element
        and y +z x = #0z                                  by poly_mod_const_add_lneg
   (6) x IN RCz /\ y IN RCz ==> x +z y = y +z x, true     by poly_mod_const_add_comm
*)
val poly_mod_const_sum_abelian_group = store_thm(
  "poly_mod_const_sum_abelian_group",
  ``!r:'a ring z. Ring r /\ pmonic z ==> AbelianGroup (PolyModConst r z).sum``,
  rw_tac std_ss[AbelianGroup_def, group_def_alt, poly_mod_const_carriers, poly_mod_const_add, poly_mod_const_ids] >-
  rw[poly_mod_const_add_element] >-
  rw[poly_mod_const_add_assoc] >-
  rw[poly_mod_const_zero_element] >-
  rw[poly_mod_const_add_lzero] >-
  metis_tac[poly_mod_const_neg_element, poly_mod_const_add_lneg] >>
  rw[poly_mod_const_add_comm]);

(* Theorem: Ring r /\ pmonic z ==> AbelianMonoid (PolyModConst r z).prod *)
(* Proof:
   By monoid definition, this is to show:
   (1) x IN RCz /\ y IN RCz ==> x *z y IN RCz, true     by poly_mod_const_mult_element
   (2) x IN RCz /\ y IN RCz /\ z' IN RCz ==>
       x *z y *z z' = x *z (y *z z'), true              by poly_mod_const_mult_assoc
   (3) #1z IN RCz, true                                 by poly_mod_const_one_element
   (4) x IN RCz ==> #1z *z x = x, true                  by poly_mod_const_mult_lone
   (5) x IN RCz ==> x *z #1z = x, true                  by poly_mod_const_mult_rone
   (6) x IN RCz /\ y IN RCz ==> x *z y = y *z x, true   by poly_mod_const_mult_comm
*)
val poly_mod_const_prod_abelian_monoid = store_thm(
  "poly_mod_const_prod_abelian_monoid",
  ``!r:'a ring z. Ring r /\ pmonic z ==> AbelianMonoid (PolyModConst r z).prod``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, poly_mod_const_carriers, poly_mod_const_mult, poly_mod_const_ids] >-
  rw[poly_mod_const_mult_element] >-
  rw[poly_mod_const_mult_assoc] >-
  rw[poly_mod_const_one_element] >-
  rw[poly_mod_const_mult_lone] >-
  rw[poly_mod_const_mult_rone] >>
  rw[poly_mod_const_mult_comm]);

(* Theorem: Ring r /\ pmonic z ==> Ring (PolyModConst r z) *)
(* Proof:
   By Ring_def, this is to show:
   (1) AbelianGroup (PolyModConst r z).sum, true    by poly_mod_const_sum_abelian_group
   (2) AbelianMonoid (PolyModConst r z).prod, true  by poly_mod_const_prod_abelian_monoid
   (3) (PolyModConst r z).sum.carrier = RCz, true   by poly_mod_const_carriers
   (4) (PolyModRing r z).prod.carrier = Rz, true    by poly_mod_const_carriers
   (5) x IN RCz /\ y IN RCz /\ z' IN RCz
       ==> x *z (y +z z') = x *z y +z x *z z', true by poly_mod_const_mult_radd
*)
val poly_mod_const_ring = store_thm(
  "poly_mod_const_ring",
  ``!r:'a ring z. Ring r /\ pmonic z ==> Ring (PolyModConst r z)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, poly_mod_const_add, poly_mod_const_mult] >-
  rw[poly_mod_const_sum_abelian_group] >-
  rw[poly_mod_const_prod_abelian_monoid] >-
  rw[poly_mod_const_carriers] >-
  rw[poly_mod_const_carriers] >>
  rw[poly_mod_const_mult_radd]);

(* Theorem: Field r /\ ipoly z ==> Field (PolyModConst r z) *)
(* Proof:
   Note pmonic z          by poly_irreducible_pmonic

   By field_def_by_inv, this is to show:
   (1) Ring (PolyModConst r z), true   by poly_mod_const_ring
   (2) #1z <> #0z
       Since #1 <> #0     by field_one_ne_zero
          so #1z <> #0z   by poly_mod_const_one_eq_zero
   (3) x IN RCz /\ x <> #0z ==> ?y. y IN RCz /\ (x *z y = #1z)
       Take y = |/z x.
       Then y IN RCz      by poly_mod_const_inv_element
        and x *z y = #1z  by poly_mod_const_mult_rinv
*)
val poly_mod_const_field = store_thm(
  "poly_mod_const_field",
  ``!r:'a field z. Field r /\ ipoly z ==> Field (PolyModConst r z)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  rw_tac std_ss[field_def_by_inv, poly_mod_const_mult, poly_mod_const_ids] >-
  rw[poly_mod_const_ring] >-
  rw[GSYM poly_mod_const_one_eq_zero] >>
  metis_tac[poly_mod_const_inv_element, poly_mod_const_mult_rinv]);

(* This is a major theorem. *)

(* Theorem: FiniteField r /\ ipoly z ==> FiniteField (PolyModConst r z) *)
(* Proof:
   By FiniteField_def, this is to show:
   (1) Field (PolyModConst r z), true    by poly_mod_const_field
   (2) FINITE R ==> FINITE RCz, true     by poly_mod_const_def, IMAGE_FINITE
*)
val poly_mod_const_finite_field = store_thm(
  "poly_mod_const_finite_field",
  ``!r:'a field z. FiniteField r /\ ipoly z ==> FiniteField (PolyModConst r z)``,
  rw[FiniteField_def, poly_mod_const_field, poly_mod_const_def]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials as Subfield                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ pmonic z ==> subring (PolyModConst r z) (PolyModRing r z) *)
(* Proof:
   By subring_def, RingHomo_def, this is to show:
   (1) x IN RCz ==> x IN Rz
           x IN RCz
       ==> poly x /\ (deg x = 0)            by poly_mod_const_element_const
       ==> poly x /\ (deg x < deg z)        by pmonic z, 0 < deg z
       ==> x IN Rz                          by poly_mod_ring_element, 0 < deg z
   (2) GroupHomo I (PolyModConst r z).sum (PolyModRing r z).sum
       By GroupHomo_def, poly_mod_ring_carriers, poly_mod_const_property, this is to show:
       (1) c IN R ==> up c IN Rz, true      by up_element
   (3) MonoidHomo I (PolyModConst r z).prod (PolyModRing r z).prod
       By MonoidHomo_def, poly_mod_ring_carriers, poly_mod_const_property, this is to show:
       (1) c IN R ==> up c IN Rz, true      by up_element
*)
val poly_mod_const_subring_poly_mod = store_thm(
  "poly_mod_const_subring_poly_mod",
  ``!r:'a ring z. Ring r /\ pmonic z ==> subring (PolyModConst r z) (PolyModRing r z)``,
  rw_tac std_ss[subring_def, RingHomo_def] >-
  metis_tac[poly_mod_const_element_const, poly_mod_ring_element, NOT_ZERO] >-
 (rw_tac std_ss[GroupHomo_def, poly_mod_ring_carriers, poly_mod_const_property] >>
  rw[up_element]) >>
  rw_tac std_ss[MonoidHomo_def, poly_mod_ring_carriers, poly_mod_const_property] >>
  rw[up_element]);

(* Theorem: Field r /\ ipoly z ==> subfield (PolyModConst r z) (PolyModRing r z) *)
(* Proof:
    Note pmonic z                                       by poly_irreducible_pmonic
     ==> subring (PolyModConst r z) (PolyModRing r z)   by poly_mod_const_subring_poly_mod
   Hence subfield (PolyModConst r z) (PolyModRing r z)  by subfield_def, subring_def, FieldHomo_def
*)
val poly_mod_const_subfield_poly_mod = store_thm(
  "poly_mod_const_subfield_poly_mod",
  ``!r:'a field z. Field r /\ ipoly z ==> subfield (PolyModConst r z) (PolyModRing r z)``,
  rpt strip_tac >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  `subring (PolyModConst r z) (PolyModRing r z)` by rw[poly_mod_const_subring_poly_mod] >>
  metis_tac[subfield_def, subring_def, FieldHomo_def]);

(* This is a major theorem. *)

(* Theorem: Field r /\ ipoly z ==> (PolyModConst r z) <<= (PolyModRing r z) *)
(* Proof:
   This is to show:
   (1) Field (PolyModRing r z), true                        by poly_mod_irreducible_field
   (2) Field (PolyModConst r z), true                       by poly_mod_const_field
   (3) subfield (PolyModConst r z) (PolyModRing r z), true  by poly_mod_const_subfield_poly_mod
*)
val poly_mod_const_subfield_poly_mod_alt = store_thm(
  "poly_mod_const_subfield_poly_mod_alt",
  ``!r:'a field z. Field r /\ ipoly z ==> (PolyModConst r z) <<= (PolyModRing r z)``,
  rw_tac std_ss[poly_mod_irreducible_field, poly_mod_const_field, poly_mod_const_subfield_poly_mod]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials as isomorphic Field                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ pmonic z ==> RingHomo up r (PolyModConst r z) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) e IN R ==> up e IN RCz, true   by poly_mod_const_element
   (2) GroupHomo (\e. up e) r.sum (PolyModConst r z).sum
       By GroupHomo_def, poly_mod_const_property, ring_carriers, this is to show:
       (1) e IN R ==> ?c. c IN R /\ (up e = up c), true            by taking c = e.
       (2) e IN R /\ e' IN R ==> up (e + e') = up e +z up e', true by up_mod_add
   (3) MonoidHomo (\e. up e) r.prod (PolyModConst r z).prod
       By MonoidHomo_def, poly_mod_const_property, ring_carriers, this is to show:
       (1) ?c. c IN R /\ (up e = up c), true                       by taking c = e.
       (2) e IN R /\ e' IN R ==> up (e * e') = up e *z up e', true by up_mod_mult
       (3) #1 = #0 ==> |0| = #1z,
           #1 = #0 ==> #1z = #0z      by poly_mod_const_one_eq_zero, 0 < deg z
                   ==> #1z = |0|      by poly_mod_ring_ids, 0 < deg z
       (4) same as (1).
       (5) same as (2).
       (6) #1 <> #0 ==> [#1] = #1z
           #1z = up #1                by poly_mod_const_one, 0 < deg z
               = [#1]                 by notation, #1 <> #0
*)
val poly_mod_const_homo_ring = store_thm(
  "poly_mod_const_homo_ring",
  ``!r:'a ring z. Ring r /\ pmonic z ==> RingHomo up r (PolyModConst r z)``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[poly_mod_const_element] >-
 (rw_tac std_ss[GroupHomo_def, poly_mod_const_property, ring_carriers] >-
  metis_tac[] >>
  rw[up_mod_add]) >>
  rw_tac std_ss[MonoidHomo_def, poly_mod_const_property, ring_carriers] >-
  metis_tac[] >-
  rw[up_mod_mult] >-
  metis_tac[poly_mod_const_one_eq_zero, poly_mod_ring_ids, NOT_ZERO] >-
  metis_tac[] >-
  rw[up_mod_mult] >>
  rw[poly_mod_const_one]);

(* Theorem: Ring r /\ pmonic z ==> RingIso up r (PolyModConst r z) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo (\e. up e) r (PolyModConst r z), true by poly_mod_const_homo_ring
   (2) BIJ (\e. up e) R RCz, true                     by up_bij
*)
val poly_mod_const_iso_ring = store_thm(
  "poly_mod_const_iso_ring",
  ``!r:'a ring z. Ring r /\ pmonic z ==> RingIso up r (PolyModConst r z)``,
  rw_tac std_ss[RingIso_def] >-
  rw[poly_mod_const_homo_ring] >>
  rw[up_bij]);

(* Theorem: Field r /\ pmonic z ==> FieldHomo up r (PolyModConst r z) *)
(* Proof:
   By FieldHomo_def, this is to show:
      RingHomo (\e. up e) r (PolyModConst r z), true by poly_mod_const_homo_ring
*)
val poly_mod_const_homo_field = store_thm(
  "poly_mod_const_homo_field",
  ``!r:'a field z. Field r /\ pmonic z ==> FieldHomo up r (PolyModConst r z)``,
  rw[FieldHomo_def, poly_mod_const_homo_ring]);

(* Theorem: Field r /\ ipoly z ==> FieldHomo up r (PolyModConst r z) *)
(* Proof:
   Note ipoly z ==> pmonic z               by poly_irreducible_pmonic
   Thus FieldHomo up r (PolyModConst r z)  by poly_mod_const_homo_field
*)
val poly_mod_const_homo_field_alt = store_thm(
  "poly_mod_const_homo_field_alt",
  ``!r:'a field z. Field r /\ ipoly z ==> FieldHomo up r (PolyModConst r z)``,
  rw_tac std_ss[poly_irreducible_pmonic, poly_mod_const_homo_field]);

(* Theorem: Field r /\ pmonic z ==> FieldIso up r (PolyModConst r z) *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo (\e. up e) r (PolyModConst r z), true by poly_mod_const_homo_field
   (2) BIJ (\e. up e) R RCz, true                      by up_bij
*)
val poly_mod_const_iso_field = store_thm(
  "poly_mod_const_iso_field",
  ``!r:'a field z. Field r /\ pmonic z ==> FieldIso up r (PolyModConst r z)``,
  rw_tac std_ss[FieldIso_def] >-
  rw[poly_mod_const_homo_field] >>
  rw[up_bij]);

(* This is a major theorem. *)

(* Theorem: Field r /\ ipoly z ==> FieldIso up r (PolyModConst r z) *)
(* Proof:
   Note ipoly z ==> pmonic z               by poly_irreducible_pmonic
   Thus FieldIso up r (PolyModConst r z)   by poly_mod_const_iso_field
   Note pmonic z   by poly_monic_irreducible_property
   Hence true      by poly_mod_const_iso_field
*)
val poly_mod_const_iso_field_alt = store_thm(
  "poly_mod_const_iso_field_alt",
  ``!r:'a field z. Field r /\ ipoly z ==> FieldIso up r (PolyModConst r z)``,
  rw_tac std_ss[poly_mod_const_iso_field, poly_irreducible_pmonic]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
