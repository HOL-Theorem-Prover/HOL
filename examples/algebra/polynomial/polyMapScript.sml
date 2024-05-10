(* ------------------------------------------------------------------------ *)
(* Polynomial Maps                                                          *)
(* ------------------------------------------------------------------------ *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyMap";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open arithmeticTheory pred_setTheory listTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;

(* (* val _ = load "polyEvalTheory"; *) *)
open polyMonicTheory polyEvalTheory;

(* (* val _ = load "polyRootTheory"; *) *)
open polyRootTheory;
open polyDividesTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;

open polyIrreducibleTheory;
open polyProductTheory;
open polyMultiplicityTheory;
open polyBinomialTheory; (* for coefficients *)

open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open subgroupTheory;

open groupMapTheory ringMapTheory fieldMapTheory;

open ringBinomialTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;

(* val _ = load "fieldOrderTheory"; *)
open fieldOrderTheory; (* for field_order_eqn *)
open groupCyclicTheory; (* for orders_def *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Maps Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   r ~~r r_          = Ring r /\ Ring r_ /\ ?f. RingHomo f r r_
   r ==r r_          = Ring r /\ Ring r_ /\ ?f. RingIso f r r_
   r ~f~ r_          = Field r /\ Field r_ /\ ?f. FieldHomo f r r_
   r =f= r_          = Field r /\ Field r_ /\ ?f. FieldIso f r r_
   r ~ff~ r_         = FiniteField r /\ FiniteField r_ /\ ?f. FieldHomo f r r_
   r =ff= r_         = FiniteField r /\ FiniteField r_ /\ ?f. FieldIso f r r_

   S_                = (s_:'b ring).carrier
   S+_               = ring_nonzero (s_:'b ring)

   zerop_            = zero_poly (r_:'b ring)
   weak_             = Weak (r_:'b ring)
   poly_             = Poly (r_:'b ring)
   chop_             = poly_chop (r_:'b ring)
   neg_              = weak_neg (r_:'b ring)
   -_                = poly_neg (r_:'b ring)
   ||_               = weak_add (r_:'b ring)
   +_                = poly_add (r_:'b ring)
   -_                = poly_sub (r_:'b ring)
   o_                = weak_cmult (r_:'b ring)
   *_                = poly_cmult (r_:'b ring)
   o_                = weak_mult (r_:'b ring)
   *_                = poly_mult (r_:'b ring)
   >>_               = poly_shift (r_:'b ring)
   **_               = poly_exp (r_:'b ring)
   deg_              = poly_deg (r_:'b ring)
   lead_             = poly_lead (r_:'b ring)
   '_                = poly_coeff (r_:'b ring)
   /_                = poly_div (r_:'b ring)
   %_                = poly_mod (r_:'b ring)
   p_                = MAP (f:'a -> 'b) (p:'a poly)
   q_                = MAP (f:'a -> 'b) (q:'a poly)
   |0|_              = poly_zero (r_:'b ring)
   |1|_              = poly_one (r_:'b ring)
   |c|_              = poly_num (r_:'b ring) c
   X_                = |1|_ >>_ 1
   eval_             = poly_eval (r_:'b ring)
   factor_ c         = poly_factor (r_:'b field) c
   root_             = poly_root (r_:'b ring)
   roots_            = poly_roots (r_:'b ring)
   pdivides_         = poly_divides (r_:'b field)
   unity_            = Unity (r_:'b ring)
   master_           = Master (r_:'b ring)
   monic_            = Monic (r_:'b ring)
   ulead_            = Ulead (r_:'b ring)``);
   pmonic_           = Pmonic (r_:'b ring)``);
   upoly_ p          = p IN (Invertibles (PolyRing (r_:'b ring)).prod).carrier
   ipoly_            = IPoly (r_:'b ring)
*)
(* Definitions and Theorems (# are exported):

   Polynomial Ring Homomorphism and Isomorphism:
   zero_poly_map           |- !r f p. (f #0 = #0) /\ zerop p ==> zerop (MAP f p)
   poly_chop_map           |- !r f p. (f #0 = #0) ==> (chop (MAP f (chop p)) = chop (MAP f p))
   poly_eq_map             |- !r s f p q. (p = q) ==> (MAP f p = MAP f q)
   poly_deg_map            |- !r s f p. poly_deg s (MAP f p) = deg p

   Ring Homomorphism:
   ring_homo_zero_poly     |- !r r_ f. (r ~r~ r_) f ==> !p. zerop p ==> zerop_ p_
   ring_homo_eq_zero_poly  |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (zerop p <=> zerop_ p_)
   ring_homo_weak          |- !r r_ f. RingHomo f r r_ ==> !p. weak p ==> weak_ p_
   ring_homo_poly          |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> poly_ p_
   ring_homo_poly_of_chop  |- !r r_ f. RingHomo f r r_ ==> !p. poly p ==> poly_ (chop_ p_)
   ring_homo_eq_poly_zero  |- !r r_ f p. (p = |0|) <=> (p_ = |0|_)
   ring_homo_poly_zero     |- !r r_ f. MAP f |0| = |0|_
   ring_homo_poly_one      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> (MAP f |1| = |1|_)
   ring_homo_poly_one_alt  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f |1| = |1|_)
   ring_homo_poly_chop     |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)
   ring_homo_poly_chop_of_chop  |- !r r_ f. (r ~r~ r_) f ==> !p. chop_ (MAP f (chop p)) = chop_ p_
   ring_homo_weak_add      |- !r r_ f. (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)
   ring_homo_poly_add      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)
   ring_homo_poly_add_chop |- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p + q)) = p_ +_ q_)
   ring_homo_weak_neg      |- !r r_ f. (r ~r~ r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)
   ring_homo_poly_neg      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> (MAP f (-p) = $-_ p_)
   ring_homo_poly_neg_chop |- !r r_ f. (r ~r~ r_) f ==> !p. poly p ==> (chop_ (MAP f (-p)) = $-_ (chop_ p_))
   ring_homo_poly_sub      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)
   ring_homo_poly_sub_chop |- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p - q)) = p_ -_ chop_ q_)
   ring_homo_poly_deg      |- !r r_ f p. deg_ p_ = deg p
   ring_homo_poly_lead     |- !r r_ f. (r ~r~ r_) f ==> !p. lead_ p_ = f (lead p)
   ring_homo_poly_coeff    |- !r r_ f. (r ~r~ r_) f ==> !p k. p_ '_ k = f (p ' k)
   ring_homo_weak_cmult    |- !r r_ f. (r ~r~ r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = f c o_ p_)
   ring_homo_poly_cmult    |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = f c *_ p_)
   ring_homo_poly_cmult_chop |- !r r_ f. (r ~r~ r_) f ==> !p c. poly p /\ c IN R ==> (chop_ (MAP f (c * p)) = f c *_ p_)
   ring_homo_poly_shift    |- !r r_ f. (r ~r~ r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n
   ring_homo_weak_mult     |- !r r_ f. (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)
   ring_homo_poly_mult     |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)
   ring_homo_poly_mult_chop|- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p * q)) = p_ *_ q_)
   ring_homo_poly_exp      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n
   ring_homo_poly_exp_chop |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. poly p ==> !n. chop_ (MAP f (p ** n)) = p_ **_ n
   ring_homo_poly_eval     |- !r r_ f. (r ~r~ r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))
   ring_homo_poly_root     |- !r r_ f. (r ~r~ r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)
   ring_homo_poly_divides  |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_
   ring_homo_poly_divides_chop |- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> chop_ p_ pdivides_ chop_ q_

   Homomorphism between Polynomial Rings:
   ring_homo_poly_ring_homo    |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_)
   ring_homo_group_homo_poly   |- !r r_ f. (r ~r~ r_) f ==> GroupHomo (chop_ o MAP f) (PolyRing r).sum (PolyRing r_).sum
   ring_homo_monoid_homo_poly  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> MonoidHomo (chop_ o MAP f) (PolyRing r).prod (PolyRing r_).prod
   ring_homo_ring_homo_poly    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> RingHomo (chop_ o MAP f) (PolyRing r) (PolyRing r_)

   More Ring Homomorphism Theorems:
   ring_homo_poly_X          |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f X = X_)
   ring_homo_poly_sum_num    |- !r r_ f. (r ~r~ r_) f ==> !c. 0 < c /\ c < char r_ ==> (MAP f |c| = |c|_)
   ring_homo_weak_monic_poly |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. weak p /\ (lead p = #1) ==> poly_ p_
   ring_homo_monic_monic     |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> monic_ p_
   ring_homo_monic_exp_monic |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> !n. monic_ (MAP f (p ** n))
   ring_homo_monic_poly_exp  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> !n. MAP f (p ** n) = p_ **_ n
   ring_homo_poly_sum_num_poly |- !r r_ f. (r ~r~ r_) f ==> !c. 0 < c /\ c < char r_ ==> poly_ (MAP f |c|)

   ring_homo_X_add_c_monic   |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. monic_ (MAP f (X + |c|))
   ring_homo_X_add_c_poly    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. poly_ (MAP f (X + |c|))
   ring_homo_poly_X_add_c    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. MAP f (X + |c|) = (MAP f X) +_ (MAP f |c|)
   ring_homo_X_exp_n_add_c_monic
                             |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. 0 < n ==> !c. monic_ (MAP f (X ** n + |c|))
   ring_homo_X_exp_n_add_c_poly
                             |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. 0 < n ==> !c. poly_ (MAP f (X ** n + |c|))
   ring_homo_poly_X_exp_n_add_c
                             |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n c. 0 < n ==> (MAP f (X ** n + |c|) = MAP f X **_ n +_ MAP f |c|)
   ring_homo_X_sub_c_monic   |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. monic_ (MAP f (X - |c|))
   ring_homo_X_sub_c_poly    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. poly_ (MAP f (X - |c|))
   ring_homo_poly_X_sub_c    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. 0 < c /\ c < char r_ ==> (MAP f (X - |c|) = MAP f X -_ MAP f |c|)
   ring_homo_X_exp_n_sub_c_monic   |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. 0 < n ==> !c. monic_ (MAP f (X ** n - |c|))
   ring_homo_X_exp_n_sub_c_poly    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. 0 < n ==> !c. poly_ (MAP f (X ** n - |c|))
   ring_homo_poly_X_exp_n_sub_c    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. 0 < n ==>
                                      !c. 0 < c /\ c < char r_ ==> (MAP f (X ** n - |c|) = MAP f X **_ n -_ MAP f |c|)

   ring_homo_unity_poly  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. poly_ (MAP f (unity n))
   ring_homo_poly_unity  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. MAP f (unity n) = MAP f X **_ n -_ MAP f |1|
   ring_homo_peval_chop  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p q. poly p /\ poly q ==>
                                     (chop_ (MAP f (peval p q)) = peval_ p_ q_)
   ring_homo_poly_nonzero       |- !r r_ f. (r ~r~ r_) f ==> !p. poly p /\ f (lead p) <> #0_ ==>
                                            poly_ p_ /\ MAP f p <> |0|_
   ring_homo_poly_negate        |- !r r_ f. (r ~r~ r_) f ==> !p. poly p /\ f (lead p) <> #0_ ==>
                                            (MAP f (-p) = $-_ p_)
   ring_homo_poly_sub_chop_alt  |- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q /\ f (lead q) <> #0_ ==>
                                            (chop_ (MAP f (p - q)) = p_ -_ q_)
   ring_homo_sub_chop_chop      |- !r r_ f. (r ~r~ r_) f ==> !p q. poly p /\ poly q ==>
                                            (chop_ (MAP f (p - q)) = chop_ p_ -_ chop_ q_)
   ring_homo_ulead              |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==> ulead_ p_
   ring_homo_pmonic             |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. pmonic p ==> pmonic_ p_
   ring_homo_poly_ulead         |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. ulead p ==> ulead_ p_
   ring_homo_poly_pmonic        |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. pmonic p ==> pmonic_ p_
   ring_homo_poly_div_mod       |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                   !p q. poly p /\ ulead q ==>
                                         (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_)
   ring_homo_poly_div_mod_eqn   |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                   !p q. poly p /\ pmonic q ==>
                                         (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\
                                         deg_ (MAP f (p % q)) < deg_ q_
   ring_homo_poly_div      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                              !p q. poly p /\ ulead q ==> (MAP f (p / q) = p_ /_ q_)
   ring_homo_poly_mod      |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                              !p q. poly p /\ ulead q ==> (MAP f (p % q) = p_ %_ q_)

   Homomorphism between Polynomial Modulo Rings:
   ring_homo_poly_mod_ring_element    |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                         !p x. x IN (PolyModRing r p).carrier ==>
                                               MAP f x IN (PolyModRing r_ p_).carrier
   ring_homo_poly_mod_ring_sum_homo   |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
                                         GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum
   ring_homo_poly_mod_ring_prod_homo  |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
                                         MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod
   ring_homo_poly_mod_ring_homo       |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
                                         (PolyModRing r p ~r~ PolyModRing r_ p_) (MAP f)
   poly_divides_poly_mod_ring_homo    |- !r z p. Ring r /\ pmonic z /\ pmonic p /\ z pdivides p ==>
                                         RingHomo (\x. x % z) (PolyModRing r p) (PolyModRing r z)

   Ring Isomorphism:
   ring_iso_zero_poly      |- !r r_ f. (r =r= r_) f ==> !p. zerop p ==> zerop_ p_
   ring_iso_eq_zero_poly   |- !r r_ f. (r =r= r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_)
   ring_iso_weak           |- !r r_ f. RingIso f r r_ ==> !p. weak p ==> weak_ p_
   ring_iso_poly           |- !r r_ f. (r =r= r_) f ==> !p. poly p ==> poly_ p_
   ring_iso_eq_poly_zero   |- !r r_ f p. (p = |0|) <=> (p_ = |0|_)
   ring_iso_poly_zero      |- !r r_ f. MAP f |0| = |0|_
   ring_iso_poly_one       |- !r r_ f. (r =r= r_) f ==> (MAP f |1| = |1|_)
   ring_iso_poly_chop      |- !r r_ f. (r =r= r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)
   ring_iso_weak_add       |- !r r_ f. (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)
   ring_iso_poly_add       |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)
   ring_iso_weak_neg       |- !r r_ f. (r =r= r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)
   ring_iso_poly_neg       |- !r r_ f. (r =r= r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_)
   ring_iso_poly_sub       |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)
   ring_iso_poly_deg       |- !r r_ f p. deg_ p_ = deg p
   ring_iso_poly_lead      |- !r r_ f. (r =r= r_) f ==> !p. lead_ p_ = f (lead p)
   ring_iso_poly_coeff     |- !r r_ f. (r =r= r_) f ==> !p k. p_ '_ k = f (p ' k)
   ring_iso_weak_cmult     |- !r r_ f. (r =r= r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = f c o_ p_)
   ring_iso_poly_cmult     |- !r r_ f. (r =r= r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = f c *_ p_)
   ring_iso_poly_shift     |- !r r_ f. (r =r= r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n
   ring_iso_weak_mult      |- !r r_ f. (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)
   ring_iso_poly_mult      |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)

   Isomorphism between Polynomial Rings:
   ring_iso_poly_inj       |- !r r_ f. (r =r= r_) f ==> INJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier
   ring_iso_poly_surj      |- !r r_ f. (r =r= r_) f ==> SURJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier
   ring_iso_poly_bij       |- !r r_ f. (r =r= r_) f ==> BIJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier
   ring_iso_poly_ring_iso  |- !r r_ f. (r =r= r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_)

   More Ring Isomorphism Theorems:
   ring_iso_poly_exp       |- !r r_ f. (r =r= r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n
   ring_iso_poly_eval      |- !r r_ f. (r =r= r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))
   ring_iso_poly_root      |- !r r_ f. (r =r= r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x):
   ring_iso_poly_divides   |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_
   ring_iso_poly_sum_num   |- !r r_ f. (r =r= r_) f ==> !c. MAP f |c| = |c|_
   ring_iso_pmonic         |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==> poly_ p_ /\ 0 < deg_ p_ /\ unit_ (lead_ p_)
   ring_iso_inverse_weak_poly
                           |- !r r_ f. (r =r= r_) f ==> !q. weak_ q ==> weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)
   ring_iso_inverse_weak   |- !r r_ f. (r =r= r_) f ==> !q. weak_ q ==> ?p. weak p /\ (q = p_)
   ring_iso_inverse_polynomial
                           |- !r r_ f. (r =r= r_) f ==> !q. poly_ q ==> poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)
   ring_iso_inverse_poly   |- !r r_ f. (r =r= r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q)
   ring_iso_poly_unique    |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q))
   ring_iso_poly_div_mod   |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
                                       (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_)
   ring_iso_poly_div_mod_eqn
                           |- !r r_ f. (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
                                       (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\
                                       deg_ (MAP f (p % q)) < deg_ q_
   ring_iso_poly_div       |- !r r_ f. (r =r= r_) f ==>
                              !p q. poly p /\ pmonic q ==> (MAP f (p / q) = p_ /_ q_)
   ring_iso_poly_mod       |- !r r_ f. (r =r= r_) f ==>
                              !p q. poly p /\ pmonic q ==> (MAP f (p % q) = p_ %_ q_)

   Isomorphism between Polynomial Modulo Rings:
   ring_iso_poly_mod_ring_element    |- !r r_ f. (r =r= r_) f ==> !p x. x IN (PolyModRing r p).carrier ==>
                                                 MAP f x IN (PolyModRing r_ p_).carrier
   ring_iso_poly_mod_ring_sum_homo   |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                                 GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum
   ring_iso_poly_mod_ring_prod_homo  |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                                 MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod
   ring_iso_poly_mod_ring_homo  |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                            (PolyModRing r p ~r~ PolyModRing r_ p_) (MAP f)
   ring_iso_poly_mod_ring_inj   |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                            INJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
   ring_iso_poly_mod_ring_surj  |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                            SURJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
   ring_iso_poly_mod_ring_bij   |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                            BIJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
   ring_iso_poly_mod_ring_iso   |- !r r_ f. (r =r= r_) f ==> !p. pmonic p ==>
                                            (PolyModRing r p =r= PolyModRing r_ p_) (MAP f)

   Field Homomorphism and Isomorphism:
   field_homo_poly_ring_homo    |- !r r_ f. (r ~~~ r_) f ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_)
   field_iso_poly_ring_iso      |- !r r_ f. (r === r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_)
   field_iso_poly_mod_ring_iso  |- !r r_ f. (r === r_) f ==>
                                   !p. ipoly p ==> RingIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_)

   Polynomial Correspondence
   field_iso_zero_poly     |- !r r_ f. (r === r_) f ==> !p. zerop p ==> zerop_ p_
   field_iso_eq_zero_poly  |- !r r_ f. (r === r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_)
   field_iso_weak          |- !r r_ f. (r === r_) f ==> !p. weak p ==> weak_ p_
   field_iso_poly          |- !r r_ f. (r === r_) f ==> !p. poly p ==> poly_ p_
   field_iso_eq_poly_zero  |- !r r_ f p. (p = |0|) <=> (p_ = |0|_)
   field_iso_poly_zero     |- !r r_ f. MAP f |0| = |0|_
   field_iso_poly_one      |- !r r_ f. (r === r_) f ==> (MAP f |1| = |1|_)
   field_iso_poly_sum_num  |- !r r_ f. (r === r_) f ==> !c. MAP f |c| = |c|_
   field_iso_poly_chop     |- !r r_ f. (r === r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)
   field_iso_weak_add      |- !r r_ f. (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)
   field_iso_poly_add      |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)
   field_iso_weak_neg      |- !r r_ f. (r === r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)
   field_iso_poly_neg      |- !r r_ f. (r === r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_)
   field_iso_poly_sub      |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)
   field_iso_weak_cmult    |- !r r_ f. (r === r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = f c o_ p_)
   field_iso_poly_cmult    |- !r r_ f. (r === r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = f c *_ p_)
   field_iso_poly_shift    |- !r r_ f. (r === r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n
   field_iso_weak_mult     |- !r r_ f. (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)
   field_iso_poly_mult     |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)
   field_iso_poly_exp      |- !r r_ f. (r === r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n
   field_iso_poly_deg      |- !r r_ f p. deg_ p_ = deg p
   field_iso_poly_lead     |- !r r_ f. (r === r_) f ==> !p. lead_ p_ = f (lead p)
   field_iso_poly_coeff    |- !r r_ f. (r === r_) f ==> !p k. p_ '_ k = f (p ' k)
   field_iso_inverse_weak_poly   |- !r r_ f. (r === r_) f ==>
                                    !q. weak_ q ==> weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)
   field_iso_inverse_weak        |- !r r_ f. (r === r_) f ==> !q. weak_ q ==> ?p. weak p /\ (q = p_)
   field_iso_inverse_polynomial  |- !r r_ f. (r === r_) f ==>
                                    !q. poly_ q ==> poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)
   field_iso_inverse_poly        |- !r r_ f. (r === r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q)
   field_iso_poly_unique   |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q))
   field_iso_poly_X        |- !r r_ f. (r === r_) f ==> (MAP f X = X_)
   field_iso_poly_unity    |- !r r_ f. (r === r_) f ==> !n. MAP f (unity n) = unity_ n
   field_iso_poly_master   |- !r r_ f. (r === r_) f ==> !n. MAP f (master n) = master_ n
   field_iso_poly_prod_set |- !r r_ f. (r === r_) f ==> !s. FINITE s /\ pset s ==>
                                                            (MAP f (PPROD s) = poly_prod_image r_ (MAP f) s)
   field_iso_poly_divides     |- !r r_ f. (r === r_) f ==>
                                 !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_
   field_iso_poly_divides_iff |- !r r_ f. (r === r_) f ==>
                                 !p q. poly p /\ poly q ==> (p pdivides q <=> p_ pdivides_ q_)
   field_iso_weak_inv         |- !r r_ f. (r === r_) f ==> !p. weak p ==> (p = MAP (LINV f R) p_)
   field_iso_poly_inv         |- !r r_ f. (r === r_) f ==> !p. poly p ==> (p = MAP (LINV f R) p_)
   field_iso_poly_monic       |- !r r_ f. (r === r_) f ==> !p. monic p ==> monic_ p_
   field_iso_poly_monic_iff   |- !r r_ f. (r === r_) f ==> !p. poly p ==> (monic p <=> monic_ p_)
   field_iso_poly_ulead       |- !r r_ f. (r === r_) f ==> !p. ulead p ==> ulead_ p_
   field_iso_poly_pmonic      |- !r r_ f. (r === r_) f ==> !p. pmonic p ==> pmonic_ p_
   field_iso_poly_unit        |- !r r_ f. (r === r_) f ==> !p. upoly p ==> upoly_ p_
   field_iso_poly_unit_iff    |- !r r_ f. (r === r_) f ==> !p. poly p ==> (upoly p <=> upoly_ p_)
   field_iso_poly_irreducible |- !r r_ f. (r === r_) f ==> !p. ipoly p ==> ipoly_ p_
   field_iso_poly_eval        |- !r r_ f. (r === r_) f ==>
                                 !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))
   field_iso_poly_root        |- !r r_ f. (r === r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)
   field_iso_poly_root_iff    |- !r r_ f. (r === r_) f ==> !p x. poly p /\ x IN R ==> (root p x <=> root_ p_ (f x))
   field_iso_poly_roots       |- !r r_ f. (r === r_) f ==>
                                 !p s. poly p /\ s SUBSET R ==> (roots p SUBSET s <=> roots_ p_ SUBSET IMAGE f s)
   field_iso_poly_roots_iff   |- !r r_ f. (r === r_) f ==> !p. poly p ==> (roots_ p_ = IMAGE f (roots p))
   field_iso_poly_X_iff       |- !r r_ f. (r === r_) f ==> !p. poly p ==> ((p_ = X_) <=> (p = X))
   field_iso_I_poly_iff       |- !r s. (r === s) I ==> !p. poly p <=> Poly s p
   field_iso_poly_X_add_c     |- !r r_ f. (r === r_) f ==> !c. MAP f (X + |c|) = X_ +_ |c|_
   field_iso_poly_X_sub_c     |- !r r_ f. (r === r_) f ==> !c. MAP f (X - |c|) = X_ -_ |c|_
   field_iso_poly_factor      |- !r r_ f. (r === r_) f ==> !c. c IN R ==> (MAP f (factor c) = factor_ (f c))
   field_iso_poly_root_multiplicity
                              |- !r r_ f. (r === r_) f ==> !p x. x IN R /\ poly p ==>
                                          (poly_root_multiplicity r_ p_ (f x) = multiplicity p x)
   field_iso_poly_separable   |- !r r_ f. (r === r_) f ==>
                                 !p. poly p /\ separable p ==> poly_separable r_ p_
   field_iso_poly_mod_field_iso
                              |- !r r_ f. (r === r_) f ==>
                                 !p. ipoly p ==> (PolyModRing r p === PolyModRing r_ p_) (MAP f)
   field_iso_poly_mod_field_isomorphism
                              |- !r r_. r =f= r_ ==>
                                 !p. ipoly p ==> ?f. PolyModRing r p =f= PolyModRing r_ (f p)

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring Homomorphism and Isomorphism                              *)
(* ------------------------------------------------------------------------- *)

(* Overloads for Homomorphism and Isomorphisms without map *)
val _ = overload_on("~~r", ``\(r:'a ring) (r_:'b ring). Ring r /\ Ring r_ /\ ?f. RingHomo f r r_``);
val _ = overload_on("==r", ``\(r:'a ring) (r_:'b ring). Ring r /\ Ring r_ /\ ?f. RingIso f r r_``);
val _ = overload_on("~f~", ``\(r:'a field) (r_:'b field). Field r /\ Field r_ /\ ?f. FieldHomo f r r_``);
val _ = overload_on("=f=", ``\(r:'a field) (r_:'b field). Field r /\ Field r_ /\ ?f. FieldIso f r r_``);
val _ = overload_on("~ff~", ``\(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ ?f. FieldHomo f r r_``);
val _ = overload_on("=ff=", ``\(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ ?f. FieldIso f r r_``);

(* make infix operators *)
val _ = set_fixity "~~r" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "==r" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "~f~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "=f=" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "~ff~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "=ff=" (Infix(NONASSOC, 450)); (* same as relation *)

(* Overloads for FiniteField of type 'b *)
val _ = overload_on("S_", ``(s_:'b ring).carrier``);
val _ = overload_on("S+_", ``ring_nonzero (s_:'b ring)``);

(* Overloads for polynomials of type 'b *)
val _ = overload_on("zerop_", ``zero_poly (r_:'b ring)``);
val _ = overload_on("weak_", ``Weak (r_:'b ring)``);
val _ = overload_on("poly_", ``Poly (r_:'b ring)``);
val _ = overload_on("chop_", ``poly_chop (r_:'b ring)``);
val _ = overload_on("neg_", ``weak_neg (r_:'b ring)``);
val _ = overload_on("-_", ``poly_neg (r_:'b ring)``);
val _ = overload_on("||_", ``weak_add (r_:'b ring)``);
val _ = overload_on("+_", ``poly_add (r_:'b ring)``);
val _ = overload_on("-_", ``poly_sub (r_:'b ring)``);
val _ = overload_on("o_", ``weak_cmult (r_:'b ring)``);
val _ = overload_on("*_", ``poly_cmult (r_:'b ring)``);
val _ = overload_on("o_", ``weak_mult (r_:'b ring)``);
val _ = overload_on("*_", ``poly_mult (r_:'b ring)``);
val _ = overload_on(">>_", ``poly_shift (r_:'b ring)``);
val _ = overload_on("**_", ``poly_exp (r_:'b ring)``);
val _ = overload_on("deg_", ``poly_deg (r_:'b ring)``);
val _ = overload_on("lead_", ``poly_lead (r_:'b ring)``);
val _ = overload_on("'_", ``poly_coeff (r_:'b ring)``);
val _ = overload_on("/_", ``poly_div (r_:'b ring)``);
val _ = overload_on("%_", ``poly_mod (r_:'b ring)``);
val _ = overload_on("p_", ``MAP (f:'a -> 'b) (p:'a poly)``);
val _ = overload_on("q_", ``MAP (f:'a -> 'b) (q:'a poly)``);
val _ = overload_on("|0|_", ``poly_zero (r_:'b ring)``);
val _ = overload_on("|1|_", ``poly_one (r_:'b ring)``);
val _ = overload_on("|c|_", ``poly_num (r_:'b ring) (c:num)``);
val _ = overload_on("X_", ``>>_ |1|_ 1``); (* before infix, will be |1|_ >>_ 1 after infix *)
val _ = overload_on("eval_", ``poly_eval (r_:'b ring)``);
val _ = overload_on("peval_", ``poly_peval (r_:'b ring)``);
val _ = overload_on("factor_", ``poly_factor (r_:'b field)``);
val _ = overload_on("root_", ``poly_root (r_:'b ring)``);
val _ = overload_on("roots_", ``poly_roots (r_:'b ring)``);
val _ = overload_on("pdivides_", ``poly_divides (r_:'b field)``);
val _ = overload_on("unity_", ``Unity (r_:'b ring)``);
val _ = overload_on("master_", ``Master (r_:'b ring)``);
val _ = overload_on("monic_", ``Monic (r_:'b ring)``);
val _ = overload_on("ulead_", ``Ulead (r_:'b ring)``);
val _ = overload_on("pmonic_", ``Pmonic (r_:'b ring)``);
val _ = overload_on("upoly_", ``\p. p IN (Invertibles (PolyRing (r_:'b ring)).prod).carrier``);
val _ = overload_on("ipoly_", ``IPoly (r_:'b ring)``);

(* make infix operators *)
val _ = set_fixity "||_" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity "o_" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity ">>_" (Infixr 700); (* same as EXP in arithmeticScript.sml, infix right *)
val _ = set_fixity "'_" (Infixl 2000); (* same as ' for function application *)
val _ = set_fixity "/_" (Infixl 600); (* same as DIV in arithmeticScript.sml *)
val _ = set_fixity "%_" (Infixl 650); (* same as MOD in arithmeticScript.sml *)
val _ = set_fixity "pdivides_" (Infix(NONASSOC, 450)); (* same as relation *)

(* ------------------------------------------------------------------------- *)
(* Special Maps                                                              *)
(* ------------------------------------------------------------------------- *)

(* Note: These maps are specialized: only for f:'a -> 'a *)
(* Note: These are good exercises, not useful for homomorphism maps *)

(* Theorem: (f #0 = #0) /\ zerop p ==> zerop (MAP f p) *)
(* Proof:
   By induction on p.
   Base case: zerop [] ==> zerop (MAP f [])
     True by MAP f [] = []                  by MAP
   Step case: zerop p ==> zerop (MAP f p) ==> !h. zerop (h::p) ==> zerop (MAP f (h::p))
     Since zerop (h::p)
           ==> h = #0 /\ zerop p            by zero_poly_cons
           ==> h = #0 /\ zerop (MAP f p)    by induction hypothesis
       and zerop (MAP f (h::p))
         = zerop (f h :: MAP f p)           by MAP
       and f h = f #0 = #0                  by given
     Hence zerop (MAP f (h::p))             by zero_poly_cons
*)
val zero_poly_map = store_thm(
  "zero_poly_map",
  ``!r:'a ring. !f p. (f #0 = #0) /\ zerop p ==> zerop (MAP f p)``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[]);
(* good exercise *)

(* Theorem: (f #0 = #0) ==> (chop (MAP f (chop p)) = chop (MAP f p)) *)
(* Proof:
   By induction on p.
   Base case: chop (MAP f (chop [])) = chop (MAP f [])
     True since chop [] = []        by poly_chop_of_zero
   Step case: chop (MAP f (chop p)) = chop (MAP f p) ==>
              !h. chop (MAP f (chop (h::p))) = chop (MAP f (h::p))
     If zerop (h::p),
        chop (h::p) = []            by poly_chop_cons
        zerop (MAP f (h::p))        by zero_poly_map
        LHS = chop (MAP f [])       by above
            = chop []               by MAP
            = []                    by poly_chop_of_zero
        RHS = [] = LHS              by zero_poly_chop
     If ~zerop (h::p),
        chop (h::p) = h:: chop p           by poly_chop_cons
        LHS = chop (MAP f (chop (h::p)))
            = chop (MAP f (h:: chop p))    by above
            = chop (f h:: MAP f (chop p))  by MAP
        RHS = chop (MAP f (h::p))
            = chop (f h:: MAP f p)         by MAP
        If zerop (f h:: MAP f p),
        That is  f h = #0 /\ zerop (MAP f p)               by zero_poly_cons
             or  f h = #0 /\ zerop (chop (MAP f p))        by zero_poly_eq_zero_poly_chop
             or  f h = #0 /\ zerop (chop (MAP f (chop p))) by induction hypothesis
             or  f h = #0 /\ zerop (MAP f (chop p))        by zero_poly_eq_zero_poly_chop
             or  zerop (f h:: MAP f (chop p))              by zero_poly_cons
          giving RHS = [] = LHS                            by zero_poly_chop
        If ~zerop (f h:: MAP f p),
          RHS = chop (f h:: MAP f p)                       by above
              = f h:: chop (MAP f p)                       by poly_chop_cons
              = f h:: chop (MAP f (chop p)) = LHS          by induction hypothesis
*)
val poly_chop_map = store_thm(
  "poly_chop_map",
  ``!r:'a ring. !f p. (f #0 = #0) ==> (chop (MAP f (chop p)) = chop (MAP f p))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >-
  metis_tac[zero_poly_map] >-
  metis_tac[zero_poly_eq_zero_poly_chop] >>
  metis_tac[zero_poly_eq_zero_poly_chop]);
(* good exercise *)

(* Theorem: !p q. (p = q) ==> (MAP f p = MAP f q) *)
(* Proof: by equality of map. *)
val poly_eq_map = store_thm(
  "poly_eq_map",
  ``!(r:'a ring) (s:'b ring) f. !p q:'a poly. (p = q) ==> (MAP f p = MAP f q)``,
  rw[]);

(* Theorem: !p. poly_deg s (MAP f p) = deg p *)
(* Proof:
   If p = [],
        poly_deg s (MAP f [])
      = poly_deg s []             by MAP
      = 0                         by poly_deg_of_zero
      = deg []                    by poly_deg_of_zero
   If p <> [],
      MAP f p <> []               by MAP_EQ_NIL
        poly_deg s (MAP f p)
      = PRE (LENGTH (MAP f p))    by poly_deg_def, MAP f p <> []
      = PRE (LENGTH p)            by LENGTH_MAP
      = deg p                     by poly_deg_def, p <> |0|
*)
val poly_deg_map = store_thm(
  "poly_deg_map",
  ``!(r:'a ring) (s:'b ring) f. !p. poly_deg s (MAP f p) = deg p``,
  rpt strip_tac >>
  Cases_on `p` >-
  rw[] >>
  rw[poly_deg_def, MAP_EQ_NIL]);

(* ------------------------------------------------------------------------- *)
(* Ring Homomorphism                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f ==> !p. zerop p ==> zerop_ p_ *)
(* Proof:
   By induction on p.
   Base: zerop [] ==> zerop_ (MAP f [])
        zerop_ (MAP f [])
      = zerop_ []                  by MAP
      = true                       by zero_poly_of_zero
   Step: zerop p ==> zerop_ p_ ==>
         !h. zerop (h::p) ==> zerop_ (MAP f (h::p))
      Note zerop (h::p)
       ==> h = #0 /\ zerop p       by zero_poly_cons
       ==> f h = #0_ /\            by ring_homo_zero
           zerop_ p_               by induction hypothesis
        zerop_ (MAP f (h::p))
      = zerop_ (f h :: p_)         by MAP
      = true                       by above, zero_poly_cons
*)
val ring_homo_zero_poly = store_thm(
  "ring_homo_zero_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p. zerop p ==> zerop_ p_``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (zerop p <=> zerop_ p_) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (zerop [] <=> zerop_ (MAP f []))
      Note zerop [] = T            by zero_poly_of_zero
        zerop_ (MAP f [])
      = zerop_ []                  by MAP
      = T                          by zero_poly_of_zero
   Step: weak p ==> (zerop p <=> zerop_ p_) ==>
         !h. weak (h::p) ==> (zerop (h::p) <=> zerop_ (MAP f (h::p)))
      Note weak (h::p)
       ==> h IN R /\ weak p        by weak_cons
           zerop (h::p)
       <=> h = #0 /\ zerop p       by zero_poly_cons
       <=> f h = #0_ /\            by ring_homo_eq_zero
           zerop_ p_               by induction hypothesis
       <=> zerop_ (MAP f (h::p))   by zero_poly_cons
*)
val ring_homo_eq_zero_poly = store_thm(
  "ring_homo_eq_zero_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (zerop p <=> zerop_ p_)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  metis_tac[ring_homo_eq_zero]);

(* Theorem: RingHomo f r r_ ==> !p. weak p ==> weak_ p_ *)
(* Proof:
   By induction on p.
   Base: weak [] ==> weak_ (MAP f [])
     weak_ (MAP f [])
   = weak_ []                   by MAP
   = T                          by Weak_def
   Step: weak p ==> weak_ p_ ==> !h. weak (h::p) ==> weak_ (MAP f (h::p))
       weak (h::p)
   ==> h IN R /\ weak p         by weak_cons
   ==> f h IN B /\ weak p       by ring_homo_element
   ==> f h IN B /\ weak_ p_     by induction hypothesis
   ==> weak_ (f h :: p_)        by weak_cons
     = weak_ (MAP f (h::p))     by MAP
*)
val ring_homo_weak = store_thm(
  "ring_homo_weak",
  ``!(r:'a ring) (r_:'b ring) f. RingHomo f r r_ ==> !p. weak p ==> weak_ p_``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons, MAP] >>
  metis_tac[ring_homo_element]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> poly_ p_ *)
(* Proof:
   If p = |0|,
      Then p_ = |0|_     by MAP, poly_zero
       and poly_ |0|_    by poly_zero_poly
   If p <> |0|,
      Then poly p
       ==> weak p /\ LAST p <> #0     by poly_def_alt, p <> |0|
      Note weak p ==> weak_ p_        by ring_homo_weak
       and LAST p_ = f (LAST p)       by LAST_MAP, poly_zero
       Now f #0 = #0_                 by ring_homo_zero
      Thus LAST q <> #0_              by INJ_DEF, weak_last_element, ring_zero_element
        so p_ <> |0|_                 by MAP_EQ_NIL, poly_zero
     Hence poly_ p_                   by poly_def_alt
*)
val ring_homo_poly = store_thm(
  "ring_homo_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> poly_ p_``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `weak p /\ LAST p <> #0` by metis_tac[poly_def_alt] >>
  `weak_ p_` by metis_tac[ring_homo_weak] >>
  `LAST p_ = f (LAST p)` by metis_tac[LAST_MAP, poly_zero] >>
  `f #0 = #0_` by rw[ring_homo_zero] >>
  `LAST p_ <> #0_` by prove_tac[INJ_DEF, weak_last_element, ring_zero_element] >>
  `p_ <> |0|_` by metis_tac[MAP_EQ_NIL, poly_zero] >>
  rw[poly_def_alt]);

(* Theorem: RingHomo f r r_ ==> !p. poly p ==> poly_ (chop_ p_) *)
(* Proof:
   Since poly p ==> weak p         by poly_is_weak
     and weak p ==> weak_ p_       by ring_homo_weak
    Thus poly_ (chop_ p_)          by poly_chop_weak_poly
*)
val ring_homo_poly_of_chop = store_thm(
  "ring_homo_poly_of_chop",
  ``!(r:'a ring) (r_:'b ring) f. RingHomo f r r_ ==> !p. poly p ==> poly_ (chop_ p_)``,
  metis_tac[poly_is_weak, ring_homo_weak, poly_chop_weak_poly]);

(* Theorem: (p = |0|) <=> (p_ = |0|_) *)
(* Proof:
       p = |0|
   <=> p = []        by poly_zero
   <=> p_ = []       by MAP_EQ_NIL
   <=> p_ = |0|_     by poly_zero
*)
val ring_homo_eq_poly_zero = store_thm(
  "ring_homo_eq_poly_zero",
  ``!(r:'a ring) (r_:'b ring) (f:'a -> 'b). !p. (p = |0|) <=> (p_ = |0|_)``,
  rw[MAP_EQ_NIL]);

(* Theorem: MAP f |0| = |0|_ *)
(* Proof:
       MAP f |0|
     = MAP f []        by poly_zero
     = []              by MAP
     = |0|_            by poly_zero
*)
val ring_homo_poly_zero = store_thm(
  "ring_homo_poly_zero",
  ``!(r:'a ring) (r_:'b ring) f. MAP f |0| = |0|_``,
  rw[]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> (MAP f |1| = |1|_) *)
(* Proof:
   Note f #0 = #0_     by ring_homo_zero
    and f #1 = #1_     by ring_homo_one
   If #1 = #0,
      #0_ = #1_        by above
       MAP f |1|
     = MAP f []        by poly_one
     = []              by MAP
     = |1|_            by poly_one, #0_ = #1_
   If #1 <> #0,
      Note #0 IN R     by ring_zero_element
       and #1 IN R     by ring_one_element
      thus #0_ <> #1_  by INJ_DEF
       MAP f |1|
     = MAP f [#1]      by poly_one
     = [f #1]          by MAP
     = [#1_]           by ring_homo_one, above
     = |1|_            by poly_one, #0_ <> #1_
*)
val ring_homo_poly_one = store_thm(
  "ring_homo_poly_one",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> (MAP f |1| = |1|_)``,
  rpt strip_tac >>
  `f #0 = #0_` by rw[ring_homo_zero] >>
  `f #1 = #1_` by rw[ring_homo_one] >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_one, MAP] >>
  `#0_ <> #1_` by metis_tac[INJ_DEF, ring_zero_element, ring_one_element] >>
  rw[poly_one]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f |1| = |1|_) *)
(* Proof:
   Note #1_ <> #0_
    ==> #1 <> #0      by ring_homo_one, ring_homo_zero
     MAP f |1|
   = MAP f [#1]       by poly_one, #1 <> #0
   = [f #1]           by MAP
   = [#1_]            by ring_homo_one
   = |1|_             by poly_one
*)
val ring_homo_poly_one_alt = store_thm(
  "ring_homo_poly_one_alt",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f |1| = |1|_)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[ring_homo_one, ring_homo_zero] >>
  rw[poly_one]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (MAP f (chop p) = chop_ p_) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (MAP f (chop []) = chop_ (MAP f []))
        MAP f (chop [])
      = MAP f []                 by poly_chop_of_zero
      = []                       by MAP
      = chop_ []                 by poly_chop_of_zero
      = chop_ (MAP f [])         by MAP
   Step: weak p ==> (MAP f (chop p) = chop_ p_) ==>
         !h. weak (h::p) ==> (MAP f (chop (h::p)) = chop_ (MAP f (h::p)))
        Note weak (h::p) ==> h IN R /\ weak p     by weak_cons
      If zerop (h::p),
        Then zerop_ (MAP f (h::p))         by ring_homo_zero_poly
        MAP f (chop (h::p))
      = MAP f []                           by poly_chop_cons
      = []                                 by MAP
      = chop_ (MAP f (h::p))               by poly_chop_zero_poly
      If ~(zerop (h::p)),
        Then ~(zerop_ (MAP f (h::p)))      by ring_homo_eq_zero_poly
        MAP f (chop (h::p))
      = MAP f (h::chop p)                  by poly_chop_cons
      = f h:: MAP f (chop p)               by MAP
      = f h:: chop_ p_                     by induction hypothesis
      = chop_ (f h:: p_)                   by poly_chop_cons
      = chop_ (MAP f (h::p))               by MAP
*)
val ring_homo_poly_chop = store_thm(
  "ring_homo_poly_chop",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `zerop (h::p)` >| [
    `zerop_ (MAP f (h::p))` by metis_tac[ring_homo_zero_poly] >>
    rw[poly_chop_zero_poly],
    `~(zerop_ (MAP f (h::p)))` by metis_tac[ring_homo_eq_zero_poly, weak_cons] >>
    `~(zerop_ (f h:: MAP f p))` by metis_tac[MAP] >>
    `MAP f (chop (h::p)) = MAP f (h::chop p)` by rw[] >>
    `_ = f h:: MAP f (chop p)` by rw[] >>
    `_ = f h:: chop_ p_` by rw[] >>
    `_ = chop_ (f h:: p_)` by rw[] >>
    `_ = chop_(MAP f (h::p))` by rw[] >>
    rw_tac std_ss[]
  ]);

(* Theorem: (r ~r~ r_) f ==> !p. chop_ (MAP f (chop p)) = chop_ p_ *)
(* Proof:
   By induction on p:
   Base: chop_ (MAP f (chop [])) = chop_ (MAP f [])
       True since chop [] = []                  by poly_chop_of_zero
   Step: chop_ (MAP f (chop p)) = chop_ p_ ==>
         !h. chop_ (MAP f (chop (h::p))) = chop_ (MAP f (h::p))
     First, f #0 = #0_                          by ring_homo_zero
     If zerop (h::p),
     then zerop_ (MAP f (h::p))                 by ring_homo_zero_poly
        LHS = chop_ (MAP f (chop (h::p)))
            = chop_ (MAP f ([])                 by poly_chop_cons, zerop (h::p)
            = chop_ []                          by MAP
            = []                                by poly_chop_of_zero
        RHS = chop_ (MAP f (h::p))) = []        by zero_poly_chop
     If ~zerop (h::p),
        LHS = chop_ (MAP f (chop (h::p)))
            = chop_ (MAP f (h :: chop p))       by poly_chop_cons, ~zerop (h::p)
            = chop_ (f h:: MAP (f (chop p)))    by MAP
        RHS = chop_ (MAP f (h::p))
            = chop_ (f h:: p_)                  by MAP
        If zerop (f h:: MAP f (chop p)),
           f h = #0 /\ zerop (MAP f (chop p))         by zero_poly_cons
        or f h = #0 /\ zerop (chop_ (MAP f (chop p))) by zero_poly_eq_zero_poly_chop
        or f h = #0 /\ zerop (chop_ p_)               by induction hypothesis
        or zerop (f h:: (chop_ p_))                   by zero_poly_cons
        so LHS = [] = RHS                             by zero_poly_chop
        If ~zerop (f h:: MAP f (chop p)),
        RHS = chop_ (f h:: p_)                  by above
            = f h :: chop_ p_                   by poly_chop_cons, ~zerop (f h:: MAP f (chop p))
            = f h :: chop_ (MAP f (chop p))     by induction hypothesis
            = LHS
*)
val ring_homo_poly_chop_of_chop = store_thm(
  "ring_homo_poly_chop_of_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p. chop_ (MAP f (chop p)) = chop_ p_``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  `f #0 = #0_` by rw[ring_homo_zero] >>
  rw[] >-
  metis_tac[ring_homo_zero_poly] >>
  metis_tac[zero_poly_eq_zero_poly_chop]);

(* Theorem: (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_) *)
(* Proof:
   By induction on p.
   Base: !q. weak [] /\ weak q ==> (MAP f ([] || q) = MAP f [] ||_ q_)
     LHS = MAP f ([] || q)
         = MAP f q                      by weak_add_of_lzero
     RHS = ||_ (MAP f []) q_
         = ||_ [] q_)            by MAP
         = MAP f q                      by weak_add_of_lzero
   Step: !q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_) ==>
         !h q. weak (h::p) /\ weak q ==> (MAP f ((h::p) || q) = MAP f (h::p) ||_ q_)
     By induction on q.
     Base: !h. weak (h::p) /\ weak [] ==> (MAP f ((h::p) || []) = MAP f (h::p) ||_ MAP f [])
        LHS = MAP f ((h::p) || [])
            = MAP f (h::p)                     by weak_add_of_rzero
        RHS = ||_ (MAP f (h::p)) (MAP f [])
            = ||_ (MAP f (h::p)) []            by MAP
            = MAP f (h::p)                     by weak_add_of_rzero
     Step: !q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_) ==>
           !h h'. weak (h'::p) /\ weak (h::q) ==> (MAP f ((h'::p) || (h::q)) = MAP f (h'::p) ||_ MAP f (h::q))
        Note weak (h'::p) ==> h' IN R /\ weak p          by weak_cons
             weak (h::q) ==> h IN R /\ weak q            by weak_cons
        LHS = MAP f ((h'::p) || (h::q))
            = MAP f ((h' + h:: p || q))                  by weak_add_cons
            = f (h' + h):: MAP f (p || q)                by MAP
            = (f h') +_ (f h)::MAP f (p || q)            by ring_homo_property
            = (f h') +_ (f h):: p_ ||_ q_                by induction hypothesis
        RHS = ||_ (MAP f (h'::p)) (MAP f (h::q)))
            = ||_ (f h':: p_) (f h:: q_)                 by MAP
            = (f h') +_ (f h):: p_ ||_ q_                by weak_add_cons
*)
val ring_homo_weak_add = store_thm(
  "ring_homo_weak_add",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)``,
  ntac 4 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  Induct_on `q` >-
  rw[] >>
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_) *)
(* Proof:
   Note weak p, weak q        by poly_is_weak
    and weak (p || q)         by weak_add_weak
     MAP f (p + q)
   = MAP f (chop (p || q))    by poly_add_def
   = chop_ (MAP f (p ||q))    by ring_homo_poly_chop, weak (p || q)
   = chop_ (p_ ||_ q_)        by ring_homo_weak_add, weak p, weak q
   = p_ +_ q_                 by poly_add_def
*)
val ring_homo_poly_add = store_thm(
  "ring_homo_poly_add",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak (p || q)` by rw[] >>
  `MAP f (p + q) = MAP f (chop (p || q))` by rw_tac std_ss[poly_add_def] >>
  `_ = chop_ (MAP f (p ||q))` by rw[ring_homo_poly_chop] >>
  `_ = chop_ (p_ ||_ q_)` by metis_tac[ring_homo_weak_add] >>
  `_ = p_ +_ q_` by rw_tac std_ss[poly_add_def] >>
  rw_tac std_ss[]);

(* Theorem: (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p + q)) = p_ +_ q_) *)
(* Proof:
     chop_ (MAP f (p + q))
   = chop_ (MAP f (chop (p || q)))      by poly_add_def
   = chop_ (MAP f (p || q))             by ring_homo_poly_chop_of_chop
   = chop_ (p_ ||_ q_)                  by ring_homo_weak_add
   = p_ +_ q_                           by poly_add_def
*)
val ring_homo_poly_add_chop = store_thm(
  "ring_homo_poly_add_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q ==> (chop_ (MAP f (p + q)) = p_ +_ q_)``,
  rw_tac std_ss[poly_add_def] >>
  metis_tac[ring_homo_poly_chop_of_chop, ring_homo_weak_add, poly_is_weak]);

(* Theorem: (r ~r~ r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (MAP f (neg []) = neg_ (MAP f []))
      LHS = MAP f (neg [])
          = MAP f []            by weak_neg_def
          = []                  by MAP
      RHS = neg_ (MAP f [])
          = neg_ []             by MAP
          = []                  by weak_neg_def
   Step:  weak p ==> (MAP f (neg p) = neg_ p_) ==>
        !h. weak (h::p) ==> (MAP f (neg (h::p)) = neg_ (MAP f (h::p)))
      Note weak (h::p) ==> h IN R /\ weak p     by weak_cons
        MAP f (neg (h::p))
      = MAP f (-h :: neg p)     by weak_neg_def
      = f (-h) :: MAP f (neg p) by MAP
      = f (-h) :: neg_ p_       by induction hypothesis
      = $-_ (f h) :: neg_ p_    by ring_homo_neg
      = neg_ (f h:: p_)         by weak_neg_def
      = neg_ (MAP f (h::p))     by MAP
*)
val ring_homo_weak_neg = store_thm(
  "ring_homo_weak_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[ring_homo_neg]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> (MAP f (- p) = $-_ p_) *)
(* Proof:
   Note poly p ==> poly_ p_    by ring_homo_poly
     MAP f (- p)
   = MAP f (neg p)             by poly_neg_def
   = neg_ p_                   by ring_homo_weak_neg
   = $-_ p_                    by poly_neg_def, poly_ p_
*)
val ring_homo_poly_neg = store_thm(
  "ring_homo_poly_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> (MAP f (- p) = $-_ p_)``,
  metis_tac[poly_neg_def, ring_homo_weak_neg, ring_homo_poly, poly_is_weak]);

(* Theorem: (r ~r~ r_) f ==> !p. poly p ==> (chop_ (MAP f (-p)) = ($-_ (chop_ p_))) *)
(* Proof:
   Note poly p ==> poly_ (chop_ p_)    by ring_homo_poly_of_chop
    and weak_ p_                       by ring_homo_weak
     chop_ (MAP f (-p))
   = chop_ (MAP f (neg p))             by poly_neg_def
   = chop_ (neg_ p_)                   by ring_homo_weak_neg
   = neg_ (chop_ p_)                   by poly_chop_neg, weak_ p_
   = $-_ (chop_ p_)                    by poly_neg_def
*)
val ring_homo_poly_neg_chop = store_thm(
  "ring_homo_poly_neg_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p. poly p ==> (chop_ (MAP f (-p)) = ($-_ (chop_ p_)))``,
  rpt strip_tac >>
  `poly_ (chop_ p_)` by metis_tac[ring_homo_poly_of_chop] >>
  `weak_ p_` by metis_tac[ring_homo_weak, poly_is_weak] >>
  `chop_ (MAP f (-p)) = chop_ (MAP f (neg p))` by rw[poly_neg_def] >>
  `_ = chop_ (neg_ p_)` by metis_tac[ring_homo_weak_neg, poly_is_weak] >>
  rw[poly_chop_neg, poly_neg_def]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_) *)
(* Proof:
   Note poly (-q)          by poly_neg_poly
     MAP f (p - q)
   = MAP f (p + (-q))      by poly_sub_def
   = p_ +_ (MAP f (-q))    by ring_homo_poly_add
   = p_ +_ ($-_ q_)        by ring_homo_poly_neg
   = p_ -_ q_              by poly_sub_def
*)
val ring_homo_poly_sub = store_thm(
  "ring_homo_poly_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)``,
  metis_tac[poly_sub_def, ring_homo_poly_add, ring_homo_poly_neg, poly_neg_poly]);

(* Theorem: (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p - q)) = p_ -_ (chop_ q_)) *)
(* Proof:
   Since poly q ==> poly (-q)             by poly_neg_poly
     chop_ (MAP f (p - q))
   = chop_ (MAP f (p + -q))               by poly_sub_def
   = p_ +_ (MAP f (-q))                   by ring_homo_poly_add_chop
   = chop_ (p_ ||_ (MAP f (-q)))          by poly_add_def
   = chop_ (p_ ||_ (chop_ (MAP f (-q))))  by poly_chop_add_comm
   = chop_ (p_ ||_ ($-_ (chop_ q_)))      by ring_homo_poly_neg_chop
   = p_ +_ ($-_ (chop_ q_))               by poly_add_def
   = p_ -_ (chop_ q_)                     by poly_sub_def
*)
val ring_homo_poly_sub_chop = store_thm(
  "ring_homo_poly_sub_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q ==> (chop_ (MAP f (p - q)) = p_ -_ (chop_ q_))``,
  rpt strip_tac >>
  `poly (-q)` by rw[] >>
  `weak_ p_ /\ weak_ (MAP f (-q))` by metis_tac[ring_homo_weak, poly_is_weak] >>
  `chop_ (MAP f (p - q)) = chop_ (MAP f (p + -q))` by rw[poly_sub_def] >>
  rw_tac std_ss[ring_homo_poly_add_chop, poly_chop_add_comm, ring_homo_poly_neg_chop, poly_add_def, poly_sub_def]);

(* Theorem: !p. deg_ p_ = deg p *)
(* Proof:
   If p = |0|,
        deg_ (MAP f |0|)
      = deg_ (MAP f [])       by poly_zero
      = deg_ []               by MAP
      = 0                     by poly_deg_of_zero
      = deg |0|               by poly_deg_zero
   If p <> |0|,
      Then p_ <> []           by MAP_EQ_NIL, poly_zero
        deg_ p_
      = PRE (LENGTH p_)       by poly_deg_def
      = PRE (LENGTH p)        by LENGTH_MAP
      = deg p                 by poly_deg_def
*)
val ring_homo_poly_deg = store_thm(
  "ring_homo_poly_deg",
  ``!(r:'a ring) (r_:'b ring) (f:'a -> 'b). !p. deg_ p_ = deg p``,
  rw[poly_deg_def, MAP_EQ_NIL]);

(* Theorem: (r ~r~ r_) f ==> !p. lead_ p_ = f (lead p) *)
(* Proof:
   If p = |0|,
        lead_ (MAP f |0|)
      = lead_ (MAP f [])       by poly_zero
      = lead_ []               by MAP
      = #0_                    by poly_lead_of_zero
      = f #0                   by ring_homo_zero
      = f (lead |0|)           by poly_lead_zero
   If p <> |0|,
      Then p_ <> []            by MAP_EQ_NIL, poly_zero
        lead_ p_
      = LAST p_                by poly_lead_alt
      = f (LAST p)             by LAST_MAP
      = f (lead p)             by poly_lead_alt
*)
val ring_homo_poly_lead = store_thm(
  "ring_homo_poly_lead",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p. lead_ p_ = f (lead p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  metis_tac[MAP_EQ_NIL, poly_lead_alt, LAST_MAP, poly_zero]);

(* Theorem: (r ~r~ r_) f ==> !p k. p_ '_ k = f (p ' k) *)
(* Proof:
   If p = |0|,
        (MAP f |0|) '_ k
      = |0|_ '_ k            by ring_homo_poly_zero
      = #0_                  by poly_coeff_zero
      = f #0                 by ring_homo_zero
      = f (|0| ' k)          by poly_coeff_zero
   If p <> |0|,
      Then p_ <> []          by MAP_EQ_NIL, poly_zero
       and deg_ p_ = deg p   by ring_homo_poly_deg
       If deg p < k,
          p_ '_ k
        = #0_                by poly_coeff_nonzero
        = f #0               by ring_homo_zero
        = f (p ' k)          by poly_coeff_nonzero
       If ~(deg p < k),
          p_ '_ k
        = EL k p_            by poly_coeff_nonzero
        = f (EL k p)         by EL_MAP, poly_deg_nonzero
        = f (p ' k)          by poly_coeff_nonzero
*)
Theorem ring_homo_poly_coeff:
  !(r:'a ring) (r_:'b ring) f.
    (r ~r~ r_) f ==> !p:'a list k. poly_coeff r_ p_ k = f (p ' k)
Proof
  rpt strip_tac >>
  Cases_on ‘p = |0|’ >-
  rw[] >>
  ‘p_ <> []’ by metis_tac[MAP_EQ_NIL, poly_zero] >>
  ‘deg_ p_ = deg p’ by rw[ring_homo_poly_deg] >>
  Cases_on ‘deg p < k’ >-
  rw[poly_coeff_nonzero] >>
  ‘~(PRE (LENGTH p) < k)’ by metis_tac[poly_deg_nonzero] >>
  ‘LENGTH p <> 0’ by metis_tac[LENGTH_NIL, poly_zero] >>
  ‘k < LENGTH p’ by decide_tac >>
  rw[poly_coeff_nonzero, EL_MAP]
QED

(* Theorem: (r ~r~ r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> (MAP f (c o []) = f c o_ MAP f [])
      LHS = MAP f (c o [])
          = MAP f []                by weak_cmult_of_zero
          = []                      by MAP
      RHS = (f c) o_ (MAP f [])
          = (f c) o_ []             by MAP
          = []                      by weak_cmult_of_zero
   Step: weak p ==> (MAP f (c o p) = f c o_ p_) ==>
         !h. weak (h::p) ==> (MAP f (c o (h::p)) = f c o_ MAP f (h::p))
      Note weak (h::p) ==> h IN R /\ weak p         by weak_cons
        MAP f (c o (h::p))
      = MAP f (c * h :: c o p)            by weak_cmult_cons
      = f (c * h) :: MAP f (c o p)        by MAP
      = f (c * h) :: (f c) o_ p_          by induction hypothesis
      = (f c) *_ (f h) ::  (f c) o_ p_    by ring_homo_property
      = (f c) o_ (f h :: p_)              by weak_cmult_cons
      = (f c) o_ (MAP f (h::p))           by MAP
*)
val ring_homo_weak_cmult = store_thm(
  "ring_homo_weak_cmult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_) *)
(* Proof:
   Note weak p                by poly_is_weak
     MAP f (c * p)
   = MAP f (chop (c o p))     by poly_cmult_def
   = chop_ (MAP f (c o p))    by ring_homo_poly_chop
   = chop_ ((f c) o_ p_)      by ring_homo_weak_cmult
   = (f c) *_ p_              by poly_cmult_def
*)
val ring_homo_poly_cmult = store_thm(
  "ring_homo_poly_cmult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_)``,
  rpt strip_tac >>
  `weak p` by rw[] >>
  `MAP f (c * p) = MAP f (chop (c o p))` by rw_tac std_ss[poly_cmult_def] >>
  `_ = chop_ (MAP f (c o p))` by rw[ring_homo_poly_chop] >>
  `_ = chop_ ((f c) o_ p_)` by metis_tac[ring_homo_weak_cmult] >>
  `_ = (f c) *_ p_` by rw_tac std_ss[poly_cmult_def] >>
  rw[]);

(* Theorem: (r ~r~ r_) f ==> !p c. poly p /\ c IN R ==> (chop_ (MAP f (c * p)) = f c *_ p_) *)
(* Proof:
     chop_ (MAP f (c * p))
   = chop_ (MAP f (chop (c o p)))   by poly_cmult_def
   = chop_ (MAP f (c o p))          by ring_homo_poly_chop_of_chop
   = chop_ ((f c) o_ p_)            by ring_homo_weak_cmult
   = (f c) *_ p_                    by poly_cmult_def
*)
val ring_homo_poly_cmult_chop = store_thm(
  "ring_homo_poly_cmult_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p c. poly p /\ c IN R ==> (chop_ (MAP f (c * p)) = f c *_ p_)``,
  rw_tac std_ss[poly_cmult_def] >>
  metis_tac[ring_homo_poly_chop_of_chop, ring_homo_weak_cmult, poly_is_weak]);

(* Theorem: (r ~r~ r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n *)
(* Proof:
   If p = |0|,
        MAP f (|0| >> n)
      = MAP f |0|              by poly_shift_zero
      = |0|_                   by ring_homo_poly_zero
      = |0|_ >>_ n             by poly_shift_zero
      = (MAP f |0|) >>_ n      by ring_homo_poly_zero
   If p <> |0|,
   By induction on n.
   Base: MAP f (p >> 0) = p_ >>_ 0
        MAP f (p >> 0)
      = p_                by shift_0
      = p_ >>_ 0          by shift_0
   Step: MAP f (p >> n) = p_ >>_ n ==>
         MAP f (p >> SUC n) = p_ >>_ SUC n
      Note p <> |0|
       ==> p_ <> |0|_           by ring_homo_eq_poly_zero
        MAP f (p >> SUC n)
      = MAP f (#0:: p >> n)     by poly_shift_suc
      = f #0 :: MAP f (p >> n)  by MAP
      = f #0 :: p_ >>_ n        by induction hypothesis
      = #0_ :: p_ >>_ n         by ring_homo_zero
      = p_ >>_  (SUC n)         by poly_shift_suc
*)
val ring_homo_poly_shift = store_thm(
  "ring_homo_poly_shift",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Induct_on `n` >-
  rw[] >>
  `p_ <> |0|_` by metis_tac[ring_homo_eq_poly_zero, poly_zero] >>
  rw[poly_shift_suc]);

(* Theorem: (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_) *)
(* Proof:
   By induction on p.
   Base: MAP f ([] o q) = MAP f [] o_ q_
      LHS = MAP f ([] o q)
          = q_                    by weak_mult_of_lzero
      RHS = MAP f [] o_ q_
          = [] o_ q_              by MAP
          = q_                    by weak_mult_of_lzero
   Step: !q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_) ==>
         !h q. weak (h::p) /\ weak q ==> (MAP f ((h::p) o q) = MAP f (h::p) o_ q_)
      Note weak (h::p) ==> h IN R /\ weak p    by weak_cons
       and weak (h o q)                        by weak_cmult_weak
       and weak (p o q)                        by weak_mult_weak
       and weak (p o q >> 1)                   by poly_shift_weak
        MAP f ((h::p) o q)
      = MAP f (h o q || p o q >> 1)            by weak_mult_cons
      = MAP f (h o q) ||_ MAP f (p o q >> 1)   by ring_homo_weak_add
      = (f h) o_ q_ ||_ MAP f (p o q >> 1)  by ring_homo_weak_cmult
      = (f h) o_ q_ ||_ (MAP f (p o q)) >>_ 1      by ring_homo_poly_shift
      = (f h) o_ q_ ||_  (p_ o_ q_) >>_ 1      by induction hypothesis
      = (f h:: MAP f p) o_ q_                  by weak_mult_cons
      = MAP f (h::p) o_ q_                     by MAP
*)
val ring_homo_weak_mult = store_thm(
  "ring_homo_weak_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)``,
  ntac 4 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h o q)` by rw[] >>
  `weak (p o q)` by rw[] >>
  `weak (p o q >> 1)` by rw[] >>
  `MAP f ((h::p) o q) = MAP f (h o q || p o q >> 1)` by rw[] >>
  `_ = MAP f (h o q) ||_ MAP f (p o q >> 1)` by rw[ring_homo_weak_add] >>
  `_ = (f h) o_ q_ ||_ MAP f (p o q >> 1)` by metis_tac[ring_homo_weak_cmult] >>
  `_ = (f h) o_ q_ ||_ (MAP f (p o q)) >>_ 1` by metis_tac[ring_homo_poly_shift] >>
  `_ = (f h) o_ q_ ||_  (p_ o_ q_) >>_ 1` by rw[] >>
  `_ = (f h:: MAP f p) o_ q_` by rw[] >>
  `_ = MAP f (h::p) o_ q_ ` by rw[] >>
  rw[]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_) *)
(* Proof:
   Note weak p, weak q       by poly_is_weak
     MAP f (p * q)
   = MAP f (chop (p o q))    by poly_mult_def
   = chop_ (MAP f (p o q))   by ring_homo_poly_chop
   = chop_ (p_ o_ q_)        by ring_homo_weak_mult
   = p_ *_ q_                by poly_mult_def
*)
val ring_homo_poly_mult = store_thm(
  "ring_homo_poly_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)``,
  rpt strip_tac >>
  `MAP f (p * q) = MAP f (chop (p o q))` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop_ (MAP f (p o q))` by rw[ring_homo_poly_chop] >>
  `_ = chop_ (p_ o_ q_)` by metis_tac[ring_homo_weak_mult, poly_is_weak] >>
  `_ = p_ *_ q_` by rw[poly_mult_def] >>
  rw[]);

(* Theorem: (r ~r~ r_) f ==> !p q. poly p /\ poly q ==> (chop_ (MAP f (p * q)) = p_ *_ q_) *)
(* Proof:
     chop_ (MAP f (p * q))
   = chop_ (MAP f (chop (p o q)))  by poly_mult_def
   = chop_ (MAP f (p o q))         by ring_homo_poly_chop_of_chop
   = chop_ (p_ o_ q_)              by ring_homo_weak_mult
   = p_ *_ q_                      by poly_mult_def
*)
val ring_homo_poly_mult_chop = store_thm(
  "ring_homo_poly_mult_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q ==> (chop_ (MAP f (p * q)) = p_ *_ q_)``,
  metis_tac[poly_mult_def, ring_homo_poly_chop_of_chop, ring_homo_weak_mult, poly_is_weak]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n *)
(* Proof:
   By induction on n.
   Base: MAP f (p ** 0) = p_ **_ 0
        MAP f (p ** 0)
      = MAP f |1|             by poly_exp_0
      = |1|_                  by ring_homo_poly_one
      = p_ **_ 0              by poly_exp_0
   Step: MAP f (p ** n) = p_ **_ n ==>
         MAP f (p ** SUC n) = p_ **_ SUC n
      Note poly_ p_           by ring_homo_poly
        MAP f (p ** SUC n)
      = MAP f (p * p ** n)    by poly_exp_SUC
      = p_ *_ MAP f (p ** n)  by ring_homo_poly_mult
      = p_ *_ p_ **_ n        by induction hypothesis
      = p_ **_ SUC n          by poly_exp_SUC
*)
val ring_homo_poly_exp = store_thm(
  "ring_homo_poly_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[ring_homo_poly_one] >>
  `poly_ p_` by metis_tac[ring_homo_poly] >>
  `MAP f (p ** SUC n) = MAP f (p * p ** n)` by rw[] >>
  `_ = p_ *_ MAP f (p ** n)` by rw[ring_homo_poly_mult] >>
  `_ = p_ *_ p_ **_ n` by rw[] >>
  `_ = p_ **_ SUC n` by rw[] >>
  rw[]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. poly p ==> !n. chop_ (MAP f (p ** n)) = p_ **_ n *)
(* Proof:
   By induction on n.
   Base: chop_ (MAP f (p ** 0)) = p_ **_ 0
     LHS = chop_ (MAP f (p ** 0))
         = chop_ (MAP f |1|)         by poly_exp_0
         = chop_ |1|_                by ring_homo_poly_one_alt
         = |1|_                      by poly_chop_one, #1_ <> #0_
         = p_ **_ 0                  by poly_exp_0
         = RHS
   Step: chop_ (MAP f (p ** n)) = p_ **_ n ==> chop_ (MAP f (p ** SUC n)) = p_ **_ SUC n
     LHS = chop_ (MAP f (p ** SUC n))
         = chop_ (MAP f (p * p ** n))              by poly_exp_SUC
         = p_ *_ (MAP f (p ** n))                  by ring_homo_poly_mult_chop
         = chop_ (p_ o_ (MAP f (p ** n)))          by poly_mult_def
         = chop_ (p_ o_ (chop_ (MAP f (p ** n))))  by poly_chop_mult_comm
         = chop_ (p_ o_ (p_ **_ n))                by induction hypothesis
         = p_ *_ (p_ **_ n)                        by poly_mult_def
         = p_ **_ SUC n                            by poly_exp_SUC
         = RHS
*)
val ring_homo_poly_exp_chop = store_thm(
  "ring_homo_poly_exp_chop",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. poly p ==> !n. chop_ (MAP f (p ** n)) = p_ **_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  metis_tac[ring_homo_poly_one_alt, poly_exp_0, poly_chop_one] >>
  `weak_ p_ /\ weak_ (MAP f (p ** n))` by metis_tac[ring_homo_weak, poly_exp_poly, poly_is_weak] >>
  `chop_ (MAP f (p ** SUC n)) = chop_ (MAP f (p * p ** n))` by rw[poly_exp_SUC] >>
  `_ = p_ *_ (MAP f (p ** n))` by rw[ring_homo_poly_mult_chop] >>
  rw_tac std_ss[poly_chop_mult_comm, poly_mult_def, poly_exp_SUC]);

(* Theorem: (r ~r~ r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x)) *)
(* Proof:
   By induction on p.
   Base: poly [] ==> (f (eval [] x) = eval_ (MAP f []) (f x))
      LHS = f (eval [] x)
          = f #0                        by poly_eval_of_zero
          = #0_                         by ring_homo_zero
      RHS = eval_ (MAP f []) (f x))
          = eval_ [] (f x))             by MAP
          = #0_                         by poly_eval_of_zero
   Step: poly p ==> (f (eval p x) = eval_ p_ (f x)) ==>
         !h. poly (h::p) ==> (f (eval (h::p) x) = eval_ (MAP f (h::p)) (f x))
        f (eval (h::p) x)
      = f (h + eval p x * x)            by poly_eval_cons
      = f h +_ f (eval p x * x)         by ring_homo_property of +
      = f h +_ f (eval p x) *_ f x      by ring_homo_property of *
      = f h +_ eval_ p_ (f x) *_ f x    by induction hypothesis
      = eval_ (f h :: p_) (f x)         by poly_eval_cons
      = eval_ (MAP f (h::p)) (f x)      by MAP
*)
val ring_homo_poly_eval = store_thm(
  "ring_homo_poly_eval",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `f (eval (h::p) x) = f (h + eval p x * x)` by rw[] >>
  `_ = f h +_ f (eval p x * x)` by rw[ring_homo_property] >>
  `_ = f h +_ f (eval p x) *_ f x` by metis_tac[ring_homo_property, poly_eval_element] >>
  rw[]);

(* Theorem: (r ~r~ r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x) *)
(* Proof:
       root p x
   <=> eval p x = #0           by poly_root_def
   ==> f (eval p x) = f #0
   ==> eval_ p_ (f x) = #0_    by ring_homo_poly_eval, ring_homo_zero
   <=> root_ p_ (f x)          by poly_root_def
*)
val ring_homo_poly_root = store_thm(
  "ring_homo_poly_root",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)``,
  metis_tac[poly_root_def, ring_homo_poly_eval, ring_homo_zero]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_ *)
(* Proof:
         p pdivides q
     <=> !t. poly t /\ (q = t * p)   by poly_divides_def
     Now poly p ==> poly_ p_         by ring_homo_poly
     and poly q ==> poly_ q_         by ring_homo_poly
     and poly t ==> poly_ (MAP f t)  by ring_homo_poly
    Also MAP f q
       = MAP f (t * p)               by above
       = (MAP f t) *_ p_             by ring_homo_poly_mult
   Hence p_ pdivides_ q_             by poly_divides_def
*)
val ring_homo_poly_divides = store_thm(
  "ring_homo_poly_divides",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_``,
  metis_tac[poly_divides_def, ring_homo_poly, ring_homo_poly_mult]);

(* Theorem: (r ~r~ r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> chop_ p_ pdivides_ chop_ q_ *)
(* Proof:
   Note p pdivides q
    ==> ?t. poly t /\ (q = t * p)         by poly_divides_def
   Let t_ = MAP f t.
     chop_ q_
   = chop_ (MAP f (t * p))                by above
   = t_ *_ p_                             by ring_homo_poly_mult_chop
   = chop_ (t_ o_ p_)                     by poly_mult_def
   = chop_ ((chop_ t_) o_ (chop_ p_))     by poly_chop_mult_chop
   = (chop_ t_) *_ (chop_ p_)             by poly_mult_def
   Note weak_ t_ /\ weak_ p_ /\ weak_ q_  by ring_homo_weak
   Since poly_ (chop_ q_)                 by poly_chop_weak_poly
         poly_ (chop_ t_)                 by poly_chop_weak_poly
         poly_ (chop_ p_)                 by poly_chop_weak_poly
   Hence chop_ p_ pdivides_ chop_ q_      by poly_divides_def
*)
val ring_homo_poly_divides_chop = store_thm(
  "ring_homo_poly_divides_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q /\ p pdivides q ==> (chop_ p_) pdivides_ (chop_ q_)``,
  rpt strip_tac >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  qabbrev_tac `t_ = MAP f t` >>
  `weak_ t_ /\ weak_ p_ /\ weak_ q_` by metis_tac[ring_homo_weak, poly_is_weak] >>
  `chop_ q_ = t_ *_ p_` by rw[ring_homo_poly_mult_chop] >>
  `_ = chop_ (t_ o_ p_)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop_ ((chop_ t_) o_ (chop_ p_))` by rw_tac std_ss[poly_chop_mult_chop] >>
  `_ = (chop_ t_) *_ (chop_ p_)` by rw_tac std_ss[poly_mult_def] >>
  metis_tac[poly_divides_def, poly_chop_weak_poly]);

(* ------------------------------------------------------------------------- *)
(* Homomorphism between Polynomial Rings                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_) *)
(* Proof:
   By RingHomo_def and poly_ring_element, this is to show:
   (1) poly x ==> poly_ (MAP f x), true by ring_map_poly_to_poly
   (2) GroupHomo f r.sum r_.sum ==> GroupHomo (MAP f) (PolyRing r).sum (PolyRing r_).sum
       By GroupHomo_def and poly_ring_element, this is to show:
       (1) poly x ==> poly_ (MAP f x), true by ring_map_poly_to_poly
       (2) poly x /\ poly y ==> MAP f (x + y) = MAP f x +_ MAP f y
           True by ring_homo_poly_add
   (3) MonoidHomo f r.prod r_.prod ==> MonoidHomo (MAP f) (PolyRing r).prod (PolyRing r_).prod
       By MonoidHomo_def and poly_ring_element, this is to show:
       (1) poly x ==> poly_ (MAP f x), true by ring_map_poly_to_poly
       (2) poly x /\ poly y ==> MAP f (x * y) = MAP f x *_ MAP f y
           True by ring_homo_poly_mult
       (3) f #1 = #1_ ==> MAP f |1| = |1|_, true by ring_homo_poly_one
*)
val ring_homo_poly_ring_homo = store_thm(
  "ring_homo_poly_ring_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_)``,
  rpt (stripDup[RingHomo_def]) >>
  rw_tac std_ss[RingHomo_def, poly_ring_element] >-
  metis_tac[ring_homo_poly] >-
 (fs[GroupHomo_def] >>
  rw[poly_ring_element] >-
  metis_tac[ring_homo_poly] >>
  rw[ring_homo_poly_add]) >>
  fs[MonoidHomo_def] >>
  rw[poly_ring_element] >-
  metis_tac[ring_homo_poly] >-
  rw[ring_homo_poly_mult] >>
  rw[ring_homo_poly_one]);

(* This is a major milestone theorem. *)

(* Theorem: (r ~r~ r_) f ==> GroupHomo (chop_ o MAP f) (PolyRing r).sum (PolyRing r_).sum *)
(* Proof:
   Note Ring (PolyRing r) and Ring (PolyRing r_)    by poly_add_mult_ring
   By GroupHomo_def and poly_ring_element, this is to show:
   (1) poly x ==> poly_ (chop_ (MAP f x))
       This is true by ring_homo_poly_of_chop.
   (2) poly x /\ poly y ==> chop_ (MAP f (x + y)) = chop_ (MAP f x) +_ chop_ (MAP f y)
         chop_ (MAP f (x + y))
       = (MAP f x) +_ (MAP f y)                                   by ring_homo_poly_add_chop
       = chop_ ((MAP f x) ||_ (MAP f y))                              by poly_add_def
       = chop_ ((chop_ (MAP f x)) ||_ (chop_ (MAP f y)))  by poly_chop_add_chop
       = (chop_ (MAP f x)) +_ (chop_ (MAP f y))       by poly_add_def
*)
val ring_homo_group_homo_poly = store_thm(
  "ring_homo_group_homo_poly",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
       GroupHomo (chop_ o MAP f) (PolyRing r).sum (PolyRing r_).sum``,
  rpt strip_tac >>
  `Ring (PolyRing r) /\ Ring (PolyRing r_)` by rw[poly_add_mult_ring] >>
  rw_tac std_ss[GroupHomo_def, poly_ring_element] >-
  metis_tac[ring_homo_poly_of_chop] >>
  `weak_ (MAP f x) /\ weak_ (MAP f y)` by metis_tac[ring_homo_weak, poly_is_weak] >>
  rw_tac std_ss[ring_homo_poly_add_chop, poly_add_def, poly_chop_add_chop]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            MonoidHomo (chop_ o MAP f) (PolyRing r).prod (PolyRing r_).prod *)
(* Proof:
   First, Ring (PolyRing r) and Ring (PolyRing r_)       by poly_add_mult_ring
   By MonoidHomo_def and poly_ring_element, this is to show:
   (1) poly x ==> poly_ (chop_ (MAP f x))
       This is true by ring_homo_poly_of_chop.
   (2) poly x /\ poly y ==> chop_ (MAP f (x * y)) = (chop_ (MAP f x)) *_ (chop_ (MAP f y))
         chop_ (MAP f (x * y))
       = (MAP f x) *_ (MAP f y)                          by ring_homo_poly_mult_chop
       = chop_ ((MAP f x) o_ (MAP f y))                  by poly_mult_def
       = chop_ ((chop_ (MAP f x)) o_ (chop_ (MAP f y)))  by poly_chop_mult_chop
       = (chop_ (MAP f x)) *_ (chop_ (MAP f y))          by poly_mult_def
   (3) chop_ (MAP f |1|) = |1|_
         chop_ (MAP f |1|)
       = chop_ |1|_          by ring_homo_poly_one_alt
       = |1|_                by poly_chop_one, #1_ <> #0_
*)
val ring_homo_monoid_homo_poly = store_thm(
  "ring_homo_monoid_homo_poly",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
     MonoidHomo (chop_ o MAP f) (PolyRing r).prod (PolyRing r_).prod``,
  rpt strip_tac >>
  `Ring (PolyRing r) /\ Ring (PolyRing r_)` by rw[poly_add_mult_ring] >>
  rw_tac std_ss[MonoidHomo_def, poly_ring_element] >-
  metis_tac[ring_homo_poly_of_chop] >-
 (`weak_ (MAP f x) /\ weak_ (MAP f y)` by metis_tac[ring_homo_weak, poly_is_weak] >>
  rw_tac std_ss[ring_homo_poly_mult_chop, poly_mult_def, poly_chop_mult_chop]) >>
  metis_tac[ring_homo_poly_one_alt, poly_chop_one]);

(* Theorem: RingHomo give polynomial RingHomo.
            (r ~r~ r_) f /\ #1_ <> #0_ ==> RingHomo (chop_ o MAP f) (PolyRing r) (PolyRing r_) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN (PolyRing r).carrier ==> chop_ (MAP f x) IN (PolyRing r_).carrier
       True by ring_homo_poly_of_chop, poly_ring_element.
   (2) GroupHomo (chop_ o MAP f) (PolyRing r).sum (PolyRing r_).sum
       True by ring_homo_group_homo_poly.
   (3) MonoidHomo (chop_ o MAP f) (PolyRing r).prod (PolyRing r_).prod
       True by ring_homo_monoid_homo_poly.
*)
val ring_homo_ring_homo_poly = store_thm(
  "ring_homo_ring_homo_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
        RingHomo (chop_ o MAP f) (PolyRing r) (PolyRing r_)``,
  rpt strip_tac >>
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[ring_homo_poly_of_chop, poly_ring_element] >-
  rw[ring_homo_group_homo_poly] >>
  rw[ring_homo_monoid_homo_poly]);

(* ------------------------------------------------------------------------- *)
(* More Ring Homomorphism Theorems                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f X = X_) *)
(* Proof:
     MAP f X
   = MAP f (|1| >> 1)          by notation
   = (MAP f |1|) >>_ 1         by ring_homo_poly_shift
   = (|1|_) >>_ 1              by ring_homo_poly_one_alt
   = X_                        by notation
*)
val ring_homo_poly_X = store_thm(
  "ring_homo_poly_X",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> (MAP f X = X_)``,
  metis_tac[ring_homo_poly_shift, ring_homo_poly_one_alt]);

(* Theorem: (r ~r~ r_) f ==> !c:num. 0 < c /\ c < char r_ ==> (MAP f |c| = |c|_) *)
(* Proof:
   Note ##c <> #0
      and ##_ #1_ c <> #0_   by ring_homo_sum_num_property
     MAP f |c|
   = MAP f [##c]             by poly_ring_sum_c, ##c <> #0
   = [f (##c)]               by MAP
   = [##_ #1_ c]             by ring_homo_num
   = |c|_                    by poly_ring_sum_c, ##_ #1_ c <> #0_
*)
val ring_homo_poly_sum_num = store_thm(
  "ring_homo_poly_sum_num",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c:num. 0 < c /\ c < char r_ ==> (MAP f |c| = |c|_)``,
  rpt strip_tac >>
  `##c <> #0 /\ ##_ #1_ c <> #0_` by metis_tac[ring_homo_sum_num_property] >>
  rw[ring_homo_num, poly_ring_sum_c]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. weak p /\ (lead p = #1) ==> poly_ p_ *)
(* Proof:
   Note weak p ==> weak_ p_      by ring_homo_weak
     and  lead_ p_
        = f #1                   by ring_homo_poly_lead
        = #1_                    by ring_homo_one
        <> #0_                   by given
   Hence poly_ p_                by poly_nonzero_lead_nonzero
*)
val ring_homo_weak_monic_poly = store_thm(
  "ring_homo_weak_monic_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. weak p /\ (lead p = #1) ==> poly_ p_``,
  metis_tac[ring_homo_weak, ring_homo_poly_lead, ring_homo_one, poly_nonzero_lead_nonzero]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> monic_ p_ *)
(* Proof:
   By poly_monic_def, this is to show:
   (1) poly p /\ lead p = #1 ==> poly_ p_
       True by ring_homo_weak_monic_poly, poly_is_weak.
   (2) lead p = #1 ==> lead_ p_ = #1_
         lead_ p_
       = f (lead p)         by ring_homo_poly_lead
       = f #1               by given
       = #1_                by ring_homo_one
*)
val ring_homo_monic_monic = store_thm(
  "ring_homo_monic_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> poly_monic r_ p_``,
  rw[poly_monic_def] >-
  metis_tac[ring_homo_weak_monic_poly, poly_is_weak] >>
  metis_tac[ring_homo_poly_lead, ring_homo_one]);

(* Theorem: !p. monic p ==> !n. monic_ (MAP f (p ** n)) *)
(* Proof:
   Since monic p
     ==> monic (p ** n)                     by poly_monic_exp_monic
     ==> monic_ (MAP f (p ** n))            by ring_homo_monic_monic
*)
val ring_homo_monic_exp_monic = store_thm(
  "ring_homo_monic_exp_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. monic p ==> !n. monic_ (MAP f (p ** n))``,
  metis_tac[ring_homo_monic_monic, poly_monic_exp_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. monic p ==> !n. MAP f (p ** n) = p_ **_ n *)
(* Proof:
   Since monic p
     ==> monic_ (MAP f (p ** n))            by ring_homo_monic_exp_monic
     ==> poly p /\ poly_ (MAP f (p ** n))   by poly_monic_def
         MAP f (p ** n)
       = chop_ (MAP f (p ** n))             by poly_chop_poly
       = p_ **_ n                           by ring_homo_poly_exp_chop
*)
val ring_homo_monic_poly_exp = store_thm(
  "ring_homo_monic_poly_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. monic p ==> !n. MAP f (p ** n) = p_ **_ n``,
  rpt strip_tac >>
  `monic_ (MAP f (p ** n))` by rw[ring_homo_monic_exp_monic] >>
  `poly p /\ poly_ (MAP f (p ** n))` by rw[] >>
  metis_tac[ring_homo_poly_exp_chop, poly_chop_poly]);

(* Theorem: (r ~r~ r_) f ==> !c. 0 < c /\ c < char r_ ==> poly_ (MAP f |c|) *)
(* Proof:
   Given 0 < c /\ c < char r_,
         f (##c) <> #0_          by ring_homo_num_nonzero
     MAP f |c|
   = MAP f (chop [##c])          by poly_ring_sum_c, ##c <> #0
   = MAP f [##c]                 by poly_chop_const_nonzero
   = [f (##c)]                   by MAP
  Since f (##c) IN R_            by ring_homo_element
  Thus poly_ [f (##c)]           by poly_nonzero_element_poly
*)
val ring_homo_poly_sum_num_poly = store_thm(
  "ring_homo_poly_sum_num_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c. 0 < c /\ c < char r_ ==> poly_ (MAP f |c|)``,
  rpt strip_tac >>
  `##c <> #0 /\ f (##c) <> #0_` by metis_tac[ring_homo_num_nonzero] >>
  `MAP f |c| = [f (##c)]` by rw[poly_ring_sum_c] >>
  `f (##c) IN R_` by metis_tac[ring_homo_element, ring_num_element] >>
  rw[poly_nonzero_element_poly]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. monic_ (MAP f (X + |c|)) *)
(* Proof:
   Note monic (X + |c|)            by poly_monic_X_add_c
   Thus monic_ (MAP f (X + |c|))   by ring_homo_monic_monic
*)
val ring_homo_X_add_c_monic = store_thm(
  "ring_homo_X_add_c_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c:num. monic_ (MAP f (X + |c|))``,
  metis_tac[poly_monic_X_add_c, ring_homo_monic_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. poly_ (MAP f (X + |c|)) *)
(* Proof:
   Since monic_ (MAP f (X + |c|))    by ring_homo_X_add_c_monic
     ==> poly_ (MAP (X + |c|))       by poly_monic_poly
*)
val ring_homo_X_add_c_poly = store_thm(
  "ring_homo_X_add_c_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c:num. poly_ (MAP f (X + |c|))``,
  rw[ring_homo_X_add_c_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. MAP f (X + |c|) = (MAP f X) +_ (MAP f |c|) *)
(* Proof:
   Since poly_ (MAP f (X + |c|))     by ring_homo_X_add_c_poly
     MAP f (X + |c|)
   = chop_ (MAP f (X + |c|))         by poly_chop_poly
   = (MAP f X) +_ (MAP f |c|)        by ring_homo_poly_add_chop
*)
val ring_homo_poly_X_add_c = store_thm(
  "ring_homo_poly_X_add_c",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !c:num. MAP f (X + |c|) = (MAP f X) +_ (MAP f |c|)``,
  rpt strip_tac >>
  `poly X /\ poly |c|` by rw[] >>
  `poly_ (MAP f (X + |c|))` by rw[ring_homo_X_add_c_poly] >>
  metis_tac[poly_chop_poly, ring_homo_poly_add_chop]);

(* Theorem: 0 < n ==> !c. monic_ (MAP f (X ** n + |c|)) *)
(* Proof:
   Note monic (X ** n + |c|)            by poly_monic_X_exp_n_add_c, 0 < n.
   Thus monic_ (MAP f (X ** n - |c|))   by ring_homo_monic_monic
*)
val ring_homo_X_exp_n_add_c_monic = store_thm(
  "ring_homo_X_exp_n_add_c_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. 0 < n ==> !c:num. monic_ (MAP f (X ** n + |c|))``,
  metis_tac[poly_monic_X_exp_n_add_c, ring_homo_monic_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !n c. 0 < n ==> poly_ (MAP f (X ** n + |c|)) *)
(* Proof:
   Since 0 < n,
         monic_ (MAP f (X ** n + |c|))   by ring_homo_X_exp_n_add_c_monic
   Hence poly_ (MAP f (X ** n + |c|))    by poly_monic_poly
*)
val ring_homo_X_exp_n_add_c_poly = store_thm(
  "ring_homo_X_exp_n_add_c_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. 0 < n ==> !c:num. poly_ (MAP f (X ** n + |c|))``,
  rw[ring_homo_X_exp_n_add_c_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !c n. 0 < n ==> (MAP f (X ** n + |c|) = MAP f X **_ n +_ MAP f |c|) *)
(* Proof:
   Since poly_ (MAP f (X ** n + |c|))     by ring_homo_X_exp_n_add_c_poly, 0 < n
     and monic X                          by poly_monic_X
     MAP f (X ** n + |c|)
   = chop_ (MAP f (X ** n + |c|))         by poly_chop_poly
   = (MAP f (X ** n)) +_ (MAP f |c|)      by ring_homo_poly_add_chop
   = (MAP f X) **_ n +_ (MAP f |c|)       by ring_homo_monic_poly_exp
*)
val ring_homo_poly_X_exp_n_add_c = store_thm(
  "ring_homo_poly_X_exp_n_add_c",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n c:num. 0 < n ==> (MAP f (X ** n + |c|) = MAP f X **_ n +_ MAP f |c|)``,
  rpt strip_tac >>
  `monic X` by rw[] >>
  `poly_ (MAP f (X ** n + |c|))` by rw[ring_homo_X_exp_n_add_c_poly] >>
  `MAP f (X ** n + |c|) = chop_ (MAP f (X ** n + |c|))` by rw[poly_chop_poly] >>
  `_ = (MAP f (X ** n)) +_ (MAP f |c|)` by rw[ring_homo_poly_add_chop] >>
  metis_tac[ring_homo_monic_poly_exp]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. monic_ (MAP f (X - |c|)) *)
(* Proof:
   Note monic (X - |c|)            by poly_monic_X_sub_c
   Thus monic_ (MAP f (X + |c|))   by ring_homo_monic_monic
*)
val ring_homo_X_sub_c_monic = store_thm(
  "ring_homo_X_sub_c_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c:num. monic_ (MAP f (X - |c|))``,
  metis_tac[poly_monic_X_sub_c, ring_homo_monic_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !c. poly_ (MAP f (X - |c|)) *)
(* Proof:
   Since monic_ (MAP f (X - |c|))    by ring_homo_X_sub_c_monic
     ==> poly_ (MAP (X - |c|))       by poly_monic_poly
*)
val ring_homo_X_sub_c_poly = store_thm(
  "ring_homo_X_sub_c_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !c:num. poly_ (MAP f (X - |c|))``,
  rw[ring_homo_X_sub_c_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !c. 0 < c /\ c < char r_ ==> (MAP f (X - |c|) = (MAP f X) -_ (MAP f |c|)) *)
(* Proof:
   Since poly_ (MAP f (X - |c|))     by ring_homo_X_sub_c_poly
     and poly_ (MAP f |c|)           by ring_homo_poly_sum_num_poly
     MAP f (X - |c|)
   = chop_ (MAP f (X - |c|))         by poly_chop_poly
   = (MAP f X) -_ chop_ (MAP f |c|)  by ring_homo_poly_sub_chop
   = (MAP f X) -_ (MAP f |c|)        by poly_chop_poly
*)
val ring_homo_poly_X_sub_c = store_thm(
  "ring_homo_poly_X_sub_c",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !c:num. 0 < c /\ c < char r_ ==> (MAP f (X - |c|) = (MAP f X) -_ (MAP f |c|))``,
  rpt strip_tac >>
  `poly X /\ poly |c|` by rw[] >>
  `poly_ (MAP f (X - |c|))` by rw[ring_homo_X_sub_c_poly] >>
  `poly_ (MAP f |c|)` by rw[ring_homo_poly_sum_num_poly] >>
  metis_tac[poly_chop_poly, ring_homo_poly_sub_chop]);

(* Theorem: 0 < n ==> !c. monic_ (MAP f (X ** n - |c|)) *)
(* Proof:
   Note monic (X ** n - |c|)            by poly_monic_X_exp_n_sub_c, 0 < n.
   Thus monic_ (MAP f (X ** n - |c|))   by ring_homo_monic_monic
*)
val ring_homo_X_exp_n_sub_c_monic = store_thm(
  "ring_homo_X_exp_n_sub_c_monic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. 0 < n ==> !c:num. monic_ (MAP f (X ** n - |c|))``,
  metis_tac[poly_monic_X_exp_n_sub_c, ring_homo_monic_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !n c. 0 < n ==> poly_ (MAP f (X ** n - |c|)) *)
(* Proof:
   Since 0 < n,
         monic_ (MAP f (X ** n - |c|))   by ring_homo_X_exp_n_sub_c_monic
   Hence poly_ (MAP f (X ** n - |c|))    by poly_monic_poly
*)
val ring_homo_X_exp_n_sub_c_poly = store_thm(
  "ring_homo_X_exp_n_sub_c_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. 0 < n ==> !c:num. poly_ (MAP f (X ** n - |c|))``,
  rw[ring_homo_X_exp_n_sub_c_monic]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !c. 0 < c /\ c < char r_ ==> !n. 0 < n ==> (MAP f (X ** n - |c|) = MAP f X **_ n -_ MAP f |c|) *)
(* Proof:
   Note  ##c <> #0 and ##_ #1_ c <> #0_       by ring_homo_sum_num_property
   Since monic X                              by poly_monic_X
         MAP f (X ** n) = (MAP f X) **_ n     by ring_homo_monic_poly_exp
   Hence goal becomes: MAP f (X ** n - |c|) = (MAP f (X ** n)) -_ (MAP f |c|)
   Now,
         poly_ (MAP f |c|)                    by ring_homo_poly_sum_num_poly
      so chop_ (MAP f |c|) = MAP f |c|        by poly_chop_poly
    Also poly_ (MAP f (X ** n - |c|))         by ring_homo_X_exp_n_sub_c_poly
      so chop_ (MAP f (X ** n - |c|)) = MAP f (X ** n - |c|)  by poly_chop_poly
    With poly |c|                             by poly_sum_num_poly
     and poly (X ** n)                        by poly_X, poly_exp_poly
    Hence result is true                      by ring_homo_poly_sub_chop
*)
val ring_homo_poly_X_exp_n_sub_c = store_thm(
  "ring_homo_poly_X_exp_n_sub_c",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. 0 < n ==> !c. 0 < c /\ c < char r_ ==> (MAP f (X ** n - |c|) = MAP f X **_ n -_ MAP f |c|)``,
  rpt strip_tac >>
  `##c <> #0 /\ ##_ #1_ c <> #0_` by metis_tac[ring_homo_sum_num_property] >>
  `MAP f (X ** n - |c|) = (MAP f (X ** n)) -_ (MAP f |c|)` suffices_by metis_tac[ring_homo_monic_poly_exp, poly_monic_X] >>
  `poly_ (MAP f |c|)` by rw[ring_homo_poly_sum_num_poly] >>
  `poly_ (MAP f (X ** n - |c|))` by rw[ring_homo_X_exp_n_sub_c_poly] >>
  `poly |c| /\ poly (X ** n)` by rw[] >>
  metis_tac[ring_homo_poly_sub_chop, poly_chop_poly]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !n. poly_ (MAP f (unity n)) *)
(* Proof:
   If n = 0, this is to show: poly_ (MAP f (unity 0))
      MAP f (unity 0)
    = MAP f |0|                  by poly_unity_0
    = |0|_                       by ring_homo_poly_zero
    and poly_ (|0|_)             by poly_zero_poly
   If n <> 0, 0 < n,
   Note |1| = ### 1              by poly_ring_sum_1
   Thus poly_ (MAP f (unity n))  by ring_homo_X_exp_n_sub_c_poly
*)
val ring_homo_unity_poly = store_thm(
  "ring_homo_unity_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. poly_ (MAP f (unity n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[poly_unity_0, ring_homo_poly_zero] >>
  `0 < n` by decide_tac >>
  metis_tac[ring_homo_X_exp_n_sub_c_poly, poly_ring_sum_1]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !n. MAP f (unity n) = MAP f X **_ n -_ MAP f |1| *)
(* Proof:
   Since monic X                              by poly_monic_X
         MAP f (X ** n) = (MAP f X) **_ n     by ring_homo_monic_poly_exp
   Hence goal becomes: MAP f (unity n) = (MAP f (X ** n)) -_ (MAP f |1|)
   Now,
         poly_ (MAP f |1|)                    by ring_homo_poly_one_alt, poly_one_poly
      so chop_ (MAP f |1|) = MAP f |1|   by poly_chop_poly
    Also poly_ (MAP f (unity n))              by ring_homo_unity_poly
      so chop_ (MAP f (unity n)) = MAP f (unity n)  by poly_chop_poly
    With poly |1|                             by poly_one_poly
     and poly (X ** n)                        by poly_X, poly_exp_poly
    Hence the result is true                  by ring_homo_poly_sub_chop
*)
val ring_homo_poly_unity = store_thm(
  "ring_homo_poly_unity",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !n. MAP f (unity n) = MAP f X **_ n -_ MAP f |1|``,
  rpt strip_tac >>
  `MAP f (unity n) = (MAP f (X ** n)) -_ (MAP f |1|)` suffices_by metis_tac[ring_homo_monic_poly_exp, poly_monic_X] >>
  `poly_ (MAP f |1|)` by metis_tac[ring_homo_poly_one_alt, poly_one_poly] >>
  `poly_ (MAP f (unity n))` by rw[ring_homo_unity_poly] >>
  `poly |1| /\ poly (X ** n)` by rw[] >>
  metis_tac[ring_homo_poly_sub_chop, poly_chop_poly]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !p q. poly p /\ poly q ==> (chop_ (MAP f (peval p q)) = peval_ p_ q_) *)
(* Proof:
   By induction on p.
   Base: poly [] ==> (chop_ (MAP f (peval [] q)) = peval_ (MAP f []) q_)
     LHS = chop_ (MAP f (peval [] q))
         = chop_ (MAP f |0|)           by poly_peval_of_zero
         = chop_ (|0|_)                by ring_homo_poly_zero
         = |0|_                        by poly_chop_zero
     RHS = peval_ (MAP f []) q_
         = peval_ [] q_                by MAP
         = |0|_                        by poly_peval_of_zero
   Step: poly p ==> (chop_ (MAP f (peval p q)) = peval_ p_ q_) ==>
         !h. poly (h::p) ==> (chop_ (MAP f (peval (h::p) q)) = peval_ (MAP f (h::p)) q_)
     poly (h::p) ==> h IN R /\ poly p  by poly_cons_poly

       chop_ (MAP f (h * |1|))
     = (f h) *_ (MAP f |1|)            by ring_homo_poly_cmult_chop
     = (f h) *_ |1|_                   by ring_homo_poly_one_alt, [1]

       chop_ (MAP f (peval p q * q))
     = (MAP f (peval p q)) *_ q_                   by ring_homo_poly_mult_chop
     = chop_ ((MAP f (peval p q)) o_ q_)           by poly_mult_def
     = chop_ ((chop_ (MAP f (peval p q))) o_ q_)   by poly_chop_mult
     = chop_ ((peval_ p_ q_) o_ q_)                by induction hypothesis
     = (peval_ p_ q_) *_ q_                        by poly_mult_def, [2]

     LHS = chop_ (MAP f (peval (h::p) q))
         = chop_ (MAP f (h * |1| + peval p q * q))                by poly_peval_cons
         = (MAP f (h * |1|)) +_ (MAP f (peval p q * q))           by ring_homo_poly_add_chop
         = chop_ ((MAP f (h * |1|)) ||_ (MAP f (peval p q * q)))  by poly_add_def
         = chop_ ((chop_ (MAP f (h * |1|))) ||_ (chop_ (MAP f (peval p q * q)))) by poly_chop_add_chop
         = chop_ (((f h) *_ |1|_) ||_ ((peval_ p_ q_) *_ q_))     by above [1] [2]
         = ((f h) *_ |1|_) +_ ((peval_ p_ q_) *_ q_)              by poly_add_def
         = peval_ ((f h)::p_) q_            by poly_peval_cons
         = peval_ (MAP f (h::p)) q_         by MAP
         = RHS
*)
val ring_homo_peval_chop = store_thm(
  "ring_homo_peval_chop",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p q. poly p /\ poly q ==> (chop_ (MAP f (peval p q)) = peval_ p_ q_)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `chop_ (MAP f (h * |1|)) = (f h) *_ (MAP f |1|)` by rw[ring_homo_poly_cmult_chop] >>
  `_ = (f h) *_ |1|_` by metis_tac[ring_homo_poly_one_alt] >>
  `weak_ (MAP f (peval p q)) /\ weak_ q_` by metis_tac[ring_homo_weak, poly_peval_poly, poly_is_weak] >>
  `chop_ (MAP f (peval p q * q)) = (MAP f (peval p q)) *_ q_` by rw[ring_homo_poly_mult_chop] >>
  `_ = chop_ ((MAP f (peval p q)) o_ q_)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop_ ((chop_ (MAP f (peval p q))) o_ q_)` by rw_tac std_ss[poly_chop_mult] >>
  `_ = chop_ ((peval_ p_ q_) o_ q_)` by rw_tac std_ss[] >>
  `_ = (peval_ p_ q_) *_ q_` by rw_tac std_ss[poly_mult_def] >>
  `poly (h * |1|) /\ poly (peval p q * q)` by rw[] >>
  `weak_ (MAP f (h * |1|)) /\ weak_ (MAP f (peval p q * q))` by metis_tac[ring_homo_weak, poly_is_weak] >>
  `chop_ (MAP f (peval (h::p) q)) = chop_ (MAP f (h * |1| + peval p q * q))` by rw_tac std_ss[poly_peval_cons] >>
  `_ = (MAP f (h * |1|)) +_ (MAP f (peval p q * q))` by rw_tac std_ss[ring_homo_poly_add_chop] >>
  `_ = chop_ ((MAP f (h * |1|)) ||_ (MAP f (peval p q * q)))` by rw_tac std_ss[poly_add_def] >>
  `_ = chop_ ((chop_ (MAP f (h * |1|))) ||_ (chop_ (MAP f (peval p q * q))))` by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = chop_ (((f h) *_ |1|_) ||_ ((peval_ p_ q_) *_ q_))` by rw_tac std_ss[] >>
  `_ = ((f h) *_ |1|_) +_ ((peval_ p_ q_) *_ q_)` by rw_tac std_ss[poly_add_def] >>
  `_ = peval_ ((f h)::p_) q_` by rw_tac std_ss[poly_peval_cons] >>
  `_ = peval_ (MAP f (h::p)) q_` by rw_tac std_ss[MAP] >>
  rw_tac std_ss[]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !p. poly p /\ f (lead p) <> #0_ ==> poly_ p_ /\ p_ <> |0|_ *)
(* Proof:
   If p = |0|,
      then lead p = #0      by poly_lead_zero
       and f #0 = #0_       by ring_homo_zero
      which contradicts f (lead p) <> #0_.
   If p <> |0|,
      poly p ==> weak p     by poly_is_weak
      so weak_ p_           by ring_homo_weak
    with lead_ p_
       = f (lead p)         by ring_homo_poly_lead
       <> #0_               by given
    This is true            by poly_nonzero_lead_nonzero
*)
val ring_homo_poly_nonzero = store_thm(
  "ring_homo_poly_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p. poly p /\ f (lead p) <> #0_ ==>
       poly_ p_ /\ p_ <> |0|_``,
  ntac 6 strip_tac >>
  Cases_on `p = |0|` >-
  metis_tac[poly_lead_zero, ring_homo_zero] >>
  metis_tac[ring_homo_weak, poly_is_weak, ring_homo_poly_lead, poly_nonzero_lead_nonzero]);

(* Theorem: (r ~r~ r_) f ==> !p. poly p /\ f (lead p) <> #0_ ==> (MAP f (-p) = $-_ p_) *)
(* Proof:
   Since poly p /\ f (lead p) <> #0_  by given
     ==> poly_ p_                     by ring_homo_poly_nonzero
     ==> poly_ ($-_ p_)               by poly_neg_poly

    Also lead p IN R                  by poly_lead_element
     ==> f (lead p) IN R_             by ring_homo_element
         f (lead (-p))
       = f (- lead p)                 by poly_lead_negate
       = $-_ (f (lead p))             by ring_homo_neg
     and $-_ (f (lead p)) <> #0_      by ring_neg_eq_zero
   Since poly (-p)                    by poly_neg_poly
   Hence poly_ (MAP f (-p))           by ring_homo_poly_nonzero

     MAP f (-p)
   = chop_ (MAP f (-p))               by poly_chop_poly
   = $-_ (chop_ p_)                   by ring_homo_poly_neg_chop
   = chop_ ($-_ p_)                   by poly_chop_negate
   = $-_ p_                           by poly_chop_poly
*)
val ring_homo_poly_negate = store_thm(
  "ring_homo_poly_negate",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p. poly p /\ f (lead p) <> #0_ ==> (MAP f (-p) = $-_ p_)``,
  rpt strip_tac >>
  `poly_ p_` by metis_tac[ring_homo_poly_nonzero] >>
  `poly_ ($-_ p_)` by rw[] >>
  `lead p IN R` by rw[] >>
  `f (lead p) IN R_` by metis_tac[ring_homo_element] >>
  `f (lead (-p)) = f (- lead p)` by rw[poly_lead_negate] >>
  `_ = $-_ (f (lead p))` by rw[ring_homo_neg] >>
  `$-_ (f (lead p)) <> #0_` by rw[ring_neg_eq_zero] >>
  `poly_ (MAP f (-p))` by metis_tac[ring_homo_poly_nonzero, poly_neg_poly] >>
  metis_tac[ring_homo_poly_neg_chop, poly_chop_negate, poly_chop_poly]);

(* Theorem: (r ~r~ r_) f ==>
           !p q. poly p /\ poly q /\ f (lead q) <> #0_ ==> (chop_ (MAP f (p - q)) = p_ -_ q_) *)
(* Proof:
   With poly q /\ f (lead q) <> #0_,
        poly_ q_             by ring_homo_poly_nonzero
     chop_ (MAP f (p - q))
   = p_ -_ (chop_ q_)        by ring_homo_poly_sub_chop
   = p_ -_ q_                by poly_chop_poly
*)
val ring_homo_poly_sub_chop_alt = store_thm(
  "ring_homo_poly_sub_chop_alt",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q /\ f (lead q) <> #0_ ==> (chop_ (MAP f (p - q)) = p_ -_ q_)``,
  metis_tac[ring_homo_poly_nonzero, ring_homo_poly_sub_chop, poly_chop_poly]);

(* Theorem: (r ~r~ r_) f ==>
           !p q. poly p /\ poly q ==> (chop_ (MAP f (p - q)) = (chop_ p_) -_ (chop_ q_)) *)
(* Proof:
   Note poly q ==> poly (-q)                       by poly_neg_poly
     chop_ (MAP f (p - q))
   = chop_ (MAP f (p + -q))                        by poly_sub_def
   = p_ +_ (MAP f (-q))                            by ring_homo_poly_add_chop
   = chop_ (p_ ||_ (MAP f (-q)))                   by poly_add_def
   = chop_ ((chop_ p_) ||_ (chop_ (MAP f (-q))))   by poly_chop_add_chop
   = chop_ ((chop_ p_) ||_ ($-_ (chop_ q_)))       by ring_homo_poly_neg_chop
   = (chop_ p_) +_ ($-_ (chop_ q_))                by poly_add_def
   = (chop_ p_) -_ (chop_ q_)                      by poly_sub_def
*)
val ring_homo_sub_chop_chop = store_thm(
  "ring_homo_sub_chop_chop",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !p q. poly p /\ poly q ==> (chop_ (MAP f (p - q)) = (chop_ p_) -_ (chop_ q_))``,
  rpt strip_tac >>
  `poly (-q)` by rw[] >>
  `weak_ p_ /\ weak_ (MAP f (-q))` by metis_tac[ring_homo_weak, poly_is_weak] >>
  `chop_ (MAP f (p - q)) = chop_ (MAP f (p + -q))` by rw[poly_sub_def] >>
  rw_tac std_ss[ring_homo_poly_add_chop, poly_chop_add_chop, ring_homo_poly_neg_chop, poly_add_def, poly_sub_def]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==>
            !p. ulead p ==> poly_ p_ /\ (unit_ (lead_ p_)) *)
(* Proof:
   Note ulead p <=> poly p /\ unit (lead p)    by notation
   Note poly p ==> poly_ p_                    by ring_homo_poly, INJ f R R_
    and unit (lead p) ==> unit_ (lead_ p_)     by ring_homo_poly_lead, ring_homo_unit
   Thus all assertions are true.
*)
val ring_homo_ulead = store_thm(
  "ring_homo_ulead",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p. ulead p ==> poly_ p_ /\ (unit_ (lead_ p_))``,
  prove_tac[ring_homo_poly, ring_homo_poly_lead, ring_homo_unit]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==>
            !p. pmonic p ==> poly_ p_ /\ (unit_ (lead_ p_)) /\ 0 < deg_ p_ *)
(* Proof:
   Note pmonic p
    <=> poly p /\ 0 < deg p /\ unit (lead p)   by notation
   Note poly p ==> poly_ p_                    by ring_homo_poly, INJ f R R_
    and deg_ p_ = deg p                        by ring_homo_poly_deg
    and unit (lead p) ==> unit_ (lead_ p_)     by ring_homo_poly_lead, ring_homo_unit
   Thus all assertions are true.
*)
val ring_homo_pmonic = store_thm(
  "ring_homo_pmonic",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p. pmonic p ==> poly_ p_ /\ (unit_ (lead_ p_)) /\ 0 < deg_ p_``,
  prove_tac[ring_homo_poly_deg, ring_homo_poly, ring_homo_poly_lead, ring_homo_unit]);

(* The following similar theorems do not rely on INJ f R R_, just #1_ <> #0_ *)

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !p. ulead p ==> poly_ p_ /\ unit_ (lead_ p_) *)
(* Proof:
   Note ulead p <=> poly p /\ unit (lead p)     by notation
   Thus unit (lead p) ==> unit_ (f (lead p))    by ring_homo_unit
                      ==> f (lead p) <> #0_     by ring_unit_nonzero
   Hence poly_ p_                               by ring_homo_poly_nonzero
     and f (lead p) = lead_ p_                  by ring_homo_poly_lead
   All assertions are true.
*)
val ring_homo_poly_ulead = store_thm(
  "ring_homo_poly_ulead",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. ulead p ==> poly_ p_ /\ unit_ (lead_ p_)``,
  ntac 6 strip_tac >>
  `unit_ (f (lead p))` by metis_tac[ring_homo_unit] >>
  `f (lead p) <> #0_` by rw[ring_unit_nonzero] >>
  prove_tac[ring_homo_poly_nonzero, ring_homo_poly_lead]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !p. pmonic p ==> poly_ p_ /\ unit_ (lead_ p_) /\ 0 < deg_ p_ *)
(* Proof:
   Note pmonic p <=>
        poly p /\ 0 < deg p /\ unit (lead p)   by notation
   Thus unit (lead p) ==> unit_ (f (lead p))   by ring_homo_unit
                      ==> f (lead p) <> #0_    by ring_unit_nonzero
   Hence poly_ p_                              by ring_homo_poly_nonzero
   Since f (lead p) = lead_ p_                 by ring_homo_poly_lead
     and deg_ p_ = deg p                       by poly_deg_map
   All assertions are true.
*)
val ring_homo_poly_pmonic = store_thm(
  "ring_homo_poly_pmonic",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !p. pmonic p ==> poly_ p_ /\ unit_ (lead_ p_) /\ 0 < deg_ p_``,
  ntac 6 strip_tac >>
  `unit_ (f (lead p))` by metis_tac[ring_homo_unit] >>
  `f (lead p) <> #0_` by rw[ring_unit_nonzero] >>
  prove_tac[ring_homo_poly_nonzero, ring_homo_poly_lead, poly_deg_map]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ ulead q ==>
            (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_) *)
(* Proof:
   Let s = p / q, t = p % q.
   Then poly s                    by poly_div_poly
    and poly t                    by poly_mod_poly
   Let s_ = MAP f s, t_ = MAP f t.
   Then poly_ p_ /\ poly_ q_      by ring_homo_poly, INJ f R R_
    and poly_ s_ /\ poly_ t_      by ring_homo_poly, INJ f R R_
   Note unit_ (lead_ q_)          by ring_homo_poly_lead, ring_homo_unit
    and deg_ q_ = deg q           by ring_homo_poly_deg

   If deg q = 0,
      Then s = |/ (lead q) * p) /\ t = |0|   by poly_div_mod_by_const
       and t_ = |0|_                         by poly_div_mod_by_const, ring_homo_poly_zero
       and s_ = |/_ (lead_ q_) *_ p_         by poly_div_mod_by_const, ring_homo_inv,
                           ring_homo_poly_lead, ring_homo_poly_cmult, ring_unit_inv_element
      Thus s_ = p_ /_ q_ /\ t_ = p_ %_ q_    by poly_div_mod_by_const

   If deg q <> 0,
      Then (p = s * q + t) /\ deg t < deg q  by poly_division, pmonic q
        p_
      = MAP f p                          by notation
      = MAP f (s * q + t)                by above
      = MAP f (s * q) +_ t_              by ring_homo_poly_add, INJ f R R_
      = s_ *_ q_ +_ t_                   by ring_homo_poly_mult, INJ f R R_
    Now deg_ t_ < deg_ q_                by ring_homo_poly_deg, deg t < deg q
   Thus s_ = p_ /_ q_ /\ t_ = p_ %_ q_   by poly_div_mod_eqn, pmonic_ q_
*)
val ring_homo_poly_div_mod = store_thm(
  "ring_homo_poly_div_mod",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ ulead q ==>
    (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_)``,
  ntac 7 strip_tac >>
  qabbrev_tac `s = p / q` >>
  qabbrev_tac `t = p % q` >>
  `poly s /\ poly t` by rw[poly_div_poly, poly_mod_poly, Abbr`s`, Abbr`t`] >>
  qabbrev_tac `s_ = MAP f s` >>
  qabbrev_tac `t_ = MAP f t` >>
  `poly_ p_ /\ poly_ q_ /\ poly_ s_ /\ poly_ t_` by metis_tac[ring_homo_poly] >>
  `unit_ (lead_ q_)` by metis_tac[ring_homo_poly_lead, ring_homo_unit] >>
  `deg_ q_ = deg q` by metis_tac[ring_homo_poly_deg] >>
  Cases_on `deg q = 0` >| [
    `(s = |/ (lead q) * p) /\ (t = |0|)` by rw[poly_div_mod_by_const, Abbr`s`, Abbr`t`] >>
    `t_ = |0|_` by metis_tac[poly_div_mod_by_const, ring_homo_poly_zero] >>
    `s_ = |/_ (lead_ q_) *_ p_` by metis_tac[poly_div_mod_by_const, ring_homo_inv, ring_homo_poly_lead, ring_homo_poly_cmult, ring_unit_inv_element] >>
    rw[poly_div_mod_by_const],
    `(p = s * q + t) /\ deg t < deg q` by rw[poly_division, Abbr`s`, Abbr`t`] >>
    `p_ = MAP f (s * q) +_ t_` by rw[ring_homo_poly_add, Abbr`t_`] >>
    `_ = s_ *_ q_ +_ t_` by metis_tac[ring_homo_poly_mult] >>
    `deg_ t_ < deg_ q_` by metis_tac[ring_homo_poly_deg] >>
    metis_tac[poly_div_mod_eqn]
  ]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ pmonic q ==>
            (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\ (deg_ (MAP f (p % q)) < deg_ q_) *)
(* Proof:
   Let s = p / q, t = p % q.
   Then poly s /\ poly t            by poly_div_poly, poly_mod_poly
    and (MAP f s = p_ /_ q_) /\
        (MAP f t = p_ %_ q_)        by ring_homo_poly_div_mod, INJ f R R_
    and unit_ (lead_ q_)            by ring_homo_poly_lead, ring_homo_unit
    and deg_ q_ = deg q             by ring_homo_poly_deg
    ==> 0 < deg_ q_                 by 0 < deg q
   Note poly_ p_ /\ poly_ q_        by ring_homo_poly, INJ f R R_
   The result follows               by poly_division, Ring r_
*)
val ring_homo_poly_div_mod_eqn = store_thm(
  "ring_homo_poly_div_mod_eqn",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ pmonic q ==>
    (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\ (deg_ (MAP f (p % q)) < deg_ q_)``,
  ntac 7 strip_tac >>
  qabbrev_tac `s = p / q` >>
  qabbrev_tac `t = p % q` >>
  `poly s /\ poly t` by rw[poly_div_poly, poly_mod_poly, Abbr`s`, Abbr`t`] >>
  `(MAP f s = p_ /_ q_) /\ (MAP f t = p_ %_ q_)` by rw[ring_homo_poly_div_mod, Abbr`s`, Abbr`t`] >>
  `unit_ (lead_ q_)` by metis_tac[ring_homo_poly_lead, ring_homo_unit] >>
  `deg_ q_ = deg q` by rw[ring_homo_poly_deg] >>
  `0 < deg_ q_` by decide_tac >>
  `poly_ p_ /\ poly_ q_` by metis_tac[ring_homo_poly] >>
  metis_tac[poly_division]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ ulead q ==> (MAP f (p / q) = p_ /_ q_) *)
(* Proof: by ring_homo_poly_div_mod *)
val ring_homo_poly_div = store_thm(
  "ring_homo_poly_div",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ ulead q ==> (MAP f (p / q) = p_ /_ q_)``,
  rw_tac std_ss[ring_homo_poly_div_mod]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p q. poly p /\ ulead q ==> (MAP f (p / q) = p_ %_ q_) *)
(* Proof: by ring_homo_poly_div_mod *)
val ring_homo_poly_mod = store_thm(
  "ring_homo_poly_mod",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p q. poly p /\ ulead q ==> (MAP f (p % q) = p_ %_ q_)``,
  rw_tac std_ss[ring_homo_poly_div_mod]);

(* ------------------------------------------------------------------------- *)
(* Homomorphism between Polynomial Modulo Rings                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==>
            !p x. x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier *)
(* Proof:
   By poly_mod_ring_element, this is to show:
       poly x /\ if deg p = 0 then x = [] else deg x < deg p
   ==> poly_ (MAP f x) /\ if deg_ p_ = 0 then x = [] else deg_ (MAP f x) < deg_ p_
   Note poly x ==> poly_ (MAP f x)   by ring_homo_poly, INJ f R R_
    and deg_ (MAP f x) = deg x       by ring_homo_poly_deg
    and deg_ p_ = deg p              by ring_homo_poly_deg
   Thus both assertions are true.
*)
val ring_homo_poly_mod_ring_element = store_thm(
  "ring_homo_poly_mod_ring_element",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==>
   !p x. x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier``,
  rpt strip_tac >>
  fs[poly_mod_ring_element] >>
  `deg_ (MAP f x) = deg x` by rw[ring_homo_poly_deg] >>
  `deg_ p_ = deg p` by rw[ring_homo_poly_deg] >>
  metis_tac[ring_homo_poly]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
            GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum *)
(* Proof:
   Note ulead_ p_         by ring_homo_poly, ring_homo_poly_lead, ring_homo_unit
    and deg_ p_ = deg p   by ring_homo_poly_deg
   If deg p = 0,
   By GroupHomo_def, poly_mod_ring_property, this is to show:
   (1) poly x ==> poly_ (MAP f x), true            by ring_homo_poly, INJ f R R_
   (2) MAP f |0| = |0|_, true                      by ring_homo_poly_zero
   (3) MAP f ((|0| + |0|) % p) = (PolyModRing r_ p_).sum.op (MAP f |0|) (MAP f |0|)
       Note Ring (PolyModRing r_ p_)               by poly_mod_ring_ring
        and (PolyModRing r_ p_).sum.id = |0|_      by poly_mod_ring_ids
            MAP f ((|0| + |0|) % p)
          = MAP f |0|                              by poly_mod_by_const
          = |0|_                                   by ring_homo_poly_zero
          = |0|_ +_ |0|_                           by ring_add_zero_zero
          = (PolyModRing r_ p_).sum.op |0|_ |0|_   by poly_mod_ring_property

   If deg p <> 0, then pmonic p.
   By GroupHomo_def, poly_mod_ring_property, this is to show:
   (1) poly x ==> poly_ (MAP f x), true                   by ring_homo_poly, INJ f R R_
   (2) deg x < deg p ==> deg_ (MAP f x) < deg_ p_, true   by ring_homo_poly_deg
   (3) MAP f ((x + y) % p) = (PolyModRing r_ p_).sum.op (MAP f x) (MAP f y)
       Note Ring (PolyModRing r p)              by poly_mod_ring_ring, Ring r
       also x IN (PolyModRing r p).carrier      by poly_mod_ring_element
            y IN (PolyModRing r p).carrier      by poly_mod_ring_element
       Let x_ = (MAP f x), y_ = (MAP f y).
       Note x_ IN (PolyModRing r_ p_).carrier   by ring_homo_poly_mod_ring_element, INJ f R R_
        and y_ IN (PolyModRing r_ p_).carrier   by ring_homo_poly_mod_ring_element, INJ f R R_

            MAP f ((x + y) % p)
          = (MAP f (x + y)) %_ p_               by ring_homo_poly_mod, poly_add_poly, INJ f R R_
          = (x_ +_ y_) %_ p_                    by ring_homo_poly_add, INJ f R R_
          = (PolyModRing r_ p_).sum.op x_ y_    by poly_mod_ring_property
*)
val ring_homo_poly_mod_ring_sum_homo = store_thm(
  "ring_homo_poly_mod_ring_sum_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
      GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum``,
  rpt strip_tac >>
  `ulead_ p_` by metis_tac[ring_homo_poly, ring_homo_poly_lead, ring_homo_unit] >>
  `deg_ p_ = deg p` by rw[ring_homo_poly_deg] >>
  Cases_on `deg p = 0` >| [
    rw_tac std_ss[GroupHomo_def, poly_mod_ring_property] >-
    rw[ring_homo_poly] >-
    rw[ring_homo_poly_zero] >>
    `Ring (PolyModRing r_ p_)` by metis_tac[poly_mod_ring_ring] >>
    `(PolyModRing r_ p_).sum.id = |0|_` by metis_tac[poly_mod_ring_ids] >>
    `(PolyModRing r_ p_).sum.op |0|_ |0|_ = |0|_` by metis_tac[ring_add_zero_zero] >>
    `( |0| + |0|) % p = |0|` by rw[poly_mod_by_const] >>
    metis_tac[ring_homo_poly_zero],
    rw_tac std_ss[GroupHomo_def, poly_mod_ring_property] >-
    metis_tac[ring_homo_poly] >-
    metis_tac[ring_homo_poly_deg] >>
    `Ring (PolyModRing r p)` by rw[poly_mod_ring_ring] >>
    `x IN (PolyModRing r p).carrier /\ y IN (PolyModRing r p).carrier` by rw[poly_mod_ring_element] >>
    qabbrev_tac `x_ = (MAP f x)` >>
    qabbrev_tac `y_ = (MAP f y)` >>
    `x_ IN (PolyModRing r_ p_).carrier /\ y_ IN (PolyModRing r_ p_).carrier` by metis_tac[ring_homo_poly_mod_ring_element] >>
    `MAP f ((x + y) % p) = (MAP f (x + y)) %_ p_` by rw[ring_homo_poly_mod] >>
    `_ = (x_ +_ y_) %_ p_` by metis_tac[ring_homo_poly_add] >>
    rw[poly_mod_ring_property, Abbr`x_`, Abbr`y_`]
  ]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
            MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod *)
(* Proof:
   Note ulead_ p_         by ring_homo_poly, ring_homo_poly_lead, ring_homo_unit
    and deg_ p_ = deg p   by ring_homo_poly_deg
   If deg p = 0,
   By MonoidHomo_def, poly_mod_ring_property, this is to show:
   (1) poly x ==> poly_ (MAP f x), true            by ring_homo_poly, INJ f R R_
   (2) MAP f |0| = |0|_, true                      by ring_homo_poly_zero
   (3) MAP f ((|0| * |0|) % p) = (PolyModRing r_ p_).prod.op (MAP f |0|) (MAP f |0|)
       Note Ring (PolyModRing r_ p_)               by poly_mod_ring_ring
        and (PolyModRing r_ p_).prod.id = |0|_     by poly_mod_ring_ids, deg_ p_ = 0
            MAP f ((|0| * |0|) % p)
          = MAP f |0|                              by poly_mod_by_const
          = |0|_                                   by ring_homo_poly_zero
          = |0|_ *_ |0|_                           by ring_mult_one_one
          = (PolyModRing r_ p_).prod.op |0|_ |0|_  by poly_mod_ring_property
   (4) MAP f |0| = |0|_, true                      by ring_homo_poly_zero

   If deg p <> 0, then pmonic p.
   By MonoidHomo_def, poly_mod_ring_property, this is to show:
   (1) poly x ==> poly_ (MAP f x), true                   by ring_homo_poly, INJ f R R_
   (2) deg x < deg p ==> deg_ (MAP f x) < deg_ p_, true   by ring_homo_poly_deg
   (3) MAP f ((x * y) % p) = (PolyModRing r_ p_).prod.op (MAP f x) (MAP f y)
       Note Ring (PolyModRing r p)              by poly_mod_ring_ring, Ring r
       also x IN (PolyModRing r p).carrier      by poly_mod_ring_element
            y IN (PolyModRing r p).carrier      by poly_mod_ring_element
       Let x_ = (MAP f x), y_ = (MAP f y).
       Note x_ IN (PolyModRing r_ p_).carrier   by ring_homo_poly_mod_ring_element, INJ f R R_
        and y_ IN (PolyModRing r_ p_).carrier   by ring_homo_poly_mod_ring_element, INJ f R R_

            MAP f ((x * y) % p)
          = (MAP f (x * y)) %_ p_               by ring_homo_poly_mod, poly_mult_poly, INJ f R R_
          = (x_ *_ y_) %_ p_                    by ring_homo_poly_mult, INJ f R R_
          = (PolyModRing r_ p_).prod.op x_ y_   by poly_mod_ring_property
   (4) MAP f |1| = |1|_, true                   by ring_homo_poly_one, INJ f R R_
*)
val ring_homo_poly_mod_ring_prod_homo = store_thm(
  "ring_homo_poly_mod_ring_prod_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
    MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod``,
  rpt strip_tac >>
  `ulead_ p_` by metis_tac[ring_homo_poly, ring_homo_poly_lead, ring_homo_unit] >>
  `deg_ p_ = deg p` by rw[ring_homo_poly_deg] >>
  Cases_on `deg p = 0` >| [
    rw_tac std_ss[MonoidHomo_def, poly_mod_ring_property] >-
    rw[ring_homo_poly] >-
    rw[ring_homo_poly_zero] >-
   (`Ring (PolyModRing r_ p_)` by metis_tac[poly_mod_ring_ring] >>
    `(PolyModRing r_ p_).prod.id = |0|_` by metis_tac[poly_mod_ring_ids] >>
    `(PolyModRing r_ p_).prod.op |0|_ |0|_ = |0|_` by metis_tac[ring_mult_one_one] >>
    `( |0| * |0|) % p = |0|` by rw[poly_mod_by_const] >>
    metis_tac[ring_homo_poly_zero]) >>
    rw[ring_homo_poly_zero],
    rw_tac std_ss[MonoidHomo_def, poly_mod_ring_property] >-
    metis_tac[ring_homo_poly] >-
    metis_tac[ring_homo_poly_deg] >-
   (`Ring (PolyModRing r p)` by rw[poly_mod_ring_ring] >>
    `x IN (PolyModRing r p).carrier /\ y IN (PolyModRing r p).carrier` by rw[poly_mod_ring_element] >>
    qabbrev_tac `x_ = (MAP f x)` >>
    qabbrev_tac `y_ = (MAP f y)` >>
    `x_ IN (PolyModRing r_ p_).carrier /\ y_ IN (PolyModRing r_ p_).carrier` by metis_tac[ring_homo_poly_mod_ring_element] >>
    `MAP f ((x * y) % p) = (MAP f (x * y)) %_ p_` by rw[ring_homo_poly_mod] >>
    `_ = (x_ *_ y_) %_ p_` by metis_tac[ring_homo_poly_mult] >>
    rw[poly_mod_ring_property, Abbr`x_`, Abbr`y_`]) >>
    rw[ring_homo_poly_one]
  ]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
            (((PolyModRing r p)) ~r~ ((PolyModRing r_ p_))) (MAP f) *)
(* Proof:
   This is to show:
   (1) Ring (PolyModRing r p), true          by poly_mod_ring_ring, ulead p
   (2) Ring (PolyModRing r_ p_)
       Note poly_ p_ /\ (unit_ (lead_ p_))   by ring_homo_ulead
       Thus true                             by poly_mod_ring_ring, ulead_ p_
   (3) RingHomo f r r_ ==> RingHomo (MAP f) (PolyModRing r p) (PolyModRing r_ p_)
       By RingHomo_def, this is to show:
       (1) x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier
           This is true                  by ring_homo_poly_mod_ring_element, INJ f R R_
       (2) GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum
           This is true                  by ring_homo_poly_mod_ring_sum_homo, INJ f R R_
       (3) MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod
           This is true                  by ring_homo_poly_mod_ring_prod_homo, INJ f R R_
*)
val ring_homo_poly_mod_ring_homo = store_thm(
  "ring_homo_poly_mod_ring_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !p. ulead p ==>
            (((PolyModRing r p)) ~r~ ((PolyModRing r_ p_))) (MAP f)``,
  rpt strip_tac >-
  rw[poly_mod_ring_ring] >-
 (`poly_ p_ /\ (unit_ (lead_ p_))` by metis_tac[ring_homo_ulead] >>
  rw[poly_mod_ring_ring]) >>
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[ring_homo_poly_mod_ring_element] >-
  rw[ring_homo_poly_mod_ring_sum_homo] >>
  rw[ring_homo_poly_mod_ring_prod_homo]);

(* Theorem: pmonic z /\ pmonic p /\ z pdivides p ==>
            RingHomo (\x. x % z) (PolyModRing r p) (PolyModRing r z) *)
(* Proof:
   Note !x. poly x ==> deg (x % z) < deg z    by poly_deg_mod_less
   Expanding by RingHomo_def, GroupHomo_def, MonoidHomo_def, poly_mod_ring_property,
   this is to show:
   (1) (x + x') % p % z = (x % z + x' % z) % z
         (x + x') % p % z
       = (x + x') % z               by poly_divides_mod_mod, z pdivides p
       = (x % z + x' % z) % z       by poly_mod_add
   (2) (x * x') % p % z = (x % z * x' % z) % z
         (x * x') % p % z
       = (x * x') % z               by poly_divides_mod_mod, z pdivides p
       = (x % z * x' % z) % z       by poly_mod_mult
*)
val poly_divides_poly_mod_ring_homo = store_thm(
  "poly_divides_poly_mod_ring_homo",
  ``!r:'a ring z p. Ring r /\ pmonic z /\ pmonic p /\ z pdivides p ==>
   RingHomo (\x. x % z) (PolyModRing r p) (PolyModRing r z)``,
  rpt strip_tac >>
  `deg z <> 0 /\ deg p <> 0` by decide_tac >>
  `!x. poly x ==> deg (x % z) < deg z` by rw[poly_deg_mod_less] >>
  rw[RingHomo_def, GroupHomo_def, MonoidHomo_def, poly_mod_ring_property] >-
  rw[poly_divides_mod_mod, GSYM poly_mod_add] >>
  rw[poly_divides_mod_mod, GSYM poly_mod_mult]);

(* ------------------------------------------------------------------------- *)
(* Ring Isomorphism                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==> !p. zerop p ==> zerop_ p_ *)
(* Proof: by RingIso_def, ring_homo_zero_poly *)
val ring_iso_zero_poly = store_thm(
  "ring_iso_zero_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. zerop p ==> zerop_ p_``,
  metis_tac[RingIso_def, ring_homo_zero_poly]);

(* Theorem: (r =r= r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_eq_zero_poly *)
val ring_iso_eq_zero_poly = store_thm(
  "ring_iso_eq_zero_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_eq_zero_poly]);

(* Theorem: RingIso f r r_ ==> !p. weak p ==> weak_ p_ *)
(* Proof: by RingIso_def, ring_homo_weak *)
val ring_iso_weak = store_thm(
  "ring_iso_weak",
  ``!(r:'a ring) (r_:'b ring) f. RingIso f r r_ ==> !p. weak p ==> weak_ p_``,
  metis_tac[RingIso_def, ring_homo_weak]);

(* Theorem: (r =r= r_) f ==> !p. poly p ==> poly_ p_ *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly *)
val ring_iso_poly = store_thm(
  "ring_iso_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. poly p ==> poly_ p_``,
  metis_tac[RingIso_def, BIJ_DEF, ring_homo_poly]);

(* Theorem: (p = |0|) <=> (p_ = |0|_) *)
(* Proof: by ring_homo_eq_poly_zero *)
val ring_iso_eq_poly_zero = save_thm("ring_iso_eq_poly_zero", ring_homo_eq_poly_zero);
(* val ring_iso_eq_poly_zero = |- !r r_ f p. (p = |0|) <=> (p_ = |0|_): thm *)

(* Theorem: MAP f |0| = |0|_ *)
(* Proof: by ring_homo_poly_zero *)
val ring_iso_poly_zero = save_thm("ring_iso_poly_zero", ring_homo_poly_zero);
(* val ring_iso_poly_zero = |- !r s f.MAP f |0| = |0|_: thm *)

(* Theorem: (r =r= r_) f ==> (MAP f |1| = |1|_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_one *)
val ring_iso_poly_one = store_thm(
  "ring_iso_poly_one",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (MAP f |1| = |1|_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_one]);

(* Theorem: (r =r= r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_chop *)
val ring_iso_poly_chop = store_thm(
  "ring_iso_poly_chop",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_chop]);

(* Theorem: (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_) *)
(* Proof: by RingIso_def, ring_homo_weak_add *)
val ring_iso_weak_add = store_thm(
  "ring_iso_weak_add",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)``,
  rw[RingIso_def, ring_homo_weak_add]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_add *)
val ring_iso_poly_add = store_thm(
  "ring_iso_poly_add",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_add]);

(* Theorem: (r =r= r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_) *)
(* Proof: by RingIso_def, ring_homo_weak_neg *)
val ring_iso_weak_neg = store_thm(
  "ring_iso_weak_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)``,
  rw[RingIso_def, ring_homo_weak_neg]);

(* Theorem: (r =r= r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_neg *)
val ring_iso_poly_neg = store_thm(
  "ring_iso_poly_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_neg]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_sub *)
val ring_iso_poly_sub = store_thm(
  "ring_iso_poly_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_sub]);

(* Theorem: deg_ p_ = deg p *)
(* Proof: by ring_homo_poly_deg *)
val ring_iso_poly_deg = save_thm("ring_iso_poly_deg", ring_homo_poly_deg);
(* val ring_iso_poly_deg = |- !r r_ f p. deg_ p_ = deg p: thm *)

(* Theorem: (r =r= r_) f ==> !p. lead_ p_ = f (lead p) *)
(* Proof: by RingIso_def, ring_homo_poly_lead *)
val ring_iso_poly_lead = store_thm(
  "ring_iso_poly_lead",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. lead_ p_ = f (lead p)``,
  rw[RingIso_def, ring_homo_poly_lead]);

(* Theorem: (r =r= r_) f ==> !p k. p_ '_ k = f (p ' k) *)
(* Proof: by RingIso_def, ring_homo_poly_coeff *)
Theorem ring_iso_poly_coeff:
  !(r:'a ring) (r_:'b ring) f.
    (r =r= r_) f ==> !(p:'a list) k. poly_coeff r_ p_ k = f (p ' k)
Proof
  rw[RingIso_def, ring_homo_poly_coeff]
QED

(* Theorem: (r =r= r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_) *)
(* Proof: by RingIso_def, ring_homo_weak_cmult *)
val ring_iso_weak_cmult = store_thm(
  "ring_iso_weak_cmult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_)``,
  rw[RingIso_def, ring_homo_weak_cmult]);

(* Theorem: (r =r= r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_) *)
(* Proof: RingIso_def, BIJ_DEF, ring_homo_poly_cmult *)
val ring_iso_poly_cmult = store_thm(
  "ring_iso_poly_cmult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_cmult]);

(* Theorem: (r =r= r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n *)
(* Proof: by RingIso_def, ring_homo_poly_shift *)
val ring_iso_poly_shift = store_thm(
  "ring_iso_poly_shift",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n``,
  rw[RingIso_def, ring_homo_poly_shift]);

(* Theorem: (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_) *)
(* Proof: by RingIso_def, ring_homo_weak_mult *)
val ring_iso_weak_mult = store_thm(
  "ring_iso_weak_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)``,
  rw[RingIso_def, ring_homo_weak_mult]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_) *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_mult *)
val ring_iso_poly_mult = store_thm(
  "ring_iso_poly_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_mult]);

(* ------------------------------------------------------------------------- *)
(* Isomorphism between Polynomial Rings                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==> INJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier *)
(* Proof:
   By INJ_DEF, poly_ring_element, this is to show:
   (1) poly x ==> poly_ (MAP f x), true            by RingIso_def, BIJ_DEF, ring_homo_poly
   (2) poly x /\ poly y /\ MAP f x = MAP f y ==> x = y
       Note INJ f R R_                             by RingIso_def, BIJ_DEF
        and !k. x ' k IN R, y ' k IN R             by poly_coeff_element
       Since !k. (MAP f x) '_ k = (MAP f y) '_ k
         ==> !k.      f (x ' k) = f (y ' k)        by ring_iso_poly_coeff
         ==> !k.          x ' k = y ' k            by INJ_DEF
       Hence                  x = y                by poly_coeff_eq_poly_eq
*)
val ring_iso_poly_inj = store_thm(
  "ring_iso_poly_inj",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> INJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier``,
  rw[INJ_DEF, poly_ring_element] >-
  metis_tac[RingIso_def, BIJ_DEF, ring_homo_poly] >>
  `INJ f R R_` by metis_tac[RingIso_def, BIJ_DEF] >>
  `!k. x ' k = y ' k` by
  (rpt strip_tac >>
  `x ' k IN R /\ y ' k IN R` by rw[] >>
  metis_tac[ring_iso_poly_coeff, INJ_DEF]) >>
  metis_tac[poly_coeff_eq_poly_eq]);

(* Theorem: (r =r= r_) f ==> SURJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier *)
(* Proof:
   By SURJ_DEF, poly_ring_element, this is to show:
   (1) poly x ==> poly_ (MAP f x), true by RingIso_def, BIJ_DEF, ring_homo_poly
   (2) poly_ x ==> ?y. poly y /\ (MAP f y = x)
       Since RingIso f r r_
         ==> RingIso (LINV f R) r_ r     by ring_iso_sym
       Let y = MAP (LINV f R) x
       Then poly y                      by ring_iso_poly

       Claim: MAP (f o LINV f R) x = MAP I x
       Proof: By MAP_EQ_f, this is to show:
              MEM e x ==> f (LINV f R e) = e
         Now poly_ x ==> EVERY (\e. e IN R_) x  by poly_every_element
          so e IN s.carrier             by EVERY_MEM
        With BIJ f R R_                 by RingIso_def
         ==> f (LINV f R e) = e         by BIJ_LINV_INV
            MAP f y
          = MAP f (MAP (LINV f R) x)
          = MAP (f o LINV f R) x        by MAP_MAP_o
          = MAP I x                     by above
          = x                           by MAP_ID
 *)
val ring_iso_poly_surj = store_thm(
  "ring_iso_poly_surj",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> SURJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier``,
  rw[SURJ_DEF, poly_ring_element] >-
  metis_tac[RingIso_def, BIJ_DEF, ring_homo_poly] >>
  `RingIso (LINV f R) r_ r` by rw[ring_iso_sym] >>
  qexists_tac `MAP (LINV f R) x` >>
  strip_tac >-
  metis_tac[ring_iso_poly] >>
  `MAP f (MAP (LINV f R) x) = MAP (f o LINV f R) x` by rw[MAP_MAP_o] >>
  `MAP (f o LINV f R) x = MAP I x` by
  (rw[MAP_EQ_f] >>
  `EVERY (\e. e IN R_) x` by rw[poly_every_element] >>
  qabbrev_tac `P = \e. e IN R_` >>
  `P e` by metis_tac[EVERY_MEM] >>
  `e IN R_` by rw[] >>
  `BIJ f R R_` by metis_tac[RingIso_def] >>
  metis_tac[BIJ_LINV_INV]) >>
  rw[MAP_ID]);

(* Theorem: (r =r= r_) f ==> BIJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier *)
(* Proof: by BIJ_DEF, ring_iso_poly_inj, ring_iso_poly_surj *)
val ring_iso_poly_bij = store_thm(
  "ring_iso_poly_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> BIJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier``,
  rw[BIJ_DEF, ring_iso_poly_inj, ring_iso_poly_surj]);

(* Theorem: (r =r= r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingIso f r r_ ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_)
       True by RingIso_def, BIJ_DEF, ring_homo_poly_ring_homo.
   (2) RingIso f r r_ ==> BIJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier
       True by ring_iso_poly_bij.
*)
val ring_iso_poly_ring_iso = store_thm(
  "ring_iso_poly_ring_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_)``,
  rpt strip_tac >>
  rw[RingIso_def] >-
  metis_tac[RingIso_def, BIJ_DEF, ring_homo_poly_ring_homo] >>
  rw[ring_iso_poly_bij]);

(* Another milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* More Ring Isomorphism Theorems                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_exp *)
val ring_iso_poly_exp = store_thm(
  "ring_iso_poly_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n``,
  rw[RingIso_def, BIJ_DEF, ring_homo_poly_exp]);

(* Theorem: (r =r= r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x)) *)
(* Proof: RingIso_def, ring_homo_poly_eval *)
val ring_iso_poly_eval = store_thm(
  "ring_iso_poly_eval",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))``,
  rw[RingIso_def, ring_homo_poly_eval]);

(* Theorem: (r =r= r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x) *)
(* Proof: by RingIso_def, ring_homo_poly_root *)
val ring_iso_poly_root = store_thm(
  "ring_iso_poly_root",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)``,
  metis_tac[RingIso_def, ring_homo_poly_root]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_ *)
(* Proof: by RingIso_def, BIJ_DEF, ring_homo_poly_divides *)
val ring_iso_poly_divides = store_thm(
  "ring_iso_poly_divides",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_``,
  metis_tac[RingIso_def, BIJ_DEF, ring_homo_poly_divides]);

(* Theorem: (r =r= r_) f ==> !c:num. (MAP f |c|) = |c|_ *)
(* Proof:
   By induction on c.
   Base: MAP f (### 0) = poly_num r_ 0
         MAP f (### 0)
       = MAP f |0|                    by poly_ring_sum_0
       = |0|_                         by ring_iso_poly_zero
       = poly_num r_ 0                by poly_ring_sum_0
   Step: MAP f |c| = |c|_ ==> MAP f (### (SUC c)) = poly_num r_ (SUC c)
         MAP f (### (SUC c))
       = MAP f (|1| + |c|)            by poly_sum_num_SUC
       = (MAP f |1|) +_ (MAP f |c|)   by ring_iso_poly_add
       = (MAP f |1|) +_ |c|_          by induction hypothesis
       = |1|_ +_ |c|_                 by ring_iso_poly_one
       = poly_num r_ (SUC c)          by poly_sum_num_SUC
*)
val ring_iso_poly_sum_num = store_thm(
  "ring_iso_poly_sum_num",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !c:num. (MAP f |c|) = |c|_``,
  rpt strip_tac >>
  Induct_on `c` >-
  metis_tac[poly_ring_sum_0, ring_iso_poly_zero] >>
  rw[poly_sum_num_SUC] >>
  metis_tac[ring_iso_poly_one, ring_iso_poly_add, poly_one_poly, poly_sum_num_poly]);

(* Theorem: (r =r= r_) f ==>
            !p. pmonic p ==> poly_ p_ /\ 0 < deg_ p_ /\ (unit_ (lead_ p_)) *)
(* Proof: by ring_homo_pmonic, RingIso_def, BIJ_DEF *)
val ring_iso_pmonic = store_thm(
  "ring_iso_pmonic",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==>
   !p. pmonic p ==> poly_ p_ /\ 0 < deg_ p_ /\ (unit_ (lead_ p_))``,
  metis_tac[ring_homo_pmonic, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !q. weak_ q ==>
            weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q) *)
(* Proof:
       weak_ q
   <=> EVERY (\x. x IN R_) q        by weak_def_alt
   <=> !x. MEM x q ==> x IN R_      by EVERY_MEM (1)

       weak (MAP (LINV f R) q)
   <=> EVERY (\x. x IN R) (MAP (LINV f R) q)    by weak_def_alt
   <=> EVERY (\x. LINV f R x IN R) q            by EVERY_MAP
   <=> !x. MEM x q ==> LINV f R x IN R          by EVERY_MEM
   Since !x. MEM x q
     ==> !x. MEM x R_                           by (1) above
     ==> LINV f R x IN R                        by ring_iso_inverse_element
   Hence true.

   Claim: !x. MEM x q ==> (f o LINV f R) x = I x
   Proof: Note MEM x q ==> x IN R_  by (1)
          (f o LINV f R) x
        = (f (LINV f R x)
        = x                         by ring_iso_inverse_element

       MAP f (MAP (LINV f R) q)
     = MAP (f o LINV f R) q
     = MAP I q                      by MAP_CONG, claim
     = q                            by MAP_ID
*)
val ring_iso_inverse_weak_poly = store_thm(
  "ring_iso_inverse_weak_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !q. weak_ q ==>
    weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)``,
  ntac 6 strip_tac >>
  fs[weak_def_alt, EVERY_MAP, EVERY_MEM, MAP_MAP_o] >>
  rpt strip_tac >-
  metis_tac[ring_iso_inverse_element] >>
  `MAP (f o LINV f R) q = MAP I q` suffices_by rw[] >>
  (irule MAP_CONG >> simp[]) >>
  metis_tac[ring_iso_inverse_element]);

(* Theorem: (r =r= r_) f ==> !q. weak_ q ==> ?p. weak p /\ (q = p_) *)
(* Proof: by ring_iso_inverse_weak_poly *)
val ring_iso_inverse_weak = store_thm(
  "ring_iso_inverse_weak",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !q. weak_ q ==> ?p. weak p /\ (q = p_)``,
  metis_tac[ring_iso_inverse_weak_poly]);

(* Theorem: (r =r= r_) f ==> !q. poly_ q ==>
            poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q) *)
(* Proof:
   Let p = MAP (LINV f R) q.
   Since poly_ q ==> weak_ q         by poly_is_weak
      so weak p /\ (p_ = q)          by ring_iso_inverse_weak_poly
   If p = |0|,
      Then poly |0| = T              by poly_zero_poly
   If p <> |0|,
      Then q <> |0|_                 by ring_iso_eq_poly_zero
        so LAST q <> #0_             by poly_def_alt
       and LAST q IN R_              by poly_lead_alt, poly_lead_element
       But f (LAST p)
         = f ((LINV f R) (LAST q))   by LAST_MAP
         = LAST q                    by BIJ_LINV_THM
        so LAST p <> #0              by ring_iso_eq_zero
     Hence poly p                    by poly_def_alt
*)
val ring_iso_inverse_polynomial = store_thm(
  "ring_iso_inverse_polynomial",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !q. poly_ q ==>
    poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)``,
  ntac 6 strip_tac >>
  `weak_ q` by rw[poly_is_weak] >>
  qabbrev_tac `p = MAP (LINV f R) q` >>
  `weak p /\ (p_ = q)` by metis_tac[ring_iso_inverse_weak_poly] >>
  Cases_on `p = |0|` >-
  rw[] >>
  `q <> |0|_` by metis_tac[ring_iso_eq_poly_zero] >>
  `LAST q <> #0_ ` by metis_tac[poly_def_alt] >>
  `LAST p IN R /\ LAST q IN R_` by metis_tac[poly_lead_alt, weak_lead_element] >>
  `f (LAST p) = LAST q` by metis_tac[LAST_MAP, BIJ_LINV_THM, poly_zero] >>
  `LAST p <> #0` by metis_tac[ring_iso_eq_zero] >>
  rw[poly_def_alt]);

(* Theorem: (r =r= r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q) *)
(* Proof: by ring_iso_inverse_polynomial *)
val ring_iso_inverse_poly = store_thm(
  "ring_iso_inverse_poly",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q)``,
  metis_tac[ring_iso_inverse_polynomial]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q)) *)
(* Proof:
   Note RingIso (MAP f) (PolyRing r) (PolyRing r_)                by ring_iso_poly_ring_iso
     so INJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier    by RingIso_def, BIJ_DEF
    Now p IN (PolyRing r).carrier /\ p_ IN (PolyRing r_).carrier  by ring_iso_poly, poly_ring_element
    and q IN (PolyRing r).carrier /\ q_ IN (PolyRing r_).carrier  by ring_iso_poly, poly_ring_element
    ==> p = q                                                     by INJ_DEF
*)
val ring_iso_poly_unique = store_thm(
  "ring_iso_poly_unique",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q))``,
  rpt strip_tac >>
  `RingIso (MAP f) (PolyRing r) (PolyRing r_)` by rw[ring_iso_poly_ring_iso] >>
  `INJ (MAP f) (PolyRing r).carrier (PolyRing r_).carrier` by metis_tac[RingIso_def, BIJ_DEF] >>
  `p IN (PolyRing r).carrier /\ p_ IN (PolyRing r_).carrier` by metis_tac[ring_iso_poly, poly_ring_element] >>
  `q IN (PolyRing r).carrier /\ q_ IN (PolyRing r_).carrier` by metis_tac[ring_iso_poly, poly_ring_element] >>
  metis_tac[INJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
            (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_) *)
(* Proof: by ring_homo_poly_div_mod, RingIso_def, BIJ_DEF. *)
val ring_iso_poly_div_mod = store_thm(
  "ring_iso_poly_div_mod",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
    (MAP f (p / q) = p_ /_ q_) /\ (MAP f (p % q) = p_ %_ q_)``,
  rw_tac std_ss[ring_homo_poly_div_mod, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
            (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\ (deg_ (MAP f (p % q)) < deg_ q_) *)
(* Proof: by ring_homo_poly_div_mod_eqn, RingIso_def, BIJ_DEF *)
val ring_iso_poly_div_mod_eqn = store_thm(
  "ring_iso_poly_div_mod_eqn",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p q. poly p /\ pmonic q ==>
    (p_ = MAP f (p / q) *_ q_ +_ MAP f (p % q)) /\ (deg_ (MAP f (p % q)) < deg_ q_)``,
  rw_tac std_ss[ring_homo_poly_div_mod_eqn, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ pmonic q ==> (MAP f (p / q) = p_ /_ q_) *)
(* Proof: by ring_iso_poly_div_mod *)
val ring_iso_poly_div = store_thm(
  "ring_iso_poly_div",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==>
   !p q. poly p /\ pmonic q ==> (MAP f (p / q) = p_ /_ q_)``,
  rw_tac std_ss[ring_iso_poly_div_mod]);

(* Theorem: (r =r= r_) f ==> !p q. poly p /\ pmonic q ==> (MAP f (p / q) = p_ %_ q_) *)
(* Proof: by ring_iso_poly_div_mod *)
val ring_iso_poly_mod = store_thm(
  "ring_iso_poly_mod",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==>
   !p q. poly p /\ pmonic q ==> (MAP f (p % q) = p_ %_ q_)``,
  rw_tac std_ss[ring_iso_poly_div_mod]);

(* ------------------------------------------------------------------------- *)
(* Isomorphism between Polynomial Modulo Rings                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==>
            !p x. x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier *)
(* Proof: by ring_homo_poly_mod_ring_element, RingIso_def, BIJ_DEF *)
val ring_iso_poly_mod_ring_element = store_thm(
  "ring_iso_poly_mod_ring_element",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==>
   !p x. x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier``,
  metis_tac[ring_homo_poly_mod_ring_element, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum *)
(* Proof: by ring_homo_poly_mod_ring_sum_homo, RingIso_def, BIJ_DEF *)
val ring_iso_poly_mod_ring_sum_homo = store_thm(
  "ring_iso_poly_mod_ring_sum_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
      GroupHomo (MAP f) (PolyModRing r p).sum (PolyModRing r_ p_).sum``,
  rw_tac std_ss[ring_homo_poly_mod_ring_sum_homo, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod *)
(* Proof: by ring_homo_poly_mod_ring_prod_homo, RingIso_def, BIJ_DEF *)
val ring_iso_poly_mod_ring_prod_homo = store_thm(
  "ring_iso_poly_mod_ring_prod_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
    MonoidHomo (MAP f) (PolyModRing r p).prod (PolyModRing r_ p_).prod``,
  rw_tac std_ss[ring_homo_poly_mod_ring_prod_homo, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            (((PolyModRing r p)) ~r~ ((PolyModRing r_ p_))) (MAP f) *)
(* Proof: by ring_homo_poly_mod_ring_homo, RingIso_def, BIJ_DEF *)
val ring_iso_poly_mod_ring_homo = store_thm(
  "ring_iso_poly_mod_ring_homo",
  ``!(r:'a field) (r_:'b field) f. (r =r= r_) f ==> !p. pmonic p ==>
       (((PolyModRing r p)) ~r~ ((PolyModRing r_ p_))) (MAP f)``,
  metis_tac[ring_homo_poly_mod_ring_homo, RingIso_def, BIJ_DEF]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            INJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier
       This is true              by ring_iso_poly_mod_ring_element
   (2) x IN (PolyModRing r p).carrier /\ y IN (PolyModRing r p).carrier /\ MAP f x = MAP f y ==> x = y
       By poly_mod_ring_element, this is to show:
          poly x /\ poly y /\ (MAP f x = MAP f y) ==> (x = y)
       This is true              by ring_iso_poly_unique
*)
val ring_iso_poly_mod_ring_inj = store_thm(
  "ring_iso_poly_mod_ring_inj",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
      INJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier``,
  rw_tac std_ss[INJ_DEF] >-
  metis_tac[ring_iso_poly_mod_ring_element] >>
  fs[poly_mod_ring_element] >>
  metis_tac[ring_iso_poly_unique]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            SURJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) x IN (PolyModRing r p).carrier ==> MAP f x IN (PolyModRing r_ p_).carrier
       This is true              by ring_iso_poly_mod_ring_element
   (2) x IN (PolyModRing r_ p_).carrier ==> ?y. y IN (PolyModRing r p).carrier /\ (MAP f y = x)
       By poly_mod_ring_element, this is to show:
          poly_ x /\ deg_ x < deg_ p_ ==> ?y. (poly y /\ deg y < deg p) /\ (MAP f y = x)
       Note ?y. poly y /\ (MAP f y = x)   by ring_iso_inverse_poly
        and deg y = deg_ p_               by ring_iso_poly_deg
       Take this y, the result is true.
*)
val ring_iso_poly_mod_ring_surj = store_thm(
  "ring_iso_poly_mod_ring_surj",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
      SURJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier``,
  rw_tac std_ss[SURJ_DEF] >-
  metis_tac[ring_iso_poly_mod_ring_element] >>
  fs[poly_mod_ring_element] >>
  `deg_ x < deg_ p_` by metis_tac[ring_iso_poly_deg, NOT_ZERO] >>
  metis_tac[ring_iso_inverse_poly, ring_iso_poly_deg]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            BIJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
       This is true        by ring_iso_poly_mod_ring_inj
   (2) SURJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
       This is true        by ring_iso_poly_mod_ring_surj
*)
val ring_iso_poly_mod_ring_bij = store_thm(
  "ring_iso_poly_mod_ring_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
      BIJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier``,
  rw_tac std_ss[BIJ_DEF, ring_iso_poly_mod_ring_inj, ring_iso_poly_mod_ring_surj]);

(* Theorem: (r =r= r_) f ==> !p. pmonic p ==>
            (((PolyModRing r p)) =r= ((PolyModRing r_ p_))) (MAP f) *)
(* Proof:
   This is to show:
   (1) Ring (PolyModRing r p), true      by poly_mod_ring_ring, pmonic p
   (2) Ring (PolyModRing r_ p_)
       Note poly_ p_ /\ 0 < deg_ p_ /\
            (unit_ (lead_ p_))           by ring_iso_pmonic
       Thus true                         by poly_mod_ring_ring
   (3) RingIso f r r_ ==> RingIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_)
       By RingIso_def, this is to show:
       (1) RingHomo (MAP f) (PolyModRing r p) (PolyModRing r_ p_)
           This is true                  by ring_iso_poly_mod_ring_homo
       (2) BIJ (MAP f) (PolyModRing r p).carrier (PolyModRing r_ p_).carrier
           This is true                  by ring_iso_poly_mod_ring_bij
*)
val ring_iso_poly_mod_ring_iso = store_thm(
  "ring_iso_poly_mod_ring_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !p. pmonic p ==>
       (((PolyModRing r p)) =r= ((PolyModRing r_ p_))) (MAP f)``,
  rpt strip_tac >-
  rw[poly_mod_ring_ring] >-
 (`poly_ p_ /\ 0 < deg_ p_ /\ (unit_ (lead_ p_))` by metis_tac[ring_iso_pmonic] >>
  rw[poly_mod_ring_ring]) >>
  rw_tac std_ss[RingIso_def] >-
  rw[ring_iso_poly_mod_ring_homo] >>
  rw[ring_iso_poly_mod_ring_bij]);

(* ------------------------------------------------------------------------- *)
(* Field Homomorphism and Isomorphism                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~~~ r_) f ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_) *)
(* Proof:
   Since FieldHomo f r r_ <=> RingHomo f r r_   by FieldHomo_def
     and FieldHomo f r r_ ==> INJ f R R_        by field_homo_map_inj
   The result follows                           by ring_homo_poly_ring_homo, field_is_ring
*)
val field_homo_poly_ring_homo = store_thm(
  "field_homo_poly_ring_homo",
  ``!(r:'a field) (r_:'b field) f. (r ~~~ r_) f ==> RingHomo (MAP f) (PolyRing r) (PolyRing r_)``,
  rw[FieldHomo_def, ring_homo_poly_ring_homo, field_homo_map_inj]);

(* Theorem: (r === r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_) *)
(* Proof:
   Since FieldIso f r r_ <=> FieldHomo f r r_ /\ BIJ f R R_   by FieldIso_def
     and RingIso f r r_ <=> RingHomo f r r_ /\ BIJ f R R_     by RingIso_def
     and FieldHomo f r r_ <=> RingHomo f r r_                 by FieldHomo_def
   The result follows                                         by ring_iso_poly_ring_iso
*)
val field_iso_poly_ring_iso = store_thm(
  "field_iso_poly_ring_iso",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> RingIso (MAP f) (PolyRing r) (PolyRing r_)``,
  rw[FieldIso_def, RingIso_def, FieldHomo_def, ring_iso_poly_ring_iso]);

(* Theorem: (r === r_) f ==> !p. ipoly p ==> RingIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_) *)
(* Proof:
   This is to show:
      RingIso f r r_ ==> FieldIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_)
   Note pmonic p                     by poly_irreducible_pmonic, ipoly p
    and RingIso f r r_               by field_iso_eq_ring_iso
    ==> RingIso (MAP f)
                (PolyModRing r p)
                (PolyModRing r_ p_)  by ring_iso_poly_mod_ring_iso
*)
val field_iso_poly_mod_ring_iso = store_thm(
  "field_iso_poly_mod_ring_iso",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. ipoly p ==>
    RingIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_)``,
  rpt strip_tac >>
  `pmonic p` by rw[poly_irreducible_pmonic] >>
  metis_tac[ring_iso_poly_mod_ring_iso, field_iso_is_ring_iso]);

(* This is a  milestone theorem! *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Correspondence                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r === r_) f ==> !p. zerop p ==> zerop_ p_ *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> zerop p ==> zerop_ p_                   by ring_iso_zero_poly
*)
val field_iso_zero_poly = store_thm(
  "field_iso_zero_poly",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. zerop p ==> zerop_ p_``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_zero_poly, field_is_ring]);

(* Theorem: (r === r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p ==> (zerop p <=> zerop_ p_)      by ring_iso_eq_zero_poly
*)
val field_iso_eq_zero_poly = store_thm(
  "field_iso_eq_zero_poly",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. weak p ==> (zerop p <=> zerop_ p_)``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_eq_zero_poly, field_is_ring]);

(* Theorem: (r === r_) f ==> !p. weak p ==> weak_ p_ *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> RingIso f r r_                          by field_iso_eq_ring_iso
   ==> weak p ==> weak_ p_                     by ring_iso_weak
*)
val field_iso_weak = store_thm(
  "field_iso_weak",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. weak p ==> weak_ p_``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_weak]);

(* Theorem: (r === r_) f ==> !p. poly p ==> poly_ p_ *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p ==> poly_ p_                     by ring_iso_poly
*)
val field_iso_poly = store_thm(
  "field_iso_poly",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> poly_ p_``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_poly, field_is_ring]);

(* Theorem: (p = |0|) <=> (p_ = |0|_) *)
(* Proof: by ring_iso_eq_poly_zero *)
val field_iso_eq_poly_zero = store_thm(
  "field_iso_eq_poly_zero",
  ``!(r:'a field) (r_:'b field) (f:'a -> 'b). !p. (p = |0|) <=> (p_ = |0|_)``,
  rw[ring_iso_eq_poly_zero]);

(* Theorem: MAP f |0| = |0|_ *)
(* Proof: by ring_iso_poly_zero *)
val field_iso_poly_zero = store_thm(
  "field_iso_poly_zero",
  ``!(r:'a field) (r_:'b field) f. MAP f |0| = |0|_``,
  rw[ring_iso_poly_zero]);

(* Theorem: (r === r_) f ==> (MAP f |1| = |1|_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> MAP f |1| = |1|_                        by ring_iso_poly_one
*)
val field_iso_poly_one = store_thm(
  "field_iso_poly_one",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (MAP f |1| = |1|_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_one]);

(* Theorem: (r === r_) f ==> !c:num. (MAP f |c|) = |c|_ *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_poly_sum_num *)
val field_iso_poly_sum_num = store_thm(
  "field_iso_poly_sum_num",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !c:num. (MAP f |c|) = |c|_``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_sum_num]);

(* Theorem: (r === r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p ==> (MAP f (chop p) = chop_ p_   by ring_iso_poly_chop
*)
val field_iso_poly_chop = store_thm(
  "field_iso_poly_chop",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. weak p ==> (MAP f (chop p) = chop_ p_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_chop]);

(* Theorem: (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p /\ weak q ==>
       (MAP f (p || q) = p_ ||_ q_)            by ring_iso_weak_add
*)
val field_iso_weak_add = store_thm(
  "field_iso_weak_add",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p || q) = p_ ||_ q_)``,
  rw[field_iso_eq_ring_iso, ring_iso_weak_add]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p /\ poly q ==>
       (MAP f (p + q) = p_ +_ q_)              by ring_iso_poly_add
*)
val field_iso_poly_add = store_thm(
  "field_iso_poly_add",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_add]);

(* Theorem: (r === r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p ==> (MAP f (neg p) = neg_ p_)    by ring_iso_weak_neg
*)
val field_iso_weak_neg = store_thm(
  "field_iso_weak_neg",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. weak p ==> (MAP f (neg p) = neg_ p_)``,
  rw[field_iso_eq_ring_iso, ring_iso_weak_neg]);

(* Theorem: (r === r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p ==> (MAP f (-p) = $-_ p_)        by ring_iso_poly_neg
*)
val field_iso_poly_neg = store_thm(
  "field_iso_poly_neg",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_neg]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p /\ poly q ==>
       (MAP f (p - q) = p_ -_ q_)              by ring_iso_poly_sub
*)
val field_iso_poly_sub = store_thm(
  "field_iso_poly_sub",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_sub]);

(* Theorem: (r === r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p /\ c IN R ==>
       (MAP f (c o p) = (f c) o_ p_)           by ring_iso_weak_cmult
*)
val field_iso_weak_cmult = store_thm(
  "field_iso_weak_cmult",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p c. weak p /\ c IN R ==> (MAP f (c o p) = (f c) o_ p_)``,
  rw[field_iso_eq_ring_iso, ring_iso_weak_cmult]);

(* Theorem: (r === r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p /\ c IN R ==>
       (MAP f (c * p) = (f c) *_ p_)           by ring_iso_poly_cmult
*)
val field_iso_poly_cmult = store_thm(
  "field_iso_poly_cmult",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = (f c) *_ p_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_cmult]);

(* Theorem: (r === r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> MAP f (p >> n) = p_ >>_ n               by ring_iso_poly_shift
*)
val field_iso_poly_shift = store_thm(
  "field_iso_poly_shift",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_shift]);

(* Theorem: (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> weak p /\ weak q ==>
       (MAP f (p o q) = p_ o_ q_)              by ring_iso_weak_mult
*)
val field_iso_weak_mult = store_thm(
  "field_iso_weak_mult",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. weak p /\ weak q ==> (MAP f (p o q) = p_ o_ q_)``,
  rw[field_iso_eq_ring_iso, ring_iso_weak_mult]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> poly p /\ poly q ==>
       (MAP f (p * q) = p_ *_ q_)              by ring_iso_poly_mult
*)
val field_iso_poly_mult = store_thm(
  "field_iso_poly_mult",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_mult]);

(* Theorem: (r === r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> MAP f (p ** n) = p_ **_ n               by ring_iso_poly_exp
*)
val field_iso_poly_exp = store_thm(
  "field_iso_poly_exp",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_exp]);

(* Theorem: deg_ p_ = deg p *)
(* Proof: by ring_iso_poly_deg *)
val field_iso_poly_deg = store_thm(
  "field_iso_poly_deg",
  ``!(r:'a field) (r_:'b field) (f:'a -> 'b). !p. deg_ p_ = deg p``,
  rw[ring_iso_poly_deg]);

(* Theorem: (r === r_) f ==> !p. lead_ p_ = f (lead p) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> lead_ p_ = f (lead p)                   by ring_iso_poly_lead
*)
val field_iso_poly_lead = store_thm(
  "field_iso_poly_lead",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. lead_ p_ = f (lead p)``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_lead]);

(* Theorem: (r === r_) f ==> !p k. p_ '_ k = f (p ' k) *)
(* Proof:
       (r === r_) f
     = Field r /\ Field r_ /\ FieldIso f r r_  by notation
   ==> Ring r /\ Ring r_ /\ RingIso f r r_     by field_iso_eq_ring_iso, field_is_ring
   ==> p_ '_ k = f (p ' k)                     by ring_iso_poly_coeff
*)
Theorem field_iso_poly_coeff:
  !(r:'a field) (r_:'b field) f.
    (r === r_) f ==> !(p:'a list) k. poly_coeff r_ p_ k = f (p ' k)
Proof
  rw[field_iso_eq_ring_iso, ring_iso_poly_coeff]
QED

(* Theorem: (r === r_) f ==> !y. y IN R_ ==> !q. weak_ q ==>
            weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_inverse_weak_poly *)
val field_iso_inverse_weak_poly = store_thm(
  "field_iso_inverse_weak_poly",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !q. weak_ q ==>
    weak (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)``,
  metis_tac[field_iso_is_ring_iso, ring_iso_inverse_weak_poly]);

(* Theorem: (r === r_) f ==> !y. y IN R_ ==> !q. weak_ q ==> ?p. weak p /\ (q = p_) *)
(* Proof: by field_iso_inverse_weak_poly *)
val field_iso_inverse_weak = store_thm(
  "field_iso_inverse_weak",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !q. weak_ q ==> ?p. weak p /\ (q = p_)``,
  metis_tac[field_iso_inverse_weak_poly]);

(* Theorem: (r === r_) f ==> !q. poly_ q ==>
            poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_inverse_polynomial *)
val field_iso_inverse_polynomial = store_thm(
  "field_iso_inverse_polynomial",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !q. poly_ q ==>
    poly (MAP (LINV f R) q) /\ (MAP f (MAP (LINV f R) q) = q)``,
  metis_tac[field_iso_is_ring_iso, ring_iso_inverse_polynomial]);

(* Theorem: (r === r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q) *)
(* Proof: by field_iso_inverse_polynomial *)
val field_iso_inverse_poly = store_thm(
  "field_iso_inverse_poly",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !q. poly_ q ==> ?p. poly p /\ (p_ = q)``,
  metis_tac[field_iso_inverse_polynomial]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q)) *)
(* Proof: by field_iso_is_ring_iso, ring_iso_poly_unique *)
val field_iso_poly_unique = store_thm(
  "field_iso_poly_unique",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q ==> ((p_ = q_) <=> (p = q))``,
  metis_tac[field_iso_is_ring_iso, ring_iso_poly_unique]);

(* Theorem: (r === r_) f ==> (MAP f X = X_) *)
(* Proof:
     MAP f X
   = MAP f (|1| >> 1)    by notation
   = (MAP f |1|) >>_ 1   by field_iso_poly_shift
   = |1|_ >>_ 1          by field_iso_poly_one
*)
val field_iso_poly_X = store_thm(
  "field_iso_poly_X",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> (MAP f X = X_)``,
  metis_tac[field_iso_poly_shift, field_iso_poly_one]);

(* Theorem: (r === r_) f ==> !n. MAP f (unity n) = unity_ n *)
(* Proof:
     MAP f (unity n)
   = MAP f (X ** n - |1|)              by notation
   = (MAP f (X ** n)) -_ (MAP f |1|)   by field_iso_poly_sub
   = (MAP f (X ** n)) -_ |1|_          by field_iso_poly_one
   = (MAP f X) **_ n -_ |1|_           by field_iso_poly_exp
   = X_ **_ n -_ |1|_                  by field_iso_poly_X
   = unity_ n                          by notation
*)
val field_iso_poly_unity = store_thm(
  "field_iso_poly_unity",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !n. MAP f (unity n) = unity_ n``,
  rpt strip_tac >>
  `Ring r /\ poly X /\ poly |1| /\ poly (X ** n)` by rw[] >>
  metis_tac[field_iso_poly_sub, field_iso_poly_one, field_iso_poly_X, field_iso_poly_exp]);

(* Theorem: (r === r_) f ==> !n. MAP f (master n) = master_ n *)
(* Proof:
     MAP f (master n)
   = MAP f (X ** n - X)              by notation
   = (MAP f (X ** n)) -_ (MAP f X)   by field_iso_poly_sub
   = (MAP f (X ** n)) -_ X_          by field_iso_poly_X
   = (MAP f X) **_ n -_ X_           by field_iso_poly_exp
   = X_ **_ n -_ X_                  by field_iso_poly_X
   = master_ n                       by notation
*)
val field_iso_poly_master = store_thm(
  "field_iso_poly_master",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !n. MAP f (master n) = master_ n``,
  rpt strip_tac >>
  `Ring r /\ poly X /\ poly (X ** n)` by rw[] >>
  metis_tac[field_iso_poly_sub, field_iso_poly_X, field_iso_poly_exp]);

(* Theorem: (r === r_) f ==> !s. FINITE s /\ pset s ==> (MAP f (PPROD s) = poly_prod_image r_ (MAP f) s) *)
(* Proof:
   By finite induction on s.
   Base: MAP f (PPROD {}) = poly_prod_image r_ (MAP f) {}
         MAP f (PPROD {})
       = MAP f |1|                       by poly_prod_set_empty
       = |1|_                            by field_iso_poly_one
       = poly_prod_set r_ {}             by poly_prod_set_empty
       = poly_prod_image r_ (MAP f) {}   by IMAGE_EMPTY
   Step: pset s ==> (MAP f (PPROD s) = poly_prod_image r_ (MAP f) s) ==>
         e NOTIN s /\ pset (e INSERT s) ==> MAP f (PPROD (e INSERT s)) = poly_prod_image r_ (MAP f) (e INSERT s)
      Note pset (e INSERT s)
       ==> poly e /\ pset s              by IN_INSERT
        so poly (PPROD s)                by poly_prod_set_poly
      Let t = IMAGE (MAP f) s.
      Then FINITE t                      by IMAGE_FINITE
       and poly_set r_ t                 by field_iso_poly, IN_IMAGE
      also MAP f e NOTIN t               by field_iso_poly_unique, IN_IMAGE
       Now poly_ (MAP f e)               by field_iso_poly
       and poly_ t                       by field_iso_poly

         MAP f (PPROD (e INSERT s))
       = MAP f (e * PPROD s)                                   by poly_prod_set_insert, e NOTIN s
       = (MAP f e) *_ (MAP f (PPROD s))                        by field_iso_poly_mult
       = (MAP f e) *_ poly_prod_image r_ (MAP f) s             by induction hypothesis
       = poly_prod_set r_ ((MAP f e) INSERT t)                 by poly_prod_set_insert, MAP f e NOTIN t
       = poly_prod_set r_ ((MAP f e) INSERT (IMAGE (MAP f) s)) by t = IMAGE (MAP f) s
       = poly_prod_image r_ (MAP f) (e INSERT s)               by IMAGE_INSERT
*)
val field_iso_poly_prod_set = store_thm(
  "field_iso_poly_prod_set",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==>
   !s. FINITE s /\ pset s ==> (MAP f (PPROD s) = poly_prod_image r_ (MAP f) s)``,
  ntac 4 strip_tac >>
  `!s. FINITE s ==> pset s ==> (MAP f (PPROD s) = poly_prod_image r_ (MAP f) s)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[poly_prod_set_empty, field_iso_poly_one] >>
  fs[] >>
  `poly e /\ poly (PPROD s)` by rw[poly_prod_set_poly] >>
  qabbrev_tac `t = IMAGE (MAP f) s` >>
  `FINITE t` by rw[Abbr`t`] >>
  `poly_set r_ t` by prove_tac[field_iso_poly, IN_IMAGE] >>
  `MAP f e NOTIN t` by prove_tac[field_iso_poly_unique, IN_IMAGE] >>
  `MAP f (PPROD (e INSERT s)) = MAP f (e * PPROD s)` by rw[poly_prod_set_insert] >>
  `_ = (MAP f e) *_ poly_prod_image r_ (MAP f) s` by metis_tac[field_iso_poly_mult] >>
  metis_tac[poly_prod_set_insert, field_iso_poly, field_is_ring]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_ *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_poly_divides *)
val field_iso_poly_divides = store_thm(
  "field_iso_poly_divides",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q /\ p pdivides q ==> p_ pdivides_ q_``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_poly_divides, field_is_ring]);

(* Theorem: (r === r_) f ==> !p q. poly p /\ poly q ==> (p pdivides q <=> p_ pdivides_ q_) *)
(* Proof:
   If part: p pdivides q ==> p_ pdivides_ q_
      True                                 by field_iso_poly_divides

   Only-if part: p_ pdivides_ q_ ==> p pdivides q
      Given p_ pdivides_ q_
        ==> ?s. poly_ s /\ (q_ = s *_ p_)  by poly_divides_def
        ==> ?t. poly t /\ (s = MAP f t)    by field_iso_inverse_poly
       Thus q_ = (MAP f t) *_ p_           by above
         or  q = MAP (t * p)               by field_iso_poly_mult
      Since poly (t * p)                   by poly_mult_poly
         so  q = t * p                     by field_iso_poly_unique
         so p pdivides q                   by poly_divides_def
*)
val field_iso_poly_divides_iff = store_thm(
  "field_iso_poly_divides_iff",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p q. poly p /\ poly q ==>
    (p pdivides q <=> p_ pdivides_ q_)``,
  rw[EQ_IMP_THM] >-
  metis_tac[field_iso_poly_divides] >>
  fs[poly_divides_def] >>
  `?t. poly t /\ (s = MAP f t)` by metis_tac[field_iso_inverse_poly] >>
  qexists_tac `t` >>
  `MAP f (t * p) = s *_ p_` by rw[field_iso_poly_mult] >>
  `poly (t * p)` by rw[] >>
  metis_tac[field_iso_poly_unique]);

(* Theorem: (r === r_) f ==> !p. weak p ==> (p = MAP (LINV f R) p_) *)
(* Proof:
   Since weak p
     <=> EVERY (\x. x IN R) p                  by weak_def_alt
     <=> !x. MEM x p ==> x IN R                by EVERY_MEM (1)
    Note BIJ f R R_                            by FieldIso_def
    Thus !x. MEM x R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM (2)
       MAP (LINV f R) p_
     = MAP (LINV f R) (MAP f p)                by notation
     = MAP (LINV f R o f) p                    by MAP_MAP_o
     = MAP I p                                 by MAP_CONG, (1) and (2)
     = p                                       by MAP_ID
*)
val field_iso_weak_inv = store_thm(
  "field_iso_weak_inv",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. weak p ==> (p = MAP (LINV f R) p_)``,
  rw[weak_def_alt, EVERY_MEM, MAP_MAP_o] >>
  `MAP (LINV f R o f) p = MAP I p` suffices_by rw[] >>
  (irule MAP_CONG >> simp[]) >>
  metis_tac[FieldIso_def, BIJ_LINV_THM]);

(* Theorem: (r === r_) f ==> !p. poly p ==> (p = MAP (LINV f R) p_) *)
(* Proof: by field_iso_weak_inv, poly_is_weak *)
val field_iso_poly_inv = store_thm(
  "field_iso_poly_inv",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> (p = MAP (LINV f R) p_)``,
  metis_tac[field_iso_weak_inv, poly_is_weak]);

(* Theorem: (r === r_) f ==> !p. monic p ==> monic_ p_ *)
(* Proof:
       monic p
   <=> poly p /\ lead p = #1   by poly_monic_def
   Note poly p ==> poly_ p_    by field_iso_poly
    and lead p = #1
    ==> lead_ p_
      = MAP f (lead p)         by field_iso_poly_lead
      = MAP f #1               by above
      = #1_                    by field_iso_one
*)
val field_iso_poly_monic = store_thm(
  "field_iso_poly_monic",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. monic p ==> monic_ p_``,
  metis_tac[poly_monic_def, field_iso_poly, field_iso_poly_lead, field_iso_one]);

(* Theorem: (r === r_) f ==> !p. poly p ==> (monic p <=> monic_ p_) *)
(* Proof:
   If part: monic p ==> monic_ p_, true by field_iso_poly_monic
   Only-if part: monic_ p_ ==> monic p
      Given poly p,
       then f (lead p)
          = lead_ p_        by field_iso_poly_lead
          = #1_             by poly_monic_lead
      Since lead p IN R     by poly_lead_element
       Thus lead p = #1     by field_iso_eq_one
         or monic p         by poly_monic_def
*)
val field_iso_poly_monic_iff = store_thm(
  "field_iso_poly_monic_iff",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> (monic p <=> monic_ p_)``,
  rw[EQ_IMP_THM] >-
  metis_tac[field_iso_poly_monic] >>
  `lead_ p_ = f (lead p)` by rw[field_iso_poly_lead] >>
  `lead_ p_ = #1_` by rw[GSYM poly_monic_lead] >>
  `lead p = #1` by metis_tac[field_iso_eq_one, poly_lead_element, field_is_ring] >>
  rw[poly_monic_def]);

(* Theorem: (r === r_) f ==> !p. ulead p ==> ulead_ p_ *)
(* Proof:
   Note ulead p <=> poly p /\ unit (lead p)     by notation
    Now  poly p <=> poly_ p_                    by field_iso_poly
    and f (lead p) = lead_ p_                   by field_iso_poly_lead
    and !x unit x <=> unit_ (f x)               by field_iso_unit
   Thus ulead_ p_  iff ulead p                  by notation
*)
val field_iso_poly_ulead = store_thm(
  "field_iso_poly_ulead",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. ulead p ==> ulead_ p_``,
  metis_tac[field_iso_poly_lead, field_iso_unit, field_iso_poly]);

(* Theorem: (r === r_) f ==> !p. pmonic p ==> pmonic_ p_ *)
(* Proof:
   Note ulead p <=>
        poly p /\ unit (lead p) /\ 0 < deg p    by notation
    Now  poly p <=> poly_ p_                    by field_iso_poly
    and f (lead p) = lead_ p_                   by field_iso_poly_lead
    and !x unit x <=> unit_ (f x)               by field_iso_unit
    and      deg p = deg_ p_                    by field_iso_poly_deg
   Thus pmonic_ p_  iff pmonic p                by notation
*)
val field_iso_poly_pmonic = store_thm(
  "field_iso_poly_pmonic",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. pmonic p ==> pmonic_ p_``,
  prove_tac[field_iso_poly_deg, field_iso_poly_lead, field_iso_unit, field_iso_poly]);

(* Theorem: (r === r_) f ==> !p. upoly p ==> upoly_ p_ *)
(* Proof:
         upoly p
     <=> poly p /\ p <> |0| /\ (deg p = 0)     by poly_field_unit
     Now poly p ==> poly_ p_                   by field_iso_poly
     and p <> |0| <=> p_ <> |0|_               by field_iso_eq_poly_zero
     and deg_ p_ = deg p = 0                   by field_iso_poly_deg
   Hence upoly_ p_                             by poly_field_unit
*)
val field_iso_poly_unit = store_thm(
  "field_iso_poly_unit",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. upoly p ==> upoly_ p_``,
  rw[poly_field_unit] >-
  metis_tac[field_iso_poly] >>
  metis_tac[field_iso_poly_deg]);

(* Theorem: (r === r_) f ==> !p. poly p ==> (upoly p <=> upoly_ p_) *)
(* Proof:
   If part: upoly p ==> upoly_ p_, true by field_iso_poly_unit
   Only-if part: upoly_ p_ ==> upoly p
     Note p_ <> |0|_ <=> p <> |0|            by field_iso_eq_poly_zero
     and deg_ p_ = deg p = 0                 by field_iso_poly_deg
   Hence upoly p                             by poly_field_unit
*)
val field_iso_poly_unit_iff = store_thm(
  "field_iso_poly_unit_iff",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> (upoly p <=> upoly_ p_)``,
  rw[poly_field_unit, EQ_IMP_THM] >-
  metis_tac[field_iso_poly] >-
  metis_tac[field_iso_poly_deg] >>
  metis_tac[field_iso_poly_deg]);

(* Theorem: (r === r_) f ==> !p. ipoly p ==> ipoly_ p_ *)
(* Proof:
   Note ipoly p
    <=> poly p /\ p <> |0| /\ ~upoly p /\
        !x y. poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y  by poly_irreducible_def
    Now poly p ==> poly_ p_           by field_iso_poly
    and p <> |0| <=> p_ <> |0|_       by field_iso_eq_poly_zero
    and ~upoly p <=> ~upoly_ p_       by field_iso_poly_unit_iff

   Then ?u. poly u /\ (x = MAP f u)   by field_iso_inverse_poly
    and ?v. poly v /\ (y = MAP f v)   by field_iso_inverse_polynomial
   Thus p_ = x *_ y
           = (MAP f u) *_ (MAP f v)   by x, y above
           = MAP f (u * v)            by field_iso_poly_mult
  Since poly (u * v)                  by poly_mult_poly
   thus p = u * v                     by field_iso_poly_unique
     or upoly u \/ upoly v            by poly_irreducible_def, above
    ==> upoly_ x \/ upoly_ y          by field_iso_poly_unit
*)
val field_iso_poly_irreducible = store_thm(
  "field_iso_poly_irreducible",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. ipoly p ==> ipoly_ p_``,
  rw[poly_irreducible_def] >-
  metis_tac[field_iso_poly] >-
  metis_tac[field_iso_poly_unit_iff] >>
  `?u. poly u /\ (x = MAP f u)` by metis_tac[field_iso_inverse_poly] >>
  `?v. poly v /\ (y = MAP f v)` by metis_tac[field_iso_inverse_poly] >>
  `p_ = MAP f (u * v)` by metis_tac[field_iso_poly_mult] >>
  `p = u * v` by metis_tac[field_iso_poly_unique, poly_mult_poly, field_is_ring] >>
  metis_tac[field_iso_poly_unit]);

(* Theorem: (r === r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x)) *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_poly_eval *)
val field_iso_poly_eval = store_thm(
  "field_iso_poly_eval",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==>
   !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))``,
  rw[field_iso_eq_ring_iso, ring_iso_poly_eval]);

(* Theorem: (r === r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x) *)
(* Proof: by field_iso_eq_ring_iso, ring_iso_poly_root *)
val field_iso_poly_root = store_thm(
  "field_iso_poly_root",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)``,
  metis_tac[field_iso_eq_ring_iso, ring_iso_poly_root, field_is_ring]);

(* Theorem: (r === r_) f ==> !p x. poly p /\ x IN R ==> (root p x <=> root_ p_ (f x)) *)
(* Proof:
       root p x
   <=> eval p x = #0            by poly_root_def
   <=> f (eval p x) = #0_       by field_iso_eq_zero
   <=> eval_ p_ (f x) = #0_     by field_iso_poly_eval
   <=> root_ p_ (f x)           by poly_root_def
*)
val field_iso_poly_root_iff = store_thm(
  "field_iso_poly_root_iff",
  ``!(r:'a ring) (r_:'b ring) f. (r === r_) f ==>
   !p x. poly p /\ x IN R ==> (root p x <=> root_ p_ (f x))``,
  metis_tac[poly_root_def, field_iso_poly_eval, field_iso_eq_zero, poly_eval_element, field_is_ring]);

(* Theorem: (r === r_) f ==>
            !p s. poly p /\ s SUBSET R ==> ((roots p) SUBSET s <=> (roots_ p_) SUBSET (IMAGE f s)) *)
(* Proof:
   Note poly_ p_       by field_iso_poly

       (roots p) SUBSET s
   <=> !x. x IN (roots p) ==> x IN s      by SUBSET_DEF
   <=> !x. x IN R /\ root p x ==> x IN s  by poly_roots_member

       roots_ p_ SUBSET (IMAGE f s)
   <=> !x. x IN (roots_ p_) ==> x IN (IMAGE f s)          by SUBSET_DEF
   <=> !x. x IN R_ /\ (root_ p_ x) ==> x IN (IMAGE f s)   by poly_roots_member

   If part: roots p SUBSET s ==> roots_ p_ SUBSET IMAGE f s
      Given roots p SUBSET s, this is to show:
      (1) !x. x IN R_ /\ (root_ p_ x) ==> x IN (IMAGE f s)
       Let y = LINV f R x.
      Note y IN R /\ (x = f y)          by field_iso_inverse_element, x IN R_
      Thus root_ p_ x
         = root_ p_ (f y)               by given
         = root p y                     by field_iso_poly_root_iff
        so y IN s                       by implication, (roots p) SUBSET s
        or (x = f y) IN (IMAGE f s)     by IN_IMAGE

   Only-if part: roots_ p_ SUBSET IMAGE f s ==> roots p SUBSET s
      Given roots_ p_ SUBSET IMAGE f s, this is to show:
      (1) !x. x IN R /\ root p x ==> x IN s
      Note INJ f R R_                   by FieldIso_def, BIJ_DEF
        so f x IN R_                    by INJ_DEF
       and root p x
         = root_ p_ (f x)               by field_iso_poly_root_iff
      thus (f x) IN (IMAGE f s)         by implication, roots_ p_ SUBSET IMAGE f s
        or ?y. y IN s /\ (f y = f x)    by IN_IMAGE
        or y IN R /\ (f y = f x)        by SUBSET_DEF, s SUBSET R
       ==> x = y, or x IN s             by INJ_DEF
*)
val field_iso_poly_roots = store_thm(
  "field_iso_poly_roots",
  ``!(r:'a ring) (r_:'b ring) f. (r === r_) f ==>
   !p s. poly p /\ s SUBSET R ==> ((roots p) SUBSET s <=> (roots_ p_) SUBSET (IMAGE f s))``,
  rpt strip_tac >>
  `poly_ p_` by metis_tac[field_iso_poly] >>
  rw[poly_roots_member, SUBSET_DEF, EQ_IMP_THM] >| [
    qabbrev_tac `y = LINV f R x` >>
    `y IN R /\ (x = f y)` by metis_tac[field_iso_inverse_element] >>
    `root p y ` by metis_tac[field_iso_poly_root_iff] >>
    metis_tac[],
    `root_ p_ (f x)` by metis_tac[field_iso_poly_root] >>
    `(f x) IN R_` by metis_tac[IN_IMAGE, FieldIso_def, BIJ_DEF, INJ_DEF] >>
    `?y. (f x = f y) /\ y IN s` by rw[] >>
    `INJ f R R_` by metis_tac[FieldIso_def, BIJ_DEF] >>
    metis_tac[SUBSET_DEF, INJ_DEF]
  ]);

(* Theorem: (r === r_) f ==> !p. poly p ==> (roots_ p_ = IMAGE f (roots p)) *)
(* Proof:
   Let s = roots p.
   Then s SUBSET R                         by poly_roots_member, SUBSET_DEF
   By SUBSET_ANTISYM, this is to show:
   (1) roots_ p_ SUBSET IMAGE f (roots p)
       Note s SUBSET s                     by SUBSET_REFL
        ==> roots_ p_ SUBSET IMAGE f s     by field_iso_poly_roots
   (2) IMAGE f s SUBSET roots_ p_
       By SUBSET_DEF, this is to show:
          !x. x IN s ==> f x IN roots_ p_
       Note x IN R                         by SUBSET_DEF, s SUBSET R
        ==> f x IN R_                      by field_iso_element
        and root p x                       by poly_roots_member
        ==> root_ p_ (f x)                 by field_iso_poly_root_iff
         or f x IN (roots_ p_)             by poly_roots_member
*)
val field_iso_poly_roots_iff = store_thm(
  "field_iso_poly_roots_iff",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> (roots_ p_ = IMAGE f (roots p))``,
  rpt strip_tac >>
  qabbrev_tac `s = roots p` >>
  `s SUBSET R` by metis_tac[poly_roots_member, SUBSET_DEF] >>
  `s SUBSET s` by rw[] >>
  `roots_ p_ SUBSET IMAGE f s` by metis_tac[field_iso_poly_roots] >>
  `IMAGE f s SUBSET roots_ p_` by
  (rw[SUBSET_DEF] >>
  `x' IN R` by metis_tac[SUBSET_DEF] >>
  `f x' IN R_` by metis_tac[field_iso_element] >>
  metis_tac[field_iso_poly_root_iff, poly_roots_member]) >>
  rw[SUBSET_ANTISYM]);

(* Theorem: (r === r_) f ==> !p. poly p ==> ((p_ = X_) <=> (p = X)) *)
(* Proof:
   If part: p_ = X_ ==> p = X
      Since poly X                by poly_X
        and MAP f X = X_          by field_iso_poly_X
         so p = X                 by field_iso_poly_unique
   Only-if part: p = X ==> p_ = X_, true  by field_iso_poly_X
*)
val field_iso_poly_X_iff = store_thm(
  "field_iso_poly_X_iff",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p ==> ((p_ = X_) <=> (p = X))``,
  metis_tac[field_iso_poly_unique, poly_X, field_iso_poly_X, field_is_ring]);

(* Theorem: (r === s) I ==> !p. poly p <=> Poly s p *)
(* Proof:
   If part: poly p ==> Poly s p
      Note poly p
       ==> Poly s (MAP I p)              by field_iso_poly
       ==> Poly s p                      by MAP_ID
   Only-if part: Poly s p ==> poly p
      Note Poly s p
       ==> ?q. poly q /\ (MAP I p = q)   by field_iso_inverse_poly
       ==> p = q, so poly p              by MAP_ID
*)
val field_iso_I_poly_iff = store_thm(
  "field_iso_I_poly_iff",
  ``!(r s):'a field. (r === s) I ==> !p. poly p <=> Poly s p``,
  metis_tac[field_iso_poly, field_iso_inverse_poly, MAP_ID]);

(* Theorem: (r === r_) f ==> !c:num. MAP f (X + |c|) = X_ +_ |c|_ *)
(* Proof:
   Note MAP f X = X_                   by field_iso_poly_X
    and MAP f |c| = poly_num r_ c      by field_iso_poly_sum_num
   Thus MAP f (X + |c|) = X_ +_ |c|_   by field_iso_poly_add
*)
val field_iso_poly_X_add_c = store_thm(
  "field_iso_poly_X_add_c",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !c:num. MAP f (X + |c|) = X_ +_ |c|_``,
  rpt strip_tac >>
  `poly X /\ poly |c|` by rw[] >>
  metis_tac[field_iso_poly_X, field_iso_poly_sum_num, field_iso_poly_add]);

(* Theorem: (r === r_) f ==> !c:num. MAP f (X - |c|) = X_ -_ |c|_ *)
(* Proof:
   Note MAP f X = X_                   by field_iso_poly_X
    and MAP f |c| = poly_num r_ c      by field_iso_poly_sum_num
   Thus MAP f (X - |c|) = X_ -_ |c|_   by field_iso_poly_sub
*)
val field_iso_poly_X_sub_c = store_thm(
  "field_iso_poly_X_sub_c",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !c:num. MAP f (X - |c|) = X_ -_ |c|_``,
  rpt strip_tac >>
  `poly X /\ poly |c|` by rw[] >>
  metis_tac[field_iso_poly_X, field_iso_poly_sum_num, field_iso_poly_sub]);

(* Theorem: (r === r_) f ==> !c. c IN R ==> (MAP f (factor c) = factor_ (f c)) *)
(* Proof:
     MAP f (factor c)
   = MAP f (-c :: |1|)           by poly_factor_def
   = (f (-c)):: (MAP f |1|)      by MAP
   = $-_ (f c):: |1|_            by field_iso_neg, field_iso_poly_one
   = factor_ (f c)               by poly_factor_def
*)
val field_iso_poly_factor = store_thm(
  "field_iso_poly_factor",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !c. c IN R ==> (MAP f (factor c) = factor_ (f c))``,
  rw[poly_factor_def, field_iso_neg, field_iso_poly_one]);

(* Theorem: (r === r_) f ==> !p x. x IN R /\ poly p ==>
                             (poly_root_multiplicity r_ p_ (f x) = multiplicity p x) *)
(* Proof:
   By poly_root_multiplicity_def, the result follows if:
      poly_root_multiplicity_set r_ p_ (f x) = multiplicity_set p x
   By poly_root_multiplicity_set_def, EXTENSION, this is to show:
   (1) !n. factor_ (f x) **_ n pdivides_ p_ <=> factor x ** n pdivides p
       Note poly (factor x)                                 by poly_factor_poly
        and poly (factor x ** n)                            by poly_exp_poly
        Now MAP f (factor x) = factor_ (f x)                by field_iso_poly_factor
        ==> MAP f (factor x ** n) = factor_ (f x) **_ n     by field_iso_poly_exp
       Thus factor x ** n pdivides p <=>
            factor_ (f x) **_ n pdivides_ p_                by field_iso_poly_divides_iff
   (2) x IN R /\ f x NOTIN R_ ==> !n. ~(factor x ** n pdivides p)
       Note f x IN R_         by field_iso_element
       Thus there is a contradiction, hence true.
*)
val field_iso_poly_root_multiplicity = store_thm(
  "field_iso_poly_root_multiplicity",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==>
   !p x. x IN R /\ poly p ==> (poly_root_multiplicity r_ p_ (f x) = multiplicity p x)``,
  rw_tac std_ss[poly_root_multiplicity_def] >>
  `poly_root_multiplicity_set r_ p_ (f x) = multiplicity_set p x` suffices_by rw[] >>
  rw[poly_root_multiplicity_set_def, EXTENSION] >| [
    `poly (factor x) /\ poly (factor x ** x')` by rw[poly_factor_poly] >>
    `MAP f (factor x) = factor_ (f x)` by rw[field_iso_poly_factor] >>
    `MAP f (factor x ** x') = factor_ (f x) **_ x'` by metis_tac[field_iso_poly_exp] >>
    prove_tac[field_iso_poly_divides_iff],
    metis_tac[field_iso_element]
  ]);

(* Theorem: (r === r_) f ==> !p. poly p /\ separable p ==> poly_separable r_ p_*)
(* Proof:
   By poly_separable_def, this is to show:
   (1) p <> |0| ==> p_ <> |0|_, true   by field_iso_eq_poly_zero
   (2) !c. c IN roots_ p_ ==> poly_root_multiplicity r_ p_ c = 1
       Note SURJ f R R_               by FieldIso_def, BIJ_DEF
        ==> ?z. z IN R /\ (c = f z)   by SURJ_DEF
       Also root_ p_ x ==> root p z   by field_iso_poly_root_iff
            poly_root_multiplicity r_ p_ c
          = multiplicity p c          by field_iso_poly_root_multiplicity
          = 1                         by poly_separable_def, separable p
*)
val field_iso_poly_separable = store_thm(
  "field_iso_poly_separable",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. poly p /\ separable p ==> poly_separable r_ p_``,
  rw_tac std_ss[poly_separable_def] >-
  metis_tac[field_iso_eq_poly_zero] >>
  fs[poly_roots_member] >>
  `?z. z IN R /\ (c = f z)` by prove_tac[FieldIso_def, BIJ_DEF, SURJ_DEF] >>
  `root p z` by metis_tac[field_iso_poly_root_iff] >>
  metis_tac[field_iso_poly_root_multiplicity]);

(* Theorem: (r === r_) f ==> !p. ipoly p ==>
            (((PolyModRing r p)) === ((PolyModRing r_ p_))) (MAP f) *)
(* Proof:
   This is to show:
   (1) Field (PolyModRing r p), true     by poly_mod_irreducible_field, ipoly p
   (2) Field (PolyModRing r_ p_)
       Note ipoly_ p_                    by field_iso_poly_irreducible
       Thus true                         by poly_mod_ring_ring
   (3) FieldIso f r r_ ==> FieldIso (MAP f) (PolyModRing r p) (PolyModRing r_ p_)
       Note RingIso (MAP f)
                    (PolyModRing r p)
                    (PolyModRing r_ p_)  by field_iso_poly_mod_ring_iso
         or FieldIso (MAP f)
                    (PolyModRing r p)
                    (PolyModRing r_ p_)  by field_iso_eq_ring_iso
*)
val field_iso_poly_mod_field_iso = store_thm(
  "field_iso_poly_mod_field_iso",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !p. ipoly p ==>
    (((PolyModRing r p)) === ((PolyModRing r_ p_))) (MAP f)``,
  rpt strip_tac >-
  rw[poly_mod_irreducible_field] >-
 (`ipoly_ p_` by metis_tac[field_iso_poly_irreducible] >>
  rw[poly_mod_irreducible_field]) >>
  rw[field_iso_poly_mod_ring_iso, field_iso_eq_ring_iso]);

(* Theorem: (r =f= r_) ==> !p. ipoly p ==>
            ?f:'a poly -> 'b poly. (((PolyModRing r p)) =f= ((PolyModRing r_ (f p)))) *)
(* Proof: by field_iso_poly_mod_field_iso *)
val field_iso_poly_mod_field_isomorphism = store_thm(
  "field_iso_poly_mod_field_isomorphism",
  ``!(r:'a field) (r_:'b field). (r =f= r_) ==> !p. ipoly p ==>
    ?f:'a poly -> 'b poly. (((PolyModRing r p)) =f= ((PolyModRing r_ (f p))))``,
  metis_tac[field_iso_poly_mod_field_iso]);

(* Another milestone theorem: This is almost F[X] iso F[Y]. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
