(* ------------------------------------------------------------------------- *)
(* Introspective Shifting: from Ring (ZN n) to Ring (ZN p)                   *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSshift";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory;

open AKSintroTheory;
open computeRingTheory; (* for overloads on x^, x+^, x^+, x^- *)

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyBinomialTheory polyDivisionTheory polyEvalTheory;

open polyDividesTheory;
open polyMonicTheory;

open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyMapTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open fieldInstancesTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Introspective Shifting Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   n intro_ p_    = poly_intro (r_:'b ring) k n (p_:'b poly)
*)
(* Definitions and Theorems (# are exported):

   Introspective Shift to Homomorphic Ring:
   ring_homo_poly_intro          |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !k. 0 < k ==>
                                    !n p. n intro p /\ f (lead p) <> #0_ ==> n intro_ p_
   ring_homo_poly_intro_monic    |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !k. 0 < k ==>
                                    !n p. n intro p /\ monic p ==> n intro_ p_
   ring_homo_poly_intro_X_add_c  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !k. 0 < k ==>
                                    !n c. n intro X + |c| ==> n intro_ (MAP f (X + |c|))
   ring_homo_ZN_to_ZN_X_add_c    |- !n m s. 0 < n /\ 1 < m /\ s < m ==> !c. 0 < c /\ c <= s ==>
                                    !f. RingHomo f (ZN n) (ZN m) ==> (MAP f (x+ n c) = x+ m c)
   ring_homo_intro_ZN_to_ZN_X_add_c
                                 |- !n m. 0 < n /\ 1 < m /\ m divides n ==>
                                    !k s. 0 < k /\ s < m ==> !h c. 0 < c /\ c <= s /\
                                     poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c)
   ring_homo_intro_ZN_to_ZN_X_add_c_alt
                                 |- !n m k h s. 0 < n /\ 0 < k /\ 1 < m /\ m divides n /\ s < m ==>
                                    !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==>
                                          poly_intro (ZN m) k h (x+ m c)
   ring_homo_intro_range_ZN_to_ZN_X_add_c
                                 |- !n m. 0 < n /\ 1 < m /\ m divides n ==>
                                    !h k s. 0 < k /\ s < m /\
                                            poly_intro_range (ZN n) k h s ==>
                                            poly_intro_range (ZN m) k h s
   ring_homo_intro_range_ZN_to_ZN_X_add_c_alt
                                 |- !n m k h s. 0 < n /\ 0 < k /\ 1 < m /\
                                                m divides n /\ s < m /\
                                                poly_intro_range (ZN n) k h s ==>
                                                poly_intro_range (ZN m) k h s

*)

(* ------------------------------------------------------------------------- *)
(* Helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Introspective Shift to Homomorphic Ring                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload poly_intro in another ring *)
val _ = overload_on("intro_", ``poly_intro (r_:'b ring) k``);
val _ = set_fixity "intro_" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !k. 0 < k ==> !n p. n intro p /\ f (lead p) <> #0_ ==> n intro_ p_ *)
(* Proof:
   First, #1 <> #0                       by ring_homo_one, ring_homo_zero
   Let z = unity k, then pmonic z        by poly_unity_pmonic, 0 < k.
       n intro p
   <=> poly p /\ z pdivides p ** n - peval p (X ** n)   by poly_intro_alt_1

   With f (lead p) <> #0_,
        poly_ p_                         by ring_homo_poly_nonzero
   With lead (X ** n) = #1               by poly_monic_lead, poly_monic_X, poly_monic_exp_monic
        poly_ (MAP f (X ** n))           by ring_homo_poly_nonzero, ring_homo_one
     so chop_ (MAP f (X ** n)) = MAP f (X ** n)  by poly_chop_poly
   With lead z = #1                      by poly_unity_lead
        poly_ (MAP f z)                  by ring_homo_poly_nonzero, ring_homo_one
     so chop_ (MAP f z) = MAP f z        by poly_chop_poly
   From z pdivides p ** n - peval p (X ** n),
        (MAP f z) pdivides_
        (chop_ (MAP f (p ** n - peval p (X ** n))))  by ring_homo_poly_divides_chop
   Simplify the complex term:
     chop_ (MAP f (p ** n - peval p (X ** n)))
   = (chop_ (MAP f (p ** n))) -_
     (chop_ (MAP f (peval p (X ** n))))  by ring_homo_sub_chop_chop
   First one:
     chop_ (MAP f (p ** n)) = p_ **_ n   by ring_homo_poly_exp_chop
   Second one:
     chop_ (MAP f (peval p (X ** n)))
   = peval_ p_ (MAP f (X ** n))          by ring_homo_peval_chop
   = peval_ p_ (MAP f X **_ n)           by ring_homo_poly_exp_chop
   Now,
   MAP f |1| = |1|_                      by ring_homo_poly_one_alt
   MAP f X = X_                          by ring_homo_poly_X
   MAP f z = MAP f X **_ k -_ MAP f |1|  by ring_homo_poly_unity
   Hence n intro_ p_                     by poly_intro_alt_1
*)
val ring_homo_poly_intro = store_thm(
  "ring_homo_poly_intro",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !k. 0 < k ==> !n p. n intro p /\ f (lead p) <> #0_ ==> n intro_ p_``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[ring_homo_one, ring_homo_zero] >>
  qabbrev_tac `z = unity k` >>
  `poly X /\ poly (X ** n) /\ pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `poly p /\ z pdivides p ** n - peval p (X ** n)` by metis_tac[poly_intro_alt_1] >>
  `poly_ p_` by metis_tac[ring_homo_poly_nonzero] >>
  `(lead (X ** n) = #1) /\ (lead z = #1)` by rw[poly_unity_lead, Abbr`z`] >>
  `poly_ (MAP f (X ** n)) /\ poly_ (MAP f z)` by metis_tac[ring_homo_poly_nonzero, ring_homo_one] >>
  `poly (p ** n) /\ poly (X ** n) /\ poly (peval p (X ** n))` by rw[] >>
  `poly (p ** n - peval p (X ** n))` by rw[] >>
  `(MAP f z) pdivides_ (chop_ (MAP f (p ** n - peval p (X ** n))))` by metis_tac[ring_homo_poly_divides_chop, poly_chop_poly] >>
  `chop_ (MAP f (p ** n - peval p (X ** n))) =
    (chop_ (MAP f (p ** n))) -_ (chop_ (MAP f (peval p (X ** n))))` by rw_tac std_ss[ring_homo_sub_chop_chop] >>
  `chop_ (MAP f (p ** n)) = p_ **_ n` by rw_tac std_ss[ring_homo_poly_exp_chop] >>
  `chop_ (MAP f (peval p (X ** n))) = peval_ p_ (MAP f (X ** n))` by rw_tac std_ss[ring_homo_peval_chop] >>
  `_ = peval_ p_ (MAP f X **_ n)` by metis_tac[ring_homo_poly_exp_chop, poly_chop_poly] >>
  `MAP f |1| = |1|_` by rw[ring_homo_poly_one_alt] >>
  `MAP f X = X_` by rw[ring_homo_poly_X] >>
  `MAP f z = MAP f X **_ k -_ MAP f |1|` by rw_tac std_ss[ring_homo_poly_unity, Abbr`z`] >>
  metis_tac[poly_intro_alt_1]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !k. 0 < k ==> !n p. n intro p /\ monic p ==> n intro_ p_ *)
(* Proof:
   Easy one:
     Since monic p
       ==> f (lead p) = f #1       by poly_monic_lead
                      = #1_        by ring_homo_one
                     <> #0_        by given
        Hence true                 by ring_homo_poly_intro
   Hard one:
   First, #1 <> #0                       by ring_homo_one, ring_homo_zero
   Let z = unity k, then pmonic z        by poly_unity_pmonic, 0 < k.
       n intro p
   <=> poly p /\ z pdivides p ** n - peval p (X ** n)   by poly_intro_alt_1

   With monic p,
        poly_ p_                         by ring_homo_weak_monic_poly
   With lead (X ** n) = #1               by poly_monic_lead, poly_monic_X, poly_monic_exp_monic
        poly_ (MAP f (X ** n))           by ring_homo_poly_nonzero, ring_homo_one
     so chop_ (MAP f (X ** n)) = MAP f (X ** n)  by poly_chop_poly
   With lead z = #1                      by poly_unity_lead
        poly_ (MAP f z)                  by ring_homo_poly_nonzero, ring_homo_one
     so chop_ (MAP f z) = MAP f z        by poly_chop_poly
   From z pdivides p ** n - peval p (X ** n),
        (MAP f z) pdivides_
        (chop_ (MAP f (p ** n - peval p (X ** n))))  by ring_homo_poly_divides_chop
   Simplify the complex term:
     chop_ (MAP f (p ** n - peval p (X ** n)))
   = (MAP f (p ** n)) -_ (chop_ (MAP f (peval p (X ** n))))   by ring_homo_poly_sub_chop
   First one:
     MAP f (p ** n) = p_ **_ n           by ring_homo_monic_poly_exp, since monic p.
   Second one:
     chop_ (MAP f (peval p (X ** n)))
   = peval_ p_ (MAP f (X ** n))          by ring_homo_peval_chop
   = peval_ p_ ((MAP f X) **_ n)         by ring_homo_poly_exp_chop
   Now,
   MAP f |1| = |1|_                      by ring_homo_poly_one_alt
   MAP f X = X_                          by ring_homo_poly_X
   MAP f z = ((MAP f X) **_ k) -_ (MAP f |1|)  by ring_homo_poly_unity
   Hence n intro_ p_                     by poly_intro_alt_1
*)
val ring_homo_poly_intro_monic = store_thm(
  "ring_homo_poly_intro_monic",
  ``!(r: 'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !k. 0 < k ==> !n p. n intro p /\ monic p ==> n intro_ p_``,
  metis_tac[ring_homo_poly_intro, poly_monic_lead, ring_homo_one]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==>
            !k. 0 < k ==> !n c:num. n intro (X + |c|) ==> n intro_ (MAP f (X + |c|)) *)
(* Proof:
   First, #1 <> #0           by ring_homo_one, ring_homo_zero
   Since monic (X + |c|)     by poly_monic_X_add_c
   This is true              by ring_homo_poly_intro_monic
*)
val ring_homo_poly_intro_X_add_c = store_thm(
  "ring_homo_poly_intro_X_add_c",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !k. 0 < k ==> !n c:num. n intro (X + |c|) ==> n intro_ (MAP f (X + |c|))``,
  metis_tac[ring_homo_poly_intro_monic, poly_monic_X_add_c, ring_homo_one, ring_homo_zero]);

(*
> poly_intro_def |> SPEC ``t:'a ring``;
val it = |- !k n p.
     poly_intro t k n p <=> Poly t p /\ 0 < k /\
     ((PolyRing t).prod.exp p n ==
      poly_peval t p ((PolyRing t).prod.exp (poly_shift t (PolyRing t).prod.id 1) n))
       (pmod t (poly_sub t ((PolyRing t).prod.exp (poly_shift t (PolyRing t).prod.id 1) k)
                           (PolyRing t).prod.id)): thm
*)

(*
MAP f (X + |c|)
= ((MAP f X) +_ (MAP f |c|)
= (|1||_ >>_ 1) +_ (MAP f |c|)
= (|1||_ >>_ 1) +_ (##_ #1_ c)
*)

(* Theorem: 0 < n /\ 1 < m /\ s < m ==> !c. 0 < c /\ c <= s ==>
           !f. RingHomo f (ZN n) (ZN m) ==> (MAP f (x+ n c) = x+ m c) *)
(* Proof:
   Since Ring (ZN n)          by ZN_ring, 0 < n
     and Ring (ZN m)          by ZN_ring, 0 < m
     and (ZN m).prod.id = 1   by ZN_property, m <> 1
         (ZN m).sum.id = 0    by ZN_property
    thus (ZN m).prod.id <> (ZN m).sum.id   by 1 <> 0
     and char (ZN m) = m      by ZN_char, 0 < m
   Since s < m, all c < m.
     MAP f (zx+ n c)
   = MAP f ((PolyRing (ZN n)).sum.op x (a c))
   = (PolyRing (ZN m)).sum.op (MAP f x) (MAP f (a c))     by ring_homo_poly_X_add_c
   = (PolyRing (ZN m)).sum.op y (MAP f (a c))             by ring_homo_poly_X
   = (PolyRing (ZN m)).sum.op y (z c)                     by ring_homo_poly_sum_num, 0 < c < m
   = zx+ m c
*)
val ring_homo_ZN_to_ZN_X_add_c = store_thm(
  "ring_homo_ZN_to_ZN_X_add_c",
  ``!n m s. 0 < n /\ 1 < m /\ s < m ==> !c. 0 < c /\ c <= s ==>
   !f. RingHomo f (ZN n) (ZN m) ==> (MAP f (x+ n c) = x+ m c)``,
  rpt strip_tac >>
  `0 < m /\ m <> 1` by decide_tac >>
  `Ring (ZN n) /\ Ring (ZN m)` by rw[ZN_ring] >>
  `(ZN m).prod.id <> (ZN m).sum.id` by rw[ZN_property] >>
  `char (ZN m) = m` by rw[ZN_char] >>
  `c < m` by decide_tac >>
  qabbrev_tac `x = poly_shift (ZN n) (PolyRing (ZN n)).prod.id 1` >>
  qabbrev_tac `y = poly_shift (ZN m) (PolyRing (ZN m)).prod.id 1` >>
  qabbrev_tac `a = \c:num. (PolyRing (ZN n)).sum.exp (PolyRing (ZN n)).prod.id c` >>
  qabbrev_tac `z = \c:num. (PolyRing (ZN m)).sum.exp (PolyRing (ZN m)).prod.id c` >>
  `MAP f ((PolyRing (ZN n)).sum.op x (a c)) = (PolyRing (ZN m)).sum.op (MAP f x) (MAP f (a c))` by metis_tac[ring_homo_poly_X_add_c] >>
  `_ = (PolyRing (ZN m)).sum.op y (MAP f (a c))` by metis_tac[ring_homo_poly_X] >>
  `_ = (PolyRing (ZN m)).sum.op y (z c)` by metis_tac[ring_homo_poly_sum_num] >>
  rw_tac std_ss[]);

(* Theorem: 0 < n /\ 1 < m /\ m divides n ==> !k s. 0 < k /\ s < m ==>
      !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c) *)
(* Proof:
   We have Ring (ZN n)                       by ZN_ring, 0 < n
       and Ring (ZN m)                       by ZN_ring, 0 < m
       and (ZN m).prod.id <> (ZN m).sum.id   by ZN_property, m <> 1
   Let f = \x. x MOD m, then
       RingHomo f (ZN n) (ZN m)              by ZN_to_ZN_ring_homo, 0 < n, m divides n
   ==> (MAP f (x+ n c) = x+ m c)             by ring_homo_ZN_to_ZN_X_add_c, 1 < m, s < m
   ==> poly_intro (ZN m) k h (x+ m c)        by ring_homo_poly_intro_X_add_c, 0 < k
*)
val ring_homo_intro_ZN_to_ZN_X_add_c = store_thm(
  "ring_homo_intro_ZN_to_ZN_X_add_c",
  ``!n m. 0 < n /\ 1 < m /\ m divides n ==>
   !k s. 0 < k /\ s < m ==>
    !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c)``,
  rpt strip_tac >>
  `0 < m /\ m <> 1` by decide_tac >>
  `Ring (ZN n) /\ Ring (ZN m)` by rw[ZN_ring] >>
  `(ZN m).prod.id <> (ZN m).sum.id` by rw[ZN_property] >>
  qabbrev_tac `f = (\x. x MOD m)` >>
  `RingHomo f (ZN n) (ZN m)` by rw[ZN_to_ZN_ring_homo, Abbr`f`] >>
  metis_tac[ring_homo_ZN_to_ZN_X_add_c, ring_homo_poly_intro_X_add_c]);

(* Theorem: 0 < n /\ 0 < k /\ 1 < m /\ m divides n /\ s < m ==>
   !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c) *)
(* Proof: by ring_homo_intro_ZN_to_ZN_X_add_c *)
val ring_homo_intro_ZN_to_ZN_X_add_c_alt = store_thm(
  "ring_homo_intro_ZN_to_ZN_X_add_c_alt",
  ``!n m k h s. 0 < n /\ 0 < k /\ 1 < m /\ m divides n /\ s < m ==>
   !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN m) k h (x+ m c)``,
  metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c]);

(* Theorem: 0 < n /\ 1 < m /\ m divides n ==>
   !h k s. 0 < k /\ s < m /\
           poly_intro_range (ZN n) k h s ==> poly_intro_range (ZN m) k h s *)
(* Proof: by ring_homo_intro_ZN_to_ZN_X_add_c *)
val ring_homo_intro_range_ZN_to_ZN_X_add_c = store_thm(
  "ring_homo_intro_range_ZN_to_ZN_X_add_c",
  ``!n m. 0 < n /\ 1 < m /\ m divides n ==>
   !h k s. 0 < k /\ s < m /\
           poly_intro_range (ZN n) k h s ==> poly_intro_range (ZN m) k h s``,
  metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c]);

(* Theorem: 0 < n /\ 0 < k /\ 1 < m /\ m divides n /\ s < m /\
            poly_intro_range (ZN n) k h s ==> poly_intro_range (ZN m) k h s *)
(* Proof: by ring_homo_intro_range_ZN_to_ZN_X_add_c *)
val ring_homo_intro_range_ZN_to_ZN_X_add_c_alt = store_thm(
  "ring_homo_intro_range_ZN_to_ZN_X_add_c_alt",
  ``!n m k h s. 0 < n /\ 0 < k /\ 1 < m /\ m divides n /\ s < m /\
        poly_intro_range (ZN n) k h s ==> poly_intro_range (ZN m) k h s``,
  metis_tac[ring_homo_intro_range_ZN_to_ZN_X_add_c]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
