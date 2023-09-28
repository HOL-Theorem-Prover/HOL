(* ------------------------------------------------------------------------- *)
(* Polynomial Division with coefficients from a Ring                         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyDivision";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;
(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "ringTheory"; *) *)
(* val _ = load "ringUnitTheory"; *)
open monoidTheory groupTheory ringTheory ringUnitTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* val _ = load "helperListTheory"; *)
(* val _ = load "helperFunctionTheory"; *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* (* val _ = load "ringIdealTheory"; *) *)
(* val _ = load "quotientRingTheory"; *)
open ringIdealTheory quotientRingTheory;
open subgroupTheory;
open quotientGroupTheory;

open monoidMapTheory groupMapTheory ringMapTheory;

(* (* val _ = load "polyWeakTheory"; *) *)
(* val _ = load "polyRingTheory"; *)
open polynomialTheory polyWeakTheory polyRingTheory;


(* ------------------------------------------------------------------------- *)
(* Polynomials Division over a Ring R[x] Documentation                       *)
(* ------------------------------------------------------------------------- *)
(*
Note:
All the theorems are weakened forms of those in polyField and polyDivision.
*)
(* Data type:
   A polynomial is just a list of coefficients from a Ring r.
   Here a polynomial has no leading zeroes, i.e. not normalized.

   Overloads:
   ulead z          = poly z /\ unit (lead z)
   pmonic z         = poly z /\ unit (lead z) /\ 0 < deg z
   |/               = r*.inv      (re-establish)
   p / q            = poly_div r p q
   p % q            = poly_mod r p q
*)
(* Definitions and Theorems (# are exported):

   Polynomial Division:
   poly_division_eqn     |- !r. Ring r ==> !p q. poly p /\ pmonic q ==>
                            ?s t. poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q
   poly_division_all_eqn |- !r p q. Ring r /\ poly p /\ ulead q ==>
                            ?s t. poly s /\ poly t /\ p = s * q + t /\
                                  if 0 < deg q then deg t < deg q else t = |0|
   poly_div_mod_all_def  |- !r p q. Ring r /\ poly p /\ ulead q ==>
                                    poly (p / q) /\ poly (p % q) /\
                                    (p = p / q * q + p % q) /\
                                    if 0 < deg q then deg (p % q) < deg q else p % q = |0|
   poly_div_mod_def      |- !r p q. Ring r /\ poly p /\ pmonic q ==>
                            poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q
#  poly_div_poly         |- !r q p. Ring r /\ poly p /\ ulead q ==> poly (p / q)
#  poly_mod_poly         |- !r q p. Ring r /\ poly p /\ ulead q ==> poly (p % q)
   poly_division_alg     |- !r q p. Ring r /\ poly p /\ ulead q ==>
                                    (p = p / q * q + p % q) /\
                                    if 0 < deg q then deg (p % q) < deg q else p % q = |0|
   poly_division         |- !r q p.  Ring r /\ poly p /\ pmonic q ==>
                            (p = p / q * q + p % q) /\ deg (p % q) < deg q
   poly_division_all     |- !r p q. Ring r /\ poly p /\ ulead q ==>
                            (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q)
   poly_div_mod_unique   |- !r. Ring r ==> !p q s1 t1 s2 t2. poly p /\ ulead q /\
                            poly s1 /\ poly t1 /\ poly s2 /\ poly t2 /\
                            (p = s1 * q + t1) /\ deg t1 < deg q /\
                            (p = s2 * q + t2) /\ deg t2 < deg q ==> (s1 = s2) /\ (t1 = t2)
   poly_div_mod_eqn      |- !r. Ring r ==> !p q s t. poly p /\ ulead q /\ poly s /\ poly t /\
                            (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t)
   poly_div_unique       |- !r. Ring r ==> !p q s t. poly p /\ ulead q /\ poly s /\ poly t /\
                            (p = s * q + t) /\ deg t < deg q ==> (p / q = s)
   poly_mod_unique       |- !r. Ring r ==> !p q s t. poly p /\ ulead q /\ poly s /\ poly t /\
                            (p = s * q + t) /\ deg t < deg q ==> (p % q = t)

   Polynomial Quotient and Remainder -- constant divisor:
   poly_mod_by_const     |- !r. Ring r ==> !p z. poly p /\ ulead z /\
                                                 (deg z = 0) ==> (p % z = |0|)
   poly_div_by_const     |- !r. Ring r ==> !p z. poly p /\ ulead z /\
                                                 (deg z = 0) ==> (p / z = |/ (lead z) * p)
   poly_div_mod_by_const |- !r. Ring r ==> !p z. poly p /\ ulead z /\
                                                 (deg z = 0) ==> (p / z = |/ (lead z) * p) /\ (p % z = |0|)
   poly_div_mod_by_one   |- !r p. Ring r /\ poly p ==> (p / |1| = p) /\ (p % |1| = |0|)
   poly_div_by_one       |- !r p. Ring r /\ poly p ==> (p / |1| = p)
   poly_mod_by_one       |- !r p. Ring r /\ poly p ==> (p % |1| = |0|)

   Polynomial Quotient and Remainder -- non-constant divisor:
   poly_div_mod_less     |- !r. Ring r ==> !p z. poly p /\ ulead z /\ deg p < deg z ==> (p / z = |0|) /\ (p % z = p)
   poly_div_less         |- !r. Ring r ==> !p z. poly p /\ ulead z /\ deg p < deg z ==> (p / z = |0|)
   poly_mod_less         |- !r. Ring r ==> !p z. poly p /\ ulead z /\ deg p < deg z ==> (p % z = p)
   poly_zero_div_mod     |- !r. Ring r ==> !z. ulead z ==> ( |0| / z = |0|) /\ ( |0| % z = |0|)
#  poly_zero_div         |- !r. Ring r ==> !z. ulead z ==> ( |0| / z = |0|)
#  poly_zero_mod         |- !r. Ring r ==> !z. ulead z ==> ( |0| % z = |0|)
   poly_mod_mod          |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (p % z % z = p % z)
#  poly_div_mod_const    |- !r. Ring r ==> !z. pmonic z ==>
                            !c. c IN R /\ c <> #0 ==> ([c] / z = |0|) /\ ([c] % z = [c])
   poly_div_const        |- !r. Ring r ==> !z. pmonic z ==>
                            !c. c IN R /\ c <> #0 ==> ([c] / z = |0|)
   poly_mod_const        |- !r. Ring r ==> !z. pmonic z ==>
                            !c. c IN R /\ c <> #0 ==> ([c] % z = [c])
   poly_div_mod_neg      |- !r. Ring r ==> !p z. poly p /\ ulead z ==>
                            (-p / z = -(p / z)) /\ (-p % z = -(p % z))
   poly_div_neg          |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (-p / z = -(p / z))
   poly_mod_neg          |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (-p % z = -(p % z))
   poly_div_mod_multiple |- !r. Ring r ==> !p z. poly p /\ ulead z ==>
                                           (p * z / z = p) /\ ((p * z) % z = |0|)
   poly_div_multiple     |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (p * z / z = p)
   poly_mod_multiple     |- !r. Ring r ==> !p z. poly p /\ ulead z ==> ((p * z) % z = |0|)
   poly_div_multiple_comm   |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (z * p / z = p)
   poly_mod_multiple_comm   |- !r. Ring r ==> !p z. poly p /\ ulead z ==> ((z * p) % z = |0|)
   poly_div_mod_id       |- !r. Ring r ==> !p. ulead p ==> (p / p = |1|) /\ (p % p = |0|)
   poly_add_mod          |- !r. Ring r ==> !p q z. poly p /\ poly q /\ ulead z /\
                                     deg q < deg z /\ (p = z + q) ==> (p % z = q)
   poly_mod_add          |- !r. Ring r ==> !p q z. poly p /\ poly q /\ ulead z ==>
                                     ((p + q) % z = (p % z + q % z) % z)
   poly_mod_add_assoc    |- !r. Ring r ==> !p q t z. poly p /\ poly q /\ poly t /\ ulead z ==>
                                     (((p + q) % z + t) % z = (p + (q + t) % z) % z)
   poly_mod_sub          |- !r. Ring r ==> !p q z. poly p /\ poly q /\ ulead z ==>
                                     ((p - q) % z = (p % z - q % z) % z)
   poly_mod_mult         |- !r. Ring r ==> !p q z. poly p /\ poly q /\ ulead z ==>
                                     ((p * q) % z = (p % z * q % z) % z)
   poly_mod_mult_assoc   |- !r. Ring r ==> !p q t z. poly p /\ poly q /\ poly t /\ ulead z ==>
                                     (((p * q) % z * t) % z = (p * (q * t) % z) % z)
   poly_mod_cmult        |- !r. Ring r ==> !p z. poly p /\ ulead z ==>
                            !c. c IN R ==> ((c * p) % z = (c * p % z) % z)
   poly_mod_eq_zero      |- !r. Ring r ==> !p z. poly p /\ ulead z ==>
                                     ((p % z = |0|) <=> ?q. poly q /\ (p = q * z))

   Polynomial Modulo Equivalence:
#  pmod_def              |- !r z p. pmod r z p = p % z
   pmod_def_alt          |- !p q z. (p == q) (pm z) <=> (p % z = q % z)
   poly_mod_reflexive    |- !r p z. (p == p) (pm z)
   poly_mod_symmetric    |- !r p q z. (p == q) (pm z) ==> (q == p) (pm z)
   poly_mod_transitive   |- !r p q t z. (p == q) (pm z) /\ (q == t) (pm z) ==> (p == t) (pm z)
   poly_mod_eq_eq        |- !r z p q u v. (p == q) (pm z) /\ (p == u) (pm z) /\ (q == v) (pm z) ==> (u == v) (pm z)
   poly_mod_equiv        |- !r z. (\x y. (x == y) (pm z)) equiv_on univ(:'a poly)
   poly_mod_equiv_on_poly_ring
                         |- !r z. (\x y. (x == y) (pm z)) equiv_on (PolyRing r).carrier

   pmod_mod    |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (p % z == p) (pm z)
   pmod_neg    |- !r. Ring r ==> !p1 p2 z. poly p1 /\ poly p2 /\ ulead z ==>
                                 ((p1 == p2) (pm z) <=> (-p1 == -p2) (pm z))
   pmod_add    |- !r. Ring r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\ ulead z ==>
                                 (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 + q1 == p2 + q2) (pm z)
   pmod_cmult  |- !r. Ring r ==> !p1 p2 z. poly p1 /\ poly p2 /\ ulead z ==>
                  !c. c IN R ==> (p1 == p2) (pm z) ==> (c * p1 == c * p2) (pm z)
   pmod_mult   |- !r. Ring r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\ ulead z ==>
                                 (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 * q1 == p2 * q2) (pm z)

   Polynomial Modulo Theorems:
   poly_mod_of_zero  |- !r. Ring r ==> !z. ulead z ==> ([] % z = |0|)
   poly_mod_zero     |- !r. Ring r ==> !z. ulead z ==> ( |0| % z = |0|)
#  poly_mod_one      |- !r. Ring r ==> !z. pmonic z ==> ( |1| % z = |1|)
   poly_mod_one_all  |- !r. Ring r ==> !z. ulead z ==> ( |1| % z = if deg z = 0 then |0| else |1|)
   poly_mod_exp      |- !r. Ring r ==> !p z. poly p /\ ulead z ==> !n. p ** n % z = (p % z) ** n % z
   poly_mod_eq       |- !r z. Ring r /\ ulead z ==>
                        !p q. poly p /\ poly q ==> ((p % z = q % z) <=> ((p - q) % z = |0|))
   poly_mod_eq_alt   |- !r z. Ring r /\ ulead z ==>
                        !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> (p - q) % z = |0|)
   poly_mod_eq_divisor    |- !r z h. Ring r /\ ulead z /\ ulead h /\ (z % h = |0|) ==>
                             !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (p == q) (pm h)
   poly_deg_mod_less      |- !r p q. Ring r /\ poly p /\ pmonic q ==> deg (p % q) < deg q
   poly_div_eq_zero       |- !r. Ring r ==> !p q. poly p /\ pmonic q ==> ((p / q = |0|) <=> deg p < deg q)
   poly_div_multiple_alt  |- !r. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
                                                (p / z * z = p) /\ (z * (p / z) = p)
   poly_ulead_cmult_eq        |- !r. Ring r ==> !p q c. poly p /\ poly q /\ unit c ==>
                                                ((c * p = c * q) <=> (p = q))
   poly_ulead_mult_rcancel    |- !r. Ring r ==> !p q t. ulead p /\ poly q /\ poly t ==>
                                                ((q * p = t * p) <=> (q = t))
   poly_ulead_mult_lcancel    |- !r. Ring r ==> !p q t. ulead p /\ poly q /\ poly t ==>
                                                ((p * q = p * t) <=> (q = t))
   poly_eval_poly_mod_at_root |- !r. Ring r ==> !p q. poly p /\ ulead q ==>
                                 !x. x IN roots q ==> (eval (p % q) x = eval p x)

*)
(* ------------------------------------------------------------------------- *)
(* Division for Polynomials over a Ring.                                     *)
(* ------------------------------------------------------------------------- *)

(*
For polynomials over a Ring, division is not always possible.
However, if the leading coefficient is invertible, division is possible.
These are called pseudo-monic polynomials: pmonic p = poly p /\ 0 < deg p /\ unit (lead p).
This is especially true for monic polynomials, with leading coefficient #1, when the Ring has #1 <> #0.
The only monic polynomial that is not pmonic is |1|.
The requirement of 0 < deg p is to allow for a remainder with degree < deg p.
*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Division (when unit (lead q))                                  *)
(* ------------------------------------------------------------------------- *)

(*
Note: In R[x], polynomial division is not always possible. An example:
In Z_6, 2*0 = 0, 2*1 = 2, 2*2 = 4, 2*3 = 0, 2*4 = 2, 2*5 = 4.
Hence (2x + 1) cannot divide into (5x^2 + 1), as the leading 5x^2 cannot be eliminated.
In Z_6, the units are: 1, 5, those coprime with 6.
Hence p divides q is meaningful only for q with unit leading coefficient.
*)

(* overload monic-like polynomial, with invertible lead, as divisor of division. *)
val _ = overload_on ("ulead", ``\z. poly z /\ unit (lead z)``);
(* Note: just require unit (lead z) to get successive coefficients of quotient. *)

(* overload monic-like polynomial with positive degree, as divisor of division. *)
val _ = overload_on ("pmonic", ``\z. poly z /\ unit (lead z) /\ 0 < deg z``);
(* Note: just require unit (lead z) to get successive coefficients of quotient. *)

(* Theorem: poly p /\ pmonic q ==> ?s t. p = s * q + t  with deg t < deg q *)
(* Proof: by complete induction on deg p.
   Let n = deg p.
   Step case: !n' p q. n' < n /\ n' = deg p /\ 0 < deg q /\ unit (lead q) ==> ?s t. p = s * q + t  /\ deg t < deg q ==>
              n = deg p /\ 0 < deg q /\ unit (lead q) ==> ?s t. poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q
      If deg p < deg q,
         take s = |0|, t = p.
      If deg q <= deg p,
         Since unit (lead q), unit ( |/ (lead q)), or |/ (lead q) IN R   by ring_unit_inv_element
         Consider  p - u, where u = (lead p) * |/ (lead q) * (q >> (deg p - deg q))
         Since deg p = deg ((lead p) * |/ (lead q) * (q >> (deg p - deg q))) by poly_deg_shift_equal
         Then  deg (p - u) < deg p
         Take n' = deg t, n = deg p, apply complete induction hypothesis
         ? s t. (p - u) = s * q + t   with deg u < deg q
         Hence  s * q + t = p - (lead p) * |/ (lead q) * (q >> (deg p - deg q))
         or p = (lead p) * |/ (lead q) * (q >> (deg p - deg q)) + s * q + t
              = ((lead p) * |/ (lead q) * q) >> (deg p - deg q) + s * q + t       by poly_cmult_shift
              = ([lead p) * |/ (lead q)] * q) >> (deg p - deg q) + s * q + t      by poly_mult_lconst
              = ([lead p) * |/ (lead q)] >> (deg p - deg q) * q + s * q + t       by poly_mult_shift_comm
              = ((lead p) * |/ (lead q) * ([#1] >> (deg p - deg q)) + s) * q + t
         Giving the required quotient and remainder.
*)
val poly_division_eqn = store_thm(
  "poly_division_eqn",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ pmonic q ==>
    ?s t. poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q``,
  rpt strip_tac >>
  completeInduct_on `deg p` >>
  rpt strip_tac >>
  `q <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
  Cases_on `deg p < deg q` >| [
    qexists_tac `|0|` >>
    qexists_tac `p` >>
    rw[],
    `deg q <= deg p /\ 0 < deg p` by decide_tac >>
    `p <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
    `lead p IN R /\ lead q IN R /\ lead p <> #0 /\ lead q <> #0` by rw[] >>
    `|/ (lead q) IN R` by metis_tac[ring_unit_inv_element] >>
    `(lead p) * |/ (lead q) IN R` by rw[] >>
    (`poly (q >> (deg p - deg q)) /\ q >> (deg p - deg q) <> |0|` by rw[poly_shift_eq_zero]) >>
    (`?u. (u = (lead p) * |/ (lead q) * q >> (deg p - deg q)) /\ poly u` by rw[]) >>
    (`deg (q >> (deg p - deg q)) = deg p` by rw[poly_deg_shift_equal]) >>
    (`lead (q >> (deg p - deg q)) = lead q` by rw[]) >>
    `(lead p) * |/ (lead q) * lead q = lead p` by rw_tac std_ss[ring_mult_assoc, ring_unit_linv, ring_mult_rone] >>
    `deg u = deg p` by metis_tac[poly_deg_shift_equal, weak_deg_cmult_nonzero, poly_is_weak] >>
    `lead u = lead p` by rw_tac std_ss[weak_lead_cmult_nonzero, poly_is_weak] >>
    `deg (p - u) < deg p` by metis_tac[poly_deg_eq_lead_sub] >>
    `poly (p - u)` by rw[] >>
    `?s t. ((p - u) = s * q + t) /\ poly s /\ poly t /\ (deg t < deg q)` by metis_tac[] >>
    `(lead p) * |/ (lead q) <> #0` by metis_tac[ring_unit_mult_zero, ring_mult_comm] >>
    `poly [(lead p) * |/ (lead q)]` by rw[] >>
    (`u = ((lead p) * |/ (lead q) * q) >> (deg p - deg q)` by rw[poly_cmult_shift]) >>
    (`_ = ([(lead p) * |/ (lead q)] * q) >> (deg p - deg q)` by rw_tac std_ss[poly_mult_lconst]) >>
    (`_ = ([(lead p) * |/ (lead q)] >> (deg p - deg q)) * q` by metis_tac[poly_mult_shift_comm]) >>
    (`?w. (w = [(lead p) * |/ (lead q)] >> (deg p - deg q)) /\ poly w` by rw[]) >>
    `p = w * q + (s * q + t)` by metis_tac[poly_sub_eq_add] >>
    `_ = (w + s) * q + t` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_mult_ladd] >>
    qexists_tac `w + s` >>
    qexists_tac `t` >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Division - for all divisor q with unit (lead q)                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ poly p /\ ulead q ==>
    ?s t. poly s /\ poly t /\ (p = s * q + t) /\
          (if 0 < deg q then deg t < deg q else t = |0|) *)
(* Proof:
   If deg q > 0,
      Take s and t         by poly_division_eqn
   If deg q = 0,
      This is to show: ?s. poly s /\ p = s * q + |0|.
      If q = |0|,
         Then unit #0      by poly_lead_zero
           so #1 = #0      by ring_unit_zero
           or |1| = |0|    by poly_one_eq_poly_zero
          ==> p = |0|      by poly_one_eq_zero
         Take any poly s, the equality is trivial.
      If q <> |0|,
         Then ?c. c IN R /\ (q = [c])    by poly_deg_eq_0
           so unit c                     by poly_lead_const
          and |/c IN R                   by ring_unit_inv_element
      Take s = ( |/c) * p,
           the equality follows          by poly_cmult_unit_eqn
*)
val poly_division_all_eqn = store_thm(
  "poly_division_all_eqn",
  ``!r:'a ring p q. Ring r /\ poly p /\ ulead q ==>
    ?s t. poly s /\ poly t /\ (p = s * q + t) /\
    (if 0 < deg q then deg t < deg q else t = |0|)``,
  rpt strip_tac >>
  Cases_on `0 < deg q` >-
  metis_tac[poly_division_eqn] >>
  simp[] >>
  `deg q = 0` by decide_tac >>
  Cases_on `q = |0|` >| [
    `#1 = #0` by fs[GSYM ring_unit_zero] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mult_rzero, poly_add_rzero, poly_zero],
    `?c. c IN R /\ (q = [c])` by metis_tac[poly_deg_eq_0] >>
    `unit c /\ |/c IN R` by metis_tac[poly_lead_const, ring_unit_inv_element] >>
    metis_tac[poly_cmult_unit_eqn, poly_cmult_poly, poly_zero]
  ]);

(* Define polynomial quotient and remainder *)

(* Theorem: Convert this existence into quotient and remainder operators. *)
(* Proof: by poly_division_all_eqn *)
val poly_division_all_lemma = prove(
  ``!(r:'a ring) p q. ?s t. Ring r /\ poly p /\ ulead q ==>
      poly s /\ poly t /\ (p = s * q + t) /\
      (if 0 < deg q then deg t < deg q else t = |0|)``,
  rpt strip_tac >>
  Cases_on `0 < deg q` >>
  metis_tac[poly_division_all_eqn]);
(* Apply Skolemization *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val poly_div_mod_all_def = new_specification(
  "poly_div_mod_all_def",
  ["poly_div", "poly_mod"],
  SIMP_RULE (bool_ss) [SKOLEM_THM] poly_division_all_lemma
            |> CONV_RULE (RENAME_VARS_CONV ["pdiv", "pmod"]));
(* use bool_ss to keep |0|.
val poly_div_mod_all_def =
   |- !r p q. Ring r /\ poly p /\ ulead q ==>
          poly (poly_div r p q) /\ poly (poly_mod r p q) /\
          p = poly_div r p q * q + poly_mod r p q /\
          if 0 < deg q then deg (poly_mod r p q) < deg q
          else poly_div r p q = |0|: thm

*)


(* Replace original poly_div_mod_def by a theorem *)

(* Theorem: Ring r /\ poly p /\ pmonic q ==>
            poly (poly_div r p q) /\ poly (poly_mod r p q) /\
            (p = poly_div r p q * q + poly_mod r p q) /\ deg (poly_mod r p q) < deg q *)
(* Proof: by poly_div_mod_all_def *)
val poly_div_mod_def = store_thm(
  "poly_div_mod_def",
  ``!r:'a ring p q. Ring r /\ poly p /\ pmonic q ==>
         poly (poly_div r p q) /\ poly (poly_mod r p q) /\
         (p = poly_div r p q * q + poly_mod r p q) /\ deg (poly_mod r p q) < deg q``,
  metis_tac[poly_div_mod_all_def]);

(* Overload on polynomial quotient and remainder *)
val _ = overload_on ("/", ``poly_div r``);
val _ = overload_on ("%", ``poly_mod r``);

val _ = set_fixity "/" (Infixl 600);
val _ = set_fixity "%" (Infixl 650);
(*
- poly_div_mod_def;
> val it = |- !r p q. Ring r /\ poly p /\ pmonic q ==>
         poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q : thm
*)


(* Theorem: poly (p / q) *)
val poly_div_poly = save_thm("poly_div_poly",
  poly_div_mod_all_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val poly_div_poly =  |- !r q p. Ring r /\ poly p /\ ulead q ==> poly (p / q) : thm *)

(* Theorem: poly (p % q) *)
val poly_mod_poly = save_thm("poly_mod_poly",
  poly_div_mod_all_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(*  val poly_mod_poly = |- !r q p. Ring r /\ poly p /\ ulead q ==> poly (p % q) : thm *)

(* export simple results *)
val _ = export_rewrites ["poly_div_poly", "poly_mod_poly"];

(* Theorem: p = p / q * q + p % q /\ if 0 < deg q then deg (p % q) < deg q else p % q = |0| *)
val poly_division_alg = save_thm("poly_division_alg",
  poly_div_mod_all_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val poly_division_alg = |- !r q p. Ring r /\ poly p /\ ulead q ==>
         p = p / q * q + p % q /\ if 0 < deg q then deg (p % q) < deg q else p % q = |0|: thm
*)


(* Theorem: Ring r /\ poly p /\ pmonic q ==>
            (p = p / q * q + p % q) /\ deg (p % q) < deg q *)
(* Proof: by poly_div_mod_def *)
val poly_division = store_thm(
  "poly_division",
  ``!r:'a ring p q. Ring r /\ poly p /\ pmonic q ==>
        (p = p / q * q + p % q) /\ deg (p % q) < deg q``,
  rw[poly_div_mod_def]);

(* Theorem: Ring r /\ poly p /\ ulead q ==>
            (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q) *)
(* Proof: by poly_division_alg, poly_div_poly, poly_mod_poly *)
val poly_division_all = store_thm(
  "poly_division_all",
  ``!r:'a ring p q. Ring r /\ poly p /\ ulead q ==>
       (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q)``,
  rw[poly_division_alg]);

(* Theorem: Uniqueness of quotient and remainder:
            (p = s1 * q + t1) /\ deg t1 < deg q
            (p = s2 * q + t2) /\ deg t2 < deg q  ==> (s1 = s2) /\ (t1 = t2) *)
(* Proof:
     s1 * q + t1 = s2 * q + t2   by equating p
     s1 * q - s2 * q = t2 - t1   by poly_add_eq_sub
       (s1 - s2) * q = t2 - t1   by poly_mult_lsub

   If s1 = s2, then
             |0| * q = t2 - t1   by poly_sub_eq_zero
                 |0| = t2 - t1   by poly_mult_lzero
                  t1 = t2        by poly_sub_eq_zero
   If s1 <> s2, then
      s1 - s2 <> |0|, also q <> |0|   as deg t1 < deg q
      deg (s1 - s2) * q = deg (s1 - s2) + deg q    by poly_deg_mult_nonzero, (s1 - s2) <> |0|, q <> |0|
                        >= deg q
   but deg (t2 - t1) <= MAX (deg t2) (deg t1)      by poly_deg_sub
                      < deg q                      since deg t1 < deg q and deg t2 < deg q
   This contradicts (s1 - s2) * q = t2 - t1.
*)
val poly_div_mod_unique = store_thm(
  "poly_div_mod_unique",
  ``!r:'a ring. Ring r ==> !p q s1 t1 s2 t2. poly p /\ ulead q /\
           poly s1 /\ poly t1 /\ poly s2 /\ poly t2 /\
           (p = s1 * q + t1) /\ deg t1 < deg q /\
           (p = s2 * q + t2) /\ deg t2 < deg q  ==> (s1 = s2) /\ (t1 = t2)``,
  ntac 9 strip_tac >>
  `(s1 * q + t1 = s2 * q + t2) <=> (s1 * q - s2 * q = t2 - t1)` by rw[poly_add_eq_sub] >>
  `t2 - t1 = s1 * q - s2 * q` by metis_tac[] >>
  `_ = (s1 - s2) * q` by rw[poly_mult_lsub] >>
  `deg (t2 - t1) <= MAX (deg t2) (deg t1)` by rw[poly_deg_sub] >>
  `MAX (deg t2) (deg t1) < deg q` by rw[] >>
  `deg (t2 - t1) < deg q` by decide_tac >>
  Cases_on `s1 = s2` >-
  metis_tac[poly_sub_eq_zero, poly_mult_lzero] >>
  `poly (s1 - s2) /\ s1 - s2 <> |0|` by rw[poly_sub_eq_zero] >>
  Cases_on `lead (s1 - s2) * lead q = #0` >| [
    `lead (s1 - s2) IN R` by rw[] >>
    `lead (s1 - s2) = #0` by metis_tac[ring_unit_mult_zero, ring_unit_element, ring_mult_comm] >>
    metis_tac[poly_lead_nonzero],
    `deg ((s1 - s2) * q) = deg (s1 - s2) + deg q` by metis_tac[weak_deg_mult_nonzero, poly_is_weak] >>
    `deg (t2 - t1) <> deg ((s1 - s2) * q)` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: Uniqueness of quotient and remainder:
            (p = s * q + t) /\ deg t < deg q ==> (s = p /q) /\ (t = p % q) *)
(* Proof: by poly_div_mod_def and poly_div_mod_unique. *)
val poly_div_mod_eqn = store_thm(
  "poly_div_mod_eqn",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ ulead q /\ poly s /\ poly t /\
     (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t)``,
  ntac 7 strip_tac >>
  `0 < deg q` by decide_tac >>
  `(p = (p / q) * q + (p % q)) /\ deg (p % q) < deg q /\ poly (p / q) /\ poly (p % q)` by rw_tac std_ss[poly_div_mod_def] >>
  metis_tac[poly_div_mod_unique]);

(* Theorem: Uniqueness of p / q *)
(* Proof: by poly_div_mod_eqn. *)
val poly_div_unique = store_thm(
  "poly_div_unique",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ ulead q /\
    poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q ==> (p / q = s)``,
  metis_tac[poly_div_mod_eqn]);

(* Theorem: Uniqueness of p % q *)
(* Proof: by poly_div_mod_eqn. *)
val poly_mod_unique = store_thm(
  "poly_mod_unique",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ ulead q /\
    poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q ==> (p % q = t)``,
  metis_tac[poly_div_mod_eqn]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Quotient and Remainder -- constant divisor                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If deg z = 0, p % z = p *)
(* Proof: by poly_div_mod_all_def *)
val poly_mod_by_const = store_thm(
  "poly_mod_by_const",
  ``!r:'a ring. Ring r ==>
   !p z. poly p /\ ulead z /\ (deg z = 0) ==> (p % z = |0|)``,
  metis_tac[poly_div_mod_all_def, NOT_ZERO]);

(* Theorem: If deg z = 0, p / z = ( |/(lead z)) * p *)
(* Proof:
   Note |/(lead z) IN R           by ring_unit_inv_element
    and poly (p / z)              by poly_div_poly
    and poly ( |/(lead z) * p)    by poly_cmult_poly
   If z = |0|,
      Then unit #0                by poly_lead_zero
        so #1 = #0                by ring_unit_zero
        or |1| = |0|              by poly_one_eq_poly_zero
      Thus p / z = |0|            by poly_one_eq_zero
       and |/(lead z) * p = |0|   by poly_one_eq_zero
        so both are equal.
   If z <> |0|,
      Then ?c. c IN R /\ (z = [c])               by poly_deg_eq_0
       and c = lead z                            by poly_lead_const
      Thus p / z  = #1 * (p / z)                 by poly_cmult_lone
                  = ( |/c * c) * (p / z)         by ring_unit_linv
                  = |/c * (c * (p / z))          by poly_cmult_cmult
                  = |/c * ((p / z) * [c])        by poly_mult_rconst
                  = |/c * ((p / z) * z)          by z = [c]
                  = |/c * ((p / z) * z + p % z)  by poly_mod_by_const, p % z = |0|
                  = |/c * p                      by poly_division_all
                  = |/(lead z) * p               by c = lead z
*)
val poly_div_by_const = store_thm(
  "poly_div_by_const",
  ``!r:'a ring. Ring r ==>
   !p z. poly p /\ ulead z /\ (deg z = 0) ==> (p / z = ( |/(lead z)) * p)``,
  rpt strip_tac >>
  `|/(lead z) IN R` by rw[ring_unit_inv_element] >>
  `poly (p / z)` by rw[] >>
  `poly ( |/(lead z) * p)` by rw[ring_unit_inv_element] >>
  Cases_on `z = |0|` >| [
    `#1 = #0` by fs[GSYM ring_unit_zero] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero],
    `?c. c IN R /\ (z = [c])` by metis_tac[poly_deg_eq_0] >>
    `c = lead z` by rw[poly_lead_const] >>
    `p / z  = #1 * (p / z)` by rw[] >>
    `_ = ( |/c * c) * (p / z)` by rw[ring_unit_linv] >>
    `_ = |/c * (c * (p / z))` by rw[poly_cmult_cmult] >>
    `_ = |/c * ((p / z) * [c])` by rw[poly_mult_rconst] >>
    `_ = |/c * ((p / z) * z)` by rfs[] >>
    `_ = |/c * ((p / z) * z + p % z)` by rw[poly_mod_by_const] >>
    metis_tac[poly_division_all]
  ]);

(* Theorem: If deg z = 0, p / z = |0| /\ p % z = p *)
(* Proof: by poly_div_by_const, poly_mod_by_const *)
val poly_div_mod_by_const = store_thm(
  "poly_div_mod_by_const",
  ``!r:'a ring. Ring r ==>
   !p z. poly p /\ ulead z /\ (deg z = 0) ==>
         (p / z = ( |/(lead z)) * p) /\ (p % z = |0|)``,
  metis_tac[poly_div_by_const, poly_mod_by_const]);

(* Theorem: Ring r /\ poly p ==> (p / |1| = p) /\ (p % |1| = |0|) *)
(* Proof:
   Note poly |1|                by poly_one_poly
    and lead |1| = #1           by poly_lead_one
    and unit #1                 by ring_unit_one
    and deg |1| = 0             by poly_deg_one
   Thus p / |1| = ( |/#1) * p   by poly_div_mod_by_const
                = #1 * p        by ring_inv_one
                = p             by poly_cmult_lone
    and p / |1| = |0|           by poly_div_mod_by_const
*)
val poly_div_mod_by_one = store_thm(
  "poly_div_mod_by_one",
  ``!r:'a ring p. Ring r /\ poly p ==> (p / |1| = p) /\ (p % |1| = |0|)``,
  ntac 3 strip_tac >>
  `poly |1| /\ (lead |1| = #1) /\ unit #1 /\ (deg |1| = 0)` by rw[] >>
  `|/ #1 = #1` by rw[ring_inv_one] >>
  metis_tac[poly_div_mod_by_const, poly_cmult_lone]);

(* Extract Theorems *)
val poly_div_by_one = save_thm("poly_div_by_one",
    poly_div_mod_by_one |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* val poly_div_by_one = |- !r p. Ring r /\ poly p ==> p / |1| = p: thm *)
val poly_mod_by_one = save_thm("poly_mod_by_one",
    poly_div_mod_by_one |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* val poly_mod_by_one = |- !r p. Ring r /\ poly p ==> p % |1| = |0|: thm *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Quotient and Remainder -- non-constant divisor                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If deg p < deg z, p / z = |0| /\ p % z = p *)
(* Proof:
   Since p = |0| * z + p,
   this follows by poly_div_mod_eqn.
*)
val poly_div_mod_less = store_thm(
  "poly_div_mod_less",
  ``!r:'a ring. Ring r ==>
    !p z. poly p /\ ulead z /\ deg p < deg z ==> (p / z = |0|) /\ (p % z = p)``,
  ntac 5 strip_tac >>
  `p = |0| * z + p` by rw[] >>
  metis_tac[poly_div_mod_eqn, poly_zero_poly]);

(* Theorem: If deg p < deg z, p / z = |0| *)
val poly_div_less = save_thm("poly_div_less",
  poly_div_mod_less |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
     |> DISCH ``poly p /\ ulead z /\ deg p < deg z``
     |> GEN ``z:'a poly`` |> GEN ``p:'a poly``
     |> DISCH_ALL |> GEN_ALL);
(* > val poly_div_less = |- !r. Ring r ==> !p z. poly p /\ ulead z /\ deg p < deg z ==> (p / z = |0|) : thm *)

(* Theorem: If deg p < deg z, p % z = p *)
val poly_mod_less = save_thm("poly_mod_less",
  poly_div_mod_less |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
     |> DISCH ``poly p /\ ulead z /\ deg p < deg z``
     |> GEN ``z:'a poly`` |> GEN ``p:'a poly``
     |> DISCH_ALL |> GEN_ALL);
(* > val poly_mod_less = |- !r. Ring r ==> !p z. poly p /\ ulead z /\ deg p < deg z ==> (p % z = p) : thm *)

(* Theorem: ulead z ==> |0| / z = |0| /\ |0| % z = |0| *)
(* Proof:
   If deg z = 0,
      Then |0| / z = |/(lead z) * |0|     by poly_div_by_const
                   = |0|                  by poly_cmult_zero
       and |0| % z = |0|                  by poly_mod_by_const
   Otherwise, 0 < deg z.
       Since deg |0| = 0                  by poly_deg_zero
       This follows                       by poly_div_mod_less.
*)
val poly_zero_div_mod = store_thm(
  "poly_zero_div_mod",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> ( |0| / z = |0|) /\ ( |0| % z = |0|)``,
  ntac 4 strip_tac >>
  Cases_on `deg z = 0` >-
  rw[poly_div_mod_by_const] >>
  rw[poly_div_mod_less]);

(* Theorem: ulead z ==> |0| / z = |0| *)
val poly_zero_div = save_thm("poly_zero_div",
  poly_zero_div_mod |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
     |> DISCH ``ulead z``
     |> GEN ``z:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_zero_div = |- !r. Ring r ==> !z. ulead z ==> ( |0| / z = |0|) : thm *)

(* Theorem: ulead z ==> |0| % z = |0| *)
val poly_zero_mod = save_thm("poly_zero_mod",
  poly_zero_div_mod |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
     |> DISCH ``ulead z``
     |> GEN ``z:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_zero_mod = |- !r. Ring r ==> !z. ulead z ==> ( |0| % z = |0|) : thm *)

(* export simple result *)
val _ = export_rewrites ["poly_zero_div"];
val _ = export_rewrites ["poly_zero_mod"];

(* Theorem: poly p /\ ulead z ==> (p % z) % z = p % z *)
(* Proof:
   If deg z = 0,
      Then (p % z) % z
         = |0| % z            by poly_mod_by_const
         = |0|                by poly_mod_by_const
   Otherwise 0 < deg z.
      Since deg (p % z) < deg z,
      this follows            by poly_mod_less
*)
val poly_mod_mod = store_thm(
  "poly_mod_mod",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==> ((p % z) % z = p % z)``,
  rpt strip_tac >>
  Cases_on `deg z = 0` >-
  rw[poly_mod_by_const] >>
  rw[poly_division, poly_mod_less]);

(* Theorem: [c] / z = |0| and [c] % z = [c] *)
(* Proof:
   Note  poly [c]     by poly_nonzero_element_poly
   and   deg [c] = 0  by poly_deg_cons
   Since [c] = |0| * z + [c],
   hence [c] /z = |0| and [c] % z = [c] by poly_div_mod_eqn
*)
val poly_div_mod_const = store_thm(
  "poly_div_mod_const",
  ``!r:'a ring. Ring r ==> !z. pmonic z ==>
   !c. c IN R /\ c <> #0 ==> (([c] / z = |0|) /\ ([c] % z = [c]))``,
  ntac 6 strip_tac >>
  `poly [c] /\ (deg [c] = 0)` by rw[] >>
  `[c] = |0| * z + [c]` by rw[] >>
  metis_tac[poly_div_mod_eqn, poly_zero_poly]);

(* export simple result *)
val _ = export_rewrites ["poly_div_mod_const"];

(* Theorem: [c] / z = |0| *)
(* Proof: by poly_div_mod_const. *)
val poly_div_const = save_thm("poly_div_const",
    poly_div_mod_const |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
                       |> DISCH ``c IN R /\ c <> #0`` |> GEN_ALL
                       |> DISCH ``pmonic z`` |> GEN_ALL
                       |> DISCH_ALL |> GEN_ALL);
(* > val poly_div_const = |- !r. Ring r ==> !z. pmonic z ==>
                             !c. c IN R /\ c <> #0 ==> ([c] / z = |0|) : thm *)

(* Theorem: [c] % z = [c] *)
(* Proof: by poly_div_mod_const. *)
val poly_mod_const = save_thm("poly_mod_const",
    poly_div_mod_const |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
                       |> DISCH ``c IN R /\ c <> #0`` |> GEN_ALL
                       |> DISCH ``pmonic z`` |> GEN_ALL
                       |> DISCH_ALL |> GEN_ALL);
(* > val poly_mod_const = |- !r. Ring r ==> !z. pmonic z ==>
                             !c. c IN R /\ c <> #0 ==> ([c] % z = [c]) : thm *)

(* Theorem: poly p /\ ulead z ==> (- p) / z = - (p / z) /\ (- p) % z = - (p % z) *)
(* Proof:
   If deg z = 0,
      Note |/(lead z) IN R               by ring_unit_inv_element
      Then -p / z = |/(lead z) * (-p)    by poly_div_by_const
                  = - |/(lead z) * p     by poly_cmult_neg
                  = - ( |/(lead z) * p)  by poly_neg_cmult
                  = - (p / z)            by poly_div_by_const
       and -p % z = |0|                  by poly_mod_by_const
                  = -|0|                 by poly_neg_zero
                  = -(p % z)             by poly_mod_by_const
   Otherwise 0 < deg z.
   Note  deg (p % z) < deg z /\
          p = (p / z) * z + (p % z)                    by poly_div_mod_def
   then  -p = -((p / z) * z + (p % z))
            = -(p /z ) * z + (- (p % z))               by poly_neg_add
            = (-(p / z)) * z + ((-p) % z)              by poly_mult_lneg
   hence (-p) / z = - (p/z) and (-p) % z = - (p % z)   by poly_div_mod_eqn
*)
val poly_div_mod_neg = store_thm(
  "poly_div_mod_neg",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==>
    (((- p) / z = - (p / z)) /\ ((- p) % z = - (p % z)))``,
  ntac 5 strip_tac >>
  `poly (p / z) /\ poly (p % z)` by rw[] >>
  Cases_on `deg z = 0` >| [
    `|/(lead z) IN R` by rw[ring_unit_inv_element] >>
    `-p / z = |/(lead z) * (-p)` by rw[poly_div_by_const] >>
    `_ = - |/(lead z) * p` by rw[] >>
    `_ = - ( |/(lead z) * p)` by rw[] >>
    `_ = - (p / z)` by rw[poly_div_by_const] >>
    `-p % z = |0|` by rw[poly_mod_by_const] >>
    `_ = -|0|` by rw[] >>
    `_ = -(p % z)` by rw[poly_mod_by_const] >>
    simp[],
    `0 < deg z` by decide_tac >>
    `deg (p % z) < deg z /\ (- p = - ((p / z) * z + (p % z)))` by metis_tac[poly_div_mod_def] >>
    `_ = ((- (p / z)) * z) + (-(p % z))` by rw[] >>
    metis_tac[poly_div_mod_eqn, poly_deg_neg, poly_neg_poly]
  ]);

(* Theorem: poly p /\ ulead z ==> (- p) / z = - (p / z) *)
(* Proof: by poly_div_mod_neg. *)
val poly_div_neg = save_thm("poly_div_neg",
    poly_div_mod_neg |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
                      |> DISCH ``poly p /\ ulead z``
                      |> GEN ``z:'a poly`` |> GEN ``p:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_div_neg = |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (-p / z = -(p / z)) : thm *)

(* Theorem: poly p /\ ulead z ==> (- p) % z = - (p % z) *)
(* Proof: by poly_div_mod_neg. *)
val poly_mod_neg = save_thm("poly_mod_neg",
    poly_div_mod_neg |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
                      |> DISCH ``poly p /\ ulead z``
                      |> GEN ``z:'a poly`` |> GEN ``p:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_mod_neg = |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (-p % z = -(p % z)) : thm *)

(* Theorem: poly p /\ ulead z ==> (p * z) / z = p /\ (p * z) % z = |0| *)
(* Proof:
   If deg z = 0,
      Note |/(lead z) IN R        by ring_unit_inv_element
       and (p * z) % z = |0|      by poly_mod_by_const
      If z = |0|,
         Then unit #0             by poly_lead_zero
          ==> #1 = #0             by ring_unit_zero
          ==> |1| = |0|           by poly_one_eq_poly_zero
         Thus (p * z) / z
            = |0| = p             by poly_one_eq_zero
      If z <> |0|,
         Then ?c. c IN R /\ c <> #0 /\ (z = [c])
                                     by poly_deg_eq_0, z <> |0|
          and lead z = c             by poly_lead_const
         Thus (p * z) / z
            = |/(lead z) * (p * z)   by poly_div_by_const
            = ( |/c * p) * [c]       by lead z = c, z = [c]
            = c * ( |/c * p)         by poly_mult_rconst
            = (c * |/c) * p          by poly_cmult_cmult
            = #1 * p                 by ring_unit_rinv
            = p                      by poly_cmult_lone

   Otherwise 0 < deg z.
   Since p * z = p * z + |0|   by poly_add_rzero
   The result follows          by poly_div_mod_eqn, 0 < deg z
*)
val poly_div_mod_multiple = store_thm(
  "poly_div_mod_multiple",
  ``!r:'a ring. Ring r ==>
   !p z. poly p /\ ulead z ==> ((p * z) / z = p) /\ ((p * z) % z = |0|)``,
  ntac 5 strip_tac >>
  Cases_on `deg z = 0` >| [
    `|/(lead z) IN R` by rw[ring_unit_inv_element] >>
    `(p * z) % z = |0|` by rw[poly_mod_by_const] >>
    Cases_on `z = |0|` >| [
      `unit #0` by fs[] >>
      `#1 = #0` by rw[GSYM ring_unit_zero] >>
      `|1| = |0|` by rw[poly_one_eq_poly_zero] >>
      metis_tac[poly_one_eq_zero, poly_mult_poly, poly_div_poly],
      `?c. c IN R /\ c <> #0 /\ (z = [c])` by rw[GSYM poly_deg_eq_0] >>
      `lead z = c` by rw[] >>
      `(p * z) / z = |/(lead z) * (p * z)` by rw[poly_div_by_const] >>
      `_ = ( |/c * p) * [c]` by fs[] >>
      `_ = c * ( |/c * p)` by rw[GSYM poly_mult_rconst] >>
      `_ = (c * |/c) * p` by rw[poly_cmult_cmult] >>
      `_ = #1 * p` by rw[ring_unit_rinv] >>
      `_ = p` by rw[] >>
      simp[]
    ],
    `0 < deg z` by decide_tac >>
    `p * z = p * z + |0|` by rw[] >>
    `poly (p * z) /\ poly |0|/\ (deg |0| = 0)` by rw[] >>
    metis_tac[poly_div_mod_eqn]
  ]);

(* Theorem: poly p /\ ulead z ==> (p * z) / z = p *)
(* Proof: by poly_div_mod_multiple. *)
val poly_div_multiple = save_thm("poly_div_multiple",
    poly_div_mod_multiple |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1
                      |> DISCH ``poly p /\ ulead z``
                      |> GEN ``z:'a poly`` |> GEN ``p:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_div_multiple = |- !r. Ring r ==> !p z. poly p /\ ulead z ==> (p * z / z = p) : thm *)

(* Theorem: poly p /\ ulead z ==> (p * z) % z = |0| *)
(* Proof: by poly_div_mod_multiple. *)
val poly_mod_multiple = save_thm("poly_mod_multiple",
    poly_div_mod_multiple |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2
                      |> DISCH ``poly p /\ ulead z``
                      |> GEN ``z:'a poly`` |> GEN ``p:'a poly`` |> DISCH_ALL |> GEN_ALL);
(* > val poly_mod_multiple = |- !r. Ring r ==> !p z. poly p /\ ulead z ==> ((p * z) % z = |0|) : thm *)

(* Theorem: poly p /\ ulead z ==> (z * p) / z = p *)
(* Proof: by poly_div_multiple and poly_mult_comm. *)
val poly_div_multiple_comm = store_thm(
  "poly_div_multiple_comm",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==> (z * p / z = p)``,
  rw[poly_div_multiple, poly_mult_comm]);

(* Theorem: poly p /\ ulead z ==> (z * p) % z = |0| *)
(* Proof: by poly_mod_multiple and poly_mult_comm. *)
val poly_mod_multiple_comm = store_thm(
  "poly_mod_multiple_comm",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==> ((z * p) % z = |0|)``,
  rw[poly_mod_multiple, poly_mult_comm]);

(* Theorem: Ring r /\ ulead p ==> (p / p = |1|) /\ (p % p = |0|) *)
(* Proof: by poly_div_mod_multiple and poly_mult_lone. *)
val poly_div_mod_id = store_thm(
  "poly_div_mod_id",
  ``!r:'a ring. Ring r ==> !p. ulead p ==> (p / p = |1|) /\ (p % p = |0|)``,
  metis_tac[poly_div_mod_multiple, poly_one_poly, poly_mult_lone]);

(* Theorem: p = z + q ==> p % z = q *)
(* Proof:
   p = z + q = |1| * z + q     by poly_mult_lone
   Hence true                  by poly_div_mod_eqn
*)
val poly_add_mod = store_thm(
  "poly_add_mod",
  ``!r:'a ring. Ring r ==>
   !p q z. poly p /\ poly q /\ ulead z /\ deg q < deg z /\ (p = z + q) ==> (p % z = q)``,
  rpt strip_tac >>
  `p = |1| * z + q` by rw[] >>
  `poly |1|` by rw[] >>
  metis_tac[poly_div_mod_eqn]);

(* Theorem: (p + q) % z = (p % z + q % z) % z *)
(* Proof:
   p = (p / z) * z + (p % z)     by poly_div_mod_all_def
   q = (q / z) * z + (q % z)     by poly_div_mod_all_def
   If deg z = 0,
      LHS = (p + q) % z = |0|           by poly_mod_by_const
      RHS = (p % z + q % z) % z = |0|   by poly_mod_by_const
      Hence equal.
   Otherwise 0 < deg z.
     p + q
   = ((p / z) * z + (p % z)) + ((q / z) * z + (q % z))
   = (p / z) * z + (q / z) * z + (p % z) + (q % z)                                  by poly_add_assoc, poly_add_comm
   = (p / z) * z + (q / z) * z + ((p % z) + (q % z)) / z * z + (p % z + q % z) % z  since poly ((p % z) + (q % z))
   = (p / z + q / z + ((p % z) + (q % z)) / z) * z + (p % z + q % z) % z            by collecting terms
   Hence  (p + q) / z = p / z + q / z + ((p % z) + (q % z)) / z, which is true, but not very useful,
     and  (p + q) % z = (p % z + q % z) % z                      by poly_div_mod_eqn, 0 < deg z
*)
val poly_mod_add = store_thm(
  "poly_mod_add",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ ulead z ==>
    ((p + q) % z = (p % z + q % z) % z)``,
  rpt strip_tac >>
  `poly (p / z) /\ poly (p % z) /\ (p = (p / z) * z + (p % z))` by metis_tac[poly_div_mod_all_def] >>
  `poly (q / z) /\ poly (q % z) /\ (q = (q / z) * z + (q % z))` by metis_tac[poly_div_mod_all_def] >>
  qabbrev_tac `t = (p % z) + (q % z)` >>
  `poly t` by rw[Abbr`t`] >>
  Cases_on `deg z = 0` >-
  rw[poly_mod_by_const] >>
  `0 < deg z` by decide_tac >>
  `poly (t / z) /\ poly (t % z) /\ deg (t % z) < deg z /\ (t = (t / z) * z + (t % z))` by metis_tac[poly_div_mod_def] >>
  `p + q = ((p / z) * z + (p % z)) + ((q / z) * z + (q % z))` by metis_tac[] >>
  `_ = ((p / z) * z + (p % z) + (q / z) * z) + (q % z)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_add_poly] >>
  `_ = ((p / z) * z + ((p % z) + (q / z) * z)) + (q % z)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly] >>
  `_ = ((p / z) * z + ((q / z) * z + (p % z))) + (q % z)` by rw_tac std_ss[poly_add_comm, poly_mult_poly] >>
  `_ = ((p / z) * z + (q / z) * z + (p % z)) + (q % z)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly] >>
  `_ = (p / z) * z + (q / z) * z + (p % z) + (q % z)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_add_poly] >>
  `_ = (p / z) * z + (q / z) * z + t` by rw_tac std_ss[poly_add_poly, poly_add_assoc, poly_mult_poly, Abbr`t`] >>
  `_ = (p / z) * z + (q / z) * z + ((t / z) * z + (t % z))` by metis_tac[] >>
  `_ = (p / z + q / z) * z + ((t / z) * z + (t % z))` by rw_tac std_ss[poly_mult_ladd] >>
  `_ = ((p / z + q / z) * z + (t /z ) * z) + t % z` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_add_poly] >>
  `_ = (p /z + q / z + t /z ) * z + t % z` by rw_tac std_ss[poly_mult_ladd, poly_add_poly] >>
  metis_tac[poly_div_mod_eqn, poly_add_poly]);

(* Theorem: ((p + q) % z + t) % z = (p + (q + t) % z) % z *)
(* Proof:
     ((p + q) % z + t) % z
   = ((p + q) % z + t % z) % z        by poly_mod_add, poly_mod_mod
   = ((p + q) + t) % z                by poly_mod_add, poly_mod_mod
   = (p + (q + t)) % z                by poly_add_assoc
   = (p % z + (q + t) % z) % z        by poly_mod_add
   = (p % z + (q + t) % z % z) % z    by poly_mod_mod
   = (p + (q + t) % z) % z            by poly_mod_add, poly_mod_mod
*)
val poly_mod_add_assoc = store_thm(
  "poly_mod_add_assoc",
  ``!r:'a ring. Ring r ==> !p q t z. poly p /\ poly q /\ poly t /\ ulead z ==>
     (((p + q) % z + t) % z = (p + (q + t) % z) % z)``,
  rpt strip_tac >>
  `poly (p + q) /\ poly (q + t) /\ poly ((p + q) % z) /\ poly ((q + t) % z)` by rw[] >>
  `((p + q) % z + t) % z = ((p + q) % z + t % z) % z` by rw_tac std_ss[poly_mod_add, poly_mod_mod] >>
  `_ = ((p + q) + t) % z` by rw_tac std_ss[poly_mod_add, poly_mod_mod] >>
  `_ = (p + (q + t)) % z` by rw[poly_add_assoc] >>
  `_ = (p % z + (q + t) % z) % z` by rw_tac std_ss[poly_mod_add] >>
  `_ = (p % z + (q + t) % z % z) % z` by rw_tac std_ss[poly_mod_mod] >>
  `_ = (p + (q + t) % z) % z` by rw_tac std_ss[poly_mod_add, poly_mod_mod] >>
  rw[]);

(* Theorem: (p - q) % z = (p % z - q % z) % z *)
(* Proof:
     (p - q) % z
   = (p + -q) % z             by poly_sub_def
   = (p % z + (-q) % z) % z   by poly_mod_add
   = (p % z + -(q % z)) % z   by poly_mod_neg
   = (p % z - q % z) % z      by poly_sub_def
*)
Theorem poly_mod_sub:
  !r:'a ring. Ring r ==>
              !p q z. poly p /\ poly q /\ ulead z ==>
                      ((p - q) % z = (p % z - q % z) % z)
Proof
  rw[poly_sub_def, poly_mod_add, poly_mod_neg]
QED

(* Theorem: (p * q) % z = (p % z * q % z) % z *)
(* Proof:
   p = (p / z) * z + (p % z)     by poly_div_mod_all_def
   q = (q / z) * z + (q % z)     by poly_div_mod_all_def
   If deg z = 0,
      LHS = (p * q) % z = |0|           by poly_mod_by_const
      RHS = (p % z * q % z) % z = |0|   by poly_mod_by_const
      Hence equal.
   Otherwise 0 < deg z.
     p * q
   = ((p / z) * z + (p % z)) * ((q / z) * z + (q % z))
   = ((p / z) * z) * ((q / z) * z + (q % z)) + (p % z) * ((q / z) * z + (q % z))   by poly_mult_ladd
   = (((p / z) * z) * ((q / z) * z) + ((p / z) * z) * (q % z)) + ((p % z) * ((q / z) * z) + (p % z) * (q % z))   by poly_mult_radd
   = (((p / z) * z) * (q / z) * z + (p / z) * (z * (q % z))) + ((p % z) * (q / z) * z + (p % z) * (q % z)) by poly_mult_assoc
   = (((p / z) * z) * (q / z) * z + (p / z) * ((q % z) * z)) + ((p % z) * (q / z) * z + (p % z) * (q % z)) by poly_mult_comm
   = (((p / z) * z) * (q / z) + (p / z) * (q % z)) * z + ((p % z) * (q / z) * z + (p % z) * (q % z))       by poly_mult_ladd
   = (((p / z) * z) * (q / z) + (p / z) * (q % z)) * z + (p % z) * (q / z) * z + (p % z) * (q % z)         by poly_add_assoc
   = ((((p / z) * z) * (q / z) + (p / z) * (q % z)) + (p % z) * (q / z)) * z + (p % z) * (q % z)           by poly_mult_ladd
   = ((((p / z) * z) * (q / z) + (p / z) * (q % z)) + (p % z) * (q / z)) * z +
     ((((p % z) * (q % z)) / z) * z + ((p % z) * (q % z)) % z)                  by poly (p % z) * (q % z) and poly_div_mod_def
   = ((((p / z) * z) * (q / z) + (p / z) * (q % z)) + (p % z) * (q / z)) * z +
     (((p % z) * (q % z)) / z) * z + ((p % z) * (q % z)) % z                    by poly_add_assoc
   = (((((p / z) * z) * (q / z) + (p / z) * (q % z)) + (p % z) * (q / z)) +
     (((p % z) * (q % z)) / z)) * z + ((p % z) * (q % z)) % z                   by poly_mult_ladd
   Hence  (p * q) / z = ((((p / z) * z) * (q / z) + (p / z) * (q % z)) + (p % z) * (q / z)) +
                       (((p % z) * (q % z)) / z), which is true, but not very useful,
     and  (p * q) % z = ((p % z) * (q % z)) % z      by poly_div_mod_eqn, 0 < deg z
*)
val poly_mod_mult = store_thm(
  "poly_mod_mult",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ ulead z ==>
    ((p * q) % z = (p % z * q % z) % z)``,
  rpt strip_tac >>
  `poly (p / z) /\ poly (p % z) /\ (p = (p / z) * z + (p % z))` by metis_tac[poly_div_mod_all_def] >>
  `poly (q / z) /\ poly (q % z) /\ (q = (q / z) * z + (q % z))` by metis_tac[poly_div_mod_all_def] >>
  qabbrev_tac `t = (p % z) * (q % z)` >>
  Cases_on `deg z = 0` >-
  metis_tac[poly_mod_by_const, poly_mult_poly, poly_div_poly, poly_mod_poly] >>
  `0 < deg z` by decide_tac >>
  `poly t` by rw[Abbr`t`] >>
  `poly (t / z) /\ poly (t % z) /\ deg (t % z) < deg z /\ (t = (t / z) * z + (t % z))` by metis_tac[poly_div_mod_def] >>
  `p * q = ((p / z) * z + (p % z)) * q` by metis_tac[] >>
  `_ = (p / z) * q * z + (p % z) * q` by rw[poly_mult_ladd, poly_mult_comm, poly_mult_assoc] >>
  `_ = (p / z) * q * z + (p % z) * ((q / z) * z + (q % z))` by metis_tac[] >>
  `_ = (p / z) * q * z + ((p % z) * (q / z) * z + t)` by rw[poly_mult_radd, poly_mult_assoc] >>
  `_ = (p / z) * q * z + (p % z) * (q / z) * z + t` by rw[poly_add_assoc] >>
  `_ = ((p / z) * q  + (p % z) * (q / z)) * z + t` by rw[poly_mult_ladd] >>
  `_ = ((p / z) * q  + (p % z) * (q / z)) * z + ((t / z) * z + (t % z))` by metis_tac[] >>
  `_ = ((p / z) * q  + (p % z) * (q / z)) * z + (t / z) * z + (t % z)` by rw_tac std_ss[poly_add_assoc, poly_add_poly, poly_mult_poly] >>
  `_ = ((p / z) * q  + (p % z) * (q / z) + (t / z)) * z + (t % z)` by rw_tac std_ss[poly_mult_ladd, poly_add_poly, poly_mult_poly] >>
  metis_tac[poly_div_mod_eqn, poly_add_poly, poly_mult_poly]);

(* Theorem: ((p * q) % z * t) % z = (p * (q * t) % z) % z *)
(* Proof:
     ((p * q) % z * t) % z
   = ((p * q) % z * t % z) % z        by poly_mod_mult, poly_mod_mod
   = (p * q * t) % z                  by poly_mod_mult
   = (p * (q * t)) % z                by poly_mult_assoc
   = (p % z * (q * t) % z) % z        by poly_mod_mult
   = (p % z * (q * t) % z % z) % z    by poly_mod_mod
   = (p * (q * t) % z) % z            by poly_mod_mult
*)
val poly_mod_mult_assoc = store_thm(
  "poly_mod_mult_assoc",
  ``!r:'a ring. Ring r ==> !p q t z. poly p /\ poly q /\ poly t /\ ulead z ==>
    (((p * q) % z * t) % z = (p * (q * t) % z) % z)``,
  rpt strip_tac >>
  `poly (p * q) /\ poly (q * t) /\ poly ((p * q) % z) /\ poly ((q * t) % z)` by rw[] >>
  `((p * q) % z * t) % z = ((p * q) % z * t % z) % z` by rw_tac std_ss[poly_mod_mult, poly_mod_mod] >>
  `_ = (p * q * t) % z` by rw_tac std_ss[poly_mod_mult] >>
  `_ = (p * (q * t)) % z` by rw[poly_mult_assoc] >>
  `_ = (p % z * (q * t) % z) % z` by rw_tac std_ss[poly_mod_mult] >>
  `_ = (p % z * (q * t) % z % z) % z` by rw[poly_mod_mod] >>
  `_ = (p * (q * t) % z) % z` by rw_tac std_ss[poly_mod_mult] >>
  rw[]);

(* Theorem: (c * p) % z = (c * (p % z)) % z *)
(* Proof:
   If deg z = 0,
      Then LHS = |0| = RHS       by poly_mod_by_const
   Otherwise, 0 < deg z.
   If c = #0,
   LHS = (#0 * p) % z
       = |0| % z                 by poly_cmult_lzero
       = (#0 * (p % z)) % z      by poly_cmult_lzero
       = RHS
   If c <> #0, poly [c]          by poly_nonzero_element_poly
   LHS = (c * p) % z
       = ([c] * p) % z           by poly_mult_lconst
       = ([c] % z * p % z) % z   by poly_mod_mult
       = ([c] * p % z) % z       by poly_mod_const
       = (c * p % z) % z         by poly_mult_lconst
       = RHS
*)
val poly_mod_cmult = store_thm(
  "poly_mod_cmult",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==>
   !c. c IN R ==> ((c * p) % z = (c * p % z) % z)``,
  rpt strip_tac >>
  Cases_on `deg z = 0` >-
  rw[poly_mod_by_const] >>
  `0 < deg z` by decide_tac >>
  `poly (p % z)` by rw[] >>
  Cases_on `c = #0` >-
  rw[] >>
  `poly [c]` by rw[] >>
  metis_tac[poly_mult_lconst, poly_mod_mult, poly_mod_const]);

(* Theorem: p % z = |0|  iff  ?q. poly q /\ p = q * z  *)
(* Proof:
   If part: p % z = |0| ==> ?q. poly q /\ (p = q * z)
        p
      = p / z * z + p % z   by poly_division_all
      = p / z * z           by poly_add_rzero, p % z = |0|
      Take q = p / z, making this true.
   Only-if part: ?q. poly q /\ (p = q * z) ==> p % z = |0|
      Since p = q * z, this is to show: (q * z) % z = |0|
      which is true         by poly_mod_multiple.
*)
val poly_mod_eq_zero = store_thm(
  "poly_mod_eq_zero",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==>
       ((p % z = |0|) <=> ?q. poly q /\ (p = q * z))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `p = p / z * z + p % z` by rw[poly_division_all] >>
    `poly (p / z)` by rw[] >>
    metis_tac[poly_add_rzero, poly_mult_poly],
    rw[poly_mod_multiple]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Equivalence                                             *)
(* ------------------------------------------------------------------------- *)
(*
To apply function equivalence, define the equivalence function f
for the function identity with notation: (x == y) f <=> f x = f y.
*)
val pmod_def = Define`
  pmod (r:'a ring) (z:'a poly) (p:'a poly) = p % z
`;

val _ = overload_on ("pm", ``pmod (r:'a ring)``);
(* This allows ``(p == q) (pm z)`` *)

(* export simple definition *)
val _ = export_rewrites ["pmod_def"];

(* Theorem: (p == q) (pm z) <=> p % z = q % z  *)
(* Proof: by pmod_def *)
val pmod_def_alt = store_thm(
  "pmod_def_alt",
  ``!p q z. (p == q) (pm z) <=> (p % z = q % z)``,
  rw[fequiv_def]);

(* Theorem: poly_mod_eq is reflexive: (p == p) (pm z) *)
(* Proof:
   (p == p) (pm z)  <=>  p % z = p % z  by pmod_def
   hence true by fequiv_refl.
*)
val poly_mod_reflexive = store_thm(
  "poly_mod_reflexive",
  ``!r:'a ring. !p z. (p == p) (pm z)``,
  rw[]);

(* Theorem: poly_mod_eq is symmetric: ((p == q) (pm z) ==> (q == p) (pm z)) *)
(* Proof:
   (p == q) (pm z)  <=>   p % z = q % z  by pmod_def
   (q == p) (pm z)  <=>   q % z = p % z  by pmod_def
   hence true by fequiv_sym.
*)
val poly_mod_symmetric = store_thm(
  "poly_mod_symmetric",
  ``!r:'a ring. !p q z. ((p == q) (pm z) ==> (q == p) (pm z))``,
  rw[fequiv_sym]);

(* Theorem: poly_mod_eq is transitive: ((p == q) (pm z) /\ (q == t) (pm z) ==> (p == t) (pm z)) *)
(* Proof:
   (p == q) (pm z)  <=>   p % z = q % z  by pmod_def
   (q == t) (pm z)  <=>   q % z = t % z  by pmod_def, and
   (p == t) (pm z)  <=>   p % z = t % z  by pmod_def
   hence true by fequiv_trans.
*)
val poly_mod_transitive = store_thm(
  "poly_mod_transitive",
  ``!r:'a ring. !p q t z. ((p == q) (pm z) /\ (q == t) (pm z) ==> (p == t) (pm z))``,
  rw[fequiv_def]);

(* Theorem: (p == q) (pm z) /\ (p == u) (pm z) /\ (q == v) (pm z) ==> (u == v) (pm z) *)
(* Proof:
   (p == u) (pm z) ==> (u == p) (pm z)                      by poly_mod_symmetric
   (u == p) (pm z) /\ (p == q) (pm z) ==> (u == q) (pm z)   by poly_mod_transitive
   (u == q) (pm z) /\ (q == v) (pm z) ==> (u == v) (pm z)   by poly_mod_transitive
*)
val poly_mod_eq_eq = store_thm(
  "poly_mod_eq_eq",
  ``!(r:'a ring) z. !p q u v.
   (p == q) (pm z) /\ (p == u) (pm z) /\ (q == v) (pm z) ==> (u == v) (pm z)``,
  metis_tac[poly_mod_symmetric, poly_mod_transitive]);

(* Theorem: poly_mod is an equivalence relation. *)
(* Proof: by poly_mod_reflexive, poly_mod_symmetric, poly_mod_transitive.
   or simply by fequiv_equiv_class for univ(:'a poly).
*)
val poly_mod_equiv = store_thm(
  "poly_mod_equiv",
  ``!r:'a ring. !z. (\x y. (x == y) (pm z)) equiv_on univ(:'a poly)``,
  rw_tac std_ss[fequiv_equiv_class]);

(* Theorem: poly_mod is an equivalence relation on (PolyRing r).carrier. *)
(* Proof: by poly_mod_equiv *)
val poly_mod_equiv_on_poly_ring = store_thm(
  "poly_mod_equiv_on_poly_ring",
  ``!r:'a ring. !z. (\x y. (x == y) (pm z)) equiv_on (PolyRing r).carrier``,
  rw_tac std_ss[equiv_on_def, fequiv_def] >>
  metis_tac[]);

(* Theorem: (p % z == p) (pm z) *)
(* Proof:
       p % z == p
   <=> (p % z) % z = p % z       by fequiv_def
   <=> p % z = p % z             by poly_mod_mod
   <=> T
*)
val pmod_mod = store_thm(
  "pmod_mod",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==> (p % z == p) (pm z)``,
  rw[fequiv_def, poly_mod_mod]);

(* Theorem: (p1 == p2) (pm z) <=> (- p1 == - p2) (pm z) *)
(* Proof:
       p1 == p2
   <=> p1 % z = p2 % z           by fequiv_def
   <=> - (p1 % z) = - (p2 % z)   by poly_neg_neg
   <=> (- p1) % z = (- p2) % z   by poly_mod_neg
   <=> - p1 == - p2              by fequiv_def
*)
val pmod_neg = store_thm(
  "pmod_neg",
  ``!r:'a ring. Ring r ==> !p1 p2 z. poly p1 /\ poly p2 /\ ulead z ==>
   ((p1 == p2) (pm z) <=> (- p1 == - p2) (pm z))``,
  rw[fequiv_def, EQ_IMP_THM] >>
  rw[poly_mod_neg] >>
  `poly (p1 % z) /\ poly (p2 % z)` by rw[poly_div_mod_def] >>
  metis_tac[poly_mod_neg, poly_neg_neg]);

(* Theorem: (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 + q1 == p2 + q2) (pm z) *)
(* Proof:
        (p1 + q1 == p2 + q2) (pm z)
    <=> (p1 + q1) % z = (p2 + q2) % z                   by fequiv_def
    <=> (p1 % z + q1 % z) % z = (p2 % z + q2 % z) % z   by poly_mod_add
    which is true since (p1 == p2) (pm z) and (q1 == q2) (pm z).
*)
val pmod_add = store_thm(
  "pmod_add",
  ``!r:'a ring. Ring r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\
   ulead z ==> (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 + q1 == p2 + q2) (pm z)``,
  rw[fequiv_def, poly_mod_add]);

(* Theorem: (p1 == p2) (pm z) ==> (c * p1 == c * p2) (pm z) *)
(* Proof:
       (p1 == p2) (pm z)
   <=>  p1 % z = p2 % z     by fequiv_def
     (c * p1) % z
   = (c * (p1 % z)) % z     by poly_mod_cmult
   = (c * (p2 % z)) % z     by above
   = (c * p2) % z           by poly_mod_cmult
   Hence (c * p1 == c * p2) (pm z)     by fequiv_def
*)
val pmod_cmult = store_thm(
  "pmod_cmult",
  ``!r:'a ring. Ring r ==> !p1 p2 z. poly p1 /\ poly p2 /\ ulead z ==>
   !c. c IN R ==> (p1 == p2) (pm z) ==> (c * p1 == c * p2) (pm z)``,
  rw[fequiv_def, poly_mod_cmult]);

(* Theorem: (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 * q1 == p2 * q2) (pm z) *)
(* Proof:
        (p1 * q1 == p2 * q2) (pm z)
    <=> (p1 * q1) % z = (p2 * q2) % z                   by fequiv_def
    <=> (p1 % z * q1 % z) % z = (p2 % z * q2 % z) % z   by poly_mod_mult
    which is true since (p1 == p2) (pm z) and (q1 == q2) (pm z).
*)
val pmod_mult = store_thm(
  "pmod_mult",
  ``!r:'a ring. Ring r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\
    ulead z ==> (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 * q1 == p2 * q2) (pm z)``,
  rw[fequiv_def, poly_mod_mult]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Theorems                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ulead z ==> [] % z = |0| *)
(* Proof: by poly_zero_mod, poly_zero *)
val poly_mod_of_zero = store_thm(
  "poly_mod_of_zero",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> ([] % z = |0|)``,
  metis_tac[poly_zero_mod, poly_zero]);

(* Theorem alias *)
val poly_mod_zero = save_thm("poly_mod_zero", poly_zero_mod);
(* val poly_mod_zero = |- !r. Ring r ==> !z. pmonic z ==> ( |0| % z = |0|): thm *)

(* Theorem: pmonic z ==> |1| % z = |1| *)
(* Proof:
   Since  poly |1|      by poly_one_poly
     and  deg |1| = 0   by poly_deg_one
   Hence true           by poly_mod_less
*)
val poly_mod_one = store_thm(
  "poly_mod_one",
  ``!r:'a ring. Ring r ==> !z. pmonic z ==> ( |1| % z = |1|)``,
  rw[poly_mod_less]);

(* export simple result *)
val _ = export_rewrites ["poly_mod_one"];

(* Theorem: ulead z ==> |1| % z = if deg z = 0 then |0| else |1| *)
(* Proof:
   If deg z = 0, then |1| % z = |0|           by poly_mod_by_const
   Otherwise, 0 < deg z, then |1| % z = |1|   by poly_mod_one
*)
val poly_mod_one_all = store_thm(
  "poly_mod_one_all",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> ( |1| % z = if deg z = 0 then |0| else |1|)``,
  metis_tac[poly_mod_one, poly_mod_by_const, poly_one_poly, NOT_ZERO]);


(* Theorem: poly p /\ pmonic z ==> !n. (p ** n) % z = ((p % z) ** n) % z  *)
(* Proof:
   By induction on n.
   Base case: p ** 0 % z = (p % z) ** 0 % z
   LHS = p ** 0 % z
       = |1| % z              by poly_exp_0
       = ((p % z) ** 0) % z   by poly_exp_0
       = RHS
   Step case: p ** n % z = (p % z) ** n % z ==> p ** SUC n % z = (p % z) ** SUC n % z
   LHS = p ** SUC n % z
       = (p * p ** n) % z                        by poly_exp_SUC
       = (p % z * (p ** n) % z) % z              by poly_mod_mult
       = (p % z * ((p % z) ** n) %z) % z         by induction hypothesis
       = ((p % z) % z * ((p % z) ** n) % z) % z  by poly_mod_mod
       = ((p % z) * ((p % z) ** n)) % z          by poly_mod_mult
       = ((p % z) ** SUC n) % z                  by poly_exp_SUC
       = RHS
*)
val poly_mod_exp = store_thm(
  "poly_mod_exp",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z ==>
    !n. (p ** n) % z = ((p % z) ** n) % z``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[poly_exp_SUC] >>
  `poly (p ** n) /\ poly (p % z) /\ poly ((p % z) ** n)` by rw[] >>
  `(p * p ** n) % z = (p % z * (p ** n) % z) % z` by rw_tac std_ss[poly_mod_mult] >>
  `_ = (p % z * ((p % z) ** n) % z) % z` by metis_tac[poly_mod_poly] >>
  `_ = ((p % z) % z * ((p % z) ** n) %z) % z` by rw[poly_mod_mod] >>
  `_ = ((p % z) * ((p % z) ** n)) % z` by rw_tac std_ss[poly_mod_mult] >>
  rw[]);

(* Theorem: (p % z = q % z) <=> ((p - q) % z = |0|) *)
(* Proof:
   If part: p % z = q % z ==> (p - q) % z = |0|
     (p - q) % z
   = (p % z - q % z) % z          by poly_mod_sub
   = |0| % z                      by poly_sub_eq_zero
   = |0|                          by poly_zero_mod
   Only-if part: (p - q) % z = |0| ==> p % z = q % z
     p % z
   = (p - q + q) % z              by poly_sub_add
   = ((p - q) % z + q % z) % z    by poly_mod_add
   = ( |0| + q % z) % z            by given
   = (q % z) % z                  by poly_add_lzero
   = q % z                        by poly_mod_mod
*)
val poly_mod_eq = store_thm(
  "poly_mod_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
    !p q. poly p /\ poly q ==> ((p % z = q % z) <=> ((p - q) % z = |0|))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `(p - q) % z = (p % z - q % z) % z` by rw_tac std_ss[poly_mod_sub] >>
    `_ = |0| % z` by metis_tac[poly_sub_eq_zero, poly_mod_poly] >>
    rw[],
    `poly (p - q) /\ poly (q % z)` by rw[] >>
    `p % z = (p - q + q) % z` by rw_tac std_ss[poly_sub_add] >>
    `_ = ((p - q) % z + q % z) % z` by rw_tac std_ss[poly_mod_add] >>
    rw[poly_mod_mod]
  ]);

(* Theorem: Ring r /\ ulead z ==>
            !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> (p - q) % z = |0|) *)
(* Proof:
       (p == q) (pm z)
   <=> p % z = q % z        by pmod_def_alt
   <=> (p - q) % z = |0|    by poly_mod_eq
*)
val poly_mod_eq_alt = store_thm(
  "poly_mod_eq_alt",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> (p - q) % z = |0|)``,
  rw[pmod_def_alt, poly_mod_eq]);

(* Theorem: ulead h /\ (z % h = |0|) ==> (p == q) (pm z) ==> (p == q) (pm h) *)
(* Proof:
   First,  (z % h = |0|)
        <=> ?u. poly u /\ (z = u * h)             by poly_mod_eq_zero
   Second,  (p == q) (pm z)
        <=> ((p - q) == |0|) (pm z)               by poly_mod_eq
        <=>  ?v. poly v /\ (p - q = v * z)        by poly_mod_eq_zero
         or                 p - q = v * (u * h)   by above, z = u * h
         or                 p - q = (v * u) * h   by poly_mult_assoc
   Hence (p - q) % h = |0|                        by poly_mod_eq_zero
      or  p % h = q % h                           by poly_mod_eq
      or (p == q) (pm h)                          by pmod_def_alt
*)
val poly_mod_eq_divisor = store_thm(
  "poly_mod_eq_divisor",
  ``!(r:'a ring) (z h:'a poly). Ring r /\ ulead z /\ ulead h /\ (z % h = |0|) ==>
      !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (p == q) (pm h)``,
  rw_tac std_ss[pmod_def_alt] >>
  `(p - q) % z = |0|` by prove_tac[poly_mod_eq] >>
  `?u. poly u /\ (z = u * h)` by rw[GSYM poly_mod_eq_zero] >>
  `?v. poly v /\ (p - q = v * (u * h))` by rw[GSYM poly_mod_eq_zero] >>
  `_ = (v * u) * h` by rw[poly_mult_assoc] >>
  `poly (v * u)` by rw[] >>
  `(p - q) % h = |0|` by metis_tac[poly_mod_eq_zero, poly_sub_poly] >>
  rw[poly_mod_eq]);

(* Theorem: pmonic q ==> deg (p % q) < deg q *)
(* Proof: by poly_div_mod_def. *)
val poly_deg_mod_less = store_thm(
  "poly_deg_mod_less",
  ``!(r:'a ring) p q. Ring r /\ poly p /\ pmonic q ==> deg (p % q) < deg q``,
  rw[poly_div_mod_def]);

(* Theorem: Ring r ==> !p q. poly p /\ pmonic q ==> ((p / q = |0|) <=> deg p < deg q) *)
(* Proof:
   If part: p / q = |0| ==> deg p < deg q
      Since p = p / q * q + p % q) /\ deg (p % q) < deg q   by poly_div_mod_def
              = |0| * q + p % q                             by given
              = p % q                                       by poly_mult_lzero, poly_add_lzero
      Hence deg p = deg (p % q) < deg q
   Only-if part: deg p < deg q ==> p / q = |0|
      True by poly_div_less
*)
val poly_div_eq_zero = store_thm(
  "poly_div_eq_zero",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ pmonic q ==> ((p / q = |0|) <=> deg p < deg q)``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `(p = p / q * q + p % q) /\ deg (p % q) < deg q` by rw[poly_div_mod_def] >>
    `p = |0| * q + p % q` by metis_tac[] >>
    `_ = p % q` by rw[] >>
    metis_tac[],
    rw[poly_div_less]
  ]);

(* Theorem: Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
                       ((p / z) * z = p) /\ (z * (p / z) = p) *)
(* Proof:
   Since p = (p / z) * z + (p % z)    by poly_division_all
           = (p / z) * z + |0|        by given
           = (p / z) * z              by poly_add_rzero
    Also p = z * (p / z)              by poly_mult_comm
*)
val poly_div_multiple_alt = store_thm(
  "poly_div_multiple_alt",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
    ((p / z) * z = p) /\ (z * (p / z) = p)``,
  ntac 5 strip_tac >>
  `p = (p / z) * z + (p % z)` by rw[poly_division_all] >>
  `_ = (p / z) * z` by rw[] >>
  metis_tac[poly_mult_comm, poly_div_poly]);

(* Theorem: poly p /\ poly q /\ unit c ==> (c * p = c * q <=> p = q) *)
(* Proof:
   If part: c * p = c * q ==> p = q
      Note |/c IN R                by ring_unit_inv_element
      Then p = ( |/c * c) * p      by ring_unit_linv
             = |/c * (c * p)       by poly_cmult_cmult
             = |/c * (c * q)       by given
             = ( |/c * c) * q      by poly_cmult_cmult
             = q                   by ring_unit_linv
   Only-if part: p = q ==> c * p = c * q
      This is trivial.
*)
val poly_ulead_cmult_eq = store_thm(
  "poly_ulead_cmult_eq",
  ``!r:'a ring. Ring r ==>
   !p q c. poly p /\ poly q /\ unit c ==> ((c * p = c * q) <=> (p = q))``,
  rw[EQ_IMP_THM] >>
  `|/c IN R` by rw[ring_unit_inv_element] >>
  `p = ( |/c * c) * p` by rw[ring_unit_linv] >>
  `_ = |/c * (c * p)` by rw[poly_cmult_cmult] >>
  `_ = |/c * (c * q)` by rw[] >>
  `_ = ( |/c * c) * q` by rw[poly_cmult_cmult] >>
  `_ = q` by rw[ring_unit_linv] >>
  simp[]);

(* Theorem: ulead p /\ poly q /\ poly t ==> ((q * p = t * p) <=> (q = t)) *)
(* Proof:
   If part: q * p = t * p ==> q = t
      If p = |0|,
         Then unit #0        by poly_lead_zero
           so #1 = #0        by ring_unit_zero
          and |1| = |0|      by poly_one_eq_poly_zero
         Thus q = t          by poly_one_eq_zero
      If p <> |0|,
         If deg p = 0,
            Then ?c. c IN R /\ c <> #0 /\ p = [c]   by poly_deg_eq_0
             and lead p = c                         by poly_lead_const
                  q * [c] = t * [c]
              <=>   c * q = c * t       by poly_mult_rconst
              <=>       q = t           by poly_ulead_cmult_eq, unit c
         Otherwise 0 < deg p.
            Let z = q * p,
           Then z = q * p + |0|
            and z = t * p + |0|
          Hence q = t                   by poly_div_mod_unique, 0 < deg p
   Only-if part: q = t ==> q * p = t * p
        This is trivial.
*)
val poly_ulead_mult_rcancel = store_thm(
  "poly_ulead_mult_rcancel",
  ``!r:'a ring. Ring r ==>
   !p q t. ulead p /\ poly q /\ poly t ==> ((q * p = t * p) <=> (q = t))``,
  rw[EQ_IMP_THM] >>
  Cases_on `p = |0|` >| [
    `unit #0` by fs[] >>
    `#1 = #0` by rw[GSYM ring_unit_zero] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mult_zero],
    Cases_on `deg p = 0` >| [
      `?c. c IN R /\ c <> #0 /\ (p = [c])` by rw[GSYM poly_deg_eq_0] >>
      `lead p = c` by rw[poly_lead_const] >>
      metis_tac[poly_mult_rconst, poly_ulead_cmult_eq],
      `0 < deg p` by decide_tac >>
      `?z. z = q * p` by rw[] >>
      `poly z /\ (z = q * p + |0|) /\ (z = t * p + |0|)` by rw[] >>
      `poly |0| /\ (deg |0| = 0)` by rw[] >>
      metis_tac[poly_div_mod_unique]
    ]
  ]);
(* better than: polyDividesTheory.poly_monic_mult_rcancel *)

(* Theorem: ulead p /\ poly q /\ poly t ==> ((p * q = p * t) <=> (q = t)) *)
(* Proof: by poly_ulead_mult_rcancel and poly_mult_comm *)
val poly_ulead_mult_lcancel = store_thm(
  "poly_ulead_mult_lcancel",
  ``!r:'a ring. Ring r ==>
   !p q t. ulead p /\ poly q /\ poly t ==> ((p * q = p * t) <=> (q = t))``,
  metis_tac[poly_ulead_mult_rcancel, poly_mult_comm]);
(* better than: polyDividesTheory.poly_monic_mult_lcancel *)

(* Theorem: Ring r ==> !p q. poly p /\ ulead q ==>
            !x. x IN roots q ==> (eval (p % q) x = eval p x) *)
(* Proof:
   Let s = p / q, t = p % q.
   Then poly s /\ poly t      by poly_div_poly, poly_mod_poly
    and p = s * q + t         by poly_division_all
   Note x IN R /\ root q x    by poly_roots_member
    and eval q x = #0         by poly_root_def
        eval p x
      = eval (s * q + t) x    by p = s * q + t
      = eval (s * q) x + eval t x    by poly_eval_add
      = (eval s x) * (eval q x) + eval t x   by poly_eval_mult
      = (eval s x) * #0 + eval t x           by root q x, above
      = #0 + eval t x                        by ring_mult_rzero
      = eval t x                             by ring_add_lzero
*)
val poly_eval_poly_mod_at_root = store_thm(
  "poly_eval_poly_mod_at_root",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ ulead q ==>
   !x. x IN roots q ==> (eval (p % q) x = eval p x)``,
  rpt strip_tac >>
  qabbrev_tac `s = p / q` >>
  qabbrev_tac `t = p % q` >>
  `x IN R /\ root q x` by metis_tac[poly_roots_member] >>
  `eval q x = #0` by rw[GSYM poly_root_def] >>
  `p = s * q + t` by rw[poly_division_all, Abbr`s`, Abbr`t`] >>
  `poly s /\ poly t` by rw[poly_div_poly, poly_mod_poly, Abbr`s`, Abbr`t`] >>
  `eval p x = (eval s x) * (eval q x) + (eval t x)` by prove_tac[poly_eval_add, poly_eval_mult, poly_mult_poly] >>
  `_ = eval t x` by rw[] >>
  rw[Abbr`t`]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
