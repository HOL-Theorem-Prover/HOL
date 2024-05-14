(* ------------------------------------------------------------------------- *)
(* Ring Polynomial Modulo                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyRingModulo";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory;

open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory polyMonicTheory;
open polyRootTheory polyEvalTheory;
open polyDividesTheory;
open polyModuloRingTheory;
open polyBinomialTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Ring Polynomial Modulo Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Lifting Polynomial Ring:
   poly_poly_ring_ring          |- !r. Ring r ==> Ring (PolyRing (PolyRing r))
   poly_mod_poly_mod_ring_ring  |- !r z h. Ring r /\ ulead z /\ Ulead (PolyModRing r z) h ==>
                                           Ring (PolyModRing (PolyModRing r z) h)

   Polynomial Modulo Evaluation Theorems:
   poly_mod_peval_sub    !r z. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==>
                                  (peval (p - q) x == peval p x - peval q x) (pm z)
   poly_mod_peval_eq     |- !r z. Ring r /\ ulead z ==> !p q x. poly p /\ poly q /\ poly x ==>
                                  ((peval p x == peval q x) (pm z) <=> (peval (p - q) x == |0|) (pm z))
   poly_mod_eq_peval_X   |- !r z. Ring r /\ ulead z ==> !p q. poly p /\ poly q /\
                                  (p == q) (pm z) ==> (peval (p - q) X == |0|) (pm z)
   poly_mod_eq_zero_root |- !r z. Ring r /\ ulead z ==> !p. poly p /\ (p == |0|) (pm z) ==>
                            !c. c IN R /\ root z c ==> root p c
   poly_peval_X_eq_zero_root|- !r z. Ring r /\ ulead z ==> !p. poly p /\ (peval p X == |0|) (pm z) ==>
                               !c. c IN R /\ root z c ==> root p c

   poly_peval_mod        |- !r z. Ring r /\ ulead z ==> !p q. poly p /\ poly q ==>
                                (peval p (q % z) % z = peval p q % z)
   poly_peval_mod_eq     |- !r z. Ring r /\ ulead z ==>
                            !p q1 q2. poly p /\ poly q1 /\ poly q2 /\ (q1 == q2) (pm z) ==>
                                      (peval p q1 == peval p q2) (pm z)

   Polynomial Modulo Theorems:
   poly_mod_ring_has_monomials
                           |- !r z. Ring r /\ poly z /\ 1 < deg z ==>
                              !c. X + |c| IN ((PolyModRing r z).prod excluding |0|).carrier

   poly_mod_ring_has_root_X
                           |- !r z. Ring r /\ ulead z ==> (peval z X % z = |0|)

   Useful Theorems:
   poly_mod_eq_peval_root  |- !r z. Ring r /\ ulead z ==> !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
                              !t. poly t /\ (peval z t == |0|) (pm z) ==> (peval (p - q) t == |0|) (pm z)
   poly_mod_eq_peval_root_eq
                           |- !r z. Ring r /\ ulead z ==> !x. poly x /\ (peval z x == |0|) (pm z) ==>
                              !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm z)
   poly_mod_eq_peval_root_2
                           |- !r z h. Ring r /\ ulead z /\ ulead h /\ z % h = |0| ==>
                              !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
                              !t. poly t /\ (peval z t == |0|) (pm h) ==> (peval (p - q) t == |0|) (pm h)
   poly_mod_eq_peval_root_eq_2
                           |- !r z h. Ring r /\ ulead z /\ ulead h /\ z % h = |0| ==>
                              !x. poly x /\ (peval z x == |0|) (pm h) ==>
                              !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm h)
   poly_unity_root_exp_mod |- !r h k. Ring r /\ ulead h /\ 0 < k /\ unity k % h = |0| ==>
                              !t. poly t /\ (t ** k == |1|) (pm h) ==> !m. (t ** m == t ** (m MOD k)) (pm h)
   poly_pmod_exp_mod       |- !r z. Ring r /\ ulead z ==>
                              !k p. 0 < k /\ poly p /\ (p ** k == |1|) (pm z) ==>
                              !m. (p ** m == p ** (m MOD k)) (pm z)
   poly_pmod_exp_mod_eq    |- !r z. Ring r /\ ulead z ==>
                              !p k. 0 < k /\ poly p /\ (p ** k == |1|) (pm z) ==>
                              !n m. (n MOD k = m MOD k) ==> (p ** n == p ** m) (pm z)
   poly_pmod_X_exp_mod     |- !r z. Ring r /\ ulead z ==>
                              !k. 0 < k /\ (X ** k == |1|) (pm z) ==> !m. (X ** m == X ** (m MOD k)) (pm z)
   poly_pmod_X_exp_mod_eq  |- !r z. Ring r /\ ulead z ==>
                              !k. 0 < k /\ (X ** k == |1|) (pm z) ==>
                              !n m. (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm z)

   More on Polynomial Evaluation:
   poly_peval_peval_X_exp        |- !r. Ring r ==> !p q. poly p /\ poly q ==>
                                    !n. peval (peval p (X ** n)) q = peval p (q ** n)
   poly_peval_peval_X_exp_X_exp  |- !r. Ring r ==> !p. poly p ==>
                                    !n m. peval (peval p (X ** n)) (X ** m) = peval p (X ** (n * m))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Lifting Polynomial Ring                                                   *)
(* ------------------------------------------------------------------------- *)

(*
- poly_add_mult_ring;
> val it = |- !r. Ring r ==> Ring (PolyRing r) : thm
- poly_mod_ring_ring;
> val it = |- !r. Ring r ==> !z. ulead z ==> Ring (PolyModRing r z) : thm
*)

(* Theorem: Ring (PolyRing (PolyRing r)) *)
(* Proof: apply poly_add_mult_ring twice. *)
val poly_poly_ring_ring = store_thm(
  "poly_poly_ring_ring",
  ``!r:'a ring. Ring r ==> Ring (PolyRing (PolyRing r))``,
  rw[poly_add_mult_ring]);

(*
- poly_mod_ring_ring |> ISPEC ``PolyModRing r z``;
> val it = |- Ring (PolyModRing r z) ==> !z'. Ulead (PolyModRing r z) z' ==>
             Ring (PolyModRing (PolyModRing r z) z') : thm
*)

(* Theorem: Ring r /\ ulead z /\ Ulead (PolyModRing r z) h
        ==> Ring (PolyModRing (PolyModRing r z) h) *)
(* Proof: apply poly_mod_ring_ring twice. *)
val poly_mod_poly_mod_ring_ring = store_thm(
  "poly_mod_poly_mod_ring_ring",
  ``!(r:'a ring) z (h:'a poly poly). Ring r /\ ulead z /\ Ulead (PolyModRing r z) h
      ==> Ring (PolyModRing (PolyModRing r z) h)``,
  rw[poly_mod_ring_ring]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Evaluation Theorems                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (peval (p - q) x == peval p x - peval q x) (pm z) *)
(* Proof: by poly_peval_sub. *)
val poly_mod_peval_sub = store_thm(
  "poly_mod_peval_sub",
  ``!(r:'a ring) z. Ring r ==>
     !p q x. poly p /\ poly q /\ poly x ==> (peval (p - q) x == peval p x - peval q x) (pm z)``,
  rw[poly_peval_sub]);

(* Theorem: (peval p x == peval q x) (pm z) <=> (peval (p - q) x == |0|) (pm z) *)
(* Proof:
   Apply pmod_def_alt,
   If part: peval p x % z = peval q x % z ==> peval (p - q) x % z = |0| % z
      peval (p - q) x % z
    = (peval p x - peval q x) % z                by poly_peval_sub
    = (peval p x % z - peval q x % z) % z        by poly_mod_sub
    = |0| % z                                    by poly_sub_eq_zero
   Only-if part: peval (p - q) x % z = |0| % z ==> peval p x % z = peval q x % z
     peval p x % z
   = peval (p - q + q) x % z                     by poly_sub_add
   = (peval (p - q) x + peval q x) % z           by poly_peval_add
   = (peval (p - q) x % z + peval q x % z) % z   by poly_mod_add
   = (|0| % z + peval q x % z) % z               by given
   = (|0| + peval q x % z) % z                   by poly_zero_mod
   = (peval q x % z) % z                         by poly_add_lzero
   = peval q x % z                               by poly_mod_mod
*)
val poly_mod_peval_eq = store_thm(
  "poly_mod_peval_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !p q x. poly p /\ poly q /\ poly x ==>
      ((peval p x == peval q x) (pm z) <=> (peval (p - q) x == |0|) (pm z))``,
  rw_tac std_ss[pmod_def_alt, EQ_IMP_THM] >| [
    `peval (p - q) x % z = (peval p x - peval q x) % z` by rw[poly_peval_sub] >>
    `_ = (peval p x % z - peval q x % z) % z` by rw_tac std_ss[poly_mod_sub, poly_peval_poly] >>
    metis_tac[poly_sub_eq_zero, poly_peval_poly, poly_mod_poly],
    `poly (p - q) /\ poly (peval (p - q) x) /\ poly (peval q x)` by rw[] >>
    `peval p x % z = peval (p - q + q) x % z` by rw_tac std_ss[poly_sub_add] >>
    `_ = (peval (p - q) x + peval q x) % z` by rw_tac std_ss[poly_peval_add] >>
    `_ = (peval (p - q) x % z + peval q x % z) % z` by rw_tac std_ss[poly_mod_add] >>
    rw[poly_mod_mod]
  ]);

(* Theorem: (p == q) (pm z) ==> (peval (p - q) X == |0|) (pm z) *)
(* Proof:
   Note p = peval p X  and q = peval q X   by poly_peval_by_X
        (p == q) (pm z)
   ==>  (peval p X == peval q X) (pm z)    by above
   ==>  (peval (p - q) X == |0|) (pm z)    by poly_mod_peval_eq
*)
val poly_mod_eq_peval_X = store_thm(
  "poly_mod_eq_peval_X",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
    !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval (p - q) X == |0|) (pm z)``,
  metis_tac[poly_mod_peval_eq, poly_peval_by_X, poly_X]);

(* Theorem: p == |0| (pm z) ==> !c. c IN R /\ root z c ==> root p c *)
(* Proof:
       (p == |0|) (pm z)
   ==> ?q. poly q /\ (p = q * z)       by pmod_eq_zero
   Now, root z c <=> eval z c = #0     by poly_root_def
   But  eval p c
      = eval (q * z) c                 by above
      = eval q c * eval z c            by poly_eval_mult
      = eval q c * #0                  by root z c
      = #0                             by ring_mult_rzero
   Hence root p c                      by poly_root_def
*)
val poly_mod_eq_zero_root = store_thm(
  "poly_mod_eq_zero_root",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
     !p. poly p /\ (p == |0|) (pm z) ==> !c. c IN R /\ root z c ==> root p c``,
  rw_tac std_ss[poly_root_def] >>
  `?q. poly q /\ (p = q * z)` by rw[GSYM pmod_eq_zero] >>
  rw[poly_eval_mult]);

(* Theorem: (peval p X == |0|) (pm z) ==> !c. c IN R /\ root z c ==> root p c *)
(* Proof: by poly_peval_by_X, poly_mod_eq_zero_root. *)
val poly_peval_X_eq_zero_root = store_thm(
  "poly_peval_X_eq_zero_root",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
     !p. poly p /\ (peval p X == |0|) (pm z) ==> !c. c IN R /\ root z c ==> root p c``,
  metis_tac[poly_peval_by_X, poly_mod_eq_zero_root]);

(* Theorem: (peval p (q % z)) % z = (peval p q) % z *)
(* Proof: by induction on p.
   Base case: peval [] (q % z) % z = peval [] q % z
     LHS = peval [] (q % z) % z
         = |0| % z                  by poly_peval_of_zero
         = peval [] q % z           by poly_peval_of_zero
         = RHS
   Step case: poly p ==> (peval p (q % z) % z = peval p q % z)
              !h. poly (h::p) ==> (peval (h::p) (q % z) % z = peval (h::p) q % z)
     poly (h::p) ==> h IN R /\ poly p    by poly_cons_poly
     LHS = peval (h::p) (q % z) % z
         = (h * |1| + peval p (q % z) * (q % z)) % z                      by poly_peval_cons
         = ((h * |1|) % z + (peval p (q % z) * (q % z)) % z) % z          by poly_mod_add
         = ((h * |1|) % z + (peval p (q % z) % z * (q % z % z)) % z) % z  by poly_mod_mult
         = ((h * |1|) % z + (peval p q % z * (q % z % z)) % z) % z        by induction hypothesis
         = ((h * |1|) % z + (peval p q % z * (q % z)) % z) % z            by poly_mod_mod
         = ((h * |1|) % z + (peval p q * q) % z) % z                      by poly_mod_mult
         = (h * |1| + peval p q * q) % z                                  by poly_mod_add
         = peval (h::p) q % z                                             by poly_peval_cons
         = RHS
*)
val poly_peval_mod = store_thm(
  "poly_peval_mod",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   !p q. poly p /\ poly q ==> ((peval p (q % z)) % z = (peval p q) % z)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `peval (h::p) (q % z) % z = (h * |1| + peval p (q % z) * (q % z)) % z` by rw[poly_peval_cons] >>
  `_ = ((h * |1|) % z + (peval p (q % z) * (q % z)) % z) % z` by rw[GSYM poly_mod_add] >>
  `_ = ((h * |1|) % z + (peval p (q % z) % z * (q % z % z)) % z) % z` by rw[GSYM poly_mod_mult] >>
  `_ = ((h * |1|) % z + (peval p q % z * (q % z % z)) % z) % z` by metis_tac[] >>
  `_ = ((h * |1|) % z + (peval p q % z * (q % z)) % z) % z` by rw[poly_mod_mod] >>
  `_ = ((h * |1|) % z + (peval p q * q) % z) % z` by rw[GSYM poly_mod_mult] >>
  `_ = (h * |1| + peval p q * q) % z` by rw[GSYM poly_mod_add] >>
  `_ = peval (h::p) q % z` by rw[poly_peval_cons] >>
  rw[]);

(* Theorem: (q1 == q2) (pm z) ==> (peval p q1 == peval p q2) (pm z) *)
(* Proof: by induction on p.
   Base case: poly [] ==> (peval [] q1 == peval [] q2) (pm z)
     Since peval [] q1 = |0|     by poly_peval_of_zero
     True by poly_mod_reflexive.
   Step case: poly p ==> (peval p q1 == peval p q2) (pm z) ==>
              !h. poly (h::p) ==> (peval (h::p) q1 == peval (h::p) q2) (pm z)
     poly (h::p) ==> h IN R /\ poly p     by poly_cons_poly
       peval (h::p) q1
     = h * |1| + peval p q1 * q1    by poly_peval_cons
     == h * |1| + peval p q1 * q2   by given, q1 == q2 (pm z)
     == h * |1| + peval p q2 * q2   by induction hypothesis
     = peval (h::p) q2              by poly_peval_cons
     Overall, (peval (h::p) q1 == peval (h::p) q2) (pm z)  by pmod_add, pmod_mult.
*)
val poly_peval_mod_eq = store_thm(
  "poly_peval_mod_eq",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   !p q1 q2. poly p /\ poly q1 /\ poly q2 /\ (q1 == q2) (pm z) ==>
             (peval p q1 == peval p q2) (pm z)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly, poly_peval_cons] >>
  rw[pmod_add, pmod_mult]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Modulo Theorems                                                *)
(* ------------------------------------------------------------------------- *)

(* The quotient ring by a non-linear polynomial has all monomials. *)

(* Theorem: Ring r /\ poly z /\ 1 < deg z ==>
            !c. X + |c| IN ((PolyModRing r z).prod excluding |0|).carrier *)
(* Proof:
   Note #1 <> #0               by poly_deg_pos_ring_one_ne_zero, 0 < deg z
    and poly (X + |c|)         by poly_X_add_c
    and deg (X + |c|) = 1      by poly_deg_X_add_c, #1 <> #0
   thus X + |c| <> |0|         by poly_deg_zero
   The result follows          by poly_mod_ring_nonzero_element, 0 < deg z
*)
val poly_mod_ring_has_monomials = store_thm(
  "poly_mod_ring_has_monomials",
  ``!(r:'a ring) z. Ring r /\ poly z /\ 1 < deg z ==>
   !c:num. X + |c| IN ((PolyModRing r z).prod excluding |0|).carrier``,
  rpt strip_tac >>
  `0 < deg z` by decide_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `poly (X + |c|)` by rw[] >>
  `deg (X + |c|) = 1` by rw[poly_deg_X_add_c] >>
  `X + |c| <> |0|` by metis_tac[poly_deg_zero, DECIDE``1 <> 0``] >>
  metis_tac[poly_mod_ring_nonzero_element]);

(* Theorem: Ring r ==> !z. ulead z ==> (peval z X) % z = |0| *)
(* Proof:
   Since  peval z X = z      by poly_peval_by_X
   This is just z % z = |0|  by poly_div_mod_id
*)
val poly_mod_ring_has_root_X = store_thm(
  "poly_mod_ring_has_root_X",
  ``!r:'a ring z. Ring r /\ ulead z ==> ((peval z X) % z = |0|)``,
  rw[poly_peval_by_X, poly_div_mod_id]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(*
poly_mod_peval_eq
|- !r z. Ring r /\ ulead z ==>
     !p q x. poly p /\ poly q /\ poly x ==>
       ((peval p x == peval q x) (pm z) <=> (peval (p - q) x == |0|) (pm z)) : thm
pmod_eq
|- !r. Ring r ==> !z. ulead z ==>
     !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> ((p - q) % z = |0|)) : thm
pmod_zero
|- !r. Ring r ==> !z. ulead z ==>
    !p. poly p ==> ((p == |0|) (pm z) <=> (p % z = |0|))
*)

(*
poly_peval_mod_eq
|- !r. Ring r ==> !p z. poly p /\ ulead z ==>
       !q1 q2. poly q1 /\ poly q2 /\ (q1 == q2) (pm z) ==>
         (peval p q1 == peval p q2) (pm z) : thm
poly_mod_eq_peval_root
|- !r z. Ring r /\ ulead z ==>
     !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
       !t. poly t /\ (peval z t == |0|) (pm z) ==> (peval (p - q) t == |0|) (pm z)
*)

(* Is it true that:
 (p == q) (pm z) ==> !t. poly t ==> (peval p t == peval q t) (pm z) ?

Example:
     X^3 == X    (pm z)  where z = X^2 - 1

peval X^3 (X + 1) = (X + 1)^3 = X^3 + 3 X^2 + 3 X + 1 -> X + 3 + 3 X + 1 = 4 X + 4 = 4 (X + 1)
peval X (X + 1) = X + 1

They differ by a unit.

Example:
     X^4 == 1 (pm z) where z = X^2 - 1
peval X^4 (X + 1) = (X + 1)^4 = X^4 + 4 X^3 + 6 X^2 + 4 X + 1 -> 1 + 4 X + 6 + 4 X + 1 = 8 X + 8 = 8 (X + 1)
peval 1 (X + 1) = 1

They are not equal!

Only true for t = X, or some special t, e.g. primitive root of unity?
That is, true when (peval z t == |0|) (pm z).

A special case is t = X, then peval z X = z, and (z == |0|) (pm z)
Idea:
        (p == q) (pm z)
    <=>  p - q = s * z    for some poly s
    so   peval (p - q) t
       = peval (s * z) t
       = (peval s t) * (peval z t)      by poly_peval_mult

   If t is a root of (lift z), i.e. (peval z t = |0|) (pm z)
   or  peval z t = u * z     for some poly u
   Thus  p - q = (peval s t) * (u * z) = ((peval s t) * u) * z
   Therefore (peval (p - q) t == |0|) (pm z)
*)

(* Theorem: (p == q) (pm z) ==> !t. poly t ==> (peval (p - q) t == |0|) (pm z) *)
(* Proof:
   Since (peval z t == |0|) (pm z)
         z pdivides (peval z t)               by poly_divides_pmod_eq_zero
         ?u. poly u /\ (peval z t) = u * z    by poly_divides_def
    Also (p == q) (pm z),
         p % z = q % z                        by pmod_def_alt
         (p - q) % z = |0|                    by poly_mod_eq
         z pdivides (p - q)                   by poly_divides_alt
         ?v. poly v /\ (p - q) = v * z        by poly_divides_def

   Therefore,
        peval (p - q) t
      = peval (v * z) t                       by above
      = (peval v t) * (peval z t)             by poly_peval_mult
      = (peval v t) * (u * z)                 by above
      = ((peval v t) * u) * z                 by poly_mult_assoc
   Hence  z pdivides (peval (p - q) t)        by poly_divides_def
      or (peval (p - q) t == |0|) (pm z)      by poly_divides_pmod_eq_zero
*)
val poly_mod_eq_peval_root = store_thm(
  "poly_mod_eq_peval_root",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
   !t. poly t /\ (peval z t == |0|) (pm z) ==> (peval (p - q) t == |0|) (pm z)``,
  rpt strip_tac >>
  `z pdivides (peval z t)` by rw[poly_divides_pmod_eq_zero] >>
  `?u. poly u /\ (peval z t = u * z)` by rw[GSYM poly_divides_def] >>
  `(p - q) % z = |0|` by metis_tac[pmod_def_alt, poly_mod_eq] >>
  `z pdivides (p - q)` by metis_tac[poly_divides_def, poly_mod_eq_zero, poly_sub_poly] >>
  `?v. poly v /\ (p - q = v * z)` by rw[GSYM poly_divides_def] >>
  `peval (p - q) t = peval (v * z) t` by rw[] >>
  `_ = (peval v t) * (peval z t)` by rw[poly_peval_mult] >>
  `_ = (peval v t) * (u * z)` by rw[] >>
  `_ = ((peval v t) * u) * z` by rw[poly_mult_assoc] >>
  `poly ((peval v t) * u)` by rw[] >>
  `z pdivides (peval (p - q) t)` by metis_tac[poly_divides_def] >>
  rw[GSYM poly_divides_pmod_eq_zero]);

(* Theorem: poly x /\ (peval z x == |0|) (pm z) ==>
           !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm z) *)
(* Proof:
   In general, (p == q) (pm z)  cannot imply  (peval p x == peval q x) (pm z)
   This is because, the first one gives: p - q = h * z    for some poly h.
     peval p x - peval q x
   = peval (p - q) x         by poly_peval_sub
   = peval (h * z) x         by above
   = peval h x * peval z x   by poly_peval_mult
   However, if (peval z x == |0|) (pm z), i.e. x is a "root" of z
      peval z x = k * z  for some poly k
   Then peval p x - peval q x
      = peval h x * k * z
      = (peval h x * k) * z     by poly_mult_assoc
     or (peval p x == peval q x) (pm z)
   This is essentially poly_mod_eq_peval_root.
       (peval z x == |0|) (pm z) /\ (p == q) (pm z)
   ==> (peval (p - q) x == |0|) (pm z)    by poly_mod_eq_peval_root
   ==> (peval p x == peval q x) (pm z)    by poly_mod_peval_eq
*)
val poly_mod_eq_peval_root_eq = store_thm(
  "poly_mod_eq_peval_root_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==> !x. poly x /\ (peval z x == |0|) (pm z) ==>
   !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm z)``,
  rw[poly_mod_eq_peval_root, poly_mod_peval_eq]);

(*
poly_mod_eq_peval_root
val it = |- !r z. Ring r /\ ulead z ==>
     !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
       !t. poly t /\ (peval z t == |0|) (pm z) ==> (peval (p - q) t == |0|) (pm z): thm
*)
(* Theorem: ulead z /\ ulead h /\ (z % h = |0|) ==> !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
            !t. poly t /\ (peval z t == |0|) (pm h) ==> (peval (p - q) t == |0|) (pm h) *)
(* Proof:
   Step 1: Show (peval z t) is a multiple of h
      Given (peval z t == |0|) (pm h),
      hence h pdivides (peval z t)              by poly_divides_pmod_eq_zero
         so ?u. poly u /\ (peval z t = u * h)   by poly_divides_def
   Step 2: Show (p - q) is a multiple of z
      Given (p == q) (pm z),
         so p % z = q % z                       by pmod_def_alt
         or (p - q) % z = |0|                   by poly_mod_eq
      hence z pdivides (p - q)                  by poly_divides_alt
         so ?v. poly v /\ (p - q = v * z)       by poly_divides_def
   Step 3: Compute peval (p - q) t
      Now  peval (p - q) t
         = peval (v * z) t                      by p - q = v * z
         = (peval v t) * (peval z t)            by poly_peval_mult
         = (peval v t) * (u * h)                by peval z t = u * h
         = ((peval v t) * u) * h                by poly_mult_assoc
      Thus h pdivides (peval (p - q) t)         by poly_divides_def
        or (peval (p - q) t == |0|) (pm h)      by poly_divides_pmod_eq_zero
*)
val poly_mod_eq_peval_root_2 = store_thm(
  "poly_mod_eq_peval_root_2",
  ``!r:'a ring z h. Ring r /\ ulead z /\ ulead h /\ (z % h = |0|) ==>
     !p q. poly p /\ poly q /\ (p == q) (pm z) ==>
       !t. poly t /\ (peval z t == |0|) (pm h) ==> (peval (p - q) t == |0|) (pm h)``,
  rpt strip_tac >>
  `h pdivides (peval z t)` by rw[poly_divides_pmod_eq_zero] >>
  `?u. poly u /\ (peval z t = u * h)` by rw[GSYM poly_divides_def] >>
  `(p - q) % z = |0|` by rw[GSYM pmod_def_alt, GSYM poly_mod_eq] >>
  `z pdivides (p - q)` by rw[poly_divides_alt] >>
  `?v. poly v /\ (p - q = v * z)` by rw[GSYM poly_divides_def] >>
  `peval (p - q) t = peval (v * z) t` by rw[] >>
  `_ = (peval v t) * (peval z t)` by rw[poly_peval_mult] >>
  `_ = ((peval v t) * u) * h` by rw[poly_mult_assoc] >>
  `poly ((peval v t) * u)` by rw[] >>
  `h pdivides (peval (p - q) t)` by metis_tac[poly_divides_def] >>
  rw[GSYM poly_divides_pmod_eq_zero]);

(*
poly_mod_eq_peval_root_eq
val it = |- !r z. Ring r /\ ulead z ==>
     !x. poly x /\ (peval z x == |0|) (pm z) ==>
       !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm z): thm
*)
(* Theorem: ulead z /\ ulead h /\ (z % h = |0|) ==> !x. poly x /\ (peval z x == |0|) (pm h) ==>
       !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm h) *)
(* Proof:
   Since (peval (p - q) x == |0|) (pm h)   by poly_mod_eq_peval_root_2
   hence (peval p x == peval q x) (pm h)   by poly_mod_peval_eq
*)
val poly_mod_eq_peval_root_eq_2 = store_thm(
  "poly_mod_eq_peval_root_eq_2",
  ``!r:'a ring z h. Ring r /\ ulead z /\ ulead h /\ (z % h = |0|) ==>
     !x. poly x /\ (peval z x == |0|) (pm h) ==>
       !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (peval p x == peval q x) (pm h)``,
  metis_tac[poly_mod_eq_peval_root_2, poly_mod_peval_eq]);

(* Theorem: ulead h /\ 0 < k /\ ((unity k) % h = |0|) ==>
            !t. poly t /\ (t ** k == |1|) (pm h) ==> !m. (t ** m == t ** (m MOD k)) (pm h) *)
(* Proof:
   Let z = unity k.
   Since m = m DIV k * k + m MOD k   by DIVISION
   Let q = m DIV k, n = m MOD k.
   Then the goal is to show: (t ** m == t ** n) (pm h)
   LHS = t ** m
       = t ** (q * k + n)            by m = q * k + n
       = t ** (k * q + n)            by MULT_COMM
       = t ** (k * q) * t ** n       by poly_exp_add
       = (t ** k) ** q * (t ** n)    by poly_exp_mult
   RHS = t ** n
       = |1| * (t ** n)              by poly_mult_lone
       = (|1| ** q) * (t ** n)       by poly_one_exp
   Given (t ** k == |1|) (pm h),
      so ((t ** k) ** q == |1| ** q) (pm h)   by pmod_exp_eq
    also (t ** n == t ** n) (pm h)            by poly_mod_reflexive
   hence ((t ** k) ** q * (t ** n) == (|1| ** q) * (t ** n)) (pm h)  by pmod_mult
      or (t ** m == t ** n) (pm h)                                   by LHS, RHS
*)
val poly_unity_root_exp_mod = store_thm(
  "poly_unity_root_exp_mod",
  ``!r:'a ring h k. Ring r /\ ulead h /\ 0 < k /\ ((unity k) % h = |0|) ==>
   !t. poly t /\ (t ** k == |1|) (pm h) ==> !m. (t ** m == t ** (m MOD k)) (pm h)``,
  rpt strip_tac >>
  qabbrev_tac `z = unity k` >>
  `m = m DIV k * k + m MOD k` by rw[DIVISION] >>
  qabbrev_tac `q = m DIV k` >>
  qabbrev_tac `n = m MOD k` >>
  `t ** m = t ** (k * q + n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = (t ** k) ** q * (t ** n)` by rw[poly_exp_add, poly_exp_mult] >>
  `t ** n = |1| ** q * (t ** n)` by metis_tac[poly_mult_lone, poly_one_exp, poly_exp_poly] >>
  metis_tac[pmod_exp_eq, poly_mod_reflexive, pmod_mult, poly_one_poly, poly_exp_poly, poly_mod_poly]);

(* The following is better. *)

(* Theorem: 0 < k /\ poly p /\ (p ** k == |1|) (pm z) ==> !m. (p ** m == p ** (m MOD k)) (pm z)  *)
(* Proof:
   Since 0 < k, m = m DIV k * k + m MOD k        by DIVISION
   or  m = q * k + n            where q = m DIV k, n = m MOD k.
     p ** m
   = p ** (q * k + n)           by above
   = p ** (k * q + n)           by MULT_COMM
   = p ** (k * q) * X ** n      by poly_exp_add
   = (p ** k) ** q * (p ** n)   by poly_exp_mult
   == |1| ** q * (p ** n)       by p ** k == |1| (pm z)
   = |1| * (p ** n)             by poly_one_exp
   = p ** n                     by poly_mult_lone
   Hence overall,
    (p ** m == p ** (m MOD k)) (pm z)
                                by pmod_exp_eq, poly_mod_reflexive, pmod_mult.
*)
val poly_pmod_exp_mod = store_thm(
  "poly_pmod_exp_mod",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !k p. 0 < k /\ poly p /\ (p ** k == |1|) (pm z) ==> !m. (p ** m == p ** (m MOD k)) (pm z)``,
  rpt strip_tac >>
  `m = m DIV k * k + m MOD k` by rw[DIVISION] >>
  qabbrev_tac `q = m DIV k` >>
  qabbrev_tac `n = m MOD k` >>
  `p ** m = p ** (k * q + n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = (p ** k) ** q * (p ** n)` by rw[poly_exp_add, poly_exp_mult] >>
  `p ** n = |1| ** q * (p ** n)` by rw[] >>
  `poly |1|` by rw[] >>
  metis_tac[pmod_exp_eq, poly_mod_reflexive, pmod_mult, poly_exp_poly, poly_mod_poly]);

(* Theorem: (p ** k == |1|) (pm z) /\ (n MOD k = m MOD k) ==> (p ** n == p ** m) (pm z) *)
(* Proof:
   Since  (p ** n == p ** (n MOD k)) (pm z)    by poly_pmod_exp_mod
     and  (p ** m == p ** (m MOD k)) (pm z)    by poly_pmod_exp_mod
   Hence  (p ** n == p ** m) (pm z)            by poly_mod_symmetric, poly_mod_transitive
*)
val poly_pmod_exp_mod_eq = store_thm(
  "poly_pmod_exp_mod_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
    !p k. 0 < k /\ poly p /\ (p ** k == |1|) (pm z) ==>
    !n m. (n MOD k = m MOD k) ==> (p ** n == p ** m) (pm z)``,
  metis_tac[poly_pmod_exp_mod, pmod_exp_eq, poly_mod_symmetric, poly_mod_transitive, poly_exp_poly]);

(* Theorem: 0 < k /\ (X ** k == |1|) (pm z) ==> !m. (X ** m == X ** (m MOD k)) (pm z)  *)
(* Proof: by poly_pmod_exp_mod, poly_X *)
val poly_pmod_X_exp_mod = store_thm(
  "poly_pmod_X_exp_mod",
  ``!r:'a ring z. Ring r /\ ulead z ==>
   !k. 0 < k /\ (X ** k == |1|) (pm z) ==> !m. (X ** m == X ** (m MOD k)) (pm z)``,
  rw[poly_pmod_exp_mod]);

(* Theorem: (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm z) *)
(* Proof: by poly_pmod_exp_mod_eq, poly_X *)
val poly_pmod_X_exp_mod_eq = store_thm(
  "poly_pmod_X_exp_mod_eq",
  ``!r:'a ring z. Ring r /\ ulead z ==>
    !k. 0 < k /\ (X ** k == |1|) (pm z) ==>
    !n m. (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm z)``,
  metis_tac[poly_pmod_exp_mod_eq, poly_X]);

(* ------------------------------------------------------------------------- *)
(* More on Polynomial Evaluation                                             *)
(* ------------------------------------------------------------------------- *)

(* Note: These are placed here due to use of polyBinomial for poly_peval_by_poly_sum *)

(* Theorem: poly p /\ poly q ==> !n. peval (peval p (X ** n)) q = peval p (q ** n) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                 by poly_one_eq_poly_zero
        so p = |0|                   by poly_one_eq_zero
           peval (peval p (X ** n)) q
         = peval |0| q               by poly_peval_zero
         = |0|                       by poly_peval_zero
         = peval p (q ** n)          by poly_peval_zero
   If #1 <> #0,
   Since  rfun (\k. p ' k)                    by poly_coeff_ring_fun
      so  poly_fun ((\k. p ' k * X ** k))     by poly_fun_from_ring_fun
     and  poly (X ** n)                       by poly_exp_poly
     peval (peval p (X ** n)) q
   = peval (poly_sum (GENLIST (\k. (p ' k) * ((X ** n) ** k)) (SUC (deg p)))) q   by poly_peval_by_poly_sum, #1 <> #0
   = poly_sum (GENLIST (\k. p ' k * ((peval (X ** n) q) ** k)) (SUC (deg p)))     by poly_peval_poly_sum_gen_poly
   = poly_sum (GENLIST (\k. p ' k * ((peval X q) ** n) ** k) (SUC (deg p)))       by poly_peval_exp
   = poly_sum (GENLIST (\k. p ' k * (q ** n) ** k) (SUC (deg p)))                 by poly_peval_X
   = peval p (q ** n)                                                             by poly_peval_by_poly_sum
*)
val poly_peval_peval_X_exp = store_thm(
  "poly_peval_peval_X_exp",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==>
    !n. peval (peval p (X ** n)) q = peval p (q ** n)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `p = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    rw[],
    `rfun (\k. p ' k)` by rw[poly_coeff_ring_fun] >>
    `poly_fun ((\k. p ' k * X ** k))` by rw[poly_fun_from_ring_fun] >>
    `peval (peval p (X ** n)) q =
    peval (poly_sum (GENLIST (\k. (p ' k) * ((X ** n) ** k)) (SUC (deg p)))) q` by rw[GSYM poly_peval_by_poly_sum] >>
    rw[poly_peval_poly_sum_gen_poly, poly_peval_exp, poly_peval_X, poly_peval_by_poly_sum]
  ]);
(* Note: not in PolyEval, as this uses poly_peval_by_poly_sum. *)

(* Theorem: poly p ==> !n m. peval (peval p (X ** n)) (X ** m) = peval p (X ** (n * m)) *)
(* Proof:
   Since poly X, poly (X ** m)            by poly_X, poly_exp_poly
     peval (peval p (X ** n)) (X ** m)
   = peval p ((X ** m) ** n)              by poly_peval_peval_X_exp
   = peval p (X ** (m * n))               by poly_exp_mult
   = peval p (X ** (n * m))               by MULT_COMM
*)
val poly_peval_peval_X_exp_X_exp = store_thm(
  "poly_peval_peval_X_exp_X_exp",
  ``!r:'a ring. Ring r ==> !p. poly p ==>
    !n m. peval (peval p (X ** n)) (X ** m) = peval p (X ** (n * m))``,
  rpt strip_tac >>
  `peval (peval p (X ** n)) (X ** m) = peval p ((X ** m) ** n)` by rw[poly_peval_peval_X_exp] >>
  metis_tac[poly_X, poly_exp_mult, MULT_COMM]);
(* Note: not in polyEval, as this uses poly_peval_peval_X_exp above. *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
