(* ------------------------------------------------------------------------- *)
(* Finite Field: Minimal Polynomial                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffMinimal";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "ffUnityTheory"; *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;

open VectorSpaceTheory;
open SpanSpaceTheory;
open LinearIndepTheory;
open FiniteVSpaceTheory;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperListTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* (* val _ = load "groupInstancesTheory"; -- in ringInstancesTheory *) *)
(* (* val _ = load "ringInstancesTheory"; *) *)
(* (* val _ = load "fieldInstancesTheory"; *) *)
open monoidTheory groupTheory ringTheory fieldTheory;
open monoidOrderTheory groupOrderTheory fieldOrderTheory;
open subgroupTheory;
open groupInstancesTheory ringInstancesTheory fieldInstancesTheory;

(* Get polynomial theory of Ring *)
(* (* val _ = load "polyFieldModuloTheory"; *) *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;
open polyMonicTheory polyEvalTheory;
open polyDividesTheory;
open polyRootTheory;

(* (* val _ = load "polyFieldDivisionTheory"; *) *)
open fieldMapTheory;
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyIrreducibleTheory;

(* (* val _ = load "ringBinomialTheory"; *) *)
open ringBinomialTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;


(* ------------------------------------------------------------------------- *)
(* Finite Field Minimal Polynomial Documentation                             *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   ebasis             = element_powers_basis r
   p <o> b            = \(p:'a poly) (b:'a list). VectorSum r.sum (MAP2 r.prod.op p b)
   subfield_monics x  = subfield_monics_of_element r s x
   Minimals x         = poly_minimals r s x
   minimal x          = poly_minimal r s x
   degree x           = poly_deg (r:'a ring) (poly_minimal (r:'a ring) (s:'a ring) x)
   degree_ x          = poly_deg (r_:'b ring) (poly_minimal (r_:'b ring) (s_:'b ring) x)
   pfmonic            = poly_monic (PF r)
   pfipoly            = irreducible (PolyRing (PF r))
   pfppideal          = principal_ideal (PolyRing r)
   sideal             = set_to_ideal r
*)
(* Definitions and Theorems (# are exported):

   Minimal Polynomial via Linear Independence:
   element_powers_basis_def       |- !r x n. ebasis x n = GENLIST (\j. x ** j) (SUC n)
   element_powers_basis_0         |- !r x. ebasis x 0 = [#1]
   element_powers_basis_suc       |- !r x. ebasis x (SUC n) = SNOC (x ** SUC n) (ebasis x n)
   element_powers_basis_is_basis  |- !r. Ring r ==> !x. x IN R ==> !n. basis r.sum (ebasis x n)
   element_powers_basis_length    |- !n. LENGTH (ebasis x n) = SUC n
   element_powers_basis_dependent |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                     ~LinearIndepBasis s r.sum $* (ebasis x (dim s r.sum $* ))
   element_powers_basis_dim_dep   |- !r. FiniteField r ==> !x. x IN R ==>
                                     ~LinearIndepBasis (PF r) r.sum $* (ebasis x (dim (PF r) r.sum $* ))

   stick_is_weak                |- !r p n. p IN sticks r n ==> weak p
   subfield_poly_weak_is_weak   |- !r s. s <<= r ==> !p. Weak s p ==> weak p
   subfield_stick_is_weak       |- !r s. s <<= r ==> !p n. p IN sticks s n ==> weak p
   subfield_sticks_vsum_eq_eval |- !r s. s <<= r ==> !p n. p IN sticks s (SUC n) ==>
                                     !x. x IN R ==> (p <o> ebasis x n = eval p x)
   subfield_poly_of_element     |- !r s. FiniteField r /\ s <<= r ==>
                                   !x. x IN R ==> ?p. Poly s p /\ 0 < deg p /\ root p x
   subfield_monic_of_element    |- !r s. FiniteField r /\ s <<= r ==>
                                   !x. x IN R ==> ?p. poly_monic s p /\ 0 < deg p /\ root p x

   Minimal Polynomial in Subfield:
   subfield_monics_of_element_def  |- !r s x. subfield_monics x =
                                              {p | poly_monic s p /\ 0 < deg p /\ root p x}
   poly_minimals_def    |- !r s x. Minimals x =
                           preimage deg (subfield_monics x) (MIN_SET (IMAGE deg (subfield_monics x)))
   poly_minimal_def     |- !r s x. minimal x = CHOICE (Minimals x)
   subfield_monics_of_element_member   |- !r s x p. p IN subfield_monics x <=>
                                              poly_monic s p /\ 0 < deg p /\ root p x
   subfield_monics_of_element_nonempty |- !r s. FiniteField r /\ s <<= r ==>
                                          !x. x IN R ==> subfield_monics x <> {}
   poly_minimals_member     |- !p. p IN Minimals x <=> poly_monic s p /\ 0 < deg p /\ root p x /\
                               (deg p = MIN_SET (IMAGE deg (subfield_monics x)))
   poly_minimals_deg_pos    |- !r s. FiniteField r /\ s <<= r ==>
                               !x. x IN R ==> 0 < MIN_SET (IMAGE deg (subfield_monics x))
   poly_minimals_has_monoimal_condition  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                               !p. poly_monic s p /\ (deg p = 1) /\ root p x ==> p IN Minimals x
   poly_minimals_nonempty   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> Minimals x <> {}
   poly_minimal_property    |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                     minimal x IN subfield_monics x /\
                                     (degree x = MIN_SET (IMAGE deg (subfield_monics x)))
   poly_minimal_subfield_property |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                     poly_monic s (minimal x) /\ 0 < degree x /\ root (minimal x) x
   poly_minimal_spoly             |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> Poly s (minimal x)
   poly_minimal_poly              |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> poly (minimal x)
   poly_minimal_deg_pos           |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> 0 < degree x
   poly_minimal_not_unit          |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> ~upoly (minimal x)
   poly_minimal_ne_poly_one       |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> minimal x <> |1|
   poly_minimal_ne_poly_zero      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> minimal x <> |0|
   poly_minimal_has_element_root  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> root (minimal x) x
   poly_minimal_monic             |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> monic (minimal x)
   poly_minimal_pmonic            |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> pmonic (minimal x)
   poly_minimal_divides_subfield_poly |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                         !p. Poly s p /\ root p x ==> minimal x pdivides p
   poly_minimal_divides_subfield_poly_alt
                                      |- !r s. FiniteField r /\ s <<= r ==>
                                         !p x. Poly s p /\ x IN roots p ==> minimal x pdivides p
   poly_minimal_divides_subfield_poly_iff
                                      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                         !p. Poly s p ==> (root p x <=> minimal x pdivides p)
   poly_minimal_eval_congruence       |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                         !p q. Poly s p /\ Poly s q ==>
                                               ((eval p x = eval q x) <=> (p % minimal x = q % minimal x))
   poly_minimal_divides_unity_order   |- !r s. FiniteField r /\ s <<= r ==>
                                         !x. x IN R ==> minimal x pdivides unity (forder x)

   Minimal Polynomial is unique and irreducible:
   poly_minimals_sing      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> SING (Minimals x)
   poly_minimal_zero       |- !r s. FiniteField r /\ s <<= r ==> (minimal #0 = X)
   poly_minimal_one        |- !r s. FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|)
   poly_minimal_eq_X       |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> ((minimal x = X) <=> (x = #0))
   poly_minimal_subfield_irreducible  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> IPoly s (minimal x)

   Minimal Polynomial of Prime Field:
   prime_field_stick_is_weak      |- !r. FiniteField r ==> !p n. p IN sticks (PF r) n ==> weak p

   vsum_element_powers_basis_eq_eval  |- !r. FiniteField r ==> !p n. p IN sticks (PF r) (SUC n) ==>
                                        !x. x IN R ==> (p <o> ebasis x n = eval p x)
   poly_prime_field_with_root_exists        |- !r. FiniteField r ==> !x. x IN R ==>
                                               ?p. pfpoly p /\ 0 < deg p /\ root p x
   poly_prime_field_monic_with_root_exists  |- !r. FiniteField r ==> !x. x IN R ==>
                                               ?p. pfmonic p /\ 0 < deg p /\ root p x

   Ideals of Polynomial Ring:
   poly_ring_zero_ideal        |- !r. Ring r ==> !p. poly p ==> ((pfppideal p = pfppideal |0|) <=> (p = |0|))
   poly_ring_ideal_gen_monic   |- !r. Field r ==> !i. i << PolyRing r /\ i <> pfppideal |0| ==>
                                  ?p. monic p /\ (i = pfppideal p)
   poly_field_principal_ideal_equal  |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                            ((pfppideal p = pfppideal q) <=> ?u. poly u /\ upoly u /\ (p = u * q))
   poly_ring_ideal_monic_gen_unique  |- !r. Field r ==> !p q. monic p /\ monic q /\
                                            (pfppideal p = pfppideal q) ==> (p = q)

   The Ideal of Polynomials sharing a root:
   set_to_ideal_def      |- !r s. sideal s =
                               <|carrier := s;
                                     sum := <|carrier := s; op := $+; id := #0|>;
                                    prod := <|carrier := s; op := $*; id := #1|>
                                |>
   poly_root_poly_ideal  |- !r. Ring r ==> !z. z IN R ==>
                                set_to_ideal (PolyRing r) {p | poly p /\ root p z} << PolyRing r

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Minimal Polynomial via Linear Independence                                *)
(* ------------------------------------------------------------------------- *)

(*
Timothy Murphy -- Finite Field (course notes) p.29, Posposition 8.

Theorem: Let F be a finite field with prime subfield P.
Each element of a IN F is a root of a unique irreducible polynomial m(x) over P.
If |F| = p**n, then deg m(x) <= n.
For each polynomial f(x) over P, f(a) = 0  iff m(x) | f(x)
Proof:
Let a IN F, and n = Dim (PF) F (or F = char r ** n). Then (n+1) elements:
       1, a, a**2, a**3, ...., a**n
must be linearly dependent, i.e.   c_0 + c_1 a + c_2 a **2 + ... + c_n a**n = 0
for some c_j IN P (not all zero). In other words, a is a root of the polynomial
      f(x) = c_0 + c_1 x + c_2 x **2 + ... + c_n x**n
Now, let m(x) be the polynomial of smallest degree > 0 satisifed by a.
Then deg m <= deg f <= n.
Also, m(x) must be irreducible. For if m(x) = u(x) v(x)
Then  0 = m(a) = u(a) v(a) ==> u(a) = 0 or v(a) = 0  since F is a field.
But this contradicts the minimality of m(x).
Finally, suppose f(x) in P(x) has f(a) = 0.
Divide f(x) by m(x):   f(x) = m(x) q(x) + r(x)     where deg r(x) < m(x)
Then r(a) = f(a) - m(a)q(a) = 0
and so r(x) = 0 by the minimality of m(x), i.e. m(x) | f(x).
This last result shows in particular that m(x) is the only irreducible polynomial
(up to a scalar multiple) satisfied by a.
*)

(* Define a basis compose of element powers *)
val element_powers_basis_def = Define`
   element_powers_basis (r:'a ring) (x:'a) n = GENLIST (\j. x ** j) (SUC n)
`;
(* overload on element powers basis *)
val _ = overload_on("ebasis", ``element_powers_basis r``);

(* Overload the vector sum of ring prod group between poly and base. *)
val _ = overload_on("<o>", ``\(p:'a poly) (b:'a list). VectorSum r.sum (MAP2 r.prod.op p b)``);
val _ = set_fixity "<o>" (Infixl 500); (* same as + in arithmeticScript.sml *)

(* Theorem: !x. ebasis x 0 = [#1] *)
(* Proof:
     ebasis x 0
   = GENLIST (\j. x ** j) (SUC 0)  by element_powers_basis_def
   = SNOC ((\j. x ** j) 0) (GENLIST (\j. x ** j) 0)   by GENLIST
   = SNOC ((\j. x ** j) 0) []                         by GENLIST
   = [((\j. x ** j) 0)]                               by SNOC
   = [x ** 0]                                         by application
   = [#1]                                             by ring_exp_0
*)
val element_powers_basis_0 = store_thm(
  "element_powers_basis_0",
  ``!r:'a field. !x. ebasis x 0 = [#1]``,
  rw[element_powers_basis_def]);

(* Theorem: ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n) *)
(* Proof:
     ebasis x (SUC n)
   = GENLIST (\j. x ** j) (SUC (SUC n))                by element_powers_basis_def
   = SNOC ((\j. x ** j) (SUC n)) (GENLIST (\j. x ** j) (SUC n))   by GENLIST
   = SNOC ((\j. x ** j) (SUC n)) (ebasis x n)          by element_powers_basis_def
   = SNOC (x ** (SUC n)) (ebasis x n)                  by application
*)
val element_powers_basis_suc = store_thm(
  "element_powers_basis_suc",
  ``!r:'a field. !x. ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n)``,
  rpt strip_tac >>
  `!n. (\j. x ** j) n = x ** n` by rw[] >>
  metis_tac[element_powers_basis_def, GENLIST]);

(* Theorem: Ring r ==> !x. x IN R ==> !n. basis r.sum (ebasis x n) *)
(* Proof:
       basis r.sum (ebasis x n)
   <=> !y. MEM y (ebasis x n) ==> y IN r.sum.carrier         by basis_member
   <=> !y. MEM y (ebasis x n) ==> y IN R                     by ring_carriers
   <=> !y. MEM y (GENLIST (\j. x ** j) (SUC n)) ==> y IN R   by element_powers_basis_def
   <=> !y. ?m. m < SUC n /\ (y = (\j. x ** j) m) ==> y IN R  by MEM_GENLIST
   <=> !y. j < SUC n ==> x ** j IN R                         by application
   <=> T                                                     by ring_exp_element
*)
val element_powers_basis_is_basis= store_thm(
  "element_powers_basis_is_basis",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. basis r.sum (ebasis x n)``,
  rw[element_powers_basis_def, basis_member, MEM_GENLIST] >>
  rw[]);

(* Theorem: LENGTH (ebasis x n) = SUC n *)
(* Proof:
     LENGTH (ebasis x n)
   = LENGTH (GENLIST (\j. x ** j) (SUC n))  by element_powers_basis_def
   = SUC n                                  by LENGTH_GENLIST
*)
val element_powers_basis_length = store_thm(
  "element_powers_basis_length",
  ``!n. LENGTH (ebasis x n) = SUC n``,
  rw[element_powers_basis_def]);

(* Theorem: FiniteField r ==> !s:'a field. s <<= r ==> !x. x IN R ==>
            ~LinearIndepBasis s r.sum $* (ebasis x (dim s r.sum $* ) *)
(* Proof:
   Let n = dim s r.sum $*.
   Since FiniteField r
     ==> FiniteVSpace s r.sum $*         by finite_subfield_is_finite_vspace_scalar
     and basis r.sum (ebasis x n)        by element_powers_basis_is_basis, field_is_ring
     and n < LENGTH (ebasis x n)         by element_powers_basis_length, n < SUC n
   Hence ~LinearIndepBasis s r.sum $* (ebasis x n)
                                         by finite_vspace_basis_dep
*)
val element_powers_basis_dependent = store_thm(
  "element_powers_basis_dependent",
  ``!r:'a field. FiniteField r ==> !s:'a field. s <<= r ==> !x. x IN R ==>
    ~LinearIndepBasis s r.sum $* (ebasis x (dim s r.sum $* ))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `n = dim s r.sum $*` >>
  `FiniteVSpace s r.sum $*` by rw[finite_subfield_is_finite_vspace_scalar] >>
  `basis r.sum (ebasis x n)` by rw[element_powers_basis_is_basis] >>
  `n < LENGTH (ebasis x n)` by rw[element_powers_basis_length] >>
  metis_tac[finite_vspace_basis_dep]);

(* Theorem: FiniteField r ==> !x. x IN R ==>
            ~LinearIndepBasis (PF r) r.sum $* (ebasis x (dim (PF r) r.sum $* )) *)
(* Proof:
   Let n = dim (PF r) r.sum $*.
   Since FiniteField r
     ==> FiniteVSpace (PF r) r.sum $*     by finite_field_is_finite_vspace
     and basis r.sum (ebasis x n)         by element_powers_basis_is_basis, field_is_ring
     and n < LENGTH (ebasis x n)          by element_powers_basis_length, n < SUC n
   Hence ~LinearIndepBasis (PF r) r.sum $* (ebasis x n)
                                          by finite_vspace_basis_dep
*)
val element_powers_basis_dim_dep = store_thm(
  "element_powers_basis_dim_dep",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==>
    ~LinearIndepBasis (PF r) r.sum $* (ebasis x (dim (PF r) r.sum $* ))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `n = dim (PF r) r.sum $*` >>
  `FiniteVSpace (PF r) r.sum $*` by rw[finite_field_is_finite_vspace] >>
  `basis r.sum (ebasis x n)` by rw[element_powers_basis_is_basis] >>
  `n < LENGTH (ebasis x n)` by rw[element_powers_basis_length] >>
  metis_tac[finite_vspace_basis_dep]);

(* Theorem: !n. p IN sticks r n ==> weak p *)
(* Proof:
   By induction on n.
   Base case: !p. p IN sticks r 0 ==> weak p
         p IN sticks r 0
     ==> p IN {[]}            by sticks_0
     ==> p = []               by IN_SING
     and weak [] = T          by weak_of_zero
   Step case: !p. p IN sticks r n ==> weak p ==>
              !p. p IN sticks r (SUC n) ==> weak p
         p IN sticks r (SUC n)
     ==> ?h t. h IN R /\ t IN sticks r n /\ (p = h::t)   by stick_cons
     ==> h IN R /\ weak t /\ (p = h::t)                  by induction hypothesis
     ==> weak p                                          by weak_cons
*)
val stick_is_weak = store_thm(
  "stick_is_weak",
  ``!(r:'a field) p  n. p IN sticks r n ==> weak p``,
  strip_tac >>
  Induct_on `n` >-
  rw[sticks_0] >>
  metis_tac[stick_cons, weak_cons]);

(* Theorem: s <<= r ==> !p. Weak s p ==> weak p *)
(* Proof:
   By induction on p.
   Base case: Weak s [] ==> weak []
      True by weak_of_zero.
   Step case: Weak s p ==> weak p ==> !h. Weak s (h::p) ==> weak (h::p)
          Weak s (h::p)
      ==> h IN s.carrier /\ Weak s p   by weak_cons
      ==> h IN s.carrier /\ weak s p   by induction hypothesis
      ==> h IN R /\ weak s p           by subfield_element
      ==> weak (h::p)                  by weak_cons
*)
val subfield_poly_weak_is_weak = store_thm(
  "subfield_poly_weak_is_weak",
  ``!(r s):'a field. s <<= r ==> !p. Weak s p ==> weak p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  metis_tac[subfield_element]);

(* Theorem: s <<= r ==> !p n. p IN sticks s n ==> weak p *)
(* Proof:
   Since p IN sticks s n
     ==> Weak s p       by stick_is_weak
     ==> weak p         by subfield_poly_weak_is_weak
*)
val subfield_stick_is_weak = store_thm(
  "subfield_stick_is_weak",
  ``!(r s):'a field. s <<= r ==> !p n. p IN sticks s n ==> weak p``,
  metis_tac[stick_is_weak, subfield_poly_weak_is_weak]);

(* Theorem: s <<= r ==> !p n. p IN sticks s (SUC n) ==>
            !x. x IN R ==> (p <o> (ebasis x n) = eval p x) *)
(* Proof:
   By induction on n.
   Base case: !p. p IN sticks s (SUC 0) ==>
              !x. x IN R ==> (p <o> ebasis x 0 = eval p x)
           p IN sticks s (SUC 0)
       ==> p IN sticks s 1            by ONE
       ==> ?c. c IN B /\ (p = [c])    by sticks_1_member
       Note c IN R                    by subfield_element
       Also ebasis x 0 = [#1]         by element_powers_basis_0
          p <o> ebasis x 0
        = VectorSum r.sum (MAP2 $* [c] [#1])       by notation, p = [c], ebasis x 0 = [#1]
        = VectorSum r.sum [c * #1]                 by MAP2
        = VectorSum r.sum [c]                      by ring_mult_rone
        = c + (VectorSum r.sum [])                 by vsum_cons
        = c + #0                                   by vsum_nil
        = c                                        by ring_add_rzero
        = eval [c] x                               by poly_eval_const
   Step case: !p. p IN sticks s (SUC (SUC n)) ==>
              !x. x IN R ==> (p <o> ebasis x (SUC n) = eval p x)
           p IN sticks s (SUC (SUC n))
       ==> ?h t. h IN B /\ t IN sticks s (SUC n) /\ (p = SNOC h t) by stick_snoc
       Note LENGTH t = SUC n                                       by stick_length
       Also ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n)    by element_powers_basis_suc
        and h IN R                        by subfield_element
        and weak t                        by subfield_stick_is_weak
        and eval t x IN R                 by weak_eval_element
         p <o> (ebasis x (SUC n)))
       = (SNOC h t) <o> (SNOC (x ** (SUC n)) (ebasis x n))  by above
       = h * (x ** SUC n) + t <o> (ebasis x n)     by vsum_stick_snoc
       = h * (x ** SUC n) + eval t x               by induction hypothesis
       = eval t x + h * x ** LENGTH t              by ring_add_comm
       = eval (SNOC h t) x                         by weak_eval_snoc
       = eval p x                                  by p = SNOC h t
*)
val subfield_sticks_vsum_eq_eval = store_thm(
  "subfield_sticks_vsum_eq_eval",
  ``!(r s):'a field. s <<= r ==> !p n. p IN sticks s (SUC n) ==>
   !x. x IN R ==> (p <o> (ebasis x n) = eval p x)``,
  ntac 3 strip_tac >>
  Induct_on `n` >| [
    rw[] >>
    `?c. c IN B /\ (p = [c])` by rw[GSYM sticks_1_member] >>
    `c IN R` by metis_tac[subfield_element] >>
    `ebasis x 0 = [#1]` by rw[element_powers_basis_0] >>
    rw[vsum_cons, vsum_nil],
    rpt strip_tac >>
    `?h t. h IN B /\ t IN sticks s (SUC n) /\ (p = SNOC h t)` by rw[GSYM stick_snoc] >>
    `ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n)` by rw_tac std_ss[element_powers_basis_suc] >>
    `VSpace s r.sum $*` by rw[field_is_vspace_over_subfield] >>
    `basis r.sum (ebasis x n)` by rw[element_powers_basis_is_basis] >>
    `LENGTH (ebasis x n) = SUC n` by rw[element_powers_basis_length] >>
    `x ** SUC n IN R /\ (R = r.sum.carrier)` by rw[] >>
    `h IN R` by metis_tac[subfield_element] >>
    `weak t` by metis_tac[subfield_stick_is_weak] >>
    `p <o> (ebasis x (SUC n)) = h * (x ** SUC n) + eval t x` by metis_tac[vsum_stick_snoc] >>
    `_ = h * x ** LENGTH t + eval t x` by metis_tac[stick_length] >>
    `_ = eval t x + h * x ** LENGTH t` by rw[ring_add_comm] >>
    `_ = eval p x` by rw[weak_eval_snoc] >>
    rw[]
  ]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> ?p. Poly s p /\ 0 < deg p /\ root p x *)
(* Proof:
   Let n = dim s r.sum $*, b = ebasis x n.
    Then ~LinearIndepBasis s r.sum $* b       by element_powers_basis_dependent
    Note basis r.sum b                        by element_powers_basis_is_basis
     and LENGTH b = SUC n                     by element_powers_basis_length
     and s.sum.id = #0                        by subfield_ids
   Hence by LinearIndepBasis_def,
     ?q. q IN sticks s (SUC n) /\
         ~(q <o> b) = #0) <=> !k. k < SUC n ==> (EL k q = #0))   [1]

    Note VSpace s r.sum $*                    by subfield_is_vspace_scalar
     and !k. k < SUC n ==> (EL k q = #0)) ==> (q <o> b) = #0)   by vspace_stick_zero
    Thus ?k. k < SUC n /\ (EL k p <> #0) /\ (q <o> b) = #0)     by [1]
     Now Weak s q                             by stick_is_weak
     and LENGTH q = SUC n                     by stick_length
      so ~(zero_poly s q)                     by zero_poly_element, EL k q <> #0
   Let p = poly_chop s q
   Then Poly s p                              by poly_chop_weak_poly
    and ~(zero_poly s p)                      by zero_poly_eq_zero_poly_chop
   thus p <> (PolyRing s).sum.id              by zero_poly_eq_poly_zero
     or p <> |0|                              by subring_poly_ids, subfield_is_subring
   Also eval p x = eval (poly_chop s q) x
                 = eval (chop q) x            by subring_poly_chop
                 = eval q x                   by poly_eval_chop
                 = q <o> b                    by subfield_sticks_vsum_eq_eval
                 = #0                         by above
  Hence root p x                              by poly_root_def
   with 0 < deg p                             by poly_nonzero_with_root_deg_pos
*)
val subfield_poly_of_element = store_thm(
  "subfield_poly_of_element",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> ?p. Poly s p /\ 0 < deg p /\ root p x``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `n = dim s r.sum $*` >>
  qabbrev_tac `b = ebasis x n` >>
  `~LinearIndepBasis s r.sum $* b` by rw[element_powers_basis_dependent, Abbr`n`, Abbr`b`] >>
  `basis r.sum b` by rw[element_powers_basis_is_basis, Abbr`b`] >>
  `LENGTH b = SUC n` by rw[element_powers_basis_length, Abbr`b`] >>
  `s.sum.id = #0` by rw[subfield_ids] >>
  `?q. q IN sticks s (SUC n) /\
    ~((q <o> b = #0) <=> !k. k < SUC n ==> (EL k q = #0))` by metis_tac[LinearIndepBasis_def] >>
  `VSpace s r.sum $*` by rw[subfield_is_vspace_scalar] >>
  `?k. k < SUC n /\ (EL k q <> #0) /\ (q <o> b = #0)` by metis_tac[vspace_stick_zero] >>
  `Weak s q` by metis_tac[stick_is_weak] >>
  qexists_tac `poly_chop s q` >>
  `Poly s (poly_chop s q)` by metis_tac[poly_chop_weak_poly] >>
  `eval q x = #0` by metis_tac[subfield_sticks_vsum_eq_eval] >>
  `root (chop q) x` by rw[poly_root_def] >>
  `Ring r /\ Ring s /\ s <= r` by rw[subfield_is_subring] >>
  `root (poly_chop s q) x` by metis_tac[subring_poly_chop] >>
  `~(zero_poly s q)` by metis_tac[zero_poly_element, stick_length] >>
  `~(zero_poly s (poly_chop s q))` by metis_tac[zero_poly_eq_zero_poly_chop] >>
  `(poly_chop s q) <> |0|` by metis_tac[zero_poly_eq_poly_zero, subring_poly_ids] >>
  `poly (poly_chop s q)` by metis_tac[subring_poly_poly] >>
  `0 < deg (poly_chop s q)` by metis_tac[poly_nonzero_with_root_deg_pos] >>
  rw[]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> ?p. poly_monic s p /\ 0 < deg p /\ root p x *)
(* Proof:
   Since FiniteField r and s <<= r,
     ==> ?q. Poly q /\ 0 < deg q /\ root q x   by subfield_poly_of_element
    Note poly_zero s = |0|                     by subring_poly_ids
   Hence ?u p. Poly s u /\ poly_monic s p /\
         (poly_deg s p = poly_deg s q) /\
         (p = poly_mult s u q)                 by poly_monic_mult_by_factor, poly_unit_poly
    with 0 < deg q = poly_deg s q = poly_deg s p = deg p
                                               by subring_poly_deg
   Since Poly s p                              by poly_monic_poly
    Thus poly u /\ poly p /\ poly q /\         by subring_poly_poly
        (p = u * q)                            by subring_poly_mult
       eval p x
     = (eval u x) * (eval q x)                 by poly_eval_mult
     = (eval u x) * #0                         by poly_root_def
     = #0                                      by poly_eval_element, field_mult_rzero
   Hence root p x                              by poly_root_def
*)
val subfield_monic_of_element = store_thm(
  "subfield_monic_of_element",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> ?p. poly_monic s p /\ 0 < deg p /\ root p x``,
  rpt (stripDup[FiniteField_def]) >>
  `s <= r` by rw[subfield_is_subring] >>
  `?q. Poly s q /\ 0 < deg q /\ root q x` by rw_tac std_ss[subfield_poly_of_element] >>
  `poly_zero s = |0|` by rw[subring_poly_ids] >>
  `q <> |0|` by rw[poly_deg_pos_nonzero] >>
  `?u p. Poly s u /\ poly_monic s p /\
    (poly_deg s p = poly_deg s q) /\ (p = poly_mult s u q)` by metis_tac[poly_monic_mult_by_factor, poly_unit_poly] >>
  `0 < deg p` by metis_tac[subring_poly_deg] >>
  `Poly s p` by rw[] >>
  `poly u /\ poly p /\ poly q /\ (p = u * q)` by metis_tac[subring_poly_poly, subring_poly_mult] >>
  `eval p x = (eval u x) * (eval q x)` by rw[poly_eval_mult] >>
  `_ = (eval u x) * #0` by metis_tac[poly_root_def] >>
  `_ = #0` by rw[] >>
  metis_tac[poly_root_def]);

(* ------------------------------------------------------------------------- *)
(* Minimal Polynomial in Subfield                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the set of monic subfield polynomials having an element as a root *)
val subfield_monics_of_element_def = Define `
    subfield_monics_of_element (r:'a ring) (s:'a ring) (x: 'a) =
      { p | poly_monic s p /\ 0 < deg p /\ root p x }
`;

(* Define the set of minimial polynomials of an element in a subfield *)
val poly_minimals_def = Define `
    poly_minimals (r:'a ring) (s:'a ring) (x: 'a) =
       preimage deg (subfield_monics_of_element r s x)
          (MIN_SET (IMAGE deg (subfield_monics_of_element r s x)))
`;

(* Define minimial polynomial of an element in a subfield *)
val poly_minimal_def = Define `
    poly_minimal (r:'a ring) (s:'a ring) (x: 'a) = CHOICE (poly_minimals r s x)
`;

(* Define overloads *)
val _ = overload_on("subfield_monics", ``subfield_monics_of_element r s``);
val _ = overload_on("Minimals", ``poly_minimals r s``);
val _ = overload_on("minimal", ``poly_minimal r s``);

(* Overload on the degree of minimal polynomial *)
val _ = overload_on("degree", ``\x. poly_deg (r:'a ring) (poly_minimal (r:'a ring) (s:'a ring) x)``);
val _ = overload_on("degree_", ``\x. poly_deg (r_:'b ring) (poly_minimal (r_:'b ring) (s_:'b ring) x)``);

(*
> subfield_monics_of_element_def;
val it = |- !r s x. subfield_monics x = {p | poly_monic s p /\ 0 < deg p /\ root p x}: thm
> poly_minimals_def;
val it = |- !r s x. Minimals x = preimage deg (subfield_monics x) (MIN_SET (IMAGE deg (subfield_monics x))): thm
> poly_minimal_def;
val it = |- !r s x. minimal x = CHOICE (Minimals x): thm
*)

(* Theorem: p IN subfield_monics x <=> poly_monic s p /\ 0 < deg p /\ root p x *)
(* Proof: by subfield_monics_of_element_def *)
val subfield_monics_of_element_member = store_thm(
  "subfield_monics_of_element_member",
  ``!(r s):'a field x p:'a poly. p IN subfield_monics x <=> poly_monic s p /\ 0 < deg p /\ root p x``,
  rw[subfield_monics_of_element_def]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> subfield_monics x <> {} *)
(* Proof: by subfield_monic_of_element *)
val subfield_monics_of_element_nonempty = store_thm(
  "subfield_monics_of_element_nonempty",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> subfield_monics x <> {}``,
  metis_tac[subfield_monic_of_element, subfield_monics_of_element_member, MEMBER_NOT_EMPTY]);

(* Theorem: p IN Minimals x <=> poly_monic s p /\ 0 < deg p /\ root p x /\
            (deg p = MIN_SET (IMAGE deg (subfield_monics x))) *)
(* Proof: by preimage_def, poly_minimals_def, subfield_monics_of_element_member *)
val poly_minimals_member = store_thm(
  "poly_minimals_member",
  ``!p. p IN Minimals x <=> poly_monic s p /\ 0 < deg p /\ root p x /\
    (deg p = MIN_SET (IMAGE deg (subfield_monics x)))``,
  rw[preimage_def, poly_minimals_def] >>
  metis_tac[subfield_monics_of_element_member]);

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !x. x IN R ==> 0 < MIN_SET (IMAGE deg (subfield_monics x)) *)
(* Proof:
   Let t = subfield_monics x.
   Then t <> {}                         by subfield_monics_of_element_nonempty
     so IMAGE deg t <> {}               by IMAGE_EQ_EMPTY
    Claim: 0 NOTIN (IMAGE deg t),
      then MIN_SET (IMAGE deg t) <> 0   by MIN_SET_LEM
        or 0 < MIN_SET (IMAGE deg t)
    For the claim, prove by contradiction.
       Let 0 IN (IMAGE deg t),
       It means there is p IN t /\ deg p = 0   by IN_IMAGE
       but p IN t ==> 0 < deg p                by subfield_monics_of_element_member
       which is a contradiction.
*)
val poly_minimals_deg_pos = store_thm(
  "poly_minimals_deg_pos",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> 0 < MIN_SET (IMAGE deg (subfield_monics x))``,
  metis_tac[subfield_monics_of_element_nonempty, IMAGE_EQ_EMPTY, IN_IMAGE,
      subfield_monics_of_element_member, MIN_SET_LEM, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !x. x IN R ==> !p. Monic s p /\ (deg p = 1) /\ root p x ==> p IN Minimals x *)
(* Proof:
   Let t = subfield_monics x.
   Then t <> {}                         by subfield_monics_of_element_nonempty
     so IMAGE deg t <> {}               by IMAGE_EQ_EMPTY
   By poly_minimals_member, need to show:  1 = MIN_SET (IMAGE deg t).
   Since deg p = 1,  0 < deg p
    thus p IN t                         by subfield_monics_of_element_member
     and deg p IN IMAGE deg t           by IN_IMAGE
      or 1 IN IMAGE deg t               by deg p = 1
   Hence MIN_SET (IMAGE deg t) <= 1     by MIN_SET_LEM
     But 0 < MIN_SET (IMAGE deg t)      by poly_minimals_deg_pos
    Thus MIN_SET (IMAGE deg t) = 1.
*)
val poly_minimals_has_monoimal_condition = store_thm(
  "poly_minimals_has_monoimal_condition",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> !p. Monic s p /\ (deg p = 1) /\ root p x ==> p IN Minimals x``,
  rw[poly_minimals_member] >>
  qabbrev_tac `t = subfield_monics x` >>
  `t <> {}` by rw[subfield_monics_of_element_nonempty, Abbr`t`] >>
  `IMAGE deg t <> {}` by rw[IMAGE_EQ_EMPTY] >>
  `0 < deg p` by decide_tac >>
  `p IN t` by rw[subfield_monics_of_element_member, Abbr`t`] >>
  `deg p IN IMAGE deg t` by rw[] >>
  `MIN_SET (IMAGE deg t) <= 1` by metis_tac[MIN_SET_LEM] >>
  `0 < MIN_SET (IMAGE deg t)` by metis_tac[poly_minimals_deg_pos] >>
  decide_tac);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> Minimals x <> {} *)
(* Proof:
   Let t = subfield_monics x, y = MIN_SET (IMAGE deg t).
   Since t <> {}                      by subfield_monics_of_element_nonempty
      so IMAGE deg t <> {}            by IMAGE_EQ_EMPTY
     and y IN (IMAGE deg t)           by MIN_SET_LEM
    thus ?p. p IN t /\ (deg p = y)    by IN_IMAGE
     and p IN preimage deg t y        by in_preimage
      or p IN Minimals x              by poly_minimals_def
   Hence Minimals x <> {}             by MEMBER_NOT_EMPTY
*)
val poly_minimals_nonempty = store_thm(
  "poly_minimals_nonempty",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> Minimals x <> {}``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = subfield_monics x` >>
  qabbrev_tac `y = MIN_SET (IMAGE deg t)` >>
  `t <> {}` by rw[subfield_monics_of_element_nonempty, Abbr`t`] >>
  `IMAGE deg t <> {}` by rw[IMAGE_EQ_EMPTY] >>
  `y IN (IMAGE deg t)` by rw[MIN_SET_LEM, Abbr`y`] >>
  metis_tac[IN_IMAGE, in_preimage, poly_minimals_def, MEMBER_NOT_EMPTY]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==>
            (minimal x) IN (subfield_monics x) /\
            (degree x = MIN_SET (IMAGE deg (subfield_monics x))) *)
(* Proof:
   Let t = subfield_monics x, y = MIN_SET (IMAGE deg t), and p = minimal x.
   Then p = CHOICE (preimage deg t y)   by poly_minimal_def, poly_minimals_def
    Now t <> {}                         by subfield_monics_of_element_nonempty
     so IMAGE deg t <> {}               by IMAGE_EQ_EMPTY, t <> {}
   Thus y IN (IMAGE deg t)              by MIN_SET_LEM, IMAGE deg t <> {}
   Hence the result                     by preimage_choice_property
*)
val poly_minimal_property = store_thm(
  "poly_minimal_property",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==>
      (minimal x) IN (subfield_monics x) /\
      (degree x = MIN_SET (IMAGE deg (subfield_monics x)))``,
  ntac 6 (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = subfield_monics x` >>
  qabbrev_tac `y = MIN_SET (IMAGE deg t)` >>
  qabbrev_tac `p = minimal x` >>
  `p = CHOICE (preimage deg t y)` by rw[poly_minimal_def, poly_minimals_def, Abbr`p`, Abbr`t`, Abbr`y`] >>
  `t <> {}` by rw[subfield_monics_of_element_nonempty, Abbr`t`] >>
  `IMAGE deg t <> {}` by rw[IMAGE_EQ_EMPTY] >>
  `y IN (IMAGE deg t)` by rw[MIN_SET_LEM, Abbr`y`] >>
  rw[preimage_choice_property]);

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !x. x IN R ==> poly_monic s (minimal x) /\ 0 < degree x /\ root (minimal x) x *)
(* Proof:
   Let t = subfield_monics x, y = MIN_SET (IMAGE deg t), and p = minimal x.
   Then p IN t /\ (deg p = y)         by poly_minimal_property
    and result follows                by subfield_monics_of_element_member
*)
val poly_minimal_subfield_property = store_thm(
  "poly_minimal_subfield_property",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
    !x. x IN R ==> poly_monic s (minimal x) /\ 0 < degree x /\ root (minimal x) x``,
  metis_tac[poly_minimal_property, subfield_monics_of_element_member]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> Poly s (minimal x) *)
(* Proof:
   Let t = subfield_monics x, y = MIN_SET (IMAGE deg t), and p = minimal x.
   Since poly_monic s p       by poly_minimal_subfield_property
     or Poly s p              by poly_monic_poly
*)
val poly_minimal_spoly = store_thm(
  "poly_minimal_spoly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> Poly s (minimal x)``,
  rw[poly_minimal_subfield_property]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> poly (minimal x) *)
(* Proof: by poly_minimal_spoly, subfield_is_subring, subring_poly_poly *)
val poly_minimal_poly = store_thm(
  "poly_minimal_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> poly (minimal x)``,
  metis_tac[poly_minimal_spoly, subfield_is_subring, subring_poly_poly]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> 0 < degree x *)
(* Proof: by poly_minimal_subfield_property *)
val poly_minimal_deg_pos = store_thm(
  "poly_minimal_deg_pos",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> 0 < degree x``,
  rw[poly_minimal_subfield_property]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> ~upoly (minimal x) *)
(* Proof:
   Since 0 < degree x                 by poly_minimal_deg_pos
     but !p. upoly p ==> deg p = 0    by poly_field_unit_deg, Field r
      so ~upoly (minimal x)
*)
val poly_minimal_not_unit = store_thm(
  "poly_minimal_not_unit",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> ~upoly (minimal x)``,
  metis_tac[poly_minimal_deg_pos, poly_field_unit_deg, finite_field_is_field, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x <> |1|) *)
(* Proof:
   Since 0 < degree x       by poly_minimal_deg_pos
     but deg |1| = 0        by poly_deg_one
      so minimal x <> |1|
*)
val poly_minimal_ne_poly_one = store_thm(
  "poly_minimal_ne_poly_one",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x <> |1|)``,
  rpt (stripDup[FiniteField_def]) >>
  `deg |1| = 0` by rw[] >>
  metis_tac[poly_minimal_deg_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x <> |0|) *)
(* Proof:
   Since 0 < degree x       by poly_minimal_deg_pos
     but deg |0| = 0        by poly_deg_zero
      so minimal x <> |0|
*)
val poly_minimal_ne_poly_zero = store_thm(
  "poly_minimal_ne_poly_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x <> |0|)``,
  rpt (stripDup[FiniteField_def]) >>
  `deg |0| = 0` by rw[] >>
  metis_tac[poly_minimal_deg_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> root (minimal x) x *)
(* Proof: by poly_minimal_subfield_property *)
val poly_minimal_has_element_root = store_thm(
  "poly_minimal_has_element_root",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> root (minimal x) x``,
  rw[poly_minimal_subfield_property]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> monic (minimal x) *)
(* Proof: by poly_minimal_subfield_property, subfield_is_subring, subring_poly_monic *)
val poly_minimal_monic = store_thm(
  "poly_minimal_monic",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> monic (minimal x)``,
  metis_tac[poly_minimal_subfield_property, subfield_is_subring, subring_poly_monic]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> pmonic (minimal x) *)
(* Proof: by poly_minimal_monic, poly_minimal_deg_pos, poly_monic_pmonic *)
val poly_minimal_pmonic = store_thm(
  "poly_minimal_pmonic",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> pmonic (minimal x)``,
  rw[poly_minimal_monic, poly_minimal_deg_pos, poly_monic_pmonic]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==>
            !p. Poly s p /\ root p x ==> (minimal x) pdivides p *)
(* Proof:
   Let q = minimal x.
    Then poly_monic s q        by poly_minimal_subfield_property
     and Poly s q              by poly_monic_poly
     and 0 < deg q             by poly_minimal_deg_pos
      so 0 < Deg s q           by subring_poly_deg
      or Pmonic s q            by poly_monic_pmonic
   Hence ?u v. Poly s u /\ Poly s v /\
         (p = u * q + v) /\ deg v < deg q      by subring_poly_division_eqn, 0 < deg q
    Note poly p /\ poly q /\ poly u /\ poly v  by subring_poly_poly

   If v = |0|,
     then p = u * q + |0| = u * q       by poly_add_rzero
     Hence q pdivides p                 by poly_divides_def

   If v <> |0|,
   Step 1: show that root z x.
     then v = |1| * p - u * q           by poly_sub_eq_add, poly_mult_lone
   Since root p x                       by given
     and root q x                       by poly_minimal_has_element_root
      so root v x                       by poly_root_sub_linear
    thus 0 < deg v                      by poly_nonzero_with_root_deg_pos
   Let z be the monic version of v,
   i.e. ?t z. Poly s t /\ poly_monic s z
        and (deg z = deg v) /\ (z = t * v) by poly_monic_mult_by_factor, poly_unit_poly
   Then root z x                           by poly_root_mult_comm

   Step 2: show that z IN subfield_monics x.
   With 0 < deg z = deg v,
        z IN subfield_monics x             by subfield_monics_of_element_member

   Step 3, derive a contradiction.
   Let m = subfield_monics x
   Since z IN m, deg z IN IMAGE deg m      by IN_IMAGE
      or IMAGE deg m <> {}                 by MEMBER_NOT_EMPTY
    Thus MIN_SET (IMAGE deg m) <= deg z    by MIN_SET_LEM, IMAGE deg m <> {}
     But deg q = MIN_SET (IMAGE deg m)     by poly_minimal_property
     and deg z = deg v < deg q             by above
   This contradicts with deg q <= deg z.
*)
val poly_minimal_divides_subfield_poly = store_thm(
  "poly_minimal_divides_subfield_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==>
   !p. Poly s p /\ root p x ==> (minimal x) pdivides p``,
  rpt (stripDup[FiniteField_def]) >>
  `s <= r` by rw[subfield_is_subring] >>
  qabbrev_tac `q = minimal x` >>
  `poly_monic s q /\ Poly s q` by rw[poly_minimal_subfield_property, Abbr`q`] >>
  `0 < deg q` by rw[poly_minimal_deg_pos, Abbr`q`] >>
  `Pmonic s q` by metis_tac[poly_monic_pmonic, subring_poly_deg] >>
  `?u v. Poly s u /\ Poly s v /\ (p = u * q + v) /\ deg v < deg q` by rw[subring_poly_division_eqn] >>
  Cases_on `v = |0|` >-
  metis_tac[poly_divides_def, subring_poly_poly, poly_mult_poly, poly_add_rzero] >>
  `poly p /\ poly q /\ poly u /\ poly v` by metis_tac[subring_poly_poly] >>
  `poly |1|` by rw[] >>
  `v = |1| * p - u * q` by metis_tac[poly_sub_eq_add, poly_mult_lone, poly_mult_poly] >>
  `root q x` by rw[poly_minimal_has_element_root, Abbr`q`] >>
  `root v x` by rw[poly_root_sub_linear] >>
  `0 < deg v` by metis_tac[poly_nonzero_with_root_deg_pos] >>
  `poly_zero s = |0|` by rw[subring_poly_ids] >>
  `?t z. Poly s t /\ poly_monic s z /\
     (poly_deg s z = poly_deg s v) /\ (z = poly_mult s t v)` by metis_tac[poly_monic_mult_by_factor, poly_unit_poly, field_is_ring] >>
  `z = t * v` by metis_tac[subring_poly_mult, poly_monic_poly] >>
  `poly t` by metis_tac[subring_poly_poly] >>
  `root z x` by rw[poly_root_mult_comm] >>
  `0 < deg z /\ deg z < deg q` by metis_tac[subring_poly_deg] >>
  `z IN subfield_monics x` by rw[subfield_monics_of_element_member] >>
  qabbrev_tac `m = subfield_monics x` >>
  `deg z IN IMAGE deg m` by rw[] >>
  `IMAGE deg m <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `MIN_SET (IMAGE deg m) <= deg z` by rw[MIN_SET_LEM] >>
  `deg q = MIN_SET (IMAGE deg m)` by rw[poly_minimal_property, Abbr`q`, Abbr`m`] >>
  decide_tac);

(* Theorem: FiniteField r /\ s <<= r ==>
            !p x. Poly s p /\ x IN (roots p) ==> minimal x pdivides p *)
(* Proof: by poly_minimal_divides_subfield_poly, poly_roots_member *)
val poly_minimal_divides_subfield_poly_alt = store_thm(
  "poly_minimal_divides_subfield_poly_alt",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==>
     !p x. Poly s p /\ x IN (roots p) ==> minimal x pdivides p``,
  rw_tac std_ss[poly_minimal_divides_subfield_poly, poly_roots_member]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            !p. Poly s p ==> (root p x <=> (minimal x) pdivides p) *)
(* Proof:
   If part: root p x ==> (minimal x) pdivides p
      True by poly_minimal_divides_subfield_poly.
   Only-if part: (minimal x) pdivides p ==> root p x
      Let q = minimal x.
      Note root q x            by poly_minimal_has_element_root
       Now s <= r              by subfield_is_subring
        so poly p              by subring_poly_poly
       and poly q              by poly_minimal_poly
       ==> root p x            by poly_divides_share_root
*)
val poly_minimal_divides_subfield_poly_iff = store_thm(
  "poly_minimal_divides_subfield_poly_iff",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==>
   !p. Poly s p ==> (root p x <=> (minimal x) pdivides p)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `q = minimal x` >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_minimal_divides_subfield_poly, Abbr`q`] >>
  `root q x` by rw[poly_minimal_has_element_root, Abbr`q`] >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `poly q` by rw[poly_minimal_poly, Abbr`q`] >>
  metis_tac[poly_divides_share_root]);

(* This is a major milestone theorem. *)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> !p q. Poly s p /\ Poly s q ==>
              ((eval p x = eval q x) <=> (p % (minimal x) = q % (minimal x))) *)
(* Proof:
   Let m = minimal x.
   Then monic m                   by poly_minimal_monic
    and 0 < deg m                 by poly_minimal_deg_pos
    ==> pmonic m                  by poly_monic_pmonic
   Let h = poly_sub s p q.
   Note s <<= r ==> s <= r        by subfield_is_subring
     so h = p - q                 by subring_poly_sub
    and Poly s h                  by poly_sub_poly
    and poly p /\ poly q          by subring_poly_poly
        eval p x = eval q x
    <=> eval p x - eval q x = #0  by field_sub_eq_zero
    <=> eval (p - q) x = #0       by poly_eval_sub
    <=> eval h x = #0             by above
    <=> root h x                  by poly_root_def
    <=> m pdivides h              by poly_minimal_divides_subfield_poly_iff
    <=> h % m = |0|               by poly_divides_alt, ulead m
    <=> p % m = q % m             by poly_mod_eq, ulead m
*)
val poly_minimal_eval_congruence = store_thm(
  "poly_minimal_eval_congruence",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN R ==>
   !p q. Poly s p /\ Poly s q ==> ((eval p x = eval q x) <=> (p % (minimal x) = q % (minimal x)))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = minimal x` >>
  qabbrev_tac `h = poly_sub s p q` >>
  `s <= r` by rw[subfield_is_subring] >>
  `Poly s h /\ (h = p - q)` by rw[subring_poly_sub, Abbr`h`] >>
  `monic m` by rw[poly_minimal_monic, Abbr`m`] >>
  `pmonic m` by rw[poly_monic_pmonic, poly_minimal_deg_pos, Abbr`m`] >>
  `poly p /\ poly q` by metis_tac[subring_poly_poly] >>
  `(eval p x = eval q x) <=> (eval p x - eval q x = #0)` by rw[field_sub_eq_zero] >>
  `_ = (eval h x = #0)` by rw[Abbr`h`] >>
  `_ = root h x` by rw[poly_root_def] >>
  `_ = (m pdivides h)` by rw[poly_minimal_divides_subfield_poly_iff, Abbr`m`] >>
  `_ = (h % m = |0|)` by rw[poly_divides_alt] >>
  `_ = (p % m = q % m)` by rw[poly_mod_eq, Abbr`h`] >>
  rw[]);

(* Theorem:  FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x) pdivides (unity (forder x)) *)
(* Proof:
   Let ox = forder x.
   If x = #0,
      Then ox = 0            by field_order_zero
       and unity 0 = |0|     by poly_unity_0
     Hence true              by poly_divides_zero
   If x <> #0,
      Then x IN R+                           by field_nonzero_eq
        so x ** ox = #1                      by field_order_property, x IN R+
       ==> root (unity ox) x                 by poly_unity_root_property
      Also Poly s (unity ox)                 by poly_unity_spoly, subfield_is_subring
     Hence (minimal x) pdivides (unity ox)   by poly_minimal_divides_subfield_poly
*)
val poly_minimal_divides_unity_order = store_thm(
  "poly_minimal_divides_unity_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x) pdivides (unity (forder x))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `ox = forder x` >>
  Cases_on `x = #0` >-
  metis_tac[field_order_zero, poly_unity_0, poly_divides_zero, field_is_ring] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `x ** ox = #1` by rw[field_order_property, Abbr`ox`] >>
  `root (unity ox) x` by rw[poly_unity_root_property] >>
  `Poly s (unity ox)` by rw[poly_unity_spoly, subfield_is_subring] >>
  rw[poly_minimal_divides_subfield_poly]);

(* ------------------------------------------------------------------------- *)
(* Minimal Polynomial is unique and irreducible                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> SING (Minimals x) *)
(* Proof:
   Let t = Minimals x, p = minimal x.
   Then t <> {}                      by poly_minimals_nonempty
    and p IN t                       by poly_minimal_def, CHOICE_DEF, t <> {}
   Suppose q IN t.
   Then poly_monic s q /\ root q x   by poly_minimals_member
     or Poly s q /\ root q x         by poly_monic_poly
   Hence p pdivides q                by poly_minimal_divides_subfield_poly
   But deg p = deg q = MIN_SET (IMAGE deg t)   by poly_minimals_member
   and both p and q are monic        by subring_poly_monic, subfield_is_subring
   so p = q                          by poly_monic_divides_eq_deg_eq
   or SING t                         by SING_ONE_ELEMENT
*)
val poly_minimals_sing = store_thm(
  "poly_minimals_sing",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> SING (Minimals x)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = Minimals x` >>
  qabbrev_tac `p = minimal x` >>
  `t <> {}` by rw[poly_minimals_nonempty, Abbr`t`] >>
  `p IN t` by rw[poly_minimal_def, CHOICE_DEF, Abbr`p`, Abbr`t`] >>
  `!q. q IN t ==> (p = q)` suffices_by metis_tac[SING_ONE_ELEMENT] >>
  rpt strip_tac >>
  `poly_monic s q /\ root q x` by metis_tac[poly_minimals_member] >>
  `Poly s q` by rw[poly_monic_poly] >>
  `p pdivides q` by rw[poly_minimal_divides_subfield_poly, Abbr`p`] >>
  `deg p = deg q` by metis_tac[poly_minimals_member] >>
  `monic p /\ monic q` by metis_tac[poly_minimals_member, subfield_is_subring, subring_poly_monic] >>
  metis_tac[poly_monic_divides_eq_deg_eq]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> (minimal #0 = X) *)
(* Proof:
   Let p = X + |c| be a monic degree 1 polynomial.
   In order that #0 is a root of p, eval (X + |c|) #0 = #0
   or #0 + c = #0 ==> c = #0.
   Hence p = X is the only choice.
   and with deg p = 1, it must be the minimal.

   Step 1: show X is a candidate.
   Note lead X = #1                 by poly_lead_X
    and deg X = 1, or 0 < deg X     by poly_deg_X
   also root X #0                   by poly_root_def, poly_eval_cons
   Since (s.sum.id = #0) /\ (s.prod.id = #1)  by subfield_ids
      so #0 IN B and #1 IN B        by field_zero_element, field_one_element
    Thus Poly s X                   by Poly_def, zero_poly_def
     and poly_lead s X = s.prod.id  by subring_poly_lead, subfield_is_subring
      so poly_monic s X             by poly_monic_def

     Let t = Minimals #0,
     Then X IN t                    by poly_minimals_has_monoimal_condition, #0 IN R

   Step 2: apply property of SING.
   Since X IN t, t <> {}            by MEMBER_NOT_EMPTY
     and poly_minimal r s #0 IN t   by poly_minimal_def, CHOICE_DEF, t <> {}
     But SING t                     by poly_minimals_sing
   Hence poly_minimal r s #0 = X    by SING_ONE_ELEMENT
*)
val poly_minimal_zero = store_thm(
  "poly_minimal_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> (minimal #0 = X)``,
  rpt (stripDup[FiniteField_def]) >>
  `(lead X = #1) /\ (deg X = 1)` by rw[] >>
  `root X #0` by rw[poly_root_def] >>
  `0 < deg X` by decide_tac >>
  `#0 IN R /\ #0 IN B /\ #1 IN B /\ (s.sum.id = #0) /\ (s.prod.id = #1)` by metis_tac[subfield_ids, field_zero_element, field_one_element] >>
  `Poly s X` by rw[] >>
  `poly_lead s X = s.prod.id` by rw[subring_poly_lead, subfield_is_subring] >>
  `poly_monic s X` by metis_tac[poly_monic_def] >>
  qabbrev_tac `t = poly_minimals r s #0` >>
  `X IN t` by metis_tac[poly_minimals_has_monoimal_condition, Abbr`t`] >>
  `t <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `minimal #0 IN t` by rw[poly_minimal_def, CHOICE_DEF, Abbr`t`] >>
  metis_tac[poly_minimals_sing, SING_ONE_ELEMENT]);

(* Theorem: FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|) *)
(* Proof:
   Let p = X + |c| be a monic degree 1 polynomial.
   In order that #1 is a root of p, eval (X + |c|) #1 = #1 + c
   or #1 + c = #0 ==> c = - #1.
   Hence p = X - |1| is the only choice.
   and with deg p = 1, it must be the minimal.

   Let p = X - |1|, t = Minimals #1.
   Note p = unity 1                 by poly_unity_1
   Step 1: show p is a candidate.
     Since deg p = 1                by poly_unity_deg
       and poly_monic s p           by poly_unity_monic, subring_poly_unity, subfield_is_subring
       and root p #1                by poly_unity_root_has_one
      Thus p IN t                   by poly_minimals_has_monoimal_condition

   Step 2: apply property of SING.
   Since p IN t, t <> {}            by MEMBER_NOT_EMPTY
     and minimal #1 IN t            by poly_minimal_def, CHOICE_DEF, t <> {}
     But SING t                     by poly_minimals_sing
   Hence minimal #1 = p             by SING_ONE_ELEMENT
*)
val poly_minimal_one = store_thm(
  "poly_minimal_one",
  ``!(r s):'a ring. FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = X - |1|` >>
  `p = unity 1` by rw[poly_unity_1, Abbr`p`] >>
  `deg p = 1` by rw[poly_unity_deg] >>
  `poly_monic s (Unity s 1)` by rw[poly_unity_monic] >>
  `poly_monic s p` by metis_tac[subring_poly_unity, subfield_is_subring] >>
  `root p #1` by rw[poly_unity_root_has_one] >>
  qabbrev_tac `t = Minimals #1` >>
  `p IN t` by rw[poly_minimals_has_monoimal_condition, Abbr`t`] >>
  `t <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `minimal #1 IN t` by rw[poly_minimal_def, CHOICE_DEF, Abbr`t`] >>
  `#1 IN R` by rw[] >>
  `SING t` by rw[poly_minimals_sing, Abbr`t`] >>
  metis_tac[SING_DEF, IN_SING]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> ((minimal x = X) <=> (x = #0)) *)
(* Proof:
   If part: minimal x = X ==> x = #0
      Since root (minimal x) x       by poly_minimal_has_element_root
         or root X x                 by minimal x = X
        <=> eval X x = #0            by poly_root_def
        <=>        x = #0            by poly_eval_X
   Only-if part: x = #0 ==> minimal x = X, true by poly_minimal_zero
*)
val poly_minimal_eq_X = store_thm(
  "poly_minimal_eq_X",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> ((minimal x = X) <=> (x = #0))``,
  metis_tac[poly_minimal_has_element_root, poly_minimal_zero, poly_root_def, poly_eval_X, field_is_ring]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> IPoly s (minimal x *)
(* Proof:
   Let p = minimal x.
    Then poly_monic s p /\ 0 < deg p /\ root p x    by poly_minimal_subfield_property
      or 0 < poly_deg s p                           by subring_poly_deg
   By contradiction, suppose ~IPoly s p.
    Then ?u v. poly_monic s u /\ poly_monic s v /\ (p = poly_mult s u v) /\
         0 < poly_deg s u /\ 0 < poly_deg s v /\ poly_deg s u < poly_deg s p /\ poly_deg s v < poly_deg s p
                                           by poly_monic_reducible_factors
      or p = u * v                         by subring_poly_mult
     and 0 < deg u /\ deg u < deg p        by subring_poly_deg, poly_monic_poly
     and 0 < deg v /\ deg v < deg p        by subring_poly_deg, poly_monic_poly
   Let t = subfield_monics x
    then t <> {}                           by subfield_monics_of_element_nonempty
     and IMAGE deg t <> {}                 by IMAGE_EQ_EMPTY
    with deg p = MIN_SET (IMAGE deg t)     by poly_minimal_property

   Since root p x                          by above, or poly_minimal_has_element_root
      so root u x  or root v x             by poly_root_field_mult
   If root u x,
      Then u IN t                          by subfield_monics_of_element_member
        so deg u IN (IMAGE deg t)          by IN_IMAGE
        or MIN_SET (IMAGE deg t) <= deg u  by MIN_SET_LEM
       This contradicts deg u < deg p = MIN_SET (IMAGE deg t)
   If root v x,
      Then v IN t                          by subfield_monics_of_element_member
        so deg v IN (IMAGE deg t)          by IN_IMAGE
        or MIN_SET (IMAGE deg t) <= deg v  by MIN_SET_LEM
       This contradicts deg v < deg p = MIN_SET (IMAGE deg t)
*)
val poly_minimal_subfield_irreducible = store_thm(
  "poly_minimal_subfield_irreducible",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> IPoly s (minimal x)``,
  rpt (stripDup[FiniteField_def]) >>
  `s <= r` by rw[subfield_is_subring] >>
  qabbrev_tac `p = minimal x` >>
  `poly_monic s p /\ 0 < deg p /\ root p x` by rw[poly_minimal_subfield_property, Abbr`p`] >>
  `0 < poly_deg s p` by metis_tac[subring_poly_deg] >>
  spose_not_then strip_assume_tac >>
  `?u v. poly_monic s u /\ poly_monic s v /\ (p = poly_mult s u v) /\
    0 < poly_deg s u /\ 0 < poly_deg s v /\ poly_deg s u < poly_deg s p /\ poly_deg s v < poly_deg s p` by rw[poly_monic_reducible_factors] >>
  `Poly s p /\ Poly s u /\ Poly s v` by rw[] >>
  `poly p /\ poly u /\ poly v` by metis_tac[subring_poly_poly] >>
  `(p = u * v) /\ 0 < deg u /\ 0 < deg v /\ deg u < deg p /\ deg v < deg p` by metis_tac[subring_poly_mult, subring_poly_deg] >>
  qabbrev_tac `t = subfield_monics x` >>
  `t <> {}` by rw[subfield_monics_of_element_nonempty, Abbr`t`] >>
  `IMAGE deg t <> {}` by rw[] >>
  `deg p = MIN_SET (IMAGE deg t)` by rw[poly_minimal_property, Abbr`t`, Abbr`p`] >>
  `root u x \/ root v x` by metis_tac[poly_root_field_mult] >| [
    `u IN t` by rw[subfield_monics_of_element_member, Abbr`t`] >>
    `MIN_SET (IMAGE deg t) <= deg u` by rw[MIN_SET_LEM] >>
    decide_tac,
    `v IN t` by rw[subfield_monics_of_element_member, Abbr`t`] >>
    `MIN_SET (IMAGE deg t) <= deg v` by rw[MIN_SET_LEM] >>
    decide_tac
  ]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Minimal Polynomial of Prime Field                                         *)
(* ------------------------------------------------------------------------- *)

(*
The following prime field theorems can be proved by subfield/subring.
Proofs below to be revised.
*)

(* Theorem: FiniteField r ==> !p n. p IN sticks (PF r) n ==> weak p *)
(* Proof:
   Since Field r             by FiniteField_def
     and Field (PF r)        by prime_field_field
     and subfield (PF r) r   by prime_field_subfield
     Now Weak (PF r) p       by stick_is_weak
   hence weak p              by subfield_poly_weak_is_weak
*)
val prime_field_stick_is_weak = store_thm(
  "prime_field_stick_is_weak",
  ``!r:'a field. FiniteField r ==> !p n. p IN sticks (PF r) n ==> weak p``,
  rpt (stripDup[FiniteField_def]) >>
  `Field (PF r)` by rw[prime_field_field] >>
  `subfield (PF r) r` by rw[prime_field_subfield] >>
  metis_tac[stick_is_weak, subfield_poly_weak_is_weak]);

(* Theorem: FiniteField r ==> !p n. p IN sticks (PF r) (SUC n) ==>
            !x. x IN R ==> (p <o> (ebasis x n) = eval p x) *)
(* Proof:
   By induction on n.
   Base case: !p. p IN sticks (PF r) (SUC 0) ==>
              !x. x IN R ==> (p <o> ebasis x 0 = eval p x)
           p IN sticks (PF r) (SUC 0)
       ==> p IN sticks (PF r) 1       by ONE
       ==> ?c. c IN Fp /\ (p = [c])   by sticks_1_member
       Note c IN R                    by prime_field_element
       Also ebasis x 0 = [#1]         by element_powers_basis_0
         VectorSum r.sum (MAP2 $* [c] [#1])
        = VectorSum r.sum [c * #1]                 by MAP2
        = VectorSum r.sum [c]                      by ring_mult_rone
        = c + (VectorSum r.sum [])                 by vsum_cons
        = c + #0                                   by vsum_nil
        = c                                        by ring_add_rzero
        = eval [c] x                               by poly_eval_const
   Step case: !p. p IN sticks (PF r) (SUC (SUC n)) ==>
              !x. x IN R ==> (p <o> ebasis x (SUC n) = eval p x)
           p IN sticks (PF r) (SUC (SUC n))
       ==> ?h t. h IN Fp /\ t IN sticks (PF r) (SUC n) /\ (p = SNOC h t)
                                                                 by stick_snoc
       Note LENGTH t = SUC n                                     by stick_length
       Also ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n)  by element_powers_basis_suc
        and h IN R                        by prime_field_element
        and weak t                        by prime_field_stick_is_weak
        and eval t x IN R                 by weak_eval_element
         p <o> (ebasis x (SUC n)))
       = (SNOC h t) <o> (SNOC (x ** (SUC n)) (ebasis x n))  by above
       = h * (x ** SUC n) + t <o> (ebasis x n)     by vsum_stick_snoc
       = h * (x ** SUC n) + eval t x               by induction hypothesis
       = eval t x + h * x ** LENGTH t              by ring_add_comm
       = eval (SNOC h t) x                         by weak_eval_snoc
       = eval p x                                  by p = SNOC h t
*)
val vsum_element_powers_basis_eq_eval = store_thm(
  "vsum_element_powers_basis_eq_eval",
  ``!r:'a field. FiniteField r ==> !p n. p IN sticks (PF r) (SUC n) ==>
   !x. x IN R ==> (p <o> (ebasis x n) = eval p x)``,
  ntac 2 (stripDup[FiniteField_def]) >>
  Induct_on `n` >| [
    rw[] >>
    `?c. c IN Fp /\ (p = [c])` by rw[GSYM sticks_1_member] >>
    `c IN R` by rw[prime_field_element] >>
    `ebasis x 0 = [#1]` by rw[element_powers_basis_0] >>
    rw[vsum_cons, vsum_nil],
    rpt strip_tac >>
    `?h t. h IN Fp /\ t IN sticks (PF r) (SUC n) /\ (p = SNOC h t)` by rw[GSYM stick_snoc] >>
    `ebasis x (SUC n) = SNOC (x ** (SUC n)) (ebasis x n)` by rw_tac std_ss[element_powers_basis_suc] >>
    `VSpace (PF r) r.sum $*` by rw[finite_field_is_vspace] >>
    `basis r.sum (ebasis x n)` by rw[element_powers_basis_is_basis] >>
    `LENGTH (ebasis x n) = SUC n` by rw[element_powers_basis_length] >>
    `x ** SUC n IN R /\ (R = r.sum.carrier)` by rw[] >>
    `h IN R` by rw[prime_field_element] >>
    `weak t` by metis_tac[prime_field_stick_is_weak] >>
    `p <o> (ebasis x (SUC n)) = h * (x ** SUC n) + eval t x` by metis_tac[vsum_stick_snoc] >>
    `_ = h * x ** LENGTH t + eval t x` by metis_tac[stick_length] >>
    `_ = eval t x + h * x ** LENGTH t` by rw[ring_add_comm] >>
    `_ = eval p x` by rw[weak_eval_snoc] >>
    rw[]
  ]);

(* Theorem: FiniteField r ==> !x. x IN R ==> ?p. pfpoly p /\ 0 < deg p /\ root p x *)
(* Proof:
   Let n = dim (PF r) r.sum $*, b = ebasis x n.
    Then ~LinearIndepBasis (PF r) r.sum $* b  by element_powers_basis_dim_dep
    Note basis r.sum b                        by element_powers_basis_is_basis
     and LENGTH b = SUC n                     by element_powers_basis_length
     and (PF r).sum.id = #0                   by PF_property
   Hence by LinearIndepBasis_def,
     ?q. q IN sticks (PF r) (SUC n) /\
         ~(q <o> b) = #0) <=> !k. k < SUC n ==> (EL k q = #0))   [1]

    Note VSpace (PF r) r.sum $*               by finite_field_is_vspace
     and !k. k < SUC n ==> (EL k q = #0)) ==> (q <o> b) = #0)   by vspace_stick_zero
    Thus ?k. k < SUC n /\ (EL k p <> #0) /\ (q <o> b) = #0)     by [1]
     Now Weak (PF r) q                        by stick_is_weak
     and LENGTH q = SUC n                     by stick_length
      so ~pfzerop q                           by zero_poly_element, EL k q <> #0
   Let p = pfchop q
   Then pfpoly p                              by poly_chop_weak_poly
    and ~pfzerop p                            by zero_poly_eq_zero_poly_chop
   thus p <> PolyRing (PF r)).sum.id          by zero_poly_eq_poly_zero
     or p <> |0|                              by poly_prime_field_ids
   Also eval p x = eval (pfchop q) x
                 = eval (chop q) x            by poly_prime_field_chop
                 = eval q x                   by poly_eval_chop
                 = q <o> b                    by vsum_element_powers_basis_eq_eval
                 = #0                         by above
  Hence root p x                              by poly_root_def
   with 0 < deg p                             by poly_nonzero_with_root_deg_pos
*)
val poly_prime_field_with_root_exists = store_thm(
  "poly_prime_field_with_root_exists",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> ?p. pfpoly p /\ 0 < deg p /\ root p x``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `n = dim (PF r) r.sum $*` >>
  qabbrev_tac `b = ebasis x n` >>
  `~LinearIndepBasis (PF r) r.sum $* b` by rw[element_powers_basis_dim_dep, Abbr`n`, Abbr`b`] >>
  `basis r.sum b` by rw[element_powers_basis_is_basis, Abbr`b`] >>
  `LENGTH b = SUC n` by rw[element_powers_basis_length, Abbr`b`] >>
  `(PF r).sum.id = #0` by rw[PF_property] >>
  `?q. q IN sticks (PF r) (SUC n) /\
    ~((q <o> b = #0) <=> !k. k < SUC n ==> (EL k q = #0))` by metis_tac[LinearIndepBasis_def] >>
  `VSpace (PF r) r.sum $*` by rw[finite_field_is_vspace] >>
  `?k. k < SUC n /\ (EL k q <> #0) /\ (q <o> b = #0)` by metis_tac[vspace_stick_zero] >>
  `Weak (PF r) q` by metis_tac[stick_is_weak] >>
  qexists_tac `pfchop q` >>
  `pfpoly (pfchop q)` by metis_tac[poly_chop_weak_poly] >>
  `eval q x = #0` by metis_tac[vsum_element_powers_basis_eq_eval] >>
  `root (chop q) x` by rw[poly_root_def] >>
  `root (pfchop q) x` by rw[poly_prime_field_chop] >>
  `~pfzerop q` by metis_tac[zero_poly_element, stick_length] >>
  `~pfzerop (pfchop q)` by metis_tac[zero_poly_eq_zero_poly_chop] >>
  `(pfchop q) <> |0|` by metis_tac[zero_poly_eq_poly_zero, poly_prime_field_ids] >>
  `poly (pfchop q)` by rw[poly_prime_field_element_poly] >>
  `0 < deg (pfchop q)` by metis_tac[poly_nonzero_with_root_deg_pos, field_is_ring] >>
  rw[]);

(* overload on monic in (PF r) poly *)
val _ = overload_on("pfmonic", ``poly_monic (PF r)``);
(* overload on ipoly in (PF r) poly *)
val _ = overload_on("pfipoly", ``irreducible (PolyRing (PF r))``);

(* Theorem: FiniteField r ==> !x. x IN R ==> ?p. pfmonic p /\ 0 < deg p /\ root p x *)
(* Proof:
   Since FiniteField r
     ==> ?q. pfpoly q /\ 0 < deg q /\ root q x by poly_prime_field_with_root_exists
    Note (PolyRing (PF r)).sum.id = |0|        by poly_prime_field_ids
     and Field (PF r)                          by prime_field_field
   Hence ?u p. pfpoly u /\ pfmonic p /\ (pfdeg p = pfdeg q) /\ (p = pfmult u q) by poly_monic_mult_by_factor, poly_unit_poly
    with 0 < deg q = pfdeg q = pfdeg p = deg p by poly_prime_field_deg
   Since pfpoly p                              by poly_monic_poly
    Thus poly u /\ poly p /\ poly q /\         by poly_prime_field_element_poly
        (p = u * q)                            by poly_prime_field_mult
       eval p x
     = (eval u x) * (eval q x)                 by poly_eval_mult
     = (eval u x) * #0                         by poly_root_def
     = #0                                      by poly_eval_element, field_mult_rzero
   Hence root p x                              by poly_root_def
*)
val poly_prime_field_monic_with_root_exists = store_thm(
  "poly_prime_field_monic_with_root_exists",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> ?p. pfmonic p /\ 0 < deg p /\ root p x``,
  rpt (stripDup[FiniteField_def]) >>
  `?q. pfpoly q /\ 0 < deg q /\ root q x` by rw_tac std_ss[poly_prime_field_with_root_exists] >>
  `(PolyRing (PF r)).sum.id = |0|` by rw[poly_prime_field_ids] >>
  `Field (PF r)` by rw[prime_field_field] >>
  `q <> |0|` by rw[poly_deg_pos_nonzero] >>
  `?u p. pfpoly u /\ pfmonic p /\ (pfdeg p = pfdeg q) /\ (p = pfmult u q)` by metis_tac[poly_monic_mult_by_factor, poly_unit_poly, field_is_ring] >>
  `0 < deg p` by metis_tac[poly_prime_field_deg] >>
  `Ring r /\ pfpoly p` by rw[] >>
  `poly u /\ poly p /\ poly q /\ (p = u * q)` by rw[poly_prime_field_element_poly, poly_prime_field_mult] >>
  `eval p x = (eval u x) * (eval q x)` by rw_tac std_ss[poly_eval_mult] >>
  `_ = (eval u x) * #0` by metis_tac[poly_root_def] >>
  `_ = #0` by rw[] >>
  metis_tac[poly_root_def]);


(* ------------------------------------------------------------------------- *)
(* Ideals of Polynomial Ring                                                 *)
(* ------------------------------------------------------------------------- *)

(*
> ringIdealTheory.ideal_has_principal_ideal;
val it = |- !r i. Ring r /\ i << r ==> !p. p IN R ==> (p IN i.carrier <=> <p> << i): thm
> ringIdealTheory.ideal_has_principal_ideal |> ISPEC ``(PolyRing r)``;
val it = |- !i. Ring (PolyRing r) /\ i << PolyRing r ==>
     !p. p IN (PolyRing r).carrier ==> (p IN i.carrier <=> principal_ideal (PolyRing r) p << i): thm
*)

(* overload on principal ideal in (PolyRing r) *)
val _ = overload_on("pfppideal", ``principal_ideal (PolyRing r)``);

(* Theorem: Ring r ==> !p. poly p ==> ((pfppideal p = pfppideal |0|) <=> (p = |0|)) *)
(* Proof:
   If part: pfppideal p = pfppideal |0| ==> p = |0|
      Since Ring (PolyRing r)                by poly_ring_ring
        and p IN (PolyRing r).carrier        by poly_ring_property
       thus p IN (pfppideal p).carrier       by principal_ideal_has_element
       Also (pfppideal p).carrier
          = (pfppideal |0|).carrier          by principal_ideal_ideal, ideal_eq_ideal
          = {|0|}                            by zero_ideal_sing
      Hence p = |0|                          by IN_SING
   Only-if part: p = |0| ==> pfppideal p = pfppideal |0|
      This is trivial.
*)
val poly_ring_zero_ideal = store_thm(
  "poly_ring_zero_ideal",
  ``!r:'a ring. Ring r ==> !p. poly p ==> ((pfppideal p = pfppideal |0|) <=> (p = |0|))``,
  rw_tac std_ss[EQ_IMP_THM] >>
  `poly |0|` by rw[] >>
  `Ring (PolyRing r)` by rw[poly_ring_ring] >>
  `p IN (pfppideal p).carrier` by metis_tac[principal_ideal_has_element, poly_ring_property] >>
  `(pfppideal p).carrier = (pfppideal |0|).carrier` by rw[principal_ideal_ideal, ideal_eq_ideal] >>
  `_ = { |0| }` by rw[zero_ideal_sing] >> (* avoid bag syntax *)
  metis_tac[IN_SING]);

(* Theorem: Field r ==> !i. i << (PolyRing r) /\ i <> pfppideal |0| ==> ?p. monic p /\ (i = pfppideal p) *)
(* Proof:
   Since Ring (PolyRing r)                by poly_ring_ring, Ring r
     and PrincipalIdealRing (PolyRing r)  by poly_ring_principal_ideal_ring, Field r
      so ?q. poly q /\ (i = pfppideal q)  by PrincipalIdealRing_def, poly_ring_property
     and q <> |0|                         by poly_ring_zero_ideal
    thus ?u p. upoly u /\
               monic p /\ (deg p = deg q) /\ (q = u * p)  by poly_monic_mult_factor
     and poly u                           by poly_unit_poly
     and poly p                           by poly_monic_def
     Now q = p * u                        by poly_mult_comm
   Hence i = pfppideal p                  by principal_ideal_eq_principal_ideal, Ring (PolyRing r)
*)
val poly_ring_ideal_gen_monic = store_thm(
  "poly_ring_ideal_gen_monic",
  ``!r:'a field. Field r ==> !i. i << (PolyRing r) /\ i <> pfppideal |0| ==>
   ?p. monic p /\ (i = pfppideal p)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw[poly_ring_ring] >>
  `PrincipalIdealRing (PolyRing r)` by rw[poly_ring_principal_ideal_ring] >>
  `?q. poly q /\ (i = pfppideal q)` by metis_tac[PrincipalIdealRing_def, poly_ring_property] >>
  `q <> |0|` by metis_tac[poly_ring_zero_ideal] >>
  `?u p. upoly u /\ monic p /\ (deg p = deg q) /\ (q = u * p)` by rw[poly_monic_mult_factor] >>
  `poly p /\ poly u` by rw[poly_unit_poly] >>
  `q = p * u` by rw[poly_mult_comm] >>
  metis_tac[principal_ideal_eq_principal_ideal, poly_ring_property]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            ((pfppideal p = pfppideal q) <=> ?u. poly u /\ upoly u /\ (p = u * q)) *)
(* Proof:
   Note Ring r                 by field_is_ring
    and Ring (PolyRing r)      by poly_ring_ring
   If part: pfppideal p = pfppideal q ==> ?u. poly u /\ upoly u /\ (p = u * q)
      If p = |0|,
         then q = |0|          by poly_ring_zero_ideal
         Take u = |1|,
         then poly |1|         by poly_one_poly
          and upoly |1|        by poly_field_unit_one
          and |0| = |1| * |0|  by poly_mult_lone
      If p <> |0|,
         then p IN (pfppideal q).carrier    by principal_ideal_has_element
          and q IN (pfppideal p).carrier    by principal_ideal_has_element
           so ?u. poly u /\ (p = q * u)     by principal_ideal_element
          and ?v. poly v /\ (q = p * v)     by principal_ideal_element
         Now  p * |1|
            = p                by poly_mult_rone
            = q * u            by above
            = (p * v) * u      by above
            = p * (v * u)      by poly_mult_assoc
         Therefore,
              v * u = |1|          by poly_mult_lcancel, p <> |0|
           or u * v = |1|          by poly_mult_comm
         thus upoly u              by poly_ring_units
          and p = q * u = u * q    by poly_mult_comm
   Only-if part: ?u. poly u /\ upoly u /\ (p = u * q) ==> pfppideal p = pfppideal q
      or to show: pfppideal (u * q) = pfppideal q
      Since p = u * q = q * u          by poly_mult_comm
      Hence pfppideal p = pfppideal q  by principal_ideal_eq_principal_ideal
*)
val poly_field_principal_ideal_equal = store_thm(
  "poly_field_principal_ideal_equal",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   ((pfppideal p = pfppideal q) <=> ?u. poly u /\ upoly u /\ (p = u * q))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `Ring (PolyRing r)` by rw[poly_ring_ring] >>
  `!p. poly p <=> p IN (PolyRing r).carrier` by rw[poly_ring_element] >>
  rw[EQ_IMP_THM] >| [
    Cases_on `p = |0|` >| [
      `q = |0|` by rw[GSYM poly_ring_zero_ideal] >>
      qexists_tac `|1|` >>
      rw[poly_field_unit_one],
      `p IN (pfppideal q).carrier` by metis_tac[principal_ideal_has_element] >>
      `q IN (pfppideal p).carrier` by metis_tac[principal_ideal_has_element] >>
      `?u. poly u /\ (p = q * u)` by metis_tac[principal_ideal_element] >>
      `?v. poly v /\ (q = p * v)` by metis_tac[principal_ideal_element] >>
      `p * |1| = p` by rw[] >>
      `_ = p * v * u` by rw[] >>
      `_ = p * (v * u)` by rw[poly_mult_assoc] >>
      `v * u = |1|` by prove_tac[poly_mult_lcancel, poly_one_poly, poly_mult_poly] >>
      metis_tac[poly_ring_units, poly_mult_comm]
    ],
    metis_tac[principal_ideal_eq_principal_ideal, poly_mult_comm]
  ]);

(* Theorem: Field r ==> !p q. monic p /\ monic q /\ (pfppideal p = pfppideal q) ==> (p = q) *)
(* Proof:
   Since ?u. poly u /\ upoly u /\ (p = u * q)   by poly_field_principal_ideal_equal
     and upoly u
     ==> u <> |0| /\ (deg u = 0)                by poly_field_units
     ==> ?c. c IN R /\ c <> #0 /\ (u = [c])     by poly_deg_eq_0
   In Field r, since p = u * q,
        lead p = lead u * lead q                by poly_lead_mult
     or     #1 = c * #1                         by poly_monic_lead, poly_lead_const
     or     #1 = c                              by field_mult_rone
     thus   u = [#1] = |1|                      by poly_one, field_one_ne_zero
   Hence p = u * q = |1| * q = q                by poly_mult_lone, poly_monic_poly
*)
val poly_ring_ideal_monic_gen_unique = store_thm(
  "poly_ring_ideal_monic_gen_unique",
  ``!r:'a field. Field r ==> !p q. monic p /\ monic q /\ (pfppideal p = pfppideal q) ==> (p = q)``,
  rpt strip_tac >>
  `?u. poly u /\ upoly u /\ (p = u * q)` by rw[GSYM poly_field_principal_ideal_equal] >>
  `u <> |0| /\ (deg u = 0)` by metis_tac[poly_field_units] >>
  `?c. c IN R /\ c <> #0 /\ (u = [c])` by rw[GSYM poly_deg_eq_0] >>
  `lead p = lead u * lead q` by rw[poly_lead_mult] >>
  `#1 = c * #1` by metis_tac[poly_monic_lead, poly_lead_const] >>
  `c = #1` by metis_tac[field_mult_rone] >>
  `u = |1|` by metis_tac[poly_one, field_one_ne_zero] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* The Ideal of Polynomials sharing a root.                                  *)
(* ------------------------------------------------------------------------- *)

(* Make an ideal from a set *)
val set_to_ideal_def = Define `
   set_to_ideal (r:'a ring) (s:'a -> bool) =
      <| carrier := s;
             sum := <| carrier := s; op := $+; id := #0 |>;
            prod := <| carrier := s; op := $*; id := #1 |>
       |>
`;
(* overload set_to_ideal *)
val _ = overload_on("sideal", ``set_to_ideal r``);

(* Theorem: Ring r ==> !z. z IN R ==>
            (set_to_ideal (PolyRing r) {p | poly p /\ root p z}) << (PolyRing r) *)
(* Proof:
   By ideal_def, set_to_ideal_def, this is to show:
   (1) <|carrier := {p | poly p /\ root p z}; op := $+; id := |0||> <= (PolyRing r).sum
       By Subgroup_def, this is to show:
       (1) Group <|carrier := {p | poly p /\ root p z}; op := $+; id := |0||>
           By group_def_alt, this is to show:
           (1) poly x /\ poly y ==> poly (x + y), true  by poly_add_poly
           (2) root x z /\ root y z ==> root (x + y) z, true  by
           (3) poly x /\ poly y /\ poly z' ==> x + y + z' = x + (y + z'), true by poly_add_assoc
           (4) poly |0|, true by poly_zero_poly
           (5) root |0| z, true by poly_root_zero
           (6) poly x ==> |0| + x = x, true by poly_add_lzero
           (7) poly x /\ root x z ==> ?y. (poly y /\ root y z) /\ (y + x = |0|)
               Let y = -x, then true by poly_root_neg
       (2) Group (PolyRing r).sum, true by poly_add_group
       (3) {p | poly p /\ root p z} SUBSET (PolyRing r).sum.carrier
           This is true by poly_ring_element, poly_ring_carriers, SUBSET_DEF.
   (2) x IN {p | poly p /\ root p z} /\ y IN (PolyRing r).carrier ==> x * y IN {p | poly p /\ root p z}
    or poly x /\ root p x /\ poly y ==> poly (x * y) /\ root (x * y) z
       This is true by poly_mult_poly, poly_root_mult.
   (3) x IN {p | poly p /\ root p z} /\ y IN (PolyRing r).carrier ==> y * x IN {p | poly p /\ root p z}
    or poly x /\ root p x /\ poly y ==> poly (x * y) /\ root (y * x) z
       This is true by poly_mult_poly, poly_root_mult_comm.
*)
val poly_root_poly_ideal = store_thm(
  "poly_root_poly_ideal",
  ``!r:'a ring. Ring r ==> !z. z IN R ==>
    (set_to_ideal (PolyRing r) {p | poly p /\ root p z}) << (PolyRing r)``,
  rw_tac std_ss[ideal_def, set_to_ideal_def, Subgroup_def, poly_ring_element, GSPECIFICATION] >| [
    rw_tac std_ss[group_def_alt, GSPECIFICATION] >-
    rw[] >-
    rw[poly_root_add] >-
    rw[poly_add_assoc] >-
    rw[] >-
    rw[] >-
    rw[] >>
    metis_tac[poly_root_neg, poly_neg_poly, poly_add_lneg],
    rw[poly_add_group],
    rw[poly_ring_element, poly_ring_carriers, SUBSET_DEF],
    rw[],
    rw[poly_root_mult],
    rw[],
    rw[poly_root_mult_comm]
  ]);

(*
Given an a which is algebraic over some subfield K of F, it can be checked (exercise!)
that the set J = {f IN K[x]: f(a) = 0} is an ideal of F[x] and J <> (0). By Theorem 3.4
it follows that there exists a uniquely determined monic polynomial g IN K[x] which
generates J, i.e. J = (g).

Definition: call this the minimal polynomial of a over K.
We refer to the degree of a over K = deg g.

type checking:
g `!r:'a ring. Ring r ==> !x. x IN R ==> sideal R << r`;
g `!r:'a ring. Ring r ==> !x. x IN R ==> set_to_ideal (PF r) Fp << (PF r)`;
g `!r:'a ring. Ring r ==> !x. x IN R ==> set_to_ideal (PF r) Fp << r`;

g `!r:'a ring. Ring r ==> !x. x IN R ==>
    (set_to_ideal (PolyRing (PF r)) (PolyRing (PF r)).carrier << (PolyRing r))`;
g `!r:'a ring. Ring r ==> !z. z IN R ==>
    (set_to_ideal (PolyRing (PF r)) {p | pfpoly p /\ (root p z)}) << (PolyRing r)`;
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
