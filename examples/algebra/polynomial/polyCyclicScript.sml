(* ------------------------------------------------------------------------- *)
(* Cyclic Polynomial: quotient of (unity n) by (unity 1).                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyCyclic";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

(* Get dependet theories local *)
open monoidTheory groupTheory ringTheory fieldTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory;
open polyMonicTheory;
open polyEvalTheory;
open polyRootTheory;
open polyDividesTheory;
open polyIrreducibleTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Cyclic Polynomial Documentation                                           *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   cyclic n   = poly_cyclic r n
*)
(* Definitions and Theorems (# are exported):

   Cyclic Polynomials:
   poly_cyclic_def             |- !r n. cyclic n = GENLIST (\k. #1) n
#  poly_cyclic_0               |- !r. cyclic 0 = |0|
#  poly_cyclic_1               |- !r. #1 <> #0 ==> (cyclic 1 = |1|)
#  poly_cyclic_suc             |- !r. #1 <> #0 ==> !n. cyclic (SUC n) = #1::cyclic n
#  poly_cyclic_poly            |- !r. Ring r /\ #1 <> #0 ==> !n. poly (cyclic n)
   poly_cyclic_eq_zero         |- !r. #1 <> #0 ==> !n. (cyclic n = |0|) <=> (n = 0)
#  poly_cyclic_lead            |- !r. #1 <> #0 ==> !n. 0 < n ==> (lead (cyclic n) = #1)
   poly_cyclic_monic           |- !r. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> monic (cyclic n)
   poly_cyclic_deg             |- !r. #1 <> #0 ==> !n. deg (cyclic n) = PRE n
   poly_cyclic_eval_by_one     |- !r. Ring r /\ #1 <> #0 ==> !n. eval (cyclic n) #1 = ##n
   poly_cyclic_peval_by_one    |- !r. Ring r /\ #1 <> #0 ==> !n. peval (cyclic n) |1| = |n|
   poly_cyclic_suc_alt         |- !r. Ring r /\ #1 <> #0 ==> !n. cyclic (SUC n) = X * cyclic n + |1|
   poly_cyclic_cofactor        |- !r. Ring r /\ #1 <> #0 ==> !n. unity n = unity 1 * cyclic n

   Cyclic Irreducible Factor:
   poly_cyclic_has_no_factor_unity_1
                               |- !r. Field r ==> !n. 0 < n /\ n < char r ==> ~(unity 1 pdivides cyclic n)
   poly_cyclic_irreducible_factor
                               |- !r. Field r ==> !n. 1 < n ==> ?h. ipoly h /\ h pdivides cyclic n
   poly_cyclic_monic_irreducible_factor
                               |- !r. Field r ==> !n. 1 < n ==> ?h. mifactor h (cyclic n)
   poly_unity_irreducible_factor_exists
                               |- !r. Field r ==> !n. 1 < n /\ n < char r ==>
                                                  ?h. mifactor h (unity n) /\ h <> unity 1
*)

(* Notes:

   Basically, cyclic n = (unity n) / (unity 1)
   provides a simple way to show that (unity n) has #1 as a simple root, multiplicity = 1.
   This is because, clearly, #1 is not a root of cyclic n = 1 + x + x^2 + ... + x^(n-1).

   Let F be a Finite Field, with n = |F|.
   In its polynomial ring F[x], this is called the Master Polynomial:

   x^n - x = x (x^n - 1) = x (x - 1)(x^(n-1) + x^(n-2) + .... + 1)

   This Master Polynomial has the following property:
   !x. x IN F <=> x is a root of Master Polynomial.

   That is, !x. x IN F <=> eval (x^n - x) x = 0

   By restricting n = |F|, it holds for primes, and powers of primes.
   This Master Polynomial plays a role in the proof that F* is cyclic.

   However, the algebraic identity is just geometric series, hence applies for general n.

   Specifically, this is called the Cyclic Polynomial:

   (x^n - 1) = (x - 1)(x^(n-1) + x^(n-2) + .... + 1)

   The roots of (x^n - 1) are called the roots of unity.

   Example: x^4 - 1 = (x-1)(x^3 + x^2 + x + 1) = (x-1)(x+1)(x^2 + 1) = (x-1)(x+1)(x-i)(x+i)

   When F = C, complex numbers, x^4 - 1 in C[x] has 4 roots: 1, -1, i, -i.
                                and order 1 = 1, order -1 = 2, order i = 4 = order -i.
   When F = GF(2), booleans, x^4 - 1 in GF(2)[x] has 2 roots: 1 = -1 (repeated),
                                and order 1 = 1 = order (-1)
   When F = Zp, p = odd prime, x^4 -1 in Zp[x] has 2 roots: 1, -1 (distinct),
                                and order 1 = 1, order -1 = 2

   Let z = an n-th root of unity.
   By definition, z^n = 1, hence divides (order z) n   by group_order_divides
   If (order z) = n, z is called a primitive n-th root unity.

   Let uroots n = {z | z IN F /\ z^n = 1}.
   Then  (uroots n) <= F*

   If F* is cyclic, (uroots n) is also cyclic     by cyclic_uroots_cyclic
   We do know that F* is cyclic                   by finite_field_mult_group_cyclic
   So (uroots n) is cyclic, or there is always a primitive n-th root of unity.

   Let q = primitive n-th root of unity.
   By definition, q^n = 1, and (order q) = n.

   Thus q is a root of the Cyclic Polynomial.
   If 1 < n, q <> 1, hence q^(n-1) + q^(n-2) + ... + 1 = 0
   Since (order q) = n, its powers q, q^2, q^3, ...., q^(n-1), q^n = 1 gives n distinct n-th roots of unity.

   Also, x^n - 1 has an irreducible factor h     by irreducible_factor_exists (almost)
   i.e. x^n - 1 = k(x)h(x)
   so   0 = q^n - 1 = k(q)h(q)
   We need somehow to conclude: There is an irreducible factor h with q as a root.

   So far, I can only show: there is an irreducible factor h with X as a root.

   Some say: X = q mod h. Can this be proved???

   If n is prime, then X is a primitive n-th root of unity, by the following:
   For any polynomial modulo h, (lift h) has X as root, by poly_mod_has_root_X.
   and X in F[x] mod h.
   By lifting,  (lift x^n-1)(X) = (lift k)(lift h)(X)
                                = (lift k)(X) * (lift h)(X)
                                = (lift k)(X) * |0|
                                = |0|
   Hence X is an n-th root of (lift x^n-1), or X^n = |1|.
   Therefore  (order X) divides n    by group_order_condition.
   If n is prime, (order X) = 1, or (order X) = n.
   (order X) = 1  iff X = |1|        by group_order_eq_1
   If X = 1, X^(n-1) + X^(n-2) + ... + |1| = |0| means (n-1) * |1| = |0|, which is impossible.
   Hence X <> 1, or (order X) <> 1, i.e. (order X) = n, or X is a primitive n-th root.

   If n is not prime, say n = pq, there is an identity:
   x^n - 1 = x^pq - 1 = (x^p(q-1)+ x^p(q-2)+ ... + 1)(x^p- 1)

   But don't know how to make use of this identity.
*)
(* Notes:
   Theory of Cyclotomic Polynomials:
   Cyclotomic polynomials are the irreducible factors of Cyclic polynomial:

   x^n - 1 = PROD polyPhi(d), over all divides d n.

   and polyPhi(n) = PROD (x - e^(i 2pi k/n)), over all coprime k n.
                  = minimal polynomial in Q[z], where z is a primitive root of unity (e.g. e^(i 2pi k/n)).
                  = PROD (x^(n/d) - 1)^mu(d), over all divides d n (by Mobius Inversion)
                  = PROD (x^d - 1)^mu(n/d), over all divides d n (again by Mobius Inversion)

   Examples:
   x^1 - 1 = (x-1) = polyPhi(1)
   x^2 - 1 = (x-1)(x+1) = polyPhi(1)polyPhi(2)
   x^3 - 1 = (x-1)(x^2+x+1) = polyPhi(1)polyPhi(3)
   x^4 - 1 = (x-1)(x+1)(x^2+1) = polyPhi(1)polyPhi(2)polyPhi(4)
   x^5 - 1 = (x-1)(x^4+x^3+x^2+1) = polyPhi(1)polyPhi(5)
   x^6 - 1 = (x-1)(x+1)(x^2+x+1)(x^2-x+1) = polyPhi(1)polyPhi(2)polyPhi(3)polyPhi(6)
   x^7 - 1 = (x-1)(x^6+x^5+x^4+x^3+x^2+x+1) = polyPhi(1)polyPhi(7)

   polyPhi(1) = (x-1)^1 = x-1
   polyPhi(2) = (x^2-1)^1(x-1)^-1 = x+1
   polyPhi(3) = (x^3-1)^1(x-1)^-1 = x^2+x+1
   polyPhi(4) = (x^4-1)^1(x^2-1)^-1 = x^2+1
   polyPhi(5) = (x^5-1)^1(x-1)^-1 = x^4+x^3+x^2+x+1
   polyPhi(6) = (x^5-1)^1(x^3-1)^-1(x^2-1)^-1(x-1)^1 = x^2-x+1
   polyPhi(7) = (x^7-1)^1(x-1)^-1 = x^6+x^5+x^4+x^3+x^2+x+1

   The irreducibility of polyPhi(n) where n is prime follows by Eisenstein's criterion.
   The degree of polyPhi(n) = phi(n) = number of k coprime to n.
   For prime n, phi(n) = n-1,
   and deg polyPhi(n) = deg (x^(n-1)+x^(n-2)+...+x+1) = n-1.

*)

(* Theorem: For a Field F, its multiplicative group F* is cyclic.

By Cyclic defintion, need to show that Group F* has a generator.
By cyclic_finite_alt, just need to show: Group F* has an element with order = size of group.

The strategy is this:
* Go through all elements, and note its order.
* There must be a maximal order m, and an element z with ord z = m.
* Show that m <= n, where n = |F*|
* Show that n <= m, hence m = n, and Group F* has generator z.

The proof of m <= n is group-theoretic:
   Given a FiniteGroup F*, let n = |F*|, m = maximal order in F*.
   Let z be the element attaining the maximal order m.
   Then <z> <= F*, hence m = |<z>| <= |F*| = n, or m <= n.

The proof of n <= m is a mix of group order and polynomial roots:
   For any element x in F*,
   Let order of x = p, then p divides m,  by group_order_divides_maximal
   That is, m = pq, and x is a root of the polynomial x^m-#1 in F[x]:
     x^m = x^(pq)
         = (x^p)^q      by group_exp_mult
         = #1^q         by group_order_property
         = #1           by group_id_exp

   Hence the polynomial x^m - |1| in F[x] has n roots in F,
   but its degree is m, thus n <= m    by poly_roots_count.

This proof is in: ffAdvancedTheory.finite_field_mult_group_cyclic
*)

(* Can this reasoning be applied to show:
   * (uroots n) <= g                      by group_uroots_subgroup
   * There is a primitive in (uroots n)   by cyclic_uroots_has_primitive
   * This is a primitive root of x ** n - #1,
     or there are n roots in (uroots n) ?

   Seems the best thing is this:
   cyclic_uroots_has_primitive  |- !g. FINITE G /\ cyclic g ==>
                                   !n. ?z. z IN (uroots n).carrier /\ (ord z = CARD (uroots n).carrier)
   cyclic_uroots_cyclic         |- !g. FINITE G /\ cyclic g ==> !n. cyclic (uroots n)
*)

(*
   Given a Field F, for any n, what about the roots of x^n - |1| ?

   If n = CARD |F*| = CARD |F| - 1, all x IN R+ are roots.
   If n < CARD |F*|,
   If n > CARD |F*|,

   Example:
   Let F = Zp where p = 2. CARD |F*| = 1.
   x^1 - 1  has 1 root: (1)^1 - 1 = 0 (splitting field).
   x^2 - 1  has 1 root: (1)^2 - 1 = 0.

   Let F = Zp where p = 3. CARD |F*| = 2.
   x^1 - 1  has 1 root:  (1)^1 - 1 = 0, (2)^1 - 1 = 1 <> 0.
   x^2 - 1  has 2 roots: (1)^2 - 1 = 0, (2)^2 - 1 = 3 = 0 = (-1)^2 - 1 (splitting field).
   x^3 - 1  has 1 root:  (1)^3 - 1 = 0, (2)^3 - 1 = 7 <> 0.
   x^4 - 1  has 2 roots: (1)^4 - 1 = 0, (2)^4 - 1 = 15 = 0 = (-1)^4 - 1.

   Let F = GF4 = {0, 1, b, t}, where b + t = 1, b * t = 1. CARD |F*| = 3.
   x^1 - 1  has 1 root:  (1)^1 - 1 = 0.
   x^2 - 1  has 2 root:  (1)^2 - 1 = 0, but -1 = 1, hence repeated.
   x^3 - 1  has 3 roots: (1)^3 - 1 = 0, b^3 - 1 = 0, t^3 - 1 = 0 (splitting field).
   x^4 - 1  has 1 root:  (1)^4 - 1 = 0.
   x^5 - 1  has 1 root:  (1)^5 - 1 = 0.

   Note: GF4 = {0, 1, x, 1+x}, with x + (1+x) = 1, x(1+x) = 1

  +    0   1     x  1+x        0 1     x 1+x
  0    0   1     x  1+x    0   0 0     0   0
  1    1   0   1+x    x    1   0 1     x 1+x
  i      x 1+x   0    1      x 0   x 1+x 1
  1+x  1+x   x   1    0    1+x 0 1+x 1     x
  i.e. in GF4, x*x = 1 + x <> -1.

   Let F = Zp where p = 5. CARD |F*| = 4.
   x^1 - 1  has 1 root:  (1)^1 - 1 = 0.
   x^2 - 1  has 2 roots: (1)^2 - 1 = 0, -1 = 4, (4)^2 - 1 = 15 = 0.
   x^3 - 1  has 1 root:  (1)^3 - 1 = 0.
   x^4 - 1  has 1 root:  (1)^4 - 1 = 0.
   x^5 - 1  has 5 roots: (1)^5 - 1 = 0, (x-1)(x^4+x^3+x^2+x+1) = 0.
   x^6 - 1  has 1 root:  (1)^6 - 1 = 0.

   The number of n-th roots equals gcd(n, CARD |F*|).

   The multiplicative group of F* is cyclic, let g be a generator.
   For an element x of the group x^n=1 holds iff x=g^m with nm divisible by CARD |F*|.
   The latter is equivalent to m divisible by (CARD |F*|)/d, where d := gcd(n, CARD |F*|),
   hence the n-th roots of unity form the subgroup generated by g^(CARD |F*|)/d.
   This subgroup clearly has d elements, so the number of n-th roots equals gcd(n, CARD |F*|).
*)

(* ------------------------------------------------------------------------- *)
(* Cyclic Polynomials                                                        *)
(* ------------------------------------------------------------------------- *)

(* The Basic Identity:
   X ** n - |1| = (X - |1|) * (X ** (n-1) + ... + X + |1|)
                = (X - |1|) * (cyclic n)
*)

(*
While cyclotomic polynomial are irreducible over Q, not all of them are irreducible
when considered as a polynomial over a finite field. For example, over F_2, the
7-th cyclotomic polynomial phi_7 = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 factors into
two factors of degree 3: phi_7 = (x^3 + x + 1)(x^3 + x^2 + 1) in F_2.

One can show that the cyclotomic polynomial phi_n is irreducible over F_p precisely
when p has multiplicative order phi(n) modulo n. This follows from the theory of
cyclotomic extension of Q.

In particular, if (Z/nZ)* is not cyclic (i.e. unless n is an odd prime, twice an odd prime,
or n = 2 or 4), then phi_n is reducible module every prime p, despite being irreducible over Q.
*)

(*
Observe that the polynomial x^k - 1 over Z_m[x], with 1 < m:

For 0 < k,  x^k - 1 = (x - 1)(x^(k-1) + ... + x + 1)

This equation holds for any Ring r with #1 <> #0.

Whether and how the cofactor of (x - 1) splits into factors depends on k and m.
Focus on the case where k, m = p are different primes.

p = 11, k = 5: In Z_11[x], x^4 + x^3 + x^2 + x + 1 = (x + 8)(x + 7)(x + 6)(x + 2) -- linear factors
p = 11, k = 7: In Z_11[x], x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 = (x^3 + 5x^2 + 4x + 10)(x^3 + 7x^2 + 6x + 10) -- irreducible pair
p =  7, k = 5: In  Z_7[x], x^4 + x^3 + x^2 + x + 1 is irreducible.

Why, because by 7.6.2 (below), the crucial parameter is order_k(p)

p = 11, k = 5, order_5(11) = order_5(11 MOD 5) = order_5(1) = 1, hence factors of degree 1.
p = 11, k = 7, order_7(11) = order_7(11 MOD 7) = order_7(4) = 3, hence factors of degree 3.
p =  7, k = 5, order_5(7) = order_5(7 MOD 5) = order_5(2) = 4, hence factors of degree 4.

-- Therefore, while PHI(prime k) is irreducible in Z[x], PHI(prime k) may/maynot be irreducible in Z_p[x].

Theorem (7.4.6): Let F' = F[x]/(h). Then e = (X % h) IN F' is a root of h, i.e. h(e) = 0 IN F'.
Note: If 1 < deg h, then e = X IN (F' - F).
      If deg h = 1, then h = X + a for some a IN F, and e = -a.
      by (7.3.3) for modulo calculation.
This is poly_mod_ring_has_root_X  |- !r z. Ring r /\ ulead z ==> (peval z X % z = |0|)
or poly_field_lift_mod_has_root_X |- !r. Field r ==> !z. poly z /\ 1 < deg z ==> rootz (lift z) X

Theorem (7.6.2): Let prime p and prime r and p <> r.
Let h = a monic irreducible factor of (X^k - 1) DIV (X - 1), which exists by 7.4.4 (Unique Factorization)
Then in the Field F = Z_p[x]/(h), the element e = (X % h) satisfies order_F(e) = k.
Proof:
Let X^k - 1 = (X - 1) * h * q
e = X % h is a root of h in F, by 7.4.6, i.e. h(e) = 0.
so e is also a root of the product h * q, and the entire product (X - 1) * h * q.
Thus (1) e^(k-1) + ... + e + 1 = 0   by (h * q)(e) = 0
 and (2) e^k - 1 = 0, or e^k = 1     by ((X - 1) * h * q)(e) = 0
From (2), order_F(e) divides k.
But prime k, so order_F(e) = 1, or order_F(e) = k.
But order_F(e) = 1 <=> e = 1      by group_order_eq_1
If e = 1, (1) gives: 1^(k-1) + ... + 1 + 1 = 0, or k = 0 (mod p), which is impossible as prime k <> p.
Therefore order_F(e) = k.

*)

(*
Factorization of Cyclic Polynomials in Finite Field

Let cyclic n = [#1;#1;#1; ... ; #1] (n elements) = GENLIST (\k. #1) n
            = 1 + X + X^2 + ... + X^(n-1) in conventional form
Then X^n - |1| = (X - |1|) * (cyclic n)

The Factorization of (cyclic n) when considered as element of R[x] is the focus here.

Should be simple to show:
cyclic 0 = [] = |0|, and X^0 - |1| = |0|, or X^0 = |1|.
cyclic 1 = [#1] = |1|, and X^1 - |1| = (X - |1|). cyclic 1 is trivially irreducible.
cyclic 2 = [#1;#1] = X + |1|, and X^2 - |1| = (X - |1|)(X + |1|). cyclic 2 is (also) trivially determine.

After this, there is no generic factorization.

cyclic 3 = X^2 + X + 1        in Z_2. order_3(2) = 2
         = (X + 2)^2          in Z_3. order_3(3) = none
         = (X + a)(X + b)     in F_4. order_3(4) = order_3(1) = 1
         = X^2 + X + 1        in Z_5. order_3(5) = order_3(2) = 2
         = (X + 5)(X + 3)     in Z_7. order_3(7) = order_3(1) = 1
         = X^2 + X + 1        in Z_11. order_3(11) = order_3(2) = 2
         = (X + 10)(X + 4)    in Z_13. order_3(13) = order_3(1) = 1
         = (X + 12)(X + 8)    in Z_19. order_3(19) = order_3(1) = 1

cyclic 4 = X^3 + X^2 + X + 1
         = (X + 1)^3               in Z_2, order_4(2) = none
         = (X^2 + 1)(X + 1)        in Z_3. order_4(3) = 2
         = (X + 3)(X + 2)(X + 1)   in Z_5. order_4(5) = order_4(1) = 1
         = (X^2 + 1)(X + 1)        in Z_7. order_4(7) = order_4(3) = 2
         = (X^2 + 1)(X + 1)        in Z_11. order_4(11) = order_4(3) = 2
         = (X + 8)(X + 5)(X + 1)   in Z_13. order_4(13) = order_4(1) = 1
         = (X + 13)(X + 4)(X + 1)  in Z_17. order_4(17) = order_4(1) = 1
         = (X^2 + 1)(X + 1)        in Z_19. order_4(19) = order_4(3) = 2

cyclic 5 = X^4 + X^3 + X^2 + X + 1        in Z_2. order_5(2) = 4
         = X^4 + X^3 + X^2 + X + 1        in Z_3. order_5(3) = 4
         = (X^2 + aX + 1)(X^2 + bX + 1)   in F_4. order_5(4) = 2
         = (X + 4)^4                      in Z_5. order_5(5) = none
         = X^4 + X^3 + X^2 + X + 1        in Z_7. order_5(7) = order_5(2) = 4
         = (X + 8)(X + 7)(X + 6)(X + 2)   in Z_11. order_5(11) = 1
         = X^4 + X^3 + X^2 + X + 1        in Z_13. order_5(13) = order_5(3) = 4
         = X^4 + X^3 + X^2 + X + 1        in Z_17. order_5(17) = order_5(2) = 4
         = (X^2 + 15X + 1)(X^2 + 5X + 1)  in Z_19. order_5(19) = order_5(4) = 2

cyclic 6 = X^5 + X^4 + X^3 + X^2 + X + 1
         = (X + 1)(X^2 + X + 1)^2                in Z_2. order_6(2) = none
         = (X + 2)^2 (X + 1)^3                   in Z_3. order_6(3) = none
         = (X^2 + 4X + 1)(X^2 + X + 1)(X + 1)    in Z_5. order_6(5) = 2
         = (X + 5)(X + 4)(X + 3)(X + 2)(X + 1)   in Z_7. order_6(7) = order_6(1) = 1
         = (X^2 + 10X + 1)(X^2 + X + 1)(X + 1)   in Z_11. order_6(11) = order_6(5) = 2
         = (X + 10)(X + 9)(X + 4)(X + 3)(X + 1)  in Z_13. order_6(13) = order_6(1) = 1
         = (X^2 + 16X + 1)(X^2 + X + 1)(X + 1)   in Z_17. order_6(17) = order_6(5) = 2
         = (X + 12)(X + 11)(X + 8)(X + 7)(X + 1) in Z_19. order_6(19) = order_6(1) = 1

cyclic 7 = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1
         = (X^3 + X^2 + 1)(X^3 + X + 1)                  in Z_2. order_7(2) = 3.
         = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1           in Z_3. order_7(3) = 6.
         = (X^3 + X^2 + 1)(X^3 + X + 1)                  in F_4. order_7(4) = 3.
         = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1           in Z_5. order_7(5) = 6.
         = (X + 6)^6                                     in Z_7. order_7(7) = none.
         = (X^3 + 7X^2 + 6X + 10)(X^3 + 5X^2 + 4X + 10)  in Z_11. order_7(11) = order_7(4) = 3.
         = (X^2 + 6X + 1)(X^2 + 5X + 1)(X^2 + 3X + 1)    in Z_13. order_7(13) = order_7(6) = 2.
         = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1           in Z_17. order_7(17) = order_7(3) = 6.
         = X^6 + X^5 + X^4 + X^3 + X^2 + X + 1           in Z_19. order_7(19) = order_7(5) = 6.

cyclic 8 = X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1
         = (X + 1)^7                                             in Z_2. order_8(2) = none
         = (X^2 + 2X + 2)(X^2 + X + 2)(X^2 + 1)(X + 1)           in Z_3. order_8(3) = 2
         = (X^2 + 3)(X^2 + 2)(X + 3)(X + 2)(X + 1)               in Z_5. order_8(5) = 2
         = (X^2 + 4X + 1)(X^2 + 3X + 1)(X^2 + 1)(X + 1)          in Z_7. order_8(7) = 2
         = (X^2 + 8X + 10)(X^2 + 3X + 10)(X^2 + 1)(X + 1)        in Z_11. order_8(11) = order_8(3) = 2
         = (X^2 + 8)(X^2 + 5)(X + 8)(X + 5)(X + 1)               in Z_13. order_8(13) = order_8(5) = 2
         = (X + 15)(X + 13)(X + 9)(X + 8)(X + 4)(X + 2)(X + 1)   in Z_17. order_8(17) = order_8(1) = 1
         = (X^2 + 13X + 18)(X^2 + 6X + 18)(X^2 + 1)(X + 1)       in Z_19. order_8(19) = order_8(3) = 2

cyclic 9 = X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1
         = (X^6 + X^3 + 1)(X^2 + X + 1)                                   in Z_2. order_9(2) = 6
         = (X + 2)^8                                                      in Z_3. order_9(3) = none
         = ???                                                            in F_4. order_9(4) = 3
         = (X^6 + X^3 + 1)(X^2 + X + 1)                                   in Z_5. order_9(5) = 6
         = (X^3 + 5)(X^3 + 3)(X + 5)(X + 3)                               in Z_7. order_9(7) =  3
         = (X^6 + X^3 + 1)(X^2 + X + 1)                                   in Z_11. order_9(11) = order_9(2) = 6
         = (X^3 + 10)(X^3 + 4)(X + 10)(X + 4)                             in Z_13. order_9(13) = order_9(4) = 3
         = (X^2 + 10X + 1)(X^2 + 4X + 1)(X^2 + 3X + 1)(X^2 + X + 1)       in Z_17. order_9(17) = order_9(8) = 2
         = (X + 15)(X + 14)(X + 13)(X + 12)(X + 10)(X + 8)(X + 3)(X + 2)  in Z_19. order_9(19) = order_9(1) = 1


p = 11, k = 5: In Z_11[x], x^4 + x^3 + x^2 + x + 1 = (x + 8)(x + 7)(x + 6)(x + 2) -- linear factors
p = 11, k = 7: In Z_11[x], x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 = (x^3 + 5x^2 + 4x + 10)(x^3 + 7x^2 + 6x + 10) -- irreducible pair
p =  7, k = 5: In  Z_7[x], x^4 + x^3 + x^2 + x + 1 is irreducible.

Why, because by 7.6.2 (below), the crucial parameter is order_k(p)

p = 11, k = 5, order_5(11) = order_5(11 MOD 5) = order_5(1) = 1, hence factors of degree 1.
p = 11, k = 7, order_7(11) = order_7(11 MOD 7) = order_7(4) = 3, hence factors of degree 3.
p =  7, k = 5, order_5(7) = order_5(7 MOD 5) = order_5(2) = 4, hence factors of degree 4.
*)

(* Define Cyclic polynomials *)
val poly_cyclic_def = Define`
   poly_cyclic (r:'a ring) n = GENLIST (\k. #1) n
`;
(* Use overload for poly_cyclic *)
val _ = overload_on("cyclic", ``poly_cyclic r``);
(* cyclic n = [#1;#1;#1; ... ;#1] (n elements) = 1 + X + X^2 + ... + X^(n-1) in conventional form *)

(* Theorem: cyclic 0 = |0| *)
(* Proof:
     cyclic 0
   = GENLIST (\k. #1) 0    by poly_cyclic_def
   = []                    by GENLIST
   = |0|                   by poly_zero
*)
val poly_cyclic_0 = store_thm(
  "poly_cyclic_0",
  ``!r:'a ring. cyclic 0 = |0|``,
  rw[poly_cyclic_def]);

(* Theorem: cyclic 1 = |1| *)
(* Proof:
     cyclic 1
   = GENLIST (\k. #1) 1            by poly_cyclic_def
   = SNOC #1 (GENLIST (\k. #1) []) by GENLIST
   = SNOC #1 []                    by GENLIST
   = [#1]                          by SNOC
   = |1|                           by poly_one
*)
val poly_cyclic_1 = store_thm(
  "poly_cyclic_1",
  ``!r:'a ring. #1 <> #0 ==> (cyclic 1 = |1|)``,
  rw[poly_cyclic_def, poly_one]);

(* export simple results *)
val _ = export_rewrites ["poly_cyclic_0", "poly_cyclic_1"];

(* Theorem: cyclic (SUC n) = #1:: cyclic n *)
(* Proof:
     cyclic (SUC n)
   = GENLIST (\k. #1) (SUC n)      by poly_cyclic_def
   = SNOC #1 (GENLIST (\k. #1) n)  by GENLIST
   = SNOC #1 (cyclic n)

   By induction on n.
   Base case: cyclic (SUC 0) = #1::cyclic 0
     LHS = cyclic (SUC 0)
         = cyclic 1                             by ONE
         = [#1]                                 by poly_cyclic_1
         = #1::|0|                              by poly_zero
         = #1::cyclic 0                         by poly_cyclic_0
         = RHS
   Step case: cyclic (SUC n) = #1::cyclic n ==> cyclic (SUC (SUC n)) = #1::cyclic (SUC n)
     LHS = cyclic (SUC (SUC n))
         = GENLIST (\k. #1) (SUC (SUC n))       by poly_cyclic_def
         = SNOC #1 (GENLIST (\k. #1) (SUC n))   by GENLIST
         = SNOC #1 (cyclic (SUC n))             by poly_cyclic_def
         = SNOC #1 (#1 :: cyclic n)             by induction hypothesis
         = #1:: SNOC #1 (cyclic n)              by SNOC
         = #1:: cyclic (SUC n)                  by above.
         = RHS
*)
val poly_cyclic_suc = store_thm(
  "poly_cyclic_suc",
  ``!r:'a ring. #1 <> #0 ==> !n. cyclic (SUC n) = #1:: cyclic n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[poly_one] >>
  `cyclic (SUC (SUC n)) = GENLIST (\k. #1) (SUC (SUC n))` by rw[poly_cyclic_def] >>
  `_ = SNOC #1 (GENLIST (\k. #1) (SUC n))` by rw[GENLIST] >>
  `_ = SNOC #1 (cyclic (SUC n))` by rw[GSYM poly_cyclic_def] >>
  `_ = SNOC #1 (#1 :: cyclic n)` by rw[] >>
  `_ = #1:: SNOC #1 (cyclic n)` by rw[SNOC] >>
  `_ = #1:: SNOC #1 (GENLIST (\k. #1) n)` by rw[poly_cyclic_def] >>
  `_ = #1:: GENLIST (\k. #1) (SUC n) ` by rw[GENLIST] >>
  `_ = #1:: cyclic (SUC n)` by rw[GSYM poly_cyclic_def] >>
  rw[]);

(* export simple results *)
val _ = export_rewrites ["poly_cyclic_suc"];

(* Theorem: poly (cyclic n) *)
(* Proof:
   By induction on n.
   Base case: poly (cyclic 0)
      Since cyclic 0 = |0|                  by poly_cyclic_0
        and poly |0|                        by poly_zero_poly
      Hence true.
   Step case: poly (cyclic n) ==> poly (cyclic (SUC n))
      Since cyclic (SUC k) = #1:: cyclic k  by poly_cyclic_suc
        and #1 IN R                         by ring_one_element
        and poly (cyclic k)                 by induction hypothesis
       Thus poly (#1:: cyclic k)            by poly_cons_poly
*)
val poly_cyclic_poly = store_thm(
  "poly_cyclic_poly",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. poly (cyclic n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* export simple results *)
val _ = export_rewrites ["poly_cyclic_poly"];

(* Theorem: cyclic n = |0| <=> n = 0 *)
(* Proof:
   If part: (cyclic n = |0|) ==> (n = 0)
      By contradiction. Let n <> 0.
      Then 0 < n, and n = SUC m.
      Hence cyclic n = cyclic (SUC m) = #1:: cyclic m   by poly_cyclic_suc
      Then cyclic n <> |0|                            by NOT_CONS_NIL
      which is a contradiction to cyclic n = |0|.
   Only-if part: (n = 0) ==> (cyclic n = |0|)
      True by poly_cyclic_0.
*)
val poly_cyclic_eq_zero = store_thm(
  "poly_cyclic_eq_zero",
  ``!r:'a ring. #1 <> #0 ==> !n. (cyclic n = |0|) <=> (n = 0)``,
  rw_tac std_ss[poly_cyclic_0, EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  metis_tac[poly_cyclic_suc, poly_zero, NOT_CONS_NIL]);

(* Theorem: 0 < n ==> lead (cyclic n) = #1 *)
(* Proof:
   By induction on n.
   Base case: 0 < 0 ==> (lead (cyclic 0) = #1)
     True since 0 < 0 is false.
   Step case: (lead (cyclic n) = #1 ==> (lead (cyclic (SUC n)) = #1)
       lead (cyclic (SUC n))
     = lead (#1:: (cyclic n))   by poly_cyclic_suc
     = lead [#1] = #1           if (cyclic n = |0|), by poly_lead_const
     = lead (cyclic n) = #1     if (cyclic n <> |0|), by induction hypothesis
*)
val poly_cyclic_lead = store_thm(
  "poly_cyclic_lead",
  ``!r:'a ring. #1 <> #0 ==> !n. 0 < n ==> (lead (cyclic n) = #1)``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rw[],
    rw_tac std_ss[] >>
    Cases_on `n = 0` >| [
      rw[],
      `0 < n` by decide_tac >>
      `cyclic n <> |0|` by metis_tac[poly_cyclic_eq_zero] >>
      rw_tac std_ss[poly_cyclic_suc, poly_lead_cons]
    ]
  ]);

(* export simple results *)
val _ = export_rewrites ["poly_cyclic_lead"];

(* Theorem: 0 < n ==> monic (cyclic n) *)
(* Proof: by poly_monic_def, with poly_cyclic_lead, poly_cyclic_poly. *)
val poly_cyclic_monic = store_thm(
  "poly_cyclic_monic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> monic (cyclic n)``,
  rw[poly_monic_def]);

(* Theorem: deg (cyclic n) = PRE n *)
(* Proof:
   By induction on n.
   Base case: deg (cyclic 0) = PRE 0
     LHS = deg (cycle 0)
         = deg |0|              by poly_cyclic_0
         = 0 = RHS              by poly_deg_zero, PRE 0 = 0.
   Step case: deg (cyclic n) = PRE n ==> deg (cyclic (SUC n)) = PRE (SUC n)
       deg (cyclic (SUC n))
     = deg (#1:: cyclic n)       by poly_cyclic_suc
     = deg [#1] = 0             if (cyclic n = |0|), by poly_deg_const, PRE 1 = 0.
     = SUC (deg (cyclic n))      if (cyclic n <> |0|), by poly_deg_cons
     = SUC (PRE n)              by induction hypothesis
     = n                        by SUC_PRE, 0 < n
     = PRE (SUC n)              by prim_recTheory.PRE
*)
val poly_cyclic_deg = store_thm(
  "poly_cyclic_deg",
  ``!r:'a ring. #1 <> #0 ==> !n. deg (cyclic n) = PRE n``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rw[],
    rw_tac std_ss[poly_cyclic_suc] >>
    Cases_on `n = 0` >| [
      rw[],
      `0 < n` by decide_tac >>
      `cyclic n <> |0|` by metis_tac[poly_cyclic_eq_zero] >>
      rw[GSYM SUC_PRE]
    ]
  ]);

(* Theorem: eval (cyclic n) #1 = ##n *)
(* Proof:
   By induction on n.
   Base case: eval (cyclic 0) #1 = ##0
     LHS = eval (cyclic 0) #1
         = eval |0| #1               by poly_cyclic_0
         = #0                        by poly_eval_zero
         = ##0                       by ring_num_0
         = RHS
   Step case: eval (cyclic n) #1 = ##n ==> eval (cyclic (SUC n)) #1 = ##(SUC n)
       eval (cyclic (SUC n)) #1
     = eval (#1::(cyclic n)) #1      by poly_cyclic_suc
     = #1 + eval (cyclic n) #1 * #1  by poly_eval_cons
     = #1 + ##n * #1                 by induction hypothesis
     = #1 + ##n                      by ring_mult_rone
     = ##(SUC n)                     by ring_num_SUC
*)
val poly_cyclic_eval_by_one = store_thm(
  "poly_cyclic_eval_by_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. eval (cyclic n) #1 = ##n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* Theorem: peval (cyclic n) |1| = |n| *)
(* Proof:
   By induction on n.
   Base case: peval (cyclic 0) |1| = ### 0
     LHS = peval (cyclic 0) |1|
         = peval |0| |1|                 by poly_cyclic_0
         = |0|                           by poly_peval_zero
         = ### 0                         by poly_one_sum_n
         = RHS
   Step case: peval (cyclic n) |1| = |n| ==> peval (cyclic (SUC n)) |1| = ### (SUC n)
       peval (cyclic (SUC n)) |1|
     = peval (#1::(cyclic n)) |1|        by poly_cyclic_suc
     = |1| + peval (cyclic n) |1| * |1|  by poly_peval_cons
     = |1| + |n| * |1|                   by induction hypothesis
     = |1| + |n|                         by poly_mult_rone
     = ### (SUC n)                       by poly_exp_SUC, ring_num_SUC
*)
val poly_cyclic_peval_by_one = store_thm(
  "poly_cyclic_peval_by_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. peval (cyclic n) |1| = |n|``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* Theorem: cyclic (SUC n) = X * cyclic n + |1| *)
(* Proof:
     cyclic (SUC n)
   = #1:: cyclic n                by poly_cyclic_suc
   = [#1] + (cyclic n) >> 1       by poly_cons_eq_add_shift
   = [#1] + (cyclic n) * X        by poly_mult_X
   = |1| + (cyclic n) * X         by poly_one, #1 <> #0
   = X * (cyclic n) + |1|         by poly_add_comm, poly_mult_comm
*)
val poly_cyclic_suc_alt = store_thm(
  "poly_cyclic_suc_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. cyclic (SUC n) = X * cyclic n + |1|``,
  rw[poly_cons_eq_add_shift, poly_mult_X, poly_add_comm, poly_mult_comm, poly_one]);

(* Theorem: unity n = unity 1 * (cyclic n) *)
(* Proof:
   By induction on n.
   Base case: unity 0 = unity 1 * cyclic 0
     LHS = unity 0
         = |0|                  by poly_unity_0
         = unity 1 * |0|        by poly_mult_rzero
         = unity 1 * cyclic 0   by poly_cyclic_0
         = RHS
   Step case: unity n = unity 1 * cyclic n ==> unity (SUC n) = unity 1 * cyclic (SUC n)
     First, unity n = unity 1 * cyclic n
      gives  X ** n = unity 1 * cyclic n + |1|

       unity (SUC n)
     = X ** SUC n - |1|                        by notation
     = X * X ** n - |1|                        by poly_exp_SUC
     = X * (unity 1 * cyclic n + |1|) - |1|    by induction hypothesis
     = X * unity 1 * cyclic n + X * |1| - |1|  by poly_mult_radd
     = X * unity 1 * cyclic n + X - |1|        by poly_mult_rone
     = X * unity 1 * cyclic n + (X - |1|)      by poly_add_assoc
     = X * unity 1 * cyclic n + unity 1        by poly_unity_1
     = unity 1 * X * cyclic n + unity 1        by poly_mult_comm
     = unity 1 * (X * cyclic n + |1|)          by poly_mult_ladd
     = unity 1 * cyclic (SUC n)                by poly_cyclic_suc_alt
*)
val poly_cyclic_cofactor = store_thm(
  "poly_cyclic_cofactor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. unity n = unity 1 * (cyclic n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[poly_unity_0, poly_cyclic_0, poly_unity_poly, poly_mult_rzero] >>
  `poly |1| /\ poly (unity 1) /\ poly (unity n) /\ poly (cyclic n)` by rw[] >>
  `poly X /\ poly (X ** n) /\ poly (X ** (SUC n))` by rw[] >>
  `X ** SUC n - X = X * X ** n - X` by rw[poly_exp_SUC] >>
  `_ = X * unity n` by rw[poly_mult_rsub] >>
  `_ = X * unity 1 * cyclic n` by rw_tac std_ss[poly_mult_assoc] >>
  `X ** SUC n = X * unity 1 * cyclic n + X` by metis_tac[poly_sub_add] >>
  `unity (SUC n) = X * unity 1 * cyclic n + (X - |1|)` by rw_tac std_ss[poly_add_sub_assoc, poly_mult_poly] >>
  `_ = unity 1 * (X * cyclic n) + unity 1` by rw_tac std_ss[poly_mult_comm, GSYM poly_mult_assoc, GSYM poly_unity_1] >>
  `_ = unity 1 * (X * cyclic n) + unity 1 * |1|` by rw_tac std_ss[poly_mult_rone] >>
  `_ = unity 1 * (X * cyclic n + |1|)` by rw_tac std_ss[GSYM poly_mult_radd, poly_mult_poly] >>
  rw_tac std_ss[poly_cyclic_suc_alt]);

(* ------------------------------------------------------------------------- *)
(* Cyclic Irreducible Factor                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r /\ 0 < n < char r ==> ~((unity 1|) pdivides (cyclic n)) *)
(* Proof:
    Since eval (cyclic n) #1 = ##n            by poly_cyclic_eval_by_one
      and 0 < n /\ n < char r                 by given
          ##n <> #0                           by char_minimal
       so ~(root (cyclic n) #1)               by poly_root_def
       or ~((cyclic n) % factor #1 = |0|)     by poly_root_thm, Field r
       or ~((cyclic n) % (X - |1|) = |0|)     by poly_factor_one
    Since pmonic (X - |1|),                   by poly_pmonic_X_sub_c
      and poly (cyclic n)                     by poly_cyclic_poly
    hence ~ ((X - |1|) pdivides (cyclic n))   by poly_divides_alt
*)
val poly_cyclic_has_no_factor_unity_1 = store_thm(
  "poly_cyclic_has_no_factor_unity_1",
  ``!r:'a field. Field r ==> !n. 0 < n /\ n < char r ==> ~((unity 1) pdivides (cyclic n))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < char r` by decide_tac >>
  `eval (cyclic n) #1 = ##n` by rw[poly_cyclic_eval_by_one] >>
  `##n <> #0` by rw[char_minimal] >>
  `~(root (cyclic n) #1)` by rw[poly_root_def] >>
  `~((cyclic n) % factor #1 = |0|)` by rw[poly_cyclic_poly, GSYM poly_root_thm] >>
  `~((cyclic n) % (unity 1) = |0|)` by metis_tac[poly_factor_one, poly_unity_1] >>
  `pmonic (unity 1)` by rw_tac std_ss[poly_unity_pmonic, DECIDE ``0 < 1``] >>
  `poly (cyclic n)` by rw[poly_cyclic_poly] >>
  metis_tac[poly_divides_alt]);

(* Theorem: Field r ==> !n. 1 < n ==> ?h. ipoly h /\ h pdivides (cyclic n) *)
(* Proof:
    Since deg (cyclic n) = PRE n                 by poly_cyclic_deg
    With  1 < n, 0 < PRE n,
    Hence 0 < deg (cyclic n)
     Thus ?h. ipoly h /\ h pdivides (cyclic n)   by poly_irreducible_factor_exists
*)
val poly_cyclic_irreducible_factor = store_thm(
  "poly_cyclic_irreducible_factor",
  ``!r:'a field. Field r ==> !n. 1 < n ==> ?h. ipoly h /\ h pdivides (cyclic n)``,
  rpt strip_tac >>
  `deg (cyclic n) = PRE n` by rw[poly_cyclic_deg] >>
  `0 < PRE n` by decide_tac >>
  rw[poly_irreducible_factor_exists]);

(*
From AKSsets.hol: Define monic irreducible factor
val _ = overload_on ("mifactor", ``\h z. monic h /\ ipoly h /\ (z % h = |0|)``);
*)

(* Theorem: Field r ==> !n. 1 < n ==> ?h. mifactor h (cyclic n) *)
(* Proof:
   Given Field r and 1 < n,
       ?q. ipoly q /\ q pdivides (cyclic n)              by poly_cyclic_irreducible_factor
    So ?c h. c IN R /\ monic h /\ ipoly h /\ (q = c * h) by poly_irreducible_make_monic
   Now pmonic h                                          by poly_monic_irreducible_property
   and ?s. poly s /\ (cyclic n = s * q)                  by poly_divides_def
   Hence  cyclic n = s * q
                  = s * (c * h)
                  = (c * s) * h                          by poly_mult_cmult
   With poly (c * s)                                     by poly_cmult_poly
    and poly (cyclic n)                                  by poly_cyclic_poly
     so (cyclic n) % h = |0|                             by poly_mod_eq_zero
   Therefore mifactor h (cyclic n)                       by overloading
*)
val poly_cyclic_monic_irreducible_factor = store_thm(
  "poly_cyclic_monic_irreducible_factor",
  ``!r:'a field. Field r ==> !n. 1 < n ==> ?h. mifactor h (cyclic n)``,
  rpt strip_tac >>
  `?q. ipoly q /\ q pdivides (cyclic n)` by rw[poly_cyclic_irreducible_factor] >>
  `?c h. c IN R /\ monic h /\ ipoly h /\ (q = c * h)` by rw[poly_irreducible_make_monic] >>
  `pmonic h` by rw[poly_monic_irreducible_property] >>
  `?s. poly s /\ (cyclic n = s * q)` by rw[GSYM poly_divides_def] >>
  `_ = c * s * h` by rw[poly_mult_cmult] >>
  `poly (c * s)` by rw[] >>
  `poly (cyclic n)` by rw[poly_cyclic_poly] >>
  metis_tac[poly_mod_eq_zero, field_is_ring]);

(* Theorem: Field r ==> !n. 1 < n /\ n < char r ==> ?h. mifactor h (unity n) /\ h <> unity 1 *)
(* Proof:
   First, unity n = unity 1 * cyclic n      by poly_cyclic_cofactor
    Thus  (cyclic n) pdivides (unity n)     by poly_divides_def
     Now  ?h. mifactor h (cyclic n)         by poly_cyclic_monic_irreducible_factor
     and  pmonic h                          by poly_monic_irreducible_property
      so  h pdivides (cyclic n)             by poly_divides_alt
   Hence  h pdivides (unity n)              by poly_divides_transitive
      so  (unity n) % h = |0|               by poly_divides_alt
   gives  mifactor h (unity n)
     But  ~(unity 1) pdivides (cyclic n))   by poly_cyclic_has_no_factor_unity_1
   Therefore h <> unity 1
*)
val poly_unity_irreducible_factor_exists = store_thm(
  "poly_unity_irreducible_factor_exists",
  ``!r:'a field. Field r ==> !n. 1 < n /\ n < char r ==> ?h. mifactor h (unity n) /\ h <> unity 1``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `unity n = unity 1 * cyclic n` by rw[poly_cyclic_cofactor] >>
  `poly (unity n) /\ poly (unity 1) /\ poly (cyclic n)` by rw[poly_unity_poly, poly_cyclic_poly] >>
  `(cyclic n) pdivides (unity n)` by metis_tac[poly_divides_def] >>
  `?h. mifactor h (cyclic n)` by rw[poly_cyclic_monic_irreducible_factor] >>
  `pmonic h` by rw[poly_monic_irreducible_property] >>
  `h pdivides (cyclic n)` by rw[poly_divides_alt] >>
  `h pdivides (unity n)` by metis_tac[poly_divides_transitive] >>
  `(unity n) % h = |0|` by rw[GSYM poly_divides_alt] >>
  `0 < n` by decide_tac >>
  metis_tac[poly_cyclic_has_no_factor_unity_1]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
