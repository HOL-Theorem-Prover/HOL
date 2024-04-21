(* ------------------------------------------------------------------------- *)
(* Polynomial Binomial with coefficients from a Ring.                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyBinomial";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory rich_listTheory numberTheory
     combinatoricsTheory dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory ringUnitTheory;

(* val _ = load "fieldInstancesTheory"; *)
open fieldTheory fieldInstancesTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;

open polyMonicTheory;
open polyFieldTheory;
open polyRootTheory;
open polyEvalTheory;

open ringBinomialTheory;
open ringInstancesTheory;

(* ------------------------------------------------------------------------- *)
(* Polynomial Binomial R[x] Documentation                                    *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   wfun f       = weak_fun r f
   psum l       = poly_weak_sum r l
   plist l      = poly_weak_list r l
   poly_fun f   = ring_fun (PolyRing r) f
   poly_sum l   = ring_sum (PolyRing r) l
   poly_list l  = ring_list (PolyRing r) l
   pdilate n p  = poly_dilate r n p
*)
(* Definitions and Theorems (# are exported):

   Polynomial Binomial in R[x]:
   poly_binomial_2       |- !r p q. Ring r ==> poly p /\ poly q ==>
                                    ((p + q) ** 2 = p ** 2 + ### 2 * (p * q) + q ** 2)
   poly_binomial_thm     |- !r x y. Ring r ==> poly x /\ poly y ==>
            !n. (x + y) ** n = poly_sum (GENLIST (\k. ### (binomial n k) * x ** (n - k) * y ** k) (SUC n))
   poly_freshman_thm     |- !r. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
                            ((x + y) ** char r = x ** char r + y ** char r)
   poly_freshman_thm_sub |- !r. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
                            ((x - y) ** char r = x ** char r - y ** char r)
   poly_freshman_all     |- !r. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
                            !n. (x + y) ** char r ** n = x ** char r ** n + y ** char r ** n
   poly_freshman_all_sub |- !r. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
                            !n. (x - y) ** char r ** n = x ** char r ** n - y ** char r ** n
   poly_fermat_thm       |- !r. Ring r /\ prime (char r) ==> !c. |c| ** char r = |c|
   poly_freshman_fermat  |- !r. Ring r /\ prime (char r) ==> !c. (X + |c|) ** char r = X ** char r + |c|
   poly_freshman_fermat_field
                         |- !r. FiniteField r ==> !c. (X + |c|) ** char r = X ** char r + |c|

   Weak Functions and Lists:
   weak_fun_def          |- !r f. wfun f <=> !x. weak (f x)
#  poly_weak_list_def    |- (!r. plist [] <=> T) /\ !r h t. plist (h::t) <=> weak h /\ plist t
   poly_weak_list_nil    |- !r. plist [] <=> T
   poly_weak_list_cons   |- !r h t. plist (h::t) <=> weak h /\ plist t
   poly_weak_list_SNOC   |- !r p s. weak p /\ plist s ==> plist (SNOC p s)
   poly_weak_list_from_weak_fun |- !r. Ring r ==> !f. wfun f ==> !n. plist (GENLIST f n)

   Weak Sum in Polynomial Ring:
#  poly_weak_sum_def   |- (!r. psum [] = |0|) /\ !r h t. psum (h::t) = h || psum t
   poly_weak_sum_nil   |- !r. psum [] = |0|
   poly_weak_sum_cons  |- !r h t. psum (h::t) = h || psum t
#  poly_weak_sum_weak  |- !r. Ring r ==> !s. plist s ==> weak (psum s)
   poly_weak_sum_sing  |- !r. Ring r ==> !p. weak p ==> (psum [p] = p)
   poly_weak_sum_SNOC  |- !r. Ring r ==> !p s. weak p /\ plist s ==> (psum (SNOC p s) = psum s || p)
   poly_weak_sum_genlist_suc      |- !r. Ring r ==> !f. wfun f ==>
                                     !n. f n || psum (GENLIST f n) = psum (GENLIST f (SUC n))

   Polynomial Functions and Lists:
   poly_fun_def                |- !r f. poly_fun f <=> !x. poly (f x)
#  poly_list_element           |- !r f. poly_fun f ==> !x. poly (f x)
#  poly_list_nil               |- !r. Ring r ==> poly_list []
#  poly_list_cons              |- !r. Ring r ==> !p s. poly_list (p::s) <=> poly p /\ poly_list s
   poly_list_SNOC              |- !r. Ring r ==> !p s. poly_list (SNOC p s) <=> poly p /\ poly_list s
   poly_list_from_poly_fun     |- !f s. poly_fun f /\ poly_list s ==> poly_list (MAP f s)
   poly_list_from_poly_mod     |- !r. Ring r ==> !z. ulead z ==> !s. poly_list s ==> poly_list (MAP (\x. x % z) s)
   poly_fun_from_ring_fun      |- !r. Ring r ==> !f. rfun f ==>
                                  !p. poly p ==> poly_fun (\j. f j * p ** j)
   poly_fun_from_ring_fun_exp  |- !r. Ring r ==> !f. rfun f ==>
                                  !p. poly p ==> !n. poly_fun (\j. (f j * p ** j) ** n)

   Polynomial Sum:
#  poly_sum_nil              |- !r. Ring r ==> (poly_sum [] = |0|)
#  poly_sum_cons             |- !r. Ring r ==> !p s. poly p /\ poly_list s ==> (poly_sum (p::s) = p + poly_sum s)
#  poly_sum_poly             |- !r. Ring r ==> !s. poly_list s ==> poly (poly_sum s)
   poly_sum_SNOC             |- !r. Ring r ==> !p s. poly p /\ poly_list s ==> (poly_sum (SNOC p s) = poly_sum s + p)
   poly_sum_const            |- !r. Ring r ==> !p. poly p ==> (poly_sum [p] = p)
   poly_cmult_poly_sum       |- !r. Ring r ==> !s. poly_list s ==>
                                !c. c IN R ==> (c * poly_sum s = poly_sum (MAP (\x. c * x) s))
   poly_mult_poly_sum        |- !r. Ring r ==> !s. poly_list s ==>
                                !p. poly p ==> (p * poly_sum s = poly_sum (MAP (\x. p * x) s))
   poly_mod_poly_sum         |- !r. Ring r ==> !s. poly_list s ==>
                                !z. ulead z ==> (poly_sum s % z = poly_sum (MAP (\x. x % z) s) % z)

   Sum over GENLIST in Polynomial Ring:
   weak_genlist            |- !r f. rfun f ==> !n. weak (GENLIST f n)
   poly_genlist            |- !r f. rfun f ==> !n. f n <> #0 ==> poly (GENLIST f (SUC n))
   poly_weak_list_genlist  |- !r. Ring r ==> !f. rfun f ==> !n. plist (GENLIST (\k. f k o (X ** k)) n)
   poly_deg_weak_sum_genlist  |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f ==>
                                 (deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n))) = n)
   poly_list_by_weak_list  |- !r. Ring r ==> !s. plist s ==> poly_list (MAP chop s)
   poly_sum_by_weak_sum    |- !r. Ring r ==> !s. plist s ==> (poly_sum (MAP chop s) = chop (psum s))
   poly_chop_weak_sum      |- !r. Ring r ==> !s. plist s ==> (chop (psum s) = poly_sum (MAP chop s))
   poly_chop_with_function |- !r. Ring r ==> !f. rfun f ==> ((\k. chop (f k o (X ** k))) = chop o (\k. f k o (X ** k)))
   poly_cmult_in_function  |- !r. Ring r ==> !f. rfun f ==> ((\j. f j * X ** j) = (\j. chop (f j o (X ** j))))
   poly_sum_by_weak_sum_genlist  |- !r. Ring r /\ #1 <> #0 ==> !f. rfun f ==>
                              !n. poly_sum (GENLIST (\j. f j * X ** j) n) = chop (psum (GENLIST (\j. f j o (X ** j)) n))
   poly_coeff_sum_genlist  |- !r. Ring r /\ #1 <> #0 ==> !f n k. rfun f /\ k < SUC n ==>
                                  (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k = f k)

   Polynomial Identity only for Primes:
   poly_mult_num_const_exp  |- !r. Ring r ==> !p c. weak p /\ c IN R ==> !n k. |n| * [c] ** k * p = ##n * c ** k * p
   poly_coeff_X_add_c_exp_n |- !r. Ring r ==> !c. c IN R /\ c <> #0 ==> !n k.
                                   k < SUC n ==> (((X + [c]) ** n) ' k = ##(binomial n k) * c ** (n - k))
   poly_coeff_factor_exp    |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==>
                               !k n. (factor c ** n) ' k = if n < k then #0
                                     else if n = k then #1 else ##(binomial n k) * -c ** (n - k)
   poly_ring_prime_identity |- !r. Ring r ==> !c. coprime c (char r) ==>
                                   (prime (char r) <=> 1 < char r /\ ((X + |c|) ** char r = X ** char r + |c|))
   poly_ring_prime_char_eqn |- !r. Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==>
                                   (prime (char r) <=> ((X + |c|) ** char r = X ** char r + |c|))
   poly_ZN_prod_id          |- !n. 1 < n ==> ((PolyRing (ZN n)).prod.id = [1])
   poly_ZN_prime_identity   |- !n c. 1 < n /\ coprime c n ==> (prime n <=> (x+^ n c n = x^+ n c n))
   poly_ZN_prime_thm        |- !n c. coprime c n ==> (prime n <=> 1 < n /\ x+^ n c n = x^+ n c n)
   poly_ZN_prime_simple     |- !n. prime n <=> 1 < n /\ (x+^ n 1 n = x^+ n 1 n)
   poly_ZN_freshman_fermat  |- !n c. prime n ==> (x+^ n c n = x^+ n c n)

   Polynomial as sum of Terms:
   poly_coeff_ring_fun      |- !r. Ring r ==> !p. poly p ==> rfun (\k. p ' k)
   poly_coeff_eq_poly_zero  |- !r. Ring r ==> !p q. poly p /\ poly q /\
                                              (!k. p ' k = q ' k) ==> ((p = |0|) <=> (q = |0|))
   poly_coeff_eq_deg_eq     |- !r. Ring r ==> !p q. poly p /\ poly q /\
                                              (!k. p ' k = q ' k) ==> (deg p = deg q)
   poly_coeff_eq_poly_eq    |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p = q) <=> !k. p ' k = q ' k)
   poly_sum_gen_append      |- !r. Ring r ==> !a b. poly_fun a /\ poly_fun b ==>
                               !n. poly_sum (GENLIST a n ++ GENLIST b n) = poly_sum (GENLIST (\k. a k + b k) n)
   poly_sum_gen_const       |- !r. Ring r ==> !p. poly p ==> !n. poly_sum (GENLIST (K p) n) = |n| * p
   poly_sum_decompose_first |- !r f n. poly_sum (GENLIST f (SUC n)) = f 0 + poly_sum (GENLIST (f o SUC) n)
   poly_sum_decompose_last  |- !r. Ring r ==> !f. poly_fun f ==>
                               !n. poly_sum (GENLIST f (SUC n)) = poly_sum (GENLIST f n) + f n

   poly_list_gen_from_poly_fun   |- !r. Ring r ==> !f. poly_fun f ==> !n. poly_list (GENLIST f n)
   poly_list_gen_from_ring_fun   |- !r. Ring r ==> !f. rfun f ==> !p. poly p ==>
                                    !n. poly_list (GENLIST (\j. f j * p ** j) n)
#  poly_sum_gen_poly_fun_poly    |- !r. Ring r ==> !f. poly_fun f ==>
                                    !n. poly (poly_sum (GENLIST f n)
#  poly_sum_gen_ring_fun_poly    |- !r. Ring r ==> !f. rfun f ==> !p. poly p ==>
                                    !n. poly (poly_sum (GENLIST (\j. f j * p ** j) n))

   poly_sum_gen_deg_bound   |- !r. Ring r /\ #1 <> #0 ==> !f. rfun f ==>
                               !n. deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) <= n
   poly_sum_gen_deg         |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
                                   (deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n)
   poly_sum_gen_lead        |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
                                   (lead (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = f n)
   poly_eq_poly_sum         |- !r. Ring r /\ #1 <> #0 ==> !p. poly p ==>
                                   (p = poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p))))
   weak_poly_sum_genlist    |- !r. Ring r ==> !f. wfun f ==> !p. weak p ==>
                                   (poly_sum (GENLIST (\k. chop p ' k * f k) (SUC (deg (chop p)))) =
                                    poly_sum (GENLIST (\k. p ' k * f k) (SUC (deg p))))

   Freshman Theorems for Polynomial Sums:
   poly_sum_freshman_thm   |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
                              !n. poly_sum (GENLIST (\j. f j * p ** j) n) ** char r =
                                  poly_sum (GENLIST (\j. (f j * p ** j) ** char r) n)
   poly_sum_freshman_all   |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
                              !n k. poly_sum (GENLIST (\j. f j * p ** j) n) ** char r ** k =
                                    poly_sum (GENLIST (\j. (f j * p ** j) ** char r ** k) n)

   More on Evaluation of Polynomials:
   poly_eval_poly_list     |- !r. Ring r ==> !s. poly_list s ==>
                              !x. x IN R ==> rlist (MAP (\p. eval p x) s)
   poly_eval_poly_sum      |- !r. Ring r ==> !s. poly_list s ==>
                              !x. x IN R ==> (eval (poly_sum s) x = rsum (MAP (\p. eval p x) s))
   poly_eval_poly_sum_gen  |- !r. Ring r ==> !f. poly_fun f ==> !x. x IN R ==>
                              !n. eval (poly_sum (GENLIST f n)) x = rsum (MAP (\p. eval p x) (GENLIST f n))
   poly_eval_poly_sum_gen_poly  |- !r. Ring r ==> !f. rfun f ==> !p x. poly p /\ x IN R ==>
                                   !n. eval (poly_sum (GENLIST (\k. f k * p ** k) n)) x =
                                       rsum (GENLIST (\k. f k * eval p x ** k) n)
   poly_eval_by_ring_sum   |- !r. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==>
                              (eval p x = rsum (GENLIST (\k. p ' k * x ** k) (SUC (deg p))))

   More on Polynomial Evaluation by Polynomials:
   poly_peval_poly_list    |- !r. Ring r ==> !s. poly_list s ==>
                              !p. poly p ==> poly_list (MAP (\x. peval x p) s)
   poly_peval_poly_sum     |- !r. Ring r ==> !s. poly_list s ==>
                              !p. poly p ==> (peval (poly_sum s) p = poly_sum (MAP (\x. peval x p) s)
   poly_peval_poly_sum_gen |- !r. Ring r ==> !f. poly_fun f ==> !p. poly p ==>
                              !n. peval (poly_sum (GENLIST f n)) p =
                                  poly_sum (MAP (\x. peval x p) (GENLIST f n))
   poly_peval_poly_sum_gen_poly
                           |- !r. Ring r ==> !f. rfun f ==> !p q. poly p /\ poly q ==>
                              !n. peval (poly_sum (GENLIST (\k. f k * p ** k) n)) q =
                                        poly_sum (GENLIST (\k. f k * peval p q ** k) n)
   poly_peval_by_poly_sum  |- !r. Ring r /\ #1 <> #0 ==> !p q. poly p /\ poly q ==>
                              (peval p q = poly_sum (GENLIST (\k. p ' k * q ** k) (SUC (deg p))))

   Polynomial Sums of Distinct Degrees:
   poly_sum_deg         |- !r. Ring r ==> !s. poly_list s /\
                ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg s)) ==> (deg (poly_sum s) = MAX_LIST (MAP deg s))
   poly_genlist_deg_distinct  |- !r. Field r ==> !p. poly p /\ 0 < deg p ==> !f. rfun f ==>
                             !n. ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) n)))
   poly_sum_gen_eq_zero |- !r. Field r ==> !f. rfun f ==> !p. poly p /\ 0 < deg p ==>
                           !n. (poly_sum (GENLIST (\j. f j * p ** j) n) = |0|) <=> !j. j < n ==> (f j = #0)
   poly_peval_eq_zero   |- !r. Field r ==> !p q. poly p /\ poly q /\ 0 < deg q ==>
                               ((peval p q = |0|) <=> (p = |0|))
   poly_peval_eq        |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t /\ 0 < deg t ==>
                               ((peval p t = peval q t) <=> (p = q))
   poly_peval_poly_set_inj    |- !r. Field r ==> !s. (!p. p IN s ==> poly p) ==>
                                 !q. poly q /\ 0 < deg q ==> INJ (\p. peval p q) s univ(:'a poly)

   Polynomial as Direct GENLIST:
   poly_genlist_nonzero  |- !r f n. GENLIST f (SUC n) <> |0|
   poly_genlist_deg      |- !r f n. deg (GENLIST f (SUC n)) = n
   poly_genlist_lead     |- !r f n. lead (GENLIST f (SUC n)) = f n
   poly_genlist_coeff    |- !r f n k. GENLIST f (SUC n) ' k = if n < k then #0 else f k
   poly_sum_nonzero      |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
                                poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) <> |0|
   poly_sum_gen_coeff      |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
      !k. poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k = if n < k then #0 else f k
   poly_sum_gen_is_genlist |- !r. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
                                 (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) = GENLIST f (SUC n))

   Investigation of Symbolic Polynomial:
   poly_binomial_2_p  |- !r p. Ring r /\ poly p ==> ((p + |1|) ** 2 = p ** 2 + ### 2 * p + |1|)
   poly_binomial_2_X  |- !r. Ring r /\ #1 <> #0 ==> ((X + |1|) ** 2 = X ** 2 + ### 2 * X + |1|)

   Polynomial Dilation:
#  poly_dilate_def      |- !r n p. pdilate n p = DILATE #0 0 n p
   poly_dilate_zero     |- !r n. pdilate n |0| = |0|
   poly_dilate_0        |- !r p. pdilate 0 p = p
   poly_dilate_eq_zero  |- !r p n. (pdilate n p = |0|) <=> (p = |0|)
   poly_dilate_deg      |- !r p n. deg (pdilate n p) =
                                   if n = 0 then deg p else if p = |0| then 0 else SUC n * deg p
   poly_dilate_deg_lower  |- !r p n. deg p <= deg (pdilate n p)
   poly_dilate_deg_upper  |- !r n. 0 < n ==> !p. deg (pdilate n p) <= SUC n * deg p

   poly_dilate_coeff  |- !r p n k. pdilate n p ' k = if k MOD SUC n = 0 then p ' (k DIV SUC n) else #0
   poly_dilate_lead   |- !r p n. lead (pdilate n p) = lead p
   weak_dilate_weak   |- !r. Ring r ==> !p. weak p ==> !n. weak (pdilate n p)
   poly_dilate_poly   |- !r. Ring r ==> !p. poly p ==> !n. poly (pdilate n p)
   poly_dilate_const  |- !r n c. pdilate n [c] = [c]

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Binomial in R[x]                                               *)
(* ------------------------------------------------------------------------- *)

(*
- ring_binomial_2;
> val it =
    |- !r.
         Ring r ==>
         !x y.
           x IN R /\ y IN R ==>
           ((x + y) ** 2 = x ** 2 + ##2 * (x * y) + y ** 2) : thm
- poly_add_mult_ring;
> val it = |- !r. Ring r ==> Ring (PolyRing r) : thm

val pamr = poly_add_mult_ring |> SPEC_ALL |> UNDISCH;
> val pamr =  [.] |- Ring (PolyRing r) : thm
ring_binomial_2 |> ISPEC ``PolyRing r``;
ring_binomial_2 |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr

ring_binomial_2 |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr |> REWRITE_RULE [GSYM poly_ring_property];

ring_binomial_2 |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr |> REWRITE_RULE [GSYM poly_ring_property] |> DISCH_ALL;
> val it =
    |- Ring r ==>
       !x y.
         poly x /\ poly y ==>
         ((PolyRing r).prod.exp (x + y) 2 =
          (PolyRing r).prod.exp x 2 +
          (PolyRing r).sum.exp |1| 2 * (x * y) +
          (PolyRing r).prod.exp y 2) : thm

val poly_binomial_2 = ring_binomial_2 |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr
    |> REWRITE_RULE [GSYM poly_ring_property] |> SPEC ``p:'a poly`` |> SPEC ``q:'a poly`` |> DISCH_ALL;
> val poly_binomial_2 =
    |- Ring r ==>
       poly p /\ poly q ==>
       ((PolyRing r).prod.exp (p + q) 2 =
        (PolyRing r).prod.exp p 2 +
        (PolyRing r).sum.exp |1| 2 * (p * q) +
        (PolyRing r).prod.exp q 2) : thm

val _ = overload_on ("**", ``(PolyRing r).prod.exp``);

poly_binomial_2;
> val it =
    |- Ring r ==>
       poly p /\ poly q ==>
       ((p + q) ** 2 =
        p ** 2 + (PolyRing r).sum.exp |1| 2 * (p * q) + q ** 2) : thm

val _ = overload_on ("##", ``(PolyRing r).sum.exp |1|``);

poly_binomial_2;
> val it =
    |- Ring r ==>
       poly p /\ poly q ==>
       ((p + q) ** 2 = p ** 2 + $## 2 * (p * q) + q ** 2) : thm
*)

val _ = overload_on ("poly_sum", ``ring_sum (PolyRing r)``);

(* Theorem: (p + q) **2 = p ** 2 + ## 2 * p * q + q ** 2 *)
(* Proof: by lifting from ring_binomial_two. *)
val pamr = poly_add_mult_ring |> SPEC_ALL |> UNDISCH;
val poly_binomial_2 = save_thm("poly_binomial_2",
    ring_binomial_2 |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr
    |> REWRITE_RULE [GSYM poly_ring_property] |> SPEC ``p:'a poly`` |> SPEC ``q:'a poly``
    |> DISCH_ALL |> GEN ``q:'a poly`` |> GEN ``p:'a poly`` |> GEN ``r:'a ring``);
(* > val poly_binomial_2 = |- !r p q. Ring r ==> poly p /\ poly q ==>
                                      ((p + q) ** 2 = p ** 2 + ### 2 * (p * q) + q ** 2) : thm *)

(* Theorem: (x + y) ** n = poly_sum (GENLIST (\k. ## (binomial n k) * x ** (n - k) * y ** k) (SUC n)) *)
(* Proof: by lifting from ring_binomial_thm. *)
val poly_binomial_thm = save_thm("poly_binomial_thm",
    ring_binomial_thm |> ISPEC ``PolyRing r`` |> UNDISCH |> PROVE_HYP pamr
    |> REWRITE_RULE [GSYM poly_ring_property] |> SPEC ``x:'a poly`` |> SPEC ``y:'a poly``
    |> DISCH_ALL |> GEN ``y:'a poly`` |> GEN ``x:'a poly`` |> GEN ``r:'a ring``);
(* > val poly_binomial_thm =
    |- !r x y. Ring r ==> poly x /\ poly y ==>
       !n. (x + y) ** n = poly_sum (GENLIST (\k. ### (binomial n k) * x ** (n - k) * y ** k) (SUC n)) : thm *)

(* Theorem: [Freshman's Theorem]
            Ring r /\ prime (char r) ==>
            !x y. poly x /\ poly y ==> ((x + y) ** (char r) = x ** (char r) + y ** (char r)) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
   and   char (PolyRing r) = char r  by poly_ring_char
   The result follows                by ring_freshman_thm,
   Ring r ==> prime (char r) ==> !x y. poly x /\ poly y ==>
   ((x + y) ** char (PolyRing r) = x ** char (PolyRing r) + y ** char (PolyRing r))
*)
val poly_freshman_thm = store_thm(
  "poly_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==> ((x + y) ** (char r) = x ** (char r) + y ** (char r))``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `char (PolyRing r) = char r` by rw_tac std_ss[poly_ring_char] >>
  metis_tac [ring_freshman_thm, poly_ring_element]);

(* Theorem: Ring r /\ prime (char r) ==>
            !x y. poly x /\ poly y ==> ((x - y) ** char r = x ** char r - y ** char r) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
   and  char (PolyRing r) = char r   by poly_ring_char
   The result follows                by ring_freshman_thm_sub,
   Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
   ((x - y) ** char r = x ** char r - y ** char r)
*)
val poly_freshman_thm_sub = store_thm(
  "poly_freshman_thm_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==>
   !x y. poly x /\ poly y ==> ((x - y) ** char r = x ** char r - y ** char r)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `char (PolyRing r) = char r` by rw_tac std_ss[poly_ring_char] >>
  metis_tac [ring_freshman_thm_sub, poly_ring_element, poly_exp_poly, poly_sub_alt]);

(* Theorem: [Freshman's Theorem, power form]
            Ring r /\ prime (char r) ==>
            !n. (x + y) ** (char r ** n) = x ** (char r ** n) + y ** (char r ** n) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
   and  char (PolyRing r) = char r   by poly_ring_char
   The result follows                by ring_freshman_all,
   Ring r ==> prime (char r) ==> !x y. poly x /\ poly y ==>
   !n. (x + y) ** (char (PolyRing r) ** n)
     = x ** (char (PolyRing r) ** n) + y ** (char (PolyRing r) ** n)
*)
val poly_freshman_all = store_thm(
  "poly_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
   !n. (x + y) ** (char r ** n) = x ** (char r ** n) + y ** (char r ** n)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `char (PolyRing r) = char r` by rw_tac std_ss[poly_ring_char] >>
  metis_tac [ring_freshman_all, poly_ring_property]);

(* Theorem: [Freshman's Theorem, power form and subtraction form]
            Ring r /\ prime (char r) ==>
            !n. (x - y) ** (char r ** n) = x ** (char r ** n) - y ** (char r ** n) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
   and  char (PolyRing r) = char r   by poly_ring_char
   The result follows                by ring_freshman_all_sub,
   Ring r ==> prime (char r) ==> !x y. poly x /\ poly y ==>
   !n. (x - y) ** (char (PolyRing r) ** n)
     = x ** (char (PolyRing r) ** n) - y ** (char (PolyRing r) ** n)
*)
val poly_freshman_all_sub = store_thm(
  "poly_freshman_all_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. poly x /\ poly y ==>
   !n. (x - y) ** (char r ** n) = x ** (char r ** n) - y ** (char r ** n)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `char (PolyRing r) = char r` by rw_tac std_ss[poly_ring_char] >>
  metis_tac [ring_freshman_all_sub, poly_ring_element, poly_exp_poly, poly_sub_alt]);

(* Theorem: [Fermat's Little Theorem]
            Ring r /\ prime (char r) ==> !c. |c| ** (char r) = |c| *)
(* Proof:
   Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
   and  char (PolyRing r) = char r   by poly_ring_char
   The result follows                by ring_fermat_thm,
   Ring r /\ prime (char r) ==> !n. ##n ** char r = ##n
*)
val poly_fermat_thm = store_thm(
  "poly_fermat_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !c:num. |c| ** (char r) = |c|``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `char (PolyRing r) = char r` by rw_tac std_ss[poly_ring_char] >>
  metis_tac [ring_fermat_thm]);

(* Theorem: Ring r /\ prime (char r) ==> (X + |c|) ** (char r) = X ** (char r) + |c| *)
(* Proof:
   Let p = char r.
      (X + |c|) ** p
    = X ** p + |c| ** p     by poly_freshman_thm
    = X ** p + |c|          by poly_fermat_thm
*)
val poly_freshman_fermat = store_thm(
  "poly_freshman_fermat",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !c:num. (X + |c|) ** (char r) = X ** (char r) + |c|``,
  rw[poly_freshman_thm, poly_fermat_thm, poly_sum_num_poly]);

(* Theorem: FiniteField r ==> !c:num. (X + |c|) ** (char r) = X ** (char r) + |c| *)
(* Proof:
   Note prime (char r)    by finite_field_char
   The result follows     by poly_freshman_fermat
*)
val poly_freshman_fermat_field = store_thm(
  "poly_freshman_fermat_field",
  ``!r:'a field. FiniteField r ==> !c:num. (X + |c|) ** (char r) = X ** (char r) + |c|``,
  rw_tac std_ss[poly_freshman_fermat, finite_field_char, finite_field_is_field, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Weak Functions and Lists.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define a weak function *)
val weak_fun_def = Define`
    weak_fun (r:'a ring) f <=> !x. weak (f x)
`;

(* Overload on weak_function *)
val _ = overload_on("wfun", ``weak_fun r``);

(* Weak poly list. *)
val poly_weak_list_def = Define`
  (poly_weak_list (r:'a ring) [] <=> T) /\
  (poly_weak_list (r:'a ring) ((h:'a poly)::(t:'a poly list)) <=> weak h /\ (poly_weak_list r t))
`;
val _ = overload_on ("plist", ``poly_weak_list r``);

(* export simple definition. *)
val _ = export_rewrites ["poly_weak_list_def"];

(* Theorem: plist [] = T *)
val poly_weak_list_nil = save_thm("poly_weak_list_nil", poly_weak_list_def |> CONJUNCT1);
(* > val poly_weak_list_nil = |- !r. plist [] <=> T : thm *)

(* Theorem: plist (h::t)= weak h /\ plist t *)
val poly_weak_list_cons = save_thm("poly_weak_list_cons", poly_weak_list_def |> CONJUNCT2);
(* > val poly_weak_list_cons = |- !r h t. plist (h::t) <=> weak h /\ plist t : thm *)

(* Theorem: weak p /\ plist s ==> plist (SNOC p s) *)
(* Proof:
   By induction on s.
   Base case: plist [] ==> plist (SNOC p [])
     True since SNOC p [] = p                   by SNOC
   Step case: plist s ==> plist (SNOC p s) ==> !h. plist (h::s) ==> plist (SNOC p (h::s))
     True since SNOC p (h::s) = h :: SNOC p s   by SNOC and induction hypothesis
*)
val poly_weak_list_SNOC = store_thm(
  "poly_weak_list_SNOC",
  ``!r:'a ring. !p s. weak p /\ plist s ==> plist (SNOC p s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: Ring r ==> !f. wfun f ==> !n. plist (GENLIST f n) *)
(* Proof:
   By induction on n.
   Base: plist (GENLIST f 0)
      Note GENLIST f 0 = []      by GENLIST
       and plist [] = T          by poly_weak_list_nil
   Step: plist (GENLIST f n) ==> plist (GENLIST f (SUC n))
      Note GENLIST f (SUC n)
         = SNOC (f n) (GENLIST f n)          by GENLIST
      Since weak (f n)                       by weak_fun_def
       and plist (GENLIST f n)               by induction hypothesis
        so plist (SNOC (f n) (GENLIST f n))  by poly_weak_list_SNOC
*)
val poly_weak_list_from_weak_fun = store_thm(
  "poly_weak_list_from_weak_fun",
  ``!r:'a ring. Ring r ==> !f. wfun f ==> !n. plist (GENLIST f n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[GENLIST, weak_fun_def, poly_weak_list_SNOC]);

(* ------------------------------------------------------------------------- *)
(* Weak Sum in Polynomial Ring.                                              *)
(* ------------------------------------------------------------------------- *)

(* Weak poly sum. *)
val poly_weak_sum_def = Define`
  (poly_weak_sum (r:'a ring) [] = |0|) /\
  (poly_weak_sum (r:'a ring) ((h:'a poly)::(t:'a poly list)) = h || (poly_weak_sum r t))
`;
val _ = overload_on ("psum", ``poly_weak_sum r``);

(* export simple definition. *)
val _ = export_rewrites ["poly_weak_sum_def"];

(* Theorem: psum [] = |0| *)
val poly_weak_sum_nil = save_thm("poly_weak_sum_nil", poly_weak_sum_def |> CONJUNCT1);
(* > val poly_weak_sum_nil = |- !r. psum [] = |0| : thm *)

(* Theorem: psum (h::t) = h || psum t *)
val poly_weak_sum_cons = save_thm("poly_weak_sum_cons", poly_weak_sum_def |> CONJUNCT2);
(* > val poly_weak_sum_cons = |- !r h t. psum (h::t) = h || psum t : thm *)

(* Theorem: plist s ==> weak (psum s) *)
(* Proof:
   By induction on s.
   Base case: plist [] ==> weak (psum [])
      true by poly_weak_sum_nil, weak_zero.
   Step case: plist s ==> weak (psum s) ==> !h. plist (h::s) ==> weak (psum (h::s))
      plist (h::s) ==> weak h /\ plist s    by poly_weak_list_cons
      since  psum (h::s) = h || psum s      by poly_weak_sum_cons
      with weak h and plist s ==> weak (psum s)  by induction hypothesis
      true by weak_add_weak
*)
val poly_weak_sum_weak = store_thm(
  "poly_weak_sum_weak",
  ``!r:'a ring. Ring r ==> !s. plist s ==> weak (psum s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

val _ = export_rewrites ["poly_weak_sum_weak"];

(* Theorem: psum [p] = p *)
(* Proof:
     psum [p]
   = p || psum []    by poly_weak_sum_cons
   = p || |0|        by poly_weak_sum_nil
   = p               by weak_add_rzero
*)
val poly_weak_sum_sing = store_thm(
  "poly_weak_sum_sing",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (psum [p] = p)``,
  rw[]);

(* Theorem: plist s ==> psum (SNOC p s) = (psum s) || p *)
(* Proof:
   By induction on s.
   Base case: plist [] ==> (psum (SNOC p []) = psum [] || p)
      psum (SNOC p [])
    = psum [p]            by SNOC
    = p || |0|            by poly_weak_sum_cons, poly_weak_sum_nil
    = p                   by weak_add_rzero
    = |0| || p            by weak_add_lzero
    = psum [] || p        by poly_weak_sum_nil
   Step case: plist s ==> (psum (SNOC p s) = psum s || p) ==>
              !h. plist (h::s) ==> (psum (SNOC p (h::s)) = psum (h::s) || p)
     psum (SNOC p (h::s))
   = psum (h::SNOC p s)   by SNOC
   = h || psum (SNOC p s) by poly_weak_sum_def
   = h || (psum s || p)   by induction hypothesis
   = (h || psum s) || p   by weak_add_assoc, poly_weak_sum_weak
   = psum(h::s) || p      by poly_weak_sum_def
*)
val poly_weak_sum_SNOC = store_thm(
  "poly_weak_sum_SNOC",
  ``!r:'a ring. Ring r ==> !p s. weak p /\ plist s ==> (psum (SNOC p s) = (psum s) || p)``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw_tac std_ss[SNOC, poly_weak_list_cons] >>
  `psum (h::SNOC p s) = h || psum (SNOC p s)` by rw[] >>
  `_ = h || ((psum s) || p)` by rw_tac std_ss[] >>
  `_ = psum(h::s) || p` by rw[weak_add_assoc] >>
  rw_tac std_ss[]);

(* Theorem: Ring r ==> !f. wfun f ==> !n. (f n) || psum (GENLIST f n) = psum (GENLIST f (SUC n)) *)
(* Proof:
   Note plist (GENLIST f n)             by poly_weak_list_from_weak_fun
    and weak (psum (GENLIST f n))       by poly_weak_sum_weak
    and weak (f n)                      by weak_fun_def

      (f n) || psum (GENLIST f n)
    = psum (GENLIST f n) || (f n)       by weak_add_comm
    = psum (SNOC (f n) (GENLIST f n))   by poly_weak_sum_SNOC
    = psum (GENLIST f (SUC n))          by GENLIST
*)
val poly_weak_sum_genlist_suc = store_thm(
  "poly_weak_sum_genlist_suc",
  ``!r:'a ring. Ring r ==> !f. wfun f ==> !n. (f n) || psum (GENLIST f n) = psum (GENLIST f (SUC n))``,
  rpt strip_tac >>
  `plist (GENLIST f n)` by rw[poly_weak_list_from_weak_fun] >>
  `weak (psum (GENLIST f n))` by rw[poly_weak_sum_weak] >>
  `weak (f n)` by metis_tac[weak_fun_def] >>
  metis_tac[weak_add_comm, poly_weak_sum_SNOC, GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Functions and Lists.                                           *)
(* ------------------------------------------------------------------------- *)

(* Overload for a polynomial output function *)
val _ = overload_on ("poly_fun", ``ring_fun (PolyRing r)``);

(* overload on polynomial list *)
val _ = overload_on ("poly_list", ``ring_list (PolyRing r)``);

(* Theorem: poly_fun f <=> !x. poly (f x) *)
(* Proof: by ring_fun_def, poly_ring_element *)
val poly_fun_def = store_thm(
  "poly_fun_def",
  ``!(r:'a ring) f. poly_fun f <=> !x. poly (f x)``,
  rw[ring_fun_def, poly_ring_element]);

(* Theorem: poly_fun f ==> !x. poly (f x) *)
(* Proof: by ring_fun_def, poly_ring_element *)
val poly_list_element = store_thm(
  "poly_list_element",
  ``!r:'a ring. !f. poly_fun f ==> !x. poly (f x)``,
  rw_tac std_ss[ring_fun_def, poly_ring_element]);

(* export simple result *)
val _ = export_rewrites ["poly_list_element"];

(* val poly_list_nil = lift_ring_thm "list_nil" "list_nil"; *)

(* Theorem: poly_list [] *)
(* Proof: by poly_add_mult_ring, ring_list_nil *)
val poly_list_nil = store_thm(
  "poly_list_nil",
  ``!r:'a ring. Ring r ==> poly_list []``,
  metis_tac [ring_list_nil, poly_add_mult_ring, poly_ring_property]);

val _ = export_rewrites ["poly_list_nil"];

(* val poly_list_cons = lift_ring_thm "list_cons" "list_cons"; *)

(* Theorem: poly_list (p::s) <=> poly p /\ poly_list s *)
(* Proof: by poly_add_mult_ring, ring_list_cons *)
val poly_list_cons = store_thm(
  "poly_list_cons",
  ``!r:'a ring. Ring r ==> !p s. poly_list (p::s) <=> poly p /\ poly_list s``,
  metis_tac [ring_list_cons, poly_add_mult_ring, poly_ring_property]);

val _ = export_rewrites ["poly_list_cons"];

(* Theorem: poly_list (SNOC p s) <=> poly p /\ poly_list s *)
(* Proof:
   By induction on s.
   Base case: poly_list (SNOC p []) <=> poly p /\ poly_list []
     LHS = poly_list (SNOC p [])
         = poly_list [p]                     by SNOC
         = poly p /\ poly_list []            by poly_list_cons
         = RHS
   Step case: poly_list (SNOC p s) <=> poly p /\ poly_list s ==>
              !h. poly_list (SNOC p (h::s)) <=> poly p /\ poly_list (h::s)
     LHS = poly_list (SNOC p (h::s))
         = poly_list (h:: SNOC p s)          by SNOC
         = poly h /\ poly_list (SNOC p s)    by poly_list_cons
         = poly h /\ poly p /\ poly_list s   by induction hypothesis
     RHS = poly p /\ poly_list (h::s)
         = poly p /\ poly h /\ poly_list s   by poly_list_cons
         = LHS
*)
val poly_list_SNOC = store_thm(
  "poly_list_SNOC",
  ``!r:'a ring. Ring r ==> !p s. poly_list (SNOC p s) <=> poly p /\ poly_list s``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[] >>
  metis_tac[]);

(* Theorem: poly_fun f /\ poly_list s ==> poly_list (MAP f s) *)
(* Proof:
   By induction on s.
   Base: poly_list [] ==> poly_list (MAP f [])
      True by MAP f [] = []         by MAP
   Step: poly_list s ==> poly_list (MAP f s) ==>
         !h. poly_list (h::s) ==> poly_list (MAP f (h::s))
      Note poly h /\ poly_list s               by poly_list_cons
       and MAP f (h::s) = (f h) :: (MAP f s)   by MAP
       Now poly (f h)                          by poly_fun f
       and poly (MAP f s)                      by induction hypothesis
      Thus poly_list ((f h) :: (MAP f s))      by poly_list_cons
*)
val poly_list_from_poly_fun = store_thm(
  "poly_list_from_poly_fun",
  ``!f s. poly_fun f /\ poly_list s ==> poly_list (MAP f s)``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  fs[poly_ring_property, ring_fun_def]);

(* Theorem: Ring r ==> !z. ulead z ==> !x. poly_list s ==> poly_list (MAP (\x. x % z) s) *)
(* Proof:
   By induction on s.
   Base: poly_list [] ==> poly_list (MAP (\x. x % z) [])
      True by MAP f [] = []             by MAP
   Step: poly_list s ==> poly_list (MAP (\x. x % z) s) ==>
         !h. poly_list (h::s) ==> poly_list (MAP (\x. x % z) (h::s))
      Note poly h /\ poly_list s        by poly_list_cons
       and MAP (\x. x % z) (h::s)
         = h % z :: MAP (\x. x % z) s   by MAP
       Now poly (h % z)                 by poly_mod_poly, ulead z
       and poly (MAP (\x. x % z) s)     by induction hypothesis
      Thus poly_list (h % z :: MAP (\x. x % z) s)  by poly_list_cons
*)
val poly_list_from_poly_mod = store_thm(
  "poly_list_from_poly_mod",
  ``!r:'a ring. Ring r ==> !z. ulead z ==> !s. poly_list s ==> poly_list (MAP (\x. x % z) s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: rfun f ==> !p. poly p ==> poly_fun (\j. f j * p ** j) *)
(* Proof:
   Since rfun f, !x. f x IN R          by ring_fun_def
      so !j. poly (f j * p ** j)       by poly_X, poly_exp_poly, poly_cmult_poly
    Thus poly_fun (\j. f j * p ** j)   by ring_fun_def, poly_ring_element
*)
val poly_fun_from_ring_fun = store_thm(
  "poly_fun_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==>
   !p. poly p ==> poly_fun (\j. f j * p ** j)``,
  rw[poly_ring_element]);

(* Theorem: rfun f ==> !p. poly p ==> !n. poly_fun (\j. (f j * p ** j) ** n) *)
(* Proof: by ring_fun_def, poly_cmult_poly, poly_exp_poly, poly_ring_property. *)
val poly_fun_from_ring_fun_exp = store_thm(
  "poly_fun_from_ring_fun_exp",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !p. poly p ==> !n. poly_fun (\j. (f j * p ** j) ** n)``,
  rw[GSYM poly_ring_property]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Sum.                                                           *)
(* ------------------------------------------------------------------------- *)

(*  poly_sum = ring_sum (PolyRing r) *)
(*  ring_sum_def      |- (!r. rsum [] = #0) /\ !r h t. rsum (h::t) = h + rsum t *)
(* val _ = overload_on ("rsum", ``ring_sum r``); *)

(* val _ = overload_on ("poly_sum", ``ring_sum (PolyRing r)``); *)
(* Note: this is defined at the beginning. *)

(* val poly_sum_nil = lift_ring_thm "sum_nil" "sum_nil"; *)

(* Theorem: poly_sum [] = |0| *)
(* Proof: by poly_add_mult_ring, ring_sum_nil *)
val poly_sum_nil = store_thm(
  "poly_sum_nil",
  ``!r:'a ring. Ring r ==> (poly_sum [] = |0|)``,
  metis_tac [ring_sum_nil, poly_add_mult_ring, poly_ring_property]);

val _ = export_rewrites ["poly_sum_nil"];

(* val poly_sum_cons = lift_ring_thm "sum_cons" "sum_cons"; *)

(* Theorem: poly_sum (p::s) = p + poly_sum s *)
(* Proof: by poly_add_mult_ring, ring_sum_cons *)
val poly_sum_cons = store_thm(
  "poly_sum_cons",
  ``!r:'a ring. Ring r ==> !p s. poly p /\ poly_list s ==> (poly_sum (p::s) = p + poly_sum s)``,
  metis_tac [ring_sum_cons, poly_add_mult_ring, poly_ring_property]);

val _ = export_rewrites ["poly_sum_cons"];

(* Theorem: poly_list s ==> poly (poly_sum s) *)
(* Proof:
   By induction on s.
   Base case: poly_list [] ==> poly (poly_sum [])
     Since poly_sum [] = |0|       by poly_sum_nil
     Hence true since poly |0|     by poly_zero_poly
   Step case: poly_list s ==> poly (poly_sum s) ==>
              !h. poly_list (h::s) ==> poly (poly_sum (h::s))
     Since poly_list (h::s)
       ==> poly h /\ poly_list s   by poly_list_cons
       and poly_sum (h::s)
         = h + poly_sum s          by poly_sum_cons
      with poly h                  by above
       and poly (poly_sum s)       by induction hypothesis
     Hence poly (poly_sum (h::s))  by poly_add_poly
*)
val poly_sum_poly = store_thm(
  "poly_sum_poly",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==> poly (poly_sum s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_sum_poly"];

(* val poly_sum_SNOC = lift_ring_thm "sum_SNOC" "sum_SNOC"; *)

(* ring_sum_SNOC |> ISPEC ``(PolyRing r)`` |> REWRITE_RULE [poly_ring_property] |> UNDISCH |> PROVE_HYP pamr |> DISCH_ALL |> GEN_ALL
*)
(* Theorem: poly_sum (SNOC p s) = (poly_sum s) + p *)
(* Proof: by poly_add_mult_ring, ring_sum_SNOC *)
val poly_sum_SNOC = store_thm(
  "poly_sum_SNOC",
  ``!r:'a ring. Ring r ==> !p s. poly p /\ poly_list s ==> (poly_sum (SNOC p s) = (poly_sum s) + p)``,
  metis_tac [ring_sum_SNOC, poly_add_mult_ring, poly_ring_property]);

(* Theorem: poly p ==> (poly_sum [p] = p) *)
(* Proof:
      poly_sum [p]
   = p + poly_sum []     by poly_sum_cons
   = p + |0|             by poly_sum_nil
   = p                   by poly_add_rzero
*)
val poly_sum_const = store_thm(
  "poly_sum_const",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (poly_sum [p] = p)``,
  rw[]);

(* Theorem: Ring r ==> !s. poly_list s ==>
            !c. c IN R ==> (c * (poly_sum s) = poly_sum (MAP (\x. c * x) s)) *)
(* Proof:
   By induction on s.
   Base: poly_list [] ==> (c * poly_sum [] = poly_sum (MAP (\x. c * x) []))
         c * poly_sum []
       = c * |0|                        by poly_sum_nil
       = |0|                            by poly_cmult_zero
       = poly_sum []                    by poly_sum_nil
       = poly_sum (MAP (\x. c * x) []   by MAP
   Step: poly_list s ==> (c * poly_sum s = poly_sum (MAP (\x. c * x) s)) ==>
         !h. poly_list (h::s) ==> (c * poly_sum (h::s) = poly_sum (MAP (\x. c * x) (h::s)))
       Note poly h /\ poly_list s       by poly_list_cons
        and poly (poly_sum s)           by poly_sum_poly
         c * poly_sum (h::s)
       = c * (h + poly_sum s)                   by poly_sum_cons
       = c * h + c * (poly_sum s)               by poly_cmult_add
       = c * h + poly_sum (MAP (\x. c * x) s)   by induction hypothesis
       = poly_sum (MAP (\x. c * x) (h::s))      by poly_sum_cons
*)
val poly_cmult_poly_sum = store_thm(
  "poly_cmult_poly_sum",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !c. c IN R ==> (c * (poly_sum s) = poly_sum (MAP (\x. c * x) s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[poly_cmult_of_zero] >>
  rw[poly_cmult_add]);

(* Theorem: Ring r ==> !s. poly_list s ==>
            !p. poly p ==> (p * (poly_sum s) = poly_sum (MAP (\x. p * x) s)) *)
(* Proof:
   By induction on s.
   Base: poly_list [] ==> (p * poly_sum [] = poly_sum (MAP (\x. p * x) []))
         p * poly_sum []
       = p * |0|                        by poly_sum_nil
       = |0|                            by poly_mult_zero
       = poly_sum []                    by poly_sum_nil
       = poly_sum (MAP (\x. p * x) []   by MAP
   Step: poly_list s ==> (p * poly_sum s = poly_sum (MAP (\x. p * x) s)) ==>
         !h. poly_list (h::s) ==> (p * poly_sum (h::s) = poly_sum (MAP (\x. p * x) (h::s)))
       Note poly h /\ poly_list s       by poly_list_cons
        and poly (poly_sum s)           by poly_sum_poly
         p * poly_sum (h::s)
       = p * (h + poly_sum s)                   by poly_sum_cons
       = p * h + p * (poly_sum s)               by poly_mult_radd
       = p * h + poly_sum (MAP (\x. p * x) s)   by induction hypothesis
       = poly_sum (MAP (\x. p * x) (h::s))      by poly_sum_cons
*)
val poly_mult_poly_sum = store_thm(
  "poly_mult_poly_sum",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !p. poly p ==> (p * (poly_sum s) = poly_sum (MAP (\x. p * x) s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[poly_mult_of_zero] >>
  rw[]);

(* Theorem: Ring r ==> !s. poly_list s ==>
            !z. ulead z ==> ((poly_sum s) % z = (poly_sum (MAP (\x. x % z) s)) % z) *)
(* Proof:
   By induction on s.
   Base: poly_list [] ==> (poly_sum [] % z = poly_sum (MAP (\x. x % z) []) % z)
         poly_sum [] % z
       = |0| % z                              by poly_sum_nil
       = (poly_sum []) % z                    by poly_sum_nil
       = (poly_sum (MAP (\x. x % z) []) % z   by MAP
   Step: poly_list s ==> (poly_sum s % z = poly_sum (MAP (\x. x % z) s) % z) ==>
         !h. poly_list (h::s) ==> (poly_sum (h::s) % z = poly_sum (MAP (\x. x % z) (h::s)) % z)
       Note poly h /\ poly_list s                 by poly_list_cons
        and poly (poly_sum s)                     by poly_sum_poly
       Also poly_list (MAP (\x. x % z) s)         by poly_list_from_poly_mod
        ==> poly (poly_sum (MAP (\x. x % z) s))   by poly_sum_poly
         poly_sum (h::s) % z
       = (h + poly_sum s) % z                     by poly_sum_cons
       = (h % z + (poly_sum s) % z) % z           by poly_mod_add
       = (h % z + poly_sum (MAP (\x. x % z) s) % z) % z         by induction hypothesis
       = ((h % z) % z + poly_sum (MAP (\x. x % z) s) % z) % z   by poly_mod_mod
       = (h % z + poly_sum (MAP (\x. x % z) s)) % z             by poly_mod_add
       = (poly_sum (MAP (\x. x % z) (h::s))) % z                by poly_sum_cons
*)
val poly_mod_poly_sum = store_thm(
  "poly_mod_poly_sum",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !z. ulead z ==> ((poly_sum s) % z = (poly_sum (MAP (\x. x % z) s)) % z)``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[] >>
  `poly (poly_sum s)` by rw[poly_sum_poly] >>
  `poly_list (MAP (\x. x % z) s)` by rw[poly_list_from_poly_mod] >>
  `poly (poly_sum (MAP (\x. x % z) s))` by rw[poly_sum_poly] >>
  `(h + poly_sum s) % z = (h % z + (poly_sum s) % z) % z` by rw_tac std_ss[poly_mod_add] >>
  `_ = (h % z + poly_sum (MAP (\x. x % z) s) % z) % z` by rw[] >>
  `_ = ((h % z) % z + poly_sum (MAP (\x. x % z) s) % z) % z` by rw[poly_mod_mod] >>
  `_ = (h % z + poly_sum (MAP (\x. x % z) s)) % z` by rw[GSYM poly_mod_add] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Sum over GENLIST in Polynomial Ring.                                      *)
(* ------------------------------------------------------------------------- *)

(* GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) -- by definition of GENLIST. *)

(* Theorem: !f. rfun f ==> !n. weak (GENLIST f n) *)
(* Proof:
   By induction on n.
   Base: weak (GENLIST f 0)
      Since GENLIST f 0 = []           by GENLIST_0
        and weak []                    by weak_of_zero
   Step: weak (GENLIST f n) ==> weak (GENLIST f (SUC n))
      Since f n IN R                   by ring_fun_def
        and GENLIST f (SUC n)
          = SNOC (f n) (GENLIST f n)   by GENLIST
      Hence weak (GENLIST f (SUC n))   by weak_snoc
*)
val weak_genlist = store_thm(
  "weak_genlist",
  ``!r:'a ring. !f. rfun f ==> !n. weak (GENLIST f n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `f n IN R` by metis_tac[ring_fun_def] >>
  rw[weak_snoc, GENLIST]);

(* Theorem: !f. rfun f ==> !n. f n <> #0 ==> poly (GENLIST f (SUC n)) *)
(* Proof:
   Since weak (GENLIST f (SUC n))         by weak_genlist
     and LAST (GENLIST f (SUC n)) = f n   by GENLIST_LAST
   Hence poly (GENLIST f (SUC n))         by poly_def_alt, f n <> #0
*)
val poly_genlist = store_thm(
  "poly_genlist",
  ``!r:'a ring. !f. rfun f ==> !n. f n <> #0 ==> poly (GENLIST f (SUC n))``,
  rw[poly_def_alt, weak_genlist, GENLIST_LAST]);

(* Theorem: !n. plist (GENLIST (\k. (f k) o (X ** k)) n) *)
(* Proof: by induction on n.
   Base case: plist (GENLIST (\k. f k o (X ** k)) 0)
     Since GENLIST (\k. f k o (X ** k)) 0 = []   by GENLIST, for any function
     hence true by poly_weak_list_nil.
   Step case: plist (GENLIST (\k. f k o (X ** k)) n) ==> plist (GENLIST (\k. f k o (X ** k)) (SUC n))
       GENLIST (\k. f k o (X ** k)) (SUC n)
     = SNOC ((f n) o X ** n) GENLIST (\k. f k o (X ** k)) n   by GENLIST
     Since (f n) IN R              by ring_fun_def
     and poly (X ** n)             by poly_X, poly_exp_poly
     giving weak (f n) o (X ** n)  by weak_cmult_weak
     thus true by poly_weak_list_SNOC.
*)
val poly_weak_list_genlist = store_thm(
  "poly_weak_list_genlist",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !n. plist (GENLIST (\k. (f k) o (X ** k)) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f n IN R` by metis_tac [ring_fun_def] >>
  `poly (X ** n)` by rw[] >>
  `weak ((f n) o (X ** n))` by rw[] >>
  rw[GENLIST, poly_weak_list_SNOC]);

(* Theorem: #1 <> #0 ==> deg (psum (GENLIST (\k. (f k) * (X ** k)) (SUC n))) = n *)
(* Proof: by induction on n.
   Base case: deg (psum (GENLIST (\k. f k o (X ** k)) (SUC 0))) = 0
       deg (psum (GENLIST (\k. f k o (X ** k)) (SUC 0)))
     = deg (psum (GENLIST (\k. f k o (X ** k)) 1))
     = deg (psum [(f 0) o (X ** 0)])
     = deg (psum [(f 0) o |1|])         by poly_exp_0
     = deg (psum [f 0])                 by weak_cmult_one, poly_one
     = deg [f 0]                        by poly_weak_sum_sing
     = 0                                by poly_deg_const
   Step case: deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n))) = n ==>
              deg (psum (GENLIST (\k. f k o (X ** k)) (SUC (SUC n)))) = SUC n
       deg (psum (GENLIST (\k. f k o (X ** k)) (SUC (SUC n))))
     = deg (psum (SNOC ((f (SUC n)) o (X ** (SUC n))) (GENLIST (\k. f k o (X ** k)) (SUC n))))     by GENLIST
     = deg deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n)) || f (SUC n) o (X ** (SUC n)))         by poly_weak_sum_SNOC
     = MAX (deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n)))) (deg (f (SUC n) o (X ** (SUC n))))  by poly_deg_weak_add
     = MAX n (SUC n)                    by induction hypothesis, poly_monic_deg_exp
     = SUC n                            by MAX_DEF
*)
val poly_deg_weak_sum_genlist = store_thm(
  "poly_deg_weak_sum_genlist",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f ==>
      (deg (psum (GENLIST (\k. (f k) o (X ** k)) (SUC n))) = n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac [ring_fun_def] >>
  `!n. plist (GENLIST (\k. f k o (X ** k)) n)` by rw[poly_weak_list_genlist] >>
  Induct_on `n` >-
  rw[weak_deg_cmult] >>
  `weak (f (SUC n) o (X ** (SUC n)))` by rw[] >>
  `poly X` by rw[] >>
  `!n. deg (X ** n) = n` by rw[poly_monic_X, poly_monic_deg_exp] >>
  `!n. deg ((f n) o (X ** n)) = n` by rw[weak_deg_cmult] >>
  `deg (psum (GENLIST (\k. f k o (X ** k)) (SUC (SUC n)))) =
    deg (psum (SNOC ((f (SUC n)) o (X ** (SUC n))) (GENLIST (\k. f k o (X ** k)) (SUC n))))` by rw_tac std_ss[GENLIST] >>
  `_ = deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n)) || f (SUC n) o (X ** (SUC n)))` by rw[poly_weak_sum_SNOC] >>
  `_ = MAX (deg (psum (GENLIST (\k. f k o (X ** k)) (SUC n)))) (deg (f (SUC n) o (X ** (SUC n))))` by rw[poly_deg_weak_add] >>
  `_ = MAX n (SUC n)` by rw[] >>
  `_ = SUC n` by rw[MAX_DEF, DECIDE ``n < SUC n``] >>
  rw[]);

(*
   Given a plist s --- every element is weak,
     poly_list (MAP chop s) -- every element is poly.
     poly_sum (MAP chop s)
   = (chop s1) + (chop s2) + ... + (chop sn)
   = chop ((chop s1) || (chop s2) || ... || (chop sn))  by generalized poly_add_def
   = chop (s1 || s2 || ... || sn)                       by generalized poly_chop_add_chop
   = chop (psum s)

*)

(* Theorem: plist s ==> poly_list (MAP chop s) *)
(* Proof: by induction on s.
   Base case: plist [] ==> poly_list (MAP chop [])
     True by MAP, poly_list_nil.
   Step case: plist s ==> poly_list (MAP chop s) ==>
              !h. plist (h::s) ==> poly_list (MAP chop (h::s))
     plist (h::s) ==> weak h /\ plist s     by poly_weak_list_cons
     MAP chop (h::s) = chop h :: MAP chop s
     weak h => poly (chop h)       by poly_chop_weak_poly
     poly_list (MAP chop s)        by induction hypothesis
     hence true by poly_list_cons.
*)
val poly_list_by_weak_list = store_thm(
  "poly_list_by_weak_list",
  ``!r:'a ring. Ring r ==> !s. plist s ==> poly_list (MAP chop s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: poly_sum (MAP chop s) = chop (psum s) *)
(* Proof: by induction on s.
   Base case: plist [] ==> (poly_sum (MAP chop []) = chop (psum []))
     LHS = poly_sum (MAP chop [])
         = poly_sum []          by MAP
         = |0|                  by poly_sum_nil
     RHS = chop (psum [])
         = chop |0|             by poly_weak_sum_nil
         = |0| = LHS            by poly_chop_zero
   Step case: plist s ==> (poly_sum (MAP chop s) = chop (psum s)) ==>
        !h. plist (h::s) ==> (poly_sum (MAP chop (h::s)) = chop (psum (h::s)))
       plist (h::s) ==> weak h /\ plist s  by poly_weak_list_cons
       plist s ==> poly_list (MAP chop s)  by poly_list_by_weak_list
       weak h ==> poly (chop h)            by poly_chop_weak_poly
       weak (psum s)                       by poly_weak_sum_weak
       poly_sum (MAP chop (h::s))
     = poly_sum (chop h :: MAP chop s)     by MAP
     = (chop h) + poly_sum (MAP chop s)    by poly_sum_cons
     = (chop h) + chop (psum s)            by induction hypothesis
     = chop ((chop h) || (chop (psum s)))  by poly_add_def
     = chop (h || (psum s))                by poly_chop_add_chop
     = chop (psum (h::s))                  by poly_weak_sum_cons
*)
val poly_sum_by_weak_sum = store_thm(
  "poly_sum_by_weak_sum",
  ``!r:'a ring. Ring r ==> !s. plist s ==> (poly_sum (MAP chop s) = chop (psum s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw_tac std_ss[poly_weak_list_cons, MAP] >>
  `poly_list (MAP chop s)` by rw[poly_list_by_weak_list] >>
  `poly (chop h)` by rw[poly_chop_weak_poly] >>
  rw_tac std_ss[poly_sum_cons] >>
  `weak (psum s)` by rw[] >>
  rw_tac std_ss[poly_add_def, poly_chop_add_chop, poly_weak_sum_cons]);

(* Theorem: Ring r ==> !s. plist s ==> (chop (psum s) = poly_sum (MAP chop s)) *)
(* Proof: reformulation of poly_sum_by_weak_sum *)
val poly_chop_weak_sum = store_thm(
  "poly_chop_weak_sum",
  ``!r:'a ring. Ring r ==> !s. plist s ==> (chop (psum s) = poly_sum (MAP chop s))``,
  rw[poly_sum_by_weak_sum]);

(* Theorem: rfun f ==> ((\k. chop ((f k) o (X ** k))) = chop o (\k. (f k) o (X ** k))) *)
(* Proof: by equal functions *)
val poly_chop_with_function = store_thm(
  "poly_chop_with_function",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> ((\k. chop ((f k) o (X ** k))) = chop o (\k. (f k) o (X ** k)))``,
  rw_tac std_ss[FUN_EQ_THM]);
(* should just prove on the fly *)

(* Theorem: rfun f ==> ((\j. (f j) * (X ** j)) = (\j. chop (f j o (X ** j))))*)
(* Proof: by poly_cmult_def. *)
val poly_cmult_in_function = store_thm(
  "poly_cmult_in_function",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> ((\j. (f j) * (X ** j)) = (\j. chop (f j o (X ** j))))``,
  rw_tac std_ss[poly_cmult_def]);

(* Theorem: From poly_sum to psum involing GENLIST and cmult: #1 <> #0 ==>
            !n. poly_sum (GENLIST (\j. f j * X ** j) n) = chop (psum (GENLIST (\j. (f j) o (X ** j)) n)) *)
(* Proof:
   Since #1 <> #0, |1| <> |0|   by poly_zero_eq_one
   hence |1| = [#1], and [#1] <> |0|.
   Since   weak ((\j. f j o (X ** j)) n)                   by weak_cmult_weak
   hence   plist (GENLIST (\j. (f j) o (X ** j)) n)        by poly_weak_list_genlist
   and     weak (psum (GENLIST (\j. (f j) o (X ** j)) n))  by poly_weak_sum_weak
   Therefore:
     poly_sum (GENLIST (\j. f j * X ** j) n)
   = poly_sum (GENLIST (\j. chop (f j o (X ** j))) n)      by poly_cmult_def
   = poly_sum (GENLIST (chop o (\j. f j o (X ** j))) n)    by equal functions
   = poly_sum (MAP chop (GENLIST (\j. f j o (X ** j)) n))  by MAP_GENLIST
   = chop (psum (GENLIST (\j. f j o (X ** j)) n))          by poly_sum_by_weak_sum
*)
val poly_sum_by_weak_sum_genlist = store_thm(
  "poly_sum_by_weak_sum_genlist",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f. rfun f ==>
   !n. poly_sum (GENLIST (\j. f j * X ** j) n) = chop (psum (GENLIST (\j. (f j) o (X ** j)) n))``,
  rpt strip_tac >>
  `!j. f j IN R` by metis_tac [ring_fun_def] >>
  `|1| <> |0| /\ ( |1| = [#1])` by metis_tac [poly_zero_eq_one, poly_one] >>
  `[#1] <> |0|` by rw[] >>
  `weak ((\j. f j o (X ** j)) n)` by rw[] >>
  `plist (GENLIST (\j. (f j) o (X ** j)) n)` by rw[poly_weak_list_genlist] >>
  `weak (psum (GENLIST (\j. (f j) o (X ** j)) n))` by rw[poly_weak_sum_weak] >>
  `poly_sum (GENLIST (\j. f j * X ** j) n) =
    poly_sum (GENLIST (\j. chop (f j o (X ** j))) n)` by rw_tac std_ss[poly_cmult_def] >>
  `_ = poly_sum (GENLIST (chop o (\j. (f j) o (X ** j))) n)` by rw[poly_chop_with_function] >>
  `_ = poly_sum (MAP chop (GENLIST (\j. (f j) o (X ** j)) n))` by rw[MAP_GENLIST] >>
  rw[poly_sum_by_weak_sum]);

(* Theorem: #1 <> #0 ==> poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k = f k  *)
(* Proof: by induction on n.
   Base case: k < SUC 0 ==> (poly_sum (GENLIST (\j. f j * X ** j) (SUC 0)) ' k = f k)
     This is to show: k < 1 ==> (f 0 * [#1]) ' k = f k
     k < 1 ==> k = 0.
       f 0 * [#1]
     = chop (f 0 o [#1])     by poly_cmult_def
     = chop [f 0 * #1]       by weak_cmult_const
     = chop [f 0]            by ring_mult_rone
     If f 0 = #0, chop [#0] = |0|   by poly_chop_const_zero
     and |0| ' 0 = #0 = f 0         by poly_coeff_zero, poly_zero
     If f 0 <> #0, chop [f 0] = f 0 by poly_chop_const_nonzero
   Step case: k < SUC n ==> (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k = f k)
     ==> k < SUC (SUC n) ==> (poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n))) ' k = f k)

     weak ((\j. f j o (X ** j)) (SUC (SUC n)))                   by weak_cmult_weak
     plist (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n)))        by poly_weak_list_genlist
     weak (psum (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n))))  by poly_weak_sum_weak

       poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n))) ' k
     = chop (psum (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n)))) ' k          by poly_sum_by_weak_sum_genlist
     = psum (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n))) ' k                 by poly_coeff_chop
     = psum (SNOC ((\j. f j o (X ** j)) (SUC n)) (GENLIST (\j. f j o (X ** j)) (SUC n))) ' k    by GENLIST
     = ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || ((\j. f j o (X ** j)) (SUC n))) ' k    by poly_weak_sum_SNOC
     = ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || (f (SUC n) o (X ** (SUC n)))) ' k      by function application

     Now,
     deg (psum (GENLIST (\j. f j o (X ** j)) (SUC n))) = n   by poly_deg_weak_sum_genlist
     Need k < SUC n to apply poly_coeff_weak_add_cmult_X_exp.

     Furthermore,
     deg (f (SUC n) o (X ** (SUC n))) = deg (X ** (SUC n))   by weak_deg_cmult
                                      = SUC n                by poly_monic_X, poly_monic_deg_exp
     hence deg ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || (f (SUC n) o (X ** (SUC n))))
         = MAX deg (psum (GENLIST (\j. f j o (X ** j)) (SUC n))) deg (f (SUC n) o (X ** (SUC n))  by poly_deg_weak_add
         = MAX n (SUC n)
         = SUC n

     If k = SUC n, this is the lead    by poly_coeff_lead
     Since
       lead ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || (f (SUC n) o (X ** (SUC n))))
     = lead (f (SUC n) o (X ** (SUC n)))               by weak_lead_weak_add
     = f (SUC n) * lead (X ** (SUC n))                 by weak_lead_cmult
     = f (SUC n) * #1                                  by poly_monic_lead
     = f (SUC n)                                       by ring_mult_rone
     This is true by poly_coeff_lead: !p. p ' (deg p) = lead p.

     If k <> SUC n,
     k < SUC (SUC n) ==> k <= SUC n, hence k < SUC n.

       (psum (GENLIST (\j. f j o (X ** j)) (SUC n)) || f (SUC n) o (X ** SUC n)) ' k
     = psum (GENLIST (\j. f j o (X ** j)) (SUC n)) ' k          by poly_coeff_weak_add_cmult_X_exp
     = chop (psum (GENLIST (\j. f j o (X ** j)) (SUC n))) ' k   by poly_coeff_chop]);
     = poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k        by poly_sum_by_weak_sum_genlist
     = f k                                                      by induction hypothesis
*)
Theorem poly_coeff_sum_genlist:
  !r:'a ring.
    Ring r /\ #1 <> #0 ==>
    !f n k. rfun f /\ k < SUC n ==>
            ((poly_sum (GENLIST (\j. (f j) * (X ** j)) (SUC n))) ' k = f k)
Proof
  rpt strip_tac >>
  `!j. f j IN R` by metis_tac [ring_fun_def] >>
  `|1| <> |0| /\ ( |1| = [#1])` by metis_tac [poly_zero_eq_one, poly_one] >>
  `[#1] <> |0|` by rw[] >>
  Induct_on `n` >| [
    rw[] >>
    Cases_on `f 0 = #0` >-
    rw[] >>
    `f 0 * [#1] = [f 0]` by metis_tac [poly_cmult_one] >>
    rw[],
    rpt strip_tac >>
    `!m. weak ((\j. f j o (X ** j)) m)` by rw[] >>
    `weak ((\j. f j o (X ** j)) n)` by rw[] >>
    `!m. plist (GENLIST (\j. (f j) o (X ** j)) m)` by rw[poly_weak_list_genlist] >>
    `!m. weak (psum (GENLIST (\j. (f j) o (X ** j)) m))` by rw[poly_weak_sum_weak] >>
    `poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n))) ' k =
    chop (psum (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n)))) ' k` by rw[poly_sum_by_weak_sum_genlist] >>
    `_ = psum (GENLIST (\j. (f j) o (X ** j)) (SUC (SUC n))) ' k` by rw[poly_coeff_chop] >>
    `_ = psum (SNOC ((\j. f j o (X ** j)) (SUC n)) (GENLIST (\j. f j o (X ** j)) (SUC n))) ' k` by rw_tac std_ss[GENLIST] >>
    `_ = ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || ((\j. f j o (X ** j)) (SUC n))) ' k` by rw[poly_weak_sum_SNOC] >>
    `_ = ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || (f (SUC n) o (X ** (SUC n)))) ' k` by rw[] >>
    `deg (psum (GENLIST (\j. f j o (X ** j)) (SUC n))) = n` by rw[poly_deg_weak_sum_genlist] >>
    Cases_on `k = SUC n` >| [
      `deg (f (SUC n) o (X ** (SUC n))) = SUC n` by rw[weak_deg_cmult] >>
      `n < SUC n` by decide_tac >>
      `lead ((psum (GENLIST (\j. f j o (X ** j)) (SUC n))) || (f (SUC n) o (X ** (SUC n)))) =
    lead (f (SUC n) o (X ** (SUC n)))` by metis_tac[weak_lead_weak_add] >>
      `_ = f (SUC n)` by rw[weak_lead_cmult, poly_monic_lead] >>
      metis_tac[poly_deg_weak_add, MAX_DEF, poly_coeff_lead],
      `k < SUC n` by decide_tac >>
      `(psum (GENLIST (\j. f j o (X ** j)) (SUC n)) || f (SUC n) o (X ** SUC n)) ' k =
    psum (GENLIST (\j. f j o (X ** j)) (SUC n)) ' k` by metis_tac[poly_coeff_weak_add_cmult_X_exp] >>
      `_ = chop (psum (GENLIST (\j. f j o (X ** j)) (SUC n))) ' k` by rw[poly_coeff_chop] >>
      `_ = poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k` by metis_tac[poly_sum_by_weak_sum_genlist] >>
      rw[]
    ]
  ]
QED


(* ------------------------------------------------------------------------- *)
(* Polynomial Identity only for Primes                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: To show: ###(binomial n j) * ([c] ** (n - j)) * (X ** j) = ##(binomial n j) * c ** (n - j) * (X ** j)
            c IN R ==> !n k. |n| * [c] ** k * p = ##n * c ** k * p  *)
(* Proof:
     |n| * [c] ** k * p
   = chop (( |n| * [c] ** k) o p)           by poly_mult_def
   = chop (chop ( |n| o ([c] ** k)) o p)    by poly_mult_def
   = chop (chop (chop [##n] o ([c] ** k)) o p)    by poly_one_sum_n
   = chop (chop (chop [##n] o chop [c ** k]) o p) by poly_exp_const
   = chop (chop ([##n] o [c ** k]) o p)     by poly_chop_mult_chop
   = chop (chop (##n o [c ** k]) o p)       by weak_mult_const
   = chop (chop [##n * c ** k] o p)         by weak_cmult_const
   = chop ([##n * c ** k] o p)              by poly_chop_mult
   = chop ((##n * c ** k) o p)              by weak_mult_const
   = ##n * c ** k * p                       by poly_cmult_def
*)
val poly_mult_num_const_exp = store_thm(
  "poly_mult_num_const_exp",
  ``!r:'a ring. Ring r ==> !p c. weak p /\ c IN R ==> !n k. |n| * [c] ** k * p = ##n * c ** k * p``,
  rpt strip_tac >>
  `##n IN R /\ weak [##n] /\ weak [c] /\ weak ([c ** k])` by rw[] >>
  `##n * c ** k IN R /\ weak [##n * c ** k]` by rw[] >>
  `|n| * [c] ** k * p = chop (( |n| * [c] ** k) o p)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop (chop ( |n| o ([c] ** k)) o p)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop (chop (chop [##n] o ([c] ** k)) o p)` by rw_tac std_ss[poly_one_sum_n] >>
  `_ = chop (chop (chop [##n] o chop [c ** k]) o p)` by rw_tac std_ss[poly_exp_const] >>
  `_ = chop (chop ([##n] o [c ** k]) o p)` by rw_tac std_ss[poly_chop_mult_chop] >>
  `_ = chop (chop (##n o [c ** k]) o p)` by rw_tac std_ss[weak_mult_const] >>
  `_ = chop (chop [##n * c ** k] o p)` by rw_tac std_ss[weak_cmult_const] >>
  `_ = chop ([##n * c ** k] o p)` by rw_tac std_ss[poly_chop_mult] >>
  rw_tac std_ss[weak_mult_const, poly_cmult_def]);

(* Theorem: c <> #0 ==> for all k <= n, ((X + [c]) ** n) ' k  = ##(binomial n k) * c ** (n - k)  *)
(* Proof:
   This is to show a sum of polynomials of increasing degree is equivalent to a single polynomial:

       poly_sum [[a];            = [a; b; c; ... ]
                 [b * X];
                 [c * X**2];
                 ... ]
   Note poly X         by poly_X
   and  poly [c]       by poly_nonzero_element_poly
   Since c <> #0, #1 <> #0   by ring_one_eq_zero, IN_SING
   rfun (\j. ##(binomial n j) * c ** (n - j))    by ring_num_element, ring_exp_element, ring_mult_element
   k <= n ==> k < SUC n
   Hence
     ((X + [c]) ** n) ' k
   = (([c] + X) ** n) ' k                                                               by poly_add_comm
   = poly_sum (GENLIST (\j. ###(binomial n j) * [c] ** (n - j) * X ** j) (SUC n)) ' k   by poly_binomial_thm
   = poly_sum (GENLIST (\j. ##(binomial n j) * c ** (n - j) * X ** j) (SUC n)) ' k      by poly_mult_num_const_exp
   = (\j. ##(binomial n j) * c ** (n - j)) k                                            by poly_coeff_sum_genlist
   = ##(binomial n k) * c ** (n - k)                                                    by function application
*)
val poly_coeff_X_add_c_exp_n = store_thm(
  "poly_coeff_X_add_c_exp_n",
  ``!r:'a ring. Ring r ==> !c. c IN R /\ c <> #0 ==>
    !n k. k < SUC n ==> (((X + [c]) ** n) ' k = ##(binomial n k) * c ** (n - k))``,
  rpt strip_tac >>
  `poly [c]` by rw[] >>
  `poly X` by rw[] >>
  `#1 <> #0` by metis_tac [ring_one_eq_zero, IN_SING] >>
  `rfun (\j. ##(binomial n j) * c ** (n - j))` by rw[] >>
  `((X + [c]) ** n) ' k = (([c] + X) ** n) ' k` by rw[poly_add_comm] >>
  `_ = poly_sum (GENLIST (\j. ###(binomial n j) * ([c] ** (n - j)) * (X ** j)) (SUC n)) ' k`
    by rw_tac std_ss[poly_binomial_thm] >>
  `_ = poly_sum (GENLIST (\j. ##(binomial n j) * c ** (n - j) * X ** j) (SUC n)) ' k`
    by rw[poly_mult_num_const_exp] >>
  rw_tac std_ss[poly_coeff_sum_genlist]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==>
            !k n. (factor c ** n) ' k = if n < k then #0 else if n = k then #1
                                        else ##(binomial n k) * (-c) ** (n - k) *)
(* Proof:
   Let p = factor c ** n.
   Note monic p             by poly_factor_monic
    and deg p = n           by poly_factor_exp_deg
    and p <> |0|            by poly_monic_nonzero
   This is to show:
   (1) n < k ==> p ' k = #0
       Note deg p < k       by deg p = n
         so p ' k = #0      by poly_coeff_nonzero
   (2) n = k ==> p ' k = #1
       Note p ' k
          = p ' (deg p)     by deg p = n = k
          = lead p          by poly_coeff_lead
          = #1              by poly_monic_lead
   (3) k < n ==> p ' k = ##(binomial n k) * -c ** (n - k)
       If c = #0,
       Note ##(binomial n k) * -#0 ** (n - k)
          = ##(binomial n k) * #0 ** (n - k)     by ring_neg_zero
          = ##(binomial n k) * #0                by ring_zero_exp, n - k <> 0
          = #0                                   by ring_mult_rzero
       Note p
          = factor #0 ** n          by c = #0
          = X ** n                  by poly_factor_zero
          = X ** n + ### 0          by poly_add_rzero
       If k = 0,
            (X ** n + ### 0) ' 0
          = (##0 :: PAD_LEFT #0 n [#1]) ' 0    by poly_X_exp_n_add_c_alt
          = #0                                 by poly_coeff_0_cons
       If k <> 0, then 0 < k.
            (X ** n + ### 0) ' k = #0          by poly_coeff_X_exp_n_add_c
       If c <> #0,
       Note factor c
          = X - c * |1|            by poly_factor_alt
          = X + (- c * |1|)        by poly_sub_def
          = X + ([- c])            by poly_cmult_one
       Note -c IN R                by field_neg_element
        and -c <> #0               by field_neg_eq_zero
       Also k <= n ==> k < SUC n   by arithmetic
       The result follows          by poly_coeff_X_add_c_exp_n

poly_coeff_X_add_c_exp_n
|- !r. Ring r ==>
     !c. c IN R /\ c <> #0 ==>
       !n k. k < SUC n ==> (((X + [c]) ** n) ' k = ##(binomial n k) * c ** (n - k))
*)
val poly_coeff_factor_exp = store_thm(
  "poly_coeff_factor_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==>
   !k n. (factor c ** n) ' k = if n < k then #0 else if n = k then #1
                               else ##(binomial n k) * (-c) ** (n - k)``,
  rpt strip_tac >>
  `monic (factor c ** n)` by rw[poly_factor_monic] >>
  `deg (factor c ** n) = n` by rw[poly_factor_exp_deg] >>
  `factor c ** n <> |0|` by rw[poly_monic_nonzero] >>
  rw_tac std_ss[] >-
  rw[poly_coeff_nonzero] >-
  metis_tac[poly_coeff_lead, poly_monic_lead] >>
  Cases_on `c = #0` >| [
    `k < n /\ n - k <> 0` by decide_tac >>
    `##(binomial n k) IN R /\ (-#0 = #0)` by rw[] >>
    `##(binomial n k) * -#0 ** (n - k) = #0` by metis_tac[ring_zero_exp, ring_mult_rzero] >>
    `k < n` by decide_tac >>
    `factor #0 ** n = X ** n` by rw[poly_factor_zero] >>
    `_ = X ** n + (poly_num r 0)` by rw[] >>
    Cases_on `k = 0` >-
    rw[poly_X_exp_n_add_c_alt, poly_coeff_0_cons] >>
    metis_tac[poly_coeff_X_exp_n_add_c, NOT_ZERO],
    `factor c = X - c * |1|` by rw[poly_factor_alt] >>
    `_ = X + (- c * |1|)` by rw[poly_sub_def] >>
    `_ = X + ([- c])` by rw[poly_cmult_one] >>
    `-c IN R /\ -c <> #0` by rw[] >>
    `k < SUC n` by decide_tac >>
    rw[GSYM poly_coeff_X_add_c_exp_n]
  ]);

(* In a binomial expansion:
     (X + |c|) ** n
   = X ** n + SUM (j, ##(binomial n j) * ##c ** (n - j) * X ** j) + c ** n
   I can show: for 0 < j < n,
   ##(binomial n j) * ##c ** (n - j) = #0
   But I want: ##(binomial n j) = #0

   Even if ##c <> #0, it can happend that ##c ** h = #0
   e.g. in 9,  ##3 <> #0, but ##3 ** 2 = ##9 = #0.


   1   2   1             -->  1  0  1           mod 2
   1   3   3   1         -->  1  0  0  1        mod 3
   1   4   6   4   1     -->  1  0  2  0  1     mod 4
                                    j=2             factors (4) = {2}
   1   5  10  10   5  1  -->  1  0  0  0  0  1  mod 5
   1   6  15  20  15  6  1     -->   1  0  3  2  3  0   1  mod 6
                                          j=2 3  4         factors (6) = {2, 3}
   1   7  21  35  35 21  7 1   -->   1  0  0  0  0 0 0  1  mod 7
   1  8  28  56 70 56 28 8 1   -->   1 0  4  0  6 0 4 0 1  mod 8
   1 9 36  83 126 126 83 36 9 1  -->  1 0  0 2 0 2 0  0 1  mod 9

   (x + 2) ^ 2   mod 2
   = x^2 + 2 x + 4  mod 2
   = x^2 + 0 x + 0  mod 2

   (x + 3) ^ 2   mod 9
   = x^3 + 3 x^2 + 3 x + 9  mod 9
   = x^3 + 3 x^2 + 3 x + 0  mod 9

*)

(* Theorem: [Two-Way Freshman's Theorem]
            Ring r ==> !c. coprime c (char r) ==>
            prime (char r) <=> 1 < (char r) /\ (X + |c|) ** (char r) = X ** (char r) + |c| *)
(* Proof:
   Let n = char r.
   Note that:
   poly X            by poly_X
   poly |c|          by poly_sum_num_poly

   If part: to show prime n ==> 1 < n /\ ((X + |c|) ** n = X ** n + |c|)
     prime n ==> 1 < n        by ONE_LT_PRIME
     (X + |c|) ** n
   = X ** n + |c| ** n        by poly_freshman_thm
   = X ** n + |c|             by poly_fermat_thm

   Only-if part: to show 1 < n /\ (X + |c|) ** n = X ** n + |c| ==> prime n
     Since n <> 1, char r <> 1,
     or #1 <> #0              by ring_char_eq_1
     and ##c <> #0            by ring_num_char_coprime_nonzero
     hence |c| = [##c]        by poly_one_sum_n, poly_chop_poly

     Given (X + |c|) ** n = X ** n + |c|, they have equal coefficients:
     !k. ((X + |c|) ** n) ' k = (X ** n + |c|) ' k

     !k. k < SUC n ==> (((X + |c|) ** n) ' k = ## (binomial n k) * ##c ** (n - k))  by poly_coeff_X_add_c_exp_n, or
     !k. k < SUC n ==> (((X + |c|) ** n) ' k = ## ((binomial n k) * c ** (n - k)))  by ring_num_mult_exp

     !k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0                                by poly_coeff_X_exp_n_add_c

     Since !k. 0 < k /\ k < n ==> k < SUC n, we have
     !k. 0 < k /\ k < n ==> n divides ((binomial n k) * c ** (n - k)    by ring_char_divides

     coprime c n ==> !j. coprime (c ** j) n  by coprime_exp
     hence
     !k. 0 < k /\ k < n ==> n divides (binomial n k)    by L_EUCLIDES (Euclid's Lemma)
     With 1 < n, prime n                                by prime_iff_divides_binomials
*)
val poly_ring_prime_identity = store_thm(
  "poly_ring_prime_identity",
  ``!r:'a ring. Ring r ==> !c. coprime c (char r) ==>
       (prime (char r) <=> 1 < char r /\ ((X + |c|) ** (char r) = X ** (char r) + |c|))``,
  rpt strip_tac >>
  qabbrev_tac `n = char r` >>
  `poly X` by rw[] >>
  `poly |c|` by rw[poly_sum_num_poly] >>
  rw_tac std_ss[EQ_IMP_THM, ONE_LT_PRIME] >-
  metis_tac [poly_freshman_thm, poly_fermat_thm] >>
  `1 <> n` by decide_tac >>
  `#1 <> #0` by rw[GSYM ring_char_eq_1] >>
  `##c <> #0` by rw[ring_num_char_coprime_nonzero] >>
  `##c IN R /\ ( |c| = [##c])` by rw[poly_one_sum_n] >>
  `!k. ((X + |c|) ** n) ' k = (X ** n + |c|) ' k` by rw_tac std_ss[] >>
  `!k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)` by rw[poly_coeff_X_exp_n_add_c] >>
  `!k. k < SUC n ==> (((X + |c|) ** n) ' k = ## ((binomial n k) * c ** (n - k)))`
    by metis_tac[poly_coeff_X_add_c_exp_n, ring_num_mult_exp] >>
  `!k. 0 < k /\ k < n ==> k < SUC n` by decide_tac >>
  metis_tac [ring_char_divides, coprime_exp, L_EUCLIDES, MULT_COMM, prime_iff_divides_binomials]);

(* Theorem: [Two-Way Freshman's Theorem]
            Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==>
            prime (char r) <=> (X + |c|) ** (char r) = X ** (char r) + |c| *)
(* Proof:
   Let n = char r.
   Note ##c <> #0           by ring_num_char_coprime_nonzero
    and ##c IN R            by ring_num_element
    and |c| = [##c]         by poly_nonzero_element_poly, poly_chop_poly


   If part: to show prime n ==> ((X + |c|) ** n = X ** n + |c|)
      Note poly X           by poly_X
      and poly |c|          by poly_sum_num_poly

       (X + |c|) ** n
      = X ** n + |c| ** n   by poly_freshman_thm
      = X ** n + |c|        by poly_fermat_thm

   Only-if part: to show (X + |c|) ** n = X ** n + |c| ==> prime n
     If n = 0,
        Then c = 1                     by coprime_0R, coprime c 0
         and [##1] = |1|               by ring_num_1, poly_one
         ==> |1| = |1| + |1|           by poly_exp_0
        Thus |1| + |0| = |1| + |1|     by poly_add_rzero
         or        |0| = |1|           by poly_add_lcancel
         or         #0 = #1            by poly_one_eq_poly_zero
        But this contradicts #1 <> #0.
     If n <> 0,
     Note n <> 1 since #1 <> #0        by ring_char_eq_1
     Thus 1 < n                        by n <> 0, n <> 1

     Given (X + |c|) ** n = X ** n + |c|
     they have equal coefficients:
     !k. ((X + |c|) ** n) ' k = (X ** n + |c|) ' k

     !k. k < SUC n ==> (((X + |c|) ** n) ' k = ## (binomial n k) * ##c ** (n - k))  by poly_coeff_X_add_c_exp_n, or
     !k. k < SUC n ==> (((X + |c|) ** n) ' k = ## ((binomial n k) * c ** (n - k)))  by ring_num_mult_exp

     !k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0                                by poly_coeff_X_exp_n_add_c

     Since !k. 0 < k /\ k < n ==> k < SUC n, we have
     !k. 0 < k /\ k < n ==> n divides ((binomial n k) * c ** (n - k)    by ring_char_divides

     coprime c n ==> !j. coprime (c ** j) n  by coprime_exp
     hence
     !k. 0 < k /\ k < n ==> n divides (binomial n k)    by L_EUCLIDES (Euclid's Lemma)
     With 1 < n, prime n                                by prime_iff_divides_binomials
*)
val poly_ring_prime_char_eqn = store_thm(
  "poly_ring_prime_char_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==>
       (prime (char r) <=> ((X + |c|) ** (char r) = X ** (char r) + |c|))``,
  rpt strip_tac >>
  qabbrev_tac `n = char r` >>
  `##c <> #0` by rw[ring_num_char_coprime_nonzero] >>
  `##c IN R /\ ( |c| = [##c])` by rw[poly_one_sum_n] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `poly X` by rw[] >>
    `poly |c|` by rw[poly_sum_num_poly] >>
    metis_tac [poly_freshman_thm, poly_fermat_thm],
    Cases_on `n = 0` >| [
      `c = 1` by metis_tac[coprime_0R] >>
      `|1| = |1| + [##1]` by metis_tac[poly_exp_0] >>
      `_ = |1| + |1|` by rw[ring_num_1, poly_one] >>
      `|1| = |0|` by metis_tac[poly_add_rzero, poly_add_lcancel, poly_one_poly, poly_zero_poly] >>
      metis_tac[poly_one_eq_poly_zero],
      `n <> 1` by metis_tac[ring_char_eq_1] >>
      `1 < n` by decide_tac >>
      `!k. ((X + |c|) ** n) ' k = (X ** n + |c|) ' k` by rw_tac std_ss[] >>
      `!k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)` by rw[poly_coeff_X_exp_n_add_c] >>
      `!k. k < SUC n ==> (((X + |c|) ** n) ' k = ## ((binomial n k) * c ** (n - k)))` by metis_tac[poly_coeff_X_add_c_exp_n, ring_num_mult_exp] >>
      `!k. 0 < k /\ k < n ==> k < SUC n` by decide_tac >>
      metis_tac [ring_char_divides, coprime_exp, L_EUCLIDES, MULT_COMM, prime_iff_divides_binomials]
    ]
  ]);

(*
> poly_ring_prime_identity |> ISPEC ``(ZN n)``;
val it = |- Ring (ZN n) ==>
   !c. coprime c (char (ZN n)) ==>
     (prime (char (ZN n)) <=>
      1 < char (ZN n) /\
      ((ring_of_poly (ZN n)).prod.exp
         ((ring_of_poly (ZN n)).sum.op
            (poly_shift (ZN n) (ring_of_poly (ZN n)).prod.id 1)
            ((ring_of_poly (ZN n)).sum.exp (ring_of_poly (ZN n)).prod.id
               c)) (char (ZN n)) =
       (ring_of_poly (ZN n)).sum.op
         ((ring_of_poly (ZN n)).prod.exp
            (poly_shift (ZN n) (ring_of_poly (ZN n)).prod.id 1)
            (char (ZN n)))
         ((ring_of_poly (ZN n)).sum.exp (ring_of_poly (ZN n)).prod.id
            c))): thm
*)

val _ = temp_overload_on ("x+", ``\n c:num. ((PolyRing (ZN n)).sum.op
                                      (poly_shift (ZN n) (PolyRing (ZN n)).prod.id 1)
                                      ((PolyRing (ZN n)).sum.exp (PolyRing (ZN n)).prod.id c))``);

(* Overloading for (X + |c|) ** m in (ZN n) *)
val _ = temp_overload_on ("x+^", ``\n c:num m. (PolyRing (ZN n)).prod.exp (x+ n c) m``);

(* Overloading for (X ** m + |c|) in (ZN n) *)
val _ = temp_overload_on ("x^+", ``\n c:num m. (PolyRing (ZN n)).sum.op
        ((PolyRing (ZN n)).prod.exp (poly_shift (ZN n) (PolyRing (ZN n)).prod.id 1) m)
        ((PolyRing (ZN n)).sum.exp (PolyRing (ZN n)).prod.id c)``);

(* Theorem: 1 < n ==> ((PolyRing (ZN n)).prod.id = [1]) *)
(* Proof:
   Since (ZN n).sum.id = 0                   by ZN_property
     and (ZN n).prod.id = 1                  by ZN_property, 1 < n.
   Hence (ring_of_poly (ZN n)).prod.id
       = poly_chop (ZN n) [(ZN n).prod.id]   by poly_ring_property
       = poly_chop (ZN n) [1]                by above
       = [1]                                 by (ZN n).prod.id <> (ZN n).sum.id
*)
val poly_ZN_prod_id = store_thm(
  "poly_ZN_prod_id",
  ``!n. 1 < n ==> ((PolyRing (ZN n)).prod.id = [1])``,
  rw[poly_ring_property, ZN_property]);

(* Theorem: 1 < n /\ coprime c n ==> (prime n <=> ((x+^ n c n) = (x^+ n c n))) *)
(* Proof:
   Since Ring (ZN n)                              by ZN_ring, 0 < n
     and char (ZN n) = n                          by ZN_char, 0 < n
   Hence prime n <=> ((x+^ n c n) = (x^+ n c n))  by poly_ring_prime_identity
*)
val poly_ZN_prime_identity = store_thm(
  "poly_ZN_prime_identity",
  ``!n (c: num). 1 < n /\ coprime c n ==> (prime n <=> ((x+^ n c n) = (x^+ n c n)))``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_ring_prime_identity]);

(* Theorem: coprime c n ==> (prime n <=> 1 < n /\ (x+^ n c n = x^+ n c n)) *)
(* Proof:
> poly_ring_prime_identity |> ISPEC ``(ZN n)``;
val it =
   |- Ring (ZN n) ==> !c. coprime c (char (ZN n)) ==>
      (prime (char (ZN n)) <=> 1 < char (ZN n) /\ x+^ n c (char (ZN n)) = x^+ n c (char (ZN n))):
  Note Ring (ZN n)       by ZN_ring
   and char (ZN n) = n   by ZN_char
 *)
val poly_ZN_prime_thm = store_thm(
  "poly_ZN_prime_thm",
  ``!n c. coprime c n ==> (prime n <=> 1 < n /\ (x+^ n c n = x^+ n c n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[NOT_PRIME_0] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_ring_prime_identity]);

(* obtain a corollary *)
val poly_ZN_prime_simple = save_thm("poly_ZN_prime_simple",
    poly_ZN_prime_thm |> ISPEC ``n:num`` |> ISPEC ``1`` |> SIMP_RULE bool_ss[GCD_1] |> GEN_ALL);
(* val poly_ZN_prime_simple =
   |- !n. prime n <=> 1 < n /\ (x+^ n 1 n = x^+ n 1 n): thm *)

(* Theorem: prime n ==> (x+^ n c n = x^+ n c n) *)
(* Proof:
   Note FiniteField (ZN n)            by ZN_finite_field, prime n
    and 0 < n                         by PRIME_POS
    ==> char (ZN n) = n               by ZN_char, 0 < n
   The result follows                 by poly_freshman_fermat_field

poly_freshman_fermat_field |> ISPEC ``(ZN n)``;
val it = |- FiniteField (ZN n) ==>
      !c. x+^ n c (char (ZN n)) = x^+ n c (char (ZN n)): thm
*)
val poly_ZN_freshman_fermat = store_thm(
  "poly_ZN_freshman_fermat",
  ``!n c. prime n ==> (x+^ n c n = x^+ n c n)``,
  metis_tac[poly_freshman_fermat_field, ZN_finite_field, ZN_char, PRIME_POS]);

(* ------------------------------------------------------------------------- *)
(* Polynomial as sum of Terms                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: rfun (poly_coeff r) *)
(* Proof: by ring_fun_def, poly_coeff_element. *)
val poly_coeff_ring_fun = store_thm(
  "poly_coeff_ring_fun",
  ``!r:'a ring. Ring r ==> !p. poly p ==> rfun (\k. p ' k)``,
  rw[]);

(* Theorem: poly p /\ poly q /\ !k. p ' k = q ' k ==> p = |0| <=> q = |0| *)
(* Proof:
   If p = |0|,
      then zerop |0|,         by zero_poly_zero
     hence !k. p ' k = #0     by zero_poly_coeff_all_zero
        so zerop q            by zero_poly_coeff_all_zero and given
        or q = |0|            by zero_poly_zero_poly, poly_zero
   If q = |0|, the proof is similar.
*)
val poly_coeff_eq_poly_zero = store_thm(
  "poly_coeff_eq_poly_zero",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\
   (!k. p ' k = q ' k) ==> ((p = |0|) <=> (q = |0|))``,
  metis_tac[zero_poly_zero, zero_poly_coeff_all_zero, zero_poly_zero_poly]);

(* Theorem: poly p /\ poly q /\ !k. p ' k = q ' k ==> deg p = deg q *)
(* Proof:
   First p = |0| <=> q = |0|     by poly_coeff_eq_poly_zero
   If p = |0|, q = |0|           by above
      So deg p = deg q = 0       by poly_deg_zero
   If p <> |0|, q <> |0|         by above
      By contradiction. Assume deg p < deg q.
      Then q ' (deg q) = lead q  by poly_coeff_lead
                       <> #0     by poly_lead_nonzero, q <> |0|.
       But p ' (deg q) = #0      by poly_coeff_nonzero, p <> |0|.
      which contradicts the given.
      Similarly for deg q < deg p.
*)
val poly_coeff_eq_deg_eq = store_thm(
  "poly_coeff_eq_deg_eq",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q /\ (!k. p ' k = q ' k) ==> (deg p = deg q)``,
  rpt strip_tac >>
  `(p = |0|) <=> (q = |0|)` by rw[poly_coeff_eq_poly_zero] >>
  Cases_on `p = |0|` >-
  rw_tac std_ss[] >>
  `q <> |0|` by metis_tac[] >>
  spose_not_then strip_assume_tac >>
  Cases_on `deg p < deg q` >| [
    all_tac,
    `deg q < deg p` by decide_tac
  ] >>
  metis_tac[poly_coeff_lead, poly_lead_nonzero, poly_coeff_nonzero]);

(* Theorem: poly p /\ poly q ==> (p = q) <=> !k. p ' k = q ' k *)
(* Proof:
   If part: (p = q) ==> !k. p ' k = q ' k
      This is trivially true.
   Only-if part: !k. p ' k = q ' k ==> (p = q)
      First, (p = |0|) <=> (q = |0|)                 by poly_coeff_eq_poly_zero
      If p = |0|, q = |0|, hence p = q               by above
      If p <> |0|, q <> |0|                          by above
      Now, deg p = deg q                             by poly_coeff_eq_deg_eq
       or  PRE (LENGTH p) = PRE (LENGTH q)           by poly_deg_nonzero
      Also LENGTH p <> 0 /\ LENGTH q <> 0            by LENGTH_NIL, poly_zero
        so LENGTH p = LENGTH q                       by SUC_PRE
     Hence !k. k < LENGTH p ==> (EL k p = EL k q)    by poly_coeff_as_element
       Thus p = q                                    by LIST_EQ
*)
val poly_coeff_eq_poly_eq = store_thm(
  "poly_coeff_eq_poly_eq",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> ((p = q) <=> !k. p ' k = q ' k)``,
  rw[EQ_IMP_THM] >>
  `(p = |0|) <=> (q = |0|)` by rw[poly_coeff_eq_poly_zero] >>
  Cases_on `p = |0|` >-
  rw[] >>
  `q <> |0|` by metis_tac[] >>
  `PRE (LENGTH p) = PRE (LENGTH q)` by metis_tac[poly_coeff_eq_deg_eq, poly_deg_nonzero] >>
  `LENGTH p <> 0 /\ LENGTH q <> 0` by metis_tac[LENGTH_NIL, poly_zero] >>
  `0 < LENGTH p /\ 0 < LENGTH q` by decide_tac >>
  `LENGTH p = LENGTH q` by metis_tac[SUC_PRE] >>
  metis_tac[poly_coeff_as_element, LIST_EQ]);

(* Theorem: Ring r ==> !a b. poly_fun a /\ poly_fun b ==>
            !n. poly_sum (GENLIST a n ++ GENLIST b n) = poly_sum (GENLIST (\k. a k + b k) n) *)
(* Proof:
   Apply ring_sum_genlist_append |> ISPEC ``(PolyRing r)``;
   val it = |- Ring (PolyRing r) ==> !a b. poly_fun a /\ poly_fun b ==>
     !n. poly_sum (GENLIST a n ++ GENLIST b n) = poly_sum (GENLIST (\k. a k + b k) n): thm
   and Ring (PolyRing r) is true by poly_add_mult_ring
*)
val poly_sum_gen_append = store_thm(
  "poly_sum_gen_append",
  ``!r:'a ring. Ring r ==> !a b. poly_fun a /\ poly_fun b ==>
   !n. poly_sum (GENLIST a n ++ GENLIST b n) = poly_sum (GENLIST (\k. a k + b k) n)``,
  rw_tac std_ss[poly_add_mult_ring, ring_sum_genlist_append]);

(* Theorem: Ring r ==> !p. poly p ==> !n. poly_sum (GENLIST (K p) n) = |n| * p *)
(* Proof:
   Apply ring_sum_genlist_const |> ISPEC ``(PolyRing r)``;
   val it = |- Ring (PolyRing r) ==> !x. x IN (PolyRing r).carrier ==>
           !n. poly_sum (GENLIST (K x) n) = |n| * x
   and Ring (PolyRing r)                     by poly_add_mult_ring
   and poly x <=> x IN (PolyRing r).carrier  by poly_ring_element
*)
val poly_sum_gen_const = store_thm(
  "poly_sum_gen_const",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. poly_sum (GENLIST (K p) n) = |n| * p``,
  rw[poly_add_mult_ring, poly_ring_element, ring_sum_genlist_const]);

(* Note: |n| = chop [##n] by poly_ring_sum_c *)

(* Theorem: poly_sum (GENLIST f (SUC n)) = f 0 + poly_sum (GENLIST (f o SUC) n) *)
(* Proof:
   Apply ring_sum_decompose_first |> GEN_ALL |> ISPEC ``(PolyRing r)``;
   val it = |- !f n. poly_sum (GENLIST f (SUC n)) = f 0 + poly_sum (GENLIST (f o SUC) n): thm
*)
val poly_sum_decompose_first = store_thm(
  "poly_sum_decompose_first",
  ``!r:'a ring. !f n. poly_sum (GENLIST f (SUC n)) = f 0 + poly_sum (GENLIST (f o SUC) n)``,
  rw[poly_add_mult_ring, ring_sum_decompose_first]);

(* Theorem: poly_fun f ==>
            !n. poly_sum (GENLIST f (SUC n)) = poly_sum (GENLIST f n) + f n *)
(* Proof:
   Since Ring r ==> Ring (PolyRing r)   by poly_add_mult_ring
   The result follows by ring_sum_decompose_last.
*)
val poly_sum_decompose_last = store_thm(
  "poly_sum_decompose_last",
  ``!r:'a ring. Ring r ==> !f. poly_fun f ==>
   !n. poly_sum (GENLIST f (SUC n)) = poly_sum (GENLIST f n) + f n``,
  rw[poly_add_mult_ring, ring_sum_decompose_last]);

(* Theorem: poly_fun f ==> !n. poly_list (GENLIST f n) *)
(* Proof:
   By induction on n.
   Base case: poly_list (GENLIST f 0)
     GENLIST f 0 = []                              by GENLIST
     and poly_list []                              by poly_list_nil
   Step case: poly_list (GENLIST f n) ==> poly_list (GENLIST f (SUC n))
     GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)  by GENLIST
     Now poly_list (GENLIST f n)                   by induction hypothesis
     and poly (f n)                                by poly_list_element
     hence poly_list (GENLIST f (SUC n)))          by poly_list_SNOC
*)
val poly_list_gen_from_poly_fun = store_thm(
  "poly_list_gen_from_poly_fun",
  ``!r:'a ring. Ring r ==> !f. poly_fun f ==> !n. poly_list (GENLIST f n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[poly_list_SNOC, GENLIST]);

(* Theorem: rfun f ==> !p. poly p ==> !n. poly_list (GENLIST (\j. f j * p ** j) n) *)
(* Proof:
   Since poly_fun (\j. f j * p ** j)  by poly_fun_from_ring_fun
   This is true by poly_list_gen_from_poly_fun.
*)
val poly_list_gen_from_ring_fun = store_thm(
  "poly_list_gen_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !p. poly p ==>
    !n. poly_list (GENLIST (\j. f j * p ** j) n)``,
  rw[poly_fun_from_ring_fun, poly_list_gen_from_poly_fun]);

(* Theorem: poly_fun f ==> !n. poly (poly_sum (GENLIST f n)) *)
(* Proof:
   Since poly_list (GENLIST f n)   by poly_list_gen_from_poly_fun
   Result is true by poly_sum_poly.
*)
val poly_sum_gen_poly_fun_poly = store_thm(
  "poly_sum_gen_poly_fun_poly",
  ``!r:'a ring. Ring r ==> !f. poly_fun f ==> !n. poly (poly_sum (GENLIST f n))``,
  rw[poly_list_gen_from_poly_fun]);

(* export simple result *)
val _ = export_rewrites ["poly_sum_gen_poly_fun_poly"];

(* Theorem: rfun f ==> !p. poly p ==> !n. poly (poly_sum (GENLIST (\j. f j * p ** j) n)) *)
(* Proof:
   Since poly_list (GENLIST (\j. f j * p ** j) n)   by poly_list_gen_from_ring_fun
   Result is true by poly_sum_poly.
*)
val poly_sum_gen_ring_fun_poly = store_thm(
  "poly_sum_gen_ring_fun_poly",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !p. poly p ==>
    !n. poly (poly_sum (GENLIST (\j. f j * p ** j) n))``,
  rw[poly_list_gen_from_ring_fun]);

(* export simple result *)
val _ = export_rewrites ["poly_sum_gen_ring_fun_poly"];

(* Theorem: rfun f ==> !n. deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) <= n *)
(* Proof:
   By induction on n.
   Base case: deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC 0))) <= 0
       poly_sum (GENLIST (\j. f j * X ** j) (SUC 0))
     = poly_sum (f 0 * X ** 0):: (GENLIST (\j. f j * X ** j) 0)   by GENLIST_CONS
     = poly_sum [f 0 * X ** 0]                                    by GENLIST
     = poly_sum [f 0 * |1|]                                       by poly_exp_0
     = f 0 * |1| + poly_sum []                                    by poly_sum_cons
     = f 0 * |1| + |0|                                            by poly_sum_nil
     = f 0 * |1|                                                  by poly_add_rzero
     If f 0 = #0, f 0 * |1| = |0|, deg |0| = 0                    by poly_deg_zero
     If f 0 <> #0, deg (f 0 * |1|) = deg [f 0] = 0                by poly_cmult_one, poly_deg_const
     Either case, 0 <= 0.
   Step case: deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n ==>
              deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))) = SUC n
     Since poly_fun (\j. f j * X ** j)               by poly_fun_from_ring_fun
       poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))
     = poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) + (f (SUC n)) * X ** (SUC n) by poly_sum_decompose_last
     deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n      by induction hypothesis
     If f (SUC n) = #0,
        #0 * X ** (SUC n)) = |0|                                  by poly_cmult_lzero
          poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))
        = poly_sum (GENLIST (\j. f j * X ** j) (SUC n))           by poly_add_rzero
        and n < SUC n.
     If f (SUC n) <> #0,
        lead (X ** (SUC n)) = lead X = #1                         by poly_monic_X, poly_monic_exp_monic
     deg ((f (SUC n)) * X ** (SUC n)) = SUC n                     by weak_deg_cmult_nonzero
     Hence deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))) = SUC n  by poly_deg_add_less
     Either case, the degree <= SUC n.
*)
val poly_sum_gen_deg_bound = store_thm(
  "poly_sum_gen_deg_bound",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f. rfun f ==>
   !n. (deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) <= n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac[ring_fun_def] >>
  Induct_on `n` >| [
    `poly (f 0 * |1|)` by rw[] >>
    `deg (f 0 * |1|) = 0` by
  (Cases_on `f 0 = #0` >-
    rw[] >>
    rw[]
    ) >>
    rw[],
    `poly X` by rw[] >>
    `poly_fun (\j. f j * X ** j)` by rw[poly_fun_from_ring_fun] >>
    `poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))
  = poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) + (f (SUC n)) * X ** (SUC n)` by rw_tac std_ss[poly_sum_decompose_last] >>
    Cases_on `f (SUC n) = #0` >| [
      `#0 * X ** (SUC n) = |0|` by rw[] >>
      `deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n))))
  = deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)))` by rw_tac std_ss[poly_sum_gen_ring_fun_poly, poly_add_rzero] >>
      decide_tac,
      `poly (X ** (SUC n)) /\ (lead (X ** (SUC n)) = #1)` by rw[] >>
      `deg ((f (SUC n)) * X ** (SUC n)) = SUC n` by rw[weak_deg_cmult_nonzero] >>
      `!m n. m <= n ==> m < SUC n` by decide_tac >>
      `deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC (SUC n)))) = SUC n`
     by rw_tac std_ss[poly_deg_add_less, poly_sum_gen_ring_fun_poly, poly_cmult_poly] >>
      decide_tac
    ]
  ]);

(* Theorem: rfun f /\ f n <> #0 ==> deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n *)
(* Proof:
   First, poly_fun (\j. f j * X ** j)                  by poly_fun_from_ring_fun
     and  poly_sum (GENLIST (\j. f j * X ** j) (SUC n))
        = poly_sum (GENLIST (\j. f j * X ** j) n) + f n * X ** n    by poly_sum_decompose_last
   If n = 0,
      poly_sum (GENLIST (\j. f j * X ** j) (SUC 0))
    = |0| + f 0 * |1|              by poly_sum_nil, GENLIST, poly_exp_0
    = f 0 * |1|                    by poly_add_lzero
    and deg (f 0 * |1|)
      = deg [f 0]                  by poly_cmult_one
      = 0                          by poly_deg_const
   If n <> 0, n = SUC m for some m.
     deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC m)) <= m         by poly_sum_gen_deg_bound
     deg (f (SUC m) * X ** SUC m) = SUC m                            by weak_deg_cmult_nonzero, f n <> #0
     Hence deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n   by poly_deg_add_less
*)
val poly_sum_gen_deg = store_thm(
  "poly_sum_gen_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
   (deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac[ring_fun_def] >>
  `poly_fun (\j. f j * X ** j)` by rw[poly_fun_from_ring_fun] >>
  `poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) = poly_sum (GENLIST (\j. f j * X ** j) n) + f n * X ** n` by rw[poly_sum_decompose_last] >>
  Cases_on `n` >-
  rw[] >>
  `deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n'))) <= n'` by rw[poly_sum_gen_deg_bound] >>
  `poly X /\ poly (X ** (SUC n')) /\ (lead (X ** (SUC n')) = #1)` by rw[] >>
  `deg (f (SUC n') * X ** SUC n') = SUC n'` by rw[weak_deg_cmult_nonzero] >>
  `!m n. m <= n ==> m < SUC n` by decide_tac >>
  rw_tac std_ss[poly_deg_add_less, poly_sum_gen_ring_fun_poly, poly_cmult_poly]);

(* Theorem: rfun f /\ f n <> #0 ==> lead (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = f n *)
(* Proof:
   First, poly_fun (\j. f j * X ** j)                  by poly_fun_from_ring_fun
     and  poly_sum (GENLIST (\j. f j * X ** j) (SUC n))
        = poly_sum (GENLIST (\j. f j * X ** j) n) + f n * X ** n    by poly_sum_decompose_last
   If n = 0,
      poly_sum (GENLIST (\j. f j * X ** j) (SUC 0))
    = |0| + f 0 * |1|              by poly_sum_nil, GENLIST, poly_exp_0
    = f 0 * |1|                    by poly_add_lzero
    and lead (f 0 * |1|)
      = lead [f 0]                 by poly_cmult_one
      = f 0                        by poly_lead_const
   If n <> 0, n = SUC m for some m.
     deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC m)) <= m         by poly_sum_gen_deg_bound
     deg (f (SUC m) * X ** SUC m) = SUC m                            by weak_deg_cmult_nonzero, f n <> #0
     Hence lead (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)))
          = lead (f (SUC m) * X ** SUC m)                            by poly_lead_add_less
          = f n                                                      by weak_lead_cmult_nonzero, f n <> #0
*)
val poly_sum_gen_lead = store_thm(
  "poly_sum_gen_lead",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
   (lead (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) = f n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac[ring_fun_def] >>
  `poly_fun (\j. f j * X ** j)` by rw[poly_fun_from_ring_fun] >>
  `poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) = poly_sum (GENLIST (\j. f j * X ** j) n) + f n * X ** n` by rw[poly_sum_decompose_last] >>
  Cases_on `n` >-
  rw[] >>
  `deg (poly_sum (GENLIST (\j. f j * X ** j) (SUC n'))) <= n'` by rw[poly_sum_gen_deg_bound] >>
  `poly X /\ poly (X ** (SUC n')) /\ (lead (X ** (SUC n')) = #1)` by rw[] >>
  `deg (f (SUC n') * X ** SUC n') = SUC n'` by rw[weak_deg_cmult_nonzero] >>
  `!m n. m <= n ==> m < SUC n` by decide_tac >>
  `lead (f (SUC n') * X ** SUC n') = f (SUC n')` by rw[weak_lead_cmult_nonzero] >>
  rw_tac std_ss[poly_lead_add_less, poly_sum_gen_ring_fun_poly, poly_cmult_poly]);

(* Theorem: poly p ==> (p = poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) *)
(* Proof:
   First, rfun (\k. p ' k)                by poly_coeff_ring_fun
     and  (\k. p ' k) (deg p) = lead p    by poly_coeff_lead
   If p = |0|,
     Since poly_fun (\j. (\k. p ' k) j * X ** j)   by poly_fun_from_ring_fun
      poly_sum (GENLIST (\k. ( |0| ' k) * (X ** k)) (SUC (deg |0|)))
    = poly_sum (GENLIST (\k. ( |0| ' k) * (X ** k)) (SUC 0))     by poly_deg_zero
    = poly_sum (GENLIST (\k. ( |0| ' k) * (X ** k)) 0) + |0| ' 0 * X ** 0   by poly_sum_decompose_last
    = |0| +  #0 * |1|                                           by poly_sum_nil, GENLIST, poly_coeff_zero, poly_exp_0
    = |0| + |0|                                                 by poly_cmult_lzero
    = |0|                                                       by poly_add_zero_zero
   If p <> |0|,
      lead p <> #0                                                               by poly_lead_nonzero
      poly (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))))           by poly_sum_gen_ring_fun_poly
      deg (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) = deg p    by poly_sum_gen_deg
      lead (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) = lead p  by poly_sum_gen_lead
      poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) <> |0|           by poly_nonzero_lead_nonzero
      Now,
      !j. j < SUC (deg p) ==>
      (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) ' j = (p ' j))  by poly_coeff_sum_genlist
      !j. deg p < j ==>
      (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) ' j = (p ' j))  by poly_coeff_nonzero
      Since  !j n. ~(n < j) <=> j < SUC n
         so  !j. poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) ' j = (p ' j)
      Hence result follows by poly_coeff_eq_poly_eq
*)
val poly_eq_poly_sum = store_thm(
  "poly_eq_poly_sum",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !p. poly p ==> (p = poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))))``,
  rpt strip_tac >>
  `rfun (\k. p ' k)` by rw[poly_coeff_ring_fun] >>
  Cases_on `p = |0|` >| [
    `poly_fun (\j. (\k. p ' k) j * X ** j)` by rw_tac std_ss[poly_fun_from_ring_fun, poly_X] >>
    rw[poly_sum_decompose_last],
    `(\k. p ' k) (deg p) = lead p` by rw[poly_coeff_lead] >>
    `lead p <> #0` by rw[] >>
    `poly (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))))` by rw[] >>
    `deg (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) = deg p` by metis_tac[poly_sum_gen_deg] >>
    `lead (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) = lead p` by metis_tac[poly_sum_gen_lead] >>
    `(poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p)))) <> |0|` by metis_tac[poly_nonzero_lead_nonzero, poly_is_weak] >>
    `!j. j < SUC (deg p) ==> (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) ' j = (p ' j))` by rw[poly_coeff_sum_genlist] >>
    `!j. deg p < j ==> (poly_sum (GENLIST (\k. (p ' k) * (X ** k)) (SUC (deg p))) ' j = (p ' j))` by metis_tac[poly_coeff_nonzero] >>
    `!j n. ~(n < j) <=> j < SUC n` by decide_tac >>
    metis_tac[poly_coeff_eq_poly_eq]
  ]);

(* Theorem: Ring r ==> !f. wfun f ==> !p. weak p ==>
            (poly_sum (GENLIST (\k. (chop p) ' k * (f k)) (SUC (deg (chop p)))) =
             poly_sum (GENLIST (\k. p ' k * (f k)) (SUC (deg p)))) *)
(* Proof:
   Applying poly_coeff_chop, this is to show:
      poly_sum (GENLIST (\k. p ' k * f k) (SUC (deg (chop p)))) =
      poly_sum (GENLIST (\k. p ' k * f k) (SUC (deg p)))
   By induction on (deg p - deg (chop p)).
   Base: 0 = deg p - deg (chop p) ==> goal
      Note deg (chop p) <= deg p        by poly_deg_chop
      Thus deg p = deg (chop p)         by difference = 0
      The result is true trivially.
   Step: SUC v = deg p - deg (chop p) ==> goal
      Note deg p <> deg (chop p)        by difference = SUC v > 0
       ==>     p <> chop p              by deg p <> deg (chop p)
      Let h = lead p, q = FRONT p.
      Then p <> |0| /\ h = #0           by poly_chop_eq
       ==> chop q = chop p              by poly_chop_front, p <> |0|
       and weak q                       by weak_front_last
       Now 0 < deg p                    by deg p - something > 0
       ==> deg p = SUC (deg q)          by weak_front_deg, 0 < deg p
      Thus SUC v = SUC (deg q) - deg (chop q)   by above
        or     v = deg q - deg (chop q)         by above
      This means the induction hypothesis is applicable to q.

      Applying poly_coeff_front, and chop p = chop q, the goal becomes:
         poly_sum (GENLIST g (SUC (deg (chop q)))) = poly_sum (GENLIST g (SUC (deg p)))
      where g = \k. q ' k * f k.

      Claim: poly_fun g
      Proof: This is to show: !k. poly (q ' k * f k)
             Thus q ' k IN R            by weak_coeff_element, weak q
              and weak (f k)            by weak_fun_def
              ==> poly (q ' k * f k)    by poly_cmult_weak_poly

      Thus poly_list (GENLIST g (SUC (deg q)))        by poly_list_gen_from_poly_fun, poly_fun g
       ==> poly (poly_sum (GENLIST g (SUC (deg q))))  by poly_sum_poly

      Claim: g (deg p) = |0|
      Proof:   g (deg p)
             = q ' (deg p) * f (deg p)    by notation
             = p ' (deg p) * f (deg p)    by poly_coeff_front
             = h * f (deg p)              by poly_coeff_lead
             = #0 * f (deg p)             by h = #0, above
             = chop (#0 o f (deg p))      by poly_cmult_def
             Note weak (f (deg p))        by weak_fun_def
               so zerop (#0 o f (deg p))  by weak_cmult_lzero
             Thus g (deg p) = |0|         by poly_chop_zero_poly

       poly_sum (GENLIST g (SUC (deg p)))
     = poly_sum (GENLIST g (deg p)) + (g (deg p))   by poly_sum_decompose_last
     = poly_sum (GENLIST g (SUC (deg q))) + |0|     by deg p = SUC (deg q), g (deg p) = |0|
     = poly_sum (GENLIST g (SUC (deg q)))           by poly_add_rzero
     = poly_sum (GENLIST g (SUC (deg (chop q))))    by induction hypothesis
*)
val weak_poly_sum_genlist = store_thm(
  "weak_poly_sum_genlist",
  ``!r:'a ring. Ring r ==> !f. wfun f ==> !p. weak p ==>
     (poly_sum (GENLIST (\k. (chop p) ' k * (f k)) (SUC (deg (chop p)))) =
      poly_sum (GENLIST (\k. p ' k * (f k)) (SUC (deg p))))``,
  rpt strip_tac >>
  rw[poly_coeff_chop] >>
  Induct_on `deg p - deg (chop p)` >| [
    rpt strip_tac >>
    `deg (chop p) <= deg p` by rw[poly_deg_chop] >>
    `deg p = deg (chop p)` by decide_tac >>
    rw[],
    rpt strip_tac >>
    `deg p <> deg (chop p) /\ 0 < deg p` by decide_tac >>
    `p <> chop p` by metis_tac[] >>
    qabbrev_tac `h = lead p` >>
    qabbrev_tac `q = FRONT p` >>
    `p <> |0| /\ (h = #0)` by metis_tac[poly_chop_eq] >>
    `weak q` by rw[weak_front_last, Abbr`q`] >>
    `chop q = chop p` by rw[GSYM poly_chop_front, Abbr`q`] >>
    `SUC (deg q) = deg p` by rw[weak_front_deg, Abbr`q`] >>
    `SUC v = SUC (deg q) - deg (chop q)` by rw[] >>
    `v = deg q - deg (chop q)` by decide_tac >>
    `poly_sum (GENLIST (\k. q ' k * f k) (SUC (deg (chop q)))) = poly_sum (GENLIST (\k. q ' k * f k) (SUC (deg p)))` suffices_by metis_tac[poly_coeff_front] >>
    qabbrev_tac `g = \k. q ' k * f k` >>
    `poly_fun g` by
  (rw[Abbr`g`] >>
    rw[poly_ring_element] >>
    `q ' k IN R` by rw[weak_coeff_element] >>
    metis_tac[weak_fun_def, poly_cmult_weak_poly]) >>
    `poly_list (GENLIST g (SUC (deg q)))` by rw[poly_list_gen_from_poly_fun] >>
    `poly (poly_sum (GENLIST g (SUC (deg q))))` by rw[poly_sum_poly] >>
    `g (deg p) = |0|` by
    (rw_tac std_ss[Abbr`g`] >>
    `q ' (deg p) * f (deg p) = p ' (deg p) * f (deg p)` by metis_tac[poly_coeff_front] >>
    `_ = #0 * f (deg p)` by rw[poly_coeff_lead] >>
    `weak (f (deg p))` by metis_tac[weak_fun_def] >>
    metis_tac[weak_cmult_lzero, poly_cmult_def, poly_chop_zero_poly]) >>
    `poly_sum (GENLIST g (SUC (deg p))) = poly_sum (GENLIST g (deg p)) + (g (deg p))` by rw[poly_sum_decompose_last] >>
    `_ = poly_sum (GENLIST g (SUC (deg q))) + |0|` by rw_tac std_ss[] >>
    `_ = poly_sum (GENLIST g (SUC (deg (chop q))))` by rw[Abbr`g`] >>
    rw[]
  ]);

(* This milestone theorem is the magic key to transform weak poly_sums. *)

(* ------------------------------------------------------------------------- *)
(* Freshman Theorems for Polynomial Sums                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
            !n. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (char r)
               = poly_sum (GENLIST (\j. (f j * p ** j) ** (char r)) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: poly_sum (GENLIST (\j. f j * p ** j) 0) ** m =
              poly_sum (GENLIST (\j. (f j * p ** j) ** m) 0)
      Note 0 < m                      by PRIME_POS
      LHS = poly_sum (GENLIST (\j. f j * p ** j) 0) ** m
          = poly_sum [] ** m          by GENLIST
          = |0| ** m                  by poly_sum_nil
          = |0|                       by poly_zero_exp, 0 < m.
      RHS = poly_sum (GENLIST (\j. (f j * p ** j) ** m) 0)
          = poly_sum []               by GENLIST
          = |0| = LHS                 by poly_sum_nil
   Step case: poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m =
              poly_sum (GENLIST (\j. (f j * p ** j) ** m) (SUC n))
      Note poly_fun (\j. f j * p ** j)                     by poly_fun_from_ring_fun
       and poly_fun (\j. (f j * p ** j) ** m)              by poly_fun_from_ring_fun_exp
       and poly (poly_sum (GENLIST (\j. f j * p ** j) n))  by poly_sum_poly, poly_list_gen_from_poly_fun
      LHS = poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m
          = (poly_sum (GENLIST (\j. f j * p ** j) n) + (f n * p ** n)) ** m       by poly_sum_decompose_last
          = (poly_sum (GENLIST (\j. f j * p ** j) n)) ** m + (f n * p ** n) ** m  by poly_freshman_thm
          = poly_sum (GENLIST (\j. (f j * p ** j) ** m) n) + (f n * p ** n) ** m  by induction hypothesis
      RHS = poly_sum (GENLIST (\j. (f j * p ** j) ** m) (SUC n))
          = poly_sum (GENLIST (\j. (f j * p ** j) ** m) n) + (f n * p ** n) ** m) by poly_sum_decompose_last
          = LHS
*)
val poly_sum_freshman_thm = store_thm(
  "poly_sum_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
   !n. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (char r)
      = poly_sum (GENLIST (\j. (f j * p ** j) ** (char r)) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, SNOC, poly_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    rw[poly_zero_exp],
    `poly_fun (\j. f j * p ** j)` by rw[poly_fun_from_ring_fun] >>
    `poly_fun (\j. (f j * p ** j) ** m)` by rw[poly_fun_from_ring_fun_exp] >>
    `poly (poly_sum (GENLIST (\j. f j * p ** j) n))` by rw[poly_sum_poly, poly_list_gen_from_poly_fun] >>
    `!n. f n IN R` by metis_tac[ring_fun_def] >>
    `poly (f n * p ** n)` by rw[] >>
    `poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m
    = (poly_sum (GENLIST (\j. f j * p ** j) n) + (f n * p ** n)) ** m` by rw[poly_sum_decompose_last] >>
    `_ = (poly_sum (GENLIST (\j. f j * p ** j) n)) ** m + (f n * p ** n) ** m` by rw[poly_freshman_thm, Abbr`m`] >>
    `_ = poly_sum (GENLIST (\j. (f j * p ** j) ** m) n) + (f n * p ** n) ** m` by rw[] >>
    `_ = poly_sum (GENLIST (\j. (f j * p ** j) ** m) (SUC n))` by rw[poly_sum_decompose_last] >>
    rw[]
  ]);

(* Theorem: Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
            !n k. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (char r ** k)
                 = poly_sum (GENLIST (\j. (f j * p ** j) ** (char r ** k)) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: poly_sum (GENLIST (\j. f j * p ** j) 0) ** m ** k =
              poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) 0)
      Note 0 < m                      by PRIME_POS
        so 0 < m ** k                 by EXP_NONZERO
      LHS = poly_sum (GENLIST (\j. f j * p ** j) 0) ** m ** k
          = poly_sum [] ** m ** k     by GENLIST
          = |0| ** m ** k             by poly_sum_nil
          = |0|                       by poly_zero_exp, 0 < m ** k.
      RHS = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) 0)
          = poly_sum []               by GENLIST
          = |0| = LHS                 by poly_sum_nil
   Step case: poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m ** k =
              poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) (SUC n))
      Note poly_fun (\j. f j * p ** j)                     by poly_fun_from_ring_fun
       and poly_fun (\j. (f j * p ** j) ** m ** k)         by poly_fun_from_ring_fun_exp
       and poly (poly_sum (GENLIST (\j. f j * p ** j) n))  by poly_sum_poly, poly_list_gen_from_poly_fun
      LHS = poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m ** k
          = (poly_sum (GENLIST (\j. f j * p ** j) n) + (f n * p ** n)) ** m ** k            by poly_sum_decompose_last
          = (poly_sum (GENLIST (\j. f j * p ** j) n)) ** m ** k + (f n * p ** n) ** m ** k  by poly_freshman_all
          = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) n) + (f n * p ** n) ** m ** k  by induction hypothesis
      RHS = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) (SUC n))
          = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) n) + (f n * p ** n) ** m ** k) by poly_sum_decompose_last
          = LHS
*)
val poly_sum_freshman_all = store_thm(
  "poly_sum_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !p. poly p ==>
   !n k. (poly_sum (GENLIST (\j. f j * p ** j) n)) ** (char r ** k)
       = poly_sum (GENLIST (\j. (f j * p ** j) ** (char r ** k)) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, SNOC, poly_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    `m ** k <> 0` by rw[EXP_NONZERO] >>
    rw[poly_zero_exp],
    `poly_fun (\j. f j * p ** j)` by rw[poly_fun_from_ring_fun] >>
    `poly_fun (\j. (f j * p ** j) ** m ** k)` by rw[poly_fun_from_ring_fun_exp] >>
    `poly (poly_sum (GENLIST (\j. f j * p ** j) n))` by rw[poly_sum_poly, poly_list_gen_from_poly_fun] >>
    `!n. f n IN R` by metis_tac[ring_fun_def] >>
    `poly (f n * p ** n)` by rw[] >>
    `poly_sum (GENLIST (\j. f j * p ** j) (SUC n)) ** m ** k
    = (poly_sum (GENLIST (\j. f j * p ** j) n) + (f n * p ** n)) ** m ** k` by rw[poly_sum_decompose_last] >>
    `_ = (poly_sum (GENLIST (\j. f j * p ** j) n)) ** m ** k + (f n * p ** n) ** m ** k` by rw[poly_freshman_all, Abbr`m`] >>
    `_ = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) n) + (f n * p ** n) ** m ** k` by rw[] >>
    `_ = poly_sum (GENLIST (\j. (f j * p ** j) ** m ** k) (SUC n))` by rw[poly_sum_decompose_last] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* More on Evaluation of Polynomials                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly_list s ==> !x. x IN R ==> rlist (MAP (\p. eval p x) s) *)
(* Proof:
   By induction on s.
   Base case: poly_list [] ==> rlist (MAP (\p. eval p x) [])
     Since MAP (\p. eval p x) [] = []          by MAP
       and rlist [] is true                    by ring_list_nil
   Step case: poly_list s ==> rlist (MAP (\p. eval p x) s) ==>
              !h. poly_list (h::s) ==> rlist (MAP (\p. eval p x) (h::s))
     Note poly_list (h::s)
      ==> poly h /\ poly_list s                by poly_list_cons
       MAP (\p. eval p x) (h::s)
     = (eval h x):: MAP (\p. eval p x) s       by MAP
     Since (eval h x) IN R                     by poly_peval_element
       and rlist (MAP (\p. eval p x) s)        by induction hypothesis
     hence rlist (MAP (\p. eval p x) (h::s))   by ring_list_cons
*)
val poly_eval_poly_list = store_thm(
  "poly_eval_poly_list",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !x. x IN R ==> rlist (MAP (\p. eval p x) s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: poly_list s ==> !x. x IN R ==> (eval (poly_sum s) x = rsum (MAP (\p. eval p x) s)) *)
(* Proof:
   By induction on s.
   Base case: poly_list [] ==> (eval (poly_sum []) x = rsum (MAP (\p. eval p x) []))
        eval (poly_sum []) x
      = eval |0| x                    by poly_sum_nil
      = #0                            by poly_eval_zero
      = rsum []                       by ring_sum_nil
      = rsum (MAP (\p. eval p x) [])  by MAP
   Step case: poly_list s ==> (eval (poly_sum s) x = rsum (MAP (\p. eval p x) s)) ==>
             !h. poly_list (h::s) ==> (eval (poly_sum (h::s)) x = rsum (MAP (\p. eval p x) (h::s)))
     Since poly_list (h::s) ==> poly h /\ poly_list s    by poly_list_cons
       and rlist (MAP (\p. eval p x) s)                  by poly_eval_poly_list
        eval (poly_sum (h::s)) x
      = eval (h + poly_sum s) x                          by poly_sum_cons
      = (eval h x) + (eval (poly_sum s) x)               by poly_eval_add
      = (eval h x) + rsum (MAP (\p. eval p x) s)         by induction hypothesis
      = rsum ((eval h x):: (MAP (\p. eval p x) s))       by ring_sum_cons
      = rsum (MAP (\p. eval p x) (h::s))                 by MAP
*)
val poly_eval_poly_sum = store_thm(
  "poly_eval_poly_sum",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !x. x IN R ==> (eval (poly_sum s) x = rsum (MAP (\p. eval p x) s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[poly_eval_add, poly_eval_poly_list]);

(* Theorem: poly_fun f ==> !x. x IN R ==>
            !n. eval (poly_sum (GENLIST f n)) x = rsum (MAP (\p. eval p x) (GENLIST f n)) *)
(* Proof:
   Since poly_list (GENLIST f n)      by poly_list_gen_from_poly_fun
   The result is true                 by poly_eval_poly_sum
*)
val poly_eval_poly_sum_gen = store_thm(
  "poly_eval_poly_sum_gen",
  ``!r:'a ring. Ring r ==> !f. poly_fun f ==> !x. x IN R ==>
   !n. eval (poly_sum (GENLIST f n)) x = rsum (MAP (\p. eval p x) (GENLIST f n))``,
  rw[poly_list_gen_from_poly_fun, poly_eval_poly_sum]);

(* Theorem: rfun f ==> !p x. poly p /\ x IN R ==>
            !n. eval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) x =
                rsum (GENLIST (\k. f k * ((eval p x) ** k)) n) *)
(* Proof:
   First, poly_fun (\j. f j * p ** j)                    by poly_fun_from_ring_fun
     and  poly_list (GENLIST (\k. f k * (p ** k)) n)     by poly_list_gen_from_poly_fun
    Also  (\p. eval p x) o (\k. f k * (p ** k))
        = (\k. eval (f k * (p ** k)) x)                  by o_thm, FUN_EQ_THM

      eval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) x
    = rsum (MAP (\p. eval p x) (GENLIST (\k. f k * (p ** k)) n))  by poly_eval_poly_sum
    = rsum (GENLIST ((\p. eval p x) o (\k. f k * (p ** k))) n)    by MAP_GENLIST
    = rsum (GENLIST (\k. eval (f k * (p ** k)) x) n)              by composition above
    = rsum (GENLIST (\k. f k * eval (p ** k) x) n)                by poly_eval_cmult
    = rsum (GENLIST (\k. f k * ((eval p x) ** k)) n)              by poly_eval_exp
*)
val poly_eval_poly_sum_gen_poly = store_thm(
  "poly_eval_poly_sum_gen_poly",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !p x. poly p /\ x IN R ==>
   !n. eval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) x =
       rsum (GENLIST (\k. f k * ((eval p x) ** k)) n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac[ring_fun_def] >>
  `poly_fun (\j. f j * p ** j)` by rw[poly_fun_from_ring_fun] >>
  `poly_list (GENLIST (\k. f k * (p ** k)) n)` by rw[poly_list_gen_from_poly_fun] >>
  `(\p. eval p x) o (\k. f k * (p ** k)) = (\k. eval (f k * (p ** k)) x)` by rw[FUN_EQ_THM] >>
  rw[poly_eval_poly_sum, MAP_GENLIST, poly_eval_cmult, poly_eval_exp]);

(* Theorem: poly p /\ x IN R ==>
            (eval p x = rsum (GENLIST (\k. (p ' k) * (x ** k)) (SUC (deg p)))) *)
(* Proof:
   Since rfun (\k. p ' k)                    by poly_coeff_ring_fun
      so poly_fun ((\k. p ' k * X ** k))     by poly_fun_from_ring_fun
     eval p x
   = eval (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))) x   by poly_eq_poly_sum
   = rsum (GENLIST (\k. p ' k * ((eval X x) ** k)) (SUC (deg p)))     by poly_eval_poly_sum_gen_poly
   = rsum (GENLIST (\k. p ' k * (x ** k)) (SUC (deg p)))              by poly_eval_X
*)
val poly_eval_by_ring_sum = store_thm(
  "poly_eval_by_ring_sum",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==>
    (eval p x = rsum (GENLIST (\k. (p ' k) * (x ** k)) (SUC (deg p))))``,
  rpt strip_tac >>
  `rfun (\k. p ' k)` by rw[poly_coeff_ring_fun] >>
  `poly_fun ((\k. p ' k * X ** k))` by rw[poly_fun_from_ring_fun] >>
  `eval p x = eval (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))) x` by rw[GSYM poly_eq_poly_sum] >>
  rw[poly_eval_poly_sum_gen_poly, poly_eval_X]);

(* ------------------------------------------------------------------------- *)
(* More on Polynomial Evaluation by Polynomials                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly_list s ==> !p. poly p ==> poly_list (MAP (\x. peval x p) s) *)
(* Proof:
   By induction on s.
   Base case: poly_list [] ==> poly_list (MAP (\x. peval x p) [])
     Since MAP (\x. peval x p) [] = []            by MAP
       and poly_list [] is true                   by poly_list_nil
   Step case: poly_list s ==> poly_list (MAP (\x. peval x p) s) ==>
              !h. poly_list (h::s) ==> poly_list (MAP (\x. peval x p) (h::s))
     poly_list (h::s) ==> poly h /\ poly_list s   by poly_list_cons
       MAP (\x. peval x p) (h::s)
     = (peval h p):: MAP (\x. peval x p) s        by MAP
     Since poly (peval h p)                       by poly_peval_poly
       and poly_list (MAP (\x. peval x p) s)      by induction hypothesis
     hence poly_list (MAP (\x. peval x p) (h::s)) by poly_list_cons
*)
val poly_peval_poly_list = store_thm(
  "poly_peval_poly_list",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==> !p. poly p ==> poly_list (MAP (\x. peval x p) s)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: poly_list s ==> !p. poly p ==>
            (peval (poly_sum s) p = poly_sum (MAP (\x. peval x p) s)) *)
(* Proof:
   By induction on s.
   Base case: poly_list [] ==> (peval (poly_sum []) p = poly_sum (MAP (\x. peval x p) []))
     LHS = peval (poly_sum []) p
         = peval |0| p              by poly_sum_nil
         = |0|                      by poly_peval_zero
     RHS = poly_sum (MAP (\x. peval x p) [])
         = poly_sum []              by MAP
         = |0|                      by poly_sum_nil
   Step case: poly_list s ==> (peval (poly_sum s) p = poly_sum (MAP (\x. peval x p) s)) ==>
             !h. poly_list (h::s) ==> (peval (poly_sum (h::s)) p = poly_sum (MAP (\x. peval x p) (h::s)))
     Since poly_list (h::s) ==> poly h /\ poly_list s        by poly_list_cons
       and poly_list (MAP (\x. peval x p) s                  by poly_peval_poly_list
     LHS = peval (poly_sum (h::s)) p
         = peval (h + poly_sum s) p                          by poly_sum_cons
         = (peval h p) + (peval (poly_sum s) p)              by poly_peval_add
         = (peval h p) + poly_sum (MAP (\x. peval x p) s)    by induction hypothesis
         = poly_sum ((peval h p):: (MAP (\x. peval x p) s))  by poly_sum_cons
         = poly_sum (MAP (\x. peval x p) (h::s))             by MAP
         = RHS
*)
val poly_peval_poly_sum = store_thm(
  "poly_peval_poly_sum",
  ``!r:'a ring. Ring r ==> !s. poly_list s ==>
   !p. poly p ==> (peval (poly_sum s) p = poly_sum (MAP (\x. peval x p) s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[poly_peval_add, poly_peval_poly_list]);

(* Theorem: poly_fun f ==> !p. poly p ==>
            !n. peval (poly_sum (GENLIST f n)) p = poly_sum (MAP (\x. peval x p) (GENLIST f n)) *)
(* Proof:
   Since poly_list (GENLIST f n)      by poly_list_gen_from_poly_fun
   The result is true                 by poly_peval_poly_sum
*)
val poly_peval_poly_sum_gen = store_thm(
  "poly_peval_poly_sum_gen",
  ``!r:'a ring. Ring r ==> !f. poly_fun f ==> !p. poly p ==>
   !n. peval (poly_sum (GENLIST f n)) p = poly_sum (MAP (\x. peval x p) (GENLIST f n))``,
  rw[poly_list_gen_from_poly_fun, poly_peval_poly_sum]);

(* Theorem: rfun f ==> !p q. poly p /\ poly q ==>
            !n. peval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) q =
                poly_sum (GENLIST (\k. f k * ((peval p q) ** k)) n) *)
(* Proof:
   First, poly_fun (\j. f j * p ** j)                    by poly_fun_from_ring_fun
     and  poly_list (GENLIST (\k. f k * (p ** k)) n)     by poly_list_gen_from_poly_fun
    Also  (\x. peval x q) o (\k. f k * (p ** k))
        = (\k. peval (f k * (p ** k)) q)                 by o_thm, FUN_EQ_THM

      peval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) q
    = poly_sum (MAP (\x. peval x q) (GENLIST (\k. f k * (p ** k)) n))  by poly_peval_poly_sum
    = poly_sum (GENLIST ((\x. peval x q) o (\k. f k * (p ** k))) n)    by MAP_GENLIST
    = poly_sum (GENLIST (\k. peval (f k * (p ** k)) q) n)              by composition above
    = poly_sum (GENLIST (\k. f k * peval (p ** k) q) n)                by poly_peval_cmult
    = poly_sum (GENLIST (\k. f k * ((peval p q) ** k)) n)              by poly_peval_exp
*)
val poly_peval_poly_sum_gen_poly = store_thm(
  "poly_peval_poly_sum_gen_poly",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !p q. poly p /\ poly q ==>
   !n. peval (poly_sum (GENLIST (\k. f k * (p ** k)) n)) q =
       poly_sum (GENLIST (\k. f k * ((peval p q) ** k)) n)``,
  rpt strip_tac >>
  `!x. f x IN R` by metis_tac[ring_fun_def] >>
  `poly_fun (\j. f j * p ** j)` by rw[poly_fun_from_ring_fun] >>
  `poly_list (GENLIST (\k. f k * (p ** k)) n)` by rw[poly_list_gen_from_poly_fun] >>
  `(\x. peval x q) o (\k. f k * (p ** k)) = (\k. peval (f k * (p ** k)) q)` by rw[FUN_EQ_THM] >>
  rw[poly_peval_poly_sum, MAP_GENLIST, poly_peval_cmult, poly_peval_exp]);

(* Theorem: poly p /\ poly q ==>
            (peval p q = poly_sum (GENLIST (\k. p ' k * (q ** k)) (SUC (deg p)))) *)
(* Proof:
   Since rfun (\k. p ' k)                    by poly_coeff_ring_fun
      so poly_fun ((\k. p ' k * X ** k))     by poly_fun_from_ring_fun
     peval p q
   = peval (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))) q     by poly_eq_poly_sum
   = poly_sum (GENLIST (\k. p ' k * ((peval X q) ** k)) (SUC (deg p)))   by poly_peval_poly_sum_gen_poly
   = poly_sum (GENLIST (\k. p ' k * (q ** k)) (SUC (deg p)))             by poly_peval_X
*)
val poly_peval_by_poly_sum = store_thm(
  "poly_peval_by_poly_sum",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. poly p /\ poly q ==>
    (peval p q = poly_sum (GENLIST (\k. (p ' k) * (q ** k)) (SUC (deg p))))``,
  rpt strip_tac >>
  `rfun (\k. p ' k)` by rw[poly_coeff_ring_fun] >>
  `poly_fun ((\k. p ' k * X ** k))` by rw[poly_fun_from_ring_fun] >>
  `peval p q = peval (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))) q` by rw[GSYM poly_eq_poly_sum] >>
  rw[poly_peval_poly_sum_gen_poly, poly_peval_X]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Sums of Distinct Degrees                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: A sum of polynomials of distinct degrees cannot be zero.
   Indeed, if a poly_list s has poly all of different degrees,
   then deg (poly_sum s) = MAX_LIST (MAP deg s)
*)

(* Theorem: Ring r ==> !s. poly_list s /\
            ALL_DISTINCT (FILTER (\p. p <> |0|) s) ==> (deg (poly_sum s) = MAX_LIST (MAP deg s)) *)
(* Proof:
   By induction on s.
   Base: deg (poly_sum []) = MAX_LIST (MAP deg [])
       LHS = deg (poly_sum [])
           = deg |0|                   by poly_sum_nil
           = 0                         by poly_deg_zero
       RHS = MAX_LIST (MAP deg [])
           = MAX_LIST []               by MAP
           = 0                         by MAX_LIST_NIL
   Step: poly_list s /\ ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg s)) ==>
         (deg (poly_sum s) = MAX_LIST (MAP deg s)) ==>
         !h. poly_list (h::s) /\ ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (h::s))) ==>
          (deg (poly_sum (h::s)) = MAX_LIST (MAP deg (h::s)))
       Let P = \x. x <> 0.
       Then P (deg h) = deg h <> 0     by predicate
       If deg h <> 0,
          If s = [],
              deg (poly_sum [h])
            = deg h                    by poly_sum_const
              MAX_LIST (MAP deg [h])
            = MAX_LIST [deg h]         by MAP
            = deg h                    by MAX_LIST_SING
          If s <> [],
          Then MAP deg s <> []         by MAP_EQ_NIL
          Then FILTER P (MAP deg (h::s))
             = FILTER P (deg h:: MAP deg s)    by MAP
             = deg h::FILTER P (MAP deg s)     by FILTER, P (deg h) = T.
           and ALL_DISTINCT (FILTER P (MAP deg (h::s)))
             = ALL_DISTINCT (deg h::FILTER P (MAP deg s))    by above
           ==> ~MEM (deg h) (FILTER P (MAP deg s)) /\
               ALL_DISTINCT (FILTER P (MAP deg s))           by ALL_DISTINCT
          Also poly_list (h::s)
           ==> poly h /\ poly_list s              by poly_list_cons
           Now ~MEM (deg h) (FILTER P (MAP deg s))
           ==> ~MEM (deg h) (MAP deg s)           by MEM_FILTER, P (deg h) = T
           ==> deg h <> MAX_LIST (MAP deg s)      by MAX_LIST_MEM
            or deg h <> deg (poly_sum s)          by induction hypothesis
          Note poly (poly_sum s)                  by poly_sum_poly
          If deg h < deg (poly_sum s),
               deg (poly_sum (h::s))
             = deg (h + poly_sum s)               by poly_sum_cons
             = deg (poly_sum s)                   by poly_deg_add_less
               MAX_LIST (MAP deg (h::s)))
             = MAX_LIST (deg h :: MAP deg s)      by MAP
             = MAX (deg h) (MAX_LIST (MPA deg s)) by MAX_LIST_CONS
             = MAX (deg h) (deg (poly_sum s))     by induction hypothesis
             = deg (poly_sum s)                   by MAX_DEF
          If deg (poly_sum s) < deg h
               deg (poly_sum (h::s))
             = deg (h + poly_sum s)               by poly_sum_cons
             = deg h                              by poly_deg_add_less_comm
               MAX_LIST (MAP deg (h::s)))
             = MAX_LIST (deg h :: MAP deg s)      by MAP
             = MAX (deg h) (MAX_LIST (MAP deg s)) by MAX_LIST_CONS
             = MAX (deg h) (deg (poly_sum s))     by induction hypothesis
             = deg h                              by MAX_DEF
       If deg h = 0,
               deg (poly_sum (h::s))
             = deg (h + poly_sum s)               by poly_sum_cons
             = deg (poly_sum s)                   by poly_deg_add_deg_zero, deg h = 0
               MAX_LIST (MAP deg (h::s))
             = MAX_LIST (0 :: (MAP deg s))        by MAP, deg h = 0
             = MAX 0 (MAX_LIST (MAP deg s))       by MAX_LIST_CONS
             = MAX_LIST (MAP deg s)               by MAX_0
             = deg (poly_sum s)                   by induction hypothesis
*)
val poly_sum_deg = store_thm(
  "poly_sum_deg",
  ``!r:'a ring. Ring r ==> !s. poly_list s /\ ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg s)) ==>
        (deg (poly_sum s) = MAX_LIST (MAP deg s))``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[] >| [
    `poly (poly_sum s)` by rw[] >>
    Cases_on `s = []` >-
    rw[] >>
    `MAP deg s <> []` by rw[MAP_EQ_NIL] >>
    qabbrev_tac `P = \x. x <> 0` >>
    qabbrev_tac `t = poly_sum s` >>
    `P (deg h) = T` by rw[Abbr`P`] >>
    `~MEM (deg h) (MAP deg s)` by metis_tac[MEM_FILTER] >>
    `deg t = MAX_LIST (MAP deg s)` by rw[Abbr`P`] >>
    `deg h <> deg t` by metis_tac[MAX_LIST_MEM] >>
    Cases_on `deg h < deg t` >| [
      `deg (h + t) = deg t` by rw[poly_deg_add_less] >>
      metis_tac[MAX_DEF],
      `deg t < deg h` by decide_tac >>
      `deg (h + t) = deg h` by rw[poly_deg_add_less_comm] >>
      metis_tac[MAX_DEF]
    ],
    `deg (h + poly_sum s) = deg (poly_sum s)` by rw[poly_deg_add_deg_zero] >>
    rw[]
  ]);

(* Theorem: Field r ==> !p. poly p /\ 0 < deg p ==> !f. rfun f ==>
            ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) n))) *)
(* Proof:
   By induction on n.
   Base: ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) 0)))
          ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) 0)))
      <=> ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg []))     by GENLIST_0
      <=> ALL_DISTINCT (FILTER (\x. x <> 0) [])               by MAP
      <=> ALL_DISTINCT []                                     by FILTER
      <=> T                                                   by ALL_DISTINCT
   Step: ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) n))) ==>
         ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) (SUC n))))
      Let g = \j. f j * p ** j.
      Then g n = f n * p ** n
          ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST g (SUC n))))
      <=> ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (SNOC (g n) (GENLIST g n))))        by GENLIST
      <=> ALL_DISTINCT (FILTER (\x. x <> 0) (SNOC (deg (g n)) (MAP deg (GENLIST g n))))  by MAP_SNOC
      If deg (g n) <> 0,
          ALL_DISTINCT (FILTER (\x. x <> 0) (SNOC (deg (g n)) (MAP deg (GENLIST g n))))
      <=> ALL_DISTINCT (SNOC (deg (g n)) (FILTER (\x. x <> 0) (MAP deg (GENLIST g n))))  by FILTER_SNOC
      <=> ~MEM (deg (g n)) FILTER (\x. x <> 0) (MAP deg (GENLIST g n))) /\
          ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST g n))))          by ALL_DISTINCT_SNOC
      <=> ~MEM (deg (g n)) FILTER (\x. x <> 0) (MAP deg (GENLIST g n))) /\ T   by induction hypothesis
      <=> ~MEM (deg (g n)) (MAP deg (GENLIST g n)))           by MEM_FILTER, deg (g n <> 0)
      <=> !y. (deg (g n) = deg y) /\ ~MEM y (GENLIST g n)     by MEM_MAP
      <=> !y. (deg (g n) = deg y) /\ !j. j < n /\ (y <> g j)  by MEM_GENLIST
      By contradiction, suppose y = g j = f j * p ** j.
      Since f n IN R /\ f j IN R            by ring_fun_def
      Given deg (g n) = deg (f n * p ** n) <> 0, and deg (g n) = deg y
         so f n <> #0 /\ f j <> #0          by poly_cmult_lzero, poly_deg_zero
        But deg (g n) = deg (p ** n)        by poly_field_deg_cmult
                      = n * deg p           by poly_field_deg_exp
        and deg y = deg (p ** j)            by poly_field_deg_cmult
                  = j * deg p               by poly_field_deg_exp
       With deg (g n) = deg y,
            n * deg p = j * deg p           by above
                    n = j                   by EQ_MULT_RCANCEL, deg p <> 0
       This contradicts j < n.

      If deg (g n) = 0,
          ALL_DISTINCT (FILTER (\x. x <> 0) (SNOC (deg (g n)) (MAP deg (GENLIST g n))))
      <=> ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST g n)))  by FILTER_SNOC
      <=> T                                                           by induction hypothesis
*)
val poly_genlist_deg_distinct = store_thm(
  "poly_genlist_deg_distinct",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p ==> !f. rfun f ==>
   !n. ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg (GENLIST (\j. f j * p ** j) n)))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[GENLIST, MAP_SNOC, FILTER_SNOC, ALL_DISTINCT_SNOC, MEM_FILTER] >>
  rw[MEM_MAP, MEM_GENLIST] >>
  spose_not_then strip_assume_tac >>
  `Ring r /\ poly (p ** n) /\ poly (p ** j)` by rw[] >>
  `f n IN R /\ f j IN R` by metis_tac[ring_fun_def] >>
  `f n <> #0 /\ f j <> #0` by metis_tac[poly_deg_zero, poly_cmult_lzero] >>
  `deg p <> 0` by decide_tac >>
  `n = j` by metis_tac[poly_field_deg_cmult, poly_field_deg_exp, EQ_MULT_RCANCEL] >>
  decide_tac);

(* Theorem: Field r ==> !f. rfun f ==> !p. poly p /\ 0 < deg p ==>
            !n. (poly_sum (GENLIST (\j. f j * p ** j) n) = |0|) <=> (!j. j < n ==> (f j = #0)) *)
(* Proof:
   Let s = GENLIST (\j. f j * p ** j) n.
   Then poly_list s                                      by poly_list_gen_from_ring_fun
    and ALL_DISTINCT (FILTER (\x. x <> 0) (MAP deg s))   by poly_genlist_deg_distinct
    ==> deg (poly_sum s) = MAX_LIST (MAP deg s)          by poly_sum_deg

   If part: (poly_sum s = |0|) ==> !j. j < n ==> (f j = #0)
      Claim: !k. 0 < k /\ k < n ==> (f k = #0)
      Proof: Note MAX_LIST (MAP deg s)
                = deg (poly_sum s)             by above
                = deg |0| = 0                  by poly_deg_zero
             ==> EVERY (\x. x = 0) (MAP deg s) by MAX_LIST_EQ_0
             Let P = \x. x = 0.
             Then EVERY (\p. P (deg p)) s      by EVERY_MAP
               or EVERY (\p. deg p = 0) s      by applying P
             Let Q = \p. deg p = 0, g = \j. f j * p ** j
             Then Q (g k)                      by EVERY_GENLIST, k < n
               or deg (f k * p ** k) = 0       by apply Q and g
             By contradiction, suppose f k <> #0.
             Now f k IN R                      by ring_fun_def
                 deg (f k * p ** k)
               = deg (p ** k)                  by poly_field_deg_cmult, f k <> #0
               = k * deg p                     by poly_field_deg_exp
               <> 0                            by MULT_EQ_0, 0 < k, 0 < deg p

             This contradicts  deg (f k * p ** k) = 0.

      Thus !k. 0 < k /\ k < n ==> (f k = #0)             by claim
        or !k. 0 < k /\ k < n ==> (f k * p ** k = |0|)   by poly_cmult_lzero, [1]
      By contradiction, suppose f j <> #0.
      Then j = 0, since any 0 < j < n gives f j = #0     by [1] above
      Thus 0 < n, since j < n, or n = SUC m for some m   by num_CASES
      From [1],
           !k. 0 < k /\ k <= m ==> (f k * p ** k = |0|)  by LESS_EQ_IFF_LESS_SUC
       ==> GENLIST ((\j. f j * p ** j) o SUC) m
         = GENLIST (K |0|) m                             by GENLIST_K_RANGE, [2]
        poly_sum s
      = poly_sum (GENLIST (\j. f j * p ** j) (SUC m))    by n = SUC m
      = f 0 * p ** 0 + poly_sum (GENLIST ((\j. f j * p ** j) o SUC) m)  by poly_sum_decompose_first
      = f 0 * |1| + poly_sum (GENLIST (K |0|) m)         by [2] above
      = f 0 * |1| + |m| * |0|                            by poly_sum_gen_const
      = f 0 * |1| + |0|                                  by poly_cmult_zero
      = f 0 * |1|                                        by poly_add_rzero
      But poly_sum s = |0|, so f 0 = #0,                 by poly_field_cmult_eq_zero
      This contradicts f j <> #0.

   Only-if part: !j. j < n ==> (f j = #0) ==> poly_sum s = |0|
      That is, !j. j < n ==> (f j * p ** j = |0|)        by poly_cmult_lzero
       ==> GENLIST (\j. f j * p ** j) n
         = GENLIST (K |0|) n                             by GENLIST_K_LESS, [3]
        poly_sum s
      = poly_sum (GENLIST (\j. f j * p ** j) n)
      = poly_sum (GENLIST (K |0|) n)                     by [3] above
      = |n| * |0|                                        by poly_sum_gen_const
      = |0|                                              by poly_cmult_zero
*)
val poly_sum_gen_eq_zero = store_thm(
  "poly_sum_gen_eq_zero",
  ``!r:'a field. Field r ==> !f. rfun f ==> !p. poly p /\ 0 < deg p ==>
   !n. (poly_sum (GENLIST (\j. f j * p ** j) n) = |0|) <=> (!j. j < n ==> (f j = #0))``,
  rpt strip_tac >>
  qabbrev_tac `s = GENLIST (\j. f j * p ** j) n` >>
  `deg (poly_sum s) = MAX_LIST (MAP deg s)` by
  ((irule poly_sum_deg >> rpt conj_tac) >-
  rw[poly_genlist_deg_distinct, Abbr`s`] >-
  rw[] >>
  rw[poly_list_gen_from_ring_fun, Abbr`s`]
  ) >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `!k. 0 < k /\ k < n ==> (f k = #0)` by
  (rpt strip_tac >>
    `MAX_LIST (MAP deg s) = 0` by metis_tac[poly_deg_zero] >>
    `EVERY (\x. x = 0) (MAP deg s)` by rw[GSYM MAX_LIST_EQ_0] >>
    qabbrev_tac `P = \x. x = 0` >>
    `EVERY (\p. P (deg p)) s` by metis_tac[EVERY_MAP] >>
    `EVERY (\p. deg p = 0) s` by fs[] >>
    qabbrev_tac `Q = \p. deg p = 0` >>
    qabbrev_tac `g = \j. f j * p ** j` >>
    `Q (g k)` by metis_tac[EVERY_GENLIST] >>
    `deg (f k * p ** k) = 0` by fs[] >>
    spose_not_then strip_assume_tac >>
    `f k IN R` by metis_tac[ring_fun_def] >>
    `deg (f k * p ** k) = deg (p ** k)` by rw[GSYM poly_field_deg_cmult] >>
    `_ = k * deg p` by rw[poly_field_deg_exp] >>
    metis_tac[MULT_EQ_0, NOT_ZERO]) >>
    `!k. 0 < k /\ k < n ==> (f k * p ** k = |0|)` by rw[] >>
    spose_not_then strip_assume_tac >>
    `j = 0` by metis_tac[NOT_ZERO] >>
    `n <> 0` by decide_tac >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    qabbrev_tac `g = \j. f j * p ** j` >>
    `g 0 = f 0 * |1|` by rw[Abbr`g`] >>
    `f 0 IN R` by metis_tac[ring_fun_def] >>
    `!k. 0 < k /\ k <= m ==> (f k * p ** k = |0|)` by metis_tac[LESS_EQ_IFF_LESS_SUC] >>
    `GENLIST (g o SUC) m = GENLIST (K |0|) m` by rw[GENLIST_K_RANGE, Abbr`g`] >>
    `poly_sum s = poly_sum (GENLIST g (SUC m))` by rw[Abbr`s`] >>
    `_ = g 0 + poly_sum (GENLIST (g o SUC) m)` by rw_tac std_ss[poly_sum_decompose_first] >>
    `_ = f 0 * |1| + poly_sum (GENLIST (K |0|) m)` by metis_tac[] >>
    `_ = f 0 * |1|` by rw[poly_sum_gen_const] >>
    `poly |1| /\ |1| <> |0|` by rw[] >>
    `f 0 = #0` by metis_tac[poly_field_cmult_eq_zero] >>
    metis_tac[],
    `!j. j < n ==> (f j * p ** j = |0|)` by rw[] >>
    `s = GENLIST (K |0|) n` by rw[GENLIST_K_LESS, Abbr`s`] >>
    `poly_sum s = poly_sum (GENLIST (K |0|) n)` by metis_tac[] >>
    rw[poly_sum_gen_const]
  ]);

(* This is a milestone theorem. *)
(* However, proof looks very ugly! Especially the part of shifting to 0 < j < n, then argue f 0 = #0. *)

(* Theorem: Field r ==>
            !p q. poly p /\ poly q /\ 0 < deg q ==> ((peval p q = |0|) <=> (p = |0|)) *)
(* Proof:
   If part: peval p q = |0| ==> p = |0|
      By contradiction, suppose p <> |0|.
      Let s = GENLIST (\k. p ' k * q ** k) (SUC (deg p)), n = deg p
      Note peval p q = |0| ==> poly_sum s = |0|  by poly_peval_by_poly_sum
       and rfun (\k. p ' k)                      by poly_coeff_ring_fun
       ==> !j. j < SUC n ==> (p ' j = #0)        by poly_sum_gen_eq_zero, 0 < deg q. [1]
        or !j. j <= n ==> (p ' j = #0)           by LESS_EQ_IFF_LESS_SUC
       But n = deg p                             by notation
        so !j. n < j ==>  (p ' j = #0)           by poly_coeff_nonzero, p <> |0|. [2]
      Thus !j. p ' j = #0                        by NOT_LESS, [1], [2]
      Hence p = |0|                              by poly_coeff_eq_zero
      This contradicts p <> |0|.

   Only-if part: peval |0| q = |0|
      True by poly_peval_zero.
*)
val poly_peval_eq_zero = store_thm(
  "poly_peval_eq_zero",
  ``!r:'a field. Field r ==>
   !p q. poly p /\ poly q /\ 0 < deg q ==> ((peval p q = |0|) <=> (p = |0|))``,
  rw_tac std_ss[poly_peval_zero, EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `n = deg p` >>
  qabbrev_tac `s = GENLIST (\k. p ' k * q ** k) (SUC n)` >>
  `poly_sum s = |0|` by metis_tac[poly_peval_by_poly_sum] >>
  `rfun (\k. p ' k)` by rw[poly_coeff_ring_fun] >>
  `!j. j <= n ==> (p ' j = #0)` by metis_tac[poly_sum_gen_eq_zero, LESS_EQ_IFF_LESS_SUC] >>
  `!j. n < j ==> (p ' j = #0)` by rw[poly_coeff_nonzero, Abbr`n`] >>
  `!j. p ' j = #0` by metis_tac[NOT_LESS] >>
  metis_tac[poly_coeff_eq_zero]);

(* This is the key for the next theorem. *)

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ poly t /\ 0 < deg t ==>
            ((peval p t = peval q t) <=> (p = q)) *)
(* Proof:
   If part: peval p t = peval q t ==> p = q
      Given peval p t = peval q t,
        peval (p - q) t
      = peval p t - peval q t       by poly_peval_sub
      = |0|                         by poly_sub_eq
      Since poly (p - q)            by poly_sub_poly
        ==> p - q = |0|             by poly_peval_eq_zero, 0 < deg t
        ==> p = q                   by poly_sub_eq_zero

   Only-if part: p = q ==> peval p t = peval q t
      This is trivially true.
*)
val poly_peval_eq = store_thm(
  "poly_peval_eq",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t /\ 0 < deg t ==>
   ((peval p t = peval q t) <=> (p = q))``,
  rw[EQ_IMP_THM] >>
  `Ring r /\ poly (p - q)` by rw[] >>
  `peval (p - q) t = |0|` by rw[poly_peval_sub] >>
  `p - q = |0|` by metis_tac[poly_peval_eq_zero] >>
  metis_tac[poly_sub_eq_zero]);

(* This is a major milestone theorem. *)

(* Theorem: Field r ==> !s. (!p. p IN s ==> poly p) ==>
            !q. poly q /\ 0 < deg q ==> INJ (\p. peval p q) s univ(:'a poly) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) p IN s ==> peval p q IN univ(:'a poly)
       Note poly p                        by p IN s, poly_set notation
         so poly (peval p q)              by poly_peval_poly
         or peval p q IN univ(:'a poly)   by IN_UNIV
   (2) p IN s /\ p' IN s /\ peval p q = peval p' q ==> p = p'
       True by poly_peval_eq, poly q /\ 0 < deg q.
*)
val poly_peval_poly_set_inj = store_thm(
  "poly_peval_poly_set_inj",
  ``!r:'a field. Field r ==> !s. (!p. p IN s ==> poly p) ==>
   !q. poly q /\ 0 < deg q ==> INJ (\p. peval p q) s univ(:'a poly)``,
  rw[INJ_DEF] >>
  metis_tac[poly_peval_eq]);

(* Note: If s = image of factor, can use poly_peval_factor_map_inj: just Ring r, and #1 <> #0. *)

(* ------------------------------------------------------------------------- *)
(* Polynomial as Direct GENLIST                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GENLIST f (SUC n) <> |0| *)
(* Proof:
   Since LENGTH (GENLIST f (SUC n))
       = SUC n                       by LENGTH_GENLIST
       <> 0                          by NOT_SUC
      so GENLIST f (SUC n) <> []     by LENGTH_NIL
      or                   <> |0|    by poly_zero
*)
val poly_genlist_nonzero = store_thm(
  "poly_genlist_nonzero",
  ``!r:'a ring. !f n. GENLIST f (SUC n) <> |0|``,
  metis_tac[LENGTH_GENLIST, LENGTH_NIL, poly_zero, numTheory.NOT_SUC]);

(* Theorem: deg (GENLIST f (SUC n)) = n *)
(* Proof:
   Let p = GENLIST f (SUC n).
   Since p <> |0|           by poly_genlist_nonzero
      so deg p
       = PRE (LENGTH p)     by poly_deg_nonzero
       = PRE (SUC n)        by LENGTH_GENLIST
       = n                  by PRE
*)
val poly_genlist_deg = store_thm(
  "poly_genlist_deg",
  ``!r:'a ring. !f n. deg (GENLIST f (SUC n)) = n``,
  rw[poly_genlist_nonzero, poly_deg_nonzero]);

(* Theorem: lead (GENLIST f (SUC n)) = f n *)
(* Proof:
   Let p = GENLIST f (SUC n).
   Since p <> |0|           by poly_genlist_nonzero
      so lead p
       = LAST p             by poly_lead_alt
       = f n                by GENLIST_LAST
*)
val poly_genlist_lead = store_thm(
  "poly_genlist_lead",
  ``!r:'a ring. !f n. lead (GENLIST f (SUC n)) = f n``,
  rw[poly_genlist_nonzero, poly_lead_alt, GENLIST_LAST]);

(* Theorem: (GENLIST f (SUC n)) ' k = if n < k then #0 else f k *)
(* Proof:
   Let p = GENLIST f (SUC n).
   Since p <> |0|           by poly_genlist_nonzero
     and deg p = n          by poly_genlist_deg
     If n < k,
        p ' k = #0          by poly_coeff_nonzero
     If ~(n < k),
        Then k <= n, or k < SUC n.
         p ' k
       = EL k p             by poly_coeff_nonzero
       = f k                by EL_GENLIST, k < SUC n
*)
val poly_genlist_coeff = store_thm(
  "poly_genlist_coeff",
  ``!r:'a ring. !f n k. (GENLIST f (SUC n)) ' k = if n < k then #0 else f k``,
  rw[poly_genlist_nonzero, poly_genlist_deg, poly_coeff_nonzero, EL_GENLIST]);

(* Theorem: Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
            poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) <> |0| *)
(* Proof:
   Let s = GENLIST (\j. f j * X ** j) (SUC n).
   Since lead (poly_sum s) = f n   by poly_sum_gen_lead
                          <> #0    by given
        so (poly_sum s) <> |0|     by poly_lead_zero
*)
val poly_sum_nonzero = store_thm(
  "poly_sum_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
    poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) <> |0|``,
  metis_tac[poly_sum_gen_lead, poly_lead_zero]);

(* Theorem: Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
            !k. (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) ' k = if n < k then #0 else f k *)
(* Proof:
   Let p = GENLIST f (SUC n).
    Then p <> |0|     by poly_genlist_nonzero
     Now poly p       by poly_genlist
     and deg p = n    by poly_genlist_deg

   If n < k,
      Let s = GENLIST (\j. f j * X ** j) (SUC n).
      Note poly_list s               by poly_list_gen_from_ring_fun
        so poly (poly_sum s)         by poly_sum_poly
       and deg (poly_sum s) = n      by poly_sum_gen_deg
       and poly_sum s <> |0|         by poly_sum_nonzero
        so (poly_sum s) ' k = #0     by poly_coeff_nonzero

   If ~(n < k),
      Then k <= n.
      Since LENGTH p = SUC n                         by LENGTH_GENLIST
         so !j. j < SUC n ==> (p ' j = EL j p)       by poly_coeff_nonzero_alt, p <> |0|
         so !j. j < SUC n ==> (p ' j = f j)          by EL_GENLIST

      Hence poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k
          = poly_sum (GENLIST (\j. p ' j * X ** j) (SUC n)) ' k  by GENLIST_EL
          = p ' k                                                by poly_eq_poly_sum
          = f k                                                  by poly_genlist_coeff
*)
val poly_sum_gen_coeff = store_thm(
  "poly_sum_gen_coeff",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
   !k. (poly_sum (GENLIST (\j. f j * X ** j) (SUC n))) ' k = if n < k then #0 else f k``,
  rpt strip_tac >>
  qabbrev_tac `p = GENLIST f (SUC n)` >>
  `p <> |0|` by rw[poly_genlist_nonzero, Abbr`p`] >>
  `poly p` by metis_tac[poly_genlist] >>
  `deg p = n` by rw[poly_genlist_deg, Abbr`p`] >>
  Cases_on `n < k` >| [
    qabbrev_tac `s = GENLIST (\j. f j * X ** j) (SUC n)` >>
    `poly_list s` by rw[poly_list_gen_from_ring_fun, Abbr`s`] >>
    `poly (poly_sum s)` by rw[poly_sum_poly] >>
    `deg (poly_sum s) = n` by rw[poly_sum_gen_deg, Abbr`s`] >>
    `(poly_sum s) <> |0|` by metis_tac[poly_sum_nonzero] >>
    rw[poly_coeff_nonzero],
    `k <= n` by decide_tac >>
    `!j. j < SUC n ==> (p ' j = f j)` by rw[poly_coeff_nonzero_alt, Abbr`p`] >>
    `GENLIST (\j. p ' j * X ** j) (SUC n) = GENLIST (\j. f j * X ** j) (SUC n)` by rw[GENLIST_EL] >>
    metis_tac[poly_eq_poly_sum, poly_genlist_coeff]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
            (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) = GENLIST f (SUC n)) *)
(* Proof:
   Let p = poly_sum (GENLIST (\j. f j * X ** j) (SUC n))
       q = GENLIST f (SUC n))
   Note poly_list (GENLIST (\j. f j * X ** j) (SUC n))   by poly_list_gen_from_ring_fun
     so poly p                                 by poly_sum_poly
    and p ' k = if n < k then #0 else f k      by poly_sum_gen_coeff
   Also poly q                                 by poly_genlist
     and q ' k = if n < k then #0 else f k     by poly_genlist_coeff
    Thus p = q                                 by poly_coeff_eq_poly_eq
*)
val poly_sum_gen_is_genlist = store_thm(
  "poly_sum_gen_is_genlist",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !f n. rfun f /\ f n <> #0 ==>
    (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) = GENLIST f (SUC n))``,
  rpt strip_tac >>
  qabbrev_tac `p = poly_sum (GENLIST (\j. f j * X ** j) (SUC n))` >>
  qabbrev_tac `q = GENLIST f (SUC n)` >>
  `poly p` by rw[poly_sum_poly, poly_list_gen_from_ring_fun, Abbr`p`] >>
  `!k. p ' k = if n < k then #0 else f k` by rw[poly_sum_gen_coeff, Abbr`p`] >>
  `poly q` by rw[poly_genlist, Abbr`q`] >>
  `!k. q ' k = if n < k then #0 else f k` by rw[poly_genlist_coeff, Abbr`q`] >>
  metis_tac[poly_coeff_eq_poly_eq]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Thoughts on Polynomial SUM by GENLIST coefficient                         *)
(* ------------------------------------------------------------------------- *)

(* We have:
> poly_coeff_sum_genlist;
val it = |- !r. Ring r /\ #1 <> #0 ==> !f n k. rfun f /\ k < SUC n ==>
       (poly_sum (GENLIST (\j. f j * X ** j) (SUC n)) ' k = f k): thm

   We want:
   poly_sum (GENLIST (\j. f j * (X ** m) ** j) (SUC n)) ' k = f k
*)

(* How to prove this theorem?
-- try:  poly_sum equal ==> list equal
--       list equal ==> elements equal
--       elements equal ==> f1 k * p ** k = f2 k * p ** k
--       hopefully this gives    f1 k = f2 k
But the first step is very unlikely: list equal ==> poly_sum equal, but not the other direction.
The only other way I can think of is this:
Treat (poly_sum (GENLIST (\k. (f1 k) * p ** k) n) as a polynomial in p.
Then ((f1 k) * p ** k) is the k-th coefficient of this 'super' polynomial.
And equating coefficients of the 'super' polynomial gives: (f1 k = f2 k).

For 'normal' polynomial, we have poly_coeff_eq_poly_eq
|- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p = q) <=> !k. p ' k = q ' k)
Since poly = 'a list, this is effectively:  list1 = list2 <=> EL (list1) k = EL (list2) k.

Now  p = poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))      by poly_eq_poly_sum
and  poly (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p))))   by poly_sum_poly
 so  p ' k = (poly_sum (GENLIST (\k. p ' k * X ** k) (SUC (deg p)))) ' k   by above

What is the effect of replacing X by X ** m ?
Let   p = 1 + 2X + 3X**2,       p ' 0 = 1, p ' 1 = 2, p ' 2 = 3.
Then  q = 1 + 2X**2 + 3X**4,    q ' 0 = 1, q ' 1 = 0, q ' 2 = 2, q ' 3 = 0, q ' 4 = 3.
That is q ' k = if k MOD 2 = 0 then p ' (k DIV 2) else 0.
or   (peval p (X ** m)) ' k  = if (k MOD m = 0) then p ' (k DIV m) else #0.

  poly_sum (GENLIST (\k. (f k) * (X ** 2) ** k) 3)
= poly_sum [(f 0) * (X ** 2) ** 0);
            (f 1) * (X ** 2) ** 1);
            (f 2) * (X ** 2) ** 2)]
= poly_sum [(f 0) * X ** (2*0); (f 1) * X ** (2*1); (f 2) * X ** (2*2)]
= GENLIST (\k. if (k MOD 2 = 0) then (f (k DIV 2)) else #0) [0; 1; 2; 3; 4]

This line of thought leads to poly_dilate in polyRing,
but that is not used now as we have above: poly_sum_gen_is_genlist

*)

(* ------------------------------------------------------------------------- *)
(* Investigation of Symbolic Polynomial                                      *)
(* ------------------------------------------------------------------------- *)

(* Try to capture: PolyRing (PolyRing r) *)

(* Theorem: Ring r /\ poly p ==> (p + |1|) ** 2 = p ** 2 + ###2 * p + |1| *)
(* Proof:
   Since  Ring r ==> Ring (PolyRing r)      by poly_add_mult_ring
     and  poly |1|                          by poly_one_poly
   Hence  p, |1| IN (PolyRing r).carrier    by poly_ring_property
    (p + |1|) ** 2
   = p ** 2 + ###2 * (p * |1|) + |1| ** 2   by ring_binomial_2
   = p ** 2 + ###2 * p + |1| ** 2           by poly_mult_rone
   = p ** 2 + ###2 * p + |1|                by poly_one_exp
*)
val poly_binomial_2_p = store_thm(
  "poly_binomial_2_p",
  ``!(r:'a ring) p. Ring r /\ poly p ==> ((p + |1|) ** 2 = p ** 2 + ###2 * p + |1|)``,
  rw[poly_add_mult_ring, ring_binomial_2, GSYM poly_ring_property]);

(* Theorem: Ring r /\ #1 <> #0 ==> (X + |1|) ** 2 = X ** 2 + ###2 * X + |1| *)
(* Proof: by poly_binomial_2_p, poly_X. *)
val poly_binomial_2_X = store_thm(
  "poly_binomial_2_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> ((X + |1|) ** 2 = X ** 2 + ###2 * X + |1|)``,
  rw_tac std_ss[poly_binomial_2_p, poly_X]);

(*
Surely, poly_binomial_2_p ==> poly_binomial_2_X
But how to show: poly_binomial_2_X ==> poly_binomial_2_p, in General?
Something like:  P |X| ==> !x. poly x ==> P x ?
This old investigation is solved in this proper script.
*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Dilation                                                       *)
(* ------------------------------------------------------------------------- *)

(* Note: This polynomial dilation is intended to be applied later, to show:
         peval p (X ** (SUC n)) = pdilate n p
*)

(* Define polynomial dilate using list DILATE *)
val poly_dilate_def = Define`
    poly_dilate (r:'a ring) n (p:'a poly) = DILATE #0 0 n p
`;
(* overload polynomial dilation *)
val _ = overload_on("pdilate", ``poly_dilate r``);
(* > poly_dilate_def;
val it = |- !r n p. pdilate n p = DILATE #0 0 n p: thm
*)

(* export simple definition *)
val _ = export_rewrites["poly_dilate_def"];

(* Theorem: pdilate n |0| = |0| *)
(* Proof:
     pdilate n |0|
   = DILATE #0 0 n |0|   by poly_dilate_def
   = DILATE #0 0 n []    by poly_zero
   = [] = |0|            by DILATE_NIL
*)
val poly_dilate_zero = store_thm(
  "poly_dilate_zero",
  ``!r:'a ring. !n. pdilate n |0| = |0|``,
  rw[]);

(* Theorem: pdilate 0 p = p *)
(* Proof:
     pdilate 0 p
   = DILATE #0 0 0 p     by poly_dilate_def
   = p                   by DILATE_0_0
*)
val poly_dilate_0 = store_thm(
  "poly_dilate_0",
  ``!r:'a ring. !p. pdilate 0 p = p``,
  rw[DILATE_0_0]);

(* Theorem: pdilate n p = |0| <=> p = |0| *)
(* Proof:
       pdilate n p = |0|
   <=> DILATE #0 0 n p = []     by poly_dilate_def, poly_zero
   <=> p = []                   by DILATE_0_EQ_NIL
   <=> p = |0|                  by poly_zero
*)
val poly_dilate_eq_zero = store_thm(
  "poly_dilate_eq_zero",
  ``!r:'a ring. !p n. (pdilate n p = |0|) <=> (p = |0|)``,
  rw[DILATE_0_EQ_NIL]);

(* Theorem: deg (pdilate n p) = if n = 0 then deg p else if p = |0| then 0 else (SUC n) * deg p *)
(* Proof:
   If n = 0,
     deg (pdilate 0 p)
   = deg p             by poly_dilate_0
   If n <> 0,
      If p = |0|,
        deg (pdilate n |0|)
      = deg |0|        by poly_dilate_zero
      = 0              by poly_deg_zero
      If p <> |0|,
        deg (pdilate n p)
      = deg (DILATE #0 0 n p)               by poly_dilate_def
      = PRE (LENGTH (DILATE #0 0 n p))      by poly_deg_def
      = PRE (SUC (SUC n * PRE (LENGTH p)))  by DILATE_0_LENGTH, p <> []
      = SUC n * PRE (LENGTH p)              by PRE
      = SUC n * deg p                       by poly_deg_def
*)
val poly_dilate_deg = store_thm(
  "poly_dilate_deg",
  ``!r:'a ring. !p n. deg (pdilate n p) = if n = 0 then deg p else if p = |0| then 0 else (SUC n) * deg p``,
  rw[DILATE_0_LENGTH, poly_deg_def, DILATE_0_EQ_NIL]);

(* Theorem: deg p <= deg (pdilate n p) *)
(* Proof:
   If p = |0|,
      Then pdilate n |0| = |0|                        by poly_dilate_zero
        so deg |0| = deg (pdilate n |0|)
   If p <> |0|,
      Then DILATE #0 0 n p <> |0|                     by DILATE_0_EQ_NIL
        so LENGTH (DILATE #0 0 n p) <> 0              by LENGTH_NIL
          LENGTH p <= LENGTH (DILATE #0 0 n p)        by DILATE_0_LENGTH_LOWER
    PRE (LENGTH p) <= PRE (LENGTH (DILATE #0 0 n p))  by INV_PRE_LESS_EQ, 0 < LENGTH (DILATE #0 0 n p)
    or       deg p <= deg (DILATE #0 0 n p)           by poly_deg_def
    or       deg p <= deg (pdilate n p)               by poly_dilate_def
*)
val poly_dilate_deg_lower = store_thm(
  "poly_dilate_deg_lower",
  ``!r:'a ring. !p n. deg p <= deg (pdilate n p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `p <> [] /\ DILATE #0 0 n p <> []` by metis_tac[DILATE_0_EQ_NIL, poly_zero] >>
  `0 < LENGTH (DILATE #0 0 n p)` by metis_tac[LENGTH_NIL, NOT_ZERO] >>
  rw[DILATE_0_LENGTH_LOWER, INV_PRE_LESS_EQ, poly_deg_def]);

(* Theorem: 0 < n ==> !p. deg (pdilate n p) <= SUC n * deg p *)
(* Proof:
   If p = |0|,
      Then deg (pdilate n |0|)
         = deg |0|                       by poly_dilate_zero
         = 0                             by poly_deg_zero
         = n * 0                         by MULT_0
         = n * deg |0|                   by poly_deg_zero
   If p <> |0|,
      Then DILATE #0 0 n p <> |0|                                      by DILATE_0_EQ_NIL
      Since 0 < SUC (SUC n * PRE (LENGTH p))                           by SUC_POS
        LENGTH (DILATE #0 0 n p) <= SUC (SUC n * PRE (LENGTH p))       by DILATE_0_LENGTH_UPPER
  PRE (LENGTH (DILATE #0 0 n p)) <= PRE (SUC (SUC n * PRE (LENGTH p))) by INV_PRE_LESS_EQ, 0 < SUC (SUC n * PRE (LENGTH p))
  PRE (LENGTH (DILATE #0 0 n p)) <= SUC n * PRE (LENGTH p)             by PRE
           deg (DILATE #0 0 n p) <= SUC n * deg p                      by poly_deg_def
               deg (pdilate n p) <= SUC n * deg p                      by poly_dilate_def
*)
val poly_dilate_deg_upper = store_thm(
  "poly_dilate_deg_upper",
  ``!r:'a ring. !n. 0 < n ==> !p. deg (pdilate n p) <= SUC n * deg p``,
  rpt strip_tac >>
  `0 < SUC (SUC n * PRE (LENGTH p))` by decide_tac >>
  `!n. PRE (SUC n) = n` by rw[] >>
  `PRE (LENGTH (DILATE #0 0 n p)) <= SUC n * PRE (LENGTH p)` by metis_tac[DILATE_0_LENGTH_UPPER, INV_PRE_LESS_EQ] >>
  rw[poly_deg_def]);

(* Theorem: (pdilate n p) ' k = if k MOD (SUC n) = 0 then p ' (k DIV (SUC n)) else #0 *)
(* Proof:
   Let m = SUC n, then 0 < m           by LESS_0
   If n = 0, m = 1                     by ONE
     LHS = (pdilate 0 p) ' k = p ' k   by poly_dilate_0
     Note k MOD 1 = 0                  by MOD_1
      and k DIV 1 = k                  by DIV_1
       so RHS = p ' k = LHS
   If n <> 0,
      If p = |0|,
        (pdilate n |0|) ' k = |0| ' k     by poly_dilate_zero
                            = #0          by poly_coeff_zero
        Then LHS = RHS.
      If p <> |0|,
        Then pdilate n p <> |0|                      by poly_dilate_eq_zero
        If k <= deg (pdilate n p),
           Then k <= m * deg p                       by poly_dilate_deg
             If k MOD m = 0, then k DIV m <= deg p   by LE_MULT_LE_DIV
           Also k <= PRE (LENGTH (pdilate n p))      by poly_deg_def
             or k <= PRE (LENGTH (DILATE #0 0 n p))  by poly_dilate_def
             or k < LENGTH (DILATE #0 0 n p)         by LESS_EQ_IFF_LESS_SUC

             (pdilate n p) ' k
           = (DILATE #0 0 n p) ' k                        by poly_dilate_def
           = EL k (DILATE #0 0 n p)                       by poly_coeff_nonzero_alt
           = if k MOD m = 0 then EL (k DIV m) p else #0   by DILATE_0_EL, k < LENGTH (DILATE #0 0 n p)
           = if k MOD m = 0 then p ' (k DIV m) else #0    by poly_coeff_nonzero, k DIV m <= deg p

        If ~(k <= deg (pdilate n p)),
           Then deg (pdilate n p) < k.
            and (pdilate n p) ' k = #0         by poly_coeff_nonzero
            If k MOD m <> 0, RHS gives #0.
            If k MOD m = 0, RHS gives EL (k DIV m) p.
            But m * deg p < k                  by poly_dilate_deg
             so     deg p < k DIV m            by MULT_LT_DIV, MULT_COMM
            Thus EL (k DIV m) p = #0           by poly_coeff_nonzero
*)
val poly_dilate_coeff = store_thm(
  "poly_dilate_coeff",
  ``!r:'a ring. !p n k. (pdilate n p) ' k = if k MOD (SUC n) = 0 then p ' (k DIV (SUC n)) else #0``,
  rpt strip_tac >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  Cases_on `n = 0` >-
  metis_tac[ONE, poly_dilate_0, MOD_1, DIV_1] >>
  Cases_on `p = |0|` >-
  rw[] >>
  `pdilate n p <> |0|` by rw[poly_dilate_eq_zero] >>
  Cases_on `k <= deg (pdilate n p)` >| [
    `k <= m * deg p` by metis_tac[poly_dilate_deg] >>
    `(k MOD m = 0) ==> (k DIV m <= deg p)` by rw[GSYM LE_MULT_LE_DIV] >>
    `(k MOD m = 0) ==> ~(deg p < k DIV m)` by decide_tac >>
    `LENGTH (DILATE #0 0 n p) <> 0` by metis_tac[DILATE_0_EQ_NIL, LENGTH_NIL, poly_zero] >>
    `k <= PRE (LENGTH (DILATE #0 0 n p))` by metis_tac[poly_deg_def, poly_dilate_def, poly_zero] >>
    `k < LENGTH (DILATE #0 0 n p)` by decide_tac >>
    `(pdilate n p) ' k = EL k (DILATE #0 0 n p)` by rw[poly_coeff_nonzero_alt] >>
    rw[DILATE_0_EL, poly_coeff_nonzero],
    `deg (pdilate n p) < k` by decide_tac >>
    `m * deg p < k` by metis_tac[poly_dilate_deg] >>
    `(k MOD m = 0) ==> deg p < k DIV m` by metis_tac[MULT_LT_DIV, MULT_COMM] >>
    rw[poly_coeff_nonzero]
  ]);

(* Theorem: lead (pdilate n p) = lead p *)
(* Proof:
   If p = |0|,
      Then pdilate n |0| = |0|   by poly_dilate_zero
      hence true.
   If p <> |0|,
      Then pdilate n p <> |0|    by poly_dilate_eq_zero
        lead (pdilate n p)
      = LAST (pdilate n p)       by poly_lead_alt, pdilate n p <> |0|
      = LAST (DILATE #0 0 n p)   by poly_dilate_def
      = LAST p                   by DILATE_0_LAST
      = lead p                   by poly_lead_alt, p <> |0|
*)
val poly_dilate_lead = store_thm(
  "poly_dilate_lead",
  ``!r:'a ring. !p n. lead (pdilate n p) = lead p``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  rw[poly_dilate_eq_zero, poly_lead_alt, DILATE_0_LAST]);

(* Theorem: Ring r ==> !p. weak p ==> !n. weak (pdilate n p) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> weak (pdilate n [])
         weak (pdilate n [])
     <=> weak []                   by poly_dilate_zero, poly_zero
   Step: weak p ==> weak (pdilate n p) ==>
         !h. weak (h::p) ==> weak (pdilate n (h::p))
     Note weak (h::p) ==> h IN R /\ weak p     by weak_cons
     If p = [],
         weak (pdilate n (h::p))
     <=> weak (DILATE #0 0 n (h::p)) by poly_dilate_def
     <=> weak [h]                    by DILATE_0_CONS
     <=> T                           by weak_const
     If p <> [],
        Note rfun (K #0)                  by ring_fun_def, ring_zero_element

         weak (pdilate n (h::p))
     <=> weak (DILATE #0 0 n (h::p))   by poly_dilate_def
     <=> weak (h::GENLIST (K #0) n ++ DILATE #0 0 n p)         by DILATE_0_CONS
     <=> weak (h::GENLIST (K #0) n) /\ weak (DILATE #0 0 n p)  by weak_append_weak
     <=> weak (h::GENLIST (K #0) n)                            by induction hypothesis
     <=> T                                                     by weak_genlist
*)
val weak_dilate_weak = store_thm(
  "weak_dilate_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !n. weak (pdilate n p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  Cases_on `p = []` >-
  rw[] >>
  rw_tac std_ss[DILATE_0_CONS] >>
  `weak (DILATE #0 0 n p)` by metis_tac[poly_dilate_def] >>
  `rfun (K #0)` by rw[ring_fun_def] >>
  rw[weak_append_weak, weak_genlist]);

(* Theorem: Ring r ==> !p. poly p ==> !n. poly (pdilate n p) *)
(* Proof:
   If p = |0|,
      Then pdilate n |0| = |0|      by poly_dilate_zero
       and poly |0|                 by poly_zero_poly
   If p <> |0|,
      Then pdilate n p <> |0|       by poly_dilate_eq_zero
       and weak (pdilate n p)       by weak_dilate_weak
       and lead (pdilate n p)
         = lead p                   by poly_dilate_lead
         <> #0                      by poly_lead_nonzero
      Hence poly (pdilate n p)      by poly_def_alt, poly_lead_alt
*)
val poly_dilate_poly = store_thm(
  "poly_dilate_poly",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. poly (pdilate n p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `pdilate n p <> |0|` by rw[poly_dilate_eq_zero] >>
  `weak (pdilate n p)` by rw[weak_dilate_weak] >>
  `lead (pdilate n p) <> #0` by rw_tac std_ss[poly_dilate_lead, poly_lead_nonzero] >>
  metis_tac[poly_def_alt, poly_lead_alt]);

(* Theorem: pdilate n [c] = [c] *)
(* Proof:
     pdilate n [c]
   = DILATE #0 0 n [c]    by poly_dilate_def
   = [c]                  by DILATE_SING
*)
val poly_dilate_const = store_thm(
  "poly_dilate_const",
  ``!r:'a ring. !n c. pdilate n [c] = [c]``,
  rw[DILATE_SING]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
