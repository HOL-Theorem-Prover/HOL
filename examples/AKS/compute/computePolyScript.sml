(* ------------------------------------------------------------------------- *)
(* Polynomial Computations                                                   *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computePoly";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory rich_listTheory arithmeticTheory numberTheory
     combinatoricsTheory dividesTheory gcdTheory logrootTheory whileTheory;

open ringTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyMonicTheory polyEvalTheory;
open polyDivisionTheory polyFieldDivisionTheory polyFieldModuloTheory;
open polyBinomialTheory;

open computeBasicTheory computeOrderTheory;

val _ = intLib.deprecate_int ();

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * (n :num)``);

(* ------------------------------------------------------------------------- *)
(* Polynomial Computations Documentation                                     *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
   shuffle n p   = poly_shuffle (r:'a ring) n p
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Polynomial Computation under modulus unity:
   poly_slide_def         |- (!r p1 p2. poly_slide r p1 p2 [] = p1) /\
                              !r p1 p2 h t. poly_slide r p1 p2 (h::t) = poly_slide r (h o p2 || p1) (turn p2) t
   unity_mod_mult_def     |- !r p q. unity_mod_mult r p q = poly_slide r |0| p q
   unity_mod_sq_def       |- !r p. unity_mod_sq r p = unity_mod_mult r p p
   unity_mod_exp_def      |- !r p n. unity_mod_exp r p n = if n = 0 then |1|
                                     else (let q = unity_mod_exp r (unity_mod_sq r p) (HALF n)
                                            in if EVEN n then q else unity_mod_mult r p q)
   unity_mod_special_def  |- !r k n c. unity_mod_special r k n c = if k = 0 then |0|
                                       else if k = 1 then [#1 + ##c]
                                       else (let q = if n MOD k = 0 then [#1 + ##c]
                                             else ##c::PAD_LEFT #0 (n MOD k) [#1] in PAD_RIGHT #0 k q)
   unity_mod_monomial_def |- !r k c. unity_mod_monomial r k c = if k = 0 then |0|
                                     else if k = 1 then [#1 + ##c] else PAD_RIGHT #0 k [##c; #1]

   Correctness of Polynomial Algorithms:
   poly_slide_length         |- !r p1 p2 q. LENGTH p1 <= LENGTH p2 ==>
                                 (LENGTH (poly_slide r p1 p2 q) = if q = [] then LENGTH p1 else LENGTH p2)
   unity_mod_mult_length     |- !r p q. LENGTH (unity_mod_mult r p q) = if q = [] then 0 else LENGTH p
   unity_mod_sq_length       |- !r p. LENGTH (unity_mod_sq r p) = LENGTH p
   unity_mod_mult_zero       |- !r p. unity_mod_mult r p |0| = |0|
   unity_mod_mult_one        |- !r. #1 <> #0 ==> !p. unity_mod_mult r p |1| = #1 o p
   unity_mod_exp_trivial     |- !r p n. (#1 = #0) ==> (unity_mod_exp r p n = |0|)
   unity_mod_exp_0           |- !r. !p. unity_mod_exp r p 0 = |1|
   unity_mod_exp_1           |- !r p. unity_mod_exp r p 1 = if (#1 = #0) then |0| else #1 o p
   unity_mod_exp_length      |- !r p n. LENGTH (unity_mod_exp r p n) =
                                        if #1 = #0 then 0 else if n = 0 then 1 else LENGTH p
   unity_mod_special_length  |- !r k n c. LENGTH (unity_mod_special r k n c) = k
   unity_mod_monomial_length |- !r k c. LENGTH (unity_mod_monomial r k c) = k

   poly_slide_weak           |- !r. Ring r ==> !q p1 p2. weak p1 /\ weak p2 /\ weak q ==>
                                                         weak (poly_slide r p1 p2 q)
   poly_slide_zero           |- !r p q. (poly_slide r p q |0| = p) /\ (poly_slide r p |0| q = p)
   poly_slide_add            |- !r. Ring r ==> !p q t1 t2.
                                    weak p /\ weak q /\ weak t1 /\ weak t2 ==>
                                    (poly_slide r (t1 || t2) p q = t1 || poly_slide r t2 p q)
   poly_slide_turn           |- !r. Ring r ==> !p q t.
                                    weak p /\ weak q /\ weak t ==>
                                    (poly_slide r t (turn p) q = t || turn (poly_slide r |0| p q))
   poly_slide_init_zero_poly |- !r. Ring r ==> !p q. weak p /\ weak q /\ q <> |0| ==>
                                 !t. zerop t /\ LENGTH t <= LENGTH p ==>
                                     (poly_slide r t p q = poly_slide r |0| p q)
   poly_slide_eqn_1     |- !r a p q. 0 < LENGTH q /\ weak q ==>
                              (poly_slide r a p q = poly_slide r (TAKE 1 q o p || a) (turn p) (DROP 1 q))
   poly_slide_eqn_2     |- !r. Ring r ==> !a p. weak a /\ weak p ==> !q. 1 < LENGTH q /\ weak q ==>
       (poly_slide r a p q = poly_slide r (EL 1 q o turn p || EL 0 q o p || a) (turn_exp p 2) (DROP 2 q))
   poly_slide_eqn       |- !r. Ring r /\ #1 <> #0 ==> !a p. weak a /\ weak p /\ LENGTH a <= LENGTH p ==>
                            !n q. weak q /\ n <= LENGTH q ==> (poly_slide r a p q =
                                  poly_slide r (psum (GENLIST (\k. q ' k o turn_exp p k) n) || a)
                                                (turn_exp p n) (DROP n q))
   unity_mod_mult_alt   |- !r. Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ q <> |0| ==>
                               (unity_mod_mult r p q = psum (GENLIST (\k. q ' k o turn_exp p k) (SUC (deg q))))
   unity_mod_mult_zero_alt  |- !r p. (unity_mod_mult r p |0| = |0|) /\ (unity_mod_mult r |0| p = |0|)
   unity_mod_mult_cons  |- !r. Ring r ==> !p h t. weak p /\ weak (h::t) ==>
                               (unity_mod_mult r p (h::t) = h o p || unity_mod_mult r (turn p) t)
   unity_mod_mult_weak  |- !r. Ring r ==> !p q. weak p /\ weak q ==> weak (unity_mod_mult r p q)
   unity_mod_sq_weak    |- !r. Ring r ==> !p. weak p ==> weak (unity_mod_sq r p)
   unity_mod_exp_weak   |- !r. Ring r ==> !n p. weak p ==> weak (unity_mod_exp r p n)
   unity_mod_mult_eqn   |- !r. Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ 1 < LENGTH p /\ q <> |0| ==>
                               (chop (unity_mod_mult r p q) = (p * q) % unity (LENGTH p))
   unity_mod_sq_eqn     |- !r. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
                               (chop (unity_mod_sq r p) = (p * p) % unity (LENGTH p))
   unity_mod_exp_even   |- !r p n. EVEN n ==> (unity_mod_exp r p n =
                                              unity_mod_exp r (unity_mod_sq r p) (HALF n))
   unity_mod_exp_odd    |- !r p n. ODD n ==> (unity_mod_exp r p n =
                                              unity_mod_mult r p (unity_mod_exp r (unity_mod_sq r p) (HALF n)))
   unity_mod_exp_eqn    |- !r. Ring r /\ #1 <> #0 ==> !n p. weak p /\ 1 < LENGTH p ==>
                               (chop (unity_mod_exp r p n) = p ** n % unity (LENGTH p))

   Special Monomials under modulus unity:
   unity_mod_special_0      |- !r n c. unity_mod_special r 0 n c = |0|
   unity_mod_special_not_0  |- !r k n c. Ring r /\ k <> 0 ==>
                                         unity_mod_special r k n c =
                                         unity_mod_special r k n 0 || PAD_RIGHT #0 k [##c]
   unity_mod_special_weak   |- !r. Ring r ==> !k n c. weak (unity_mod_special r k n c)
   unity_mod_monomial_alt   |- !r k c. unity_mod_monomial r k c = unity_mod_special r k 1 c
   unity_mod_monomial_weak  |- !r. Ring r ==> !k c. weak (unity_mod_monomial r k c)
   unity_mod_special_chop   |- !r. Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
                               !n c. chop (unity_mod_special r k n c) = (X ** n + |c|) % unity k
   unity_mod_monomial_chop  |- !r. Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
                               !c. chop (unity_mod_monomial r k c) = (X + |c|) % unity k

   Constant polynomials under modulus unity:
   unity_mod_const_def      |- !r k c. unity_mod_const r k c =
                                       if k = 0 then |0| else PAD_RIGHT #0 k [##c]
   unity_mod_zero_def       |- !r k. unity_mod_zero r k = unity_mod_const r k 0
   unity_mod_one_def        |- !r k. unity_mod_one r k = unity_mod_const r k 1
   unity_mod_const_length   |- !r k c. LENGTH (unity_mod_const r k c) = k
   unity_mod_const_weak     |- !r. Ring r ==> !k c. weak (unity_mod_const r k c)
   unity_mod_const_0        |- !r k. unity_mod_const r k 0 = unity_mod_zero r k
   unity_mod_const_1        |- !r k. unity_mod_const r k 1 = unity_mod_one r k
   unity_mod_const_eqn      |- !r k. unity_mod_const r k c =
                               if k = 0 then [] else ##c::GENLIST (K #0) (k - 1)
   unity_mod_zero_length    |- !r k. LENGTH (unity_mod_zero r k) = k
   unity_mod_zero_weak      |- !r k. Ring r ==> weak (unity_mod_zero r k)
   unity_mod_zero_alt       |- !r k. unity_mod_zero r k = PAD_RIGHT #0 k []
   unity_mod_zero_eqn       |- !r k. unity_mod_zero r k = GENLIST (K #0) k
   unity_mod_zero_chop      |- !r k. chop (unity_mod_zero r k) = |0|
   unity_mod_one_length     |- !r k. LENGTH (unity_mod_one r k) = k
   unity_mod_one_weak       |- !r k. Ring r ==> weak (unity_mod_one r k)
   unity_mod_one_cons       |- !r. Ring r ==> !k. 0 < k ==>
                                   unity_mod_one r k = #1::unity_mod_zero r (k - 1)
   unity_mod_one_eqn        |- !r k. unity_mod_one r k =
                                     if k = 0 then [] else ##1::GENLIST (K #0) (k - 1)
   unity_mod_one_chop       |- !r k. Ring r /\ #1 <> #0 ==>
                               (chop (unity_mod_one r k) = if k = 0 then |0| else |1|)
   unity_mod_const_chop     |- !r. Ring r ==>
                               !k c. chop (unity_mod_const r k c) =
                                     if (k = 0) \/ char r divides c then |0| else |c|

   Powers of X under modulus unity:
   unity_mod_X_exp_def      |- !r k n. unity_mod_X_exp r k n = unity_mod_special r k n 0
   unity_mod_X_exp_0        |- !r k. unity_mod_X_exp r k 0 = unity_mod_one r k
   unity_mod_X_exp_0_n      |- !r n. unity_mod_X_exp r 0 n = |0|
   unity_mod_X_exp_1_n      |- !r n. unity_mod_X_exp r 1 n = [##1]
   unity_mod_X_exp_length   |- !r k n. LENGTH (unity_mod_X_exp r k n) = k
   unity_mod_X_exp_weak     |- !r. Ring r ==> !k n. weak (unity_mod_X_exp r k n)
   unity_mod_special_alt    |- !r. Ring r ==>
                               !k n c. unity_mod_special r k n c =
                                       unity_mod_X_exp r k n || unity_mod_const r k c

   Polynomials in (ZN n):
   ZN_weak             |- !n p. Weak (ZN n) p <=> EVERY (\c. c < n) p
   ZN_unity_mod_special_weak
                       |- !n k m c. 0 < n ==> Weak (ZN n) (unity_mod_special (ZN n) k m c)
   ZN_unity_mod_monomial_weak
                       |- !n k c. 0 < n ==> Weak (ZN n) (unity_mod_monomial (ZN n) k c)
   ZN_unity_mod_const_weak
                       |- !n k c. 0 < n ==> Weak (ZN n) (unity_mod_const (ZN n) k c)

   Extra Work:

   Polynomial Shuffle:
   poly_shuffle_def    |- !r n p. shuffle n p =
                                  if p = |0| then |0|
                                  else (let q = FRONT p in let t = DROP n q
                                         in TAKE n q ++ [HD t + LAST p] ++ TL t)
   poly_shuffle_zero   |- !r n. shuffle n |0| = |0|
   poly_shuffle_length |- !r p n. SUC n < LENGTH p ==> (LENGTH (shuffle n p) = LENGTH p - 1)
   poly_shuffle_0      |- !r p. shuffle 0 p = if p = |0| then |0| else HD (FRONT p) + LAST p::TL (FRONT p)

   Polynomial Remainder of unity:
   unity_mod_def          |- !r p k. unity_mod r k p =
                                if 0 < k then
                                   if k < LENGTH p then unity_mod r k (shuffle (LENGTH p - k - 1) p)
                                                   else PAD_RIGHT #0 k p
                                   else p % |0|
   old_unity_mod_zero_eqn     |- !r k. 0 < k ==> (unity_mod r k |0| = GENLIST (K #0) k)
   old_unity_mod_zero_chop    |- !r k. 0 < k ==> (chop (unity_mod r k |0|) = |0|)
   old_unity_mod_zero_length  |- !r k. 0 < k ==> (LENGTH (unity_mod r k |0|) = k)
   old_unity_mod_length       |- !r k. 0 < k ==> !p. LENGTH (unity_mod r k p) = k

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Computation under modulus unity k = X ** k - |1|               *)
(* ------------------------------------------------------------------------- *)

(*
The aim is to devise purely list-manipulating algorithm to perform the polynomial introspective check:

(X + c) ** n = X ** n + c  MOD (n, X ** k - |1|).

In terms of list representation for polynomials, this is to verify, in (ZN n),
<---- k ----------->
[c; 1; 0; 0; 0; ; 0]
        |
        | perform (exp n) by repeated squares, always reduce by X ** k -> |1|
        \/
[a; b; c; ......; x] =
[c; 0; 0; 0; 1; 0; 0; 0]   position of 1 at (n MOD k)
        /\
        |
        | peform remaindering, reduce by X ** k -> |1|, for a number of times.
        |
[c; 0; 0; 0; 0;             ;0; 1]
<----------- n ------------------>

How to avoid the initial storage of a list with n coefficients?
Have to make this a virtual list!

   (X + c) ** n = X ** n + c  MOD (n, X ** k - |1|).
or ((X + c) ** n) MOD (n, unity k) = X ** (n MOD k) + c

e.g. (x ** 5 + 1) MOD (unity 3)
> EVAL ``unity_mod (ZN 5) 3 [3; 0; 0; 0; 0; 1] -> [3; 0; 1]``;

  (X ** n + |1|) MOD (unity 3)
= (X ** n) MOD (unity 3) + |1| MOD (unity 3)
= (X ** (n MOD 3)) + |1|
For n = 5, result is X ** 2 + |1|.

To multiply by (X + c),
  (X + c) * p
= X * p + c * p
Here p1 = c * p is scalar multiplication: MAP (\x. c * x) p.
Also p2 = X * p is just shifting, but MOD (unity k) means it is just a rotation.
Then p3 = p1 + p2 is just parallel add: MAP2 (\x y. x + y) p1 p2

How to square a polynomial? Just multiply by itself.

This is Horner's Method:
  (x^2 + 2x + 3) * p
= ((x + 2)x + 3) * p
= (x + 2) x p + 3 * p
let p1 = 3 * p      scalar  = 3 * p
let p2 = x * p      rotate  = x * p
let p3 = 2 * p2     scalar  = 2 * x * p
let p4 = x * p2     rotate  = x * x * p
let p5 = p4 + p3 + p1    parallel add = x * x * p + 2 * x * p + 3 * p

This is different from:
   (x + 2)(x + 3) * p
let p1 = 3 * p      scalar        = 3 * p
let p2 = x * p      rotate        = x * p
let p3 = p1 + p2    parallel add  = x * p + 3 * p = y = (x + 3) * p
let p4 = 2 * p3     scalar        = 2 * y
let p5 = x * p3     rotate        = x * y
let p6 = p4 + p5    parallel add  = x * y + 2 * y = (x + 2) * y = (x + 2)(x + 3) * p

In general, Horner's method goes like this:
   (x^3 + 2x^2 + 3x + 4) * p
 = ((x + 2) x + 3) x + 4) * p
 p1 <- 4 * p    = 4 * p
 p2 <- x * p    = x * p
 p3 <- 3 * p2   = 3 * x * p
 p4 <- x * p2   = x * x * p
 p5 <- 2 * p4   = 2 * x * x * p
 p6 <- x * p4   = x * x * x * p
 p7 <- p6 + p5 + p3 + p1

 Improvement:
 p1 <- 4 * p    = 4 * p
 p2 <- x * p    = x * p
 p3 <- 3 * p2   = 3 * x * p
 p3 <- p3 + p1  = 3 * x * p + 4 * p  (can discard p1)
 p4 <- x * p2   = x * x * p          (can discard p2)
 p5 <- 2 * p4   = 2 * x * x * p
 p5 <- p5 + p3  = 2 * x * x * p + 3 * x * p + 4 * p  (can discard p3)
 p6 <- x * p4   = x * x * x * p                      (can discard p4)
 p7 <- 1 * p6   (dummy)
 p7 <- p7 + p5  = x * x * x * p + 2 * x * x * p + 3 * x * p + 4 * p (can discard p5)

 Next Improvement (using 3 registers: r1, r2, r3):
 r1 <- 4 * p    = 4 * p
 r2 <- x * p    = x * p
 r3 <- 3 * r2   = 3 * x * p
 r1 <- r3 + r1  = 3 * x * p + 4 * p  (back to r1)
 r2 <- x * r2   = x * x * p          (back to r2)
 r3 <- 2 * r2   = 2 * x * x * p
 r1 <- r3 + r1  = 2 * x * x * p + 3 * x * p + 4 * p (back to r1)
 r2 <- x * r2   = x * x * x * p                     (back to r2)
 r3 <- 1 * r2   (dummy)
 r1 <- r3 + r1  = 1 * x * x * x * p + 2 * x * x * p + 3 * x * p + 4 * p

 Consistency Improvement (using 3 registers: r1, r2, r3):
 r1 <- 0 * p    = 0
 r2 <- 1 * p    = p
 ------------------------ initialization
 r3 <- 4 * r2   = 4 * p
 r1 <- r3 + r1  = 4 * p + 0 = 4 * p
 r2 <- x * r2   = x * p
 ------------------------ iteration
 r3 <- 3 * r2   = 3 * x * p
 r1 <- r3 + r1  = 3 * x * p + 4 * p  (back to r1)
 r2 <- x * r2   = x * x * p          (back to r2)
 ------------------------ iteration
 r3 <- 2 * r2   = 2 * x * x * p
 r1 <- r3 + r1  = 2 * x * x * p + 3 * x * p + 4 * p (back to r1)
 r2 <- x * r2   = x * x * x * p                     (back to r2)
 ------------------------ iteration
 r3 <- 1 * r2   (dummy)
 r1 <- r3 + r1  = 1 * x * x * x * p + 2 * x * x * p + 3 * x * p + 4 * p  (stop)
 r2 <- x * r2   (not required)
 ------------------------ iteration

 Better Iteration (using 3 registers: r0, r1, r2):
 r1 <- 0
 r2 <- p
 ------------------------ initialization
 r0 <- 4 * r2   = 4 * p
 r1 <- r0 + r1  = 4 * p + 0 = 4 * p
 r2 <- x * r2   = x * p
 ------------------------ iteration
 r0 <- 3 * r2   = 3 * x * p
 r1 <- r0 + r1  = 3 * x * p + 4 * p
 r2 <- x * r2   = x * x * p
 ------------------------ iteration
 r0 <- 2 * r2   = 2 * x * x * p
 r1 <- r0 + r1  = 2 * x * x * p + 3 * x * p + 4 * p
 r2 <- x * r2   = x * x * x * p
 ------------------------ iteration
 r0 <- 1 * r2   = 1 * x * x * x * p    (last coefficient)
 r0 <- r0 + r1  = 1 * x * x * x * p + 2 * x * x * p + 3 * x * p + 4 * p  (stop)
 --- stop, product in r0.

*)

(* Convert a polynomial to MOD (unity k), and ensure its length is k (un-normalized remainder). *)
(* This is now automatically done in unity_mod r k p:
val unity_unchop_def = Define`
    unity_unchop (r:'a ring) k (p:'a poly) =
       (unity_mod r k p) || (GENLIST (K #0) k)  (* from PAD_LEFT, PAD_RIGHT *)
`;
*)
(* Simple MOD (unity k) -- just gives a weak extension
val poly_pad_def = Define`
  poly_pad (r:'a ring) (k:num) (p:'a poly) =
      if 0 < k then PAD_RIGHT #0 k p (* assume LENGTH p <= k *)
      else p % |0| (* whatever that is! *)
`;
*)

(* Horner's method to multiply by coefficients of q *)
(* This is not Horner's method -- which takes the leading coefficient first *)
(* The weak_mult_def, which is recursive and really does first take the leading coefficient, is Horner's *)
(* This is actually unwinding the Horner's recursion, the usual mult-1-p, mult-X-p, mult-X-X-p, etc. *)
(* So call this sliding add of partial products, or just slide. *)
(* Note: use weak scalar and weak add to keep length *)
(*
val poly_slide_def = Define`
    (poly_slide (r:'a ring) (r1:'a poly) (r2:'a poly) [] = r1) /\
    (poly_slide (r:'a ring) (r1:'a poly) (r2:'a poly) ((h::t):'a poly) =
       let r0 = h o r2 in poly_slide r (r0 || r1) (turn r2) t)
`;
*)
val poly_slide_def = Define`
    (poly_slide (r:'a ring) p1 p2 [] = p1) /\
    (poly_slide (r:'a ring) p1 p2 ((h::t):'a poly) = poly_slide r ((h o p2) || p1) (turn p2) t)
    (* Note: turn p2 = X * p2 only when length p2 = k *)
`;

(* Polynomial multiplication with MOD (unity k) *)
(*
val unity_mod_mult_def = Define`
    unity_mod_mult (r:'a ring) (k:num) (p:'a poly) (q:'a poly) =
    poly_slide r (unity_mod r k |0|) (unity_mod r k p) (unity_mod r k q)
`;
*)
val unity_mod_mult_def = Define`
    unity_mod_mult (r:'a ring) (p:'a poly) (q:'a poly) =
    poly_slide r |0| p q (* both p and q are of length k, for MOD (unity k) *)
`;

(*
> EVAL ``unity_mod_mult (ZN 5) [1;2;3] [1;2;3]``; --> [3; 3; 0]  yes!

(3x^2 + 2x + 1)^2 (MOD 5, x^3 - 1) = 3x + 3

This is correct? -- debug using Javascript!
*)

(* Polynomial square with MOD (unity k) *)
val unity_mod_sq_def = Define`
    unity_mod_sq (r:'a ring) (p:'a poly) = unity_mod_mult r p p
    (* Note LENGTH p = k, for MOD (unity k) *)
`;

(*
> EVAL ``unity_mod_sq (ZN 5) [1;2;3]``; --> [3; 3; 0]
> EVAL ``unity_mod_sq (ZN 5) [3;2;1]``; --> [3; 3; 0]  yes
> EVAL ``unity_mod_sq (ZN 5) [1;1]``; --> [2; 2]       for MOD (unity 2)
> EVAL ``unity_mod_sq (ZN 5) [1;1;1]``; --> [3; 3; 3]  yes
*)

(* Polynomial exponentiation p ** n with MOD (unity k) *)
(*
val unity_mod_exp_def = Define`
    unity_mod_exp (r:'a ring) k (p:'a poly) n =
     if n = 0 then (unity_mod r k |1|)
     else let q = unity_mod_exp r k (unity_mod_sq r p) (HALF n)
          in if EVEN n then q else (unity_mod_mult r p q)
`;
*)
val unity_mod_exp_def = Define`
    unity_mod_exp (r:'a ring) (p:'a poly) n =
       if n = 0 then |1| (* p ** 0 = |1| *)
       else let q = unity_mod_exp r (unity_mod_sq r p) (HALF n)
             in if EVEN n then q else (unity_mod_mult r p q)
`;

(*
> EVAL ``unity_mod_exp (ZN 5) [1;1] 2``; --> [2; 2]    (X + |1|) ** 2 MOD (X ** (LENGTH [1;1]) - |1|)
> EVAL ``unity_mod_exp (ZN 5) [1;1;0;0] 2``; --> [1; 2; 1; 0]
> EVAL ``unity_mod_exp (ZN 5) [1;1;0;0] 3``; --> [1; 3; 3; 1]
> EVAL ``unity_mod_exp (ZN 5) [1;1;0;0] 4``; --> [2; 4; 1; 4]
> EVAL ``unity_mod_exp (ZN 5) [1;1;0;0] 5``; --> [1; 1; 0; 0]  <-- Fermat's Little Theorem for polynomials.
*)

(* These are the initial weak polynomials with length equal to k *)

(* Define (X ** n + |c|) MOD (unity k) *)
(*
val unity_mod_special_def = Define`
    unity_mod_special (r:'a ring) k n (c:num) =
       if k = 0 then |0|
       else if k = 1 then [#1 + ##c]
            else PAD_RIGHT #0 k (##c :: (PAD_LEFT #0 (n MOD k) [#1]))
`;
*)
val unity_mod_special_def = Define`
    unity_mod_special (r:'a ring) k n (c:num) =
       if k = 0 then |0|
       else if k = 1 then [#1 + ##c]
     else (let q = if n MOD k = 0 then [#1 + ##c] else ##c :: PAD_LEFT #0 (n MOD k) [#1]
            in PAD_RIGHT #0 k q)
`;
(* Note: k = 0 is special since n MOD 0 is undefined, and unity 0 = |0|, with MOD |0| undefined.
   Moreover, for k = 1, (unity 1 = X - |1|), and p MOD (unity 1) = constant with degree = 0.
By making unity_mod_special r 0 n c = |0|, this keeps the length equals to 0 = k.
By making unity_mod_special r 0 n c = (X ** n + |c|) MOD |0| (whatever that is), length is undefined.
*)

(*
> EVAL ``unity_mod (ZN 5) 3 [1; 0; 0; 0; 0; 0; 0; 0; 1]``; --> [1; 0; 1]
> EVAL ``unity_mod_special (ZN 5) 3 8 1``; --> [1; 0; 1]  yes  x^2 + 1
> EVAL ``unity_mod (ZN 5) 3 [2; 0; 0; 0; 0; 0; 0; 1]``; --> [2; 1; 0]
> EVAL ``unity_mod_special (ZN 5) 3 7 2``; --> [2; 1; 0]  yes  x + 2
*)

(* Define (X + c) MOD (unity k) *)
val unity_mod_monomial_def = Define`
    unity_mod_monomial (r:'a ring) (k:num) (c:num) =
       if k = 0 then |0| else if k = 1 then [#1 + ##c] else PAD_RIGHT #0 k [##c; #1]
`;
(* Note: k = 0 is special since (unity 0 = |0|), and MOD |0| is undefined.
   Moreover, for k = 1, (unity 1 = X - |1|), and p MOD (unity 1) = constant with degree = 0.
   Thus to ensure unity_mod_monomial r k c always have length equals to k, these special cases are taken care of.
*)

(*
> EVAL ``unity_mod_monomial (ZN 5) 3 2``; --> [2; 1; 0]
> EVAL ``unity_mod (ZN 5) 3 [2; 1]``;    --> [2; 1; 0]
> EVAL ``unity_mod_monomial (ZN 5) 7 4``; --> [4; 1; 0; 0; 0; 0; 0]
> EVAL ``unity_mod (ZN 5) 7 [4; 1]``;    --> [4; 1; 0; 0; 0; 0; 0]
*)

(*
> EVAL ``unity_mod_exp (ZN 5) (unity_mod_monomial (ZN 5) 3 1) 5``; --> [1; 0; 1]
> EVAL ``unity_mod_special (ZN 5) 3 5 1``; --> [1; 0; 1]
> EVAL ``unity_mod_exp (ZN 5) (unity_mod_monomial (ZN 5) 3 2) 5``; --> [2; 0; 1]
> EVAL ``unity_mod_special (ZN 5) 3 5 2``; --> [2; 0; 1]
*)

(* ------------------------------------------------------------------------- *)
(* Correctness of Polynomial Algorithms                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: LENGTH p1 <= LENGTH p2 ==>
            (LENGTH (poly_slide r p1 p2 q) = if q = [] then LENGTH p1 else LENGTH p2) *)
(* Proof:
   By complete induction on (LENGTH q).
   If q = [],
   to show: LENGTH (poly_slide r p1 p2 []) = if [] = [] then LENGTH p1 else LENGTH p2
        LENGTH (poly_slide r p1 p2 [])
      = LENGTH p1                              by poly_slide_def
      and [] = [] is true.
   If q = (h::t),
   to show: LENGTH (poly_slide r p1 p2 (h::t)) = if h::t = [] then LENGTH p1 else LENGTH p2
      Let q1 = h o p2 || p1, q2 = turn p2.
      Then LENGTH q2 = LENGTH p2               by turn_length
       and LENGTH q1
         = MAX (LENGTH (h o p1)) (LENGTH p2)   by weak_add_length
         = MAX (LENGTH p1) (LENGTH p2)         by weak_cmult_length
         = LENGTH p2                           by MAX_DEF, LENGTH p1 <= LENGTH p2
      If t = [],
           LENGTH (poly_slide r q1 q2 [])
         = LENGTH q1                           by poly_slide_def
         = LENGTH p2                           by above
      If t <> [],
         Since LENGTH t < SUC (LENGTH t)             by SUC_LESS
                        = LENGTH (h::t) = LENGTH q   by LENGTH
         The result follows by induction hypothesis to q1, q2, t.
*)
val poly_slide_length = store_thm(
  "poly_slide_length",
  ``!r:'a ring. !p1 p2 q. LENGTH p1 <= LENGTH p2 ==>
               (LENGTH (poly_slide r p1 p2 q) = if q = [] then LENGTH p1 else LENGTH p2)``,
  strip_tac >>
  completeInduct_on `LENGTH q` >>
  rpt strip_tac >>
  Cases_on `q` >-
  rw[poly_slide_def] >>
  rw[poly_slide_def] >>
  qabbrev_tac `q1 = h o p2 || p1` >>
  qabbrev_tac `q2 = turn p2` >>
  `LENGTH q2 = LENGTH p2` by rw[turn_length, Abbr`q2`] >>
  `LENGTH q1 = LENGTH p2` by rw[weak_cmult_length, weak_add_length, MAX_DEF, Abbr`q1`] >>
  Cases_on `t = []` >-
  rw[poly_slide_def] >>
  rw[]);

(* Theorem: LENGTH (unity_mod_mult r p q) = if q = [] then 0 else LENGTH p *)
(* Proof:
   Note LENGTH |0| = 0                  by LENGTH, poly_zero
    and 0 <= LENGTH p,
     LENGTH (unity_mod_mult r p q)
   = LENGTH (poly_slide r |0| p q)      by unity_mod_mult_def
   = if q = [] then 0 else LENGTH p     by poly_slide_length, 0 <= LENGTH p
*)
val unity_mod_mult_length = store_thm(
  "unity_mod_mult_length",
  ``!r:'a ring. !p q. LENGTH (unity_mod_mult r p q) = if q = [] then 0 else LENGTH p``,
  rw[unity_mod_mult_def, poly_slide_length]);

(* Theorem: LENGTH (unity_mod_sq r p) = LENGTH p *)
(* Proof:
     LENGTH (unity_mod_sq r p)
   = LENGTH (unity_mod_mult r p p)       by unity_mod_sq_def
   = if p = [] then 0 else LENGTH p      by unity_mod_mult_length
   = LENGTH p                            by LENGTH
*)
val unity_mod_sq_length = store_thm(
  "unity_mod_sq_length",
  ``!r:'a ring. !p. LENGTH (unity_mod_sq r p) = LENGTH p``,
  rw[unity_mod_sq_def, unity_mod_mult_length]);


(* Theorem: unity_mod_mult r p |0| = |0| *)
(* Proof:
     unity_mod_mult r p |0|
   = poly_slide r |0| p |0|      by unity_mod_mult_def
   = poly_slide r |0| p []       by poly_zero
   = |0|                         by poly_slide_def
*)
val unity_mod_mult_zero = store_thm(
  "unity_mod_mult_zero",
  ``!r:'a ring. !p. unity_mod_mult r p |0| = |0|``,
  rw[unity_mod_mult_def, poly_slide_def]);

(* Theorem: unity_mod_mult r p |1| = #1 o p *)
(* Proof:
     unity_mod_mult r p |1|
   = poly_slide r |0| p |1|       by unity_mod_mult_def
   = poly_slide r |0| p [#1]      by poly_one, #1 <> #0
   = poly_slide r (#1 o p || |0|) (turn p) []  by poly_slide_def
   = #1 o p || |0|                by poly_slide_def
   = #1 o p                       by weak_add_rzero
   This can be simplified to p    by weak_cmult_lone, need Ring r, weak p
*)
val unity_mod_mult_one = store_thm(
  "unity_mod_mult_one",
  ``!r:'a ring. #1 <> #0 ==> !p. unity_mod_mult r p |1| = #1 o p``,
  rw[unity_mod_mult_def, poly_slide_def, poly_one]);

(* Theorem: (#1 = #0) ==> (unity_mod_exp r p n = |0|) *)
(* Proof:
   By induction from unity_mod_exp_def.
   Base: n = 0 ==> |1| = |0|,
      The is true                by poly_one
   Step: unity_mod_exp r (unity_mod_sq r p) (HALF n) = |0| ==>
         unity_mod_exp r p n = |0|
      If EVEN n,
        unity_mod_exp r p n
      = unity_mod_exp r (unity_mod_sq r p) (HALF n)
                                 by unity_mod_exp_def
      = |0|                      by induction hypothesis
      If ~EVEN n,
        unity_mod_exp r p n
      = unity_mod_mult r p (unity_mod_exp r (unity_mod_sq r p) (HALF n))
                                 by unity_mod_exp_def
      = unity_mod_mult r p |0|   by induction hypothesis
      = |0|                      by unity_mod_mult_zero
*)
val unity_mod_exp_trivial = store_thm(
  "unity_mod_exp_trivial",
  ``!r:'a ring p n. (#1 = #0) ==> (unity_mod_exp r p n = |0|)``,
  ho_match_mp_tac (theorem "unity_mod_exp_ind") >>
  rw_tac std_ss[] >>
  rw_tac std_ss[Once unity_mod_exp_def] >-
  metis_tac[poly_one, poly_zero] >>
  metis_tac[unity_mod_mult_zero]);

(* Theorem: !p. unity_mod_exp r p 0 = |1| *)
(* Proof: by unity_mod_exp_def *)
val unity_mod_exp_0 = store_thm(
  "unity_mod_exp_0",
  ``!r:'a ring. !p. unity_mod_exp r p 0 = |1|``,
  rw[Once unity_mod_exp_def]);

(* Theorem: !p. unity_mod_exp r p 1 = if #1 = #0 then |0| else #1 o p *)
(* Proof:
   If #1 = #0,
      Then unity_mod_exp r p 1 = |0|      by unity_mod_exp_trivial
   If #1 <> #0,
      Note ~(EVEN 1)                      by EVEN, ADD1
      Let q = unity_mod_exp r (unity_mod_sq r p) (HALF 1)
            = unity_mod_exp r (unity_mod_sq r p) 0         by HALF_EQ_0
            = |1|
        unity_mod_exp r p 1
      = unity_mod_mult r p |1|     by unity_mod_exp_def
      = #1 o p                     by unity_mod_mult_one, #1 <> #0
*)
val unity_mod_exp_1 = store_thm(
  "unity_mod_exp_1",
  ``!r:'a ring. !p. unity_mod_exp r p 1 = if #1 = #0 then |0| else #1 o p``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >-
  rw[unity_mod_exp_trivial] >>
  `~(EVEN 1)` by rw[] >>
  qabbrev_tac `q = unity_mod_exp r (unity_mod_sq r p) (HALF 1)` >>
  `q = |1|` by rw[Once unity_mod_exp_def, Abbr`q`] >>
  rw[unity_mod_exp_def, unity_mod_mult_one, Abbr`q`]);

(* Theorem: LENGTH (unity_mod_exp r p n) =
            if #1 = #0 then 0 else if n = 0 then 1 else LENGTH p *)
(* Proof:
   By induction based on unity_mod_exp_def.
   If #1 = #0,
        LENGTH (unity_mod_exp r p n)
      = LENGTH |0| = 0                by unity_mod_exp_trivial
   If n = 0,
        LENGTH (unity_mod_exp r p 0)
      = LENGTH |1|                    by unity_mod_exp_0
      = LENGTH [#1] = 1               by poly_one, #1 <> #0
   If n = 1,
        LENGTH (unity_mod_exp r p 1)
      = LENGTH (#1 o p)               by unity_mod_exp_1
      = LENGTH p                      by weak_cmult_length
   If n <> 1
      Let q = unity_mod_exp r (unity_mod_sq r p) (HALF n)
      Note 0 < HALF n                 by HALF_EQ_0, n <> 1, n <> 0.
       and HALF n < n                 by DIV_LESS, 0 < n
           LENGTH q
         = LENGTH (unity_mod_sq r p)        by induction hypothesis
         = LENGTH p                         by unity_mod_sq_length
      If EVEN n,
           LENGTH (unity_mod_exp r p n)
         = LENGTH q                         by unity_mod_exp_def
         = LENGTH p                         by above
      If ~(EVEN n),
           LENGTH (unity_mod_exp r p n)
         = LENGTH (unity_mod_mult r p q)    by unity_mod_exp_def
         If q = [],
            Then p = []                     by LENGTH_NIL, LENGTH p = LENGTH q
            LENGTH (unity_mod_mult r p [])
          = LENGTH []                       by unity_mod_mult_zero, poly_zero
          = LENGTH p
         If q <> [],
            LENGTH (unity_mod_mult r p q)
          = LENGTH p                        by unity_mod_mult_length
*)
val unity_mod_exp_length = store_thm(
  "unity_mod_exp_length",
  ``!r:'a ring p n. LENGTH (unity_mod_exp r p n) =
                   if #1 = #0 then 0 else if n = 0 then 1 else LENGTH p``,
  ho_match_mp_tac (theorem "unity_mod_exp_ind") >>
  rpt strip_tac >>
  (Cases_on `#1 = #0` >> simp[]) >-
  rw[unity_mod_exp_trivial] >>
  (Cases_on `n = 0` >> simp[]) >-
  rw[unity_mod_exp_0, poly_one] >>
  Cases_on `HALF n = 0` >| [
    `n = 1` by fs[HALF_EQ_0] >>
    rw[unity_mod_exp_1, weak_cmult_length],
    rw[Once unity_mod_exp_def] >-
    rw[unity_mod_sq_length] >>
    qabbrev_tac `q = unity_mod_exp r (unity_mod_sq r p) (HALF n)` >>
    `LENGTH q = LENGTH (unity_mod_sq r p)` by rw[Abbr`q`] >>
    `_ = LENGTH p` by rw[unity_mod_sq_length] >>
    Cases_on `q = []` >-
    metis_tac[unity_mod_mult_zero, poly_zero, LENGTH_NIL] >>
    rw[unity_mod_mult_length]
  ]);

(* Theorem: LENGTH (unity_mod_special r k n c) = k *)
(* Proof:
   If k = 0,
       unity_mod_special r 0 n c
     = |0|                             by unity_mod_special_def
     and LENGTH |0| = 0 = k            by LENGTH, poly_zero
   If k = 1,
       unity_mod_special r 1 n c
     = [#1 + ##c]                      by unity_mod_special_def
     and LENGTH [#1 + ##c] = 1 = k     by LENGTH
   If k <> 0 and k <> 1, 1 < k.
     Let q = if n MOD k = 0 then [#1 + ##c] else ##c::PAD_LEFT #0 (n MOD k) [#1]
   If n MOD k = 0, q = [#1 + ##c]
     LENGTH (unity_mod_special r k n c)
   = LENGTH (PAD_RIGHT #0 k q)         by unity_mod_special_def
   = MAX k (LENGTH q)                  by PAD_RIGHT_LENGTH
   = MAX k 1                           by LENGTH
   = k                                 by MAX_DEF, 1 < k
   If n MOD k <> 0, q = ##c::PAD_LEFT #0 (n MOD k) [#1]
     LENGTH (unity_mod_special r k n c)
   = LENGTH (PAD_RIGHT #0 k q)                          by unity_mod_special_def
   = MAX k (LENGTH q)                                   by PAD_RIGHT_LENGTH
   = MAX k (SUC (LENGTH (PAD_LEFT #0 (n MOD k) [#1])))  by LENGTH
   = MAX k (SUC (MAX (n MOD k) (LENGTH [#1])))          by PAD_LEFT_LENGTH
   = MAX k (SUC (MAX (n MOD k) 1))                      by LENGTH
   Take cases to resolve the inner MAX,
   If n MOD k < 1,
        MAX k (SUC (MAX (n MOD k) 1))
      = MAX k (SUC 1)                    by MAX_DEF
      = MAX k 2                          by TWO
      = k                                by MAX_DEF, 1 < k ==> 2 <= k
   If ~(n MOD k < 1),
      Note n MOD k < k                   by MOD_LESS, 0 < k
        MAX k (SUC (MAX (n MOD k) 1))
      = MAX k (SUC (n MOD k))            by MAX_DEF
      = k                                by MAX_DEF, SUC (n MOD k) <= k
*)
val unity_mod_special_length = store_thm(
  "unity_mod_special_length",
  ``!r:'a ring. !k n c. LENGTH (unity_mod_special r k n c) = k``,
  rw[unity_mod_special_def, PAD_RIGHT_LENGTH, PAD_LEFT_LENGTH] >-
  rw[MAX_DEF] >>
  Cases_on `n MOD k < 1` >-
  rw[MAX_DEF] >>
  `n MOD k < k` by rw[MOD_LESS] >>
  rw[MAX_DEF]);

(* Theorem: LENGTH (unity_mod_monomial r k c) = k *)
(* Proof:
   If k = 0,
      unity_mod_monomial r 0 c = |0|      by unity_mod_monomial_def
      and LENGTH |0|
        = LENGTH [] = 0 = k               by poly_zero, LENGTH
   If k = 1,
      unity_mod_monomial r 1 c = [#0]     by unity_mod_monomial_def
      and LENGTH [#0] = 1 = k             by LENGTH
   If k <> 0 and k <> 1,
     LENGTH (unity_mod_monomial r k c)
   = LENGTH (PAD_RIGHT #0 k [##c; #1])    by unity_mod_monomial_def
   = MAX k (LENGTH [##c; #1])             by PAD_RIGHT_LENGTH
   = MAX k 2                              by LENGTH, ONE, TWO
   = k                                    by MAX_DEF, 1 < k ==> 2 <= k
*)
val unity_mod_monomial_length = store_thm(
  "unity_mod_monomial_length",
  ``!r:'a ring. !k c. LENGTH (unity_mod_monomial r k c) = k``,
  rw[unity_mod_monomial_def, PAD_RIGHT_LENGTH, MAX_DEF]);

(* Theorem: Ring r ==> !q p1 p2. weak p1 /\ weak p2 /\ weak q ==> weak (poly_slide r p1 p2 q) *)
(* Proof:
   By induction on q.
   Base: weak p1 /\ weak p2 weak [] ==> weak (poly_slide r p1 p2 [])
      Note poly_slide r p1 p2 [] = p1       by poly_slide_def
       and weak p1                          by given
   Step: !p1 p2. weak p1 /\ weak p2 /\ weak q ==> weak (poly_slide r p1 p2 q) ==>
         !h. weak (h::q) ==> weak (poly_slide r p1 p2 (h::q))
      Note h IN R /\ weak q         by weak_cons
       and poly_slide r p1 p2 (h::q)
         = poly_slide r (h o p2 || p1) (turn p2) q   by poly_slide_def
       But weak (h o p2 || p1)      by weak_cmult_weak, weak_add_weak
       and weak (turn p2)           by weak_turn
      Thus weak (poly_slide r p1 p2 (h::q))          by induction hypothesis
*)
val poly_slide_weak = store_thm(
  "poly_slide_weak",
  ``!r:'a ring. Ring r ==> !q p1 p2. weak p1 /\ weak p2 /\ weak q ==> weak (poly_slide r p1 p2 q)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[poly_slide_def] >>
  rw[poly_slide_def, weak_turn]);

(* Theorem: (poly_slide r p q |0| = p) /\ (poly_slide r p |0| q = p) *)
(* Proof:
   Note poly_slide r p q |0| = p        by poly_slide_def
   For the second one,
   By induction on p.
   Base: poly_slide r p |0| [] = p, true            by poly_slide_def
   Step: poly_slide r p |0| q = p ==> !h. poly_slide r p |0| (h::q) = p

         poly_slide r p |0| (h::q)
       = poly_slide r (h o |0| || p) (turn |0|) q   by poly_slide_def
       = poly_slide r (|0| || p) |0| q              by weak_cmult_zero, turn_nil
       = poly_slide r p |0| q                       by weak_add_zero
       = p                                          by induction hypothesis
*)
val poly_slide_zero = store_thm(
  "poly_slide_zero",
  ``!r:'a ring p q. (poly_slide r p q |0| = p) /\ (poly_slide r p |0| q = p)``,
  rw[poly_slide_def] >>
  Induct_on `q` >-
  rw[poly_slide_def] >>
  fs[poly_slide_def, turn_nil]);

(* Theorem: Ring r ==> !p q t1 t2. weak p /\ weak q /\ weak t1 /\ weak t2 ==>
            (poly_slide r (t1 || t2) p q = t1 || poly_slide r t2 p q) *)
(* Proof:
   By induction on q.
   Base: !p t1 t2. weak p /\ weak [] /\ weak t1 /\ weak t2 ==>
                   poly_slide r (t1 || t2) p [] = t1 || poly_slide r t2 p []
        poly_slide r (t1 || t2) p []
      = t1 || t2                          by poly_slide_def
      = t1 || (poly_slide r t2 p [])      by poly_slide_def
   Step: !p t1 t2. weak p /\ weak q /\ weak t1 /\ weak t2 ==>
                   poly_slide r (t1 || t2) p q = t1 || poly_slide r t2 p q ==>
         !h p t1 t2. weak p /\ weak (h::q) /\ weak t1 /\ weak t2 ==>
                     poly_slide r (t1 || t2) p (h::q) = t1 || poly_slide r t2 p (h::q)
         poly_slide r (t1 || t2) p (h::q)
       = poly_slide r ((h o p) || (t1 || t2)) (turn p) q   by poly_slide_def
       = poly_slide r ((h o p) || t1 || t2) (turn p) q     by weak_add_assoc
       = poly_slide r (t1 || (h o p) || t2) (turn p) q     by weak_add_comm
       = poly_slide r (t1 || ((h o p) || t2)) (turn p) q   by weak_add_assoc
       = t1 || poly_slide r ((h o p) || t2) (turn p) q     by induction hypothesis
       = t1 || poly_slide r t2 p (h::q)                    by poly_slide_def
*)
val poly_slide_add = store_thm(
  "poly_slide_add",
  ``!r:'a ring. Ring r ==> !p q t1 t2. weak p /\ weak q /\ weak t1 /\ weak t2 ==>
       (poly_slide r (t1 || t2) p q = t1 || poly_slide r t2 p q)``,
  ntac 2 strip_tac >>
  Induct_on `q` >-
  rw[poly_slide_def] >>
  rw[poly_slide_def, weak_turn] >>
  qabbrev_tac `t = poly_slide r t2 (turn p) q` >>
  `weak (h o p)` by rw[] >>
  `weak t` by rw[poly_slide_weak, weak_turn, Abbr`t`] >>
  rw[weak_add_assoc, weak_add_comm]);

(*
EVAL ``poly_slide (ZN 10) (weak_cmult (ZN 10) 3 [1;2;3]) (turn [1;2;3]) [4;5]``; = [5; 5; 2]: thm
EVAL ``weak_add (ZN 10) (weak_cmult (ZN 10) 3 [1;2;3]) (poly_slide (ZN 10) [] (turn [1;2;3]) [4;5])``; = [5; 5; 2]: thm

EVAL ``poly_slide (ZN 10) (weak_cmult (ZN 10) 3 [1;2]) (turn [1;2]) [4;5]``; = [6; 0]: thm
EVAL ``weak_add (ZN 10) (weak_cmult (ZN 10) 3 [1;2]) (poly_slide (ZN 10) [] (turn [1;2]) [4;5])``; = [6; 0]: thm

They are equal because:

EVAL ``weak_cmult (ZN 10) 3 [1;2]``; = [3; 6]: thm
EVAL ``turn [1;2]``; = [2; 1]: thm
EVAL ``poly_slide (ZN 10) [] (turn [1;2]) [4;5]``; = [3; 4]: thm
(1 + 2 x)(4 + 5x) = 4 + 5 x + 8 x + 10 x ** 2 = 4 + 3 x + 10 = 4 + 3x
EVAL ``poly_slide (ZN 10) [] (turn [1;2]) [1;2]``; = [4; 5]: thm
EVAL ``poly_slide (ZN 10) [] [1;2] [4;5]``; = [4; 3]: thm


poly_slide r [] (turn p) q = turn (poly_slide r [] p q)
poly_slide r q (turn p) t = q || turn (poly_slide r [] p t) <-- this is most general

EVAL ``poly_slide (ZN 10) [6] (turn [1;2]) [4;5]``; = [9; 4]: thm
EVAL ``weak_add (ZN 10) [6] (turn (poly_slide (ZN 10) [] [1;2] [4;5]))``; = [9; 4]: thm
*)

(* Theorem: Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
            (poly_slide r t (turn p) q = t || turn (poly_slide r |0| p q)) *)
(* Proof:
   By induction on q.
   Base: !p t. weak p /\ weak [] /\ weak t ==>
               poly_slide r t (turn p) [] = t || turn (poly_slide r |0| p [])
      LHS = poly_slide r t (turn p) [] = t       by poly_slide_def
      RHS = t || turn (poly_slide r |0| p [])
          = t || turn |0|                        by poly_slide_def
          = t || |0|                             by turn_nil
          = t = LHS                              by weak_add_zero
   Step: !p t. weak p /\ weak q /\ weak t ==>
               poly_slide r t (turn p) q = t || turn (poly_slide r |0| p q) ==>
         !h p t. weak p /\ weak q /\ weak t ==>
                 poly_slide r t (turn p) (h::q) = t || turn (poly_slide r |0| p (h::q))
       Let p' = turn p, t' = h o p' || t, q' = poly_slide r |0| p' q.
       Then weak p'                              by weak_turn
        and weak t'                              by weak_cmult_weak, weak_add_weak
        and weak q'                              by poly_slide_weak, Ring r
       If q = [],
         poly_slide r t (turn p) [h]
       = h o (turn p) || t                       by poly_slide_def
       = t || h o (turn p)                       by weak_add_comm
       = t || turn (h o p)                       by weak_cmult_turn
       = t || turn (h o p || |0|)                by weak_add_zero
       = t || turn (poly_slide r |0| p [h])      by poly_slide_def
       If q <> [],
        Then LENGTH q' = LENGTH p'               by poly_slide_length, q <> []
                       = LENGTH p                by turn_length
        and LENGTH (h o p) = LENGTH p            by weak_cmult_length
         poly_slide r t (turn p) (h::q)
       = poly_slide r ((h o (turn p)) || t) (turn (turn p)) q)         by poly_slide_def
       = ((h o (turn p)) || t) || turn (poly_slide r |0| (turn p) q)   by induction hypothesis, t' and p'
       = turn (h o p) || t || turn (poly_slide r |0| (turn p) q)       by weak_cmult_turn
       = t || turn (h o p) || turn (poly_slide r |0| (turn p) q)       by weak_add_assoc, weak_add_comm, need Ring r
       = t || turn ((h o p) || poly_slide r |0| (turn p) q)            by weak_add_turn, same length
       = t || turn (poly_slide r (h o p || |0|) (turn p) q)            by poly_slide_add
       = t || turn (poly_slide r |0| p (h::q))                         by poly_slide_def
*)
val poly_slide_turn = store_thm(
  "poly_slide_turn",
  ``!r:'a ring. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
         (poly_slide r t (turn p) q = t || turn (poly_slide r |0| p q))``,
  ntac 2 strip_tac >>
  Induct_on `q` >-
  rw[poly_slide_def, turn_nil] >>
  rw[poly_slide_def] >>
  qabbrev_tac `p' = turn p` >>
  qabbrev_tac `t' = h o p' || t` >>
  `weak p'` by rw[weak_turn, Abbr`p'`] >>
  `weak t'` by rw[Abbr`t'`] >>
  `t' = turn (h o p) || t` by rw[weak_cmult_turn, Abbr`t'`] >>
  `_ = t || turn (h o p)` by rw[weak_add_comm, weak_turn] >>
  Cases_on `q = []` >-
  rw[poly_slide_def, turn_nil] >>
  qabbrev_tac `q' = poly_slide r |0| p' q` >>
  `LENGTH q' = LENGTH p` by rw[poly_slide_length, turn_length, Abbr`q'`, Abbr`p'`] >>
  `LENGTH (h o p) = LENGTH p` by rw[weak_cmult_length] >>
  `weak q'` by rw[poly_slide_weak, Abbr`q'`] >>
  `poly_slide r t' (turn p') q = t' || turn (poly_slide r |0| p' q)` by rw[] >>
  `_ = t || (turn (h o p) || turn q')` by rw[weak_add_assoc, weak_turn] >>
  `_ = t || turn (h o p || q')` by rw[weak_add_turn] >>
  `_ = t || turn (poly_slide r (h o p) p' q)` by rw[GSYM poly_slide_add, Abbr`q'`] >>
  rw[poly_slide_def, Abbr`p'`]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q /\ q <> |0| ==>
            !t. zerop t /\ (LENGTH t <= LENGTH p) ==> (poly_slide r t p q = poly_slide r |0| p q) *)
(* Proof:
   Note q <> []                      by poly_zero, q <> |0|
    ==> ?h s. q = h::s               by list_CASES
    and h IN R                       by weak_cons
   Thus weak (h o p)                 by weak_cmult_weak
    and LENGTH (h o p) = LENGTH p    by weak_cmult_length
    ==> h o p || t = h o p           by weak_add_rzero_poly, LENGTH t <= LENGTH (h o p)

      poly_slide r t p q
    = poly_slide r t p (h::s)                by q = h::s
    = poly_slide r (h o p || t) (turn p) s   by poly_slide_def
    = poly_slide r (h o p) (turn p) s        by above
    = poly_slide r |0| p (h::s)              by poly_slide_def
    = poly_slide r |0| p q                   by q = h::s
*)
val poly_slide_init_zero_poly = store_thm(
  "poly_slide_init_zero_poly",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q /\ q <> |0| ==>
   !t. zerop t /\ (LENGTH t <= LENGTH p) ==> (poly_slide r t p q = poly_slide r |0| p q)``,
  rpt strip_tac >>
  `?h s. q = h::s` by metis_tac[poly_zero, list_CASES] >>
  `weak (h o p)` by metis_tac[weak_cons, weak_cmult_weak] >>
  rw[poly_slide_def, weak_add_rzero_poly, weak_cmult_length]);

(* Theorem: 0 < LENGTH q /\ weak q ==>
            (poly_slide r a p q = poly_slide r (((TAKE 1 q) o p) || a) (turn p) (DROP 1 q)) *)
(* Proof:
   Note q <> 0            by LENGTH_NIL, 0 < LENGTH q
     so ?h t. q = h::t    by list_CASES
    and h IN R /\ weak t  by weak_cons
    Now TAKE 1 q = [h]    by TAKE_def
    and DROP 1 q = t      by DROP_def
        poly_slide r a p q
      = poly_slide r a p (h::t)                 by notation
      = poly_slide r (h o p || a) (turn p) t    by poly_slide_def
      = poly_slide r ([h] o p || a) (turn p) t  by weak_mult_const
      = poly_slide r ((TAKE 1 q) o p || a) (turn p) (DROP 1 q)   by above
*)
val poly_slide_eqn_1 = store_thm(
  "poly_slide_eqn_1",
  ``!r:'a ring. !(a p):'a poly. !q. 0 < LENGTH q /\ weak q ==>
   (poly_slide r a p q = poly_slide r (((TAKE 1 q) o p) || a) (turn p) (DROP 1 q))``,
  rpt strip_tac >>
  `LENGTH q <> 0` by decide_tac >>
  `q <> [] /\ ?h t. q = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
  `poly_slide r a p (h::t) = poly_slide r (h o p || a) (turn p) t` by rw[poly_slide_def] >>
  `_ = poly_slide r ([h] o p || a) (turn p) t` by rw[weak_mult_const] >>
  rw[]);

(* Theorem: Ring r ==> !a p. weak a /\ weak p ==> !q. 1 < LENGTH q /\ weak q ==>
            (poly_slide r a p q =
             poly_slide r ((EL 1 q) o (turn p) || (EL 0 q) o p || a) (turn_exp p 2) (DROP 2 q)) *)
(* Proof:
   Note LENGTH q <> 0                by 1 < LENGTH q
   Thus q <> [] /\ ?h s. q = h::s    by LENGTH_NIL, list_CASES
    Now LENGTH s = LENGTH q - 1      by LENGTH
     so LENGTH s <> 0                by 1 < LENGTH q
    and s <> [] /\ ?k t. s = k::t    by LENGTH_NIL, list_CASES
   Note k IN R /\ h IN R /\ weak t   by weak_cons
    and weak k o (turn p)            by weak_turn, weak_cmult_weak
    and weak (h o p)                 by weak_cmult_weak

        poly_slide r a p q
      = poly_slide r (h o p || a) (turn p) (k::t)                       by poly_slide_def
      = poly_slide r (k o (turn p) || (h o p || a)) (turn (turn p)) t   by poly_slide_def
      = poly_slide r (k o (turn p) || (h o p) || a) (turn (turn p)) t   by weak_add_assoc

    Now EL 0 q = h                   by EL
    and EL 1 q = EL 0 s = k          by EL_restricted, EL
    and DROP 2 q = DROP 1 s = t      by DROP, DROP_def
    and turn_exp p 2 = turn (turn p) by turn_exp_2
   Thus the result follows.
*)
val poly_slide_eqn_2 = store_thm(
  "poly_slide_eqn_2",
  ``!r:'a ring. Ring r ==> !a p. weak a /\ weak p ==> !q. 1 < LENGTH q /\ weak q ==>
   (poly_slide r a p q =
    poly_slide r ((EL 1 q) o (turn p) || (EL 0 q) o p || a) (turn_exp p 2) (DROP 2 q))``,
  rpt strip_tac >>
  `LENGTH q <> 0` by decide_tac >>
  `q <> [] /\ ?h s. q = h::s` by metis_tac[LENGTH_NIL, list_CASES] >>
  `LENGTH s = LENGTH q - 1` by rw[] >>
  `LENGTH s <> 0` by decide_tac >>
  `s <> [] /\ ?k t. s = k::t` by metis_tac[LENGTH_NIL, list_CASES] >>
  `k IN R /\ h IN R /\ weak t` by metis_tac[weak_cons] >>
  `poly_slide r a p q = poly_slide r (h o p || a) (turn p) (k::t)` by rw[poly_slide_def] >>
  `_ = poly_slide r (k o (turn p) || (h o p || a)) (turn (turn p)) t` by rw[poly_slide_def] >>
  `_ = poly_slide r (k o (turn p) || (h o p) || a) (turn (turn p)) t` by rw[weak_add_assoc, weak_turn] >>
  `EL 0 q = h` by rw[] >>
  `EL 1 q = EL 0 s` by metis_tac[EL_restricted, ONE] >>
  `_ = k` by rw[] >>
  `DROP 2 q = DROP 1 s` by metis_tac[DROP, TWO] >>
  `_ = t` by rw[] >>
  rw[turn_exp_2]);

(*

  poly_slide r |0| p [4; 3; 2; 1]
= poly_slide r (|0| + (TAKE 0 [4; 3; 2; 1]) * p) (FUNPOW turn 0 p) (DROP 0 [4; 3; 2; 1])
= poly_slide r (|0| + (TAKE 1 [4; 3; 2; 1]) * p) (FUNPOW turn 1 p) (DROP 1 [4; 3; 2; 1])
= poly_slide r (|0| + (TAKE 2 [4; 3; 2; 1]) * p) (FUNPOW turn 2 p) (DROP 2 [4; 3; 2; 1])
= poly_slide r (|0| + (TAKE 3 [4; 3; 2; 1]) * p) (FUNPOW turn 3 p) (DROP 3 [4; 3; 2; 1])
= poly_slide r (|0| + (TAKE 4 [4; 3; 2; 1]) * p) (FUNPOW turn 4 p) (DROP 4 [4; 3; 2; 1])
----------------------- have to express this part as constant length as (LENGTH p)

  unity_mod_mult r p [4; 3; 2; 1]          k = LENGTH p
= poly_slide r |0| p [4; 3; 2; 1]
= poly_slide r (4 * p + |0|) (turn p) [3; 2; 1]
= poly_slide r (3 * (turn p) + 4 * p + |0|) (turn (turn p)) [2; 1]
= poly_slide r (2 * (turn (turn p)) + 3 * (turn p) + 4 * p + |0|) (turn (turn (turn p))) [1]
= poly_slide r (1 * (turn (turn (turn p))) + 2 * (turn (turn p)) + 3 * (turn p) + 4 * p + |0|) (turn (turn (turn (turn p)))) []
= 1 * (turn (turn (turn p))) + 2 * (turn (turn p)) + 3 * (turn p) + 4 * p + |0|
= (1 * (turn (turn (turn p))) + 2 * (turn (turn p)) + 3 * (turn p) + 4 * p + |0|) % z
= (p * [4; 3; 2; 1]) % z

g `!r:'a ring. Ring r /\ #1 <> #0 ==> !(a p):'a poly. LENGTH a <= LENGTH p ==>
   !n q. poly_slide r a p q = poly_slide r t (FUNPOW turn n p) (DROP n q)
     where chop t = (a + (TAKE n q) * p) % (unity (LENGTH p))`;
-- Question: how to formulate this?
-- Question: what this the best expression for t?
-- Roughly:   t = (repeated ||-sum of: (EL n q) o (FUNPOW turn n p)) || a

This is because:

    (p * q) % z = (p * SUM+ (q ' k) * X ** k) % z
                = (SUM+ (q ' k) * p * X ** k) % z
                = (SUM+ (q ' k) * (p * X ** k) % z) % z
                = (SUM+ (q ' k) * ((p * X) % z) ** k)) % z
                = (SUM+ (q ' k) * (chop (turn p)) ** k) % z
                = (SUM+ (q ' k) * chop (FUNPOW turn k p)) % z
                = (SUM+ chop (q ' k) o (FUNPOW turn k p)) % z   by poly_cmult_def
                = (chop (SUM|| (q ' k) o (FUNPOW turn k p))) % z  by poly_add_def


*)

(* Theorem: Ring r /\ #1 <> #0 ==> !(a p):'a poly. weak a /\ weak p /\ LENGTH a <= LENGTH p ==>
            !n q. weak q /\ n <= LENGTH q ==> (poly_slide r a p q =
             poly_slide r (psum (GENLIST (\k. (q ' k) o (turn_exp p k)) n) || a) (turn_exp p n) (DROP n q)) *)
(* Proof:
   By induction on n.
   Base: poly_slide r a p q =
         poly_slide r (psum (GENLIST (\k. q ' k o turn_exp p k) 0) || a) (turn_exp p 0) (DROP 0 q)
      Note DROP 0 q = q            by DROP_0
       and turn_exp p 0 = p        by turn_exp_0
       and psum (GENLIST (\k. q ' k o turn_exp p k) 0) || a
         = psum [] || a            by GENLIST
         = |0| || a                by poly_weak_sum_nil
         = a                       by weak_add_lzero
      Thus LHS = RHS.
   Step: poly_slide r a p q =
         poly_slide r (psum (GENLIST (\k. q ' k o turn_exp p k) n) || a) (turn_exp p n) (DROP n q) ==>
         poly_slide r a p q =
         poly_slide r (psum (GENLIST (\k. q ' k o turn_exp p k) (SUC n)) || a) (turn_exp p (SUC n)) (DROP (SUC n) q)

      Let f = \k. q ' k o turn_exp p k, b = psum (GENLIST f n)).
      Note n < LENGTH q               by SUC n <= LENGTH q
      Let c = EL n q = q ' n          by poly_coeff_as_element, n < LENGTH q
       so c IN R                      by weak_coeff_element
      and weak (c o (turn_exp p n))   by weak_turn_exp
      Now wfun f                      by weak_fun_def, weak_coeff_element, weak_turn_exp, weak_cmult_weak
      ==> plist (GENLIST f n)         by poly_weak_list_from_weak_fun
      ==> weak b                      by poly_weak_sum_weak

         poly_slide r a p q
       = poly_slide r (b || a) (turn_exp p n) (DROP n q)            by induction hypothesis
       = poly_slide r (b || a) (turn_exp p n) (c::DROP (SUC n) q)   by DROP_BY_DROP_SUC, n < LENGTH q
       = poly_slide r (c o (turn_exp p n) || (b || a)) (turn (turn_exp p n)) (DROP (SUC n) q)   by poly_slide_def
       = poly_slide r (c o (turn_exp p n) || (b || a)) (turn_exp p (SUC n)) (DROP (SUC n) q)    by turn_exp_suc
       = poly_slide r (c o (turn_exp p n) || b || a) (turn_exp p (SUC n)) (DROP (SUC n) q)      by weak_add_assoc

         c o turn_exp p n || b
       = (q ' n) o turn_exp p n || psum (GENLIST f n))   by notation
       = (f n) || psum (GENLIST f n)                     by applying f
       = psum (GENLIST f (SUC n))                        by poly_weak_sum_genlist_suc

      Hence the result follows.
*)
val poly_slide_eqn = store_thm(
  "poly_slide_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !(a p):'a poly. weak a /\ weak p /\ LENGTH a <= LENGTH p ==>
   !n q. weak q /\ n <= LENGTH q ==> (poly_slide r a p q =
    poly_slide r (psum (GENLIST (\k. (q ' k) o (turn_exp p k)) n) || a) (turn_exp p n) (DROP n q))``,
  ntac 5 strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  qabbrev_tac `f = \k. q ' k o turn_exp p k` >>
  qabbrev_tac `b = psum (GENLIST f n)` >>
  qabbrev_tac `c = EL n q` >>
  `n < LENGTH q` by decide_tac >>
  `LENGTH q <> 0` by decide_tac >>
  `q <> |0|` by metis_tac[LENGTH_NIL, poly_zero] >>
  `c = q ' n` by metis_tac[poly_coeff_as_element, Abbr`c`] >>
  `c IN R` by rw[weak_coeff_element] >>
  `weak (c o (turn_exp p n))` by rw[weak_turn_exp] >>
  `wfun f` by rw[weak_fun_def, weak_turn_exp, weak_coeff_element, weak_cmult_weak, Abbr`f`] >>
  `weak b` by rw[poly_weak_list_from_weak_fun, poly_weak_sum_weak, Abbr`b`] >>
  `poly_slide r a p q = poly_slide r (b || a) (turn_exp p n) (DROP n q)` by rw[Abbr`b`] >>
  `_ = poly_slide r (b || a) (turn_exp p n) (c::DROP (SUC n) q)` by rw[DROP_BY_DROP_SUC, Abbr`c`] >>
  `_ = poly_slide r (c o (turn_exp p n) || (b || a)) (turn (turn_exp p n)) (DROP (SUC n) q)` by rw[poly_slide_def] >>
  `_ = poly_slide r (c o (turn_exp p n) || (b || a)) (turn_exp p (SUC n)) (DROP (SUC n) q)` by rw[turn_exp_suc] >>
  `_ = poly_slide r (c o (turn_exp p n) || b || a) (turn_exp p (SUC n)) (DROP (SUC n) q)` by rw[weak_add_assoc] >>
  `c o turn_exp p n || b = (f n) || psum (GENLIST f n)` by rw[Abbr`b`, Abbr`c`, Abbr`f`] >>
  `_ = psum (GENLIST f (SUC n))` by rw[poly_weak_sum_genlist_suc] >>
  rw[]);

(* This is a major milestone result! *)

(*
> EVAL ``unity_mod (ZN 5) [4; 3; 2; 1]``; --> [0; 3; 2]
> EVAL ``unity_mod_mult (ZN 5) [0; 3; 2] [4; 3; 2; 1]``; --> [2; 4; 4]
> EVAL ``unity_mod_mult (ZN 5) [0; 3; 2] [0; 3; 2]``; --> [2; 4; 4]
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ q <> |0| ==>
            (unity_mod_mult r p q = psum (GENLIST (\k. (q ' k) o (turn_exp p k)) (SUC (deg q)))) *)
(* Proof:
   Let f = \k. q ' k o turn_exp p k, b = psum (GENLIST f n).
   Note wfun f                     by weak_fun_def, weak_coeff_element, weak_turn_exp, weak_cmult_weak
    ==> plist (GENLIST f n)        by poly_weak_list_from_weak_fun
    ==> weak b                     by poly_weak_sum_weak
   Thus b || |0| = b               by weak_add_rzero

   Note LENGTH |0| = 0             by poly_zero
    and 0 <= LENGTH p
   Let n = LENGTH q.
   Then n <> 0                     by LENGTH_NIL, q <> |0|
    and deg q = PRE n              by poly_deg_def, q <> |0|
   Thus n = SUC (deg q)            by arithmetic
   Also DROP n q = []              by DROP_LENGTH_NIL

     unity_mod_mult r p q
   = poly_slide r |0| p q              by unity_mod_mult_def
   = poly_slide r b (turn_exp p n) []  by poly_slide_eqn
   = b                                 by poly_slide_def
   = psum (GENLIST (\k. (q ' k) o (turn_exp p k)) (SUC (deg q))  by notation, above
*)
val unity_mod_mult_alt = store_thm(
  "unity_mod_mult_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ q <> |0| ==>
         (unity_mod_mult r p q = psum (GENLIST (\k. (q ' k) o (turn_exp p k)) (SUC (deg q))))``,
  rpt strip_tac >>
  `LENGTH |0| = 0` by rw[] >>
  `LENGTH |0| <= LENGTH p` by decide_tac >>
  qabbrev_tac `n = LENGTH q` >>
  `poly_slide r |0| p q =
    poly_slide r (psum (GENLIST (\k. q ' k o turn_exp p k) n) || |0|) (turn_exp p n) (DROP n q)` by rw[poly_slide_eqn] >>
  qabbrev_tac `f = \k. q ' k o turn_exp p k` >>
  qabbrev_tac `b = psum (GENLIST f n)` >>
  `wfun f` by rw[weak_fun_def, weak_turn_exp, weak_coeff_element, weak_cmult_weak, Abbr`f`] >>
  `weak b` by rw[poly_weak_list_from_weak_fun, poly_weak_sum_weak, Abbr`b`] >>
  `b || |0| = b` by rw[] >>
  `n <> 0` by metis_tac[LENGTH_NIL] >>
  `deg q = PRE n` by rw[poly_deg_def, Abbr`n`] >>
  `n = SUC (deg q)` by decide_tac >>
  `DROP n q = []` by rw[DROP_LENGTH_NIL, Abbr`n`] >>
  rw[poly_slide_def, unity_mod_mult_def]);

(* Theorem: (unity_mod_mult r p |0| = |0|) /\ (unity_mod_mult r |0| p = |0|) *)
(* Proof: by unity_mod_mult_def, poly_slide_zero. *)
val unity_mod_mult_zero_alt = store_thm(
  "unity_mod_mult_zero_alt",
  ``!r:'a ring p. (unity_mod_mult r p |0| = |0|) /\ (unity_mod_mult r |0| p = |0|)``,
  rw[unity_mod_mult_def, poly_slide_zero]);


(* Theorem: Ring r ==> !p h t. weak p /\ weak (h::t) ==>
            unity_mod_mult r p (h::t) = (h o p || unity_mod_mult r (turn p) t) *)
(* Proof:
   Note h IN R and weak t                     by weak_cons
   Thus weak (h o p)                          by weak_cmult_weak
    and weak (turn p)                         by weak_turn
     unity_mod_mult r p (h::t)
   = poly_slide r |0| p (h::t)                by unity_mod_mult_def
   = poly_slide r (h o p || |0|) (turn p) t   by poly_slide_def
   = h o p || poly_slide r |0| (turn p) t     by poly_slide_add
   = h o p || unity_mod_mult r (turn p) t     by unity_mod_mult_def
*)
val unity_mod_mult_cons = store_thm(
  "unity_mod_mult_cons",
  ``!r:'a ring. Ring r ==> !p h t. weak p /\ weak (h::t) ==>
         (unity_mod_mult r p (h::t) = (h o p || unity_mod_mult r (turn p) t))``,
  rw[weak_cons] >>
  `unity_mod_mult r p (h::t) = poly_slide r |0| p (h::t)` by rw[unity_mod_mult_def] >>
  `_ = poly_slide r (h o p || |0|) (turn p) t` by rw[poly_slide_def] >>
  `_ = h o p || poly_slide r |0| (turn p) t` by rw[GSYM poly_slide_add, weak_turn] >>
  `_ = h o p || unity_mod_mult r (turn p) t` by rw[unity_mod_mult_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> weak (unity_mod_mult r p q) *)
(* Proof:
   Note unity_mod_mult r p q
      = poly_slide r |0| p q         by unity_mod_mult_def
    and weak |0|                     by weak_zero
    ==> weak (poly_slide r |0| p q)  by poly_slide_weak
*)
val unity_mod_mult_weak = store_thm(
  "unity_mod_mult_weak",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> weak (unity_mod_mult r p q)``,
  rw[unity_mod_mult_def, poly_slide_weak]);

(* Theorem: Ring r ==> !p. weak p ==> weak (unity_mod_sq r p) *)
(* Proof:
   Note unity_mod_sq r p
      = unity_mod_mult r p p      by unity_mod_sq_def
   Thus weak (unity_mod_sq r p)   by unity_mod_mult_weak
*)
val unity_mod_sq_weak = store_thm(
  "unity_mod_sq_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> weak (unity_mod_sq r p)``,
  rw[unity_mod_sq_def, unity_mod_mult_weak]);

(* Theorem: Ring r ==> !n p. weak p ==> weak (unity_mod_exp r p n) *)
(* Proof:
   By complete induction on n.
   If n = 0,
      Then unity_mod_exp r p 0 = |1|       by unity_mod_exp_def
       and weak |1| = T                    by poly_one_poly, poly_is_weak
   If n <> 0,
      Note HALF n < n                      by DIV_LESS, 0 < n, 1 < 2.
      Let q = unity_mod_exp r (unity_mod_sq r p) (HALF n)
      Note weak (unity_mod_sq r p)         by unity_mod_sq_weak
      Then weak q                          by induction hypothesis
      If EVEN n,
         Then unity_mod_exp r p n = q      by unity_mod_exp_def
      If ~EVEN n
         Then unity_mod_exp r p n
            = unity_mod_mult r p q         by unity_mod_exp_def
          and weak (unity_mod_mult r p q)  by unity_mod_mult_weak
*)
val unity_mod_exp_weak = store_thm(
  "unity_mod_exp_weak",
  ``!r:'a ring. Ring r ==> !n p. weak p ==> weak (unity_mod_exp r p n)``,
  ntac 2 strip_tac >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    rw_tac std_ss[Once unity_mod_exp_def] >>
    rw[],
    `HALF n < n` by rw[] >>
    `weak (unity_mod_sq r p)` by rw[unity_mod_sq_weak] >>
    `weak (unity_mod_exp r (unity_mod_sq r p) (HALF n))` by rw[] >>
    rw_tac std_ss[Once unity_mod_exp_def] >>
    rw[unity_mod_mult_weak]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ 1 < LENGTH p /\ q <> |0| ==>
            (chop (unity_mod_mult r p q) = (p * q) % (unity (LENGTH p))) *)
(* Proof:
   The essential idea is:
      p * q
    = p * poly_sum (GENLIST (\k. q ' k * X ** k) (SUC (deg q)))                poly_eq_poly_sum, poly q!
    = poly_sum (MAP (\x. p * x) (GENLIST (\k. q ' k * X ** k) (SUC (deg q))))  by poly_mult_poly_sum, poly p!
    = poly_sum (GENLIST (\x. p * x) o (\k. q ' k * X ** k) (SUC (deg q)))      by MAP_GENLIST
    = poly_sum (GENLIST (\k. q ' k * p * X ** k) (SUC (deg q)))                by poly_mult_cmult, poly p!

      (p * q) % z
    = (poly_sum (GENLIST (\k. q ' k * p * X ** k) (SUC (deg q)))) % z
    = (poly_sum (MAP (\x. x % z) (GENLIST (\k. q ' k * p * X ** k) (SUC (deg q))))) % z      by poly_mod_poly_sum, poly_list s!
    = (poly_sum (GENLIST (\k. (q ' k * p * X ** k) % z) (SUC (deg q)))) % z                  by MAP_GENLIST
    = (poly_sum (GENLIST (\k. (q ' k * (p * X ** k) % z) % z) (SUC (deg q)))) % z            by poly_mod_cmult, poly (p * X ** k) -- ok
    = (poly_sum (GENLIST (\k. (q ' k * (chop (turn_exp p k))) % z) (SUC (deg q)))) % z       by chop_turn_exp_eqn
    = (poly_sum (GENLIST (\k. chop (q ' k o (chop (turn_exp p k))) % z) (SUC (deg q)))) % z  by poly_mult_def
    = (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k) % z) (SUC (deg q)))) % z   by poly_chop_cmult
    = (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q)))) % z       by poly_mod_less, as LENGTH (q ' k o turn_exp p k) = LENGTH p.
    = (poly_sum (MAP chop (GENLIST (\k. (q ' k o turn_exp p k)) (SUC (deg q))))) % z by MAP_GENLIST
    = (chop (psum (GENLIST (\k. (q ' k o turn_exp p k)) (SUC (deg q))))) % z         by poly_chop_weak_sum
    = (chop (unity_mod_mult r p q)) % z      by unity_mod_mult_alt
    = chop (unity_mod_mult r p q)            by poly_mod_less, LENGTH (unity_mod_mult r p q) = LENGTH p, by unity_mod_mult_length

   Let k = LENGTH p, z = unity k.
   Note k <> 0                    by 1 < k ==> 0 < k
     so pmonic z                  by poly_unity_pmonic, 0 < k
    and q <> []                   by poly_zero, q <> |0|
    and !k. weak (turn_exp p k)   by weak_turn_exp
   Let pc = chop p, qc = chop q.
   Then poly pc /\ poly qc        by poly_chop_weak_poly

   Stage 1: chop (unity_mod_mult r p q)
            = (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q)))) % z
   Let f1 = \k. q ' k o turn_exp p k,
   and f2 = \k. chop (q ' k o turn_exp p k)
   Note wfun f1                            by weak_fun_def, weak_cmult_weak
    ==> plist (GENLIST f1 (SUC (deg q)))   by poly_weak_list_from_weak_fun, [1]
   Also chop o f1 = f2                     by FUN_EQ_THM
   Note weak (unity_mod_mult r p q)        by unity_mod_mult_weak
    and LENGTH (unity_mod_mult r p q) = k  by unity_mod_mult_length, q <> []

     chop (unity_mod_mult r p q)
   = (chop (unity_mod_mult r p q)) % z                      by poly_mod_less_weak, 0 < k
   = (chop (psum (GENLIST f1 (SUC (deg q))))) % z           by unity_mod_mult_alt, q <> |0|
   = (poly_sum (MAP chop (GENLIST f1 (SUC (deg q))))) % z   by poly_chop_weak_sum, [1]
   = (poly_sum (GENLIST (chop o f1) (SUC (deg q)))) % z     by MAP_GENLIST
   = (poly_sum (GENLIST f2 (SUC (deg q)))) % z              by f2 = chop o f1
   = (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q)))) % z  by notation

   Stage 2: (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q)))) % z
            = (poly_sum (GENLIST (\k. (q ' k * p * X ** k) % z) (SUC (deg q)))) % z
   Let f3 = \k. (q ' k * p * X ** k) % z
   The result follows if f2 = f3. By FUN_EQ_THM, this is to show:
       !k'. chop (q ' k' o turn_exp p k') = (q ' k' * p * X ** k') % z

   Note weak (q ' k' o turn_exp p k')     by weak_cmult_weak
    and LENGTH (q ' k' o turn_exp p k')
      = LENGTH (turn_exp_2 p k')          by weak_cmult_length
      = k                                 by turn_exp_length

     chop (q ' k' o turn_exp p k')
   = (chop (q ' k' o turn_exp p k')) % z            by poly_mod_less_weak, 0 < k
   = (chop (q ' k' o (chop (turn_exp p k')))) % z   by poly_chop_cmult
   = (q ' k' * (chop (turn_exp p k'))) % z          by poly_cmult_def
   = (q ' k' * (p * X ** k') % z) % z               by chop_turn_exp_eqn, 1 < k
   = (q ' k' * (p * X ** k')) % z                   by poly_mod_cmult
   = (q ' k' * p * X ** k') % z                     by poly_cmult_mult_weak

   This completes Stage 2.

   Stage 3: (poly_sum (GENLIST (\k. (q ' k * p * X ** k) % z) (SUC (deg q)))) % z
            = (p * q) % z
   Let g1 = \k. qc ' k * X ** k
   and g2 = \k. qc ' k * (pc * X ** k)
   Note poly_fun g1                  by poly_fun_def, poly_cmult_poly
    ==> poly_list (GENLIST g1 (SUC (deg qc)))   by poly_list_gen_from_poly_fun, [2]
    and g2 = (\x. pc * x) o g1       by poly_mult_cmult, poly_cmult_mult, FUN_EQ_THM

   Let h = \k. p * X ** k, g3 = \k. qc ' k * (h k).
   Then g2 = g3                      by poly_mult_weak_right, FUN_EQ_THM
    and wfun h                       by weak_fun_def, poly_mult_weak_poly, poly_is_weak

   This is the trick using weak and chop:
     p * q
   = pc * qc                                                   by poly_mult_weak
   = pc * poly_sum (GENLIST g1 (SUC (deg qc)))                 by poly_eq_poly_sum
   = poly_sum (MAP (\x. pc * x) (GENLIST g1 (SUC (deg qc))))   by poly_mult_poly_sum, [2]
   = poly_sum (GENLIST g3 (SUC (deg qc)))                      by MAP_GENLIST
   = poly_sum (GENLIST (\k. qc ' k * (h k)) (SUC (deg qc)))    by notation
   = poly_sum (GENLIST (\k. q ' k * (h k)) (SUC (deg q)))      by weak_poly_sum_genlist, the magic key!

   Let h1 = \k. q ' k * (h k)
   and h2 = \k. (q ' k * p * X ** k) % z

   Claim: h2 = (\x. x % z) o h1
   Proof: By FUN_EQ_THM, this is to show:
          !k'. (q ' k' * p * X ** k') % z = (q ' k' * (p * X ** k')) % z
            (q ' k' * p * X ** k') % z
          = (q ' k' * pc * X ** k') % z     by poly_cmult_weak
          = (q ' k' * (pc * X ** k')) % z   by poly_cmult_mult
          = (q ' k' * (p * X ** k')) % z    by poly_mult_weak_right

   Note poly_fun h1                         by poly_fun_def, poly_mult_weak_poly
    and poly_list (GENLIST h1 (SUC (deg q)))   by poly_list_gen_from_poly_fun, [3]

     (p * q) % z
   = (poly_sum (GENLIST h1 (SUC (deg q)))) % z                    by p * q, above
   = (poly_sum (MAP (\x. x % z) (GENLIST h1 (SUC (deg q))))) % z  by poly_mod_poly_sum, [3]
   = (poly_sum (GENLIST h2 (SUC (deg q)))) % z                    by MAP_GENLIST

   This completes Stage 3, and the whole proof.
*)
val unity_mod_mult_eqn = store_thm(
  "unity_mod_mult_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. weak p /\ weak q /\ 1 < LENGTH p /\ q <> |0| ==>
               (chop (unity_mod_mult r p q) = (p * q) % (unity (LENGTH p)))``,
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `0 < k` by decide_tac >>
  `q <> []` by metis_tac[poly_zero] >>
  qabbrev_tac `pc = chop p` >>
  qabbrev_tac `qc = chop q` >>
  `poly pc /\ poly qc` by rw[poly_chop_weak_poly, Abbr`pc`, Abbr`qc`] >>
  `!k. poly (X ** k) /\ weak (X ** k)` by rw[] >>
  `!k. (qc ' k) IN R /\ (q ' k) IN R` by rw[weak_coeff_element] >>
  `!k. weak (turn_exp p k)` by rw[weak_turn_exp] >>
  `chop (unity_mod_mult r p q) = (poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q)))) % z` by
  (qabbrev_tac `f1 = \k. (q ' k o turn_exp p k)` >>
  `wfun f1` by rw_tac std_ss[weak_fun_def, weak_cmult_weak, Abbr`f1`] >>
  `plist (GENLIST f1 (SUC (deg q)))` by rw[poly_weak_list_from_weak_fun] >>
  qabbrev_tac `f2 = \k. chop (q ' k o turn_exp p k)` >>
  `chop o f1 = f2` by rw_tac std_ss[Abbr`f1`, Abbr`f2`, FUN_EQ_THM] >>
  `weak (unity_mod_mult r p q)` by rw[unity_mod_mult_weak] >>
  `LENGTH (unity_mod_mult r p q) = k` by rw[unity_mod_mult_length, Abbr`k`] >>
  `chop (unity_mod_mult r p q) = (chop (unity_mod_mult r p q)) % z` by metis_tac[poly_mod_less_weak] >>
  `_ = (chop (psum (GENLIST f1 (SUC (deg q))))) % z` by rw[unity_mod_mult_alt, Abbr`f1`] >>
  `_ = (poly_sum (MAP chop (GENLIST f1 (SUC (deg q))))) % z` by rw[poly_chop_weak_sum] >>
  `_ = (poly_sum (GENLIST (chop o f1) (SUC (deg q)))) % z` by rw[MAP_GENLIST] >>
  `_ = (poly_sum (GENLIST f2 (SUC (deg q)))) % z` by rw[] >>
  rw[]) >>
  `poly_sum (GENLIST (\k. chop (q ' k o turn_exp p k)) (SUC (deg q))) % z
    = (poly_sum (GENLIST (\k. (q ' k * p * X ** k) % z) (SUC (deg q)))) % z` by
    (qabbrev_tac `f2 = \k. chop (q ' k o turn_exp p k)` >>
  qabbrev_tac `f3 = \k. (q ' k * p * X ** k) % z` >>
  `f2 = f3` by
      (rw_tac std_ss[Abbr`f2`, Abbr`f3`, FUN_EQ_THM] >>
  `poly (p * X ** k')` by rw[poly_mult_weak_poly] >>
  `poly (X ** k') /\ weak (X ** k')` by rw[] >>
  `weak (q ' k' o turn_exp p k')` by rw[] >>
  `LENGTH (q ' k' o turn_exp p k') = k` by rw[weak_cmult_length, turn_exp_length] >>
  `chop (q ' k' o turn_exp p k') = (chop (q ' k' o turn_exp p k')) % z` by metis_tac[poly_mod_less_weak] >>
  `_ = (chop (q ' k' o (chop (turn_exp p k')))) % z` by metis_tac[poly_chop_cmult] >>
  `_ = (q ' k' * (chop (turn_exp p k'))) % z` by metis_tac[poly_cmult_def] >>
  `_ = (q ' k' * (p * X ** k') % z) % z` by rw_tac std_ss[chop_turn_exp_eqn] >>
  `_ = (q ' k' * (p * X ** k')) % z` by rw_tac std_ss[poly_mod_cmult] >>
  `_ = (q ' k' * p * X ** k') % z` by rw_tac std_ss[poly_cmult_mult_weak] >>
  rw[]) >>
  rw[]) >>
  `poly_sum (GENLIST (\k. (q ' k * p * X ** k) % z) (SUC (deg q))) % z = (p * q) % z` by
      (qabbrev_tac `g1 = \k. qc ' k * X ** k` >>
  `poly_fun g1` by rw_tac std_ss[poly_fun_def, poly_cmult_poly, Abbr`g1`] >>
  `poly_list (GENLIST g1 (SUC (deg qc)))` by rw[poly_list_gen_from_poly_fun] >>
  qabbrev_tac `g2 = \k. qc ' k * (pc * X ** k)` >>
  `g2 = (\x. pc * x) o g1` by rw_tac std_ss[poly_mult_cmult, poly_cmult_mult, FUN_EQ_THM, Abbr`g1`, Abbr`g2`] >>
  qabbrev_tac `h = \k. p * X ** k` >>
  qabbrev_tac `g3 = \k. qc ' k * (h k)` >>
  `g2 = g3` by rw_tac std_ss[poly_mult_weak_right, FUN_EQ_THM, Abbr`g2`, Abbr`g3`, Abbr`h`] >>
  `wfun h` by rw_tac std_ss[weak_fun_def, poly_mult_weak_poly, poly_is_weak, Abbr`h`] >>
  `p * q = pc * qc` by rw[GSYM poly_mult_weak, Abbr`pc`, Abbr`qc`] >>
  `_ = pc * poly_sum (GENLIST g1 (SUC (deg qc)))` by rw[GSYM poly_eq_poly_sum, Abbr`g1`] >>
  `_ = poly_sum (MAP (\x. pc * x) (GENLIST g1 (SUC (deg qc))))` by rw[poly_mult_poly_sum] >>
  `_ = poly_sum (GENLIST g3 (SUC (deg qc)))` by rw[MAP_GENLIST, Abbr`g2`] >>
  `_ = poly_sum (GENLIST (\k. qc ' k * (h k)) (SUC (deg qc)))` by rw[Abbr`g3`] >>
  `_ = poly_sum (GENLIST (\k. q ' k * (h k)) (SUC (deg q)))` by rw[weak_poly_sum_genlist, Abbr`qc`] >>
  qabbrev_tac `h1 = \k. q ' k * (h k)` >>
  qabbrev_tac `h2 = \k. (q ' k * p * X ** k) % z` >>
  `h2 = (\x. x % z) o h1` by
        (rw_tac std_ss[FUN_EQ_THM, Abbr`h`, Abbr`h1`, Abbr`h2`] >>
  `(q ' k' * p * X ** k') % z = (q ' k' * pc * X ** k') % z` by rw_tac std_ss[poly_cmult_weak, Abbr`pc`] >>
  `_ = (q ' k' * (pc * X ** k')) % z` by rw_tac std_ss[poly_cmult_mult] >>
  `_ = (q ' k' * (p * X ** k')) % z` by rw_tac std_ss[poly_mult_weak_right, Abbr`pc`] >>
  rw[]) >>
  `poly_fun h1` by rw[poly_fun_def, poly_mult_weak_poly, Abbr`h1`, Abbr`h`] >>
  `poly_list (GENLIST h1 (SUC (deg q)))` by rw[poly_list_gen_from_poly_fun] >>
  `(p * q) % z = (poly_sum (GENLIST h1 (SUC (deg q)))) % z` by metis_tac[] >>
  `_ = (poly_sum (MAP (\x. x % z) (GENLIST h1 (SUC (deg q))))) % z` by rw[poly_mod_poly_sum] >>
  `_ = (poly_sum (GENLIST h2 (SUC (deg q)))) % z` by metis_tac[MAP_GENLIST, Abbr`h1`, Abbr`h2`] >>
  rw[]) >>
  rw[]);

(* This is the next major milestone theorem, using the magic trick! *)

(* Theorem: Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
            (chop (unity_mod_sq r p) = (p * p) % (unity (LENGTH p))) *)
(* Proof:
   Note LENGTH p <> 0      by 1 < LENGTH p
     so p <> |0|           by LENGTH_NIL, poly_zero
   Thus the result follows by unity_mod_sq_def, unity_mod_mult_eqn
*)
val unity_mod_sq_eqn = store_thm(
  "unity_mod_sq_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
               (chop (unity_mod_sq r p) = (p * p) % (unity (LENGTH p)))``,
  rpt strip_tac >>
  `LENGTH p <> 0` by decide_tac >>
  `p <> |0|` by metis_tac[LENGTH_NIL, poly_zero] >>
  rw[unity_mod_sq_def, unity_mod_mult_eqn]);

(* Theorem: EVEN n ==> (unity_mod_exp r p n = unity_mod_exp r (unity_mod_sq r p) (HALF n)) *)
(* Proof:
   If n = 0,
      Then HALF 0 = 0     by ZERO_DIV, 0 < 2
      Thus true           by unity_mod_exp_0
   If n <> 0,
      Then true           by unity_mod_exp_def
*)
val unity_mod_exp_even = store_thm(
  "unity_mod_exp_even",
  ``!r:'a ring. !p n. EVEN n ==> (unity_mod_exp r p n = unity_mod_exp r (unity_mod_sq r p) (HALF n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[unity_mod_exp_0] >>
  rw[Once unity_mod_exp_def]);

(* Theorem: ODD n ==>
            (unity_mod_exp r p n = unity_mod_mult r p (unity_mod_exp r (unity_mod_sq r p) (HALF n))) *)
(* Proof:
   Note ~(EVEN n)    by EVEN_ODD
    and n <> 0       by EVEN
   Thus the result follows by unity_mod_exp_def
*)
val unity_mod_exp_odd = store_thm(
  "unity_mod_exp_odd",
  ``!r:'a ring. !p n. ODD n ==>
        (unity_mod_exp r p n = unity_mod_mult r p (unity_mod_exp r (unity_mod_sq r p) (HALF n)))``,
  rpt strip_tac >>
  `~(EVEN n) /\ n <> 0` by metis_tac[EVEN_ODD, EVEN] >>
  rw[Once unity_mod_exp_def]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n p. weak p /\ 1 < LENGTH p ==>
            (chop (unity_mod_exp r p n) = (p ** n) % (unity (LENGTH p))) *)
(* Proof:
   By complete induction on n.
   To show: !m. m < n ==> !p. weak p /\ 1 < LENGTH p ==>
                (chop (unity_mod_exp r p m) = p ** m % unity (LENGTH p)) ==>
            chop (unity_mod_exp r p n) = p ** n % z

   Let k = LENGTH p, z = unity k.
   Note k <> 0                by 1 < k ==> 0 < k
     so pmonic z              by poly_unity_pmonic, 0 < k
   If n = 0,
        chop (unity_mod_exp r p 0)
      = chop |1|              by unity_mod_exp_0
      = |1|                   by poly_chop_one, #1 <> #0
      = |1| % z               by poly_mod_one
      = (p ** 0) % z          by poly_exp_0

   If n = 1,
        chop (unity_mod_exp r p 1)
      = chop p                by unity_mod_exp_1, #1 <> #0
      = (chop p) % z          by poly_mod_less_weak
      = (p * |1|) % z         by poly_chop_weak_alt
      = (p ** 1) % z          by weak_exp_1

   If n <> 0, n <> 1, then 1 < n.
      Then HALF n < n         by DIV_LESS, 0 < n
       and HALF n <> 0        by HALF_EQ_0 (for q <> |0| later [1])
      Let pc = chop p.
      Then poly pc            by poly_chop_weak_poly
      Let t = (unity_mod_sq r p), q = unity_mod_exp r t (HALF n).
      Also weak t             by unity_mod_sq_weak
       and LENGTH t = k       by unity_mod_sq_length
      Thus t <> |0|           by LENGTH_NIL, k <> 0.
      Then weak q             by unity_mod_exp_weak
       and LENGTH q
         = LENGTH t           by unity_mod_exp_length, 0 < HALF n
         = k                  by above
      Thus q <> |0|           by LENGTH_NIL, k <> 0, [1], for later [2]

           chop q
         = t ** (HALF n) % z                by induction hypothesis
         = (chop t) ** (HALF n) % z         by poly_exp_weak
         = ((p * p) % z) ** (HALF n) % z    by unity_mod_sq_eqn
         = ((pc * pc) % z) ** (HALF n) % z  by poly_mult_weak
         = (pc * pc) ** (HALF n) % z        by poly_mod_exp
         = (p * p) ** (HALF n) % z          by poly_mult_weak

      If EVEN n,
           chop (unity_mod_exp r p n)
         = chop q                           by unity_mod_exp_def
         = (p * p) ** (HALF n) % z          by above
         = (pc * pc) ** (HALF n) % z        by poly_mult_weak
         = (pc ** n) % z                    by poly_exp_even
         = (p ** n) % z                     by poly_exp_weak
      If ~(EVEN n),
         Then ODD n                         by EVEN_ODD
           chop (unity_mod_exp r p n)
         = chop (unity_mod_mult r p q)      by unity_mod_exp_def
         = (p * q) % z                      by unity_mod_mult_eqn, q <> |0|, [2]
         = (pc * (chop q)) % z              by poly_mult_weak
         = (pc * (p * p) ** (HALF n) % z) % z          by above
         = (pc * (pc * pc) ** (HALF n) % z) % z        by poly_mult_weak
         = ((pc % z) * (pc * pc) ** (HALF n) % z) % z  by poly_mod_less_weak
         = (pc * (pc * pc) ** (HALF n)) % z            by poly_mod_mult
         = (pc ** n) % z                               by poly_exp_odd
         = (p ** n) % z                                by poly_exp_weak
*)
val unity_mod_exp_eqn = store_thm(
  "unity_mod_exp_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n p. weak p /\ 1 < LENGTH p ==>
               (chop (unity_mod_exp r p n) = (p ** n) % (unity (LENGTH p)))``,
  ntac 2 strip_tac >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  `0 < k` by decide_tac >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  Cases_on `n = 0` >-
  rw[unity_mod_exp_0] >>
  Cases_on `n = 1` >| [
    `chop (unity_mod_exp r p 1) = chop p` by rw[unity_mod_exp_1] >>
    `_ = (chop p) % z` by rw[poly_mod_less_weak, Abbr`z`, Abbr`k`] >>
    `_ = (p * |1|) % z`  by rw[poly_chop_weak_alt] >>
    `_ = (p ** 1) % z` by rw[weak_exp_1] >>
    rw[],
    `HALF n <> 0` by metis_tac[HALF_EQ_0] >>
    `HALF n < n` by rw[] >>
    qabbrev_tac `pc = chop p` >>
    `poly pc` by rw[poly_chop_weak_poly, Abbr`pc`] >>
    qabbrev_tac `t = (unity_mod_sq r p)` >>
    qabbrev_tac `q = unity_mod_exp r t (HALF n)` >>
    `weak t` by rw[unity_mod_sq_weak, Abbr`t`] >>
    `LENGTH t = k` by rw[unity_mod_sq_length, Abbr`t`, Abbr`k`] >>
    `t <> |0|` by metis_tac[LENGTH_NIL, poly_zero, NOT_ZERO] >>
    `weak q` by rw[unity_mod_exp_weak, Abbr`q`] >>
    `LENGTH q = k` by metis_tac[unity_mod_exp_length, NOT_ZERO] >>
    `q <> |0|` by metis_tac[LENGTH_NIL, poly_zero, NOT_ZERO] >>
    `chop q = t ** (HALF n) % z` by rw_tac std_ss[Abbr`q`, Abbr`t`] >>
    `_ = (chop t) ** (HALF n) % z` by rw_tac std_ss[poly_exp_weak] >>
    `_ = ((p * p) % z) ** (HALF n) % z` by rw_tac std_ss[unity_mod_sq_eqn, Abbr`t`] >>
    `_ = ((pc * pc) % z) ** (HALF n) % z` by rw_tac std_ss[poly_mult_weak] >>
    `_ = (pc * pc) ** (HALF n) % z` by rw_tac std_ss[poly_mod_exp, poly_mult_poly] >>
    `_ = (p * p) ** (HALF n) % z` by rw_tac std_ss[poly_mult_weak] >>
    Cases_on `EVEN n` >| [
      `chop (unity_mod_exp r p n) = chop q` by rw_tac std_ss[unity_mod_exp_even, Abbr`q`, Abbr`t`] >>
      `_ = (pc * pc) ** (HALF n) % z` by rw_tac std_ss[poly_mult_weak] >>
      `_ = (pc ** n) % z` by rw_tac std_ss[poly_exp_even] >>
      `_ = (p ** n) % z` by rw_tac std_ss[poly_exp_weak] >>
      rw[],
      `ODD n` by metis_tac[EVEN_ODD] >>
      `chop (unity_mod_exp r p n) = chop (unity_mod_mult r p q)` by rw_tac std_ss[unity_mod_exp_odd, Abbr`q`, Abbr`t`] >>
      `_ = (p * q) % z` by rw_tac std_ss[unity_mod_mult_eqn] >>
      `_ = (pc * (chop q)) % z` by rw_tac std_ss[poly_mult_weak] >>
      `_ = (pc * (pc * pc) ** (HALF n) % z) % z` by rw_tac std_ss[poly_mult_weak] >>
      `_ = ((pc % z) * (pc * pc) ** (HALF n) % z) % z` by rw_tac std_ss[poly_mod_less_weak, Abbr`pc`, Abbr`z`, Abbr`k`] >>
      `_ = (pc * (pc * pc) ** (HALF n)) % z` by rw_tac std_ss[poly_mod_mult, poly_mult_poly, poly_exp_poly] >>
      `_ = (pc ** n) % z` by rw_tac std_ss[poly_exp_odd] >>
      `_ = (p ** n) % z` by rw_tac std_ss[poly_exp_weak] >>
      rw[]
    ]
  ]);

(* This is another major milestone theorem, using the magic trick! *)

(* ------------------------------------------------------------------------- *)
(* Special Monomials under modulus unity: X ** n + |c| MOD (unity k)         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: unity_mod_special r 0 n c = |0| *)
(* Proof: by unity_mod_special_def *)
val unity_mod_special_0 = store_thm(
  "unity_mod_special_0",
  ``!r:'a ring n c. unity_mod_special r 0 n c = |0|``,
  rw[unity_mod_special_def]);

(* Theorem: Ring r /\ k <> 0 ==>
            (unity_mod_special r k n c = unity_mod_special r k n 0 || PAD_RIGHT #0 k [##c]) *)
(* Proof:
   By unity_mod_special_def, PAD_RIGHT, PAD_LEFT, this is to show:
   (1) 1 < k /\ n MOD k = 0 ==> z = z || z, where z = GENLIST (K #0) (k - 1)
       Note zerop z                     by zero_poly_every_zero, EVERY_GENLIST
        and weak z                      by weak_every_element, EVERY_GENLIST
       Thus z || z = z                  by weak_add_rzero_poly
   (2) 1 < k /\ n MOD k <> 0 ==>  t = t || z,
       where z = GENLIST (K #0) (k - 1),
             t = GENLIST (K #0) (n MOD k - 1) ++ [#1] ++ GENLIST (K #0) (k - SUC (n MOD k))
       Note zerop z                     by zero_poly_every_zero, EVERY_GENLIST
        and weak t                      by weak_every_element, EVERY_GENLIST
        Now LENGTH z = k - 1            by LENGTH_GENLIST
       Also n MOD k < k                 by MOD_LESS, k <> 0
         so LENGTH t
          = (n MOD k - 1) + 1 +         by LENGTH_APPEND
            (k - SUC (n MOD k))         by LENGTH_GENLIST
          = k - 1                       by n MOD k <> 0, SUC (m MOD k) <= k
      Thus t || t = z                   by weak_add_rzero_poly
*)
val unity_mod_special_not_0 = store_thm(
  "unity_mod_special_not_0",
  ``!r:'a ring k n c. Ring r /\ k <> 0 ==>
     (unity_mod_special r k n c = unity_mod_special r k n 0 || PAD_RIGHT #0 k [##c])``,
  rw[unity_mod_special_def, PAD_RIGHT, PAD_LEFT] >| [
    qabbrev_tac `z = GENLIST (K #0) (k - 1)` >>
    `zerop z` by rw[zero_poly_every_zero, EVERY_GENLIST, Abbr`z`] >>
    `weak z` by rw[weak_every_element, EVERY_GENLIST, Abbr`z`] >>
    rw[weak_add_rzero_poly],
    qabbrev_tac `z = GENLIST (K #0) (k - 1)` >>
    qabbrev_tac `t = GENLIST (K #0) (n MOD k - 1) ++ [#1] ++ GENLIST (K #0) (k - SUC (n MOD k))` >>
    `zerop z` by rw[zero_poly_every_zero, EVERY_GENLIST, Abbr`z`] >>
    `weak t` by rw[weak_every_element, EVERY_GENLIST, Abbr`t`] >>
    `LENGTH z = k - 1` by rw[Abbr`z`] >>
    `n MOD k < k` by rw[] >>
    `LENGTH t = (n MOD k - 1) + 1 + (k - SUC (n MOD k))` by rw[Abbr`t`] >>
    `_ = k - 1` by decide_tac >>
    rw[weak_add_rzero_poly]
  ]);

(* Theorem: Ring r ==> !k n c. weak (unity_mod_special r k n c) *)
(* Proof:
   If k = 0,
      unity_mod_special r 0 n c = |0|          by unity_mod_special_def
      and weak |0|                             by weak_zero
   If k = 1,
      unity_mod_special r 1 n c = [#1 + ##c]   by unity_mod_special_def
      Note ##c IN R                            by ring_num_element
       and #1 IN R                             by ring_one_element
       ==> (#1 + ##c) IN R                     by ring_sub_element
      Thus weak  (unity_mod_special r 1 n c)   by weak_every_element
   If k <> 0, k <> 1, then 1 < k.
      Let let q = if n MOD k = 0 then [#1 + ##c] else ##c::PAD_LEFT #0 (n MOD k) [#1]
        unity_mod_special r k n c
      = PAD_RIGHT #0 k q                       by unity_mod_special_def

      Note every MEM x (unity_mod_special r k n c) is either #0, #1, or ##c.
      i.e. !n. weak (GENLIST (K #0) n)         by weak_every_mem, MEM_GENLIST
      Thus weak (unity_mod_special r k n c)    by weak_append_weak
*)
val unity_mod_special_weak = store_thm(
  "unity_mod_special_weak",
  ``!r:'a ring. Ring r ==> !k n c. weak (unity_mod_special r k n c)``,
  rw_tac std_ss[unity_mod_special_def] >>
  (`!n. weak (GENLIST (K #0) n)` by (rw[weak_every_mem, MEM_GENLIST] >> rw[])) >>
  rw[PAD_LEFT, PAD_RIGHT, Abbr`q`] >>
  rw[weak_append_weak]);

(* Theorem: unity_mod_monomial r k c = unity_mod_special r k 1 c *)
(* Proof:
   If k = 0,
        unity_mod_monomial r 0 c      by unity_mod_monomial_def
      = |0|
      = unity_mod_special r 0 1 c     by unity_mod_special_def
   If k = 1,
        unity_mod_monomial r 1 c      by unity_mod_monomial_def
      = [#1 + ##c]
      = unity_mod_special r 1 1 c     by unity_mod_special_def
   If k <> 0 and k <> 1, then 1 < k.
     Let q = if 1 MOD k = 0 then [#1 + ##c] else ##c::PAD_LEFT #0 (n MOD k) [#1]
     Note 1 MOD k = 1 <> 0            by ONE_MOD, 1 < k
     unity_mod_special r k 1 c
   = PAD_RIGHT #0 k (##c::PAD_LEFT #0 (1 MOD k) [#1])   by unity_mod_special_def
   = PAD_RIGHT #0 k (##c::PAD_LEFT #0 1 [#1])           by ONE_MOD, 1 < k
   = PAD_RIGHT #0 k (##c::[#1])                         by PAD_LEFT_ID, LENGTH [#1] = 1
   = PAD_RIGHT #0 k [##c; #1]                           by CONS
   = unity_mod_monomial r k c                           by unity_mod_monomial_def
*)
val unity_mod_monomial_alt = store_thm(
  "unity_mod_monomial_alt",
  ``!r:'a ring. !k c. unity_mod_monomial r k c = unity_mod_special r k 1 c``,
  rw[unity_mod_monomial_def, unity_mod_special_def, PAD_LEFT, PAD_RIGHT]);

(* Theorem: Ring r ==> !k c. weak (unity_mod_monomial r k c) *)
(* Proof: by unity_mod_monomial_alt, unity_mod_special_weak *)
val unity_mod_monomial_weak = store_thm(
  "unity_mod_monomial_weak",
  ``!r:'a ring. Ring r ==> !k c. weak (unity_mod_monomial r k c)``,
  rw[unity_mod_monomial_alt, unity_mod_special_weak]);

(* Theorem: Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
            !n c. chop (unity_mod_special r k n c) = (X ** n + |c|) % (unity k) *)
(* Proof:
   If k = 1,
     chop (unity_mod_special r 1 n c)
   = chop ([#1 + ##c])                          by unity_mod_special_def
   = chop [#1] + chop [##c]                     by poly_add_const_const
   = |1| + |c|                                  by poly_ring_ids, poly_ring_sum_c

   Note unity 1 = X - |1|                       by poly_unity_1
    and X ** n + |c| = |1| * (X - |1|) + (|1| + |c|)
   Thus (X ** n + |c|) % (X - |1|) + |1| + |c|  by poly_mod_unique

   IF k <> 1,
   Let q = if n MOD k = 0 then [#1 + ##c] else ##c::PAD_LEFT #0 (n MOD k) [#1]
     chop (unity_mod_special r k n c)
   = chop (PAD_RIGHT #0 k q)                    by unity_mod_special_def, 1 < k
   = chop q                                     by poly_chop_pad_right

   If n MOD k = 0,
      Then q = [#1 + ##c]
       and chop q
         = chop [#1] + chop [##c]               by poly_add_const_const
         = |1| + |c|                            by poly_ring_ids, poly_ring_sum_c
         = X ** 0 + |c|                         by poly_exp_0
         = X ** (n MOD k) + |c|                 by n MOD k = 0

   If n MOD k <> 0,
      Then q = ##c::PAD_LEFT #0 (n MOD k) [#1]

      Note poly (PAD_LEFT #0 (n MOD k) [#1])    by rw[poly_pad_left_poly
       and [#1] <> |0|                          by poly_one, poly_one_eq_poly_zero
      Thus (PAD_LEFT #0 (n MOD k) [#1]) <> |0|  by PAD_LEFT_EQ_NIL, poly_zero
        or poly q                               by poly_nonzero_cons_poly

           chop q
         = q                                    by poly_chop_poly
         = ##c::PAD_LEFT #0 (n MOD k) [#1]      by notation
         = X ** (n MOD k) + |c|                 by poly_X_exp_n_add_c_alt
         = (X ** n + |c|) % (unity k)           by poly_unity_mod_X_exp_n_add_c
*)
val unity_mod_special_chop = store_thm(
  "unity_mod_special_chop",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
   !n c. chop (unity_mod_special r k n c) = (X ** n + |c|) % (unity k)``,
  rw_tac std_ss[poly_unity_mod_X_exp_n_add_c] >>
  rw_tac std_ss[unity_mod_special_def] >-
  metis_tac[DECIDE``~(0 < 0)``] >-
 (rw_tac std_ss[poly_exp_0] >>
  `#1 IN R /\ ##c IN R` by rw[] >>
  rw_tac std_ss[poly_add_const_const, poly_ring_ids, poly_ring_sum_c]) >-
 (rw_tac std_ss[poly_exp_0, Abbr`q`, poly_chop_pad_right] >>
  `#1 IN R /\ ##c IN R` by rw[] >>
  rw_tac std_ss[poly_add_const_const, poly_ring_ids, poly_ring_sum_c]) >>
  `poly (PAD_LEFT #0 (n MOD k) [#1])` by rw[poly_pad_left_poly] >>
  `[#1] <> |0|` by rw[] >>
  `(PAD_LEFT #0 (n MOD k) [#1]) <> |0|` by metis_tac[PAD_LEFT_EQ_NIL, poly_zero] >>
  `poly q` by rw[poly_nonzero_cons_poly, Abbr`q`] >>
  `chop (PAD_RIGHT #0 k q) = chop q` by rw[poly_chop_pad_right] >>
  `_ = q` by rw[] >>
  `_ = X ** (n MOD k) + |c|` by rw[poly_X_exp_n_add_c_alt, Abbr`q`] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
            !c. chop (unity_mod_monomial r k c) = (X + |c|) % (unity k) *)
(* Proof:
     chop (unity_mod_monomial r k c)
   = chop (unity_mod_special r k 1 c)     by unity_mod_monomial_alt
   = (X ** 1 + |c|) % (unity k)           by unity_mod_special_chop
   = (X + |c|) % (unity k)                by poly_exp_1
*)
val unity_mod_monomial_chop = store_thm(
  "unity_mod_monomial_chop",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k. 0 < k ==>
   !c. chop (unity_mod_monomial r k c) = (X + |c|) % (unity k)``,
  rw[unity_mod_monomial_alt, unity_mod_special_chop]);

(* ------------------------------------------------------------------------- *)
(* Constant polynomials under modulus unity: |c| MOD (unity k)               *)
(* ------------------------------------------------------------------------- *)

(* Define constant ##c in (unity k) *)
val unity_mod_const_def = Define`
    unity_mod_const (r:'a ring) k (c:num) =
       if k = 0 then |0| else PAD_RIGHT #0 k [##c]
`;

(*
EVAL ``unity_mod_const (ZN 10) 7 0``; = [0; 0; 0; 0; 0; 0; 0]
EVAL ``unity_mod_const (ZN 10) 7 1``; = [1; 0; 0; 0; 0; 0; 0]
*)

(* Constants zero and one in MOD (unity k) *)
val unity_mod_zero_def = Define `unity_mod_zero (r:'a ring) k = unity_mod_const r k 0`;
val unity_mod_one_def = Define `unity_mod_one (r:'a ring) k = unity_mod_const r k 1`;

(* Theorem: LENGTH (unity_mod_const r k c) = k *)
(* Proof:
   If k = 0,
        LENGTH (unity_mod_const r k c)
      = LENGTH |0|                         by unity_mod_const_def
      = 0                                  by poly_zero, LENGTH
   If k <> 0,
        LENGTH (unity_mod_const r k c)
      = LENGTH (PAD_RIGHT #0 k [##c])      by unity_mod_const_def
      = MAX k (LENGTH [##c])               by PAD_RIGHT_LENGTH
      = MAX k 1                            by LENGTH_SING
      = k                                  by MAX_DEF, k <> 0
*)
val unity_mod_const_length = store_thm(
  "unity_mod_const_length",
  ``!r:'a ring k c. LENGTH (unity_mod_const r k c) = k``,
  rw[unity_mod_const_def, PAD_RIGHT_LENGTH, MAX_DEF]);

(* Theorem: Ring r ==> !k c. weak (unity_mod_const r k c) *)
(* Proof:
   Note !n. weak (GENLIST (K #0) n)     by weak_every_mem, MEM_GENLIST
       weak (unity_mod_const r k c)
   <=> weak (if k = 0 then |0| else PAD_RIGHT #0 k [##c])             by unity_mod_const_def
   <=> weak (if k = 0 then |0| else [##c] ++ GENLIST (K #0) (k - 1))  by PAD_RIGHT
   <=> if k = 0 then weak |0| else weak ([##c] ++ GENLIST (K #0) (k - 1)))
   <=> T                                                              by weak_zero, weak_const
*)
val unity_mod_const_weak = store_thm(
  "unity_mod_const_weak",
  ``!r:'a ring. Ring r ==> !k c. weak (unity_mod_const r k c)``,
  rw[unity_mod_const_def, PAD_RIGHT] >>
  (`!n. weak (GENLIST (K #0) n)` by (rw[weak_every_mem, MEM_GENLIST] >> rw[])) >>
  rw[]);

(* Theorem: unity_mod_const r k 0 = unity_mod_zero r k *)
(* Proof: by unity_mod_zero_def *)
val unity_mod_const_0 = store_thm(
  "unity_mod_const_0",
  ``!r:'a ring k. unity_mod_const r k 0 = unity_mod_zero r k``,
  rw[unity_mod_zero_def]);

(* Theorem: unity_mod_const r k 1 = unity_mod_one r k *)
(* Proof: by unity_mod_one_def *)
val unity_mod_const_1 = store_thm(
  "unity_mod_const_1",
  ``!r:'a ring k. unity_mod_const r k 1 = unity_mod_one r k``,
  rw[unity_mod_one_def]);

(* Theorem: unity_mod_const r k c = if k = 0 then [] else ##c :: GENLIST (K #0) (k - 1) *)
(* Proof:
   If k = 0,
       unity_mod_const r 0 c
     = |0| = []                         by unity_mod_const_def, poly_zero
   If k <> 0,
       unity_mod_const r k c
     = PAD_RIGHT #0 k [##c]             by unity_mod_const_def, k <> 0
     = [##c] ++ GENLIST (K #0) (k - 1)  by PAD_RIGHT
     = ##c :: GENLIST (K #0) (k - 1)    by CONS_APPEND
*)
val unity_mod_const_eqn = store_thm(
  "unity_mod_const_eqn",
  ``!r:'a ring k. unity_mod_const r k c =
      if k = 0 then [] else ##c :: GENLIST (K #0) (k - 1)``,
  rw[unity_mod_const_def, PAD_RIGHT]);

(* Theorem: LENGTH (unity_mod_zero r k) = k *)
(* Proof:
     LENGTH (unity_mod_zero r k)
   = LENGTH (unity_mod_const r k 0)    by unity_mod_zero_def
   = k                                 by unity_mod_const_length
*)
val unity_mod_zero_length = store_thm(
  "unity_mod_zero_length",
  ``!r:'a ring k. LENGTH (unity_mod_zero r k) = k``,
  rw[unity_mod_zero_def, unity_mod_const_length]);

(* Theorem: Ring r ==> weak (unity_mod_zero r k) *)
(* Proof: by unity_mod_zero_def, unity_mod_const_weak *)
val unity_mod_zero_weak = store_thm(
  "unity_mod_zero_weak",
  ``!r:'a ring k. Ring r ==> weak (unity_mod_zero r k)``,
  rw[unity_mod_zero_def, unity_mod_const_weak]);

(* Theorem: unity_mod_zero r k = PAD_RIGHT #0 k [] *)
(* Proof:
   If k = 0,
        unity_mod_zero r 0
      = unity_mod_const r 0 0     by unity_mod_zero_def
      = |0|                       by unity_mod_const_def
      = []                        by poly_zero
      = PAD_RIGHT #0 0 []         by PAD_RIGHT_0
   If k = 0,
        unity_mod_zero r k
      = unity_mod_const r k 0     by unity_mod_zero_def
      = PAD_RIGHT #0 k [##0]      by unity_mod_const_def
      = PAD_RIGHT #0 k [#0]       by ring_num_0
      = PAD_RIGHT #0 k []         by PAD_RIGHT_NIL_EQ, 0 < k
*)
val unity_mod_zero_alt = store_thm(
  "unity_mod_zero_alt",
  ``!r:'a ring k. unity_mod_zero r k = PAD_RIGHT #0 k []``,
  rw[unity_mod_zero_def, unity_mod_const_def] >-
  rw[PAD_RIGHT_0] >>
  rw[PAD_RIGHT_NIL_EQ]);

(* Theorem: unity_mod_zero r k = GENLIST (K #0) k *)
(* Proof:
     unity_mod_zero r k
   = PAD_RIGHT #0 k []             by unity_mod_zero_alt
   = [] ++ GENLIST (K #0) (k - 0)  by PAD_RIGHT
   = GENLIST (K #0) k              by APPEND
*)
val unity_mod_zero_eqn = store_thm(
  "unity_mod_zero_eqn",
  ``!r:'a ring k. unity_mod_zero r k = GENLIST (K #0) k``,
  rw[unity_mod_zero_alt, PAD_RIGHT]);

(* Theorem: chop (unity_mod_zero r k) = |0| *)
(* Proof:
   Let z = GENLIST (K #0) k.
   Then unity_mod_zero r k = z    by unity_mod_zero_eqn
   Note EVERY (\x. x = #0) z      by EVERY_GENLIST
    ==> zerop z                   by zero_poly_every_zero
   Thus chop z = |0|              by poly_chop_zero_poly
*)
val unity_mod_zero_chop = store_thm(
  "unity_mod_zero_chop",
  ``!r:'a ring k. chop (unity_mod_zero r k) = |0|``,
  rpt strip_tac >>
  qabbrev_tac `z = GENLIST (K #0) k` >>
  `unity_mod_zero r k = z` by rw[unity_mod_zero_eqn, Abbr`z`] >>
  `EVERY (\x. x = #0) z` by rw[EVERY_GENLIST, Abbr`z`] >>
  `zerop z` by rw[zero_poly_every_zero, Abbr`z`] >>
  rw[poly_chop_zero_poly]);

(* Theorem: LENGTH (unity_mod_one r k) = k *)
(* Proof:
     LENGTH (unity_mod_one r k)
   = LENGTH (unity_mod_const r k 1)    by unity_mod_one_def
   = k                                 by unity_mod_const_length
*)
val unity_mod_one_length = store_thm(
  "unity_mod_one_length",
  ``!r:'a ring k. LENGTH (unity_mod_one r k) = k``,
  rw[unity_mod_one_def, unity_mod_const_length]);

(* Theorem: Ring r ==> weak (unity_mod_one r k) *)
(* Proof: by unity_mod_one_def, unity_mod_const_weak *)
val unity_mod_one_weak = store_thm(
  "unity_mod_one_weak",
  ``!r:'a ring k. Ring r ==> weak (unity_mod_one r k)``,
  rw[unity_mod_one_def, unity_mod_const_weak]);

(* Theorem: Ring r ==> !k. 0 < k ==> (unity_mod_one r k = #1 :: unity_mod_zero r (k - 1)) *)
(* Proof:
   If k = 1,
      LHS = unity_mod_one r 1
          = PAD_RIGHT #0 1 [##1]     by unity_mod_one_def, unity_mod_const_def, ZN_property
          = [##1]      by PAD_RIGHT
          = [#1]       by ring_num_1
      RHS = #1 :: unity_mod_zero r 0
          = #1 :: []    by unity_mod_zero_def, unity_mod_const_def
          = [#1] = LHS
   If k <> 1,
      Then SUC (k - 1) = k           by 0 < k, k <> 1.
            unity_mod_one r k
          = PAD_RIGHT #0 k [##1]     by unity_mod_one_def, unity_mod_const_def, ZN_property
          = PAD_RIGHT #0 k [#1]      by ring_num_1
          = PAD_RIGHT #0 (SUC (k - 1)) (#1::[])    by CONS
          = #1::PAD_RIGHT #0 (k - 1) []            by PAD_RIGHT_CONS
          = #1::PAD_RIGHT #0 (k - 1) [#0]          by PAD_RIGHT_NIL_EQ
          = #1::unity_mod_zero r (k - 1)  by unity_mod_zero_def, unity_mod_const_def, ZN_property
*)
val unity_mod_one_cons = store_thm(
  "unity_mod_one_cons",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==> (unity_mod_one r k = #1 :: unity_mod_zero r (k - 1))``,
  rpt strip_tac >>
  Cases_on `k = 1` >| [
    `unity_mod_one r 1 = PAD_RIGHT #0 1 [#1]` by rw[unity_mod_one_def, unity_mod_const_def, ZN_property, ring_num_1] >>
    `_ = [#1]` by rw[PAD_RIGHT] >>
    `unity_mod_zero r (k - 1) = []` by rw[unity_mod_zero_def, unity_mod_const_def] >>
    rw[],
    `SUC (k - 1) = k` by decide_tac >>
    `unity_mod_one r k = PAD_RIGHT #0 k [#1]` by rw[unity_mod_one_def, unity_mod_const_def, ZN_property, ring_num_1] >>
    `_ = #1::PAD_RIGHT #0 (k - 1) []` by rw[PAD_RIGHT_CONS] >>
    `_ = #1::PAD_RIGHT #0 (k - 1) [#0]` by rw[PAD_RIGHT_NIL_EQ] >>
    `_ = #1::unity_mod_zero r (k - 1)` by rw[unity_mod_zero_def, unity_mod_const_def, ZN_property] >>
    rw[]
  ]);

(* Theorem: unity_mod_one r k = if k = 0 then [] else ##1::GENLIST (K #0) (k - 1) *)
(* Proof:
     unity_mod_one r k
   = unity_mod_const r k 1            by unity_mod_one_def
   = PAD_RIGHT #0 k [##1]             by unity_mod_const_def
   = [##1] ++ GENLIST (K #0) (k - 1)  by PAD_RIGHT
   = ##1:: GENLIST (K #0) (k - 1)     by CONS_APPEND

     ring_num_1 |- !r. Ring r ==> (##1 = #1)
*)
val unity_mod_one_eqn = store_thm(
  "unity_mod_one_eqn",
  ``!r:'a ring k. unity_mod_one r k = if k = 0 then [] else ##1::GENLIST (K #0) (k - 1)``,
  rw[unity_mod_one_def, unity_mod_const_def, PAD_RIGHT]);

(* Theorem: Ring r /\ #1 <> #0 ==> (chop (unity_mod_one r k) = if k = 0 then |0| else |1|) *)
(* Proof:
   If k = 0,
        chop (unity_mod_one r 0)
      = chop []                   by unity_mod_one_eqn
      = |0|                       by poly_chop_zero
   If k <> 0,
        chop (unity_mod_one r 0)
      = chop (##1::GENLIST (K #0) (k - 1))   by unity_mod_one_eqn

      Let z = GENLIST (K #0) (k - ).
      Note EVERY (\x. x = #0) z      by EVERY_GENLIST
       ==> zerop z                   by zero_poly_every_zero
      Thus chop z = |0|              by poly_chop_zero_poly

        chop (unity_mod_one r 0)
      = ##1::chop z = [##1]          by above
      = [#1]                         by ring_num_1
      = |1|                          by poly_one, #1 <> #0
*)
val unity_mod_one_chop = store_thm(
  "unity_mod_one_chop",
  ``!r:'a ring k. Ring r /\ #1 <> #0 ==> (chop (unity_mod_one r k) = if k = 0 then |0| else |1|)``,
  rw[unity_mod_one_eqn] >>
  qabbrev_tac `z = GENLIST (K #0) (k - 1)` >>
  `EVERY (\x. x = #0) z` by rw[EVERY_GENLIST, Abbr`z`] >>
  `zerop z` by rw[zero_poly_every_zero, Abbr`z`] >>
  `chop z = |0|` by rw[poly_chop_zero_poly] >>
  rw[poly_one]);

(* Theorem: Ring r ==> !k c. chop (unity_mod_const r k c) =
            if (k = 0) \/ ((char r) divides c) then |0| else |c| *)
(* Proof:
   If k = 0,
        chop (unity_mod_const r 0 c)
      = chop |0|                              by unity_mod_const_def
      = |0|                                   by poly_chop_zero
   If (char r) divides c,
      Then ##c = #0                           by ring_char_divides
        chop (unity_mod_const r k c)
      = chop (#0 :: GENLIST (K #0) (k - 1))   by unity_mod_const_eqn, k <> 0
      = chop (GENLIST (K #0) (SUC (k - 1)))   by GENLIST_K_CONS
      = chop (GENLIST (K #0) k)               by SUC (k - 1) = k, k <> 0
      = chop (unity_mod_zero r k)             by unity_mod_zero_eqn
      = |0|                                   by unity_mod_zero_chop
   Otherwise, 0 < k /\ ~(char r) divides c.
      Then ##c <> #0                          by ring_char_divides
        so ~zerop (##c :: t) for any t        by zero_poly_cons
        chop (unity_mod_const r k c)
      = chop (##c :: GENLIST (K #0) (k - 1))  by unity_mod_const_eqn, k <> 0
      = ##c :: chop (GENLIST (K #0) (k - 1))  by poly_chop_cons

        Let z = GENLIST (K #0) (k - 1).
        Note EVERY (\x. x = #0) z      by EVERY_GENLIST
        ==> zerop z                    by zero_poly_every_zero
        Thus chop z = |0|              by poly_chop_zero_poly

        chop (unity_mod_const r k c)
      = ##c :: |0|                     by above
      = [##c]                          by CONS
      = chop [##c]                     by poly_chop_const_nonzero
      = |c|                            by poly_ring_sum_c
*)
val unity_mod_const_chop = store_thm(
  "unity_mod_const_chop",
  ``!r:'a ring. Ring r ==>
   !k c. chop (unity_mod_const r k c) =
     if (k = 0) \/ ((char r) divides c) then |0| else |c|``,
  rpt strip_tac >>
  (Cases_on `k = 0` >> simp[]) >-
  rw[unity_mod_const_def] >>
  (Cases_on `(char r) divides c` >> simp[]) >| [
    `##c = #0` by rw[ring_char_divides] >>
    `SUC (k - 1) = k` by decide_tac >>
    `unity_mod_const r k c = #0 :: GENLIST (K #0) (k - 1)` by rw[unity_mod_const_eqn] >>
    `_ = GENLIST (K #0) k` by rw[GSYM GENLIST_K_CONS] >>
    `_ = unity_mod_zero r k` by rw[unity_mod_zero_eqn] >>
    rw[unity_mod_zero_chop],
    `##c <> #0` by rw[ring_char_divides] >>
    `unity_mod_const r k c = ##c :: GENLIST (K #0) (k - 1)` by rw[unity_mod_const_eqn] >>
    `chop (GENLIST (K #0) (k - 1)) = |0|` by
  (qabbrev_tac `z = GENLIST (K #0) (k - 1)` >>
    `EVERY (\x. x = #0) z` by rw[EVERY_GENLIST, Abbr`z`] >>
    `zerop z` by rw[zero_poly_every_zero, Abbr`z`] >>
    rw[poly_chop_zero_poly]) >>
    rw[poly_chop_cons, poly_ring_sum_c]
  ]);

(* ------------------------------------------------------------------------- *)
(* Powers of X under modulus unity: X ** n| MOD (unity k)                    *)
(* ------------------------------------------------------------------------- *)

(* Define X ** n in (unity k) *)
val unity_mod_X_exp_def = Define `
    unity_mod_X_exp (r:'a ring) k n = unity_mod_special r k n 0
`;

(* Theorem: unity_mod_X_exp r k 0 = unity_mod_one r k *)
(* Proof:
   If k = 0,
        unity_mod_X_exp r 0 0
      = unity_mod_special r 0 0 0   by unity_mod_X_exp_def
      = |0|                         by unity_mod_special_def
      = unity_mod_const r 0 1       by unity_mod_const_def
      = unity_mod_one r 0           by unity_mod_one_def
   If k = 1,
        unity_mod_X_exp r 1 0
      = unity_mod_special r 1 0 0   by unity_mod_X_exp_def
      = [#1 + ##0]                  by unity_mod_special_def
      = [#1 + #0]                   by ring_num_0
      = [##1]                       by ring_num_one
      = PAD_RIGHT #0 1 [##1]        by PAD_RIGHT
      = unity_mod_const r 1 1       by unity_mod_const_def
      = unity_mod_one r 1           by unity_mod_one_def

   Otherwise,
       unity_mod_X_exp r k 0
     = unity_mod_special r k 0 0    by unity_mod_X_exp_def
     = PAD_RIGHT #0 k [#1 + #0]     by unity_mod_special_def, 0 MOD k = 0
     = PAD_RIGHT #0 k [##1]         by ring_num_one
     = unity_mod_const r k 1        by unity_mod_const_def
     = unity_mod_one r k            by unity_mod_one_def
*)
val unity_mod_X_exp_0 = store_thm(
  "unity_mod_X_exp_0",
  ``!r:'a ring k. unity_mod_X_exp r k 0 = unity_mod_one r k``,
  rpt strip_tac >>
  `##1 = #1 + #0` by rw[ring_num_one] >>
  rw[unity_mod_X_exp_def, unity_mod_special_def, unity_mod_one_def, unity_mod_const_def] >>
  rw[PAD_RIGHT]);

(* Theorem: unity_mod_X_exp r 0 n = |0| *)
(* Proof: by unity_mod_X_exp_def, unity_mod_special_def *)
val unity_mod_X_exp_0_n = store_thm(
  "unity_mod_X_exp_0_n",
  ``!r:'a ring n. unity_mod_X_exp r 0 n = |0|``,
  rw[unity_mod_X_exp_def, unity_mod_special_def]);

(* Theorem: unity_mod_X_exp r 1 n = [##1] *)
(* Proof: by unity_mod_X_exp_def, unity_mod_special_def, ring_num_one *)
val unity_mod_X_exp_1_n = store_thm(
  "unity_mod_X_exp_1_n",
  ``!r:'a ring n. unity_mod_X_exp r 1 n = [##1]``,
  rw[unity_mod_X_exp_def, unity_mod_special_def, ring_num_one]);

(* Theorem: LENGTH (unity_mod_X_exp r k n) = k *)
(* Proof:
     LENGTH (unity_mod_X_exp r k n)
   = LENGTH (unity_mod_special r k n 0)      by unity_mod_X_exp_def
   = k                                       by unity_mod_special_length
*)
val unity_mod_X_exp_length = store_thm(
  "unity_mod_X_exp_length",
  ``!r:'a ring k n. LENGTH (unity_mod_X_exp r k n) = k``,
  rw[unity_mod_X_exp_def, unity_mod_special_length]);

(* Theorem: Ring r ==> weak (unity_mod_X_exp r k n) *)
(* Proof:
     weak (unity_mod_X_exp r k n)
   = weak (unity_mod_special r k n 0)       by unity_mod_X_exp_def
   = T                                      by unity_mod_special_weak
*)
val unity_mod_X_exp_weak = store_thm(
  "unity_mod_X_exp_weak",
  ``!r:'a ring. Ring r ==> !k n. weak (unity_mod_X_exp r k n)``,
  rw[unity_mod_X_exp_def, unity_mod_special_weak]);

(* Theorem: Ring r ==> !k n c. unity_mod_special r k n c =
             (unity_mod_X_exp r k n) || (unity_mod_const r k c) *)
(* Proof:
   By unity_mod_X_exp_def, unity_mod_const_def, this is to show:
   (1) unity_mod_special r 0 n c = unity_mod_special r 0 n 0
       This is true                by unity_mod_special_0
   (2) k <> 0 ==> unity_mod_special r k n c = unity_mod_special r k n 0 || PAD_RIGHT #0 k [##c]
       This is true                by unity_mod_special_not_0
*)
val unity_mod_special_alt = store_thm(
  "unity_mod_special_alt",
  ``!r:'a ring k n c. Ring r ==>
   !k n c. unity_mod_special r k n c = (unity_mod_X_exp r k n) || (unity_mod_const r k c)``,
  rw[unity_mod_X_exp_def, unity_mod_const_def] >>
  (Cases_on `k = 0` >> simp[]) >-
  rw[unity_mod_special_0] >>
  rw[GSYM unity_mod_special_not_0]);

(* ------------------------------------------------------------------------- *)
(* Polynomials in (ZN n)                                                     *)
(* ------------------------------------------------------------------------- *)

(* Obtain a theorem *)
val ZN_weak = save_thm("ZN_weak",
    weak_every_element |> ISPEC ``(ZN n)`` |>
    SIMP_RULE bool_ss [ZN_property] |> GEN_ALL);
(* val ZN_weak = |- !n p. Weak (ZN n) p <=> EVERY (\c. c < n) p: thm *)

(* Theorem: 0 < n ==> Weak (ZN n) (unity_mod_special (ZN n) k m c) *)
(* Proof:
   Let p = unity_mod_special (ZN n) k m c.
   Note Ring (ZN n)               by ZN_ring, 0 < n
    ==> Weak (ZN n) p             by unity_mod_special_weak
*)
val ZN_unity_mod_special_weak = store_thm(
  "ZN_unity_mod_special_weak",
  ``!n k m c. 0 < n ==> Weak (ZN n) (unity_mod_special (ZN n) k m c)``,
  rw[ZN_ring, unity_mod_special_weak]);

(* Theorem: 0 < n ==> Weak (ZN n) (unity_mod_monomial (ZN n) k c) *)
(* Proof:
   Let p = unity_mod_monomial (ZN n) k c.
   Note Ring (ZN n)               by ZN_ring, 0 < n
    ==> Weak (ZN n) p             by unity_mod_monomial_weak
*)
val ZN_unity_mod_monomial_weak = store_thm(
  "ZN_unity_mod_monomial_weak",
  ``!n k c. 0 < n ==> Weak (ZN n) (unity_mod_monomial (ZN n) k c)``,
  rw[ZN_ring, unity_mod_monomial_weak]);

(* Theorem: 0 < n ==> Weak (ZN n) (unity_mod_const (ZN n) k c) *)
(* Proof:
   Let p = unity_mod_const (ZN n) k c.
   Note Ring (ZN n)               by ZN_ring, 0 < n
    ==> Weak (ZN n) p             by unity_mod_const_weak
*)
val ZN_unity_mod_const_weak = store_thm(
  "ZN_unity_mod_const_weak",
  ``!n k c. 0 < n ==> Weak (ZN n) (unity_mod_const (ZN n) k c)``,
  rw[ZN_ring, unity_mod_const_weak]);

(* ------------------------------------------------------------------------- *)
(* Extra Work (not used)                                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Shuffle                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define a shuffle operation for polynomials. *)
(*
val poly_shuffle_def = Define`
    poly_shuffle n (r:'a ring) (p:'a poly) =
       if p = |0| then |0| else (FRONT p) + [LAST p] >> n
`;
*)
(*
val poly_shuffle_def = Define`
    (poly_shuffle (r:'a ring) n [] = []) /\
    (poly_shuffle (r:'a ring) n ((h::t):'a poly) = (FRONT (h::t)) + [LAST (h::t)] >> n)
`;
*)
(*
val poly_shuffle_def = Define`
    poly_shuffle (r:'a ring) (p:'a poly) n =
       if p = |0| then |0| else
       let q = FRONT p in
       (TAKE n q) ++ [HD (DROP n q) + LAST p] ++ TL (DROP n q)
`;
*)
(* Make polynomial p as the last parameter *)
val poly_shuffle_def = Define`
    poly_shuffle (r:'a ring) (n:num) (p:'a poly) =
       if p = |0| then |0| else
       let q = FRONT p in let t = DROP n q in
       (TAKE n q) ++ [HD t + LAST p] ++ TL t
`;
(* Note: Ring r is required for the add operator. *)

(* Overloading on polynomial shuffle *)
val _ = overload_on("shuffle", ``poly_shuffle (r:'a ring)``);

(* Theorem: shuffle n |0| = |0| *)
(* Proof: by poly_shuffle_def *)
val poly_shuffle_zero = store_thm(
  "poly_shuffle_zero",
  ``!r:'a ring. !n. shuffle n |0| = |0|``,
  rw_tac std_ss[poly_shuffle_def]);

(* Theorem: SUC n < LENGTH p ==> (LENGTH (shuffle n p) = LENGTH p - 1) *)
(* Proof:
   Note LENGTH p <> 0     by SUC n < LENGTH p
     so p <> []           by LENGTH_NIL
     or p <> |0|          by poly_zero
   By poly_shuffle_def, this is to show:
      LENGTH (TL (DROP n (FRONT p))) + (LENGTH (TAKE n (FRONT p)) + 1) < LENGTH p

   Note LENGTH (FRONT p) = PRE (LENGTH p)       by LENGTH_FRONT, p <> []
   Also n < PRE (LENGTH p)                      by SUC n < LENGTH p
     or n <= LENGTH p                           by SUC n < LENGTH p
   Thus LENGTH (TAKE n (FRONT p)) = n           by LENGTH_TAKE, n <= LENGTH p

   Note LENGTH (DROP n (FRONT p)) = PRE (LENGTH p) - n   by LENGTH_DROP
    and 0 < PRE (LENGTH p) - n                  by SUC n < LENGTH p
   Thus LENGTH (TL (DROP n (FRONT p))) = PRE (LENGTH p) - n - 1   by LENGTH_TL, 0 < LENGTH (DROP n (FRONT p))

        LENGTH (TL (DROP n (FRONT p))) + (LENGTH (TAKE n (FRONT p)) + 1)
      = (PRE (LENGTH p) - n - 1) + (n + 1)
      = PRE (LENGTH p)                          by n < PRE (LENGTH p)
      = LENGTH - 1                              by PRE_SUB1
*)
val poly_shuffle_length = store_thm(
  "poly_shuffle_length",
  ``!r:'a ring. !p n. SUC n < LENGTH p ==> (LENGTH (shuffle n p) = LENGTH p - 1)``,
  rpt strip_tac >>
  `LENGTH p <> 0` by decide_tac >>
  `p <> []` by metis_tac[LENGTH_NIL] >>
  rw[poly_shuffle_def] >>
  `LENGTH (FRONT p) = PRE (LENGTH p)` by rw[LENGTH_FRONT] >>
  `n < PRE (LENGTH p)` by decide_tac >>
  `n <= LENGTH p` by decide_tac >>
  `LENGTH (TAKE n (FRONT p)) = n` by rw[LENGTH_TAKE] >>
  `LENGTH (DROP n (FRONT p)) = PRE (LENGTH p) - n` by rw[LENGTH_DROP] >>
  `0 < PRE (LENGTH p) - n` by decide_tac >>
  `LENGTH (TL (DROP n (FRONT p))) = PRE (LENGTH p) - n - 1` by rw[LENGTH_TL] >>
  decide_tac);

(* Theorem: shuffle 0 p = if p = |0| then |0| else [HD (FRONT p) + LAST p] ++ TL (FRONT p) *)
(* Proof:
   If p <> |0|
      shuffle 0 p
    = let q = FRONT p in let t = DROP 0 q in
      TAKE 0 q ++ [HD t + LAST p] ++ TL t         by poly_shuffle_def
    = let q = FRONT p in let t = q in
      [] ++ [HD t + LAST p] ++ TL t               by TAKE_0, DROP_0
    = let q = FRONT p in [HD q + LAST p] ++ TL q  by APPEND
    = [HD (FRONT p) + LAST p] ++ TL (FRONT p)     by simplication
    = (HD (FRONT p) + LAST p) :: TL (FRONT p)     by CONS_APPEND
*)
val poly_shuffle_0 = store_thm(
  "poly_shuffle_0",
  ``!r:'a ring. !p. shuffle 0 p = if p = |0| then |0| else (HD (FRONT p) + LAST p) :: TL (FRONT p)``,
  rw[poly_shuffle_def]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Remainder of unity k = X ** k - 1                              *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``poly_add (ZN 5) [0; 1; 4; 0; 1] [2; 0; 4; 1; 1]``; --> [2; 1; 3; 1; 2]
> EVAL ``poly_add (ZN 5) [0; 1; 4] [2; 0; 4; 1; 1]``; --> [2; 1; 3; 1; 1]
> EVAL ``poly_add (ZN 5) [1; 1] [1; 1]``; --> [2; 2]
> EVAL ``poly_mult (ZN 5) [1; 1] [1; 1]``; --> [1; 2; 1]
> EVAL ``poly_mod (ZN 5) [1;2;3;2;1] [1;0;0;1]``; --> just notation
*)

(* Example:
   [3; 2; 1; 2; 3] 3 =  [3; 2; 1; 2; 3] MOD (X ** 3 - |1|)
   x0 x1 x2 x3
-> [3; 2; 1; 2] = poly_shuffle (ZN 5) [3; 2; 1; 2; 3] 1   1 = (LENGTH - 3 - 1), add to x1
       3
 = [3; 0; 1; 2] = poly_shuffle (ZN 5) [3; 0; 1; 2] 0      0 = (LENGTH - 3 - 1), add to x0
-> [3; 0; 1]
    2
 = [0; 0; 1]
*)

(* Define polynomimal remainder by unity k = X ** k - |1|, returns a weak list of length k *)
Definition unity_mod_def:
  unity_mod (r:'a ring) (k:num) (p:'a poly) =
      if 0 < k then
         if k < LENGTH p then unity_mod r k (shuffle (LENGTH p - k - 1) p) else (PAD_RIGHT #0 k p)
      else p % |0| (* whatever that is! *)
Termination WF_REL_TAC `measure (λ(r, k, p). LENGTH p)` >>
            rpt strip_tac >>
            rw[poly_shuffle_length]
End
(*
val unity_mod_def =
   |- !r p k. unity_mod r k p =
     if 0 < k then
       if k < LENGTH p then unity_mod r k (shuffle (LENGTH p - k - 1) p) else p
     else p % |0|:
   thm
*)

(*
> EVAL ``unity_mod (ZN 5) 3 [1;2]``; --> [1; 2; 0]
> EVAL ``unity_mod (ZN 5) 3 [1;2;1]``; --> [1; 2; 1]
> EVAL ``unity_mod (ZN 5) 3 [1;2;1;1]``; --> [2; 2; 1]
> EVAL ``unity_mod (ZN 5) 3 [3;2;1;2]``; --> [0; 2; 1]
> EVAL ``unity_mod (ZN 5) 3 [3;2;1;2;3]``; --> [0; 0; 1]
> EVAL ``unity_mod (ZN 5) 3 [1;2;3;2;1]``; --> [3; 3; 3]
*)

(* Theorem: 0 < k ==> (unity_mod r k |0| = GENLIST (K #0) k) *)
(* Proof:
     unity_mod r k |0|
   = unity_mod r k []          by poly_zero
   = PAD_RIGHT #0 k []         by unity_mod_def
   = GENLIST (K #0) k          by PAD_RIGHT_NIL
*)
val old_unity_mod_zero_eqn = store_thm(
  "old_unity_mod_zero_eqn",
  ``!r:'a ring. !k. 0 < k ==> (unity_mod r k |0| = GENLIST (K #0) k)``,
  rw[Once unity_mod_def, PAD_RIGHT_NIL]);

(* Theorem: 0 < k ==> (chop (unity_mod r k |0|) = |0|) *)
(* Proof:
   Note unity_mod r k |0|
      = GENLIST (K #0) k       by old_unity_mod_zero_eqn
   Let z = GENLIST (K #0) k.
   Note EVERY (\x. x = #0) z   by EVERY_GENLIST
    ==> zerop z                by zero_poly_every_zero
   Thus chop z = |0|           by poly_chop_zero_poly
*)
val old_unity_mod_zero_chop = store_thm(
  "old_unity_mod_zero_chop",
  ``!r:'a ring. !k. 0 < k ==> (chop (unity_mod r k |0|) = |0|)``,
  rpt strip_tac >>
  `unity_mod r k |0| = GENLIST (K #0) k` by rw[old_unity_mod_zero_eqn] >>
  qabbrev_tac `z = GENLIST (K #0) k` >>
  `EVERY (\x. x = #0) z` by rw[EVERY_GENLIST, Abbr`z`] >>
  `zerop z` by rw[zero_poly_every_zero, Abbr`z`] >>
  rw[poly_chop_zero_poly]);

(* Theorem: 0 < k ==> (LENGTH (unity_mod r k |0|) = k) *)
(* Proof:
     LENGTH (unity_mod r k |0|)
   = LENGTH (GENLIST (K #0) k)     by old_unity_mod_zero_eqn
   = k                             by LENGTH_GENLIST
*)
val old_unity_mod_zero_length = store_thm(
  "old_unity_mod_zero_length",
  ``!r:'a ring. !k. 0 < k ==> (LENGTH (unity_mod r k |0|) = k)``,
  rw_tac std_ss[old_unity_mod_zero_eqn, LENGTH_GENLIST]);

(* Theorem: 0 < k ==> !p. LENGTH (unity_mod r k p) = k *)
(* Proof:
   By complete induction on (LENGTH p).
   By unity_mod_def, this is to show:
   (1) k < LENGTH p ==> LENGTH (unity_mod r k (shuffle (LENGTH p - (k + 1)) p)) = k
       Note LENGTH p - k < LENGTH p        by k < LENGTH p
         so SUC (LENGTH p - (k + 1)) < LENGTH p
        Let q = shuffle (LENGTH p - (k + 1)) p
       Then LENGTH q < LENGTH p            by poly_shuffle_length
       Thus LENGTH (unity_mod r k q) = k   by induction hypothesis
   (2) ~(k < LENGTH p) ==> LENGTH (PAD_RIGHT #0 k p) = k
      Note LENGTH p <= k                   by ~(k < LENGTH p)
        so MAX k (LENGTH p) = k            by MAX_DEF
      Thus LENGTH (PAD_RIGHT #0 k p) = k   by PAD_RIGHT_LENGTH
*)
val old_unity_mod_length = store_thm(
  "old_unity_mod_length",
  ``!r:'a ring. !k. 0 < k ==> !p. LENGTH (unity_mod r k p) = k``,
  rpt strip_tac >>
  completeInduct_on `LENGTH p` >>
  rpt strip_tac >>
  rw[Once unity_mod_def] >-
  rw[poly_shuffle_length] >>
  rw[PAD_RIGHT_LENGTH, MAX_DEF]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
