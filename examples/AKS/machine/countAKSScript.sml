(* ------------------------------------------------------------------------- *)
(* AKS computations in monadic style.                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countAKS";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     rich_listTheory listRangeTheory numberTheory combinatoricsTheory
     logrootTheory pairTheory optionTheory primeTheory;

(* Get dependent theories local *)
(* val _ = load "countParamTheory"; *)
open countMonadTheory countMacroTheory;
open countModuloTheory countOrderTheory;
open countParamTheory;

(* val _ = load "countPowerTheory"; *)
open countPowerTheory;

(* val _ = load "countPolyTheory"; *)
open countPolyTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory loopListTheory;

open monadsyntax;

(* val _ = load "ringInstancesTheory"; *)
open ringInstancesTheory; (* for ZN order *)

open computeParamTheory computeAKSTheory;
open computeBasicTheory; (* for power_free_check_eqn *)

(* (* val _ = load "computePolyTheory"; *) *)
open computePolyTheory; (* for unity_mod_monomial *)
(* Try: import computeRing rather than computePoly *)

open polynomialTheory polyWeakTheory;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* AKS computations in monadic style Documentation                           *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Special Polynomials:
   poly_X_exp_addM_def   |- !n k m c. poly_X_exp_addM n k m c =
                                      do
                                        p0 <- poly_X_expM n k m;
                                        p1 <- poly_constM n k c;
                                        poly_addM n p0 p1
                                      od
   poly_X_addM_def       |- !n k c. poly_X_addM n k c = poly_X_exp_addM n k 1 c
#  poly_X_exp_addM_value |- !n k m c. 0 < n ==>
                                      valueOf (poly_X_exp_addM n k m c) = unity_mod_special (ZN n) k m c
#  poly_X_addM_value     |- !n k c. 0 < n ==>
                                    valueOf (poly_X_addM n k c) = unity_mod_monomial (ZN n) k c
   poly_X_exp_addM_weak  |- !n k m c. 0 < n ==> Weak (ZN n) (valueOf (poly_X_exp_addM n k m c))
   poly_X_exp_addM_length|- !n k m c. 0 < n ==> LENGTH (valueOf (poly_X_exp_addM n k m c)) = k
   poly_X_addM_weak      |- !n k c. 0 < n ==> Weak (ZN n) (valueOf (poly_X_addM n k c))
   poly_X_addM_length    |- !n k c. 0 < n ==> LENGTH (valueOf (poly_X_addM n k c)) = k

   poly_X_exp_addM_steps_thm
                         |- !n k m c. 0 < n ==>
                                      stepsOf (poly_X_exp_addM n k m c) =
                                        stepsOf (poly_X_expM n k m) + stepsOf (poly_constM n k c) +
                                        stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k m)
                                                             (unity_mod_const (ZN n) k c))
   poly_X_exp_addM_steps_upper
                         |- !n k m c. 0 < n ==>
                                      stepsOf (poly_X_exp_addM n k m c) <=
                                      15 * MAX 1 k * size k * size n * size m +
                                      7 * MAX 1 k * size k * size c * size n + 12 * MAX 1 k * size n ** 2
   poly_X_exp_addM_steps_bound
                         |- !n k m c. 0 < n ==>
                                      stepsOf (poly_X_exp_addM n k m c) <=
                                      34 * MAX 1 k * size k * size m * size c * size n ** 2
   poly_X_addM_steps_thm |- !n k c. 0 < n ==>
                                    stepsOf (poly_X_addM n k c) =
                                      stepsOf (poly_X_expM n k 1) + stepsOf (poly_constM n k c) +
                                      stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k 1)
                                                           (unity_mod_const (ZN n) k c))
   poly_X_addM_steps_upper
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_X_addM n k c) <=
                                    15 * MAX 1 k * size k * size n +
                                    7 * MAX 1 k * size k * size c * size n + 12 * MAX 1 k * size n ** 2
   poly_X_addM_steps_bound
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_X_addM n k c) <=
                                    34 * MAX 1 k * size k * size c * size n ** 2

   Introspective Checks:
   poly_introM_def       |- !n k c. poly_introM n k c =
                                    do
                                      p <- poly_X_addM k c;
                                      q <- poly_expM n k p n;
                                      r <- poly_X_exp_addM n k c;
                                      poly_eqM q r k
                                    od
   poly_introM_alt        |- !n k c. poly_introM n k c =
                                     do
                                       p <- poly_X_exp_addM n k 1 c;
                                       q <- poly_expM n p n;
                                       r <- poly_X_exp_addM n k n c;
                                       poly_eqM q r
                                     od
   poly_intro_rangeM_def  |- !n k c. poly_intro_rangeM n k c =
                                   do
                                     c0 <- zeroM c;
                                     if c0 then unit T
                                     else
                                       do
                                         b1 <- poly_introM n k c;
                                         if b1 then do j <- decM c; poly_intro_rangeM n k j od
                                         else unit F
                                       od
                                   od
#  poly_introM_value     |- !n k c. 0 < n ==>
                                    (valueOf (poly_introM n k c) <=> unity_mod_intro (ZN n) k n c)
#  poly_intro_rangeM_value
                         |- !n k c. 0 < n ==>
                                    (valueOf (poly_intro_rangeM n k c) <=> unity_mod_intro_range (ZN n) k n c)
   poly_introM_steps_thm |- !n k c. (let p = valueOf (poly_X_addM n k c) ;
                                         q = valueOf (poly_expM n p n) ;
                                         r = valueOf (poly_X_exp_addM n k n c)
                                      in stepsOf (poly_introM n k c) =
                                         stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
                                         stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r))
   poly_introM_steps_upper
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_introM n k c) <=
                                    9 * MAX 1 k * size n +
                                    34 * MAX 1 k * size k * size c * size n ** 2 +
                                    34 * MAX 1 k * size k * size c * size n ** 3 +
                                    83 * MAX 1 k ** 2 * size n ** 4
   poly_introM_steps_bound
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_introM n k c) <=
                                    160 * MAX 1 k ** 2 * size k * size c * size n ** 4
   poly_introM_steps_bound_alt
                         |- !n k c. 1 < n /\ 1 < k ==>
                                    stepsOf (poly_introM n k c) <=
                                    160 * k ** 2 * size k * size c * size n ** 4
   poly_intro_rangeM_steps_thm
                         |- !n k c. stepsOf (poly_intro_rangeM n k c) =
                                    size c +
                                    if c = 0 then 0
                                    else stepsOf (poly_introM n k c) +
                                         if ~valueOf (poly_introM n k c) then 0
                                         else size c + stepsOf (poly_intro_rangeM n k (c - 1))
   poly_intro_rangeM_steps_by_dec_loop
                         |- !n k c. stepsOf (poly_intro_rangeM n k c) =
                                    if c = 0 then 1
                                    else size c + stepsOf (poly_introM n k c) +
                                         (if ~valueOf (poly_introM n k c) then 0 else size c) +
                                         if ~valueOf (poly_introM n k c) then 0
                                         else stepsOf (poly_intro_rangeM n k (c - 1))
   poly_intro_rangeM_steps_upper
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_intro_rangeM n k c) <=
                                    1 + TWICE c * size c +
                                    160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4
   poly_intro_rangeM_steps_bound
                         |- !n k c. 0 < n ==>
                                    stepsOf (poly_intro_rangeM n k c) <=
                                    163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4
   poly_intro_rangeM_steps_bound_alt
                         |- !n k c. 1 < n /\ 1 < k ==>
                                    stepsOf (poly_intro_rangeM n k c) <=
                                    163 * MAX 1 c * k ** 2 * size k * size c * size n ** 4
   poly_intro_rangeM_steps_bound_thm
                         |- !n k c. c <= k /\ k < n ==>
                                    stepsOf (poly_intro_rangeM n k c) <= 163 * MAX 1 k ** 3 * size n ** 6

   AKS Algorithm with simple bound:
   aksM_def          |- !n. aksM n =
                            do
                              b0 <- power_freeM n;
                              if b0 then
                                do
                                  c0 <- paramM n;
                                  case c0 of
                                    nice j => eqM j n
                                  | good k => poly_intro_rangeM n k k
                                  | bad => unit F
                                od
                              else unit F
                            od
#  aksM_value        |- !n. valueOf (aksM n) <=> aks0 n
   aksM_steps_thm    |- !n. stepsOf (aksM n) =
                            stepsOf (power_freeM n) +
                            if power_free n then
                              stepsOf (paramM n) +
                              case param n of
                                nice j => size (MAX j n)
                              | good k => stepsOf (poly_intro_rangeM n k k)
                              | bad => 0
                            else 0
   aksM_steps_base   |- stepsOf (aksM 0) = 2 /\ stepsOf (aksM 1) = 12
   aksM_steps_upper  |- !n. stepsOf (aksM n) <=
                                207 * size n ** 9 + 1348980357 * size n ** 20 +
                                4075 * size n ** 21
   aksM_steps_bound  |- !n. stepsOf (aksM n) <= 1348984639 * size n ** 21
   aksM_steps_O_poly |- stepsOf o aksM IN O_poly 21
   aksM_steps_big_O  |- stepsOf o aksM IN big_O (\n. ulog n ** 21)
   aksM_thm          |- !n. (valueOf (aksM n) <=> aks0 n) /\
                            stepsOf o aksM IN big_O (\n. ulog n ** 21)

*)
(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* for EVAL IFm *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* EVAL IFm must be in current script, e.g. EVAL ``expn 1 2 3``; *)

(* ------------------------------------------------------------------------- *)
(* Special Polynomials                                                       *)
(* ------------------------------------------------------------------------- *)

(*
> AKS_compute_def;
val it =
   |- !n.
          AKS_compute n <=>
          1 < n /\ power_free_check n /\
          case aks_param n of
            nice j => j = n
          | good k =>
            unity_mod_intro_range (ZN n) k n
              (sqrt_compute (phi_compute k) * ulog n)
          | bad => F
> unity_mod_intro_range_def;
val it =
   |- (!r k n. unity_mod_intro_range r k n 0 <=> T) /\
      !r k n m.
          unity_mod_intro_range r k n (SUC m) <=>
          unity_mod_intro r k n (SUC m) /\ unity_mod_intro_range r k n m: thm
val it =
   |- !r k n c.
          unity_mod_intro r k n c <=>
          unity_mod_exp r (unity_mod_monomial r k c) n =
          unity_mod_special r k n c: thm
> unity_mod_monomial_def;
val it =
   |- !r k c.
          unity_mod_monomial r k c =
          if k = 0 then |0|
          else if k = 1 then [#1 + ##c]
          else PAD_RIGHT #0 k [##c; #1]: thm
> unity_mod_special_def;
val it =
   |- !r k n c.
          unity_mod_special r k n c =
          if k = 0 then |0|
          else if k = 1 then [#1 + ##c]
          else
            (let
               q =
                 if n MOD k = 0 then [#1 + ##c]
                 else ##c::PAD_LEFT #0 (n MOD k) [#1]
             in
               PAD_RIGHT #0 k q): thm
> unity_mod_monomial_alt
|- !r k c. unity_mod_monomial r k c = unity_mod_special r k 1 c
*)

(* ------------------------------------------------------------------------- *)
(* (X ** m + c) (MOD n, (unity k))                                           *)
(* ------------------------------------------------------------------------- *)

(* Make (X ** m + c) (MOD n, (unity k)) of length k. *)
(* This is X ** (m MOD k) + c *)
(* e.g. X ** 7 + |1| (MOD 7, (unity 4)) = X ** (7 MOD 4) + 1 = X ** 3 + 1 = [1; 0; 0; 1] *)
val poly_X_exp_addM_def = Define`
    poly_X_exp_addM n k m c =
      do
        p0 <- poly_X_expM n k m;
        p1 <- poly_constM n k c;
        poly_addM n p0 p1;
      od
`;

(* (X ** m + 13)  (mod 10, (unity 7)), m = 1 ... 10
> EVAL ``poly_X_exp_addM 10 7 1 13``; = ([3; 1; 0; 0; 0; 0; 0],Count 201): thm
> EVAL ``poly_X_exp_addM 10 7 2 13``; = ([3; 0; 1; 0; 0; 0; 0],Count 202): thm
> EVAL ``poly_X_exp_addM 10 7 3 13``; = ([3; 0; 0; 1; 0; 0; 0],Count 200): thm
> EVAL ``poly_X_exp_addM 10 7 4 13``; = ([3; 0; 0; 0; 1; 0; 0],Count 204): thm
> EVAL ``poly_X_exp_addM 10 7 5 13``; = ([3; 0; 0; 0; 0; 1; 0],Count 206): thm
> EVAL ``poly_X_exp_addM 10 7 6 13``; = ([3; 0; 0; 0; 0; 0; 1],Count 209): thm
> EVAL ``poly_X_exp_addM 10 7 7 13``; = ([4; 0; 0; 0; 0; 0; 0],Count 215): thm
> EVAL ``poly_X_exp_addM 10 7 10 13``; = ([3; 0; 0; 1; 0; 0; 0],Count 206): thm
> EVAL ``poly_X_exp_addM 10 0 2 13``; = ([],Count 4): thm
> EVAL ``poly_X_exp_addM 10 1 2 13``; = ([4],Count 50): thm

> EVAL ``unity_mod_special (ZN 10) 7 1 13``; = [3; 1; 0; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 2 13``; = [3; 0; 1; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 3 13``; = [3; 0; 0; 1; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 4 13``; = [3; 0; 0; 0; 1; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 5 13``; = [3; 0; 0; 0; 0; 1; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 6 13``; = [3; 0; 0; 0; 0; 0; 1]: thm
> EVAL ``unity_mod_special (ZN 10) 7 7 13``; = [4; 0; 0; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 10 13``; = [3; 0; 0; 1; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 0 2 13``; = []: thm
> EVAL ``unity_mod_special (ZN 10) 1 2 13``; = [4]: thm
*)

(* ------------------------------------------------------------------------- *)
(* (X + c) (MOD n, (unity k))                                                *)
(* ------------------------------------------------------------------------- *)

(* Make (X + c) (MOD n, (unity k)) of length k. *)
(* This is X ** 1 + c *)
(*
> unity_mod_monomial_alt
|- !r k c. unity_mod_monomial r k c = unity_mod_special r k 1 c
*)
val poly_X_addM_def = Define`
    poly_X_addM n k c = poly_X_exp_addM n k 1 c
`;

(*  (x + 13)  (mod 10, (unity 7))
> EVAL ``poly_X_addM 10 7 13``; = ([3; 1; 0; 0; 0; 0; 0],Count 201): thm
> EVAL ``poly_X_addM 10 0 13``; = ([],Count 4): thm
> EVAL ``poly_X_addM 10 1 13``; = ([4],Count 50): thm
> EVAL ``unity_mod_monomial (ZN 10) 7 13``; = [3; 1; 0; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_monomial (ZN 10) 0 13``; = []: thm
> EVAL ``unity_mod_monomial (ZN 10) 1 13``; = [4]: thm
*)

(* Theorem: 0 < n ==> (valueOf (poly_X_exp_addM n k m c) = unity_mod_special (ZN n) k m c) *)
(* Proof:
   Note Ring (ZN n)                                     by ZN_ring, 0 < n
     valueOf (poly_X_exp_addM n k m c)
   = valueOf (poly_addM (valueOf (poly_X_expM n k m))
                        (valueOf (poly_constM n k c))   by poly_X_exp_addM_def
   = valueOf (poly_addM (unity_mod_X_exp (ZN n) k m)    by poly_X_expM_value
                        (unity_mod_const (ZN n) k c))   by poly_constM_value
   = weak_add (ZN n) (unity_mod_X_exp (ZN n) k m)
                     (unity_mod_const (ZN n) k c)       by poly_addM_value
   = unity_mod_special (ZN n) k m c)                    by unity_mod_special_alt
*)
val poly_X_exp_addM_value = store_thm(
  "poly_X_exp_addM_value[simp]",
  ``!n k m c. 0 < n ==> (valueOf (poly_X_exp_addM n k m c) = unity_mod_special (ZN n) k m c)``,
  rw[poly_X_exp_addM_def, unity_mod_special_alt, ZN_ring]);

(* Theorem: 0 < n ==> (valueOf (poly_X_addM n k c) = unity_mod_monomial (ZN n) k c) *)
(* Proof:
     valueOf (poly_X_addM n k c)
   = valueOf (poly_X_exp_addM n k 1)   by poly_X_addM_def
   = unity_mod_special (ZN n) k 1 c    by poly_X_exp_addM_value, 0 < n
   = unity_mod_monomial (ZN n) k c     by unity_mod_monomial_alt
*)
val poly_X_addM_value = store_thm(
  "poly_X_addM_value[simp]",
  ``!n k c. 0 < n ==> (valueOf (poly_X_addM n k c) = unity_mod_monomial (ZN n) k c)``,
  rw[poly_X_addM_def, unity_mod_monomial_alt]);

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_X_exp_addM n k m c)) *)
(* Proof:
   Note Ring (ZN n)                                     by ZN_ring, 0 < n
       Weak (ZN n) (valueOf (poly_X_exp_addM n k m c))
   <=> Weak (ZN n) (unity_mod_special (ZN n) k m c)     by poly_X_exp_addM_value
   <=> T                                                by unity_mod_special_weak, Ring (ZN n)
*)
val poly_X_exp_addM_weak = store_thm(
  "poly_X_exp_addM_weak",
  ``!n k m c. 0 < n ==> Weak (ZN n) (valueOf (poly_X_exp_addM n k m c))``,
  rw[unity_mod_special_weak, ZN_ring]);

(* Theorem: 0 < n ==> LENGTH (valueOf (poly_X_exp_addM n k m c)) = k *)
(* Proof:
     LENGTH (valueOf (poly_X_exp_addM n k m c))
   = LENGTH (unity_mod_special (ZN n) k m c)         by poly_X_exp_addM_value
   = k                                               by unity_mod_special_length
*)
val poly_X_exp_addM_length = store_thm(
  "poly_X_exp_addM_length",
  ``!n k m c. 0 < n ==> LENGTH (valueOf (poly_X_exp_addM n k m c)) = k``,
  rw[unity_mod_special_length]);

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_X_addM n k c)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_X_addM n k c))
   = Weak (ZN n) (valueOf (poly_X_exp_addM n k 1 c))    by poly_X_addM_def
   = T                                                  by poly_X_exp_addM_weak
*)
val poly_X_addM_weak = store_thm(
  "poly_X_addM_weak",
  ``!n k c. 0 < n ==> Weak (ZN n) (valueOf (poly_X_addM n k c))``,
  metis_tac[poly_X_addM_def, poly_X_exp_addM_weak]);

(* Theorem: 0 < n ==> LENGTH (valueOf (poly_X_addM n k c)) = k *)
(* Proof:
     LENGTH (valueOf (poly_X_addM n k c))
   = LENGTH (valueOf (poly_X_exp_addM n k 1 c))      by poly_X_addM_def
   = k                                               by poly_X_exp_addM_length
*)
val poly_X_addM_length = store_thm(
  "poly_X_addM_length",
  ``!n k c. 0 < n ==> LENGTH (valueOf (poly_X_addM n k c)) = k``,
  metis_tac[poly_X_addM_def, poly_X_exp_addM_length]);

(* Theorem: 0 < n ==>
            stepsOf (poly_X_exp_addM n k m c) =
              stepsOf (poly_X_expM n k m) +
              stepsOf (poly_constM n k c) +
              stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k m) (unity_mod_const (ZN n) k c)) *)
(* Proof:
     stepsOf (poly_X_exp_addM k n m c)
   = stepsOf (poly_X_expM n k m) +
     stepsOf (poly_constM n k c) +
     stepsOf (poly_addM n (valueOf (poly_X_expM n k m)) (valueOf (poly_constM n k c)))
                                       by poly_X_exp_addM_def
   = stepsOf (poly_X_expM n k m) +
     stepsOf (poly_constM n k c) +
     stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k m) (unity_mod_const (ZN n) k c))
                                       by poly_X_expM_value, poly_constM_value
*)
val poly_X_exp_addM_steps_thm = store_thm(
  "poly_X_exp_addM_steps_thm",
  ``!n k m c. 0 < n ==>
             stepsOf (poly_X_exp_addM n k m c) =
             stepsOf (poly_X_expM n k m) +
             stepsOf (poly_constM n k c) +
             stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k m) (unity_mod_const (ZN n) k c))``,
  rw[poly_X_exp_addM_def]);

(* Theorem: 0 < n ==>
             stepsOf (poly_X_exp_addM n k m c) <=
             15 * MAX 1 k * size k * size n * size m +
              7 * MAX 1 k * size k * size c * size n +
             12 * MAX 1 k * size n ** 2 *)
(* Proof:
   Let p = unity_mod_X_exp (ZN n) k m,
       q = unity_mod_const (ZN n) k c.
   Note LENGTH p = k                          by unity_mod_X_exp_length
    and LENGTH q = k                          by unity_mod_const_length
    Now Ring (ZN n)                           by ZN_ring, 0 < n
     so Weak (ZN n) p                         by unity_mod_X_exp_weak
    and Weak (ZN n) q                         by unity_mod_const_weak
      stepsOf (poly_X_exp_addM n k m c)
    = stepsOf (poly_X_expM n k m) +
      stepsOf (poly_constM n k c) +
      stepsOf (poly_addM n p q)                   by poly_X_exp_addM_steps_thm
   <= 15 * MAX 1 k * size k * size n * size m +   by poly_X_expM_steps_bound
      7 * MAX 1 k * size k * size c * size n +    by poly_constM_steps_bound
      12 * MAX 1 k * size n ** 2                  by poly_addM_steps_bound
*)
val poly_X_exp_addM_steps_upper = store_thm(
  "poly_X_exp_addM_steps_upper",
  ``!n k m c. 0 < n ==>
             stepsOf (poly_X_exp_addM n k m c) <=
             15 * MAX 1 k * size k * size n * size m +
              7 * MAX 1 k * size k * size c * size n +
             12 * MAX 1 k * size n ** 2``,
  rpt strip_tac >>
  imp_res_tac poly_X_exp_addM_steps_thm >>
  first_x_assum (qspecl_then [`m`, `k`, `c`] strip_assume_tac) >>
  `stepsOf (poly_X_expM n k m) <= 15 * MAX 1 k * size k * size n * size m` by rw[poly_X_expM_steps_bound] >>
  `stepsOf (poly_constM n k c) <= 7 * MAX 1 k * size k * size c * size n` by rw[poly_constM_steps_bound] >>
  qabbrev_tac `p = unity_mod_X_exp (ZN n) k m` >>
  qabbrev_tac `q = unity_mod_const (ZN n) k c` >>
  `LENGTH p = k` by rw[unity_mod_X_exp_length, Abbr`p`] >>
  `LENGTH q = k` by rw[unity_mod_const_length, Abbr`q`] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `Weak (ZN n) p ` by rw[unity_mod_X_exp_weak, Abbr`p`] >>
  `Weak (ZN n) q ` by rw[unity_mod_const_weak, Abbr`q`] >>
  `stepsOf (poly_addM n p q) <= 12 * MAX 1 k * size n ** 2` by rw[poly_addM_steps_bound] >>
  decide_tac);

(* Theorem: 0 < n ==>
             stepsOf (poly_X_exp_addM n k m c) <=
             34 * MAX 1 k * size k * size m * size c * size n ** 2 *)
(* Proof:
     stepsOf (poly_X_exp_addM n k m c)
  <= 15 * MAX 1 k * size k * size n * size m +
      7 * MAX 1 k * size k * size c * size n +
     12 * MAX 1 k * size n ** 2                       by poly_X_exp_addM_steps_upper
  <= (15 + 7 + 12) * MAX 1 k * size k * size m * size c * size n ** 2   by dominant term
   = 34 * MAX 1 k * size k * size m * size c * size n ** 2
*)
val poly_X_exp_addM_steps_bound = store_thm(
  "poly_X_exp_addM_steps_bound",
  ``!n k m c. 0 < n ==>
             stepsOf (poly_X_exp_addM n k m c) <=
             34 * MAX 1 k * size k * size m * size c * size n ** 2``,
  rpt strip_tac >>
  imp_res_tac poly_X_exp_addM_steps_upper >>
  first_x_assum (qspecl_then [`m`, `k`, `c`] strip_assume_tac) >>
  qabbrev_tac `h = MAX 1 k` >>
  qabbrev_tac `t = h * size k * size m * size c * size n ** 2` >>
  `stepsOf (poly_X_exp_addM n k m c) <= 34 * t` suffices_by rw[Abbr`t`] >>
  `0 < h` by rw[Abbr`h`] >>
  `h * size k * size n * size m <= t` by
  (`h * size k * size n * size m <= h * size k * size n * size m * (size c * size n)` by rw[MULT_POS] >>
  `h * size k * size n * size m * (size c * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `h * size k * size c * size n <= t` by
    (`h * size k * size c * size n <= h * size k * size c * size n * (size m * size n)` by rw[MULT_POS] >>
  `h * size k * size c * size n * (size m * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `h * size n ** 2 <= t` by
      (`h * size n ** 2 <= h * size n ** 2 * (size k * size m * size c)` by rw[MULT_POS] >>
  `h * size n ** 2 * (size k * size m * size c) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: 0 < n ==>
           stepsOf (poly_X_addM n k c) =
           stepsOf (poly_X_expM n k 1) + stepsOf (poly_constM n k c) +
           stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k 1)
                                (unity_mod_const (ZN n) k c)) *)
(* Proof:
    stepsOf (poly_X_addM n k c)
  = stepsOf (poly_X_exp_addM n k 1 c)                     by poly_X_addM_def
  = stepsOf (poly_X_expM n k 1) + stepsOf (poly_constM n k c) +
    stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k 1)
                         (unity_mod_const (ZN n) k c))    by poly_X_exp_addM_steps_thm
*)
val poly_X_addM_steps_thm = store_thm(
  "poly_X_addM_steps_thm",
  ``!n k c. 0 < n ==>
           stepsOf (poly_X_addM n k c) =
           stepsOf (poly_X_expM n k 1) + stepsOf (poly_constM n k c) +
           stepsOf (poly_addM n (unity_mod_X_exp (ZN n) k 1)
                                (unity_mod_const (ZN n) k c))``,
  rw[poly_X_addM_def, poly_X_exp_addM_steps_thm]);

(* Theorem: 0 < n ==>
           stepsOf (poly_X_addM n k c) <=
           15 * MAX 1 k * size k * size n +
            7 * MAX 1 k * size k * size c * size n +
           12 * MAX 1 k * size n ** 2 *)
(* Proof:
     stepsOf (poly_X_addM n k c)
   = stepsOf (poly_X_exp_addM n k 1 c)              by poly_X_addM_def
  <= 15 * MAX 1 k * size k * size n * size 1 +
     7 * MAX 1 k * size k * size c * size n +
     12 * MAX 1 k * size n ** 2                     by poly_X_exp_addM_steps_upper
   = 15 * MAX 1 k * size k * size n +               by size_1
     7 * MAX 1 k * size k * size c * size n +
     12 * MAX 1 k * size n ** 2
*)
val poly_X_addM_steps_upper = store_thm(
  "poly_X_addM_steps_upper",
  ``!n k c. 0 < n ==>
           stepsOf (poly_X_addM n k c) <=
           15 * MAX 1 k * size k * size n +
            7 * MAX 1 k * size k * size c * size n +
           12 * MAX 1 k * size n ** 2``,
  metis_tac[poly_X_addM_def, poly_X_exp_addM_steps_upper, size_1, MULT_RIGHT_1]);

(* Theorem: 0 < n ==>
           stepsOf (poly_X_addM n k c) <= 34 * MAX 1 k * size k * size c * size n ** 2 *)
(* Proof:
     stepsOf (poly_X_addM n k c)
   = stepsOf (poly_X_exp_addM n k 1 c)                      by poly_X_addM_def
  <= 34 * MAX 1 k * size k * size 1 * size c * size n ** 2  by poly_X_exp_addM_steps_bound
   = 34 * MAX 1 k * size k * size c * size n ** 2           by size_1
*)
val poly_X_addM_steps_bound = store_thm(
  "poly_X_addM_steps_bound",
  ``!n k c. 0 < n ==>
           stepsOf (poly_X_addM n k c) <= 34 * MAX 1 k * size k * size c * size n ** 2``,
  metis_tac[poly_X_addM_def, poly_X_exp_addM_steps_bound, size_1, MULT_RIGHT_1]);

(* ------------------------------------------------------------------------- *)
(* Introspective Checks                                                      *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``poly_expM 7 [1;1;0;0] 7``; = ([1; 0; 0; 1],Count 3060): thm
> EVAL ``poly_X_exp_addM 7 4 7 1``; = ([1; 0; 0; 1],Count 108): thm
> EVAL ``poly_expM 7 [2;1;0;0] 7``; = ([2; 0; 0; 1],Count 3123): thm
> EVAL ``poly_X_exp_addM 7 4 7 2``; = ([2; 0; 0; 1],Count 115): thm
> EVAL ``poly_expM 7 [3;1;0;0] 7``; = ([3; 0; 0; 1],Count 3232): thm
> EVAL ``poly_X_exp_addM 7 4 7 3``; = ([3; 0; 0; 1],Count 115): thm
*)

(* Introspective check for (X + c) in (MOD n, unity k) *)
val poly_introM_def = Define`
    poly_introM n k c =
      do
         p <- poly_X_addM n k c;       (* p <- X + c *)
         q <- poly_expM n p n;         (* q <- p ** n (MOD n, unity k) *)
         r <- poly_X_exp_addM n k n c; (* r <- X ** n + c *)
         poly_eqM q r;                 (* return q = r *)
      od
`;

(*
> EVAL ``poly_introM 7 4 1``; = (T,Count 3299): thm
> EVAL ``poly_introM 7 4 2``; = (T,Count 3377): thm
> EVAL ``poly_introM 7 4 3``; = (T,Count 3486): thm
> EVAL ``poly_introM 7 4 4``; = (T,Count 3446): thm
> EVAL ``poly_introM 10 4 1``; = (F,Count 4089): thm
*)

(* Theorem: poly_introM n k c =
            do
              p <- poly_X_exp_addM n k 1 c;
              q <- poly_expM n p n;
              r <- poly_X_exp_addM n k n c;
              poly_eqM q r;
            od *)
(* Proof: by poly_introM_def, poly_X_addM_def *)
val poly_introM_alt = store_thm(
  "poly_introM_alt",
  ``!n k c. poly_introM n k c =
      do
         p <- poly_X_exp_addM n k 1 c;
         q <- poly_expM n p n;
         r <- poly_X_exp_addM n k n c;
         poly_eqM q r;
      od``,
  rw[poly_introM_def, poly_X_addM_def]);

(* Introspective range check for c = 1 .. s, (X + c) in (MOD n, unity k) *)
(* use count down from s to match unity_mod_intro_range *)
Definition poly_intro_rangeM_def:
    poly_intro_rangeM n k c =
       do
         c0 <- zeroM c;
         if c0 then return T
         else do
                b1 <- poly_introM n k c;
                if b1 then do
                             j <- decM c;
                             poly_intro_rangeM n k j;
                           od
                else return F
              od
       od
Termination WF_REL_TAC `measure (\(n,k,c). c)` >> simp[]
End

(*
> EVAL ``poly_intro_rangeM 10 7 2``; = (F,Count 10726): thm
> EVAL ``poly_intro_rangeM 7 4 4``; = (T,Count 13625): thm
for n = 31, k = 29, s = 25.
> EVAL ``poly_intro_rangeM 31 29 25``;
*)


(* Theorem: 0 < n ==> (valueOf (poly_introM n k c) = unity_mod_intro (ZN n) k n c) *)
(* Proof:
     valueOf (poly_introM n k c)
   = valueOf (poly_eqM (valueOf (poly_expM n (valueOf (poly_X_addM n k c)) n))
                       (valueOf (poly_X_exp_addM n k n c))    by poly_introM_def
   = (valueOf (poly_expM n (valueOf (poly_X_addM n k c)) n) =
       valueOf (poly_X_exp_addM n k n c))                     by poly_eqM_value
   = (unity_mod_exp (ZN n) (unity_mod_monomial (ZN n) k c) n =
      unity_mod_special (ZN n) k m c)                         by poly_expM_value, poly_X_addM_weak
   = unity_mod_intro (ZN n) k n c)                            by unity_mod_intro_def
*)
val poly_introM_value = store_thm(
  "poly_introM_value[simp]",
  ``!n k c. 0 < n ==> (valueOf (poly_introM n k c) = unity_mod_intro (ZN n) k n c)``,
  rw[poly_introM_def, unity_mod_intro_def, unity_mod_monomial_weak, ZN_ring]);

(* Theorem: 0 < n ==> (valueOf (poly_intro_rangeM n k c) = unity_mod_intro_range (ZN n) k n c) *)
(* Proof:
   By induction from poly_intro_rangeM_def.
   Base: valueOf (poly_intro_rangeM n k 0) <=> unity_mod_intro_range (ZN n) k n 0
      LHS = valueOf (poly_intro_rangeM n k 0) = T     by poly_intro_rangeM_def
      RHS = unity_mod_intro_range (ZN n) k n 0 = T    by unity_mod_intro_range_def
   Step: c <> 0 ==>
         valueOf (if unity_mod_intro (ZN n) k n c
                  then do j <- decM c; poly_intro_rangeM n k j od
                  else unit F) <=> unity_mod_intro_range (ZN n) k n c
      Note valueOf (poly_introM n k c)
         = unity_mod_intro (ZN n) k n c   by poly_introM_value
       and SUC (c - 1) = c                by c <> 0
      If unity_mod_intro (ZN n) k n c,
         valueOf (do j <- decM c; poly_intro_rangeM n k j od)
       = valueOf (poly_intro_rangeM n k (c - 1))
       = unity_mod_intro_range (ZN n) k n (c - 1))   by induction hypothesis
       = unity_mod_intro_range (ZN n) k n c          by unity_mod_intro_range_def
      If ~unity_mod_intro (ZN n) k n c
         valueOf (unit F)
       = F
       = unity_mod_intro_range (ZN n) k n c          by unity_mod_intro_range_def
*)
val poly_intro_rangeM_value = store_thm(
  "poly_intro_rangeM_value[simp]",
  ``!n k c. 0 < n ==> (valueOf (poly_intro_rangeM n k c) = unity_mod_intro_range (ZN n) k n c)``,
  ho_match_mp_tac (theorem "poly_intro_rangeM_ind") >>
  rw[] >>
  rw[Once poly_intro_rangeM_def] >-
  rw[Once unity_mod_intro_range_def] >>
  `valueOf (poly_introM n k c) = unity_mod_intro (ZN n) k n c` by rw[] >>
  `SUC (c - 1) = c` by decide_tac >>
  (Cases_on `unity_mod_intro (ZN n) k n c` >> simp[] >> metis_tac[unity_mod_intro_range_def]));

(* Theorem: let p = valueOf (poly_X_addM n k c);
               q = valueOf (poly_expM n p n);
               r = valueOf (poly_X_exp_addM n k n c)
            in stepsOf (poly_introM n k c) =
               stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
               stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r) *)
(* Proof:
     stepsOf (poly_introM n k c)
   = stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
     stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r)     by poly_introM_def
      where p = valueOf (poly_X_addM n k c),
            q = valueOf (poly_expM n p n),
            r = valueOf (poly_X_exp_addM n k n c)
*)
val poly_introM_steps_thm = store_thm(
  "poly_introM_steps_thm",
  ``!n k c. let p = valueOf (poly_X_addM n k c);
                q = valueOf (poly_expM n p n);
                r = valueOf (poly_X_exp_addM n k n c)
             in stepsOf (poly_introM n k c) =
                stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
                stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r)``,
  rw[poly_introM_def]);

(* Theorem: 0 < n ==>
           stepsOf (poly_introM n k c) <=
           9 * MAX 1 k * size n +
           34 * MAX 1 k * size k * size c * size n ** 2 +
           34 * MAX 1 k * size k * size c * size n ** 3 +
           83 * MAX 1 k ** 2 * size n ** 4 *)
(* Proof:
   Note Weak (ZN n) p                       by poly_X_addM_weak
    and LENGTH p = k                        by poly_X_addM_length
   Note Weak (ZN n) q                       by poly_expM_weak
    and LENGTH q = k                        by poly_expM_length
   Note Weak (ZN n) r                       by poly_X_exp_addM_weak
    and LENGTH r = k                        by poly_X_exp_addM_length
      stepsOf (poly_introM n k c)
    = stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
      stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r)  by poly_introM_steps_thm
   <= 34 * MAX 1 k * size k * size c * size n ** 2 +              by poly_X_addM_steps_bound
      83 * MAX 1 k ** 2 * size n ** 2 * size n ** 2 +             by poly_expM_steps_bound
      34 * MAX 1 k * size k * size n * size c * size n ** 2 +     by poly_X_exp_addM_steps_bound
      9 * MAX 1 k * size n                                        by poly_eqM_steps_thm, poly_eqM_steps_bound, cases on n = 1
   <= 9 * MAX 1 k * size n +
      34 * MAX 1 k * size k * size c * size n ** 2 +
      34 * MAX 1 k * size k * size c * size n ** 3 +
      83 * MAX 1 k ** 2 * size n ** 4
*)
val poly_introM_steps_upper = store_thm(
  "poly_introM_steps_upper",
  ``!n k c. 0 < n ==>
           stepsOf (poly_introM n k c) <=
           9 * MAX 1 k * size n +
           34 * MAX 1 k * size k * size c * size n ** 2 +
           34 * MAX 1 k * size k * size c * size n ** 3 +
           83 * MAX 1 k ** 2 * size n ** 4``,
  rpt strip_tac >>
  assume_tac poly_introM_steps_thm >>
  first_x_assum (qspecl_then [`n`, `k`, `c`] strip_assume_tac) >>
  qabbrev_tac `p = valueOf (poly_X_addM n k c)` >>
  qabbrev_tac `q = valueOf (poly_expM n p n)` >>
  qabbrev_tac `r = valueOf (poly_X_exp_addM n k n c)` >>
  `stepsOf (poly_introM n k c) =
     stepsOf (poly_X_addM n k c) + stepsOf (poly_expM n p n) +
     stepsOf (poly_X_exp_addM n k n c) + stepsOf (poly_eqM q r)` by metis_tac[] >>
  `Weak (ZN n) p` by rw[poly_X_addM_weak, Abbr`p`] >>
  `LENGTH p = k` by rw[poly_X_addM_length, Abbr`p`] >>
  `Weak (ZN n) q` by rw[poly_expM_weak, Abbr`q`] >>
  `LENGTH q = if n = 1 then 0 else k` by rw[poly_expM_length, Abbr`q`] >>
  `Weak (ZN n) r` by rw[poly_X_exp_addM_weak, Abbr`r`] >>
  `LENGTH r = k` by rw[poly_X_exp_addM_length, Abbr`r`] >>
  `stepsOf (poly_X_addM n k c) <= 34 * MAX 1 k * size k * size c * size n ** 2` by rw[poly_X_addM_steps_bound] >>
  `stepsOf (poly_expM n p n) <= 83 * MAX 1 k ** 2 * size n ** 2 * size n ** 2` by rw[poly_expM_steps_bound] >>
  `stepsOf (poly_X_exp_addM n k n c) <= 34 * MAX 1 k * size k * size n * size c * size n ** 2` by rw[poly_X_exp_addM_steps_bound] >>
  `stepsOf (poly_eqM q r) <= 9 * MAX 1 k * size n` by
  (Cases_on `n = 1` >| [
    `q = []` by rw[poly_expM_trivial, Abbr`q`] >>
    `stepsOf (poly_eqM q r) = 2` by rw[Once poly_eqM_steps_thm] >>
    `0 < MAX 1 k * size n` by rw[] >>
    decide_tac,
    rw[poly_eqM_steps_bound]
  ]) >>
  `MAX 1 k * size k * size n * size c * size n ** 2 = MAX 1 k * size k * size c * size n ** 3` by rw[] >>
  `MAX 1 k ** 2 * size n ** 2 * size n ** 2 = MAX 1 k ** 2 * size n ** 4` by rw[] >>
  decide_tac);

(* Theorem: 0 < n ==>
           stepsOf (poly_introM n k c) <= 160 * MAX 1 k ** 2 * size k * size c * size n ** 4 *)
(* Proof:
      stepsOf (poly_introM n k c)
   <= 9 * MAX 1 k * size n +
      34 * MAX 1 k * size k * size c * size n ** 2 +
      34 * MAX 1 k * size k * size c * size n ** 3 +
      83 * MAX 1 k ** 2 * size n ** 4               by poly_introM_steps_upper
   <= (9 + 34 + 34 + 83) * MAX 1 k ** 2 * size k * size c * size n ** 4   by dominant term
    = 160 * MAX 1 k ** 2 * size k * size c * size n ** 4
*)
val poly_introM_steps_bound = store_thm(
  "poly_introM_steps_bound",
  ``!n k c. 0 < n ==>
           stepsOf (poly_introM n k c) <= 160 * MAX 1 k ** 2 * size k * size c * size n ** 4``,
  rpt strip_tac >>
  imp_res_tac poly_introM_steps_upper >>
  first_x_assum (qspecl_then [`k`, `c`] strip_assume_tac) >>
  qabbrev_tac `h = MAX 1 k` >>
  qabbrev_tac `t = h ** 2 * size k * size c * size n ** 4` >>
  `stepsOf (poly_introM n k c) <= 160 * t` suffices_by rw[Abbr`t`] >>
  `0 < h` by rw[Abbr`h`] >>
  `h * size n <= t` by
  (`h * size n <= h * size n * (h * size k * size c * size n ** 3)` by rw[MULT_POS] >>
  `h * size n * (h * size k * size c * size n ** 3) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `h * size k * size c * size n ** 2 <= t` by
    (`h * size k * size c * size n ** 2 <= h * size k * size c * size n ** 2 * (h * size n ** 2)` by rw[MULT_POS] >>
  `h * size k * size c * size n ** 2 * (h * size n ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `h * size k * size c * size n ** 3 <= t` by
      (`h * size k * size c * size n ** 3 <= h * size k * size c * size n ** 3 * (h * size n)` by rw[MULT_POS] >>
  `h * size k * size c * size n ** 3 * (h * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `h ** 2 * size n ** 4 <= t` by
        (`h ** 2 * size n ** 4 <= h ** 2 * size n ** 4 * (size k * size c)` by rw[MULT_POS] >>
  `h ** 2 * size n ** 4 * (size k * size c) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* The following is just to match conditions in AKSclean.poly_introM_value_alt *)

(* Theorem: 1 < n /\ 1 < k ==>
           stepsOf (poly_introM n k c) <= 160 * k ** 2 * size k * size c * size n ** 4 *)
(* Proof: poly_introM_steps_bound, MAX_1_POS *)
val poly_introM_steps_bound_alt = store_thm(
  "poly_introM_steps_bound_alt",
  ``!n k c. 1 < n /\ 1 < k ==>
           stepsOf (poly_introM n k c) <= 160 * k ** 2 * size k * size c * size n ** 4``,
  metis_tac[poly_introM_steps_bound, MAX_1_POS, DECIDE``1 < n ==> 0 < n``]);

(* Theorem: stepsOf (poly_intro_rangeM n k c) =
           size c +
           if c = 0 then 0
           else stepsOf (poly_introM n k c) +
                if ~(valueOf (poly_introM n k c)) then 0
                else size c + stepsOf (poly_intro_rangeM n k (c - 1)) *)
(* Proof:
     stepsOf (poly_intro_rangeM n k c)
   = stepsOf (zeroM c) + if c = 0 then 0
     else stepsOf (poly_introM n k c) + if ~(valueOf (poly_introM n k c)) then 0
     else stepsOf (decM c) + stepsOf (poly_intro_rangeM n k (c - 1))   by poly_intro_rangeM_def
   = size c + if c = 0 then 0
     else stepsOf (poly_introM n k c) + if ~(valueOf (poly_introM n k c)) then 0
     else size c + stepsOf (poly_intro_rangeM n k (c - 1))
*)
val poly_intro_rangeM_steps_thm = store_thm(
  "poly_intro_rangeM_steps_thm",
  ``!n k c. stepsOf (poly_intro_rangeM n k c) =
           size c +
           if c = 0 then 0
           else stepsOf (poly_introM n k c) +
                if ~(valueOf (poly_introM n k c)) then 0
                else size c + stepsOf (poly_intro_rangeM n k (c - 1))``,
  rw[Once poly_intro_rangeM_def] >>
  fs[]);

(* Theorem: stepsOf (poly_intro_rangeM n k c) =
           if c = 0 then 1
           else size c + stepsOf (poly_introM n k c) +
                (if ~(valueOf (poly_introM n k c)) then 0 else size c) +
                if ~(valueOf (poly_introM n k c)) then 0
                else stepsOf (poly_intro_rangeM n k (c - 1)) *)
(* Proof:
     stepsOf (poly_intro_rangeM n k c)
   = size c + if c = 0 then 0
     else stepsOf (poly_introM n k c) + if ~(valueOf (poly_introM n k c)) then 0
     else size c + stepsOf (poly_intro_rangeM n k (c - 1))      by poly_intro_rangeM_steps_thm
   = if c = 0 then size 0
     else size c + stepsOf (poly_introM n k c) +
          (if ~(valueOf (poly_introM n k c)) then 0 else size c) +
     if ~(valueOf (poly_introM n k c)) then 0 else stepsOf (poly_intro_rangeM n k (c - 1))
*)
val poly_intro_rangeM_steps_by_dec_loop = store_thm(
  "poly_intro_rangeM_steps_by_dec_loop",
  ``!n k c. stepsOf (poly_intro_rangeM n k c) =
           if c = 0 then 1
           else size c + stepsOf (poly_introM n k c) +
                (if ~(valueOf (poly_introM n k c)) then 0 else size c) +
                if ~(valueOf (poly_introM n k c)) then 0
                else stepsOf (poly_intro_rangeM n k (c - 1))``,
  rw[Once poly_intro_rangeM_steps_thm]);

(*
This puts poly_intro_rangeM_steps in the category: decreasing loop with body cover and exit.
   poly_intro_rangeM_steps_by_dec_loop:
        !c. loop c = if c = 0 then c else body c + if exit c then 0 else loop (c - 1)
suitable for: loop_dec_count_cover_exit_le
*)

(* Theorem: 0 < n ==>
           stepsOf (poly_intro_rangeM n k c) <=
           1 + 2 * c * size c + 160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4 *)
(* Proof:
   Let body = (\c. size c + stepsOf (poly_introM n k c) +
                (if ~(valueOf (poly_introM n k c)) then 0 else size c)),
       cover = (\c. 2 * size c + 160 * MAX 1 k ** 2 * size k * size c * size n ** 4)
       exit = (\c. ~(valueOf (poly_introM n k c))),
       loop = (\c. stepsOf (poly_intro_rangeM n k c)).
   Then !c. loop c = if c = 0 then 1 else body c + if exit c then 0 else loop (c - 1)
                                          by poly_intro_rangeM_steps_by_dec_loop
    Now !x. body x <= cover x             by poly_introM_steps_bound
    and MONO cover                        by size_monotone_le
   Thus loop c
     <= 1 + hop 1 c * cover c             by loop_dec_count_cover_exit_le
      = 1 + c * (2 * size c + 160 * MAX 1 k ** 2 * size k * size c * size n ** 4)  by hop_1_n
      = 1 + 2 * c * size c + 160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4
*)
val poly_intro_rangeM_steps_upper = store_thm(
  "poly_intro_rangeM_steps_upper",
  ``!n k c. 0 < n ==>
           stepsOf (poly_intro_rangeM n k c) <=
           1 + 2 * c * size c + 160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4``,
  rpt strip_tac >>
  assume_tac poly_intro_rangeM_steps_by_dec_loop >>
  first_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  qabbrev_tac `body = \c. size c + stepsOf (poly_introM n k c) +
                (if ~(valueOf (poly_introM n k c)) then 0 else size c)` >>
  qabbrev_tac `cover = \c. 2 * size c + 160 * MAX 1 k ** 2 * size k * size c * size n ** 4` >>
  qabbrev_tac `exit = \c. ~(valueOf (poly_introM n k c))` >>
  qabbrev_tac `loop = \c. stepsOf (poly_intro_rangeM n k c)` >>
  `loop c <= 1 + 2 * c * size c + 160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4` suffices_by rw[] >>
  `!c. loop c = if c = 0 then 1 else body c + if exit c then 0 else loop (c - 1)` by metis_tac[] >>
  `0 < 1` by decide_tac >>
  `!x. body x <= cover x` by
  (rpt strip_tac >>
  `body x <= 2 * size x + stepsOf (poly_introM n k x)` by rw[Abbr`body`] >>
  `stepsOf (poly_introM n k x) <= 160 * MAX 1 k ** 2 * size k * size x * size n ** 4` by rw[poly_introM_steps_bound] >>
  rw[Abbr`cover`]) >>
  `MONO cover` by
    (rw[Abbr`cover`] >>
  `size x <= size y` by rw[size_monotone_le] >>
  `size k * size n ** 4 * size x * MAX 1 k ** 2 <=
    size k * size n ** 4 * size y * MAX 1 k ** 2` by rw[size_monotone_le] >>
  decide_tac) >>
  drule loop_dec_count_cover_exit_le >>
  ntac 2 (disch_then drule) >>
  disch_then dxrule >>
  simp[hop_1_n] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `c` strip_assume_tac) >>
  `c * cover c = 2 * c * size c + 160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4` by rw[Abbr`cover`] >>
  decide_tac);

(* Theorem: 0 < n ==>
           stepsOf (poly_intro_rangeM n k c) <=
           163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4 *)
(* Proof:
      stepsOf (poly_intro_rangeM n k c)
   <= 1 + 2 * c * size c +
      160 * c * MAX 1 k ** 2 * size k * size c * size n ** 4   by poly_intro_rangeM_steps_upper
   <= (1 + 2 + 160) * c * MAX 1 k ** 2 * size k * size c * size n ** 4   by dominant term
    = 163 * c * MAX 1 k ** 2 * size k * size c * size n ** 4
   Use (MAX 1 c) to cater for c = 0
*)
val poly_intro_rangeM_steps_bound = store_thm(
  "poly_intro_rangeM_steps_bound",
  ``!n k c. 0 < n ==>
           stepsOf (poly_intro_rangeM n k c) <=
           163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4``,
  rpt strip_tac >>
  imp_res_tac poly_intro_rangeM_steps_upper >>
  first_x_assum (qspecl_then [`k`, `c`] strip_assume_tac) >>
  qabbrev_tac `d = MAX 1 c` >>
  qabbrev_tac `h = MAX 1 k` >>
  qabbrev_tac `t = d * h ** 2 * size k * size c * size n ** 4` >>
  `stepsOf (poly_intro_rangeM n k c) <= 163 * t` suffices_by rw[Abbr`t`] >>
  `0 < d /\ 0 < h` by rw[Abbr`d`, Abbr`h`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `c * size c <= t` by
  (`c * size c <= d * size c` by rw[Abbr`d`] >>
  `d * size c <= d * size c * (h ** 2 * size k * size n ** 4)` by rw[MULT_POS] >>
  `d * size c * (h ** 2 * size k * size n ** 4) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `c * h ** 2 * size k * size c * size n ** 4 <= t` by
    (`c * h ** 2 * size k * size c * size n ** 4 <= d * h ** 2 * size k * size c * size n ** 4` by rw[Abbr`d`] >>
  `d * h ** 2 * size k * size c * size n ** 4 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* The following is just to match conditions in AKSclean.poly_intro_rangeM_value_alt *)

(* Theorem: 1 < n /\ 1 < k ==>
           stepsOf (poly_intro_rangeM n k c) <=
           163 * MAX 1 c * k ** 2 * size k * size c * size n ** 4 *)
(* Proof: poly_intro_rangeM_steps_bound, MAX_1_POS *)
val poly_intro_rangeM_steps_bound_alt = store_thm(
  "poly_intro_rangeM_steps_bound_alt",
  ``!n k c. 1 < n /\ 1 < k ==>
           stepsOf (poly_intro_rangeM n k c) <=
           163 * MAX 1 c * k ** 2 * size k * size c * size n ** 4``,
  metis_tac[poly_intro_rangeM_steps_bound, MAX_1_POS, DECIDE``1 < n ==> 0 < n``]);

(* Theorem: c <= k /\ k < n ==>
           stepsOf (poly_intro_rangeM n k c) <= 163 * MAX 1 k ** 3 * size n ** 6 *)
(* Proof:
   Note 0 < n                              by c <= k /\ k < n
    and MAX 1 c <= MAX 1 k                 by MAX_LE, c <= k
    and size c <= size k                   by size_monotone_le, c <= k
    and size k <= size n                   by size_monotone_lt, k < n

      stepsOf (poly_intro_rangeM n k c)
   <= 163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4
                                           by poly_intro_rangeM_steps_bound
   <= 163 * MAX 1 k * MAX 1 k ** 2 * size n * size n * size n ** 4
                                           by inequalities
    = 163 * MAX 1 k ** 3 * size n ** 6     by arithmetic
*)
val poly_intro_rangeM_steps_bound_thm = store_thm(
  "poly_intro_rangeM_steps_bound_thm",
  ``!n k c. c <= k /\ k < n ==>
           stepsOf (poly_intro_rangeM n k c) <= 163 * MAX 1 k ** 3 * size n ** 6``,
  rpt strip_tac >>
  qabbrev_tac `s = stepsOf (poly_intro_rangeM n k c)` >>
  `s <= 163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4`
               by rw[poly_intro_rangeM_steps_bound, Abbr`s`] >>
  `MAX 1 c <= MAX 1 k` by rw[] >>
  `size c <= size k` by rw[size_monotone_le] >>
  `size k <= size n` by rw[size_monotone_lt] >>
  `163 * MAX 1 c * MAX 1 k ** 2 * size k * size c * size n ** 4 <=
    163 * MAX 1 k * MAX 1 k ** 2 * size n * size n * size n ** 4`
                      by rw[MULT_POS, LESS_MONO_MULT2] >>
  `MAX 1 k * MAX 1 k ** 2 = MAX 1 k ** 3` by rw[] >>
  `size n * size n * size n ** 4 = size n ** 6` by rw[] >>
  `163 * MAX 1 k * MAX 1 k ** 2 * size n * size n * size n ** 4 =
    163 * MAX 1 k ** 3 * size n ** 6` by rw[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* AKS Algorithm with simple bound                                           *)
(* ------------------------------------------------------------------------- *)
(*
> aks_def;
val it = |- !n. aks n <=>
          power_free_test n /\
          case aks_param n of
            nice j => j = n
          | good k => unity_mod_intro_range (ZN n) k n k
          | bad => F: thm
*)

(* The full AKS in monadic style *)
val aksM_def = Define`
    aksM n =
      do
        b0 <- power_freeM n;
        if b0 then do
                     c0 <- paramM n;
                     case c0 of
                       nice j => eqM j n
                     | good k => poly_intro_rangeM n k k
                     | bad => return F
                   od
        else return F
      od
`;

(*
> EVAL ``aksM 0``; = (F,Count 2): thm
> EVAL ``aksM 1``; = (F,Count 12): thm
> EVAL ``aksM 2``; = (T,Count 129): thm
> EVAL ``aksM 3``; = (T,Count 337): thm
> EVAL ``aksM 4``; = (F,Count 243): thm
> EVAL ``aksM 5``; = (T,Count 866): thm
> EVAL ``aksM 6``; = (F,Count 581): thm
> EVAL ``aksM 7``; = (T,Count 1423): thm
> EVAL ``aksM 8``; = (F,Count 330): thm
> EVAL ``MAP aksM [0 .. 11]``; =
      [(F,Count 2); (F,Count 12); (T,Count 129); (T,Count 337);
       (F,Count 243); (T,Count 866); (F,Count 581); (T,Count 1423);
       (F,Count 330); (F,Count 606); (F,Count 1003); (T,Count 3447)]: thm
*)

(* Theorem: valueOf (aksM n) = aks0 n *)
(* Proof:
   Note power_free_test n
    ==> power_free n                    by power_free_test_eqn
    ==> n <> 0                          by power_free_0
     valueOf (aksM n)
   = if (valueOf (power_freeM n)) then
             case (valueOf (paramM n)) of
               nice j => valueOf (eqM j n)
             | good k => valueOf (poly_intro_rangeM n k k)
             | bad => return F
          else F                         by aksM_def
   = if ~(power_free_test n) then F      by power_freeM_value
     else case (param M) of              by paramM_value
            nice j => (j = n)            by eqM_value
          | good k => unity_mod_intro_range (ZN n) k n k
                                         by poly_intro_rangeM_value, 0 < n
          | bad => return F
   = aks0 n                              by aks0_def
*)
val aksM_value = store_thm(
  "aksM_value[simp]",
  ``!n. valueOf (aksM n) = aks0 n``,
  rw[aksM_def, aks0_def] >>
  `n <> 0` by metis_tac[power_free_test_eqn, power_free_0] >>
  (Cases_on `param n` >> simp[]));

(* Theorem: stepsOf (power_freeM n) +
            if power_free n
            then stepsOf (paramM n) +
                 case (param n) of
                   nice j => size (MAX j n)
                 | good k => stepsOf (poly_intro_rangeM n k k)
                 | bad => 0
            else 0 *)
(* Proof:
     stepsOf (aksM n)
   = stepsOf (power_freeM n) +
     if power_free_test n
     then stepsOf (paramM n) +
           case (param n) of
             nice j => stepsOf (eqM j n)
           | good k => stepsOf (poly_intro_rangeM n k k)
           | bad => 0
     else 0                         by aksM_def
   = stepsOf (power_freeM n) +
     if power_free n                by power_free_test_eqn
     then stepsOf (paramM n) +
           case (param n) of
             nice j => size (MAX j n)       by size_max
           | good k => stepsOf (poly_intro_rangeM n k k)
           | bad => 0
     else 0
*)
val aksM_steps_thm = store_thm(
  "aksM_steps_thm",
  ``!n. stepsOf (aksM n) =
       stepsOf (power_freeM n) +
            if power_free n
            then stepsOf (paramM n) +
                 case (param n) of
                   nice j => size (MAX j n)
                 | good k => stepsOf (poly_intro_rangeM n k k)
                 | bad => 0
            else 0``,
  rw[aksM_def, power_free_test_eqn] >>
  (Cases_on `param n` >> simp[size_max]));

(* Theorem: (stepsOf (aksM 0) = 2) /\ (stepsOf (aksM 1) = 12) *)
(* Proof: by evaluation *)
val aksM_steps_base = store_thm(
  "aksM_steps_base",
  ``(stepsOf (aksM 0) = 2) /\ (stepsOf (aksM 1) = 12)``,
  EVAL_TAC);

(* Theorem: stepsOf (aksM n) <=
            207 * size n ** 9 + 1418157969 * size n ** 20 + 4075 * size n ** 21 *)
(* Proof:
   Note stepsOf (aksM n)
      = stepsOf (power_freeM n) +
             if power_free n
             then stepsOf (paramM n) +
                  case (param n) of
                    nice j => size (MAX j n)
                  | good k => stepsOf (poly_intro_rangeM n k k)
                  | bad => 0
             else 0                      by aksM_steps_thm
    and stepsOf (power_freeM n)
     <= 207 * size n ** 9                by power_freeM_steps_bound
    and stepsOf (paramM n)
     <= 1348980357 * size n ** 20        by paramM_steps_bound

   Note 1 < n                            by power_free_gt_1
   If ~power_free n, true                by first and second term.
   If (param n = bad), true              by first, second and third term.

   Before going further,
   Let c = 1 + HALF (ulog n ** 5)
        <= 1 + HALF (size n ** 5)        by size_ulog, HALF_LE_MONO
   Note size n <> 0                      by size_pos
    and size n <> 1                      by size_eq_1, 1 < n
     so 1 < size n                       by size n <> 0, size n <> 1
    ==> 1 < size n ** 5                  by ONE_LT_EXP
   Thus 1 + HALF (size n ** 5)
     <= size n ** 5                      by HALF_ADD1_LE
     or c <= size n ** 5                 by above
    and size c <= size (size n ** 5)     by size_monotone_le
               <= 5 * size (size n)      by size_exp_upper_alt
               <= 5 * size n             by size_size_le

   If (param n = nice k),
      There is an additional term: size (MAX k n)
      If n = 2,
         Then k = 2                      by param_2
         so size (MAX k n)
          = size 2                       by MAX_DEF
          = 2                            by size_2
         Hence happens to be true, smaller than fourth term.
      If n <> 2, then 2 < n              by 1 < n
         Then k <= c                     by param_nice_bound, 2 < n
           so size k <= size c           by size_monotone_le
                     <= 5 * size n       by above
         so size (MAX k n)
          = MAX (size k) (size n)        by size_max
         <= 5 * size n                   by MAX_LE
         This also happens to be true, smaller than fourth term.

   If (param n = good k),
      There is an additional term: stepsOf (poly_intro_rangeM n k k)
      Note k <= c                        by param_good_bound
       and size k <= size c              by size_monotone_le
                  <= 5 * size n          by above
      Note 1 < k                         by aks_param_good, param_eqn
        so MAX 1 k = k                   by MAX_DEF
       Now stepsOf (poly_intro_rangeM n k k)
        <= 163 * MAX 1 k * MAX 1 k ** 2 * size k * size k * size n ** 4
                                         by poly_intro_rangeM_steps_bound, 0 < n
         = 163 * k ** 3 * size k ** 2 * size n ** 4
        <= 163 * (size n ** 5) ** 3 * size k ** 2 * size n ** 4        by k <= c, c <= size n ** 5
        <= 163 * (size n ** 5) ** 3 * (5 * size n) ** 2 * size n ** 4  by size k <= 5 * size n
         = 163 * 25 * size n ** 15 * size n ** 2 * size n ** 4         by EXP_EXP_MULT
         = 4075 * size n ** 21           which is the fourth term.

   Overall,
      stepsOf (aksM n)
   <= 207 * size n ** 9 + 1348980357 * size n ** 20 + 4075 * size n ** 21
*)
val aksM_steps_upper = store_thm(
  "aksM_steps_upper",
  ``!n. stepsOf (aksM n) <=
       207 * size n ** 9 + 1348980357 * size n ** 20 + 4075 * size n ** 21``,
  rpt strip_tac >>
  qabbrev_tac `c = 1 + HALF (ulog n ** 5)` >>
  `stepsOf (power_freeM n) <= 207 * size n ** 9` by rw[power_freeM_steps_bound] >>
  `stepsOf (paramM n) <= 1348980357 * size n ** 20` by rw[paramM_steps_bound] >>
  rw[aksM_steps_thm] >>
  `1 < n` by rw[power_free_gt_1] >>
  `c <= size n ** 5` by
  (`c <= 1 + HALF (size n ** 5)` by rw[size_ulog, HALF_LE_MONO, Abbr`c`] >>
  `size n <> 0` by rw[] >>
  `size n <> 1` by fs[size_eq_1] >>
  `1 < size n` by decide_tac >>
  `1 < size n ** 5` by rw[ONE_LT_EXP] >>
  `1 + HALF (size n ** 5) <= size n ** 5` by rw[HALF_ADD1_LE] >>
  decide_tac) >>
  `size c <= 5 * size n` by
    (`size c <= size (size n ** 5)` by rw[size_monotone_le] >>
  `size (size n ** 5) <= 5 * size (size n)` by rw[size_exp_upper_alt] >>
  `size (size n) <= size n` by rw[size_size_le] >>
  decide_tac) >>
  (Cases_on `param n` >> simp[]) >| [
    `size (MAX n' n) <= 4075 * size n ** 21` suffices_by decide_tac >>
    Cases_on `n = 2` >| [
      `n' = 2` by fs[param_2] >>
      `size (MAX n' n) = 2` by rw[] >>
      `0 < size n ** 21` by rw[] >>
      decide_tac,
      `n' <= c` by rw[param_nice_bound, Abbr`c`] >>
      `size n' <= size c` by rw[size_monotone_le] >>
      `size n' <= 5 * size n` by decide_tac >>
      `size (MAX n' n) = MAX (size n') (size n)` by rw[size_max] >>
      `MAX (size n') (size n) <= 5 * size n` by rw[MAX_LE] >>
      `size n <= size n * size n ** 20` by rw[MULT_POS] >>
      `size n * size n ** 20 = size n ** 21` by rw[] >>
      decide_tac
    ],
    `stepsOf (poly_intro_rangeM n n' n') <= 4075 * size n ** 21` suffices_by decide_tac >>
    `n' <= c` by rw[param_good_bound, Abbr`c`] >>
    `size n' <= size c` by rw[size_monotone_le] >>
    `size n' <= 5 * size n` by decide_tac >>
    `stepsOf (poly_intro_rangeM n n' n') <=
    163 * MAX 1 n' * MAX 1 n' ** 2 * size n' * size n' * size n ** 4` by rw[poly_intro_rangeM_steps_bound] >>
    `1 < n'` by metis_tac[aks_param_good, param_eqn] >>
    `MAX 1 n' = n'` by rw[MAX_DEF] >>
    `stepsOf (poly_intro_rangeM n n' n') <= 163 * n' ** 3 * size n' ** 2 * size n ** 4` by fs[] >>
    `n' ** 3 * size n' ** 2 * size n ** 4 <=
    c ** 3 * size n' ** 2 * size n ** 4` by rw[] >>
    `c ** 3 * size n' ** 2 * size n ** 4 <=
    (size n ** 5) ** 3 * size n' ** 2 * size n ** 4` by rw[] >>
    `(size n ** 5) ** 3 * size n' ** 2 * size n ** 4 <=
    (size n ** 5) ** 3 * (5 * size n) ** 2 * size n ** 4` by rw[] >>
    `(size n ** 5) ** 3 * (5 * size n) ** 2 * size n ** 4 =
    (size n ** 15) * (25 * size n ** 2) * size n ** 4` by rw[EXP_BASE_MULT, GSYM EXP_EXP_MULT] >>
    `_ = 25 * size n ** 21` by rw[] >>
    decide_tac
  ]);

(* Theorem: stepsOf (aksM n) <= 1348984639 * size n ** 21 *)
(* Proof:
     stepsOf (aksM n)
   <= 207 * size n ** 9 + 1348980357 * size n ** 20 + 4075 * size n ** 21
                                                      by aksM_steps_upper
   <= (207 + 1348980357 + 4075) * size n ** 21        by dominant term
    = 1348984639 * size n ** 21
*)
val aksM_steps_bound = store_thm(
  "aksM_steps_bound",
  ``!n. stepsOf (aksM n) <= 1348984639 * size n ** 21``,
  rpt strip_tac >>
  assume_tac aksM_steps_upper >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `t = size n ** 21` >>
  `size n ** 9 <= size n ** 9 * size n ** 12` by rw[MULT_POS] >>
  `size n ** 20 <= size n ** 20 * size n` by rw[MULT_POS] >>
  `size n ** 9 * size n ** 12 = t` by rw[Abbr`t`] >>
  `size n ** 20 * size n = t` by rw[Abbr`t`] >>
  decide_tac);

(* Theorem: (stepsOf o aksM) IN O_poly 21 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (aksM n) <= k * size n ** 21
   Note stepsOf (aksM n) <= 1348984639 * size n ** 21  by aksM_steps_bound
   Take any h, put k = 1348984639, the result follows.
*)
val aksM_steps_O_poly = store_thm(
  "aksM_steps_O_poly",
  ``(stepsOf o aksM) IN O_poly 21``,
  metis_tac[aksM_steps_bound, O_poly_thm, combinTheory.o_THM]);

(* Theorem: (stepsOf o aksM) IN big_O (\n. ulog n ** 21) *)
(* Proof:
   Note (stepsOf o aksM) IN O_poly 21     by aksM_steps_O_poly
    and O_poly 21
      = big_O (POLY 21 o ulog)            by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 21)                by POLY_def, FUN_EQ_THM
   The result follows.
*)
val aksM_steps_big_O = store_thm(
  "aksM_steps_big_O",
  ``(stepsOf o aksM) IN big_O (\n. ulog n ** 21)``,
  assume_tac aksM_steps_O_poly >>
  `O_poly 21 = big_O (POLY 21 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 21 o ulog = \n. ulog n ** 21` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (aksM n) <=> aks0 n) /\
            (stepsOf o aksM) IN big_O (\n. ulog n ** 21) *)
(* Proof: by aksM_value, aksM_steps_big_O *)
val aksM_thm = store_thm(
  "aksM_thm",
  ``!n. (valueOf (aksM n) <=> aks0 n) /\ (stepsOf o aksM) IN big_O (\n. ulog n ** 21)``,
  metis_tac[aksM_value, aksM_steps_big_O]);

(* Note: aks0 n = aks n  is proved in AKSclean: aks0_eq_aks *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
