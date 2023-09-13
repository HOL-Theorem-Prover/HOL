(* ------------------------------------------------------------------------- *)
(* Windmills and Involutions.                                                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "windmill";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)
(* val _ = load "helperTwosqTheory"; *)
open helperTwosqTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
(* val _ = load "dividesTheory"; *)
open dividesTheory;
(* val _ = load "gcdTheory"; *)
open gcdTheory; (* for P_EUCLIDES *)

open pairTheory; (* for FORALL_PROD, PAIR_EQ *)

(* val _ = load "involuteFixTheory"; *)
open involuteTheory involuteFixTheory;

(* val _ = load "GaussTheory"; *)
open logrootTheory logPowerTheory; (* for SQRT, SQRT_LE *)
open GaussTheory; (* for divisors_has_factor *)


(* ------------------------------------------------------------------------- *)
(* Windmills and Involutions Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Helper Theorem:
   triple_parts            |- !t. ?x y z. t = (x,y,z)

   Windmill:
   windmill_def            |- !x y z. windmill (x, y, z) = x ** 2 + 4 * y * z
   windmill_comm           |- !x y z. windmill (x, y, z) = windmill (x, z, y)
   windmill_flip           |- !x y z. windmill (x, y, z) = windmill (x, z, y)
   windmill_by_squares     |- !x y. windmill (x, y, y) = x ** 2 + (2 * y) ** 2
   windmill_eq_0           |- !x y z. windmill (x, y, z) = 0 <=> x = 0 /\ y * z = 0
   windmill_trivial        |- !k. windmill (1,1,k) = 4 * k + 1
   windmill_trivial_flip   |- !k. windmill (1,k,1) = 4 * k + 1
   windmill_trivial_prime  |- !p. p MOD 4 = 1 /\ prime p ==>
                                  !x z. p = windmill (x, x, z) <=> x = 1 /\ z = p DIV 4
   windmill_x_y_y          |- !n x y. n = windmill (x, y, y) ==>
                                  n = x ** 2 + (2 * y) ** 2 /\ (ODD n <=> ODD x)
   windmill_yz_product     |- !n x y z. n = windmill (x, y, z) ==> y * z = (n - x ** 2) DIV 4
   windmill_yz_eq_0        |- !n x y z. n = windmill (x, y, z) ==> ((n - x ** 2) DIV 4 = 0 <=> y = 0 \/ z = 0)
   windmill_x_upper        |- !n x y z. n = windmill (x,y,z) ==> x <= SQRT n
   windmill_yz_upper       |- !n x y z. n = windmill (x,y,z) ==> y * z <= n DIV 4
   windmill_y_upper        |- !n x y z. n = windmill (x,y,z) /\ 0 < z ==> y <= n DIV 4
   windmill_z_upper        |- !n x y z. n = windmill (x,y,z) /\ 0 < y ==> z <= n DIV 4
   windmill_nonsquare      |- !n x y z. ~square n /\ n = windmill (x, y, z) ==> y * z <> 0
   windmill_arm_divisors   |- !n x y z. ~square n /\ n = windmill (x, y, z) ==>
                                        (let p = (n - x * x) DIV 4 in y IN divisors p /\ z = p DIV y)
   windmill_with_no_mind   |- !n. n MOD 4 = 0 <=> ?y z. n = windmill (0,y,z)
   windmill_with_mind      |- !n x y z. n MOD 4 <> 0 /\ n = windmill (x,y,z) ==> 0 < x
   windmill_with_no_arms   |- !n. square n <=> ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y)
   windmill_with_arms      |- !n x y z. ~square n /\ n = windmill (x,y,z) ==> 0 < y /\ 0 < z
   windmill_mind_and_arms  |- !n x y z. n MOD 4 <> 0 /\ ~square n /\ n = windmill (x,y,z) ==> 0 < x /\ 0 < y /\ 0 < z

   Set of windmills:
   mills_def               |- !n. mills n = {(x,y,z) | n = windmill (x, y, z)}
   mills_element           |- !n x y z. (x,y,z) IN mills n <=> n = windmill (x, y, z)
   mills_element_alt       |- !n t. t IN mills n <=> n = windmill t
   mills_element_triple    |- !n t. t IN mills n <=> ?x y z. t = (x,y,z) /\ n = windmill (x, y, z)
   mills_element_flip      |- !n x y z. (x,y,z) IN mills n ==> (x,z,y) IN mills n
   mills_element_trivial   |- !n. n MOD 4 = 1 ==> (1,1,n DIV 4) IN mills n
   mills_element_trivial_flip
                           |- !n. n MOD 4 = 1 ==> (1,n DIV 4,1) IN mills n
   mills_0                 |- mills 0 = {(0,0,n) | n IN univ(:num)} UNION
                                         {(0,n,0) | n IN univ(:num)}
   mills_0_infinite        |- INFINITE (mills 0)
   mills_1                 |- mills 1 = {1} CROSS ({0} CROSS univ(:num)) UNION
                                        {1} CROSS (univ(:num) CROSS {0})
   mills_1_infinite        |- INFINITE (mills 1)
   mills_non_square_bound  |- !n x y z. ~square n /\ (x,y,z) IN mills n ==> x < n /\ y < n /\ z < n
   mills_non_square_subset |- !n. ~square n ==> mills n SUBSET count n CROSS (count n CROSS count n)
   mills_non_square_card_upper
                           |- !n. ~square n ==> CARD (mills n) < n ** 3
   mills_non_square_finite |- !n. ~square n ==> FINITE (mills n)
   mills_finite_non_square |- !n. FINITE (mills n) <=> ~square n

   mills_with_no_mind      |- !n. n MOD 4 = 0 <=> ?y z. (0,y,z) IN mills n
   mills_with_all_mind     |- !n. n MOD 4 <> 0 <=> !x y z. (x,y,z) IN mills n ==> x <> 0
   mills_with_mind         |- !n. n MOD 4 <> 0 <=> !x y z. (x,y,z) IN mills n ==> 0 < x
   mills_with_no_arms      |- !n. square n <=> ?x y. (x,y,0) IN mills n \/ (x,0,y) IN mills n
   mills_with_all_arms     |- !n. ~square n <=> !x y z. (x,y,z) IN mills n ==> y <> 0 /\ z <> 0
   mills_with_arms         |- !n. ~square n <=> !x y z. (x,y,z) IN mills n ==> 0 < y /\ 0 < z
   mills_with_mind_and_arms|- !n. n MOD 4 <> 0 /\ ~square n <=>
                                  !x y z. (x,y,z) IN mills n ==> 0 < x /\ 0 < y /\ 0 < z
   mills_non_empty         |- !n. n MOD 4 = 1 ==> mills n <> {}
   mills_triple_nonzero    |- !n. n MOD 4 <> 0 /\ ~square n ==>
                              !x y z. (x,y,z) IN mills n ==> x <> 0 /\ y <> 0 /\ z <> 0
   mills_prime_triple_nonzero
                           |- !p x y z. prime p /\ (x,y,z) IN mills p ==>
                                        x <> 0 /\ y <> 0 /\ z <> 0

   Flip involution:
   flip_def                |- !x y z. flip (x,y,z) = (x,z,y)
   flip_fix                |- !x y z. flip (x,y,z) = (x,y,z) <=> y = z
   flip_fixes              |- !n. fixes flip (mills n) = {(x,y,y) | n = windmill (x,y,y)}
   flip_fixes_element      |- !n x y z. (x,y,z) IN fixes flip (mills n) <=> n = windmill (x,y,z) /\ y = z
   flip_fixes_alt          |- !s x. x IN fixes flip s <=> x IN s /\ flip x = x
   flip_windmill           |- !t. windmill t = windmill (flip t)
   flip_closure            |- !n t. t IN mills n ==> flip t IN mills n
   flip_closure_iff        |- !n t. t IN mills n <=> flip t IN mills n
   flip_involute           |- !t. flip (flip t) = t
   flip_involute_mills     |- !n. flip involute (mills n)

   Zagier's involution:
   zagier_def              |- !x y z. zagier (x,y,z) =
                                      if x < y - z then (x + 2 * z,z,y - z - x)
                                      else if x < 2 * y then (2 * y - x,y,x + z - y)
                                      else (x - 2 * y,x + z - y,y)
   zagier_fix              |- !x y z. x <> 0 ==> (zagier (x,y,z) = (x,y,z) <=> x = y)
   zagier_fixes            |- !n. n MOD 4 <> 0 ==> fixes zagier (mills n) = {(x,x,z) | n = windmill (x,x,z)}
   zagier_fixes_element    |- !n x y z. n MOD 4 <> 0 ==>
                                        ((x,y,z) IN fixes zagier (mills n) <=> n = windmill (x,y,z) /\ x = y)
   zagier_fixes_alt        |- !s x. x IN fixes zagier s <=> x IN s /\ zagier x = x
   zagier_windmill         |- !t. windmill t = windmill (zagier t)
   zagier_closure          |- !n t. t IN mills n ==> zagier t IN mills n
   zagier_closure_iff      |- !n t. t IN mills n <=> zagier t IN mills n
   zagier_0_y_z            |- !y z. zagier (0,y,z) =
                                    if z < y then (2 * z,z,y - z)
                                    else if 0 < y then (2 * y,y,z - y)
                                    else (0,z,0)
   zagier_x_0_z            |- !x z. zagier (x,0,z) = (x,x + z,0)
   zagier_x_y_0            |- !x y. zagier (x,y,0) =
                                    if x < y then (x,0,y - x)
                                    else if x < 2 * y then (2 * y - x,y,x - y)
                                    else (x - 2 * y,x - y,y)
   zagier_1_y_1            |- !y. zagier (1,y,1) =
                                  if y = 0 then (1,2,0)
                                  else if y = 1 then (1,1,1)
                                  else if y = 2 then (3,2,0)
                                  else (3,1,y - 2)
   zagier_1_1_z            |- !z. zagier (1,1,z) = (1,1,z)
   zagier_x_0_0            |- !x. zagier (x,0,0) = (x,x,0)
   zagier_0_y_0            |- !y. zagier (0,y,0) = (0,0,y)
   zagier_0_0_z            |- !z. zagier (0,0,z) = (0,z,0)
   zagier_0_1_z            |- !z. zagier (0,1,z) = if z = 0 then (0,0,1) else (2,1,z - 1)
   zagier_0_0_0            |- zagier (0,0,0) = (0,0,0)
   zagier_x_y_y            |- !x y. zagier (x,y,y) =
                                    if x < 2 * y then (2 * y - x,y,x) else (x - 2 * y,x,y)
   zagier_x_x_z            |- !x z. x <> 0 ==> zagier (x,x,z) = (x,x,z)
   zagier_involute         |- !x y z. x <> 0 /\ z <> 0 ==> zagier (zagier (x,y,z)) = (x,y,z)
   zagier_involute_alt     |- !x y z. x * z <> 0 ==> zagier (zagier (x,y,z)) = (x,y,z)
   zagier_involute_thm     |- !t. FST t <> 0 /\ SND (SND t) <> 0 ==> zagier (zagier t) = t

   doublet_def             |- !x y z. doublet (x,y,z) = x * z
   doublet_eq_0            |- !x y z. (doublet (x,y,z) = 0) <=> (x = 0) \/ (z = 0)
   zagier_involute_alt     |- !t. doublet t <> 0 ==> zagier (zagier t) = t
   zagier_involute_mills   |- !n. n MOD 4 <> 0 /\ ~square n ==> zagier involute (mills n)
   zagier_involute_mills_prime
                           |- !p. prime p ==> zagier involute (mills p)

   Mind of a windmill:
   mind_def            |- !x y z. mind (x,y,z) =
                                  if x < y - z then x + 2 * z
                                  else if x < y then 2 * y - x
                                  else x
   mind_zagier_eqn     |- !x y z. mind (zagier (x,y,z)) = mind (x,y,z)
   mind_zagier_thm     |- !t. mind (zagier t) = mind t
   mind_flip_eqn       |- !x y z. mind (flip (x,y,z)) =
                                  if x < z - y then x + 2 * y
                                  else if x < z then 2 * z - x
                                  else x
   mind_flip_1_1_z     |- !z. mind (flip (1,1,z)) = if z < 2 then 1 else 3
   mind_flip_x_x_z     |- !x z. mind (flip (x,x,z)) =
                                if x < z - x then 3 * x else if x < z then 2 * z - x else x
   mind_flip_x_y_y     |- !x y. mind (flip (x,y,y)) = if x < y then 2 * y - x else x

   Gap of a Windmill:
   gap_def             |- !x y z. gap (x,y,z) = if y < z then z - y else y - z
   gap_flip_eqn        |- !x y z. gap (flip (x,y,z)) = gap (x,y,z)
   gap_flip_thm        |- !t. gap (flip t) = gap t

   Zagier and Flip:
   zagier_flip_windmill|- !t. windmill t = windmill ((zagier o flip) t)
   zagier_flip_eqn     |- !x y z. (zagier o flip) (x,y,z) =
                                  if x < z - y then (x + 2 * y,y,z - y - x)
                                  else if x < 2 * z then (2 * z - x,z,x + y - z)
                                  else (x - 2 * z,x + y - z,z)
   zagier_flip_1_1_z   |- !z. (zagier o flip) (1,1,z) =
                              if z = 0 then (1,2,0)
                              else if z = 1 then (1,1,1)
                              else if z = 2 then (3,2,0)
                              else (3,1,z - 2)
   zagier_flip_0_1_z   |- !z. (zagier o flip) (0,1,z) =
                              if z = 0 then (0,1,0)
                              else (2,1,z - 1)
   zagier_flip_0_y_z   |- !y z. (zagier o flip) (0,y,z) =
                                if 0 < z - y then (2 * y,y,z - y)
                                else if 0 < z then (2 * z,z,y - z)
                                else (0,y,0)
   zagier_flip_x_0_z   |- !x z. (zagier o flip) (x,0,z) =
                                if x < z then (x,0,z - x)
                                else if x < 2 * z then (2 * z - x,z,x - z)
                                else (x - 2 * z,x - z,z)
   zagier_flip_x_y_0   |- !x y. (zagier o flip) (x,y,0) = (x,x + y,0)
   zagier_flip_x_y_x   |- !x y. 0 < x ==> (zagier o flip) (x,y,x) = (x,x,y)

   flip_zagier_windmill|- !t. windmill t = windmill ((flip o zagier) t)
   flip_zagier_eqn     |- !x y z. (flip o zagier) (x,y,z) =
                                  if x < y - z then (x + 2 * z,y - z - x,z)
                                  else if x < 2 * y then (2 * y - x,x + z - y,y)
                                  else (x - 2 * y,y,x + z - y)
   flip_zagier_x_x_z   |- !x z. 0 < x ==> (flip o zagier) (x,x,z) = (x,z,x)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ?x y z. t = (x, y, z) *)
(* Proof: by x = FST t, FST (SND t), and SND (SND t). *)
Theorem triple_parts:
  !(t :num # num # num). ?x y z. t = (x, y, z)
Proof
  metis_tac[PAIR]
QED

(* ------------------------------------------------------------------------- *)
(* Windmill Theory                                                           *)
(* ------------------------------------------------------------------------- *)

(*

             +---+
             |   |
             |   |
             |   |
             |   |
             |   |          y
             |   +---------------------+
             |   |                     | z
             |   +-----+---+-----------+
             |   |  x  |   |
             |   |     |   |
 +-----------+---+-----+   |
 |                     |   |
 +---------------------+   |
                       |   |
                       |   |
                       |   |
                       |   |
                       |   |
                       +---+

 Note: need n not a square, so that y * z <> 0.
 Note: need n not a multiple of 4, so that x <> 0.

 Note: need x * y * z <> 0 for the windmill picture:

   Algorithm:
   1. draw the square of side x.
   2. from each square vertex, put the line y alongside, in clockwise manner.
   3. complete the 4 rectangles y * z, around the central square.


 The 5 types of windmills:
 -------------------------

 Type 1: x < y - z, so x < y.
 example: zagier (3,6,1) = (5,1,2)

       * *                          * *
       * *                          * *
       * * * * * * * *              * * * * * * * *
       * * * * * * * *              *         * * *
       * *     * *                  *         *
       * *     * *        -->       *         *
   * * * * * * * *              * * *         *
   * * * * * * * *              * * * * * * * *
               * *                          * *
               * *                          * *

       square: 3x3 -> 5x5, mind = 5x5.
         x' = x + left z + right z = x + 2z
         y' = z
         z' = y - (x + z) = y - x - z, because x + z < y.

 Type 2: y - z < x, and x < y, so x < 2y.
 example: zagier (3,6,4) = (9,6,1)

               * * * * * * *                 * * * * * * *
       * * * * * * * * * * *         * * * * * * * * * * *
       * * * * * * * * * * *         * *                 *
       * * * * * * * * * * *         * *                 *
       * * * * * * * * * * * *       * *                 * *
       * * * * *     * * * * *       * *                 * *
       * * * * *     * * * * *  -->  * *                 * *
       * * * * * * * * * * * *       * *                 * *
         * * * * * * * * * * *         *                 * *
         * * * * * * * * * * *         *                 * *
         * * * * * * * * * * *         * * * * * * * * * * *
         * * * * * * *                 * * * * * * *

       square: 3x3 -> 9x9, mind = 9x9.
         x' = x + left (y - x) + right (y - x) = 2y - x
         y' = y
         z' = (x + z) - y = x + z - y, because y < x + z.

 Type 3: y = x, so y - z < x, and x < 2y.
 example: zagier (4,4,2) = (4,4,2)

         * * * * *                 * * * * *
         * * * * *                 * * * * *
     * * * * * * * * *         * * * * * * * * *
     * * *       * * *         * * *       * * *
     * * *       * * *   -->   * * *       * * *
     * * *       * * *         * * *       * * *
     * * * * * * * * *         * * * * * * * * *
         * * * * *                 * * * * *
         * * * * *                 * * * * *

       square: 4x4 -> 4x4, mind = 4x4.
         x' = x
         y' = y
         z' = z, all unchanged.

 Type 4: y < x, but x < 2y.
 example: zagier (6,4,2) = (2,4,4)

        * * * * *                     * * * * *
        * * * * *                     * * * * *
        * * * * * * * * *             * * * * * * * * *
        *           * * *             * * * * * * * * *
    * * *           * * *         * * * * * * * * * * *
    * * *           * * *    -->  * * * * *   * * * * *
    * * *           * * *         * * * * * * * * * * *
    * * *           *             * * * * * * * * *
    * * * * * * * * *             * * * * * * * * *
            * * * * *                   * * * * * *
            * * * * *                   * * * * * *

       square: 6x6 -> 2x2, mind = 6x6.
         x' = x - left (x - y) - right (x - y) = 2y - x
         y' = y
         z' = (x + z) - y = x + z - y, because y < x + z.

 Type 5: 2y < x, so y < x.
 example: zagier (8,3,2) = (2,7,3)

      * * * *                           * * * *
      * * * *                           * * * *
      * * * * * * * * * * *             * * * * * * * * * * *
      *               * * *             * * * * * * * * * * *
      *               * * *             * * * * * * * * * * *
      *               * * *             * * * * * * * * * * *
      *               *       -->       * * * *   * * * *
  * * *               *             * * * * * * * * * * *
  * * *               *             * * * * * * * * * * *
  * * *               *             * * * * * * * * * * *
  * * * * * * * * * * *             * * * * * * * * * * *
                * * * *                           * * * *
                * * * *                           * * * *

       square: 8x8 -> 2x2, mind = 6x6.
         x' = x - left y - right y = x - 2y
         y' = (x + z) - y = x + z - y, because y < x + z.
         z' = y.

   "mind" is the maximum central square:
   if x < y - z, central square expands to x + left z + right z = x + 2z.
   else if x < y, central square expands to x + left (y - x) + right (y - x) = 2y - x.
   else central square is at maximum, keeps as x.

*)

(* ------------------------------------------------------------------------- *)
(* Part 1: Windmill                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define windmill of a triple *)
Definition windmill_def:
   windmill (x, y, z) = x ** 2 + 4 * y * z
End

(* Theorem: windmill (x, y, z) = windmill (x, z, y) *)
(* Proof:
     windmill (x, y, z)
   = x ** 2 + 4 * y * z         by windmill_def
   = x ** 2 + 4 * z * y         by MULT_COMM
   = windmill (x, z, y)         by windmill_def
*)
Theorem windmill_comm:
  !x y z. windmill (x, y, z) = windmill (x, z, y)
Proof
  simp[windmill_def]
QED

(* Theorem alias *)
Theorem windmill_flip = windmill_comm;
(* val windmill_flip = |- !x y z. windmill (x, y, z) = windmill (x, z, y): thm *)

(* Theorem: windmill (x, y, y) = x ** 2 + (2 * y) ** 2 *)
(* Proof:
     windmill (x, y, y)
   = x ** 2 + 4 * y * y           by windmill_def
   = x ** 2 + (2 * y) * (2 * y)   by arithmetic
   = x ** 2 + (2 * y) ** 2        by EXP_2
*)
Theorem windmill_by_squares:
  !x y. windmill (x, y, y) = x ** 2 + (2 * y) ** 2
Proof
  simp[windmill_def, EXP_BASE_MULT]
QED

(* Theorem: windmill (x, y, z) = 0 <=> x = 0 /\ y * z = 0 *)
(* Proof:
       windmill (x, y, z) = 0
   <=> x ** 2 + 4 * y * z = 0           by windmill_def
   <=> x * x + 4 * y * z = 0            by EXP_2
   <=> (x * x = 0) /\ (4 * y * z = 0)   by ADD_EQ_0
   <=> (x = 0) /\ (y * z = 0)           by MULT_EQ_0
*)
Theorem windmill_eq_0:
  !x y z. windmill (x, y, z) = 0 <=> x = 0 /\ y * z = 0
Proof
  simp[windmill_def]
QED

(* Theorem: windmill (1, 1, k) = 4 * k + 1 *)
(* Proof:
     windmill (1, 1, k)
   = 1 ** 2 + 4 * 1 * k         by windmill_def
   = 1 + 4 * k                  by arithmetic
   = 4 * k + 1                  by arithmetic
*)
Theorem windmill_trivial:
  !k. windmill (1, 1, k) = 4 * k + 1
Proof
  simp[windmill_def]
QED

(* Theorem: windmill (1,k,1) = 4 * k + 1 *)
(* Proof:
     windmill (1,k,1)
   = 1 ** 2 + 4 * k * 1            by windmill_def
   = 4 * k + 1                     by arithmetic
*)
Theorem windmill_trivial_flip:
  !k. windmill (1,k,1) = 4 * k + 1
Proof
  simp[windmill_def]
QED

(* Theorem: p MOD 4 = 1 /\ prime p ==>
            !x z. p = windmill (x, x, z) <=> x = 1 /\ z = p DIV 4 *)
(* Proof:
   Let k = p DIV 4,
   Then p = 4 * k + 1                by DIVISION

   If part: p = windmill (x, x, z) ==> ((x = 1) /\ (z = k))
      Note p = windmill (x, x, z)
             = x ** 2 + 4 * x * z    by windmill_def
             = x * (x + 4 * z)       by arithmetic
      Thus x divides p               by divides_def
        so x = 1 or x = p            by prime_def
      If x = 1,
         p = 4 * k + 1
           = 1 + 4 * z               by above
        so z = k                     by arithmetic
      If x = p,
         then p + 4 * z = 1          by EQ_MULT_LCANCEL
         but 1 < p                   by ONE_LT_PRIME
        and this is impossible.
   Only-if part: p = windmill (1, 1, k)
      Note p = 4 * k + 1
             = windmill (1, 1, k)        by windmill_trivial
*)
Theorem windmill_trivial_prime:
  !p. p MOD 4 = 1 /\ prime p ==>
      !x z. p = windmill (x, x, z) <=> x = 1 /\ z = p DIV 4
Proof
  rpt strip_tac >>
  qabbrev_tac `k = p DIV 4` >>
  `p = k * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  `_ = 4 * k + 1` by simp[] >>
  simp[EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    `p = x ** 2 + 4 * x * z` by rw[windmill_def] >>
    `_ = x * x + 4 * z * x` by simp[] >>
    `_ = (x + 4 * z) * x` by decide_tac >>
    `x divides p` by metis_tac[divides_def] >>
    `(x = 1) \/ (x = p)` by metis_tac[prime_def] >-
    fs[] >>
    fs[],
    rw[windmill_trivial]
  ]
QED

(* Theorem: n = windmill (x, y, y) ==>
            n = x ** 2 + (2 * y) ** 2 /\ (ODD n <=> ODD x) *)
(* Proof:
   Note n = x ** 2 + (2 * y) ** 2    by windmill_by_squares
    and EVEN (2 * y)                 by EVEN_DOUBLE
     so EVEN (2 * y) ** 2            by EVEN_SQ
        ODD n
    <=> ODD (x ** 2)                 by ODD_ADD, ODD_EVEN
    <=> ODD x                        by ODD_SQ
*)
Theorem windmill_x_y_y:
  !n x y. n = windmill (x, y, y) ==>
          n = x ** 2 + (2 * y) ** 2 /\ (ODD n <=> ODD x)
Proof
  ntac 4 strip_tac >>
  `n = x ** 2 + (2 * y) ** 2` by rw[windmill_by_squares] >>
  `EVEN (2 * y)` by rw[EVEN_DOUBLE] >>
  `EVEN ((2 * y) ** 2)` by rw[EVEN_SQ] >>
  `ODD n <=> ODD (x ** 2)` by metis_tac[ODD_ADD, ODD_EVEN] >>
  simp[ODD_SQ]
QED

(* Theorem: n = windmill (x, y, z) ==> y * z = (n - x ** 2) DIV 4 *)
(* Proof:
   Note n = x ** 2 + 4 * y * z                 by windmill_def
     so y * z = (n - x ** 2) DIV 4             by arithmetic
*)
Theorem windmill_yz_product:
  !n x y z. n = windmill (x, y, z) ==> y * z = (n - x ** 2) DIV 4
Proof
  rw[windmill_def]
QED

(* Theorem: n = windmill (x, y, z) ==> ((n - x ** 2) DIV 4 = 0 <=> y = 0 \/ z = 0) *)
(* Proof:
   Note n = x ** 2 + 4 * y * z                 by windmill_def
     so (n - x ** 2) DIV 4 = y * z             by arithmetic
   Thus     (n - x ** 2) DIV 4 = 0
         <=> y * z = 0                         by above
    or   <=> y = 0 \/ z = 0                    by MULT_EQ_0
*)
Theorem windmill_yz_eq_0:
  !n x y z. n = windmill (x, y, z) ==> ((n - x ** 2) DIV 4 = 0 <=> y = 0 \/ z = 0)
Proof
  rw[windmill_def]
QED

(* Theorem: n = windmill (x,y,z) ==> x <= SQRT n *)
(* Proof:
   Note n = x ** 2 + 4 * y * z     by windmill_def
     so x ** 2 <= n                by inequality
    ==> SQRT (x ** 2) <= SQRT n    by SQRT_LE
     or             x <= SQRT n    by SQRT_OF_SQ
*)
Theorem windmill_x_upper:
  !n x y z. n = windmill (x,y,z) ==> x <= SQRT n
Proof
  rw[windmill_def] >>
  qabbrev_tac `n = 4 * (y * z) + x ** 2` >>
  `x ** 2 <= n` by simp[Abbr`n`] >>
  metis_tac[SQRT_LE, SQRT_OF_SQ]
QED

(* Theorem: n = windmill (x,y,z) ==> y * z <= n DIV 4 *)
(* Proof:
   Note n = x ** 2 + 4 * y * z     by windmill_def
     so 4 y * z <= n               by inequality
    ==>   y * z <= n DIV 4         by DIV_LE_MONOTONE
*)
Theorem windmill_yz_upper:
  !n x y z. n = windmill (x,y,z) ==> y * z <= n DIV 4
Proof
  simp[windmill_def]
QED

(* Theorem: n = windmill (x,y,z) /\ 0 < z ==> y <= n DIV 4 *)
(* Proof:
   Note y <= y * z             by LE_MULT_CANCEL_LBARE, 0 < z
    and y * z <= n DIV 4       by windmill_yz_upper
     so y <= n DIV 4           by LESS_EQ_TRANS
*)
Theorem windmill_y_upper:
  !n x y z. n = windmill (x,y,z) /\ 0 < z ==> y <= n DIV 4
Proof
  metis_tac[windmill_yz_upper, LE_MULT_CANCEL_LBARE, LESS_EQ_TRANS]
QED

(* Theorem: n = windmill (x,y,z) /\ 0 < y ==> z <= n DIV 4 *)
(* Proof:
   Note windmill (x,y,z) = windmill (x,z,y)    by windmill_comm
     so z <= n DIV 4                           by windmill_y_upper
*)
Theorem windmill_z_upper:
  !n x y z. n = windmill (x,y,z) /\ 0 < y ==> z <= n DIV 4
Proof
  metis_tac[windmill_y_upper, windmill_comm]
QED

(* Theorem: ~square n /\ n = windmill (x, y, z) ==> y * z <> 0 *)
(* Proof:
   Note n = x ** 2 + 4 * y * z                 by windmill_def
   By contradiction, assume y * z = 0.
   Then n = x ** 2, contradicting ~square n    by square_def
*)
Theorem windmill_nonsquare:
  !n x y z. ~square n /\ n = windmill (x, y, z) ==> y * z <> 0
Proof
  rw_tac bool_ss[windmill_def] >>
  spose_not_then strip_assume_tac >>
  `x ** 2 + 4 * y * z = x * x` by fs[GSYM EXP_2] >>
  metis_tac[square_def]
QED

(* Theorem: ~square n /\ n = windmill (x, y, z) ==>
     let p = (n - x * x) DIV 4 in y IN divisors p /\ z = p DIV y *)
(* Proof:
   Note n = x ** 2 + 4 * y * z     by windmill_def
     so p = y * z                  by p = (n - x * x) DIV 4
    but 0 < p                      by square_def, ~square n
     so y IN divisors p            by divisors_has_factor
   Also 0 < y                      by MULT_EQ_0
     so z = p DIV y                by DIV_SOLVE_COMM
*)
Theorem windmill_arm_divisors:
  !n x y z. ~square n /\ n = windmill (x, y, z) ==>
     let p = (n - x * x) DIV 4 in y IN divisors p /\ z = p DIV y
Proof
  rpt strip_tac >>
  qabbrev_tac `foo = (n = windmill (x, y, z))` >>
  rw_tac bool_ss[] >| [
    qabbrev_tac `foo = (~square n)` >>
    fs[windmill_def] >>
    `y * z = p` by fs[Abbr`p`] >>
    `0 < p` by metis_tac[MULT_0, ADD, square_def, NOT_ZERO, EXP_2] >>
    metis_tac[divisors_has_factor],
    qabbrev_tac `foo = (~square n)` >>
    fs[windmill_def] >>
    `y * z = p` by fs[Abbr`p`] >>
    `p <> 0` by metis_tac[MULT_0, ADD, square_def, EXP_2] >>
    metis_tac[DIV_SOLVE_COMM, MULT_EQ_0, NOT_ZERO]
  ]
QED

(* Theorem: n MOD 4 = 0 <=> ?y z. n = windmill (0,y,z) *)
(* Proof:
   If part: n MOD 4 = 0 ==> ?y z. n = windmill (0,y,z)
      Note n = n DIV 4 * 4 + n MOD 4    by DIVISION
      Let y = n DIV 4, z = 1.
      Then n = 0 ** 2 + 4 * n DIV 4     by n MOD 4 = 0
             = windmill (0,y,z)         by windmill_def
   Only-if part: ?y z. n = windmill (0,y,z) ==> n MOD 4 = 0
          n = windmill (0, y, z)
      ==> n = 0 ** 2 + 4 * y * z        by windmill_def
      ==> n = 4 * y * z                 by arithmetic
      ==> n MOD 4 = 0                   by MOD_EQ_0
*)
Theorem windmill_with_no_mind:
  !n. n MOD 4 = 0 <=> ?y z. n = windmill (0,y,z)
Proof
  rw[windmill_def, EQ_IMP_THM] >| [
    `n = n DIV 4 * 4 + n MOD 4` by rw[DIVISION] >>
    map_every qexists_tac [`n DIV 4`, `1`] >>
    simp[],
    simp[]
  ]
QED

(* Theorem: n MOD 4 <> 0 /\ n = windmill (x,y,z) ==> 0 < x *)
(* Proof:
   Note x <> 0                     by windmill_with_no_mind
     so 0 < x                      by NOT_ZERO
*)
Theorem windmill_with_mind:
  !n x y z. n MOD 4 <> 0 /\ n = windmill (x,y,z) ==> 0 < x
Proof
  metis_tac[windmill_with_no_mind, NOT_ZERO]
QED

(* Theorem: square n <=> ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y) *)
(* Proof:
   If part: square n ==> ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y)
      Note ?k. n = k ** 2          by square_alt
      Let x = k, any y will do,
      Then n = x ** 2 + 4 * y * 0  or n = x ** 2 + 4 * 0 * y
        so n = windmill (x, y, 0)  or n = windmill (x,0,y)
                                   by windmill_def
   Only-if part: ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y) ==> square n
          n = windmill (x,y,0) or n = windmill (x,0,y)
      ==> n = x ** 2               by windmill_def
      ==> square n                 by square_alt
*)
Theorem windmill_with_no_arms:
  !n. square n <=> ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y)
Proof
  rw[windmill_def, EQ_IMP_THM] >-
  simp[GSYM square_alt] >>
  simp[square_alt]
QED

(* Theorem: ~square n /\ n = windmill (x,y,z) ==> 0 < y /\ 0 < z *)
(* Proof:
   Note y * z <> 0                 by windmill_nonsquare
     so 0 < y /\ 0 < z             by MULT_EQ_0
*)
Theorem windmill_with_arms:
  !n x y z. ~square n /\ n = windmill (x,y,z) ==> 0 < y /\ 0 < z
Proof
  metis_tac[windmill_nonsquare, MULT_EQ_0, NOT_ZERO]
QED

(* Theorem: n MOD 4 <> 0 /\ ~square n /\ n = windmill (x,y,z) ==> 0 < x /\ 0 < y /\ 0 < z *)
(* Proof:
   Note 0 < x                      by windmill_with_mind
    and 0 < y /\ 0 < z             by windmill_with_arms, ~square n
*)
Theorem windmill_mind_and_arms:
  !n x y z. n MOD 4 <> 0 /\ ~square n /\ n = windmill (x,y,z) ==> 0 < x /\ 0 < y /\ 0 < z
Proof
  metis_tac[windmill_with_mind, windmill_with_arms]
QED

(* ------------------------------------------------------------------------- *)
(* Part 2: Set of windmills                                                  *)
(* ------------------------------------------------------------------------- *)


(* The set of windmills of a number *)
Definition mills_def[nocompute]:
    mills n = {(x,y,z) | n = windmill (x, y, z)}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: (x, y, z) IN mills n <=> n = windmill (x, y, z) *)
(* Proof: by mills_def. *)
Theorem mills_element:
  !n x y z. (x, y, z) IN mills n <=> n = windmill (x, y, z)
Proof
  simp[mills_def]
QED

(* Theorem: t IN mills n <=> n = windmill t *)
(* Proof: by mills_element, triple_parts. *)
Theorem mills_element_alt:
  !n t. t IN mills n <=> n = windmill t
Proof
  metis_tac[mills_element, triple_parts]
QED

(* Theorem: t IN mills n <=> ?x y z. (t = (x, y, z)) /\ n = windmill (x, y, z) *)
(* Proof: by mills_def. *)
Theorem mills_element_triple:
  !n t. t IN mills n <=> ?x y z. (t = (x, y, z)) /\ n = windmill (x, y, z)
Proof
  simp[mills_def, FORALL_PROD]
QED

(* Theorem: (x, y, z) IN mills n ==> (x, z, y) IN mills n *)
(* Proof:
       (x, y, z) IN mills n
   <=> n = windmill (x, y, z)      by mills_def
   <=> n = windmill (x, z, y)      by windmill_flip
   <=> (x, z, y) IN mills n        by mills_def
*)
Theorem mills_element_flip:
  !n x y z. (x, y, z) IN mills n ==> (x, z, y) IN mills n
Proof
  simp[mills_def, windmill_flip]
QED

(* Theorem: n MOD 4 = 1 ==> (1, 1, n DIV 4) IN mills n *)
(* Proof:
   Note n = (n DIV 4) * 4 + n MOD 4     by DIVISION
          = 4 * (n DIV 4) + 1           by arithmetic
          = windmill (1, 1, (n DIV 4))  by windmill_trivial
   Thus (1, 1, n DIV 4) IN (mills n)    by mills_element
*)
Theorem mills_element_trivial:
  !n. n MOD 4 = 1 ==> (1, 1, n DIV 4) IN mills n
Proof
  rpt strip_tac >>
  `n = (n DIV 4) * 4 + n MOD 4` by rw[DIVISION] >>
  `_ = windmill (1, 1, (n DIV 4))` by rw[windmill_trivial] >>
  fs[mills_element]
QED

(* Theorem: n MOD 4 = 1 ==> (1,n DIV 4,1) IN mills n *)
(* Proof:
   Note (1,1,n DIV 4) IN mills n               by mills_element_trivial
    ==> n = windmill (1,1,n DIV 4)             by mills_element
    ==> n = windmill (1,n DIV 4,1)             by windmill_flip
     so (1,n DIV 4,1) IN mills n               by mills_element
*)
Theorem mills_element_trivial_flip:
  !n. n MOD 4 = 1 ==> (1,n DIV 4,1) IN mills n
Proof
  metis_tac[mills_element_trivial, windmill_flip, mills_element]
QED

(* Theorem: mills 0 = {(0,0,n) | n IN univ(:num)} UNION
                      {(0,n,0) | n IN univ(:num)} *)
(* Proof:
   Let (x,y,z) IN mills 0
   Then 0 = windmill (x, y, z)          by mills_def
          = x ** 2 + 4 * y * z          by windmill_def
    ==> x ** 2 = 0 /\ 4 * y * z = 0     by ADD_EQ_0
    ==>  x * x = 0 /\     y * z = 0     by EXP_2
    ==>      x = 0 /\ (y = 0 \/ z = 0)  by MULT_EQ_0
*)
Theorem mills_0:
  mills 0 = {(0,0,n) | n IN univ(:num)} UNION
            {(0,n,0) | n IN univ(:num)}
Proof
  rw[mills_def, windmill_def, FORALL_PROD, EXTENSION]
QED

(* Theorem: INFINITE (mills 0) *)
(* Proof:
   Let f = (\n. (0,0,n)).
   Then INJ f univ(:num) (mills 0)   by INJ_DEF, mills_0
   Note INFINITE univ(:num)          by INFINITE_NUM_UNIV
    ==> INFINITE (mills 0)           by INFINITE_INJ
*)
Theorem mills_0_infinite:
  INFINITE (mills 0)
Proof
  qabbrev_tac `f = \n:num. (0,0,n)` >>
  `INJ f univ(:num) (mills 0)` by rw[INJ_DEF, mills_0, Abbr`f`] >>
  `INFINITE univ(:num)` by rw[] >>
  metis_tac[INFINITE_INJ]
QED

(* Theorem: mills 1 = {1} CROSS ({0} CROSS univ(:num)) UNION
                      {1} CROSS (univ(:num) CROSS {0}) *)
(* Proof:
   Let (x,y,z) IN mills 1
   Note 4 * y * z <> 1                  by MULT_EQ_1
   Then 1 = windmill (x, y, z)          by mills_def
          = x ** 2 + 4 * y * z          by windmill_def
    <=> x ** 2 = 1 /\ 4 * y * z = 0     by ADD_EQ_1
    <=>  x * x = 1 /\     y * z = 0     by EXP_2
    <=>      x = 1 /\ (y = 0 \/ z = 0)  by MULT_EQ_0
    <=> (x,y,z) IN (1,0,n)  where n IN univ(:num)
     or (x,y,z) IN (1,n,0)  where n IN univ(:num)
    <=> (x,y,z) IN {1} CROSS ({0} CROSS univ(:num))
     or (x,y,z) IN {1} CROSS (univ(:num) CROSS {0})
*)
Theorem mills_1:
  mills 1 = {1} CROSS ({0} CROSS univ(:num)) UNION
            {1} CROSS (univ(:num) CROSS {0})
Proof
  rw[mills_def, windmill_def, FORALL_PROD, EXTENSION, ADD_EQ_1]
QED

(* Theorem: INFINITE (mills 1) *)
(* Proof:
   Let f = (\n. (1,0,n)).
   Then INJ f univ(:num) (mills 0)   by INJ_DEF, mills_1
   Note INFINITE univ(:num)          by INFINITE_NUM_UNIV
    ==> INFINITE (mills 0)           by INFINITE_INJ
*)
Theorem mills_1_infinite:
  INFINITE (mills 1)
Proof
  qabbrev_tac `f = \n:num. (1,0,n)` >>
  `INJ f univ(:num) (mills 1)` by rw[INJ_DEF, mills_1, Abbr`f`] >>
  `INFINITE univ(:num)` by rw[] >>
  metis_tac[INFINITE_INJ]
QED

(* Theorem: ~square n /\ (x, y, z) IN mills n ==> x < n /\ y < n /\ z < n *)
(* Proof:
   Expand by square_def, mills_def, windmill_def, this is to show,
    given !k. 4 * (y * z) + x ** 2 <> k ** 2:
   (1) x < 4 * (y * z) + x ** 2
       Note y * z <> 0          by given condition
         so y <> 0 /\ z <> 0    by MULT_EQ_0
         or 4 * (y * z) <> 0    by MULT_EQ_0
       Note x <= x ** 2         by X_LE_X_SQUARED
       Hence x < 4 * (y * z) + x ** 2    by adding nonzero term to RHS.
   (2) y < 4 * (y * z) + x ** 2
       Note y * z <> 0          by given condition
         so y <> 0 /\ z <> 0    by MULT_EQ_0
       thus 4 * z <> 0          by MULT_EQ_0, z <> 0
        and 4 * z <> 1          by MULT_EQ_1, 4 <> 1
         so y < y * (4 * z)     by LT_MULT_CANCEL_LBARE
       Hence y < 4 * (y * z) + x ** 2    by adding to RHS.
   (3) y <> 0 /\ z <> 0 ==> z < 4 * (y * z) + x ** 2
       Note y * z <> 0          by given condition
         so y <> 0 /\ z <> 0    by MULT_EQ_0
       thus 4 * y <> 0          by MULT_EQ_0, y <> 0
        and 4 * y <> 1          by MULT_EQ_1, 4 <> 1
         so z < z * (4 * y)     by LT_MULT_CANCEL_LBARE
       Hence z < 4 * (y * z) + x ** 2    by adding to RHS.
*)
Theorem mills_non_square_bound:
  !n x y z. ~square n /\ (x, y, z) IN mills n ==> x < n /\ y < n /\ z < n
Proof
  rw[square_def, mills_def, windmill_def] >| [
    `y * z <> 0` by metis_tac[MULT_0, ADD] >>
    `4 * (y * z) <> 0` by metis_tac[MULT_EQ_0, DECIDE``4 <> 0``] >>
    `x <= x ** 2` by rw[X_LE_X_SQUARED] >>
    decide_tac,
    `y * z <> 0` by metis_tac[MULT_0, ADD] >>
    `y <> 0 /\ z <> 0` by metis_tac[MULT_EQ_0] >>
    `4 * z <> 0` by metis_tac[MULT_EQ_0, DECIDE``4 <> 0``] >>
    `4 * z <> 1` by metis_tac[MULT_EQ_1, DECIDE``4 <> 1``] >>
    `y < y * (4 * z)` by rw[LT_MULT_CANCEL_LBARE] >>
    decide_tac,
    `y * z <> 0` by metis_tac[MULT_0, ADD] >>
    `y <> 0 /\ z <> 0` by metis_tac[MULT_EQ_0] >>
    `4 * y <> 0` by metis_tac[MULT_EQ_0, DECIDE``4 <> 0``] >>
    `4 * y <> 1` by metis_tac[MULT_EQ_1, DECIDE``4 <> 1``] >>
    `z < z * (4 * y)` by rw[LT_MULT_CANCEL_LBARE] >>
    decide_tac
  ]
QED

(* Theorem: ~square n ==> mills n SUBSET (count n) CROSS (count n CROSS (count n)) *)
(* Proof: by SUBSET_DEF, mills_non_square_bound, IN_COUNT *)
Theorem mills_non_square_subset:
  !n. ~square n ==> mills n SUBSET (count n) CROSS (count n CROSS (count n))
Proof
  (rw[SUBSET_DEF, FORALL_PROD] >> metis_tac[mills_non_square_bound])
QED

(* Theorem: ~square n ==> CARD (mills n) < n ** 3 *)
(* Proof:
   Let s = count n CROSS (count n CROSS count n),
       t = mills n.
   Then t SUBSET s       by mills_non_square_subset
    and FINITE s         by FINITE_CROSS, FINITE_COUNT
   Note n <> 0           by square_0, ~square n.
    and n <> 1           by square_1, ~square n.
     so 1 < n            by arithmetic
   Thus (1,1,0) IN s     by IN_CROSS, IN_COUNT, 1 < n
    but windmill (1, 1, 0)
      = 1 <> n           by windmill_trivial
     so (1,1,0) NOTIN t  by mills_element
    ==> t <> s           by EXTENSION
    ==> t PSUBSET s      by PSUBSET_DEF
    Now CARD s = n ** 3  by CARD_CROSS, CARD_COUNT
     so CARD t < n ** 3  by CARD_PSUBSET
*)
Theorem mills_non_square_card_upper:
  !n. ~square n ==> CARD (mills n) < n ** 3
Proof
  rpt strip_tac >>
  qabbrev_tac `s = count n CROSS (count n CROSS count n)` >>
  qabbrev_tac `t = mills n` >>
  `t SUBSET s` by fs[mills_non_square_subset, Abbr`t`, Abbr`s`] >>
  `FINITE s` by rw[Abbr`s`] >>
  (Cases_on `n = 0` >> fs[square_def]) >>
  (Cases_on `n = 1` >> fs[square_def]) >>
  `1 < n` by decide_tac >>
  `(1,1,0) IN s` by rw[Abbr`s`] >>
  `(1,1,0) NOTIN t` by rw[mills_element, windmill_trivial, Abbr`t`] >>
  `t <> s` by metis_tac[EXTENSION] >>
  `t PSUBSET s` by fs[PSUBSET_DEF] >>
  `CARD s = n ** 3` by rw[CARD_CROSS, Abbr`s`] >>
  metis_tac[CARD_PSUBSET]
QED
(* This is a very generous upper bound. *)

(* Theorem: ~square n ==> FINITE (mills n) *)
(* Proof:
   Let c = count n.
   Note FINITE c                            by FINITE_COUNT
     so FINITE (c CROSS c CROSS c)          by FINITE_CROSS
    Now mills n SUBSET (c CROSS c CROSS c)  by mills_non_square_subset
     so FINITE (mills n)                    by SUBSET_FINITE
*)
Theorem mills_non_square_finite:
  !n. ~square n ==> FINITE (mills n)
Proof
  metis_tac[mills_non_square_subset, SUBSET_FINITE, FINITE_CROSS, FINITE_COUNT]
QED

(* Another proof of the same theorem. *)

(* Theorem: FINITE (mills n) <=> ~square n *)
(* Proof:
   If part: FINITE (mills n) ==> ~square n
      By contradiction, suppose square n.
      Then ?k. n = k * k = k ** 2       by square_def
      Then n = k ** 2 + 4 * 0 * t       for any t
             = windmill (k, 0, t)       by windmill_def
        so (k,0,t) IN (mills n)
      Let f = \t:num. (k,0,t).
      Then INJ f univ(:num) (mills n)   by INJ_DEF
       But INFINITE univ(:num)          by INFINITE_NUM_UNIV
       ==> INFINITE (mills n)           by INFINITE_INJ
       This contradicts FINITE (mills n).
   Only-if part: ~square n ==> FINITE (mills n)
      This is true                      by mills_non_square_finite
*)
Theorem mills_finite_non_square:
  !n. FINITE (mills n) <=> ~square n
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    fs[square_def] >>
    qabbrev_tac `f = \t:num. (k, 0, t)` >>
    `INJ f univ(:num) (mills n)` by
  (rw[INJ_DEF, mills_def, windmill_def] >| [
      qexists_tac `k` >>
      qexists_tac `0` >>
      qexists_tac `x` >>
      simp[],
      fs[PAIR_EQ, Abbr`f`]
    ]) >>
    metis_tac[INFINITE_NUM_UNIV, INFINITE_INJ],
    rw[mills_non_square_finite]
  ]
QED

(* Theorem: n MOD 4 = 0 <=> ?y z. (0, y, z) IN mills n *)
(* Proof:
       n MOD 4 = 0
   <=> ?y z. n = windmill (0,y,z)       by windmill_with_no_mind
   <=> ?y z. (0, y, z) IN mills n       by mills_element
*)
Theorem mills_with_no_mind:
  !n. n MOD 4 = 0 <=> ?y z. (0, y, z) IN mills n
Proof
  simp[windmill_with_no_mind, mills_element]
QED

(* Theorem: n MOD 4 <> 0 <=> !x y z. (x, y, z) IN mills n ==> x <> 0 *)
(* Proof: by mills_with_no_mind *)
Theorem mills_with_all_mind:
  !n. n MOD 4 <> 0 <=> !x y z. (x, y, z) IN mills n ==> x <> 0
Proof
  metis_tac[mills_with_no_mind]
QED

(* Theorem: n MOD 4 <> 0 <=> !x y z. (x,y,z) IN mills n ==> 0 < x *)
(* Proof: by mills_with_no_mind. *)
Theorem mills_with_mind:
  !n. n MOD 4 <> 0 <=> !x y z. (x,y,z) IN mills n ==> 0 < x
Proof
  metis_tac[mills_with_no_mind, NOT_ZERO]
QED

(* Theorem: square n <=> ?x y. (x, y, 0) IN mills n \/ (x, 0, y) IN mills n *)
(* Proof:
       square n
   <=> ?x y. n = windmill (x,y,0) \/ n = windmill (x,0,y)
                                        by windmill_with_no_arms
   <=> ?x y. (x,y,0) IN mills n \/ (x,0,y) IN mills n
                                        by mills_element
*)
Theorem mills_with_no_arms:
  !n. square n <=> ?x y. (x, y, 0) IN mills n \/ (x, 0, y) IN mills n
Proof
  simp[windmill_with_no_arms, mills_element]
QED

(* Theorem: ~square n <=> !x y z. (x, y, z) IN mills n ==> y <> 0 /\ z <> 0 *)
(* Proof: by mills_with_no_arms *)
Theorem mills_with_all_arms:
  !n. ~square n <=> !x y z. (x, y, z) IN mills n ==> y <> 0 /\ z <> 0
Proof
  metis_tac[mills_with_no_arms]
QED

(* Theorem: ~square n <=> !x y z. (x,y,z) IN mills n ==> 0 < y /\ 0 < z *)
(* Proof: by mills_with_no_arms. *)
Theorem mills_with_arms:
  !n. ~square n <=> !x y z. (x,y,z) IN mills n ==> 0 < y /\ 0 < z
Proof
  metis_tac[mills_with_no_arms, NOT_ZERO]
QED

(* Theorem: n MOD 4 <> 0 /\ ~square n <=> !x y z. (x,y,z) IN mills n ==> 0 < x /\ 0 < y /\ 0 < z *)
(* Proof: by mills_with_mind, mills_with_arms. *)
Theorem mills_with_mind_and_arms:
  !n. n MOD 4 <> 0 /\ ~square n <=> !x y z. (x,y,z) IN mills n ==> 0 < x /\ 0 < y /\ 0 < z
Proof
  metis_tac[mills_with_mind, mills_with_arms]
QED

(* Theorem: n MOD 4 = 1 ==> mills n <> {} *)
(* Proof:
   By contradiction, suppose (mills n = {}).
   Now ?k. n = k * 4 + 1              by DIVISION
    so     n = 1 ** 2 + 4 * 1 * k     by arithmetic
             = windmill (1, 1, k)     by windmill_def
   Thus (1, 1, k) IN mills n          by mills_def
   This contradicts mills n = {}      by MEMBER_NOT_EMPTY
*)
Theorem mills_non_empty:
  !n. n MOD 4 = 1 ==> mills n <> {}
Proof
  rpt strip_tac >>
  `?k. n = k * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  `_ = windmill (1, 1, k)` by rw[windmill_def] >>
  `(1, 1, k) IN (mills n)` by metis_tac[mills_element] >>
  metis_tac[MEMBER_NOT_EMPTY]
QED

(* Theorem: n MOD 4 <> 0 /\ ~square n ==>
            !x y z. (x,y,z) IN (mills n) ==> x <> 0 /\ y <> 0 /\ z <> 0 *)
(* Proof:
   Note n = windmill (x, y, z)        by mills_def
          = x ** 2 + 4 * y * z        by windmill_def
   By contradiction, suppose x = 0, or y = 0, or z = 0.
   If x = 0, then n MOD 4 = 0         by MOD_EQ_0
             which contradicts n MOD 4 <> 0.
   If y = 0 or z = 0, then n = x ** 2
             which contradicts ~square n
                                      by square_def, EXP_2
*)
Theorem mills_triple_nonzero:
  !n. n MOD 4 <> 0 /\ ~square n ==>
      !x y z. (x,y,z) IN (mills n) ==> x <> 0 /\ y <> 0 /\ z <> 0
Proof
  spose_not_then strip_assume_tac >>
  rfs[square_def, mills_def, windmill_def] >>
  `y <> 0 /\ z <> 0` by metis_tac[MULT_EQ_0, ADD] >>
  `x <> 0` by metis_tac[SQ_0, ADD_0, MULT_COMM, MOD_EQ_0, DECIDE``0 < 4``] >>
  decide_tac
QED

(* Theorem: prime p /\ (x,y,z) IN (mills p) ==> x <> 0 /\ y <> 0 /\ z <> 0 *)
(* Proof:
   Note ~square p                    by prime_non_square
    and p MOD 4 <> 0                 by prime_mod_eq_0, NOT_PRIME_4
     so (x,y,z) IN (mills p)
    ==> x <> 0 /\ y <> 0 /\ z <> 0   by mills_triple_nonzero
*)
Theorem mills_prime_triple_nonzero:
  !p x y z. prime p /\ (x,y,z) IN (mills p) ==> x <> 0 /\ y <> 0 /\ z <> 0
Proof
  ntac 5 strip_tac >>
  `~square p` by metis_tac[prime_non_square] >>
  `p MOD 4 <> 0` by metis_tac[prime_mod_eq_0, NOT_PRIME_4, DECIDE``1 < 4``] >>
  metis_tac[mills_triple_nonzero]
QED

(* ------------------------------------------------------------------------- *)
(* Flip involution.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define the flip function for last two elements of a triple. *)
Definition flip_def:
   flip (x:num, y:num, z:num) = (x, z, y)
End

(* Theorem: flip (x,y,z) = (x,y,z) <=> y = z *)
(* Proof:
       flip (x,y,z) = (x,y,z)
   <=>      (x,z,y) = (x,y,z)  by flip_def
   <=> x = x, z = y, y = z.
*)
Theorem flip_fix:
  !x y z. flip (x,y,z) = (x,y,z) <=> y = z
Proof
  simp[flip_def]
QED

(* Theorem: fixes flip (mills n) = {(x,y,y) | n = windmill (x,y,y)} *)
(* Proof:
     fixes flip (mills n)
   = {t | t IN (mills n) /\ flip t = t}        by fixes_def
   = {(x,y,z) | (x,y,z) IN (mills n) /\ flip (x,y,z) = (x,y,z)}    by triple_parts
   = {(x,y,z) | (x,y,z) IN (mills n) /\ y = z} by flip_fix
   = {(x,y,y) | (x,y,y) IN (mills n)}          by simplification
   = {(x,y,y) | n = windmill (x,y,y)}          by mills_def
*)
Theorem flip_fixes:
  !n. fixes flip (mills n) = {(x,y,y) | n = windmill (x,y,y)}
Proof
  rw[fixes_def, mills_def, EXTENSION] >>
  metis_tac[flip_fix]
QED

(* Theorem: (x,y,z) IN fixes flip (mills n) <=> (n = windmill (x,y,z) /\ y = z) *)
(* Proof: by flip_fixes. *)
Theorem flip_fixes_element:
  !n x y z. (x,y,z) IN fixes flip (mills n) <=> (n = windmill (x,y,z) /\ y = z)
Proof
  simp[flip_fixes] >>
  metis_tac[]
QED

(* Extract Theorem *)
Theorem flip_fixes_alt = fixes_element |> ISPEC ``flip``;
(* val flip_fixes_alt = |- !s x. x IN fixes flip s <=> x IN s /\ flip x = x: thm *)

(* Theorem: windmill t = windmill (flip t) *)
(* Proof:
   Let (x,y,z) = t             by FORALL_PROD
     windmill (flip t)
   = windmill (flip (x,y,z))   by notation
   = windmill (x,z,y)          by flip_def
   = x ** 2 + 4 * z * y        by windmill_def
   = x ** 2 + 4 * y * z        by MULT_COMM
   = windmill (x,y,z)          by windmill_def
   = windmill t                by notation
*)
Theorem flip_windmill:
  !t. windmill t = windmill (flip t)
Proof
  simp[flip_def, windmill_def, FORALL_PROD]
QED

(* Theorem: t IN mills n ==> flip t IN mills n *)
(* Proof:
   Let (x,y,z) = t             by FORALL_PROD
       t IN mills n
   <=> (x,y,z) IN mills n      by notation
   ==> (x,z,y) IN mills n      by mills_element_flip
   <=> flip (x,y,z) IN mills n by flip_def
   <=> flip t IN mills n       by notation
*)
Theorem flip_closure:
  !n t. t IN mills n ==> flip t IN mills n
Proof
  simp[flip_def, mills_element_flip, FORALL_PROD]
QED

(* Theorem: t IN mills n <=> flip t IN mills n *)
(* Proof:
       t IN mills n
   <=> n = windmill t              by mills_element_alt
   <=> n = windmill (flip t)       by flip_windmill
   <=> flip t IN mills n           by mills_element_alt
*)
Theorem flip_closure_iff:
  !n t. t IN mills n <=> flip t IN mills n
Proof
  simp[mills_element_alt, GSYM flip_windmill]
QED

(* Theorem: flip (flip t) = t *)
(* Proof:
   Let (x,y,z) = t             by FORALL_PROD
     flip (flip t)
   = flip (flip (x,y,z))       by notation
   = flip (x,z,y)              by flip_def
   = (x,y,z)                   by flip_def
*)
Theorem flip_involute:
  !t. flip (flip t) = t
Proof
  simp[flip_def, FORALL_PROD]
QED

(* Theorem: flip involute (mills n) *)
(* Proof:
   Note flip t IN mills n          by flip_closure
    and flip (flip t) = t          by flip_involute
     so flip involute (mills n)    by involution
*)
Theorem flip_involute_mills:
  !n. flip involute (mills n)
Proof
  simp[flip_closure, flip_involute]
QED

(* flip_involute_mills |> SPEC ``n:num``;
val it = |- flip involute mills n: thm
*)

(* ------------------------------------------------------------------------- *)
(* Zagier's involution.                                                      *)
(*                                                                           *)
(* A One-Sentence Proof That                                                 *)
(* Every Prime p = 1 (mod 4) Is a Sum of Two Squares (Don Zagier)            *)
(* http://igor-kortchemski.perso.math.cnrs.fr/mathclub/Zagier.pdf            *)
(* The American Mathematical Monthly, Vol. 97, No. 2 (Feb., 1990), p. 144    *)
(* ------------------------------------------------------------------------- *)

(* Define the Zagier's involution: a self-inverse bijection *)
Definition zagier_def:
    zagier (x, y, z) =
    if x < y - z then (x + 2 * z, z, y - z - x)
    else if x < 2 * y then (2 * y - x, y, x + z - y) (* 2 * y - x = y + y - x *)
    else (x - 2 * y, x + z - y, y) (* here y - z <= x /\ y <= x *)
End
(*
At the two boundaries:
x = y - z, windmill (x, y, z) = (y - z) ** 2 + 4 * y * z = (y + z) ** 2, not a windmill.
x = 2 * y, windmill (x, y, z) = (2 * y) ** 2 + 4 * y * z = 4 * y * (y + z), not for a prime.
*)


(*
For p = 41 = 4 * 10 + 1, k = 10.

EVAL ``zagier (3,8,1)``;  -> (5,1,4)  -> (3,8,1)
EVAL ``zagier (3,4,2)``;  -> (5,4,1)  -> (3,4,2)
EVAL ``zagier (1,10,1)``; -> (3,1,8)  -> (1,10,1)
EVAL ``zagier (1,5,2)``;  -> (5,2,2)  -> (1,5,2)
EVAL ``zagier (1,2,5)``;  -> (3,2,4)  -> (1,2,5)
EVAL ``zagier (1,1,10)``; -> (1,1,10) -> (1,1,10)

EVAL ``MAP zagier [(3,8,1);(3,4,2);(1,10,1);(1,5,2);(1,2,5);(1,1,10)]``;
-> [(5,1,4); (5,4,1); (3,1,8); (5,2,2); (3,2,4); (1,1,10)]: thm
EVAL ``MAP zagier [(5,1,4);(5,4,1);(3,1,8);(5,2,2);(3,2,4);(1,1,10)]``;
-> [(3,8,1); (3,4,2); (1,10,1); (1,5,2); (1,2,5); (1,1,10)]: thm
*)


(* Theorem: x <> 0 ==> (zagier (x,y,z) = (x,y,z) <=> x = y) *)
(* Proof:
   By zagier_def,
   If x < y - z, then 0 < y by x <> 0.
          (x + 2 * z,z,y - z - x) = (x, y, z)
      <=>  x + 2 * z = x, z = y, y - z - x = z
      <=>  x + 2 * y = x, z = y, 0 - x = y
      <=>  x + 2 * y = x, z = y, y = 0
      This contradicts 0 < y.
   Next, if x < 2 * y,
          (2 * y - x,y,x + z - y) = (x, y, z)
      <=>  2 * y - x = x, y = y, x + z - y = z
      <=>  2 * y - x = x, y = y, x - y = 0
      <=> x = y
   Otherwise,
          (x - 2 * y,x + z - y,y) = (x, y, z)
      <=> x - 2 * y = x, x + z - y = y, y = z
      <=> x - 2 * y = x, x = y, y = z
      <=> x - 2 * x = x, x = y, y = z
      <=> x = 0, y = 0, z = 0
      This contradicts x <> 0.
*)
Theorem zagier_fix:
  !x y z. x <> 0 ==> (zagier (x,y,z) = (x,y,z) <=> x = y)
Proof
  rw[zagier_def]
QED

(* Theorem: n MOD 4 <> 0 ==> fixes zagier (mills n) = {(x,x,z) | n = windmill (x,x,z)} *)
(* Proof:
   Note !x y z. !x y z. (x,y,z) IN mills n ==> x <> 0
                                               by mills_with_all_mind
     fixes zagier (mills n)
   = {t | t IN (mills n) /\ zagier t = t}      by fixes_def
   = {(x,y,z) | (x,y,z) IN (mills n) /\ zagier (x,y,z) = (x,y,z)}    by triple_parts
   = {(x,y,z) | (x,y,z) IN (mills n) /\ x = y} by zagier_fix, x <> 0
   = {(x,y,y) | (x,y,y) IN (mills n)}          by simplification
   = {(x,y,y) | n = windmill (x,y,y)}          by mills_def
*)
Theorem zagier_fixes:
  !n. n MOD 4 <> 0 ==> fixes zagier (mills n) = {(x,x,z) | n = windmill (x,x,z)}
Proof
  rw[fixes_def, mills_def, EXTENSION, EQ_IMP_THM] >| [
    rename1 `windmill (x,y,z)` >>
    `x <> 0` by metis_tac[windmill_with_no_mind] >>
    fs[zagier_fix, windmill_def],
    rename1 `windmill (x,x,z)` >>
    `x <> 0` by metis_tac[windmill_with_no_mind] >>
    simp[zagier_fix]
  ]
QED

(* Theorem: n MOD 4 <> 0 ==> ((x,y,z) IN fixes zagier (mills n) <=> n = windmill (x,y,z) /\ x = y) *)
(* Proof: by zagier_fixes. *)
Theorem zagier_fixes_element:
  !n x y z. n MOD 4 <> 0 ==> ((x,y,z) IN fixes zagier (mills n) <=> n = windmill (x,y,z) /\ x = y)
Proof
  rpt strip_tac >>
  imp_res_tac zagier_fixes >>
  fs[EXTENSION] >>
  metis_tac[]
QED

(* Extract Theorem *)
Theorem zagier_fixes_alt = fixes_element |> ISPEC ``zagier``;
(* val zagier_fixes_alt = |- !s x. x IN fixes zagier s <=> x IN s /\ zagier x = x: thm *)

(* Theorem: windmill t = windmill (zagier t) *)
(* Proof:
   Let (x,y,z) = t             by FORALL_PROD
   By windmill_def, zagier_def, this is to show:
   (1) x < y - z ==>
       4 * (y * z) + x ** 2 = 4 * (z * (y - (x + z))) + (x + 2 * z) ** 2
       or windmill (x, y, z) = windmill (x + 2 * z) z (y - (x + z))
       From      x < y - z
         so  x + z < y               by LESS_SUB_ADD_LESS, or in detail:
       Note x < 0 is impossible, so ~(y <= z), or z < y, implies z <= y.
         so  x + z < y - z + z = y   by SUB_ADD, z <= y
       Thus  x + z <= y              by x + z < y

         windmill (x + 2 * z, z ,y - (x + z))
       = (x + 2 * z) ** 2 + 4 * z * (y - (x + z))
       = x ** 2 + (2 * z) ** 2 + 4 * x * z + 4 * z * (y - (x + z))   by SUM_SQUARED
       = x ** 2 + 4 * z * z + 4 * z * x + 4 * z (y - (x + z))        by EXP_2
       = x ** 2 + 4 * z * (x + z) + 4 * z (y - (x + z)) by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * z * ((x + z) + (y - (x + z)))     by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * z * ((x + z) + y - (x + z))       by LESS_EQ_ADD_SUB, x + z <= y
       = x ** 2 + 4 * z * (y + (x + z) - (x + z))
       = x ** 2 + 4 * z * y                             by ADD_SUB
       = x ** 2 + 4 * y * z
       = windmill (x, y, z)

   (2) ~(x < y - z) /\ x < 2 * y ==>
        4 * (y * z) + x ** 2 = 4 * (y * (x + z - y)) + (2 * y - x) ** 2
       or windmill (x, y, z) = windmill (2 * y - x) y (x + z - y)
       Note y - z <= x             by ~(x < y - z)
         so y <= x + z             by SUB_RIGHT_LESS_EQ

         windmill (2 * y - x, y, x + z - y)
       = (2 * y - x) ** 2 + 4 * y * (x + z - y)
       = (2 * y - x) ** 2 + 8 * y * x - 8 * y * x + 4 * y * (x + z - y)  by ADD_SUB
       = (2 * y - x) ** 2 + 8 * y * x + 4 * y * (x + z - y) - 8 * y * x  by SUB_RIGHT_ADD,
                        since 8 * y * x <= (2 * y - x) ** 2 + 8 * y * x
       = (2 * y + x) ** 2 + 4 * y * (x + z - y) - 8 * y * x   by binomial_sub_add, x < 2 * y
       = (2 * y) ** 2 + x ** 2 + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x
                                                              by SUM_SQUARED
       = x ** 2 + 4 * y * y + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x
                                                              by EXP_2
       = x ** 2 + 4 * y * (y + x) + 4 * y * (x + z - y) - 8 * y * x
                                                              by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * y * (y + x + (x + z - y)) - 8 * y * x   by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * y * (y + x + x + z - y) - 8 * y * x     by LESS_EQ_ADD_SUB, y <= x + z
       = x ** 2 + 4 * y * (2 * x + z) - 4 * y * (2 * x)       by arithmetic
       = x ** 2 + 4 * y * (2 * x + z - 2 * x)                 by LEFT_SUB_DISTRIB
       = x ** 2 + 4 * y * z                                   by ADD_SUB
       = windmill (x, y, z)

   (3) ~(x < y - z) /\ ~(x < 2 * y) ==>
       4 * (y * z) + x ** 2 = 4 * (y * (x + z - y)) + (x - 2 * y) ** 2
       or windmill (x, y, z) = windmill (x - 2 * y) y (x + z - y)
       Note y - z <= x             by ~(x < y - z)
         so y <= x + z             by SUB_RIGHT_LESS_EQ
       Also 2 * y <= x             by ~(x < 2 * y)

         windmill (x - 2 * y, y, x + z - y)
       = (x - 2 * y) ** 2 + 4 * y * (x + z - y)
       = (x - 2 * y) ** 2 + 8 * y * x - 8 * y * x + 4 * y * (x + z - y)  by ADD_SUB
       = (x - 2 * y) ** 2 + 8 * y * x + 4 * y * (x + z - y) - 8 * y * x  by SUB_RIGHT_ADD,
                        since 8 * y * x <= (2 * y - x) ** 2 + 8 * y * x
       = (x + 2 * y) ** 2 + 4 * y * (x + z - y) - 8 * y * x   by binomial_sub_add, 2 * y <= x
       = x ** 2 + (2 * y) ** 2 + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x
                                                              by SUM_SQUARED
       = x ** 2 + 4 * y * y + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x
                                                              by EXP_2
       = x ** 2 + 4 * y * (y + x) + 4 * y * (x + z - y) - 8 * y * x
                                                              by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * y * (y + x + (x + z - y)) - 8 * y * x   by LEFT_ADD_DISTRIB
       = x ** 2 + 4 * y * (y + x + x + z - y) - 8 * y * x     by LESS_EQ_ADD_SUB, y <= x + z
       = x ** 2 + 4 * y * (2 * x + z) - 4 * y * (2 * x)       by arithmetic
       = x ** 2 + 4 * y * (2 * x + z - 2 * x)                 by LEFT_SUB_DISTRIB
       = x ** 2 + 4 * y * z                                   by ADD_SUB
       = windmill (x, y, z)
*)
Theorem zagier_windmill:
  !t. windmill t = windmill (zagier t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill(x,y,z)` >>
  rw[windmill_def, zagier_def] >| [
    `x + z < y` by decide_tac >>
    `(x + 2 * z) ** 2 + 4 * (z * (y - (x + z))) =
    x ** 2 + (2 * z) ** 2 + 4 * x * z + 4 * z * (y - (x + z))` by simp[SUM_SQUARED] >>
    `_ = x ** 2 + (2 * z) ** 2 + 4 * z * x + 4 * z * (y - (x + z))` by decide_tac >>
    `_ = x ** 2 + (2 * z) * (2 * z) + 4 * z * x + 4 * z * (y - (x + z))` by metis_tac[EXP_2] >>
    `_ = x ** 2 + 4 * z * z + 4 * z * x + 4 * z * (y - (x + z))` by decide_tac >>
    `_ = x ** 2 + 4 * z * (z + x) + 4 * z * (y - (x + z))` by decide_tac >>
    `_ = x ** 2 + 4 * z * ((x + z) + (y - (x + z)))` by rw[LEFT_ADD_DISTRIB] >>
    `_ = x ** 2 + 4 * z * ((x + z) + y - (x + z))` by rw[] >>
    `_ = x ** 2 + 4 * z * y` by decide_tac >>
    simp[],
    `y <= x + z` by decide_tac >>
    `(2 * y - x) ** 2 + 4 * (y * (x + z - y)) =
    (2 * y - x) ** 2 + 4 * y * (x + z - y)` by decide_tac >>
    `_ = (2 * y - x) ** 2 + 8 * y * x - 8 * y * x + 4 * y * (x + z - y)` by decide_tac >>
    `_ = (2 * y - x) ** 2 + 4 * (2 * y) * x + 4 * y * (x + z - y) - 8 * y * x` by fs[] >>
    `_ = (2 * y + x) ** 2 + 4 * y * (x + z - y) - 8 * y * x` by simp[binomial_sub_add] >>
    `_ = (2 * y) ** 2 + x ** 2 + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by simp[SUM_SQUARED] >>
    `_ = (2 * y) * (2 * y) + x ** 2 + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by metis_tac[EXP_2] >>
    `_ = x ** 2 + 4 * y * y + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by fs[] >>
    `_ = x ** 2 + 4 * y * (y + x) + 4 * y * (x + z - y) - 8 * y * x` by rw[LEFT_ADD_DISTRIB] >>
    `_ = x ** 2 + 4 * y * (y + x + (x + z - y)) - 8 * y * x` by rw[LEFT_ADD_DISTRIB] >>
    `_ = x ** 2 + 4 * y * (y + x + x + z - y) - 8 * y * x` by rw[LESS_EQ_ADD_SUB] >>
    `_ = x ** 2 + 4 * y * (x + x + z) - 4 * y * (x + x)` by decide_tac >>
    `_ = x ** 2 + 4 * y * (x + x + z - (x + x))` by decide_tac >>
    `_ = x ** 2 + 4 * y * z` by decide_tac >>
    simp[],
    `y <= x + z` by decide_tac >>
    `2 * y <= x` by decide_tac >>
    `(x - 2 * y) ** 2 + 4 * (y * (x + z - y)) =
    (x - 2 * y) ** 2 + 4 * y * (x + z - y)` by decide_tac >>
    `_ = (x - 2 * y) ** 2 + 8 * y * x - 8 * y * x + 4 * y * (x + z - y)` by decide_tac >>
    `_ = (x - 2 * y) ** 2 + 4 * x * (2 * y) + 4 * y * (x + z - y) - 8 * y * x` by fs[] >>
    `_ = (x + 2 * y) ** 2 + 4 * y * (x + z - y) - 8 * y * x` by simp[binomial_sub_add] >>
    `_ = x ** 2 + (2 * y) ** 2 + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by simp[SUM_SQUARED] >>
    `_ = x ** 2 + (2 * y) * (2 * y) + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by metis_tac[EXP_2] >>
    `_ = x ** 2 + 4 * y * y + 4 * y * x + 4 * y * (x + z - y) - 8 * y * x` by fs[] >>
    `_ = x ** 2 + 4 * y * (y + x) + 4 * y * (x + z - y) - 8 * y * x` by rw[LEFT_ADD_DISTRIB] >>
    `_ = x ** 2 + 4 * y * (y + x + (x + z - y)) - 8 * y * x` by rw[LEFT_ADD_DISTRIB] >>
    `_ = x ** 2 + 4 * y * (y + x + x + z - y) - 8 * y * x` by rw[LESS_EQ_ADD_SUB] >>
    `_ = x ** 2 + 4 * y * (x + x + z) - 4 * y * (x + x)` by decide_tac >>
    `_ = x ** 2 + 4 * y * (x + x + z - (x + x))` by decide_tac >>
    `_ = x ** 2 + 4 * y * z` by decide_tac >>
    simp[]
  ]
QED

(* Theorem: t IN mills n ==> zagier t IN mills n *)
(* Proof:
       t IN mills n
   <=> n = windmill t              by mills_element_alt
   ==> n = windmill (zagier t)     by zagier_windmill
   <=> zagier t IN mills n         by mills_element_alt
*)
Theorem zagier_closure:
  !n t. t IN mills n ==> zagier t IN mills n
Proof
  simp[mills_element_alt, GSYM zagier_windmill]
QED

(* Theorem: t IN mills n <=> zagier t IN mills n *)
(* Proof:
       t IN mills n
   <=> n = windmill t              by mills_element_alt
   <=> n = windmill (zagier t)     by zagier_windmill
   <=> zagier t IN mills n         by mills_element_alt
*)
Theorem zagier_closure_iff:
  !n t. t IN mills n <=> zagier t IN mills n
Proof
  simp[mills_element_alt, GSYM zagier_windmill]
QED

(* Theorem: zagier (0, y, z) =
            if z < y then (2 * z,z,y - z)
            else if 0 < y then (2 * y,y,z - y) else (0,z,0) *)
(* Proof:
   If x = 0, for 0 < y - z, need z < y.
   In this case, 0 < y, so 0 < 2 * y.
   Otherwise, y <= z. If ~(0 < y), then y = 0
     zagier (0, y, z)
   = if z < y then (2 * z,z,y - z)
     else if 0 < y then (2 * y,y,z - y)
     else (0,z,0)
*)
Theorem zagier_0_y_z:
  !y z. zagier (0, y, z) =
        if z < y then (2 * z,z,y - z)
        else if 0 < y then (2 * y,y,z - y)
        else (0,z,0)
Proof
  rw[zagier_def]
QED

(* Theorem: zagier (x, 0, z) = (x, x + z, 0) *)
(* Proof:
   If y = 0, y - z = 0, so x < y - z <=> F.
   Also x < 2 * y <=> F. Thus this is the third case:
     zagier (x, 0, z)
   = (x - 2 * 0,x + z - 0,0)
   = (x, x + z, 0)
*)
Theorem zagier_x_0_z:
  !x z. zagier (x, 0, z) = (x, x + z, 0)
Proof
  simp[zagier_def]
QED

(* Theorem: zagier (x, y, 0) =
            if x < y then (x, 0, y - x)
            else if x < 2 * y then (2 * y - x, y, x - y)
            else (x - 2 * y, x - y, y) *)
(* Proof:
   If z = 0, y - z = y, so x < y - z <=> x < y.
     zagier (x, y, 0)
   = if x < y then (x + 2 * 0,0,y - 0 - x)
     if x < 2 * y then (2 * y - x,y,x + 0 - y)
                  else (x - 2 * y,x + 0 - y,y)
   = if x < y then (x, 0, y - x)
     else if x < 2 * y then (2 * y - x, y, x - y)
     else (x - 2 * y, x - y, y)
*)
Theorem zagier_x_y_0:
  !x y. zagier (x, y, 0) =
        if x < y then (x, 0, y - x)
        else if x < 2 * y then (2 * y - x, y, x - y)
        else (x - 2 * y, x - y, y)
Proof
  simp[zagier_def]
QED

(* Theorem: zagier (1, 1, z) = (1, 1, z) *)
(* Proof:
   If x = 1 and y = 1, then x < y - z <=> F, but x < 2 * y <=> T.
     zagier (1, 1, z)
   = (2 * 1 - 1,1,1 + z - 1)
   = (1,1,z)
*)
Theorem zagier_1_1_z:
  !z. zagier (1, 1, z) = (1, 1, z)
Proof
  simp[zagier_def]
QED

(* Theorem: zagier (1, y, 1) =
            if y = 0 then (1, 2, 0)
            else if y = 1 then (1, 1, 1)
            else if y = 2 then (3, 2, 0)
            else (3, 1, y - 2) *)
(* Proof:
   If x = 1 and z = 1, then x < y - z <=> 2 < y,
   and zagier (1, y, 1) = (1 + 2 * 1,1,y - 1 - 1) = (3, 1, y - 2)
   Otherwise, y <= 2, so y = 0, 1, 2.
   For x < 2 * y <=> 1 < 2 * y, y = 1 or 2
   and zagier (1, y, 1) = (2 * y - 1,y,1 + 1 - y) = (2 * y - 1, y, 2 - y)
   when y = 1, zagier (1, 1, 1) = (1, 1, 1)
   when y = 2, zagier (1, 2, 1) = (3, 2, 0)
   Otherwise y = 0, zagier (1, 0, 1) = (1 - 2 * 0,1 + 1 - 0,0) = (1, 2, 0)
*)
Theorem zagier_1_y_1:
  !y. zagier (1, y, 1) =
         if y = 0 then (1, 2, 0)
         else if y = 1 then (1, 1, 1)
         else if y = 2 then (3, 2, 0)
         else (3, 1, y - 2)
Proof
  rw[zagier_def]
QED

(* Theorem: zagier (x,0,0) = (x,x,0) *)
(* Proof:
   If y = 0 and z = 0, x < y - z becomes x < 0, which is false.
   Next x < 2 * y becomes x < 2 * 0 = 0 is false, too.
   Thus zagier (x,0,0) = (x - 2 * y,x + z - y,y) = (x,x,0).
*)
Theorem zagier_x_0_0:
  !x. zagier (x,0,0) = (x,x,0)
Proof
  simp[zagier_def]
QED

(* Theorem: zagier (0,y,0) = (0,0,y) *)
(* Proof:
   If x = 0 and z = 0, x < y - z becomes 0 < y.
   If 0 < y,
      then zagier (0,y,0) = (x + 2 * z,z,y - z - x) = (0,0,y)
   Otherwise y = 0, and x < 2 * y becomes 0 < 2 * 0 = 0 is false.
   Thus zagier (0,0,0) = (x - 2 * y,x + z - y,y) = (0,0,0).
*)
Theorem zagier_0_y_0:
  !y. zagier (0,y,0) = (0,0,y)
Proof
  rw[zagier_def]
QED

(* Theorem: zagier (0,0,z) = (0,z,0) *)
(* Proof:
   If x = 0 and y = 0, x < y - z becomes 0 < 0 - z = 0 is false.
   Next x < 2 * y becomes 0 < 2 * 0 = 0 is false, too.
   Thus zagier (0,0,z) = (x - 2 * y,x + z - y,y) = (0,z,0).
*)
Theorem zagier_0_0_z:
  !z. zagier (0,0,z) = (0,z,0)
Proof
  simp[zagier_def]
QED

(*
> zagier_0_y_z |> SPEC ``1`` |> SIMP_RULE std_ss[DECIDE``n < 1 <=> n = 0``];
val it = |- !z. zagier (0,1,z) = if z = 0 then (0,0,1) else (2,1,z - 1): thm
*)

(* Theorem: zagier (0,1,z) = (0,z,0) *)
(* Proof:
   If x = 0 and y = 1, x < y - z becomes 0 < 1 - z, true when z = 0, giving (0,0,1).
   Next x < 2 * y becomes 0 < 2 * 1 = 2, which is true.
   Thus zagier (0,1,z) = (2 * y - x,y,x + z - y) = (2,1,z - 1).
*)
Theorem zagier_0_1_z:
  !z. zagier (0,1,z) = if z = 0 then (0,0,1) else (2,1,z - 1)
Proof
  rw[zagier_def]
QED

(* Theorem: zagier (0,0,0) = (0,0,0) *)
(* Proof: by zagier_x_0_0, or zagier_0_0_z or zagier_0_y_0 *)
Theorem zagier_0_0_0:
  zagier (0,0,0) = (0,0,0)
Proof
  simp[zagier_def]
QED

(* Theorem: zagier (x, y, y) =
         if x < 2 * y then (2 * y - x,y,x) else (x - 2 * y,x,y) *)
(* Proof: by zagier_def, x < y - y = 0 is false. *)
Theorem zagier_x_y_y:
  !x y. zagier (x, y, y) =
        if x < 2 * y then (2 * y - x,y,x) else (x - 2 * y,x,y)
Proof
  rw[zagier_def]
QED

(* Theorem: x <> 0 ==> zagier (x, x, z) = (x, x, z) *)
(* Proof: by zagier_fix. *)
Theorem zagier_x_x_z:
  !x z. x <> 0 ==> zagier (x, x, z) = (x, x, z)
Proof
  simp[zagier_fix]
QED


(* Theorem: x <> 0 /\ z <> 0 ==> zagier (zagier (x, y, z)) = (x, y, z) *)
(* Proof:
   Put the 3 branches of zagier_def into 5 cases for a triple (x,y,z):
   Case 1: x < y and x < y - z      for branch 1
   Case 2: x < y and y - z < x      for branch 2
   Case 3: x = y                    for branch 2
   Case 4: y < x and x < 2 * y      for branch 2
   Case 5: y < x and 2 * y < x      for branch 3

   Note x <> 0 /\ y <> 0 /\ z <> 0 implies proper windmills.
   Boundary cases correspond to improper windmills, hence not considered:
   For x < y, x = y - z gives
       n = (y - z) ** 2 + 4 * y * z = (y + z) ** 2, a windmill without arms.
   For y < x, x = 2 * y gives
       n = (2 * y) ** 2 + 4 * y * z = 4 * y * (y + z), a windmill with only four arms.

   By zagier_def,
   If x < y - z,
      then (x,y,z) will be in case 1.
      zagier (x,y,z) = (x + 2 * z,z,y - z - x) = (x',y',z')   by first branch
      so x' = x + 2 * z = z + x + z, expand inner square,
         y' = z,
         z' = y - z - x, excess to fit the mind.
      Thus 2 * y' = 2 * z < x + 2 * z = x' for x <> 0,
      which is case 5, so
        zagier (x',y',z')
      = (x' - 2 * y',x' + z' - y',y')     by third branch
      = (x + 2 * z - 2 * z, x + 2 * z + (y - z - x) - z, z)
      = (x, y, z)

   If ~(x < y - z), but x < 2 * y,
      then (x,y,z) will be in case 2 or case 3 or case 4.
      zagier (x,y,z) = (2 * y - x,y,x + z - y) = (x',y',z')   by second branch
      so x' = 2 * y - x,
         y' = y,
         z' = x + z - y.

      If x < y, this is case 2.
         x' = 2 * y - x = x + 2 * (y - x), expand inner square,
         y' = y,
         z' = x + z - y, excess to fit the mind.
      Thus x' = 2 * y - x < 2 * y = 2 * y' for x <> 0,
      which is case 4, so
        zagier (x',y',z')
      = (2 * y' - x',y',x' + z' - y')     by second branch
      = (2 * y - (2 * y - x),y,(2 * y - x) + (x + z - y) - y)
      = (x, y, z)

      If x = y, this is case 3.
         x' = 2 * y - x = 2 * y - y = x, no change to inner square,
         y' = y,
         z' = x + z - y = y + z - y = z, no excess, fit the mind.
      Thus x' = y', which is case 3, so
        zagier (x',y',z')
      = (2 * y' - x',y',x' + z' - y')     by second branch
      = (2 * y - (2 * y - x),y,(2 * y - x) + (x + z - y) - y)
      = (x, y, z)

      If y < x, this is case 4.
         x' = 2 * y - x = x - 2 * (x - y), shrink inner square,
         y' = y,
         z' = x + z - y = z + (x - y), excess to fit the mind.
      Thus y' - z' = y - (x + z - y) < 2 * y - x = x' for z <> 0,
      which is case 2, so
        zagier (x',y',z')
      = (2 * y' - x',y',x' + z' - y')     by second branch
      = (2 * y - (2 * y - x),y,(2 * y - x) + (x + z - y) - y)
      = (x, y, z)

   If ~(x < y - z), and ~(x < 2 * y),
      then (x,y,z) will be in case 5.
      zagier (x,y,z) = (x - 2 * y,x + z - y,y) = (x',y',z')   by third branch
      so x' = x - 2 * y, shrink inner square
         y' = x + z - y,
         z' = y.
      Thus x' = x - 2 * y < (x + z - y) - y = y' - z' for z <> 0,
      which is case 1, so
        zagier (x',y',z')
      = (x' + 2 * z',z',y' - z' - x')    by first branch
      = (x - 2 * y + 2 * y, y, (x + z - y) - y - (x - 2 * y))
      = (x, y, z)
  If y = 0, then
        zagier (zagier (x, 0, z))
      = zagier (x, x + z, 0)             by zagier_x_0_z
      = (x, 0, x + z - x)                by zagier_x_y_0, z <> 0
      = (x, 0, z)                        by arithmetic
*)
Theorem zagier_involute:
  !x y z. x <> 0 /\ z <> 0 ==> zagier (zagier (x, y, z)) = (x, y, z)
Proof
  rw[zagier_def]
QED

(* Theorem: x * z <> 0 ==> zagier (zagier (x, y, z)) = (x, y, z) *)
(* Proof: by MULT_EQ_0, zagier_involute. *)
Theorem zagier_involute_alt0:
  !x y z. x * z <> 0 ==> zagier (zagier (x, y, z)) = (x, y, z)
Proof
  rw[zagier_involute]
QED

(* Theorem: FST t <> 0 /\ SND (SND t) <> 0 ==> zagier (zagier t) = t *)
(* Proof: by zagier_involute *)
Theorem zagier_involute_thm:
  !t. FST t <> 0 /\ SND (SND t) <> 0 ==> zagier (zagier t) = t
Proof
  simp[zagier_involute, FORALL_PROD]
QED

(* Define doublet of a triple *)
Definition doublet_def:
   doublet (x, y, z) = x * z
End

(* Theorem: doublet (x, y, z) = 0 <=> x = 0 \/ z = 0 *)
(* Proof: by doublet_def, MULT_EQ_0 *)
Theorem doublet_eq_0:
  !x y z. doublet (x, y, z) = 0 <=> x = 0 \/ z = 0
Proof
  simp[doublet_def]
QED

(* Theorem: doublet t <> 0 ==> zagier (zagier t) = t *)
(* Proof:
   Let t = (x, y, z).
   Then x <> 0 /\ z <> 0           by doublet_eq_0
   Thus zagier (zagier t) = t      by zagier_involute
*)
Theorem zagier_involute_alt:
  !t. doublet t <> 0 ==> zagier (zagier t) = t
Proof
  metis_tac[triple_parts, doublet_eq_0, zagier_involute]
QED

(* Theorem: n MOD 4 <> 0 /\ ~square n ==> zagier involute (mills n) *)
(* Proof:
   Let t = (x,y,z).                           by triple_parts
   Then zagier (x,y,z) IN mills n             by zagier_closure
   Note !x y z. (x,y,z) IN mills n ==>
                x <> 0 /\ y <> 0 /\ z <> 0    by mills_triple_nonzero
     so zagier (zagier (x,y,z)) = (x,y,z)     by zagier_involute
     so zagier involute (mills n)             by involution
*)
Theorem zagier_involute_mills:
  !n. n MOD 4 <> 0 /\ ~square n ==> zagier involute (mills n)
Proof
  metis_tac[mills_triple_nonzero, zagier_closure, zagier_involute, triple_parts]
QED

(* Theorem: prime p ==> zagier involute (mills p) *)
(* Proof:
   Note ~square p                  by prime_non_square
    and p MOD 4 <> 0               by prime_mod_eq_0, NOT_PRIME_4
   Thus zagier involute (mills p)  by zagier_involute_mills
*)
Theorem zagier_involute_mills_prime:
  !p. prime p ==> zagier involute (mills p)
Proof
  ntac 2 strip_tac >>
  `~square p` by simp[prime_non_square] >>
  `1 < 4` by decide_tac >>
  `p MOD 4 <> 0` by metis_tac[prime_mod_eq_0, NOT_PRIME_4] >>
  metis_tac[zagier_involute_mills]
QED

(* ------------------------------------------------------------------------- *)
(* Part 3: Mind of a windmill                                                *)
(* ------------------------------------------------------------------------- *)

(* The mind of a windmill:

    +----+
    |    |     y
    |    +-------------+
    |    |             |z
    |    +-----+----+--+
    |    |  x  | z  |
    |    |     |    |
 +--+----+-----+    |
 |             |    |
 +-------------+    |
               |    |
               +----+
   Algorithm:
   1. draw the square of side x.
   2. from each square vertex, put the line y alongside, in clockwise manner.
   3. complete the 4 rectangles y * z, around the central square.

   "mind" is the side of central square:
   from the picture above, it is evident that,
   assume y > z, then (y - z) is the slack for inner square x to fit in.
   If x < y - z, the inner square can grow to:
      x' = x + 2 * z, y' = z, z' = y - x - z. (result looks like the third diagram)

          y
      +--------+
 +----|        |z
 |    +-----+--+-+
 |    |  x  | z  |
 |    |     |    |
 +-+--+-----+    |
   |        |----+
   +--------+

   If y < z, assume y > x, the inner square can only grow to:
      x' = x + 2 * (y - x) = 2 * y - x, y' = y, z' = x + z - y.
      this only works with 0 < x' for x < 2 * y.

   Otherwise, y < x, the mind has to shrink:
      x' = x - 2 * (x - y) = 2 * y - x, y' = x + z - y, z' = y.

        y
      +---+
      |   |z
      +---+-+---+
  +---|  x  | z |
  |   |     |---+
  +---+-+---+
        |   |
        +---+

*)
(* Define the mind of a triple, for a windmill. *)
Definition mind_def:
   mind (x,y,z) = if x < y - z then x + 2 * z
                  else if x < y then 2 * y - x
                  else x (* maximal central square *)
End

(* Investigation:

zagier (3,8,2) = (7,2,3)
zagier (3,6,4) = (9,6,1)
zagier (7,3,2) = (1,6,3)

EVAL ``mind (3,8,2)``; = 7
EVAL ``mind (zagier (3,8,2))``; = 7

EVAL ``mind (3,6,4)``; = 9
EVAL ``mind (zagier (3,6,4))``; = 9
EVAL ``mind (9,6,1)``; = 9

EVAL ``mind (7,3,2)``; = 7
EVAL ``mind (zagier (7,3,2))``; = 7

*)


(* Theorem: mind (zagier (x, y, z)) = mind (x, y, z) *)
(* Proof:
   If x < y - z,
      then since 2 * z < z is false,
        so x + 2 * z < z - (y - z - x) is false
       and x + 2 * z < z is also false, so
           mind (zagier (x, y, z))
         = mind (x + 2 * z,z,y - z - x)  by zagier_def
         = x + 2 * z                     by mind_def, third case
         = mind (x, y, z)                by mind_def
    Otherwise, if x < y,
       then x < 2 * y,
           mind (zagier (x, y, z))
         = mind (2 * y - x,y,x + z - y)  by zagier_def
         = 2 * y - x                     by mind_def, third case
         = mind (x, y, z)                by mind_def
    Otherwise, if x < 2 * y,
       then if 2 * y - x < y
           mind (zagier (x, y, z))
         = mind (2 * y - x,y,x + z - y)  by zagier_def
         = 2 * y - (2 * y - x)           by mind_def, second case
         = x
         = mind (x, y, z)                by mind_def
       else ~(2 * y - x < y)
           so y = x,
           mind (zagier (x, y, z))
         = mind (2 * y - x,y,x + z - y)  by zagier_def
         = 2 * y - x                     by mind_def, third case
         = x                             by y = x
         = mind (x, y, z)                by mind_def
    Otherwise,
       then if x - 2 * y < (x + z - y) - y
           mind (zagier (x, y, z))
         = mind (x - 2 * y,x + z - y,y)  by zagier_def
         = (x - 2 * y) + 2 * y           by mind_def, first case
         = x
         = mind (x, y, z)                by mind_def
       else if x - 2 * y < x + z - y
           so z = 0,                     by arithmetic
           mind (zagier (x, y, z))
         = mind (x - 2 * y,x + z - y,y)  by zagier_def
         = 2 * (x + z - y) - (x - 2 * y) by mind_def, second case
         = 2 * x + 2 * z - x             by arithmetic
         = x                             by z = 0
         = mind (x, y, z)                by mind_def
       else ~(x - 2 * y < x + z - y)
           so y = 0,                     by arithmetic
           mind (zagier (x, y, z))
         = mind (x - 2 * y,x + z - y,y)  by zagier_def
         = x - 2 * y                     by mind_def, third case
         = x                             by y = 0
         = mind (x, y, z)                by mind_def
*)
Theorem mind_zagier_eqn:
  !x y z. mind (zagier (x, y, z)) = mind (x, y, z)
Proof
  rw[mind_def, zagier_def]
QED

(* Theorem: mind (zagier t) = mind t *)
(* Proof: by triple_parts, mind_zagier_eqn. *)
Theorem mind_zagier_thm:
  !t. mind (zagier t) = mind t
Proof
  metis_tac[triple_parts, mind_zagier_eqn]
QED

(* What is the mind of a flip? *)

(* Theorem: mind (flip (x,y,z)) =
            if x < z - y then x + 2 * y
            else if x < z then 2 * z - x
            else x *)
(* Proof: by mind_def, flip_def *)
Theorem mind_flip_eqn:
  !x y z. mind (flip (x,y,z)) =
             if x < z - y then x + 2 * y
             else if x < z then 2 * z - x
             else x
Proof
  simp[mind_def, flip_def]
QED

(*
> mind_flip_eqn |> SPEC ``1`` |> SPEC ``1`` |> SPEC ``k:num``;
val it = |- mind (flip (1,1,k)) =
if 1 < k - 1 then 1 + 2 * 1 else if 1 < k then 2 * k - 1 else 1: thm
*)

(* Theorem: mind (flip (1,1,z)) = if z < 2 then 1 else 3 *)
(* Proof: by mind_flip_eqn. *)
Theorem mind_flip_1_1_z:
  !z. mind (flip (1,1,z)) = if z < 2 then 1 else 3
Proof
  simp[mind_flip_eqn]
QED

(*
> mind_flip_eqn |> SPEC ``x:num`` |> SPEC ``x:num`` |> SPEC ``z:num``;
val it = |- mind (flip (x,x,z)) =
if x < z - x then x + 2 * x else if x < z then 2 * z - x else x: thm
*)

(* Theorem: mind (flip (x,y,y)) = if x < y then 2 * y - x else x *)
(* Proof: by mind_flip_eqn. *)
Theorem mind_flip_x_x_z:
  !x z. mind (flip (x,x,z)) =
        if x < z - x then 3 * x else if x < z then 2 * z - x else x
Proof
  simp[mind_flip_eqn]
QED

(*
> mind_flip_eqn |> SPEC ``x:num`` |> SPEC ``y:num`` |> SPEC ``y:num``;
val it = |- mind (flip (x,y,y)) =
if x < y - y then x + 2 * y else if x < y then 2 * y - x else x: thm
*)

(* Theorem: mind (flip (x,y,y)) = if x < y then 2 * y - x else x *)
(* Proof: by mind_flip_eqn. *)
Theorem mind_flip_x_y_y:
  !x y. mind (flip (x,y,y)) = if x < y then 2 * y - x else x
Proof
  simp[mind_flip_eqn]
QED

(* ------------------------------------------------------------------------- *)
(* Gap of a Windmill.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the gap, the absolute difference of y and z in a triple. *)
Definition gap_def:
   gap (x,y,z) = if y < z then z - y else y - z
End

(* Theorem: gap (flip (x, y, z)) = gap (x, y, z) *)
(* Proof: by gap_def, flip_def. *)
Theorem gap_flip_eqn:
  !x y z. gap (flip (x, y, z)) = gap (x, y, z)
Proof
  simp[gap_def, flip_def]
QED

(* Theorem: gap (flip t) = gap t *)
(* Proof: by triple_parts, gap_flip_eqn. *)
Theorem gap_flip_thm:
  !t. gap (flip t) = gap t
Proof
  metis_tac[triple_parts, gap_flip_eqn]
QED


(* ------------------------------------------------------------------------- *)
(* Zagier and Flip.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: windmill t = windmill ((zagier o flip) t) *)
(* Proof:
     windmill ((zagier o flip) t)
   = windmill (zagier (flip t))    by o_THM
   = windmill (flip t)             by zagier_windmill
   = windmill t                    by flip_windmill
*)
Theorem zagier_flip_windmill:
  !t. windmill t = windmill ((zagier o flip) t)
Proof
  simp[GSYM zagier_windmill, GSYM flip_windmill]
QED

(* Theorem: (zagier o flip) (x, y, z) =
            if x < z - y then (x + 2 * y, y, z - y - x)
            else if x < 2 * z then (2 * z - x, z, x + y - z)
            else (x - 2 * z, x + y - z, z) *)
(* Proof:
   Let t = (x,y,z).
     (zagier o flip) t
   = zagier (x,z,y)                            by flip_def
   = if x < z - y then (x + 2 * y, y, z - y - x)
     else if x < 2 * z then (2 * z - x, z, x + y - z)
     else (x - 2 * z, x + y - z, z)            by zagier_def
*)
Theorem zagier_flip_eqn:
  !x y z. (zagier o flip) (x, y, z) =
           if x < z - y then (x + 2 * y, y, z - y - x)
           else if x < 2 * z then (2 * z - x, z, x + y - z)
           else (x - 2 * z, x + y - z, z)
Proof
  rw[zagier_def, flip_def]
QED

(*
zagier_flip_eqn |> SPEC ``x:num`` |> SPEC ``0`` |> SIMP_RULE std_ss [];
|- !z. zagier (flip (x,0,z)) = if x < z then (x,0,z - x)
                               else if x < 2 * z then (2 * z - x,z,x - z)
                               else (x - 2 * z,x - z,z)
> zagier_flip_eqn |> SPEC ``x:num`` |> SPEC ``y:num`` |> SPEC ``0`` |> SIMP_RULE std_ss [];
|- zagier (flip (x,y,0)) = (x,x + y,0)
> zagier_flip_eqn |> SPEC ``x:num`` |> SPEC ``y:num`` |> SPEC ``0`` |> SIMP_RULE std_ss [] |> GEN ``y:num`` |> GEN ``x:num``;
val it = |- !x y. zagier (flip (x,y,0)) = (x,x + y,0): thm
> zagier_flip_eqn |> SPEC ``0`` |> SIMP_RULE std_ss [];
val it = |- !y z.  zagier (flip (0,y,z)) =
        if 0 < z - y then (2 * y,y,z - y) else if 0 < z then (2 * z,z,y - z)  else (0,y,0): thm
> zagier_flip_eqn |> SPEC ``0`` |> SPEC ``1`` |> SIMP_RULE std_ss[];
val it = |- !z. zagier (flip (0,1,z)) =
          if 0 < z - 1 then (2,1,z - 1)
          else if 0 < z then (2 * z,z,1 - z)
          else (0,1,0): thm
> zagier_def |> ISPEC ``1`` |> ISPEC ``z:num`` |> ISPEC ``1`` |> SIMP_RULE arith_ss [];
|- zagier (1,z,1) =
      if 1 < z - 1 then (3,1,z - 2)
      else if 1 < 2 * z then (2 * z - 1,z,2 - z)
      else (1 - 2 * z,2 - z,z): thm
zagier_def |> ISPEC ``x:num`` |> ISPEC ``z:num`` |> ISPEC ``x:num`` |> SIMP_RULE arith_ss [];
*)

(* Theorem: (zagier o flip) (1,1,z) =
            if z = 0 then (1,2,0)
            else if z = 1 then (1,1,1)
            else if z = 2 then (3,2,0)
            else (3,1,z - 2) *)
(* Proof:
     (zagier o flip) (1,1,z)
   = zagier (flip (1,1,z))      by o_THM
   = zagier (1,z,1)             by flip_def
   = if z = 0 then (1,2,0)
     else if z = 1 then (1,1,1)
     else if z = 2 then (3,2,0)
     else (3,1,z - 2)           by zagier_def
*)
Theorem zagier_flip_1_1_z:
  !z. (zagier o flip) (1,1,z) =
         if z = 0 then (1,2,0)
         else if z = 1 then (1,1,1)
         else if z = 2 then (3,2,0)
         else (3,1,z - 2)
Proof
  rw[zagier_def, flip_def]
QED

(* Theorem: (zagier o flip) (0,1,z) =
            if z = 0 then (0,1,0)
            else (2,1,z - 1) *)
(* Proof:
     (zagier o flip) (0,1,z)
   = zagier (flip (0,1,z))      by o_THM
   = zagier (0,z,1)             by flip_def
   = if z = 0 then (0,1,0)
     else if z = 1 then (2,1,0)
     else (2,1,z - 1)           by zagier_def
     which also holds for z = 1.

*)
Theorem zagier_flip_0_1_z:
  !z. (zagier o flip) (0,1,z) =
         if z = 0 then (0,1,0)
         else (2,1,z - 1)
Proof
  rw[zagier_def, flip_def]
QED

(* Theorem: (zagier o flip) (0, y, z) = if 0 < z - y then (2 * y,y,z - y)
                                        else if 0 < z then (2 * z,z,y - z)
                                        else (0,y,0) *)
(* Proof: by zagier_flip_eqn. *)
Theorem zagier_flip_0_y_z:
  !y z. (zagier o flip) (0, y, z) =
         if 0 < z - y then (2 * y, y, z - y)
         else if 0 < z then (2 * z, z, y - z)
         else (0,y,0)
Proof
  rw[zagier_flip_eqn]
QED

(* Theorem: (zagier o flip) (x, 0, z) = if x < z then (x, 0, z - x)
                                        else if x < 2 * z then (2 * z - x, z, x - z)
                                        else (x - 2 * z, x - z, z) *)
(* Proof: by zagier_flip_eqn. *)
Theorem zagier_flip_x_0_z:
  !x z. (zagier o flip) (x, 0, z) =
         if x < z then (x, 0, z - x)
         else if x < 2 * z then (2 * z - x, z, x - z)
         else (x - 2 * z, x - z, z)
Proof
  rw[zagier_flip_eqn]
QED

(* Theorem: (zagier o flip) (x, y, 0) = (x, x + y, 0) *)
(* Proof: by zagier_flip_eqn. *)
Theorem zagier_flip_x_y_0:
  !x y. (zagier o flip) (x, y, 0) = (x, x + y, 0)
Proof
  rw[zagier_flip_eqn]
QED

(* Theorem: 0 < x ==> (zagier o flip) (x,y,x) = (x,x,y) *)
(* Proof:
      (zagier o flip) (x,y,x)
    = (2 * x - x,x,x + y - x)      by zagier_flip_eqn
    = (x,x,y)                      by arithmetic
*)
Theorem zagier_flip_x_y_x:
  !x y. 0 < x ==> (zagier o flip) (x,y,x) = (x,x,y)
Proof
  simp[zagier_flip_eqn]
QED


(* Theorem: windmill t = windmill ((flip o zagier) t) *)
(* Proof:
     windmill ((flip o zagier) t
   = windmill (flip (zagier t))    by o_THM
   = windmill (zagier t)           by flip_windmill
   = windmill t                    by zagier_windmill
*)
Theorem flip_zagier_windmill:
  !t. windmill t = windmill ((flip o zagier) t)
Proof
  simp[GSYM flip_windmill, GSYM zagier_windmill]
QED

(* Theorem: (flip o zagier) (x, y, z) =
            if x < y - z then (x + 2 * z, y - z - x, z)
            else if x < 2 * y then (2 * y - x, x + z - y, y)
            else (x - 2 * y, y, x + z - y) *)
(* Proof: by flip_def, zagier_def. *)
Theorem flip_zagier_eqn:
  !x y z. (flip o zagier) (x, y, z) =
           if x < y - z then (x + 2 * z, y - z - x, z)
           else if x < 2 * y then (2 * y - x, x + z - y, y)
           else (x - 2 * y, y, x + z - y)
Proof
  rw[flip_def, zagier_def]
QED

(* Theorem: 0 < x ==> (flip o zagier) (x,x,z) = (x,z,x) *)
(* Proof:
   Note x < x - z is false         by LESS_REFL
    and x < 2 * x is true          by 0 < x
      (flip o zagier) (x,x,z)
    = (2 * x - x,x + z - x,x)      by flip_zagier_eqn
    = (x,z,x)                      by arithmetic
*)
Theorem flip_zagier_x_x_z:
  !x z. 0 < x ==> (flip o zagier) (x,x,z) = (x,z,x)
Proof
  simp[flip_zagier_eqn]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
