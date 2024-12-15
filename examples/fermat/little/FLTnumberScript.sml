(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Number-theoretic Proof.                         *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Number Theory)
=======================================
Equivalent statements of Feramt's Little Theorem:
#0. For prime p, 0 < a < p, a ** (p-1) = 1 MOD p.
#1. For prime p, 0 < a < p, a ** p = a MOD p.
#2. For prime p, 0 < a < p, (a ** p - a) = 0 MOD p.
#3. For prime p, 0 < a < p, p divides (a ** p - a).
#4. For prime p, 0 < a < p, 0 < (a ** (p-2) MOD p) < p and
                            ((a ** (p-2) MOD p) * a) MOD p = 1.

The first one (#0) will be called Fermat's Identity.

There is a number-theoretic proof without reference to Group Theory.

Number-theoretic Proof:
----------------------
For a prime p, consider the set of residue p = { i | 0 < i < p }.

This set is non-empty since prime p > 1.

For a fixed a in residue p, multiply each element in the above set
by a and take MOD p, i.e. form this coset { (a * i) MOD p | 0 < i < p }.

These two sets are the same because:
(1) 0 < a < p implies 0 < (a * i) MOD p < p.
    The crucial part is to show:
    a MOD p = a <> 0 and i MOD p = i <> 0 implies (a * i) MOD p <> 0,
    but this is the contrapositive of Euclid's Lemma:
      If prime p divides a * b, then (p divides a) or (p divides b).
(2) If (a*i) MOD p = (a*j) MOD p, then i = j.
    This is due to left-cancellation for MOD p when p is prime,
    again given by Euclid Lemma:
        (a * i) MOD p = (a * j) MOD p
    ==> (a * i - a * j) MOD p = 0
    ==>   (a * (i - j)) MOD p = 0
    ==>         (i - j) MOD p = 0          since a MOD p <> 0
    ==>               i MOD p = j MOD p    assume i > j, otherwise switch i, j.
    ==>                     i = j          as 0 < i < p, 0 < j < p.

Hence for prime p, and any a in (residue p),

  (residue p) = IMAGE (row p a) (residue p)   where row p a x = (a * x) MOD p.

Take the product of elements in each set, MOD p, and they are equal:

  PROD_SET (residue p) = PROD_SET (IMAGE (row p a) (residue p))

Computation by induction gives:

  PROD_SET (residue p) = (FACT (p-1)) MOD p,  and
  PROD_SET (IMAGE (row p a) (residue p)) = (a ** (p-1) * FACT (p-1)) MOD p

Hence   (FACT (p-1) * a ** (p-1)) MOD p = (FACT (p-1)) MOD p

Since a prime p cannot divide FACT (p-1), cancellation law applies, giving:

         a ** (p-1) MOD p = 1, which is Fermat's Identity.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "FLTnumber";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory pred_setTheory dividesTheory gcdTheory numberTheory
     combinatoricsTheory;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Number Theory Documentation                    *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Mapping residues to a row of residues:
   row_def             |- !n a x. row n a x = (a * x) MOD n
   row_prime_not_in_residue_image
                       |- !p a n. prime p /\ a IN residue p /\ n <= p ==>
                                  row p a n NOTIN IMAGE (row p a) (residue n)
   prod_set_image_row_reduction
                       |- !p a n. prime p /\ a IN residue p /\ 0 < n /\ n <= p ==>
                                  PROD_SET (IMAGE (row p a) (residue (SUC n))) =
                                    (a * n) MOD p * PROD_SET (IMAGE (row p a) (residue n))
   prod_set_image_row  |- !p a n. prime p /\ a IN residue p /\ 0 < n /\ n <= p ==>
                                  PROD_SET (IMAGE (row p a) (residue n)) MOD p =
                                    (a ** (n - 1) * FACT (n - 1)) MOD p
   prod_set_image_row_all
                       |- !p a. prime p /\ a IN residue p ==>
                                PROD_SET (IMAGE (row p a) (residue p)) MOD p =
                                  (a ** (p - 1) * FACT (p - 1)) MOD p

   Fermat's Identity:
   residue_prime_row_inj   |- !p a. prime p /\ a IN residue p ==>
                                    INJ (row p a) (residue p) (residue p)
   residue_prime_row_surj  |- !p a. prime p /\ a IN residue p ==>
                                    SURJ (row p a) (residue p) (residue p)
   residue_prime_row_bij   |- !p a. prime p /\ a IN residue p ==> row p a PERMUTES residue p
   residue_prime_row_image |- !p a. prime p /\ a IN residue p ==>
                                    IMAGE (row p a) (residue p) = residue p
   residue_prime_identity  |- !p a. prime p /\ a IN residue p ==>
                                    FACT (p - 1) MOD p = (a ** (p - 1) * FACT (p - 1)) MOD p
   fermat_identity     |- !p a. prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1

   Fermat's Little Theorem (various forms):
   fermat_little_4     |- !p a. prime p ==> a ** p MOD p = a MOD p
   fermat_little_5     |- !p a. prime p ==> (a ** p - a) MOD p = 0
   fermat_little_6     |- !p a. prime p ==> p divides a ** p - a
   fermat_little_7     |- !p a b. prime p /\ a IN residue p /\ (b = a ** (p - 2) MOD p) ==>
                                  b IN residue p /\ (b * a) MOD p = 1
   fermat_little_exp   |- !p a n. prime p ==> a ** p ** n MOD p = a MOD p

*)

(* ------------------------------------------------------------------------- *)
(* Number-theoretic Proof without Group Theory.                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Mapping residues to a row of residues.                                    *)
(* ------------------------------------------------------------------------- *)

(* Define the row function: producing a row of the Z[n] multiplication table *)
Definition row_def:
   row n a x = (a * x) MOD n
End

(*
> EVAL ``residue 7``; = {6; 5; 4; 3; 2; 1}: thm, elements of Z[7].
> EVAL ``IMAGE (row 7 1) (residue 7)``; = {6; 5; 4; 3; 2; 1}: thm
> EVAL ``IMAGE (row 7 2) (residue 7)``; = {5; 3; 1; 6; 4; 2}: thm
> EVAL ``IMAGE (row 7 3) (residue 7)``; = {4; 1; 5; 2; 6; 3}: thm
> EVAL ``IMAGE (row 7 4) (residue 7)``; = {3; 6; 2; 5; 1; 4}: thm
> EVAL ``IMAGE (row 7 5) (residue 7)``; = {2; 4; 6; 1; 3; 5}: thm
> EVAL ``IMAGE (row 7 6) (residue 7)``; = {1; 2; 3; 4; 5; 6}: thm
*)

(*
> EVAL ``(row 7 2)(6)``; = 5: thm
> EVAL ``IMAGE (row 7 2) (residue 6)``; = {3; 1; 6; 4; 2}: thm
> EVAL ``(row 7 2)(5)``; = 3: thm
> EVAL ``IMAGE (row 7 2) (residue 5)``; = {1; 6; 4; 2}: thm

For (residue n) with n <= p for (row p a),
n NOTIN (residue n), row p a n = (a * n) MOD p,
but IMAGE (row p a) (residue n) = {(a * j) MOD p | j < n}, no (a * n) MOD p.
*)

(* Idea: for prime p, a in (residue p) /\ (n <= p) ==>
              (row p a)(n) not IN IMAGE (row p a) (residue n). *)

(* Theorem: prime p /\ a IN (residue p) /\ n <= p ==>
            (row p a)(n) NOTIN IMAGE (row p a) (residue n) *)
(* Proof:
   Note (row p a)(n) = (a * n) MOD p      by row_def
    and x IN residue n is mapped to
        (row p a)(x) = (a * x) MOD p      by row_def
    But (a * n) MOD p <> (a * x) MOD p    by residue_prime_neq
*)
Theorem row_prime_not_in_residue_image:
  !p a n. prime p /\ a IN (residue p) /\ n <= p ==>
          (row p a)(n) NOTIN IMAGE (row p a) (residue n)
Proof
  rw[row_def] >>
  metis_tac[residue_prime_neq]
QED

(* ------------------------------------------------------------------------- *)
(* More PROD_SET properties, especially with row.                            *)
(* ------------------------------------------------------------------------- *)

(* Idea: [Inductive step of prod_set_image_row]
         for prime p, a in (residue p), 0 < n <= p,
         PROD_SET (IMAGE (row p a) (residue (SUC n))) =
             ((a * n) MOD p) * PROD_SET (IMAGE (row p a) (residue n)) *)

(* Theorem: prime p /\ a IN (residue p) /\ 0 < n /\ n <= p ==>
            (PROD_SET (IMAGE (row p a) (residue (SUC n))) =
                    ((a * n) MOD p) * PROD_SET (IMAGE (row p a) (residue n))) *)
(* Proof:
   Let f = row p a, s = residue n.
   Note FINITE s                    by residue_insert
     so FINITE (IMAGE f s)          by IMAGE_FINITE
    and (f n) NOTIN (IMAGE f s)     by row_prime_not_in_residue_image

     PROD_SET (IMAGE f (residue (SUC n)))
   = PROD_SET (IMAGE f (n INSERT s)           by residue_insert, 0 < n
   = (f n) * PROD_SET (IMAGE f s)             by PROD_SET_IMAGE_REDUCTION
   = ((a * n) MOD p) * PROD_SET (IMAGE f s)   by row_def
*)
Theorem prod_set_image_row_reduction:
  !p a n. prime p /\ a IN (residue p) /\ 0 < n /\ n <= p ==>
          PROD_SET (IMAGE (row p a) (residue (SUC n))) =
                    ((a * n) MOD p) * PROD_SET (IMAGE (row p a) (residue n))
Proof
  rpt strip_tac >>
  imp_res_tac row_prime_not_in_residue_image >>
  `FINITE (IMAGE (row p a) (residue n))` by rw[residue_finite, IMAGE_FINITE] >>
  `PROD_SET (IMAGE (row p a) (residue (SUC n))) =
    PROD_SET (IMAGE (row p a) (n INSERT residue n))` by rw[residue_insert] >>
  `_ = ((row p a)(n)) * PROD_SET (IMAGE (row p a) (residue n))` by rw[PROD_SET_IMAGE_REDUCTION] >>
  simp[row_def]
QED

(* Idea: for prime p, and a in (residue p),
         PROD_SET IMAGE (row p a) (residue p) = (a ** (p-1) * FACT (p-1)) MOD p. *)
(* Proof:
   Observe the pattern when p = 5, a = 3,

     PROD_SET IMAGE (row 5 3) (residue 5)
   = PROD_SET IMAGE (row 5 3) {x | 0 < x < 5 }
   = PROD_SET {row 5 3 x | 0 < x < 5 }
   = PROD_SET {(3*x) MOD 5 | 0 < x < 5 }
   = ((3*4) MOD 5) * PROD_SET {(3*x) MOD 5 | 0 < x < 4 }
   = ((3*4) MOD 5) * ((3*3) MOD 5) * PROD_SET {(3*x) MOD 5 | 0 < x < 3 }
   = ((3*4) MOD 5) * ((3*3) MOD 5) * ((3*2) MOD 5) * PROD_SET {(3*x) MOD 5 | 0 < x < 2 }
   = ((3*4) MOD 5) * ((3*3) MOD 5) * ((3*2) MOD 5) * ((3*1) MOD 5) * PROD_SET {(3*x) MOD 5 | 0 < x < 1 }
   = ((3*4) MOD 5) * ((3*3) MOD 5) * ((3*2) MOD 5) * ((3*1) MOD 5) * PROD_SET EMPTY
   = ((3*4) MOD 5) * ((3*3) MOD 5) * ((3*2) MOD 5) * ((3*1) MOD 5) * 1
   = ((3*4) MOD 5) * ((3*3) MOD 5) * ((3*2) MOD 5) * ((3*1) MOD 5) * (1 MOD 5)
   = ((3*4) * (3*3) * (3*2) * (3*1)) MOD 5
   = ((3*3*3*3) * (4*3*2*1)) MOD 5
   = ((3^4) * FACT 4) MOD 5

   Note that MOD p is not changing, but residue n is changing with n <= p.
   So change this theorem to:

   !n. PROD_SET IMAGE (row p a) (residue n) = (a ** (n-1) * FACT (n-1)) MOD p

   and apply induction on n.
*)

(* Theorem: prime p /\ a IN (residue p) /\ 0 < n /\ n <= p ==>
            PROD_SET (IMAGE (row p a) (residue n)) MOD p =
                     (a ** (n-1) * FACT (n-1)) MOD p *)
(* Proof:
   Let f = row p a, s = residue n.
   By induction on n.
   Base: 0 < 0 ==> ..., since 0 < 0 = F, hence true.
   Step: 0 < n /\ n <= p ==>
         (PROD_SET (IMAGE f s) MOD p = (a ** (n - 1) * FACT (n - 1)) MOD p) ==>
         SUC n <= p ==>
         (PROD_SET (IMAGE f (residue (SUC n))) MOD p = (a ** n * FACT n) MOD p)

     If n = 0, this is to show:
          PROD_SET (IMAGE f (residue 1)) MOD p = FACT 0 MOD p

          PROD_SET (IMAGE f (residue 1)) MOD p
        = PROD_SET (IMAGE f {}) MOD p                   by residue_1
        = PROD_SET {} MOD p                             by IMAGE_EMPTY
        = 1 MOD p                                       by PROD_SET_EMPTY
        = FACT 0 MOD p                                  by FACT_0

     If n <> 0, this is to show:
          PROD_SET (IMAGE f (residue (SUC n))) MOD p = (a ** n * FACT n) MOD p

        Note 0 < n /\ n <= p /\ 0 < p                          by arithmetic
          PROD_SET (IMAGE f (residue (SUC n))) MOD p
        = (((a * n) MOD p) * PROD_SET (IMAGE f s)) MOD p       by prod_set_image_row_reduction
        = ((a * n) * PROD_SET (IMAGE f s)) MOD p               by MOD_TIMES2
        = ((a * n) MOD p * (PROD_SET (IMAGE f s)) MOD p) MOD p by MOD_TIMES2
        = ((a * n) MOD p * ((a ** (n - 1) * FACT (n - 1))) MOD p) MOD p
                                                               by inductive hypothesis
        = ((a * n) * (a ** (n - 1) * FACT (n - 1))) MOD p      by MOD_TIMES2
        = ((a * (a ** (n-1))) * (n * FACT (n-1))) MOD p        by arithmetic
        = (a ** (SUC (n-1)) * (n * FACT (n-1))) MOD p          by EXP
        = ((a ** n) * (SUC (n-1) * FACT (n-1))) MOD p          by ADD1
        = (a ** n * FACT (SUC (n-1))) MOD p                    by FACT
        = (a ** n * FACT n * a ** n) MOD p                     by ADD1
*)
Theorem prod_set_image_row:
  !p a n. prime p /\ a IN (residue p) /\ 0 < n /\ n <= p ==>
          PROD_SET (IMAGE (row p a) (residue n)) MOD p =
                     (a ** (n-1) * FACT (n-1)) MOD p
Proof
  rpt strip_tac >>
  (Induct_on `n` >> rw[]) >>
  (Cases_on `n = 0` >> simp[]) >-
  rw[residue_1, PROD_SET_EMPTY, FACT_0] >>
  `0 < n /\ n <= p /\ 0 < p` by decide_tac >>
  `(PROD_SET (IMAGE (row p a) (residue (SUC n)))) MOD p =
      (((a * n) MOD p) * PROD_SET (IMAGE (row p a) (residue n))) MOD p` by rw[prod_set_image_row_reduction] >>
  `_ = ((a * n) * PROD_SET (IMAGE (row p a) (residue n))) MOD p` by rw[MOD_TIMES2] >>
  `_ = ((a * n) MOD p * (PROD_SET (IMAGE (row p a) (residue n))) MOD p) MOD p` by rw[MOD_TIMES2] >>
  `_ = ((a * n) MOD p * ((a ** (n - 1) * FACT (n - 1))) MOD p) MOD p` by simp[] >>
  `_ = ((a * n) * (a ** (n - 1) * FACT (n - 1))) MOD p` by rw[MOD_TIMES2] >>
  `_ = ((a * (a ** (n-1))) * (n * FACT (n-1))) MOD p` by simp[] >>
  `_ = (a ** (SUC (n-1)) * (n * FACT (n-1))) MOD p` by rw[EXP] >>
  `_ = ((a ** n) * (SUC (n-1) * FACT (n-1))) MOD p` by rw[ADD1] >>
  `_ = (a ** n * FACT (SUC (n-1))) MOD p` by rw[FACT] >>
  simp[ADD1]
QED

(* Idea: The above version with n = p *)

(* Theorem: prime p /\ a IN (residue p) ==>
            PROD_SET (IMAGE (row p a) (residue p)) MOD p = (a ** (p-1) * FACT (p-1)) MOD p *)
(* Proof:
   Note 0 < p            by PRIME_POS
   The result follows    by prod_set_image_row, 0 < p <= p.
*)
Theorem prod_set_image_row_all:
  !p a. prime p /\ a IN (residue p) ==>
        PROD_SET (IMAGE (row p a) (residue p)) MOD p = (a ** (p-1) * FACT (p-1)) MOD p
Proof
  rw[prod_set_image_row, PRIME_POS]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat's Identity                                                         *)
(* ------------------------------------------------------------------------- *)

(* Idea: Let Z* = {n | 0 < n /\ n < p} with prime p, i.e. residue p.
         Then !a in Z*, the function f: Z* -> Z* = x -> (a * x) MOD p is an injection,
   or
   For prime p and a in residue p,
   the map  (row p a): (residue p) -> (residue p) is an injection. *)

(* Theorem: prime p /\ a IN (residue p) ==> INJ (row p a) (residue p) (residue p) *)
(* Proof:
   Note 0 < p        by PRIME_POS
    and a MOD p = a  by MOD_LESS
   By residue_def, row_def, INJ_DEF, this is to show:
   (1) 0 < a MOD p /\ 0 < x /\ x < p ==> 0 < (a * x) MOD p
       Note x MOD p = x <> 0       by MOD_LESS
       so (a * x) MOD p <> 0       by EUCLID_LEMMA, prime p
   (2) 0 < x /\ x < p /\ 0 < y /\ y < p /\ (a * x) MOD p = (a * y) MOD p ==> x = y
       Note x MOD p = y MOD p      by MOD_MULT_LCANCEL, prime p
        and x MOD p = x            by MOD_LESS
        and y MOD p = y            by MOD_LESS
       Thus x = y
*)
Theorem residue_prime_row_inj:
  !p a. prime p /\ a IN (residue p) ==> INJ (row p a) (residue p) (residue p)
Proof
  rw[residue_def] >>
  `0 < p` by rw[PRIME_POS] >>
  `a MOD p <> 0` by rw[] >>
  rw[row_def, INJ_DEF] >| [
    `x MOD p <> 0` by rw[] >>
    metis_tac[EUCLID_LEMMA, NOT_ZERO],
    metis_tac[MOD_MULT_LCANCEL, LESS_MOD]
  ]
QED

(* Idea: for prime p, and a in residue p,
         the map  (row p a): (residue p) -> (residue p) is a surjection. *)

(* Theorem: prime p /\ (a IN residue p) ==> SURJ (row p a) (residue p) (residue p) *)
(* Proof:
   Let f = row p a, s = residue p.
   Note FINITE s       by residue_finite
    and INJ f s s      by residue_prime_row_inj
     so SURJ f s s     by FINITE_INJ_AS_SURJ
*)
Theorem residue_prime_row_surj:
  !p a. prime p /\ (a IN residue p) ==> SURJ (row p a) (residue p) (residue p)
Proof
  rpt strip_tac >>
  `FINITE (residue p)` by rw[residue_finite] >>
  simp[residue_prime_row_inj, FINITE_INJ_AS_SURJ]
QED

(* Idea: for prime p, and a in residue p,
         the map  (row p a): (residue p) -> (residue p) is a bijection,
         thus a permutation on (residue p). *)

(* Theorem: prime p /\ (a IN residue p) ==> (row p a) PERMUTES (residue p) *)
(* Proof:
   Let f = row p a, s = residue p.
   Note INJ f s s         by residue_prime_row_inj
     so SURJ f s s        by residue_prime_row_surj
   Thus BIJ f s s         by BIJ_DEF
     or f PERMUTES s      by notation
*)
Theorem residue_prime_row_bij:
  !p a. prime p /\ (a IN residue p) ==> (row p a) PERMUTES (residue p)
Proof
  simp[BIJ_DEF, residue_prime_row_inj, residue_prime_row_surj]
QED

(* Idea: for prime p, residue p = IMAGE (row p a) (residue p) *)

(* Theorem: prime p /\ (a IN residue p) ==> IMAGE (row p a) (residue p) = residue p *)
(* Proof:
   Let f = row p a, s = residue p.
   Note SURJ f s s     by residue_prime_row_surj
   Thus IMAGE f s = s  by IMAGE_SURJ
*)
Theorem residue_prime_row_image:
  !p a. prime p /\ (a IN residue p) ==> IMAGE (row p a) (residue p) = residue p
Proof
  simp[residue_prime_row_surj, GSYM IMAGE_SURJ]
QED

(* Idea: an identity for residue modulo prime:
         For prime p, FACT (p-1) MOD p = (a ** (p-1) * (FACT (p-1)) MOD p *)

(* Theorem: prime p /\ a IN (residue p) ==>
            FACT (p - 1) MOD p = (a ** (p - 1) * FACT (p - 1)) MOD p *)
(* Proof:
     FACT (p - 1) MOD p
   = PROD_SET (residue p) MOD p                     by prod_set_residue
   = PROD_SET (IMAGE (row p a) (residue p)) MOD p   by residue_prime_row_image
   = (a ** (p - 1) * FACT (p - 1)) MOD p            by prod_set_image_row_all
*)
Theorem residue_prime_identity:
  !p a. prime p /\ a IN (residue p) ==>
        FACT (p - 1) MOD p = (a ** (p - 1) * FACT (p - 1)) MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  simp[GSYM prod_set_image_row_all] >>
  simp[GSYM prod_set_residue] >>
  metis_tac[residue_prime_row_image]
QED

(* Idea: Fermat's Identity: for prime p, a ** (p - 1) MOD p = 1 *)

(* Theorem: prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1 *)
(* Proof:
   Let q = FACT (p - 1).
   Note 1 < p                                by ONE_LT_PRIME
    and a IN (residue p)                     by residue_def
   Note q MOD p = (a ** (p - 1) * q) MOD p   by residue_prime_identity
    and q MOD p <> 0                         by FACT_MOD_PRIME
     so 1 MOD p = (a ** (p - 1)) MOD p       by MOD_MULT_LCANCEL
     or a ** (p - 1) MOD p = 1               by ONE_MOD, 1 < p
*)
Theorem fermat_identity:
  !p a. prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `a IN (residue p)` by fs[residue_def] >>
  imp_res_tac residue_prime_identity >>
  `FACT (p - 1) MOD p <> 0` by rw[FACT_MOD_PRIME] >>
  metis_tac[MULT_LEFT_1, MULT_COMM, MOD_MULT_LCANCEL, ONE_MOD]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem (various forms)                                   *)
(* ------------------------------------------------------------------------- *)

(* These are derived from fermat_identity:
|- !p a. prime p /\ 0 < a /\ a < p ==> a ** (p - 1) MOD p = 1
*)

(* Idea: Fermat's Little Theorem: For prime p, (a ** p) MOD p = a MOD p. *)

(* Theorem: prime p ==> (a ** p) MOD p = a MOD p *)
(* Proof:
   Note 0 < p                          by 0 < a < p
   Let b = a MOD p.
   If b = 0,
        (a ** p) MOD p
      = (b ** p) MOD p    by EXP_MOD, 0 < p
      = 0                 by ZERO_EXP
      = b                 by notation
   If n <> 0,
      Then 0 < n < p      by MOD_LESS, 0 < p
        (a ** p) MOD p
      = (b ** p) MOD p    by EXP_MOD, 0 < p
      = (b ** (SUC (p - 1))) MOD p     by arithmetic, 0 < p
      = (b * b ** (p - 1)) MOD p       by EXP
      = ((b MOD p) * (b ** (p - 1) MOD p)) MOD p
                                       by MOD_TIMES2, 0 < p
      = ((b MOD p) * 1) MOD p          by fermat_identity for b, prime p
      = b = a MOD p                    by MOD_MOD, 0 < p
*)
Theorem fermat_little_4:
  !p a. prime p ==> (a ** p) MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `b = a MOD p` >>
  `b MOD p = b` by rw[MOD_MOD, Abbr`b`] >>
  `a ** p MOD p = b ** p MOD p` by rw[EXP_MOD, Abbr`b`] >>
  Cases_on `b = 0` >-
  metis_tac[ZERO_EXP, NOT_ZERO] >>
  `0 < b` by decide_tac >>
  `b < p` by rw[Abbr`b`] >>
  `p = SUC (p - 1)` by decide_tac >>
  `(b ** p) MOD p = (b ** (SUC (p - 1))) MOD p` by metis_tac[] >>
  `_ = (b * b ** (p - 1)) MOD p` by rw[EXP] >>
  `_ = ((b MOD p) * (b ** (p - 1) MOD p)) MOD p` by rw[MOD_TIMES2] >>
  rfs[fermat_identity]
QED

(* Idea: Fermat's Little Theorem: for prime p, (a ** p - a) MOD p = 0. *)

(* Theorem: prime p /\ 0 < a /\ a < p ==> (a ** p - a) MOD p = 0 *)
(* Proof:
   Note 0 < p                            by PRIME_POS
    and     (a ** p) MOD p = a MOD p     by fermat_little_4
     so (a ** p - a) MOD p = 0           by MOD_EQ_DIFF, 0 < p
*)
Theorem fermat_little_5:
  !p a. prime p ==> (a ** p - a) MOD p = 0
Proof
  simp[fermat_little_4, PRIME_POS, MOD_EQ_DIFF]
QED

(* Idea: Fermat's Little Theorem: for prime p, p divides (a ** p - a) *)

(* Theorem: prime p /\ 0 < a /\ a < p ==> p divides (a ** p - a) *)
(* Proof:
   Note 0 < p                      by PRIME_POS
    and (a ** p - a) MOD p = 0     by fermat_little_5
     so p divides (a ** p - a)     by DIVIDES_MOD_0, 0 < p
*)
Theorem fermat_little_6:
  !p a. prime p ==> p divides (a ** p - a)
Proof
  simp[fermat_little_5, PRIME_POS, DIVIDES_MOD_0]
QED

(* Idea: Fermat's Little Theorem: for prime p, a IN (residue p),
    (1) (a ** (p-2) MOD p) IN (residue p
    (2) ((a ** (p-2) MOD p) * a) MOD p = 1.
    This shows b = a ** (p - 2) MOD p is a multiplicative inverse of a in MOD p. *)

(* Theorem: prime p /\ a IN (residue p) /\ (b = a ** (p - 2) MOD p) ==>
            b IN (residue p) /\ (b * a) MOD p = 1 *)
(* Proof:
   Let q = a ** (p - 2).
   Note 0 < p                           by 0 < a < p, a IN residue p.
        (b * a) MOD p
      = (q * a) MOD p                   by MOD_TIMES2
      = (a * a ** (p - 2)) MOD p        by MULT_COMM
      = (a * a ** (SUC (p - 1))) MOD p  by 0 < p
      = (a ** (p - 1)) MOD p            by EXP
      = 1                               by fermat_identity
   To show 0 < b < p                    by residue_def
   Note b < p                           by MOD_LESS, 0 < p
   By contradiction, suppose ~(0 < b),
   that is, b = 0.
   Then (b * a) MOD p = 0               by ZERO_MOD, 0 < p
   This contradicts (b * a) MOD = 1.
*)
Theorem fermat_little_7:
  !p a b. prime p /\ a IN (residue p) /\ (b = a ** (p - 2) MOD p) ==>
          b IN (residue p) /\ (b * a) MOD p = 1
Proof
  simp[residue_def] >>
  ntac 3 strip_tac >>
  qabbrev_tac `b = a ** (p - 2)` >>
  `0 < p /\ (SUC (p - 2) = p - 1)` by decide_tac >>
  `a * b = a ** (p - 1)` by rw[GSYM EXP, Abbr`b`] >>
  `(a * b) MOD p = 1` by fs[fermat_identity] >>
  simp[] >>
  spose_not_then strip_assume_tac >>
  `b MOD p = 0` by decide_tac >>
  `0 = 1` by metis_tac[MOD_TIMES2, MULT_0, ZERO_MOD] >>
  decide_tac
QED

(* ------------------------------------------------------------------------- *)
(* Power Version of Fermat's Little Theorem                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea: (Power version of Fermat's Little Theorem)
         For prime p, a ** (p ** n) = a (mod p) *)

(* Theorem: prime p ==> a ** (p ** n) MOD p = a MOD p *)
(* Proof:
   By induction on n:
   Base: a ** p ** 0 MOD p = a MOD p
         a ** p ** 0 MOD p
       = a ** 1 MOD p     by EXP_0
       = a MOD p          by EXP_1
   Step: a ** p ** n MOD p = a MOD p ==>
         a ** p ** SUC n MOD p = a MOD p

         (a ** (p ** SUC n)) MOD p
       = (a ** (p * p ** n)) MOD p             by EXP
       = ((a ** p) ** (p ** n)) MOD p          by EXP_EXP_MULT
       = (((a ** p) MOD p) ** (p ** n)) MOD p  by EXP_MOD, 0 < p
       = ((a MOD p) ** (p ** n)) MOD p         by fermat_little_4
       = (a ** (p ** n)) MOD p                 by EXP_MOD, 0 < p
       = a MOD p                               by induction hypothesis
*)
Theorem fermat_little_exp:
  !p a n. prime p ==> a ** (p ** n) MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  Induct_on `n` >-
  simp[EXP_0, EXP_1] >>
  `(a ** (p ** SUC n)) MOD p = (a ** (p * p ** n)) MOD p` by rw[EXP] >>
  `_ = ((a ** p) ** (p ** n)) MOD p` by rw[EXP_EXP_MULT] >>
  `_ = (((a ** p) MOD p) ** (p ** n)) MOD p` by rw[EXP_MOD] >>
  `_ = ((a MOD p) ** (p ** n)) MOD p` by rw[fermat_little_4] >>
  `_ = (a ** (p ** n)) MOD p` by rw[EXP_MOD] >>
  `_ = a MOD p` by rw[] >>
  simp[]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
