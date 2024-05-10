(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation giving Polynomial.                                  *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyEval";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;

(* val _ = load "polyMonicTheory"; *)
open polyMonicTheory;

(* val _ = load "polyRootTheory"; *)
open polyRootTheory;

(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation giving Polynomial Documentation                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   peval p q     = poly_peval r p q
*)
(* Definitions and Theorems (# are exported):

   Polynomial Evaluation giving Polynomial:
#  poly_peval_def       |- (!r x. peval [] x = |0|) /\ !r h t x. peval (h::t) x = h * |1| + peval t x * x
   poly_peval_of_zero   |- !r x. peval [] x = |0|
   poly_peval_cons      |- !r h t x. peval (h::t) x = h * |1| + peval t x * x
   weak_peval_poly      |- !r. Ring r ==> !p q. weak p /\ poly q ==> poly (peval p q)
#  poly_peval_poly      |- !r. Ring r ==> !p q. poly p /\ poly q ==> poly (peval p q)
#  weak_peval_weak      |- !r. Ring r ==> !p x. weak p /\ poly x ==> weak (peval p x)
#  poly_peval_zerop     |- !r. Ring r ==> !p x. zerop p /\ poly x ==> (peval p x = |0|)
   weak_peval_chop      |- !r. Ring r ==> !p x. weak p /\ poly x ==> (peval (chop p) x = peval p x)
   poly_peval_chop      |- !r. Ring r ==> !p x. poly p /\ poly x ==> (peval (chop p) x = chop (peval p x))
   poly_peval_cons_alt  |- !r. Ring r ==> !h t x. h IN R /\ poly t /\ poly x ==>
                                          (peval (h::t) x = chop (h o |1| || peval t x o x))
   poly_peval_add       |- !r. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p + q) x = peval p x + peval q x)
   poly_peval_neg       |- !r. Ring r ==> !p x. poly p /\ poly x ==> (peval (-p) x = -peval p x)
   poly_peval_sub       |- !r. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p - q) x = peval p x - peval q x)
   poly_peval_cmult     |- !r. Ring r ==> !p x. poly p /\ poly x ==> !c. c IN R ==> (peval (c * p) x = c * peval p x)
   poly_peval_shift     |- !r. Ring r ==> !p x. poly p /\ poly x ==> !n. peval (p >> n) x = peval p x * x ** n
   poly_peval_mult      |- !r. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p * q) x = peval p x * peval q x)

   More Polynomials Theorems and Evaluation:
#  poly_peval_zero      |- !r x. peval |0| x = |0|
   poly_peval_const     |- !r x c. Ring r /\ c IN R /\ c <> #0 ==> (peval [c] x = [c])
#  poly_peval_one       |- !r. Ring r ==> !x. poly x ==> (peval |1| x = |1|)
   poly_peval_X         |- !r. Ring r ==> !p. poly p ==> (peval X p = p)
   poly_peval_exp       |- !r. Ring r ==> !p x. poly p /\ poly x ==> !n. peval (p ** n) x = peval p x ** n
   poly_peval_ring_sum  |- !r. Ring r ==> !p. poly p ==> (peval |c| p = |c|)
   poly_peval_X_add_c   |- !r. Ring r ==> !p. poly p ==> (peval (X + |c|) p = p + |c|)
   poly_peval_X_sub_c   |- !r. Ring r ==> !p. poly p ==> (peval (X - |c|) p = p - |c|)
   poly_peval_X_exp     |- !r. Ring r /\ #1 <> #0 ==> !p. poly p ==> !n. peval (X ** n) p = p ** n
   poly_peval_X_exp_n_add_c    |- !r. Ring r ==>
                                  !p. poly p ==> !n c. peval (X ** n + |c|) p = p ** n + |c|
   poly_peval_X_exp_n_sub_c    |- !r. Ring r ==>
                                  !p. poly p ==> !n c. peval (X ** n - |c|) p = p ** n - |c|
   poly_peval_by_X             |- !r p. Ring r /\ poly p ==> (peval p X = p)
   poly_peval_X_add_c_by_zero  |- !r. Ring r ==> !c. peval (X + |c|) |0| = |c|
   poly_peval_X_sub_c_by_zero  |- !r. Ring r ==> !c. peval (X - |c|) |0| = -|c|
   poly_peval_X_add_c_by_one   |- !r. Ring r ==> !c. peval (X + |c|) |1| = |1| + |c|
   poly_peval_X_sub_c_by_one   |- !r. Ring r ==> !c. peval (X - |c|) |1| = |1| - |c|
   poly_peval_factor           |- !r. Ring r ==> !c p. c IN R /\ poly p ==>
                                      (peval (factor c) p = if c = #0 then p else p - [c])
   poly_peval_factor_alt       |- !r. Ring r /\ #1 <> #0 ==>
                                  !c p. c IN R /\ poly p ==> (peval (factor c) p = p - c * |1|)
   poly_peval_factor_map_inj   |- !r. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==>
                                  !q. poly q ==> INJ (\p. peval p q) (IMAGE factor s) univ(:'a poly)
   poly_peval_unity     |- !r. Ring r ==> !p. poly p ==> !n. peval (unity n) p = p ** n - |1|
   poly_peval_unity_1   |- !r. Ring r ==> !p. poly p ==> (peval (unity 1) p = p - |1|)
   poly_peval_by_zero   |- !r p. Ring r /\ poly p ==> peval p |0| = chop [eval p #0]
   poly_peval_by_one    |- !r p. Ring r /\ poly p ==> peval p |1| = chop [eval p #1]

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation giving Polynomial                                   *)
(* ------------------------------------------------------------------------- *)

(* Similar to evaluation of a polynomial, but results in a polynomial. *)
val poly_peval_def = Define`
  (poly_peval (r:'a ring) [] x = |0|) /\
  (poly_peval (r:'a ring) (h:'a :: t:'a poly) x = h * |1| + (poly_peval r t x) * x)
`;
val _ = overload_on ("peval", ``poly_peval r``);

(* export simple case definition *)
val _ = export_rewrites ["poly_peval_def"];

(* Note:
   This maybe obtained by lifting theorems of poly_eval
   from a Ring with polynomial elements, i.e. (PolyRing r).

   However, a direct definition seems more appropriate.
   And with a strange/good result:  peval (chop p) x = peval p x
   i.e. peval "survives" the chop. This is becasuse all the * and + ensures chops already.
   Can this be exploited in the poly_eval proofs?
*)

val poly_peval_of_zero = save_thm("poly_peval_of_zero", poly_peval_def |> CONJUNCT1);
(* > val poly_peval_of_zero = |- !r x. peval [] x = |0| : thm *)

val poly_peval_cons = save_thm("poly_peval_cons", poly_peval_def |> CONJUNCT2);
(* > val poly_peval_cons = |- !r h t x. peval (h::t) x = h * |1| + peval t x * x : thm *)

(* Theorem: poly (peval p q) *)
(* Proof: by induction on p.
   Base case: poly (peval [] q)
      true by poly_peval_of_zero, poly_zero_poly.
   Step case: !q. poly p /\ poly q ==> poly (peval p q) ==>
              !h q. poly (h::p) /\ poly q ==> poly (peval (h::p) q)
      peval (h::p) q
    = h * |1| + peval p q     by poly_peval_cons
      poly (peval p q)        by induction hypothesis
      h IN R                  by weak_cons
      poly (h * |1|)          by poly_cmult_poly, poly_one_poly
    Hence poly (h * |1| + peval p q)    by poly_add_poly.
*)
val weak_peval_poly = store_thm(
  "weak_peval_poly",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ poly q ==> poly (peval p q)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: poly (peval p q) *)
(* Proof: by weak_peval_poly. *)
val poly_peval_poly = store_thm(
  "poly_peval_poly",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> poly (peval p q)``,
  rw[weak_peval_poly]);

(* export simple result *)
val _ = export_rewrites ["poly_peval_poly"];

(* A property of peval: replace X by x *)

(* Theorem: weak p ==> weak (peval p x) *)
(* Proof:
   By induction on p:
   Base case: weak (peval [] x)
     True by pmod_peval_zero.
   Step case: weak p ==> weak (peval p x) ==> !h. weak (h::p) ==> weak (peval (h::p) x)
     (peval (h::p) x)
   = h * |1| + (peval p x) * x   by poly_peval_cons
     True by weak_add_weak, weak_mult_weak, poly_chop_weak.
*)
val weak_peval_weak = store_thm(
  "weak_peval_weak",
  ``!r:'a ring. Ring r ==> !p x. weak p /\ poly x ==> weak (peval p x)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons, poly_peval_cons] >>
  `weak (peval p x)` by rw[] >>
  `weak (peval p x * x)` by rw_tac std_ss[poly_mult_def, weak_mult_weak, poly_is_weak, poly_chop_weak] >>
  `weak (h * |1|)` by rw[] >>
  rw_tac std_ss[poly_add_def, weak_add_weak, poly_chop_weak]);

val _ = export_rewrites ["weak_peval_weak"];

(* Theorem: zerop p ==> peval p x = |0| *)
(* Proof: by induction on p.
   Base case: zerop [] ==> (peval [] x = |0|)
     True by poly_peval_of_zero.
   Step case: zerop p ==> (peval p x = |0|) ==> !h. zerop (h::p) ==> (peval (h::p) x = |0|)
     Since zerop (h::p) ==> h = #0 /\ zerop p   by zero_poly_cons
     peval (h::p) x
   = h * |1| + peval p x * x    by poly_peval_cons
   = h * |1| + |0| * x          by induction hypothesis
   = #0 * |1| + |0| * x         by above
   = |0| + |0|                  by poly_cmult_lzero, poly_mult_lzero
   = |0|                        by poly_add_zero_zero
*)
val poly_peval_zerop = store_thm(
  "poly_peval_zerop",
  ``!r:'a ring. Ring r ==> !p x. zerop p /\ poly x ==> (peval p x = |0|)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[] >>
  metis_tac[poly_mult_lzero, poly_zero]);

val _ = export_rewrites ["poly_peval_zerop"];

(* Theorem: weak p ==> peval (chop p) x = peval p x *)
(* Proof:
   By induction on p.
   Base case: peval (chop []) x = peval [] x
   LHS = peval (chop []) x
       = peval [] x         by poly_chop_of_zero
       = |0|                by poly_peval_of_zero
       = chop (peval [] x)  by poly_peval_of_zero
       = RHS
   Step case: peval (chop p) x = peval p x ==>
              !h. peval (chop (h::p)) x = peval (h::p) x
   Since chop (h::p) = if zerop (h::p) then [] else h::chop p   by poly_chop_cons
   If zerop (h::p),
   LHS = peval (chop (h::p)) x
       = peval ([]) x            by poly_chop_cons
       = |0|                     by poly_peval_of_zero
       = peval (h::p) x          by poly_peval_zerop
       = RHS
   If ~zerop (h::p)
   LHS = peval (chop (h::p)) x
       = peval (h::chop p) x              by poly_chop_cons
       = h * |1| + peval (chop p) x * x   by poly_peval_cons
       = h * |1| + peval p x * x          by induction hypothesis
       = peval (h::p) x                   by poly_peval_cons
       = RHS
*)
val weak_peval_chop = store_thm(
  "weak_peval_chop",
  ``!r:'a ring. Ring r ==> !p x. weak p /\ poly x ==> (peval (chop p) x = peval p x)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[poly_chop_cons] >| [
    `peval (h::p) x = |0|` by rw_tac std_ss[poly_peval_zerop] >>
    rw[],
    `h IN R /\ weak p` by metis_tac[weak_cons] >>
    `weak (h * |1|)` by rw[] >>
    `weak (h * |1|) /\ weak (peval p x) /\ weak x /\ weak ((peval p x) o x)` by rw[] >>
    rw_tac std_ss[poly_chop_cons, poly_peval_cons, poly_peval_cons]
  ]);

(* Theorem: poly p ==> peval (chop p) x = chop (peval p x) *)
(* Proof:
     peval (chop p) x
   = peval p x            by weak_peval_chop, poly_is_weak
   = chop (peval p x)     by poly_peval_poly, poly_chop_poly
*)
val poly_peval_chop = store_thm(
  "poly_peval_chop",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ poly x ==> (peval (chop p) x = peval p x)``,
  rw[weak_peval_chop]);

(* Theorem: peval (h::t) x = chop (h o |1| || peval t x o x)  *)
(* Proof:
     peval (h::t) x
   = h * |1| + peval t x * x                        by poly_peval_cons
   = chop (h * |1| || peval t x * x)                by poly_add_def
   = chop (chop (h o |1|) || chop (peval t x o x))  by poly_cmult_def, poly_mult_def
   = chop (h o |1| || peval t x o x)                by poly_chop_add_chop
*)
val poly_peval_cons_alt = store_thm(
  "poly_peval_cons_alt",
  ``!r:'a ring. Ring r ==> !h t x. h IN R /\ poly t /\ poly x ==> (peval (h::t) x = chop (h o |1| || peval t x o x))``,
  rw_tac std_ss[poly_peval_def] >>
  `weak |1| /\ weak (h o |1|)` by rw[] >>
  `weak x /\ weak t /\ weak (peval t x)` by rw[] >>
  `h * |1| + peval t x * x = chop (h * |1| || peval t x * x)` by rw_tac std_ss[poly_add_def] >>
  `_ = chop (chop (h o |1|) || chop (peval t x o x))` by rw_tac std_ss[poly_cmult_def, poly_mult_def] >>
  rw_tac std_ss[poly_chop_add_chop, weak_mult_weak]);

(* Theorem: peval (p + q) x = (peval p x) + (peval q x) *)
(* Proof: by induction on p and q.
   Base case: peval ([] + q) x = peval [] x + peval q x
     peval ([] + q) x
   = peval q x                 by poly_add_lzero, poly_zero
   = |0| + peval q x           by poly_add_lzero
   = peval [] x + peval q x    by poly_eval_of_zero
   Step case: induct on q.
      Base case: peval ((h::p) + []) x = peval (h::p) x + peval [] x
      LHS = peval ((h::p) + []) x
          = peval (h::p) x                 by poly_add_rzero, poly_zero
          = peval (h::p) x + |0|           by poly_add_rzero
          = peval (h::p) x + peval [] x    by poly_peval_of_zero, poly_zero
          = RHS
      Step case: peval (p + q) x = peval p x + peval q x ==>
                 peval ((h::p) + (h'::q)) x = peval (h::p) x + peval (h'::q) x
      LHS = peval ((h::p) + (h'::q)) x
          = peval (chop ((h::p) || (h'::q))) x                          by poly_add_def
          = peval ((h::p) || (h'::q)) x                                 by weak_peval_chop
          = peval (h+h'::p || q) x)                                     by weak_add_cons
          = (h + h') * |1| + peval (p || q) x * x                       by poly_peval_cons
          = (h + h') * |1| + peval (chop (p || q)) x * x                by weak_peval_chop
          = (h + h') * |1| + peval (p + q) x * x                        by poly_add_def
          = (h + h') * |1| + (peval p x + peval q x) * x                by induction hypothesis
          = h * |1| + h' * |1| + (peval p x + peval q x) * x            by poly_add_cmult
          = h * |1| + h' * |1| + (peval p x * x + peval q x * x)        by poly_mult_ladd
          = h * |1| + (h' * |1| + (peval p x * x + peval q x * x))      by poly_add_assoc
          = h * |1| + (h' * |1| + peval p x * x + peval q x * x)        by poly_add_assoc
          = h * |1| + (peval p x * x + h' * |1| + peval q x * x)        by poly_add_comm
          = h * |1| + (peval p x * x + (h' * |1| + peval q x * x))      by poly_add_assoc
          = (h * |1| + peval p x * x) + (h' * |1| + peval q x * x)      by poly_add_assoc
          = peval (h::p) x + peval (h'::q) x                            by poly_peval_cons
*)
val poly_peval_add = store_thm(
  "poly_peval_add",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p + q) x = (peval p x) + (peval q x))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `poly |1| /\ poly (h * |1|) /\ poly (h' * |1|)` by rw[] >>
  `poly (peval p x) /\ poly (peval q x)` by rw[] >>
  `weak (p || q) /\ weak ((h::p) || (h'::q))` by rw[] >>
  `peval ((h::p) + (h'::q)) x = peval (chop ((h::p) || (h'::q))) x` by rw_tac std_ss[poly_add_def] >>
  `_ = peval ((h::p) || (h'::q)) x` by rw_tac std_ss[weak_peval_chop] >>
  `_ = peval (h + h'::p || q) x` by rw_tac std_ss[weak_add_cons] >>
  `_ = (h + h') * |1| + peval (p || q) x * x` by rw_tac std_ss[poly_peval_cons] >>
  `_ = (h + h') * |1| + peval (chop (p || q)) x * x` by rw_tac std_ss[weak_peval_chop] >>
  `_ = (h + h') * |1| + peval (p + q) x * x` by rw_tac std_ss[GSYM poly_add_def] >>
  `_ = (h + h') * |1| + (peval p x + peval q x) * x` by rw_tac std_ss[] >>
  `_ = h * |1| + h' * |1| + (peval p x + peval q x) * x` by rw_tac std_ss[poly_add_cmult] >>
  `_ = h * |1| + h' * |1| + (peval p x * x + peval q x * x)` by rw_tac std_ss[poly_mult_ladd] >>
  `_ = h * |1| + (h' * |1| + (peval p x * x + peval q x * x))` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_add_poly] >>
  `_ = h * |1| + (h' * |1| + peval p x * x + peval q x * x)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly] >>
  `_ = h * |1| + (peval p x * x + h' * |1| + peval q x * x)` by rw_tac std_ss[poly_add_comm, poly_mult_poly] >>
  `_ = h * |1| + (peval p x * x + (h' * |1| + peval q x * x))` by rw_tac std_ss[poly_add_assoc, poly_mult_poly] >>
  `_ = (h * |1| + peval p x * x) + (h' * |1| + peval q x * x)` by rw_tac std_ss[poly_add_assoc, poly_mult_poly, poly_add_poly] >>
  rw_tac std_ss[poly_peval_cons]);

(* Theorem: peval (-p) x = -(peval p x) *)
(* Proof:
   By induction on p.
   Base case: peval (-[]) x = -peval [] x
     peval (-[]) x
   = peval [] x       by poly_neg_zero
   = |0|              by poly_peval_of_zero
   = - |0|            by poly_neg_zero
   = - (peval [] x)   by poly_peval_of_zero
   Step case: poly p ==> (peval (-p) x = -peval p x) ==> !h. poly (h::p) ==> (peval (-(h::p)) x = -peval (h::p) x)
     peval (-(h::p)) x
   = peval (-h::-p) x                  by poly_neg_cons
   = -h * |1| + peval (-p) x * x       by poly_peval_cons
   = -h * |1| + - (peval p x) * x      by induction hypothesis
   = -(h * |1|) + -(peval p x) * x     by poly_neg_cmult
   = -(h * |1|) + -((peval p x) * x)   by poly_mult_lneg
   = -(h * |1| + peval p x * x)        by poly_neg_add
   = -(peval (h::p) x)                 by poly_peval_cons
*)
val poly_peval_neg = store_thm(
  "poly_peval_neg",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ poly x ==> (peval (-p) x = - (peval p x))``,
  rpt strip_tac >>
  Induct_on `p` >-
  metis_tac[poly_neg_zero, poly_peval_of_zero, poly_zero] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `poly |1| /\ poly (peval p x)` by rw[] >>
  `poly (h * |1|) /\ poly (peval p x * x)` by rw[] >>
  rw_tac std_ss[poly_neg_cons, poly_peval_cons, poly_neg_add, poly_mult_lneg, poly_neg_cmult]);

(* Theorem: peval (p - q) x = (peval p x) - (peval q x) *)
(* Proof:
     peval (p - q) x
   = peval (p + -q) x             by poly_sub_def
   = peval p x + peval (-q) x     by poly_peval_add
   = peval p x + -(peval q x)     by poly_peval_neg
   = peval p x - peval q x        by poly_sub_def
*)
val poly_peval_sub = store_thm(
  "poly_peval_sub",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p - q) x = (peval p x) - (peval q x))``,
  rw_tac std_ss[poly_sub_def, poly_peval_add, poly_peval_neg, poly_neg_poly]);

(* Theorem: peval (c * p) x = c * (peval p x) *)
(* Proof:
   By induction on p.
   Base case: peval (c * []) x = c * peval [] x
   LHS = peval (c * []) x
       = peval [] x          by poly_cmult_zero, poly_zero
       = |0|                 by poly_peval_of_zero
       = c * |0|             by poly_cmult_zero
       = c * peval [] x      by poly_peval_of_zero
       = RHS
   Step case: poly p ==> (peval (c * p) x = c * peval p x) ==>
              !h. poly (h::p) ==> (peval (c * (h::p)) x = c * peval (h::p) x)
   LHS = peval (c * (h::p)) x
       = peval (chop (c o (h::p))) x   by poly_cmult_def
       = peval (c o (h::p)) x          by weak_peval_chop
       = peval (c * h :: c o p) x      by weak_cmult_cons
       = (c * h) * |1| + peval (c o p) x * x          by poly_peval_cons
       = (c * h) * |1| + peval (chop (c o p)) x * x   by weak_peval_chop
       = (c * h) * |1| + peval (c * p) x * x          by poly_cmult_def
       = (c * h) * |1| + c * peval p x * x            by induction hypothesis
       = c * (h * |1|) + c * peval p x * x             by poly_cmult_cmult
       = c * (h * |1|) + c * (peval p x * x)             by poly_cmult_mult
       = c * (h * |1| + peval p x * x)                  by poly_cmult_add
       = c * peval (h::p) x                         by poly_peval_cons
       = RHS
*)
val poly_peval_cmult = store_thm(
  "poly_peval_cmult",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ poly x ==> !c. c IN R ==> (peval (c * p) x = c * (peval p x))``,
  rpt strip_tac >>
  Induct_on `p` >-
  metis_tac[poly_cmult_zero, poly_peval_of_zero, poly_zero] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `weak (c o p) /\ weak (c o (h::p))` by rw[] >>
  `poly |1| /\ poly (h * |1|) /\ poly (peval p x) /\ poly (peval p x * x)` by rw[] >>
  `peval (c * (h::p)) x = peval (chop (c o (h::p))) x` by rw_tac std_ss[poly_cmult_def] >>
  `_ = peval (c o (h::p)) x` by rw_tac std_ss[weak_peval_chop] >>
  `_ = peval (c * h :: c o p) x` by rw_tac std_ss[weak_cmult_cons] >>
  `_ = (c * h) * |1| + peval (c o p) x * x` by rw_tac std_ss[poly_peval_cons] >>
  `_ = (c * h) * |1| + peval (chop (c o p)) x * x` by rw_tac std_ss[weak_peval_chop] >>
  `_ = (c * h) * |1| + peval (c * p) x * x` by rw_tac std_ss[GSYM poly_cmult_def] >>
  rw_tac std_ss[poly_cmult_add, poly_peval_cons, poly_cmult_cmult, poly_cmult_mult]);

(* Theorem: peval (p >> n) x = (peval p x) * x ** n *)
(* Proof:
   By induction on n.
   Base case: peval (p >> 0) x = peval p x * x **
   LHS = peval (p >> 0) x
       = peval p x               by poly_shift_0
       = (peval p x) * |1|       by poly_mult_rone
       = (peval p x) * (x ** 0)  by poly_exp_0
       = RHS
   Step case: peval (p >> n) x = peval p x * x ** n ==> peval (p >> SUC n) x = peval p x * x ** SUC n
   p >> SUC n = if p = |0| then |0| else #0::p >> n
   If p = |0|
   LHS = peval ( |0| >> SUC n) x
       = peval |0| x                 by poly_shift_suc
       = |0|                         by poly_peval_of_zero
       = |0| * x ** SUC n            by poly_mult_lzero
       = (peval |0| x) * x ** SUC n  by poly_peval_of_zero
       = RHS
   If p <> |0|
   LHS = peval (p >> SUC n) x
       = peval (#0::p >> n) x      by poly_shift_suc
       = #0 * |1| + peval (p >> n) x * x   by poly_peval_cons
       = #0 * |1| + (peval p x) * x ** n * x   by induction hypothesis
       = |0| + (peval p x) * x ** n * x        by poly_cmult_lzero
       = (peval p x) * x ** n * x              by poly_add_lzero
       = (peval p x) * (x ** n * x)            by poly_mult_assoc
       = (peval p x) * x ** SUC n              by poly_exp_suc
       = RHS
*)
val poly_peval_shift = store_thm(
  "poly_peval_shift",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ poly x ==> !n. (peval (p >> n) x = (peval p x) * x ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  Cases_on `p = |0|` >| [
    (`peval (p >> SUC n) x = peval ( |0| >> SUC n) x` by rw[]) >>
    `_ = peval |0| x` by rw_tac std_ss[poly_shift_suc] >>
    `_ = |0|` by rw_tac std_ss[poly_peval_of_zero, poly_zero] >>
    `_ = |0| * x ** SUC n` by rw_tac std_ss[poly_mult_lzero] >>
    rw_tac std_ss[poly_peval_of_zero, poly_zero],
    (`peval (p >> SUC n) x = peval (#0::p >> n) x` by rw_tac std_ss[poly_shift_suc]) >>
    (`_ = #0 * |1| + peval (p >> n) x * x` by rw_tac std_ss[poly_peval_cons]) >>
    `_ = #0 * |1| + (peval p x) * x ** n * x` by rw_tac std_ss[] >>
    `_ = (peval p x) * x ** n * x` by rw[poly_cmult_lzero] >>
    `_ = (peval p x) * (x ** n * x)` by rw[poly_mult_assoc] >>
    rw_tac std_ss[poly_exp_suc]
  ]);

(* Theorem: peval (p * q) x = (peval p x) * (peval q x) *)
(* Proof:
   By induction on p.
   Base case: peval ([] * q) x = peval [] x * peval q x
   LHS = peval ([] * q) x
       = peval [] x               by poly_mult_lzero, poly_zero
       = |0|                      by poly_peval_of_zero
       = |0| * peval q x          by poly_mult_lzero
       = peval [] x * peval q x   by poly_peval_of_zero
       = RHS
   Step case: peval (p * q) x = peval p x * peval q x ==> peval ((h::p) * q) x = peval (h::p) x * peval q x
   LHS = peval ((h::p) * q) x
       = peval (h * q + (p * q) >> 1) x                         by poly_mult_cons
       = peval (h * q) x + peval ((p * q) >> 1) x               by poly_peval_add
       = h * peval q x   + peval ((p * q) >> 1) x               by poly_peval_cmult
       = h * peval q x   + (peval (p * q) x) * x ** 1           by poly_peval_shift
       = h * peval q x   + (peval (p * q) x) * x                by poly_exp_1
       = h * peval q x   + ((peval p x) * (peval q x)) * x      by induction hypothesis
       = h * peval q x   + (peval p x * x) * peval q x          by poly_mult_assoc, poly_mult_comm
       = h * ( |1| * peval q x) + (peval p x * x) * peval q x    by poly_mult_lone
       = (h * |1|) * peval q x + (peval p x * x) * peval q x    by poly_cmult_mult
       = (h * |1| + peval p x * x) * peval q x                  by poly_mult_ladd
       = peval (h::p) x * peval q x                             by poly_peval_cons
       = RHS
*)
val poly_peval_mult = store_thm(
  "poly_peval_mult",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p * q) x = (peval p x) * (peval q x))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  metis_tac[poly_mult_lzero, poly_peval_of_zero, poly_zero] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `weak (h::p) /\ weak q` by rw[] >>
  (`poly (h * q) /\ poly (p * q) /\ poly ((p * q) >> 1)` by rw[]) >>
  `poly |1| /\ poly (h * |1|)` by rw[] >>
  `poly (peval p x) /\ poly (peval q x) /\ poly (peval p x * x)` by rw[] >>
  (`peval ((h::p) * q) x = peval (h * q + (p * q) >> 1) x` by rw_tac std_ss[polyRingTheory.poly_mult_cons]) >>
  (`_ = peval (h * q) x + peval ((p * q) >> 1) x` by rw_tac std_ss[poly_peval_add]) >>
  (`_ = h * peval q x + peval ((p * q) >> 1) x` by rw_tac std_ss[poly_peval_cmult]) >>
  `_ = h * peval q x + (peval (p * q) x) * x ** 1` by rw_tac std_ss[poly_peval_shift] >>
  `_ = h * peval q x + (peval (p * q) x) * x` by rw_tac std_ss[poly_exp_1] >>
  `_ = h * peval q x + ((peval p x) * (peval q x)) * x` by rw_tac std_ss[] >>
  `_ = h * peval q x + peval p x * (peval q x * x)` by rw_tac std_ss[poly_mult_assoc] >>
  `_ = h * peval q x + peval p x * (x * peval q x)` by rw_tac std_ss[poly_mult_comm] >>
  `_ = h * peval q x + (peval p x * x) * peval q x` by rw_tac std_ss[poly_mult_assoc] >>
  `_ = h * ( |1| * peval q x) + (peval p x * x) * peval q x` by rw_tac std_ss[poly_mult_lone] >>
  `_ = (h * |1|) * peval q x + (peval p x * x) * peval q x` by rw_tac std_ss[poly_cmult_mult] >>
  rw_tac std_ss[poly_mult_ladd, poly_peval_cons]);

(* ------------------------------------------------------------------------- *)
(* More Polynomials Theorems and Evaluation.                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !x. peval |0| x = |0| *)
(* Proof: by poly_peval_of_zero, poly_zero. *)
val poly_peval_zero = store_thm(
  "poly_peval_zero",
  ``!(r:'a ring) x. peval |0| x = |0|``,
  rw[poly_peval_of_zero]);

(* export simple result *)
val _ = export_rewrites ["poly_peval_zero"];

(* Theorem: |x c. c IN R /\ c <> #0 ==> peval [c] x = [c] *)
(* Proof:
   Since c IN R /\ c <> #0,
     poly [c]                 by poly_nonzero_element_poly
     peval [c] x
   = c * |1| + peval [] x     by poly_peval_cons
   = c * |1| + |0|            by poly_peval_of_zero
   = c * |1|                  by poly_add_rzero
   = [c]                      by poly_cmult_one
*)
val poly_peval_const = store_thm(
  "poly_peval_const",
  ``!(r:'a ring) x c. Ring r /\ c IN R /\ c <> #0 ==> (peval [c] x = [c])``,
  rw[poly_peval_cons] >>
  metis_tac[poly_mult_lzero, poly_zero, poly_add_rzero, poly_nonzero_element_poly]);

(* Theorem: Ring r ==> !x. poly x ==> peval |1| x = |1| *)
(* Proof:
   If #1 = #0, |1| = [] = |0|,  by poly_zero
      hence true by poly_peval_zero.
   If #1 <> #0, |1| = [#1]      by poly_one
      peval |1| x
    = peval [#1] x              by above
    = [#1]                      by poly_peval_const
    = |1|                       by above
*)
val poly_peval_one = store_thm(
  "poly_peval_one",
  ``!r:'a ring. Ring r ==> !x. poly x ==> (peval |1| x = |1|)``,
  rw[poly_peval_def, poly_one] >>
  metis_tac[poly_mult_lzero, poly_zero, poly_add_rzero, poly_one, poly_one_poly]);

(* export simple result *)
val _ = export_rewrites ["poly_peval_one"];

(* Original to include this. *)
(* Theorem: Ring r ==> !p. poly p ==> (peval X p = p) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|            by poly_one_eq_poly_zero
      p = |0| /\ X = |0|        by poly_one_eq_zero, poly_X
      peval X p = |0| = p       by poly_peval_zero
   If #1 <> #0,
     peval X p
   = peval [#0:#1] p                by poly_X_def, need #1 <> #0.
   = #0 * |1| + (peval [#1] p) * p  by poly_peval_cons
   = |0| + (peval [#1] p) * p       by poly_cmult_lzero
   = (peval [#1] p) * p             by poly_add_lzero
   = (#1 * |1| + (peval [] p) * p   by poly_peval_cons
   = (#1 * |1| + |0|) * p           by poly_peval_of_zero
   = (#1 * |1|) * p                 by poly_add_rzero
   = |1| * p                        by poly_cmult_lone
   = p                              by poly_mult_lone
*)
val poly_peval_X = store_thm(
  "poly_peval_X",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (peval X p = p)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `(p = |0|) /\ (X = |0|)` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_X] >>
    rw[],
    rw[poly_peval_def] >>
    metis_tac[poly_zero, poly_mult_lzero, poly_add_rzero]
  ]);

(* Theorem: poly p /\ poly x ==> !n. peval (p ** n) x = (peval p x) ** n *)
(* Proof:
   By induction on n.
   Base case: peval (p ** 0) x = peval p x ** 0
     LHS = peval (p ** 0) x
         = peval |1| x         by poly_exp_0
         = |1|                 by poly_peval_one
         = (peval p x) ** 0    by poly_exp_0
         = RHS
   Step case: peval (p ** n) x = peval p x ** n ==> peval (p ** SUC n) x = peval p x ** SUC n
     LHS = peval (p ** SUC n) x
         = peval (p * p ** n) x            by poly_exp_SUC
         = (peval p x) * (peval p ** n)    by poly_peval_mult
         = (peval p x) * (peval p x) ** n  by induction hypothesis
         = (peval p x) ** SUC n            by poly_exp_SUC
         = RHS
*)
val poly_peval_exp = store_thm(
  "poly_peval_exp",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ poly x ==> !n. peval (p ** n) x = (peval p x) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[poly_peval_mult]);

(* Theorem: !p. poly p ==> peval |c| p = |c| *)
(* Proof:
   Note that |c| = chop [##c]    by poly_ring_sum_c
   If ##c = #A0,
      |c| = chop [##0]
          = chop [#0]     by ring_num_0
          = |0|           by poly_chop_const_zero
          = []            by poly_zero
      Hence  peval |c| p
           = peval [] p   by above
           = |0|          by poly_peval_of_zero
           = |c|          by above
   If ##c <> #0,
      Since ##c IN R      by ring_num_element
      hence poly [##c]    by poly_nonzero_element_poly
      |c| = chop [##c]
          = [##c]         by poly_chop_const_nonzero
      Hence  peval |c| p
           = peval [##c] p                  by above
           = ##c * |1| + (peval [] p) * p   by poly_peval_cons
           = [##c] + (peval [] p) * p       by poly_cmult_one, ##c <> #0
           = [##c] + [] * p                 by poly_peval_of_zero
           = [##c] + |0|                    by poly_mult_lzero, poly_zero
           = [##c]                          by poly_add_rzero
           = |c|                            by above
*)
val poly_peval_ring_sum = store_thm(
  "poly_peval_ring_sum",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (peval |c| p = |c|)``,
  rpt strip_tac >>
  `|c| = chop [##c]` by rw[poly_ring_sum_c] >>
  Cases_on `##c = #0` >-
  rw[] >>
  `poly [##c]` by rw[] >>
  rw[poly_peval_def, poly_ring_sum_c] >>
  metis_tac[poly_zero, poly_mult_lzero, poly_add_rzero]);

(* Theorem: poly p ==> peval (X + |c|) p = p + |c| *)
(* Proof:
     peval (X + |c|) p
   = (peval X p) + (peval |c| p)   by poly_peval_add
   = p + |c|                       by poly_peval_X, poly_peval_ring_sum
*)
val poly_peval_X_add_c = store_thm(
  "poly_peval_X_add_c",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (peval (X + |c|) p = p + |c|)``,
  rw[poly_sum_num_poly, poly_peval_add, poly_peval_X, poly_peval_ring_sum]);

(* Theorem: poly p ==> peval (X - |c|) p = p - |c| *)
(* Proof:
     peval (X - |c|) p
   = (peval X p) - (peval |c| p)   by poly_peval_sub
   = p - |c|                       by poly_peval_X, poly_peval_ring_sum
*)
val poly_peval_X_sub_c = store_thm(
  "poly_peval_X_sub_c",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (peval (X - |c|) p = p - |c|)``,
  rw[poly_sum_num_poly, poly_peval_sub, poly_peval_X, poly_peval_ring_sum]);

(* Theorem: poly p ==> !n. peval (X ** n) p = p ** n *)
(* Proof: by induction on n.
   Base case: peval (X ** 0) p = p ** 0
     LHS = peval (X ** 0) p
         = peval |1| p          by poly_X, poly_exp_0
         = |1|                  by poly_peval_one
         = p ** 0               by poly_exp_0
         = RHS
   Step case: peval (X ** n) p = p ** n ==> peval (X ** SUC n) p = p ** SUC n
     LHS = peval (X ** SUC n) p
         = peval (X * X ** n) p           by poly_exp_SUC
         = peval X p * peval (X ** n) p   by poly_peval_mult
         = peval X p * p ** n             by induction hypothesis
         = p * p ** n                     by poly_peval_X
         = p ** SUC n                     by poly_exp_SUC
         = RHS
*)
val poly_peval_X_exp = store_thm(
  "poly_peval_X_exp",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. peval (X ** n) p = p ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `peval (X ** SUC n) p = peval (X * X ** n) p` by rw[poly_exp_SUC] >>
  `_ = peval X p * peval (X ** n) p` by rw[poly_peval_mult] >>
  `_ = p * p ** n` by rw[poly_peval_X] >>
  `_ = p ** SUC n` by rw[poly_exp_SUC] >>
  rw[]);

(* Theorem: peval (X ** n + |c|) p = p ** n + |c| *)
(* Proof:
     peval (X ** n + |c|) p
   = peval (X ** n) p + peval |c| p     by poly_peval_add
   = p ** n + peval |c| p               by poly_peval_X_exp
   = p ** n + |c|                       by poly_peval_ring_sum
*)
val poly_peval_X_exp_n_add_c = store_thm(
  "poly_peval_X_exp_n_add_c",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n c:num. peval (X ** n + |c|) p = p ** n + |c|``,
  rw[poly_peval_add, poly_peval_X_exp, poly_peval_ring_sum]);

(* Theorem: peval (X ** n - |c|) p = p ** n - |c| *)
(* Proof:
     peval (X ** n - |c|) p
   = peval (X ** n) p - peval |c| p     by poly_peval_sub
   = p ** n - peval |c| p               by poly_peval_X_exp
   = p ** n - |c|                       by poly_peval_ring_sum
*)
val poly_peval_X_exp_n_sub_c = store_thm(
  "poly_peval_X_exp_n_sub_c",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n c:num. peval (X ** n - |c|) p = p ** n - |c|``,
  rw[poly_peval_sub, poly_peval_X_exp, poly_peval_ring_sum]);

(* Theorem: !p. peval p X = p *)
(* Proof: by induction on p.
   Base case: poly [] ==> (peval [] X = [])
     True by poly_peval_zero, poly_zero.
   Step case: poly p ==> (peval p X = p) ==> !h. poly (h::p) ==> (peval (h::p) X = h::p)
       poly (h::p)
   ==> h IN R /\ poly p          by poly_cons_poly
     peval (h::p) X
   = h * |1| + (peval p X) * X   by poly_peval_cons
   = h * |1| + p * X             by induction hypothesis
   If h = #0,
     p <> []                     by poly_cons_property, poly(h::p)
     h * |1| + p * X
   = |0| + p * X                 by poly_cmult_one, since h = #0,
   = p * X                       by poly_add_rzero
   = p >> 1                      by poly_mult_X
   = #0::p                       by poly_shift_1_cons, since p <> [].
   If h <> #0,
     h * |1| + p * X
   = [h] + p * X                 by poly_cmult_one, since h <> #0
   = [h] + p >> 1                by poly_mult_X
   = h::p                        by poly_cons_eq_add_shift
*)
val poly_peval_by_X = store_thm(
  "poly_peval_by_X",
  ``!(r:'a ring) p. Ring r /\ poly p ==> (peval p X = p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `peval (h::p) X = h * |1| + p * X` by rw_tac std_ss[poly_peval_cons] >>
  Cases_on `h = #0` >| [
    `p <> []` by metis_tac[poly_cons_property] >>
    `h * |1| + p * X = p * X` by rw[] >>
    metis_tac[poly_mult_X, poly_shift_1_cons, list_CASES],
    rw[poly_cmult_one, poly_mult_X, poly_cons_eq_add_shift]
  ]);

(* Theorem: peval (X + |c|) |0| = |c| *)
(* Proof:
     peval (X + |c|) |0|
   = |0| + |c|             by poly_peval_X_add_c
   = |c|                   by poly_add_lzero
*)
val poly_peval_X_add_c_by_zero = store_thm(
  "poly_peval_X_add_c_by_zero",
  ``!r:'a ring. Ring r ==> !c:num. peval (X + |c|) |0| = |c|``,
  rw[poly_peval_X_add_c]);

(* Theorem: peval (X - |c|) |0| = - |c| *)
(* Proof:
     peval (X - |c|) |0|
   = |0| - |c|             by poly_peval_X_sub_c
   = |c|                   by poly_sub_lzero
*)
val poly_peval_X_sub_c_by_zero = store_thm(
  "poly_peval_X_sub_c_by_zero",
  ``!r:'a ring. Ring r ==> !c:num. peval (X - |c|) |0| = - |c|``,
  rw[poly_peval_X_sub_c]);

(* Theorem: peval (X + |c|) |1| = |1| + |c| *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                           by poly_one_eq_poly_zero
      Note poly (X + |c|)                      by poly_X, poly_sum_num_poly
       and poly ( |1| + |c|)                   by poly_one_poly, poly_sum_num_poly
        so X + |c| = |0| and |1| + |c| = |0|   by poly_one_eq_zero
      Thus peval |0| = |0|                     by poly_peval_zero
   If #1 <> #0,
     peval (X + |c|) |1|
   = peval ([- ##c; #1]) |1|                     by poly_X_sub_c_list
   = - ##c * |1| + (peval [#1] |1|) * |1|        by poly_peval_cons
   = - ##c * |1| + peval [#1] |1|                by poly_mult_rone
   = - ##c * |1| + [#1]                          by poly_peval_const
   = - ##c * |1| + |1|                           by poly_one, #1 <> #0
   = (if - ##c = #0 then |0| else [- ##c]) + |1| by poly_cmult_one
   = - |c| + |1|                                 by poly_one_sum_n_eq
   = |1| + -|c|                                  by poly_add_comm
   = |1| - |c|
*)
val poly_peval_X_add_c_by_one = store_thm(
  "poly_peval_X_add_c_by_one",
  ``!r:'a ring. Ring r ==> !c:num. peval (X + |c|) |1| = |1| + |c|``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `!p. poly p ==> (p = |0|)` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    `poly (X + |c|) /\ poly ( |1| + |c|)` by rw[] >>
    metis_tac[poly_peval_zero],
    `peval (X + |c|) |1| = peval ([##c; #1]) |1|` by rw[poly_X_add_c_list] >>
    `_ = ##c * |1| + (peval [#1] |1|) * |1|` by rw[poly_peval_cons] >>
    `_ = ##c * |1| + peval [#1] |1|` by rw[] >>
    `_ = ##c * |1| + [#1]` by rw[poly_peval_const] >>
    `_ = ##c * |1| + |1|` by rw[poly_one] >>
    `_ = |c| + |1|` by rw[poly_cmult_one, poly_one_sum_n_eq] >>
    rw[poly_add_comm]
  ]);

(* Theorem: peval (X - |c|) |1| = |1| - |c| *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                           by poly_one_eq_poly_zero
      Note poly (X - |c|)                      by poly_X, poly_sum_num_poly
       and poly ( |1| - |c|)                   by poly_one_poly, poly_sum_num_poly
        so X - |c| = |0| and |1| - |c| = |0|   by poly_one_eq_zero
      Thus peval |0| = |0|                     by poly_peval_zero
   If #1 <> #0,
     peval (X - |c|) |1|
   = peval ([- ##c; #1]) |1|                   by poly_X_sub_c_list
   = - ##c * |1| + (peval [#1] |1|) * |1|      by poly_peval_cons
   = - ##c * |1| + peval [#1] |1|              by poly_mult_rone
   = - ##c * |1| + [#1]                        by poly_peval_const
   = - ##c * |1| + |1|                         by poly_one, #1 <> #0
   = (if - ##c = #0 then |0| else [- ##c]) + |1|   by poly_cmult_one
   = -|c| + |1|                                by poly_one_sum_n_eq
   = |1| + -|c|                                by poly_add_comm
   = |1| - |c|                                 by poly_sub_def
*)
val poly_peval_X_sub_c_by_one = store_thm(
  "poly_peval_X_sub_c_by_one",
  ``!r:'a ring. Ring r ==> !c:num. peval (X - |c|) |1| = |1| - |c|``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `!p. poly p ==> (p = |0|)` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    `poly (X - |c|) /\ poly ( |1| - |c|)` by rw[] >>
    metis_tac[poly_peval_zero],
    `peval (X - |c|) |1| = peval ([- ##c; #1]) |1|` by rw[poly_X_sub_c_list] >>
    `_ = - ##c * |1| + (peval [#1] |1|) * |1|` by rw[poly_peval_cons] >>
    `_ = - ##c * |1| + peval [#1] |1|` by rw[] >>
    `_ = - ##c * |1| + [#1]` by rw[poly_peval_const] >>
    `_ = - ##c * |1| + |1|` by rw[poly_one] >>
    `_ = -|c| + |1|` by rw[poly_cmult_one, poly_one_sum_n_eq] >>
    rw[poly_add_comm]
  ]);

(* Theorem: peval (factor c) p = if c = #0 then p else p - [c] *)
(* Proof:
     peval (factor c) p
   = peval (-c:: |1|) p                        by poly_factor_def
   = -c * |1| + (peval |1| p) * p              by poly_peval_cons
   = -c * |1| + |1| * p                        by poly_peval_one
   = -c * |1| + p                              by poly_mult_lone
   = p + -c * |1|                              by poly_add_comm
   = p + -(c * |1|)                            by poly_neg_cmult
   = p + -(if c = #0 then |0| else [c])        by poly_cmult_one
   = if c = #0 then p + -|0| else p + -[c]
   = if c = #0 then p else p - [c]             by poly_sub_def
*)
val poly_peval_factor = store_thm(
  "poly_peval_factor",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ poly p ==>
      (peval (factor c) p = if c = #0 then p else p - [c])``,
  rw[poly_factor_def] >>
  rw[poly_add_comm]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c p. c IN R /\ poly p ==> (peval (factor c) p = p - c * |1|) *)
(* Proof:
     peval (factor c) p
   = peval (X - c * |1|) p            by poly_factor_alt
   = peval (X) p - peval (c * |1|) p  by poly_peval_sub
   = p - peval (c * |1|) p            by poly_peval_X
   = p - c * (peval |1| p)            by poly_peval_cmult
   = p - c * |1|                      by poly_peval_one
*)
val poly_peval_factor_alt = store_thm(
  "poly_peval_factor_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c p. c IN R /\ poly p ==> (peval (factor c) p = p - c * |1|)``,
  rpt strip_tac >>
  `poly X /\ poly |1| /\ poly (c * |1|)` by rw[] >>
  rw_tac std_ss[poly_factor_alt, poly_peval_sub, poly_peval_X, poly_peval_cmult, poly_peval_one]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==>
            !q. poly q ==> INJ (\p. peval p q) (IMAGE factor s) univ(:'a poly) *)
(* Proof:
   By INJ_DEF, IN_IMAGE, this is to show:
   (1) x IN s ==> peval (factor x) q IN univ(:'a poly)
       Note x IN R                               by SUBSET_DEF
         so poly (factor x)                      by poly_factor_poly
        and poly (peval (factor x) q)            by poly_peval_poly
       thus peval (factor x) q IN univ(:'a poly) by IN_UNIV
   (2) x IN s /\ x' IN s /\ peval (factor x) q = peval (factor x') q ==> factor x = factor x'
       Note x IN R /\ x' IN R                    by SUBSET_DEF
        and q - x * |1| = q - x' * |1|           by poly_peval_factor_alt
       Thus     x * |1| = x' * |1|               by poly_sub_lcancel
         or X - x * |1| = X - x' * |1|           by poly_sub_lcancel
         or    factor x = factor x'              by poly_factor_alt
*)
val poly_peval_factor_map_inj = store_thm(
  "poly_peval_factor_map_inj",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==>
   !q. poly q ==> INJ (\p. peval p q) (IMAGE factor s) univ(:'a poly)``,
  rw[INJ_DEF] >>
  `x IN R /\ x' IN R` by metis_tac[SUBSET_DEF] >>
  `poly X /\ poly (x * |1|) /\ poly (x' * |1|)` by rw[] >>
  metis_tac[poly_peval_factor_alt, poly_sub_lcancel, poly_factor_alt]);

(* Theorem: peval (unity n) p = p ** n - |1| *)
(* Proof:
     peval (unity n) p
   = peval (X ** n - |1|) p           by notation
   = peval (X ** n) p - peval |1| p   by poly_peval_sub
   = p ** n - |1|                     by poly_peval_X_exp, poly_peval_one
   Or, true                           by poly_peval_X_exp_n_sub_c
*)
val poly_peval_unity = store_thm(
  "poly_peval_unity",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. peval (unity n) p = p ** n - |1|``,
  rw[poly_peval_sub, poly_peval_X_exp]);

(* Theorem: poly p ==> peval (unity 1) p = p - |1| *)
(* Proof:
     peval (unity 1) p
   = p ** 1 - |1|          by poly_peval_unity
   = p - |1|               by poly_exp_1
*)
val poly_peval_unity_1 = store_thm(
  "poly_peval_unity_1",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (peval (unity 1) p = p - |1|)``,
  rw[poly_peval_unity]);

(* Theorem: peval p |0| == chop [eval p #0]), the constant term *)
(* Proof:
   Let p = c0 + c1 * x^1 + .....
   Hence peval p |0| = c0, the constant term,
   As cj * x^j
    = cj * |0|    by poly_zero_exp, 0 < n
    = |0|         by poly_cmult_zero
   Hence result follows by poly_add_zero

   By induction on n:
   Base case: poly [] ==> (peval [] |0| == chop [eval [] #0])
     True by poly_peval_def.
   Step case: poly p ==> (peval p |0| == chop [eval p #0]) ==>
              !h. poly (h::p) ==> (peval (h::p) |0| == chop [eval (h::p) #0])
         peval (h::p) |0|
       = h * |1| + peval p |0| * |0|        by poly_peval_def
       = h * |1| + (chop [eval p #0]) * |0| by induction hypothesis
       = h * |1| + |0|                      by poly_mult_rzero
       = if h = #0 then |0| else [h]        by poly_cmult_one
       = chop [eval (h::p) #0]              by poly_eval_def, poly_chop_def
*)
val poly_peval_by_zero = store_thm(
  "poly_peval_by_zero",
  ``!r:'a ring p. Ring r /\ poly p ==> (peval p |0| = chop [eval p #0])``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[poly_peval_def]);

(* Theorem: peval p |1| == chop [eval p #1]), the sum of constant terms *)
(* Proof:
   Let p = c0 + c1 * x^1 + .....
   Hence peval p |1| = c0 + c1 + ...., the sum of constant terms,

   By induction on n:
   Base case: poly [] ==> (peval [] |1| == chop [eval [] #1])
     True by poly_peval_def.
   Step case: poly p ==> (peval p |1| == chop [eval p #1]) ==>
              !h. poly (h::p) ==> (peval (h::p) |1| == chop [eval (h::p) #1])
         peval (h::p) |1|
       = h * |1| + peval p |1| * |1|        by poly_peval_def
       = h * |1| + (chop [eval p #1]) * |1| by induction hypothesis
       = h * |1| + chop [eval p #1]         by poly_mult_rone
       = (if h = #0 then |0| else [h]) + chop [eval p #1]
                                            by poly_cmult_one
       = chop [eval (h::p) #1]              by poly_eval_def, poly_chop_def
*)
val poly_peval_by_one = store_thm(
  "poly_peval_by_one",
  ``!r:'a ring p. Ring r /\ poly p ==> (peval p |1| = chop [eval p #1])``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[poly_peval_def] >>
  `#0 IN R /\ #1 IN R /\ (- #0 = #0)` by rw[] >>
  rw[poly_peval_def] >-
  metis_tac[ring_add_rzero] >-
  metis_tac[ring_add_eq_zero, poly_eval_element] >-
  metis_tac[ring_add_rzero] >-
  rw[poly_add_weak_const_const] >>
  rw[poly_add_weak_const_const]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
