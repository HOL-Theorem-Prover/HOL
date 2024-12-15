(* ------------------------------------------------------------------------- *)
(* Formal Derivative of Polynomials.                                         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyDerivative";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory;

open polynomialTheory polyWeakTheory polyRingTheory;
open polyMonicTheory polyRootTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Formal Derivative of Polynomials Documentation                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   diff   = poly_diff r
*)
(* Definitions and Theorems (# are exported):

   Formal Derivative:
   poly_diff_def       |- (!r. diff [] = []) /\ !r h t. diff (h::t) = t + diff t >> 1
#  poly_diff_of_zero   |- !r. diff [] = []
#  poly_diff_zero      |- !r. diff |0| = |0|
   poly_diff_cons      |- !r h t. diff (h::t) = t + diff t >> 1
#  poly_diff_const     |- !r c. diff [c] = |0|
#  poly_diff_one       |- !r. Ring r ==> (diff |1| = |0|)
#  poly_diff_weak      |- !r. Ring r ==> !p. weak p ==> weak (diff p)
#  poly_diff_poly      |- !r. Ring r ==> !p. poly p ==> poly (diff p)
   poly_diff_cons_alt  |- !r. Ring r ==> !h t. poly t ==> (diff (h::t) = t + diff t * X)
#  poly_diff_sum_num   |- !r. Ring r ==> !c. diff |c| = |0|
   poly_diff_zero_poly |- !r p. zerop p ==> (diff p = |0|)
   poly_diff_chop      |- !r. Ring r ==> !p. weak p ==> (diff (chop p) = chop (diff p))
   poly_diff_add       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (diff (p + q) = diff p + diff q)
   poly_diff_neg       |- !r. Ring r ==> !p. poly p ==> (diff (-p) = -diff p)
   poly_diff_sub       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (diff (p - q) = diff p - diff q)
   poly_diff_cmult     |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> (diff (c * p) = c * diff p)
   poly_diff_shift_1   |- !r. Ring r ==> !p. poly p ==> (diff (p >> 1) = p + diff p >> 1)
   poly_diff_mult      |- !r. Ring r ==> !p q. poly p /\ poly q ==> (diff (p * q) = diff p * q + p * diff q)
   poly_diff_exp       |- !r. Ring r ==> !p. poly p ==> !n. diff (p ** n) = ##n * p ** PRE n * diff p

   Formal Derivative Examples:
#  poly_diff_X         |- !r. Ring r /\ #1 <> #0 ==> (diff X = |1|)
   poly_diff_X_exp_n   |- !r. Ring r /\ #1 <> #0 ==> !n. diff (X ** n) = ##n * X ** PRE n
   poly_diff_factor    |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (diff (factor c) = |1|)
   poly_diff_unity                 |- !r. Ring r /\ #1 <> #0 ==> !n. diff (unity n) = ##n * X ** PRE n
   poly_diff_unity_roots           |- !r. Field r ==> !n. 1 < n /\ coprime n (char r) ==>
                                          (roots (diff (unity n)) = {#0})
   poly_diff_master                |- !r. Ring r /\ #1 <> #0 ==>
                                      !n. diff (master n) = ##n * X ** PRE n - |1|
   poly_diff_master_char_exp       |- !r. Ring r /\ #1 <> #0 ==>
                                      !n. diff (master (char r ** n)) = if n = 0 then |0| else -|1|
   poly_diff_master_char_exp_roots |- !r. Ring r /\ #1 <> #0 ==>
                                      !n. 0 < n ==> (roots (diff (master (char r ** n))) = {})

*)

(* ------------------------------------------------------------------------- *)
(* Formal Derivative                                                         *)
(* ------------------------------------------------------------------------- *)

(* If X is replaced by primitive k-th root of unity, what changes are required?
   The road seems block because so far:
   * know that primitive k-th root of unity spans all the roots
   * but don't know that all the roots means k roots -- there may be multiple roots.
   * The only way to tackle multiple roots is to use formal derivatives.
*)

(* Define Formal Derivative *)
val poly_diff_def = Define `
   (poly_diff (r:'a ring) [] = []) /\
   (poly_diff (r:'a ring) (h::t) = t + (poly_diff r t) >> 1)
`;

(* overload on formal derivative *)
val _ = overload_on("diff", ``poly_diff r``);

(* Theorem: diff [] = [] *)
(* Proof: by poly_diff_def *)
val poly_diff_of_zero = store_thm(
  "poly_diff_of_zero",
  ``!r:'a ring. diff [] = []``,
  rw[poly_diff_def]);

(* Theorem: diff |0| = |0| *)
(* Proof: by poly_diff_def *)
val poly_diff_zero = store_thm(
  "poly_diff_zero",
  ``!r:'a ring. diff |0| = |0|``,
  rw[poly_diff_def]);

(* export simple results *)
val _ = export_rewrites["poly_diff_of_zero", "poly_diff_zero"];

(* Theorem: diff (h::t) = t + (diff t) >> 1 *)
(* Proof: by poly_diff_def *)
val poly_diff_cons = store_thm(
  "poly_diff_cons",
  ``!r:'a ring. !h t. diff (h::t) = t + (diff t) >> 1``,
  rw[poly_diff_def]);

(* Theorem: diff [c] = |0| *)
(* Proof: by poly_diff_def *)
val poly_diff_const = store_thm(
  "poly_diff_const",
  ``!r:'a ring. !c:'a. diff [c] = |0|``,
  rw[poly_diff_def] >>
  metis_tac[poly_add_zero_zero, poly_zero]);

(* export simple results *)
val _ = export_rewrites["poly_diff_const"];

(* Theorem: diff |1| = |0| *)
(* Proof:
   If #1 = #0, |1| = []           by poly_one
      diff |1| = diff [] = |0|    by poly_diff_zero, poly_zero
   If #1 <> #0, |1| = [#1]        by poly_one
      diff |1| = diff [#1] = |0|  by poly_diff_const
*)
val poly_diff_one = store_thm(
  "poly_diff_one",
  ``!r:'a ring. Ring r ==> (diff |1| = |0|)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_one, poly_diff_zero, poly_zero] >>
  rw_tac std_ss[poly_one, poly_diff_const]);

(* export simple results *)
val _ = export_rewrites["poly_diff_one"];

(* Theorem: weak p ==> weak (diff p) *)
(* Proof:
   By induction on p.
   Base case: weak [] ==> weak (diff [])
     True by poly_diff_of_zero, zero_poly_poly.
   Step case: weak p ==> weak (diff p) ==> !h. weak (h::p) ==> weak (diff (h::p))
     weak (h::p) ==> h IN R /\ poly p     by weak_cons
     diff (h::p) = p + (diff p) >> 1      by poly_diff_cons
     Since weak (diff p)                  by induction hypothesis
       and weak (diff p) >> 1             by poly_shift_weak
     Hence weak (diff (h::p))             by poly_add_def, weak_add_weak, poly_chop_weak
*)
val poly_diff_weak = store_thm(
  "poly_diff_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> weak (diff p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons, poly_diff_cons, poly_shift_weak, poly_add_def, weak_add_weak, poly_chop_weak]);

(* export simple results *)
val _ = export_rewrites["poly_diff_weak"];

(* Theorem: poly p ==> poly (diff p) *)
(* Proof:
   By induction on p.
   Base case: poly [] ==> poly (diff [])
     True by poly_diff_of_zero, zero_poly_poly.
   Step case: poly p ==> poly (diff p) ==> !h. poly (h::p) ==> poly (diff (h::p))
     poly (h::p) ==> h IN R /\ poly p     by poly_cons_poly
     diff (h::p) = p + (diff p) >> 1      by poly_diff_def
     Since poly (diff p)                  by induction hypothesis
       and poly (diff p) >> 1             by poly_shift_poly
     Hence poly (diff (h::p))             by poly_add_poly
*)
val poly_diff_poly = store_thm(
  "poly_diff_poly",
  ``!r:'a ring. Ring r ==> !p. poly p ==> poly (diff p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[poly_diff_def]);

(* export simple results *)
val _ = export_rewrites["poly_diff_poly"];

(* Theorem: diff (h::t) = t + (diff t)* X *)
(* Proof: by poly_diff_def, poly_mult_X *)
val poly_diff_cons_alt = store_thm(
  "poly_diff_cons_alt",
  ``!r:'a ring. Ring r ==> !h t. poly t ==> (diff (h::t) = t + (diff t)* X)``,
  rw[poly_diff_cons, poly_mult_X]);

(* Theorem: Ring r ==> diff |c| = |0| *)
(* Proof:
   Since |c| = chop [##c]      by poly_ring_sum_c
   If ##c = #0,
        diff (chop [#0])
      = diff |0|               by poly_chop_const_zero
      = |0|                    by poly_diff_zero
   If ##c <> #0,
        diff (chop [##c])
      = diff [##c]             by poly_chop_const_nonzero
      = |0|                    by poly_diff_const
*)
val poly_diff_sum_num = store_thm(
  "poly_diff_sum_num",
  ``!r:'a ring. Ring r ==> !c:num. diff |c| = |0|``,
  rw[poly_ring_sum_c] >>
  rw[]);

(* export simple results *)
val _ = export_rewrites["poly_diff_sum_num"];

(* Theorem: zerop p ==> diff p = |0| *)
(* Proof:
   By induction on p.
   Base case: zerop [] ==> (diff [] = |0|)
      True by poly_diff_of_zero, poly_zero
   Step case: zerop p ==> (diff p = |0|) ==> !h. zerop (h::p) ==> (diff (h::p) = |0|)
      zerop (h::p) ==> h = #0 /\ zerop p   by zero_poly_cons
        diff (h::p)
      = p + (diff p) >> 1     by poly_diff_cons
      = p + |0| >> 1          by induction hypothesis
      = p + |0|               by poly_shift_zero
      = |0|                   by poly_add_def, zero_poly_chop
*)
val poly_diff_zero_poly = store_thm(
  "poly_diff_zero_poly",
  ``!r:'a ring. !p. zerop p ==> (diff p = |0|)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[poly_diff_cons] >>
  rw[poly_add_def, GSYM zero_poly_chop]);

(* Theorem: weak p ==> diff (chop p) = chop (diff p) *)
(* Proof:
   By induction on p.
   Base case: weak [] ==> (diff (chop []) = chop (diff []))
     LHS = diff (chop [])
         = diff []             by poly_chop_of_zero
         = []                  by poly_diff_of_zero
         = chop []             by poly_chop_of_zero
         = chop (diff [])      by poly_diff_of_zero
         = RHS
   Step case: weak p ==> (diff (chop p) = chop (diff p)) ==>
              !h. weak (h::p) ==> (diff (chop (h::p)) = chop (diff (h::p)))
     weak (h::p) ==> h IN R /\ weak p           by weak_cons
     if zerop (h::p),
        diff (chop (h::p))
      = diff []                                 by poly_chop_cons
      = []                                      by poly_diff_of_zero
      = |0|                                     by poly_zero
      = chop |0|                                by poly_chop_zero
      = chop (diff (h::p))                      by poly_diff_zero_poly
     if ~zerop (h::p),
        diff (chop (h::p))
      = diff (h:: chop p)                       by poly_chop_cons
      = chop p + (diff (chop p)) >> 1           by poly_diff_cons
      = chop p + (chop (diff p)) >> 1           by induction hypothesis
      = chop p + chop ((diff p) >> 1)           by poly_chop_shift
      = chop (chop p || chop ((diff p) >> 1))   by poly_add_def
      = chop (p || (diff p) >> 1)               by poly_chop_add_chop
      = chop (chop (p || (diff p) >> 1))        by poly_chop_chop
      = chop (p + (diff p) >> 1)                by poly_add_def
      = chop (diff (h::p))                      by poly_diff_cons
*)
val poly_diff_chop = store_thm(
  "poly_diff_chop",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (diff (chop p) = chop (diff p))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `zerop (h::p)` >-
  rw[poly_chop_cons, poly_diff_zero_poly] >>
  `diff (chop (h::p)) = diff (h:: chop p)` by rw[poly_chop_cons] >>
  `_ = chop p + (diff (chop p)) >> 1` by rw[poly_diff_cons] >>
  `_ = chop p + (chop (diff p)) >> 1` by rw[] >>
  `_ = chop p + chop ((diff p) >> 1)` by rw[poly_chop_shift] >>
  `_ = chop (chop p || chop ((diff p) >> 1))` by rw[poly_add_def] >>
  `_ = chop (p || (diff p) >> 1)` by rw[poly_chop_add_chop] >>
  `_ = chop (chop (p || (diff p) >> 1))` by rw[poly_chop_chop] >>
  `_ = chop (p + (diff p) >> 1)` by rw_tac std_ss[poly_add_def] >>
  `_ = chop (diff (h::p))` by rw[poly_diff_cons] >>
  rw[]);

(* Theorem: poly p /\ poly q ==> (diff (p + q) = diff p + diff q) *)
(* Proof:
   By induction on p.
   Base case: !q. poly [] /\ poly q ==> (diff ([] + q) = diff [] + diff q)
     LHS = diff ([] + q)
         = diff q              by poly_add_lzero, poly_zero
         = [] + diff q         by poly_add_lzero, poly_zero
         = diff [] + diff q    by poly_diff_of_zero
         = RHS
   Step case: !q. poly p /\ poly q ==> (diff (p + q) = diff p + diff q) ==>
              !h q. poly (h::p) /\ poly q ==> (diff ((h::p) + q) = diff (h::p) + diff q)
     By induction on q.
     Base case: !h. poly (h::p) /\ poly [] ==> (diff ((h::p) + []) = diff (h::p) + diff [])
       True by poly_add_rzero, poly_diff_of_zero, poly_zero
     Step case: !q. poly p /\ poly q ==> (diff (p + q) = diff p + diff q) ==>
                !h h'. poly (h'::p) /\ poly (h::q) ==> (diff ((h'::p) + (h::q)) = diff (h'::p) + diff (h::q))
        poly (h'::p) ==> h' IN R /\ poly p      by poly_cons_poly
        poly (h::q) ==> h IN R /\ poly q        by poly_cons_poly
        LHS = diff ((h'::p) + (h::q))
            = diff (chop ((h'::p) || (h::q)))                   by poly_add_def
            = chop (diff ((h'::p) || (h::q)))                   by poly_diff_chop
            = chop (diff (h' + h :: p || q))                    by weak_add_cons
            = chop ((p || q) + (diff (p || q)) >> 1)            by poly_diff_cons
            = chop (chop ((p || q) || (diff (p || q)) >> 1))    by poly_add_def
            = chop ((p || q) || (diff (p || q)) >> 1)           by poly_chop_chop
            = chop (chop (p || q) || chop ((diff (p || q)) >> 1))   by poly_chop_add_chop
            = chop (chop (p || q) || (chop (diff (p || q))) >> 1)   by poly_chop_shift
            = chop (chop (p || q) || (diff (chop (p || q))) >> 1)   by poly_diff_chop
            = (p + q) + (diff (p + q)) >> 1                         by poly_add_def
            = (p + q) + (diff p + diff q) >> 1                  by induction hypothesis
            = (p + q) + (diff p >> 1 + diff q >> 1)             by poly_add_shift
            = ((p + q) + diff p >> 1) + diff q >> 1             by poly_add_assoc
            = (p + (q + diff p >> 1)) + diff q >> 1             by poly_add_assoc
            = (p + (diff p >> 1 + q)) + diff q >> 1             by poly_add_comm
            = ((p + diff p >> 1) + q) + diff q >> 1             by poly_add_assoc
            = (p + diff p >> 1) + (q + diff q >> 1)             by poly_add_assoc
            = diff (h'::p) + diff (h::q)                        by poly_diff_cons
            = RHS
*)
val poly_diff_add = store_thm(
  "poly_diff_add",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (diff (p + q) = diff p + diff q)``,
  ntac 2 strip_tac >>
  Induct_on `p` >-
  rw[] >>
  Induct_on `q` >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `weak (p || q) /\ weak ((diff (p || q)) >> 1)` by rw[] >>
  `poly (diff p) /\ poly (diff q) /\ poly ((diff p) >> 1) /\ poly ((diff q) >> 1)` by rw[] >>
  `diff ((h'::p) + (h::q)) = diff (chop ((h'::p) || (h::q)))` by rw_tac std_ss[poly_add_def] >>
  `_ = chop (diff ((h'::p) || (h::q)))` by rw[poly_diff_chop] >>
  `_ = chop (diff (h' + h :: p || q))` by rw[weak_add_cons] >>
  `_ = chop ((p || q) + (diff (p || q)) >> 1)` by rw_tac std_ss[poly_diff_cons] >>
  `_ = chop (chop ((p || q) || (diff (p || q)) >> 1))` by rw_tac std_ss[poly_add_def] >>
  `_ = chop ((p || q) || (diff (p || q)) >> 1)` by rw_tac std_ss[poly_chop_chop] >>
  `_ = chop (chop (p || q) || chop ((diff (p || q)) >> 1))` by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = chop (chop (p || q) || (chop (diff (p || q))) >> 1)` by rw_tac std_ss[poly_chop_shift] >>
  `_ = chop (chop (p || q) || (diff (chop (p || q))) >> 1)` by rw_tac std_ss[poly_diff_chop] >>
  `_ = (p + q) + (diff (p + q)) >> 1` by rw_tac std_ss[GSYM poly_add_def] >>
  `_ = (p + q) + (diff p + diff q) >> 1` by rw_tac std_ss[] >>
  `_ = (p + q) + (diff p >> 1 + diff q >> 1)` by rw_tac std_ss[poly_add_shift] >>
  `_ = ((p + q) + diff p >> 1) + diff q >> 1` by rw_tac std_ss[poly_add_assoc, poly_add_poly] >>
  `_ = (p + (q + diff p >> 1)) + diff q >> 1` by rw_tac std_ss[poly_add_assoc] >>
  `_ = (p + (diff p >> 1 + q)) + diff q >> 1` by rw_tac std_ss[poly_add_comm] >>
  `_ = ((p + diff p >> 1) + q) + diff q >> 1` by rw_tac std_ss[poly_add_assoc] >>
  `_ = (p + diff p >> 1) + (q + diff q >> 1)` by rw_tac std_ss[poly_add_assoc, poly_add_poly] >>
  `_ = diff (h'::p) + diff (h::q)` by rw_tac std_ss[poly_diff_cons] >>
  rw_tac std_ss[]);

(* Theorem: poly p ==> (diff (-p) = - diff p) *)
(* Proof:
   By induction on p.
   Base case: poly [] ==> (diff (-[]) = -diff [])
     LHS = diff (-[])
         = diff []           by poly_neg_of_zero
         = []                by poly_diff_of_zero
         = - []              by poly_neg_of_zero
         = - diff []         by poly_diff_of_zero
         = RHS
   Step case: poly p ==> (diff (-p) = -diff p) ==>
              !h. poly (h::p) ==> (diff (-(h::p)) = -diff (h::p))
     poly (h::p) ==> h IN R /\ poly p      by poly_cons_poly
     LHS = diff (-(h::p))
         = diff (-h::-p)              by poly_neg_cons, poly (h::p)
         = (-p) + (diff (-p)) >> 1    by poly_diff_cons
         = (-p) + (- diff p) >> 1     by induction hypothesis
         = (-p) + (- (diff p >> 1))   by poly_neg_shift
         = - (p + (diff p) >> 1)      by poly_neg_add
         = - diff (h::p)              by poly_diff_cons
         = RHS
*)
val poly_diff_neg = store_thm(
  "poly_diff_neg",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (diff (-p) = - diff p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rpt (stripDup[poly_cons_poly]) >>
  `poly (diff p >> 1)` by rw[] >>
  `diff (-(h::p)) = diff (-h::-p)` by rw[poly_neg_cons] >>
  `_ = (-p) + (diff (-p)) >> 1` by rw[poly_diff_cons] >>
  `_ = (-p) + (- diff p) >> 1` by rw[] >>
  `_ = (-p) + (- (diff p >> 1))` by rw[poly_neg_shift] >>
  `_ = - (p + diff p >> 1)` by rw[poly_neg_add] >>
  `_ = - diff (h::p)` by rw_tac std_ss[poly_diff_cons] >>
  rw_tac std_ss[]);

(* Theorem: poly p /\ poly q ==> (diff (p - q) = diff p - diff q) *)
(* Proof:
     poly q ==> poly (-q)    by poly_neg_poly
     diff (p - q)
   = diff (p + -q)           by poly_sub_def
   = diff p + diff (-q)      by poly_diff_add
   = diff p + - diff q       by poly_diff_neg
   = diff p - diff q         by poly_sub_def
*)
val poly_diff_sub = store_thm(
  "poly_diff_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (diff (p - q) = diff p - diff q)``,
  rw[poly_sub_def, poly_diff_add, poly_diff_neg]);

(* Theorem: poly p ==> !c. c IN R ==> (diff (c * p) = c * diff p) *)
(* Proof:
   By induction on p.
   Base case: poly [] ==> (diff (c * []) = c * diff [])
     LHS = diff (c * [])
         = diff []          by poly_cmult_zero, poly_zero
         = []               by poly_diff_of_zero
         = c * []           by poly_cmult_zero, poly_zero
         = c * diff []      by poly_diff_of_zero
         = RHS
   Step case: poly p ==> (diff (c * p) = c * diff p) ==>
              !h. poly (h::p) ==> (diff (c * (h::p)) = c * diff (h::p))
     poly (h::p) ==> h IN R /\ poly p                         by poly_cons_poly
     LHS = diff (c * (h::p))
         = diff (chop (c o (h::p)))                           by poly_cmult_def
         = chop (diff (c o (h::p)))                           by poly_diff_chop
         = chop (diff (c * h :: c o p))                       by weak_cmult_cons
         = chop ((c o p) + (diff (c o p)) >> 1)               by poly_diff_cons
         = chop (chop ((c o p) || (diff (c o p)) >> 1))       by poly_add_def
         = chop ((c o p) || (diff (c o p)) >> 1)              by poly_chop_chop
         = chop (chop (c o p) || chop ((diff (c o p)) >> 1))  by poly_chop_add_chop
         = chop (chop (c o p) || (chop (diff (c o p))) >> 1)  by poly_chop_shift
         = chop (chop (c o p) || (diff (chop (c o p))) >> 1)  by poly_diff_chop
         = chop ((c * p) || (diff (c * p) >> 1))              by poly_cmult_def
         = chop ((c * p) || (c * diff p) >> 1)                by induction hypothesis
         = (c * p) + (c * diff p) >> 1                        by poly_add_def
         = (c * p) + c * (diff p >> 1)                        by poly_cmult_shift
         = c * (p + diff p >> 1)                              by poly_cmult_add
         = c * diff (h::p)                                    by poly_diff_cons
         = RHS
*)
val poly_diff_cmult = store_thm(
  "poly_diff_cmult",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R ==> (diff (c * p) = c * diff p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  metis_tac[poly_cmult_zero, poly_zero, poly_diff_of_zero] >>
  rpt (stripDup[poly_cons_poly]) >>
  `weak (c o (h::p))` by rw[] >>
  `weak (c o p) /\ weak ((diff (c o p)) >> 1)` by rw[] >>
  `poly (c * p) /\ poly (diff p) /\ poly ((diff p) >> 1) /\ poly ((c * diff p) >> 1)` by rw[] >>
  `diff (c * (h::p)) = diff (chop (c o (h::p)))` by rw_tac std_ss[poly_cmult_def] >>
  `_ = chop (diff (c o (h::p)))` by rw_tac std_ss[poly_diff_chop] >>
  `_  = chop (diff (c * h :: c o p))` by rw_tac std_ss[weak_cmult_cons] >>
  `_ = chop ((c o p) + (diff (c o p)) >> 1)` by rw_tac std_ss[poly_diff_cons] >>
  `_ = chop (chop ((c o p) || (diff (c o p)) >> 1))` by rw_tac std_ss[poly_add_def] >>
  `_ = chop ((c o p) || (diff (c o p)) >> 1)` by rw_tac std_ss[poly_chop_chop] >>
  `_ = chop (chop (c o p) || chop ((diff (c o p)) >> 1))` by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = chop (chop (c o p) || (chop (diff (c o p))) >> 1)` by rw_tac std_ss[poly_chop_shift] >>
  `_ = chop (chop (c o p) || (diff (chop (c o p))) >> 1)` by rw_tac std_ss[poly_diff_chop] >>
  `_ = chop ((c * p) || (diff (c * p) >> 1))` by rw_tac std_ss[GSYM poly_cmult_def] >>
  `_ = chop ((c * p) || (c * diff p) >> 1)` by rw_tac std_ss[] >>
  `_ = (c * p) + (c * diff p) >> 1` by rw_tac std_ss[poly_add_def] >>
  `_ = (c * p) + c * (diff p >> 1)` by rw_tac std_ss[poly_cmult_shift] >>
  `_ = c * (p + diff p >> 1)` by rw_tac std_ss[poly_cmult_add] >>
  `_ = c * diff (h::p)` by rw_tac std_ss[poly_diff_cons] >>
  rw_tac std_ss[]);

(* Theorem: poly p ==> diff (p >> 1) = p + (diff p) >> 1 *)
(* Proof:
   By induction on p.
   Base case: poly [] ==> (diff ([] >> 1) = [] + diff [] >> 1)
     LHS = diff ([] >> 1)
         = diff []             by poly_shift_of_zero
         = []                  by poly_diff_of_zero
         = [] + []             by poly_add_zero_zero, poly_zero
         = [] + [] >> 1        by poly_shift_of_zero
         = [] + diff [] >> 1   by poly_diff_of_zero
         = RHS
   Step case: poly p ==> (diff (p >> 1) = p + diff p >> 1) ==>
              !h. poly (h::p) ==> (diff ((h::p) >> 1) = (h::p) + diff (h::p) >> 1)
     poly (h::p) ==> h IN R /\ poly p      by poly_cons_poly
     LHS = diff ((h::p) >> 1)
         = diff (#0::h::p)                 by poly_shift_1_cons
         = (h::p) + (diff (h::p)) >> 1     by poly_diff_cons
         = RHS
*)
val poly_diff_shift_1 = store_thm(
  "poly_diff_shift_1",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (diff (p >> 1) = p + (diff p) >> 1)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw[poly_cons_poly, poly_shift_1_cons, poly_diff_cons]);

(* Theorem: poly p /\ poly q ==> diff (p * q) = (diff p) * q + p * (diff q) *)
(* Proof:
   By induction on p.
   Base case: !q. poly [] /\ poly q ==> (diff ([] * q) = diff [] * q + [] * diff q)
     LHS = diff ([] * q)
         = diff []                     by poly_mult_lzero, poly_zero
         = []                          by poly_diff_of_zero
         = [] + []                     by poly_add_zero_zero, poly_zero
         = [] * q + [] * diff q        by poly_mult_lzero, poly_zero
         = diff [] * q + [] * diff q   by poly_diff_of_zero
         = RHS
   Step case: !q. poly p /\ poly q ==> (diff (p * q) = diff p * q + p * diff q) ==>
              !h q. poly (h::p) /\ poly q ==> (diff ((h::p) * q) = diff (h::p) * q + (h::p) * diff q)
      poly (h::p) ==> h IN R /\ poly p     by poly_cons_poly
      LHS = diff ((h::p) * q)
          = diff (h * q + (p * q) >> 1)                                      by poly_mult_cons
          = diff (h * q) + diff ((p * q) >> 1)                               by poly_diff_add
          = diff (h * q) + ((p * q) + (diff (p * q)) >> 1)                   by poly_diff_shift_1
          = h * diff q + ((p * q) + (diff (p * q)) >> 1)                     by poly_diff_cmult
          = h * diff q + (p * q) + (diff (p * q)) >> 1                       by poly_add_assoc
          = h * diff q + (p * q) + (diff p * q + p * diff q) >> 1            by induction hypothesis
          = h * diff q + p * q + ((diff p * q) >> 1 + (p * diff q) >> 1)     by poly_add_shift
          = h * diff q + p * q + ((diff p >> 1) * q + (p * diff q) >> 1)     by poly_mult_shift_comm
          = (h * diff q + p * q + (diff p >> 1) * q) + (p * diff q) >> 1     by poly_add_assoc
          = (h * diff q + (p * q + (diff p >> 1) * q)) + (p * diff q) >> 1   by poly_add_assoc
          = ((p * q + (diff p >> 1) * q) + h * diff q) + (p * diff q) >> 1   by poly_add_comm
          = p * q + (diff p >> 1) * q + (h * diff q + (p * diff q) >> 1)     by poly_add_assoc
          = p * q + (diff p >> 1) * q + (h::p) * diff q                      by poly_mult_cons
          = (p + diff p >> 1) * q + (h::p) * diff q                          by poly_mult_ladd
          = diff (h::p) * q + (h::p) * diff q                                by poly_mult_cons
          = RHS
*)
val poly_diff_mult = store_thm(
  "poly_diff_mult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (diff (p * q) = (diff p) * q + p * (diff q))``,
  ntac 2 strip_tac >>
  Induct_on `p` >-
  metis_tac[poly_mult_lzero, poly_zero, poly_diff_of_zero, poly_add_zero_zero] >>
  rpt (stripDup[poly_cons_poly]) >>
  `weak (h::p) /\ weak q /\ weak (diff q)` by rw[] >>
  `poly (h * q) /\ poly (p * q) /\ poly ((p * q) >> 1)` by rw[] >>
  `poly (diff p) /\ poly ((diff (p * q)) >> 1) /\ poly (diff p >> 1) /\ poly ((p * diff q) >> 1)` by rw[] >>
  `poly (h * diff q) /\ poly ((diff p >> 1) * q) /\ poly (diff p * q) /\ poly (p * diff q)` by rw[] >>
  `diff ((h::p) * q) = diff (h * q + (p * q) >> 1)` by rw_tac std_ss[poly_mult_cons] >>
  `_ = diff (h * q) + diff ((p * q) >> 1)` by rw_tac std_ss[poly_diff_add] >>
  `_ = diff (h * q) + ((p * q) + (diff (p * q)) >> 1)` by rw_tac std_ss[poly_diff_shift_1] >>
  `_ = h * diff q + ((p * q) + (diff (p * q)) >> 1)` by rw_tac std_ss[poly_diff_cmult] >>
  `_ = h * diff q + (p * q) + (diff (p * q)) >> 1` by rw_tac std_ss[poly_add_assoc] >>
  `_ = h * diff q + (p * q) + (diff p * q + p * diff q) >> 1` by rw_tac std_ss[] >>
  `_ = h * diff q + p * q + ((diff p * q) >> 1 + (p * diff q) >> 1)` by rw_tac std_ss[poly_add_shift] >>
  `_ = h * diff q + p * q + ((diff p >> 1) * q + (p * diff q) >> 1)` by rw_tac std_ss[poly_mult_shift_comm] >>
  `_ = (h * diff q + p * q + (diff p >> 1) * q) + (p * diff q) >> 1` by rw_tac std_ss[poly_add_assoc, poly_add_poly] >>
  `_ = (h * diff q + (p * q + (diff p >> 1) * q)) + (p * diff q) >> 1` by rw_tac std_ss[poly_add_assoc] >>
  `_ = ((p * q + (diff p >> 1) * q) + h * diff q) + (p * diff q) >> 1` by rw_tac std_ss[poly_add_comm, poly_add_poly] >>
  `_ = p * q + (diff p >> 1) * q + (h * diff q + (p * diff q) >> 1)` by rw_tac std_ss[poly_add_assoc, poly_add_poly] >>
  `_ = p * q + (diff p >> 1) * q + (h::p) * diff q` by rw_tac std_ss[poly_mult_cons] >>
  `_ = (p + diff p >> 1) * q + (h::p) * diff q` by rw_tac std_ss[poly_mult_ladd] >>
  `_ = diff (h::p) * q + (h::p) * diff q` by rw_tac std_ss[poly_diff_cons] >>
  rw_tac std_ss[]);

(* Theorem: poly p ==> !n. diff (p ** n) = ##n * (p ** PRE n) * diff p *)
(* Proof:
   By induction on n.
   Base case: diff (p ** 0) = ##0 * p ** PRE 0 * diff p
     LHS = diff (p ** 0)
         = diff |1|                       by poly_exp_0
         = |0|                            by poly_diff_one
         = #0 * (p ** PRE 0 * diff p)     by poly_cmult_lzero
         = #0 * p ** PRE 0 ** diff p      by poly_cmult_mult
         = ##0 * p ** PRE 0 * diff p      by ring_num_0
         = RHS
   Step case: diff (p ** n) = ##n * p ** PRE n * diff p ==>
              diff (p ** SUC n) = ##(SUC n) * p ** PRE (SUC n) * diff p
     to show: diff (p ** SUC n) = ##(SUC n) * p ** n * diff p    by PRE
     If n = 0,
     LHS = diff (p ** SUC 0)
         = diff (p ** 1)                 by ONE
         = diff p                        by poly_exp_1
         = |1| * diff p                  by poly_mult_lone
         = #1 * (|1| * diff p)           by poly_cmult_lone
         = #1 * |1| * diff p             by poly_cmult_mult
         = #1 * p ** 0 * diff p          by poly_exp_0
         = ##1 * p ** 0 * diff p         by ring_num_1
         = ##(SUC 0) * p ** 0 * diff p   by ONE
         = RHS
     If n <> 0,
     LHS = diff (p ** SUC n)
         = diff (p * p ** n)                                       by poly_exp_SUC
         = (diff p) * p ** n + p * diff (p ** n)                   by poly_diff_mult
         = (diff p) * p ** n + p * (##n * p ** PRE n * diff p)     by induction hypothesis
         = (diff p) * p ** n + p * (##n * (p ** PRE n * diff p))   by poly_cmult_mult
         = (diff p) * p ** n + ##n * p * (p ** PRE n * diff p)     by poly_mult_cmult
         = (diff p) * p ** n + ##n * (p * (p ** PRE n * diff p))   by poly_cmult_mult
         = (diff p) * p ** n + ##n * (p * p ** PRE n * diff p)     by poly_mult_assoc
         = (diff p) * p ** n + ##n * (p ** SUC (PRE n) * diff p)   by poly_exp_SUC
         = (diff p) * p ** n + ##n * (p ** n * diff p)             by SUC_PRE, 0 < n
         = (p ** n * diff p) + ##n * (p ** n * diff p)             by poly_mult_comm
         = #1 * (p ** n * diff p) + ##n * (p ** n * diff p)        by poly_cmult_lone
         = (#1 + ##n) * (p ** n * diff p)                          by poly_add_cmult
         = ##(SUC n) * (p ** n * diff p)                           by ring_num_SUC
         = ##(SUC n) * p ** n * diff p                             by poly_cmult_mult
         = RHS
*)
val poly_diff_exp = store_thm(
  "poly_diff_exp",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. diff (p ** n) = ##n * (p ** PRE n) * diff p``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[prim_recTheory.PRE] >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n` by decide_tac >>
  `#1 IN R /\ ##n IN R /\ ##(SUC n) IN R` by rw[] >>
  `poly (diff p) /\ poly (p ** n) /\ poly (p ** PRE n)` by rw[] >>
  `diff (p ** SUC n) = diff (p * p ** n)` by rw_tac std_ss[poly_exp_SUC] >>
  `_ = (diff p) * p ** n + p * diff (p ** n)` by rw_tac std_ss[poly_diff_mult] >>
  `_ = (diff p) * p ** n + p * (##n * p ** PRE n * diff p)` by rw_tac std_ss[] >>
  `_ = (diff p) * p ** n + p * (##n * (p ** PRE n * diff p))` by rw_tac std_ss[poly_cmult_mult] >>
  `_ = (diff p) * p ** n + ##n * p * (p ** PRE n * diff p)` by rw_tac std_ss[poly_mult_cmult, poly_mult_poly] >>
  `_ = (diff p) * p ** n + ##n * (p * (p ** PRE n * diff p))` by rw_tac std_ss[poly_cmult_mult, poly_mult_poly] >>
  `_ = (diff p) * p ** n + ##n * (p * p ** PRE n * diff p)` by rw_tac std_ss[poly_mult_assoc] >>
  `_ = (diff p) * p ** n + ##n * (p ** SUC (PRE n) * diff p)` by rw_tac std_ss[poly_exp_SUC] >>
  `_ = (diff p) * p ** n + ##n * (p ** n * diff p)` by metis_tac[SUC_PRE] >>
  `_ = (p ** n * diff p) + ##n * (p ** n * diff p)` by rw_tac std_ss[poly_mult_comm] >>
  `_ = #1 * (p ** n * diff p) + ##n * (p ** n * diff p)` by rw_tac std_ss[poly_cmult_lone, poly_mult_poly] >>
  `_ = (#1 + ##n) * (p ** n * diff p)` by rw_tac std_ss[poly_add_cmult, poly_mult_poly] >>
  `_ = ##(SUC n) * (p ** n * diff p)` by rw_tac std_ss[ring_num_SUC] >>
  `_ = ##(SUC n) * p ** n * diff p` by rw_tac std_ss[poly_cmult_mult] >>
  rw_tac std_ss[]);

(* ------------------------------------------------------------------------- *)
(* Formal Derivative Examples                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: #1 <> #0 ==> (diff X = |1|) *)
(* Proof:
     diff X
   = diff [#0;#1]               by notation
   = [#1] + (diff [#1]) >> 1    by poly_diff_cons
   = [#1] + |0| >> 1            by poly_diff_const
   = [#1] + |0|                 by poly_shift_zero
   = [#1]                       by poly_add_rzero
   = |1|                        by poly_one
*)
val poly_diff_X = store_thm(
  "poly_diff_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (diff X = |1|)``,
  rw[poly_diff_def, poly_one]);

(* export simple results *)
val _ = export_rewrites["poly_diff_X"];

(* Theorem: !n. diff (X ** n) = ##n * X ** PRE n *)
(* Proof:
     diff (X ** n)
   = ##n * (X ** PRE n) * diff X    by poly_diff_exp
   = ##n * (X ** PRE n) * |1|       by poly_diff_X
   = ##n * X ** PRE n               by poly_mult_rone
*)
val poly_diff_X_exp_n = store_thm(
  "poly_diff_X_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. diff (X ** n) = ##n * X ** PRE n``,
  rw[poly_diff_exp]);

(* Theorem: diff (factor c) = |1| *)
(* Proof:
     diff (factor c)
   = diff (X - c * |1|)        by poly_factor_alt
   = diff X - diff (c * |1|)   by poly_diff_sub
   = |1| - diff (c * |1|)      by poly_diff_X
   = |1| - c * (diff |1|)      by poly_diff_cmult
   = |1| - c * |0|             by poly_diff_one
   = |1| - |0|                 by poly_cmult_zero
   = |1|                       by poly_sub_rzero
*)
val poly_diff_factor = store_thm(
  "poly_diff_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (diff (factor c) = |1|)``,
  rpt strip_tac >>
  `diff (factor c) = diff (X - c * |1|)` by rw[poly_factor_alt] >>
  `_ = diff X - diff (c * |1|)` by rw[poly_diff_sub] >>
  `_ = |1| - diff (c * |1|)` by rw[] >>
  `_ = |1| - c * (diff |1|)` by rw[poly_diff_cmult] >>
  `_ = |1| - c * |0| ` by rw_tac std_ss[poly_diff_one] >>
  rw[]);

(* Theorem: diff (unity n) = ##n * X ** PRE n *)
(* Proof:
     diff (unity n)
   = diff (X ** n - |1|)        by notation
   = diff (X ** n) - diff |1|   by poly_diff_sub
   = diff (X ** n) - |0|        by poly_diff_one
   = diff (X ** n)              by poly_sub_rzero
   = ##n * X ** PRE n           by poly_diff_X_exp_n
*)
val poly_diff_unity = store_thm(
  "poly_diff_unity",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n.  diff (unity n) = ##n * X ** PRE n``,
  rw[poly_diff_sub, poly_diff_X_exp_n]);

(* Theorem: Field r ==> !n. 1 < n /\ coprime n (char r) ==> (roots (diff (unity n)) = {#0}) *)
(* Proof:
    Let x be a root of (diff (unity n)),
    Then #0 = eval (diff (unity n)) x         by poly_root_def
            = eval (##n * X ** PRE n) x       by poly_diff_unity
            = ##n * eval (X ** PRE n) x       by poly_eval_cmult
            = ##n * (eval X x) ** PRE n       by poly_eval_exp
            = ##n * x ** PRE n                by poly_eval_X
    Given coprime n (char r), ##n <> #0       by ring_num_char_coprime_nonzero
    Hence x ** PRE n = #0                     by field_mult_eq_zero
       or x = #0                              by field_exp_eq_zero, PRE n <> 0
    Also, eval (diff (unity n)) #0
        = ##n * #0 ** PRE n = #0              by above, ring_zero_exp, PRE n <> 0
    Hence root (diff (unity n) #0             by poly_root_def
    Thus roots (diff (unity n) = {#0}
*)
val poly_diff_unity_roots = store_thm(
  "poly_diff_unity_roots",
  ``!r:'a field. Field r ==> !n. 1 < n /\ coprime n (char r) ==> (roots (diff (unity n)) = {#0})``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `n <> 0 /\ n <> 1 /\ PRE n <> 0` by decide_tac >>
  `#0 IN R /\ ##n <> #0` by rw[ring_num_char_coprime_nonzero] >>
  `##n IN R /\ poly X /\ poly (X ** PRE n)` by rw[] >>
  rw_tac std_ss[poly_roots_def, GSPECIFICATION, EXTENSION, IN_SING, EQ_IMP_THM] >| [
    `#0 = eval (diff (unity n)) x` by rw[GSYM poly_root_def] >>
    `_ = eval (##n * X ** PRE n) x` by rw_tac std_ss[poly_diff_unity] >>
    `_ = ##n * eval (X ** PRE n) x` by rw_tac std_ss[poly_eval_cmult] >>
    `_ = ##n * (eval X x) ** PRE n` by rw_tac std_ss[poly_eval_exp] >>
    `_ = ##n * x ** PRE n` by rw_tac std_ss[poly_eval_X] >>
    `x ** PRE n = #0` by metis_tac[field_mult_eq_zero, ring_exp_element] >>
    metis_tac[field_exp_eq_zero],
    `eval (diff (unity n)) #0 = eval (##n * X ** PRE n) #0` by rw_tac std_ss[poly_diff_unity] >>
    `_ = ##n * eval (X ** PRE n) #0` by rw_tac std_ss[poly_eval_cmult] >>
    `_ = ##n * (eval X #0) ** PRE n` by rw_tac std_ss[poly_eval_exp] >>
    `_ = ##n * #0 ** PRE n` by rw_tac std_ss[poly_eval_X] >>
    `_ = ##n * #0 ` by rw_tac std_ss[ring_zero_exp] >>
    `_ = #0` by rw_tac std_ss[ring_mult_rzero] >>
    rw[poly_root_def]
  ]);

(* Theorem: diff (master n) = ##n * X ** PRE n - |1| *)
(* Proof:
     diff (master n)
   = diff (X ** n - X)          by notation
   = diff (X ** n) - diff X     by poly_diff_sub
   = diff (X ** n) - |1|        by poly_diff_X
   = ##n * X ** PRE n - |1|     by poly_diff_X_exp_n
*)
val poly_diff_master = store_thm(
  "poly_diff_master",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. diff (master n) = ##n * X ** PRE n - |1|``,
  rw[poly_diff_sub, poly_diff_X, poly_diff_X_exp_n]);

(* Theorem: diff (master (char r ** n)) = if n = 0 then |0| else - |1| *)
(* Proof:
   If n = 0,
      diff (master (char r ** 0))
    = diff (X ** (char r) ** 0 - X)     by notation
    = diff (X ** 1 - X)                 by EXP
    = diff (X - X)                      by poly_exp_1
    = diff |0|                          by poly_sub_eq
    = |0|                               by poly_diff_zero
   If n <> 0,
     diff (master (char r ** n))
   = diff (X ** (char r) ** n - X)                    by notation
   = ##(char r ** n) * X ** PRE (char r ** n) - |1|   by poly_diff_master
   = (##(char r) ** n) * X ** PRE (char r ** n) - |1| by ring_num_exp
   = (#0 ** n) * X ** PRE (char r ** n) - |1|         by char_property
   = #0 * X ** PRE (char r ** n) - |1|                by ring_zero_exp, n <> 0
   = |0| - |1|                                        by poly_cmult_lzero
   = -|1|                                             by poly_sub_lzero
*)
val poly_diff_master_char_exp = store_thm(
  "poly_diff_master_char_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. diff (master (char r ** n)) = if n = 0 then |0| else - |1|``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw_tac std_ss[EXP, poly_X, poly_exp_1, poly_sub_eq, poly_diff_zero] >>
  `diff (master (char r ** n)) = ##(char r ** n) * X ** PRE (char r ** n) - |1|` by rw[poly_diff_master] >>
  `_ = (##(char r) ** n) * X ** PRE (char r ** n) - |1|` by rw[ring_num_exp] >>
  rw[char_property, ring_zero_exp]);

(* Theorem: !n. 0 < n ==> roots (diff (master (char r ** n))) = {} *)
(* Proof:
   Since diff (master (char r ** n)) = -|1|     by poly_diff_master_char_exp, n <> 0
     and -|1| = -[#1] = [-#1] and -#1 <> #0     by poly_one_alt, poly_neg_cons, ring_neg_eq_zero
   Hence roots (-|1|) = {}                      by poly_roots_const
*)
val poly_diff_master_char_exp_roots = store_thm(
  "poly_diff_master_char_exp_roots",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> (roots (diff (master (char r ** n))) = {})``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `diff (master (char r ** n)) = -|1|` by rw[poly_diff_master_char_exp] >>
  `_ = -[#1]` by rw[poly_one_alt] >>
  `_ = [-#1]` by rw[] >>
  `-#1 <> #0` by rw[] >>
  rw[poly_roots_const]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
