(* ------------------------------------------------------------------------- *)
(* Multiple Roots of Polynomials.                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyMultiplicity";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory numberTheory
     combinatoricsTheory dividesTheory gcdTheory gcdsetTheory;

(* Get dependent theories local *)
open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyBinomialTheory polyDivisionTheory polyEvalTheory;
open polyMonicTheory;
open polyRootTheory;
open polyDividesTheory;
open polyProductTheory;
open polyIrreducibleTheory;
open polyDerivativeTheory;
open polyGCDTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Multiple Roots of Polynomials Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   multiplicity_set   = poly_root_multiplicity_set r
   multiplicity       = poly_root_multiplicity r
#  term p c           = factor c ** multiplicity p c
   separable          = poly_separable r
*)
(* Definitions and Theorems (# are exported):

   Root Multiplicity:
   poly_root_multiplicity_set_def      |- !r p c. multiplicity_set p c =
                                                  if c IN R then {m | factor c ** m pdivides p} else {}
   poly_root_multiplicity_def          |- !r p c. multiplicity p c = MAX_SET (multiplicity_set p c)
   poly_root_multiplicity_set_member   |- !r p c. c IN R ==>
                                          !n. n IN multiplicity_set p c <=> factor c ** n pdivides p
   poly_root_multiplicity_set_empty    |- !r p c. c NOTIN R ==> (multiplicity_set p c = {})
   poly_root_multiplicity_0            |- !r p c. c NOTIN R ==> (multiplicity p c = 0)
   poly_root_multiplicity_set_has_0    |- !r. Ring r ==> !p c. poly p /\ c IN R ==> 0 IN multiplicity_set p c
   poly_root_multiplicity_set_nonempty |- !r. Ring r ==> !p c. poly p /\ c IN R ==> multiplicity_set p c <> {}
   poly_root_multiplicity_set_finite   |- !r. Ring r ==>
                                          !p c. poly p /\ p <> |0| ==> FINITE (multiplicity_set p c)
   poly_root_multiplicity_lower        |- !r. Ring r ==> !p c n. poly p /\ p <> |0| /\
                                              c IN R /\ factor c ** n pdivides p ==> n <= multiplicity p c
   poly_root_multiplicity_set_has_1    |- !r. Ring r /\ #1 <> #0 ==>
                                          !p c. poly p /\ c IN roots p ==> 1 IN multiplicity_set p c
   poly_root_multiplicity_set_eq_empty |- !r. Ring r ==>
                                          !p c. poly p ==> ((multiplicity_set p c = {}) <=> c NOTIN R)
   poly_root_multiplicity_set_eq_sing  |- !r. Ring r /\ #1 <> #0 ==>
                                          !p c. poly p /\ c IN R ==>
                                                ((multiplicity_set p c = {0}) <=> c NOTIN roots p)
   poly_root_multiplicity_le        |- !r. Ring r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q pdivides p ==>
                                       !c. c IN R ==> multiplicity q c <= multiplicity p c
   poly_root_multiplicity_nonzero   |- !r. Ring r ==> !p. poly p /\ p <> |0| ==>
                                       !c. c IN roots p ==> 0 < multiplicity p c
   poly_root_multiplicity_factor    |- !r. Ring r /\ #1 <> #0 ==>
                                       !c. c IN R ==> (multiplicity (factor c) c = 1)
   poly_root_multiplicity_eq_0      |- !r. Ring r ==> !p. poly p /\ p <> |0| ==>
                                       !c. c NOTIN roots p <=> (multiplicity p c = 0)
   poly_root_multiplicity_root_property |- !r. Ring r ==>
                                           !p c. poly p /\ p <> |0| /\ c IN roots p ==> term p c pdivides p
   poly_root_multiplicity_property      |- !r. Ring r ==>
                                           !p c. poly p /\ p <> |0| /\ c IN R ==> term p c pdivides p
   poly_root_multiplicity_factor_out_root
                                    |- !r. Ring r ==> !p q. poly p /\ poly q /\ p <> |0| ==>
                                       !c. c IN R /\ (p = term p c * q) ==> c NOTIN roots q
   poly_root_multiplicity_test      |- !r. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R ==>
                                       !n. (multiplicity p c = n) <=>
                                           factor c ** n pdivides p /\ ~(factor c ** SUC n pdivides p)
   poly_root_multiplicity_term_pmonic  |- !r. Ring r ==>
                                          !p c. poly p /\ p <> |0| /\ c IN roots p ==> pmonic (term p c)
   poly_root_multiplicity_out_root     |- !r. Ring r ==>
                                          !p c. poly p /\ p <> |0| /\ c IN roots p ==>
                                                c NOTIN roots (p / term p c)
   poly_root_multiplicity_no_root      |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
                                          !c. c IN roots p /\ c NOTIN roots q ==>
                                              (multiplicity (p * q) c = multiplicity p c)
   poly_root_multiplicity_both_roots   |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
                                          !c. c IN roots p /\ c IN roots q ==>
                                              (multiplicity (p * q) c = multiplicity p c + multiplicity q c)

   poly_root_multiplicity_neg       |- !r. Ring r /\ #1 <> #0 ==>
                                       !p. poly p ==> !c. multiplicity (-p) c = multiplicity p c
   poly_root_multiplicity_cmult     |- !r. Field r ==> !p b. poly p /\ b IN R /\ b <> #0 ==>
                                       !c. multiplicity (b * p) c = multiplicity p c
   poly_root_multiplicity_mult_comm |- !r. Ring r ==> !p q x. poly p /\ poly q ==>
                                           (multiplicity (p * q) = multiplicity (q * p))
   poly_root_multiplicity_mult      |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
                                       !c. multiplicity (p * q) c = multiplicity p c + multiplicity q c
   poly_root_multiplicity_const     |- !r. Ring r ==> !b. b IN R /\ b <> #0 ==>
                                       !c. multiplicity [b] c = 0
   poly_root_multiplicity_one       |- !r. Ring r /\ #1 <> #0 ==> !c. multiplicity |1| c = 0
   poly_root_multiplicity_exp       |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                       !c n. multiplicity (p ** n) c = n * multiplicity p c

   poly_root_condition   |- !r. Ring r ==> !p. poly p /\ p <> |0| ==>
                            !c. c IN roots p <=> 0 < multiplicity p c
   poly_root_multiple    |- !r. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R ==>
                                (1 < multiplicity p c <=> root p c /\ root (diff p) c)
   poly_root_factor_out_root    |- !r. Field r ==> !p c. poly p /\ p <> |0| /\ c IN roots p ==>
                                   ?q. poly q /\ (p = term p c * q) /\ c NOTIN roots q /\
                                       (deg q = deg p - multiplicity p c)
   poly_roots_card_upper        |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                       CARD (roots p) <= SIGMA (multiplicity p) (roots p)
   poly_prod_term_roots_monic   |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                       monic (PPIMAGE (\x. term p x) (roots p))
   poly_prod_term_roots_poly    |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                       poly (PPIMAGE (\x. term p x) (roots p))
   poly_root_factor_multiplicity_finite
                                |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                       FINITE (IMAGE (\x. factor x ** multiplicity p x) (roots p))
   poly_root_factor_multiplicity_poly
                                |- !r. Field r ==>
                                   !p z. z IN IMAGE (\x. factor x ** multiplicity p x) (roots p) ==> poly z

   Separable Polynomials:
   poly_separable_def      |- !r p. separable p <=> p <> |0| /\ !c. c IN roots p ==> (multiplicity p c = 1)
   poly_separable_unity    |- !r. Field r ==> !n. 1 < n /\ coprime n (char r) ==> separable (unity n)
   poly_separable_master_char_exp       |- !r. Ring r /\ 1 < char r ==>
                                           !n. 0 < n ==> separable (master (char r ** n))
   poly_separable_divisor_separable     |- !r. Ring r ==> !p q. poly p /\ poly q /\
                                               q pdivides p /\ separable p ==> separable q
   poly_separable_factors_separable     |- !r. Ring r ==> !p q. poly p /\ poly q /\
                                                 separable (p * q) ==> separable p /\ separable q
   poly_separable_factor_roots_disjoint |- !r. Field r ==> !p q. poly p /\ poly q /\
                                               separable (p * q) ==> DISJOINT (roots p) (roots q)
*)

(* ------------------------------------------------------------------------- *)
(* Helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Root Multiplicity                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define root multiplicity *)
val poly_root_multiplicity_set_def = Define `
  poly_root_multiplicity_set (r:'a ring) (p:'a poly) (c:'a) =
    if c IN R then {m | (factor c) ** m pdivides p} else {}
`;
val poly_root_multiplicity_def = Define `
  poly_root_multiplicity (r:'a ring) (p:'a poly) (c:'a) =
    MAX_SET (poly_root_multiplicity_set r p c)
`;

(* Overload on root multiplicity *)
val _ = overload_on("multiplicity_set", ``poly_root_multiplicity_set r``);
val _ = overload_on("multiplicity", ``poly_root_multiplicity r``);

(* Theorem: c IN R ==> !n. n IN multiplicity_set p c <=> factor c ** n pdivides p *)
(* Proof: by poly_root_multiplicity_set_def *)
val poly_root_multiplicity_set_member = store_thm(
  "poly_root_multiplicity_set_member",
  ``!r:'a ring. !p c. c IN R ==> !n. n IN multiplicity_set p c <=> factor c ** n pdivides p``,
  rw[poly_root_multiplicity_set_def]);

(* Theorem: c NOTIN R ==> multiplicity_set p c = {} *)
(* Proof: by poly_root_multiplicity_set_def *)
val poly_root_multiplicity_set_empty = store_thm(
  "poly_root_multiplicity_set_empty",
  ``!r:'a ring. !p c. c NOTIN R ==> (multiplicity_set p c = {})``,
  rw_tac std_ss[poly_root_multiplicity_set_def]);

(* Theorem: c NOTIN R ==> multiplicity p c = 0 *)
(* Proof:
       c NOTIN R
   ==> poly_root_multiplicity_set p c = {}   by poly_root_multiplicity_set_empty
   ==> multiplicity p x = MAX_SET {}         by poly_root_multiplicity_def
                        = 0                  by MAX_SET_EMPTY
*)
val poly_root_multiplicity_0 = store_thm(
  "poly_root_multiplicity_0",
  ``!r:'a ring. !p c. c NOTIN R ==> (multiplicity p c = 0)``,
  metis_tac[poly_root_multiplicity_set_empty, poly_root_multiplicity_def, MAX_SET_EMPTY]);

(* Theorem: Ring r ==> !p c. poly p /\ c IN R ==> 0 IN multiplicity_set p c *)
(* Proof:
   Note factor c ** 0 = |1|     by poly_exp_0
    and |1| pdivides p          by poly_one_divides_all, poly p
   Thus 0 IN s                  by poly_root_multiplicity_set_def
*)
val poly_root_multiplicity_set_has_0 = store_thm(
  "poly_root_multiplicity_set_has_0",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ c IN R ==> 0 IN multiplicity_set p c``,
  rw[poly_one_divides_all, poly_root_multiplicity_set_def]);

(* Theorem: Ring r ==> !p c. poly p /\ c IN R ==> multiplicity_set p c <> {} *)
(* Proof:
   Let s = multiplicity_set p c.
   Note 0 IN s        by poly_root_multiplicity_set_has_0
   Thus s <> {}       by MEMBER_NOT_EMPTY
*)
val poly_root_multiplicity_set_nonempty = store_thm(
  "poly_root_multiplicity_set_nonempty",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ c IN R ==> multiplicity_set p c <> {}``,
  metis_tac[poly_root_multiplicity_set_has_0, MEMBER_NOT_EMPTY]);

(* Theorem: poly p /\ p <> |0| ==> FINITE (multiplicity_set p c) *)
(* Proof:
   Note #1 <> #0       by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   Let s = multiplicity_set p c.
   If c IN R,
      Claim: s SUBSET count (SUC (deg p))
      Proof: By poly_root_multiplicity_set_def, SUBSET_DEF, this is to show:
                factor c ** x pdivides p ==> x < SUC (deg p)
             Note monic (factor c)                by poly_factor_monic
              ==> monic (factor c ** x)           by poly_monic_exp_monic
             Note deg (factor c ** x) = x         by poly_factor_exp_deg
             If x = 0, 0 < SUC (deg p) is true    by SUC_POS
             If x <> 0, then 0 < x.
             Then monic (factor c ** x)           by poly_monic_pmonic, 0 < x
             Thus factor c ** x pdivides p        by given
              ==> x <= deg p                      by poly_divides_deg_le, p <> |0|
               or x < SUC (deg p)                 by LESS_EQ_IMP_LESS_SUC

      Since FINITE (count (SUC (deg p)))          by FINITE_COUNT
      Hence FINITE s                              by SUBSET_FINITE, Claim
   If c NOTIN R,
      Then s = {}                                 by poly_root_multiplicity_set_def
       and FINITE {}                              by FINITE_EMPTY
*)
val poly_root_multiplicity_set_finite = store_thm(
  "poly_root_multiplicity_set_finite",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ p <> |0| ==> FINITE (multiplicity_set p c)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  Cases_on `c IN R` >| [
    `s SUBSET count (SUC (deg p))` by
  (rw[poly_root_multiplicity_set_def, SUBSET_DEF, Abbr`s`] >>
    `monic (factor c ** x)` by rw[poly_factor_monic] >>
    `deg (factor c ** x) = x` by rw[poly_factor_exp_deg] >>
    Cases_on `x = 0` >-
    decide_tac >>
    `0 < x` by decide_tac >>
    `pmonic (factor c ** x)` by rw[poly_monic_pmonic] >>
    `x <= deg p` by metis_tac[poly_divides_deg_le] >>
    decide_tac
    ) >>
    metis_tac[SUBSET_FINITE, FINITE_COUNT],
    rw[poly_root_multiplicity_set_def, Abbr`s`]
  ]);

(* Theorem: poly p /\ p <> |0| /\ c IN R /\ (factor c) ** n pdivides p ==> n <= multiplicity p c *)
(* Proof:
   Let s = multiplicity_set p c.
   By poly_root_multiplicity_def, this is to show: n <= MAX_SET s.
   Note FINITE s             by poly_root_multiplicity_set_finite, p <> |0|
    and n IN s               by poly_root_multiplicity_set_def, c IN R
   Thus n <= MAX_SET s       by in_max_set
*)
val poly_root_multiplicity_lower = store_thm(
  "poly_root_multiplicity_lower",
  ``!r:'a ring. Ring r ==> !p c n. poly p /\ p <> |0| /\
       c IN R /\ (factor c) ** n pdivides p ==> n <= multiplicity p c``,
  rw_tac std_ss[poly_root_multiplicity_def] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  `FINITE s` by rw[poly_root_multiplicity_set_finite, Abbr`s`] >>
  `n IN s` by rw[poly_root_multiplicity_set_def, Abbr`s`] >>
  rw[in_max_set]);

(* Theorem: poly p /\ c IN roots p ==> 1 IN multiplicity_set p c *)
(* Proof:
        c IN roots p
    ==> c IN R /\ factor c pdivides p      by poly_root_factor
   Note poly (factor c)                    by poly_factor_poly, c IN R
    and (factor c) ** 1 pdivides p         by poly_exp_1, poly (factor c)
    ==> 1 IN multiplicity_set p c          by poly_root_multiplicity_set_def
*)
val poly_root_multiplicity_set_has_1 = store_thm(
  "poly_root_multiplicity_set_has_1",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p c. poly p /\ c IN roots p ==> 1 IN multiplicity_set p c``,
  rpt strip_tac >>
  `c IN R /\ factor c pdivides p` by metis_tac[poly_root_factor] >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  rw[poly_root_multiplicity_set_def]);

(* Theorem: poly p ==> ((multiplicity_set p c = {}) <=> (c NOTIN R)) *)
(* Proof:
   Let s = multiplicity_set p c.
   If part: s = {} ==> c NOTIN R
      By contradiction, suppose c IN R.
      Then 0 IN s        by poly_root_multiplicity_set_has_0
       ==> s <> {}       by MEMBER_NOT_EMPTY
      This contradicts with s = {}.
   Only-if part: c NOTIN R ==> s = {}
      This is true       by poly_root_multiplicity_set_empty
*)
val poly_root_multiplicity_set_eq_empty = store_thm(
  "poly_root_multiplicity_set_eq_empty",
  ``!r:'a ring. Ring r ==> !p c. poly p ==> ((multiplicity_set p c = {}) <=> (c NOTIN R))``,
  rw[EQ_IMP_THM] >-
  metis_tac[poly_root_multiplicity_set_has_0, MEMBER_NOT_EMPTY] >>
  rw[poly_root_multiplicity_set_empty]);

(* Theorem: poly p /\ c IN R ==> ((multiplicity_set p c = {0}) <=> (c NOTIN roots p)) *)
(* Proof:
   Let s = multiplicity_set p c.
   If part: s = {0} ==> c NOTIN roots p
      By contradiction, suppose c IN roots p
      Then 1 IN s      by poly_root_multiplicity_set_has_1
       ==> 1 = 0       by IN_SING
      This is a contradiction.
   Only-if part: c NOTIN roots p ==> s = {0}
      By contradiction, suppose s <> {0}.
      Note c IN R ==> s <> {}            by poly_root_multiplicity_set_nonempty, c IN R
       ==> ?n. n IN s /\ n <> 0          by ONE_ELEMENT_SING
       ==> factor c ** n pdivides p      by poly_root_multiplicity_set_member
      Note poly (factor c)               by poly_factor_poly
       Now c IN roots (factor c)         by poly_factor_roots, IN_SING
       and roots (factor c) SUBSET roots (factor c ** n)    by poly_roots_exp_subset
      also roots (factor c ** n) SUBSET roots p             by poly_divides_share_roots
       ==> c IN roots p                   by SUBSET_DEF
      This contradicts c NOTIN roots p.
*)
val poly_root_multiplicity_set_eq_sing = store_thm(
  "poly_root_multiplicity_set_eq_sing",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !p c. poly p /\ c IN R ==> ((multiplicity_set p c = {0}) <=> (c NOTIN roots p))``,
  rw[EQ_IMP_THM] >-
  metis_tac[poly_root_multiplicity_set_has_1, IN_SING, DECIDE``1 <> 0``] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  CCONTR_TAC >>
  `s <> {}` by rw[poly_root_multiplicity_set_nonempty, Abbr`s`] >>
  `?n. n IN s /\ n <> 0` by metis_tac[ONE_ELEMENT_SING] >>
  `factor c ** n pdivides p` by rw[GSYM poly_root_multiplicity_set_member, Abbr`s`] >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `c IN roots (factor c)` by rw[poly_factor_roots, IN_SING] >>
  `roots (factor c) SUBSET roots (factor c ** n)` by rw[poly_roots_exp_subset] >>
  `roots (factor c ** n) SUBSET roots p` by rw[poly_divides_share_roots] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: poly p /\ poly q /\ p <> |0| /\ q pdivides p ==>
        !c. c IN R ==> multiplicity q c <= multiplicity p c *)
(* Proof:
   Note #1 <> #0         by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
    and q <> |0|         by poly_zero_divides
   By poly_root_multiplicity_def, this is to show:
      MAX_SET (multiplicity_set q c) <= MAX_SET (multiplicity_set p c)
   By SUBSET_MAX_SET, this is to show:
   (1) q <> |0| ==> FINITE (multiplicity_set q c), true by poly_root_multiplicity_set_finite
   (2) p <> |0| ==> FINITE (multiplicity_set p c), true by poly_root_multiplicity_set_finite
   (3) multiplicity_set q c SUBSET multiplicity_set p c
       By poly_root_multiplicity_set_def, SUBSET_DEF, this is to show:
          q pdivides p /\ factor c ** x pdivides q ==> factor c ** x pdivides p
       Note poly (factor c ** x)        by poly_factor_poly, poly_exp_poly, #1 <> #0
       Thus factor c ** x pdivides p    by poly_divides_transitive
*)
val poly_root_multiplicity_le = store_thm(
  "poly_root_multiplicity_le",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q pdivides p ==>
   !c. c IN R ==> multiplicity q c <= multiplicity p c``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  rw_tac std_ss[poly_root_multiplicity_def] >>
  `q <> |0|` by metis_tac[poly_zero_divides] >>
  (irule SUBSET_MAX_SET >> rpt conj_tac) >-
  rw[poly_root_multiplicity_set_finite] >-
  rw[poly_root_multiplicity_set_finite] >>
  rw[poly_root_multiplicity_set_def, SUBSET_DEF] >>
  `poly (factor c ** x)` by rw[poly_factor_poly] >>
  metis_tac[poly_divides_transitive]);

(* Theorem: poly p /\ p <> |0| ==> !c. c IN (roots p) ==> 0 < multiplicity p c *)
(* Proof:
   Note #1 <> #0                by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   Let s = multiplicity_set p c.
   Note FINITE s                by poly_root_multiplicity_set_finite
    and 1 IN s                  by poly_root_multiplicity_set_has_1
     so 1 <= MAX_SET s          by in_max_set
     or 1 <= multiplicity p c   by poly_root_multiplicity_def
    <=> 0 < multiplicity p c    by LESS_EQ
*)
val poly_root_multiplicity_nonzero = store_thm(
  "poly_root_multiplicity_nonzero",
  ``!r:'a ring. Ring r ==> !p. poly p /\ p <> |0| ==>
   !c. c IN (roots p) ==> 0 < multiplicity p c``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  `FINITE s` by rw[poly_root_multiplicity_set_finite, Abbr`s`] >>
  `1 IN s` by rw[poly_root_multiplicity_set_has_1, Abbr`s`] >>
  `1 <= multiplicity p c` by rw[poly_root_multiplicity_def, in_max_set, Abbr`s`] >>
  decide_tac);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> (multiplicity (factor c) c = 1)  *)
(* Proof:
   Let s = multiplicity_set (factor c) c.
   By poly_root_multiplicity_def, this is to show: MAX_SET s = 1.
   Claim: s = {0; 1}
   Proof: By poly_root_multiplicity_set_def, EXTENSION, this is to show:
          (1) !x. factor c ** x pdivides factor c ==> (x = 0) \/ (x = 1)
              Note monic (factor c)          by poly_factor_monic
               and monic (factor c ** x)     by poly_monic_exp_monic
              Also deg (factor c) = 1        by poly_deg_factor
               and deg (factor c ** x) = x   by poly_monic_deg_exp
               Now deg (factor c ** x) <= deg (factor c)   by poly_monic_divides_deg_le
             Hence                   x <= 1                by above
                or x = 0 or x = 1.
          (2) factor c ** 0 pdivides factor c
              Note factor c ** 0 = |1|               by poly_exp_0
               and |1| pdivides (factor c)           by poly_one_divides_all
          (3) factor c ** 1 pdivides factor c
              Note factor c ** 1 = factor c          by poly_exp_1
               and (factor c) pdivides (factor c)    by poly_divides_reflexive
          Thus s = {0; 1}
   Thus MAX_SET s = MAX_SET {0; 1} = 1       by evaluation
*)
val poly_root_multiplicity_factor = store_thm(
  "poly_root_multiplicity_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (multiplicity (factor c) c = 1)``,
  rw[poly_root_multiplicity_def] >>
  qabbrev_tac `s = multiplicity_set (factor c) c` >>
  `s = {0; 1}` by
  (rw[poly_root_multiplicity_set_def, EXTENSION, EQ_IMP_THM, Abbr`s`] >| [
    `monic (factor c)` by rw[poly_factor_monic] >>
    `monic (factor c ** x)` by rw[poly_monic_exp_monic] >>
    `deg (factor c) = 1` by rw[poly_deg_factor] >>
    `deg (factor c ** x) = x` by rw[poly_monic_deg_exp] >>
    `deg (factor c ** x) <= deg (factor c)` by rw[poly_monic_divides_deg_le] >>
    decide_tac,
    rw[poly_factor_poly, poly_one_divides_all],
    rw[poly_factor_poly, poly_divides_reflexive]
  ]) >>
  `MAX_SET {0; 1} = 1` by EVAL_TAC >>
  rw[]);

(* Theorem: poly p /\ p <> |0| ==> !c. c NOTIN roots p <=> (multiplicity p c = 0) *)
(* Proof:
   Note #1 <> #0   by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   If part: c NOTIN roots p ==> multiplicity p c = 0
      If c IN R,
         Then multiplicity_set p c = {0}    by poly_root_multiplicity_set_eq_sing, #1 <> #0
         Thus multiplicity p c
            = MAX_SET {0}                   by poly_root_multiplicity_def
            = 0                             by MAX_SET_SING
      Otherwise, c NOTIN R, true            by poly_root_multiplicity_0

   Only-if part: multiplicity p c = 0 ==> c NOTIN roots p
      By contradiction, suppose c IN roots p.
      Then 0 < multiplicity p c             by poly_root_multiplicity_nonzero
      This contradicts multiplicity p c = 0.
*)
val poly_root_multiplicity_eq_0 = store_thm(
  "poly_root_multiplicity_eq_0",
  ``!r:'a ring. Ring r ==> !p. poly p /\ p <> |0| ==>
   !c. c NOTIN roots p <=> (multiplicity p c = 0)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    Cases_on `c IN R` >| [
      `multiplicity_set p c = {0}` by rw[poly_root_multiplicity_set_eq_sing] >>
      rw[poly_root_multiplicity_def],
      rw[poly_root_multiplicity_0]
    ],
    CCONTR_TAC >>
    qabbrev_tac `s = multiplicity_set p c` >>
    `0 < multiplicity p c` by fs[poly_root_multiplicity_nonzero] >>
    decide_tac
  ]);

(* Overload the complicated function *)
val _ = temp_overload_on("term", ``\p c. factor c ** multiplicity p c``);

(* Theorem: poly p /\ p <> |0| /\ c IN roots p ==> term p c pdivides p *)
(* Proof:
   Note #1 <> #0   by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   Let s = multiplicity_set p c.
   Note FINITE s                     by poly_root_multiplicity_set_finite, p <> |0|
    and 1 IN s                       by poly_root_multiplicity_set_has_1
     or s <> {}                      by MEMBER_NOT_EMPTY
   Thus MAX_SET s IN s               by MAX_SET_IN_SET
     or multiplicity p c IN s        by poly_root_multiplicity_def
   Note c IN roots p ==> c IN R      by poly_roots_element
    ==> (term p c) pdivides p        by poly_root_multiplicity_set_def
*)
val poly_root_multiplicity_root_property = store_thm(
  "poly_root_multiplicity_root_property",
  ``!r:'a ring. Ring r ==>
   !p c. poly p /\ p <> |0| /\ c IN roots p ==> term p c pdivides p``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  `FINITE s` by rw[poly_root_multiplicity_set_finite, Abbr`s`] >>
  `1 IN s` by rw[poly_root_multiplicity_set_has_1, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `MAX_SET s IN s` by rw[MAX_SET_IN_SET] >>
  `c IN R` by metis_tac[poly_roots_element] >>
  fs[poly_root_multiplicity_def, poly_root_multiplicity_set_def, Abbr`s`]);

(* Theorem: poly p /\ p <> |0| /\ c IN R ==> term p c pdivides p *)
(* Proof:
   If c IN roots p,
      Then term p x pdivides p     by poly_root_multiplicity_root_property
   If c NOTIN roots p,
      Note multiplicity p c = 0    by poly_root_multiplicity_eq_0
      Thus term p c = |1|          by poly_exp_1
      Then |1| pdivides p          by poly_one_divides_all
*)
val poly_root_multiplicity_property = store_thm(
  "poly_root_multiplicity_property",
  ``!r:'a ring. Ring r ==>
   !p c. poly p /\ p <> |0| /\ c IN R ==> term p c pdivides p``,
  rpt strip_tac >>
  Cases_on `c IN roots p` >-
  rw[poly_root_multiplicity_root_property] >>
  `multiplicity p c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
  `term p c = |1|` by rw[] >>
  rw[poly_one_divides_all]);

(* Theorem: poly p /\ poly q /\ p <> |0| ==>
            !c. c IN R /\ (p = term p c * q) ==> c NOTIN (roots q) *)
(* Proof:
   Note #1 <> #0                  by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   By contradiction, assume c IN (roots q).
   Let m = multiplicity p c.
   Note poly (factor c)           by poly_factor_poly
    and factor c pdivides q       by poly_root_factor, c IN roots q
    ==> ?t. poly t /\
        q = t * (factor c)        by poly_divides_def
          = (factor c) * t        by poly_mult_comm

   Thus p = (factor c) ** m * q   by given
          = (factor c) ** m * ((factor c) * t)   by above
          = (factor c) ** m * (factor c) * t     by poly_mult_assoc
          = (factor c) ** (SUC m) * t            by poly_exp_suc
    Now poly ((factor c) ** (SUC m))             by poly_exp_poly
   Thus (factor c) ** (SUC m) pdivides p         by poly_divides_def, poly_mult_comm
     ==> SUC m <= multiplicity p c               by poly_root_multiplicity_lower, p <> |0|
      or SUC m <= m, which is false.
*)
val poly_root_multiplicity_factor_out_root = store_thm(
  "poly_root_multiplicity_factor_out_root",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p <> |0| ==>
   !c. c IN R /\ (p = term p c * q) ==> c NOTIN (roots q)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  qabbrev_tac `m = multiplicity p c` >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `factor c pdivides q` by metis_tac[poly_root_factor] >>
  `?t. poly t /\ (q = t * (factor c))` by rw[GSYM poly_divides_def] >>
  `_ = (factor c) * t` by rw[poly_mult_comm] >>
  `p = (factor c) ** m * (factor c) * t` by rw[poly_mult_assoc] >>
  `_ = (factor c) ** (SUC m) * t` by rw[poly_exp_suc] >>
  `poly ((factor c) ** (SUC m))` by rw[] >>
  `(factor c) ** (SUC m) pdivides p` by metis_tac[poly_divides_def, poly_mult_comm] >>
  `SUC m <= m` by rw[poly_root_multiplicity_lower, Abbr`m`] >>
  decide_tac);

(* Theorem: poly p /\ p <> |0| /\ c IN R ==>
            !n. (multiplicity p c = n) <=> factor c ** n pdivides p /\ ~(factor c ** (SUC n) pdivides p) *)
(* Proof:
   Note #1 <> #0       by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
    and factor c ** (SUC n) = factor c * term p c    by poly_exp_SUC
   If part: (multiplicity p c = n) ==> factor c ** n pdivides p /\ ~(factor c ** (SUC n) pdivides p)
      This is to show:
   (1) c IN R ==> term p c pdivides p, true          by poly_root_multiplicity_property
   (2) c IN R ==> ~(factor c * term p c pdivides p)
       By contradiction, suppose factor c * term p c pdivides p.
       Note poly (factor c) /\ poly (term p c)       by poly_factor_poly, poly_exp_poly
       Thus ?t. poly t /\
            p = t * (factor c * term p c)            by poly_divides_def
              = (t * factor c) * term p c            by poly_mult_assoc
              = term p c * (t * factor c)            by poly_mult_comm
              = term p c * q,
            where q = t * factor c
        ==> factor c pdivides q                      by poly_divides_def
         or c IN roots q                             by poly_root_factor
        But c NOTIN roots q                          by poly_root_multiplicity_factor_out_root
        This is a contradiction.

   Only-if: factor c ** n pdivides p /\ ~(factor c ** (SUC n) pdivides p) ==> (multiplicity p c = n)
        Let m = multiplicity p c.
        Then factor c ** n pdivides p ==> n <= m     by poly_root_multiplicity_lower
        By contradiction, suppose n <> m.
        Then n <= m /\ n <> m ==> n < m, or SUC n <= m.
        Let s = multiplicity_set p c.
        Then m = MAX_SET s                           by poly_root_multiplicity_def
        Note factor c ** m pdivides p                by poly_root_multiplicity_property
         and factor c ** (SUC n) pdivides factor c ** m  by poly_divides_exp_le, SUC n <= m
         ==> factor c ** (SUC n) pdivides p              by poly_divides_transitive
        This contradicts ~(factor c ** (SUC n) pdivides p).
*)
val poly_root_multiplicity_test = store_thm(
  "poly_root_multiplicity_test",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R ==>
   !n. (multiplicity p c = n) <=> factor c ** n pdivides p /\ ~(factor c ** (SUC n) pdivides p)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_root_multiplicity_property] >-
 (CCONTR_TAC >>
  `poly (factor c) /\ poly (term p c)` by rw[poly_factor_poly] >>
  `?t. poly t /\ (p = t * (factor c * term p c))` by rw[GSYM poly_divides_def] >>
  `_ = (t * factor c) * term p c` by rw[poly_mult_assoc] >>
  `_ = term p c * (t * factor c)` by rw[poly_mult_comm] >>
  qabbrev_tac `q = t * factor c` >>
  `poly q` by rw[Abbr`q`] >>
  metis_tac[poly_divides_def, poly_root_factor, poly_root_multiplicity_factor_out_root]) >>
  qabbrev_tac `m = multiplicity p c` >>
  `n <= m` by rw[poly_root_multiplicity_lower, Abbr`m`] >>
  CCONTR_TAC >>
  `SUC n <= m` by decide_tac >>
  qabbrev_tac `s = multiplicity_set p c` >>
  `m = MAX_SET s` by rw[poly_root_multiplicity_def, Abbr`m`] >>
  `factor c ** m pdivides p` by rw[poly_root_multiplicity_property, Abbr`m`] >>
  `factor c ** (SUC n) pdivides factor c ** m` by rw[poly_factor_poly, poly_divides_exp_le] >>
  `factor c ** (SUC n) = factor c * factor c ** n` by rw[] >>
  `!k. poly (factor c ** k)` by rw[poly_factor_poly] >>
  metis_tac[poly_divides_transitive, poly_mult_poly]);

(* Theorem: poly p /\ p <> |0| /\ c IN roots p ==> pmonic (term p c) *)
(* Proof:
   Note #1 <> #0    by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
    and c IN R                              by poly_roots_element
    and monic (factor c)                    by poly_factor_monic, c IN R
    and monic (term p c)                    by poly_monic_exp_monic
   Also deg (term p c) = multiplicity p c   by poly_factor_exp_deg
    and 0 < multiplicity p c                by poly_root_multiplicity_nonzero
   Thus pmonic (term p c)                   by poly_monic_pmonic, 0 < deg (term p c)
*)
val poly_root_multiplicity_term_pmonic = store_thm(
  "poly_root_multiplicity_term_pmonic",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN roots p ==> pmonic (term p c)``,
  ntac 5 strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `monic (term p c)` by rw[poly_factor_monic] >>
  `deg (term p c) = multiplicity p c` by rw[poly_factor_exp_deg] >>
  `0 < multiplicity p c` by rw[poly_root_multiplicity_nonzero] >>
  rw[poly_monic_pmonic]);

(* Theorem: poly p /\ p <> |0| /\ c IN roots p ==> c NOTIN roots (p / (term p c)) *)
(* Proof:
   Note #1 <> #0       by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   Let q = p / term p c, m = multiplicity p c.
   By contradiction, suppose c IN roots q.
   Note c IN R                     by poly_roots_element
    and term p c pdivides p        by poly_root_multiplicity_property
    and monic (factor c)           by poly_factor_monic
    and monic (term p c)           by poly_monic_exp_monic
   Also pmonic (term p c)          by poly_root_multiplicity_term_pmonic
    ==> p = q * term p c           by poly_divides_eqn

   Then poly q                     by poly_div_poly
    and factor c pdivides q        by poly_root_factor, c IN roots q
    ==> ?t. poly t /\ (q = t * (factor c)) by poly_divides_def
        p = q * term p c                   by above
          = (t * (factor c)) * term p c    by above
          = t * (factor c * term p c)      by poly_mult_assoc
          = t * (factor c ** SUC m)        by poly_exp_SUC
   Thus factor c ** SUC m pdivides p       by poly_divides_def
   But ~factor c ** SUC m pdivides p       by poly_root_multiplicity_test
   This is a contradiction.
*)
val poly_root_multiplicity_out_root = store_thm(
  "poly_root_multiplicity_out_root",
  ``!r:'a ring. Ring r ==>
   !p c. poly p /\ p <> |0| /\ c IN roots p ==> c NOTIN roots (p / (term p c))``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  qabbrev_tac `q = p / term p c` >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `term p c pdivides p` by rw[poly_root_multiplicity_property] >>
  `monic (factor c) /\ monic (term p c)` by rw[poly_factor_monic] >>
  `pmonic (term p c)` by rw[poly_root_multiplicity_term_pmonic] >>
  `p = q * term p c` by rw[GSYM poly_divides_eqn, Abbr`q`] >>
  `poly q` by rw[poly_div_poly, Abbr`q`] >>
  `factor c pdivides q` by metis_tac[poly_root_factor] >>
  `?t. poly t /\ (q = t * (factor c))` by rw[GSYM poly_divides_def] >>
  `p = (t * (factor c)) * term p c` by rw[] >>
  `_ = t * (factor c * term p c)` by rw[poly_mult_assoc] >>
  `_ = t * (factor c ** SUC (multiplicity p c))` by rw[] >>
  `factor c ** SUC (multiplicity p c) pdivides p` by metis_tac[poly_divides_def, poly_monic_poly] >>
  metis_tac[poly_root_multiplicity_test]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
            !c. c IN roots p /\ c NOTIN roots q ==> (multiplicity (p * q) c = multiplicity p c) *)
(* Proof:
   The aim to to prove this by poly_root_multiplicity_test.
   Let n = multiplicity p c
   Note term p c = factor c ** n            by notation

   Part 1: assert nonzero poly (p * q)
   Note poly (p * q)                        by poly_mult_poly
    and p * q <> |0|                        by poly_mult_eq_zero, Field r

   Part 2: assert factor c ** n pdivides p * q
   Note c IN R                              by poly_roots_element
    and poly (factor c) /\ poly (term p c)  by poly_factor_poly, poly_exp_poly
   Also term p c pdivides p                 by poly_root_multiplicity_property
    and p pdivides p * q                    by poly_divides_def, poly_mult_comm
    ==> term p c pdivides p * q             by poly_divides_transitive

   Part 3: assert ~(factor c pdivides (p / term p c))
   Let h = p / term p c.
   Note pmonic (term p c)                   by poly_root_multiplicity_term_pmonic
     so p = h * term p c                    by poly_divides_eqn, term p c pdivides p
    and poly h                              by poly_div_poly, pmonic (term p c)
   Note c NOTIN roots h                     by poly_root_multiplicity_out_root
    ==> ~(factor c pdivides h)              by poly_root_factor, c NOTIN (roots h)
    and ~(factor c pdivides q)              by poly_root_factor, c NOTIN (roots q)

   Part 4: assert ~(factor c ** (SUC n) pdivides p * q)
   By contradiction, assume factor c ** (SUC n) pdivides p * q
   Then ?t. poly t /\
        p * q
      = t * factor c ** SUC n               by poly_divides_def
      = t * (factor c ** n * factor c)      by poly_exp_suc
      = (t * factor c ** n) * factor c      by poly_mult_assoc
      = (factor c ** n * t) * factor c      by poly_mult_comm
      = factor c ** n * (t * factor c)      by poly_mult_assoc

   But p = h * term p c, and term p c = factor c ** n.
   Thus factor c ** n * (t * factor c)
      = p * q                               by above
      = (h * factor c ** n) * q             by above
      = (factor c ** n * h) * q             by poly_mult_comm
      = factor c ** n * (h * q)             by poly_mult_assoc
   Note deg (factor c ** n) <> 0            by pmonic (term p c)
     so factor c ** n <> |0|                by poly_deg_zero
    ==> h * q = t * factor c                by poly_mult_lcancel, Field r
   Thus factor c pdivides h * q             by poly_divides_def
    But ipoly (factor c)                    by poly_factor_irreducible
    ==> factor c pdivides h \/
        factor c pdivides q                 by poly_irreducible_divides_product, Field r
   This contradicts ~(factor c pdivides h) /\ ~(factor c pdivides q) in Part 3.

   Therefore, multiplicity (p * q) c = n    by poly_root_multiplicity_test
*)
val poly_root_multiplicity_no_root = store_thm(
  "poly_root_multiplicity_no_root",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
   !c. c IN roots p /\ c NOTIN roots q ==> (multiplicity (p * q) c = multiplicity p c)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly (p * q)` by rw[] >>
  `p * q <> |0|` by metis_tac[poly_mult_eq_zero] >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `poly (factor c) /\ poly (term p c)` by rw[poly_factor_poly] >>
  `term p c pdivides p` by rw[poly_root_multiplicity_property] >>
  `p pdivides p * q` by metis_tac[poly_divides_def, poly_mult_comm] >>
  `term p c pdivides p * q` by metis_tac[poly_divides_transitive] >>
  qabbrev_tac `h = p / term p c` >>
  `pmonic (term p c)` by rw[poly_root_multiplicity_term_pmonic] >>
  `p = h * term p c` by rw[GSYM poly_divides_eqn, Abbr`h`] >>
  `poly h` by rw[poly_div_poly, Abbr`h`] >>
  `c NOTIN roots h` by metis_tac[poly_root_multiplicity_out_root] >>
  `~(factor c pdivides h)` by metis_tac[poly_root_factor] >>
  `~(factor c pdivides q)` by metis_tac[poly_root_factor] >>
  qabbrev_tac `n = multiplicity p c` >>
  `~(factor c ** SUC n pdivides p * q)` by
  (CCONTR_TAC >>
  `?t. poly t /\ (p * q = t * factor c ** SUC n)` by rw[GSYM poly_divides_def] >>
  `_ = t * factor c ** n * factor c` by rw[poly_exp_suc, poly_mult_assoc] >>
  `_ = factor c ** n * t * factor c` by rw[poly_mult_comm] >>
  `_ = factor c ** n * (t * factor c)` by rw[poly_mult_assoc] >>
  `factor c ** n * (t * factor c) = factor c ** n * h * q` by metis_tac[poly_mult_comm] >>
  `_ = factor c ** n * (h * q)` by rw[poly_mult_assoc] >>
  `factor c ** n <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
  `poly (t * factor c) /\ poly (h * q)` by rw[] >>
  `h * q = t * factor c` by prove_tac[poly_mult_lcancel] >>
  `factor c pdivides h * q` by metis_tac[poly_divides_def] >>
  `ipoly (factor c)` by rw[poly_factor_irreducible] >>
  metis_tac[poly_irreducible_divides_product]) >>
  metis_tac[poly_root_multiplicity_test]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
   !c. c IN roots p /\ c IN roots q ==> (multiplicity (p * q) c = multiplicity p x + multiplicity q c) *)
(* Proof:
   The aim to to prove this by poly_root_multiplicity_test.
   Let n = multiplicity p c, m = multiplicity q c.
   Note term p c = factor c ** n            by notation
    and term q c = factor c ** m            by notation

   Part 1: assert nonzero poly (p * q)
   Note poly (p * q)                        by poly_mult_poly
    and p * q <> |0|                        by poly_mult_eq_zero, Field r

   Part 2: assert factor c ** (n + m) pdivides p * q
   Note c IN R                              by poly_roots_element
    and poly (factor c)                     by poly_factor_poly
    and poly (term p c) /\ poly (term q c)  by poly_exp_poly
   Also term p c pdivides p                 by poly_root_multiplicity_property
    and term q c pdivides q                 by poly_root_multiplicity_property
    ==> (term p c * term q c) pdivides p * q   by poly_divides_pair
     or factor c ** (n + m) pdivides p * q     by poly_exp_add

   Part 3: assert ~(factor c pdivides (p / term p c)) and ~(factor c pdivides (q / term q c))
   Let h = p / term p c, k = q / term q c.
   Note pmonic (term p c)                   by poly_root_multiplicity_term_pmonic
    and pmonic (term q c)                   by poly_root_multiplicity_term_pmonic
     so p = h * term p c                    by poly_divides_eqn, term p c pdivides p
    and q = k * term q c                    by poly_divides_eqn, term q c pdivides q
    and poly h /\ poly k                    by poly_div_poly
   Note c NOTIN roots h                     by poly_root_multiplicity_out_root
    ==> ~(factor c pdivides h)              by poly_root_factor, c NOTIN (roots h)
    and c NOTIN roots k                     by poly_root_multiplicity_out_root
    ==> ~(factor c pdivides k)              by poly_root_factor, c NOTIN (roots k)

   Part 4: assert ~(factor c ** (SUC (n + m)) pdivides p * q)
   By contradiction, assume factor c ** (SUC (n + m)) pdivides p * q
   Then ?t. poly t /\
        p * q
      = t * factor c ** SUC (n + m)               by poly_divides_def
      = t * (factor c ** (n + m) * factor c)      by poly_exp_suc
      = (t * factor c ** (n + m)) * factor c      by poly_mult_assoc
      = (factor c ** (n + m) * t) * factor c      by poly_mult_comm
      = factor c ** (n + m) * (t * factor c)      by poly_mult_assoc

   But p = h * term p c, and term p c = factor c ** n.
   and q = k * term q c, and term q c = factor c ** m.
   Thus factor c ** (n + m) * (t * factor c)
      = p * q                                       by above
      = (h * factor c ** n) * (k * factor c ** m)   by above
      = (factor c ** n * h) * (factor c ** m * k)   by poly_mult_comm
      = (factor c ** n * h) * factor c ** m * k     by poly_mult_assoc
      = factor c ** n * (h * factor c ** m) * k     by poly_mult_assoc
      = factor c ** n * (factor c ** m * h) * k     by poly_mult_comm
      = (factor c ** n * factor c ** m) * h * k     by poly_mult_assoc
      = factor c ** n * (factor c ** m * h * k)     by poly_mult_assoc
      = factor c ** n * factor c ** m) * (h * k)    by poly_mult_assoc
      = (factor c ** (n + m)) * (h * k)             by poly_exp_add

   Note deg (factor c ** (n + m)) = n + m <> 0      by pmonic (term p c), pmonic (term q c)
     so factor c ** (n + m) <> |0|                  by poly_deg_zero
    ==> h * k = t * factor c                        by poly_mult_lcancel, Field r
   Thus factor c pdivides h * k                     by poly_divides_def
    But ipoly (factor c)                            by poly_factor_irreducible
    ==> factor c pdivides h \/
        factor c pdivides k                         by poly_irreducible_divides_product, Field r
   This contradicts ~(factor c pdivides h) /\ ~(factor c pdivides k) in Part 3.

   Therefore, multiplicity (p * q) c = (n + m)      by poly_root_multiplicity_test
*)
val poly_root_multiplicity_both_roots = store_thm(
  "poly_root_multiplicity_both_roots",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
   !c. c IN roots p /\ c IN roots q ==> (multiplicity (p * q) c = multiplicity p c + multiplicity q c)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly (p * q)` by rw[] >>
  `p * q <> |0|` by metis_tac[poly_mult_eq_zero] >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `poly (factor c) /\ poly (term p c) /\ poly (term q c)` by rw[poly_factor_poly] >>
  `term p c pdivides p /\ term q c pdivides q` by rw[poly_root_multiplicity_property] >>
  `term p c * term q c pdivides p * q` by metis_tac[poly_divides_pair] >>
  qabbrev_tac `h = p / term p c` >>
  qabbrev_tac `k = q / term q c` >>
  `pmonic (term p c) /\ pmonic (term q c)` by rw[poly_root_multiplicity_term_pmonic] >>
  `p = h * term p c` by rw[GSYM poly_divides_eqn, Abbr`h`] >>
  `q = k * term q c` by rw[GSYM poly_divides_eqn, Abbr`k`] >>
  `poly h /\ poly k` by rw[poly_div_poly, Abbr`h`, Abbr`k`] >>
  `c NOTIN roots h /\ c NOTIN roots k` by metis_tac[poly_root_multiplicity_out_root] >>
  `~(factor c pdivides h)` by metis_tac[poly_root_factor] >>
  `~(factor c pdivides k)` by metis_tac[poly_root_factor] >>
  qabbrev_tac `n = multiplicity p c` >>
  qabbrev_tac `m = multiplicity q c` >>
  `~(factor c ** SUC (n + m) pdivides p * q)` by
  (CCONTR_TAC >>
  `?t. poly t /\ (p * q = t * factor c ** SUC (n + m))` by rw[GSYM poly_divides_def] >>
  `_ = t * factor c ** (n + m) * factor c` by rw[poly_exp_suc, poly_mult_assoc] >>
  `_ = factor c ** (n + m) * t * factor c` by rw[poly_mult_comm] >>
  `_ = factor c ** (n + m) * (t * factor c)` by rw[poly_mult_assoc] >>
  `factor c ** (n + m) * (t * factor c) = (factor c ** n * h) * (factor c ** m * k)` by metis_tac[poly_mult_comm] >>
  `_ = factor c ** n * (h * factor c ** m) * k` by rw[poly_mult_assoc] >>
  `_ = factor c ** n * (factor c ** m * h) * k` by rw[poly_mult_comm] >>
  `_ = (factor c ** n * factor c ** m) * (h * k)` by rw[poly_mult_assoc] >>
  `_ = (factor c ** (n + m)) * (h * k)` by rw[poly_exp_add] >>
  `deg (factor c ** (n + m)) = n + m` by rw[poly_factor_exp_deg] >>
  `factor c ** (n + m) <> |0|` by metis_tac[poly_deg_zero, ADD_EQ_0, NOT_ZERO_LT_ZERO] >>
  `poly (t * factor c) /\ poly (h * k) /\ poly (factor c ** (n + m))` by rw[] >>
  `h * k = t * factor c` by prove_tac[poly_mult_lcancel] >>
  `factor c pdivides h * k` by metis_tac[poly_divides_def] >>
  `ipoly (factor c)` by rw[poly_factor_irreducible] >>
  metis_tac[poly_irreducible_divides_product]) >>
  `term p c * term q c = factor c ** (n + m)` by rw[poly_exp_add] >>
  metis_tac[poly_root_multiplicity_test]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p. poly p ==> !c. multiplicity (-p) c = multiplicity p c *)
(* Proof:
   If c NOTIN R, true              by poly_root_multiplicity_0
   If c IN R,
   Note !n. poly (factor c ** n)   by poly_factor_poly, poly_exp_poly
   By poly_root_multiplicity_def, this is to show:
      MAX_SET (multiplicity_set (-p) c) = MAX_SET (multiplicity_set p c)

   Claim: multiplicity_set (-p) c = multiplicity_set p c
   Proof: By poly_root_multiplicity_set_def, EXTENSION, this is to show:
     (1) {m | factor c ** m pdivides -p} SUBSET {m | factor c ** m pdivides p}
         That is, factor c ** m pdivides -p ==> factor c ** m pdivides p
         This is true by poly_divides_def, poly_neg_neg, poly_neg_mult.
     (2) {m | factor c ** m pdivides p} SUBSET {m | factor c ** m pdivides -p}
         That is, factor c ** m pdivides p ==> factor c ** m pdivides -p
         This is true by poly_divides_def, poly_neg_mult.

   Hence their MAX_SET are equal.
*)
val poly_root_multiplicity_neg = store_thm(
  "poly_root_multiplicity_neg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. poly p ==> !c. multiplicity (-p) c = multiplicity p c``,
  rpt strip_tac >>
  reverse (Cases_on `c IN R`) >-
  rw[poly_root_multiplicity_0] >>
  rw[poly_root_multiplicity_def] >>
  `!n. poly (factor c ** n)` by rw[poly_factor_poly] >>
  `multiplicity_set (-p) c = multiplicity_set p c` suffices_by rw[] >>
  rw[poly_root_multiplicity_set_def, EXTENSION, EQ_IMP_THM] >| [
    `?q. poly q /\ (-p = q * (factor c ** x))` by rw[GSYM poly_divides_def] >>
    `p = (-q) * (factor c ** x)` by metis_tac[poly_neg_neg, poly_neg_mult] >>
    metis_tac[poly_divides_def, poly_neg_poly],
    `?q. poly q /\ (p = q * (factor c ** x))` by rw[GSYM poly_divides_def] >>
    `-p = (-q) * (factor c ** x)` by metis_tac[poly_neg_mult] >>
    metis_tac[poly_divides_def, poly_neg_poly]
  ]);

(* Theorem: Field r ==> !p b. poly p /\ b IN R /\ b <> #0 ==>
  !c. multiplicity (b * p) c = multiplicity p c *)
(* Proof:
   If c NOTIN R, true        by poly_root_multiplicity_0
   If c IN R,
   By poly_root_multiplicity_def, the result follows if:
      multiplicity_set (b * p) c = multiplicity_set p c
   By poly_root_multiplicity_set_def, EXTENSION,
   Let q = factor c ** x, this is to show:
       q pdivides c * p <=> q pdivides p
   Note poly q               by poly_factor_poly, poly_exp_poly
   Thus this is true         by poly_field_divides_cmult_iff
*)
val poly_root_multiplicity_cmult = store_thm(
  "poly_root_multiplicity_cmult",
  ``!r:'a field. Field r ==> !p b. poly p /\ b IN R /\ b <> #0 ==>
   !c. multiplicity (b * p) c = multiplicity p c``,
  rpt strip_tac >>
  reverse (Cases_on `c IN R`) >-
  rw[poly_root_multiplicity_0] >>
  rw[poly_root_multiplicity_def] >>
  `multiplicity_set (b * p) c = multiplicity_set p c` suffices_by rw[] >>
  rw[poly_root_multiplicity_set_def, EXTENSION] >>
  rw[poly_field_divides_cmult_iff, poly_factor_poly]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q ==> (multiplicity (p * q) = multiplicity (q * p)) *)
(* Proof: by poly_mult_comm *)
val poly_root_multiplicity_mult_comm = store_thm(
  "poly_root_multiplicity_mult_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (multiplicity (p * q) = multiplicity (q * p))``,
  rw_tac std_ss[poly_mult_comm]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
            !c. multiplicity (p * q) c = multiplicity p c + multiplicity q c *)
(* Proof:
   If c NOTIN R, true                      by poly_root_multiplicity_0
   If c IN R,
   If c IN roots p,
      If c IN roots q, then true           by poly_root_multiplicity_both_roots
      If c NOTIN roots q,
         Note multiplicity q c = 0         by poly_root_multiplicity_eq_0
           multiplicity (p * q) c
         = multiplicity p c                by poly_root_multiplicity_no_root
         = multiplicity p c + 0            by ADD_0
   If c NOTIN roots p,
      If c IN roots q,
         Note multiplicity p c = 0         by poly_root_multiplicity_eq_0
           multiplicity (p * q) c
         = multiplicity (q * p) c          by poly_root_multiplicity_mult_comm
         = multiplicity q c                by poly_root_multiplicity_no_root
         = 0 + multiplicity q c            by ADD
      If c NOTIN roots q,
         Note multiplicity p c = 0         by poly_root_multiplicity_eq_0
         Note multiplicity q c = 0         by poly_root_multiplicity_eq_0
         Also roots (p * q)
            = (roots p) UNION (roots q)    by poly_roots_mult
          ==> c NOTIN roots (p * q)        by IN_UNION, Field r
          Now p * q <> |0|                 by poly_mult_eq_zero, Field r
         Thus multiplicity (p * q) c = 0   by poly_root_multiplicity_eq_0
*)
val poly_root_multiplicity_mult = store_thm(
  "poly_root_multiplicity_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
   !c. multiplicity (p * q) c = multiplicity p c + multiplicity q c``,
  rpt strip_tac >>
  reverse (Cases_on `c IN R`) >-
  rw[poly_root_multiplicity_0] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Cases_on `c IN roots p` >| [
    Cases_on `c IN roots q` >-
    rw[poly_root_multiplicity_both_roots] >>
    `multiplicity q c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
    rw[poly_root_multiplicity_no_root],
    Cases_on `c IN roots q` >| [
      `multiplicity p c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
      `multiplicity (q * p) c = multiplicity q c` by rw[poly_root_multiplicity_no_root] >>
      metis_tac[poly_root_multiplicity_mult_comm, ADD],
      `multiplicity p c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
      `multiplicity q c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
      `c NOTIN roots (p * q)` by rw[poly_roots_mult] >>
      `p * q <> |0|` by metis_tac[poly_mult_eq_zero] >>
      `multiplicity (p * q) c = 0` by rw[GSYM poly_root_multiplicity_eq_0] >>
      decide_tac
    ]
  ]);

(* Theorem: b IN R /\ b <> #0 ==> !c. multiplicity [b] c = 0 *)
(* Proof:
   If c NOTIN R, true            by poly_root_multiplicity_0
   If c IN R,
   Note poly [b]                 by poly_nonzero_element_poly
    and [b] <> |0|               by poly_zero, #1 <> #0
    and roots [b] = {}           by poly_roots_const, b <> #0
   Thus ~(x IN roots [b])        by MEMBER_NOT_EMPTY
    ==> multiplicity [b] c = 0   by poly_root_multiplicity_eq_0
*)
val poly_root_multiplicity_const = store_thm(
  "poly_root_multiplicity_const",
  ``!r:'a ring. Ring r ==> !b. b IN R /\ b <> #0 ==> !c. multiplicity [b] c = 0``,
  rpt strip_tac >>
  reverse (Cases_on `c IN R`) >-
  rw[poly_root_multiplicity_0] >>
  `poly [b] /\ [b] <> |0|` by rw[] >>
  `roots [b] = {}` by rw[poly_roots_const] >>
  `~(c IN roots [b])` by rw[] >>
  rw[GSYM poly_root_multiplicity_eq_0]);;

(* Theorem: multiplicity |1| c = 0 *)
(* Proof:
     multiplicity |1| c
   = multiplicity [#1] c    by poly_one, #1 <> #0
   = 1                      by poly_root_multiplicity_const, #1 IN R
*)
val poly_root_multiplicity_one = store_thm(
  "poly_root_multiplicity_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. multiplicity |1| c = 0``,
  rw[poly_root_multiplicity_const, poly_one]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            !c n. multiplicity (p ** n) c = n * multiplicity p c *)
(* Proof:
   By induction on n.
   Base: multiplicity (p ** 0) c = 0 * multiplicity p c
         multiplicity (p ** 0) c
       = multiplicity |1| c          by poly_exp_0
       = 0                           by poly_root_multiplicity_one
       = 0 * multiplicity p c        by MULT
   Step: multiplicity (p ** n) c = n * multiplicity p c ==>
         multiplicity (p ** SUC n) c = SUC n * multiplicity p c
       Note p ** n <> |0|            by poly_exp_eq_zero
         multiplicity (p ** SUC n) c
       = multiplicity (p ** n * p) c                  by poly_exp_suc
       = multiplicity (p ** n) c + multiplicity p c   by poly_root_multiplicity_mult, p ** n <> |0|
       = n * multiplicity p c + multiplicity p c      by induction hypothesis
       = SUC n * multiplicity p c                     by MULT
*)
val poly_root_multiplicity_exp = store_thm(
  "poly_root_multiplicity_exp",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
   !c n. multiplicity (p ** n) c = n * multiplicity p c``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[poly_root_multiplicity_one] >>
  `p ** n <> |0|` by metis_tac[poly_exp_eq_zero] >>
  `multiplicity (p ** SUC n) c = multiplicity (p ** n * p) c` by rw[poly_exp_suc] >>
  `_ = multiplicity (p ** n) c + multiplicity p c` by rw[poly_root_multiplicity_mult] >>
  `_ = n * multiplicity p c + multiplicity p c` by rw[] >>
  `_ = SUC n * multiplicity p c` by rw[MULT] >>
  rw[]);

(* Theorem: poly p /\ p <> |0| ==> !c. c IN roots p <=> 0 < multiplicity p c *)
(* Proof:
   Note c NOTIN roots p <=> multiplicity p c = 0    by poly_root_multiplicity_eq_0
   Thus    c IN roots p <=> multiplicity p c <> 0   by negation on both sides
    or     c IN roots p <=> 0 < multiplicity p c    by arithmetic
*)
val poly_root_condition = store_thm(
  "poly_root_condition",
  ``!r:'a ring. Ring r ==> !p. poly p /\ p <> |0| ==>
   !c. c IN roots p <=> 0 < multiplicity p c``,
  metis_tac[poly_root_multiplicity_eq_0, NOT_ZERO_LT_ZERO]);

(* Theorem: poly p /\ p <> |0| /\ c IN R ==>
            (1 < multiplicity p c <=> root p c /\ root (diff p) c) *)
(* Proof:
   Note #1 <> #0             by poly_one_eq_poly_zero, poly_one_eq_zero, p <> |0|
   Let s = multiplicity_set p c.
   Note FINITE s             by poly_root_multiplicity_set_finite
    and poly (factor c)      by poly_factor_poly
   By poly_root_multiplicity_def, this is to show:
   If part: 1 < MAX_SET s ==> root p c /\ root (diff p) c
      Let k = MAX_SET s, to show: 1 < k ==> root p c /\ root (diff p) c
      Note 1 < k ==> 0 < k
      Thus c IN roots p                by poly_root_condition
        or root p c                    by poly_roots_member
      Next, to show: root (diff p) c.
      Note k = multiplicity p c        by poly_root_multiplicity_def
      Thus factor c ** k pdivides p    by poly_root_multiplicity_property
       ==> ?q. poly q /\ (p = q * factor c ** k)    by poly_divides_def
       Now, eval (factor c) c = #0     by poly_eval_factor, root p c
       and k <> 0 /\ PRE k <> 0        by 1 < k
         eval (diff p) c
       = eval (diff q * factor c ** k + q * diff (factor c ** k)) c          by poly_diff_mult
       = eval (diff q * factor c ** k) c + eval (q * diff (factor c ** k)) c by poly_eval_add
       = (eval (diff q) c) * (eval (factor c ** k) c) +
         (eval q c) * (eval (diff (factor c ** k)) c)                        by poly_eval_mult
       Compute:
         eval (factor c ** k) c
       = (eval (factor c) c) ** k            by poly_eval_exp
       = #0 ** k                             by poly_eval_factor
       = #0                                  by ring_zero_exp, k <> 0
         eval (diff (factor c ** k)) c
       = eval (##k * (factor c) ** PRE k * diff (factor c)) c    by poly_diff_exp
       = eval (##k * (factor c) ** PRE k * |1|) c                by poly_diff_factor
       = eval (##k * (factor c) ** PRE k) c                      by poly_mult_rone
       = ##k * (eval ((factor c) ** PRE k) c)                    by poly_eval_cmult
       = ##k * (eval (factor c) c) ** PRE k                      by poly_eval_exp
       = ##k * #0 ** PRE k                                       by poly_eval_factor
       = ##k * #0                                                by ring_zero_exp, PRE k <> 0
       = #0                                                      by ring_mult_rzero
       Hence eval (diff p) c = #0, or root (diff p) c            by poly_root_def
   Only-if part: root p c /\ root (diff p) c ==> 1 < MAX_SET s
     Since root p c ==> (factor c) pdivides p          by poly_root_factor, poly_roots_member
        or ?q. poly q /\ (p = q * factor c)            by poly_divides_def
     Given root (diff p) c,
        #0 = eval (diff p) c                           by poly_root_def
           = eval (diff (q * factor c)) c              by p = q * factor c
           = eval (diff q * factor c + q * (diff (factor c)) c     by poly_diff_mult
           = eval (diff q * factor c + q * |1|) c      by poly_diff_factor
           = eval (diff q * factor c + q) c            by poly_mult_rone
           = eval (diff q * factor c) + eval q c       by poly_eval_add
           = (eval (diff q) c) * (eval (factor c) c) + eval q c    by poly_eval_mult
           = (eval (diff q) c) * #0  + eval q c        by poly_eval_factor
           = #0 + eval q c                             by ring_mult_rzero
           = eval q c                                  by ring_add_lzero
      Thus root q c                                    by poly_root_def
       ==> (factor c) pdivides q                       by poly_root_factor, poly_roots_member
        or ?t. poly t /\ (q = t * factor c)            by poly_divides_def
     Hence p = (t * factor c) * factor c               by combining above
             = t * (factor c * factor c)               by poly_mult_assoc
             = t * (factor c) ** 2                     by poly_exp_2
      Thus (factor c) ** 2 pdivides p                  by poly_divides_def
        or 2 IN s                                      by poly_root_multiplicity_set_member
        so 2 <= MAX_SET s                              by in_max_set
        or 1 < MAX_SET s
*)
val poly_root_multiple = store_thm(
  "poly_root_multiple",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R ==>
     (1 < multiplicity p c <=> root p c /\ root (diff p) c)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  rw_tac std_ss[poly_root_multiplicity_def] >>
  qabbrev_tac `s = multiplicity_set p c` >>
  `FINITE s` by rw[poly_root_multiplicity_set_finite, Abbr`s`] >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `eval (factor c) c = #0` by rw[poly_eval_factor] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < MAX_SET s` by decide_tac >>
    metis_tac[poly_root_multiplicity_def, poly_root_condition, poly_roots_member],
    qabbrev_tac `k = MAX_SET s` >>
    `k = multiplicity p c` by rw[poly_root_multiplicity_def, Abbr`k`, Abbr`s`] >>
    `factor c ** k pdivides p` by rw[poly_root_multiplicity_property] >>
    `?q. poly q /\ (p = q * factor c ** k)` by rw[GSYM poly_divides_def] >>
    `poly (diff q) /\ poly (factor c ** k) /\ poly (diff (factor c ** k))` by rw[] >>
    `k <> 0 /\ PRE k <> 0` by decide_tac >>
    `eval (factor c ** k) c = #0` by rw[poly_eval_exp, ring_zero_exp] >>
    `eval (factor c ** PRE k) c = #0` by rw[poly_eval_exp, ring_zero_exp] >>
    `eval (diff p) c = eval (diff q * factor c ** k + q * diff (factor c ** k)) c` by rw[poly_diff_mult] >>
    `_ = eval (diff q * factor c ** k) c + eval (q * diff (factor c ** k)) c` by rw[poly_eval_add] >>
    `_ = (eval q c) * (eval (diff (factor c ** k)) c)` by rw[poly_eval_mult] >>
    `_ = (eval q c) * (eval (##k * (factor c) ** PRE k * diff (factor c)) c)` by rw[poly_diff_exp] >>
    `_ = #0` by rw[poly_diff_factor, poly_eval_cmult] >>
    rw[poly_root_def],
    `(factor c) pdivides p` by metis_tac[poly_root_factor, poly_roots_member] >>
    `?q. poly q /\ (p = q * factor c)` by rw[GSYM poly_divides_def] >>
    `poly (diff q)` by rw[] >>
    `eval (diff p) c = eval (diff q * factor c + q * (diff (factor c))) c` by rw[poly_diff_mult] >>
    `_ = eval (diff q * factor c + q) c` by rw[poly_diff_factor] >>
    `_ = eval (diff q * factor c) c + eval q c` by rw[poly_eval_add] >>
    `_ = eval q c` by rw[poly_eval_mult] >>
    `root q c` by fs[poly_root_def] >>
    `(factor c) pdivides q` by metis_tac[poly_root_factor, poly_roots_member] >>
    `?t. poly t /\ (q = t * factor c)` by rw[GSYM poly_divides_def] >>
    `p = t * (factor c * factor c)` by rw[poly_mult_assoc] >>
    `_ = t * (factor c) ** 2` by rw[poly_exp_2] >>
    `(factor c) ** 2 pdivides p` by metis_tac[poly_divides_def] >>
    `2 IN s` by metis_tac[poly_root_multiplicity_set_member] >>
    `2 <= MAX_SET s` by rw[in_max_set] >>
    decide_tac
  ]);

(* This is a major result. *)

(* Theorem: Field r ==> !p c. poly p /\ p <> |0| /\ c IN roots p ==>
   ?q. poly q /\ (p = (term p c) * q) /\ (c NOTIN roots q) /\ (deg q = deg p - multiplicity p c) *)
(* Proof:
   Let m = multiplicity p c.
   Note c IN roots p ==> c IN R         by poly_roots_element
   Note monic (factor c)                by poly_factor_monic
   Thus poly (factor c)                 by poly_monic_poly
    and poly ((factor c) ** m)          by poly_exp_poly
   Note (factor c) ** m pdivides p      by poly_root_multiplicity_root_property
    ==> ?q. poly q /\
            p = q * (factor c) ** m     by poly_divides_def
              = (factor c) ** m * q     by poly_mult_comm
   Thus c NOTIN roots q                 by poly_root_multiplicity_factor_out_root
    Now q <> |0|                        by poly_mult_eq_zero
     so lead q <> #0                    by poly_lead_nonzero
    and monic ((factor c) ** m)         by poly_monic_exp_monic
     so lead ((factor c) ** m) = #1     by poly_monic_lead
    ==> unit (lead ((factor c) ** m))   by field_one_unit
   Thus deg p
      = deg ((factor c) ** m) + deg q   by poly_deg_mult_unit
      = m + deg q                       by poly_factor_deg
    or deg q = deg p - m                by arithmetic
*)
val poly_root_factor_out_root = store_thm(
  "poly_root_factor_out_root",
  ``!r:'a field. Field r ==> !p c. poly p /\ p <> |0| /\ c IN roots p ==>
   ?q. poly q /\ (p = (term p c) * q) /\ (c NOTIN roots q) /\ (deg q = deg p - multiplicity p c)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = multiplicity p c` >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `monic (factor c)` by rw[poly_factor_monic] >>
  `poly (factor c) /\ poly ((factor c) ** m)` by rw[] >>
  `(factor c) ** m pdivides p` by rw[poly_root_multiplicity_root_property, Abbr`m`] >>
  `?q. poly q /\ (p = q * (factor c) ** m)` by rw[GSYM poly_divides_def] >>
  `_ = (factor c) ** m * q` by rw[poly_mult_comm] >>
  `c NOTIN roots q` by metis_tac[poly_root_multiplicity_factor_out_root] >>
  `q <> |0|` by metis_tac[poly_mult_eq_zero] >>
  `lead q <> #0` by rw[poly_lead_nonzero] >>
  `unit (lead ((factor c) ** m))` by rw[] >>
  `deg ((factor c) ** m) = m` by rw[poly_factor_deg, poly_monic_deg_exp] >>
  `deg p = m + deg q` by rw[poly_deg_mult_unit] >>
  `deg q = deg p - m` by decide_tac >>
  metis_tac[]);

(* This is a weak result. *)
(* Theorem: poly p /\ p <> |0| ==> CARD (roots p) <= SIGMA (multiplicity p) (roots p) *)
(* Proof:
   Since Field r
     ==> FINITE (roots p)                              by poly_roots_finite
     ==> CARD (roots p) = SIGMA (\x. 1) (roots p)      by CARD_AS_SIGMA
    Now  !c. c IN (roots p) ==> 0 < multiplicity p c   by poly_root_multiplicity_nonzero
     or  !c. c IN (roots p) ==> 1 <= multiplicity p c  by arithmetic
    Hence SIGMA (\x. 1) (roots p) <= SIGMA (multiplicity p) (roots p)  by SIGMA_LE_SIGMA
       or          CARD (roots p) <= SIGMA (multiplicity p) (roots p)  by above
*)
val poly_roots_card_upper = store_thm(
  "poly_roots_card_upper",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= SIGMA (multiplicity p) (roots p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `CARD (roots p) = SIGMA (\x. 1) (roots p)` by rw[CARD_AS_SIGMA] >>
  `!c. c IN (roots p) ==> 1 <= multiplicity p c` by metis_tac[poly_root_multiplicity_nonzero, DECIDE ``!n. 0 < n <=> 1 <= n``] >>
  qabbrev_tac `f = (\x. 1)` >>
  qabbrev_tac `g = multiplicity p` >>
  `!x. f x = 1` by rw[Abbr`f`] >>
  `!c. g c = multiplicity p c` by rw[Abbr`g`] >>
  metis_tac[SIGMA_LE_SIGMA]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> monic (PPIMAGE (term p) (roots p)) *)
(* Proof:
   Let s = IMAGE (term p) (roots p).
   Note FINITE (roots p)                     by poly_roots_finite, p <> |0|
     so FINITE s                             by IMAGE_FINITE
    and mset s                               by poly_factor_monic, poly_roots_element
   Thus monic (PPIMAGE (term p) (roots p))   by poly_monic_prod_set_monic
*)
val poly_prod_term_roots_monic = store_thm(
  "poly_prod_term_roots_monic",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> monic (PPIMAGE (term p) (roots p))``,
  rpt strip_tac >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  (irule poly_monic_prod_set_monic >> simp[]) >>
  rpt strip_tac >>
  `c IN R` by metis_tac[poly_roots_element] >>
  rw[poly_factor_monic]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> poly (PPIMAGE (term p) (roots p)) *)
(* Proof: by poly_prod_term_roots_monic, poly_monic_poly *)
val poly_prod_term_roots_poly = store_thm(
  "poly_prod_term_roots_poly",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> poly (PPIMAGE (term p) (roots p))``,
  rw_tac std_ss[poly_prod_term_roots_monic, poly_monic_poly]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            FINITE (IMAGE (\x. factor x ** multiplicity p x) (roots p)) *)
(* Proof:
   Let s = IMAGE (\x. factor x ** multiplicity p x) (roots p)
   Since Field r, poly p /\ p <> |0| ==> FINITE (roots p)   by poly_roots_finite
   Hence FINITE s                                           by IMAGE_FINITE
*)
val poly_root_factor_multiplicity_finite = store_thm(
  "poly_root_factor_multiplicity_finite",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
       FINITE (IMAGE (\x. factor x ** multiplicity p x) (roots p))``,
  rw[poly_roots_finite]);

(* Theorem: Field r ==> !p z. z IN IMAGE (\x. factor x ** multiplicity p x) (roots p) ==> poly z *)
(* Proof:
       z IN IMAGE (\x. factor x ** multiplicity p x) (roots p) ==> poly z
   ==> ?x. (z = factor x ** multiplicity p x) /\ x IN (roots p)       by IN_IMAGE
   ==>     (z = factor x ** multiplicity p x) /\ x IN R /\ root p x   by poly_roots_member
   Since  x IN R ==> poly (factor x)                                  by poly_factor_property
   Hence poly z                                                       by poly_exp_poly
*)
val poly_root_factor_multiplicity_poly = store_thm(
  "poly_root_factor_multiplicity_poly",
  ``!r:'a field. Field r ==>
   !p z. z IN IMAGE (\x. factor x ** multiplicity p x) (roots p) ==> poly z``,
  rpt strip_tac >>
  `?x. (z = factor x ** multiplicity p x) /\ x IN (roots p)` by rw[GSYM IN_IMAGE] >>
  `!x. x IN R ==> poly (factor x)` by rw[poly_factor_property] >>
  metis_tac[poly_exp_poly, poly_roots_member, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Separable Polynomials                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define separable polynomial *)
val poly_separable_def = Define`
  poly_separable (r:'a ring) (p:'a poly) <=>
    p <> |0| /\ !c. c IN roots p ==> (multiplicity p c = 1)
`;
(* Note: roots |0| = R, and multiplicity_set |0| c = univ(:num), with multiplicity |0| c undefined. *)

(* overload on separable polynomial *)
val _ = overload_on("separable", ``poly_separable r``);

(* Theorem: Field r ==> !n. 1 < n /\ coprime n (char r) ==> separable (unity n) *)
(* Proof:
   Let p = unity n.
   Note monic p               by poly_monic_X_exp_n_sub_c, 0 < n
    ==> poly p /\ p <> |0|    by poly_monic_poly, poly_monic_nonzero
   By poly_separable_def, this is to show:
      !c. c IN roots p  ==> (multiplicity p c = 1)
   By contradiction, assume multiplicity p c <> 1.
   Now  c IN roots p
    ==> 0 < multiplicity p c   by poly_root_condition
     so 1 < multiplicity p c   by multiplicity p c <> 1
   With c IN R /\ root p c     by poly_roots_member
   Thus root (diff p) c        by poly_root_multiple
    ==> c IN {#0}              by poly_diff_unity_roots, poly_roots_member
     or c = #0                 by IN_SING
   Compute
        eval p #0
      = #0 ** n - #1           by poly_eval_X_exp_n_sub_c
      = #0 - #1                by ring_zero_exp, n <> 0
     <> #0                     by field_one_ne_zero
   This contradicts root p c   by poly_root_def
*)
val poly_separable_unity = store_thm(
  "poly_separable_unity",
  ``!r:'a field. Field r ==> !n. 1 < n /\ coprime n (char r) ==> separable (unity n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0` by decide_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = unity n` >>
  `monic p` by metis_tac[poly_monic_X_exp_n_sub_c, poly_ring_sum_1, Abbr`p`] >>
  `poly p /\ p <> |0|` by rw[poly_monic_nonzero] >>
  rw_tac std_ss[poly_separable_def] >>
  spose_not_then strip_assume_tac >>
  `0 < multiplicity p c` by rw[GSYM poly_root_condition] >>
  `1 < multiplicity p c` by decide_tac >>
  `c IN R /\ root p c` by metis_tac[poly_roots_member] >>
  `root (diff p) c` by metis_tac[poly_root_multiple] >>
  `c = #0` by metis_tac[poly_diff_unity_roots, poly_roots_member, IN_SING] >>
  `eval p #0 = #0 ** n - #1` by rw[poly_eval_X_exp_n_sub_c, Abbr`p`] >>
  `_ = #0 - #1` by rw[ring_zero_exp] >>
  `#0 - #1 <> #0` by rw[] >>
  fs[poly_root_def]);

(* Theorem: 1 < char r ==> !n. 0 < n ==> separable (master (char r ** n)) *)
(* Proof:
   Note #1 <> #0                               by ring_char_eq_1
   Let p = master (char r ** n).
    Note deg X = 1                             by poly_deg_X, #1 <> #0
     and deg (X ** char r ** n) = char r ** n  by poly_deg_X_exp, #1 <> #0
     and 1 < char r ** n                       by ONE_LT_EXP, 1 < char r, 0 < n
      so lead p = #1                           by poly_lead_sub_less
   hence monic p                               by poly_master_monic
     ==> poly p /\ p <> |0|                    by poly_monic_poly, poly_monic_nonzero
   By poly_separable_def, this is to show:
      !c. c IN roots p ==> (multiplicity p c = 1)
   By contradiction, assume multiplicity p c <> 1.
   Note c IN R /\ root p c                     by poly_roots_member
    ==> root p c ==> 0 < multiplicity p c      by poly_root_condition
      so 1 < multiplicity p c                  by multiplicity p c <> 1
   Hence root (diff p) c                       by poly_root_multiple
      or c IN roots (diff p)                   by poly_roots_member
     But roots (diff p) = {}                   by poly_diff_master_char_exp_roots
   This is a contradiction                     by MEMBER_NOT_EMPTY
*)
val poly_separable_master_char_exp = store_thm(
  "poly_separable_master_char_exp",
  ``!r:'a ring. Ring r /\ 1 < char r ==>
   !n. 0 < n ==> separable (master (char r ** n))``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[ring_char_eq_1, LESS_NOT_EQ] >>
  qabbrev_tac `p = master (char r ** n)` >>
  `1 < char r ** n` by rw[ONE_LT_EXP] >>
  `monic p` by rw[poly_master_monic, Abbr`p`] >>
  `poly p /\ p <> |0|` by rw[poly_monic_nonzero] >>
  rw_tac std_ss[poly_separable_def] >>
  spose_not_then strip_assume_tac >>
  `0 < multiplicity p c` by rw[GSYM poly_root_condition] >>
  `1 < multiplicity p c` by decide_tac >>
  `c IN roots (diff p)` by metis_tac[poly_root_multiple, poly_roots_member] >>
  metis_tac[poly_diff_master_char_exp_roots, MEMBER_NOT_EMPTY]);

(* Theorem: poly p /\ poly q /\ q pdivides p /\ separable p ==> separable q *)
(* Proof:
   By poly_separable_def, this is to show:
   (1) q <> |0|.
       By contradiction, suppose q = |0|,
       Then |0| pdivides p ==> p = |0|      by poly_zero_divides
       This contradicts p <> |0|            by separable p
   (2) !c. c IN roots q ==> multiplicity q c = 1
       Note c IN R /\ root q c         by poly_roots_member
        and root q c ==> root p c      by poly_divides_share_root
         so c IN roots p               by poly_roots_member
       Thus multiplicity p c = 1       by poly_separable_def, separable p
       Note multiplicity q c <= multiplicity p c  by poly_root_multiplicity_le
                              = 1                 by above
       Note q <> |0|                   by poly_zero_divides, p <> |0|
       With c IN roots q               by given
       Thus 0 < multiplicity q c       by poly_root_multiplicity_nonzero, q <> |0|
         or 1 <= multiplicity q c      by LESS_IMP_LESS_OR_EQ

       Hence, multiplicity q c = 1     by LESS_EQUAL_ANTISYM
*)
val poly_separable_divisor_separable = store_thm(
  "poly_separable_divisor_separable",
  ``!r:'a ring. Ring r ==>
   !p q. poly p /\ poly q /\ q pdivides p /\ separable p ==> separable q``,
  rw_tac std_ss[poly_separable_def] >-
  metis_tac[poly_zero_divides] >>
  `Ring r` by rw[] >>
  `c IN R /\ root q c` by metis_tac[poly_roots_member] >>
  `root p c` by metis_tac[poly_divides_share_root] >>
  `multiplicity q c <= 1` by metis_tac[poly_root_multiplicity_le, poly_roots_member] >>
  `q <> |0|` by metis_tac[poly_zero_divides] >>
  `0 < multiplicity q c` by rw[poly_root_multiplicity_nonzero] >>
  decide_tac);

(* Theorem: poly p /\ poly q /\ separable (p * q) ==> separable p /\ separable q *)
(* Proof:
   Note poly (p * q)         by poly_mult_poly
    and p * q = q * p        by poly_mult_comm, Ring r
   Thus p divides q * p /\
        q divides p * q      by poly_divides_def
   The result follows        by poly_separable_divisor_separable
*)
val poly_separable_factors_separable = store_thm(
  "poly_separable_factors_separable",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\
    separable (p * q) ==> separable p /\ separable q``,
  ntac 5 strip_tac >>
  `poly (p * q)` by rw[] >>
  `p * q = q * p` by rw[poly_mult_comm] >>
  metis_tac[poly_separable_divisor_separable, poly_divides_def]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\
            separable (p * q) ==> DISJOINT (roots p) (roots q) *)
(* Proof:
   By DISJOINT_DEF, this is to show: roots p INTER roots q = {}
   By contradiction, suppose roots p INTER roots q <> {}.
   Then ?c. c IN roots p /\ c IN roots q    by IN_INTER, MEMBER_NOT_EMPTY
   Let h = factor c.
   Note c IN R                              by poly_roots_element
    and poly h                              by poly_factor_poly
    and h pdivides p /\ h pdivides q        by poly_root_factor
   Thus h * h pdivides (p * q)              by poly_divides_pair
     or h ** 2 pdivides (p * q)             by poly_exp_2
    But c IN roots (p * q)                  by poly_roots_mult, IN_UNION, Field r
    ==> p * q <> |0| /\
        multiplicity (p * q) c = 1          by poly_separable_def
    Now 2 <= multiplicity (p * q) c         by poly_root_multiplicity_lower, p * q <> |0|
   This implies 2 <= 1, which is false.
*)
val poly_separable_factor_roots_disjoint = store_thm(
  "poly_separable_factor_roots_disjoint",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\
    separable (p * q) ==> DISJOINT (roots p) (roots q)``,
  rw_tac std_ss[DISJOINT_DEF] >>
  CCONTR_TAC >>
  `?c. c IN roots p /\ c IN roots q` by metis_tac[IN_INTER, MEMBER_NOT_EMPTY] >>
  qabbrev_tac `h = factor c` >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `c IN R` by metis_tac[poly_roots_element] >>
  `poly h` by metis_tac[poly_factor_poly] >>
  `h pdivides p /\ h pdivides q` by metis_tac[poly_root_factor] >>
  `h ** 2 pdivides (p * q)` by rw[poly_divides_pair, poly_exp_2] >>
  `c IN roots (p * q)` by rw[poly_roots_mult] >>
  `p * q <> |0| /\ (multiplicity (p * q) c = 1)` by metis_tac[poly_separable_def] >>
  `2 <= multiplicity (p * q) c` by rw[poly_root_multiplicity_lower] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
