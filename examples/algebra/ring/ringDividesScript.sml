(* ------------------------------------------------------------------------- *)
(* Divisibility in Ring                                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringDivides";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dep_rewrite numberTheory
     combinatoricsTheory;

open ringIdealTheory;
open ringUnitTheory;
open ringTheory;
open groupTheory;
open monoidTheory bagTheory containerTheory;

open ringMapTheory groupMapTheory;
open subgroupTheory quotientGroupTheory;

(* ------------------------------------------------------------------------- *)
(* Divisbility in Ring Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   I             = i.carrier
   J             = j.carrier
   p rdivides q  = ring_divides r p q
   rassoc p q    = ring_associates r p q
   rprime p      = ring_prime r p
   rgcd p q      = ring_gcd r p q
   <a>           = principal_ideal r a
   <b>           = principal_ideal r b
   <u>           = principal_ideal r u
*)
(* Definitions and Theorems (# are exported):

   Ring Divisiblity:
   ring_divides_def     |- !r q p. q rdivides p <=> ?s. s IN R /\ (p = s * q)
   ring_associates_def  |- !r p q. rassoc p q <=> ?s. unit s /\ (p = s * q)
   ring_prime_def       |- !r p. rprime p <=> !a b. a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b

   irreducible_associates |- !r. Ring r /\ #1 <> #0 ==> !p s. p IN R /\ unit s ==> (atom p <=> atom (s * p))
   irreducible_factors   |- !r z. atom z ==> z IN R+ /\ z NOTIN R* /\ !p. p IN R /\ p rdivides z ==> rassoc z p \/ unit p

   ring_divides_refl    |- !r. Ring r ==> !p. p IN R ==> p rdivides p
   ring_divides_trans   |- !r. Ring r ==> !p q t. p IN R /\ q IN R /\ t IN R /\ p rdivides q /\ q rdivides t ==> p rdivides t
   ring_divides_zero    |- !r. Ring r ==> !p. p IN R ==> p rdivides #0
   ring_zero_divides    |- !r. Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))
   ring_divides_by_one  |- !r. Ring r ==> !p. p IN R ==> #1 rdivides p
   ring_divides_by_unit |- !r. Ring r ==> !p t. p IN R /\ unit t ==> t rdivides p
   ring_factor_multiple |- !r. Ring r ==> !p q. p IN R /\ q IN R /\ (?k. k IN R /\ (p = k * q)) ==>
                           !z. z IN R /\ (?s. s IN R /\ (z = s * p)) ==> ?t. t IN R /\ (z = t * q)

   Euclidean Ring Greatest Common Divisor:
   ring_gcd_def          |- !r f p q. rgcd p q = if p = #0 then q else if q = #0 then p
                                  else (let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                                        in CHOICE (preimage f s (MIN_SET (IMAGE f s))))
   ring_gcd_zero         |- !r f p. (rgcd p #0 = p) /\ (rgcd #0 p = p)
   ring_gcd_linear       |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)
   ring_gcd_is_gcd       |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  rgcd p q rdivides p /\ rgcd p q rdivides q /\
                                  !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q
   ring_gcd_divides      |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q rdivides p /\ rgcd p q rdivides q
   ring_gcd_property     |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q
   ring_gcd_element      |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q IN R
   ring_gcd_sym          |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> (rgcd p q = rgcd q p)
   ring_irreducible_gcd  |- !r f. EuclideanRing r f ==> !p. p IN R /\ atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q

   ring_ordering_def     |- !r f. ring_ordering r f <=> !a b. a IN R /\ b IN R /\ b <> #0 ==> f a <= f (a * b)
   ring_divides_le       |- !r f. EuclideanRing r f /\ ring_ordering r f ==>
                                  !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p

   Principal Ideal Ring: Irreducibles and Primes:
   principal_ideal_element_divides            |- !r. Ring r ==> !p. p IN R ==> !x. x IN <p>.carrier <=> p rdivides x
   principal_ideal_sub_implies_divides        |- !r. Ring r ==> !p q. p IN R /\ q IN R ==> (q rdivides p <=> <p> << <q>)
   principal_ideal_ring_atom_is_prime         |- !r. PrincipalIdealRing r ==> !p. atom p ==> rprime p
   principal_ideal_ring_irreducible_is_prime  |- !r. PrincipalIdealRing r ==> !p. atom p ==> rprime p
*)

(* ------------------------------------------------------------------------- *)
(* Ring Divisiblity                                                          *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* Divides relation in ring *)
val ring_divides_def = Define `
  ring_divides (r:'a ring) (q:'a) (p:'a) =
    ?s:'a. s IN R /\ (p = s * q)
`;

(* Overload ring divides *)
val _ = overload_on ("rdivides", ``ring_divides r``);
val _ = set_fixity "rdivides" (Infix(NONASSOC, 450)); (* same as relation *)
(*
ring_divides_def;
> val it = |- !r q p. q | p <=> ?s. p = s * q : thm
*)

(* Define ring associates *)
val ring_associates_def = Define `
  ring_associates (r:'a ring) (p:'a) (q:'a) =
  ?s:'a. unit s /\ (p = s * q)
`;
(* Overload ring associates *)
val _ = overload_on ("rassoc", ``ring_associates r``);
(*
- ring_associates_def;
> val it = |- !r p q. rassoc p q <=> ?s. unit s /\ (p = s * q) : thm
*)

(* Define prime in ring *)
val ring_prime_def = Define `
  ring_prime (r:'a ring) (p:'a) =
  !a b. a IN R /\ b IN R /\ p rdivides a * b ==> (p rdivides a) \/ (p rdivides b)
`;
(* Overload prime in ring *)
val _ = overload_on ("rprime", ``ring_prime r``);
(*
- ring_prime_def;
> val it = |- !r p. rprime p <=> !a b. a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b : thm
*)

(* Theorem: Ring r /\ #1 <> #0 ==> p IN R /\ unit s ==> atom p <=> atom (s * p) *)
(* Proof:
   If part: atom p /\ unit s ==> atom (s * p)
   unit s ==> unit ( |/ s)   by ring_unit_has_inv
   and |/s IN R              by ring_unit_element
     |/s * (s * p)
   = ( |/s * s) * p          by ring_mult_assoc
   = #1 * p                  by ring_unit_linv
   = p                       by ring_mult_lone
   Since p <> #0             by irreducible_def, ring_nonzero_eq
   s * p <> #0               by ring_mult_rzero
   so s * p IN R+            by ring_nonzero_eq
   By irreducible_def, still more to show:
   (1) unit s /\ atom p ==> s * p NOTIN R*
       By contradiction, assume unit (s * p)
       Since Group r*                 by ring_units_group
           unit ( |/s) and unit (s * p)
       ==> unit ( |/s * (s * p))      by group_op_element
       ==> unit p                     by above
       which contradicts atom p       by irreducible_def
   (2) atom p /\ s * p = x * y ==> unit x \/ unit y
       |/s * (s * p) = |/s * (x * y)
       p = ( |/s * x) * y             by ring_mult_assoc
       Since atom p
       this means unit ( |/s * x) or unit y
                                      by irreducible_def
       If unit ( |/s * x)
       Since Group r*                 by ring_units_group
          unit s and unit ( |/s * x)
       ==> unit (s * |/s * x)         by group_op_element
       ==> unit (#1 * x) ==> unit x
       If unit y, this is trivial.
   Only-if part: p IN R /\ unit s /\ atom (s * p) ==> atom p /\ unit s
     unit s ==> s IN R                by ring_unit_element
     atom (p * s) ==> p * s <> #0     by irreducible_def
     hence p <> #0                    by ring_mult_rzero
     or p IN R+                       by ring_nonzero_eq
   By irreducible_def, still more to show:
   (1) unit s /\ atom (s * p) ==> p NOTIN R*
       By contradiction, assume unit p
       Since Group r*                 by ring_units_group
           unit s and unit p
       ==> unit (s * p)               by group_op_element
       which contradicts atom (s * p) by irreducible_def
   (2) unit s /\ atom (s * (x * y)) ==> unit x \/ unit y
       s * (x * y) = (s * x) * y      by ring_mult_assoc
       Since atom (s * (x * y))
       this means unit (s * x) or unit y
                                      by irreducible_def
       If unit (s * x)
       Since Group r*                 by ring_units_group
          unit ( |/s) and unit (s * x)
       ==> unit ( |/s * (s * x))      by group_op_element
       ==> unit (#1 * x) ==> unit x
       If unit y, this is trivial.
*)
val irreducible_associates = store_thm(
  "irreducible_associates",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p s. p IN R /\ unit s ==> (atom p <=> atom (s * p))``,
  rw[EQ_IMP_THM] >| [
    `unit ((Invertibles r.prod).inv s)` by rw[ring_unit_has_inv] >>
    `s IN R` by rw[ring_unit_element] >>
    `s * p IN R /\ (Invertibles r.prod).inv s IN R` by rw[ring_unit_element] >>
    `((Invertibles r.prod).inv s) * (s * p) = ((Invertibles r.prod).inv s) * s * p` by rw[ring_mult_assoc] >>
    `_ = #1 * p` by rw[ring_unit_linv] >>
    `_ = p` by rw[] >>
    `p <> #0` by metis_tac[irreducible_def, ring_nonzero_eq] >>
    `s * p <> #0` by metis_tac[ring_mult_rzero] >>
    `s * p IN R+` by rw[ring_nonzero_eq] >>
    rw[irreducible_def] >| [
      spose_not_then strip_assume_tac >>
      `Group r*` by rw[ring_units_group] >>
      `unit (((Invertibles r.prod).inv s) * (s * p))` by metis_tac[group_op_element, ring_units_property] >>
      metis_tac[irreducible_def],
      `((Invertibles r.prod).inv s) * (x * y) = ((Invertibles r.prod).inv s) * x * y` by rw[ring_mult_assoc] >>
      `((Invertibles r.prod).inv s) * x IN R` by rw[] >>
      `unit (((Invertibles r.prod).inv s) * x) \/ unit y` by metis_tac[irreducible_def] >| [
        `Group r*` by rw[ring_units_group] >>
        `unit (s * (((Invertibles r.prod).inv s) * x))` by metis_tac[group_op_element, ring_units_property] >>
        `s * (((Invertibles r.prod).inv s) * x) = s * ((Invertibles r.prod).inv s) * x` by rw[ring_mult_assoc] >>
        `_ = #1 * x` by rw[ring_unit_rinv] >>
        `_ = x` by rw[] >>
        metis_tac[],
        rw[]
      ]
    ],
    `s IN R` by rw[ring_unit_element] >>
    `p IN R+` by metis_tac[ring_mult_rzero, irreducible_def, ring_nonzero_eq] >>
    rw[irreducible_def] >| [
      spose_not_then strip_assume_tac >>
      `Group r*` by rw[ring_units_group] >>
      `unit (s * p)` by metis_tac[group_op_element, ring_units_property] >>
      metis_tac[irreducible_def],
      `s * (x * y) = s * x * y` by rw[ring_mult_assoc] >>
      `s * x IN R` by rw[] >>
      `unit (s * x) \/ unit y` by metis_tac[irreducible_def] >| [
        `Group r*` by rw[ring_units_group] >>
        `unit ((Invertibles r.prod).inv s)` by rw[ring_unit_has_inv] >>
        `unit (((Invertibles r.prod).inv s) * (s * x))` by metis_tac[group_op_element, ring_units_property] >>
        `(Invertibles r.prod).inv s IN R` by rw[ring_unit_element] >>
        `((Invertibles r.prod).inv s) * (s * x) = ((Invertibles r.prod).inv s) * s * x` by rw[ring_mult_assoc] >>
        `_ = #1 * x` by rw[ring_unit_linv] >>
        `_ = x` by rw[] >>
        metis_tac[],
        rw[]
      ]
    ]
  ]);

(* Theorem: atom z ==> z IN R+ /\ ~(unit z) /\ (!p. p IN R /\ p rdivides z ==> (rassoc z p) \/ unit p) *)
(* Proof:
       p rdivides z
   ==> ?s. s IN R /\ (z = s * p)    by ring_divides_def
   ==> unit s \/ unit p             by irreducible_def
   If unit s, rassoc z p            by ring_associates_def
   If unit p, trivially true.
*)
val irreducible_factors = store_thm(
  "irreducible_factors",
  ``!r:'a ring. !z. atom z ==> z IN R+ /\ ~(unit z) /\ (!p. p IN R /\ p rdivides z ==> (rassoc z p) \/ unit p)``,
  rw[irreducible_def] >>
  `?s. s IN R /\ (z = s * p)` by rw[GSYM ring_divides_def] >>
  `unit s \/ unit p` by rw[] >-
  metis_tac[ring_associates_def] >>
  rw[]);

(* Theorem: p rdivides p *)
(* Proof:
   Since #1 * p = p      by ring_mult_lone
   p rdivides p          by ring_divides_def
*)
val ring_divides_refl = store_thm(
  "ring_divides_refl",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p rdivides p``,
  rw[ring_divides_def] >>
  metis_tac[ring_mult_lone, ring_one_element]);

(* Theorem: p rdivides q /\ q rdivides p ==> p = q *)
(* Proof:
*)

(* Theorem: p rdivides q /\ q rdivides t ==> p rdivides t *)
(* Proof:
   p rdivides q ==> ?s. s IN R /\ q = s * p     by ring_divides_def
   q rdivides t ==> ?s'. s' IN R /\ t = s' * q  by ring_divides_def
   Hence t = s' * (s * p)
           = (s' * s) * p                       by ring_mult_assoc
   Since s' * s IN R                            by ring_mult_element
   p rdivides t                                 by ring_divides_def
*)
val ring_divides_trans = store_thm(
  "ring_divides_trans",
  ``!r:'a ring. Ring r ==> !p q t. p IN R /\ q IN R /\ t IN R /\ p rdivides q /\ q rdivides t ==> p rdivides t``,
  rw[ring_divides_def] >>
  `s' * (s * p) = s' * s * p` by rw[ring_mult_assoc] >>
  metis_tac[ring_mult_element]);

(* Theorem: p rdivides #0 *)
(* Proof:
   Since #0 = #0 * p     by ring_mult_lzero
   Hence p rdivides #0   by ring_divides_def
*)
val ring_divides_zero = store_thm(
  "ring_divides_zero",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p rdivides #0``,
  rw[] >>
  metis_tac[ring_divides_def, ring_mult_lzero, ring_zero_element]);

(* Theorem: Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0)) *)
(* Proof:
       #0 rdivides x
   <=> ?s. s IN R /\ (x = s * #0)    by ring_divides_def
   <=> ?s. s IN R /\ (x = #0)        by ring_mult_rzero
   <=> x = #0
*)
val ring_zero_divides = store_thm(
  "ring_zero_divides",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))``,
  metis_tac[ring_divides_def, ring_mult_rzero]);

(* Theorem: #1 rdivides p *)
(* Proof:
   Since p = p * #1   by ring_mult_rone
   Hence true         by ring_divides_def
*)
val ring_divides_by_one = store_thm(
  "ring_divides_by_one",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> #1 rdivides p``,
  metis_tac[ring_divides_def, ring_mult_rone]);

(* Theorem: unit t ==> t rdivides p *)
(* Proof:
   unit t ==> |/t IN R        by ring_unit_inv_element
   Since p = p * #1           by ring_mult_rone
           = p * ( |/ t * t)  by ring_unit_linv
           = (p * |/t) * t    by ring_mult_assoc
   Hence true                 by ring_divides_def
*)
val ring_divides_by_unit = store_thm(
  "ring_divides_by_unit",
  ``!r:'a ring. Ring r ==> !p t. p IN R /\ unit t ==> t rdivides p``,
  rpt strip_tac >>
  `|/t IN R /\ p * |/t IN R` by rw[ring_unit_inv_element] >>
  `p = p * #1` by rw[] >>
  `_ = p * ( |/t * t)` by rw[ring_unit_linv] >>
  `_ = p * |/t * t` by rw[ring_mult_assoc] >>
  metis_tac[ring_divides_def]);

(* Theorem: p = k * q ==> z = s * p ==> z = t * q *)
(* Proof:
   z = s * p           by given
     = s * (k * q)     by given
     = (s * k) * q     by ring_mult_assoc
   So let t = s * k, then z = t * q
*)
val ring_factor_multiple = store_thm(
  "ring_factor_multiple",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN R /\ (?k. k IN R /\ (p = k * q)) ==>
     !z. z IN R /\ (?s. s IN R /\ (z = s * p)) ==> (?t. t IN R /\ (z = t * q))``,
  rpt strip_tac >>
  qexists_tac `s * k` >>
  rw[ring_mult_assoc]);

Theorem ring_prime_divides_product:
  !r. Ring r ==>
  !p. p IN r.carrier ==>
    (ring_prime r p /\ ~Unit r p <=>
     (!b. FINITE_BAG b /\ SET_OF_BAG b SUBSET r.carrier /\
          ring_divides r p (GBAG r.prod b) ==>
          ?x. BAG_IN x b /\ ring_divides r p x))
Proof
  rpt strip_tac
  \\ reverse eq_tac
  >- (
    strip_tac
    \\ conj_tac
    >- (
      rw[ring_prime_def]
      \\ first_x_assum(qspec_then`{|a; b|}`mp_tac)
      \\ simp[SUBSET_DEF]
      \\ DEP_REWRITE_TAC[GBAG_INSERT]
      \\ simp[SUBSET_DEF]
      \\ dsimp[]
      \\ metis_tac[Ring_def])
    \\ strip_tac
    \\ `ring_divides r p r.prod.id`
    by (
      rfs[ring_unit_property, ring_divides_def]
      \\ metis_tac[ring_mult_comm] )
    \\ first_x_assum(qspec_then`{||}`mp_tac)
    \\ simp[] )
  \\ strip_tac
  \\ simp[Once(GSYM AND_IMP_INTRO)]
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ simp[Once ring_divides_def]
  \\ conj_tac >- metis_tac[ring_unit_property, ring_mult_comm]
  \\ rpt strip_tac
  \\ fs[SUBSET_DEF]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ fs[SUBSET_DEF]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ fs[ring_prime_def]
  \\ `GBAG r.prod b IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ fs[SUBSET_DEF] )
  \\ rfs[] \\ strip_tac
  \\ `e IN r.carrier` by metis_tac[]
  \\ first_x_assum(drule_then (drule_then drule))
  \\ metis_tac[]
QED

Theorem ring_product_factors_divide:
  !r. Ring r ==>
  !b. FINITE_BAG b ==>
      SET_OF_BAG b SUBSET r.carrier /\
      ring_divides r (GBAG r.prod b) x ==>
      !y. BAG_IN y b ==> ring_divides r y x
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ fs[SUBSET_DEF]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ gs[ring_divides_def, PULL_EXISTS]
  \\ gen_tac \\ strip_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ last_x_assum(qspec_then`s * e`mp_tac)
  \\ simp[]
  \\ `GBAG r.prod b IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[SUBSET_DEF] )
  \\ rfs[]
  \\ simp[ring_mult_assoc]
  \\ strip_tac
  \\ strip_tac
  \\ strip_tac
  >- (
    qexists_tac`s * GBAG r.prod b`
    \\ simp[ring_mult_assoc]
    \\ AP_TERM_TAC
    \\ simp[ring_mult_comm] )
  \\ res_tac
  \\ simp[]
QED

Theorem ring_mult_divides:
  !r p q x.
    Ring r /\ ring_divides r (r.prod.op p q) x /\
    p IN R /\ q IN R
    ==>
    ring_divides r p x /\ ring_divides r q x
Proof
  rpt strip_tac
  \\ drule ring_product_factors_divide
  \\ disch_then(qspecl_then[`x`,`{|p;q|}`]mp_tac)
  \\ simp[SUBSET_DEF]
  \\ dsimp[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ metis_tac[Ring_def]
QED

Theorem ring_associates_sym:
  !r p q.
    Ring r /\ q IN r.carrier /\ ring_associates r p q ==>
    ring_associates r q p
Proof
  rw[ring_associates_def]
  \\ rfs[ring_unit_property]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`v`
  \\ qexists_tac`s`
  \\ simp[]
  \\ simp[Once ring_mult_comm]
  \\ simp[GSYM ring_mult_assoc]
  \\ metis_tac[ring_mult_comm, ring_mult_lone]
QED

Theorem ring_associates_trans:
  !r x y z.
    Ring r /\ z IN r.carrier /\
    ring_associates r x y /\
    ring_associates r y z ==>
    ring_associates r x z
Proof
  rw[ring_associates_def]
  \\ qexists_tac`s * s'`
  \\ simp[ring_mult_assoc]
  \\ simp[ring_unit_mult_unit]
QED

Theorem ring_associates_refl:
  !r x. Ring r /\ x IN r.carrier ==> ring_associates r x x
Proof
  rw[ring_associates_def]
  \\ qexists_tac`#1`
  \\ simp[]
QED

Theorem ring_associates_mult:
  !r p q x.
    Ring r /\ p IN r.carrier /\ q IN r.carrier /\ x IN r.carrier /\
    ring_associates r p q ==>
    ring_associates r (r.prod.op x p) (r.prod.op x q)
Proof
  rw[ring_associates_def]
  \\ rfs[ring_unit_property]
  \\ simp[PULL_EXISTS]
  \\ qexistsl_tac[`s`,`v`]
  \\ simp[GSYM ring_mult_assoc]
  \\ metis_tac[ring_mult_comm]
QED

Theorem ring_associates_divides:
  !r p q x. Ring r /\ ring_associates r p q /\ q IN R /\
  ring_divides r p x ==> ring_divides r q x
Proof
  rw[ring_associates_def, ring_divides_def]
  \\ qexists_tac`s' * s`
  \\ simp[]
  \\ simp[ring_mult_assoc]
QED

Theorem ring_divides_associates:
  !r x y p. Ring r /\ ring_associates r x y /\ p IN R /\ y IN R /\ ring_divides r p x ==>
  ring_divides r p y
Proof
  rw[ring_associates_def, ring_divides_def]
  \\ qexists_tac`|/ s * s'`
  \\ simp[ring_unit_inv_element, ring_mult_assoc]
  \\ simp[ring_unit_inv_element, GSYM ring_mult_assoc]
  \\ simp[ring_unit_linv]
QED

Theorem LIST_REL_ring_associates_product:
  Ring r ==>
  !l1 l2. LIST_REL (ring_associates r) l1 l2 /\
          set l2 SUBSET r.carrier
          ==>
          ring_associates r (GBAG r.prod (LIST_TO_BAG l1))
                            (GBAG r.prod (LIST_TO_BAG l2))
Proof
  strip_tac
  \\ Induct_on`LIST_REL`
  \\ rw[]
  >- ( simp[ring_associates_def] \\ qexists_tac`#1` \\ simp[] )
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SUBSET_DEF, IN_LIST_TO_BAG]
  \\ conj_asm1_tac >- (
    fs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    \\ fs[ring_associates_def]
    \\ reverse conj_tac >- metis_tac[Ring_def]
    \\ rw[] \\ res_tac \\ rfs[]
    \\ res_tac \\ fs[] )
  \\ irule ring_associates_trans
  \\ simp[]
  \\ `GBAG r.prod (LIST_TO_BAG l2) IN r.prod.carrier` by (
    irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ `GBAG r.prod (LIST_TO_BAG l1) IN r.prod.carrier` by (
    irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ conj_tac >- ( irule ring_mult_element \\ rfs[] )
  \\ qexists_tac`h2 * GBAG r.prod (LIST_TO_BAG l1)`
  \\ reverse conj_tac
  >- ( irule ring_associates_mult \\ rfs[] )
  \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ rfs[]
  \\ qmatch_goalsub_abbrev_tac`rassoc foo _`
  \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ rfs[]
  \\ qunabbrev_tac`foo`
  \\ irule ring_associates_mult \\ rfs[]
QED

(* ------------------------------------------------------------------------- *)
(* Euclidean Ring Greatest Common Divisor                                    *)
(* ------------------------------------------------------------------------- *)

(* Define greatest common divisor *)
val ring_gcd_def = Define`
  ring_gcd (r:'a ring) (f:'a -> num) (p:'a) (q:'a) =
   if p = #0 then q
   else if q = #0 then p
   else let s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
         in CHOICE (preimage f s (MIN_SET (IMAGE f s)))
`;

(* Overload ring gcd *)
val _ = overload_on ("rgcd", ``ring_gcd r f``);
(*
- ring_gcd_def;
> val it = |- !r f p q. rgcd p q = if p = #0 then q else if q = #0 then p else
              (let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                in CHOICE (preimage f s (MIN_SET (IMAGE f s)))) : thm
*)

(* Theorem: !p. (rgcd p #0 = p) /\ (rgcd #0 p = p) *)
(* Proof: by ring_gcd_def *)
val ring_gcd_zero = store_thm(
  "ring_gcd_zero",
  ``!(r:'a ring) (f :'a -> num). !p. (rgcd p #0 = p) /\ (rgcd #0 p = p)``,
  rw[ring_gcd_def]);

(* Theorem: EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
            (?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)) *)
(* Proof:
   If p = #0, rgcd p q = q = #0 * p + #1 * q.
   If q = #0, rgcd p q = p = #1 * p + #0 * q.
   If p <> #0 and q <> #0, by ring_gcd_def,
   rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))
   where s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
   Since p = #1 * p + #0 * q,
   and with p <> #0, f p <> 0                by euclid_ring_map
   Hence s <> {},
    and  IMAGE f s <> {}                     by IMAGE_EMPTY
    and  MIN_SET (IMAGE f s) IN (IMAGE f s)  by MIN_SET_LEM
   Thus CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s  by preimage_choice_property
     or rgcd p q IN s                        by IN_IMAGE
     or ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q).
*)
val ring_gcd_linear = store_thm(
  "ring_gcd_linear",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==>
     !p q. p IN R /\ q IN R ==> ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  `p = #1 * p + #0 * q` by rw[] >>
  `q = #0 * p + #1 * q` by rw[] >>
  Cases_on `p = #0` >-
  metis_tac[ring_gcd_def] >>
  Cases_on `q = #0` >-
  metis_tac[ring_gcd_def] >>
  qabbrev_tac `s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }` >>
  `rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))` by rw[ring_gcd_def] >>
  `!z. z IN s <=> ?a b. (z = a * p + b * q) /\ a IN R /\ b IN R /\ 0 < f (a * p + b * q)` by rw[Abbr`s`] >>
  `f p <> 0` by metis_tac[euclid_ring_map] >>
  `p IN s` by metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `IMAGE f s <> {}` by rw[IMAGE_EMPTY] >>
  `MIN_SET (IMAGE f s) IN (IMAGE f s)` by rw[MIN_SET_LEM] >>
  `CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s` by rw[preimage_choice_property] >>
  metis_tac[]);

(* Theorem: EuclideanRing r f ==> rgcd p q rdivides p /\ rgcd p q rdivides q /\
            !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q *)
(* Proof:
   If p = #0, rgcd #0 q = q        by ring_gcd_def
      rgcd #0 q rdivides #0        by ring_divides_zero
      rgcd #0 q rdivides q         by ring_divides_refl
      d rdivides q ==> d rdivides rgcd #0 q = q is trivial.
   If q = #0, rgcd p #0 = p        by ring_gcd_def
      rgcd p #0 rdivides p         by ring_divides_refl
      rgcd p #0 rdivides #0        by ring_divides_zero
      d rdivides p ==> d rdivides rgcd p #0 = p is trivial.
   If p <> #0 and q <> #0,
      Let s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
      Then rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))  by ring_gcd_def
      Since p = #1 * p + #0 * q
        and p <> #0 ==> f p <> 0   by euclid_ring_map
      hence p IN s                 by SPECIIFICATION
         or s <> {}                by MEMBER_NOT_EMPTY
        and IMAGE f s <> {}        by IMAGE_EMPTY
      Therefore, by MIN_SET_LEM,
            MIN_SET (IMAGE f s) IN (IMAGE f s)
        and !x. x IN (IMAGE f s) ==> MIN_SET (IMAGE f s) <= x
      Also, by preimage_choice_property,
            CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s /\
            f (CHOICE (preimage f s (MIN_SET (IMAGE f s)))) = MIN_SET (IMAGE f s)
      Hence,
          rgcd p q IN s /\ f (rgcd p q) = MIN_SET (IMAGE f s)
      and ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)
      Let g = rgcd p q
      Then by g IN s, 0 < f g
      Hence   g <> #0              by euclid_ring_map
      Also    g IN R               by ring_mult_element, ring_add_element
      Now for each of the goals:
      (1) g rdivides p
          Divide p by g,
          ?u t. u IN R /\ t IN R /\ (p = u * g + t) /\ f t < f g  by euclid_ring_property
          If t = #0, g rdivides p is true.
          If t <> #0, f t <> 0     by euclid_ring_map
          and t = p - u * g        by ring_sub_eq_add
                = p - u * (a * p + b * q)
                = #1 * p + - (u * a) * p + - (u * b) * q
                = (#1 + - (u * a)) * p + - (u * b) * q
          Hence t IN s
             so f t IN IMAGE f s          by IN_IMAGE
           thus f g <= f t                from MIN_SET
           which contradicts f t < f g    from euclid_ring_property
      (2) g rdivides q
          Divide q by g,
          ?u t. u IN R /\ t IN R /\ (q = u * g + t) /\ f t < f g  by euclid_ring_property
          If t = #0, g rdivides q is true.
          If t <> #0, f t <> 0     by euclid_ring_map
          and t = q - u * g        by ring_sub_eq_add
                = q - u * (a * p + b * q)
                = - u * (a * p + b * q) + q
                = - (u * b) * q + - (u * a) * p + #1 * q
                = - (u * a) * p + (#1 + - (u * b)) * q
          Hence t IN s
             so f t IN IMAGE f s          by IN_IMAGE
           thus f g <= f t                from MIN_SET
           which contradicts f t < f g    from euclid_ring_property
      (3) d rdivides p /\ d rdivides q ==> d rdivides g
          d rdivides p ==> ?u. u IN R /\ (p = u * d)    by ring_divides_def
          d rdivides q ==> ?v. v IN R /\ (q = v * d)    by ring_divides_def
          g = a * p + b * q
            = a * (u * d) + b * (v * d)
            = a * u * d + b * v * d       by ring_mult_assoc
            = (a * u + b * v) * d         by ring_mult_ladd
          Hence d rdivides g              by ring_divides_def
*)
val ring_gcd_is_gcd = store_thm(
  "ring_gcd_is_gcd",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
      rgcd p q rdivides p /\ rgcd p q rdivides q /\
      (!d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q)``,
  ntac 6 strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  Cases_on `p = #0` >-
  rw[ring_gcd_def, ring_divides_zero, ring_divides_refl] >>
  Cases_on `q = #0` >-
  rw[ring_gcd_def, ring_divides_zero, ring_divides_refl] >>
  qabbrev_tac `s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }` >>
  `rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))` by rw[ring_gcd_def] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  `p = #1 * p + #0 * q` by rw[] >>
  `!z. z IN s <=> ?a b. (z = a * p + b * q) /\ a IN R /\ b IN R /\ 0 < f (a * p + b * q)` by rw[Abbr`s`] >>
  `f p <> 0` by metis_tac[euclid_ring_map] >>
  `p IN s` by metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `IMAGE f s <> {}` by rw[IMAGE_EMPTY] >>
  `MIN_SET (IMAGE f s) IN (IMAGE f s) /\ !x. x IN (IMAGE f s) ==> MIN_SET (IMAGE f s) <= x` by rw[MIN_SET_LEM] >>
  `CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s /\
    (f (CHOICE (preimage f s (MIN_SET (IMAGE f s)))) = MIN_SET (IMAGE f s))` by rw[preimage_choice_property] >>
  `rgcd p q IN s /\ (f (rgcd p q) = MIN_SET (IMAGE f s))` by metis_tac[] >>
  `?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)` by metis_tac[] >>
  qabbrev_tac `g = rgcd p q` >>
  `0 < f g` by metis_tac[] >>
  `g <> #0` by metis_tac[euclid_ring_map, DECIDE ``!n. n < 0 ==> n <> 0``] >>
  `g IN R` by rw[] >>
  rpt strip_tac >| [
    `?u t. u IN R /\ t IN R /\ (p = u * g + t) /\ f t < f g` by rw[euclid_ring_property] >>
    `u * g IN R /\ a * p IN R /\ b * q IN R` by rw[] >>
    Cases_on `t = #0` >-
    metis_tac[ring_divides_def, ring_add_rzero, ring_mult_comm] >>
    `f t <> 0` by metis_tac[euclid_ring_map] >>
    `t IN s` by
  (`t = p - u * g` by metis_tac[ring_sub_eq_add] >>
    `_ = p - u * (a * p + b * q)` by rw[] >>
    `_ = p - (u * (a * p) + u * (b * q))` by rw_tac std_ss[ring_mult_radd] >>
    `_ = p - (u * a * p + u * b * q)` by rw_tac std_ss[ring_mult_assoc] >>
    `_ = p + (- (u * a * p + u * b * q))` by rw_tac std_ss[ring_sub_def] >>
    `_ = p + (- (u * a * p) + - (u * b * q))` by rw_tac std_ss[ring_neg_add, ring_mult_element] >>
    `_ = p + - (u * a * p) + - (u * b * q)` by rw_tac std_ss[ring_add_assoc, ring_mult_element, ring_neg_element] >>
    `_ = p + - (u * a) * p + - (u * b) * q` by rw_tac std_ss[ring_neg_mult, ring_mult_element] >>
    `_ = #1 * p + - (u * a) * p + - (u * b) * q` by rw_tac std_ss[ring_mult_lone] >>
    `_ = (#1 + - (u * a)) * p + - (u * b) * q` by rw_tac std_ss[ring_mult_ladd, ring_mult_element, ring_neg_element] >>
    `(#1 + - (u * a)) IN R /\ - (u * b) IN R` by rw[] >>
    metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``]) >>
    `f t IN IMAGE f s` by rw[] >>
    `f g <= f t` by metis_tac[] >>
    `!n m. n < m ==> ~(m <= n)` by decide_tac >>
    metis_tac[],
    `?u t. u IN R /\ t IN R /\ (q = u * g + t) /\ f t < f g` by rw[euclid_ring_property] >>
    `u * g IN R /\ a * p IN R /\ b * q IN R` by rw[] >>
    Cases_on `t = #0` >-
    metis_tac[ring_divides_def, ring_add_rzero, ring_mult_comm] >>
    `f t <> 0` by metis_tac[euclid_ring_map] >>
    `t IN s` by
  (`t = q - u * g` by metis_tac[ring_sub_eq_add] >>
    `_ = - (u * g) + q` by rw_tac std_ss[ring_sub_def, ring_add_comm, ring_neg_element] >>
    `_ = - u * g + q` by rw_tac std_ss[ring_neg_mult] >>
    `_ = - u * (a * p + b * q) + q` by rw[] >>
    `_ = - u * (a * p) + - u * (b * q) + q` by rw_tac std_ss[ring_mult_radd, ring_neg_element] >>
    `_ = - u * a * p + - u * b * q + q` by rw_tac std_ss[ring_mult_assoc, ring_neg_element] >>
    `_ = - u * a * p + (- u * b * q + q)` by rw_tac std_ss[ring_add_assoc, ring_mult_element, ring_neg_element] >>
    `_ = - u * a * p + (- u * b * q + #1 * q)` by rw_tac std_ss[ring_mult_lone] >>
    `_ = - u * a * p + (- u * b + #1) * q` by rw_tac std_ss[ring_mult_ladd, ring_mult_element, ring_neg_element] >>
    `- u * a  IN R /\ (- u * b + #1) IN R` by rw[] >>
    metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``]) >>
    `f t IN IMAGE f s` by rw[] >>
    `f g <= f t` by metis_tac[] >>
    `!n m. n < m ==> ~(m <= n)` by decide_tac >>
    metis_tac[],
    `?u. u IN R /\ (p = u * d)` by rw[GSYM ring_divides_def] >>
    `?v. v IN R /\ (q = v * d)` by rw[GSYM ring_divides_def] >>
    `g = a * (u * d) + b * (v * d)` by rw[] >>
    `_ = a * u * d + b * v * d` by rw[ring_mult_assoc] >>
    `_ = (a * u + b * v) * d` by rw[ring_mult_ladd] >>
    `a * u + b * v IN R` by rw[] >>
    metis_tac[ring_divides_def]
  ]);

(* Theorem: rgcd p q rdivides p /\ rgcd p q rdivides q *)
val ring_gcd_divides = save_thm("ring_gcd_divides",
  (CONJ (ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1)
        (ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1))
        |> DISCH ``p IN R /\ q IN R`` |> GEN ``q`` |> GEN ``p`` |> DISCH_ALL |> GEN_ALL);
(* > val ring_gcd_divides = |- !r f. EuclideanRing r f ==>
         !p q. p IN R /\ q IN R ==> rgcd p q rdivides p /\ rgcd p q rdivides q : thm *)

(* Theorem: d rdivides p /\ d rdivides q ==> d rdivides (rgcd p q) *)
val ring_gcd_property = save_thm("ring_gcd_property",
  ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> last
        |> DISCH ``p IN R /\ q IN R`` |> GEN ``q`` |> GEN ``p`` |> DISCH_ALL |> GEN_ALL);
(* > val ring_gcd_property = |- !r f. EuclideanRing r f ==>
         !p q. p IN R /\ q IN R ==> !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q : thm *)

(* Theorem: p IN R /\ q IN R ==> rgcd p q IN R *)
(* Proof:
   ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)  by ring_gcd_linear
   Hence (rgcd p q) IN R                                 by ring_mult_element, ring_add_element
*)
val ring_gcd_element = store_thm(
  "ring_gcd_element",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q IN R``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)` by rw[ring_gcd_linear] >>
  rw[]);

(* Theorem: rgcd p q = rgcd q p *)
(* Proof:
   If p = #0,
   LHS = rgcd #0 q = q = rgcd q #0 = RHS    by ring_gcd_def
   If q = #0,
   LHS = rgcd p #0 = p = rgcd #0 p = RHS    by ring_gcd_def
   If p <> #0 and q <> #0, by ring_gcd_def,
   rgcd p q = let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                 in CHOICE (preimage f s (MIN_SET (IMAGE f s))))
   rgcd q p = let s' = {a * q + b * p | (a,b) | a IN R /\ b IN R /\ 0 < f (a * q + b * p)}
                 in CHOICE (preimage f s' (MIN_SET (IMAGE f s'))))
   But s = s'  by exchanging a and b, and by ring_add_comm
   Hence rgcd p q = rgcd q p.
*)
val ring_gcd_sym = store_thm(
  "ring_gcd_sym",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> (rgcd p q = rgcd q p)``,
  rw_tac std_ss[ring_gcd_def] >>
  `s = s'` by
  (rw[Abbr`s`, Abbr`s'`, EXTENSION] >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  rw[EQ_IMP_THM] >| [
    qexists_tac `b` >>
    qexists_tac `a` >>
    rw[ring_add_comm],
    qexists_tac `b` >>
    qexists_tac `a` >>
    rw[ring_add_comm]
  ]) >>
  rw[]);

(* Theorem: atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q *)
(* Proof:
   Let g = rgcd p q
   Since g rdivides p        by ring_gcd_divides
   ?t. t IN R /\ p = t * g   by ring_divides_def
   Hence unit t or unit g    by irreducible_def
   If unit g, this is trivially true.
   If unit t, |/t exists     by ring_unit_has_inv
   so g = |/t * p,
   or p rdivides g.
   Since g rdivides q        by ring_gcd_divides
   p rdivides q              by ring_divides_trans
*)
val ring_irreducible_gcd = store_thm(
  "ring_irreducible_gcd",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==>
     !p. p IN R /\ atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  qabbrev_tac `g = rgcd p q` >>
  `g rdivides p /\ g rdivides q` by rw[ring_gcd_divides, Abbr`g`] >>
  `?t. t IN R /\ (p = t * g)` by rw[GSYM ring_divides_def] >>
  `g IN R` by rw[ring_gcd_element, Abbr`g`] >>
  `unit t \/ unit g` by metis_tac[irreducible_def] >| [
    `|/t IN R` by rw[ring_unit_inv_element] >>
    `|/t * p = |/t * t * g` by rw[ring_mult_assoc] >>
    `_ = #1 * g` by rw[ring_unit_linv] >>
    `_ = g` by rw[] >>
    `p rdivides g` by metis_tac[ring_divides_def] >>
    metis_tac[ring_divides_trans],
    rw[]
  ]);

(* Define ring ordering function *)
val ring_ordering_def = Define `
  ring_ordering (r:'a ring) (f:'a -> num) =
    !a b. a IN R /\ b IN R /\ b <> #0 ==> f a <= f (a * b)
`;

(* Theorem: EuclideanRing r /\ ring_ordering r f ==>
            !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p *)
(* Proof:
   Since q rdivides p:
   ?s. s IN R /\ (p = s * q)     by ring_divides_def
   Since p <> #0, s <> #0        by ring_mult_lzero
   Hence f q <= f (q * s)        by ring_ordering_def
              = f (s * q)        by ring_mult_comm
              = f p
*)
val ring_divides_le = store_thm(
  "ring_divides_le",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f /\ ring_ordering r f ==>
        !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `?s. s IN R /\ (p = s * q)` by rw[GSYM ring_divides_def] >>
  `_ = q * s` by rw[ring_mult_comm] >>
  metis_tac[ring_ordering_def, ring_mult_rzero]);

(* division and primality are preserved by isomorphism *)

Theorem ring_divides_iso:
  !r r_ f. Ring r /\ Ring r_ /\ RingIso f r r_ ==>
    !p q. p IN r.carrier /\ ring_divides r p q ==>
      ring_divides r_ (f p) (f q)
Proof
  rw[ring_divides_def]
  \\ qexists_tac`f s`
  \\ fs[RingIso_def, RingHomo_def]
  \\ rfs[MonoidHomo_def]
QED

Theorem ring_prime_iso:
  !r r_ f. Ring r /\ Ring r_ /\ RingIso f r r_ ==>
    !p. p IN r.carrier /\ ring_prime r p ==> ring_prime r_ (f p)
Proof
  rw[ring_prime_def]
  \\ `BIJ f r.carrier r_.carrier` by fs[RingIso_def]
  \\ `∃x y. a = f x /\ b = f y /\ x IN r.carrier /\ y IN r.carrier`
  by (
    fs[BIJ_DEF, SURJ_DEF]
    \\ res_tac \\ rw[]
    \\ metis_tac[] )
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ drule_then (drule_then drule) ring_iso_sym
  \\ strip_tac
  \\ first_x_assum(qspecl_then[`x`,`y`]mp_tac)
  \\ qspecl_then[`r`,`r_`,`f `]mp_tac ring_divides_iso
  \\ simp[] \\ strip_tac
  \\ impl_tac
  >- (
    `p = LINV f R (f p) /\ x = LINV f R (f x) /\ y = LINV f R (f y)`
    by metis_tac[BIJ_LINV_THM]
    \\ ntac 3 (pop_assum SUBST1_TAC)
    \\ `r.prod.op (LINV f R (f x)) (LINV f R (f y)) =
        LINV f R (r_.prod.op (f x) (f y))`
    by (
      qhdtm_x_assum`RingIso`mp_tac
      \\ simp_tac(srw_ss())[RingIso_def, RingHomo_def]
      \\ simp[MonoidHomo_def] )
    \\ pop_assum SUBST1_TAC
    \\ irule ring_divides_iso
    \\ metis_tac[BIJ_DEF, INJ_DEF] )
  \\ metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Principal Ideal Ring: Irreducibles and Primes                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN <p>.carrier ==> p rdivides x *)
(* Proof:
        x IN <p>.carrier
   iff  ?z. z IN R /\ (x = p * z)    by principal_ideal_element
   iff  z IN R /\ (x = z * p)        by ring_mult_comm
   iff  p rdivides x                 by ring_divides_def
*)
val principal_ideal_element_divides = store_thm(
  "principal_ideal_element_divides",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> !x. x IN <p>.carrier <=> p rdivides x``,
  rw[principal_ideal_element, ring_divides_def] >>
  metis_tac[ring_mult_comm]);

(* Theorem: q rdivides p <=> <p> << <q> *)
(* Proof:
   Note that <p> << r         by principal_ideal_ideal
         and <q> << r         by principal_ideal_ideal
   If part: q rdivides p ==> <p> << <q>
     This is to show <p>.carrier SUBSET <q>.carrier    by ideal_sub_ideal
     or p * R SUBSET q * R                             by principal_ideal_def
     Now q rdivides p
     ==> ?s. s IN R /\ (p = s * q)                     by ring_divides_def
     By coset_def, this is to show:
        ?z'. (s * q * z = q * z') /\ z' IN R
     But  s * q * z
        = q * s * z                                    by ring_mult_comm
        = q * (s * z)                                  by ring_mult_assoc
     Put z' = s * z, and z' IN R                       by ring_mult_element
  Only-if part: <p> << <q> ==> q rdivides p
     <p> << <q> means <p>.carrier SUBSET <q>.carrier   by ideal_sub_ideal
     Since p IN <p>.carrier                            by principal_ideal_has_element
           p IN <q>.carrier                            by SUBSET_DEF
     or    ?z. z IN R /\ (p = q * z)                   by principal_ideal_element
     i.e.  p = z * q                                   by ring_mult_comm
     Hence q rdivides p                                by ring_divides_def
*)
val principal_ideal_sub_implies_divides = store_thm(
  "principal_ideal_sub_implies_divides",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN R ==> (q rdivides p <=> <p> << <q>)``,
  rpt strip_tac >>
  `<p> << r /\ <q> << r` by rw[principal_ideal_ideal] >>
  rw[EQ_IMP_THM] >| [
    `<p>.carrier SUBSET <q>.carrier` suffices_by metis_tac[ideal_sub_ideal] >>
    rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
    `?s. s IN R /\ (p = s * q)` by rw[GSYM ring_divides_def] >>
    `s * q * z = q * s * z` by rw[ring_mult_comm] >>
    `_ = q * (s * z)` by rw[ring_mult_assoc] >>
    metis_tac[ring_mult_element],
    `<p>.carrier SUBSET <q>.carrier` by metis_tac[ideal_sub_ideal] >>
    `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
    `p IN <q>.carrier` by metis_tac[SUBSET_DEF] >>
    `?z. z IN R /\ (p = q * z)` by rw[GSYM principal_ideal_element] >>
    `_ = z * q` by rw[ring_mult_comm] >>
    metis_tac[ring_divides_def]
  ]);

(* Introduce temporary overlaods *)
val _ = temp_overload_on ("<a>", ``principal_ideal r a``);
val _ = temp_overload_on ("<b>", ``principal_ideal r b``);
val _ = temp_overload_on ("<u>", ``principal_ideal r u``);

(* Theorem: PrincipalIdealRing r ==> !p. atom p ==> rprime p *)
(* Proof:
   By ring_prime_def, this is to show:
   a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b
   By contradiction, assume ~(p rdivides a) /\ ~(p rdivides b).
       ~(p rdivides a)
   ==> ~(<a> << <p>)           by principal_ideal_sub_implies_divides
   ==> ~((<a> + <p>) << <p>)   by ideal_sum_sub_ideal
   Since PrincipalIdealRing r,
   ?u. u IN R /\ <a> + <p> = <u>    by PrincipalIdealRing_def
   But p IN <p>.carrier             by principal_ideal_has_element
   so  p IN (<a> + <p>).carrier     by ideal_sum_element
   Therefore
       p IN <u>.carrier             by above
   or  ?z. z IN R /\ p = u * z      by principal_ideal_element
   Since atom p, unit u or unit z   by irreducible_def
   If unit z,
   <p> = <u>                        by principal_ideal_eq_principal_ideal
   and <u> << <p>                   by ideal_refl
   which contradicts ~(<u> << <p>)  since <u> = <a> + <p>.
   Hence unit u,
   Since u IN <u>.carrier           by principal_ideal_has_element
      so <u> = r                    by ideal_with_unit
   Since #1 IN R                    by ring_one_element
   ?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)   by ideal_sum_element
   ?h k. h IN R /\ k IN R /\ #1 = a * h + p * k                 by principal_ideal_element
   Multiply by b,
   b = b * #1                       by ring_mult_rone
     = b * (a * h + p * k)          by substitution
     = b * (a * h) + b * (p * k)    by ring_mult_radd
     = b * a * h + b * p * k        by ring_mult_assoc
     = a * b * h + p * b * k        by ring_mult_comm
   But p rdivides a * b,
   ?s. s IN R /\ (a * b = s * p)    by ring_divides_def
   or  a * b = p * s                by ring_mult_comm
   Thus
   b = p * s * h + p * b * k        by substitution
     = p * (s * h) + p * (b * k)    by ring_mult_assoc
     = p * (s * h + b * k)          by ring_mult_radd
     = (s * h + b * k) * p          by ring_mult_comm
   Hence p rdivides b               by ring_divides_def
   which contradicts ~(p rdivides b).
*)
val principal_ideal_ring_atom_is_prime = store_thm(
  "principal_ideal_ring_atom_is_prime",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> rprime p``,
  rw[ring_prime_def] >>
  `Ring r` by metis_tac[PrincipalIdealRing_def] >>
  `p IN R` by rw[irreducible_element] >>
  spose_not_then strip_assume_tac >>
  `~(<a> << <p>)` by rw[GSYM principal_ideal_sub_implies_divides] >>
  `<a> << r /\ <p> << r` by rw[principal_ideal_ideal] >>
  `~((<a> + <p>) << <p>)` by rw[ideal_sum_sub_ideal] >>
  `(<a> + <p>) << r` by rw[ideal_sum_ideal] >>
  `?u. u IN R /\ (<a> + <p> = <u>)` by metis_tac[PrincipalIdealRing_def] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `#0 IN <a>.carrier` by rw[ideal_has_zero] >>
  `p = #0 + p` by rw[] >>
  `p IN <u>.carrier` by metis_tac[ideal_sum_element] >>
  `?z. z IN R /\ (p = u * z)` by rw[GSYM principal_ideal_element] >>
  `unit z \/ unit u` by metis_tac[irreducible_def] >-
  metis_tac[principal_ideal_eq_principal_ideal, ideal_sub_itself] >>
  `u IN <u>.carrier` by rw[principal_ideal_has_element] >>
  `<u> = r` by metis_tac[ideal_with_unit] >>
  `#1 IN R` by rw[] >>
  `?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)` by rw[GSYM ideal_sum_element] >>
  `?h k. h IN R /\ k IN R /\ (#1 = a * h + p * k)` by metis_tac[principal_ideal_element] >>
  `?s. s IN R /\ (a * b = s * p)` by rw[GSYM ring_divides_def] >>
  `_ = p * s` by rw[ring_mult_comm] >>
  `b = b * #1` by rw[] >>
  `_ = b * (a * h + p * k)` by metis_tac[] >>
  `_ = b * (a * h) + b * (p * k)` by rw[ring_mult_radd] >>
  `_ = b * a * h + b * p * k` by rw[ring_mult_assoc] >>
  `_ = a * b * h + p * b * k` by rw[ring_mult_comm] >>
  `_ = p * s * h + p * b * k` by metis_tac[] >>
  `_ = p * (s * h) + p * (b * k)` by rw[ring_mult_assoc] >>
  `_ = p * (s * h + b * k)` by rw[ring_mult_radd] >>
  `_ = (s * h + b * k) * p` by rw[ring_mult_comm] >>
  `s * h + b * k IN R` by rw[] >>
  metis_tac[ring_divides_def]);

(* Another proof: *)
(* Theorem: PrincipalIdealRing r ==> !p. atom p ==> rprime p *)
(* Proof:
   By ring_prime_def, this is to show:
   a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b
   Since p rdivides a * b,
   ?s. s IN R /\ (a * b = s * p)    by ring_divides_def
   or  a * b = p * s                by ring_mult_comm
   By contradiction, assume ~(p rdivides a) /\ ~(p rdivides b).
       ~(p rdivides a)
   ==> ~(a IN <p>.carrier)          by principal_ideal_element_divides
   ==> <a> + <p> <> <p>             by principal_ideal_sum_equal_ideal
   ==> <a> + <p> = r                by principal_ideal_ring_ideal_maximal
   Since #1 IN R                    by ring_one_element
   ?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)   by ideal_sum_element
   ?h k. h IN R /\ k IN R /\ #1 = a * h + p * k                 by principal_ideal_element
   Multiply by b,
   b = b * #1                       by ring_mult_rone
     = b * (a * h + p * k)          by substitution
     = b * (a * h) + b * (p * k)    by ring_mult_radd
     = b * a * h + b * p * k        by ring_mult_assoc
     = a * b * h + p * b * k        by ring_mult_comm
     = p * s * h + p * b * k        by substitution, a * b = p * s
     = p * (s * h) + p * (b * k)    by ring_mult_assoc
     = p * (s * h + b * k)          by ring_mult_radd
     = (s * h + b * k) * p          by ring_mult_comm
   Hence p rdivides b               by ring_divides_def
   which contradicts ~(p rdivides b).
*)
val principal_ideal_ring_irreducible_is_prime = store_thm(
  "principal_ideal_ring_irreducible_is_prime",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> rprime p``,
  rw[ring_prime_def] >>
  `Ring r` by metis_tac[PrincipalIdealRing_def] >>
  `p IN R` by rw[irreducible_element] >>
  `<a> << r /\ <p> << r` by rw[principal_ideal_ideal] >>
  `(<a> + <p>) << r /\ <p> << (<a> + <p>)` by rw[ideal_sum_ideal, ideal_sum_has_ideal_comm] >>
  spose_not_then strip_assume_tac >>
  `~(a IN <p>.carrier)` by metis_tac[principal_ideal_element_divides] >>
  `<a> + <p> <> <p>` by metis_tac[principal_ideal_sum_equal_ideal] >>
  `<a> + <p> = r` by metis_tac[principal_ideal_ring_ideal_maximal, ideal_maximal_def] >>
  `?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)` by rw[GSYM ideal_sum_element] >>
  `?h k. h IN R /\ k IN R /\ (#1 = a * h + p * k)` by metis_tac[principal_ideal_element] >>
  `?s. s IN R /\ (a * b = s * p)` by rw[GSYM ring_divides_def] >>
  `_ = p * s` by rw[ring_mult_comm] >>
  `b = b * #1` by rw[] >>
  `_ = b * (a * h + p * k)` by metis_tac[] >>
  `_ = b * (a * h) + b * (p * k)` by rw[ring_mult_radd] >>
  `_ = b * a * h + b * p * k` by rw[ring_mult_assoc] >>
  `_ = a * b * h + p * b * k` by rw[ring_mult_comm] >>
  `_ = p * s * h + p * b * k` by metis_tac[] >>
  `_ = p * (s * h) + p * (b * k)` by rw[ring_mult_assoc] >>
  `_ = p * (s * h + b * k)` by rw[ring_mult_radd] >>
  `_ = (s * h + b * k) * p` by rw[ring_mult_comm] >>
  `s * h + b * k IN R` by rw[] >>
  metis_tac[ring_divides_def]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
