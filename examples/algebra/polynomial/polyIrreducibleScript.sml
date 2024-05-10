(* ------------------------------------------------------------------------- *)
(* Irreducible Polynomials                                                   *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyIrreducible";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open fieldIdealTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;

open polyMonicTheory;
open polyDivisionTheory;
open polyFieldDivisionTheory;
open polyRootTheory;
open polyDividesTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Irreducible Polynomials Documentation                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   IPoly r        = irreducible (PolyRing r)
   ipoly p        = IPoly r p
   mifactor h z   = monic h /\ ipoly h /\ (z % h = |0|)
*)
(* Definitions and Theorems (# are exported):

   Irreducible polynomials:
   poly_irreducible_def            |- !r p. ipoly p <=> poly p /\ p <> |0| /\ ~ upoly p /\
                                      !x y. poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y
   poly_irreducible_not_unit       |- !r p. ipoly p ==> ~ upoly p
   poly_irreducible_poly           |- !r. !p. ipoly p ==> poly p
   poly_irreducible_nonzero        |- !r. !p. ipoly p ==> p <> |0|
   poly_irreducible_ne_poly_one    |- !r. Ring r ==> !p. ipoly p ==> p <> |1|
   poly_deg_1_irreducible          |- !r. Field r ==> !p. poly p /\ (deg p = 1) ==> ipoly p
   poly_irreducible_deg_nonzero    |- !r. Field r ==> !p. ipoly p ==> 0 < deg p
   poly_irreducible_property       |- !r. Field r ==> !p. ipoly p ==> p <> |0| /\ 0 < deg p
   poly_irreducible_ulead          |- !r. Field r ==> !p. ipoly p ==> ulead p
   poly_irreducible_pmonic         |- !r. Field r ==> !p. ipoly p ==> pmonic p
   poly_monic_irreducible_property |- !r. Field r ==> !p. monic p /\ ipoly p ==>
                                          poly p /\ 0 < deg p /\ unit (lead p)

   Irreducible Factors:
   poly_monic_irreducible_factor   |- !r. Field r ==> !h z. mifactor h z ==> pmonic h
   poly_X_add_c_irreducible        |- !r. Field r ==> !c. ipoly (X + |c|)
   poly_X_sub_c_irreducible        |- !r. Field r ==> !c. ipoly (X - |c|)
   poly_factor_irreducible         |- !r. Field r ==> !c. c IN R ==> ipoly (factor c)
   poly_reducible_has_factors      |- !r. Field r ==> !p. poly p /\ 0 < deg p /\ ~ipoly p ==>
                                      ?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y)
   poly_irreducible_factor_exists  |- !r. Field r ==> !p. poly p /\ 0 < deg p ==> ?q. ipoly q /\ q pdivides p
   poly_cmult_irreducible          |- !r. Field r ==> !c p. c IN R /\ poly p /\ 0 < deg p /\ ipoly (c * p) ==> ipoly p
   poly_irreducible_make_monic     |- !r. Field r ==> !p. ipoly p ==> ?c q. c IN R /\ monic q /\ ipoly q /\ (p = c * q)
   poly_monic_irreducible_factor_exists  |- !r. Field r ==> !p. poly p /\ 0 < deg p ==>
                                                ?q. monic q /\ ipoly q /\ q pdivides p
   poly_monic_divides_monic_irreducible  |- !r. Ring r ==> !p q. monic p /\ monic q /\ ipoly q ==>
                                                (p pdivides q <=> (p = |1|) \/ (p = q))
   poly_irreducible_monic  |- !r. Field r ==> !p. ipoly p ==> ?q. ipoly q /\ (deg q = deg p) /\ monic q
   poly_deg_2_irreducible  |- !r. Field r ==> !p. monic p /\ (deg p = 2) /\ (roots p = {}) ==> ipoly p

   Reducible Factors:
   poly_reducible_factor         |- !r. Field r ==> !p. poly p /\ 0 < deg p /\ ~ipoly p ==>
                                    ?q t. poly q /\ poly t /\ (p = q * t) /\
                                          0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p
   poly_monic_reducible_factors  |- !r. Field r ==> !p. monic p /\ 0 < deg p /\ ~ipoly p ==>
                                    ?q t. monic q /\ monic t /\ (p = q * t) /\
                                          0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p

*)

(* ------------------------------------------------------------------------- *)
(* Irreducible polynomials.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Overloads for polynomial ring properties *)
val _ = overload_on("IPoly", ``\r. irreducible (PolyRing r)``);

(* define irreducible polynomial by overloading *)
val _ = overload_on ("ipoly", ``\x. IPoly r x``);

(* Theorem: ipoly definition:
   ipoly p = (poly p) /\ (p <> |0|) /\ (~ upoly p) /\
             (!x y. poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y) *)
(* Proof:
   By irreducible_def |> ISPEC ``PolyRing (r:'a ring)`` |> SPEC ``p:'a poly``;
   |- ipoly p <=> p IN ring_nonzero (PolyRing r) /\
                  p NOTIN (Invertibles (PolyRing r).prod).carrier /\
                  !x y. x IN (PolyRing r).carrier /\ y IN (PolyRing r).carrier /\ (p = x * y) ==>
                        upoly x \/ upoly y : thm
   Expanding implications, this is to show:
   (1) poly p
           p IN ring_nonzero (PolyRing r)
       ==> p IN (PolyRing r)                      by ring_nonzero_element
       ==> poly p                                 by poly_ring_property
   (2) p <> |0|
           p IN ring_nonzero (PolyRing r)
       ==> p IN (PolyRing r).carrier DIFF {|0|}   by ring_nonzero_def
       ==> p NOTIN {|0|}                          by IN_DIFF
       ==> p <> |0|                               by IN_SING
   (3) poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y
       poly x /\ poly y ==>
       x IN (PolyRing r).carrier /\
       y IN (PolyRing r).carrier /\               by poly_ring_property
       (p = x * y) ==> upoly x /\ upoly y         by given implication
   (4) poly p /\ p <> |0| ==> p IN ring_nonzero (PolyRing r)
       poly p ==> p IN (PolyRing r).carrier       by poly_ring_property
       p <> |0| ==> p NOTIN {|0|}                 by IN_SING
       Hence p IN (PolyRing r).carrier DIFF {|0|} by IN_DIFF
       or p IN ring_nonzero (PolyRing r)          by ring_nonzero_def
   (5) x IN (PolyRing r).carrier /\ y IN (PolyRing r).carrier ==> upoly x \/ upoly y
       similar to (3), by poly_ring_property and given implication.
*)
val poly_irreducible_def = store_thm(
  "poly_irreducible_def",
  ``!(r:'a ring) (p:'a poly). ipoly p <=>
        (poly p) /\ (p <> |0|) /\ (~ upoly p) /\
        (!x y. poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y)``,
  rw_tac std_ss[irreducible_def, ring_nonzero_def, poly_ring_property, IN_DIFF, IN_SING, EQ_IMP_THM]);

(* Theorem: ipoly p ==> ~ upoly p *)
(* Proof: by irreducible_def. *)
val poly_irreducible_not_unit = store_thm(
  "poly_irreducible_not_unit",
  ``!(r:'a ring) p. ipoly p ==> ~ upoly p``,
  rw[irreducible_def]);

(* Theorem: ipoly p ==> poly p *)
(* Proof:
       ipoly p
   ==> p IN ring_nonzero (PolyRing r)   by irreducible_def
   ==> p IN (PolyRing r).carrier        by ring_nonzero_element
   ==> poly p                           by poly_ring_element
*)
val poly_irreducible_poly = store_thm(
  "poly_irreducible_poly",
  ``!r:'a ring. !p. ipoly p ==> poly p``,
  rw[irreducible_def, ring_nonzero_element, GSYM poly_ring_element]);

(* DO NOT export this! -- otherwise all "poly p" will try "ipoly p". *)
(* val _ = export_rewrites ["poly_irreducible_poly"]; *)

(* Theorem: ipoly p ==> p <> |0| *)
(* Proof:
       ipoly p
   ==> p IN ring_nonzero (PolyRing r)   by irreducible_def
   ==> p <> |0|                         by ring_nonzero_eq
*)
val poly_irreducible_nonzero = store_thm(
  "poly_irreducible_nonzero",
  ``!r:'a ring. !p. ipoly p ==> p <> |0|``,
  rw[irreducible_def, ring_nonzero_eq]);

(* Theorem: Ring r ==> !p. ipoly p ==> p <> |1| *)
(* Proof:
   Since ipoly p ==> ~(upoly p)    by poly_irreducible_not_unit
     but upoly |1|                 by poly_unit_one
      so p <> |1|
*)
val poly_irreducible_ne_poly_one = store_thm(
  "poly_irreducible_ne_poly_one",
  ``!r:'a ring. Ring r ==> !p. ipoly p ==> p <> |1|``,
  metis_tac[poly_irreducible_not_unit, poly_unit_one]);

(* Theorem: Field r ==> poly p /\ deg p = 1 ==> ipoly p *)
(* Proof:
   By irreducible_def, this is to show:
   (1) poly p /\ deg p = 1 ==> p IN ring_nonzero (PolyRing r)
       Since deg |0| = 0                         by poly_deg_zero
       p <> |0|, hence true                      by ring_nonzero_eq, poly_ring_element.
   (2) poly p /\ deg p = 1 ==> p NOTIN (Invertibles (PolyRing r).prod).carrier
           p IN (Invertibles (PolyRing r).prod).carrier
       <=> p <> |0| /\ deg p = 0                 by poly_field_units
       Hence true.
   (3) x IN (PolyRing r).carrier /\ y IN (PolyRing r).carrier /\ deg (x * y) = 1 ==> upoly x /\ upoly y
       Since deg |0| = 0                         by poly_deg_zero
       x <> |0| /\ y <> |0|                      by poly_mult_lzero, poly_mult_rzero
       also poly x /\ poly y                     by poly_ring_element
       so   deg x + deg y = 1                    by poly_deg_mult_nonzero
       Therefore deg x = 0 or deg y = 0          by arithemtic
       If deg x = 0, with x <> |0| ==> upoly x   by poly_field_units
       If deg y = 0, with y <> |0| ==> upoly y   by poly_field_units
*)
val poly_deg_1_irreducible = store_thm(
  "poly_deg_1_irreducible",
  ``!r:'a field. Field r ==> !p. poly p /\ (deg p = 1) ==> ipoly p``,
  rw[irreducible_def] >| [
    `p <> |0|` by metis_tac[poly_deg_zero, DECIDE ``0 <> 1``] >>
    `Ring r` by rw[] >>
    metis_tac[ring_nonzero_eq, poly_ring_element],
    metis_tac[poly_field_units, DECIDE ``0 <> 1``],
    `1 <> 0` by decide_tac >>
    `x <> |0| /\ y <> |0|` by metis_tac[poly_mult_lzero, poly_mult_rzero, poly_deg_zero] >>
    `poly x /\ poly y` by rw[GSYM poly_ring_element] >>
    `deg x + deg y = 1` by metis_tac[poly_deg_mult_nonzero] >>
    `(deg x = 0) \/ (deg y = 0)` by rw_tac arith_ss[] >-
    rw[poly_field_units] >>
    rw[poly_field_units]
  ]);

(* Theorem: Field r ==> !p. ipoly p ==> 0 < deg p *)
(* Proof:
   By contradiction, suppose deg p = 0
   But ipoly p ==> poly p /\  by poly_irreducible_poly
                   p <> |0|   by poly_irreducible_nonzero
   So  ?h. h IN R /\ h <> #0
       /\ (p = [h])           by poly_deg_eq_zero
   This means: upoly p        by poly_field_const_unit
   But ipoly p ==> ~(upoly p) by poly_irreducible_def
   which is a contradiction.
*)
val poly_irreducible_deg_nonzero = store_thm(
  "poly_irreducible_deg_nonzero",
  ``!r:'a field. Field r ==> !p. ipoly p ==> 0 < deg p``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `deg p = 0` by decide_tac >>
  `p <> |0|` by rw[poly_irreducible_nonzero] >>
  `poly p` by rw[poly_irreducible_poly] >>
  `?h. h IN R /\ h <> #0 /\ (p = [h])` by metis_tac[poly_deg_eq_zero] >>
  `upoly p` by rw[poly_field_const_unit] >>
  metis_tac[poly_irreducible_def]);

(* Theorem: Field r ==> !p. ipoly p ==> p <> |0| /\ 0 < deg p *)
(* Proof: by poly_irreducible_nonzero, poly_irreducible_deg_nonzero *)
val poly_irreducible_property = store_thm(
  "poly_irreducible_property",
  ``!r:'a field. Field r ==> !p. ipoly p ==> p <> |0| /\ 0 < deg p``,
  rw_tac std_ss[poly_irreducible_nonzero, poly_irreducible_deg_nonzero]);

(* Theorem: Field r ==> !p. ipoly p ==> ulead p *)
(* Proof:
   Note poly p        by poly_irreducible_poly
    and p <> |0|      by poly_irreducible_nonzero
    ==> ulead p       by poly_field_poly_ulead
*)
val poly_irreducible_ulead = store_thm(
  "poly_irreducible_ulead",
  ``!r:'a field. Field r ==> !p. ipoly p ==> ulead p``,
  rw_tac std_ss[poly_irreducible_poly, poly_irreducible_nonzero, poly_field_poly_ulead]);

(* Theorem: Field r ==> !p. ipoly p ==> pmonic p *)
(* Proof:
   Note poly p        by poly_irreducible_poly
    and 0 < deg p     by poly_irreducible_deg_nonzero
    ==> pmonic p      by poly_field_poly_pmonic
*)
val poly_irreducible_pmonic = store_thm(
  "poly_irreducible_pmonic",
  ``!r:'a field. Field r ==> !p. ipoly p ==> pmonic p``,
  rw_tac std_ss[poly_irreducible_poly, poly_irreducible_deg_nonzero, poly_field_poly_pmonic]);

(* Theorem: Field r ==> !p. monic p /\ ipoly p ==> poly p /\ 0 < deg p /\ unit (lead p) *)
(* Proof:
   monic p ==> poly p /\ lead p = #1    by poly_monic_def
   Hence  unit (lead p)                 by ring_unit_one
   ipoly p ==> p <> |0|                 by poly_irreducible_nonzero
   ipoly p ==> ~upoly p                 by poly_irreducible_not_unit
   Hence  deg p <> 0                    by poly_field_units
   or 0 < deg p                         by decide_tac
*)
val poly_monic_irreducible_property = store_thm(
  "poly_monic_irreducible_property",
  ``!r:'a field. Field r ==> !p. monic p /\ ipoly p ==> poly p /\ 0 < deg p /\ unit (lead p)``,
  rw[poly_monic_def] >>
  `p <> |0|` by rw[poly_irreducible_nonzero] >>
  `deg p <> 0` by metis_tac[poly_irreducible_not_unit, poly_field_units] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Irreducible Factors.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define monic irreducible factor *)
val _ = overload_on ("mifactor", ``\h z. monic h /\ ipoly h /\ (z % h = |0|)``);

(* Theorem: Field r ==> !h z. mifactor h z ==> pmonic h *)
(* Proof:
   This is to show: ipoly h ==> 0 < deg h
   which is true by poly_irreducible_deg_nonzero
*)
val poly_monic_irreducible_factor = store_thm(
  "poly_monic_irreducible_factor",
  ``!r:'a field. Field r ==> !h z. mifactor h z ==> pmonic h``,
  rw[poly_irreducible_deg_nonzero]);

(* Theorem: ipoly (X + |c|) *)
(* Proof:
   Since poly (X + |c|)       by poly_X_add_c
     and deg (X + |c|) = 1    by poly_deg_X_add_c
   Hence ipoly (X + |c|)      by poly_deg_1_irreducible
*)
val poly_X_add_c_irreducible = store_thm(
  "poly_X_add_c_irreducible",
  ``!r:'a field. Field r ==> !c:num. ipoly (X + |c|)``,
  rw[poly_X_add_c, poly_deg_X_add_c, poly_deg_1_irreducible]);

(* Theorem: ipoly (X - |c|) *)
(* Proof:
   Since poly (X - |c|)       by poly_X_sub_c
     and deg (X - |c|) = 1    by poly_deg_X_sub_c
   Hence ipoly (X - |c|)      by poly_deg_1_irreducible
*)
val poly_X_sub_c_irreducible = store_thm(
  "poly_X_sub_c_irreducible",
  ``!r:'a field. Field r ==> !c:num. ipoly (X - |c|)``,
  rw[poly_X_sub_c, poly_deg_X_sub_c, poly_deg_1_irreducible]);

(* Theorem: Field r ==> !c. c IN R ==> ipoly (factor c) *)
(* Proof:
   Note poly (factor c)        by poly_factor_poly
    and deg (factor c) = 1     by poly_factor_deg
   Thus ipoly (factor c)       by poly_deg_1_irreducible
*)
val poly_factor_irreducible = store_thm(
  "poly_factor_irreducible",
  ``!r:'a field. Field r ==> !c. c IN R ==> ipoly (factor c)``,
  rw[poly_factor_poly, poly_factor_deg, poly_deg_1_irreducible]);

(* Theorem: Field r ==> !p. poly p /\ 1 < deg p /\ ~ipoly p ==>
            ?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y) *)
(* Proof:
   Since deg p <> 0
         p <> |0|      by poly_deg_zero
      so ~(upoly p)    by poly_field_units
    thus ~(!x y. poly x /\ poly y /\ (p = x * y) ==> upoly x \/ upoly y)  by poly_irreducible_def
      or ?x y. poly x /\ poly y /\ (p = x * y) /\ ~upoly x /\ ~upoly y
   Hence goal is: poly x /\ poly y /\ ~upoly x /\ ~upoly y ==>
                  ?x' y'. poly x' /\ poly y' /\ 0 < deg x' /\ 0 < deg y' /\ (x * y = x' * y')
     Now x <> |0| /\ y <> |0|      by poly_mult_lzero, poly_mult_rzero
      so deg x <> 0 /\ deg y <> 0  by poly_field_units
      or 0 < deg x /\ 0 < deg y
     So just take x' = x, y' = y.
*)
val poly_reducible_has_factors = store_thm(
  "poly_reducible_has_factors",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p /\ ~ipoly p ==>
            ?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y)``,
  rpt strip_tac >>
  `!n. 0 < n <=> n <> 0` by decide_tac >>
  `p <> |0|` by metis_tac[poly_deg_zero] >>
  metis_tac[poly_irreducible_def, poly_field_units, poly_mult_lzero, poly_mult_rzero]);

(* Theorem: Field r ==> !p. poly p /\ 0 < deg p ==> ?q. ipoly q /\ q pdivides p *)
(* Proof:
   By complete induction on (deg p).
   If ipoly p,
      Take q = p. p pdivides p                                        by poly_divides_reflexive
   If ~(ipoly p),
      ?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ p = x * y   by poly_reducible_has_factors
      i.e.  y pdivides p                                              by poly_divides_def
      Now   x <> |0| /\ y <> |0|                                      by poly_deg_zero
      and   deg p = deg x + deg y                                     by poly_deg_mult_nonzero
      i.e.  deg y < deg p                                             as 0 < deg x
      Hence ?q. ipoly q /\ q pdivides y                               by induction hypothesis
        and q pdivides y /\ y pdivides p ==> q pdivides p             by poly_divides_transitive
*)
val poly_irreducible_factor_exists = store_thm(
  "poly_irreducible_factor_exists",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p ==> ?q. ipoly q /\ q pdivides p``,
  rpt strip_tac >>
  completeInduct_on `deg p` >>
  rw[] >>
  `Ring r` by rw[] >>
  Cases_on `ipoly p` >-
  metis_tac[poly_divides_reflexive] >>
  `?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y)` by rw[poly_reducible_has_factors] >>
  `y pdivides p` by metis_tac[poly_divides_def] >>
  `deg x <> 0 /\ deg y <> 0` by decide_tac >>
  `x <> |0| /\ y <> |0|` by metis_tac[poly_deg_zero] >>
  `deg p = deg x + deg y` by rw[poly_deg_mult_nonzero] >>
  `deg y < deg p` by decide_tac >>
  `?q. ipoly q /\ q pdivides y` by rw[] >>
  metis_tac[poly_divides_transitive, poly_irreducible_poly]);

(* Theorem: Field r ==> !c p. c IN R /\ poly p /\ 0 < deg p /\ ipoly (c * p) ==> ipoly p *)
(* Proof:
   By contradiction. Suppose ~(ipoy p).
   Then ?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y)  by poly_reducible_has_factors
   and c * p = c * (x * y)
             = (c * x) * y      by poly_cmult_mult
   Thus (c * p) has a factors (c * x) and y.
    Now 0 < deg y ==> ~upoly y  by poly_field_units
   Also poly (c * x)            by poly_cmult_poly
  Since ipoly (c * p),
        c * p <> |0|            by poly_irreducible_nonzero
  Hence c <> #0                 by poly_cmult_lzero
     so deg (c * x) = deg x     by poly_field_deg_cmult
     or deg (c * x) <> 0        by 0 < deg x
   Thus ~upoly (c * x)          by poly_field_units
   which contradicts the fact ipoly (c * p).
*)
val poly_cmult_irreducible = store_thm(
  "poly_cmult_irreducible",
  ``!r:'a field. Field r ==> !c p. c IN R /\ poly p /\ 0 < deg p /\ ipoly (c * p) ==> ipoly p``,
  spose_not_then strip_assume_tac >>
  `?x y. poly x /\ poly y /\ 0 < deg x /\ 0 < deg y /\ (p = x * y)` by rw[poly_reducible_has_factors] >>
  `c * p = c * x * y` by rw[poly_cmult_mult] >>
  `deg y <> 0` by decide_tac >>
  `~upoly y` by metis_tac[poly_field_units] >>
  `poly (c * x)` by rw[] >>
  `c * p <> |0|` by rw[poly_irreducible_nonzero] >>
  `c <> #0` by metis_tac[poly_cmult_lzero, field_is_ring] >>
  `deg (c * x) = deg x` by rw[poly_field_deg_cmult] >>
  `deg (c * x) <> 0` by decide_tac >>
  `~upoly (c * x)` by metis_tac[poly_field_units] >>
  metis_tac[poly_irreducible_def]);

(* Theorem: ipoly p ==> ?c q. c IN R /\ monic q /\ ipoly q /\ (p = c * q) *)
(* Proof:
   Since ipoly p ==> poly p                       by poly_irreducible_poly
         ?c q. c IN R /\ monic q /\ (p = c * q)   by poly_field_make_monic
     Now poly q                                   by poly_monic_def
     and q <> |0|                                 by poly_monic_nonzero
    Also p <> |0|                                 by poly_irreducible_nonzero
      so c <> #0                                  by poly_cmult_lzero
    with deg p = deg q                            by poly_field_deg_cmult
   Since 0 < deg p                                by poly_irreducible_deg_nonzero
      so 0 < deg q                                by above
   Therefore ipoly (c * q) ==> ipoly q            by poly_cmult_irreducible
*)
val poly_irreducible_make_monic = store_thm(
  "poly_irreducible_make_monic",
  ``!r:'a field. Field r ==> !p. ipoly p ==> ?c q. c IN R /\ monic q /\ ipoly q /\ (p = c * q)``,
  rpt strip_tac >>
  `poly p` by rw[poly_irreducible_poly] >>
  `?c q. c IN R /\ monic q /\ (p = c * q)` by rw[poly_field_make_monic] >>
  `poly q` by rw[] >>
  `q <> |0|` by rw[poly_monic_nonzero] >>
  `p <> |0|` by rw[poly_irreducible_nonzero] >>
  `c <> #0` by metis_tac[poly_cmult_lzero, field_is_ring] >>
  `deg p = deg q` by rw[poly_field_deg_cmult] >>
  `0 < deg p` by rw[poly_irreducible_deg_nonzero] >>
  metis_tac[poly_cmult_irreducible]);

(* Theorem: Field r ==> !p. poly p /\ 0 < deg p ==> ?q. monic q /\ ipoly q /\ q pdivides p *)
(* Proof:
   Since poly p /\ 0 < deg p
     ==> ?t. ipoly t /\ t pdivides p    by poly_irreducible_factor_exists
      so ?c t. c IN R /\ monic q /\ ipoly q /\ (t = c * q)  by poly_irreducible_make_monic
     Now q pdivides t                   by poly_divides_cmult_alt
     With t pdivides p                  by above
     Thus q pdivides p                  by poly_divides_transitive
*)
val poly_monic_irreducible_factor_exists = store_thm(
  "poly_monic_irreducible_factor_exists",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p ==> ?q. monic q /\ ipoly q /\ q pdivides p``,
  rpt strip_tac >>
  `?t. ipoly t /\ t pdivides p` by rw[GSYM poly_irreducible_factor_exists] >>
  `?c q. c IN R /\ monic q /\ ipoly q /\ (t = c * q)` by rw[poly_irreducible_make_monic] >>
  `poly q /\ poly t` by rw[] >>
  metis_tac[poly_divides_cmult_alt, poly_divides_transitive, field_is_ring]);

(* Theorem: Ring r ==> !p q. monic p /\ monic q /\ ipoly q ==>
                        (p pdivides q <=> ((p = |1|) \/ (p = q))) *)
(* Proof:
   If part: p pdivides q ==> (p = |1|) \/ (p = q)
      Note p pdivides q
       ==> ?s. poly s /\ (q = s * p)     by poly_divides_def
       ==> upoly s \/ upoly p            by poly_irreducible_def
      If upoly s,
         Then ?t. upoly t /\ (s * t = |1|)   by poly_unit_property
          and poly t                         by poly_unit_poly
              t * q
            = t * (s * p)                by above
            = t * s * p                  by poly_mult_assoc
            = s * t * p                  by poly_mult_comm
            = |1| * p                    by above
            = p                          by poly_mult_lone
         Thus q pdivides p               by poly_divides_def
         With p pdivides q               by given
          ==> p = q                      by poly_monic_divides_antisymmetric
      If upoly p
         With monic p                    by given
          ==> p = |1|                    by poly_unit_monic
   Only-if part: (p = |1|) \/ (p = q) ==> p pdivides q
      If p = |1|, true                   by poly_one_divides_all
      If p = q, true                     by poly_divides_reflexive
*)
val poly_monic_divides_monic_irreducible = store_thm(
  "poly_monic_divides_monic_irreducible",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ monic q /\ ipoly q ==>
               (p pdivides q <=> ((p = |1|) \/ (p = q)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
    `poly p /\ poly q` by rw[] >>
    `upoly s \/ upoly p` by metis_tac[poly_irreducible_def] >| [
      `?t. upoly t /\ (s * t = |1|)` by metis_tac[poly_unit_property] >>
      `poly t` by rw[poly_unit_poly] >>
      `t * q = t * s * p` by rw[poly_mult_assoc] >>
      `_ = p` by rw[poly_mult_comm] >>
      `q pdivides p` by metis_tac[poly_divides_def] >>
      metis_tac[poly_monic_divides_antisymmetric],
      rw[GSYM poly_unit_monic]
    ],
    rw[poly_one_divides_all],
    rw[poly_divides_reflexive]
  ]);

(* Theorem: ipoly p ==> ?q. ipoly q /\ (deg q = deg p) /\ unit (lead q) *)
(* Proof:
       ipoly p
   ==> poly p                                      by poly_irreducible_poly
   and  p <> |0|                                   by poly_irreducible_nonzero
   Also lead p <> #0                               by poly_lead_nonzero
   so |/lead p <> #0  /\ |/lead p IN R             by field_inv_element, field_inv_nonzero
   Let q = |/ (lead p) * p
   Then this is to show:
   (1) ipoly ( |/ (lead p) * p)
       Since |/ (lead p) * p = [|/ (lead p)] * p   by poly_mult_lconst
       We have poly [|/ (lead p)]                  by poly_nonzero_element_poly
           and [|/ (lead p)] <> |0|                by poly_zero
       Also    deg [|/ (lead p)] = 0               by poly_deg_const
       Thus    upoly [|/ (lead p)]                 by poly_field_units
       Now  Ring (PolyRing r)                      by poly_ring_ring
       and  |1| <> |0|                             by poly_field_one_ne_zero
       Hence true                                  by irreducible_associates
   (2) deg ( |/ (lead p) * p) = deg p
       True by poly_field_deg_cmult.
   (3) monic ( |/ (lead p) * p)
       Since lead ( |/ (lead p) * p)
           = |/ (lead p) * lead p                  by poly_lead_cmult
           = #1                                    by field_mult_linv
       True by poly_monic_def.
*)
(* Example of Debugging *)
fun print_tac s g = (print (s^"\n"); ALL_TAC g);
val poly_irreducible_monic = store_thm(
  "poly_irreducible_monic",
  ``!r:'a field. Field r ==> !p. ipoly p ==> ?q. ipoly q /\ (deg q = deg p) /\ monic q``,
  print_tac "Start: poly_irreducible_monic" >>
  rpt strip_tac >>
  `poly p` by rw[poly_irreducible_poly] >>
  `p <> |0|` by rw[poly_irreducible_nonzero] >>
  `lead p <> #0` by rw[poly_lead_nonzero] >>
  `lead p IN R` by rw[] >>
  `lead p IN R+` by metis_tac[field_nonzero_eq] >>
  `|/ (lead p) IN R` by rw[field_inv_element] >>
  `|/ (lead p) <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
  qexists_tac `|/ (lead p) * p` >>
  print_tac "About to rw and split" >>
  rw_tac std_ss[] >| [
    print_tac "Case 1" >>
    `|/ (lead p) * p = [|/ (lead p)] * p` by rw[poly_mult_lconst] >>
    `poly [|/ (lead p)] /\ [|/ (lead p)] <> |0|` by rw[] >>
    `deg [|/ (lead p)] = 0` by rw[] >>
    `upoly [|/ (lead p)]` by rw[poly_field_units] >>
    `Ring (PolyRing r)` by rw[poly_ring_ring] >>
    `|1| <> |0|` by rw[] >>
    metis_tac[irreducible_associates, poly_ring_element],
    print_tac "Case 2" >> rw[poly_field_deg_cmult],
    print_tac "Case 3" >> rw[poly_monic_def]
  ]);

(* Theorem: Ring r /\ monic p /\ poly q /\ p * q = |1| ==> monic q *)
(* Proof:
   monic p ==> poly p            by poly_monic_poly
   deg (p * q) = deg p + deq q   by poly_monic_deg_mult
   deg |1| = 0                   by poly_deg_one
   In a Ring, poly p is never invertible!
*)

(* Theorem: Field r /\ monic p /\ deg p = 2 /\ roots p = {} ==> ipoly p *)
(* Proof:
   By irreducible_def, this is to show:
   (1) p IN ring_nonzero (PolyRing r)
       monic p ==> poly p                           by poly_monic_poly
       poly p ==> p IN ring_nonzero (PolyRing r)    by poly_ring_element
       p <> []                                      by poly_deg_eq_zero
       Hence true                                   by ring_nonzero_def
   (2) p NOTIN (Invertibles (PolyRing r).prod).carrier
       Expanding by defintions, this is to show: ~poly y \/ p * y <> |1| \/ y * p <> |1|
       By contradiction, assume poly y /\ p * y = |1| /\ y * p = |1|.
       Since |1| <> |0|      by poly_one_ne_poly_zero
       p <> |0| /\ y <> |0|  by poly_mult_rzero
       Hence lead y <> #0    by poly_lead_nonzero
       Since lead p = #1     by poly_monic_def
       Hence lead p * lead y = lead y               by ring_mult_lone
                             <> #0                  by above
       Then  deg (p * y) = deg p + deg y            by weak_deg_mult_nonzero
       Since deg |1| = 0                            by poly_deg_one
       We have         0 = deg p + deg y
       or    deg p = 0                              by ADD_EQ_0
       which contradicts deg p = 2.
   (3) monic (x * y) /\ poly x /\ poly y /\ (roots (x * y) = {}) ==> upoly x \/ upoly y
       Since monic (x * y) means lead (x * y) = #1  by poly_monic_def
       but lead |0| = #0                            by poly_lead_zero
       So  x <> |0| /\ y <> |0|                     by poly_mult_lzero, poly_mult_rzero
       Now deg (x * y) = deg x + deg y              by poly_deg_mult_nonzero
       and lead (x * y) = lead x * lead y           by poly_lead_mult
       The current goal is: upoly x \/ upoly y
       Expanding by poly_field_units,
       goal becomes: (deg x = 0) \/ (deg y = 0)
       By contradiction, assume deg x <> 0 /\ deg y <> 0.
       Then  (deg x = 1) /\ (deg y = 1)             by ADD_EQ_2
       Apply poly_field_make_monic:
          x = cx * qx    for some cx IN R and monic qx
          y = cy * qy    for some cy IN R and monic qy
       Now   cx <> #0 /\ cy <> #0                   by poly_cmult_lzero
        so   (deg qx = 1) /\ (deg qy = 1)           by poly_field_deg_cmult
       Hence ?xc. xc IN R /\ (qx = factor xc)       by poly_monic_deg1_factor
        Thus root x xc                              by poly_factor_root
         and roots x <> {}                          by poly_roots_member
       Since roots (x * y) = roots x UNION roots y  by poly_roots_mult
       This is a contradiction                      by EMPTY_UNION
*)
val poly_deg_2_irreducible = store_thm(
  "poly_deg_2_irreducible",
  ``!r:'a field. Field r ==> !p. monic p /\ (deg p = 2) /\ (roots p = {}) ==> ipoly p``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly p /\ (lead p = #1)` by rw[poly_monic_def] >>
  rw[irreducible_def] >| [
    rw[ring_nonzero_def, poly_ring_element] >>
    metis_tac[poly_deg_zero, poly_zero, DECIDE ``0 <> 2``],
    rw[Invertibles_def, monoid_invertibles_def, poly_ring_element] >>
    spose_not_then strip_assume_tac >>
    `|1| <> |0|` by rw[] >>
    `p <> |0| /\ y <> |0|` by metis_tac[poly_mult_rzero] >>
    `deg (p * y) = deg p + deg y` by rw[poly_deg_mult_nonzero] >>
    `deg |1| = 0` by rw[] >>
    `(deg p = 0) /\ (deg y = 0)` by metis_tac[ADD_EQ_0] >>
    decide_tac,
    `poly x /\ poly y` by rw[GSYM poly_ring_element] >>
    `lead |0| = #0` by rw[] >>
    `x <> |0| /\ y <> |0|` by metis_tac[poly_mult_lzero, poly_mult_rzero] >>
    `deg (x * y) = deg x + deg y` by rw[GSYM poly_deg_mult_nonzero] >>
    `lead (x * y) = lead x * lead y` by rw[GSYM poly_lead_mult] >>
    rw[poly_field_units] >>
    spose_not_then strip_assume_tac >>
    `(deg x = 1) /\ (deg y = 1)` by metis_tac[ADD_EQ_2, NOT_ZERO_LT_ZERO] >>
    `?cx qx. cx IN R /\ monic qx /\ (x = cx * qx)` by rw[poly_field_make_monic] >>
    `?cy qy. cy IN R /\ monic qy /\ (y = cy * qy)` by rw[poly_field_make_monic] >>
    `cx <> #0 /\ cy <> #0` by metis_tac[poly_cmult_lzero, poly_monic_poly] >>
    `(deg qx = 1) /\ (deg qy = 1)` by metis_tac[poly_field_deg_cmult, poly_monic_poly] >>
    `?xc. xc IN R /\ (qx = factor xc)` by rw[poly_monic_deg1_factor] >>
    `root x xc` by metis_tac[poly_factor_root] >>
    `roots x <> {}` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    metis_tac[poly_roots_mult, EMPTY_UNION]
  ]);

(* ------------------------------------------------------------------------- *)
(* Reducible Factors                                                         *)
(* ------------------------------------------------------------------------- *)

(*
> irreducible_def |> ISPEC ``(PolyRing r)``;
val it = |- !z. ipoly z <=>
     z IN ring_nonzero (PolyRing r) /\
     z NOTIN (Invertibles (PolyRing r).prod).carrier /\
     !x y. x IN (PolyRing r).carrier /\ y IN (PolyRing r).carrier /\ (z = x * y) ==> upoly x \/ upoly y: thm
*)

(* Theorem: Field r ==> !p. poly p /\ 0 < deg p /\ ~(ipoly p) ==>
      ?q t. poly q /\ poly t /\ (p = q * t) /\ 0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p *)
(* Proof:
   Since 0 < deg p, p <> |0|                       by poly_deg_zero
   By irreducible_def, this is to show:
   (1) poly p /\ p <> |0| /\ p NOTIN ring_nonzero (PolyRing r) ==> ...
           poly p /\ p <> |0|
       <=> p IN (PolyRing r).carrier /\ p <> |0|   by poly_ring_element
       <=> p IN ring_nonzero (PolyRing r)          by ring_nonzero_eq
       This contradicts with p NOTIN ring_nonzero (PolyRing r)
   (2) poly p /\ p <> |0| /\ deg p <> 0 /\ upoly p ==> ...
       upoly p <=> p <> |0| /\ (deg p = 0)         by poly_field_units
       This contradicts with deg p <> 0.
   (3) x IN (PolyRing r).carrier /\ y IN (PolyRing r).carrier /\
       ~(upoly x) /\ ~(upoly y) /\ deg (x * y) <> 0 ==>
       ?q t. poly q /\ poly t /\ (x * y = q * t) /\ deg q < deg (x * y) /\ deg t < deg (x * y)
       x IN (PolyRing r).carrier <=> poly x        by poly_ring_element
       y IN (PolyRing r).carrier <=> poly y        by poly_ring_element
       deg (x * y) <> 0 ==> x <> |0| and y <> |0|  by poly_deg_zero, poly_mult_zero
       Since ~(upoly x) /\ ~(upoly y), deg x <> 0 /\ deg y <> 0   by poly_field_units
       But deg (x * y) = deg x + deg y             by poly_deg_mult_nonzero
       Therefore deg x < deg x + deg y             by arithmetic
             and deg y < deg x + deg y             by arithmetic
             and 0 < deg x /\ 0 < deg y            by deg x <> 0, deg y <> 0
       Thus take q = x, t = y, and the result follows.
*)
val poly_reducible_factors = store_thm(
  "poly_reducible_factors",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p /\ ~(ipoly p) ==>
   ?q t. poly q /\ poly t /\ (p = q * t) /\ 0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p``,
  rpt strip_tac >>
  `deg p <> 0` by decide_tac >>
  `p <> |0|` by metis_tac[poly_deg_zero] >>
  full_simp_tac std_ss[irreducible_def] >-
  metis_tac[ring_nonzero_eq, poly_ring_element] >-
  metis_tac[poly_field_units] >>
  `poly x /\ poly y` by rw[GSYM poly_ring_element] >>
  `x <> |0| /\ y <> |0|` by metis_tac[poly_deg_zero, poly_mult_zero] >>
  `deg x <> 0 /\ deg y <> 0` by metis_tac[poly_field_units] >>
  `deg (x * y) = deg x + deg y` by rw[poly_deg_mult_nonzero] >>
  `deg x < deg x + deg y` by decide_tac >>
  `deg y < deg x + deg y` by decide_tac >>
  `0 < deg x /\ 0 < deg y` by decide_tac >>
  metis_tac[]);

(* Theorem: Field r ==> !p. monic p /\ 0 < deg p /\ ~(ipoly p) ==>
      ?q t. monic q /\ monic t /\ (p = q * t) /\ 0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p *)
(* Proof:
   Note monic p ==> poly p /\ (lead p = #1)   by poly_monic_def
   Then ?q t. poly q /\ poly t /\ (p = q * t) /\
        0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p  by poly_reducible_factors
    Now monic p ==> p <> |0|                  by poly_field_monic_nonzero
     so q <> |0| /\ t <> |0|                  by poly_mult_zero
    Let u, v be the monic parts of q, t, i.e.
    ?h u. h IN R /\ h <> #0 /\ monic u /\
          (deg u = deg q) /\ (q = h * u)      by poly_monic_cmult_factor, q <> |0|
    ?k v. k IN R /\ k <> #0 /\ monic v /\
          (deg v = deg t) /\ (t = k * v)      by poly_monic_cmult_factor, t <> |0|
    Note lead q = h * lead u = h              by poly_lead_cmult, poly_lead_monic
     and lead t = k * lead v = k              by poly_lead_cmult, poly_lead_monic
     But lead p = lead q * lead t             by poly_lead_mult
      or     #1 = h * k                       by above
    Hence p = q * t
            = (h * u) * (k * v)               by q = h * u, t = k * v
            = k * (h * u) * v                 by poly_mult_cmult
            = k * h * u * v                   by poly_cmult_cmult
            = h * k * u * v                   by field_mult_comm
            = #1 * u * v                      by above
            = u * v                           by poly_cmult_lone
    Take q = u, t = v, the result follows.
*)
val poly_monic_reducible_factors = store_thm(
  "poly_monic_reducible_factors",
  ``!r:'a field. Field r ==> !p. monic p /\ 0 < deg p /\ ~(ipoly p) ==>
   ?q t. monic q /\ monic t /\ (p = q * t) /\ 0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p``,
  rpt strip_tac >>
  `poly p /\ (lead p = #1)` by rw[] >>
  `?q t. poly q /\ poly t /\ (p = q * t) /\ 0 < deg q /\ 0 < deg t /\ deg q < deg p /\ deg t < deg p` by rw[poly_reducible_factors] >>
  `p <> |0|` by rw[poly_field_monic_nonzero] >>
  `q <> |0| /\ t <> |0|` by metis_tac[poly_mult_zero] >>
  `?h u. h IN R /\ h <> #0 /\ monic u /\ (deg u = deg q) /\ (q = h * u)` by rw[poly_monic_cmult_factor] >>
  `?k v. k IN R /\ k <> #0 /\ monic v /\ (deg v = deg t) /\ (t = k * v)` by rw[poly_monic_cmult_factor] >>
  `(lead q = h) /\ (lead t = k)` by rw[poly_lead_cmult] >>
  `h * k = #1` by metis_tac[poly_lead_mult] >>
  `Ring r /\ poly u /\ poly v` by rw[] >>
  `p = (h * u) * (k * v)` by metis_tac[] >>
  `_ = k * (h * u) * v` by metis_tac[poly_mult_cmult] >>
  `_ = k * h * u * v` by metis_tac[poly_cmult_cmult] >>
  `_ = #1 * u * v` by metis_tac[field_mult_comm] >>
  `_ = u * v` by metis_tac[poly_cmult_lone] >>
  metis_tac[]);


(* Note:
   This script has only basic properties of irreducible polynomials.
   More advanced properties (e.g. they are primes and they can build finite fields)
   are put into polyFieldModulo script, which establishes the polynomial quotient field.
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
