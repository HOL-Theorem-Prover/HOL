(* ------------------------------------------------------------------------- *)
(* Divisibility of Polynomials                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyDivides";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "ringTheory"; *) *)
(* val _ = load "ringUnitTheory"; (* this overloads |/ as r*.inv *) *)
(* (* val _ = load "integralDomainTheory"; *) *)
(* val _ = load "fieldTheory"; (* see poly_roots_mult, this overload |/ as (r.prod excluding #0).inv *) *)
open monoidTheory groupTheory ringTheory ringUnitTheory fieldTheory;

open subgroupTheory;
open monoidOrderTheory groupOrderTheory;

(* (* val _ = load "polyWeakTheory"; *) *)
(* (* val _ = load "polyRingTheory"; *) *)
(* val _ = load "polyDivisionTheory"; *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;

(* val _ = load "polyRootTheory"; *)
open polyRootTheory;
open polyMonicTheory;

(* val _ = load "polyFieldDivisionTheory"; *)
open polyFieldTheory;
open polyFieldDivisionTheory;

(* val _ = load "ringDividesTheory"; *)
open ringDividesTheory;

(* val _ = load "polyEvalTheory"; *)
open polyEvalTheory;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* val _ = load "helperListTheory"; *)
(* val _ = load "helperFunctionTheory"; *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory;


(* ------------------------------------------------------------------------- *)
(* Divisibility of Polynomials Documentation                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   upoly p      = p IN (Invertibles (PolyRing r).prod).carrier
   pdivides     = poly_divides r
   p ~~ q       = unit_eq (PolyRing r) p q
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Unit Polynomials:
   poly_unit_poly         |- !r. Ring r ==> !p. upoly p ==> poly p
   poly_unit_zero         |- !r. Ring r ==> (upoly |0| <=> ( |1| = |0|))
   poly_unit_property     |- !r. Ring r ==> !p. upoly p <=> poly p /\ ?q. upoly q /\ (p * q = |1|)
   poly_unit_partner      |- !r. Ring r ==> !u. upoly u <=> poly u /\ ?v. poly v /\ (u * v = |1|)
   poly_unit_one          |- !r. Ring r ==> upoly |1|
   poly_unit_monic        |- !r. Ring r ==> !p. upoly p /\ monic p <=> (p = |1|)
   poly_unit_neg          |- !r. Ring r ==> !u. upoly u ==> upoly (-u)
   poly_unit_cmult        |- !r. Ring r ==> !u p. unit u /\ upoly p ==> upoly (u * p)
   poly_unit_mult         |- !r. Ring r ==> !u v. upoly u /\ upoly v ==> upoly (u * v)
   poly_mult_eq_one       |- !r. Ring r ==> !p q. poly p /\ poly q /\ (p * q = |1|) ==> upoly p /\ upoly q
   poly_mult_lunit        |- !r. Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (u * p = q) ==>
                                            ?v. poly v /\ (p = v * q)
   poly_mult_runit        |- !r. Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (p * u = q) ==>
                                            ?v. poly v /\ (p = q * v)

   poly_monic_mult_rcancel |- !r. Ring r ==> !p q t. monic p /\ poly q /\ poly t ==> ((q * p = t * p) <=> (q = t))
   poly_monic_mult_lcancel |- !r. Ring r ==> !p q t. monic p /\ poly q /\ poly t ==> ((p * q = p * t) <=> (q = t))

   Divisibility of Polynomials:
   poly_divides_def          |- !r q p. q pdivides p <=> ?s. poly s /\ (p = s * q)
   poly_divides_zero         |- !r p. p pdivides |0|
   poly_zero_divides         |- !r p. |0| pdivides p <=> (p = |0|)
   poly_one_divides_all      |- !r. Ring r ==> !p. poly p ==> |1| pdivides p
   poly_unit_divides_all     |- !r. Ring r ==> !p. poly p ==> !u. upoly u ==> u pdivides p
   poly_divides_one          |- !r. Ring r ==> !p. poly p /\ p pdivides |1| <=> upoly p
   poly_monic_divides_deg_le |- !r. Ring r /\ #1 <> #0 ==>
                                !p q. monic p /\ monic q /\ p pdivides q ==> deg p <= deg q
   poly_divides_alt          |- !r. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q % p = |0|))
   poly_divides_pmod_eq_zero |- !r. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q == |0|) (pm p))
   poly_divides_eqn          |- !r. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q = q / p * p))
   poly_divides_mod_mod      |- !r. Ring r ==> !x p q. poly x /\ ulead p /\ ulead q /\
                                                       q pdivides p ==> (x % p % q = x % q)

   Polynomial Remainder Equivalence:
   pmod_eq               |- !r z. Ring r /\ ulead z ==>
                            !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> ((p - q) % z = |0|))
   pmod_zero             |- !r z. Ring r /\ ulead z ==> !p. (p == |0|) (pm z) <=> (p % z = |0|)
   pmod_eq_zero          |- !r z. Ring r /\ ulead z ==> !p. poly p ==>
                                  ((p == |0|) (pm z) <=> ?q. poly q /\ (p = q * z))
   poly_pmod_sub_eq_zero |- !r z. Ring r /\ ulead z ==>
                            !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> (p - q == |0|) (pm z))
   poly_divides_sub      |- !r z. Ring r /\ ulead z ==>
                            !p q. poly p /\ poly q ==> (z pdivides p - q <=> (p == q) (pm z))
   pmod_exp              |- !r z. Ring r /\ ulead z ==>
                            !p n. poly p ==> (p ** n == (p % z) ** n) (pm z)
   poly_mod_ring_sum     |- !r z. Ring r /\ pmonic z ==> !c. |c| % z = |c|
   poly_pmod_ring_sum_eq_zero
                         |- !r z. Ring r /\ pmonic z ==> !c. ( |c| == |0|) (pm z) <=> ( |c| = |0|)
   pmod_exp_eq           |- !r z. Ring r /\ ulead z ==> !p q. poly p /\ poly q /\
                                  (p == q) (pm z) ==> !n. (p ** n == q ** n) (pm z)
   poly_pmod_id          |- !r z. Ring r /\ ulead z ==> !p q. poly p /\ poly q /\
                                                   (z = p - q) ==> (p == q) (pm z)
   poly_divides_pmod_eq  |- !r z. Ring r /\ ulead z /\ ulead p /\ z pdivides p ==>
                            !x y. poly x /\ poly y /\ (x == y) (pm p) ==> (x == y) (pm z)

   Properties of Polynomial Divisors:
   poly_divides_is_ring_divides |- !r p q. p pdivides q <=> ring_divides (PolyRing r) p q
   poly_divides_reflexive     |- !r. Ring r ==> !p. poly p ==> p pdivides p
   poly_divides_antisymmetric |- !r. Ring r ==> !p q. monic p /\
                                                 p pdivides q /\ q pdivides p ==> ?u. upoly u /\ (p = u * q)
   poly_divides_transitive    |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\
                                                 p pdivides q /\ q pdivides t ==> p pdivides t
   poly_divides_pair          |- !r. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                                 p pdivides q /\ s pdivides t ==> p * s pdivides q * t
   poly_divides_deg_le        |- !r. Ring r ==> !p q. ulead p /\ poly q /\ q <> |0| /\
                                     p pdivides q ==> deg p <= deg q
   poly_field_divides_deg_le  |- !r. Field r ==> !p q. poly p /\ poly q /\ q <> |0| /\
                                     p pdivides q ==> deg p <= deg q
   poly_divides_share_root    |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !x. x IN R /\ root p x ==> root q x
   poly_divides_share_roots   |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                    roots p SUBSET roots q
   poly_monic_divides_antisymmetric  |- !r. Ring r ==>
                                        !p q. monic p /\ monic q /\ p pdivides q /\ q pdivides p ==> (p = q)
   poly_divides_cmult         |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !c. c IN R ==> p pdivides c * q
   poly_divides_cmult_alt     |- !r. Ring r ==> !c p. c IN R /\ poly p ==> p pdivides c * p
   poly_divides_cmult_iff     |- !r. Ring r ==> !p q. poly p /\ poly q ==>
                                 !c. unit c ==> (p pdivides c * q <=> p pdivides q)
   poly_field_divides_cmult_iff
                              |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                 !c. c IN R /\ c <> #0 ==> (p pdivides c * q <=> p pdivides q)

   poly_divides_exp           |- !r. Ring r ==> !p. poly p ==> !n. 0 < n ==> p pdivides p ** n
   poly_divides_exp_le        |- !r. Ring r ==> !p. poly p ==> !m n. m <= n ==> p ** m pdivides p ** n
   poly_roots_exp_subset      |- !r. Ring r ==> !p n. poly p /\ 0 < n ==> roots p SUBSET roots (p ** n)

   poly_const_divides         |- !r. Ring r ==> !c. unit c ==> !p. poly p ==> [c] pdivides p
   poly_field_const_divides   |- !r. Field r ==> !c. c IN R /\ c <> #0 ==> !p. poly p ==> [c] pdivides p
   poly_cmult_divides         |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !c. unit c ==> c * p pdivides q
   poly_field_cmult_divides         |- !r. Field r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                 !c. c IN R /\ c <> #0 ==> c * p pdivides q
   poly_mult_divides_factor   |- !r. Field r ==> !p q. poly p /\ poly q /\
                                                       p * q pdivides q ==> (q = |0|) \/ upoly p
   poly_field_divides_alt     |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| ==>
                                                       (p pdivides q <=> (q % p = |0|))

   poly_mult_divides          |- !r. Ring r ==> !p q. poly p /\ poly q ==>
                                 !t. poly t /\ p * q pdivides t ==> p pdivides t /\ q pdivides t
   poly_divides_mult          |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !t. poly t ==> p pdivides t * q
   poly_divides_mult_comm     |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !t. poly t ==> p pdivides q * t
   poly_divides_multiple      |- !r. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
                                                !t. poly t ==> p pdivides t * q
   poly_divides_multiple_mod  |- !r. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
                                 !t. poly t ==> ((t * p) % z = |0|) /\ ((p * t) % z = |0|)
   poly_mult_div_alt          |- !r. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
                                 !q. poly q ==> (p * q / z = p / z * q) /\ (p * q / z = q * (p / z))
   poly_divides_eq_deg        |- !r. Field r ==> !p q. poly p /\ poly q /\ q <> |0| /\
                                                 (deg p = deg q) /\ p pdivides q ==> q pdivides p
   poly_monic_divides_eq_deg_eq        |- !r. Field r ==> !p q. monic p /\ monic q /\
                                              (deg p = deg q) /\ p pdivides q ==> (p = q)
   poly_divides_common_multiple        |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t /\
                                              p pdivides q ==> t * p pdivides t * q
   poly_monic_divides_common_multiple  |- !r. Ring r ==> !p q t. poly p /\ poly q /\ monic t /\
                                              p pdivides q ==> t * p pdivides t * q

   poly_divides_linear          |- !r. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
                                       z pdivides p /\ z pdivides q ==>
                                       !s t. poly s /\ poly t ==> z pdivides p * s + q * t
   poly_divides_linear_comm     |- !r. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
                                       z pdivides p /\ z pdivides q ==>
                                       !s t. poly s /\ poly t ==> z pdivides s * p + t * q
   poly_divides_linear_sub      |- !r. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
                                       z pdivides p /\ z pdivides q ==>
                                       !s t. poly s /\ poly t ==> z pdivides p * s - q * t
   poly_divides_linear_sub_comm |- !r. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
                                       z pdivides p /\ z pdivides q ==>
                                       !s t. poly s /\ poly t ==> z pdivides s * p - t * q
   poly_sub_divides_exp_sub     |- !r. Ring r ==> !p q. poly p /\ poly q ==> !n. p - q pdivides p ** n - q ** n

   Polynomial Root Factor Theorem:
   poly_root_factor     |- !r. Ring r ==> !p. poly p ==>
                           !c. c IN roots p <=> c IN R /\ factor c pdivides p
   poly_root_factor_alt |- !r. Ring r ==>
                           !p c. poly p /\ c IN R ==> (root p c <=> factor c pdivides p)
   poly_root_factor_thm |- !r. Ring r ==>
                           !p c. poly p /\ c IN R ==> ((eval p c = #0) <=> factor c pdivides p)
   poly_root_factor_eqn |- !r. Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
                           ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * factor c)
   poly_field_root_factor      |- !r. Field r ==>
                                  !p. poly p ==> !c. c IN roots p <=> c IN R /\ factor c pdivides p
   poly_field_root_factor_alt  |- !r. Field r ==>
                                  !p c. poly p /\ c IN R ==> (root p c <=> factor c pdivides p)
   poly_field_root_factor_thm  |- !r. Field r ==>
                                  !p c. poly p /\ c IN R ==> (eval p c = #0 <=> factor c pdivides p)
   poly_field_root_factor_eqn  |- !r. Field r ==>
                                  !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
                                  ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * factor c)

   Polynomial Ring Unit Equivalence:
   poly_unit_eq_property  |- !r x y. x ~~ y <=> ?u. upoly u /\ (x = u * y)
   poly_unit_eq_one       |- !r. Ring r ==> !u. upoly u <=> u ~~ |1|
   poly_unit_eq_zero      |- !r. Ring r ==> !p. poly p ==> (p ~~ |0| <=> (p = |0|))
   poly_unit_eq_refl      |- !r. Ring r ==> !p. poly p ==> p ~~ p
   poly_unit_eq_sym       |- !r. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> q ~~ p
   poly_unit_eq_trans     |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ p ~~ q /\ q ~~ t ==> p ~~ t
   poly_unit_eq_divides   |- !r. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==>
                             !t. p pdivides t ==> q pdivides t
   poly_unit_eq_cmult     |- !r. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==>
                             !c. c IN R ==> c * p ~~ c * q
   poly_unit_eq_mult      |- !r. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==>
                             !t. poly t ==> p * t ~~ q * t
   poly_unit_eq_mult_comm |- !r. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==>
                             !t. poly t ==> t * p ~~ t * q
   poly_unit_eq_mult_pair |- !r. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                             p ~~ q /\ s ~~ t ==> p * s ~~ q * t
   poly_unit_eq_monic_eq  |- !r. Ring r ==> !p q. monic p /\ monic q ==> (p ~~ q <=> (p = q))
   poly_eq_unit_eq        |- !r. Ring r ==> !p q. poly p /\ poly q /\ (p = q) ==> p ~~ q
   poly_ring_units        |- !r. Ring r ==> !p. poly p ==> (upoly p <=> ?q. poly q /\ (p * q = |1|))
   poly_field_units       |- !r. Field r ==> !p. poly p ==> (upoly p <=> p <> |0| /\ (deg p = 0))
   poly_field_unit_one    |- !r. Field r ==> upoly |1|
   poly_field_const_unit  |- !r. Field r ==> !h. h IN R /\ h <> #0 ==> upoly [h]
   poly_field_unit_alt    |- !r. Field r ==> !p. upoly p <=> ?c. c IN R /\ c <> #0 /\ (p = [c])
   poly_field_unit        |- !r. Field r ==> !p. upoly p <=> poly p /\ p <> |0| /\ (deg p = 0)
   poly_field_unit_deg    |- !r. Field r ==> !p. upoly p ==> (deg p = 0)
   poly_field_unit_eq_alt |- !r. Field r ==> !p q. poly p /\ poly q /\ p ~~ q ==>
                                             ?c. c IN R /\ c <> #0 /\ (p = c * q)
   poly_field_unit_divides  |- !r. Field r ==> !p q. upoly p /\ poly q ==> p pdivides q
   poly_field_divides_unit  |- !r. Field r ==> !p q. poly p /\ upoly q /\ p pdivides q ==> upoly p
   poly_field_divides_antisym  |- !r. Field r ==>
                                  !p q. poly p /\ poly q /\ p pdivides q /\ q pdivides p ==> p ~~ q
   poly_monic_mult_factor    |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (p = u * q)
   poly_monic_mult_by_factor |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (q = u * p)
   poly_unit_eq_divisor      |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\
                                    p pdivides q /\ q ~~ t ==> p pdivides t
   poly_unit_eq_divides_iff  |- !r. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                    p ~~ q /\ s ~~ t ==> (p pdivides s <=> q pdivides t)

   Useful Theorems:
   poly_divides_unit       |- !r. Ring r ==> !p u. poly p /\ upoly u ==> (p pdivides u <=> upoly p)
   poly_roots_field_unit   |- !r. Field r ==> !p. upoly p ==> (roots p = {})
   poly_roots_field_deg1   |- !r. Field r ==> !p. poly p /\ (deg p = 1) ==> ?c. c IN R /\ (roots p = {c})
   poly_unity_1_divides    |- !r. Ring r ==> !n. X - |1| pdivides unity n
   poly_unity_divides      |- !r. Ring r ==> !n m. unity n pdivides unity (n * m)
   poly_X_divides_master   |- !r. Ring r ==> !n. 0 < n ==> X pdivides master n
   poly_monic_divides_one  |- !r. Field r ==> !p. monic p ==> (p pdivides |1| <=> (p = |1|))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Unit Polynomials                                                          *)
(* ------------------------------------------------------------------------- *)

(* define unit polynomial by overloading *)
val _ = overload_on ("upoly", ``\x. x IN (Invertibles (PolyRing r).prod).carrier``);

(* Theorem: Ring r ==> !p. upoly p ==> poly p *)
(* Proof: by poly_ring_ring, ring_unit_element, poly_ring_element *)
val poly_unit_poly = store_thm(
  "poly_unit_poly",
  ``!r:'a ring. Ring r ==> !p. upoly p ==> poly p``,
  metis_tac[poly_ring_ring, ring_unit_element, poly_ring_element]);

(* DO NOT export this, otherwise every poly p will lead to resolving upoly p *)

(* Theorem: Ring r ==> (upoly |0| <=> ( |1| = |0|) *)
(* Proof: by poly_ring_ring, ring_unit_zero *)
val poly_unit_zero = store_thm(
  "poly_unit_zero",
  ``!r:'a ring. Ring r ==> (upoly |0| <=> ( |1| = |0|))``,
  rw[poly_ring_ring, ring_unit_zero]);

(* Theorem: Ring r ==> !p. upoly p <=> poly p /\ ?q. upoly q /\ (p * q = |1|) *)
(* Proof:
   Since Ring (PolyRing r)        by poly_ring_ring
   Apply: ring_unit_property |> ISPEC ``PolyRing r`` |> REWRITE_RULE[poly_ring_element];
   val it = |- Ring (PolyRing r) ==> !u. upoly u <=> poly u /\ ?v. poly v /\ (u * v = |1|): thm

   If part: upoly p ==> poly p /\ ?q. upoly q /\ (p * q = |1|)
      Since upoly p ==> poly p              by poly_unit_poly
            ?q. poly q /\ (p * q = |1|)     by ring_unit_property
         or poly q /\ (q * p = |1|)         by poly_mult_comm
      Hence upoly q                         by ring_unit_property
   Only-if part: poly p /\ upoly q /\ (p * q = |1|) ==> upoly p
      Since upoly q ==> poly q              by poly_unit_poly
        and |1| = p * q = q * p             by poly_mult_comm
      Hence upoly p                         by ring_unit_property
*)
val poly_unit_property = store_thm(
  "poly_unit_property",
  ``!r:'a ring. Ring r ==> !p. upoly p <=> poly p /\ ?q. upoly q /\ (p * q = |1|)``,
  metis_tac[poly_ring_ring, ring_unit_property, poly_ring_element, poly_unit_poly, poly_mult_comm]);

(* Theorem: Ring r ==> !u. upoly u <=> poly u /\ ?v. poly v /\ (u * v = |1|) *)
(* Proof:
   Note Ring (PolyRing r)      by poly_ring_ring
   > ring_unit_property |> ISPEC ``PolyRing r``;
   val it = |- Ring (PolyRing r) ==> !u. upoly u <=>
     u IN (PolyRing r).carrier /\ ?v. v IN (PolyRing r).carrier /\ (u * v = |1|): thm
   Apply poly_ring_element.
*)
val poly_unit_partner = store_thm(
  "poly_unit_partner",
  ``!r:'a ring. Ring r ==> !u. upoly u <=> poly u /\ ?v. poly v /\ (u * v = |1|)``,
  rw[poly_ring_ring, ring_unit_property, poly_ring_element]);
(* not same as polyDivideTheory.poly_unit_property (which specifies upoly u instead of just poly u):
|- !r. Ring r ==> !p. upoly p <=> poly p /\ ?q. upoly q /\ (p * q = |1|)
*)

(* Theorem: Ring r ==> upoly |1| *)
(* Proof:
   Since poly |1|            by poly_one_poly
     and |1| * |1| = |1|     by poly_mult_one_one
    Take p = |1|
    then ?q. poly q /\ (p * q = |1|)   by above
   Hence upoly p             by poly_ring_ring, ring_unit_property, poly_ring_element
*)
val poly_unit_one = store_thm(
  "poly_unit_one",
  ``!r:'a ring. Ring r ==> upoly |1|``,
  metis_tac[poly_ring_ring, ring_unit_property, poly_ring_element, poly_mult_one_one, poly_one_poly]);

(* Theorem: Ring r ==> !p. upoly p /\ monic p <=> (p = |1|) *)
(* Proof:
   If part: upoly p /\ monic p ==> (p = |1|)
      Since upoly p
        ==> ?q. upoly q /\ (p * q = |1|)  by poly_unit_property
        Now monic |1|                     by poly_monic_one
         so monic q                       by poly_monic_monic_mult, poly_unit_poly
       Thus deg p + deg q = deg |1| = 0   by poly_monic_deg_mult, poly_deg_one
     Giving deg p = 0, hence p = |1|      by poly_monic_deg_0
   Only-if part: (p = |1|) ==> upoly p /\ monic p
      True by poly_unit_one.
*)
val poly_unit_monic = store_thm(
  "poly_unit_monic",
  ``!r:'a ring. Ring r ==> !p. upoly p /\ monic p <=> (p = |1|)``,
  rw[EQ_IMP_THM] >| [
    `?q. upoly q /\ (p * q = |1|)` by metis_tac[poly_unit_property] >>
    `monic |1|` by rw[] >>
    `monic q` by metis_tac[poly_monic_monic_mult, poly_unit_poly] >>
    `deg p + deg q = 0` by metis_tac[poly_monic_deg_mult, poly_deg_one] >>
    `deg p = 0` by decide_tac >>
    rw[GSYM poly_monic_deg_0],
    rw[poly_unit_one]
  ]);

(* Theorem: Ring r ==> !u. upoly u ==> upoly (-u) *)
(* Proof: by poly_unit_partner, poly_mult_neg_neg, poly_neg_poly *)
val poly_unit_neg = store_thm(
  "poly_unit_neg",
  ``!r:'a ring. Ring r ==> !u. upoly u ==> upoly (-u)``,
  metis_tac[poly_unit_partner, poly_mult_neg_neg, poly_neg_poly]);

(* Theorem: Ring r ==> !u p. unit u /\ upoly p ==> upoly (u * p) *)
(* Proof:
   Note unit u ==> u IN R /\ ?v. v IN R /\ (u * v = #1)     by ring_unit_property
    and upoly p ==> poly p /\ ?s. poly s /\ (p * s = |1|)   by poly_unit_partner
        (u * p) * (v * s)
      = v * (u * p) * s        by poly_mult_cmult
      = (v * u) * p * s        by poly_cmult_cmult
      = #1 * |1|               by ring_mult_comm
      = |1|                    by poly_cmult_lone
   Since poly (v * s)          by poly_cmult_poly
   Hence upoly (u * p)         by poly_unit_partner
*)
val poly_unit_cmult = store_thm(
  "poly_unit_cmult",
  ``!r:'a ring. Ring r ==> !u p. unit u /\ upoly p ==> upoly (u * p)``,
  rpt strip_tac >>
  `u IN R /\ ?v. v IN R /\ (u * v = #1)` by metis_tac[ring_unit_property] >>
  `poly p /\ ?s. poly s /\ (p * s = |1|)` by metis_tac[poly_unit_partner] >>
  `(u * p) * (v * s) = v * (u * p) * s` by rw[GSYM poly_mult_cmult] >>
  `_ = (v * u) * p * s` by rw[GSYM poly_cmult_cmult] >>
  `_ = |1|` by rw[poly_cmult_lone, ring_mult_comm] >>
  metis_tac[poly_unit_partner, poly_cmult_poly]);

(* Theorem: Ring r ==> !u v. upoly u /\ upoly v ==> upoly (u * v) *)
(* Proof:
   Note upoly u ==> poly u /\ ?s. poly s /\ (u * s = |1|)    by poly_unit_partner
    and upoly v ==> poly v /\ ?t. poly t /\ (v * t = |1|)    by poly_unit_partner
   Thus poly (u * v) /\ poly (s * t)   by poly_mult_poly
        |1| = (u * s) * (v * t)        by poly_mult_one_one
            = (u * s * v) * t          by poly_mult_assoc
            = (u * (s * v)) * t        by poly_mult_assoc
            = (u * (v * s)) * t        by poly_mult_comm
            = (u * v * s) * t          by poly_mult_assoc
            = (u * v) * (s * t)        by poly_mult_assoc
   Thus upoly (u * v)                  by poly_unit_partner
*)
val poly_unit_mult = store_thm(
  "poly_unit_mult",
  ``!r:'a ring. Ring r ==> !u v. upoly u /\ upoly v ==> upoly (u * v)``,
  rpt strip_tac >>
  `poly u /\ ?s. poly s /\ (u * s = |1|)` by metis_tac[poly_unit_partner] >>
  `poly v /\ ?t. poly t /\ (v * t = |1|)` by metis_tac[poly_unit_partner] >>
  `poly (u * v) /\ poly (s * t)` by rw[] >>
  `(u * v) * (s * t) = (u * (v * s)) * t` by rw[poly_mult_assoc] >>
  `_ = (u * (s * v)) * t` by rw[poly_mult_comm] >>
  `_ = (u * s) * (v * t)` by rw[poly_mult_assoc] >>
  `_ = |1|` by rw[] >>
  metis_tac[poly_unit_partner]);

(* Theorem: poly p /\ poly q /\ (p * q = |1|) ==> upoly p /\ upoly q *)
(* Proof:
   Since upoly x <=> x IN (Invertibles (PolyRing r).prod).carrier
   Expanding definitions, the goal is:
   (p * q = |1|) ==> (?y. poly y /\ (p * y = |1|) /\ (y * p = |1|)) /\
                      ?y. poly y /\ (q * y = |1|) /\ (y * q = |1|)
   This is true by poly_mult_comm.
*)
val poly_mult_eq_one = store_thm(
  "poly_mult_eq_one",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (p * q = |1|) ==> upoly p /\ upoly q``,
  ntac 5 strip_tac >>
  rw[Invertibles_def, monoid_invertibles_def, poly_ring_element] >>
  metis_tac[poly_mult_comm]);

(* Theorem: Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (u * p = q) ==> ?v. poly v /\ (p = v * q) *)
(* Proof:
   Since upoly u ==> ?v. poly v /\ (u * v = |1|)   by poly_unit_partner
    thus v * q = v * (u * p)                       by given
               = (v * u) * p                       by poly_mult_assoc
               = (u * v) * p                       by poly_mult_comm
               = |1| * p                           by above
               = p                                 by poly_mult_lone
*)
val poly_mult_lunit = store_thm(
  "poly_mult_lunit",
  ``!r:'a ring. Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (u * p = q) ==> ?v. poly v /\ (p = v * q)``,
  rw[poly_unit_partner] >>
  metis_tac[poly_mult_assoc, poly_mult_comm, poly_mult_lone]);

(* Theorem: Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (p * u = q) ==> ?v. poly v /\ (p = q * v) *)
(* Proof:
   Since upoly u ==> poly u          by poly_unit_poly
      so p * u = q = u * p           by poly_mult_comm
    thus ?v. poly v /\ (p = v * q)   by poly_mult_lunit
      or p = q * v                   by poly_mult_comm
*)
val poly_mult_runit = store_thm(
  "poly_mult_runit",
  ``!r:'a ring. Ring r ==> !u p q. upoly u /\ poly p /\ poly q /\ (p * u = q) ==> ?v. poly v /\ (p = q * v)``,
  metis_tac[poly_mult_lunit, poly_mult_comm, poly_unit_poly]);

(* Theorem: monic p /\ poly q /\ poly t ==> ((q * p = t * p) <=> (q = t)) *)
(* Proof:
   If part: q * p = t * p ==> q = t
     If deg p = 0,
        Then p = |1|            by poly_monic_deg_0
          so q * |1| = t * |1|
         ==>       q = t        by poly_mult_rone
     If deg p <> 0,
        Then 0 < deg p          by NOT_ZERO_LT_ZERO
        Let z = q * p,
       Then z = q * p + |0|
        and z = t * p + |0|
      Hence q = t               by poly_div_mod_unique, deg |0| < deg p
   Only-if part: q = t ==> q * p = t * p
     This is trivial.
*)
val poly_monic_mult_rcancel = store_thm(
  "poly_monic_mult_rcancel",
  ``!r:'a ring. Ring r ==> !p q t. monic p /\ poly q /\ poly t ==> ((q * p = t * p) <=> (q = t))``,
  rw[EQ_IMP_THM] >>
  Cases_on `deg p = 0` >-
  metis_tac[poly_monic_deg_0, poly_mult_rone] >>
  `0 < deg p` by decide_tac >>
  `?z. z = q * p` by rw[] >>
  `poly z /\ (z = q * p + |0|) /\ (z = t * p + |0|)` by rw[] >>
  `poly p /\ unit (lead p)` by rw[] >>
  `poly |0| /\ (deg |0| = 0)` by rw[] >>
  metis_tac[poly_div_mod_unique]);
(* cannot move to polyMonic, since this requires polyDivision.poly_div_mod_unique. *)

(*
In Z_6, 2 has no inverse, thus (2x + 3) cannot be made into 2 * (monic p).
But suppose q * (2x + 3) = X * (2x + 3), is there an example that q <> X ?
If there is such a case, that means the product has two factorizations.
We know that the (PolyRing r) is a Euclidean ring.
Maybe that is enough to give a Unique Factorization Ring.
However, even when a product has two factorizations, it is rare that one part equal, another part differs!

On the other hand, in Z_6, 1 * 2 = 4 * 2, and 1 * 4 = 4 * 4
Therefore |1| * (2 x + 4) = [4] * (2 x + 4), so such an example can be found.
Even though  2x + 4 = [2] * (x + 2), with a monic p, the [2] cannot be cancelled as it is not a unit in Z_6.

Hence this is not true:
!r:'a ring. Ring r ==> !p q. poly q /\ poly t ==> ((q * p = t * p) <=> (q = t))
*)

(* Theorem: monic p /\ poly q /\ poly t ==> ((p * q = p * t) <=> (q = t)) *)
(* Proof: by poly_monic_mult_rcancel and poly_mult_comm *)
val poly_monic_mult_lcancel = store_thm(
  "poly_monic_mult_lcancel",
  ``!r:'a ring. Ring r ==> !p q t. monic p /\ poly q /\ poly t ==> ((p * q = p * t) <=> (q = t))``,
  metis_tac[poly_monic_mult_rcancel, poly_mult_comm, poly_monic_poly]);
(* cannot move to polyMonic, since this requires polyDivides.poly_monic_mult_rcancel. *)

(* ------------------------------------------------------------------------- *)
(* Divisibility of Polynomials                                               *)
(* ------------------------------------------------------------------------- *)

(* Divides relation between polynomials *)
val poly_divides_def = Define `
  poly_divides (r:'a field) (q:'a poly) (p:'a poly) =
    ?s:'a poly. poly s /\ (p = s * q)
`;

(* Overload polynomial divides *)
val _ = overload_on ("pdivides", ``poly_divides r``);
val _ = set_fixity "pdivides" (Infix(NONASSOC, 450)); (* same as relation *)
(*
poly_divides_def;
> val it = |- !r q p. q pdivides p <=> ?s. poly s /\ (p = s * q) : thm
*)

(* Theorem: p pdivides |0| *)
(* Proof:
   By poly_divides_def, this is to show: ?s. poly s /\ ( |0| = s * p)
   Take s = |0|,
   then poly |0|         by poly_zero_poly
    and |0| = |0| * p    by poly_mult_lzero
*)
val poly_divides_zero = store_thm(
  "poly_divides_zero",
  ``!r:'a ring. !p. p pdivides |0|``,
  metis_tac[poly_divides_def, poly_zero_poly, poly_mult_lzero]);

(* Theorem: |0| pdivides p <=> p = |0| *)
(* Proof:
   If part: |0| pdivides p ==> p = |0|
      ?s. poly s /\ p = s * |0|      by poly_divides_def
                      = |0|          by poly_mult_rzero
   Only-if part: p = |0| ==> |0| pdivides p
      i.e. show: |0| pdivides |0|
      True by poly_divides_zero      by poly_zero_poly
*)
val poly_zero_divides = store_thm(
  "poly_zero_divides",
  ``!r:'a ring. !p. |0| pdivides p <=> (p = |0|)``,
  metis_tac[poly_divides_def, poly_zero_poly, poly_mult_zero]);

(* Theorem: poly p ==> |1| pdivides p *)
(* Proof:
   Since p = p * |1|       by poly_mult_rone
    Thus |1| pdivides p    by poly_divides_def
*)
val poly_one_divides_all = store_thm(
  "poly_one_divides_all",
  ``!r:'a ring. Ring r ==> !p. poly p ==> |1| pdivides p``,
  metis_tac[poly_divides_def, poly_mult_rone, poly_one_poly]);

(* Theorem: Ring r ==> !p. poly p ==> !u. upoly u ==> u pdivides p *)
(* Proof:
   Since upoly u
     ==> poly u /\ ?v. poly v /\ (u * v = |1|)   by poly_unit_partner
      so p = p * |1|                             by poly_mult_rone
           = p * (u * v)                         by above
           = p * (v * u)                         by poly_mult_comm
           = (p * v) * u                         by poly_mult_assoc
   Hence u pdivides p                            by poly_divides_def
*)
val poly_unit_divides_all = store_thm(
  "poly_unit_divides_all",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !u. upoly u ==> u pdivides p``,
  rpt strip_tac >>
  `poly u /\ ?v. poly v /\ (u * v = |1|)` by metis_tac[poly_unit_partner] >>
  `p = p * v * u` by rw[poly_mult_assoc, poly_mult_comm] >>
  metis_tac[poly_divides_def, poly_mult_poly]);

(* Theorem: Ring r ==> !p. poly p /\ p pdivides |1| <=> upoly p *)
(* Proof:
       poly u /\ p pdivides |1|
   <=> poly u /\ ?v. poly v /\ ( |1| = v * u)  by poly_divides_def
   <=> poly u /\ ?v. poly v /\ (u * v = |1|)  by poly_mult_comm
   <=> upoly p                                by poly_unit_partner
*)
val poly_divides_one = store_thm(
  "poly_divides_one",
  ``!r:'a ring. Ring r ==> !p. poly p /\ p pdivides |1| <=> upoly p``,
  metis_tac[poly_divides_def, poly_unit_partner, poly_mult_comm]);

(* Theorem: !p q. monic p /\ monic q /\ p pdivides q ==> deg p <= deg q *)
(* Proof:
   Since p pdivides q,
         ?s. poly s /\ q = s * p     by poly_divides_def
     and monic s                     by poly_monic_monic_mult_comm
      so deg q = deg s + deg p       by poly_monic_deg_mult
      or deg p <= deg q
*)
val poly_monic_divides_deg_le = store_thm(
  "poly_monic_divides_deg_le",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. monic p /\ monic q /\ p pdivides q ==> deg p <= deg q``,
  rw[poly_divides_def] >>
  `poly p /\ poly (s * p)` by rw[] >>
  `monic s` by metis_tac[poly_monic_monic_mult_comm] >>
  `deg (s * p) = deg s + deg p` by rw[poly_monic_deg_mult] >>
  decide_tac);

(* Theorem: ulead p /\ poly q ==> (p pdivides q <=> q % p = |0|) *)
(* Proof:
       p pdivides q
   <=> ?s. poly s /\ (q = s * p)   by poly_divides_def
   <=> q % p = |0|                 by poly_mod_eq_zero
*)
val poly_divides_alt = store_thm(
  "poly_divides_alt",
  ``!r:'a ring. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q % p = |0|))``,
  rw[poly_divides_def, poly_mod_eq_zero]);

(* Theorem: Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q == |0|) (pm p)) *)
(* Proof:
       p pdivides q
   <=> q % p = |0|         by poly_divides_alt
   <=> (q == |0|) (pm p)   by pmod_def_alt, poly_zero_mod
*)
val poly_divides_pmod_eq_zero = store_thm(
  "poly_divides_pmod_eq_zero",
  ``!r:'a ring. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q == |0|) (pm p))``,
  rw[poly_divides_alt, pmod_def_alt]);

(* Theorem: Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q = (q / p) * p)) *)
(* Proof:
       p pdivides q
   <=> (q % p = |0|)                             by poly_divides_alt
   <=> (q / p * p + (q % p) = q / p * p + |0|)   by poly_add_lcancel
   <=> (q = q / p * p + |0|)                     by poly_div_mod_all_def
   <=> (q = q / p * p)                           by poly_add_rzero
*)
val poly_divides_eqn = store_thm(
  "poly_divides_eqn",
  ``!r:'a ring. Ring r ==> !p q. ulead p /\ poly q ==> (p pdivides q <=> (q = (q / p) * p))``,
  rpt strip_tac >>
  `poly (q / p) /\ (q = q / p * p + (q % p))` by rw[poly_div_mod_all_def] >>
  `p pdivides q <=> (q % p = |0|)` by rw[poly_divides_alt] >>
  `_ = (q / p * p + (q % p) = q / p * p + |0|)` by rw[poly_add_lcancel] >>
  `_ = (q = q / p * p)` by metis_tac[poly_mult_poly, poly_add_rzero] >>
  rw[]);

(* Theorem: poly x /\ ulead p /\ ulead q /\ q pdivides p ==> ((x % p) % q = x % q) *)
(* Proof:
   Note x = x / p * p + x % p                              by poly_division_all
   Thus x % q
      = ((x / p * p) % q + (x % p) % q) % q                by poly_mod_add
      = (((x / p) % q) * (p % q)) % q + (x % p) % q) % q   by poly_mod_mult
      = (((x / p) % q) * |0|) % q + (x % p) % q) % q       by poly_divides_alt
      = ( |0| % q + (x % p) % q) % q                       by poly_mult_zero
      = |0| + ((x % p) % q) % q                            by poly_zero_mod
      = x % p % q                                          by poly_mod_mod
*)
val poly_divides_mod_mod = store_thm(
  "poly_divides_mod_mod",
  ``!r:'a ring. Ring r ==> !x p q. poly x /\
         ulead p /\ ulead q /\ q pdivides p ==> ((x % p) % q = x % q)``,
  rpt strip_tac >>
  `x = x / p * p + x % p` by rw[poly_division_all] >>
  `((x / p) * p) % q = (((x / p) % q) * (p % q)) % q` by rw[Once poly_mod_mult] >>
  `_ = |0|` by metis_tac[poly_divides_alt, poly_mult_zero, poly_zero_mod] >>
  qabbrev_tac `m = x / p * p` >>
  qabbrev_tac `y = x % p` >>
  `poly m /\ poly y` by rw[Abbr`m`, Abbr`y`] >>
  `x % q = (m % q + y % q) % q` by metis_tac[poly_mod_add] >>
  `_ = (y % q) % q` by fs[] >>
  `_ = y % q` by rw[poly_mod_mod] >>
  simp[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Remainder Equivalence                                          *)
(* ------------------------------------------------------------------------- *)

(*
- poly_eval_sub;
> val it = |- !r. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p - q) x = eval p x - eval q x) : thm
- poly_eval_sub |> ISPEC ``PolyModRing r z``;
<<HOL message: inventing new type variable names: 'a>>
> val it = |- Ring (PolyModRing r z) ==>
       !p q x. Poly (PolyModRing r z) p /\ Poly (PolyModRing r z) q /\ x IN (PolyModRing r z).carrier ==>
         (poly_eval (PolyModRing r z) (poly_sub (PolyModRing r z) p q) x =
          ring_sub (PolyModRing r z) (poly_eval (PolyModRing r z) p x) (poly_eval (PolyModRing r z) q x)) : thm
- poly_peval_sub;
> val it = |- !r. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p - q) x = peval p x - peval q x) : thm
*)

(*
- poly_peval_sub;
> val it = |- !r. Ring r ==> !p q x. poly p /\ poly q /\ poly x ==> (peval (p - q) x = peval p x - peval q x) : thm
*)

(* Theorem: ulead z ==> !p q. (p == q) (pm z) <=> (p - q) % z = |0| *)
(* Proof:
       (p == q) (pm z)
   <=> p % z = q % z      by pmod_def_alt
   <=> (p - q) % z = |0|  by poly_mod_eq
*)
val pmod_eq = store_thm(
  "pmod_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
     !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> ((p - q) % z = |0|))``,
  rw[pmod_def_alt, poly_mod_eq]);

(* Theorem: ulead z ==> !p. (p == |0|) (pm z) <=> p % z == |0| *)
(* Proof:
     (p == |0|) (pm z)
   <=> p % z = |0| % z      by pmod_def_alt
   <=> p % z = |0|          by poly_zero_mod
*)
val pmod_zero = store_thm(
  "pmod_zero",
  ``!(r:'a ring) z. Ring r /\ ulead z ==> !p. (p == |0|) (pm z) <=> (p % z = |0|)``,
  rw[pmod_def_alt, poly_zero_mod]);

(* Theorem: ulead z ==> !p. (p == |0|) (pm z) <=> ?q. poly q /\ (p = q * z) *)
(* Proof:
        (p == |0|) (pm z)
   <=>  p % z = |0| % z              by pmod_def_alt
   <=>  p % z = |0|                  by poly_zero_mod
   <=>  ?q. poly q /\ (p = q * z)    by poly_mod_eq_zero
*)
val pmod_eq_zero = store_thm(
  "pmod_eq_zero",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !p. poly p ==> ((p == |0|) (pm z) <=> ?q. poly q /\ (p = q * z))``,
  metis_tac[pmod_def_alt, poly_zero_mod, poly_mod_eq_zero]);

(* Theorem: ulead z ==> !p q. (p == q) (pm z) <=> (p - q == |0|) (pm z) *)
(* Proof:
       (p == q) (pm z)
   <=> (p - q) % z = |0|      by pmod_eq
   <=> (p - q == |0|) (pm z)  by pmod_zero, poly_sub_poly
*)
val poly_pmod_sub_eq_zero = store_thm(
  "poly_pmod_sub_eq_zero",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
     !p q. poly p /\ poly q ==> ((p == q) (pm z) <=> (p - q == |0|) (pm z))``,
  rw[pmod_eq]);

(* Theorem: ulead z ==> !p q. poly p /\ poly q ==> (z pdivides (p - q) <=> (p == q) (pm z)) *)
(* Proof:
       z pdivides (p - q)
   <=> (p - q == |0|) (pm z)   by poly_divides_pmod_eq_zero, poly_sub_poly
   <=> (p == q) (pm z)         by poly_pmod_sub_eq_zero
*)
val poly_divides_sub = store_thm(
  "poly_divides_sub",
  ``!(r:'a ring) z. Ring r /\ ulead z ==> !p q. poly p /\ poly q ==>
    (z pdivides (p - q) <=> (p == q) (pm z))``,
  rw[poly_divides_pmod_eq_zero, GSYM poly_pmod_sub_eq_zero]);

(* Theorem: ulead z ==> !p n. poly p ==> (p ** n == (p % z) ** n) (pm z) *)
(* Proof: by pmod_def_alt and poly_mod_exp. *)
val pmod_exp = store_thm(
  "pmod_exp",
  ``!(r:'a ring) z. Ring r /\ ulead z ==> !p n. poly p ==> (p ** n == (p % z) ** n) (pm z)``,
  metis_tac[pmod_def_alt, poly_mod_exp]);

(* Theorem: pmonic z ==> !c. |c| % z = |c| *)
(* Proof:
   Since deg |c| = 0     by poly_deg_sum_num
   Hence |c| % z = |c|   by poly_mod_less, pmonic z
*)
val poly_mod_ring_sum = store_thm(
  "poly_mod_ring_sum",
  ``!(r:'a ring) z. Ring r /\ pmonic z ==> !c:num. |c| % z = |c|``,
  rw_tac std_ss[poly_mod_less, poly_deg_sum_num, poly_sum_num_poly]);

(* Theorem: pmonic z ==> !c. ( |c| == |0|) (pm z) <=> ( |c| = |0|) *)
(* Proof:
       ( |c| == |0|) (pm z)
   <=> |c| % z = |0| % z    by pmod_def_alt
   <=>     |c| = |0|        by poly_mod_ring_sum, poly_zero_mod
*)
val poly_pmod_ring_sum_eq_zero = store_thm(
  "poly_pmod_ring_sum_eq_zero",
  ``!(r:'a ring) z. Ring r /\ pmonic z ==> !c:num. ( |c| == |0|) (pm z) <=> ( |c| = |0|)``,
  rw[pmod_def_alt, poly_mod_ring_sum]);

(* Theorem: ulead z ==> !p q. (p == q) (pm z) ==> !n. (p ** n == q ** n) (pm z) *)
(* Proof:
        (p == q) (pm z)
   <=>  p % z = q % z                  by pmod_def_alt
   <=>  (p % z) ** n = (q % z) ** n    by above
   ==>  (p % z) ** n % z = (q % z) ** n % z
   <=>  (p ** n) % z = (q ** n) % z    by poly_mod_exp
   <=>  (p ** n == q ** n) (pm z)      by pmod_def_alt
*)
val pmod_exp_eq = store_thm(
  "pmod_exp_eq",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !p q. poly p /\ poly q /\ (p == q) (pm z) ==> !n. (p ** n == q ** n) (pm z)``,
  rw_tac std_ss[pmod_def_alt, poly_mod_exp]);

(* Theorem: ulead z ==> !p q. (z = p - q) ==> (p == q) (pm z) *)
(* Proof:
   Since z = p - q
      so (p - q) % z = z % z = |0|  by poly_div_mod_id
   Hence (p == q) (pm z)            by pmod_eq
*)
val poly_pmod_id = store_thm(
  "poly_pmod_id",
  ``!(r:'a ring) z. Ring r /\ ulead z ==>
   !p q. poly p /\ poly q /\ (z = p - q) ==> (p == q) (pm z)``,
  metis_tac[poly_div_mod_id, pmod_eq]);

(* Theorem: ulead z /\ ulead p /\ z pdivides p ==>
      !x y. poly x /\ poly y /\ (x == y) (pm p) ==> (x == y) (pm z) *)
(* Proof:
       (x == y) (pm p)
   <=> (x - y) % p = |0|           by pmod_eq
   ==> (x - y) % p % z = |0| % z
                       = |0|       by poly_zero_mod
   <=> (x - y) % z = |0|           by poly_divides_mod_mod, z pdivides p
   <=> (x == y) (pm z)             by pmod_eq
*)
val poly_divides_pmod_eq = store_thm(
  "poly_divides_pmod_eq",
  ``!(r:'a ring) z p. Ring r /\ ulead z /\ ulead p /\ z pdivides p ==>
   !x y. poly x /\ poly y /\ (x == y) (pm p) ==> (x == y) (pm z)``,
  metis_tac[pmod_eq, poly_divides_mod_mod, poly_zero_mod, poly_sub_poly]);

(* ------------------------------------------------------------------------- *)
(* Properties of Polynomial Divisors.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !p q. p pdivides q <=> ring_divides (PolyRing r) p q *)
(* Proof: by poly_divides_def, ring_divides_def *)
val poly_divides_is_ring_divides = store_thm(
  "poly_divides_is_ring_divides",
  ``!r:'a ring. !p q. p pdivides q <=> ring_divides (PolyRing r) p q``,
  metis_tac[poly_divides_def, ring_divides_def, poly_ring_element]);

(* Note:
Ring does not have mult_rcancel:   x * z = y * z  cannot give x = y, only field does.
EuclideanRing still has no mult_rcancel:  it is still a ring.
PolyRing does have mult_rcancel, due to poly_div_mod_unique.

Hence there is no ring_divides_antisymmetric:
??  Ring r ==> !p q. p IN R /\ q IN R /\ p rdivides q /\ q rdivides p ==> ?u. p = u * q
But only poly_divides_antisymmetric:
|- !r. Ring r ==> !p q. monic p /\ p pdivides q /\ q pdivides p ==> ?u. upoly u /\ (p = u * q)
and poly_monic_divides_antisymmetric:
|- !r. Ring r ==> !p q. monic p /\ monic q /\ p pdivides q /\ q pdivides p ==> (p = q)
*)

(* Theorem: p pdivides p *)
(* Proof:
     p pdivides p <=> ?s. poly s /\ (p = s * p)    by poly_divides_def
     So take s = |1|, and poly |1| /\ p = |1| * p  by poly_one_poly, poly_mult_lone
*)
val poly_divides_reflexive = store_thm(
  "poly_divides_reflexive",
  ``!r:'a ring. Ring r ==> !p. poly p ==> p pdivides p``,
  metis_tac[poly_divides_def, poly_one_poly, poly_mult_lone]);

(* Theorem: monic p /\ p pdivides q /\ q pdivides p ==> ?u. upoly u /\ p = u * q *)
(* Proof:
     p pdivides q <=> ?s. poly s /\ (q = s * p)    by poly_divides_def
     q pdivides p <=> ?t. poly t /\ (p = t * q)    by poly_divides_def
     Hence  p = t * q
              = t * (s * p)
              = (t * s) * p                        by poly_mult_assoc
     or |1| * p = (t * s) * p  with monic p        by poly_mult_lone
     Hence t * s = |1|                             by poly_monic_mult_rcancel
     or s and t are units                          by poly_mult_eq_one
     Therefore take u = t.
*)
val poly_divides_antisymmetric = store_thm(
  "poly_divides_antisymmetric",
  ``!r:'a ring. Ring r ==>
    !p q. monic p /\ p pdivides q /\ q pdivides p ==> ?u. upoly u /\ (p = u * q)``,
  rpt strip_tac >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `?t. poly t /\ (p = t * q)` by rw[GSYM poly_divides_def] >>
  `p = t * (s * p)` by metis_tac[] >>
  `t * s * p = |1| * p` by rw[poly_mult_assoc] >>
  `poly (t * s) /\ poly |1|` by rw[] >>
  metis_tac[poly_monic_mult_rcancel, poly_mult_eq_one]);

(* Theorem: p pdivides q /\ q pdivides t ==> p pdivides t *)
(* Proof:
     p pdivides q <=> ?u. poly u /\ (q = u * p)    by poly_divides_def
     q pdivides t <=> ?v. poly v /\ (t = v * q)    by poly_divides_def
     Hence t = v * q
             = v * (u * p)
             = (v * u) * p                         by poly_mult_assoc
     Since poly (v * u)                            by poly_mult_poly
     Hence p pdivides t                            by poly_divides_def
*)
val poly_divides_transitive = store_thm(
  "poly_divides_transitive",
  ``!r:'a ring. Ring r ==>
    !p q t. poly p /\ poly q /\ poly t /\ p pdivides q /\ q pdivides t ==> p pdivides t``,
  rw[poly_divides_def] >>
  `s' * (s * p) = s' * s * p` by rw[poly_mult_assoc] >>
  metis_tac[poly_mult_poly]);

(* Theorem: Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
            p pdivides q /\ s pdivides t ==> (p * s) pdivides (q * t) *)
(* Proof:
   Note ?u. poly u /\ (q = u * p)   by poly_divides_def
    and ?v. poly v /\ (t = v * s)   by poly_divides_def
        q * t
      = (u * p) * (v * s)           by above
      = (u * p * v) * s             by poly_mult_assoc
      = (u * (p * v)) * s           by poly_mult_assoc
      = (u * (v * p)) * s           by poly_mult_comm
      = (u * v * p) * s             by poly_mult_assoc
      = (u * v) * (p * s)           by poly_mult_assoc
   Note poly (u * v)                by poly_mult_poly
   Thus (p * s) pdivides (q * t)    by poly_divides_def
*)
val poly_divides_pair = store_thm(
  "poly_divides_pair",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
      p pdivides q /\ s pdivides t ==> (p * s) pdivides (q * t)``,
  rpt strip_tac >>
  `?u. poly u /\ (q = u * p)` by rw[GSYM poly_divides_def] >>
  `?v. poly v /\ (t = v * s)` by rw[GSYM poly_divides_def] >>
  `q * t = (u * p * v) * s` by rw[poly_mult_assoc] >>
  `_ = (u * (p * v)) * s` by rw[GSYM poly_mult_assoc] >>
  `_ = (u * (v * p)) * s` by rw[poly_mult_comm] >>
  `_ = (u * v) * (p * s)` by rw[poly_mult_assoc] >>
  metis_tac[poly_divides_def, poly_mult_poly]);

(* Theorem: Ring r ==> !p q. ulead p /\ poly q /\ q <> |0| /\ p pdivides q ==> deg p <= deg q *)
(* Proof:
   Note p pdivides q
    ==> ?t. poly t /\ (q = t * p)       by poly_divides_def
   Note unit (lead p)                   by ulead p
    and t <> |0|                        by poly_mult_lzero
     so lead t <> #0                    by poly_nonzero_lead_nonzero
    ==> deg q = deg t + deg p           by poly_deg_mult_unit_comm
   Hence deg p <= deg q                 by deg p is bounded by deg q
*)
val poly_divides_deg_le = store_thm(
  "poly_divides_deg_le",
  ``!r:'a ring. Ring r ==>
   !p q. ulead p /\ poly q /\ q <> |0| /\ p pdivides q ==> deg p <= deg q``,
  rpt strip_tac >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `t <> |0|` by metis_tac[poly_mult_lzero] >>
  `lead t <> #0` by metis_tac[poly_nonzero_lead_nonzero] >>
  `deg q = deg t + deg p` by rw[poly_deg_mult_unit_comm] >>
  decide_tac);

(* Theorem: Field r ==> poly p /\ poly q /\ q <> |0| /\ p pdivides q ==> deg p <= deg q *)
(* Proof:
   Note p <> |0|         by poly_zero_divides
   Thus ulead p          by poly_field_poly_ulead
   The result follows    by poly_divides_deg_le
*)
val poly_field_divides_deg_le = store_thm(
  "poly_field_divides_deg_le",
  ``!r:'a field. Field r ==>
   !p q. poly p /\ poly q /\ q <> |0| /\ p pdivides q ==> deg p <= deg q``,
  rpt strip_tac >>
  `p <> |0|` by metis_tac[poly_zero_divides] >>
  rw[poly_divides_deg_le, poly_field_poly_ulead]);

(* Theorem: p pdivides q ==> !x. x IN R /\ root p x ==> root q x *)
(* Proof:
       p pdivides q
   ==> ?t. poly t /\ (q = t * p)                by poly_divides_def
   Since root p x ==> eval p x = #0             by poly_root_def
   Then   eval q x = (eval t x) * (eval p x)    by poly_eval_mult
                   = (eval t x) * #0            by above
                   = #0                         by poly_eval_element, ring_mult_lzero
   Hence  root q x                              by poly_root_def
*)
val poly_divides_share_root = store_thm(
  "poly_divides_share_root",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
   !x. x IN R /\ root p x ==> root q x``,
  rw[poly_root_def, poly_divides_def] >>
  rw[]);

(* Theorem: p pdivides q ==> (roots p) SUBSET (roots q) *)
(* Proof:
   Since !x. x IN (roots p)
     ==> root p x                          by poly_roots_member
     ==> root q x                          by poly_divides_share_root
   Therefore (roots p) SUBSET (roots q)    by SUBSET_DEF
*)
val poly_divides_share_roots = store_thm(
  "poly_divides_share_roots",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==> (roots p) SUBSET (roots q)``,
  rw[poly_roots_member, SUBSET_DEF] >>
  metis_tac[poly_divides_share_root]);

(* Theorem: monic p /\ monic q /\ p pdivides q /\ q pdivides p ==> (p = q) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                    by poly_one_eq_poly_zero
       ==> p = |0| = q                  by poly_one_eq_zero, |1| = |0|
   If #1 <> #0,
   Given monic p and monic q,
      so poly p and poly q              by poly_monic_poly
     and p <> |0| and q <> |0|          by poly_monic_nonzero, #1 <> #0
   Given p pdivides q, deg p <= deq q   by poly_divides_deg_le, p <> |0|
   Given q pdivides p, deg q <= deg p   by poly_divides_deg_le, q <> |0|
   Hence deg p = deq q                  by LESS_EQUAL_ANTISYM
     Now p pdivides q means
         ?s. poly s /\ (q = s * p)      by poly_divides_def
    Note monic s                        by poly_monic_monic_mult, monic p, monic q
      so deg q = deg s + deg p          by poly_monic_deg_mult
    thus deg s = 0                      by deg p = deq q
     ==> s = |1|                        by poly_monic_deg_0
   Hence q = |1| * p = p                by poly_mult_lone
*)
val poly_monic_divides_antisymmetric = store_thm(
  "poly_monic_divides_antisymmetric",
  ``!r:'a ring. Ring r ==>
   !p q. monic p /\ monic q /\ p pdivides q /\ q pdivides p ==> (p = q)``,
  rpt strip_tac >>
  `poly p /\ poly q` by rw[] >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  `p <> |0| /\ q <> |0|` by rw[poly_monic_nonzero] >>
  `deg p <= deg q /\ deg q <= deg p` by rw[poly_divides_deg_le] >>
  `deg p = deg q` by decide_tac >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `monic s` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
  `deg q = deg s + deg p` by rw[GSYM poly_monic_deg_mult] >>
  `deg s = 0` by decide_tac >>
  `s = |1|` by rw[GSYM poly_monic_deg_0] >>
  rw[]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
            !c. c IN R ==> p pdivides (c * q) *)
(* Proof:
   Since p pdivides q
     ==> ?s. poly s /\ (q = s * p)    by poly_divides_def
      so c * q = c * (s * p)          by above
               = (c * s) * p          by poly_cmult_mult
   Since poly (c * s)                 by poly_cmult_poly
   Hence p pdivides (c * q)           by poly_divides_def
*)
val poly_divides_cmult = store_thm(
  "poly_divides_cmult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
   !c. c IN R ==> p pdivides (c * q)``,
  metis_tac[poly_divides_def, poly_cmult_mult, poly_cmult_poly]);

(* Theorem: Ring r ==> !c p. c IN R /\ poly p ==> p pdivides (c * p) *)
(* Proof:
   If c = #0,
      Then #0 * p = |0|         by poly_cmult_lzero
       and p pdivides |0|       by poly_divides_zero
   If c <> #0,
      Then c * p = [c] * p      by poly_mult_lconst
     Since poly [c]             by poly_nonzero_element_poly
     Hence p pdivides (c * p)   by poly_divides_def
   Or,
     Since p pdivides p         by poly_divides_reflexive
     Hence p pdivides (c * p)   by poly_divides_cmult
*)
val poly_divides_cmult_alt = store_thm(
  "poly_divides_cmult_alt",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ poly p ==> p pdivides (c * p)``,
  rw[poly_divides_reflexive, poly_divides_cmult]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q ==>
            !c. unit c ==> (p pdivides c * q <=> p pdivides q) *)
(* Proof:
   If part: p pdivides c * q ==> p pdivides q
      Note ?t. poly t /\ (c * q = t * p)  by poly_divides_def
       But |/ c IN R                      by ring_unit_inv_element
       q = ( |/c * c) * q                 by ring_unit_linv, poly_cmult_lone
         = |/ c * (c * q)                 by poly_cmult_cmult
         = |/ c * (t * p)                 by above
         = ( |/ c * t) * p                by poly_cmult_mult
      Note poly ( |/ c * t)               by poly_cmult_poly
      Thus p pdivides q                   by poly_divides_def
   Only-if part: p pdivides q ==> p pdivides c * q
      This is true                        by poly_divides_cmult
*)
val poly_divides_cmult_iff = store_thm(
  "poly_divides_cmult_iff",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==>
   !c. unit c ==> (p pdivides c * q <=> p pdivides q)``,
  rpt strip_tac >>
  rw[EQ_IMP_THM] >| [
    `?t. poly t /\ (c * q = t * p)` by rw[GSYM poly_divides_def] >>
    `|/ c IN R` by rw[ring_unit_inv_element] >>
    `q = ( |/c * c) * q` by rw[ring_unit_linv] >>
    `_ = |/ c * (c * q)` by rw[poly_cmult_cmult] >>
    `_ = |/ c * (t * p)` by rw[] >>
    `_ = ( |/ c * t) * p` by rw[poly_cmult_mult] >>
    metis_tac[poly_divides_def, poly_cmult_poly],
    rw[poly_divides_cmult]
  ]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !c. c IN R /\ c <> #0 ==> (p pdivides c * q <=> p pdivides q) *)
(* Proof:
   Note c IN R+           by field_nonzero_eq
     so unit c            by field_nonzero_unit
   The result follows     by poly_divides_cmult_iff
*)
val poly_field_divides_cmult_iff = store_thm(
  "poly_field_divides_cmult_iff",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !c. c IN R /\ c <> #0 ==> (p pdivides c * q <=> p pdivides q)``,
  rw[poly_divides_cmult_iff, field_nonzero_unit, GSYM field_nonzero_eq]);

(* Theorem: poly p ==> !n. 0 < n ==> p pdivides (p ** n) *)
(* Proof:
   Since 0 < n, ?m. n = SUC m         by num_CASES
      so p ** n = p ** m * p          by poly_exp_suc
      or p pdivides (p ** n)          by poly_divides_def, poly_exp_poly
*)
val poly_divides_exp = store_thm(
  "poly_divides_exp",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. 0 < n ==> p pdivides (p ** n)``,
  metis_tac[poly_exp_suc, poly_divides_def, poly_exp_poly, num_CASES, NOT_ZERO_LT_ZERO]);

(* Theorem: Ring r ==> !p. poly p ==> !m n. m <= n ==> p ** m pdivides p ** n *)
(* Proof:
   Note n = (n - m) + m                 by SUB_ADD
     so p ** n = p ** (n - m) * p ** m  by poly_exp_add
   Thus p ** m pdivides p ** n          by poly_divides_def
*)
val poly_divides_exp_le = store_thm(
  "poly_divides_exp_le",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !m n. m <= n ==> p ** m pdivides p ** n``,
  rpt strip_tac >>
  `p ** n = p ** (n - m) * p ** m` by rw[GSYM poly_exp_add] >>
  metis_tac[poly_divides_def, poly_exp_poly]);

(* Theorem: Ring r ==> !p n. poly p /\ 0 < n ==> (roots p) SUBSET (roots (p ** n)) *)
(* Proof:
   Note p pdivides p ** n                   by poly_divides_exp
   Thus (roots p) SUBSET (roots (p ** n))   by poly_divides_share_roots
*)
val poly_roots_exp_subset = store_thm(
  "poly_roots_exp_subset",
  ``!r:'a ring. Ring r ==> !p n. poly p /\ 0 < n ==> (roots p) SUBSET (roots (p ** n))``,
  rw[poly_divides_exp, poly_divides_share_roots]);

(* Theorem: Ring r ==> !c. unit c ==> !p. poly p ==> [c] pdivides p *)
(* Proof:
   By poly_divides_def, this is to show:
   ?s. poly s /\ (p = s * [c])
   Since c IN R                 by ring_unit_element
      so |/ c IN R              by ring_unit_inv_element
   Take s = |/ c * p
   Then poly s                  by poly_cmult_poly
    and s * [c]
      = c * s                   by poly_mult_rconst
      = c * ( |/c * p)          by above
      = (c * |/c) * p           by poly_cmult_cmult
      = #1 * p                  by ring_unit_rinv
      = p                       by poly_cmult_lone
*)
val poly_const_divides = store_thm(
  "poly_const_divides",
  ``!r:'a ring. Ring r ==> !c. unit c ==> !p. poly p ==> [c] pdivides p``,
  rw[poly_divides_def] >>
  `c IN R /\ |/ c IN R` by rw[ring_unit_element, ring_unit_inv_element] >>
  qexists_tac `|/ c * p` >>
  rw[poly_mult_rconst] >>
  rw[poly_cmult_cmult, ring_unit_rinv]);

(* Theorem: Field r ==> !c. c IN R /\ c <> #0 ==> !p. poly p ==> [c] pdivides p *)
(* Proof:
   Note c IN R+           by field_nonzero_eq
     so unit c            by field_nonzero_unit
   The result follows     by poly_const_divides
*)
val poly_field_const_divides = store_thm(
  "poly_field_const_divides",
  ``!r:'a field. Field r ==> !c. c IN R /\ c <> #0 ==> !p. poly p ==> [c] pdivides p``,
  rw[poly_const_divides, field_nonzero_unit, GSYM field_nonzero_eq]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
            !c. unit c ==> (c * p) pdivides q *)
(* Proof:
   Since p pdivides q,
     ==> ?s. poly s /\ (q = s * p)     by poly_divides_def
   Since c IN R                        by ring_unit_element
     and |/c IN R                      by ring_unit_inv_element
    thus |/ c * c = #1                 by ring_unit_linv
         q = #1 * q                    by poly_cmult_lone
           = ( |/ c * c) * (s * p)     by above
           = |/ c * (c * (s * p))      by poly_cmult_cmult
           = |/ c * (c * s * p)        by poly_cmult_mult
           = |/ c * (s * (c * p))      by poly_mult_cmult
           = ( |/ c * s) * (c * p)     by poly_cmult_mult
   Since poly ( |/ c * s)              by poly_cmult_poly
   Hence (c * p) pdivides q            by poly_divides_def
*)
val poly_cmult_divides = store_thm(
  "poly_cmult_divides",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
   !c. unit c ==> (c * p) pdivides q``,
  rpt strip_tac >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `c IN R /\ |/c IN R` by rw[ring_unit_element, ring_unit_inv_element] >>
  `q = #1 * (s * p)` by rw[] >>
  `_ = ( |/ c * c) * (s * p)` by rw[ring_unit_linv] >>
  `_ = |/ c * (c * (s * p))` by rw[poly_cmult_cmult] >>
  `_ = |/ c * (c * s * p)` by rw[poly_cmult_mult] >>
  `_ = |/ c * (s * (c * p))` by rfs[poly_mult_cmult] >>
  `_ = ( |/ c * s) * (c * p)` by rw[poly_cmult_mult] >>
  metis_tac[poly_divides_def, poly_cmult_poly]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
            !c. c IN R /\ c <> #0 ==> (c * p) pdivides q *)
(* Proof:
   Note c IN R+           by field_nonzero_eq
     so unit c            by field_nonzero_unit
   The result follows     by poly_cmult_divides
*)
val poly_field_cmult_divides = store_thm(
  "poly_field_cmult_divides",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
   !c. c IN R /\ c <> #0 ==> (c * p) pdivides q``,
  rw[poly_cmult_divides, field_nonzero_unit, GSYM field_nonzero_eq]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ (p * q) pdivides q ==> (q = |0|) \/ (upoly p) *)
(* Proof:
   Since (p * q) pdivides q
     ==> ?s. poly s /\ (q = s * (p * q))   by poly_divides_def
     or |1| * q = s * (p * q)              by poly_mult_lone
                = (s * p) * q              by poly_mult_assoc
                = (p * s) * q              by poly_mult_comm
   By contradiction, suppose q <> |0| /\ ~(upoly p).
   Then |1| = p * s                        by poly_mult_rcancel, q <> |0|
   Thus upoly p                            by poly_unit_partner
   which contradicts ~(upoly p)
*)
val poly_mult_divides_factor = store_thm(
  "poly_mult_divides_factor",
  ``!r:'a field. Field r ==>
    !p q. poly p /\ poly q /\ (p * q) pdivides q ==> (q = |0|) \/ (upoly p)``,
  rpt strip_tac >>
  `?s. poly s /\ (q = s * (p * q))` by rw[GSYM poly_divides_def] >>
  `_ = s * p * q` by rw[poly_mult_assoc] >>
  `_ = p * s * q` by rw[poly_mult_comm] >>
  spose_not_then strip_assume_tac >>
  `poly |1| /\ poly (p * s)` by rw[] >>
  `|1| * q = p * s * q` by rw[] >>
  `p * s = |1|` by metis_tac[poly_mult_rcancel] >>
  metis_tac[poly_unit_partner, field_is_ring]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| ==> (p pdivides q <=> (q % p = |0|)) *)
(* Proof:
   Note unit (lead p)  by poly_field_poly_ulead
   The result follows  by poly_divides_alt
*)
val poly_field_divides_alt = store_thm(
  "poly_field_divides_alt",
  ``!r:'a field. Field r ==>
   !p q. poly p /\ poly q /\ p <> |0| ==> (p pdivides q <=> (q % p = |0|))``,
  rw[poly_divides_alt]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q ==>
            !t. poly t /\ (p * q) pdivides t ==> (p pdivides t) /\ (q pdivides t) *)
(* Proof:
   Since (p * q) pdivides t
      ?s. poly s /\ t = s * (p * q)     by poly_divides_def
                      = (s * p) * q     by poly_mult_assoc
   Hence q pdivides t                   by poly_divides_def
    Also t = s * (q * p)                by poly_mult_comm
           = (s * q) * p                by poly_mult_assoc
   Hence p pdivides t                   by poly_divides_def
*)
val poly_mult_divides = store_thm(
  "poly_mult_divides",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==>
   !t. poly t /\ (p * q) pdivides t ==> (p pdivides t) /\ (q pdivides t)``,
  rw[poly_divides_def] >| [
    qexists_tac `s * q` >>
    rw[poly_mult_comm, poly_mult_assoc],
    qexists_tac `s * p` >>
    rw[poly_mult_assoc]
  ]);

(* Theorem: Ring r ==> !p q. p pdivides q ==> !t. poly t ==> p pdivides (t * q) *)
(* Proof:
   Since q pdivides (t * q)      by poly_divides_def
     and poly (t * q)            by poly_mult_poly
   Hence p pdivides (t * q)      by poly_divides_transitive
*)
val poly_divides_mult = store_thm(
  "poly_divides_mult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==> !t. poly t ==> p pdivides (t * q)``,
  metis_tac[poly_divides_def, poly_divides_transitive, poly_mult_poly]);

(* Theorem: Ring r ==> !p q. p pdivides q ==> !t. poly t ==> p pdivides (q * t) *)
(* Proof: by poly_divides_mult, poly_mult_comm. *)
val poly_divides_mult_comm = store_thm(
  "poly_divides_mult_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==> !t. poly t ==> p pdivides (q * t)``,
  metis_tac[poly_divides_mult, poly_mult_comm]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==> !t. poly t ==> p pdivides (t * q) *)
(* Proof:
   Since p pdivides q,
         ?s. poly s /\ (q = s * p)      by poly_divides_def
      so t * q = t * (s * p)
               = (t * s) * p            by poly_mult_assoc
      or p pdivides (t * q)             by poly_divides_def
*)
val poly_divides_multiple = store_thm(
  "poly_divides_multiple",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p pdivides q ==>
   !t. poly t ==> p pdivides (t * q)``,
  rw_tac std_ss[poly_divides_def] >>
  qexists_tac `t * s` >>
  rw[poly_mult_assoc]);

(* This is the same as poly_divides_mult, different proof. *)

(* Note: For any poly p, (p ** 6) cannot divide (p ** 2), but divides (p ** 2) ** 3 *)

(* The mod version of poly_divides_multiple *)

(* Theorem: Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
            !t. poly t  ==> ((t * p) % z = |0|) /\ ((p * t) % z = |0|) *)
(* Proof:
        p % z = |0|
    ==> z pdivides p           by poly_divides_alt
    ==> z pdivides (t * p)     by poly_divides_multiple
    ==> (t * p) % z = |0|      by poly_divides_alt
   Also z pdivides (p * t)     by poly_mult_comm
    ==> (p * t) % z = |0|      by poly_divides_alt
*)
val poly_divides_multiple_mod = store_thm(
  "poly_divides_multiple_mod",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
   !t. poly t  ==> ((t * p) % z = |0|) /\ ((p * t) % z = |0|)``,
  ntac 7 strip_tac >>
  `z pdivides p` by rw[poly_divides_alt] >>
  `z pdivides (t * p)` by rw[poly_divides_multiple] >>
  `z pdivides (p * t)` by metis_tac[poly_mult_comm] >>
  rw[GSYM poly_divides_alt]);

(* Theorem: Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
            !q. poly q ==> ((p * q) / z = (p / z) * q) /\ ((p * q) / z = q * (p / z)) *)
(* Proof:
   Since p % z = |0|
     ==> (p * q) % z = |0|          by poly_divides_multiple_mod
    Thus (p / z) * z = p            by poly_div_multiple_alt, p % z = |0|
     and (p * q) / z * z = p * q    by poly_div_multiple_alt, (p * q) % z = |0|
     Now (p * q) / z * z
       = p * q                      by above
       = (p / z) * z * q            by above, p = (p / z) * z
       = (p / z) * (z * q)          by poly_mult_assoc
       = (p / z) * (q * z)          by poly_mult_comm
       = (p / z) * q * z            by poly_mult_assoc
   Hence (p * q) / z = (p / z) * q  by poly_ulead_mult_rcancel
    Also (p * q) / z * z
       = (q * (p / z)) * z          by poly_mult_comm
   Hence (p * q) / z = q * (p / z)  by poly_ulead_mult_rcancel
*)
val poly_mult_div_alt = store_thm(
  "poly_mult_div_alt",
  ``!r:'a ring. Ring r ==> !p z. poly p /\ ulead z /\ (p % z = |0|) ==>
   !q. poly q ==> ((p * q) / z = (p / z) * q) /\ ((p * q) / z = q * (p / z))``,
  ntac 7 strip_tac >>
  `(p / z) * z = p` by rw[poly_div_multiple_alt] >>
  `(p * q) % z = |0|` by rw[poly_divides_multiple_mod] >>
  `(p * q) / z * z = p * q` by rw[poly_div_multiple_alt] >>
  `_ = (p / z) * z * q` by rw[] >>
  `_ = (p / z) * (z * q)` by rw[poly_mult_assoc] >>
  `_ = (p / z) * (q * z)` by rw[poly_mult_comm] >>
  `_ = (p / z) * q * z` by rw[poly_mult_assoc] >>
  `(p * q) / z * z = (q * (p / z)) * z` by rw[poly_mult_comm] >>
  `poly ((p * q) / z) /\ poly ((p / z) * q) /\ poly (q * (p / z))` by rw[] >>
  metis_tac[poly_ulead_mult_rcancel]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ q <> |0| /\
            (deg p = deg q) /\ p pdivides q ==> q pdivides p *)
(* Proof:
   Since p pdivides q,
         ?t. poly t /\ (q = t * p)     by poly_divides_def
     Now t <> |0|                      by poly_mult_lzero
     and p <> |0|                      by poly_mult_rzero
    Also deg q = deg t + deg p         by poly_deg_mult_nonzero, p <> |0|, q <> |0|
      so deg t = 0                     by arithmetic
    Thus ?c. c IN R /\ c <> #0 /\ (t = [c])
                                       by poly_deg_eq_0, t <> |0|
   Hence p = [ |/ c] * q               by poly_mult_lconst_swap
    also |/ c IN R /\ |/ c <> #0       by field_inv_nonzero, field_nonzero_eq
    thus poly [ |/ c]                  by poly_nonzero_element_poly
   Hence q pdivides p                  by poly_divides_def
*)
val poly_divides_eq_deg = store_thm(
  "poly_divides_eq_deg",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ q <> |0| /\
         (deg p = deg q) /\ p pdivides q ==> q pdivides p``,
  rpt strip_tac >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `t <> |0|` by metis_tac[poly_mult_lzero] >>
  `p <> |0|` by metis_tac[poly_mult_rzero] >>
  `deg q = deg t + deg p` by rw[GSYM poly_deg_mult_nonzero] >>
  `deg t = 0` by decide_tac >>
  `?c. c IN R /\ c <> #0 /\ (t = [c])` by rw[GSYM poly_deg_eq_0] >>
  `p = [ |/ c] * q` by rw[GSYM poly_mult_lconst_swap] >>
  `|/ c IN R /\ |/ c <> #0` by metis_tac[field_inv_nonzero, field_nonzero_eq] >>
  `poly [ |/ c]` by rw[poly_nonzero_element_poly] >>
  metis_tac[poly_divides_def]);

(* However, p pdivides q /\ q pdivides p gives only p = u * q where u = upoly, not p = q *)

(* Theorem: Field r ==> !p q. monic p /\ monic q /\ (deg p = deg q) /\ p pdivides q ==> (p = q) *)
(* Proof:
   Since monic p /\ monic q,
    thus p <> |0| /\ q <> |0|           by poly_monic_nonzero, #1 <> #0
     and poly p /\ poly q               by poly_monic_poly
    with (lead p = #1) /\ (lead q = #1) by poly_monic_lead
   Since p pdivides q,
         ?t. poly t /\ (q = t * p)      by poly_divides_def
     and t <> |0|                       by poly_mult_lzero
    Thus deg q = deg t + deg p          by poly_deg_mult_nonzero, p <> |0|, t <> |0|
      so deg t = 0                      by arithmetic
      or ?c. c IN R /\ c <> #0 /\ (t = [c])   by poly_deg_eq_0, t <> |0|
   Since lead t IN R                    by poly_lead_element
      so lead t = #1                    by poly_lead_mult, field_mult_rone
      or c = #1                         by poly_lead_const
   Hence q = [#1] * p = #1 * p          by poly_mult_lconst
      or q = p                          by poly_mult_lone
*)
val poly_monic_divides_eq_deg_eq = store_thm(
  "poly_monic_divides_eq_deg_eq",
  ``!r:'a field. Field r ==> !p q. monic p /\ monic q /\ (deg p = deg q) /\ p pdivides q ==> (p = q)``,
  rpt strip_tac >>
  `p <> |0| /\ q <> |0|` by rw[poly_monic_nonzero] >>
  `poly p /\ poly q` by rw[] >>
  `(lead p = #1) /\ (lead q = #1)` by rw[] >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `t <> |0|` by metis_tac[poly_mult_lzero] >>
  `deg q = deg t + deg p` by rw[GSYM poly_deg_mult_nonzero] >>
  `deg t = 0` by decide_tac >>
  `?c. c IN R /\ (t = [c])` by metis_tac[poly_deg_eq_0] >>
  `lead t IN R` by rw[] >>
  `lead t = #1` by metis_tac[poly_lead_mult, field_mult_rone] >>
  `c = #1` by metis_tac[poly_lead_const] >>
  rw[poly_mult_lconst]);

(* Theorem: Field r ==> !p q t. poly p /\ poly q /\ poly t /\ p pdivides q ==> t * p pdivides t * q *)
(* Proof:
   If t = |0|,
      Then t * p = |0| = t * q          by poly_mult_lzero
       and |0| pdivides |0|             by poly_divides_zero, poly_zero_poly
   If t <> |0|,
   Since p pdivides q
     ==> ?s. poly s /\ (q = s * p)      by poly_divides_def
      so t * q = t * (s * p)            by poly_mult_lcancel, t <> |0|
               = s * (t * p)            by poly_mult_assoc_comm
   Hence (t * p) pdivides (t * q)       by poly_divides_def
*)
val poly_divides_common_multiple = store_thm(
  "poly_divides_common_multiple",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t /\ p pdivides q ==> t * p pdivides t * q``,
  rpt strip_tac >>
  Cases_on `t = |0|` >| [
    `(t * p = |0|) /\ (t * q = |0|)` by rw[] >>
    metis_tac[poly_divides_zero, poly_zero_poly],
    `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
    `t * q = t * (s * p)` by rw[poly_mult_lcancel] >>
    `_ = s * (t * p)` by rw[poly_mult_assoc_comm] >>
    metis_tac[poly_divides_def]
  ]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ monic t /\ p pdivides q ==> t * p pdivides t * q *)
(* Proof:
   Since p pdivides q
     ==> ?s. poly s /\ (q = s * p)      by poly_divides_def
      so t * q = t * (s * p)            by poly_monic_mult_lcancel
               = s * (t * p)            by poly_mult_assoc_comm
   Hence (t * p) pdivides (t * q)       by poly_divides_def
*)
val poly_monic_divides_common_multiple = store_thm(
  "poly_monic_divides_common_multiple",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ monic t /\ p pdivides q ==> t * p pdivides t * q``,
  rpt strip_tac >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `t * q = t * (s * p)` by rw[poly_monic_mult_lcancel] >>
  `_ = s * (t * p)` by rw[poly_mult_assoc_comm] >>
  metis_tac[poly_divides_def]);

(* Theorem: poly z /\z pdivides p /\ z pdivides q ==>
            !s t. poly s /\ poly t ==> z pdivides (p * s + q * t) *)
(* Proof:
   Since z pdivides p, let p = h * z  with poly h    by poly_divides_def
   Since z pdivides q, let q = k * z  with poly k    by poly_divides_def
   Then   p * s + q * t
        = (h * z) * s + (k * z) * t                  by above
        = s * (h * z) + t * (k * z)                  by poly_mult_comm
        = (s * h) * z + (t * k) * z                  by poly_mult_assoc
        = (s * h + t * k) * z                        by poly_mult_ladd
   Since poly (s * h + t * k)                        by poly_mult_poly, poly_add_poly
   Hence z pdivides (p * s + q * t)                  by poly_divides_def
*)
val poly_divides_linear = store_thm(
  "poly_divides_linear",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
    z pdivides p /\ z pdivides q ==> !s t. poly s /\ poly t ==> z pdivides (p * s + q * t)``,
  rpt strip_tac >>
  `?h. poly h /\ (p = h * z)` by rw[GSYM poly_divides_def] >>
  `?k. poly k /\ (q = k * z)` by rw[GSYM poly_divides_def] >>
  `p * s + q * t = s * (h * z) + t * (k * z)` by rw[poly_mult_comm] >>
  `_ = (s * h) * z + (t * k) * z` by rw[poly_mult_assoc] >>
  `_ = (s * h + t * k) * z` by rw[poly_mult_ladd] >>
  metis_tac[poly_divides_def, poly_mult_poly, poly_add_poly]);

(* Theorem: poly z /\ z pdivides p /\ z pdivides q ==>
            !s t. poly s /\ poly t ==> z pdivides s * p + t * q *)
(* Proof: by poly_divides_linear, poly_mult_comm. *)
val poly_divides_linear_comm = store_thm(
  "poly_divides_linear_comm",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
       z pdivides p /\ z pdivides q ==> !s t. poly s /\ poly t ==> z pdivides s * p + t * q``,
  rw_tac std_ss[poly_divides_linear, poly_mult_comm]);

(* Theorem: poly z /\ pdivides p /\ z pdivides q ==>
            !s t. poly s /\ poly t ==> z pdivides p * s - q * t *)
(* Proof:
   Since p * s - q * t
       = p * s + -(q * t)    by poly_sub_def
       = p * s + q * (-t)    by poly_neg_mult
     and poly (-t)           by poly_neg_poly
   Hence result follows      by poly_divides_linear
*)
val poly_divides_linear_sub = store_thm(
  "poly_divides_linear_sub",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
       z pdivides p /\ z pdivides q ==> !s t. poly s /\ poly t ==> z pdivides p * s - q * t``,
  rpt strip_tac >>
  `p * s - q * t = p * s + q * (-t)` by metis_tac[poly_sub_def, poly_neg_mult] >>
  metis_tac[poly_divides_linear, poly_neg_poly]);

(* Theorem: poly z /\ z pdivides p /\ z pdivides q ==>
            !s t. poly s /\ poly t ==> z pdivides s * p - t * q *)
(* Proof: by poly_divides_linear_sub, poly_mult_comm. *)
val poly_divides_linear_sub_comm = store_thm(
  "poly_divides_linear_sub_comm",
  ``!r:'a ring. Ring r ==> !p q z. poly p /\ poly q /\ poly z /\
       z pdivides p /\ z pdivides q ==> !s t. poly s /\ poly t ==> z pdivides s * p - t * q``,
  rw_tac std_ss[poly_divides_linear_sub, poly_mult_comm]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q ==> !n. (p - q) pdivides (p ** n - q ** n) *)
(* Proof:
   By induction on n.
   Base: p - q pdivides p ** 0 - q ** 0
      Since p ** 0 - q ** 0 = |1| - |1|    by poly_exp_0
                            = |0|          by poly_sub_eq
        and (p - q) pdivides |0|           by poly_divides_zero
   Step: p - q pdivides p ** n - q ** n ==>
         p - q pdivides p ** SUC n - q ** SUC n
      Since p - q pdivides p ** n - q ** n
        ==> ?t. poly t /\ (p ** n - q ** n = t * (p - q))     by poly_divides_def
          p ** SUC n - q ** SUC n
        = p * p ** n - q * q ** n                             by poly_exp_SUC
        = p * p ** n - q * p ** n + q * p ** n - q * q ** n   by poly_sub_add
        = (p - q) * p ** n + q * p ** n - q * q ** n          by poly_mult_lsub
        = (p - q) * p ** n + (q * p ** n - q * q ** n)        by poly_add_sub_assoc
        = (p - q) * p ** n + q * (p ** n - q ** n)            by poly_mult_rsub
        = (p - q) * p ** n + q * t * (p - q)                  by poly_mult_assoc
        = p ** n * (p - q) + q * t * (p - q)                  by poly_mult_comm
        = (p ** n + q * t) * (p - q)                          by poly_mult_ladd

     Hence (p - q) pdivides (p ** SUC n - q ** SUC n)         by poly_divides_def
*)
val poly_sub_divides_exp_sub = store_thm(
  "poly_sub_divides_exp_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> !n. (p - q) pdivides (p ** n - q ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[poly_exp_0, poly_one_poly, poly_sub_eq, poly_sub_poly, poly_divides_zero] >>
  `poly (p - q) /\ poly (p ** n) /\ poly (q ** n)` by rw[] >>
  `?t. poly t /\ (p ** n - q ** n = t * (p - q))` by rw[GSYM poly_divides_def] >>
  `p ** SUC n - q ** SUC n = p * p ** n - q * q ** n` by rw_tac std_ss[poly_exp_SUC] >>
  `_ = p * p ** n - q * p ** n + q * p ** n - q * q ** n` by rw_tac std_ss[poly_sub_add, poly_mult_poly] >>
  `_ = (p - q) * p ** n + q * p ** n - q * q ** n` by rw_tac std_ss[poly_mult_lsub] >>
  `_ = (p - q) * p ** n + (q * p ** n - q * q ** n)` by rw_tac std_ss[poly_add_sub_assoc, poly_mult_poly] >>
  `_ = (p - q) * p ** n + q * (p ** n - q ** n)` by rw_tac std_ss[poly_mult_rsub] >>
  `_ = (p - q) * p ** n + q * t * (p - q)` by rw_tac std_ss[poly_mult_assoc] >>
  `_ = p ** n * (p - q) + q * t * (p - q)` by rw_tac std_ss[poly_mult_comm] >>
  `_ = (p ** n + q * t) * (p - q)` by rw_tac std_ss[poly_mult_ladd, poly_mult_poly] >>
  metis_tac[poly_divides_def, poly_mult_poly, poly_add_poly]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Root Factor Theorem.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> !c. c IN (roots p) <=> c IN R /\ (factor c) pdivides p *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                 by poly_one_eq_poly_zero
        so p = |0|                   by poly_one_eq_zero
       and R = {#0}                  by ring_one_eq_zero
        so roots p = R               by poly_roots_zero
       Hence true by                 by poly_divides_zero
   Otherwise, #1 <> #0.
   If part: c IN (roots p) ==> (factor c) pdivides p
       c IN (roots p)
   <=> root p c               by poly_roots_member
   <=> eval p c = #0          by poly_root_def
   Since pmonic (factor c)    by poly_factor_pmonic
   ?s t. (p = s * (factor c) + t) /\ deg t < deg (factor c)     by poly_division_eqn
   Since deg (factor c) = 1   by poly_deg_factor
      so deg t = 0,
   If t <> |0|, then ?k. k IN R /\ k <> #0 /\ t = [k]           by poly_deg_eq_0
   Now   #0 = eval p c
            = eval (s * (factor c) + [k]) c    by given
            = (eval s c) * (eval (factor c) c) + (eval [k] c)   by poly_eval_add, poly_eval_mult.
            = (eval s c) * (c - c) + (eval [k] c)               by poly_eval_factor
            = (eval s c) * #0 + (eval [k] c)                    by ring_sub_eq
            = k                                                 by poly_eval_const
   But this contradicts k <> #0.
  Hence t = |0|, or (factor c) pdivides p                       by poly_divides_def
  Only-if part: (factor c) pdivides p ==> c IN (roots p)
    (factor c) pdivides p
  <=> ?q. poly q /\ p = q * (factor c)                          by poly_divides_def
  Hence eval p c
      = eval (q * (factor c)) c
      = (eval q c) * (eval (factor c) c)                        by poly_eval_mult
      = (eval q c) * (c - c)                                    by poly_eval_factor
      = (eval q c) * #0                                         by ring_sub_eq
      = #0                                                      by ring_mult_rzero
  or c IN (roots p)                                             by poly_roots_member, poly_root_def
*)
val poly_root_factor = store_thm(
  "poly_root_factor",
  ``!r:'a ring. Ring r ==> !p. poly p ==>
   !c. c IN (roots p) <=> c IN R /\ (factor c) pdivides p``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `p = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    `R = {#0}` by rw[GSYM ring_one_eq_zero] >>
    `roots p = R` by rw[poly_roots_zero] >>
    rw_tac std_ss[EQ_IMP_THM, poly_divides_zero],
    rw[poly_roots_member, poly_root_def, EQ_IMP_THM] >| [
      `pmonic (factor c)` by rw[poly_factor_pmonic] >>
      `?s t. poly s /\ poly t /\ (p = s * (factor c) + t) /\ deg t < deg (factor c)` by rw[poly_division_eqn] >>
      `deg (factor c) = 1` by rw[poly_deg_factor] >>
      `deg t = 0` by decide_tac >>
      `eval (factor c) c = #0` by rw[poly_eval_factor] >>
      Cases_on `t = |0|` >-
      metis_tac[poly_divides_def, poly_mult_poly, poly_add_rzero] >>
      `?k. k IN R /\ k <> #0 /\ (t = [k])` by metis_tac[poly_deg_eq_0] >>
      `poly (s * (factor c))` by rw[] >>
      `eval p c = eval (s * (factor c)) c + eval [k] c` by metis_tac[poly_eval_add] >>
      `_ = (eval s c) * (eval (factor c) c) + k` by rw[poly_eval_mult, poly_eval_const] >>
      `_ = k` by rw[] >>
      metis_tac[],
      `?q. poly q /\ (p = q * (factor c))` by rw[GSYM poly_divides_def] >>
      `poly (factor c)` by rw[poly_factor_poly] >>
      `eval p c = (eval q c) * (eval (factor c) c)` by rw[poly_eval_mult] >>
      `_ = #0 ` by rw[poly_eval_factor] >>
      metis_tac[]
    ]
  ]);
(* This cannot move to polyRoot, as it does not have pdivides. *)

(* Theorem: poly p /\ c IN R ==> (root p c <=> (factor c) pdivides p) *)
(* Proof: by poly_root_factor, poly_roots_member *)
val poly_root_factor_alt = store_thm(
  "poly_root_factor_alt",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ c IN R ==> (root p c <=> (factor c) pdivides p)``,
  metis_tac[poly_root_factor, poly_roots_member]);

(* Theorem: poly p /\ c IN R ==> ((eval p c = #0) <=> (factor c) pdivides p) *)
(* Proof: by poly_root_factor_alt, poly_root_def *)
val poly_root_factor_thm = store_thm(
  "poly_root_factor_thm",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ c IN R ==> ((eval p c = #0) <=> (factor c) pdivides p)``,
  rw[poly_root_factor_alt, GSYM poly_root_def]);

(* Theorem: Ring r ==> !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
            ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * (factor c)) *)
(* Proof:
   Note p <> |0|
    ==> #1 <> #0                          by poly_one_eq_poly_zero, poly_one_eq_zero
       root p c
   ==> p % factor c = |0|                 by poly_root_thm
   ==> (factor x) pdivides p              by poly_divides_alt, poly_factor_pmonic
   ==> ?q. poly q /\ p = q * (factor c)   by poly_divides_def
   Since p <> |0|,
         q <> |0|                         by poly_mult_lzero
         factor c <> |0|                  by poly_mult_rzero
     Now lead (factor c) = #1             by poly_lead_factor
     and lead q <> #0                     by poly_lead_nonzero, q <> |0|
      so lead q * lead (factor c) <> #0   by poly_lead_element, ring_mult_rone
   deg p = deg q + deg (factor c)         by weak_deg_mult_nonzero
         = deg q + 1                      by poly_deg_factor
         = SUC q                          by ADD1
   Hence PRE (deg p) = PRE (SUC q) = q    by PRE
*)
val poly_root_factor_eqn = store_thm(
  "poly_root_factor_eqn",
  ``!r:'a ring. Ring r ==>
   !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
    ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * (factor c))``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
  `p % factor c = |0|` by rw[GSYM poly_root_thm] >>
  `pmonic (factor c)` by rw[poly_factor_pmonic] >>
  `(factor c) pdivides p` by rw[poly_divides_alt] >>
  `?q. poly q /\ (p = q * (factor c))` by rw[GSYM poly_divides_def] >>
  qexists_tac `q` >>
  `q <> |0| /\ factor c <> |0|` by metis_tac[poly_mult_lzero, poly_mult_rzero] >>
  `deg (factor c) = 1` by rw[poly_deg_factor] >>
  `lead (factor c) = #1` by rw[poly_lead_factor] >>
  `lead q <> #0` by rw[poly_lead_nonzero] >>
  `lead q * lead (factor c) <> #0` by metis_tac[poly_lead_element, ring_mult_rone, poly_is_weak] >>
  `deg p = deg q + 1` by rw[weak_deg_mult_nonzero] >>
  `_ = SUC (deg q)` by rw[ADD1] >>
  rw[]);
(* This cannot move to polyRoot, as it does not have pdivides. *)

(* Theorem: Field r ==> !p. poly p ==> !c. c IN roots p <=> c IN R /\ factor c pdivides p *)
(* Proof: by poly_root_factor *)
val poly_field_root_factor = store_thm(
  "poly_field_root_factor",
  ``!r:'a field. Field r ==> !p. poly p ==> !c. c IN roots p <=> c IN R /\ factor c pdivides p``,
  rw[poly_root_factor]);

(* Theorem: Field r ==> !p c. poly p /\ c IN R ==> (root p c <=> factor c pdivides p) *)
(* Proof: by poly_root_factor_alt *)
val poly_field_root_factor_alt = store_thm(
  "poly_field_root_factor_alt",
  ``!r:'a field. Field r ==> !p c. poly p /\ c IN R ==> (root p c <=> factor c pdivides p)``,
  rw[poly_root_factor_alt]);

(* Theorem: Field r ==> !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
            ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * factor c) *)
(* Proof: by poly_root_factor_thm *)
val poly_field_root_factor_thm = store_thm(
  "poly_field_root_factor_thm",
  ``!r:'a field. Field r ==>
   !p c. poly p /\ c IN R ==> (eval p c = #0 <=> factor c pdivides p)``,
  rw[poly_root_factor_thm]);

(* Theorem: Field r ==> !p c. poly p /\ p <> |0| /\ c IN R /\ root p c ==>
            ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * factor c) *)
(* Proof: by poly_root_factor_eqn *)
val poly_field_root_factor_eqn = store_thm(
  "poly_field_root_factor_eqn",
  ``!r:'a field. Field r ==> !p c.
         poly p /\ p <> |0| /\ c IN R /\ root p c ==>
         ?q. poly q /\ (deg q = PRE (deg p)) /\ (p = q * factor c)``,
  rw[poly_root_factor_eqn]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring Unit Equivalence                                          *)
(* ------------------------------------------------------------------------- *)

(* Overload unit equivalence for polynomial *)
val _ = overload_on("~~", ``unit_eq (PolyRing r)``);
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: x ~~ y <=> ?u. upoly u /\ (x = u * y) *)
(* Proof: by unit_eq_def *)
val poly_unit_eq_property = save_thm("poly_unit_eq_property", unit_eq_def |> ISPEC ``PolyRing r`` |> GEN_ALL);
(* val poly_unit_eq_property = |- !r x y. x ~~ y <=> ?u. upoly u /\ (x = u * y): thm *)

(* Theorem: Ring r ==> !u. upoly u <=> u ~~ |1| *)
(* Proof:
      u ~~ |1|
   <=> ?u'. upoly u' /\ (u = u' * |1|)    by poly_unit_eq_property
   <=> ?u'. upoly u' /\ (u = u')          by poly_unit_poly, poly_mult_rone
   <=> upoly u
*)
val poly_unit_eq_one = store_thm(
  "poly_unit_eq_one",
  ``!r:'a ring. Ring r ==> !u. upoly u <=> u ~~ |1|``,
  metis_tac[poly_unit_eq_property, poly_unit_poly, poly_mult_rone]);

(*
related to: polyDividesTheory.poly_divides_one
|- !r. Ring r ==> !p. poly p /\ p pdivides |1| <=> upoly p
*)

(* Theorem: Ring r ==> !p. poly p ==> (p ~~ |0| <=> (p = |0|)) *)
(* Proof:
   If part: p ~~ |0| ==> (p = |0|)
      Since p ~~ |0|
        ==> ?u. upoly u /\ (p = u * |0|)   by poly_unit_eq_property
        now upoly u ==> poly u             by poly_unit_poly
         so p = u * |0| = |0|              by poly_mult_rzero
   Only-if part: (p = |0|) ==> p ~~ |0|
      By poly_unit_eq_property, this is to show:
         ?u. upoly u /\ |0| = u * |0|
      Take u = |1|,
      Then upoly |1|                       by poly_unit_one
       and |0| = |1| * |0|                 by poly_mult_rzero
*)
val poly_unit_eq_zero = store_thm(
  "poly_unit_eq_zero",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p ~~ |0| <=> (p = |0|))``,
  rw_tac std_ss[poly_unit_eq_property, EQ_IMP_THM] >-
  rw[poly_unit_poly] >>
  qexists_tac `|1|` >>
  rw[poly_unit_one]);

(* Theorem: Ring r ==> !p. poly p ==> (p ~~ p) *)
(* Proof: by poly_ring_ring, unit_eq_refl, poly_ring_element *)
val poly_unit_eq_refl = store_thm(
  "poly_unit_eq_refl",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p ~~ p)``,
  rw[poly_ring_ring, unit_eq_refl, poly_ring_element]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> q ~~ p *)
(* Proof: by poly_ring_ring, unit_eq_sym, poly_ring_element *)
val poly_unit_eq_sym = store_thm(
  "poly_unit_eq_sym",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> q ~~ p``,
  rw[poly_ring_ring, unit_eq_sym, poly_ring_element]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ p ~~ q /\ q ~~ t ==> p ~~ t *)
(* Proof: by poly_ring_ring, unit_eq_trans, poly_ring_element *)
val poly_unit_eq_trans = store_thm(
  "poly_unit_eq_trans",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ p ~~ q /\ q ~~ t ==> p ~~ t``,
  metis_tac[poly_ring_ring, unit_eq_trans, poly_ring_element]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. p pdivides t ==> q pdivides t *)
(* Proof:
    Note p ~~ q
     ==> ?u. upoly u /\ (p = u * q)   by poly_unit_eq_property
     and poly u                       by poly_unit_poly
   Since p pdivides t
     ==> ?s. poly s /\ (t = s * p)    by poly_divides_def
    Thus t = s * (u * q)              by above
           = (s * u) * q              by poly_mult_assoc
   Hence q pdivides t                 by poly_divides_def
*)
val poly_unit_eq_divides = store_thm(
  "poly_unit_eq_divides",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. p pdivides t ==> q pdivides t``,
  rpt strip_tac >>
  `?u. upoly u /\ (p = u * q)` by rw[GSYM poly_unit_eq_property] >>
  `poly u` by rw[poly_unit_poly] >>
  `?s. poly s /\ (t = s * p)` by rw[GSYM poly_divides_def] >>
  `_ = (s * u) * q` by rw[poly_mult_assoc] >>
  metis_tac[poly_divides_def, poly_mult_poly]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !c. c IN R ==> c * p ~~ c * q *)
(* Proof:
   Since p ~~ q, ?u. upoly u /\ (p = u * q)      by poly_unit_eq_property
   Hence c * p = c * (u * q) = u * (c * q)       by poly_mult_cmult, poly_cmult_mult
   Thus  c * p ~~ c * q                          by poly_unit_eq_property
*)
val poly_unit_eq_cmult = store_thm(
  "poly_unit_eq_cmult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !c. c IN R ==> c * p ~~ c * q``,
  rw[poly_unit_eq_property] >>
  metis_tac[poly_mult_cmult, poly_cmult_mult, poly_unit_poly]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. poly t ==> p * t ~~ q * t *)
(* Proof:
   Since p ~~ q, ?u. upoly u /\ (p = u * q)      by poly_unit_eq_property
   Hence p * t = (u * q) * t = u * (q * t)       by poly_mult_assoc
   Thus  p * t ~~ q * t                          by poly_unit_eq_property
*)
val poly_unit_eq_mult = store_thm(
  "poly_unit_eq_mult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. poly t ==> p * t ~~ q * t``,
  rw[poly_unit_eq_property] >>
  metis_tac[poly_mult_assoc, poly_unit_poly]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. poly t ==> t * p ~~ t * q *)
(* Proof:
   Since p ~~ q, ?u. upoly u /\ (p = u * q)      by poly_unit_eq_property
   Hence t * p = t * (u * q) = u * (t * q)       by poly_mult_assoc_comm
   Thus  t * p ~~ t * q                          by poly_unit_eq_property
*)
val poly_unit_eq_mult_comm = store_thm(
  "poly_unit_eq_mult_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ p ~~ q ==> !t. poly t ==> t * p ~~ t * q``,
  rw[poly_unit_eq_property] >>
  metis_tac[poly_mult_assoc_comm, poly_unit_poly]);

(* Theorem: Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                 p ~~ q /\ s ~~ t ==> p * s ~~ q * t *)
(* Proof:
   Note p ~~ q ==> ?u. upoly u /\ (p = u * q)   by poly_unit_eq_property
    and s ~~ t ==> ?v. upoly v /\ (s = v * t)   by poly_unit_eq_property
   Thus upoly (u * v)                           by poly_unit_mult
    and poly u /\ poly v           by poly_unit_poly
        p * s
      = (u * q) * (v * t)          by above
      = ((u * q) * v) * t          by poly_mult_assoc
      = (u * (q * v)) * t          by poly_mult_assoc
      = (u * (v * q)) * t          by poly_mult_comm
      = (u * v * q) * t            by poly_mult_assoc
      = (u * v) * (q * t)          by poly_mult_assoc
   Thus p * s ~~ q * t             by poly_unit_eq_property
*)
val poly_unit_eq_mult_pair = store_thm(
  "poly_unit_eq_mult_pair",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
               p ~~ q /\ s ~~ t ==> p * s ~~ q * t``,
  rpt strip_tac >>
  `?u. upoly u /\ (p = u * q)` by rw[GSYM poly_unit_eq_property] >>
  `?v. upoly v /\ (s = v * t)` by rw[GSYM poly_unit_eq_property] >>
  `upoly (u * v)` by rw[poly_unit_mult] >>
  `poly u /\ poly v` by rw[poly_unit_poly] >>
  `p * s = (u * (q * v)) * t` by rw[poly_mult_assoc] >>
  `_ = (u * (v * q)) * t` by rw[poly_mult_comm] >>
  `_ = (u * v) * (q * t)` by rw[poly_mult_assoc] >>
  metis_tac[poly_unit_eq_property]);

(* Theorem: Ring r ==> !p q. monic p /\ monic q ==> (p ~~ q <=> (p = q)) *)
(* Proof:
   If part: p ~~ q ==> (p = q)
   Since p ~~ q
         ?u. upoly u /\ (p = u * q)   by poly_unit_eq_property
      or p = q * u                    by poly_mult_comm
    Thus monic u                      by poly_monic_monic_mult
   Since upoly u, this means u = |1|  by poly_unit_monic
   Hence p = |1| * q = q              by poly_mult_rone
   Only-if part: (p = q) ==> p ~~ q
     That is, p ~~ p, true            by poly_unit_eq_refl, poly_monic_poly
*)
val poly_unit_eq_monic_eq = store_thm(
  "poly_unit_eq_monic_eq",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ monic q ==> (p ~~ q <=> (p = q))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `?u. upoly u /\ (p = u * q)` by rw[GSYM poly_unit_eq_property] >>
    `_ = q * u` by rw[poly_mult_comm, poly_unit_poly] >>
    `monic u` by metis_tac[poly_monic_monic_mult, poly_unit_poly] >>
    `u = |1|` by rw[GSYM poly_unit_monic] >>
    rw[],
    rw[poly_unit_eq_refl]
  ]);

(* Not very useful for poly GCD, which is defined only up to a unit multiple.
   Given two monic p and q, there is a monic (pgcd p g), but also other non-monic GCDs.
   However, it is useful for poly_divides_iff_gcd_fix: pgcd p q ~~ p
   When pgcd p q has another expression, say pgcd p q ~~ t, then if both p and t are monic, p = t.
*)

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ (p = q) ==> (p ~~ q) *)
(* Proof: by poly_ring_ring, ring_eq_unit_eq, poly_ring_element *)
val poly_eq_unit_eq = store_thm(
  "poly_eq_unit_eq",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (p = q) ==> (p ~~ q)``,
  rw[poly_ring_ring, ring_eq_unit_eq, poly_ring_element]);

(* Theorem: Ring r ==> !p. poly p ==> (upoly p <=> ?q. poly q /\ (p * q = |1|)) *)
(* Proof:
   Since Ring (PolyRing r)                          by poly_ring_ring
     and !p. poly p <=> p IN (PolyRing r).carrier   by poly_ring_element
   Result follows by ring_unit_property:
   > ring_unit_property |> ISPEC ``PolyRing r``;
   val it = |- Ring (PolyRing r) ==> !u. upoly u <=>
     u IN (PolyRing r).carrier /\ ?v. v IN (PolyRing r).carrier /\ (u * v = |1|): thm
*)
val poly_ring_units = store_thm(
  "poly_ring_units",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (upoly p <=> ?q. poly q /\ (p * q = |1|))``,
  rw_tac std_ss[poly_ring_ring, ring_unit_property, poly_ring_element]);

(* Theorem: In the polynomial ring F[x], only constants are units. *)

(* Theorem: Field r ==> !p. (upoly p <=> p <> |0| /\ (deg p = 0)) *)
(* Proof:
   After expanding by definitions, this is to show:
   (1) poly p /\ poly y /\ p * y = |1| /\ y * p = |1| ==> p <> |0|
       True by poly_mult_lzero.
   (2) poly p /\ poly y /\ p * y = |1| /\ y * p = |1| ==> deg p = 0
       Since p <> |0| /\ y <> |0|           by poly_mult_lzero
       hence lead p <> #0 /\ lead y <> #0   by poly_lead_nonzero
       and lead p * lead y <> #0            by field_mult_eq_zero
       thus deg p + deg y = deg (p * y)     by weak_deg_mult_nonzero
                          = deg |1| = 0     by poly_deg_on
       Therefore deg p = 0                  by ADD_EQ_0
   (3) poly p /\ p <> [] /\ deg p = 0 ==> ?y. poly y /\ (p * y = |1|) /\ (y * p = |1|)
       Since deg p = 0,
       ?h. h IN R /\ h <> #0 /\ (p = [h])   by poly_deg_eq_zero
       so h IN R+                           by ring_nonzero_eq
       and |/h IN R+,                       by field_inv_nonzero
       or |/h IN R /\ |/h <> #0             by ring_nonzero_eq
       and |/h * h = #1                     by field_mult_linv
       Let y = [|/h],
       then poly y                          by poly_nonzero_element_poly
       and y * p = [|/h] * [h]
                 = |/h * [h]                by poly_mult_lconst
                 = [|/h * h]                by poly_cmult_const_nonzero
                 = [#1]                     by above
                 = |1|                      by poly_one, and #1 <> #0 in Field r.
       p * y = y * p = |1|                  by poly_mult_comm
*)
val poly_field_units = store_thm(
  "poly_field_units",
  ``!r:'a field. Field r ==> !p. poly p ==> (upoly p <=> p <> |0| /\ (deg p = 0))``,
  rw[Invertibles_def, monoid_invertibles_def, GSYM poly_ring_property] >>
  `#1 <> #0 /\ |1| <> |0|` by rw[GSYM poly_one_ne_poly_zero] >>
  rw[EQ_IMP_THM] >-
  metis_tac[poly_mult_lzero, poly_zero] >-
 (`p <> |0| /\ y <> |0|` by metis_tac[poly_mult_lzero] >>
  `lead p <> #0 /\ lead y <> #0` by rw[] >>
  `lead p * lead y <> #0` by rw[field_mult_eq_zero] >>
  `deg p + deg y = deg (p * y)` by rw[weak_deg_mult_nonzero] >>
  `_ = 0` by rw[] >>
  metis_tac[ADD_EQ_0]) >>
  `?h. h IN R /\ h <> #0 /\ (p = [h])` by metis_tac[poly_deg_eq_zero, poly_zero] >>
  `h IN R+` by rw[ring_nonzero_eq] >>
  `|/ h * h = #1` by metis_tac[field_mult_linv] >>
  `|/ h IN R /\ |/ h <> #0` by metis_tac[field_inv_nonzero, ring_nonzero_eq] >>
  `poly [|/ h]` by rw[] >>
  `[|/ h] * [h] = |/ h * [h]` by rw[poly_mult_lconst] >>
  `_ = [|/ h * h]` by rw_tac std_ss[poly_cmult_const_nonzero, field_one_ne_zero] >>
  `_ = |1|` by rw[poly_one, field_one_ne_zero] >>
  metis_tac[poly_mult_comm, field_is_ring]);

(* Theorem: Field r ==> upoly |1| *)
(* Proof:
   Since Field r
     ==> #1 <> #0           by field_one_ne_zero
     ==> |1| <> |0|         by poly_one_ne_poly_zero
     and deg |1| = 0        by poly_deg_one
   Hence upoly |1|          by poly_field_units
*)
val poly_field_unit_one = store_thm(
  "poly_field_unit_one",
  ``!r:'a field. Field r ==> upoly |1|``,
  rw[poly_field_units]);

(* Theorem: Field r ==> !h. h IN R /\ h <> #0 ==> upoly [h] *)
(* Proof:
   Given  h IN R /\ h <> #0,
      so  poly [h]           by poly_nonzero_element_poly
     and  [h] <> |0|         by poly_zero, NOT_NIL_CONS
     and  deg [h] = 0        by poly_deg_const
    thus  upoly [h]          by poly_field_units
*)
val poly_field_const_unit = store_thm(
  "poly_field_const_unit",
  ``!r:'a field. Field r ==> !h. h IN R /\ h <> #0 ==> upoly [h]``,
  rw[poly_field_units]);

(* Theorem: Field r ==> !p. upoly p <=> ?c. c IN R /\ c <> #0 /\ (p = [c]) *)
(* Proof:
   upoly p <=> p IN (Invertibles (PolyRing r).prod).carrier   by overload
   Expanding by definitions, this is to show:
      poly p /\ (?y. poly y /\ (p * y = |1|) /\ (y * p = |1|)) <=> ?c. c IN R /\ c <> #0 /\ (p = [c])
   If part: poly p /\ (?y. poly y /\ (p * y = |1|) /\ (y * p = |1|)) ==> ?c. c IN R /\ c <> #0 /\ (p = [c])
      Since p * y = |1|              by given
            upoly p                  by poly_mult_eq_one
            p <> |0| /\ deg p = 0    by poly_field_units
      Hence true                     by poly_deg_eq_zero
   Only-if part: ?c. c IN R /\ c <> #0 /\ (p = [c]) ==> poly p /\ (?y. poly y /\ (p * y = |1|) /\ (y * p = |1|))
      First, poly [c] is true        by poly_nonzero_element_poly
      Since c <> #0, c IN R+         by field_nonzero_eq
            unit c                   by field_nonzero_unit
         so unit ( |/ c)             by field_unit_has_inv
        and |/ c IN R /\ |/ c <> #0  by field_nonzero_unit, field_nonzero_eq
        Let y = [|/ c]
       Then poly y                   by poly_nonzero_element_poly
        and p * y = [c] * [|/ c]
                  = c * [|/ c]       by poly_mult_lconst
                  = chop [c * |/ c]  by poly_cmult_const
                  = chop [#1]        by field_mult_rinv
                  = |1|              by poly_ring_ids

*)
val poly_field_unit_alt = store_thm(
  "poly_field_unit_alt",
  ``!r:'a field. Field r ==> !p. upoly p <=> ?c. c IN R /\ c <> #0 /\ (p = [c])``,
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, poly_ring_element, GSPECIFICATION] >>
  `Ring r` by rw[] >>
  rw[EQ_IMP_THM] >-
  metis_tac[poly_mult_eq_one, poly_field_units, poly_deg_eq_zero] >-
  rw[poly_nonzero_element_poly] >>
  `unit c` by metis_tac[field_nonzero_eq, field_nonzero_unit] >>
  `unit ( |/ c)` by rw[field_unit_has_inv] >>
  `|/ c IN R /\ |/ c <> #0` by metis_tac[field_inv_element, field_nonzero_unit, field_nonzero_eq] >>
  qexists_tac `[|/ c]` >>
  `poly [|/ c]` by rw[poly_nonzero_element_poly] >>
  `[c] * [|/ c] = chop [c * |/ c]` by rw[poly_mult_lconst, poly_cmult_const] >>
  `_ = chop [#1]` by metis_tac[field_mult_rinv, field_nonzero_unit, field_nonzero_eq] >>
  `_ = |1|` by rw[poly_ring_ids] >>
  rw[poly_mult_comm]);

(* Slightly better than: polyFieldDivisionTheory.poly_field_units
   |- !r. Field r ==> !p. poly p ==> (upoly p <=> p <> |0| /\ (deg p = 0))
*)

(* Theorem: Field r ==> !p. upoly p <=> poly p /\ p <> |0| /\ (deg p = 0) *)
(* Proof:
   If part: upoly p ==> poly p /\ p <> |0| /\ (deg p = 0)
      (1) upoly p ==> poly p         by poly_unit_poly
      (2) upoly p ==> p <> |0|       by poly_unit_zero, |1| <> |0|
      (3) upoly p ==> deg p = 0      by poly_field_unit_alt, poly_deg_const
   Only-if part: poly p /\ p <> |0| /\ (deg p = 0) ==> upoly p
      Since ?c. c IN R /\ c <> #0 /\ (p = [c])   by poly_deg_eq_0
         so upoly p                  by poly_field_unit_alt
*)
val poly_field_unit = store_thm(
  "poly_field_unit",
  ``!r:'a field. Field r ==> !p. upoly p <=> poly p /\ p <> |0| /\ (deg p = 0)``,
  rpt strip_tac >>
  `Ring r /\ |1| <> |0|` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[poly_unit_poly] >-
  metis_tac[poly_unit_zero] >-
  metis_tac[poly_field_unit_alt, poly_deg_const] >>
  metis_tac[poly_field_unit_alt, poly_deg_eq_0]);

(* Theorem: Field r ==> !p. upoly p ==> (deg p = 0) *)
(* Proof: by poly_field_unit *)
val poly_field_unit_deg = store_thm(
  "poly_field_unit_deg",
  ``!r:'a field. Field r ==> !p. upoly p ==> (deg p = 0)``,
  rw[poly_field_unit]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p ~~ q ==> ?c. c IN R /\ c <> #0 /\ (p = c * q) *)
(* Proof:
   Since p ~~ q
     ==> ?u. upoly u /\ (p = u * q)           by poly_unit_eq_property
     and upoly u
     ==> ?c. c IN R /\ c <> #0 /\ (u = [c])   by poly_field_unit_alt
   Hence p = [c] * q = c * q                  by poly_mult_lconst
*)
val poly_field_unit_eq_alt = store_thm(
  "poly_field_unit_eq_alt",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p ~~ q ==> ?c. c IN R /\ c <> #0 /\ (p = c * q)``,
  metis_tac[poly_unit_eq_property, poly_field_unit_alt, poly_mult_lconst, field_is_ring]);

(* Theorem: Field r ==> !p q. upoly p /\ poly q ==> p pdivides q *)
(* Proof:
   Since upoly p <=> ?c. c IN R /\ c <> #0 /\
          (p = [c])            by poly_field_unit_alt
    Thus c IN R+               by field_nonzero_eq
     and |/ c * c = #1         by field_mult_linv
      or |/ c * [c] = [#1]     by poly_cmult_const_nonzero
                    = |1|      by poly_one_alt
     Now q = q * |1|           by poly_mult_rone
           = q * ( |/ c * p)   by above
           = ( |/ c * q) * p   by poly_mult_cmult
   Hence p pdivides q          by poly_divides_def
*)
val poly_field_unit_divides = store_thm(
  "poly_field_unit_divides",
  ``!r:'a field. Field r ==> !p q. upoly p /\ poly q ==> p pdivides q``,
  rw[poly_field_unit_alt] >>
  `c IN R+` by metis_tac[field_nonzero_eq] >>
  `( |/ c * c = #1) /\ #1 <> #0` by rw[] >>
  `|/ c * [c] = |1|` by rw[poly_cmult_const_nonzero, poly_one_alt] >>
  `q = q * |1|` by rw[] >>
  `_ = q * ( |/ c * [c])` by rw[] >>
  `_ = |/ c * q * [c]` by rw[poly_mult_cmult] >>
  `poly ( |/ c * q)` by rw[] >>
  metis_tac[poly_divides_def]);

(* Theorem: Field r ==> !p q. poly p /\ upoly q /\ p pdivides q ==> upoly p *)
(* Proof:
   Since p pdivides q ==>
         ?t. poly t /\ (q = t * p)   by poly_divides_def
     Now q <> |0|                    by poly_unit_zero, |1| <> |0|
      so p <> |0| /\ t <> |0|        by poly_mult_zero
    Thus deg q = deg t + deg p       by poly_deg_mult_nonzero
     But deg q = 0                   by poly_field_unit
      so deg p = 0                   by arithmetic
   Hence upoly p                     by poly_field_unit
*)
val poly_field_divides_unit = store_thm(
  "poly_field_divides_unit",
  ``!r:'a field. Field r ==> !p q. poly p /\ upoly q /\ p pdivides q ==> upoly p``,
  rpt strip_tac >>
  `Ring r /\ |1| <> |0|` by rw[] >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `q <> |0|` by metis_tac[poly_unit_zero] >>
  `p <> |0| /\ t <> |0|` by metis_tac[poly_mult_zero] >>
  `deg q = deg t + deg p` by rw[poly_deg_mult_nonzero] >>
  metis_tac[poly_field_unit, DECIDE``!x y. (x + y = 0) <=> (x = 0) /\ (y = 0)``]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p pdivides q /\ q pdivides p ==> p ~~ q *)
(* Proof:
   If p = |0|,
      Then q = |0|              by poly_zero_divides
       and |0| ~~ |0|           by poly_unit_eq_refl
   If p <> |0|,
   Since p pdivides q ==> ?s. poly s /\ (q = s * p)  by poly_divides_def
     and q pdivides p ==> ?t. poly t /\ (p = t * q)  by poly_divides_def
    Thus |1| * p = t * (s * p)  by poly_mult_lone, above
           = (t * s) * p        by poly_mult_assoc
   Giving t * s = |1|           by poly_mult_rcancel, p <> |0|
     Thus upoly t /\ upoly s    by poly_mult_eq_one
       or p ~~ q                by poly_unit_eq_property
*)
val poly_field_divides_antisym = store_thm(
  "poly_field_divides_antisym",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p pdivides q /\ q pdivides p ==> p ~~ q``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  Cases_on `p = |0|` >-
  metis_tac[poly_zero_divides, poly_unit_eq_refl] >>
  `?s. poly s /\ (q = s * p)` by rw[GSYM poly_divides_def] >>
  `?t. poly t /\ (p = t * q)` by rw[GSYM poly_divides_def] >>
  `poly |1| /\ poly (t * s) /\ ( |1| * p = p)` by rw[] >>
  `_ = t * (s * p)` by metis_tac[] >>
  `_ = (t * s) * p` by rw[poly_mult_assoc] >>
  metis_tac[poly_mult_rcancel, poly_mult_eq_one, poly_unit_eq_property]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (p = u * q) *)
(* Proof:
   Since ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (p = c * q)  by poly_monic_cmult_factor
   Let u = [c], q = q.
    and u <> |0|       by poly_zero, NOT_NIL_CONS
    and deg u = 0      by poly_deg_const
   Hence upoly u       by poly_field_unit_alt
     and p = c * q
           = [c] * q   by poly_mult_lconst
           = u * q     by u = [c]
*)
val poly_monic_mult_factor = store_thm(
  "poly_monic_mult_factor",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
   ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (p = u * q)``,
  rpt strip_tac >>
  `?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (p = c * q)` by rw_tac std_ss[poly_monic_cmult_factor] >>
  qexists_tac `[c]` >>
  qexists_tac `q` >>
  rw[poly_field_unit_alt, poly_mult_lconst]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (q = u * p) *)
(* Proof:
   Since ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (q = c * p)  by poly_monic_cmult_by_factor
   Let u = [c], q = q.
    and u <> |0|       by poly_zero, NOT_NIL_CONS
    and deg u = 0      by poly_deg_const
   Hence upoly u       by poly_field_unit_alt
     and q = c * p
           = [c] * p   by poly_mult_lconst
           = u * p     by u = [c]
*)
val poly_monic_mult_by_factor = store_thm(
  "poly_monic_mult_by_factor",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
   ?u q. upoly u /\ monic q /\ (deg q = deg p) /\ (q = u * p)``,
  rpt strip_tac >>
  `?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (q = c * p)` by rw[poly_monic_cmult_by_factor] >>
  qexists_tac `[c]` >>
  qexists_tac `q` >>
  rw[poly_field_unit_alt, poly_mult_lconst]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ p pdivides q /\ q ~~ t ==> p pdivides t *)
(* Proof:
   Since p pdivides q ==> ?s. poly s /\ (q = s * p)    by poly_divides_def
     and q ~~ t ==> ?u. upoly u /\ (q = u * t)         by poly_unit_eq_property
      so u * t = q = s * p
   Hence ?v. poly v /\ (t = v * (s * p))   by poly_mult_lunit
      or t = v * s * p                     by poly_mult_assoc
    since poly (v * s)                     by poly_mult_poly
    hence p divides t                      by poly_divides_def
*)
val poly_unit_eq_divisor = store_thm(
  "poly_unit_eq_divisor",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ p pdivides q /\ q ~~ t ==> p pdivides t``,
  rw[poly_divides_def, poly_unit_eq_property] >>
  `?v. poly v /\ (t = v * (s * p))` by metis_tac[poly_mult_lunit] >>
  `_ = v * s * p` by rw[poly_mult_assoc] >>
  metis_tac[poly_mult_poly]);

(* Theorem: Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
            p ~~ q /\ s ~~ t ==> (p pdivides s <=> q pdivides t) *)
(* Proof:
   If part: p pdivides s ==> q pdivides t
      Given p ~~ q ==> ?u. upoly u /\ (p = u * q)     by poly_unit_eq_property
      Given s ~~ t ==> ?v. upoly v /\ (t = v * s)     by poly_unit_eq_property
      Since p pdivides s
        ==> ?x. poly x /\ (s = x * p)              by poly_divides_def
         or t = v * s = v * (x * (u * q))          by above
                      = (v * x * u) * q            by poly_mult_assoc
       Thus q pdivides t                           by poly_divides_def
   Only-if part: q pdivides t ==> p pdivides s
      True by symmetry argument.
*)
val poly_unit_eq_divides_iff = store_thm(
  "poly_unit_eq_divides_iff",
  ``!r:'a ring. Ring r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
      p ~~ q /\ s ~~ t ==> (p pdivides s <=> q pdivides t)``,
  rw[poly_divides_def, EQ_IMP_THM] >| [
    `?u. upoly u /\ (p = u * q)` by rw[GSYM poly_unit_eq_property] >>
    `?v. upoly v /\ (s' * p = v * t)` by rw[GSYM poly_unit_eq_property] >>
    `poly u` by rw[poly_unit_poly] >>
    `?z. poly z /\ (t = z * (s' * (u * q)))` by metis_tac[poly_mult_lunit, poly_mult_poly] >>
    `_ = z * s' * u * q` by rw[poly_mult_assoc] >>
    prove_tac[poly_mult_poly],
    `q ~~ p /\ s' * q ~~ s` by rw[poly_unit_eq_sym] >>
    `?u. upoly u /\ (q = u * p)` by rw[GSYM poly_unit_eq_property] >>
    `?v. upoly v /\ (s' * q = v * s)` by rw[GSYM poly_unit_eq_property] >>
    `poly u` by rw[poly_unit_poly] >>
    `?z. poly z /\ (s = z * (s' * (u * p)))` by metis_tac[poly_mult_lunit, poly_mult_poly] >>
    `_ = z * s' * u * p` by rw[poly_mult_assoc] >>
    prove_tac[poly_mult_poly]
  ]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !p u. poly p /\ upoly u ==> (p pdivides u <=> upoly p) *)
(* Proof:
   If part: p pdivides u ==> upoly p
      Since p pdivides u
        ==> ?q. poly q /\ (u = q * p)       by poly_divides_def
        and upoly u
        ==> ?v. poly v /\ (u * v = |1|)     by poly_unit_partner

       Thus |1| = q * p * v
                = p * q * v                 by poly_mult_comm
                = p * (q * v)               by poly_mult_assoc
      Since poly (q * v)                    by poly_mult_poly
      Hence upoly p                         by poly_unit_partner
   Only-if part: upoly p  ==> p pdivides u
      Since upoly u /\ upoly p
        ==> poly u /\ poly p                by poly_unit_poly
        ==> ?q. poly q /\ ( |1| = p * q)     by poly_unit_partner
        Now u = u * |1|                     by poly_mult_rone
              = u * (p * q)                 by above
              = u * (q * p)                 by poly_mult_comm
              = (u * q) * p                 by poly_mult_assoc
      Since poly (u * q)                    by poly_mult_poly
      Hence p pdivides u                    by poly_divides_def
*)
val poly_divides_unit = store_thm(
  "poly_divides_unit",
  ``!r:'a ring. Ring r ==> !p u. poly p /\ upoly u ==> (p pdivides u <=> upoly p)``,
  rw[EQ_IMP_THM] >| [
    `?q. poly q /\ (u = q * p)` by rw[GSYM poly_divides_def] >>
    `?v. poly v /\ ( |1| = q * p * v)` by metis_tac[poly_unit_partner] >>
    `_ = p * q * v` by rw[poly_mult_comm] >>
    `_ = p * (q * v)` by rw[poly_mult_assoc] >>
    metis_tac[poly_unit_partner, poly_mult_poly],
    rw[poly_divides_def] >>
    `poly u /\ poly p` by rw[poly_unit_poly] >>
    `?q. poly q /\ ( |1| = p * q)` by metis_tac[poly_unit_partner] >>
    `u = u * (p * q)` by metis_tac[poly_mult_rone] >>
    `_ = u * q * p` by rw[poly_mult_comm, poly_mult_assoc] >>
    metis_tac[poly_mult_poly]
  ]);

(* Theorem: Field r ==> !p. upoly p ==> (roots p = {}) *)
(* Proof:
   Note upoly p ==> poly p                   by poly_unit_poly
    and |1| <> |0|                           by poly_one_eq_poly_zero, #1 <> #0
    ==> p <> |0|                             by poly_unit_zero
   Also deg p = 0                            by poly_field_unit_deg, Field r
    ==> ?c. c IN R /\ c <> #0 /\ (p = [c])   by poly_deg_eq_0
    But roots [c] = {}                       by poly_roots_const
     or roots p = {}                         by above
*)
val poly_roots_field_unit = store_thm(
  "poly_roots_field_unit",
  ``!r:'a field. Field r ==> !p. upoly p ==> (roots p = {})``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly p` by rw[poly_unit_poly] >>
  `p <> |0|` by metis_tac[poly_unit_zero, poly_one_eq_poly_zero] >>
  `deg p = 0` by rw[poly_field_unit_deg] >>
  `?c. c IN R /\ c <> #0 /\ (p = [c])` by rw[GSYM poly_deg_eq_0] >>
  rw[poly_roots_const]);

(* Theorem: Field r ==> !p. poly p /\ (deg p = 1) ==> ?c. c IN R /\ (roots p = {c}) *)
(* Proof:
   Note p <> |0|                          by poly_deg_zero
    ==> ?u q. upoly u /\ monic q /\
              (deg q = 1) /\ (p = u * q)  by poly_monic_mult_factor, Field r
    and poly u                            by poly_unit_poly
    and poly q                            by poly_monic_poly
   Thus ?c. c IN R /\ (q = factor c)      by poly_monic_deg1_factor, Ring r
    ==> roots q = {c}                     by poly_factor_roots, Ring r
   Also roots u = {}                      by poly_roots_field_unit, Field r
   Thus roots p = {} UNION {c}            by poly_roots_mult]
                = {c}                     by UNION_EMPTY
   Take this c, and the result follows.
*)
val poly_roots_field_deg1 = store_thm(
  "poly_roots_field_deg1",
  ``!r:'a field. Field r ==> !p. poly p /\ (deg p = 1) ==> ?c. c IN R /\ (roots p = {c})``,
  rpt strip_tac >>
  `p <> |0|` by metis_tac[poly_deg_zero, DECIDE``1 <> 0``] >>
  `?u q. upoly u /\ monic q /\ (deg q = 1) /\ (p = u * q)` by metis_tac[poly_monic_mult_factor] >>
  `poly u /\ poly q` by rw[poly_unit_poly] >>
  `?c. c IN R /\ (q = factor c)` by rw[poly_monic_deg1_factor] >>
  `roots q = {c}` by rw[poly_factor_roots] >>
  `roots u = {}` by rw[poly_roots_field_unit] >>
  `roots p = {c}` by rw[poly_roots_mult] >>
  metis_tac[]);

(* Theorem: Ring r ==> !n. (X - |1|) pdivides (unity n) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                           by poly_one_eq_poly_zero
        so unity (n) = |0|                     by poly_one_eq_zero, poly_unity_poly
       ==> (X - |1|) pdivides (unity n)        by poly_divides_zero
   If #1 <> #0,
    Note unity n = X ** n - |1|                by notation
   Since poly (X ** n - |1|)                   by poly_X_exp_n_sub_c
     and eval (X ** n - |1|) #1 = #0           by poly_eval_X_exp_n_sub_c
      so root (X ** n - |1|) #1                by poly_root_def
    Thus (factor #1) pdivides (X ** n - |1|)   by poly_root_factor, poly_roots_member
      or (X - |1|) pdivides (X ** n - |1|)     by poly_factor_one
*)
val poly_unity_1_divides = store_thm(
  "poly_unity_1_divides",
  ``!r:'a ring. Ring r ==> !n. (X - |1|) pdivides (unity n)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_unity_poly, poly_divides_zero] >>
  `|1| = ###1` by rw[poly_ring_sum_1] >>
  `poly (X ** n - |1|)` by rw[] >>
  `eval (X ** n - |1|) #1 = #0` by rw[poly_eval_X_exp_n_sub_c] >>
  `root (X ** n - |1|) #1` by rw[poly_root_def] >>
  metis_tac[poly_root_factor, poly_roots_member, ring_one_element, poly_factor_one]);

(* Theorem: Ring r ==> !n m. (unity n) pdivides (unity (n * m)) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|                            by poly_one_eq_poly_zero
        so unity (n * m) = |0|                  by poly_one_eq_zero, poly_unity_poly
       ==> unity n pdivides unity (n * m)       by poly_divides_zero
   If #1 <> #0,
   Let p = X - |1|, q = X ** m - |1|.
   By two views of peval q (X ** n).
    First,
      peval q (X ** n)
    = (X ** n) ** m - |1|                       by poly_peval_X_exp_n_sub_c
    = X ** (n * m) - |1|                        by poly_exp_mult
    Also,
      Since p pdivides q                        by poly_unity_1_divides
      ?t. poly t /\ (q = t * p)                 by poly_divides_def
      peval q (X ** n)
    = peval (t * p) (X ** n)                    by above
    = peval t (X ** n) * peval p (X ** n)       by poly_peval_mult
    = peval t (X ** n) * (X ** n - |1|)         by poly_peval_X_exp_n_sub_c, poly_exp_1
    Hence X ** (n * m) - |1|
        = peval t (X ** n) * (X ** n - |1|)     by equating peval q (X ** n)
    Since poly (peval t (X ** n))               by poly_peval_poly
     Thus (unity n) pdivides (unity (n * m))    by poly_divides_def
*)
val poly_unity_divides = store_thm(
  "poly_unity_divides",
  ``!r:'a ring. Ring r ==> !n m. (unity n) pdivides (unity (n * m))``,
  rpt strip_tac >>
  rpt strip_tac >>
  Cases_on `#1 = #0` >-
  metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_unity_poly, poly_divides_zero] >>
  `poly X /\ poly (X ** n) /\ ( |1| = ###1)` by rw[poly_ring_sum_1] >>
  qabbrev_tac `p = X - |1|` >>
  qabbrev_tac `q = X ** m - |1|` >>
  `poly p /\ poly q` by rw[Abbr`p`, Abbr`q`] >>
  `p pdivides q` by rw[poly_unity_1_divides, Abbr`p`, Abbr`q`] >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `X ** (n * m) - |1| = (X ** n) ** m - |1|` by rw[poly_exp_mult] >>
  `_ = peval q (X ** n)` by metis_tac[poly_peval_X_exp_n_sub_c] >>
  `_ = peval (t * p) (X ** n)` by rw[] >>
  `_ = peval t (X ** n) * peval p (X ** n)` by rw[poly_peval_mult] >>
  `_ = peval t (X ** n) * (X ** n - |1|)` by metis_tac[poly_peval_X_exp_n_sub_c, poly_exp_1] >>
  `poly (X ** n - |1|) /\ poly (peval t (X ** n))` by rw[] >>
  metis_tac[poly_divides_def]);

(* Theorem: Ring r ==> !n. 0 < n ==> X pdivides (master n) *)
(* Proof:
      master n
    = X * unity (n - 1)            by poly_master_factors, 0 < n
    = unity (n - 1) * X            by poly_mult_comm
    Hence X pdivides (master n)    by poly_divides_def
*)
val poly_X_divides_master = store_thm(
  "poly_X_divides_master",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> X pdivides (master n)``,
  metis_tac[poly_master_factors, poly_divides_def, poly_mult_comm, poly_X, poly_unity_poly]);

(* Theorem: Field r ==> !p. monic p ==> (p pdivides |1| <=> (p = |1|)) *)
(* Proof:
   If part: p pdivides |1| ==> p = |1|
      Note upoly p             by poly_divides_one
      Then deg p = 0           by poly_field_unit
       ==> p = |1|             by poly_monic_deg_0
   Only-if part: p = |1| ==> p pdivides |1|
      This is true             by poly_divides_reflexive
*)
val poly_monic_divides_one = store_thm(
  "poly_monic_divides_one",
  ``!r:'a field. Field r ==> !p. monic p ==> (p pdivides |1| <=> (p = |1|))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  rw[EQ_IMP_THM] >| [
    `upoly p` by metis_tac[poly_divides_one, poly_monic_poly] >>
    `deg p = 0` by metis_tac[poly_field_unit] >>
    metis_tac[poly_monic_deg_0],
    rw[poly_divides_reflexive]
  ]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
