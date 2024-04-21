(* ------------------------------------------------------------------------- *)
(* Polynomial with coefficients from a Field  (Part 2)                       *)
(* To show: Polynomial Division Algorithm for any nonzero polynomials.       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyFieldDivision";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory integralDomainTheory fieldTheory;

open ringIdealTheory fieldIdealTheory;

open groupOrderTheory;
open subgroupTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;

(* val _ = load "polyMonicTheory"; *)
open polyMonicTheory;
open polyDivisionTheory;

(* ------------------------------------------------------------------------- *)
(* Polynomials Division in F[x] Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   A polynomial is just a list of coefficients from a Field r.
   Here a polynomial has no leading zeroes, i.e. not normalized.

   Overloading:
   p / q          = poly_div r p q  (from polyDivision)
   p % q          = poly_mod r p q  (from polyDivision)
*)
(* Definitions and Theorems (# are exported):

   Polynomial Division in F[x]:
#  poly_field_poly_ulead     |- !r. Field r ==> !p. poly p /\ p <> |0| ==> ulead p
#  poly_field_poly_pmonic    |- !r. Field r ==> !p. poly p /\ 0 < deg p ==> pmonic p
   poly_field_division_all   |- !r p q. Field r /\ poly p /\ poly q /\ q <> |0| ==>
                                        (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q)
   poly_field_division       |- !r p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
                                        (p = p / q * q + p % q) /\ deg (p % q) < deg q
   poly_field_division_all_eqn
                             |- !r. Field r ==> !p q. poly p /\ poly q /\ q <> |0| ==>
                                ?s t. poly s /\ poly t /\ p = s * q + t /\
                                      if 0 < deg q then deg t < deg q else t = |0|
   poly_field_division_eqn   |- !r. Field r ==> !p q. poly p /\ poly q /\ 0 < deg q ==>
                                             ?s t. poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q
   poly_field_div_mod_all_def|- !r p q. Field r /\ poly p /\ poly q /\ q <> |0| ==>
                                        poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\
                                        if 0 < deg q then deg (p % q) < deg q else p % q = |0|
   poly_field_div_mod_def    |- !r p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
                                        poly (p / q) /\ poly (p % q) /\
                                        (p = p / q * q + p % q) /\ deg (p % q) < deg q
   poly_field_div_mod_unique |- !r. Field r ==> !p q s1 t1 s2 t2. poly p /\ poly q /\
                                            poly s1 /\ poly t1 /\ poly s2 /\ poly t2 /\
                                            (p = s1 * q + t1) /\ deg t1 < deg q /\
                                            (p = s2 * q + t2) /\ deg t2 < deg q ==> (s1 = s2) /\ (t1 = t2)
   poly_field_div_mod_eqn |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                             (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t)
   poly_field_div_unique  |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                             (p = s * q + t) /\ deg t < deg q ==> (p / q = s)
   poly_field_mod_unique  |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
                                             (p = s * q + t) /\ deg t < deg q ==> (p % q = t)
   poly_field_div_poly    |- !r q p. Field r /\ poly p /\ poly q /\ q <> |0| ==> poly (p / q)
   poly_field_mod_poly    |- !r q p. Field r /\ poly p /\ poly q /\ q <> |0| ==> poly (p % q)


   Polynomial Division Theorems simplification:
   poly_field_div_mod_less   |- !r. Field r ==> !p z. poly p /\ poly z /\ deg p < deg z ==>
                                    (p / z = |0|) /\ (p % z = p)
   poly_field_div_less       |- !r. Field r ==>
                                !p z. poly p /\ poly z /\ deg p < deg z ==> (p / z = |0|)
   poly_field_mod_less       |- !r. Field r ==>
                                !p z. poly p /\ poly z /\ deg p < deg z ==> (p % z = p)
   poly_field_zero_div_mod   |- !r. Field r ==>
                                !z. poly z /\ z <> |0| ==> ( |0| / z = |0|) /\ ( |0| % z = |0|)
   poly_field_zero_div       |- !r. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| / z = |0|)
   poly_field_zero_mod       |- !r. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| % z = |0|)
   poly_field_mod_mod        |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                    (p % z % z = p % z)
   poly_field_div_mod_by_const  |- !r. Field r ==>
                                   !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                                         (p / z = |/ (lead z) * p) /\ (p % z = |0|)
   poly_field_div_by_const   |- !r. Field r ==>
                                !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                                      (p / z = |/ (lead z) * p)
   poly_field_mod_by_const   |- !r. Field r ==>
                                !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                                      (p % z = |0|)
   poly_field_div_mod_const  |- !r. Field r ==> !z. poly z /\ 0 < deg z ==>
                                !c. c IN R /\ c <> #0 ==> ([c] / z = |0|) /\ ([c] % z = [c])
   poly_field_div_const      |- !r. Field r ==> !z. poly z /\ 0 < deg z ==>
                                !c. c IN R /\ c <> #0 ==> ([c] / z = |0|)
   poly_field_mod_const      |- !r. Field r ==> !z. poly z /\ 0 < deg z ==>
                                !c. c IN R /\ c <> #0 ==> ([c] % z = [c])
   poly_field_div_mod_neg    |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                    (-p / z = -(p / z)) /\ (-p % z = -(p % z))
   poly_field_div_neg        |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                    (-p / z = -(p / z))
   poly_field_mod_neg        |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                    (-p % z = -(p % z))
   poly_field_div_mod_multiple   |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                        (p * z / z = p) /\ ((p * z) % z = |0|)
   poly_field_div_multiple       |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (p * z / z = p)
   poly_field_mod_multiple       |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> ((p * z) % z = |0|)
   poly_field_div_multiple_comm  |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (z * p / z = p)
   poly_field_mod_multiple_comm  |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> ((z * p) % z = |0|)
   poly_field_div_mod_id     |- !r. Field r ==> !p. poly p /\ z <> |0| ==>
                                                (p / p = |1|) /\ (p % p = |0|)
   poly_field_add_mod        |- !r. Field r ==> !p q z. poly p /\ poly q /\ poly z /\
                                            deg q < deg z /\ (p = z + q) ==> (p % z = q)
   poly_field_mod_add        |- !r. Field r ==> !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==>
                                            ((p + q) % z = (p % z + q % z) % z)
   poly_field_mod_add_assoc  |- !r. Field r ==> !p q t z. poly p /\ poly q /\ poly t /\ poly z /\ z <> |0| ==>
                                            (((p + q) % z + t) % z = (p + (q + t) % z) % z)
   poly_field_mod_sub        |- !r. Field r ==> !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==>
                                            ((p - q) % z = (p % z - q % z) % z)
   poly_field_mod_mult       |- !r. Field r ==> !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==>
                                            ((p * q) % z = (p % z * q % z) % z)
   poly_field_mod_mult_assoc |- !r. Field r ==> !p q t z. poly p /\ poly q /\ poly t /\ poly z /\ z <> |0| ==>
                                            (((p * q) % z * t) % z = (p * (q * t) % z) % z)
   poly_field_mod_cmult      |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                !c. c IN R ==> ((c * p) % z = (c * p % z) % z)
   poly_field_mod_eq_zero    |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                           ((p % z = |0|) <=> ?q. poly q /\ (p = q * z))
   pmod_field_mod            |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                           (p % z == p) (pm z)
   pmod_field_neg            |- !r. Field r ==> !p1 p2 z. poly p1 /\ poly p2 /\ poly z /\ z <> |0| ==>
                                           ((p1 == p2) (pm z) <=> (-p1 == -p2) (pm z))
   pmod_field_add            |- !r. Field r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\
                                           poly q1 /\ poly q2 /\ poly z /\ z <> |0| ==>
                                           (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 + q1 == p2 + q2) (pm z)
   pmod_field_mult           |- !r. Field r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\
                                           poly q1 /\ poly q2 /\ poly z /\ z <> |0| ==>
                                           (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 * q1 == p2 * q2) (pm z)
   pmod_field_cmult          |- !r. Field r ==> !p1 p2 z. poly p1 /\ poly p2 /\ poly z /\ z <> |0| ==>
                                !c. c IN R ==> (p1 == p2) (pm z) ==> (c * p1 == c * p2) (pm z)
   poly_field_mod_of_zero    |- !r. Field r ==> !z. poly z /\ z <> |0| ==> ([] % z = |0|)
   poly_field_mod_zero       |- !r. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| % z = |0|)
   poly_field_mod_one_all    |- !r. Field r ==> !z. poly z /\ z <> |0| ==>
                                    |1| % z = if deg z = 0 then |0| else |1|
   poly_field_mod_one        |- !r. Field r ==> !z. poly z /\ 0 < deg z ==> ( |1| % z = |1|)
   poly_field_mod_exp        |- !r. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
                                                !n. p ** n % z = (p % z) ** n % z
   poly_field_mod_eq         |- !r z. Field r /\ poly z /\ z <> |0| ==>
                                !p q. poly p /\ poly q ==> ((p % z = q % z) <=> ((p - q) % z = |0|))
   poly_field_mod_eq_divisor |- !r z h. Field r /\ poly z /\ poly h /\ z <> |0| /\
                                           h <> |0| /\ (z % h = |0|) ==>
                                !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (p == q) (pm h)
   poly_field_deg_mod_less   |- !r p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==> deg (p % q) < deg q
   poly_field_div_eq_zero    |- !r. Field r ==> !p q. poly p /\ poly q /\ 0 < deg q ==>
                                                ((p / q = |0|) <=> deg p < deg q)
   poly_field_div_multiple_alt |- !r. Field r ==>
          !p z. poly p /\ poly z /\ z <> |0| /\ (p % z = |0|) ==>
                (p / z * z = p) /\ (z * (p / z) = p)
   poly_field_mult_rcancel   |- !r. Field r ==>
          !p q t. poly p /\ poly q /\ poly t /\ p <> |0| ==> ((q * p = t * p) <=> (q = t))
   poly_field_mult_lcancel   |- !r. Field r ==>
          !p q t. poly p /\ poly q /\ poly t /\ p <> |0 ==> ((p * q = p * t) <=> (q = t))
   poly_field_eval_poly_mod_at_root  |- !r. Field r ==>
          !p q. poly p /\ poly q /\ q <> |0| ==> !x. x IN roots q ==> (eval (p % q) x = eval p x)

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Division in F[x]                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> ulead p *)
(* Proof: by poly_field_unit_lead. *)
val poly_field_poly_ulead = store_thm(
  "poly_field_poly_ulead",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> ulead p``,
  rw[]);

(* Theorem: Field r ==> !p. poly p /\ 0 < deg p ==> pmonic p *)
(* Proof:
   Since deg p <> 0, p <> |0|     by poly_deg_zero
   Hence unit (lead p)            by poly_field_unit_lead
*)
val poly_field_poly_pmonic = store_thm(
  "poly_field_poly_pmonic",
  ``!r:'a field. Field r ==> !p. poly p /\ 0 < deg p ==> pmonic p``,
  metis_tac[poly_field_unit_lead, poly_deg_zero, NOT_ZERO]);

(* export simple results *)
val _ = export_rewrites["poly_field_poly_ulead", "poly_field_poly_pmonic"];

(*
- COMPLETE_INDUCTION;
> val it = |- !P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n : thm

boss\bossLib.sml(122): val completeInduct_on = SingleStep.completeInduct_on

Now poly_field_division_eqn is based on poly_division_eqn.
*)

(* Theorem: poly p /\ poly q /\ q <> |0| ==>
            (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q) *)
(* Proof:
   Note unit (lead q)      by poly_field_poly_ulead
   The result follows      by poly_division_all
*)
val poly_field_division_all = store_thm(
  "poly_field_division_all",
  ``!r:'a field p q. Field r /\ poly p /\ poly q /\ q <> |0| ==>
        (p = p / q * q + p % q) /\ poly (p / q) /\ poly (p % q)``,
  rw[poly_division_all]);

(* Theorem: poly p /\ poly q /\ 0 < deg q ==>
            (p = p / q * q + p % q) /\ deg (p % q) < deg q *)
(* Proof:
   Since 0 < deg q, unit (lead q)    by poly_field_poly_pmonic
   The result follows                by poly_division
*)
val poly_field_division = store_thm(
  "poly_field_division",
  ``!r:'a field p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
          (p = p / q * q + p % q) /\ deg (p % q) < deg q``,
  rw[poly_division]);

(* Theorem: poly p /\ poly q /\ q <> |0| ==>
            ?s t. poly s /\ poly t /\ (p = s * q + t) /\
            if 0 < deg q then deg t < deg q else t = |0| *)
(* Proof:
   Since unit (lead q)       by poly_field_poly_ulead
   The result follows        by poly_division_all_eqn
*)
val poly_field_division_all_eqn = store_thm(
  "poly_field_division_all_eqn",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ q <> |0| ==>
     ?s t. poly s /\ poly t /\ (p = s * q + t) /\
           if 0 < deg q then deg t < deg q else t = |0|``,
  rw[poly_division_all_eqn]);

(* Theorem: poly p /\ poly q /\ 0 < deg q ==> ?s t. p = s * q + t  with deg t < deg q *)
(* Proof:
   Since 0 < deg q, unit (lead q)    by poly_field_poly_pmonic
   The result follows                by poly_division_eqn
*)
val poly_field_division_eqn = store_thm(
  "poly_field_division_eqn",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ 0 < deg q ==>
     ?s t. poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q``,
  rw[poly_division_eqn]);

(* Convert this existence into quotient and remainder operators. *)
(*
val poly_division_lemma = prove(
  ``!(r:'a field) p q. ?s t. Field r /\ poly p /\ poly q /\ 0 < deg q ==> poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q``,
  metis_tac[poly_field_division_eqn]);
*)
(* Old method with RENAME_VARS_CONV ["f"] still required? *)
(*
val poly_field_div_mod_def = new_specification(
  "poly_field_div_mod_def",
  ["poly_div", "poly_mod"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] poly_division_lemma
            |> CONV_RULE (RENAME_VARS_CONV ["pdiv", "pmod"] >>C
                          STRIP_QUANT_CONV (RENAME_VARS_CONV ["f"])));
*)
(*
val poly_field_div_mod_def = new_specification(
  "poly_field_div_mod_def",
  ["poly_div", "poly_mod"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] poly_division_lemma
            |> CONV_RULE (RENAME_VARS_CONV ["pdiv", "pmod"]));
*)
(*
> val poly_field_div_mod_def =
    |- !r p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
               poly (poly_div r p q) /\ poly (poly_mod r p q) /\
               (p = poly_div r p q * q + poly_mod r p q) /\ deg (poly_mod r p q) < deg q : thm*)
(*
val _ = overload_on ("/", ``poly_div r``);
val _ = overload_on ("%", ``poly_mod r``);

val _ = set_fixity "/" (Infixl 600);
val _ = set_fixity "%" (Infixl 650);
*)
(*
- poly_field_div_mod_def;
> val it = |- !r p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
                      poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q : thm
*)

(* Theorem: poly p /\ poly q /\ q <> |0| ==>
            poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\
            if 0 < deg q then deg (p % q) < deg q else p % q = |0| *)
(* Proof:
   Since unit (lead q)    by poly_field_unit_lead
   The result follows     by poly_div_mod_all_def
*)
val poly_field_div_mod_all_def = store_thm(
  "poly_field_div_mod_all_def",
  ``!(r:'a field) p q. Field r /\ poly p /\ poly q /\ q <> |0| ==>
      poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\
      if 0 < deg q then deg (p % q) < deg q else p % q = |0|``,
  rw[poly_div_mod_all_def]);

(* Theorem: poly p /\ poly q /\ 0 < deg q ==>
            poly (p / q) /\ poly (p % q) /\
            (p = p / q * q + p % q) /\ deg (p % q) < deg q *)
(* Proof:
   Since 0 < deg q, unit (lead q)    by poly_field_poly_pmonic
   The result follows                by poly_div_mod_all_def
*)
val poly_field_div_mod_def = store_thm(
  "poly_field_div_mod_def",
  ``!(r:'a field) p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==>
     poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q``,
  rw[poly_div_mod_def]);

(* Theorem: Uniqueness of quotient and remainder:
            (p = s1 * q + t1) /\ deg t1 < deg q
            (p = s2 * q + t2) /\ deg t2 < deg q  ==> (s1 = s2) /\ (t1 = t2) *)
(* Proof:
   If deg q = 0, deg t1 < 0 and deg t2 < 0, which is impossible.
   If deg q <> 0, then 0 < deg q.
   Since unit (lead q)           by poly_field_poly_pmonic
   Result follows                by poly_div_mod_unique
*)
val poly_field_div_mod_unique = store_thm(
  "poly_field_div_mod_unique",
  ``!r:'a field. Field r ==> !p q s1 t1 s2 t2. poly p /\ poly q /\ poly s1 /\ poly t1 /\ poly s2 /\ poly t2 /\
           (p = s1 * q + t1) /\ deg t1 < deg q /\
           (p = s2 * q + t2) /\ deg t2 < deg q  ==> (s1 = s2) /\ (t1 = t2)``,
  ntac 9 strip_tac >>
  Cases_on `deg q = 0` >| [
    `0 <= deg t1 /\ 0 <= deg t2` by rw[] >>
    metis_tac[NOT_LESS],
    `0 < deg q` by decide_tac >>
    metis_tac[poly_div_mod_unique, poly_field_poly_pmonic, field_is_ring]
  ]);

(* Theorem: Uniqueness of quotient and remainder:
            (p = s * q + t) /\ deg t < deg q ==> (s = p /q) /\ (t = p % q) *)
(* Proof: by poly_field_div_mod_def and poly_field_div_mod_unique. *)
val poly_field_div_mod_eqn = store_thm(
  "poly_field_div_mod_eqn",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
     (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t)``,
  ntac 7 strip_tac >>
  `0 < deg q` by decide_tac >>
  `(p = (p / q) * q + (p % q)) /\ deg (p % q) < deg q /\ poly (p / q) /\ poly (p % q)`
    by rw_tac std_ss[poly_field_div_mod_def] >>
  metis_tac[poly_field_div_mod_unique]);

(* Theorem: Uniqueness of p / q *)
(* Proof: by poly_field_div_mod_eqn. *)
val poly_field_div_unique = store_thm(
  "poly_field_div_unique",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q ==> (p / q = s)``,
  metis_tac[poly_field_div_mod_eqn]);

(* Theorem: Uniqueness of p % q *)
(* Proof: by poly_field_div_mod_eqn. *)
val poly_field_mod_unique = store_thm(
  "poly_field_mod_unique",
  ``!r:'a field. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\ (p = s * q + t) /\ deg t < deg q ==> (p % q = t)``,
  metis_tac[poly_field_div_mod_eqn]);

(* Compare these with:
poly_div_poly  |- !r q p. Ring r /\ poly p /\ pmonic q ==> poly (p / q): thm
poly_mod_poly  |- !r q p. Ring r /\ poly p /\ pmonic q ==> poly (p % q): thm
*)

(* Theorem: poly (p / q) *)
val poly_field_div_poly = save_thm("poly_field_div_poly",
  poly_field_div_mod_all_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val poly_field_div_poly = |- !r q p. Field r /\ poly p /\ poly q /\ q <> |0| ==> poly (p / q): thm *)

(* Theorem: poly (p % q) *)
val poly_field_mod_poly = save_thm("poly_field_mod_poly",
  poly_field_div_mod_all_def |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(* > val poly_field_mod_poly = |- !r q p. Field r /\ poly p /\ poly q /\ q <> |0| ==> poly (p % q): thm *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Division Theorems simplification: by 0 < deg p, unit (lead p). *)
(* ------------------------------------------------------------------------- *)

(* Note: 0 < deg z comes from deg p < deq z *)
val poly_field_div_mod_less = store_thm("poly_field_div_mod_less",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ deg p < deg z ==> (p / z = |0|) /\ (p % z = p)``,
  rw[poly_div_mod_less]);

val poly_field_div_less = store_thm("poly_field_div_less",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ deg p < deg z ==> (p / z = |0|)``,
  rw[poly_div_less]);

val poly_field_mod_less = store_thm("poly_field_mod_less",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ deg p < deg z ==> (p % z = p)``,
  rw[poly_mod_less]);

val poly_field_zero_div_mod = store_thm("poly_field_zero_div_mod",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| / z = |0|) /\ ( |0| % z = |0|)``,
  rw[Once poly_zero_div_mod]);

val poly_field_zero_div = store_thm("poly_field_zero_div",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| / z = |0|)``,
  rw[Once poly_zero_div]);

val poly_field_zero_mod = store_thm("poly_field_zero_mod",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| % z = |0|)``,
  rw[Once poly_zero_mod]);

val poly_field_mod_mod = store_thm("poly_field_mod_mod",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> ((p % z) % z = p % z)``,
  rw[Once poly_mod_mod]);

val poly_field_div_mod_by_const = store_thm("poly_field_div_mod_by_const",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                 (p / z = |/ (lead z) * p) /\ (p % z = |0|)``,
  rw[poly_div_mod_by_const]);

val poly_field_div_by_const = store_thm("poly_field_div_by_const",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                 (p / z = |/ (lead z) * p)``,
  rw[Once poly_div_by_const]);

val poly_field_mod_by_const = store_thm("poly_field_mod_by_const",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| /\ (deg z = 0) ==>
                 (p % z = |0|)``,
  rw[Once poly_mod_by_const]);

val poly_field_div_mod_const = store_thm("poly_field_div_mod_const",
  ``!r:'a field. Field r ==> !z. poly z /\ 0 < deg z ==>
    !c. c IN R /\ c <> #0 ==> (([c] / z = |0|) /\ ([c] % z = [c]))``,
  rw[Once poly_div_mod_const]);
(* Note: when deg z = 0, [c] / z <> |0|, but [c] % z = |0| *)

val poly_field_div_const = store_thm("poly_field_div_const",
  ``!r:'a field. Field r ==> !z. poly z /\ 0 < deg z ==>
    !c. c IN R /\ c <> #0 ==> ([c] / z = |0|)``,
  rw[Once poly_div_const]);
(* Note: when deg z = 0, [c] / z <> |0|. *)

val poly_field_mod_const = store_thm("poly_field_mod_const",
  ``!r:'a field. Field r ==> !z. poly z /\ 0 < deg z ==>
    !c. c IN R /\ c <> #0 ==> ([c] % z = [c])``,
  rw[Once poly_mod_const]);
(* Note: when deg z = 0, [c] % z = |0| *)

val poly_field_div_mod_neg = store_thm("poly_field_div_mod_neg",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
    (((- p) / z = - (p / z)) /\ ((- p) % z = - (p % z)))``,
  rw[poly_div_mod_neg]);

val poly_field_div_neg = store_thm("poly_field_div_neg",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (-p / z = -(p / z))``,
  rw[Once poly_div_neg]);

val poly_field_mod_neg = store_thm("poly_field_mod_neg",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (-p % z = -(p % z))``,
  rw[Once poly_mod_neg]);

val poly_field_div_mod_multiple = store_thm("poly_field_div_mod_multiple",
  ``!r:'a field. Field r ==>
    !p z. poly p /\ poly z /\ z <> |0| ==> ((p * z) / z = p) /\ ((p * z) % z = |0|)``,
  rw[poly_div_mod_multiple]);

val poly_field_div_multiple = store_thm("poly_field_div_multiple",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (p * z / z = p)``,
  rw[Once poly_div_multiple]);

val poly_field_mod_multiple = store_thm("poly_field_mod_multiple",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> ((p * z) % z = |0|)``,
  rw[Once poly_mod_multiple]);

val poly_field_div_multiple_comm = store_thm("poly_field_div_multiple_comm",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (z * p / z = p)``,
  rw[Once poly_div_multiple_comm]);

val poly_field_mod_multiple_comm = store_thm("poly_field_mod_multiple_comm",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> ((z * p) % z = |0|)``,
  rw[Once poly_mod_multiple_comm]);

val poly_field_div_mod_id = store_thm("poly_field_div_mod_id",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> (p / p = |1|) /\ (p % p = |0|)``,
  rw[poly_div_mod_id]);

val poly_field_add_mod = store_thm("poly_field_add_mod",
  ``!r:'a field. Field r ==>
    !p q z. poly p /\ poly q /\ poly z /\ deg q < deg z /\ (p = z + q) ==> (p % z = q)``,
  rw[Once poly_add_mod]);
(* Note: when z <> |0| and deg z = 0, p % z = |0| *)

val poly_field_mod_add = store_thm("poly_field_mod_add",
  ``!r:'a field. Field r ==> !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==>
                 ((p + q) % z = (p % z + q % z) % z)``,
  rw[Once poly_mod_add]);

val poly_field_mod_add_assoc = store_thm("poly_field_mod_add_assoc",
  ``!r:'a field. Field r ==> !p q t z. poly p /\ poly q /\ poly t /\ poly z /\ z <> |0| ==>
     (((p + q) % z + t) % z = (p + (q + t) % z) % z)``,
  rw[Once poly_mod_add_assoc]);

val poly_field_mod_sub = store_thm("poly_field_mod_sub",
  ``!r:'a field. Field r ==>
    !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==> ((p - q) % z = (p % z - q % z) % z)``,
  rw[Once poly_mod_sub]);

val poly_field_mod_mult = store_thm("poly_field_mod_mult",
  ``!r:'a field. Field r ==>
    !p q z. poly p /\ poly q /\ poly z /\ z <> |0| ==> ((p * q) % z = (p % z * q % z) % z)``,
  rw[Once poly_mod_mult]);

val poly_field_mod_mult_assoc = store_thm("poly_field_mod_mult_assoc",
  ``!r:'a field. Field r ==> !p q t z. poly p /\ poly q /\ poly t /\ poly z /\ z <> |0| ==>
                 (((p * q) % z * t) % z = (p * (q * t) % z) % z)``,
  rw[Once poly_mod_mult_assoc]);

val poly_field_mod_cmult = store_thm("poly_field_mod_cmult",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
   !c. c IN R ==> ((c * p) % z = (c * p % z) % z)``,
  rw[Once poly_mod_cmult]);

val poly_field_mod_eq_zero = store_thm("poly_field_mod_eq_zero",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
       ((p % z = |0|) <=> ?q. poly q /\ (p = q * z))``,
  rw[Once poly_mod_eq_zero]);

val pmod_field_mod = store_thm("pmod_field_mod",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==> (p % z == p) (pm z)``,
  rw[Once pmod_mod]);

val pmod_field_neg = store_thm("pmod_field_neg",
  ``!r:'a field. Field r ==> !p1 p2 z. poly p1 /\ poly p2 /\ poly z /\ z <> |0| ==>
   ((p1 == p2) (pm z) <=> (- p1 == - p2) (pm z))``,
  rw[Once pmod_neg]);

val pmod_field_add = store_thm("pmod_field_add",
  ``!r:'a field. Field r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\
   poly z /\ z <> |0| ==> (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 + q1 == p2 + q2) (pm z)``,
  rw[Once pmod_add]);

val pmod_field_mult = store_thm("pmod_field_mult",
  ``!r:'a field. Field r ==> !p1 p2 q1 q2 z. poly p1 /\ poly p2 /\ poly q1 /\ poly q2 /\
    poly z /\ z <> |0| ==> (p1 == p2) (pm z) /\ (q1 == q2) (pm z) ==> (p1 * q1 == p2 * q2) (pm z)``,
  rw[Once pmod_mult]);

val pmod_field_cmult = store_thm("pmod_field_cmult",
  ``!r:'a field. Field r ==> !p1 p2 z. poly p1 /\ poly p2 /\ poly z /\ z <> |0| ==>
   !c. c IN R ==> (p1 == p2) (pm z) ==> (c * p1 == c * p2) (pm z)``,
  rw[Once pmod_cmult]);

val poly_field_mod_of_zero = store_thm("poly_field_mod_of_zero",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> ([] % z = |0|)``,
  rw[Once poly_mod_of_zero]);

val poly_field_mod_zero = store_thm("poly_field_mod_zero",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==> ( |0| % z = |0|)``,
  rw[Once poly_mod_zero]);

val poly_field_mod_one = store_thm("poly_field_mod_one",
  ``!r:'a field. Field r ==> !z. poly z /\ 0 < deg z ==> ( |1| % z = |1|)``,
  rw[Once poly_mod_one]);
(* Note: when deg z = 0, |1| % z = |0|, not |1|. *)

val poly_field_mod_one_all = store_thm("poly_field_mod_one_all",
  ``!r:'a field. Field r ==> !z. poly z /\ z <> |0| ==>
         |1| % z = if deg z = 0 then |0| else |1|``,
  rw[Once poly_mod_one_all]);

val poly_field_mod_exp = store_thm("poly_field_mod_exp",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| ==>
    !n. (p ** n) % z = ((p % z) ** n) % z``,
  rw[Once poly_mod_exp]);

val poly_field_mod_eq = store_thm("poly_field_mod_eq",
  ``!(r:'a field) z. Field r /\ poly z /\ z <> |0| ==>
    !p q. poly p /\ poly q ==> ((p % z = q % z) <=> ((p - q) % z = |0|))``,
  rw[Once poly_mod_eq]);

val poly_field_mod_eq_divisor = store_thm("poly_field_mod_eq_divisor",
  ``!(r:'a field) z h. Field r /\ poly z /\ poly h /\
                       z <> |0| /\ h <> |0| /\ (z % h = |0|) ==>
    !p q. poly p /\ poly q /\ (p == q) (pm z) ==> (p == q) (pm h)``,
  metis_tac[poly_mod_eq_divisor, poly_field_poly_ulead, field_is_ring]);

val poly_field_deg_mod_less = store_thm("poly_field_deg_mod_less",
  ``!(r:'a field) p q. Field r /\ poly p /\ poly q /\ 0 < deg q ==> deg (p % q) < deg q``,
  rw[Once poly_deg_mod_less]);
(* Note: when deg q = 0, deg (p % q) < 0 is meaningless. *)

val poly_field_div_eq_zero = store_thm("poly_field_div_eq_zero",
  ``!r:'a field. Field r ==>
    !p q. poly p /\ poly q /\ 0 < deg q ==> ((p / q = |0|) <=> deg p < deg q)``,
  rw[Once poly_div_eq_zero]);
(* Note: when deg q = 0, deg p < 0 is meaningless. *)

val poly_field_div_multiple_alt = store_thm("poly_field_div_multiple_alt",
  ``!r:'a field. Field r ==> !p z. poly p /\ poly z /\ z <> |0| /\ (p % z = |0|) ==>
             ((p / z) * z = p) /\ (z * (p / z) = p)``,
  rw[poly_div_multiple_alt]);

val poly_field_mult_rcancel = store_thm("poly_field_mult_rcancel",
  ``!r:'a field. Field r ==>
    !p q t. poly p /\ poly q /\ poly t /\ p <> |0| ==> ((q * p = t * p) <=> (q = t))``,
  rw[Once poly_ulead_mult_rcancel]);

val poly_field_mult_lcancel = store_thm("poly_field_mult_lcancel",
  ``!r:'a field. Field r ==>
    !p q t. poly p /\ poly q /\ poly t /\ p <> |0| ==> ((p * q = p * t) <=> (q = t))``,
  rw[Once poly_ulead_mult_lcancel]);

val poly_field_eval_poly_mod_at_root = store_thm("poly_field_eval_poly_mod_at_root",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ q <> |0| ==>
    !x. x IN roots q ==> (eval (p % q) x = eval p x)``,
  rw[Once poly_eval_poly_mod_at_root]);




(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
