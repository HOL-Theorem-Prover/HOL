(* ------------------------------------------------------------------------- *)
(* Finite Field: Basic Theory                                                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffBasic";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory numberTheory
     combinatoricsTheory;

open polyFieldModuloTheory;

(* (* val _ = load "fieldTheory"; *) *)
open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open groupMapTheory ringMapTheory fieldMapTheory;

(* val _ = load "fieldInstancesTheory"; *)
open groupInstancesTheory ringInstancesTheory;
open fieldInstancesTheory; (* for GF_property, in prime field homomorphism *)

(* Note:

ring has the following overloads:

val _ = overload_on ("ring_numr", ``r.sum.exp #1``); (* for fallback *)
val _ = overload_on ("##", ``r.sum.exp #1``);        (* current use *)
val _ = overload_on ("**", ``r.prod.exp``);

polynomial changes the following overloads:

val _ = clear_overloads_on "##";
val _ = overload_on ("##", ``(PolyRing r).sum.exp |1|``);
val _ = overload_on ("**", ``(PolyRing r).prod.exp``);

Therefore, keep this file clean by not loading any polynomials.
*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Basic Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   Fp       = (PF r).carrier
*)
(* Definitions and Theorems (# are exported):


   Every Finite Field F has GF(p) as prime sub-field:
   PF_def                |- !r. PF r = <|carrier := IMAGE $## univ(:num);
                                             sum := <|carrier := IMAGE $## univ(:num); op := $+; id := #0|>;
                                            prod := <|carrier := IMAGE $## univ(:num); op := $*; id := #1|>
                                        |>
   PF_property           |- !r. ((PF r).carrier = IMAGE $## univ(:num)) /\
                                ((PF r).sum.carrier = IMAGE $## univ(:num)) /\
                                ((PF r).sum.op = $+) /\ ((PF r).sum.id = #0) /\
                                ((PF r).prod.carrier = IMAGE $## univ(:num)) /\
                                ((PF r).prod.op = $* ) /\ ((PF r).prod.id = #1) /\
                                ((PF r).prod.exp = $** )
   prime_field_carrier_subset     |- !r. Ring r ==> Fp SUBSET R
   prime_field_element            |- !r. Ring r ==> !x. x IN Fp ==> x IN R
   prime_field_sum_abelian_group  |- !r. Field r /\ 0 < char r ==> AbelianGroup (PF r).sum
   prime_field_prod_abelian_group |- !r. Field r /\ 0 < char r ==> AbelianGroup ((PF r).prod excluding #0)
   prime_field_is_field           |- !r. Field r /\ 0 < char r ==> Field (PF r)
   prime_field_field              |- !r. FiniteField r ==> Field (PF r)
   prime_field_finite_field       |- !r. FiniteField r ==> FiniteField (PF r)
   prime_field_subfield           |- !r. Field r ==> subfield (PF r) r
   prime_field_is_subfield        |- !r. FiniteField r ==> PF r <<= r
   prime_field_char               |- !r. FiniteField r ==> (char (PF r) = char r)
#  prime_field_element_element    |- !r. Field r ==> !x. x IN Fp ==> x IN R
   finite_field_homo_GF_PF        |- !r. FiniteField r ==> FieldHomo $## (GF (char r)) (PF r)
   finite_field_iso_GF_PF         |- !r. FiniteField r ==> FieldIso $## (GF (char r)) (PF r)
   finite_field_homo_ZN_PF        |- !r. FiniteField r ==> FieldHomo $## (ZN (char r)) (PF r)
   finite_field_iso_ZN_PF         |- !r. FiniteField r ==> FieldIso $## (ZN (char r)) (PF r)
   prime_field_every_subfield     |- !r s. s <<= r ==> subfield (PF r) s
   prime_field_minimal_subfield   |- !r s. FiniteField r /\ s <<= r ==> PF r <<= s
   prime_field_neg                |- !r. FiniteField r ==> !x. x IN Fp ==> ((PF r).sum.inv x = -x)
   prime_field_card               |- !r. FiniteField r ==> (CARD Fp = char r)
   prime_field_subfield_property  |- !r. FiniteField r ==> PF r <<= r /\ (CARD Fp = char r)
   prime_field_fermat_thm         |- !r. FiniteField r ==> !x. x IN Fp ==> (x ** char r = x)
   prime_field_fermat_all         |- !r. FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x

   Useful Theorems for Finite Field:
   finite_field_prime_sq     |- !r. FiniteField r ==> !z. z IN R /\ z NOTIN Fp ==>
                                    INJ (\e. FST e * #1 + SND e * z) (Fp CROSS Fp) R
   finite_field_prime_sq_alt |- !r. FiniteField r ==> !z. z IN R /\ z NOTIN Fp ==>
                                    INJ (\(i,j). i * #1 + j * z) (Fp CROSS Fp) R
   ZN_prime_field_iso_itself |- !n. prime n ==> FieldIso I (PF (ZN n)) (ZN n)

   Prime Field as Scalar Ring:
   scalar_ring_sum_abelian_group  |- !r. Ring r /\ 0 < char r ==> AbelianGroup (PF r).sum
   scalar_ring_sum_group          |- !r. Ring r /\ 0 < char r ==> Group (PF r).sum
   scalar_ring_prod_abelian_monoid|- !r. Ring r ==> AbelianMonoid (PF r).prod
   scalar_ring_prod_monoid        |- !r. Ring r ==> Monoid (PF r).prod
   scalar_ring_is_ring       |- !r. Ring r /\ 0 < char r ==> Ring (PF r)
   scalar_ring_ring          |- !r. FiniteRing r ==> Ring (PF r)
   scalar_ring_iso_ZN_char   |- !r. Ring r /\ 0 < char r ==> RingIso (\n. ##n) (ZN (char r)) (PF r)
   scalar_ring_char          |- !r. Ring r /\ 0 < char r ==> (char (PF r) = char r)
*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Basic                                                        *)
(* -- properties not involving Vector Space (those are in Advanced)          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Every Finite Field F has GF(p) as prime sub-field.                        *)
(* ------------------------------------------------------------------------- *)

(* Prime Field *)
val PF_def = zDefine`
  PF (r:'a field) =
   <| carrier := IMAGE (r.sum.exp #1) univ(:num);
          sum := <| carrier := IMAGE (r.sum.exp #1) univ(:num); op := r.sum.op; id := #0 |>;
         prod := <| carrier := IMAGE (r.sum.exp #1) univ(:num); op := r.prod.op; id := #1 |>
    |>
`;

(* Theorem: Properties of Prime Field *)
(* Proof: by definition.
   For the last one: (PF r).prod.exp = r.prod.exp
   By FUN_EQ_THM, to show: (PF r).prod.exp x n = x ** n
     (PF r).prod.exp x n
   = FUNPOW ((PF r).prod.op x) n (PF r).prod.id   by monoid_exp_def |> ISPEC ``(PF r).prod``
   = FUNPOW ($* x) n #1                           by (PF r).prod.op = r.prod.op
   = x ** n                                       by monoid_exp_def |> ISPEC ``r.prod``
*)
val PF_property = store_thm(
  "PF_property",
  ``!r:'a field. ((PF r).carrier = IMAGE (r.sum.exp #1) univ(:num)) /\
                ((PF r).sum.carrier = IMAGE (r.sum.exp #1) univ(:num)) /\
                ((PF r).sum.op = r.sum.op) /\ ((PF r).sum.id = #0) /\
                ((PF r).prod.carrier = IMAGE (r.sum.exp #1) univ(:num)) /\
                ((PF r).prod.op = r.prod.op) /\ ((PF r).prod.id = #1) /\
                ((PF r).prod.exp = r.prod.exp)``,
  rw[PF_def, monoid_exp_def, FUN_EQ_THM]);

(* Overload PF carrier *)
val _ = overload_on ("Fp", ``(PF r).carrier``);

(* Theorem: Ring r ==> Fp SUBSET R *)
(* Proof:
   Since Fp = IMAGE $## univ(:num)    by PF_property
   This is to show: ##(x:num) IN R    by SUBSET_DEF
   This is true                       by ring_num_element
*)
val prime_field_carrier_subset = store_thm(
  "prime_field_carrier_subset",
  ``!r:'a ring. Ring r ==> Fp SUBSET R``,
  rw[PF_property, SUBSET_DEF] >>
  rw[ring_num_element]);

(* Theorem: Ring r ==> !x. x IN Fp ==> x IN R *)
(* Proof: by prime_field_carrier_subset, SUBSET_DEF *)
val prime_field_element = store_thm(
  "prime_field_element",
  ``!r:'a ring. Ring r ==> !x. x IN Fp ==> x IN R``,
  rw[prime_field_carrier_subset, GSYM SUBSET_DEF]);

(* export simple result -- this affects some proofs below, better export prime_field_element_element later. *)
(* val _ = export_rewrites ["prime_field_element"]; *)

(* Theorem: Field r /\ 0 < char r ==> AbelianGroup (PF r).sum *)
(* Proof:
   Expanding by definition, this is to show:
   (1) ?x'''. ##x' + ##x'' = ##x''', true                    by field_num_add
   (2) ##x' + ##x'' + ##x''' = ##x' + (##x'' + ##x'''), true by field_num_add, field_num_add_assoc
   (3) ?x. #0 = ##x, true                                    by field_num_0
   (4) #0 + ##x' = ##x', true                                by field_add_lzero
   (5) ?y. (?x. (y = ##x) /\ (y + ##x' = #0), true           by field_num_negative, 0 < char r
   (6) ##x' + ##x'' = ##x'' + ##x'
         ##x' + ##x''
       = ##(x' + x'')   by field_num_add
       = ##(x'' + x')   by ADD_COMM
       = ##x'' + ##x'   by field_num_add
*)
val prime_field_sum_abelian_group = store_thm(
  "prime_field_sum_abelian_group",
  ``!r:'a field. Field r /\ 0 < char r ==> AbelianGroup (PF r).sum``,
  rpt strip_tac >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, PF_def, GSPECIFICATION, IN_IMAGE, IN_UNIV] >-
  metis_tac[field_num_add] >-
  rw[field_num_add_assoc] >-
  metis_tac[field_num_0] >-
  rw[field_add_lzero] >-
  metis_tac[field_num_negative] >>
  metis_tac[field_num_add, ADD_COMM]);

(* Theorem: Field r /\ 0 < char r ==> AbelianGroup ((PF r).prod excluding #0) *)
(* Proof:
   Expanding by definition, this is to show:
   (1) ?x'''. ##x' * ##x'' = ##x''', true since ##x' * ##x'' = ##(x' * x'')  by field_num_mult
   (2) ##x' <> #0 /\ ##x'' <> #0 ==> ##x' * ##x'' <> #0, true                by field_mult_nonzero
   (3) ##x' * ##x'' * ##x''' = ##x' * (##x'' * ##x'''), true                 by field_mult_assoc
   (4) ?x. #1 = ##x, true since #1 = ##1                                     by field_num_1
   (5) #1 <> #0, true                                                        by field_one_ne_zero
   (6) #1 * ##x' = ##x', true                                                by field_mult_lone
   (7) ?y. ((?x. (y = ##x) /\ y <> #0) /\ (y * ##x' = #1), true              by field_num_inverse, 0 < char r
   (8) ##x' * ##x'' = ##x'' * ##x', true                                     by field_mult_comm
*)
val prime_field_prod_abelian_group = store_thm(
  "prime_field_prod_abelian_group",
  ``!r:'a field. Field r /\ 0 < char r ==> AbelianGroup ((PF r).prod excluding #0)``,
  rpt strip_tac >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, excluding_def, PF_def, GSPECIFICATION, IN_IMAGE, IN_DIFF, IN_SING, IN_UNIV] >-
  metis_tac[field_num_mult] >-
  metis_tac[field_mult_nonzero, field_nonzero_eq, field_num_element] >-
  rw[field_mult_assoc] >-
  metis_tac[field_num_1] >-
  rw[] >-
  rw[] >-
  metis_tac[field_num_inverse] >>
  rw[field_mult_comm]);

(* Theorem: Field r /\ 0 < char r ==> Field (PF r) *)
(* Proof:
   By field_def_alt, this is to show:
   (1) AbelianGroup (PF r).sum, true                            by prime_field_sum_abelian_group
   (2) AbelianGroup ((PF r).prod excluding (PF r).sum.id), true by prime_field_prod_abelian_group
   (3) (PF r).sum.carrier = (PF r).carrier, true                by PF_property
   (4) (PF r).prod.carrier = (PF r).carrier, true               by PF_property
   (5) (PF r).prod.op (PF r).sum.id x = (PF r).sum.id, true     by PF_property, field_mult_lzero for ##0 * x = #0
   (6) ##x' * (##x'' + ##x''') = ##x' * ##x'' + ##x' * ##x''', true by field_mult_radd
*)
val prime_field_is_field = store_thm(
  "prime_field_is_field",
  ``!r:'a field. Field r /\ 0 < char r ==> Field (PF r)``,
  rpt strip_tac >>
  rw_tac std_ss[field_def_alt] >-
  rw[prime_field_sum_abelian_group] >-
  rw[prime_field_prod_abelian_group, PF_property] >-
  rw[PF_property] >-
  rw[PF_property] >-
  metis_tac[PF_property, field_mult_lzero, IN_IMAGE, field_num_element] >>
  fs[PF_property]);

(* Theorem: FiniteField r ==> Field (PF r) *)
(* Proof: by prime_field_is_field, finite_field_char_pos *)
val prime_field_field = store_thm(
  "prime_field_field",
  ``!r:'a field. FiniteField r ==> Field (PF r)``,
  rw[prime_field_is_field, finite_field_char_pos, finite_field_is_field]);

(* Theorem: FiniteField r ==> FiniteField (PF r) *)
(* Proof:
   By FiniteField_def, this is to show:
   (1) Field (PF r), true by prime_field_field.
   (2) FINITE (IMAGE $## univ(:num))
       Note 0 < char r                                   by finite_field_char_pos
       Since IMAGE $## univ(:num) = IMAGE $## (count p)  by field_num_mod, MOD_LESS
       result follows                                    by FINITE_COUNT
*)
val prime_field_finite_field = store_thm(
  "prime_field_finite_field",
  ``!r:'a field. FiniteField r ==> FiniteField (PF r)``,
  rpt strip_tac >>
  rw[FiniteField_def] >-
  rw[prime_field_field] >>
  rw[PF_property] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `0 < char r` by rw[finite_field_char_pos] >>
  qabbrev_tac `p = char r` >>
  `IMAGE $## univ(:num) = IMAGE $## (count p)` by
  (rw[EXTENSION] >>
  metis_tac[field_num_mod, MOD_LESS]) >>
  rw[]);

(* Theorem: Field r ==> subfield (PF r) r  *)
(* Proof:
   By subfield_def and FieldHomo_def, this is to show:
   (1) x IN (PF r).carrier ==> x IN R
       True by PF_property, field_num_element.
   (2) GroupHomo I (PF r).sum r.sum
       True by definitions, and field_num_element.
   (3) MonoidHomo I (PF r).prod r.prod
       True by definitions, and field_num_element.
*)
val prime_field_subfield = store_thm(
  "prime_field_subfield",
  ``!r:'a field. Field r ==> subfield (PF r) r``,
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def] >-
  metis_tac[PF_property, IN_IMAGE, field_num_element] >-
 (rw_tac std_ss[GroupHomo_def, PF_def, IN_IMAGE] >>
  metis_tac[field_num_element, field_carriers]) >>
  rw_tac std_ss[MonoidHomo_def, PF_def, IN_IMAGE] >>
  metis_tac[field_num_element, field_carriers]);

(* Theorem: FiniteField r ==> (PF r) <<= r *)
(* Proof:
   FiniteField r ==> Field r                   by FiniteField_def
                 ==> Field (PF r)              by prime_field_field
                 ==> subfield (PF r) r         by prime_field_subfield
   Hence (PF r) <<= r                          by notation
*)
val prime_field_is_subfield = store_thm(
  "prime_field_is_subfield",
  ``!r:'a field. FiniteField r ==> (PF r) <<= r``,
  rw_tac std_ss[FiniteField_def, prime_field_field, prime_field_subfield]);

(* Theorem: FiniteField r ==> (char (PF r) = char r) *)
(* Proof:
   Note (PF r) <<= r            by prime_field_is_subfield
     so char (PF r) = char r    by subfield_char
*)
val prime_field_char = store_thm(
  "prime_field_char",
  ``!r:'a field. FiniteField r ==> (char (PF r) = char r)``,
  rw_tac std_ss[prime_field_is_subfield, subfield_char]);

(* Theorem: x IN Fp ==> x IN R *)
(* Proof:
   Since (PF r) is a subfield   by prime_field_subfield,
   Fp SUBSET R                  by subfield_carrier_subset
   Hence true by SUBSET_DEF.
*)
Theorem prime_field_element_element:
  !r:'a field. Field r ==> !x. x IN Fp ==> x IN R
Proof
  metis_tac[prime_field_subfield, subfield_carrier_subset, SUBSET_DEF]
QED
(* Note: this is more restrictive than prime_field_element: |- !r. Ring r ==> !x. x IN Fp ==> x IN R *)

(* export simple result - terrible idea, causes massive simplifier slowdown *)

(* Theorem: FiniteField r ==> FieldHomo $## (GF (char r)) (PF (char r)) *)
(* Proof:
   By FieldHomo_def, this is to show:
   (1) x IN (GF (char r)).carrier ==> ##x IN (PF r).carrier
       True by GF_property, PF_property.
   (2) GroupHomo $## (GF (char r)).sum (PF r).sum
       By definitions, this is to show: x < char r /\ y < char r ==> ##((x + y) MOD char r) = ##x + ##y
         ##((x + y) MOD char r)
       = ##(x + y)               by field_num_mod, 0 < char r
       = ##x + ##y               by field_num_add
   (3) MonoidHomo $## (GF (char r)).prod (PF r).prod
       Note that 0 < char r      by finite_ring_char, finite_field_is_finite_ring
       and       0 MOD char r    by ZERO_MOD
       By definitions, this is to show:
       (a) x < char r /\ y < char r ==> ##((x * y) MOD char r) = ##x * ##y
             ##((x * y) MOD char r)
           = ##(x * y)               by field_num_mod, 0 < char r
           = ##x * ##y               by field_num_mult
       (b) ##((x * 0) MOD char r) = ##x * ##0
             ##((x * 0) MOD char r)
           = ##0                     by above
           = ##(x * 0)               by MULT_CLAUSES
           = ##x * ##0               by field_num_mult
       (c) ##((0 * y) MOD char r) = ##0 * ##y
             ##((0 * y) MOD char r)
           = ##0                     by above
           = ##(0 * y)               by MULT
           = ##0 * ##y               by field_num_mult
       (d) ##((0 * 0) MOD char r) = ##0 * ##0
           True by field_num_mult.
*)
val finite_field_homo_GF_PF = store_thm(
  "finite_field_homo_GF_PF",
  ``!r:'a field. FiniteField r ==> FieldHomo (r.sum.exp #1) (GF (char r)) (PF r)``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  rw[FieldHomo_def, RingHomo_def] >| [
    pop_assum mp_tac >>
    rw[GF_property, PF_property],
    rw[GroupHomo_def, GF_property, PF_property] >>
    `0 < char r` by decide_tac >>
    metis_tac[field_num_mod, field_num_add],
    `0 < char r` by rw[finite_field_char_pos] >>
    `!n:num. (n * 0 = 0) /\ (0 * n = 0) /\ (0 MOD char r = 0)` by rw_tac arith_ss[ZERO_MOD] >>
    rw[MonoidHomo_def, GF_property, PF_property, including_def] >-
    metis_tac[field_num_mod, field_num_mult] >-
    rw[] >-
    rw[] >>
    rw[]
  ]);

(* Theorem: FiniteField r ==> FieldIso $## (GF (char r)) (PF (char r)) *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo $## (GF (char r)) (PF r),
       True by finite_field_homo_GF_PF.
   (2) BIJ $## (GF (char r)).carrier (PF r).carrier
       By definitions, this is to show:
       (a) x < char /\ y < char /\ ##x = ##y ==> x = y
           ##x = ##y <=> x = y, true by finite_field_num_eq.
       (b) ?y. y < char r /\ (##y = ##x')
           Let y = x' MOD char r, then
           0 < char r                by finite_field_char_pos
           n MOD char r < char r     by MOD_LESS
           ##(x' MOD char r) = ##x'  by field_num_mod
*)
val finite_field_iso_GF_PF = store_thm(
  "finite_field_iso_GF_PF",
  ``!r:'a field. FiniteField r ==> FieldIso (r.sum.exp #1) (GF (char r)) (PF r)``,
  rw[FieldIso_def] >-
  rw[finite_field_homo_GF_PF] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  rw[GF_property, PF_property, BIJ_DEF, SURJ_DEF, INJ_DEF] >-
  metis_tac[field_num_eq] >>
  metis_tac[field_num_mod, MOD_LESS, finite_field_char_pos]);

(* Theorem: FiniteField r ==> FieldHomo $## (ZN (char r)) (PF (char r)) *)
(* Proof:
   Note that 0 < char r          by finite_field_char_pos
   By FieldHomo_def, this is to show:
   (1) x IN (ZN (char r)).carrier ==> ##x IN (PF r).carrier
       True by ZN_property, PF_property.
   (2) GroupHomo $## (ZN (char r)).sum (PF r).sum
       By definitions, this is to show: x < char r /\ y < char r ==> ##((x + y) MOD char r) = ##x + ##y
         ##((x + y) MOD char r)
       = ##(x + y)               by field_num_mod, 0 < char r
       = ##x + ##y               by field_num_add
   (3) MonoidHomo $## (ZN (char r)).prod (PF r).prod
       By definitions, this is to show:
       (a) char r = 1 ==> F
           True, since char r <> 1   by field_char_ne_1
       (b) x < char r /\ y < char r ==> ##((x * y) MOD char r) = ##x * ##y
             ##((x * y) MOD char r)
           = ##(x * y)               by field_num_mod, 0 < char r
           = ##x * ##y               by field_num_mult
*)
val finite_field_homo_ZN_PF = store_thm(
  "finite_field_homo_ZN_PF",
  ``!r:'a field. FiniteField r ==> FieldHomo (r.sum.exp #1) (ZN (char r)) (PF r)``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `0 < char r` by rw[finite_field_char_pos] >>
  rw[FieldHomo_def, RingHomo_def] >-
  rw[ZN_property, PF_property] >-
 (`(ZN (char r)).sum.carrier = (ZN (char r)).carrier` by rw[ZN_ring, ring_carriers] >>
  rw[GroupHomo_def, ZN_property, PF_property] >>
  metis_tac[field_num_mod, field_num_add]) >>
  `(ZN (char r)).prod.carrier = (ZN (char r)).carrier` by rw[ZN_ring, ring_carriers] >>
  rw[MonoidHomo_def, ZN_property, PF_property, including_def] >-
  metis_tac[field_char_ne_1] >>
  metis_tac[field_num_mod, field_num_mult]);

(* Theorem: FiniteField r ==> FieldIso $## (ZN (char r)) (PF (char r)) *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo $## (ZN (char r)) (PF r),
       True by finite_field_homo_ZN_PF.
   (2) BIJ $## (ZN (char r)).carrier (PF r).carrier
       By definitions, this is to show:
       (a) x < char /\ y < char /\ ##x = ##y ==> x = y
           ##x = ##y <=> x = y, true by field_num_eq, 0 < char r
       (b) ?y. y < char r /\ (##y = ##x')
           Let y = x' MOD char r, then
           0 < char r                by finite_field_char_pos
           n MOD char r < char r     by MOD_LESS
           ##(x' MOD char r) = ##x'  by field_num_mod
*)
val finite_field_iso_ZN_PF = store_thm(
  "finite_field_iso_ZN_PF",
  ``!r:'a field. FiniteField r ==> FieldIso (r.sum.exp #1) (ZN (char r)) (PF r)``,
  rw[FieldIso_def] >-
  rw[finite_field_homo_ZN_PF] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `0 < char r` by rw[finite_field_char_pos] >>
  rw[ZN_property, PF_property, BIJ_DEF, SURJ_DEF, INJ_DEF] >-
  metis_tac[field_num_eq] >>
  metis_tac[field_num_mod, MOD_LESS]);

(* Theorem: s <<= r ==> subfield (PF r) s *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) x IN (PF r).carrier ==> x IN B
       x IN Fp means ?n. x = ##n      by PF_property, IN_IMAGE
       s.sum.exp s.prod.id n = ##n    by subfield_num
       Hence true                     by field_num_element
   (2) GroupHomo I (PF r).sum s.sum
       After expanding by defintions, this is to show:
       (a) ##x' + ##x'' = s.sum.op (##x') (##x''), true by subfield_property.
   (3) MonoidHomo I (PF r).prod s.prod
       After expanding by defintions, this is to show:
       (a) ##x' * ##x'' = s.prod.op (##x') (##x''), true by subfield_property.
       (b) #1 = s.prod.id, true       by subfield_ids.
*)
Theorem prime_field_every_subfield:
  !(r s):'a field. s <<= r ==> subfield (PF r) s
Proof
  rpt strip_tac >>
  ‘!n. s.sum.exp s.prod.id n = ##n’ by rw[subfield_num] >>
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def] >| [
    ‘?n. x = ##n’ by metis_tac[PF_property, IN_IMAGE] >>
    metis_tac[field_num_element],
    rw[GroupHomo_def, PF_property] >>
    metis_tac[subfield_property, field_num_element],
    rw[MonoidHomo_def, PF_property]
    >- metis_tac[subfield_property, field_num_element]
    >- metis_tac[subfield_property, field_num_element] >>
    rw[subfield_ids, subfield_property]
  ]
QED

(* Theorem: FiniteField r /\ s <<= r ==> (PF r) <<= s *)
(* Proof: by prime_field_every_subfield, prime_field_field *)
val prime_field_minimal_subfield = store_thm(
  "prime_field_minimal_subfield",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> (PF r) <<= s``,
  rw_tac std_ss[prime_field_every_subfield, prime_field_field]);

(* Theorem: FiniteField r ==> !x. x IN Fp ==> ((PF r).sum.inv x = -x) *)
(* Proof:
   Since FiniteField r
     ==> Field (PF r)                         by prime_field_field
      so (PF r).sum.inv x IN Fp               by field_neg_element
     and (PF r).sum.op ((PF r).sum.inv x) x = (PF r).sum.id  by field_add_lneg
      or (PF r).sum.inv x + x = #0            by PF_property
     Now x IN R                               by prime_field_element
     and (PF r).sum.inv x IN R                by prime_field_element
    Also Group r.sum /\ (R = r.sum.carrier)   by field_add_group
   Hence (PF r).sum.inv x = -x                by group_linv_unique
*)
val prime_field_neg = store_thm(
  "prime_field_neg",
  ``!r:'a field. FiniteField r ==> !x. x IN Fp ==> ((PF r).sum.inv x = -x)``,
  rpt (stripDup[FiniteField_def]) >>
  `Field (PF r)` by rw[prime_field_field] >>
  `(PF r).sum.inv x IN Fp` by rw[] >>
  `(PF r).sum.inv x + x = #0` by metis_tac[PF_property, field_add_lneg] >>
  metis_tac[field_add_group, group_linv_unique, prime_field_element, field_is_ring]);

(* Theorem: FiniteField r ==> (CARD Fp = char r) *)
(* Proof:
   Since FieldIso $## (GF (char r)) (PF r)   by finite_field_iso_GF_PF
   i.e.   BIJ $## (GF (char r)).carrier Fp   by FieldIso_def
   Since  prime (char r)                     by finite_field_char
          FiniteField (GF (char r))          by GF_finite_field
      ==> FINITE (GF (char r)).carrier       by FiniteField_def
     and  FiniteField (PF r)                 by prime_field_finite_field
      ==> FINITE Fp                          by FiniteField_def
     CARD Fp
   = CARD (GF (char r)).carrier              by FINITE_BIJ_CARD_EQ
   = CARD (count (char r))                   by GF_property
   = char r                                  by CARD_COUNT
*)
val prime_field_card = store_thm(
  "prime_field_card",
  ``!r:'a field. FiniteField r ==> (CARD Fp = char r)``,
  rpt strip_tac >>
  `FieldIso $## (GF (char r)) (PF r)` by rw[finite_field_iso_GF_PF] >>
  `BIJ $## (GF (char r)).carrier Fp` by metis_tac[FieldIso_def] >>
  `prime (char r)` by rw[finite_field_char] >>
  `FiniteField (GF (char r))` by rw[GF_finite_field] >>
  `FiniteField (PF r)` by rw[prime_field_finite_field] >>
  metis_tac[FiniteField_def, FINITE_BIJ_CARD_EQ, GF_property, CARD_COUNT]);

(* Theorem: FiniteField r ==> (PF r) <<= r /\ (CARD Fp = char r) *)
(* Proof: by prime_field_is_subfield, prime_field_card. *)
val prime_field_subfield_property = store_thm(
  "prime_field_subfield_property",
  ``!r:'a field. FiniteField r ==> (PF r) <<= r /\ (CARD Fp = char r)``,
  rw[prime_field_is_subfield, prime_field_card]);

(*
> finite_field_fermat_thm |> SPEC ``PF r``;
val it = |- FiniteField (PF r) ==> !x. x IN Fp ==> ((PF r).prod.exp x (CARD Fp) = x): thm
*)

(* Theorem: FiniteField r ==> !x. x IN Fp ==> (x ** char r = x) *)
(* Proof:
   Note FiniteField (PF r)        by prime_field_finite_field
    and CARD Fp = char r          by prime_field_card
    and (PF r).prod.exp = $**     by PF_property
   Hence x ** char r = x          by finite_field_fermat_thm
*)
val prime_field_fermat_thm = store_thm(
  "prime_field_fermat_thm",
  ``!r:'a field. FiniteField r ==> !x. x IN Fp ==> (x ** char r = x)``,
  metis_tac[prime_field_finite_field, prime_field_card, finite_field_fermat_thm, PF_property]);

(* Theorem: FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x *)
(* Proof:
   Note FiniteField (PF r)        by prime_field_finite_field
    and CARD Fp = char r          by prime_field_card
    and (PF r).prod.exp = $**     by PF_property
   Hence x ** char r ** n = x     by finite_field_fermat_all
*)
val prime_field_fermat_all = store_thm(
  "prime_field_fermat_all",
  ``!r:'a field. FiniteField r ==> !x. x IN Fp ==> !n. x ** char r ** n = x``,
  metis_tac[prime_field_finite_field, prime_field_card, finite_field_fermat_all, PF_property]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems for Finite Field.                                         *)
(* ------------------------------------------------------------------------- *)

(*
Since every FiniteField r has prime subfield (PF r), Fp SUBSET R, and |Fp| = p elements, distinct.
If there is another element e NOTIN Fp, then {i * #1 + j * e, i, j IN Fp} SUBSET R, with p^2 elements, distinct.
*)

(* Theorem: If z NOTIN Fp, then Fp x Fp maps to distinct elements in R via (\(i, j). i * #1 + j * z). *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) FST e IN Fp /\ SND e IN Fp ==> FST e * #1 + SND e * z IN R
       Since FST e IN R /\ SND e IN R     by prime_field_element_element
       This is true by field_mult_element, field_add_element.
   (2) FST e IN Fp /\ SND e IN Fp /\ FST e' IN Fp /\ SND e' IN Fp /\ FST e + SND e * z = FST e' + SND e' * z ==> e = e'
       Since FST e IN R /\ SND e IN R   by prime_field_element_element
         and FST e' IN R /\ SND e' IN R   by prime_field_element_element
            FST e + SND e * z = FST e' + SND e' * z
       <=>  FST e - FST e' = (SND e' - SND e) * z
       If SND e' <> SND e, |/ (SND e' - SND e) exists,
       and   z = (FST e - FST e') / (SND e' - SND e) IN Fp, a contradiction.
       Therefore  SND e = SND e',
       and        FST e - FST e' = #0 * z = #0 ==> FST e = FST e',
       Hence e = e'   by PAIR_FST_SND_EQ.
*)
Theorem finite_field_prime_sq:
  !r:'a field.
    FiniteField r ==>
    !z. z IN R /\ z NOTIN Fp ==>
        INJ (\e. (FST e) * #1 + (SND e) * z) (Fp CROSS Fp) R
Proof
  rpt (stripDup[FiniteField_def]) >>
  drule_then assume_tac prime_field_element_element >>
  rw[INJ_DEF, pairTheory.EXISTS_PROD] >>
  ‘FST e IN R /\ SND e IN R ∧ FST e' IN R /\ SND e' IN R’ by rw[] >>
  ‘SND e * z IN R /\ SND e' * z IN R’ by rw[] >>
  ‘(FST e + SND e * z = FST e' + SND e' * z) <=>
   (FST e = FST e' + SND e' * z - SND e * z)’ by metis_tac[field_add_sub] >>
  ‘_ = (FST e = FST e' + (SND e' * z - SND e * z))’ by rw_tac std_ss[field_add_assoc, field_sub_def, field_neg_element] >>
  ‘_ = (FST e = (SND e' * z - SND e * z) + FST e')’ by rw_tac std_ss[field_add_comm, field_sub_element] >>
  ‘_ = (FST e - FST e' = (SND e' * z - SND e * z) + FST e' - FST e')’ by metis_tac[] >>
  ‘_ = (FST e - FST e' = SND e' * z - SND e * z)’ by rw_tac std_ss[field_add_sub, field_sub_element] >>
  ‘_ = (FST e - FST e' = (SND e' - SND e) * z)’ by rw_tac std_ss[field_mult_lsub] >>
  Cases_on ‘SND e = SND e'’ >| [
    ‘SND e' - SND e = #0’ by rw[] >>
    ‘FST e - FST e' = #0’ by metis_tac[field_mult_lzero] >>
    ‘FST e = FST e'’ by metis_tac[field_sub_eq_zero] >>
    rw[pairTheory.PAIR_FST_SND_EQ],
    ‘Field (PF r)’ by rw[prime_field_field] >>
    ‘((PF r).sum.op = $+) /\ ((PF r).sum.id = #0) /\ ((PF r).prod.op = $* ) /\ ((PF r).prod.id = #1)’ by rw[PF_property] >>
    ‘!x. x IN Fp ==> ((PF r).sum.inv x = -x)’
      by (rpt strip_tac >>
          ‘x + (PF r).sum.inv x = (PF r).sum.op x ((PF r).sum.inv x)’
            by metis_tac[] >>
          ‘_ = #0’ by rw[] >>
          ‘x + -x = #0’ by rw[] >>
          ‘x + -x = x + (PF r).sum.inv x’ by rw_tac std_ss[] >>
          ‘!z. z IN Fp ==> z IN R’ by rw[prime_field_element_element] >>
          ‘(PF r).sum.inv x IN Fp’ by rw[] >>
          ‘x IN R /\ -x IN R’ by rw[] >>
          metis_tac[field_add_lcancel]) >>
    ‘SND e' - SND e IN Fp’ by metis_tac[field_sub_def, field_add_element, field_neg_element] >>
    ‘SND e' - SND e <> #0’ by metis_tac[field_sub_eq_zero] >>
    ‘SND e' - SND e IN ring_nonzero (PF r)’ by metis_tac[field_nonzero_eq] >>
    ‘(Invertibles (PF r).prod).inv (SND e' - SND e) IN Fp’ by metis_tac[field_inv_element] >>
    qabbrev_tac ‘v = (Invertibles (PF r).prod).inv (SND e' - SND e)’ >>
    ‘v IN R /\ (SND e' - SND e) IN R’ by rw[prime_field_element_element] >>
    ‘v * (FST e - FST e') = v * ((SND e' - SND e) * z)’ by metis_tac[] >>
    ‘_ = v * (SND e' - SND e) * z’ by rw_tac std_ss[field_mult_assoc] >>
    ‘_ = z’ by metis_tac[field_mult_linv, field_mult_lone] >>
    ‘FST e - FST e' IN Fp’ by metis_tac[field_sub_def, field_add_element, field_neg_element] >>
    metis_tac[field_mult_element]
  ]
QED

(* Better Proof of same theorem. *)
(* Theorem: If z NOTIN Fp, then Fp x Fp maps to distinct elements in R via (\(i, j). i * #1 + j * z). *)
(* Proof:
   By INJ_DEF and field_mult_rone, this is to show:
   (1) FST x IN Fp /\ SND x IN Fp ==> FST x + SND x * z IN R
       Since FST x IN R and SND x IN R        by prime_field_element_element
       Hence FST x * #1 + SND x * z IN R      by field_mult_element, field_add_element
   (2) FST x + SND x * z = FST y + SND y * z ==> x = y
       Note FST x IN R /\ SND x IN R          by prime_field_element_element
        and FST y IN R /\ SND y IN R          by prime_field_element_element
            FST x + SND x * z = FST y + SND y * z
        <=> FST x - FST y = SND y * z - SND x * z   by field_add_sub_identity
        <=> FST x - FST y = (SND y - SND x) * z     by field_mult_lsub
       If SND x <> SND y, |/ (SND y - SND x) exists,
       and   z = (FST x - FST y) / (SND y - SND x) IN Fp, a contradiction.
       Therefore  SND x = SND y,
       and        FST x - FST y = #0 * z = #0
              ==> FST x = FST y,
       Hence x = y   by PAIR_FST_SND_EQ.
*)
Theorem finite_field_prime_sq_alt:
  !r:'a field.
    FiniteField r ==>
    !z. z IN R /\ z NOTIN Fp ==> INJ (λ(i, j). i * #1 + j * z) (Fp CROSS Fp) R
Proof
  rpt (stripDup[FiniteField_def]) >>
  drule_then assume_tac prime_field_element_element >>
  rw_tac std_ss[INJ_DEF, IN_CROSS, pairTheory.UNCURRY, field_mult_rone]
  >- rw[] >>
  ‘(FST x + SND x * z = FST y + SND y * z) <=>
    (FST x - FST y = SND y * z - SND x * z)’ by rw[GSYM field_add_sub_identity] >>
  ‘_ = (FST x - FST y = (SND y - SND x) * z)’ by rw_tac std_ss[field_mult_lsub] >>
  Cases_on ‘SND x = SND y’ >| [
    ‘SND x - SND y = #0’ by rw[] >>
    ‘FST x - FST y = #0’ by metis_tac[field_mult_lzero] >>
    ‘FST x = FST y’ by metis_tac[field_sub_eq_zero] >>
    rw[pairTheory.PAIR_FST_SND_EQ],
    ‘Field (PF r)’ by rw[prime_field_field] >>
    qabbrev_tac ‘u = SND y - SND x’ >>
    ‘u <> #0’ by metis_tac[field_sub_eq_zero] >>
    ‘!x. x IN Fp ==> ((PF r).sum.inv x = -x)’ by rw[prime_field_neg] >>
    ‘u IN Fp’ by metis_tac[field_sub_def, field_add_element, field_neg_element, PF_property] >>
    ‘u IN ring_nonzero (PF r)’ by metis_tac[field_nonzero_eq, PF_property] >>
    ‘(Invertibles (PF r).prod).inv u IN Fp’ by metis_tac[field_inv_element] >>
    qabbrev_tac ‘v = (Invertibles (PF r).prod).inv u’ >>
    ‘v IN R /\ u IN R’ by rw[] >>
    ‘v * (FST x - FST y) = v * (u * z)’ by metis_tac[] >>
    ‘_ = v * u * z’ by rw_tac std_ss[field_mult_assoc] >>
    ‘_ = z’ by metis_tac[field_mult_linv, field_mult_lone, PF_property] >>
    ‘FST x - FST y IN Fp’ by metis_tac[field_sub_def, field_add_element, field_neg_element, PF_property] >>
    ‘v * (FST x - FST y) IN Fp’ by metis_tac[field_mult_element, PF_property] >>
    metis_tac[]
  ]
QED

(* Theorem: prime n ==> FieldIso I (PF (ZN n)) (ZN n) *)
(* Proof:
   By subfield_carrier_antisym, this is to show:
   (1) prime n ==> (ZN n).carrier SUBSET (PF (ZN n)).carrier
       Note n <> 1                               by NOT_PRIME_1
        ==> (ZN n).prod.id = 1                   by ZN_property, n <> 1
       Note (ZN n).carrier = count n             by ZN_eval
        and (PF (ZN n)).carrier
          = IMAGE ((ZN n).sum.exp 1) univ(:num)  by PF_property
       By SUBSET_DEF, this is to show:
          x IN (count n) ==> x IN IMAGE ((ZN n).sum.exp 1) univ(:num)
       or x < n ==> ?y. y = (ZN n).sum.exp 1 x   by IN_COUNT, IN_IMAGE
       or       ==> ?y. y = x MOD n              by ZN_num
       Put y = x, this is true                   by LESS_MOD
   (2) prime n ==> subfield (PF (ZN n)) (ZN n)
       Note Field (ZN n)                         by ZN_field, prime n
       Thus subfield (PF (ZN n)) (ZN n)          by prime_field_subfield
*)
val ZN_prime_field_iso_itself = store_thm(
  "ZN_prime_field_iso_itself",
  ``!n. prime n ==> FieldIso I (PF (ZN n)) (ZN n)``,
  rpt strip_tac >>
  (irule subfield_carrier_antisym >> rpt conj_tac) >| [
    `(ZN n).carrier = count n` by rw[ZN_eval] >>
    `(ZN n).prod.id = 1` by metis_tac[ZN_property, NOT_PRIME_1] >>
    `(PF (ZN n)).carrier = IMAGE ((ZN n).sum.exp 1) univ(:num)` by rw[PF_property] >>
    rw[ZN_num, SUBSET_DEF] >>
    metis_tac[LESS_MOD],
    `Field (ZN n)` by rw[ZN_field] >>
    rw[prime_field_subfield]
  ]);


(* ------------------------------------------------------------------------- *)
(* Prime Field as Scalar Ring                                                *)
(* ------------------------------------------------------------------------- *)

(* Easier to show first AbelianGroup, then Group *)

(* Theorem: Ring r /\ 0 < char r ==> AbelianGroup (PF r).sum *)
(* Proof:
   By definitions, this is to show:
   (1) ?x'''. ##x' + ##x'' = ##x''', true                    by ring_num_add
   (2) ##x' + ##x'' + ##x''' = ##x' + (##x'' + ##x'''), true by ring_num_add, ADD_ASSOC
   (3) ?x. #0 = ##x, true                                    by ring_num_0
   (4) #0 + ##x' = ##x', true                                by ring_add_lzero, ring_num_element
   (5) ?y. (?x. (y = ##x) /\ (y + ##x' = #0), true           by ring_num_negative
   (6) ##x' + ##x'' = ##x'' + ##x', true                     by ring_num_add, ADD_COMM
*)
val scalar_ring_sum_abelian_group = store_thm(
  "scalar_ring_sum_abelian_group",
  ``!r:'a ring. Ring r /\ 0 < char r ==> AbelianGroup (PF r).sum``,
  rpt strip_tac >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, PF_def, GSPECIFICATION, IN_IMAGE, IN_UNIV] >-
  metis_tac[ring_num_add] >-
  metis_tac[ring_num_add, ADD_ASSOC] >-
  metis_tac[ring_num_0] >-
  rw[] >-
  metis_tac[ring_num_negative] >>
  metis_tac[ring_num_add, ADD_COMM]);

(* Theorem: Ring r /\ 0 < char r ==> Group (PF r).sum *)
(* Proof: by scalar_ring_sum_abelian_group, AbelianGroup_def. *)
val scalar_ring_sum_group = store_thm(
  "scalar_ring_sum_group",
  ``!r:'a ring. Ring r /\ 0 < char r ==> Group (PF r).sum``,
  metis_tac[scalar_ring_sum_abelian_group, AbelianGroup_def]);

(* Easier to show first AbelianMonoid, then Monoid *)

(* Theorem: Ring r ==> AbelianMonoid (PF r).prod *)
(* Proof:
   By definitions, this is to show:
   (1) ?x'''. ##x' * ##x'' = ##x''', true                    by ring_num_mult
   (2) ##x' * ##x'' * ##x''' = ##x' * (##x'' * ##x'''), true by ring_num_mult, MULT_ASSOC
   (3) ?x. #1 = ##x, true                                    by ring_num_1
   (4) #1 * ##x' = ##x', true                                by ring_mult_lone, ring_num_element
   (5) ##x' * #1 = ##x', true                                by ring_mult_rone, ring_num_element
   (6) ##x' * ##x'' = ##x'' * ##x', true                     by ring_num_mult, MULT_COMM
*)
val scalar_ring_prod_abelian_monoid = store_thm(
  "scalar_ring_prod_abelian_monoid",
  ``!r:'a ring. Ring r ==> AbelianMonoid (PF r).prod``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, PF_def, GSPECIFICATION, IN_IMAGE, IN_UNIV] >-
  metis_tac[ring_num_mult] >-
  metis_tac[ring_num_mult, MULT_ASSOC] >-
  metis_tac[ring_num_1] >-
  rw[] >-
  rw[] >>
  metis_tac[ring_num_mult, MULT_COMM]);

(* Theorem: Ring r ==> Monoid (PF r).prod *)
(* Proof: by scalar_ring_prod_abelian_monoid, AbelianMonoid_def. *)
val scalar_ring_prod_monoid = store_thm(
  "scalar_ring_prod_monoid",
  ``!r:'a ring. Ring r ==> Monoid (PF r).prod``,
  metis_tac[scalar_ring_prod_abelian_monoid, AbelianMonoid_def]);

(* Theorem: Ring r /\ 0 < char r ==> Ring (PF r) *)
(* Proof:
   By Ring_def, this is to show:
   (1) AbelianGroup (PF r).sum, true          by scalar_ring_sum_abelian_group
   (2) AbelianMonoid (PF r).prod, true        by scalar_ring_prod_abelian_monoid
   (3) (PF r).sum.carrier = Fp, true          by PF_property
   (4) (PF r).prod.carrier = Fp, true         by PF_property
   (5) x IN Fp /\ y IN Fp /\ z IN Fp ==> x * (y + z) = x * y + x * z, or
       ##x' * (##x'' + ##x''') = ##x' * ##x'' + ##x' * ##x''', true bu PF_property
*)
val scalar_ring_is_ring = store_thm(
  "scalar_ring_is_ring",
  ``!r:'a ring. Ring r /\ 0 < char r ==> Ring (PF r)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, PF_property, IN_IMAGE, IN_UNIV] >-
  rw[scalar_ring_sum_abelian_group] >-
  rw[scalar_ring_prod_abelian_monoid] >>
  metis_tac[ring_num_mult_radd, ring_num_element]);

(* Theorem: FiniteRing r ==> Ring (PF r) *)
(* Proof: by scalar_ring_is_ring, finite_ring_char_pos *)
val scalar_ring_ring = store_thm(
  "scalar_ring_ring",
  ``!r:'a ring. FiniteRing r ==> Ring (PF r)``,
  rw[scalar_ring_is_ring, finite_ring_char_pos, FiniteRing_def]);

(*
> ring_num_eq |> ISPEC ``(PF r)``;
val it = |- Ring (PF r) ==>
   !n m. n < char (PF r) /\ m < char (PF r) ==>
     (((PF r).sum.exp (PF r).prod.id n = (PF r).sum.exp (PF r).prod.id m) <=> (n = m)): thm

> ring_num_eq |> ISPEC ``PF (PolyRing r)``;
val it = |- Ring (PF (PolyRing r)) ==>
   !n m. n < char (PF (PolyRing r)) /\ m < char (PF (PolyRing r)) ==>
     (((PF (PolyRing r)).sum.exp (PF (PolyRing r)).prod.id n =
       (PF (PolyRing r)).sum.exp (PF (PolyRing r)).prod.id m) <=> (n = m)): thm
*)

(* Theorem: Ring r /\ 0 < char r ==> RingIso (ZN (char r)) (PF r) *)
(* Proof:
   Since 0 < char r, Ring (ZN (char r))    by ZN_ring
   By RingIso_def, this is to show:
   (1) RingHomo (\n. ##n) (ZN (char r)) (PF r)
       By definitions, this is to show:
       (1) char r = 1 ==> #0 = ##n + ##n'
           But char r = 1 ==> #1 = #0      by ring_char_eq_1
           and #1 = #0 ==> R = {#0}        by ring_one_eq_zero
           Hence true by #0 = #0 + #0      by ring_add_zero_zero
       (2) char r = 1 ==> #0 = ##n * ##n'
           But char r = 1 ==> #1 = #0      by ring_char_eq_1
           and #1 = #0 ==> R = {#0}        by ring_one_eq_zero
           Hence true by #0 = #0 * #0      by ring_mult_zero_zero
       (3) char r = 1 ==> #0 = #1
           True by ring_char_eq_1.
       (4) ##((n + n') MOD char r) = ##n + ##n'
             ##((n + n') MOD char r)
           = ##(n + n')                    by ring_num_mod
           = ##n + ##n'                    by ring_num_add
       (5) ##((n * n') MOD char r) = ##n * ##n'
             ##((n * n') MOD char r)
           = ##(n * n')                    by ring_num_mod
           = ##n * ##n'                    by ring_num_mult
   (2) BIJ (\n. ##n) (ZN (char r)).carrier Fp
       By definitions, this is to show:
       (1) n < char r /\ n' < char r ==> ##n = ##n' ==> n = n'
           True by ring_num_eq.
       (2) ?n. n < char r /\ (##n = ##x')
           Let n = x' MOD (char r)
           Then n < char r        by MOD_LESS
           and ##n = ##x'         by ring_num_mod
*)

Theorem scalar_ring_iso_ZN_char:
  !r:'a ring. Ring r /\ 0 < char r ==> RingIso (\n. ##n) (ZN (char r)) (PF r)
Proof
  rpt strip_tac >>
  `Ring (ZN (char r))` by rw[ZN_ring] >>
  rw_tac std_ss[RingIso_def] >| [
    rw[RingHomo_def, GroupHomo_def, MonoidHomo_def, ZN_property, PF_property]
    >- metis_tac[ring_char_eq_1, ring_one_eq_zero, IN_SING, ring_num_element,
                 ring_mult_zero_zero]
    >- metis_tac[ring_num_add, ring_num_mod] >>
    metis_tac[ring_num_mult, ring_num_mod],
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF, ZN_property, PF_property] >-
    metis_tac[ring_num_eq] >>
    metis_tac[MOD_LESS, ring_num_mod]
  ]
QED

(* Theorem: Ring r /\ 0 < char r ==> char (PF r) = char r *)
(* Proof:
   Since 0 < char r, Ring (ZN (char r))          by ZN_ring
    Also Ring (PF r)                             by scalar_ring_is_ring
     ==> RingIso (\n. ##n) (ZN (char r)) (PF r)  by scalar_ring_iso_ZN_char
    Thus char (PF r)
       = char (ZN (char r))                      by ring_iso_char_eq
       = char r                                  by ZN_char
*)
val scalar_ring_char = store_thm(
  "scalar_ring_char",
  ``!r:'a ring. Ring r /\ 0 < char r ==> (char (PF r) = char r)``,
  rpt strip_tac >>
  `Ring (ZN (char r))` by rw[ZN_ring] >>
  `Ring (PF r)` by rw[scalar_ring_is_ring] >>
  `RingIso (\n. ##n) (ZN (char r)) (PF r)` by rw[scalar_ring_iso_ZN_char] >>
  metis_tac[ring_iso_char_eq, ZN_char]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
