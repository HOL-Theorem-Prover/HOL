(* ------------------------------------------------------------------------- *)
(* Finite Field: Advanced Theory                                             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffAdvanced";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory numberTheory
     combinatoricsTheory primeTheory;

(* val _ = load "ffBasicTheory"; *)
open ffBasicTheory;

(* val _ = load "FiniteVSpaceTheory"; *)
open VectorSpaceTheory FiniteVSpaceTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open groupInstancesTheory ringInstancesTheory;
open fieldInstancesTheory; (* for GF_finite_field, in finite_field_subfield_card *)

(* Get polynomial theory of Ring *)
(* (* val _ = load "polyFieldModuloTheory"; -- in ffBasic *) *)
(* (* val _ = load "polyFieldTheory"; *) *)
open polynomialTheory polyWeakTheory polyRingTheory;
open polyMonicTheory polyEvalTheory;
open polyDividesTheory;
open polyRootTheory;
open polyFieldTheory polyDivisionTheory polyFieldDivisionTheory;
open polyModuloRingTheory;
open polyFieldModuloTheory;
open polyIrreducibleTheory;

open groupMapTheory ringMapTheory fieldMapTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;
open subgroupTheory;
open quotientGroupTheory;

open groupCyclicTheory;
open groupOrderTheory;
open fieldOrderTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Field Advanced Documentation                                       *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   r <:> s       = dim s (r.sum) $*
   fdim r        = r <:> (PF r)
   FPrimitives r = {z | z IN R+ /\ (forder z = CARD R+)}
   primitive r   = field_primitive r
   idx x         = field_index r x
   r >= s        = field_extend r s
*)
(* Definitions and Theorems (# are exported):

   Finite Field is Vector Space over Subfield:
   field_is_vspace_over_subfield           |- !r. Field r ==> !s. s <= r ==> VSpace s r.sum $*
   subfield_is_vspace_scalar               |- !r s. s <<= r ==> VSpace s r.sum $*
   finite_subfield_is_finite_vspace_scalar |- !r. FiniteField r ==> !s. s <<= r ==> FiniteVSpace s r.sum $*
   finite_subfield_card       |- !r. FiniteField r ==> !s. s <<= r ==> (CARD R = CARD B ** (r <:> s))
   finite_subfield_dim_pos    |- !r. FiniteField r ==> !s. s <<= r ==> 0 < (r <:> s)
   finite_subfield_card_eqn   |- !r. FiniteField r ==> !s. s <<= r ==>
                                     (CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s)
   finite_subfield_card_pos   |- !r. FiniteField r ==> !s. s <<= r ==> 0 < CARD B
   finite_subfield_card_gt_1  |- !r. FiniteField r ==> !s. s <<= r ==> 1 < CARD B
   finite_field_over_subfield_dim_pos      |- !r a. FiniteField r /\ s <<= r ==> 0 < (r <:> s)
   finite_field_over_subfield_dim          |- !r s. FiniteField r /\ s <<= r ==>
                                              !n. (CARD R = CARD B ** n) <=> (n = (r <:> s))

   Finite Field is Vector Space over Prime Field:
   finite_field_is_vspace        |- !r. FiniteField r ==> VSpace (PF r) r.sum $*
   finite_field_is_finite_vspace |- !r. FiniteField r ==> FiniteVSpace (PF r) r.sum $*
   finite_field_dim_pos          |- !r. FiniteField r ==> 0 < fdim r
   finite_field_card_eqn         |- !r. FiniteField r ==> (CARD R = char r ** fdim r) /\ 0 < fdim r
   finite_field_card_alt         |- !r. FiniteField r ==> (CARD R = char r ** fdim r)
   finite_field_dim_eq           |- !r. FiniteField r ==> !n. (CARD R = char r ** n) <=> (n = fdim r)
   finite_field_card             |- !r. FiniteField r ==> ?d. 0 < d /\ (CARD R = char r ** d)
   finite_field_card_prime_power |- !r. FiniteField r ==> ?p. prime p /\ perfect_power (CARD R) p
   finite_field_card_eq_char_eq  |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                                           (char r = char r_)
   finite_field_card_eq_dim_eq   |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                                           (fdim r = fdim r_)
   finite_field_card_eq_property |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                                           (char r = char r_) /\ (fdim r = fdim r_)
   finite_field_mult_carrier_card_alt
                                 |- !r. FiniteField r ==> (CARD R+ = char r ** fdim r - 1)
   finite_field_subfield_dim_divides
                                 |- !r s. FiniteField r /\ s <<= r ==> fdim s divides fdim r

   Finite Field Properties by Cardinality:
   finite_field_order_coprime_char_exp
                                 |- !r. FiniteField r ==> !x. x IN R+ ==> !n. coprime (forder x) (char r ** n)
   finite_field_card_mod_order   |- !r. FiniteField r ==> !x. x IN R+ /\ x <> #1 ==> (CARD R MOD forder x = 1)
   finite_field_one_condition    |- !r. FiniteField r ==> !x. x IN R ==> !n. (x ** char r ** n = #1) <=> (x = #1)
   finite_field_element_eq_condition   |- !r. FiniteField r ==> !x y. x IN R /\ y IN R ==>
                                          !n. (x ** char r ** n = y ** char r ** n) <=> (x = y)
   finite_field_char_2           |- !r. FiniteField r /\ (char r = 2) ==> EVEN (CARD R)
   finite_field_char_even_has_odd_order
                                 |- !r. FiniteField r ==> EVEN (char r) ==> !x. x IN R+ ==> ODD (forder x)
   finite_field_order_eq_2       |- !r. FiniteField r ==> !x. x IN R /\ (forder x = 2) ==> (x = -#1)

   Subfield is Vector Space over Prime Field:
   finite_field_subfield_is_vspace     |- !r. FiniteField r ==> !s. s <<= r ==> VSpace (PF r) s.sum $*
   finite_field_subfield_card          |- !r. FiniteField r ==> !s. s <<= r ==> ?d. 0 < d /\ (CARD B = char r ** d)
   finite_field_card_subfield          |- !r. FiniteField r ==> !s. s <<= r ==> ?d. 0 < d /\ (CARD R = CARD B ** d)
   finite_field_subfield_card_property |- !r. FiniteField r ==> !s. s <<= r ==> ?n m. 0 < n /\ 0 < m /\
                                              (CARD R = char r ** n) /\ (CARD B = char r ** m) /\ m divides n
   finite_field_subfield_card_divides  |- !r s. FiniteField r /\ s <<= r ==> CARD B divides CARD R
   finite_field_subfield_nonzero_card_divides
                                       |- !r s. FiniteField r /\ s <<= r ==> CARD B* divides CARD F*
   finite_field_order_coprime          |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                          !n. coprime (forder x) (CARD B ** n)
   finite_field_order_property         |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                                0 < forder x /\ coprime (forder x) (CARD B)
   subfield_card_order_divides_dim     |- !r s. FiniteField r /\ s <<= r ==>
                                          !x. x IN R+ ==> ordz (forder x) (CARD B) divides (r <:> s)
   subfield_card_coprime_condition     |- !r s. FiniteField r /\ s <<= r ==>
                                          !n. n divides CARD R+ ==> coprime n (CARD B)
   subfield_card_coprime_iff           |- !r s. FiniteField r /\ s <<= r ==>
                                          !n. 0 < n /\ (ordz n (CARD B) = r <:> s) ==>
                                             (coprime n (CARD B) <=> n divides CARD R+)

   Multiplicative Group of Field is Cyclic:
   finite_field_mult_group_has_gen   |- !r. FiniteField r ==> ?z. z IN R+ /\ (forder z = CARD R+)
   finite_field_mult_group_cyclic    |- !r. FiniteField r ==> cyclic f*
   finite_field_orders_nonempty_iff  |- !r. FiniteField r ==> !n. n divides CARD R+ <=> orders f* n <> {}
   finite_field_eq_order_partition   |- !r. FiniteField r ==>
                      (partition (\x y. forder x = forder y) R+ = {orders f* n | n IN divisors (CARD R+)})

   Finite Field Primitive:
   field_primitive_def       |- !r. primitive r = CHOICE (FPrimitives r)
   field_primitives_element  |- !r z. z IN FPrimitives r <=> z IN R+ /\ (forder z = CARD R+)
   field_primitives_nonempty |- !r. FiniteField r ==> FPrimitives r <> {}
   field_primitives_has_primitive  |- !r. FiniteField r ==> primitive r IN FPrimitives r
   field_primitive_property  |- !r. FiniteField r ==> primitive r IN R+ /\ (forder (primitive r) = CARD R+)
#  field_primitive_element   |- !r. FiniteField r ==> primitive r IN R
#  field_primitive_nonzero   |- !r. FiniteField r ==> primitive r IN R+
   field_primitive_order     |- !r. FiniteField r ==> (forder (primitive r) = CARD R+)
   field_primitives_order_eq |- !r s. FiniteField r /\ FiniteField s /\ (CARD R = CARD s.carrier) ==>
                                (forder (primitive r) = order (s.prod excluding s.sum.id) (primitive s))
   field_primitives_element_property
                             |- !r. FiniteField r ==> !x. x IN R+ ==>
                                !z. z IN FPrimitives r ==> ?n. n < CARD R+ /\ (x = z ** n)
   finite_field_neg_one_alt  |- !r. FiniteField r ==> !z. z IN FPrimitives r ==>
                                    (-#1 = if char r = 2 then #1 else z ** (CARD R+ DIV 2))
   finite_field_neg_one      |- !r. FiniteField r ==>
                                    (-#1 = if char r = 2 then #1 else primitive r ** (CARD R+ DIV 2))

   Finite Field Nonzero Element Index:
   field_index_exists     |- !r. FiniteField r ==> !x. x IN R+ ==> ?n. x = primitive r ** n
   field_index_def        |- !r x. FiniteField r /\ x IN R+ ==> (x = primitive r ** idx x)
   field_index_alt        |- !r. FiniteField r ==> !x. x IN R+ ==>
                             !n. (idx x = n) <=> n < CARD R+ /\ (x = primitive r ** n)
   field_index_one        |- !r. FiniteField r ==> (idx #1 = 0)
   field_index_eq_0       |- !r. FiniteField r ==> !x. x IN R+ ==> ((idx x = 0) <=> (x = #1))
   field_index_primitive  |- !r. FiniteField r ==> (idx (primitive r) = if CARD R+ = 1 then 0 else 1)
   field_index_neg_one    |- !r. FiniteField r ==> (idx (-#1) = if char r = 2 then 0 else CARD R+ DIV 2)
   field_index_mult       |- !r. FiniteField r ==> !x y. x IN R+ /\ y IN R+ ==>
                                                   (idx (x * y) = (idx x + idx y) MOD CARD R+)
   field_index_neg        |- !r. FiniteField r ==> !x. x IN R+ ==>
                             (idx (-x) = if char r = 2 then idx x else (idx x + CARD R+ DIV 2) MOD CARD R+)

   More properties about Constant Polynomial Field:
   poly_mod_const_subring_card  |- !r. FiniteRing r ==> !z. pmonic z ==> (CARD RCz = CARD R)
   poly_mod_const_subfield_card |- !r. FiniteField r ==> !z. pmonic z ==> (CARD RCz = CARD R)
   poly_mod_const_subfield_dim  |- !r. FiniteField r ==> !z. monic z /\ ipoly z ==>
                                       (PolyModRing r z <:> PolyModConst r z) = deg z

   Field Extension:
   field_extend_def    |- !r s. r >= s <=> ?f. subfield (ring_homo_image f r s) s
   field_homo_extend   |- !r s f. Field r /\ Field s /\ FieldHomo f r s ==> r >= s
   field_extend_refl   |- !r. Field r ==> r >= r

*)

(* ------------------------------------------------------------------------- *)
(* Finite Field is Vector Space over Subfield.                               *)
(* ------------------------------------------------------------------------- *)

(* Overload on dimension of Field r over subfield s *)
val _ = overload_on("<:>", ``\(r s):'a ring. dim s (r.sum) $*``);

(* Make dimension ":" infix *)
val _ = set_fixity "<:>" (Infix(NONASSOC, 450)); (* same as relation *)

(* Overload dimension of a finite field *)
val _ = overload_on("fdim", ``\r:'a field. r <:> (PF r)``);

(* Theorem: Field is vector space over subfield:
            Field r ==> !s. s <<= r ==> VSpace s r.sum r.prod.op *)
(* Proof:
   By VSpace_def, this is to show:
   (1) Field r ==> AbelianGroup r.sum
       True by field_def_alt.
   (2) a IN B /\ v IN R ==> a * v IN R
           a IN R          by subfield_property_alt
       and s.prod.op = $*  by subfield_property_alt
       Hence true          by field_mult_element
   (3) a IN B /\ b IN B /\ v IN R ==> a * (b * v) = s.prod.op a b * v
           a, b IN R       by subfield_property_alt
       and s.prod.op = $*  by subfield_property_alt
       Hence true          by field_mult_assoc
   (4) v IN R ==> s.prod.id * v = v
          s.prod.id = #1   by subfield_property_alt
       Hence true          by field_mult_lone
   (5) a IN B /\ u IN R /\ v IN R ==> a * (u + v) = a * u + a * v
           a IN R          by subfield_property_alt
       Hence true          by field_mult_radd
   (6) a IN B /\ b IN B /\ v IN R ==> s.sum.op a b * v = a * v + b * v
           a, b IN R       by subfield_property_alt
       and s.sum.op = $+   by subfield_property_alt
       Hence true          by field_mult_ladd
*)
Theorem field_is_vspace_over_subfield:
  !r:'a field. Field r ==> !s. s <<= r ==> VSpace s r.sum r.prod.op
Proof
  rpt strip_tac >>
  ‘!z. z IN B ==> z IN R’ by metis_tac[subfield_property_alt] >>
  rw[VSpace_def]
  >- (‘s.prod.op a b = a * b’ by metis_tac[subfield_property_alt] >>
      rw[field_mult_assoc])
  >- (‘s.prod.id = #1’ by metis_tac[subfield_property_alt] >>
      rw[]) >>
  ‘s.sum.op a b = a + b’ by metis_tac[subfield_property_alt] >>
  rw[field_mult_ladd]
QED

(* Theorem: s <<= r ==> VSpace s r.sum $* *)
(* Proof: by field_is_vspace_over_subfield *)
val subfield_is_vspace_scalar = store_thm(
  "subfield_is_vspace_scalar",
  ``!(r s):'a field. s <<= r ==> VSpace s r.sum $*``,
  rw[field_is_vspace_over_subfield]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> FiniteVSpace s r.sum $* *)
(* Proof:
   Since FiniteField r ==> Field r /\ FINITE R        by FiniteField_def
     and s <<= r ==> VSpace s r.sum $*                by subfield_is_vspace_scalar
    also FiniteField r /\ subfield s r ==> FINITE B   by subfield_carrier_finite
   Hence FiniteVSpace s r.sum $*                      by FiniteVSpace_def, field_carriers
*)
val finite_subfield_is_finite_vspace_scalar = store_thm(
  "finite_subfield_is_finite_vspace_scalar",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> FiniteVSpace s r.sum $*``,
  metis_tac[FiniteField_def, FiniteVSpace_def, subfield_is_vspace_scalar, subfield_carrier_finite, field_carriers]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> (CARD R = CARD B ** (r <:> s)) *)
(* Proof:
   FiniteField r ==> FiniteVSpace s r.sum $*   by finite_subfield_is_finite_vspace_scalar
   Hence  CARD R
        = CARD (r.sum.carrier)          by field_carriers
        = (CARD B) ** (r <:> s)         by finite_vspace_card
*)
val finite_subfield_card = store_thm(
  "finite_subfield_card",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> (CARD R = CARD B ** (r <:> s))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteVSpace s r.sum $*` by rw[finite_subfield_is_finite_vspace_scalar] >>
  rw[GSYM finite_vspace_card]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> 0 < (r <:> s) *)
(* Proof:
   Note CARD R = (CARD B) ** (r <:> s)  by finite_subfield_card
    and 1 < CARD R                      by finite_field_card_gt_1
     ==> 0 < (r <:> s)                  by ONE_LT_EXP
*)
val finite_subfield_dim_pos = store_thm(
  "finite_subfield_dim_pos",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> 0 < (r <:> s)``,
  rpt strip_tac >>
  `CARD R = CARD B ** (r <:> s)` by rw[finite_subfield_card] >>
  `1 < CARD R` by rw[finite_field_card_gt_1] >>
  metis_tac[ONE_LT_EXP]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> (CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s) *)
(* Proof: by finite_subfield_card, finite_subfield_dim_pos *)
val finite_subfield_card_eqn = store_thm(
  "finite_subfield_card_eqn",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> (CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s)``,
  rw_tac std_ss[finite_subfield_card, finite_subfield_dim_pos]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> 0 < CARD B *)
(* Proof:
   Since FiniteField s       by subfield_finite_field
      so 0 < CARD B          by finite_field_card_pos
*)
val finite_subfield_card_pos = store_thm(
  "finite_subfield_card_pos",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> 0 < CARD B``,
  metis_tac[subfield_finite_field, finite_field_card_pos]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> 1 < CARD B *)
(* Proof:
   Since FiniteField s       by subfield_finite_field
      so 1 < CARD B          by finite_field_card_gt_1
*)
val finite_subfield_card_gt_1 = store_thm(
  "finite_subfield_card_gt_1",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> 1 < CARD B``,
  metis_tac[subfield_finite_field, finite_field_card_gt_1]);

(* Theorem: FiniteField r /\ s <<= r ==> 0 < (r <:> s) *)
(* Proof:
   By contradiction, assume (r <:> s) = 0.
   Since FiniteVSpace s r.sum $*         by finite_subfield_is_finite_vspace_scalar
      so r.sum.carrier = {r.sum.id}      by finite_vspace_dim_eq_0
      or             R = {#0}            by field_carriers
      giving        #1 = #0              by field_is_ring, ring_one_eq_zero
   This contradicts #1 <> #0             by field_one_ne_zero
*)
val finite_field_over_subfield_dim_pos = store_thm(
  "finite_field_over_subfield_dim_pos",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> 0 < (r <:> s)``,
  rpt (stripDup[FiniteField_def]) >>
  spose_not_then strip_assume_tac >>
  `(r <:> s) = 0` by decide_tac >>
  `FiniteVSpace s r.sum $*` by rw[finite_subfield_is_finite_vspace_scalar] >>
  `R = {#0}` by metis_tac[finite_vspace_dim_eq_0, field_carriers] >>
  `#1 = #0` by rw[ring_one_eq_zero] >>
  metis_tac[field_one_ne_zero]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. (CARD R = CARD B ** n) <=> (n = (r <:> s)) *)
(* Proof:
   Let d = (r <:> s).
   Since CARD R = (CARD B) ** d        by finite_subfield_card_eqn
     and 1 < CARD B                    by finite_subfield_card_gt_1
    Thus CARD B ** n = (CARD B) ** d
     <=>           n = d               by EXP_BASE_INJECTIVE, 1 < CARD B
*)
val finite_field_over_subfield_dim = store_thm(
  "finite_field_over_subfield_dim",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. (CARD R = CARD B ** n) <=> (n = (r <:> s))``,
  metis_tac[finite_subfield_card_gt_1, finite_subfield_card_eqn, EXP_BASE_INJECTIVE]);

(* ------------------------------------------------------------------------- *)
(* Finite Field is Vector Space over Prime Field.                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Take Prime Field as scalars, Finite Field as vector, this forms a Vector Space. *)
(* Proof:
   By VSpace_def, this is to show:
   (1) Field (PF r), true by prime_field_field.
   (2) AbelianGroup r.sum, true by field_def_alt
   (3) a * (b * v) = (PF r).prod.op a b * v, true by PF_property, field_mult_assoc.
   (4) (PF r).prod.id * v = v, true by PF_property, field_mult_lone
   (5) (PF r).sum.op a b * v = a * v + b * v, true by PF_property, field_mult_ladd.
*)
Theorem finite_field_is_vspace:
  !r:'a field. FiniteField r ==> VSpace (PF r) r.sum r.prod.op
Proof
  rpt strip_tac >>
  ‘Field r /\ FINITE R’ by metis_tac[FiniteField_def] >>
  drule_then assume_tac prime_field_element_element >>
  rw[VSpace_def, prime_field_field, PF_property, field_mult_assoc]
QED

(* Theorem: FiniteVSpace (PF r) r.sum r.prod.op *)
(* Proof:
   This is to show:
   (1) FiniteField r ==> VSpace (PF r) r.sum r.prod.op
       True by finite_field_over_prime_field.
   (2) FiniteField r ==> FINITE Fp
       True by prime_field_finite_field.
   (3) FiniteField r ==> FINITE r.sum.carrier
       True by field_carriers, FiniteField_def.
*)
val finite_field_is_finite_vspace = store_thm(
  "finite_field_is_finite_vspace",
  ``!r:'a field. FiniteField r ==> FiniteVSpace (PF r) r.sum r.prod.op``,
  rw[FiniteVSpace_def] >| [
    rw[finite_field_is_vspace],
    metis_tac[prime_field_finite_field, FiniteField_def],
    metis_tac[field_carriers, FiniteField_def]
  ]);

(* Theorem: FiniteField r ==> 0 < fdim r *)
(* Proof:
   By contradiction, assume fdim r = 0.
   Since FiniteVSpace (PF r) r.sum $*    by finite_field_is_finite_vspace
      so r.sum.carrier = {r.sum.id}      by finite_vspace_dim_eq_0
      or             R = {#0}            by field_carriers
      giving        #1 = #0              by field_is_ring, ring_one_eq_zero
   This contradicts #1 <> #0             by field_one_ne_zero
*)
val finite_field_dim_pos = store_thm(
  "finite_field_dim_pos",
  ``!r:'a field. FiniteField r ==> 0 < fdim r``,
  rpt (stripDup[FiniteField_def]) >>
  spose_not_then strip_assume_tac >>
  `fdim r = 0` by decide_tac >>
  `FiniteVSpace (PF r) r.sum $*` by rw[finite_field_is_finite_vspace] >>
  `R = {#0}` by metis_tac[finite_vspace_dim_eq_0, field_carriers] >>
  `#1 = #0` by rw[ring_one_eq_zero] >>
  metis_tac[field_one_ne_zero]);

(* Theorem: Finite Field has p ** d elements, of prime p and some nonzero d:
            FiniteField r ==> CARD R = (char r) ** (fdim r) /\ 0 < fdim r *)
(* Proof:
   FiniteField r ==> FiniteVSpace (PF r) r.sum $*    by finite_field_is_finite_vspace
   Hence  CARD R
        = CARD (r.sum.carrier)         by field_carriers
        = (CARD Fp) ** (fdim r)        by finite_vspace_card
        = (char r) ** (fdim r)         by prime_field_card
   Since 1 < CARD R                    by finite_field_card_gt_1
     ==> 0 < fdim r                    by ONE_LT_EXP
*)
val finite_field_card_eqn = store_thm(
  "finite_field_card_eqn",
  ``!r:'a field. FiniteField r ==> (CARD R = (char r) ** (fdim r)) /\ 0 < fdim r``,
  ntac 2 strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `FiniteVSpace (PF r) r.sum $*` by rw[finite_field_is_finite_vspace] >>
  metis_tac[field_carriers, finite_vspace_card, prime_field_card, finite_field_card_gt_1, ONE_LT_EXP]);

(* Theorem: FiniteField r ==> (CARD R = char r ** fdim r) *)
(* Proof: by finite_field_card_eqn *)
val finite_field_card_alt = store_thm(
  "finite_field_card_alt",
  ``!r:'a field. FiniteField r ==> (CARD R = char r ** fdim r)``,
  rw_tac std_ss[finite_field_card_eqn]);

(* Theorem: FiniteField r ==> !n. (CARD R = (char r) ** n) <=> (n = fdim r) *)
(* Proof:
   Note CARD R = (char r) ** (fdim r) /\
        0 < fdim r                           by finite_field_card_eqn
   also prime (char r)                       by finite_field_char
   Thus (char r) ** (fdim r) = (char r) ** n
    ==> n = fdim r                           by prime_powers_eq
*)
val finite_field_dim_eq = store_thm(
  "finite_field_dim_eq",
  ``!r:'a field. FiniteField r ==> !n. (CARD R = (char r) ** n) <=> (n = fdim r)``,
  metis_tac[finite_field_card_eqn, finite_field_char, prime_powers_eq]);

(* Theorem: Finite Field has p ** d elements, of prime p and some nonzero d:
            FiniteField r ==> ?d. CARD R = (char r) ** d *)
(* Proof: by finite_field_card_eqn *)
val finite_field_card = store_thm(
  "finite_field_card",
  ``!r:'a field. FiniteField r ==> ?d. 0 < d /\ (CARD R = (char r) ** d)``,
  metis_tac[finite_field_card_eqn]);

(* Theorem: FiniteField r ==> ?p. prime p /\ perfect_power (CARD R) p *)
(* Proof:
   FiniteField r ==> prime (char r)                   by finite_field_char
   FiniteField r ==> ?d. CARD R = (char r) ** d       by finite_field_card
                 ==> perfect_power (CARD R) (char r)  by perfect_power_def
   Hence take p = char r.
*)
val finite_field_card_prime_power = store_thm(
  "finite_field_card_prime_power",
  ``!r:'a field. FiniteField r ==> ?p. prime p /\ perfect_power (CARD R) p``,
  metis_tac[perfect_power_def, finite_field_card, finite_field_char]);

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (char r = char r_) *)
(* Proof:
    Note ?d. 0 < d /\ (CARD R = char r ** d)      by finite_field_card
     and ?e. 0 < e /\ (CARD R_ = char r_ ** e)    by finite_field_card
    Also prime (char r) /\ prime (char r_)        by finite_field_char
   Hence char r = char r_                         by prime_powers_eq
*)
val finite_field_card_eq_char_eq = store_thm(
  "finite_field_card_eq_char_eq",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (char r = char r_)``,
  metis_tac[finite_field_card, finite_field_char, prime_powers_eq]);

(* Note: char r = char r_ cannot imply CARD R = CARD R_:
   Both GF_2 and GF_4 have characteristic 2.
*)

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (fdim r = fdim r_) *)
(* Proof:
   Note (CARD R = (char r) ** (fdim r)) /\ 0 < (fdim r)      by finite_field_card_eqn
    and (CARD R_ = (char r_) ** (fdim r_)) /\ 0 < (fdim r_)  by finite_field_card_eqn
    Now char r = char r_                                     by finite_field_card_eq_char_eq
    and prime (char r) /\ prime (char r_)                    by finite_field_char
    ==> (fdim r = fdim r_)                                   by prime_powers_eq
*)
val finite_field_card_eq_dim_eq = store_thm(
  "finite_field_card_eq_dim_eq",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
     (fdim r = fdim r_)``,
  rpt strip_tac >>
  `(CARD R = (char r) ** (fdim r)) /\ 0 < (fdim r)` by rw[GSYM finite_field_card_eqn] >>
  `(CARD R_ = (char r_) ** (fdim r_)) /\ 0 < (fdim r_)` by rw[GSYM finite_field_card_eqn] >>
  `char r = char r_` by rw[finite_field_card_eq_char_eq] >>
  `prime (char r) /\ prime (char r_)` by rw[finite_field_char] >>
  metis_tac[prime_powers_eq]);

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
            (char r = char r_) /\ (fdim r = fdim r_) *)
(* Proof: by finite_field_card_eq_char_eq, finite_field_card_eq_dim_eq *)
val finite_field_card_eq_property = store_thm(
  "finite_field_card_eq_property",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
     (char r = char r_) /\ (fdim r = fdim r_)``,
  rw_tac std_ss[finite_field_card_eq_char_eq, finite_field_card_eq_dim_eq]);

(* Theorem: FiniteField r ==> (CARD R+ = char r ** fdim r - 1) *)
(* Proof:
     CARD R+
   = CARD F*                 by field_mult_carrier
   = CARD R - 1              by finite_field_mult_carrier_card
   = char r ** fdim r - 1    by finite_field_card_alt
*)
val finite_field_mult_carrier_card_alt = store_thm(
  "finite_field_mult_carrier_card_alt",
  ``!r:'a field. FiniteField r ==> (CARD R+ = char r ** fdim r - 1)``,
  metis_tac[finite_field_mult_carrier_card, finite_field_card_alt, field_mult_carrier, finite_field_is_field]);

(* Theorem: FiniteField r /\ s <<= r ==> (fdim s) divides (fdim r) *)
(* Proof:
   Let c = char r.
   Then prime c                                  by finite_field_char
    and char s = c                               by subfield_char
   Note FiniteField s                            by subfield_finite_field
     so (CARD R = c ** (fdim r)) /\ 0 < fdim r   by finite_field_card_eqn, vector space
    and CARD B = c ** (fdim s)                   by finite_field_card_eqn, vector space
   Also ?d. CARD R = CARD B ** d                 by finite_subfield_card_eqn, vector space
   Thus c ** (fdim r) = (c ** (fdim s)) ** d     by above
     or               = c ** (d * (fdim s))      by EXP_EXP_MULT, MULT_COMM
    ==>       fdim r = d * (fdim s)              by prime_powers_eq
     or (fdim s) divides (fdim r)                by divides_def
*)
val finite_field_subfield_dim_divides = store_thm(
  "finite_field_subfield_dim_divides",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> (fdim s) divides (fdim r)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  qabbrev_tac `c = char r` >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `char s = c` by rw[subfield_char, Abbr`c`] >>
  `(CARD R = c ** (fdim r)) /\ 0 < fdim r` by rw[finite_field_card_eqn, Abbr`c`] >>
  `CARD B = c ** (fdim s)` by rw[finite_field_card_eqn] >>
  `?d. CARD R = CARD B ** d` by metis_tac[finite_subfield_card_eqn] >>
  `c ** (fdim r) = c ** (d * (fdim s))` by metis_tac[EXP_EXP_MULT, MULT_COMM] >>
  metis_tac[prime_powers_eq, divides_def]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Properties by Cardinality                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x. x IN R+ ==> !n. coprime (forder x) ((char r) ** n) *)
(* Proof:
   Let ox = forder x, c = char r.
   If n = 0,
      Then c ** 0 = 1                   by EXP
        so coprime ox (c ** 0)          by GCD_1
   If n <> 0,
      Then 0 < n                        by NOT_ZERO_LT_ZERO
    Note coprime ox (CARD R)            by field_order_coprime_card
     Now ?d. 0 < d /\ CARD R = c ** d   by finite_field_card
      so coprime ox c                   by coprime_iff_coprime_exp
      or coprime ox c ** n              by coprime_iff_coprime_exp, 0 < n
*)
val finite_field_order_coprime_char_exp = store_thm(
  "finite_field_order_coprime_char_exp",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> !n. coprime (forder x) ((char r) ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `n = 0` >-
  rw[EXP, GCD_1] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `c = char r` >>
  `coprime ox (CARD R)` by rw[field_order_coprime_card, Abbr`ox`] >>
  `?d. 0 < d /\ (CARD R = c ** d)` by rw[finite_field_card, Abbr`c`] >>
  metis_tac[coprime_iff_coprime_exp]);

(* Theorem: FiniteField r ==> !x. x IN R+ /\ x <> #1 ==> ((CARD R) MOD (forder x) = 1) *)
(* Proof:
   Let ox = forder x.
   Note x IN R                  by field_nonzero_element
    and 0 < ox                  by field_order_property, x IN R+
    and ox <> 1                 by field_order_eq_1, x <> #1
     so 1 < ox                  by arithmetic

      x ** ((CARD R) MOD ox)
    = x ** (CARD R)             by finite_field_exp_mod_order
    = x                         by finite_field_fermat_thm
    = x ** 1                    by field_exp_1

   Note FiniteGroup f*          by finite_field_mult_finite_group
    and F* = R+                 by field_mult_carrier
    and f*.exp = $**            by field_nonzero_mult_property

    Now (CARD R) MOD ox < ox    by MOD_LESS
    and 1 < ox                  by above
    so (CARD R) MOD ox = 1      by group_exp_equal
*)
val finite_field_card_mod_order = store_thm(
  "finite_field_card_mod_order",
  ``!r:'a field. FiniteField r ==>
   !x. x IN R+ /\ x <> #1 ==> ((CARD R) MOD (forder x) = 1)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `ox = forder x` >>
  `x IN R` by rw[field_nonzero_element] >>
  `0 < ox` by rw[field_order_property, Abbr`ox`] >>
  `ox <> 1` by rw[field_order_eq_1, Abbr`ox`] >>
  `1 < ox` by decide_tac >>
  `(CARD R) MOD ox < ox` by rw[MOD_LESS] >>
  `x ** ((CARD R) MOD ox) = x ** (CARD R)` by rw[GSYM finite_field_exp_mod_order, Abbr`ox`] >>
  `_ = x` by rw[finite_field_fermat_thm] >>
  `_ = x ** 1` by rw[] >>
  `Group f*` by rw[field_mult_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  metis_tac[group_exp_equal, field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> !x. x IN R ==> !n. (x ** (char r) ** n = #1) <=> (x = #1) *)
(* Proof:
   If part: (x ** (char r) ** n = #1) ==> (x = #1)
   Let c = char r.
   Then 0 < c         by finite_field_char_pos
     so 0 < c ** n    by EXP_POS, 0 < c
    ==> x <> #0       by field_zero_exp
   Thus x IN R+
   Note ?d. 0 < d /\ (CARD R = c ** d)  by finite_field_card
    and CARD R+ = CARD R - 1            by finite_field_nonzero_carrier_card

   With x ** c ** n = #1
    ==> forder x divides c ** n         by field_order_divides_exp, x IN R+
   Also forder x divides CARD R+        by field_order_divides, x IN R+
     so forder x divides gcd (c ** n) (c ** d - 1)   by GCD_IS_GREATEST_COMMON_DIVISOR
    But gcd (c ** n) (c ** d - 1) = 1                by coprime_power_and_power_predecessor, 0 < c, 0 < d
     so forder x = 1                    by DIVIDES_ONE
     or x = #1                          by field_order_eq_1

   Only-if part: x = #1 ==> x ** (char r) ** n = #1
      True by field_one_exp
*)
val finite_field_one_condition = store_thm(
  "finite_field_one_condition",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> !n. (x ** (char r) ** n = #1) <=> (x = #1)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >>
  qabbrev_tac `c = char r` >>
  `0 < c` by rw[finite_field_char_pos, Abbr`c`] >>
  `0 < c ** n` by rw[EXP_POS] >>
  `c ** n <> 0` by decide_tac >>
  `x <> #0` by metis_tac[field_zero_exp, field_one_ne_zero] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `?d. 0 < d /\ (CARD R = c ** d)` by rw[finite_field_card, Abbr`c`] >>
  `CARD R+ = CARD R - 1` by rw[finite_field_nonzero_carrier_card] >>
  `forder x divides c ** n` by rw[GSYM field_order_divides_exp] >>
  `forder x divides CARD R+` by rw[field_order_divides] >>
  `gcd (c ** n) (c ** d - 1) = 1` by rw[coprime_power_and_power_predecessor] >>
  `forder x divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  `forder x = 1` by rw[GSYM DIVIDES_ONE] >>
  rw[GSYM field_order_eq_1]);

(* Theorem: FiniteField r ==>
            !x y. x IN R /\ y IN R ==> !n. (x ** (char r) ** n = y ** (char r) ** n) <=> (x = y) *)
(* Proof:
   If part: (x ** (char r) ** n = y ** (char r) ** n) ==> (x = y)
      Let m = (char r) ** n.

      Claim: x = #0 <=> y = #0
      Proof: Note 0 < char r             by finite_field_char_pos
               so 0 < m                  by EXP_POS, 0 < char r
             Thus x = #0 <=> y = #0      by field_exp_eq_zero

      If y = #0,
        Then y = #0                 by claim

      If y <> #0,
       Then x <> #0                 by claim
         so x IN R+ /\ y IN R+      by field_nonzero_eq
        ==> |/ y IN R               by field_nonzero_element
        Let z = x * |/ y.
       Then z IN R                  by field_mult_element
            z ** m
          = (x * |/ y) ** m         by z = x * |/ y
          = x ** m * (|/ y) ** m    by field_mult_exp
          = x ** m * |/ (y ** m)    by field_inv_exp, y IN R+
          = y ** m * |/ (y ** m)    by given x ** m = y ** m
          = #1                      by field_mult_rinv
      Hence z = #1                  by finite_field_one_condition, x IN R+, y IN R+
         or x = y                   by field_mult_rinv_eq_one

   Only-if part: (x = y) ==> (x ** (char r) ** n = y ** (char r) ** n)
      This is trivial.
*)
val finite_field_element_eq_condition = store_thm(
  "finite_field_element_eq_condition",
  ``!r:'a field. FiniteField r ==>
   !x y. x IN R /\ y IN R ==> !n. (x ** (char r) ** n = y ** (char r) ** n) <=> (x = y)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >>
  qabbrev_tac `m = (char r) ** n` >>
  `(x = #0) <=> (y = #0)` by metis_tac[finite_field_char_pos, EXP_POS, field_exp_eq_zero, NOT_ZERO_LT_ZERO] >>
  Cases_on `y = #0` >-
  rw[] >>
  `x <> #0` by rw[] >>
  `x IN R+ /\ y IN R+` by rw[field_nonzero_eq] >>
  `|/ y IN R` by rw[] >>
  qabbrev_tac `z = x * |/ y` >>
  `z IN R` by rw[Abbr`z`] >>
  `z ** m = #1` by rw[Abbr`z`] >>
  metis_tac[finite_field_one_condition, field_mult_rinv_eq_one]);

(* Theorem: FiniteField r /\ (char r = 2) ==> EVEN (CARD R) *)
(* Proof:
   Note FiniteField r
    ==> ?d. 0 < d /\ (CARD R = char r ** d)  by finite_field_card
     or     0 < d /\ (CARD R = 2 ** d)       by given, char r = 2
   Hence EVEN (CARD R)                       by EXP_2_EVEN
*)
val finite_field_char_2 = store_thm(
  "finite_field_char_2",
  ``!r:'a field. FiniteField r /\ (char r = 2) ==> EVEN (CARD R)``,
  metis_tac[finite_field_card, EXP_2_EVEN]);

(* Note: All finite fields with char r = 2 has -#1 = #1  by ring_char_2_neg_one,
   But R maybe just {#0, #1} for GF_2, or bigger: GF_4 = {#0, #1, alpha, alpha ** 2}
*)

(* Theorem: FiniteField r ==> EVEN (char r) ==> (!x. x IN R+ ==> ODD (forder x)) *)
(* Proof:
   Note FiniteField r
    ==> ?d. 0 < d /\ (CARD R = (char r) ** d)      by finite_field_card
     so EVEN (CARD R)                              by EVEN_EXP, EVEN (char r)
   Also CARD R = SUC (CARD R+)                     by finite_field_carrier_card
     so ODD (CARD R+)                              by EVEN_ODD_SUC
    Now (forder x) divides (CARD R+)               by field_order_divides
   Hence ODD (forder x)                            by DIVIDES_ODD
*)
val finite_field_char_even_has_odd_order = store_thm(
  "finite_field_char_even_has_odd_order",
  ``!r:'a field. FiniteField r ==> EVEN (char r) ==> (!x. x IN R+ ==> ODD (forder x))``,
  rpt (stripDup[FiniteField_def]) >>
  `?d. 0 < d /\ (CARD R = (char r) ** d)` by rw[finite_field_card] >>
  `CARD R = SUC (CARD R+)` by rw[GSYM finite_field_carrier_card] >>
  `ODD (CARD R+)` by metis_tac[EVEN_EXP, EVEN_ODD_SUC] >>
  `(forder x) divides (CARD R+)` by rw[field_order_divides] >>
  metis_tac[DIVIDES_ODD]);

(* Theorem: FiniteField r ==> !x. x IN R /\ (forder x = 2) ==> (x = -#1) *)
(* Proof:
   Let p = unity 2.
    Then poly p             by poly_unity_poly
     and deg p = 2          by poly_unity_deg
      so p <> |0|           by poly_deg_zero, 0 <> 2
    Claim: !z. z IN R /\ (z ** 2 = #1) ==> z IN roots p
    Proof: By poly_roots_member, poly_root_def, this is to show:
              eval p z = #0
           Now  eval p z
              = z ** 2 - #1     by poly_eval_X_exp_n_sub_c
              = #1 - #1         by given, z ** 2 = #1
              = #0

    The goal is: x IN R /\ (forder x = 2) ==> x = #1.
    By contradiction, suppose x <> #1.
    But  #1 IN R /\ #1 ** 2 = #1        by field_one_exp
    and -#1 IN R /\ (-#1) ** 2 = #1     by field_exp_small, field_mult_neg_neg

    Step 1: get three roots
     Now x <> #0             by field_order_zero, 0 <> 2
     and x <> #1             by field_order_one, 1 <> 2
      so x IN R+             by field_nonzero_eq, x <> #0
    thus x ** 2 = #1         by field_order_property
    Claim: char r <> 2.
    Proof: By contradiction.  Suppose char r = 2.
           Then EVEN (char r)                by EVEN_2
             so ODD (forder x)               by finite_field_char_even_has_odd_order
           This contradicts (forder x = 2)   by EVEN_ODD, x IN R+

    With char r <> 2, -#1 <> #1              by ring_neg_one_eq_one, char <> 2
     Hence {#1; -#1; x} SUBSET roots p       by SUBSET_DEF, first claim

    Step 2: get a contradiction by counting roots
      Note CARD {#1; -#1; x} = 3             by CARD_INSERT
       But CARD (roots p) <= deg p = 2       by poly_roots_count, Field r, p <> |0|
       Now FINITE (roots p                   by poly_roots_finite, p <> |0|
       ==> 3 <= CARD (roots p)               by CARD_SUBSET
      This contradicts (CARD (roots p) = 2).
*)
val finite_field_order_eq_2 = store_thm(
  "finite_field_order_eq_2",
  ``!r:'a field. FiniteField r ==> !x. x IN R /\ (forder x = 2) ==> (x = -#1)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = unity 2` >>
  `poly p` by rw[Abbr`p`] >>
  `deg p = 2` by rw[Abbr`p`] >>
  `p <> |0|` by metis_tac[poly_deg_zero, DECIDE``0 <> 2``] >>
  `!z. z IN R /\ (z ** 2 = #1) ==> z IN roots p` by
  (rw[poly_roots_member, poly_root_def] >>
  `eval p z = z ** 2 - #1` by rw[Abbr`p`] >>
  rw[]) >>
  `#1 ** 2 = #1` by rw[] >>
  `(-#1) ** 2 = #1` by rw[field_exp_small] >>
  spose_not_then strip_assume_tac >>
  `x <> #1` by metis_tac[field_order_one, DECIDE``1 <> 2``] >>
  `x <> #0` by metis_tac[field_order_zero, DECIDE``0 <> 2``] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `x ** 2 = #1` by metis_tac[field_order_property] >>
  `char r <> 2` by metis_tac[finite_field_char_even_has_odd_order, EVEN_2, EVEN_ODD] >>
  `-#1 <> #1` by rw[ring_neg_one_eq_one] >>
  `{#1; -#1; x} SUBSET roots p` by rw[SUBSET_DEF] >>
  `CARD {#1; -#1; x} = 3` by rw[] >>
  `CARD (roots p) <= 2` by metis_tac[poly_roots_count] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `3 <= CARD (roots p)` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* Note: the converse is not generally true, due to:
field_order_neg_one  |- !r. Field r ==> (forder (-#1) = if char r = 2 then 1 else 2)
field_neg_one_eq_one |- !r. Field r ==> ((-#1 = #1) <=> (char r = 2))
*)

(* ------------------------------------------------------------------------- *)
(* Subfield is Vector Space over Prime Field.                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Subfield is a vector space over Prime Field:
            !s. s <<= r ==> VSpace (PF r) s.sum r.prod.op *)
(* Proof:
   Since subfield (PF r) s           by prime_field_every_subfield
   and   Field (PF r)                by prime_field_field
   so    !z. z IN Fp ==> z IN B      by subfield_property_alt
   By VSpace_def, this is to show:
   (0) FiniteField r ==> Field (PF r), alreay asserted.
   (1) Field s ==> AbelianGroup s.sum
       True by field_def_alt
   (2) a IN Fp /\ v IN B ==> a * v IN B
       Since subfield (PF r) s       by prime_field_every_subfield
       and   Field (PF r)            by prime_field_field
       so    a IN B                  by subfield_property_alt
       and   s.prod.op = $*          by subfield_property_alt
       Hence true                    by field_mult_element
   (3) a IN Fp /\ b IN Fp ==> a * (b * v) = (PF r).prod.op a b * v
       or to show: a * (b * v) = a * b * v   by PF_property
       Since subfield (PF r) s       by prime_field_every_subfield
       and   Field (PF r)            by prime_field_field
       so    a, b IN B               by subfield_property_alt
       and   s.prod.op = $*          by subfield_property_alt
       Hence true                    by field_mult_assoc
   (4) v IN B ==> (PF r).prod.id * v = v
       (PF r).prod.id = #1           by PF_property
       v IN R                        by subfield_property_alt
       Hence true                    by field_mult_lone.
   (5) a IN Fp /\ u IN B /\ v IN B ==> a * s.sum.op u v = s.sum.op (a * u) (a * v)
       Since subfield (PF r) s       by prime_field_every_subfield
       and   Field (PF r)            by prime_field_field
       so    a IN B                  by subfield_property_alt
       and   s.prod.op = $+          by subfield_property_alt
       and   s.prod.op = $*          by subfield_property_alt
       Hence true                    by field_mult_radd.
   (6) a IN Fp /\ b IN Fp /\ v IN B ==> (PF r).sum.op a b * v = s.sum.op (a * v) (b * v)
       Since subfield (PF r) s       by prime_field_every_subfield
       and   Field (PF r)            by prime_field_field
       so    a, b IN B               by subfield_property_alt
       and   s.prod.op = $+          by subfield_property_alt
       and   s.prod.op = $*          by subfield_property_alt
       Hence true                    by field_mult_ladd.
*)
Theorem finite_field_subfield_is_vspace:
  !r:'a field. FiniteField r ==> !s. s <<= r ==> VSpace (PF r) s.sum r.prod.op
Proof
  rpt strip_tac >>
  ‘Field r /\ FINITE R’ by metis_tac[FiniteField_def] >>
  ‘subfield (PF r) s’ by rw[prime_field_every_subfield] >>
  ‘Field (PF r)’ by rw[prime_field_field] >>
  ‘!z. z IN Fp ==> z IN B’ by metis_tac[subfield_property_alt] >>
  rw[VSpace_def]
  >- metis_tac[field_mult_element, subfield_property_alt]
  >- (‘(s.prod.op (s.prod.op a b) v = s.prod.op a (s.prod.op b v))’
        by rw[field_mult_assoc] >>
      ‘s.prod.op a b IN B /\ s.prod.op b v IN B’ by rw[] >>
      metis_tac[PF_property, subfield_property_alt])
  >- metis_tac[PF_property, subfield_property_alt, field_mult_lone]
  >- (‘s.prod.op a (s.sum.op u v) = s.sum.op (s.prod.op a u) (s.prod.op a v)’
        by rw[field_mult_radd] >>
      ‘s.sum.op u v IN B /\ s.prod.op a u IN B /\ s.prod.op a v IN B’ by rw[] >>
      metis_tac[subfield_property_alt]) >>
  rw[PF_property] >>
  ‘s.prod.op (s.sum.op a b) v = s.sum.op (s.prod.op a v) (s.prod.op b v)’
    by rw[field_mult_ladd] >>
  ‘s.sum.op a b IN B /\ s.prod.op a v IN B /\ s.prod.op b v IN B’ by rw[] >>
  metis_tac[subfield_property_alt]
QED

(* Theorem: Any subfield of finite field has p ** d elements, where p = char r, and some nonzero d:
            FiniteField r ==> !s. s <<= r ==>
            ?d. 0 < d /\ (CARD B = (char r) ** d) *)
(* Proof:
   Since  VSpace (PF r) s.sum $*        by finite_field_subfield_is_vspace
     and  FINITE (PF r).carrier         by prime_field_finite_field, FiniteField_def
    also  B SUBSET R                    by SUBSET_DEF, subfield_property_alt
    thus  FINITE B                      by SUBSET_FINITE
     and  s.sum.carrier = B             by field_carriers
    Thus  FiniteVSpace (PF r) s.sum $*  by FiniteVSpace_def
   Hence  CARD (s.sum.carrier) = CARD (PF r).carrier ** (dim (PF r) s.sum $*    by finite_vspace_card
    Note  1 < CARD (s.sum.carrier)      by FiniteField_def, finite_field_card_gt_1
    Thus  0 < (dim (PF r) s.sum $* )    by ONE_LT_EXP

   But    FieldIso $## (GF (char r)) (PF r)              by finite_field_iso_GF_PF
   i.e.   BIJ $## (GF (char r)).carrier (PF r).carrier   by FieldIso_def
   Since  prime (char r)                by finite_field_char
     and  FiniteField (GF (char r))     by GF_finite_field
      ==> FINITE (GF (char r)).carrier  by FiniteField_def
     CARD (PF r).carrier
   = CARD (GF (char r)).carrier         by FINITE_BIJ_CARD_EQ
   = CARD (count (char r))              by GF_property
   = char r                             by CARD_COUNT
   Hence  CARD B = (char r) ** d, with prime (char r) and d = (dim (PF r) s.sum $*
*)
val finite_field_subfield_card = store_thm(
  "finite_field_subfield_card",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   ?d. 0 < d /\ (CARD B = (char r) ** d)``,
  rpt (stripDup[FiniteField_def]) >>
  `VSpace (PF r) s.sum $*` by rw[finite_field_subfield_is_vspace] >>
  `FINITE (PF r).carrier` by metis_tac[prime_field_finite_field, FiniteField_def] >>
  `B SUBSET R` by metis_tac[SUBSET_DEF, subfield_property_alt] >>
  `FINITE B` by metis_tac[SUBSET_FINITE] >>
  `s.sum.carrier = B` by metis_tac[field_carriers] >>
  `FiniteVSpace (PF r) s.sum $*` by rw[FiniteVSpace_def] >>
  `CARD (s.sum.carrier) = CARD Fp ** (dim (PF r) s.sum $* )` by rw[finite_vspace_card] >>
  `0 < (dim (PF r) s.sum $* )` by metis_tac[FiniteField_def, finite_field_card_gt_1, ONE_LT_EXP] >>
  `FieldIso $## (GF (char r)) (PF r)` by rw[finite_field_iso_GF_PF] >>
  `BIJ $## (GF (char r)).carrier (PF r).carrier` by metis_tac[FieldIso_def] >>
  `prime (char r)` by rw[finite_field_char] >>
  `FINITE (GF (char r)).carrier` by metis_tac[GF_finite_field, FiniteField_def] >>
  metis_tac[FINITE_BIJ_CARD_EQ, GF_property, CARD_COUNT]);

(* Theorem: Finite Field has q ** d elements, where q is the cardinality of a subfield, and some nonzero d:
            FiniteField r ==> !s. s <<= r ==> ?d. 0 < d /\ (CARD R = (CARD B) ** d) *)
(* Proof:
   Since  Field r /\ FINITE R        by FiniteField_def
   Hence  VSpace s r.sum $*          by field_is_vspace_over_subfield
   Given  B SUBSET R                 by SUBSET_DEF, subfield_property_alt
      so  FINITE B                   by SUBSET_FINITE
    Also  r.sum.carrier = R          by field_carriers
    Thus  FiniteVSpace s r.sum $*    by FiniteVSpace_def
      so  CARD (r.sum.carrier) = CARD B ** (r <:> s)    by finite_vspace_card
   Hence  CARD R = (CARD B) ** d, with d = (r <:> s)
    Note  1 < CARD R                 by finite_field_card_gt_1
    Thus  0 < d                      by ONE_LT_EXP
*)
val finite_field_card_subfield = store_thm(
  "finite_field_card_subfield",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   ?d. 0 < d /\ (CARD R = (CARD B) ** d)``,
  rpt (stripDup[FiniteField_def]) >>
  `VSpace s r.sum $*` by rw[field_is_vspace_over_subfield] >>
  `B SUBSET R` by metis_tac[SUBSET_DEF, subfield_property_alt] >>
  `FINITE B` by metis_tac[SUBSET_FINITE] >>
  `r.sum.carrier = R` by metis_tac[field_carriers] >>
  `FiniteVSpace s r.sum $*` by rw[FiniteVSpace_def] >>
  `CARD (r.sum.carrier) = CARD B ** (r <:> s)` by rw[finite_vspace_card] >>
  metis_tac[finite_field_card_gt_1, ONE_LT_EXP]);

(* Theorem: Given a finite field with p^n elements, where p = char r,
            Any subfield has p^m elements, where m divides n.
            FiniteField r ==> !s. s <<= r ==>
            ?n m. 0 < n /\ 0 < m /\
                  (CARD R = (char r) ** n) /\ (CARD (B) = (char r) ** m) /\ (m divides n) *)
(* Proof:
   Since  ?n. 0 < n /\ CARD R = char r ** n  by finite_field_card
     and  ?m. 0 < m /\ CARD B = char r ** m  by finite_field_subfield_card
    also  ?d. 0 < d /\ CARD R = CARD B ** d  by finite_field_card_subfield
    Let p = char r, the last equation is:
          p ** n = (p ** m) ** d             by substitution
                 = p ** (m * d)              by EXP_EXP_MULT
    Since prime (char r)                     by finite_field_char
          1 < p                              by ONE_LT_PRIME
    Hence n = m * d                          by EXP_BASE_INJECTIVE
            = d * m                          by MULT_COMM
    or m divides n                           by divides_def
*)
val finite_field_subfield_card_property = store_thm(
  "finite_field_subfield_card_property",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   ?n m. 0 < n /\ 0 < m /\ (CARD R = (char r) ** n) /\ (CARD (B) = (char r) ** m) /\ (m divides n)``,
  rpt strip_tac >>
  `prime (char r)` by rw[finite_field_char] >>
  qabbrev_tac `p = char r` >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `?n. 0 < n /\ (CARD R = p ** n)` by rw[finite_field_card, Abbr`p`] >>
  `?m. 0 < m /\ (CARD B = p ** m)` by rw[finite_field_subfield_card, Abbr`p`] >>
  `?d. 0 < d /\ (CARD R = CARD B ** d)` by rw[finite_field_card_subfield] >>
  metis_tac[EXP_EXP_MULT, EXP_BASE_INJECTIVE, MULT_COMM, divides_def]);

(* Theorem: FiniteField r /\ s <<= r ==> (CARD B divides CARD R) *)
(* Proof:
   Note FiniteField s                   by subfield_finite_field
    and CARD R = (char r) ** (fdim r)   by finite_field_card_alt
    and CARD B = (char s) ** (fdim s)   by finite_field_card_alt
    and char r = char s                 by subfield_char
   Also fdim s divides fdim r           by finite_field_subfield_dim_divides
    But 0 < fdim r                      by finite_field_dim_pos
    ==> fdim s <= fdim r                by DIVIDES_LE, 0 < fdim r
    Now 1 < char r                      by finite_field_char_gt_1
    ==> CARD B divides CARD R           by power_divides_iff

   Can also use: finite_field_subfield_card_property
*)
val finite_field_subfield_card_divides = store_thm(
  "finite_field_subfield_card_divides",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (CARD B divides CARD R)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `(CARD R = (char r) ** (fdim r)) /\ 0 < fdim r` by rw[finite_field_card_eqn] >>
  `CARD B = (char s) ** (fdim s)` by rw[finite_field_card_eqn] >>
  `char r = char s` by rw[subfield_char] >>
  `fdim s divides fdim r` by rw[finite_field_subfield_dim_divides] >>
  `fdim s <= fdim r` by rw[DIVIDES_LE] >>
  `1 < char r` by rw[finite_field_char_gt_1] >>
  rw[power_divides_iff]);

(* Theorem: FiniteField r /\ s <<= r ==> (CARD B* divides CARD F* ) *)
(* Proof:
   Note FiniteField s                   by subfield_finite_field
    and CARD F* = CARD R - 1            by finite_field_mult_carrier_card
    and CARD B* = CARD B - 1            by finite_field_mult_carrier_card
   Note CARD R = (char r) ** (fdim r)   by finite_field_card_alt
    and CARD B = (char s) ** (fdim s)   by finite_field_card_alt
    and char r = char s                 by subfield_char
    and 1 < char r                      by finite_field_char_gt_1
   Now fdim s divides fdim r            by finite_field_subfield_dim_divides
   ==> CARD B* divides CARD F*          by power_predecessor_divisibility
*)
val finite_field_subfield_nonzero_card_divides = store_thm(
  "finite_field_subfield_nonzero_card_divides",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (CARD B* divides CARD F* )``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `CARD F* = CARD R - 1` by rw[finite_field_mult_carrier_card] >>
  `CARD B* = CARD B - 1` by rw[finite_field_mult_carrier_card] >>
  `CARD R = (char r) ** (fdim r)` by rw[finite_field_card_alt] >>
  `CARD B = (char s) ** (fdim s)` by rw[finite_field_card_alt] >>
  `char r = char s` by rw[subfield_char] >>
  `1 < char r` by rw[finite_field_char_gt_1] >>
  `fdim s divides fdim r` by rw[finite_field_subfield_dim_divides] >>
  rw[power_predecessor_divisibility]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==> !n. coprime (forder x) (CARD B ** n) *)
(* Proof:
   Let a = forder x.
   Note a divides (CARD R+)           by field_order_divides, x IN R+
    and CARD R = SUC (CARD R+)        by finite_field_carrier_card
     so coprime a (CARD R)            by divides_imp_coprime_with_successor
    Now ?d. 0 < d /\ (CARD R = CARD B ** d)  by finite_field_card_subfield
     so coprime a (CARD B ** d)       by CARD R = CARD B ** d
   thus coprime a (CARD B)            by coprime_iff_coprime_exp, 0 < d
    and coprime a (CARD B ** n)       by coprime_exp_comm
*)
val finite_field_order_coprime = store_thm(
  "finite_field_order_coprime",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==> !n. coprime (forder x) (CARD B ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `a = forder x` >>
  `a divides (CARD R+)` by metis_tac[field_order_divides] >>
  `CARD R = SUC (CARD R+)` by rw[GSYM finite_field_carrier_card] >>
  `coprime a (CARD R)` by rw[divides_imp_coprime_with_successor] >>
  `?d. 0 < d /\ (CARD R = CARD B ** d)` by rw[finite_field_card_subfield] >>
  metis_tac[coprime_iff_coprime_exp, coprime_exp_comm]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==> 0 < forder x /\ coprime (forder x) (CARD B) *)
(* Proof:
   Let m = CARD B, ox = forder x.
   Note x IN R                              by field_nonzero_element
    and 0 < ox                              by field_order_property, x IN R+
  Since ?d. 0 < d /\ (m = (char r) ** d)    by finite_field_subfield_card
     so coprime ox m                        by finite_field_order_coprime_char_exp, m = (char r) ** d
    Or, coprime ox m                        by finite_field_order_coprime, with n = 1
*)
val finite_field_order_property = store_thm(
  "finite_field_order_property",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R+ ==> 0 < forder x /\ coprime (forder x) (CARD B)``,
  metis_tac[FiniteField_def, field_nonzero_element, field_order_property, finite_field_order_coprime, EXP_1]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R+ ==> ordz (forder x) (CARD B) divides (r <:> s) *)
(* Proof:
   Let m = CARD B, ox = forder x, om = ordz ox m, d = r <:> s.
   To show: om divides d
   Note x IN R                    by field_nonzero_element

   If x = #1,
   Then ox = 1                    by field_order_one
     so om = 1                    by ZN_order_mod_1
    and 1 divides d               by ONE_DIVIDES_ALL

   If x <> #1,
   Then 0 < ox /\ coprime ox m    by finite_field_order_property
    and ox <> 1                   by field_order_eq_1, x <> #1
   Let g = Invertibles (ZN ox).prod, the Euler group.
   and z = m MOD ox.
   Then Group g                   by ZN_invertibles_group, 0 < ox
    ==> z IN g.carrier            by ZN_coprime_invertible, 1 < ox, coprime ox m
    Note om = ordz ox m           by ZN_order_mod, 0 < ox
            = order g z           by ZN_invertibles_order, 0 < ox

   Thus g.exp z om = (z ** om) MOD ox = 1    by ZN_order_property, EXP_MOD
    and CARD R = m ** d                      by finite_subfield_card_eqn

   Note !x k. g.exp x k = (ZN ox).prod.exp x k         by Invertibles_property
    and !x k. (ZN ox).prod.exp x k = (x ** k) MOD ox   by ZN_exp

        g.exp z d
      = (z ** d) MOD ox           by above
      = ((m MOD ox) ** d) MOD ox  by z = m MOD ox
      = (m ** d) MOD ox           by EXP_MOD
      = (CARD R) MOD ox           by above
      = 1                         by finite_field_card_mod_order

   Given g.exp z d = 1,
     and g.exp z om = 1
     and g.id = 1                 by ZN_property, Invertibles_property
     ==> om divides d             by group_order_divides_exp
*)
val subfield_card_order_divides_dim = store_thm(
  "subfield_card_order_divides_dim",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==> ordz (forder x) (CARD B) divides (r <:> s)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `om = ordz ox m` >>
  qabbrev_tac `d = (r <:> s)` >>
  `x IN R` by rw[field_nonzero_element] >>
  Cases_on `x = #1` >| [
    `ox = 1` by rw[field_order_one, Abbr`ox`] >>
    `om = 1` by rw[ZN_order_mod_1, Abbr`om`] >>
    rw[],
    `0 < ox /\ coprime ox m` by metis_tac[finite_field_order_property] >>
    `ox <> 1` by rw[field_order_eq_1, Abbr`ox`] >>
    `1 < ox` by decide_tac >>
    qabbrev_tac `g = Invertibles (ZN ox).prod` >>
    qabbrev_tac `z = m MOD ox` >>
    `Group g` by rw[ZN_invertibles_group, Abbr`g`] >>
    `z IN g.carrier` by rw[ZN_coprime_invertible, Abbr`g`, Abbr`z`] >>
    `f*.exp = $**` by rw[field_nonzero_mult_property] >>
    `om = ordz ox m` by rw[ZN_order_mod, Abbr`om`] >>
    `_  = order g z` by rw[ZN_invertibles_order, Abbr`g`, Abbr`z`] >>
    `!x k. !x k. g.exp x k = (x ** k) MOD ox` by rw[Invertibles_property, ZN_exp, Abbr`g`] >>
    `g.exp z om = 1` by metis_tac[ZN_order_property_alt, EXP_MOD] >>
    `CARD R = m ** d` by rw[finite_subfield_card_eqn, Abbr`m`, Abbr`d`] >>
    `g.exp z d = (m ** d) MOD ox` by metis_tac[EXP_MOD] >>
    `_ = (CARD R) MOD ox` by metis_tac[finite_subfield_card_eqn] >>
    `_ = 1` by metis_tac[finite_field_card_mod_order] >>
    `g.id = 1` by rw[ZN_property, Invertibles_property, Abbr`g`] >>
    rw[GSYM group_order_divides_exp]
  ]);

(* This is a milestone theorem. *)

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides (CARD R+) ==> coprime n (CARD B) *)
(* Proof:
   Note n divides CARD R+
    ==> coprime n (SUC (CARD R+))       by divides_imp_coprime_with_successor
     or coprime n (CARD R)              by finite_field_carrier_card
    Now CARD R = CARD B ** (r <:> s)
    and 0 < (r <:> s)                   by finite_subfield_card_eqn
    ==> coprime n (CARD B)              by coprime_iff_coprime_exp
*)
val subfield_card_coprime_condition = store_thm(
  "subfield_card_coprime_condition",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides (CARD R+) ==> coprime n (CARD B)``,
  rpt (stripDup[FiniteField_def]) >>
  `coprime n (SUC (CARD R+))` by rw[divides_imp_coprime_with_successor] >>
  `CARD R = SUC (CARD R+)` by rw[finite_field_carrier_card] >>
  `(CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s)` by rw[finite_subfield_card_eqn] >>
  metis_tac[coprime_iff_coprime_exp]);

(* Note: In general, the converse not valid: coprime n (CARD B) ==> n divides CARD R+
The best one can do is:
Since (CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s)        by finite_subfield_card_eqn
We have coprime n (CARD B) ==> coprime n (CARD R)            by coprime_iff_coprime_exp,
or coprime n (SUC (CARD R+)), due to CARD R = SUC (CARD R+)  by finite_field_carrier_card
That's about it, not really getting n divides (CARD R+).

For example, if CARD R = 11^2, n = 7,
then coprime n (CARD R), and CARD R+ = 120, but 7 does not divide 120.

However, 7 does divide 11^(ord 7 11) - 1, or 11^3 - 1 by ZN_order_divisibility, and (ord 7 11 = 3).
Even 7 divides (121)^(ord 7 121) - 1, or 121^3 - 1, again by ZN_order_divisibility, and (ord 7 121 = 3).
so there is hope.
*)

(* Note: The solution to this dilemma is this:
Given a positive n and a FiniteField s, we treat this s as a 'subfield' of some big FiniteField r to be determined.
Let m = CARD B, and assume that coprime n m.
Then if 1 < n, 0 < ordz n m /\ (m ** ordz n m MOD n = 1) by ZN_coprime_order_property
Let d = ordz n m, then 0 < d and m ** d MOD n = 1, the least such d.
Now, let FiniteField r be such that (r <:> s) = d. This r exists by Existence Theorem.
That is, CARD R = m ** d,
Thus n divides m ** d - 1, or n divides (CARD R+)   by ZN_order_divisibility, 1 < n.
*)

(* Theorem: FiniteField r /\ s <<= r ==> !n. 0 < n /\ (ordz n (CARD B) = (r <:> s)) ==>
           (coprime n (CARD B) <=> n divides (CARD R+)) *)
(* Proof:
   If part: coprime n (CARD B) ==> n divides (CARD R+)
        Let m = CARD B, d = (r <:> s).
       Note (CARD R = m ** d) /\ 0 < d    by finite_subfield_card_eqn
        and CARD R+ = CARD R - 1          by finite_field_nonzero_carrier_card
        ==> n divides (CARD R+)           by ZN_order_divisibility

   Only-if part: n divides (CARD R+) ==> coprime n (CARD B)
      This is true                        by subfield_card_coprime_condition
*)
val subfield_card_coprime_iff = store_thm(
  "subfield_card_coprime_iff",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. 0 < n /\ (ordz n (CARD B) = (r <:> s)) ==>
           (coprime n (CARD B) <=> n divides (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  metis_tac[finite_subfield_card_eqn, finite_field_nonzero_carrier_card, ZN_order_divisibility] >>
  metis_tac[subfield_card_coprime_condition]);

(* ------------------------------------------------------------------------- *)
(* Multiplicative Group of Field is Cyclic.                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The multiplicative group of a Finite Finite has a generator. *)
(* Proof:
   Note R+ = F*                by field_mult_carrier
   Let n = size of F* = |F*|
   Let m = maximal order in F*, so m <= n.
   Let p be the order of an element in F*.
   Then p divides m, i.e. m = p * q,   by group_order_divides_maximal
   Hence the polynomial x ** m - #1 in F[x] has n roots in F*, since:
     x ** m = x ** (p * q)
            = (x ** p) ** q    by group_exp_mult
            = #1 ** q          by order_property
            = #1               by group_id_exp

   But by poly_roots_count,
   n <= m since a degree m polynomial can have at most m roots.
   Hence m = n.

   And the element attaining the maximal order is the generator of F*.
*)
val finite_field_mult_group_has_gen = store_thm(
  "finite_field_mult_group_has_gen",
  ``!r:'a field. FiniteField r ==> ?z:'a. z IN R+ /\ (forder z = CARD R+)``,
  rpt (stripDup[FiniteField_def]) >>
  `Group f* /\ (F* = R+) /\ !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x)` by rw[field_mult_group] >>
  `FINITE F*` by metis_tac[field_nonzero_element, SUBSET_DEF, SUBSET_FINITE] >>
  `FiniteGroup f*` by rw[FiniteGroup_def] >>
  `(f*.id = #1) /\ (f*.exp = $** )` by rw[field_nonzero_mult_property] >>
  `!x. x IN F* ==> 0 < forder x /\ (x ** (forder x) = #1)` by metis_tac[group_order_property] >>
  qabbrev_tac `s = (IMAGE (forder ) F* )` >>
  qabbrev_tac `m = MAX_SET s` >>
  qabbrev_tac `n = CARD F*` >>
  `FINITE s` by rw[IMAGE_FINITE, Abbr`s`] >>
  `s <> {}` by metis_tac[field_one_nonzero, IN_IMAGE, MEMBER_NOT_EMPTY, IMAGE_EMPTY] >>
  `m IN s /\ !y. y IN s ==> y <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `!x. x IN F* ==> (x ** m = #1)` by
  (rpt strip_tac >>
  `FiniteAbelianGroup f*` by rw[field_mult_group, FiniteAbelianGroup_def_alt] >>
  `(forder x) divides m` by metis_tac[group_order_divides_maximal] >>
  `?y. m = y * (forder x)` by rw[GSYM divides_def] >>
  metis_tac[MULT_COMM, group_exp_mult, group_id_exp]) >>
  qabbrev_tac `p = X ** m - |1|` >>
  `!x. x IN R+ ==> ((x ** m = #1) <=> root p x)` by
    (rw_tac std_ss[poly_root_def, Abbr`p`] >>
  `x ** m = #1` by rw[] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly X /\ poly (X ** m) /\ poly |1| /\ poly (-|1|)` by rw[] >>
  `x IN R` by rw[ring_nonzero_element] >>
  `eval (X ** m + -|1|) x = (eval (X ** m) x) + -(eval |1| x)` by metis_tac[poly_eval_add, poly_eval_neg] >>
  `_ = eval (X ** m) x - eval |1| x` by rw[] >>
  `_ = #0` by rw[poly_eval_exp, poly_eval_X] >>
  rw_tac std_ss[poly_sub_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `|1| = chop[##1]` by rw[poly_one] >>
  `deg p = m` by metis_tac[poly_deg_X_exp_n_sub_c, poly_one_sum_n] >>
  `0 < m` by metis_tac[IN_IMAGE] >>
  `deg p <> 0` by decide_tac >>
  `p <> |0|` by metis_tac[poly_deg_zero] >>
  `poly X /\ poly |1|` by rw[poly_sum_num_poly] >>
  `poly p` by rw[Abbr`p`] >>
  `CARD (roots p) <= m` by rw[poly_roots_count] >>
  `F* = roots p` by
      (rw[poly_roots_def, EXTENSION, EQ_IMP_THM] >-
  rw[ring_nonzero_element] >-
  metis_tac[] >>
  Cases_on `x = #0` >| [
    qabbrev_tac `m = deg p` >>
    `#0 IN R /\ poly (X ** m) /\ poly (-|1|)` by rw[] >>
    `#0 = eval p #0` by rw[GSYM poly_root_def] >>
    `_ = eval (X ** m + -|1|) #0` by rw[Abbr`p`] >>
    `_ = (eval (X ** m) #0) + -(eval |1| #0)` by metis_tac[poly_eval_add, poly_eval_neg] >>
    `_ = eval (X ** m) #0 - eval |1| #0` by rw[] >>
    `_ = -#1` by rw[poly_eval_exp, poly_eval_X, ring_zero_exp] >>
    metis_tac[ring_neg_zero, ring_neg_neg, ring_one_element],
    rw[ring_nonzero_eq]
  ]
  ) >>
  `n = CARD (roots p)` by rw[Abbr`n`] >>
  `n <= m` by decide_tac >>
  `?z. z IN R+ /\ (m = forder z)` by metis_tac[IN_IMAGE] >>
  `z IN R /\ z <> #0` by metis_tac[ring_nonzero_eq] >>
  `Generated f* z <= f*` by metis_tac[generated_subgroup] >>
  `CARD (Generated f* z).carrier = m` by metis_tac[generated_group_card] >>
  `m divides n` by metis_tac[Lagrange_thm] >>
  `R+ <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `n <> 0` by metis_tac[CARD_EQ_0] >>
  `0 < n` by decide_tac >>
  `m <= n` by rw[DIVIDES_LE] >>
  `m = n` by decide_tac >>
  metis_tac[]);

(* Theorem: The multiplicative group of a Finite Field is cyclic. *)
(* Proof:
   Note R+ = F*               by field_mult_carrier
   Since F* has a generator   by finite_field_mult_group_has_gen
   F* is cyclic               by cyclic_finite_alt
*)
val finite_field_mult_group_cyclic = store_thm(
  "finite_field_mult_group_cyclic",
  ``!r:'a field. FiniteField r ==> cyclic f*``,
  rpt strip_tac >>
  `?z:'a. z IN R+ /\ (forder z = CARD R+)` by rw[finite_field_mult_group_has_gen] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `Group f* /\ (F* = R+)` by rw[field_mult_group] >>
  `FINITE F*` by metis_tac[field_nonzero_element, SUBSET_DEF, SUBSET_FINITE] >>
  `FiniteGroup f*` by rw[FiniteGroup_def] >>
  metis_tac[cyclic_finite_alt]);

(* This is a most significant milestone theorem! *)

(* Theorem: FiniteField r ==> !n. n divides (CARD R+) <=> (orders f* n) <> {} *)
(* Proof:
   If part: n divides CARD R+ ==> orders f* n <> {}

      Note FiniteField r
       ==> ?z. z IN R+ /\ (forder z = CARD R+)   by finite_field_mult_group_has_gen
       and z IN R                                by field_nonzero_element
       Now n divides (CARD R+)
       ==> ?m. CARD R+ = m * n             by divides_def
        or m divides (CARD R+)             by divides_def, MULT_COMM
       ==> gcd m (CARD R+) = m             by divides_iff_gcd_fix
      Note forder (z ** m) * gcd m (CARD R+) = forder z    by field_order_power, x IN R
        or               forder (z ** m) * m = CARD R+     by above
        or               forder (z ** m) * m = n * m       by above, MULT_COMM
      Since 0 < CARD R+                    by field_nonzero_card_pos
         so m <> 0                         by MULT_EQ_0, CARD R+ <> 0
         so forder (z ** m) = n            by EQ_MULT_RCANCEL, m <> 0
        and z ** m IN R+                   by field_exp_nonzero, z IN R+
        ==> z ** m IN (orders f* n)        by field_orders_element_property
         or (orders f* n) <> {}            by MEMBER_NOT_EMPTY

   Only-if part: orders f* n <> {} ==> n divides CARD R+
      Since ?x. x IN orders f* n           by MEMBER_NOT_EMPTY
        ==> x IN R+ /\ (forder x = n)      by field_orders_element_property
        ==> (forder x) divides (CARD R+)   by field_order_divides, x IN R+
         or n divides (CARD R+)            by forder x = n
*)
val finite_field_orders_nonempty_iff = store_thm(
  "finite_field_orders_nonempty_iff",
  ``!r:'a field. FiniteField r ==> !n. n divides (CARD R+) <=> (orders f* n) <> {}``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >| [
    `?z. z IN R+ /\ (forder z = CARD R+)` by rw[finite_field_mult_group_has_gen] >>
    `z IN R` by rw[field_nonzero_element] >>
    `?m. CARD R+ = m * n` by rw[GSYM divides_def] >>
    `m divides (CARD R+)` by metis_tac[divides_def, MULT_COMM] >>
    `gcd m (CARD R+) = m` by rw[GSYM divides_iff_gcd_fix] >>
    `forder (z ** m) * m = CARD R+` by metis_tac[field_order_power] >>
    `_ = n * m` by rw[] >>
    `0 < CARD R+` by rw[field_nonzero_card_pos] >>
    `CARD R+ <> 0` by decide_tac >>
    `m <> 0` by metis_tac[MULT_EQ_0] >>
    `forder (z ** m) = n` by metis_tac[EQ_MULT_RCANCEL] >>
    `z ** m IN R+` by rw[field_exp_nonzero] >>
    metis_tac[field_orders_element_property, MEMBER_NOT_EMPTY],
    metis_tac[field_order_divides, field_orders_element_property, MEMBER_NOT_EMPTY]
  ]);

(*
> cyclic_eq_order_partition |> ISPEC ``f*``;
val it =
   |- cyclic f* /\ FINITE F* ==>
   (partition (eq_order f* ) F* = {orders f* n | n | n divides CARD F*}):
   thm
> eq_order_def |> ISPEC ``f*``;
val it =
   |- !x y. eq_order f* x y <=> (forder x = forder y):
   thm
*)

(* Theorem: FiniteField r ==>
            (partition (\x y. forder x = forder y) R+ = {orders f* n | n IN divisors (CARD R+)}) *)
(* Proof:
   Note F* = R+            by field_mult_carrier, Field r
    and FINITE R+          by field_nonzero_finite, by FINITE R
    and cyclic f*          by finite_field_mult_group_cyclic, FiniteField r
   Also eq_order f* = \x y. (forder x = forder y)   by eq_order_def, FUN_EQ_THM
        partition (\x y. (forder x = forder y)) R+
      = partition (eq_order f* ) R+         by above
      = partition (eq_order f* ) F*         by above
      = {orders f* n | n IN divisors (CARD F* )}   by cyclic_eq_order_partition_alt
      = {orders f* n | n IN divisors (CARD R+)}    by above
*)
val finite_field_eq_order_partition = store_thm(
  "finite_field_eq_order_partition",
  ``!r:'a field. FiniteField r ==>
               (partition (\x y. forder x = forder y) R+ = {orders f* n | n IN divisors (CARD R+)})``,
  rpt (stripDup[FiniteField_def]) >>
  `F* = R+` by rw[field_mult_carrier] >>
  `FINITE R+` by rw[field_nonzero_finite] >>
  `cyclic f*` by rw[finite_field_mult_group_cyclic] >>
  `eq_order f* = \x y. (forder x = forder y)` by rw[eq_order_def, FUN_EQ_THM] >>
  `partition (\x y. (forder x = forder y)) R+ = partition (eq_order f* ) R+` by rw[] >>
  `_ = partition (eq_order f* ) F*` by metis_tac[] >>
  `_ = {orders f* n | n IN divisors (CARD F* )}` by rw[cyclic_eq_order_partition_alt] >>
  `_ = {orders f* n | n IN divisors (CARD R+)}` by rw[] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Primitive                                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of field primitives *)
val _ = overload_on("FPrimitives", `` \(r:'a field). {z | z IN R+ /\ (forder z = CARD R+)}``);

(* Define primitive generator of a FiniteField *)
val field_primitive_def = Define`
  field_primitive (r:'a field) = CHOICE (FPrimitives r)
`;
val _ = overload_on ("primitive", ``field_primitive``);
(*
- field_primitive_def;
> val it = |- !r. primitive r = CHOICE (FPrimitives r) : thm
*)

(* Theorem: z IN FPrimitives r <=> z IN R+ /\ (forder z = CARD R+) *)
(* Proof: by notation *)
val field_primitives_element = store_thm(
  "field_primitives_element",
  ``!r:'a field. !z. z IN FPrimitives r <=> z IN R+ /\ (forder z = CARD R+)``,
  rw[]);

(* Theorem: FiniteField r ==> FPrimitives r <> {} *)
(* Proof:
   Given FiniteField r,
   ?z. z IN R+ /\ (forder z = CARD R+)     by finite_field_mult_group_has_gen
     ==> z IN FPrimitives r                by field_primitives_element
   Hence FPrimitives r <> {}               by MEMBER_NOT_EMPTY
*)
val field_primitives_nonempty = store_thm(
  "field_primitives_nonempty",
  ``!r:'a field. FiniteField r ==> FPrimitives r <> {}``,
  metis_tac[finite_field_mult_group_has_gen, field_primitives_element, MEMBER_NOT_EMPTY]);

(* Theorem: FiniteField r ==> (primitive r) IN (FPrimitives r) *)
(* Proof:
   Let s = FPrimitives r.
   Since s <> {}               by field_primitives_nonempty
    Thus CHOICE s IN s         by CHOICE_DEF
   i.e. (primitive r) IN s     by field_primitive_def
*)
val field_primitives_has_primitive = store_thm(
  "field_primitives_has_primitive",
  ``!r:'a field. FiniteField r ==> (primitive r) IN (FPrimitives r)``,
  rw_tac std_ss[field_primitive_def, field_primitives_nonempty, CHOICE_DEF]);

(* Theorem: FiniteField r ==> (primitive r) IN R+ /\ (forder (primitive r) = CARD R+) *)
(* Proof:
   Since (primitive r) IN (FPrimitives r)                        by field_primitives_has_primitive
      so (primitive r) IN R+ /\ forder (primitive r) = CARD R+   by field_primitives_element
*)
val field_primitive_property = store_thm(
  "field_primitive_property",
  ``!r:'a field. FiniteField r ==> (primitive r) IN R+ /\ (forder (primitive r) = CARD R+ )``,
  metis_tac[field_primitives_has_primitive, field_primitives_element]);

(* Theorem: FiniteField r ==> (primitive r) IN R *)
(* Proof:
   Since (primitive r) IN R+      by field_primitive_property
   hence (primitive r) IN R       by field_nonzero_element
*)
val field_primitive_element = store_thm(
  "field_primitive_element",
  ``!r:'a field. FiniteField r ==> (primitive r) IN R``,
  rw[field_primitive_property, field_nonzero_element]);

(* export simple result *)
val _ = export_rewrites ["field_primitive_element"];

(* Theorem: FiniteField r ==> (primitive r) IN R *)
(* Proof: by field_primitive_property *)
val field_primitive_nonzero = store_thm(
  "field_primitive_nonzero",
  ``!r:'a field. FiniteField r ==> (primitive r) IN R+``,
  rw[field_primitive_property]);

(* export simple result *)
val _ = export_rewrites ["field_primitive_nonzero"];

(* Theorem: FiniteField r ==> (forder (primitive r) = CARD R+) *)
(* Proof: by field_primitive_property *)
val field_primitive_order = store_thm(
  "field_primitive_order",
  ``!r:'a field. FiniteField r ==> (forder (primitive r) = CARD R+)``,
  rw_tac std_ss[field_primitive_property]);

(* Theorem: FiniteField r /\ FiniteField s /\ (CARD R = CARD s.carrier) ==>
            (forder (primitive r) = order (s.prod excluding s.sum.id) (primitive s)) *)
(* Proof:
   Note CARD R = SUC (CARD R+)                            by finite_field_carrier_card
    and CARD s.carrier = SUC (CARD (ring_nonzero s))      by finite_field_carrier_card
   Thus CARD R+ = CARD (ring_nonzero s)                   by SUC_EQ
        (forder (primitive r)
      = CARD R+                                           by field_primitive_property
      = CARD (ring_nonzero s)                             by above
      = order (s.prod excluding s.sum.id) (primitive s)   by field_primitive_property
*)
val field_primitives_order_eq = store_thm(
  "field_primitives_order_eq",
  ``!(r:'a field) (s:'b field). FiniteField r /\ FiniteField s /\ (CARD R = CARD s.carrier) ==>
    (forder (primitive r) = order (s.prod excluding s.sum.id) (primitive s))``,
  rpt (stripDup[FiniteField_def]) >>
  metis_tac[finite_field_carrier_card, SUC_EQ, field_primitive_property]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==>
            !z. z IN FPrimitives r ==> ?n. n < CARD R+ /\ (x = z ** n) *)
(* Proof:
   Note z IN R+ /\ (forder z = CARD R+)      by field_primitives_element
    and Group f*                             by field_nonzero_mult_is_group
   Also F* = R+                              by field_mult_carrier
    and R+ SUBSET R                          by field_nonzero_element, SUBSET_DEF
   Thus FINITE R+                            by SUBSET_FINITE
    and FiniteGroup f*                       by FiniteGroup_def
    ==> ?n. n < CARD R+ /\ x = f*.exp z n    by finite_group_primitive_property
     or                    x = z ** n        by field_nonzero_mult_property
*)
val field_primitives_element_property = store_thm(
  "field_primitives_element_property",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==>
   !z. z IN FPrimitives r ==> ?n. n < CARD R+ /\ (x = z ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  `z IN R+ /\ (forder z = CARD R+)` by fs[field_primitives_element] >>
  `Group f*` by rw[field_nonzero_mult_is_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  `R+ SUBSET R` by metis_tac[field_nonzero_element, SUBSET_DEF] >>
  `FINITE R+` by metis_tac[SUBSET_FINITE] >>
  `FiniteGroup f*` by metis_tac[FiniteGroup_def] >>
  metis_tac[finite_group_primitive_property, field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> !z. z IN (FPrimitives r) ==>
            (-#1 = if char r = 2 then #1 else z ** ((CARD R+) DIV 2)) *)
(* Proof:
   If char r = 2,
      Then -#1 = #1                by ring_char_2_neg_one
   If char r <> 2,
      Let m = (CARD R+) DIV 2
      Since prime (char r)         by finite_field_char
         so ODD (char r)           by ODD_PRIME, char r <> 2
        Now ?d. 0 < d /\ (CARD R = (char r) ** d)  by finite_field_card
       thus ODD (CARD R)           by power_parity
        ==> EVEN (CARD R+)         by finite_field_carrier_parity
        ==> (CARD R+) MOD 2 = 0    by EVEN_MOD2
         or m * 2 = CARD R+        by DIVIDES_MOD_0, DIVIDES_EQN

      Let z = primitive r
      Then z IN R               by field_primitive_element
      Also z IN R+ /\ (forder z = CARD R+)   by field_primitive_property
      Let x = z ** m.
      Then x ** 2
         = (z ** m) ** 2
         = z ** (m * 2)         by field_exp_mult
         = #1                   by field_order_property, m * 2 = CARD R+ = forder z

       Now x IN R+              by field_exp_nonzero
        so x IN R               by field_nonzero_element
     Since 0 < CARD R+          by field_nonzero_card_pos
        so m < CARD R+          by DIV_LESS, 0 < CARD R+, 1 < 2.
       and x = z ** m <> #1     by field_order_minimal
      Thus x ** 1 <> #1         by field_exp_1
       but x ** 2 = #1          by above
     Hence forder x = 2         by field_order_thm
        or x = -#1              by finite_field_order_eq_2
*)
val finite_field_neg_one_alt = store_thm(
  "finite_field_neg_one_alt",
  ``!r:'a field. FiniteField r ==> !z. z IN (FPrimitives r) ==>
    (-#1 = if char r = 2 then #1 else z ** ((CARD R+) DIV 2))``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[] >-
  rw[ring_char_2_neg_one] >>
  qabbrev_tac `m = (CARD R+) DIV 2` >>
  `m * 2 = CARD R+` by
  (`prime (char r)` by rw[finite_field_char] >>
  `ODD (char r)` by rw[ODD_PRIME] >>
  `?d. 0 < d /\ (CARD R = (char r) ** d)` by rw[finite_field_card] >>
  `ODD (CARD R)` by rw[GSYM power_parity] >>
  `EVEN (CARD R+)` by rw[finite_field_carrier_parity] >>
  `(CARD R+) MOD 2 = 0` by rw[GSYM EVEN_MOD2] >>
  metis_tac[DIVIDES_MOD_0, DIVIDES_EQN, DECIDE``0 < 2``]) >>
  `z IN R /\ z IN R+ /\ (forder z = CARD R+)` by metis_tac[field_primitives_element, field_nonzero_element] >>
  qabbrev_tac `x = z ** m` >>
  `x ** 2 = z ** (m * 2)` by rw[field_exp_mult, Abbr`x`] >>
  `_ = #1` by metis_tac[field_order_property] >>
  `x IN R+` by rw[field_exp_nonzero, Abbr`x`] >>
  `x IN R` by rw[field_nonzero_element] >>
  `m < CARD R+` by rw[DIV_LESS, field_nonzero_card_pos, Abbr`m`] >>
  `x ** 1 <> #1` by rw[field_order_minimal, Abbr`x`] >>
  `forder x = 2` by metis_tac[field_order_thm, DECIDE``0 < 2 /\ !m. 0 < m /\ m < 2 ==> (m = 1)``] >>
  rw[finite_field_order_eq_2]);

(* Theorem: FiniteField r ==> (-#1 = if char r = 2 then #1 else (primitive r) ** ((CARD R+) DIV 2)) *)
(* Proof: by field_primitives_has_primitive, finite_field_neg_one_alt *)
val finite_field_neg_one = store_thm(
  "finite_field_neg_one",
  ``!r:'a field. FiniteField r ==> (-#1 = if char r = 2 then #1 else (primitive r) ** ((CARD R+) DIV 2))``,
  rw_tac std_ss[field_primitives_has_primitive, finite_field_neg_one_alt]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Nonzero Element Index                                        *)
(* ------------------------------------------------------------------------- *)

(* Note: Field index is not defined for field zero. *)

(* Theorem: FiniteField r ==> !x. x IN R+ ==> ?n. x = (primitive r) ** n *)
(* Proof: by field_primitives_has_primitive, field_primitives_element_property *)
val field_index_exists = store_thm(
  "field_index_exists",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> ?n. n < CARD R+ /\ (x = (primitive r) ** n)``,
  rw_tac std_ss[field_primitives_has_primitive, field_primitives_element_property]);

(* Apply Skolemization *)
val lemma = prove(
  ``!(r:'a field) x. ?n. FiniteField r /\ x IN R+ ==> n < CARD R+ /\ (x = (primitive r) ** n)``,
  metis_tac[field_index_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define field index *)
(*
- SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma;
> val it = |- ?f. !r x. FiniteField r /\ x IN R+ ==> n < CARD R+ /\ (x = primitive r ** f r x) : thm
*)
val field_index_def = new_specification(
    "field_index_def",
    ["field_index"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val field_index_def =
|- !r x. FiniteField r /\ x IN R+ ==> field_index r x < CARD R+ /\ (x = primitive r ** field_index r x): thm
*)
val _ = overload_on ("idx", ``field_index r``);
(*
- field_index_def;
> val it = |- !r x. FiniteField r /\ x IN R+ ==> idx x < CARD R+ /\ (x = primitive r ** idx x) : thm
*)

(* Theorem: FiniteField r ==> !x. x IN R+ ==>
            !n. (idx x = n) <=> n < CARD R+ /\ (x = (primitive r) ** n) *)
(* Proof:
   If part: idx x = n ==> n < CARD R+ /\ (x = (primitive r) ** n)
      True by field_index_def.
   Only-if part: n < CARD R+ /\ (x = (primitive r) ** n) ==> idx x = n
      Let m = idx (primitive r ** n). The goal: m = n.
      Then m < CARD R+ /\ (primitive r ** n = primitive r ** m)     by field_index_def
       and primitive r IN R+ /\ (forder (primitive r) = CARD R+)    by field_primitive_property
        so n < forder (primitive r) /\ m < forder (primitive r)
      Hence m = n                                                   by field_nonzero_exp_eq
*)
val field_index_alt = store_thm(
  "field_index_alt",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==>
   !n. (idx x = n) <=> n < CARD R+ /\ (x = (primitive r) ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  rw[field_index_def] >-
  rw[field_index_def] >>
  metis_tac[field_index_def, field_primitive_property, field_nonzero_exp_eq]);

(* Theorem: FiniteField r ==> (idx #1 = 0) *)
(* Proof:
   Since #1 IN R+                    by field_one_nonzero
     and 0 < CARD R+                 by field_nonzero_card_pos
     and (primitive r) IN R          by field_primitive_element
     and (primitive r) ** 0 = #1     by field_exp_0
      so idx #1 = 0                  by field_index_alt
*)
val field_index_one = store_thm(
  "field_index_one",
  ``!r:'a field. FiniteField r ==> (idx #1 = 0)``,
  rw[FiniteField_def, field_nonzero_card_pos, field_index_alt]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> ((idx x = 0) <=> (x = #1)) *)
(* Proof:
   If part: idx x = 0 ==> x = #1
      Then x = (primitive r) ** 0   by field_index_def
             = #1                   by field_exp_0
   Only-if part: x = #1 ==> idx x = 0
      True by field_index_one
*)
val field_index_eq_0 = store_thm(
  "field_index_eq_0",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> ((idx x = 0) <=> (x = #1))``,
  metis_tac[field_index_def, field_exp_0, field_index_one]);

(* Theorem: FiniteField r ==> (idx (primitive r) = if CARD R+ = 1 then 0 else 1) *)
(* Proof:
   Let z = primitive r.
   Then z IN R+                by field_primitive_nonzero
   If CARD R+ = 1,
      Then idx z < CARD R+     by field_index_def
        or idx z < 1
        so idx z = 0           by arithmetic
   If CARD R+ <> 1,
      Then 0 < CARD R+         by field_nonzero_card_pos
        so 1 < CARD R+         by arithmetic
       and z = z ** 1          by field_primitive_element, field_exp_1
        so idx z = 1           by field_index_alt
*)
val field_index_primitive = store_thm(
  "field_index_primitive",
  ``!r:'a field. FiniteField r ==> (idx (primitive r) = if CARD R+ = 1 then 0 else 1)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `z = primitive r` >>
  rw[] >| [
    `idx z < CARD R+` by rw[field_index_def, Abbr`z`] >>
    decide_tac,
    `0 < CARD R+` by rw[field_nonzero_card_pos] >>
    `1 < CARD R+` by decide_tac >>
    `z = z ** 1` by rw[Abbr`z`] >>
    rw[field_index_alt, Abbr`z`]
  ]);

(* Theorem: FiniteField r ==> (idx (-#1) = if char r = 2 then 0 else (CARD R+) DIV 2) *)
(* Proof:
   Note #1 IN R+                      by field_one_nonzero
    so -#1 IN R+                      by field_neg_nonzero
   If char r = 2,
      Then idx (-#1)
         = idx #1                     by finite_field_neg_one
         = 0                          by field_index_one
   If char r <> 2,
      Let m = (CARD R+) DIV 2
      Then 0 < CARD R+                by field_nonzero_card_pos
        so m < CARD R+                by DIV_LESS, 0 < CARD R+, 1 < 2.
      Then -#1 = (primitive r) ** m   by finite_field_neg_one
     Hence idx (-#1) = m              by field_index_alt
*)
val field_index_neg_one = store_thm(
  "field_index_neg_one",
  ``!r:'a field. FiniteField r ==> (idx (-#1) = if char r = 2 then 0 else (CARD R+) DIV 2)``,
  rpt (stripDup[FiniteField_def]) >>
  `-#1 IN R+` by rw[] >>
  rw[] >-
  rw[finite_field_neg_one, field_index_one] >>
  qabbrev_tac `m = (CARD R+) DIV 2` >>
  `m < CARD R+` by rw[field_nonzero_card_pos, DIV_LESS, Abbr`m`] >>
  metis_tac[finite_field_neg_one, field_index_alt]);

(* Theorem: FiniteField r ==> !x y. x IN R+ /\ y IN R+ ==>
            (idx (x * y) = (idx x + idx y) MOD (CARD R+)) *)
(* Proof:
   Let z = primitive r.
   Note z IN R+ /\ (forder z = CARD R+)                 by field_primitive_property

    Now idx x < CARD R+ /\ (x = z ** idx x)             by field_index_def
    and idx y < CARD R+ /\ (y = z ** idx y)             by field_index_def
   Thus x * y = (z ** idx x) * (z ** idx y)
              = z ** (idx x + idx y)                    by field_exp_add
              = z ** ((idx x + idx y) MOD (CARD R+))    by finite_field_exp_mod_order
  Since x * y <> #0                                     by field_mult_eq_zero
    and 0 < CARD R+                                     by field_nonzero_card_pos
    and (idx x + idx y) MOD (CARD R+) < (CARD R+)       by MOD_LESS, 0 < CARD R+
  Hence idx (x * y) = (idx x + idx y) MOD (CARD R+)     by field_index_alt
*)
val field_index_mult = store_thm(
  "field_index_mult",
  ``!r:'a field. FiniteField r ==> !x y. x IN R+ /\ y IN R+ ==>
   (idx (x * y) = (idx x + idx y) MOD (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `z = primitive r` >>
  `z IN R+ /\ (forder z = CARD R+)` by rw[field_primitive_property, Abbr`z`] >>
  `idx x < CARD R+ /\ (x = z ** idx x)` by rw[field_index_def, Abbr`z`] >>
  `idx y < CARD R+ /\ (y = z ** idx y)` by rw[field_index_def, Abbr`z`] >>
  `x IN R /\ y IN R /\ z IN R` by rw[field_nonzero_element] >>
  `x * y = z ** (idx x + idx y)` by metis_tac[field_exp_add] >>
  `_ = z ** ((idx x + idx y) MOD (CARD R+))` by metis_tac[finite_field_exp_mod_order] >>
  `x * y <> #0` by metis_tac[field_mult_eq_zero, field_nonzero_eq] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `(idx x + idx y) MOD (CARD R+) < (CARD R+)` by rw[MOD_LESS] >>
  rw[field_index_alt]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==>
            (idx (-x) = if char r = 2 then (idx x) else (idx x + (CARD R+) DIV 2) MOD (CARD R+)) *)
(* Proof:
   Since x IN R+
     ==> idx x < CARD R+      by field_index_def
    Note -#1 IN R+            by field_one_nonzero, field_neg_nonzero
   Since -x = -(x * #1)       by field_mult_rone
            = x * (-#1)       by field_neg_mult
      so idx (-x)
       = idx (x * (-#1))                     by above
       = (idx x + idx (-#1)) MOD (CARD R+)   by field_index_mult
   If char r = 2,
      Then idx (-x)
         = (idx x + #0) MOD (CARD R+)        by field_index_neg_one
         = (idx x) MOD (CARD R+)             by field_add_rzero
         = idx x                             by LESS_MOD, idx x < CARD R+
   If char r <> 2,
      Then idx (-x)
         = (idx x + CARD R+ DIV 2) MOD (CARD R+)  by field_index_neg_one
*)
val field_index_neg = store_thm(
  "field_index_neg",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==>
     (idx (-x) = if char r = 2 then (idx x) else (idx x + (CARD R+) DIV 2) MOD (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  `idx x < CARD R+` by rw[field_index_def] >>
  `-#1 IN R+` by rw[] >>
  `#1 IN R /\ x IN R` by rw[field_nonzero_element] >>
  `-x = -(x * #1)` by rw[] >>
  `_ = x * (-#1)` by metis_tac[field_neg_mult] >>
  `idx (-x) = (idx x + idx (-#1)) MOD (CARD R+)` by rw_tac std_ss[field_index_mult] >>
  rw_tac std_ss[field_index_neg_one]);

(* ------------------------------------------------------------------------- *)
(* More properties about Constant Polynomial Field                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteRing r ==> !z. pmonic z ==> (CARD RCz = CARD R) *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R   by FiniteRing_def
    Now RingIso up r (PolyModConst r z)       by poly_mod_const_iso_ring
    ==> CARD R = CARD RCz                     by ring_iso_card_eq
*)
val poly_mod_const_subring_card = store_thm(
  "poly_mod_const_subring_card",
  ``!r:'a ring. FiniteRing r ==> !z. pmonic z ==> (CARD RCz = CARD R)``,
  metis_tac[FiniteRing_def, poly_mod_const_iso_ring, ring_iso_card_eq]);

(* Theorem: FiniteField r ==> !z. pmonic z ==> (CARD RCz = CARD R) *)
(* Proof:
   Note FiniteField r ==> Field r /\ FINITE R   by FiniteField_def
    Now FieldIso up r (PolyModConst r z)        by poly_mod_const_iso_field, field_is_ring
    ==> CARD R = CARD RCz                       by field_iso_card_eq
*)
val poly_mod_const_subfield_card = store_thm(
  "poly_mod_const_subfield_card",
  ``!r:'a field. FiniteField r ==> !z. pmonic z ==> (CARD RCz = CARD R)``,
  metis_tac[FiniteField_def, poly_mod_const_iso_field, field_iso_card_eq]);

(* Theorem: FiniteField r ==> !z. monic z /\ ipoly z ==>
              ((PolyModRing r z) <:> (PolyModConst r z) = deg z) *)
(* Proof:
   Note FiniteField (PolyModRing r z)                      by poly_mod_irreducible_finite_field
    and Field (PolyModRing r z)                            by finite_field_is_field
    and Field (PolyModConst r z)                           by poly_mod_const_field
   also subfield (PolyModConst r z) (PolyModRing r z)      by poly_mod_const_subfield_poly_mod
    Now pmonic z                                           by poly_monic_irreducible_property
    and CARD RCz = CARD R                                  by poly_mod_const_subfield_card
   Note FiniteRing r                                       by finite_field_is_finite_ring
    ==> CARD Rz = CARD R ** deg z                          by poly_mod_ring_card
   Thus (PolyModRing r z) <:> (PolyModConst r z) = deg z   by finite_field_over_subfield_dim
*)
val poly_mod_const_subfield_dim = store_thm(
  "poly_mod_const_subfield_dim",
  ``!r:'a field. FiniteField r ==> !z. monic z /\ ipoly z ==>
                ((PolyModRing r z) <:> (PolyModConst r z)) = deg z``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `Field (PolyModRing r z)` by rw[finite_field_is_field] >>
  `Field (PolyModConst r z)` by rw[poly_mod_const_field] >>
  `subfield (PolyModConst r z) (PolyModRing r z)` by rw[poly_mod_const_subfield_poly_mod] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  `CARD RCz = CARD R` by rw[poly_mod_const_subfield_card] >>
  `CARD Rz = CARD R ** deg z` by rw[poly_mod_ring_card, finite_field_is_finite_ring] >>
  metis_tac[finite_field_over_subfield_dim]);

(* This is a major theorem. *)

(* ------------------------------------------------------------------------- *)
(* Extension Field Relation                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define extension of a field to a different type *)
val field_extend_def = Define `
  field_extend (r:'a field) (s:'b field) <=> ?(f:'a -> 'b). subfield (ring_homo_image f r s) s
`;
(* use overloading *)
val _ = overload_on (">=", ``field_extend``);
(*
- field_extend_def;
> val it = |- !r s. r >= s <=> ?f. subfield (ring_homo_image f r s) s : thm
*)

(* Theorem: Field r /\ Field s /\ FieldHomo f r s ==> r >= s *)
(* Proof:
       Field r /\ Field s /\ FieldHomo f r s
   ==> subfield (ring_homo_image f r s) s         by field_homo_subfield
   ==> r >= s    using f                          by field_extend_def
*)
val field_homo_extend = store_thm(
  "field_homo_extend",
  ``!(r:'a field) (s:'b field) f. Field r /\ Field s /\ FieldHomo f r s ==> r >= s``,
  metis_tac[field_extend_def, field_homo_subfield]);

(* Theorem: Field r ==> r >= r  *)
(* Proof:
   Field r ==> FieldHomo I r r     by field_homo_I_refl
   Hence true by field_homo_extend:
   |- !r s f. Field r /\ Field s /\ FieldHomo f r s ==> r >= s
   by taking f = I.
*)
val field_extend_refl = store_thm(
  "field_extend_refl",
  ``!r:'a field. Field r ==> r >= r``,
  metis_tac[field_homo_I_refl, field_homo_extend]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
