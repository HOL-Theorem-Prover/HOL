(* ------------------------------------------------------------------------- *)
(* Integers as a Ring                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ringInteger";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* val _ = load "integerTheory"; *)
open integerTheory;

(* Get dependent theories local *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "ringTheory"; *) *)
(* (* val _ = load "ringIdealTheory"; *) *)
(* val _ = load "quotientRingTheory"; *)
open quotientRingTheory;
open ringIdealTheory;
open ringTheory;
open groupTheory;
open monoidTheory;
open monoidMapTheory groupMapTheory ringMapTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory;

(* (* val _ = load "subgroupTheory"; *) *)
(* val _ = load "quotientGroupTheory"; *)
open subgroupTheory quotientGroupTheory;

(* (* val _ = load "monoidInstancesTheory"; *) *)
(* (* val _ = load "groupInstancesTheory"; *) *)
(* val _ = load "ringInstancesTheory"; *)
open groupInstancesTheory;
open monoidInstancesTheory;
open ringInstancesTheory;


(* ------------------------------------------------------------------------- *)
(* Integer Ring Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   Z*      = Z_ideal
*)
(* Definitions and Theorems (# are exported):

   Integer Ring:
   Z_add_def             |- Z_add = <|carrier := univ(:int); op := (\x y. x + y); id := 0|>
   Z_mult_def            |- Z_mult = <|carrier := univ(:int); op := (\x y. x * y); id := 1|>
   Z_def                 |- Z = <|carrier := univ(:int); sum := Z_add; prod := Z_mult|>

   Z_add_group           |- Group Z_add
   Z_add_abelian_group   |- AbelianGroup Z_add
   Z_mult_monoid         |- Monoid Z_mult
   Z_mult_abelian_monoid |- AbelianMonoid Z_mult
   Z_ring                |- Ring

   Ideals in Integer Ring:
   Z_multiple_def        |- !n. Z_multiple n = {&n * z | z IN univ(:int)}
   Z_ideal_def           |- !n. Z* n = <|carrier := Z_multiple n;
                                             sum := <|carrier := Z_multiple n; op := Z.sum.op; id := Z.sum.id|>;
                                            prod := <|carrier := Z_multiple n; op := Z.prod.op;
                                              id := Z.prod.id|>
                                        |>

   Z_ideal_sum_group     |- !n. Group (Z* n).sum
   Z_ideal_sum_subgroup  |- !n. (Z* n).sum <= Z.sum
   Z_ideal_sum_normal    |- !n. (Z* n).sum << Z.sum
   Z_ideal_thm           |- !n. Z* n << Z

   Integer Quotient Ring isomorphic to Integer Modulo:
   Z_add_inv               |- !z. z IN Z_add.carrier ==> (Z_add.inv z = -z)
   Z_sum_cogen             |- !n. 0 < n ==> !x. x IN Z.sum.carrier ==>
                              ?y. cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y
   Z_sum_coset_eq          |- !n. 0 < n ==> !p. coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier
   Z_multiple_less_neg_eq  |- !n x y. 0 < n /\ x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y)

   Z_ideal_map_element     |- !n j. 0 < n /\ j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
   Z_ideal_map_group_homo  |- !n. 0 < n ==> GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum
   Z_ideal_map_monoid_homo |- !n. 0 < n ==> MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod
   Z_ideal_map_bij         |- !n. 0 < n ==> BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier
   Z_quotient_iso_ZN       |- !n. 0 < n ==> RingIso (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n) (Z / Z* n)

   Integer as Euclidean Ring:
   Z_euclid_ring           |- EuclideanRing Z (Num o ABS)
   Z_principal_ideal_ring  |- PrincipalIdealRing Z
*)

(* ------------------------------------------------------------------------- *)
(* Integer Ring                                                              *)
(* ------------------------------------------------------------------------- *)

(* Integer Additive Group *)
val Z_add_def = Define `
  Z_add = <| carrier := univ(:int);
                  op := \(x:int) (y:int). x + y;
                  id := (0:int)
           |>
`;

(* Integer Multiplicative Monoid *)
val Z_mult_def = Define `
  Z_mult = <| carrier := univ(:int);
                   op := \(x:int) (y:int). x * y;
                   id := (1:int)
            |>
`;

(* Integer Ring *)
val Z_def = Define `
  Z = <| carrier := univ(:int);
             sum := Z_add;
            prod := Z_mult
       |>
`;

(* Theorem: Z_add is a Group. *)
(* Proof: check group axioms:
   (1) x + y IN univ(:int), true.
   (2) x + y + z = x + (y + z), true by INT_ADD_ASSOC.
   (3) 0 IN univ(:int), true.
   (4) 0 + x = x, true by INT_ADD_LID.
   (5) !x. x IN univ(:int) ==> ?y. y IN univ(:int) /\ (y + x = 0)
       Let y = -x, apply INT_ADD_LINV.
*)
val Z_add_group = store_thm(
  "Z_add_group",
  ``Group Z_add``,
  rw_tac std_ss[Z_add_def, group_def_alt] >| [
    rw[],
    rw[INT_ADD_ASSOC],
    rw[],
    rw[],
    qexists_tac `-x` >>
    rw[]
  ]);

(* Theorem: Z_add is an Abelian Group. *)
(* Proof: by Group Z_add and INT_ADD_COMM. *)
val Z_add_abelian_group = store_thm(
  "Z_add_abelian_group",
  ``AbelianGroup Z_add``,
  rw[AbelianGroup_def, Z_add_group, Z_add_def, INT_ADD_COMM]);

(* Theorem: Z_mult is a Monoid. *)
(* Proof: check monoid axioms:
   (1) x * y IN univ(:int), true.
   (2) x * y * z = x * (y * z), true by INT_MUL_ASSOC.
   (3) 1 IN univ(:int), true.
   (4) 1 * x = x, true by INT_MUL_LID.
   (5) x * 1 = x, true by INT_MUL_RID.
*)
val Z_mult_monoid = store_thm(
  "Z_mult_monoid",
  ``Monoid Z_mult``,
  rw_tac std_ss [Z_mult_def, Monoid_def] >>
  rw[INT_MUL_ASSOC]);

(* Theorem: Z_mult is an Abelian Monoid. *)
(* Proof: by Monoid Z_mult and INT_MUL_COMM. *)
val Z_mult_abelian_monoid = store_thm(
  "Z_mult_abelian_monoid",
  ``AbelianMonoid Z_mult``,
  rw[AbelianMonoid_def, Z_mult_monoid, Z_mult_def, INT_MUL_COMM]);

(* Theorem: Z is a Ring. *)
(* Proof: check ring axioms.
   (1) AbelianGroup Z_add, true by Z_add_abelian_group.
   (2) AbelianMonoid Z_mult, true by Z_mult_abelian_monoid.
   (3) Z_add.carrier = univ(:int), true by Z_add_def.
   (4) Z_mult.carrier = univ(:int), true by Z_mult_def.
   (5) Z_mult.op x (Z_add.op y z) = Z_add.op (Z_mult.op x y) (Z_mult.op x z)
       or x * (y + z) = x * y + x * z, true by INT_LDISTRIB.
*)
val Z_ring = store_thm(
  "Z_ring",
  ``Ring Z``,
  rw_tac std_ss [Ring_def, Z_def] >| [
    rw[Z_add_abelian_group],
    rw[Z_mult_abelian_monoid],
    rw[Z_add_def],
    rw[Z_mult_def],
    rw[Z_add_def, Z_mult_def, INT_LDISTRIB]
  ]);

(* ------------------------------------------------------------------------- *)
(* Ideals in Integer Ring                                                    *)
(* ------------------------------------------------------------------------- *)

(* Integer Multiples *)
val Z_multiple_def = Define `Z_multiple (n:num) = {&n * z | z IN univ(:int)}`;

(* Integer Ring Ideals are multiples *)
val Z_ideal_def = Define `
  Z_ideal (n:num) = <| carrier := Z_multiple n;
                           sum := <| carrier := Z_multiple n; op := Z.sum.op; id := Z.sum.id |>;
                          prod := <| carrier := Z_multiple n; op := Z.prod.op; id := Z.prod.id |>
                     |>
`;

(* set overloading *)
val _ = overload_on ("Z*", ``Z_ideal``);

(* Theorem: Group (Z* n).sum *)
(* Proof: check group axioms:
   (1) x + y IN Z_multiple n
       &n * x' + &n * y' = &n * (x' + y') by INT_LDISTRIB, hence true.
   (2) x + y + z = x + (y + z)
       Since t IN Z_multiple n ==> t IN univ(:int),
       this is true by INT_ADD_ASSOC.
   (3) 0 IN Z_multiple n
       true by INT_MUL_RZERO.
   (4) 0 + x = x
       true by INT_ADD_LID.
   (5) ?y. y IN Z_multiple n /\ (y + x = 0)
       Since x = &n * x'
       Let y = &n * (-x')
       Then y IN Z_multiple n,
       y + x = &n * (-x' + x') = 0   by INT_LDISTRIB, INT_ADD_LINV, hence true.
*)
val Z_ideal_sum_group = store_thm(
  "Z_ideal_sum_group",
  ``!n. Group (Z* n).sum``,
  rpt strip_tac >>
  `!t. t IN Z_multiple n ==> t IN univ(:int)` by rw[Z_multiple_def] >>
  rw_tac std_ss[group_def_alt, Z_ideal_def, Z_def, Z_add_def] >| [
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_LDISTRIB],
    rw[INT_ADD_ASSOC],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_RZERO],
    rw[],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    `?x'. x = &n * x'` by metis_tac[] >>
    qexists_tac `&n * (-x')` >>
    `-x' IN univ(:int)` by rw[] >>
    `&n * -x' + &n * x' = &n * (-x' + x')` by rw[INT_LDISTRIB] >>
    `_ = 0` by rw[INT_ADD_LINV] >>
    metis_tac[]
  ]);

(* Theorem: Monoid (Z* n).prod *)
(* Not true: 1 IN Z_multiple n is FALSE. *)
(* Note: Ideal is not a sub-ring. *)

(* Theorem: (Z* n).sum <= Z.sum *)
(* Proof:
   (1) Group (Z* n).sum     true by Z_ideal_sum_group
   (2) Group Z.sum          true by Z_ring, Ring_def
   (3) (Z* n).sum.carrier SUBSET Z.sum.carrier   true by definitions
   (4) (Z* n).sum.op x y = Z.sum.op x y          true by Z_ideal_def
*)
val Z_ideal_sum_subgroup = store_thm(
  "Z_ideal_sum_subgroup",
  ``!n. (Z* n).sum <= Z.sum``,
  rw_tac std_ss[Subgroup_def] >| [
    rw[Z_ideal_sum_group],
    rw[Z_ring, Ring_def, AbelianGroup_def],
    rw[Z_ideal_def, Z_def, Z_add_def],
    rw[Z_ideal_def]
  ]);

(* Theorem: (Z* n).sum << Z.sum *)
(* Proof:
   (1) (Z* n).sum <= Z.sum
       true by Z_ideal_sum_subgroup.
   (2) !a. a IN Z.sum.carrier ==> coset Z.sum a (Z* n).sum.carrier = right_coset Z.sum (Z* n).sum.carrier a
       i.e. IMAGE (\z. a + z) (Z_multiple n) = IMAGE (\z. z + a) (Z_multiple n)
       true by INT_ADD_COMM.
*)
val Z_ideal_sum_normal = store_thm(
  "Z_ideal_sum_normal",
  ``!n. (Z* n).sum << Z.sum``,
  rw[normal_subgroup_alt, coset_def, right_coset_def] >| [
    rw[Z_ideal_sum_subgroup],
    pop_assum mp_tac >>
    rw_tac std_ss[Z_ideal_def, Z_def, Z_add_def] >>
    rw[INT_ADD_COMM]
  ]);

(* Theorem: Z* n is an ideal of Z *)
(* Proof:
   (1) (Z* n).sum <= Z.sum
       true by Z_ideal_sum_subgroup.
   (2) x IN Z_multiple n ==> x * y IN Z_multiple n
       (&n * x') * y = &n * (x' * y)  by INT_MUL_ASSOC, hence true.
   (3) x IN Z_multiple n ==> y * x IN Z_multiple n
       y * (&n * x') = &n * (y * x')  by INT_MUL_ASSOC, INT_MUL_COMM, hence true.
*)
val Z_ideal_thm = store_thm(
  "Z_ideal_thm",
  ``!n. (Z* n) << Z``,
  rw_tac std_ss[ideal_def, Z_ideal_def, Z_def, Z_mult_def] >| [
    `Z.sum = Z_add` by rw[Z_def] >>
    `(Z* n).sum = <|carrier := Z_multiple n; op := Z_add.op; id := Z_add.id|>` by rw[Z_ideal_def] >>
    metis_tac[Z_ideal_sum_subgroup],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_ASSOC],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_ASSOC, INT_MUL_COMM]
  ]);

(* ------------------------------------------------------------------------- *)
(* Integer Quotient Ring isomorphic to Integer Modulo                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Z_add.inv z = -z *)
(* Proof:
   Since -z + z = 0,
   this follows by group_linv_unique.
*)
val Z_add_inv = store_thm(
  "Z_add_inv",
  ``!z. z IN Z_add.carrier ==> (Z_add.inv z = -z)``,
  rpt strip_tac >>
  `Group Z_add` by rw[Z_add_group] >>
  `-z IN Z_add.carrier /\ (Z_add.op (-z) z = Z_add.id)` by rw[Z_add_def] >>
  metis_tac[group_linv_unique]);

(* Theorem: cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y  for some y. *)
(* Proof:
   (Z* n).sum <= Z.sum   by Z_ideal_sum_subgroup
   hence  (coset Z.sum x (Z* n).sum.carrier) IN CosetPartition Z.sum (Z* n).sum  by definitions
   By cogen_def, putting m = cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)
         m IN Z.sum.carrier,
   and   coset Z.sum x (Z* n).sum.carrier = coset Z.sum m (Z* n).sum.carrier
   Hence -x + m IN (Z* n).sum.carrier  by subgroup_coset_eq
   or    -x + m IN Z_multiple n        by Z_ideal_def
   or    -x + m = &n * y               by Z_multiple_def
   or    m = x + &n * y
*)
val Z_sum_cogen = store_thm(
  "Z_sum_cogen",
  ``!n. 0 < n ==> !x. x IN Z.sum.carrier ==> ? y:int. cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y``,
  rpt strip_tac >>
  `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
  `(coset Z.sum x (Z* n).sum.carrier) IN CosetPartition Z.sum (Z* n).sum` by
  (rw[CosetPartition_def, partition_def, inCoset_def] >>
  qexists_tac `x` >>
  rw[EXTENSION] >>
  metis_tac[subgroup_coset_subset]) >>
  `cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) IN Z.sum.carrier /\
   (coset Z.sum x (Z* n).sum.carrier = coset Z.sum (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)) (Z* n).sum.carrier)` by rw[cogen_def] >>
  `Z.sum.op (Z.sum.inv x) (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)) IN (Z* n).sum.carrier` by rw[GSYM subgroup_coset_eq] >>
  `Z.sum = Z_add` by rw[Z_def] >>
  `(Z* n).sum.carrier = Z_multiple n` by rw[Z_ideal_def] >>
  qabbrev_tac `m = (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier))` >>
  `Z_add.op (- x) m IN Z_multiple n` by metis_tac[Z_add_inv] >>
  `Z_add.op (- x) m = (- x) + m` by rw[Z_add_def] >>
  `!y. y IN Z_multiple n ==> ?k. y = &n * k` by rw[Z_multiple_def] >>
  `?k. -x + m = &n * k` by metis_tac[] >>
  `x + &n * k = x + (-x + m)` by rw[] >>
  `_ = (x + -x) + m` by rw[INT_ADD_ASSOC] >>
  `_ = m` by rw[] >>
  metis_tac[]);

(* Theorem: coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier *)
(* Proof:
   Since (Z* n).sum <= Z.sum   by Z_ideal_sum_subgroup
   By subgroup_coset_eq, this is to show:
       Z.sum.op (Z.sum.inv (p % &n)) p IN (Z* n).sum.carrier
   or  -(p % &n) + p IN Z_multiple n
     -(p % &n) + p
   = -(p % &n) + ((p / &n) * &n + p % &n)   by INT_DIVISION
   = -(p % &n) + (p % &n + (p / &n) * &n)   by INT_ADD_COMM
   = -(p % &n) + p % &n + (p / &n) * &n     by INT_ADD_ASSOC
   = (p / &n) * &n                          by INT_ADD_LINV, INT_ADD_LID
   = &n * (p / &n)                          by INT_MUL_COMM
   hence in Z_multiple n.
*)
val Z_sum_coset_eq = store_thm(
  "Z_sum_coset_eq",
  ``!n. 0 < n ==> !p. coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `&n <> 0` by rw[INT_INJ] >>
  `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
  `p IN Z.sum.carrier /\ p % &n IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
  `Z.sum.op (Z.sum.inv (p % &n)) p IN (Z* n).sum.carrier` suffices_by rw[subgroup_coset_eq] >>
  `Z.sum = Z_add` by rw[Z_def] >>
  `Z.sum.op (- (p % &n)) p IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
  `-(p % &n) + p IN Z_multiple n` suffices_by rw_tac std_ss[Z_def, Z_add_def, Z_ideal_def] >>
  `-(p % &n) + p = -(p % &n) + ((p / &n) * &n + p % &n)` by metis_tac[INT_DIVISION] >>
  `_ = -(p % &n) + (p % &n + (p / &n) * &n)` by rw[INT_ADD_COMM] >>
  `_ = -(p % &n) + p % &n + (p / &n) * &n` by rw[INT_ADD_ASSOC] >>
  `_ = (p / &n) * &n` by rw[INT_ADD_LINV, INT_ADD_LID] >>
  `_ = &n * (p / &n)` by rw[INT_MUL_COMM] >>
  rw[Z_multiple_def]);

(* Theorem: x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y) *)
(* Proof:
   By Z_multiple_def, this is to show:
      -&x + &y = &n * z ==> x = y
   or  &y = &n * z + &x ==> x = y
   If z = 0,
      &y = &n * z + &x
         = 0 + &x         by INT_MUL_RZERO
         = &x             by INT_ADD_LID
      hence y = x         by INT_INJ
   If z < 0,
      z < -1 + 1          by INT_ADD_LINV, -1 + 1 = 0
   or z <= -1             by INT_LE_LT1
   &n * z <= &n * -1      by INT_LE_MONO
           = - &n         by INT_NEG_RMUL, INT_MUL_RID
   Now
    x < n means &x < &n    by INT_INJ
   i.e. -&n < -&x          by INT_LT_NEG
   Combining inequalities,
      &n * z <= -&n < -&x  by INT_LET_TRANS
      &n * z < 0 - &x      by INT_SUB_LZERO
   or &n * z + &x < 0      by INT_LT_SUB_LADD
   i.e.        &y < 0
   which contradicts ~(y < 0), y being :num.
   If z > 0,
      0 < z
   or 1 - 1 < z            by INT_SUB_REFL
   or 1 < z + 1            by INT_LT_SUB_RADD
   or 1 <= z               by INT_LE_LT1
      &n * 1 <= &n * z     by INT_LE_MONO
          &n <= &n * z     by INT_MUL_RID
     &n + &x <= &y         by INT_LE_RADD
   Now
     &n <= &n + &x
   Combining inequalities
     &n <= &y              by INT_LE_TRANS
      n <= y               by INT_LE
   but this contradicts y < n
*)
val Z_multiple_less_neg_eq = store_thm(
  "Z_multiple_less_neg_eq",
  ``!n x y. 0 < n /\ x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y)``,
  rw[Z_multiple_def] >>
  `-&x + &y + &x = &n * z + &x` by rw[] >>
  `--&x = &x` by rw[INT_NEGNEG] >>
  `&y = &n * z + &x` by metis_tac[INT_ADD_SUB, int_sub] >>
  Cases_on `z = 0` >| [
    `&y = &x` by metis_tac[INT_MUL_RZERO, INT_ADD_LID] >>
    metis_tac[INT_INJ],
    Cases_on `z < 0` >| [
      `z < -1 + 1` by rw[INT_ADD_LINV] >>
      `z <= -1` by rw[INT_LE_LT1] >>
      `&n * z <= &n * -1` by rw[INT_LE_MONO] >>
      `&n * z <= - (&n * 1)` by rw[INT_NEG_RMUL] >>
      `&n * z <= - &n` by metis_tac[INT_MUL_RID] >>
      `- &n < - &x` by rw[] >>
      `&n * z < - &x` by metis_tac[INT_LET_TRANS] >>
      `&n * z < 0 - &x` by rw[INT_SUB_LZERO] >>
      `&n * z + &x < 0` by rw[GSYM INT_LT_SUB_LADD] >>
      `y < 0` by metis_tac[INT_LT] >>
      decide_tac,
      `0 <= z` by rw[GSYM INT_NOT_LT] >>
      `0 < z` by metis_tac[INT_LE_LT] >>
      `1 - 1 < z` by rw[INT_SUB_REFL] >>
      `1 < z + 1` by rw[INT_LT_SUB_RADD] >>
      `1 <= z` by rw[INT_LE_LT1] >>
      `&n * 1 <= &n * z` by rw[INT_LE_MONO] >>
      `&n <= &n * z` by metis_tac[INT_MUL_RID] >>
      `&n + &x <= &y` by rw[INT_LE_RADD] >>
      `&n <= &n + &x` by rw[] >>
      `&n <= &y` by metis_tac[INT_LE_TRANS] >>
      `n <= y` by rw[GSYM INT_LE] >>
      decide_tac
    ]
  ]);

(* Theorem: j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier *)
(* Proof: by definitions,
   this is to show: 0 < n /\ j < n ==>
   ?x. IMAGE (\z. &j + z) (Z_multiple n) = {y | ?z. (y = x + z) /\ z IN Z_multiple n}
   Just take x = &j.
*)
val Z_ideal_map_element = store_thm(
  "Z_ideal_map_element",
  ``!n j. 0 < n /\ j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier``,
  rw_tac std_ss[quotient_ring_def, coset_def, ZN_def, Z_ideal_def, Z_def, Z_add_def,
     CosetPartition_def, partition_def, inCoset_def, IN_COUNT] >>
  rw[] >>
  qexists_tac `&j` >>
  rw[EXTENSION]);

(* Theorem: GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum *)
(* Proof: by GroupHomo_def, this is to show
   (1) j IN (ZN n).sum.carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).sum.carrier
       Since
       (ZN n).sum.carrier = (ZN n).carrier         by Ring_def, and Ring (ZN n)        by ZN_ring
       (Z / Z* n).sum.carrier = (Z / Z* n).carrier by Ring_def, and Ring (Z / (Z* n))  by quotient_ring_ring
       Hence true by Z_ideal_map_element.
   (2) j IN (ZN n).sum.carrier /\ j' IN (ZN n).sum.carrier ==>
       coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier =
       (Z / Z* n).sum.op (coset Z.sum (&j) (Z* n).sum.carrier) (coset Z.sum (&j') (Z* n).sum.carrier)
       After expanding by definitions, this is to show:
       coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier =
       coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                             (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier
       Since (Z* n).sum << Z.sum     by Z_ideal_sum_normal
       applying normal_coset_property:
       coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                             (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier =
       coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier
       So this is to show:
       coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier = coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier
       By subgroup_coset_eq, this is to show:
       Z.sum.op (Z.sum.inv (Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN  (Z* n).sum.carrier
       or  -(&j + &j') + &((j + j') MOD n) IN Z_multiple n
         -(&j + &j') + &((j + j') MOD n)
       = -&(j + j') + &((j + j') MOD n)     by INT_ADD
       = -&(j + j') + &(j + j') % &n        by INT_MOD
       = -((&(j + j') / &n) * &n + (&(j + j') % &n)) + (&(j + j') % &n)   by INT_DIVISION
       = -((&(j + j') / &n) * &n) - (&(j + j') % &n) + (&(j + j') % &n)   by INT_SUB_LNEG
       = -((&(j + j') / &n) * &n)           by INT_SUB_ADD
       = -(&(j + j') / &n) * &n             by INT_NEG_LMUL
       = &n * -(&(j + j') / &n)             by INT_MUL_COMM]
       Hence in Z_multiple n.
*)
val Z_ideal_map_group_homo = store_thm(
  "Z_ideal_map_group_homo",
  ``!n. 0 < n ==> GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum``,
  rpt strip_tac >>
  `!r. Ring r ==> (r.sum.carrier = R)` by rw_tac std_ss[Ring_def] >>
  rw[GroupHomo_def] >| [
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(Z* n) << Z` by rw[Z_ideal_thm] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (Z / (Z* n))` by rw[quotient_ring_ring] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by rw[] >>
    `(Z / Z* n).sum.carrier = (Z / Z* n).carrier` by rw[] >>
    metis_tac[Z_ideal_map_element],
    rw[quotient_ring_def, quotient_ring_add_def] >>
    `(Z* n).sum << Z.sum` by rw[Z_ideal_sum_normal] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by rw[] >>
    `Z.sum.carrier = Z.carrier` by rw[] >>
    `!k. k IN (ZN n).carrier ==> &k IN Z.carrier` by rw[ZN_def, Z_def] >>
    `&j IN Z.sum.carrier /\ &j' IN Z.sum.carrier` by metis_tac[] >>
    `(Z* n).carrier = (Z* n).sum.carrier` by rw[Z_ideal_def] >>
    `coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                          (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier =
    coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier` by rw[normal_coset_property] >>
    `coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier =
     coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier` suffices_by rw[] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(Z.sum.op (&j) (&j')) IN Z.sum.carrier` by rw[ring_add_group] >>
    `&(ZN n).sum.op j j' IN Z.sum.carrier` by rw[Z_def] >>
    `Z.sum.op (Z.sum.inv (Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN  (Z* n).sum.carrier`
      suffices_by metis_tac[subgroup_coset_eq] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    `(Z.sum = Z_add)` by rw[Z_def] >>
    `Z.sum.op (&j) (&j') IN Z_add.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (&j) (&j') IN Z.sum.carrier ==>
    &(ZN n).sum.op j j' IN Z.sum.carrier ==>
    Z.sum.op (-(Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
    rw_tac std_ss[Z_def, Z_add_def, ZN_def, add_mod_def, Z_ideal_def] >>
    `n <> 0` by decide_tac >>
    `-(&j + &j') + &((j + j') MOD n) = -&(j + j') + &((j + j') MOD n)` by rw[INT_ADD] >>
    `_ = -&(j + j') + &(j + j') % &n` by rw[INT_MOD] >>
    `_ = -((&(j + j') / &n) * &n + (&(j + j') % &n)) + (&(j + j') % &n)` by rw[INT_DIVISION] >>
    `_ = -((&(j + j') / &n) * &n) - (&(j + j') % &n) + (&(j + j') % &n)` by rw[INT_SUB_LNEG] >>
    `_ = -((&(j + j') / &n) * &n)` by rw[INT_SUB_ADD] >>
    `_ = -(&(j + j') / &n) * &n` by rw[INT_NEG_LMUL] >>
    `_ = &n * -(&(j + j') / &n)` by rw[INT_MUL_COMM] >>
    rw[Z_multiple_def]
  ]);

(* Theorem: MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod *)
(* Proof: by MonoidHomo_def, this is to show:
   (1) j IN (ZN n).prod.carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).prod.carrier
       Since (ZN n).prod.carrier = (ZN n).carrier          by Ring_def
             (Z / Z* n).prod.carrier = (Z / Z* n).carrier  by Ring_def
       true by Z_ideal_map_element.
   (2) j IN (ZN n).prod.carrier /\ j' IN (ZN n).prod.carrier ==>
       coset Z.sum (&(ZN n).prod.op j j') (Z* n).sum.carrier =
       (Z / Z* n).prod.op (coset Z.sum (&j) (Z* n).sum.carrier) (coset Z.sum (&j') (Z* n).sum.carrier)
       Since (Z* n).sum <= Z.sum    by Z_ideal_sum_subgroup
       and   ?k. cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier) = &j + &n * k      by Z_sum_cogen
       and   ?k'. cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier) = &j' + &n * k'  by Z_sum_cogen
       By subgroup_coset_eq, this reduces to:
       Z.sum.op (Z.sum.inv (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier
       Now (Z* n).sum.carrier = (Z* n).carrier = Z_multiple n,
         Z.prod.op (&j + &n * k) (&j' + &n * k')
       = (&j + &n * k) * (&j' + &n * k')
       = (&j) * (&j') + &n * h   for some h, by INT_LDISTRIB
       = &(j * j') + &n * h      by INT_MUL
       Hence the difference with &(ZN n).prod.op j j') = &((j * j') MOD n) = &(j * j') % &n
       is a multiple of n, i.e. in (Z* n).sum.carrier.
   (3) coset Z.sum (&(ZN n).prod.id) (Z* n).sum.carrier = (Z / Z* n).prod.id
       Since (Z* n).sum <= Z.sum     by Z_ideal_sum_subgroup
       expand by definition, this is to show:
       coset Z.sum (&(ZN n).prod.id) (Z* n).sum.carrier = coset Z.sum Z.prod.id (Z* n).carrier
       and by subgroup_coset_eq, this is to show:
       Z.sum.op (- Z.prod.id) (&(ZN n).prod.id) IN (Z* n).sum.carrier
       or    - 1 + &(ZN n).prod.id IN (Z* n).sum.carrier
       Since (ZN n).prod.id = if n = 1 then 0 else 1, two cases:
       If n = 1, to show -1 in (Z* 1).sum.carrier = Z_multiple 1, true.
       If n <> 1, to show 0 in (Z* n).sum.carrier = Z_multiple n, true.
*)
val Z_ideal_map_monoid_homo = store_thm(
  "Z_ideal_map_monoid_homo",
  ``!n. 0 < n ==> MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod``,
  rpt strip_tac >>
  rw[MonoidHomo_def] >| [
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(Z* n) << Z` by rw[Z_ideal_thm] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (Z / (Z* n))` by rw[quotient_ring_ring] >>
    `(ZN n).prod.carrier = (ZN n).carrier` by metis_tac[Ring_def] >>
    `(Z / Z* n).prod.carrier = (Z / Z* n).carrier` by metis_tac[Ring_def] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by metis_tac[Ring_def] >>
    metis_tac[Z_ideal_map_element],
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `&j IN Z.sum.carrier /\ &j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `?k. cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier) = &j + &n * k` by rw[Z_sum_cogen] >>
    `?k'. cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier) = &j' + &n * k'` by rw[Z_sum_cogen] >>
    `(Z* n).sum.carrier = (Z* n).carrier` by rw[Z_ideal_def] >>
    `coset Z.sum (&(ZN n).prod.op j j') (Z* n).sum.carrier =
     coset Z.sum (Z.prod.op (&j + &n * k) (&j' + &n * k')) (Z* n).sum.carrier` suffices_by metis_tac[] >>
    `&(ZN n).prod.op j j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.prod.op (&j + &n * k) (&j' + &n * k') IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (Z.sum.inv (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier`
      suffices_by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier`
      suffices_by metis_tac[Z_add_inv] >>
    rw_tac std_ss[Z_def, Z_add_def, Z_mult_def, ZN_def, times_mod_def, Z_ideal_def] >>
    `n <> 0` by decide_tac >>
    `-&((j * j') MOD n) + (&j + &n * k) * (&j' + &n * k') = -(&(j * j') % &n) + (&j + &n * k) * (&j' + &n * k')` by rw[INT_MOD] >>
    `_ = -(&(j * j') % &n) + (&j * (&j' + &n * k') + &n * k * (&j' + &n * k'))` by rw[INT_RDISTRIB] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &j * (&n * k') + &n * k * (&j' + &n * k'))` by rw[INT_LDISTRIB] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &n * k' * &j + &n * k * (&j' + &n * k'))` by rw[INT_MUL_COMM] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + (&n * k' * &j + &n * k * (&j' + &n * k')))` by rw[INT_ADD_ASSOC] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + (&n * (k' * &j) + &n * (k * (&j' + &n * k'))))` by rw[INT_MUL_ASSOC] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &n * (k' * &j + k * (&j' + &n * k')))` by rw[GSYM INT_LDISTRIB] >>
    `_ = -(&(j * j') % &n) + &j * &j' + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_ASSOC] >>
    `_ = -(&(j * j') % &n) + &(j * j') + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_MUL] >>
    `_ = -(&(j * j') % &n) + (&(j * j') / &n * &n + &(j * j') % &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_DIVISION] >>
    `_ = -(&(j * j') % &n) + (&(j * j') % &n + &(j * j') / &n * &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_COMM] >>
    `_ = -(&(j * j') % &n) + &(j * j') % &n + &(j * j') / &n * &n + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_ASSOC] >>
    `_ = &(j * j') / &n * &n + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_LINV] >>
    `_ = &n * (&(j * j') / &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_MUL_COMM] >>
    `_ = &n * (&(j * j') / &n + (k' * &j + k * (&j' + &n * k')))` by rw[INT_LDISTRIB] >>
    rw[Z_multiple_def],
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(Z* n).sum.carrier = (Z* n).carrier` by rw[Z_ideal_def] >>
    `&(ZN n).prod.id IN Z.sum.carrier` by rw[Z_def, Z_add_def, ZN_def, times_mod_def] >>
    `Z.prod.id IN Z.sum.carrier` by rw[Z_def, Z_add_def, Z_mult_def] >>
    `Z.sum.op (Z.sum.inv Z.prod.id) &(ZN n).prod.id IN (Z* n).sum.carrier` suffices_by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- Z.prod.id) (&(ZN n).prod.id) IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
    `n <> 0` by decide_tac >>
    rw[Z_def, Z_add_def, Z_mult_def, ZN_def, times_mod_def] >-
    rw[Z_ideal_def, Z_multiple_def] >>
    rw[Z_ideal_def, Z_multiple_def]
  ]);

(* Theorem: BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier *)
(* Proof:
   (1) j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
       true by Z_ideal_map_element.
   (2) coset Z.sum (&j) (Z* n).sum.carrier = coset Z.sum (&j') (Z* n).sum.carrier ==> j = j'
       &j - &j' = multiple of n, but j < n and j' < n, hence j = j'.
       true by Z_multiple_less_neg_eq.
   (3) same as (1)
   (4) x IN (Z / Z* n).carrier ==> ?j. j IN (ZN n).carrier /\ (coset Z.sum (&j) (Z* n).sum.carrier = x)
       Expanding by definition, this is to show:
       x IN CosetPartition Z.sum (Z* n).sum ==> ?j. j IN (ZN n).carrier /\ (coset Z.sum (&j) (Z* n).sum.carrier = x)
       Let p = (cogen Z.sum (Z* n).sum x, then
            p IN Z.sum.carrier     by cogen_element
       thus p IN univ(:int)        by Z_def, Z_add_def
       By coset_cogen_property, we have:  coset Z.sum p (Z* n).sum.carrier = x
       So it is just choosing j, depending on p, to satisfy: j IN (ZN n).carrier
       If p = 0, take j = 0, then 0 IN (ZN n).carrier,
       If p <> 0, since by Z_sum_coset_eq,
          coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier
       If p > 0, choose j = p MOD n,
       then &j = &(p MOD n) = &p % &n, so true by INT_MOD
       If p < 0, choose j = (n + (p MOD n)) MOD n,
       then &j = &((n + (p MOD n)) MOD n)
               = &(n + (p MOD n)) % &n      by INT_MOD
               = (&n % &n + &(p MOD n) % &n) % &n   by INT_ADD
               = &(p MOD n)                 by INT_MOD_ID, INT_MOD_MOD
               = &p % &n                    by INT_MOD
*)
val Z_ideal_map_bij = store_thm(
  "Z_ideal_map_bij",
  ``!n. 0 < n ==> BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    rw[Z_ideal_map_element],
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `&j IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `&j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (Z.sum.inv &j) &j' IN (Z* n).sum.carrier` by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- &j) &j' IN (Z* n).sum.carrier` by metis_tac[Z_add_inv] >>
    `(Z* n).sum.carrier = Z_multiple n` by rw[Z_ideal_def] >>
    `!x y. Z.sum.op x y = x + y` by rw[Z_def, Z_add_def] >>
    `(- &j) +  &j' IN Z_multiple n` by metis_tac[] >>
    `!x. x IN (ZN n).carrier ==> x < n` by rw[ZN_def] >>
    metis_tac[Z_multiple_less_neg_eq],
    rw[Z_ideal_map_element],
    pop_assum mp_tac >>
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(cogen Z.sum (Z* n).sum x) IN Z.sum.carrier` by rw[cogen_element] >>
    `(cogen Z.sum (Z* n).sum x) IN univ(:int)` by rw[Z_def, Z_add_def] >>
    qabbrev_tac `p = (cogen Z.sum (Z* n).sum x)` >>
    `coset Z.sum p (Z* n).sum.carrier = x` by rw[coset_cogen_property, Abbr`p`] >>
    `!x. x IN (ZN n).carrier <=> x < n` by rw[ZN_def] >>
    Cases_on `p = 0` >| [
      qexists_tac `0` >>
      rw[],
      `n <> 0` by decide_tac >>
      `&n <> 0` by rw[INT_INJ] >>
      `coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier` by rw[GSYM Z_sum_coset_eq] >>
      Cases_on `0 <= p` >| [
        `?k. p = &k` by metis_tac[NUM_POSINT] >>
        qexists_tac `k MOD n` >>
        rw[MOD_LESS, INT_MOD],
        `p < 0` by rw[GSYM INT_NOT_LE] >>
        `?k. p = -&k` by metis_tac[NUM_NEGINT_EXISTS, INT_LT_IMP_LE] >>
        `k MOD n < n` by rw[MOD_LESS] >>
        `p % &n = (- &k) % &n` by rw[] >>
        `_ = (&n - &k) % &n` by rw[INT_MOD_NEG_NUMERATOR] >>
        `_ = (&n % &n - &k % &n) % &n` by rw[INT_MOD_SUB] >>
        `_ = (&n % &n - &k % &n % &n) % &n` by rw[INT_MOD_MOD] >>
        `_ = (&n % &n - &(k MOD n) % &n) % &n` by rw[INT_MOD] >>
        `_ = (&n  - &(k MOD n)) % &n` by rw[INT_MOD_SUB] >>
        `_ = &(n - k MOD n) % &n` by rw[INT_SUB, LESS_IMP_LESS_OR_EQ] >>
        `_ = &((n - k MOD n) MOD n)` by rw[INT_MOD] >>
        qexists_tac `(n - k MOD n) MOD n` >>
        rw[MOD_LESS]
      ]
    ]
  ]);

(* Theorem: (ZN n) isomorphic to Z / (Z* n) *)
(* Proof:
   The bijection is: j IN (ZN n) -> coset (Z* n).sum (&j) (Z* n).sum.carrier
   where (Z* n).sum.carrier = Z_multiple n
   (1) j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
       true by Z_ideal_map_element.
   (2) GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum
       true by Z_ideal_map_group_homo.
   (3) MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod
       true by Z_ideal_map_monoid_homo.
   (4) BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier
       true by Z_ideal_map_bij.
*)
val Z_quotient_iso_ZN = store_thm(
  "Z_quotient_iso_ZN",
  ``!n. 0 < n ==> RingIso (\(j:num). coset Z.sum (&j) (Z* n).sum.carrier) (ZN n) (Z / (Z* n))``,
  rw[RingIso_def, RingHomo_def] >-
  rw[Z_ideal_map_element] >-
  rw[Z_ideal_map_group_homo] >-
  rw[Z_ideal_map_monoid_homo] >>
  rw[Z_ideal_map_bij]);

(* ------------------------------------------------------------------------- *)
(* Integer as Euclidean Ring.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EuclideanRing Z *)
(* Proof:
   By EuclideanRing_def, this is to show:
   (1) Ring Z, true       by Z_ring
   (2) (Num (ABS x) = 0) <=> (x = 0)
       If part: Num (ABS x) = 0 ==> x = 0
       If ABS x = &n, n <> 0, Num (&n) = n  by NUM_OF_INT, or n = 0, contradicts n <> 0.
       If ABS x = -&n, n <> 0, then -&n < 0, contradicts ~(ABS x < 0) by INT_ABS_LT0.
       If ABS x = 0, this means ABS x <= 0, hence x = 0 by INT_ABS_LE0.
       Only-if part: x = 0 ==> Num (ABS x) = 0
       i.e to show: Num (ABS 0) = 0
         Num (ABS 0)
       = Num 0            by INT_ABS_EQ0, ABS 0 = 0
       = 0                by NUM_OF_INT, Num (&n) = n
   (3) !x y. y <> 0 ==> ?q t. (x = q * y + t) /\ Num (ABS t) < Num (ABS y)
       Let q = x / y, t = x % y.
       Then by INT_DIVISION,
       (x = q * y + t) /\ if y < 0 then (y < t /\ t <= 0) else (0 <= t /\ t < y)
       If y = &n, n <> 0, then ~(y < 0), hence 0 <= t /\ t < y
       0 <= t ==> ?k. t = &k       by NUM_POSINT
       So   Num (ABS t) = k        by INT_ABS_NUM, NUM_OF_INT
       and  Num (ABS y) = n        by INT_ABS_NUM, NUM_OF_INT
       and  &k < &n ==> k < n      by INT_LT
       If y = -&n, n <> 0, then y < 0, hence y < t /\ t <= 0
       t <= 0 ==> ?k. t = -&k      by NUM_NEGINT_EXISTS
       But  Num (ABS t) = k        by INT_ABS_NEG, INT_ABS_NUM, NUM_OF_INT
       and  Num (ABS y) = n        by INT_ABS_NEG, INT_ABS_NUM, NUM_OF_INT
       and  -&n < -&k
         ==> &k < &n               by INT_LT_CALCULATE
         ==> k < n                 by INT_LT (or INT_LT_CALCULATE)
*)

Theorem Z_euclid_ring: EuclideanRing Z Num
Proof
  rw[EuclideanRing_def]
  >- rw[Z_ring]
  >- rw[Z_def, Z_add_def] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[Z_def, Z_add_def, Z_mult_def] >>
  qexists_tac ‘x / y’ >>
  qexists_tac ‘x % y’ >>
  ‘(x = x / y * y + x % y) /\
   if y < 0 then (y < x % y /\ x % y <= 0) else (0 <= x % y /\ x % y < y)’
    by rw[INT_DIVISION] >>
  qabbrev_tac ‘q = x / y’ >>
  qabbrev_tac ‘t = x % y’ >>
  ‘(?n. (y = &n) /\ n <> 0) \/ (?n. (y = -&n) /\ n <> 0) \/ (y = 0)’
    by rw[INT_NUM_CASES]
  >- (‘~(y < 0)’ by rw[] >>
      ‘0 <= t /\ t < y’ by metis_tac[] >>
      ‘?k. t = &k’ by metis_tac[NUM_POSINT] >>
      gvs[]) >>
  ‘y < 0’ by rw[] >>
  ‘y < t /\ t <= 0’ by metis_tac[] >>
  ‘?k. t = -&k’ by metis_tac[NUM_NEGINT_EXISTS] >>
  gvs[]
QED

(* Theorem: PrincipalIdealRing Z *)
(* Proof:
   Since EuclideanRing Z (Num o ABS)   by Z_euclid_ring
   hence PrincipalIdealRing Z          by euclid_ring_principal_ideal_ring
*)
val Z_principal_ideal_ring = store_thm(
  "Z_principal_ideal_ring",
  ``PrincipalIdealRing Z``,
  metis_tac[Z_euclid_ring, euclid_ring_principal_ideal_ring]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
