(* ------------------------------------------------------------------------- *)
(* Field Extension.                                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffExtend";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     gcdsetTheory numberTheory combinatoricsTheory cardinalTheory;

(* Get dependent theories local *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffMinimalTheory;
open ffConjugateTheory;
open ffExistTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open fieldMapTheory;

open fieldInstancesTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;
open polyMonicTheory;
open polyDividesTheory;
open polyProductTheory;
open polyRootTheory;
open polyIrreducibleTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;
open polyMapTheory;

(* ------------------------------------------------------------------------- *)
(* Field Extension Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   C            = (t:'a field).carrier
   generator    = field_generator r
   generators   = field_generators
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   CARD_EQ_BIJ                |- !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t
   CARD_EQ_INJ                |- !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. INJ f s t /\ (IMAGE f s = t)
   INJ_FINITE_INFINITE        |- !s. FINITE s /\ INFINITE univ(:'b) ==> ?f. INJ f s univ(:'b)
   INFINITE_UNIV_DIFF_FINITE  |- !s. FINITE s /\ INFINITE univ(:'a) ==> INFINITE (univ(:'a) DIFF s)
   finite_subset_exists       |- !t n. INFINITE t ==> ?s. s SUBSET t /\ FINITE s /\ (CARD s = n)

   Extending Finite Set:
   subset_inj_extension_exists  |- !s t f. FINITE t /\ s SUBSET t /\ INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
                                   ?g. INJ g t univ(:'b) /\ !x. x IN s ==> (g x = f x)
   subset_inj_extension_def     |- !s t f. FINITE t /\ s SUBSET t /\
                                           INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
                                           INJ (subset_inj_extension s t f) t univ(:'b) /\
                                           !x. x IN s ==> (subset_inj_extension s t f x = f x)
   finite_super_set_exists      |- !s. FINITE s /\ INFINITE univ(:'a) ==>
                                   !n. CARD s <= n ==> ?t. FINITE t /\ s SUBSET t /\ (CARD t = n)

   Extending Finite Field:
   finite_field_clone_extension_exists
                                |- !r. FiniteField r /\ INFINITE univ(:'b) ==> !n. 0 < n ==>
                                   ?r_ s_ f. FiniteField r_ /\ FiniteField s_ /\ FieldIso f r s_ /\
                                             s_ <<= r_ /\ (CARD R_ = CARD R ** n)
   finite_field_self_extension_exists
                                |- !r. FiniteField r /\ INFINITE univ(:'a) ==> !n. 0 < n ==>
                                   ?r_ s_ f. FiniteField r_ /\ FiniteField s_ /\ FieldIso f r s_ /\
                                              s_ <<= r_ /\ (CARD r_.carrier = CARD R ** n)
   subfield_ring_inj_image_subfield  |- !r s f. s <<= r /\ INJ f R univ(:'a) ==>
                                                subfield (ring_inj_image s f) (ring_inj_image r f)
   field_iso_with_subfield_ring_inj_image_subfield
                                     |- !r s t f g. (r === s) f /\ ring_inj_image s g <<= t /\
                                                    (!x. x IN B ==> (g x = LINV f R x)) ==> subfield r t
   finite_field_extension_exists     |- !r. FiniteField r /\ INFINITE univ(:'a) ==>
                                        !n. 0 < n ==> ?t. FiniteField t /\ r <<= t /\ (CARD C = CARD R ** n)

   Extension Field of Polynomial:
   finite_field_irreducible_extension_exists
                                     |- !r. FiniteField r /\ INFINITE univ(:'b) ==>
                                        !p. ipoly p /\ 1 < deg p ==>
                                        ?r_ f b. FieldHomo f r r_ /\ b IN R_ /\ root_ p_ b
   finite_field_irreducible_iso_extension_exists
                                     |- !r. FiniteField r /\ INFINITE univ(:'b) ==>
                                        !p. ipoly p /\ 1 < deg p ==>
                                        ?s r_ f b. FieldIso f r s /\ s <<= r_ /\
                                                   FINITE R_ /\ b IN R_ /\ root_ p_ b
   poly_extension_field_exists       |- !r. FiniteField r /\ INFINITE univ(:'a) ==>
                                        !p. poly p /\ 0 < deg p ==>
                                        ?s t f b. FieldIso f r s /\ s <<= t /\
                                                  FINITE C /\ b IN C /\ poly_root t (MAP f p) b
   poly_extension_field_exists_alt   |- !r. FiniteField r /\ INFINITE univ(:'a) ==>
                                        !p. poly p /\ 0 < deg p ==>
                                        ?s t f b. FieldIso f r s /\ s <<= t /\
                                                  FINITE C /\ b IN poly_roots t (MAP f p)

   Finite Field Generators:
   field_generator_def      |- !r s z. generator s z <=> (IMAGE (\p. eval p z) (PolyRing s).carrier = R)
   field_generators_def     |- !r s. generators r s = {z | z IN R /\ field_generator r s z}
   field_generator_alt      |- !r s. s <= r ==> !z. z IN R ==>
                                     (generator s z <=> !x. x IN R ==> ?p. Poly s p /\ (x = eval p z))
   field_generators_member  |- !r s z. z IN generators r s <=> z IN R /\ generator s z
   field_primitives_subset_field_generators
                            |- !r s. FiniteField r /\ s <<= r ==> FPrimitives r SUBSET generators r s
   field_primitive_in_field_generators  |- !r s. FiniteField r /\ s <<= r ==> primitive r IN generators r s
   field_primitive_is_field_generator   |- !r s. FiniteField r /\ s <<= r ==> generator s (primitive r)

   Finite Field Isomorphism by Minimal Polynomial of generator:
   poly_mod_ring_by_minimal_sum_homo    |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                                 GroupHomo (\p. eval p x) (PolyModRing s (minimal x)).sum r.sum
   poly_mod_ring_by_minimal_prod_homo   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                                 MonoidHomo (\p. eval p x) (PolyModRing s (minimal x)).prod r.prod
   poly_mod_ring_by_minimal_homo_field  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                                 FieldHomo (\p. eval p x) (PolyModRing s (minimal x)) r
   poly_mod_ring_by_minimal_map_inj     |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                                 INJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
   poly_mod_ring_by_minimal_map_surj    |- !r s. FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
                                                 SURJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
   poly_mod_ring_by_minimal_map_bij     |- !r s. FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
                                                 BIJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
   poly_mod_ring_by_minimal_iso_field   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
                                                 FieldIso (\p. eval p x) (PolyModRing s (minimal x)) r
   poly_mod_ring_by_minimal_field_iso   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
                                                 (PolyModRing s (minimal x) === r) (\p. eval p x)
   poly_mod_ring_by_minimal_finite_field        |- !r s. FiniteField r /\ s <<= r ==>
                                                   !x. x IN R ==> FiniteField (PolyModRing s (minimal x))
   poly_mod_ring_by_minimal_field_isomorphism   |- !r s. FiniteField r /\ s <<= r ==>
                                                   !x. x IN generators r s ==> r =ff= PolyModRing s (minimal x)
   poly_mod_ring_by_primitive_minimal_field_iso |- !r s. FiniteField r /\ s <<= r ==>
                                      (PolyModRing s (minimal (primitive r)) === r) (\p. eval p (primitive r))
   poly_mod_ring_by_primitive_minimal_field_isomorphism
                                                |- !r s. FiniteField r /\ s <<= r ==>
                                                         r =ff= PolyModRing s (minimal (primitive r))
   poly_mod_ring_by_primitives_element_field_iso
                                       |- !r s z. FiniteField r /\ s <<= r /\ z IN FPrimitives r ==>
                                                  (PolyModRing s (minimal z) === r) (\p. eval p z)
   poly_mod_ring_by_primitives_element_field_isomorphism
                                       |- !r s z. FiniteField r /\ s <<= r /\ z IN FPrimitives r ==>
                                                  r =ff= PolyModRing s (minimal z)

   Uniqueness of Finite Field by Isomorphisms
   finite_field_eq_card_field_iso       |- !r r_. FiniteField r /\ FiniteField r_ /\
                                                  (CARD R = CARD R_) ==> r =ff= r_
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note: These theorems require cardinalTheory. *)
(* Note: helperSet is basic, no cardinalTheory. *)

(* Theorem: FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t *)
(* Proof: by CARD_CARDEQ_I, cardeq_def *)
val CARD_EQ_BIJ = store_thm(
  "CARD_EQ_BIJ",
  ``!s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t``,
  rw[CARD_CARDEQ_I, GSYM cardeq_def]);

(* Theorem: FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. INJ f s t /\ (IMAGE f s = t) *)
(* Proof:
   Note ?f. BIJ f s t                 by CARD_EQ_BIJ
     or INJ f s t /\ SURJ f s t       by BIJ_DEF
     or INJ f s t /\ (IMAGE f s = t)  by IMAGE_SURJ
*)
val CARD_EQ_INJ = store_thm(
  "CARD_EQ_INJ",
  ``!s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. INJ f s t /\ (IMAGE f s = t)``,
  rpt strip_tac >>
  `?f. INJ f s t /\ SURJ f s t` by metis_tac[CARD_EQ_BIJ, BIJ_DEF] >>
  qexists_tac `f` >>
  rw[GSYM IMAGE_SURJ]);

(* Theorem: FINITE s /\ INFINITE univ(:'b) ==> ?f. INJ f s univ(:'b) *)
(* Proof:
   Note ?t:'b -> bool. FINITE t /\ (CARD t = CARD s)   by finite_set_exists
     so ?f. INJ f s t                                  by CARD_EQ_INJ
   Since      s SUBSET s                               by SUBSET_REFL
     and      t SUBSET univ(:'b)                       by SUBSET_UNIV
   Hence    INJ f s univ(:'b)                          by INJ_SUBSET
*)
val INJ_FINITE_INFINITE = store_thm(
  "INJ_FINITE_INFINITE",
  ``!s. FINITE s /\ INFINITE univ(:'b) ==> ?f. INJ f s univ(:'b)``,
  metis_tac[finite_set_exists, CARD_EQ_INJ, INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV]);

(* Theorem: FINITE s /\ INFINITE univ(:'a) ==> INFINITE (univ(:'a) DIFF s) *)
(* Proof:
   By contradiction, suppose FINITE (univ(:'a) DIFF s).
   Note s SUBSET univ(:'a)                       by SUBSET_UNIV
     so univ(:'a) = (univ(:'a) DIFF s) UNION s   by UNION_DIFF
    ==> FINITE univ(:'a)                         by FINITE_UNION
   But this contradicts INFINITE univ(:'a).
*)
val INFINITE_UNIV_DIFF_FINITE = store_thm(
  "INFINITE_UNIV_DIFF_FINITE",
  ``!s. FINITE s /\ INFINITE univ(:'a) ==> INFINITE (univ(:'a) DIFF s)``,
  spose_not_then strip_assume_tac >>
  `univ(:'a) = (univ(:'a) DIFF s) UNION s` by rw[UNION_DIFF, SUBSET_UNIV] >>
  metis_tac[FINITE_UNION]);

(* Theorem: INFINITE t ==> ?s. s SUBSET t /\ FINITE s /\ (CARD s = n) *)
(* Proof:
    Note INFINITE t
     ==> ?f. INJ f univ(:num) t            by infinite_num_inj
      or     INJ f (count n) t             by INJ_SUBSET, SUBSET_UNIV, SUBSET_REFL
    Take s = IMAGE f (count n), this is to show:
    (1) IMAGE f (count n) SUBSET t, true   by IMAGE_SUBSET_TARGET, INJ_DEF
    (2) FINITE (IMAGE f (count n)), true   by FINITE_COUNT, IMAGE_FINITE
    (3) CARD (IMAGE f (count n)) = n
        Note FINITE (count n)              by FINITE_COUNT
          CARD (IMAGE f (count n))         by notation
        = CARD (count n)                   by INJ_CARD_IMAGE_EQ
        = n                                by CARD_COUNT
*)
val finite_subset_exists = store_thm(
  "finite_subset_exists",
  ``!(t:'a -> bool) n. INFINITE t ==> ?s. s SUBSET t /\ FINITE s /\ (CARD s = n)``,
  rpt strip_tac >>
  `?f. INJ f univ(:num) t` by rw[GSYM infinite_num_inj] >>
  `INJ f (count n) t` by metis_tac[INJ_SUBSET, SUBSET_UNIV, SUBSET_REFL] >>
  qexists_tac `IMAGE f (count n)` >>
  rpt strip_tac >-
  metis_tac[IMAGE_SUBSET_TARGET, INJ_DEF] >-
  rw[] >>
  metis_tac[INJ_CARD_IMAGE_EQ, FINITE_COUNT, CARD_COUNT]);

(* ------------------------------------------------------------------------- *)
(* Extending Finite Set                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE t /\ s SUBSET t /\ INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
            ?g. INJ g t univ(:'b) /\ !x. x IN s ==> (g x = f x) *)
(* Proof:
   Let d = t DIFF s, m = IMAGE f s.
   Then FINITE d                           by FINITE_DIFF
    and FINITE s                           by SUBSET_FINITE
    and FINITE m                           by IMAGE_FINITE
    but INFINITE (univ(:'b) DIFF m)        by INFINITE_UNIV_DIFF_FINITE
    ==> ?e:'b -> bool. e SUBSET (univ(:'b) DIFF m) /\ FINITE e /\ (CARD e = CARD d)   by finite_subset_exists
   also ?g. INJ g d e /\ (IMAGE g d = e)   by CARD_EQ_INJ
   Take this split function: \x. if (x IN s) then f x else g x.
   This is to show:
   (1) INJ (\x. if x IN s then f x else g x) t univ(:'b)
       By INJ_DEF, this is to show: x IN t /\ x' IN t ==> x = x'
       Note e = IMAGE g d.
       If x IN s,
          If x' IN s, then f x = f x' ==> x = x', true    by INJ_DEF
          If ~(x' IN s) to show f x = g x' ==> x = x'.
             Note x' IN d                                 by IN_DIFF
               so f x IN m and g x' IN e                  by IN_IMAGE
             Note e SUBSET (univ(:'b) DIFF m)             by above
             Thus g x' NOTIN m                            by IN_DIFF, SUBSET_DEF
             This contradicts g x' = f x, but f x IN m.
       If ~(x IN s),
          If x' IN s, to show g x = f x' ==> x = x'.
             Note x IN d                                  by IN_DIFF
               so g x IN e and f x' IN m                  by IN_IMAGE
             Note e SUBSET (univ(:'b) DIFF m)             by above
             Thus g x NOTIN m                             by IN_DIFF, SUBSET_DEF
             This contradicts g x = f x', but f x' IN m.
          If ~(x' IN s), then g x = g x' ==> x = x', true by INJ_DEF, IN_DIFF
   (2) x IN s ==> (\x. if x IN s then f x else g x) x = f x
       This is trivially true.
*)
val subset_inj_extension_exists = store_thm(
  "subset_inj_extension_exists",
  ``!s t f. FINITE t /\ s SUBSET t /\ INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
   ?g. INJ g t univ(:'b) /\ !x. x IN s ==> (g x = f x)``,
  rpt strip_tac >>
  qabbrev_tac `d = t DIFF s` >>
  qabbrev_tac `m = IMAGE f s` >>
  `FINITE d` by rw[Abbr`d`] >>
  `FINITE s /\ FINITE m` by metis_tac[SUBSET_FINITE, IMAGE_FINITE] >>
  `INFINITE (univ(:'b) DIFF m)` by rw[INFINITE_UNIV_DIFF_FINITE] >>
  `?e:'b -> bool. e SUBSET (univ(:'b) DIFF m) /\ FINITE e /\ (CARD e = CARD d)` by rw[finite_subset_exists] >>
  `?g. INJ g d e /\ (IMAGE g d = e)` by rw[CARD_EQ_INJ] >>
  qexists_tac `\x. if (x IN s) then f x else g x` >>
  rpt strip_tac >| [
    rw[INJ_DEF] >>
    qabbrev_tac `e = IMAGE g d` >>
    Cases_on `x IN s` >| [
      Cases_on `x' IN s` >-
      metis_tac[INJ_DEF] >>
      `f x IN m` by rw[Abbr`m`] >>
      `g x' IN e` by rw[Abbr`e`,Abbr`d`] >>
      metis_tac[IN_DIFF, SUBSET_DEF],
      Cases_on `x' IN s` >| [
        `x IN d` by rw[Abbr`d`] >>
        `g x IN e` by rw[Abbr`e`] >>
        `f x' IN m` by rw[Abbr`m`] >>
        metis_tac[IN_DIFF, SUBSET_DEF],
        metis_tac[INJ_DEF, IN_DIFF]
      ]
    ],
    rw[]
  ]);

(* Apply Skolemization *)
val lemma = prove(
  ``!s t f. ?g. FINITE t /\ s SUBSET t /\ INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
                INJ g t univ(:'b) /\ !x. x IN s ==> (g x = f x)``,
  metis_tac[subset_inj_extension_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(*
- SIMP_RULE (bool_ss) [SKOLEM_THM] lemma;
- lemma |> SIMP_RULE bool_ss [SKOLEM_THM];
*)
(* Define injection extended for subset. *)
val subset_inj_extension_def = new_specification(
    "subset_inj_extension_def",
    ["subset_inj_extension"],
    lemma |> SIMP_RULE bool_ss [SKOLEM_THM]
          |> CONV_RULE (RENAME_VARS_CONV ["g"] (* to allow rename of f' back to f *)
                        THENC BINDER_CONV (RENAME_VARS_CONV ["s", "t", "f"])));
(*
> val subset_inj_extension_def =
   |- !s t f. FINITE t /\ s SUBSET t /\ INJ f s univ(:'b) /\ INFINITE univ(:'b) ==>
     INJ (subset_inj_extension s t f) t univ(:'b) /\
     !x. x IN s ==> (subset_inj_extension s t f x = f x): thm
*)

(* Theorem: FINITE s /\ INFINITE univ(:'a) ==>
            !n. CARD s <= n ==> ?t. FINITE t /\ (s SUBSET t) /\ (CARD t = n) *)
(* Proof:
   Let m = CARD s.
   Note ?f. BIJ f (count m) s                       by eqcard_bij_exists
    ==> INJ f (count m) s /\ SURJ f (count m) s     by BIJ_DEF
   thus INJ f (count m) univ(:'a)                   by INJ_UNIV
    and IMAGE f (count m) = s                       by IMAGE_SURJ

    Now m <= n                                      by given
     so (count m) SUBSET (count n)                  by SUBSET_DEF, IN_COUNT
    ==> ?g. INJ g (count n) univ(:'a) /\
        !x. x IN (count m) ==> (g x = f x)          by subset_inj_extension_exists

    Let t = IMAGE g (count n). This is to show:
    (1) FINITE (IMAGE g (count n))
        Since FINITE (count n)                      by FINITE_COUNT
           so FINITE (IMAGE g (count n))            by IMAGE_FINITE
    (2) s SUBSET IMAGE g (count n)
        Note (IMAGE g (count m)) SUBSET (IMAGE g (count n))   by IMAGE_SUBSET
         and IMAGE g (count m)
           = IMAGE f (count m)                      by IN_IMAGE, EXTENSION
           = s                                      by above, IMAGE_SURJ
    (3) CARD (IMAGE g (count n)) = n
        Since FINITE (count n)                      by FINITE_COUNT
           so CARD (IMAGE g (count n))
            = CARD (count n)                        by INJ_CARD_IMAGE
            = n                                     by CARD_COUNT
*)
val finite_super_set_exists = store_thm(
  "finite_super_set_exists",
  ``!s:'a -> bool. FINITE s /\ INFINITE univ(:'a) ==>
   !n. CARD s <= n ==> ?t. FINITE t /\ (s SUBSET t) /\ (CARD t = n)``,
  rpt strip_tac >>
  qabbrev_tac `m = CARD s` >>
  `?f. BIJ f (count m) s` by rw[eqcard_bij_exists, Abbr`m`] >>
  `INJ f (count m) s /\ SURJ f (count m) s` by metis_tac[BIJ_DEF] >>
  `INJ f (count m) univ(:'a)` by metis_tac[INJ_UNIV] >>
  `IMAGE f (count m) = s` by rw[GSYM IMAGE_SURJ] >>
  `(count m) SUBSET (count n)` by rw[SUBSET_DEF] >>
  `?g. INJ g (count n) univ(:'a) /\ !x. x IN (count m) ==> (g x = f x)` by rw[subset_inj_extension_exists] >>
  qexists_tac `IMAGE g (count n)` >>
  rpt strip_tac >-
  rw[] >-
 ((`IMAGE g (count m) = IMAGE f (count m)` by (rw_tac std_ss[IN_IMAGE, EXTENSION] >> metis_tac[])) >>
  metis_tac[IMAGE_SUBSET]) >>
  metis_tac[INJ_CARD_IMAGE, FINITE_COUNT, CARD_COUNT]);

(* ------------------------------------------------------------------------- *)
(* Extending Finite Field                                                    *)
(* ------------------------------------------------------------------------- *)

(*
> ffAdvancedTheory.field_extend_def;
val it = |- !r s f. (r <= s) f <=> subfield (ring_homo_image f r s) s: thm
> ffAdvancedTheory.field_extend_refl;
val it = |- !r. Field r ==> (r <= r) I: thm
> ffAdvancedTheory.field_homo_extend;
val it = |- !r s f. Field r /\ Field s /\ FieldHomo f r s ==> (r <= s) f: thm
*)

(* The extension of GF(2) to GF(4):

The GF(2) is simple:   add x y = (x + y) MOD 2,  mult x y = (x * y) MOD 2,
or     + | 0 1      * | 0 1
      ---+-----    ---+-----
       0 | 0 1      0 | 0 0
       1 | 1 0      1 | 0 1

To construct GF(4), need a monic irreducible GF(2) polynomial of degree 2.
The 2^2 = 4 condidates are:
x^2 + 0x + 0 = x^2 = (x - 0)(x - 0) = (x - 0)^2
x^2 + 0x + 1 = x^2 + 1 = (x + 1)^2 = (x - 1)^2
x^2 + 1x + 0 = x^2 + x = x (x + 1) = (x - 0)(x - 1)
x^2 + 1x + 1 = x^2 + x + 1,  0 not a root, 1 not a root, so it is irreducible (by degree 2).

In binary tuple, GF(4) is:
    + | 00 01 10 11       * | 00 01 10 11
   ---+-------------     ---+-------------
   00 | 00 01 10 11      00 | 00 00 00 00
   01 | 01 00 11 10      01 | 00 01 10 11
   10 | 10 11 00 01      10 | 00 10 11 01
   11 | 11 10 01 00      11 | 00 11 01 10

Converting binary tuple to ordinary numbers:
    + | 0  1  2  3       * | 0  1  2  3
   ---+-------------    ---+-------------
    0 | 0  1  2  3       0 | 0  0  0  0
    1 | 1  0  3  2       1 | 0  1  2  3
    2 | 2  3  0  1       2 | 0  2  3  1
    3 | 3  2  1  0       3 | 0  3  1  2

Thus in GF(4), add x y = decimal ((binary x) xor (binary y)),
              mult x y = if (x == 0) then 0 else if (y == 0) then 0 else 1 + (((x - 1) + (y - 1)) MOD 3)
Thus on the surface, GF(2) is not a subfield of GF(4), since they involve different operations.
However, if x, y are restricted to 0, 1 = GF(2),
         GF(4).add x y = GF(2).add x y
        GF(4).mult x y = GF(2).mult x y
Thus in this sense, GF(2) is a subfield of GF(4).
*)

(* ------------------------------------------------------------------------- *)
(* Field Extension Existence                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload on field extensin carrier *)
val _ = overload_on ("C", ``(t:'a field).carrier``);

(* Theorem: FiniteField r /\ INFINITE univ(:'b) ==>
            !n. 0 < n ==> ?(r_:'b field) (s_:'b field) f. FiniteField r_ /\ FiniteField s_ /\
            FieldIso f r s_ /\ s_ <<= r_ /\ (CARD R_ = (CARD R) ** n) *)
(* Proof:
   Note ?p m. prime p /\ 0 < m /\ (CARD R = p ** m)     by finite_field_card_eq_prime_power
     so 0 < m * n                                       by ZERO_LESS_MULT
    and ?(r_:'b field). FiniteField r_ /\
        CARD R_ = p ** (m * n)                          by finite_field_existence
     or CARD R_ = (p ** m) ** n = (CARD R) ** n         by EXP_EXP_MULT
   Note m divides (m * n)                               by divides_def, MULT_COMM
    ==> ?(s_:'b field). Field s_ /\
          s_ <<= r_ /\ (CARD S_ = p ** m)               by finite_field_subfield_existence
    and FiniteField s_                                  by subfield_finite_field
   With CARD R = p ** m = CARD S_                       by above
     so r =f= s_                                        by finite_field_eq_card_isomorphic
*)
val finite_field_clone_extension_exists = store_thm(
  "finite_field_clone_extension_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'b) ==>
   !n. 0 < n ==> ?(r_:'b field) (s_:'b field) f. FiniteField r_ /\ FiniteField s_ /\
      FieldIso f r s_ /\ s_ <<= r_ /\ (CARD R_ = (CARD R) ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  `?p m. prime p /\ 0 < m /\ (CARD R = p ** m)` by rw[finite_field_card_eq_prime_power] >>
  `?(r_:'b field). FiniteField r_ /\ (CARD R_ = p ** (m * n))` by rw[finite_field_existence, ZERO_LESS_MULT] >>
  `CARD R_ = (CARD R) ** n` by rw[EXP_EXP_MULT] >>
  `m divides (m * n)` by metis_tac[divides_def, MULT_COMM] >>
  `?(s_:'b field). Field s_ /\ s_ <<= r_ /\ (CARD S_ = p ** m)` by metis_tac[finite_field_subfield_existence] >>
  `FiniteField s_` by metis_tac[subfield_finite_field] >>
  metis_tac[finite_field_eq_card_isomorphic]);

(* Theorem: FiniteField r /\ INFINITE univ(:'a) ==>
            !n. 0 < n ==> ?(t:'a field) (s:'a field) f. FiniteField t /\ FiniteField s /\
                          FieldIso f r s /\ s <<= t /\ (CARD C = (CARD R) ** n) *)
(* Proof: by finite_field_clone_extension_exists, matching types. *)
(* Better use theorem type transform *)
val finite_field_self_extension_exists =
    save_thm("finite_field_self_extension_exists",
              finite_field_clone_extension_exists |> INST_TYPE [beta |-> alpha]);

(* Theorem: s <<= r /\ INJ f R univ(:'a) ==> subfield (ring_inj_image s f) (ring_inj_image r f) *)
(* Proof:
   Note B SUBSET R                                             by subfield_carrier_subset
     so (IMAGE f B) SUBSET (IMAGE f R)                         by SUBSET_DEF, IN_IMAGE
    and INJ f B univ(:'a)                                      by INJ_SUBSET, SUBSET_REFL

   Claim 1: !z. z IN IMAGE f B ==> (LINV f B z) IN B
   Proof: By INJ_LINV_OPT, this is to show:
          x IN B ==> LINV f B (f x) IN B, true                 by LINV_DEF

   Claim 2: !z. z IN IMAGE f B ==> (LINV f B z = LINV f R z)
   Proof: By IN_IMAGE, this is to show:
          x' IN B ==> LINV f B (f x') = LINV f R (f x'), true  by LINV_DEF, SUBSET_DEF

   Expanding by subfield_def, FieldHomo_def, RingHomo_def, ring_inj_image_carrier, this is to show:
   (1) x IN IMAGE f B ==> x IN IMAGE f R, true       by SUBSET_DEF
   (2) GroupHomo I (ring_inj_image s f).sum (ring_inj_image r f).sum
       By GroupHomo_def, ring_inj_image_def, this is to show:
       (1) x IN IMAGE f B ==> x IN IMAGE f R, true   by SUBSET_DEF
       (2) x IN IMAGE f B /\ y IN IMAGE f B ==>
           f (s.sum.op (LINV f R x) (LINV f R y)) = f (LINV f R x + LINV f R y)
                                              true   by subfield_property_alt
   (3) MonoidHomo I (ring_inj_image s f).prod (ring_inj_image r f).prod
       By MonoidHomo_def, ring_inj_image_def, this is to show:
       (1) x IN IMAGE f B ==> x IN IMAGE f R, true   by SUBSET_DEF
       (2) x IN IMAGE f B /\ y IN IMAGE f B ==>
           f (s.prod.op (LINV f R x) (LINV f R y)) = f (LINV f R x * LINV f R y)
                                              true   by subfield_property_alt
       (3) f s.prod.id = f #1, true                  by subfield_ids
*)
val subfield_ring_inj_image_subfield = store_thm(
  "subfield_ring_inj_image_subfield",
  ``!(r s:'a field) f. s <<= r /\ INJ f R univ(:'a) ==> subfield (ring_inj_image s f) (ring_inj_image r f)``,
  rpt strip_tac >>
  `B SUBSET R` by rw[subfield_carrier_subset] >>
  `(IMAGE f B) SUBSET (IMAGE f R)` by rw[SUBSET_DEF] >>
  `INJ f B univ(:'a)` by metis_tac[INJ_SUBSET, SUBSET_REFL] >>
  `!z. z IN IMAGE f B ==> (LINV f B z) IN B` by
  (rw[INJ_LINV_OPT] >>
  metis_tac[LINV_DEF]) >>
  `!z. z IN IMAGE f B ==> (LINV f B z = LINV f R z)` by
    (rw[] >>
  metis_tac[LINV_DEF, SUBSET_DEF]) >>
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def, ring_inj_image_carrier] >-
  metis_tac[SUBSET_DEF] >-
 (rw_tac std_ss[GroupHomo_def, ring_inj_image_def] >-
  metis_tac[SUBSET_DEF] >>
  metis_tac[subfield_property_alt]) >>
  rw_tac std_ss[MonoidHomo_def, ring_inj_image_def] >-
  metis_tac[SUBSET_DEF] >-
  metis_tac[subfield_property_alt] >>
  metis_tac[subfield_ids]);

(* Theorem: (r === s) f /\ (ring_inj_image s g) <<= t /\
            (!x. x IN B ==> (g x = LINV f R x)) ==> subfield r t *)
(* Proof:
   Note FieldIso r s ==> BIJ f R B                   by FieldIso_def
   Thus IMAGE f R = B                                by BIJ_DEF, IMAGE_SURJ
   Also (ring_inj_image s g).carrier = IMAGE g B     by ring_inj_image_carrier
     so (IMAGE g B) SUBSET C                         by subfield_carrier_subset, above

   Claim 1: !z. z IN R ==> z IN (ring_inj_image s g).carrier
   Proof: Since (ring_inj_image s g).carrier = IMAGE g B,
          By IN_IMAGE, this is to show: ?x. (z = g x) /\ x IN B
          Now f z IN B                               by IN_IMAGE, B = IMAGE f R
           so g (f z) = LINV f R (f z)               by implication
                      = z                            by BIJ_LINV_THM

   Note FieldIso (LINV f R) s r                      by field_iso_sym
    ==> FieldIso g s r                               by field_iso_cong, implication
    ==> FieldHomo g s r /\ BIJ g B R                 by FieldIso_def, FieldIso g s r

   Claim 2: !z. z IN R ==> LINV g B z IN B
   Proof: Note f z IN B                              by IN_IMAGE, B = IMAGE f R
          Thus LINV g B z IN B                       by field_iso_inverse_element, FieldIso g s r

   Expand by subfield_def, FieldHomo_def, RingHomo_def, ring_inj_image_carrier, this is to show:
   (1) x IN R ==> x IN C, true                       by SUBSET_DEF, IMAGE g B SUBSET C
   (2) GroupHomo I r.sum t.sum
       Expand by GroupHomo_def, field_carriers, this is to show:
       (1) x IN R ==> x IN C, true                   by SUBSET_DEF
       (2) x IN R /\ y IN R ==> x + y = t.sum.op x y
             t.sum.op x y
           = (ring_inj_image s g).sum.op x y         by subfield_property_alt
           = g (s.sum.op (LINV g B x) (LINV g B y))  by ring_inj_image_def
           = g (LINV g B x) + g (LINV g B y)         by field_homo_property, FieldHomo g s r
           = x + y                                   by BIJ_LINV_THM, BIJ g B R
   (3) MonoidHomo I r.prod t.prod
       Expand by MonoidHomo_def, field_carriers, this is to show:
       (1) x IN R ==> x IN C, true                   by SUBSET_DEF
       (2) x IN R /\ y IN R ==> x * y = t.prod.op x y
             t.prod.op x y
           = (ring_inj_image s g).prod.op x y        by subfield_property_alt
           = g (s.prod.op (LINV g B x) (LINV g B y)) by ring_inj_image_def
           = g (LINV g B x) * g (LINV g B y)         by field_homo_property, FieldHomo g s r
           = x * y                                   by BIJ_LINV_THM, BIJ g B R
       (3) #1 = t.prod.id
             t.prod.id
           = (ring_inj_image s g).prod.id            by subfield_ids
           = g (s.prod.id)                           by ring_inj_image_def
           = #1                                      by field_homo_ids, FieldHomo g s r
*)
val field_iso_with_subfield_ring_inj_image_subfield = store_thm(
  "field_iso_with_subfield_ring_inj_image_subfield",
  ``!(r:'a field) (s:'a field) (t:'a field) f g. (r === s) f /\ (ring_inj_image s g) <<= t /\
      (!x. x IN B ==> (g x = LINV f R x)) ==> subfield r t``,
  rpt strip_tac >>
  `BIJ f R B` by metis_tac[FieldIso_def] >>
  `IMAGE f R = B` by fs[BIJ_DEF, IMAGE_SURJ] >>
  `(ring_inj_image s g).carrier = IMAGE g B` by rw[ring_inj_image_carrier] >>
  `(IMAGE g B) SUBSET C` by metis_tac[subfield_carrier_subset] >>
  `!z. z IN R ==> z IN (ring_inj_image s g).carrier` by
  (rw[] >>
  metis_tac[IN_IMAGE, BIJ_LINV_THM]) >>
  `FieldIso (LINV f R) s r` by rw[field_iso_sym] >>
  `FieldIso g s r` by metis_tac[field_iso_cong] >>
  `FieldHomo g s r /\ BIJ g B R` by metis_tac[FieldIso_def] >>
  `!z. z IN R ==> LINV g B z IN B` by
    (rw[] >>
  metis_tac[IN_IMAGE, field_iso_inverse_element]) >>
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def, ring_inj_image_carrier] >-
  metis_tac[SUBSET_DEF] >-
 (rw_tac std_ss[GroupHomo_def, field_carriers] >-
  metis_tac[SUBSET_DEF] >>
  `t.sum.op x y = (ring_inj_image s g).sum.op x y` by rw[GSYM subfield_property_alt] >>
  `_ = g (s.sum.op (LINV g B x) (LINV g B y))` by rw_tac std_ss[ring_inj_image_def] >>
  `_ = g (LINV g B x) + g (LINV g B y)` by rw[field_homo_property] >>
  `_ = x + y` by metis_tac[BIJ_LINV_THM] >>
  rw[]) >>
  rw_tac std_ss[MonoidHomo_def, field_carriers] >-
  metis_tac[SUBSET_DEF] >-
 (`t.prod.op x y = (ring_inj_image s g).prod.op x y` by rw[GSYM subfield_property_alt] >>
  `_ = g (s.prod.op (LINV g B x) (LINV g B y))` by rw_tac std_ss[ring_inj_image_def] >>
  `_ = g (LINV g B x) * g (LINV g B y)` by rw[field_homo_property] >>
  `_ = x * y` by metis_tac[BIJ_LINV_THM] >>
  rw[]) >>
  `t.prod.id = (ring_inj_image s g).prod.id` by rw[subfield_ids] >>
  `_ = g (s.prod.id)` by rw_tac std_ss[ring_inj_image_def] >>
  `_ = #1` by rw_tac std_ss[field_homo_ids] >>
  rw[]);

(* Theorem: FiniteField r /\ INFINITE univ(:'a) ==>
            !n. 0 < n ==> ?(t:'a field). FiniteField t /\ r <<= t /\ (CARD C = (CARD R) ** n) *)
(* Proof:
   Step 1: Clone an extension field of FiniteField r.
   With the given conditions,
   ?(u:'a field) (v:'a field) f. FiniteField u /\ FiniteField v /\ FieldIso f r v /\
            subfield v u /\ (CARD u.carrier = (CARD R ** n))   by finite_field_clone_extension_exists
   Note FiniteField u ==> Field u /\ FINITE u.carrier          by FiniteField_def
    and FiniteField v ==> Field v                              by finite_field_is_field
   also FieldIso f r v ==> FieldIso (LINV f R) v r             by field_iso_sym

   Step 2: Extension (LINV f R) on v.carrier to u.carrier.
   Claim: ?g. INJ g u.carrier univ(:'a) /\ !x. x IN v.carrier ==> (g x = (LINV f R) x)
   Proof: By subset_inj_extension_exists, this is to show:
          (1) v.carrier SUBSET u.carrier, true                 by subfield_carrier_subset
          (2) INJ (LINV f R) v.carrier univ(:'a)
              Note BIJ (LINV f R) v.carrier R                  by FieldIso_def, FieldIso (LINV f R) v r
                so INJ (LINV f R) v.carrier R                  by BIJ_DEF
                or INJ (LINV f R) v.carrier univ(:'a)          by INJ_UNIV

   Note INJ (LINV f R) v.carrier univ(:'a)                     by Claim
    ==> INJ g v.carrier univ(:'a)                              by INJ_SUBSET, subfield_carrier_subset, SUBSET_REFL
    and Field (ring_inj_image v g)                             by field_inj_image_field, INJ g v.carrier univ(:'a)
    and Field (ring_inj_image u g)                             by field_inj_image_field, INJ g u.carrier univ(:'a)

   Step 3: Copy back as extension field (ring_inj_image u g).
   Take t = ring_inj_image u g, this is to show:
   (1) FiniteField (ring_inj_image u g), true                  by field_inj_image_finite_field
   (2) Field (ring_inj_image u g), true                        by field_inj_image_finite_field, finite_field_is_field
   (3) Field r                                                 by given
   (4) subfield r (ring_inj_image u g)
       Note subfield v u
        ==> subfield (ring_inj_image v g) (ring_inj_image u g) by subfield_ring_inj_image_subfield
       Thus subfield r (ring_inj_image u g)                    by field_iso_with_subfield_ring_inj_image_subfield
   (5) CARD (ring_inj_image u g).carrier = CARD R ** n
         CARD (ring_inj_image u g).carrier
       = CARD (IMAGE g u.carrier)                              by ring_inj_image_carrier
       = CARD (u.carrier)                                      by INJ_CARD_IMAGE, FINITE u.carrier
       = CARD R ** n                                           by above
*)
val finite_field_extension_exists = store_thm(
  "finite_field_extension_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'a) ==>
   !n. 0 < n ==> ?(t:'a field). FiniteField t /\ r <<= t /\ (CARD C = (CARD R) ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  `?(u:'a field) (v:'a field) f. FiniteField u /\ FiniteField v /\ FieldIso f r v /\
            v <<= u /\ (CARD u.carrier = (CARD R ** n))` by metis_tac[finite_field_clone_extension_exists] >>
  `Field u /\ FINITE u.carrier /\ Field v` by metis_tac[FiniteField_def] >>
  `FieldIso (LINV f R) v r` by metis_tac[field_iso_sym] >>
  `?g. INJ g u.carrier univ(:'a) /\ !x. x IN v.carrier ==> (g x = (LINV f R) x)` by
  ((irule subset_inj_extension_exists >> rpt conj_tac >> simp[]) >-
  rw[subfield_carrier_subset] >>
  metis_tac[FieldIso_def, BIJ_DEF, INJ_UNIV]
  ) >>
  `INJ g v.carrier univ(:'a)` by metis_tac[INJ_SUBSET, subfield_carrier_subset, SUBSET_REFL] >>
  `Field (ring_inj_image v g)` by rw[field_inj_image_field] >>
  `Field (ring_inj_image u g)` by rw[field_inj_image_field] >>
  qexists_tac `ring_inj_image u g` >>
  rpt strip_tac >-
  rw[field_inj_image_finite_field] >-
  rw[field_inj_image_finite_field, finite_field_is_field] >-
  rw[] >-
  metis_tac[subfield_ring_inj_image_subfield, field_iso_with_subfield_ring_inj_image_subfield] >>
  metis_tac[ring_inj_image_carrier, INJ_CARD_IMAGE]);

(* This is a major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Extension Field of Polynomial                                             *)
(* ------------------------------------------------------------------------- *)


(* Extension field is a combination of field isomorphism and subfield homomorphism. *)

(*
poly_mod_const_homo_field
|- !r. Field r ==> !z. pmonic z ==> FieldHomo (\e. up e) r (PolyModConst r z)

finite_field_clone_exists
|- !r. FiniteField r /\ INFINITE univ(:'b) ==> ?r_ f. FiniteField r_ /\ FieldIso f r r_
*)

(* Theorem: FiniteField r /\ INFINITE univ(:'b) ==> !p. ipoly p /\ 1 < deg p ==>
            ?(r_:'b field) f b. FieldHomo f r r_ /\ b IN R_ /\ (root_ p_ b) *)
(* Proof:
   Let t = PolyModRing r p, st = PolyModConst r p.
   Note FiniteField t            by poly_mod_irreducible_finite_field, FiniteField r
    and FiniteField st           by poly_mod_const_finite_field, FiniteField r
   Also FieldHomo up r st        by poly_mod_const_homo_field_alt
    and subfield st t            by poly_mod_const_subfield_poly_mod
    ==> FieldHomo I st t         by subfield_def
    ==> FieldHomo (I o up) r t   by field_homo_compose
    ==> FieldHomo up r t         by I_o_ID

   Since INFINITE univ(:'b)                 by given
     ==> ?r_:'b field g. FiniteField r_ /\
                FieldIso g t r_             by finite_field_clone_exists, FiniteField t
    Thus FieldHomo (g o up) r r_            by field_homo_iso_homo

   Note poly_root t (lift p) X              by poly_monic_irreducible_lift_has_root_X
    and poly p                              by poly_irreducible_poly
     so Poly t (lift p)                     by poly_mod_lift_poly
   Also poly X                              by poly_X
    ==> X IN t.carrier                      by poly_mod_ring_element, deg p <> 0
    ==> g X IN R_                           by field_iso_element
   Thus root_ (MAP g (lift p)) (g X)        by field_iso_poly_root
    But MAP g (lift p) = MAP (g o up) p     by poly_lift_def, MAP_COMPOSE
   Take f = g o up, b = g X, the result follows.
*)
val finite_field_irreducible_extension_exists = store_thm(
  "finite_field_irreducible_extension_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'b) ==>
   !p. ipoly p /\ 1 < deg p ==>
       ?(r_:'b field) f b. FieldHomo f r r_ /\ b IN R_ /\ (root_ p_ b)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = PolyModRing r p` >>
  qabbrev_tac `st = PolyModConst r p` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `FiniteField st` by rw[poly_mod_const_finite_field, Abbr`st`] >>
  `FieldHomo up r st` by rw[poly_mod_const_homo_field_alt, Abbr`st`] >>
  `subfield st t` by rw[poly_mod_const_subfield_poly_mod, Abbr`st`, Abbr`t`] >>
  `FieldHomo I st t` by rw[GSYM subfield_def] >>
  `FieldHomo (I o up) r t` by prove_tac[field_homo_compose] >>
  `?r_:'b field g. FiniteField r_ /\ FieldIso g t r_` by rw[finite_field_clone_exists] >>
  `FieldHomo (g o up) r r_` by metis_tac[field_homo_iso_homo] >>
  `poly_root t (lift p) X` by rw[poly_irreducible_lift_has_root_X, Abbr`t`] >>
  `Poly t (lift p)` by rw[poly_mod_lift_poly, poly_irreducible_poly, Abbr`t`] >>
  `X IN t.carrier` by rw[poly_mod_ring_element, Abbr`t`] >>
  `g X IN R_` by metis_tac[field_iso_element] >>
  `root_ (MAP g (lift p)) (g X)` by metis_tac[field_iso_poly_root, finite_field_is_field] >>
  `MAP g (lift p) = MAP (g o up) p` by rw[poly_lift_def, MAP_COMPOSE] >>
  metis_tac[]);

(* We can clone a finite field (from finite_set_clone_exists):
finite_field_clone_exists
|- !r. FiniteField r /\ INFINITE univ(:'b) ==>?r_ f. FiniteField r_ /\ FieldIso f r r_

Can we clone an infinite field?
The FiniteField r in the following is purely due to finite_field_clone_exists.
*)

(* Theorem: FiniteField r /\ INFINITE univ(:'b) ==> !p. monic p /\ ipoly p /\ 1 < deg p ==>
   ?(s:'b field) (r_:'b field) f b. FieldIso f r s /\ s <<= r_ /\ FINITE R_ /\ b IN R_ /\ (root_ p_ b) *)
(* Proof:
   Part 1: the polynomial fields.
   Let t = PolyModRing r p, st = PolyModConst r p.
   Note FiniteField t            by poly_mod_irreducible_finite_field, FiniteField r
    and FiniteField st           by poly_mod_const_finite_field, FiniteField r
    Now pmonic p                 by poly_irreducible_pmonic, ipoly p
    ==> FieldIso up r st         by poly_mod_const_iso_field, pmonic p
    and st <<= t                 by poly_mod_const_subfield_poly_mod_alt

   Part 2: the clones.
   Since INFINITE univ(:'b)                 by given
     ==> ?r_:'b field g. FiniteField r_ /\
                FieldIso g t r_             by finite_field_clone_exists, FiniteField t
     ==> Field r_ /\ FINITE R_              by FiniteField_def
   Let s = ring_homo_image g st r_.
   Then (st === s) g                        by field_iso_subfield_iso
    and s <<= r_                            by subfield_field_iso_ring_homo_subfield
   With FieldIso up r st /\ FieldIso g st s,
    ==> FieldIso (g o up) r s               by field_iso_compose

   Part 3: the root.
   Note poly_root t (lift p) X              by poly_irreducible_lift_has_root_X
    and poly p                              by poly_irreducible_poly
     so Poly t (lift p)                     by poly_mod_lift_poly
   Also poly X                              by poly_X
    ==> X IN t.carrier                      by poly_mod_ring_element, deg p <> 0
    ==> g X IN R_                           by field_iso_element
   Thus root_ (MAP g (lift p)) (g X)        by field_iso_poly_root
    But MAP g (lift p) = MAP (g o up) p     by poly_lift_def, MAP_COMPOSE
   Take f = g o up, b = g X, the result follows.
*)
val finite_field_irreducible_iso_extension_exists = store_thm(
  "finite_field_irreducible_iso_extension_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'b) ==>
   !p. ipoly p /\ 1 < deg p ==>
    ?(s:'b field) (r_:'b field) f b. FieldIso f r s /\ s <<= r_ /\ FINITE R_ /\ b IN R_ /\ (root_ p_ b)``,
  rpt (stripDup[FiniteField_def]) >>
  `pmonic p` by rw[poly_irreducible_pmonic] >>
  qabbrev_tac `t = PolyModRing r p` >>
  qabbrev_tac `st = PolyModConst r p` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `FiniteField st` by rw[poly_mod_const_finite_field, Abbr`st`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod_alt, Abbr`st`, Abbr`t`] >>
  `?r_:'b field g. FiniteField r_ /\ FieldIso g t r_` by rw[finite_field_clone_exists] >>
  `Field r_ /\ FINITE R_` by metis_tac[FiniteField_def] >>
  qabbrev_tac `s = ring_homo_image g st r_` >>
  `(st === s) g` by metis_tac[field_iso_subfield_iso] >>
  `s <<= r_` by metis_tac[subfield_field_iso_ring_homo_subfield] >>
  `FieldIso (g o up) r s` by metis_tac[field_iso_compose] >>
  `poly_root t (lift p) X` by rw[poly_irreducible_lift_has_root_X, Abbr`t`] >>
  `Poly t (lift p)` by rw[poly_mod_lift_poly, poly_irreducible_poly, Abbr`t`] >>
  `X IN t.carrier` by rw[poly_mod_ring_element, Abbr`t`] >>
  `g X IN R_` by metis_tac[field_iso_element] >>
  `root_ (MAP g (lift p)) (g X)` by metis_tac[field_iso_poly_root] >>
  `MAP g (lift p) = MAP (g o up) p` by rw[poly_lift_def, MAP_COMPOSE] >>
  metis_tac[]);

(* Theorem: FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
            ?(s:'a field) (t:'a field) f b.
            FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN C /\ (poly_root t (MAP f p) b) *)
(* Proof:
   If roots p = {},
      Note poly p /\ 0 < deg p                      by given
       ==> ?q. ipoly q /\ q pdivides p              by poly_irreducible_factor_exists
       and poly q                                   by poly_irreducible_poly
       and roots q SUBSET roots p                   by poly_divides_share_roots
       ==> roots q = {}                             by SUBSET_EMPTY, roots p = {}
      Thus deg q <> 1                               by poly_roots_field_deg1, NOT_SING_EMPTY
       Now 0 < deg q                                by poly_irreducible_deg_nonzero, ipoly q
       ==> 1 < deg q                                by 0 < deg q /\ deg q <> 1
      Thus ?(s:'a field) (t:'a field) f b.
           FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN C /\
           (poly_root t (MAP f q) b)                by finite_field_irreducible_iso_extension_exists
       Note FieldIso f r s
        ==> poly_divides s (MAP f q) (MAP f p)      by field_iso_poly_divides
        and Poly s (MAP f q) /\ Poly s (MAP f p)    by field_iso_poly
       Also s <= t                                  by subfield_is_subring, s <<= t
       Thus poly_divides t (MAP f q) (MAP f p)      by subring_poly_divides
        and Poly t (MAP f q) /\ Poly t (MAP f p)    by subring_poly_poly
        ==> poly_root t (MAP f p) b                 by poly_divides_share_root, poly_root t (MAP f q) b
      Take This s and t, the result follows.

   If roots p <> {},
      Then ?x. x IN R /\ root p x                   by poly_roots_member, MEMBER_NOT_EMPTY
      Note FieldIso I r r                           by field_iso_I_refl
       and r <<= r                                  by subfield_refl
      also MAP I p = p                              by MAP_ID
      Take s = r, t = r, the result follows.
*)
val poly_extension_field_exists = store_thm(
  "poly_extension_field_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
   ?(s:'a field) (t:'a field) f b.
       FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN C /\ (poly_root t (MAP f p) b)``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `roots p = {}` >| [
    `?q. ipoly q /\ q pdivides p` by rw[poly_irreducible_factor_exists] >>
    `poly q` by rw[poly_irreducible_poly] >>
    `roots q SUBSET roots p` by rw[poly_divides_share_roots] >>
    `roots q = {}` by metis_tac[SUBSET_EMPTY] >>
    `deg q <> 1` by metis_tac[poly_roots_field_deg1, NOT_SING_EMPTY] >>
    `0 < deg q` by rw[poly_irreducible_deg_nonzero] >>
    `1 < deg q` by decide_tac >>
    `?(s:'a field) (t:'a field) f b. FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN C /\
     (poly_root t (MAP f q) b)` by rw[finite_field_irreducible_iso_extension_exists] >>
    `poly_divides s (MAP f q) (MAP f p)` by metis_tac[field_iso_poly_divides] >>
    `Poly s (MAP f q) /\ Poly s (MAP f p)` by metis_tac[field_iso_poly] >>
    `s <= t` by rw[subfield_is_subring] >>
    `poly_divides t (MAP f q) (MAP f p)` by metis_tac[subring_poly_divides] >>
    `Poly t (MAP f q) /\ Poly t (MAP f p)` by metis_tac[subring_poly_poly] >>
    metis_tac[poly_divides_share_root],
    `?x. x IN R /\ root p x` by rw[GSYM poly_roots_member, MEMBER_NOT_EMPTY] >>
    `FieldIso I r r` by rw[field_iso_I_refl] >>
    `r <<= r` by rw[subfield_refl] >>
    `MAP I p = p` by rw[] >>
    metis_tac[]
  ]);

(* Theorem: FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
    ?(s:'a field) (t:'a field) f b. FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN (poly_roots t (MAP f p)) *)
(* Proof: by poly_extension_field_exists, poly_roots_member *)
val poly_extension_field_exists_alt = store_thm(
  "poly_extension_field_exists_alt",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
   ?(s:'a field) (t:'a field) f b.
       FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN (poly_roots t (MAP f p))``,
  metis_tac[poly_extension_field_exists, poly_roots_member]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Generators                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define generator of a field, relative to a subfield *)
val field_generator_def = Define`
    field_generator (r:'a field) (s:'a field) (z:'a) =
       (IMAGE (\p. eval p z) (PolyRing s).carrier = R)
`;
(* Note: p is a subfield polynomial, with coefficients in subfield s. *)

(* Define generator set of a field, relative to a subfield *)
val field_generators_def = Define`
    field_generators (r:'a field) (s:'a field) = {z | z IN R /\ field_generator r s z}
`;

(* Overload field generator and generators set *)
val _ = overload_on("generator", ``field_generator r``);
val _ = overload_on("generators", ``field_generators``);

(* Theorem: s <= r ==> !z. z IN R ==>
            (generator s z <=> !x. x IN R ==> ?p. Poly s p /\ (x = eval p z)) *)
(* Proof:
   By field_generator_def, EXTENSION, IN_IMAGE, poly_ring_element, this is to show:
   (1) x IN R ==> ?p. Poly s p /\ (x = eval p z), true by implication
   (2) Poly s p ==> eval p z IN R
       Note poly p                 by subring_poly_poly
        and eval p a IN R          by poly_eval_element
   (3) x IN R ==> ?p. (x = eval p z) /\ Poly s p, true by implication
*)
val field_generator_alt = store_thm(
  "field_generator_alt",
  ``!(r:'a ring) s. s <= r ==> !z. z IN R ==>
     (generator s z <=> !x. x IN R ==> ?p. Poly s p /\ (x = eval p z))``,
  rw_tac std_ss[field_generator_def, EXTENSION, IN_IMAGE, poly_ring_element, EQ_IMP_THM] >-
  metis_tac[] >-
 (`poly p` by metis_tac[subring_poly_poly] >>
  rw[]) >>
  metis_tac[]);

(* Theorem: z IN generators r s <=> z IN R /\ generator s z *)
(* Proof: by field_generators_def *)
val field_generators_member = store_thm(
  "field_generators_member",
  ``!(r:'a ring) (s:'a ring). !z. z IN generators r s <=> z IN R /\ generator s z``,
  rw[field_generators_def]);

(* Theorem: FiniteField r /\ s <<= r ==> (FPrimitives r) SUBSET field_generators r s *)
(* Proof:
   By field_generators_def, SUBSET_DEF, this is to show:
      !x. x IN FPrimitives r ==> x IN R /\ generator r s x
   Note s <= r                by subfield_is_subring
    and x IN R                by field_primitives_element, field_nonzero_element
   By field_generator_alt, this is to show:
      !y. y IN R ==> ?p. Poly s p /\ (y = eval p x)
   If y = #0,
      Take p = |0|.
      Then Poly s |0|        by poly_zero_spoly
       and eval |0| x = #0   by poly_eval_zero
   If y <> #0,
      Then y IN R+                            by field_nonzero_eq
       ==> ?n. n < CARD R+ /\ (y = x ** n)    by field_primitives_element_property
      Take p = X ** n.
      Then Poly s p          by poly_X_exp_n_spoly
       and eval p x
         = eval (X ** n) x   by p = X ** n
         = x ** n            by poly_eval_X, poly_eval_exp
         = y                 by above
*)
val field_primitives_subset_field_generators = store_thm(
  "field_primitives_subset_field_generators",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (FPrimitives r) SUBSET field_generators r s``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[field_generators_def, SUBSET_DEF] >>
  `s <= r` by rw[subfield_is_subring] >>
  `x IN R` by metis_tac[field_primitives_element, field_nonzero_element] >>
  `!y. y IN R ==> ?p. Poly s p /\ (y = eval p x)` suffices_by rw[field_generator_alt] >>
  rpt strip_tac >>
  Cases_on `y = #0` >| [
    qexists_tac `|0|` >>
    rw_tac std_ss[poly_zero_spoly, poly_eval_zero],
    `y IN R+` by rw[field_nonzero_eq] >>
    `?n. n < CARD R+ /\ (y = x ** n)` by rw[field_primitives_element_property] >>
    qexists_tac `X ** n` >>
    rw[poly_X_exp_n_spoly]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> (primitive r) IN generators r s *)
(* Proof:
   Let z = primitive r.
   Then z IN FPrimitives r                    by field_primitives_has_primitive
    and FPrimitives r SUBSET generators r s   by field_primitives_subset_field_generators
   Thus z IN generators r s                   by SUBSET_DEF
*)
val field_primitive_in_field_generators = store_thm(
  "field_primitive_in_field_generators",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (primitive r) IN field_generators r s``,
  metis_tac[field_primitives_has_primitive, field_primitives_subset_field_generators, SUBSET_DEF]);

(* Theorem: FiniteField r /\ s <<= r ==> generator s (primitive r) *)
(* Proof:
   Let z = primitive r.
   Note z IN generators r s    by field_primitive_in_field_generators
   Thus generator s z          by field_generators_member
*)
val field_primitive_is_field_generator = store_thm(
  "field_primitive_is_field_generator",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> generator s (primitive r)``,
  metis_tac[field_primitive_in_field_generators, field_generators_member]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Isomorphism by Minimal Polynomial of generator               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            GroupHomo (\p. eval p x) (PolyModRing s (minimal x)).sum r.sum *)
(* Proof:
   Let m = minimal x.
   The goal is: GroupHomo (\p. eval p x) (PolyModRing s m).sum r.sum
   Note s <= r                         by subfield_is_subring
    and 0 < deg m                      by poly_minimal_deg_pos
    and Deg s m = deg m                by subring_poly_deg
   By GroupHomo_def, poly_mod_ring_property,  this is to show;
   (1) Poly s p ==> eval p x IN r.sum.carrier
       Note poly p                     by subring_poly_poly
        ==> eval p x IN R              by poly_eval_element
         or eval p a IN r.sum.carrier  by field_carriers
   (2) Poly s p /\ Poly s p' ==> eval (poly_mod s (poly_add s p p') m) x = eval p x + eval p' x
       Note IPoly s m                  by poly_minimal_subfield_irreducible, s <<= r
       Thus Ulead s m                  by poly_irreducible_ulead
       Also x IN roots m               by poly_minimal_has_element_root, poly_roots_member
       Note poly p /\ poly p'          by subring_poly_poly
        and ulead m                    by subring_poly_ulead
            eval (poly_mod s (poly_add s p p') m) x
          = eval (poly_mod s (p + p') m) x     by subring_poly_add
          = eval ((p + p') % m) x              by subring_poly_mod, poly_add_poly
          = eval (p + p') x                    by poly_eval_poly_mod_at_root, poly_add_poly
          = eval p x + eval p' x               by poly_eval_add
*)
val poly_mod_ring_by_minimal_sum_homo = store_thm(
  "poly_mod_ring_by_minimal_sum_homo",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN R ==>
         GroupHomo (\p. eval p x) (PolyModRing s (minimal x)).sum r.sum``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = minimal x` >>
  `s <= r` by rw[subfield_is_subring] >>
  `0 < deg m` by rw[poly_minimal_deg_pos, Abbr`m`] >>
  `deg m <> 0` by decide_tac >>
  `Deg s m <> 0` by metis_tac[subring_poly_deg] >>
  rw_tac std_ss[GroupHomo_def, poly_mod_ring_property] >| [
    `poly p` by metis_tac[subring_poly_poly] >>
    rw[],
    `IPoly s m` by rw[poly_minimal_subfield_irreducible, Abbr`m`] >>
    `Ulead s m` by rw[poly_irreducible_ulead] >>
    `x IN roots m` by metis_tac[poly_minimal_has_element_root, poly_roots_member] >>
    `poly p /\ poly p'` by metis_tac[subring_poly_poly] >>
    `ulead m` by metis_tac[subring_poly_ulead] >>
    `eval (poly_mod s (poly_add s p p') m) x = eval ((p + p') % m) x` by prove_tac[subring_poly_add, subring_poly_mod, poly_add_poly] >>
    rw[poly_eval_poly_mod_at_root]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            MonoidHomo (\p. eval p x) (PolyModRing s (minimal x)).prod r.prod *)
(* Proof:
   Let m = minimal x.
   The goal is: MonoidHomo (\p. eval p x) (PolyModRing s m).prod r.prod
   Note s <= r                         by subfield_is_subring
    and 0 < deg m                      by poly_minimal_deg_pos
    and Deg s m = deg m                by subring_poly_deg
   By MonoidHomo_def, poly_mod_ring_property, this is to show;
   (1) Poly s p ==> eval p x IN r.sum.carrier
       Note poly p                     by subring_poly_poly
        ==> eval p x IN R              by poly_eval_element
         or eval p a IN r.prod.carrier by field_carriers
   (2) Poly s p /\ Poly s p' ==> eval (poly_mod s (poly_mult s p p') m) x = eval p x * eval p' x
       Note IPoly s m                  by poly_minimal_subfield_irreducible, s <<= r
       Thus Ulead s m                  by poly_irreducible_ulead
       Also x IN roots m               by poly_minimal_has_element_root, poly_roots_member
       Note poly p /\ poly p'          by subring_poly_poly
        and ulead m                    by subring_poly_ulead
            eval (poly_mod s (poly_mult s p p') m) x
          = eval (poly_mod s (p * p') m) x     by subring_poly_mult
          = eval ((p * p') % m) x              by subring_poly_mod, poly_mult_poly
          = eval (p * p') x                    by poly_eval_poly_mod_at_root, poly_mult_poly
          = eval p x * eval p' x               by poly_eval_mult
   (3) eval (poly_one s) x = #1
       Note eval (poly_one s)
          = eval |1| s         by subring_poly_one
          = #1                 by poly_eval_one
*)
val poly_mod_ring_by_minimal_prod_homo = store_thm(
  "poly_mod_ring_by_minimal_prod_homo",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN R ==>
         MonoidHomo (\p. eval p x) (PolyModRing s (minimal x)).prod r.prod``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = minimal x` >>
  `s <= r` by rw[subfield_is_subring] >>
  `0 < deg m` by rw[poly_minimal_deg_pos, Abbr`m`] >>
  `deg m <> 0` by decide_tac >>
  `Deg s m <> 0` by metis_tac[subring_poly_deg] >>
  rw_tac std_ss[MonoidHomo_def, poly_mod_ring_property] >| [
    `poly p` by metis_tac[subring_poly_poly] >>
    rw[],
    `IPoly s m` by rw[poly_minimal_subfield_irreducible, Abbr`m`] >>
    `Ulead s m` by rw[poly_irreducible_ulead] >>
    `x IN roots m` by metis_tac[poly_minimal_has_element_root, poly_roots_member] >>
    `poly p /\ poly p'` by metis_tac[subring_poly_poly] >>
    `ulead m` by metis_tac[subring_poly_ulead] >>
    `eval (poly_mod s (poly_mult s p p') m) x = eval ((p * p') % m) x` by prove_tac[subring_poly_mult, subring_poly_mod, poly_mult_poly] >>
    rw[poly_eval_poly_mod_at_root],
    metis_tac[subring_poly_one, poly_eval_one]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            FieldHomo (\p. eval p x) (PolyModRing s (minimal x)) r *)
(* Proof:
   Let m = minimal x.
   The goal is: FieldHomo (\p. eval p x) (PolyModRing s m) r
   By FieldHomo_def, RingHomo_def, poly_mod_ring_property, this is to show:
   (1) Poly s p ==> eval p x IN R
       Note s <= r                     by subfield_is_subring
         so poly p                     by subring_poly_poly
        ==> eval p x IN R              by poly_eval_element
   (2) GroupHomo (\p. eval p x) (PolyModRing s m).sum r.sum
       This is true    by poly_mod_ring_by_minimal_sum_homo
   (3) MonoidHomo (\p. eval p x) (PolyModRing s m).prod r.prod
       This is true    by poly_mod_ring_by_minimal_prod_homo
*)
val poly_mod_ring_by_minimal_homo_field = store_thm(
  "poly_mod_ring_by_minimal_homo_field",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN R ==>
         FieldHomo (\p. eval p x) (PolyModRing s (minimal x)) r``,
  rw_tac std_ss[FieldHomo_def, RingHomo_def, poly_mod_ring_property] >-
  metis_tac[subfield_is_subring, subring_poly_poly, poly_eval_element] >-
  rw[poly_mod_ring_by_minimal_sum_homo] >>
  rw[poly_mod_ring_by_minimal_prod_homo]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            INJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R *)
(* Proof:
   Let m = minimal x.
   The goal is: INJ (\p. eval p x) (PolyModRing s m).carrier R
   Note s <= r                         by subfield_is_subring
   By INJ_DEF, poly_mod_ring_property, this is to show:
   (1) Poly s p ==> eval p x IN R
       Note poly p                     by subring_poly_poly
        ==> eval p x IN R              by poly_eval_element
   (2) Poly s p /\ Poly s p' /\ eval p a = eval p' a ==> p = p'
       Note p % m = p' % m             by poly_minimal_eval_congruence
        Now monic m                    by poly_minimal_monic
        and 0 < deg m                  by poly_minimal_deg_pos
        ==> pmonic m                   by poly_monic_pmonic
       Note poly p /\ poly q'          by subring_poly_poly
        and deg p < deg m              by subring_poly_deg
        and deg p' < deg m             by subring_poly_deg
       Thus p % m = p, and q % m = q   by poly_mod_less
         or p = q                      by above, p % m = p' % m
*)
val poly_mod_ring_by_minimal_map_inj = store_thm(
  "poly_mod_ring_by_minimal_map_inj",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN R ==>
     INJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = minimal x` >>
  `s <= r` by rw[subfield_is_subring] >>
  rw_tac std_ss[INJ_DEF, poly_mod_ring_property] >-
  metis_tac[poly_eval_element, subring_poly_poly] >>
  `p % m = p' % m` by rw[GSYM poly_minimal_eval_congruence, Abbr`m`] >>
  `monic m` by rw[poly_minimal_monic, Abbr`m`] >>
  `pmonic m` by rw[poly_monic_pmonic, poly_minimal_deg_pos, Abbr`m`] >>
  metis_tac[subring_poly_poly, subring_poly_deg, poly_mod_less]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
            SURJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R *)
(* Proof:
   Let m = minimal x.
   The goal is: SURJ (\p. eval p x) (PolyModRing s m).carrier R
   Note s <= r                         by subfield_is_subring
   and x IN R /\ generator s x         by field_generators_def
   By SURJ_DEF, poly_mod_ring_property, this is to show:
   (1) Poly s p ==> eval p x IN R
       Note poly p                     by subring_poly_poly
        ==> eval p x IN R              by poly_eval_element
   (2) ?p. (Poly s p /\ Deg s p < Deg s m) /\ (eval p x = x')
       Note ?q. Poly s q /\ (x' = eval q x)   by field_generator_alt, s <= r
        and IPoly s m                  by poly_minimal_subfield_irreducible, s <<= r
        ==> Pmonic s m                 by poly_irreducible_pmonic
         so pmonic m                   by subring_poly_pmonic
       Take p = poly_mod s q m.
       Then Poly s p                   by poly_mod_poly
        and Deg s p < Deg s m          by poly_deg_mod_less, Pmonic s m
       Note x IN roots m               by poly_minimal_has_element_root, poly_roots_member
        and p = q % m                  by subring_poly_mod, Ulead s m
        ==> eval p x
          = eval q x                   by poly_eval_poly_mod_at_root, subring_poly_poly
          = x'                         by above
*)
val poly_mod_ring_by_minimal_map_surj = store_thm(
  "poly_mod_ring_by_minimal_map_surj",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
     SURJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = minimal x` >>
  `s <= r` by rw[subfield_is_subring] >>
  fs[field_generators_def] >>
  rw_tac std_ss[SURJ_DEF, poly_mod_ring_property] >-
  metis_tac[poly_eval_element, subring_poly_poly] >>
  `?q. Poly s q /\ (x' = eval q x)` by metis_tac[field_generator_alt] >>
  `IPoly s m` by rw[poly_minimal_subfield_irreducible, Abbr`m`] >>
  `Pmonic s m` by rw[poly_irreducible_pmonic] >>
  `pmonic m` by metis_tac[subring_poly_pmonic] >>
  qabbrev_tac `p = poly_mod s q m` >>
  qexists_tac `p` >>
  rpt strip_tac >-
  rw[poly_mod_poly, Abbr`p`] >-
  rw[poly_deg_mod_less, Abbr`p`] >>
  `x IN roots m` by metis_tac[poly_minimal_has_element_root, poly_roots_member] >>
  `p = q % m` by rw[subring_poly_mod, Abbr`p`] >>
  metis_tac[poly_eval_poly_mod_at_root, subring_poly_poly]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
            BIJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R *)
(* Proof:
   Note x IN R            by field_generators_def
   By BIJ_DEF, this is to show:
   (1) INJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
       This is true       by poly_mod_ring_by_minimal_map_inj
   (2) SURJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
       This is true       by poly_mod_ring_by_minimal_map_surj
*)
val poly_mod_ring_by_minimal_map_bij = store_thm(
  "poly_mod_ring_by_minimal_map_bij",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
     BIJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R``,
  rpt strip_tac >>
  `x IN R` by fs[field_generators_def] >>
  rw_tac std_ss[BIJ_DEF] >-
  rw[poly_mod_ring_by_minimal_map_inj] >>
  rw[poly_mod_ring_by_minimal_map_surj]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
            FieldIso (\p. eval p x) (PolyModRing s (minimal x)) r *)
(* Proof:
   Note x IN R            by field_generators_def
   By FieldIso_def, this is to show:
   (1) FieldHomo (\p. eval p x) (PolyModRing s (minimal x)) r
       This is true       by poly_mod_ring_by_minimal_homo_field
   (2) BIJ (\p. eval p x) (PolyModRing s (minimal x)).carrier R
       This is true       by poly_mod_ring_by_minimal_map_bij
*)
val poly_mod_ring_by_minimal_iso_field = store_thm(
  "poly_mod_ring_by_minimal_iso_field",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
         FieldIso (\p. eval p x) (PolyModRing s (minimal x)) r``,
  rpt strip_tac >>
  `x IN R` by fs[field_generators_def] >>
  rw_tac std_ss[FieldIso_def] >-
  rw[poly_mod_ring_by_minimal_homo_field] >>
  rw[poly_mod_ring_by_minimal_map_bij]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
            ((PolyModRing s (minimal x)) === r) (\p. eval p x) *)
(* Proof:
   This is to show:
   (1) Field (PolyModRing s (minimal x))
       Note x IN R                              by field_generators_def
       Thus IPoly s (minimal x)                 by poly_minimal_subfield_irreducible
        ==> Field (PolyModRing s (minimal x))   by poly_mod_irreducible_field, Field s
   (2) FieldIso (\p. eval p x) (PolyModRing s (minimal x)) r
       This is true                             by poly_mod_ring_by_minimal_iso_field
*)
val poly_mod_ring_by_minimal_field_iso = store_thm(
  "poly_mod_ring_by_minimal_field_iso",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==> !x. x IN generators r s ==>
         ((PolyModRing s (minimal x)) === r) (\p. eval p x)``,
  (rpt strip_tac >> simp[]) >| [
    `x IN R` by fs[field_generators_def] >>
    `IPoly s (minimal x)` by rw[poly_minimal_subfield_irreducible] >>
    rw[poly_mod_irreducible_field],
    rw[poly_mod_ring_by_minimal_iso_field]
  ]);

(* Another milestone theorem! *)

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R ==> FiniteField (PolyModRing s (minimal x)) *)
(* Proof:
   Note FiniteField s                             by subfield_finite_field, FiniteField r
    and IPoly s (minimal x)                       by poly_minimal_subfield_irreducible, x IN R
    ==> FiniteField (PolyModRing s (minimal x))   by poly_mod_irreducible_finite_field
*)
val poly_mod_ring_by_minimal_finite_field = store_thm(
  "poly_mod_ring_by_minimal_finite_field",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==>
   !x. x IN R ==> FiniteField (PolyModRing s (minimal x))``,
  rpt strip_tac >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `IPoly s (minimal x)` by rw[poly_minimal_subfield_irreducible] >>
  rw[poly_mod_irreducible_finite_field]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN generators r s ==> (r =ff= PolyModRing s (minimal x)) *)
(* Proof:
   Let t = PolyModRing s (minimal x).
   Note x IN R                     by field_generators_member
    and FiniteField t              by poly_mod_ring_by_minimal_finite_field
    and (t === r) (\p. eval p x)   by poly_mod_ring_by_minimal_field_iso
    ==> r =ff= t                   by field_iso_sym, finite_field_is_field
*)
val poly_mod_ring_by_minimal_field_isomorphism = store_thm(
  "poly_mod_ring_by_minimal_field_isomorphism",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==>
   !x. x IN generators r s ==> (r =ff= PolyModRing s (minimal x))``,
  ntac 5 strip_tac >>
  `x IN R` by metis_tac[field_generators_member] >>
  `FiniteField (PolyModRing s (minimal x))` by rw[poly_mod_ring_by_minimal_finite_field] >>
  metis_tac[poly_mod_ring_by_minimal_field_iso, field_iso_sym, finite_field_is_field]);

(* Theorem: FiniteField r /\ s <<= r ==>
            ((PolyModRing s (minimal (primitive r))) === r) (\p. eval p (primitive r)) *)
(* Proof:
   Let x = primitive r.
   Then x IN generators r s                                by field_primitive_in_field_generators
    ==> (PolyModRing s (minimal x) === r) (\p. eval p x)   by poly_mod_ring_by_minimal_field_iso
*)
val poly_mod_ring_by_primitive_minimal_field_iso = store_thm(
  "poly_mod_ring_by_primitive_minimal_field_iso",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==>
    ((PolyModRing s (minimal (primitive r))) === r) (\p. eval p (primitive r))``,
  rw_tac std_ss[field_primitive_in_field_generators, poly_mod_ring_by_minimal_field_iso]);

(* Theorem: FiniteField r /\ s <<= r ==>
            (r =ff= (PolyModRing s (minimal (primitive r)))) *)
(* Proof:
   Let x = primitive r, t = PolyModRing s (minimal x).
   Note x IN R                     by field_primitive_element
   Thus FiniteField t              by poly_mod_ring_by_minimal_finite_field
    and (t === r) (\p. eval p x)   by poly_mod_ring_by_primitive_minimal_field_iso
     or r =ff= t                   by field_iso_sym
*)
val poly_mod_ring_by_primitive_minimal_field_isomorphism = store_thm(
  "poly_mod_ring_by_primitive_minimal_field_isomorphism",
  ``!(r:'a field) (s:'a field). FiniteField r /\ s <<= r ==>
    (r =ff= (PolyModRing s (minimal (primitive r))))``,
  ntac 3 strip_tac >>
  `(primitive r) IN R` by rw[field_primitive_element] >>
  `FiniteField (PolyModRing s (minimal (primitive r)))` by rw[poly_mod_ring_by_minimal_finite_field] >>
  metis_tac[poly_mod_ring_by_primitive_minimal_field_iso, field_iso_sym]);

(* Theorem: FiniteField r /\ s <<= r /\ z IN (FPrimitives r) ==>
            ((PolyModRing s (minimal z)) === r) (\p. eval p z) *)
(* Proof:
   Let z IN FPrimitives r
   Then z IN generators r s                                by field_primitives_subset_field_generators, SUBSET_DEF
    ==> (PolyModRing s (minimal z) === r) (\p. eval p z)   by poly_mod_ring_by_minimal_field_iso
*)
val poly_mod_ring_by_primitives_element_field_iso = store_thm(
  "poly_mod_ring_by_primitives_element_field_iso",
  ``!(r:'a field) (s:'a field) z. FiniteField r /\ s <<= r /\ z IN (FPrimitives r) ==>
    ((PolyModRing s (minimal z)) === r) (\p. eval p z)``,
  metis_tac[field_primitives_subset_field_generators, poly_mod_ring_by_minimal_field_iso, SUBSET_DEF]);

(* Theorem: FiniteField r /\ s <<= r /\ z IN (FPrimitives r) ==> (r =ff= (PolyModRing s (minimal z))) *)
(* Proof:
   Let t = PolyModRing s (minimal z).
   Note z IN R+, so z IN R         by field_primitives_element, field_nonzero_element
   Thus FiniteField t              by poly_mod_ring_by_minimal_finite_field
    and (t === r) (\p. eval p z)   by poly_mod_ring_by_primitives_element_field_iso
     or r =ff= t                   by field_iso_sym
*)
val poly_mod_ring_by_primitives_element_field_isomorphism = store_thm(
  "poly_mod_ring_by_primitives_element_field_isomorphism",
  ``!(r:'a field) (s:'a field) z. FiniteField r /\ s <<= r /\ z IN (FPrimitives r) ==>
    (r =ff= (PolyModRing s (minimal z)))``,
  ntac 4 strip_tac >>
  `z IN R` by metis_tac[field_primitives_element, field_nonzero_element] >>
  `FiniteField (PolyModRing s (minimal z))` by rw[poly_mod_ring_by_minimal_finite_field] >>
  metis_tac[poly_mod_ring_by_primitives_element_field_iso, field_iso_sym]);

(* ------------------------------------------------------------------------- *)
(* Uniqueness of Finite Field by Isomorphisms                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> r =ff= r_ *)
(* Proof:
   Part 1: isomorphic subfields
   Let s = PF r, s_ = PF r_.
   Then ?f. FieldIso f s s_    by finite_field_prime_field_isomorphic, CARD R = CARD R_

   Part 2: isomorphic quotient fields
   Let z = primitive r, z_ = mirror f z.
   Note s <<= r                by prime_field_is_subfield
    and s_ <<= r_              by prime_field_is_subfield
   This gives the pattern:  r =| (s,f,s_) |= r_

   Note z IN generators r s    by field_primitive_in_field_generators, s <<= r
     so z IN R                 by field_generators_def
   Let m = minimal z, m_ = minimal_ z_
   Then m_ = MAP f m           by finite_field_element_mirror_poly_minimal, r =| (s,f,s_) |= r_
   Note IPoly s m              by poly_minimal_subfield_irreducible, z IN R, s <<= r
    ==> FieldIso (MAP f) (PolyModRing s m) (PolyModRing s_ m_)   by field_iso_poly_mod_field_iso

   Part 3: quotient field isomorphic to original field
   Note z_ IN FPrimitives r_           by finite_field_primitive_mirror, r =| (s,f,s_) |= r_
    and z_ IN field_generators r_ s_   by field_primitives_subset_field_generators, SUBSET_DEF, s_ <<= r_
   Thus FieldIso (\p. eval p z) (PolyModRing s m) r       by poly_mod_ring_by_minimal_iso_field, z IN generators r s
    and FieldIso (\p. eval_ p z_) (PolyModRing s_ m_) r_  by poly_mod_ring_by_minimal_iso_field, z_ IN field_generators r_ s_

   Part 4: conclude
   Note z_ IN R_                       by field_primitives_element, field_nonzero_element
   Thus IPoly s_ m_                    by poly_minimal_subfield_irreducible, by z_ IN R_, s_ <<= r_
    ==> Field (PolyModRing s_ m_)      by poly_mod_irreducible_field, IPoly s_ m_
   Also Field (PolyModRing s m)        by poly_mod_irreducible_field, IPoly s m

   Let f1 = (\p. eval p z), f2 = (MAP f), f3 = (\p. eval_ p z_).
        FieldIso f1 (PolyModRing s m) r
    ==> FieldIso (LINV f1 (PolyModRing s m).carrier) r (PolyModRing s m)   by field_iso_sym
    and FieldIso f2 (PolyModRing s m) (PolyModRing s_ m_)
    and FieldIso f3 (PolyModRing s_ m_) r_
   Thus ?f4. FieldIso f4 r r_          by field_iso_iso
*)
val finite_field_eq_card_field_iso = store_thm(
  "finite_field_eq_card_field_iso",
  ``!(r:'a field) (r_:'b field).
      FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> r =ff= r_``,
  rw_tac std_ss[] >>
  qabbrev_tac `s = PF r` >>
  qabbrev_tac `s_ = PF r_` >>
  `?f. FieldIso f s s_` by rw[finite_field_prime_field_isomorphic, Abbr`s`, Abbr`s_`] >>
  qabbrev_tac `z = primitive r` >>
  qabbrev_tac `z_ = mirror f z` >>
  `s <<= r` by rw[prime_field_is_subfield, Abbr`s`] >>
  `s_ <<= r_` by rw[prime_field_is_subfield, Abbr`s_`] >>
  `z IN generators r s` by rw[field_primitive_in_field_generators, Abbr`z`] >>
  `z IN R` by fs[field_generators_def] >>
  qabbrev_tac `m = minimal z` >>
  qabbrev_tac `m_ = minimal_ z_` >>
  `m_ = MAP f m` by rw[finite_field_element_mirror_poly_minimal, Abbr`z_`, Abbr`m`, Abbr`m_`] >>
  `IPoly s m` by rw[poly_minimal_subfield_irreducible, Abbr`m`] >>
  `FieldIso (MAP f) (PolyModRing s m) (PolyModRing s_ m_)` by rw[field_iso_poly_mod_field_iso] >>
  `z_ IN FPrimitives r_` by rw[finite_field_primitive_mirror, Abbr`z_`, Abbr`z`] >>
  `z_ IN field_generators r_ s_` by metis_tac[field_primitives_subset_field_generators, SUBSET_DEF] >>
  `FieldIso (\p. eval p z) (PolyModRing s m) r` by rw[poly_mod_ring_by_minimal_iso_field, Abbr`m`] >>
  `FieldIso (\p. eval_ p z_) (PolyModRing s_ m_) r_` by rw[poly_mod_ring_by_minimal_iso_field, Abbr`m_`] >>
  `z_ IN R_` by fs[field_primitives_element, field_nonzero_element] >>
  `IPoly s_ m_` by rw[poly_minimal_subfield_irreducible, Abbr`m_`] >>
  `Field (PolyModRing s_ m_)` by rw[poly_mod_irreducible_field] >>
  `Field (PolyModRing s m)` by rw[poly_mod_irreducible_field] >>
  metis_tac[field_iso_iso, field_iso_sym]);

(* Another proof of the milestone: uniqueness of finite fields up to isomorphism. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
