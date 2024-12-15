(* ------------------------------------------------------------------------- *)
(* Finite Vector Space                                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "FiniteVSpace";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory numberTheory combinatoricsTheory;

open VectorSpaceTheory SpanSpaceTheory LinearIndepTheory;
open monoidTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Vector Space Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overload:
*)
(* Definitions and Theorems (# are exported):

   Finite Vector Space:
   FiniteVSpace_def          |- !r g op. FiniteVSpace r g op <=> VSpace r g op /\ FINITE R /\ FINITE V
   finite_vspace_is_vspace   |- !r g op. FiniteVSpace r g op ==> VSpace r g op
   finite_vspace_is_finite   |- !r g op. FiniteVSpace r g op ==> FINITE R /\ FINITE V
   finite_vspace_all_basis   |- !r g op. FiniteVSpace r g op ==> basis g (SET_TO_LIST V)
   finite_vspace_span_itself |- !r g op. FiniteVSpace r g op ==> (SpanSpace r g op (SET_TO_LIST V) = g)

   Finite Vector Space Dimension:
   dim_def                 |- !r g op. dim r g op =
                                       MIN_SET (IMAGE LENGTH {b | basis g b /\ (SpanSpace r g op b = g)})
   finite_vspace_dim_basis |- !r g op. FiniteVSpace r g op ==>
                              ?b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g)
   finite_vspace_dim_eq_0  |- !r g op. FiniteVSpace r g op /\ (dim r g op = 0) ==> (g.carrier = {g.id})

   finite_vspace_dim_basis_indep |- !r g op. FiniteVSpace r g op ==>
                                    !b. basis g b /\ (LENGTH b = dim r g op) /\
                                        (SpanSpace r g op b = g) ==> LinearIndepBasis r g op b
   finite_vspace_dim_map_inj     |- !r g op. FiniteVSpace r g op ==>
                                    !b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g) ==>
                                        INJ (\n. n |o| b) (sticks r (LENGTH b)) V

   Finite Vector Space Cardinality and Linear Independence:
   finite_vspace_card               |- !r g op. FiniteVSpace r g op ==> (CARD V = CARD R ** dim r g op)
   finite_vspace_indep_span_card    |- !r g op. FiniteVSpace r g op ==> !b. LinearIndepBasis r g op b ==>
                                                (CARD (SpanSpace r g op b).carrier = CARD R ** LENGTH b)
   finite_vspace_dim_basis_span     |- !r g op. FiniteVSpace r g op ==>
                                      !b. basis g b /\ (LENGTH b = dim r g op) /\
                                          LinearIndepBasis r g op b ==> (SpanSpace r g op b = g)
   finite_vspace_dim_basis_property |- !r g op. FiniteVSpace r g op ==>
                                      !b. basis g b /\ (LENGTH b = dim r g op) ==>
                                          (LinearIndepBasis r g op b <=> (SpanSpace r g op b = g))
   finite_vspace_basis_dep_special  |- !r g op. FiniteVSpace r g op ==>
                        !b. basis g b /\ (LENGTH b = SUC (dim r g op)) ==> ~LinearIndepBasis r g op b
   finite_vspace_basis_dep          |- !r g op. FiniteVSpace r g op ==>
                                !b. basis g b /\ dim r g op < LENGTH b ==> ~LinearIndepBasis r g op b

*)

(* Overloads for convenience *)
val _ = temp_overload_on ("o", ``(op:'a -> 'b -> 'b)``);
val _ = temp_overload_on ("V", ``(g:'b group).carrier``);
val _ = temp_overload_on ("||", ``(g:'b group).op``);
val _ = temp_overload_on ("|0|", ``(g:'b group).id``);
val _ = set_fixity "||" (Infixl 500); (* same as + in arithmeticScript.sml *)

val _ = temp_overload_on ("+", ``stick_add r``);
val _ = temp_overload_on ("-", ``stick_neg r``);
val _ = temp_overload_on ("*", ``stick_cmult r``);
val _ = temp_overload_on ("-", ``stick_sub r``);

(* ------------------------------------------------------------------------- *)
(* Finite Vector Space.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define Finite Vector Space *)
val FiniteVSpace_def = Define`
  FiniteVSpace (r:'a field) (g:'b group) op <=> VSpace r g op /\ FINITE R /\ FINITE V
`;

(* Theorem: FiniteVSpace r g op ==> VSpace r g op *)
(* Proof: by FiniteVSpace_def. *)
(*
val finite_vspace_is_vspace = store_thm(
  "finite_vspace_is_vspace",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==> VSpace r g op``,
  rw[FiniteVSpace_def]);
*)
val finite_vspace_is_vspace = save_thm("finite_vspace_is_vspace",
   FiniteVSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |>
                       UNDISCH |> CONJUNCTS |> el 1 |> DISCH_ALL |> GEN_ALL);
(* val finite_vspace_is_vspace = |- !r op g. FiniteVSpace r g op ==> VSpace r g op: thm *)

(* Theorem: FiniteVSpace r g op ==> FINITE R /\ FINITE V *)
(* Proof: by FiniteVSpace_def. *)
val finite_vspace_is_finite = store_thm(
  "finite_vspace_is_finite",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==> FINITE R /\ FINITE V``,
  rw[FiniteVSpace_def]);

(* Theorem: For FiniteVSpace, list of all vectors is a basis: basis g (SET_TO_LIST V) *)
(* Proof:
   Since FINITE V, !x. MEM x (SET_TO_LIST V) <=> x IN V     by MEM_SET_TO_LIST
   Thus true by basis_member.
*)
val finite_vspace_all_basis = store_thm(
  "finite_vspace_all_basis",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==> basis g (SET_TO_LIST V)``,
  metis_tac[FiniteVSpace_def, basis_member, MEM_SET_TO_LIST]);

(* Theorem: The whole Group g can span itself.
            SpanSpace r g op (SET_TO_LIST V) = g  *)
(* Proof:
   Note FiniteSpace r g op ==> basis g (SET_TO_LIST V)   by finite_vspace_all_basis
   By SpanSpace_def and monoid_component_equality, this is to show:
      SpanSpace r g op (SET_TO_LIST V).carrier = V
   or IMAGE (\n. n |o| (SET_TO_LIST V)) (sticks r (LENGTH (SET_TO_LIST V))) = V
   which is to show:
   (1) n IN sticks r (LENGTH (SET_TO_LIST V)) ==> n |o| (SET_TO_LIST V) IN V
       n |o| (SET_TO_LIST V) IN V                       by vsum_basis_stick_vector
   (2) x IN V ==> ?n. (x = n |o| (SET_TO_LIST V)) /\ n IN sticks r (LENGTH (SET_TO_LIST V))
       x IN V ==> MEM x (SET_TO_LIST V)                 by MEM_SET_TO_LIST
       Let n = the sticks of LENGTH (SET_TO_LIST V), with all #0, but #1 at x.
       Then n |o| (SET_TO_LIST V) = x                   by vspace_basis_stick
*)
val finite_vspace_span_itself = store_thm(
  "finite_vspace_span_itself",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==> (SpanSpace r g op (SET_TO_LIST V) = g)``,
  rpt (stripDup[FiniteVSpace_def]) >>
  `basis g (SET_TO_LIST V)` by metis_tac[finite_vspace_all_basis] >>
  rw[monoid_component_equality, SpanSpace_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[vsum_basis_stick_vector] >>
  metis_tac[vspace_basis_stick, MEM_SET_TO_LIST]);

(* ------------------------------------------------------------------------- *)
(* Finite Vector Space Dimension.                                            *)
(* ------------------------------------------------------------------------- *)

(* Dimension = LENGTH of shortest basis spanning the whole vector space) *)
val dim_def = Define`
  dim (r:'a field) (g:'b group) op =
      MIN_SET (IMAGE LENGTH { b | basis g b /\ (SpanSpace r g op b = g) })
`;

(* Theorem: Existence of Spanning basis with dimension.
            FiniteVSpace r g op ==> ?b. basis g b /\ (LENGTH b = dim r g op) *)
(* Proof:
   Given FiniteVSpace r g op,
     ==> basis g (SET_TO_LIST V)                               by finite_vspace_all_basis
   (SpanSpace r g op (SET_TO_LIST V) = g)                      by finite_vspace_span_itself
   hence SET_TO_LIST V IN { b | basis g b /\ (SpanSpace r g op b = g) }
   or s = { b | basis g b /\ (SpanSpace r g op b = g) } <> {}  by MEMBER_NOT_EMPTY
   Thus IMAGE LENGTH s <> {}                                   by IMAGE_EQ_EMPTY
   so dim r g op exists, and
      dim r g op = MIN_SET (IMAGE LENGTH s) IN (IMAGE LENGTH s)             by MIN_SET_LEM
   or ?b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g)  by IN_IMAGE
*)
val finite_vspace_dim_basis = store_thm(
  "finite_vspace_dim_basis",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
   ?b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g)``,
  rw[dim_def] >>
  qabbrev_tac `s = { b | basis g b /\ (SpanSpace r g op b = g) }` >>
  `!b. b IN s ==> basis g b /\ (SpanSpace r g op b = g)` by rw[Abbr`s`] >>
  `basis g (SET_TO_LIST V)` by metis_tac[finite_vspace_all_basis] >>
  `(SpanSpace r g op (SET_TO_LIST V) = g)` by rw[finite_vspace_span_itself] >>
  `SET_TO_LIST V IN s` by rw[Abbr`s`] >>
  `IMAGE LENGTH s <> {}` by metis_tac[MEMBER_NOT_EMPTY, IMAGE_EQ_EMPTY] >>
  `MIN_SET (IMAGE LENGTH s) IN (IMAGE LENGTH s)` by rw[MIN_SET_LEM] >>
  metis_tac[IN_IMAGE]);

(* Theorem: FiniteVSpace r g op /\ (dim r g op = 0) ==> (g.carrier = {g.id}) *)
(* Proof:
    Since FiniteVSpace r g op
      ==> ?b. basis g b /\ (LENGTH b = dim r g op) /\
              (SpanSpace r g op b = g)               by finite_vspace_dim_basis
    Given dim r g op = 0,
       so LENGTH b = 0, or b = []                    by LENGTH_NIL
      and sticks r 0 = {[]}                          by sticks_0
    Hence g.carrier
        = (SpanSpace r g op b).carrier               by above
        = IMAGE (\n. n |o| b) (sticks r (LENGTH b))  by vspace_span_property
        = IMAGE (\n. n |o| []) {[]}                  by above
        = {[] |o| []}                                by application
        = {g.id}                                     by vsum_nil
*)
val finite_vspace_dim_eq_0 = store_thm(
  "finite_vspace_dim_eq_0",
  ``!(r:'a ring) (g:'b group) op. FiniteVSpace r g op /\ (dim r g op = 0) ==> (g.carrier = {g.id})``,
  rpt (stripDup[FiniteVSpace_def]) >>
  `?b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g)` by rw[finite_vspace_dim_basis] >>
  `b = []` by metis_tac[LENGTH_NIL] >>
  `sticks r 0 = {[]}` by rw[sticks_0] >>
  `g.carrier = IMAGE (\n. n |o| b) (sticks r (LENGTH b))` by rw[GSYM vspace_span_property] >>
  rw[vsum_nil]);

(* Theorem: In a Finite Vector Space,
            A spanning basis of dimension size is linearly independent:
            basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g) ==> LinearIndepBasis r g op b *)
(* Proof:
   By LinearIndepBasis_def, this is to show:
   (1) k < dim r g op ==> EL k n = #0
       Let u = EL k b
           b' = DROP (SUC k) b ++ TAKE k b
       By contradiction, suppose EL k n = u <> #0.
       (1) Show: LENGTH b' < LENGTH b
           Note rotate k b = u::b'                by rotate_shift_element
             so LENGTH b = SUC(LENGTH b')         by rotate_same_length, LENGTH
             or LENGTH b' < LENGTH b
       (2) Show: LENGTH b <= LENGTH b'
            Let s = { b | basis g b /\ (SpanSpace r g op b = g) }
           Then dim r g op = MIN_SET (IMAGE LENGTH s)
                                                  by dim_def
           Since basis g (rotate k b)             by basis_rotate_basis
               = basis g (u::b')                  by above, rotate k b = u::b'
           Hence basis g b'                       by basis_cons
             and SpanSpace r g op b' = SpanSpace r g op b   by vspace_span_basis_shrink
            Thus b' IN s                          by definition of s
              so s <> {}                          by MEMBER_NOT_EMPTY
             and IMAGE LENGTH s <> {}             by IMAGE_EQ_EMPTY
            Also LENGTH b' IN IMAGE LENGTH s      by IN_IMAGE
              so LENGTH b <= LENGTH b'            by MIN_SET_LEM
       However, (1) and (2) lead to a contradiction.
   (2) n IN sticks r (dim r g op) /\ !k. k < dim r g op ==> (EL k n = #0) ==> n |o| b = |0|
       True by vspace_stick_zero.
*)
val finite_vspace_dim_basis_indep = store_thm(
  "finite_vspace_dim_basis_indep",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
     !b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g) ==>
      LinearIndepBasis r g op b``,
  rpt (stripDup[FiniteVSpace_def]) >>
  rw[LinearIndepBasis_def, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `u = EL k b` >>
    qabbrev_tac `b' = DROP (SUC k) b ++ TAKE k b` >>
    `rotate k b = u::b'` by rw[rotate_shift_element] >>
    `LENGTH b = SUC(LENGTH b')` by metis_tac[rotate_same_length, LENGTH] >>
    `LENGTH b' < LENGTH b` by decide_tac >>
    qabbrev_tac `s = { b | basis g b /\ (SpanSpace r g op b = g) }` >>
    `dim r g op = MIN_SET (IMAGE LENGTH s)` by rw[GSYM dim_def, Abbr`s`] >>
    `basis g b'` by metis_tac[basis_rotate_basis, basis_cons] >>
    `SpanSpace r g op b' = SpanSpace r g op b` by metis_tac[vspace_span_basis_shrink] >>
    `b' IN s` by rw[Abbr`b'`, Abbr`s`] >>
    `IMAGE LENGTH s <> {}` by metis_tac[MEMBER_NOT_EMPTY, IMAGE_EQ_EMPTY] >>
    `LENGTH b <= LENGTH b'` by metis_tac[MIN_SET_LEM, IN_IMAGE] >>
    decide_tac,
    metis_tac[vspace_stick_zero]
  ]);

(* Theorem: In a Finite Vector Space,
            A spanning basis of dimension size gives an injective map:
     basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g) ==>
           INJ (\n. n |o| b) (sticks r (LENGTH b)) V       *)
(* Proof:
   Since FiniteVSpace r g op ==> VSpace r g op       by finite_vspace_is_vspace
     and LinearIndepBasis r g op b                   by finite_vspace_dim_basis_indep
      so INJ (\n. n |o| b) (sticks r (LENGTH b)) V   by vspace_indep_basis_inj
*)
val finite_vspace_dim_map_inj = store_thm(
  "finite_vspace_dim_map_inj",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
     !b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g) ==>
      INJ (\n. n |o| b) (sticks r (LENGTH b)) V``,
  rw[FiniteVSpace_def, finite_vspace_dim_basis_indep, vspace_indep_basis_inj]);

(* ------------------------------------------------------------------------- *)
(* Finite Vector Space Cardinality and Linear Independence.                  *)
(* ------------------------------------------------------------------------- *)

(* Then show: CARD V = (CARD R) ** DIM (VSpace r g op)
   Possibly, this involves showing n IN (sticks r (LENGTH b)) ==> (\n. n |o| p) is INJ.
*)

(* Theorem: FiniteVSpace r g op ==> CARD V = (CARD R) ** dim r g op *)
(* Proof:
   Since FiniteVSpace r g op,
         ?b. basis g b /\ (LENGTH b = dim r g op) /\
         (SpanSpace r g op b = g)                               by finite_vspace_dim_basis
      so  V = (SpanSpace r g op b).carrier                      by monoid_component_equality
            = IMAGE (\n. n |o| b) (sticks r (LENGTH b))         by vspace_span_property
     Now INJ (\n. VSUM (MAP2 op n b)) (sticks r (LENGTH b)) V   by finite_vspace_dim_map_inj
     and SURJ (\n. VSUM (MAP2 op n b)) (sticks r (LENGTH b)) V  by IMAGE_SURJ
     and FINITE (sticks r (LENGTH b)),
   Hence CARD V
       = CARD (sticks r (LENGTH b))     by FINITE_BIJ_CARD_EQ, BIJ_DEF
       = CARD R ** (LENGTH b)           by sticks_card
       = CARD R ** (dim r g op)         by given LENGTH b = dim r g op
*)
val finite_vspace_card = store_thm(
  "finite_vspace_card",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==> (CARD V = (CARD R) ** dim r g op)``,
  rpt (stripDup[FiniteVSpace_def]) >>
  `?b. basis g b /\ (LENGTH b = dim r g op) /\ (SpanSpace r g op b = g)` by rw[finite_vspace_dim_basis] >>
  `V = IMAGE (\n. n |o| b) (sticks r (LENGTH b))` by metis_tac[vspace_span_property, monoid_component_equality] >>
  `INJ (\n. VSUM (MAP2 op n b)) (sticks r (LENGTH b)) V` by rw[finite_vspace_dim_map_inj] >>
  `SURJ (\n. VSUM (MAP2 op n b)) (sticks r (LENGTH b)) V` by rw[IMAGE_SURJ] >>
  `FINITE (sticks r (LENGTH b))` by rw[sticks_finite] >>
  metis_tac[FINITE_BIJ_CARD_EQ, BIJ_DEF, sticks_card]);

(*

Vector Space:
(1) a set of scalars (e.g. the basis field)
(2) a set of vectors (e.g. the extended field), forming a group (an Abelian group)
(3) an operation: (scalar, vector) -> vector, that preserves the group structure of vectors.

First goal: establish a dimension for vector space.
Since I define:  dim = size of smallest basis that can span the whole space.
The route is quite complicated:
(a) Define a basis (or basis) = a list of vectors
(b) Define what is meant by spanning by a basis: the set of all linear combinations.
(b1) Linear combinations of basis with what? with sticks = a list of scalars.
(b2) How to get a linear combination? VSUM (MAP (\(se, ve). se o ve) (ZIP (sticks, basis)))
(c) Define a SpanSpace by basis.
(d) Show that SpanSpace with basis = all vectors spans the whole space (of course).
(e) Show that a basis can shrink if it includes a dependent element.
(f) Since the possible basis is not empty, and empty basis cannot span the whole, there must be a minimum.
(g) Define dim = cardinality (smallest spanning basis)
Since this is the smallest spanning basis, all vectors are linear combinations of these vectors.
By counting how many such linear combinations,
finally giving the first important result: CARD (vector space) = CARD (scalar) ** (dimension)

Next goal: any set of vectors with cardinality more than dim is linearly dependent.

Can the first goal be done directly with the concept of linearly dependency and linear independency?
(a) Define a vlist = list of vectors
(b) Define a slist = list of scalars
(c) Define linear combination = VSUM (MAP f (ZIP (slist, vlist)))  of same length
(d) Define a linear independent vlist <=> (linear_comb (slist, vlist) = ||0|| ==> (slist = all #0))
    can call a linear independent basis.
(e) Show that a singleton basis is linearly independent.
    Show that the whole basis is linearly dependent (because ???)
    So there is a maximum linearly independent basis.
    Define dim = size of maximum linearly independent basis
(f) Then, all basis of cardinality exceeding dim will be linearly dependent.

*)

(* Theorem: FiniteVSpace r g op ==> !b. LinearIndepBasis r g op b ==>
            (CARD ((SpanSpace r g op b).carrier) = CARD R ** LENGTH b) *)
(* Proof:
   Note VSpace r g op /\ FINITE R /\ FINITE V             by FiniteVSpace_def
    and basis g b                                         by indep_basis_is_basis
    Now INJ (\n. n |o| b) (sticks r (LENGTH b)) V         by vspace_indep_basis_inj
    and FINITE (sticks r (LENGTH b)                       by sticks_finite, FINITE R
        CARD ((SpanSpace r g op b).carrier)
      = CARD (IMAGE (\n. n |o| b) (sticks r (LENGTH b)))  by vspace_span_property
      = CARD (sticks r (LENGTH b))                        by INJ_CARD_IMAGE_EQ
      = CARD R ** LENGTH b                                by sticks_card
*)
val finite_vspace_indep_span_card = store_thm(
  "finite_vspace_indep_span_card",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
   !b. LinearIndepBasis r g op b ==> (CARD ((SpanSpace r g op b).carrier) = CARD R ** LENGTH b)``,
  rpt (stripDup[FiniteVSpace_def]) >>
  `basis g b` by metis_tac[indep_basis_is_basis] >>
  `INJ (\n. n |o| b) (sticks r (LENGTH b)) V` by rw[vspace_indep_basis_inj] >>
  `FINITE (sticks r (LENGTH b))` by rw[sticks_finite] >>
  metis_tac[vspace_span_property, INJ_CARD_IMAGE_EQ, sticks_card]);

(* Theorem: basis g b /\ (LENGTH b = dim r g op) /\ LinearIndepBasis r g op b ==> (SpanSpace r g op b = g) *)
(* Proof:
   Note  FiniteVSpace r g op
         ==> VSpace r g op /\ FINITE R /\ FINITE V     by FiniteVSpace_def
   Since   CARD V
         = CARD R ** dim r g op                        by finite_vspace_card, FiniteVSpace r g op
         = CARD R ** LENGTH b                          by given
         = CARD ((SpanSpace r g op b).carrier)         by finite_vspace_indep_span_card
    Also (SpanSpace r g op b).carrier SUBSET V         by vspace_span_vector, SUBSET_DEF
    thus FINITE (SpanSpace r g op b).carrier           by SUBSET_FINITE
      so (SpanSpace r g op b).carrier = V              by SUBSET_EQ_CARD
    Hence SpanSpace r g op b = g                       by SpanSpace_def, monoid_component_equality
*)
val finite_vspace_dim_basis_span = store_thm(
  "finite_vspace_dim_basis_span",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
    !b. basis g b /\ (LENGTH b = dim r g op) /\ LinearIndepBasis r g op b ==> (SpanSpace r g op b = g)``,
  rpt (stripDup[FiniteVSpace_def]) >>
  `CARD V = CARD R ** dim r g op` by rw[finite_vspace_card] >>
  `CARD ((SpanSpace r g op b).carrier) = CARD R ** LENGTH b` by rw[finite_vspace_indep_span_card] >>
  `(SpanSpace r g op b).carrier SUBSET V` by metis_tac[vspace_span_vector, SUBSET_DEF] >>
  `FINITE (SpanSpace r g op b).carrier` by metis_tac[SUBSET_FINITE] >>
  `(SpanSpace r g op b).carrier = V` by rw[SUBSET_EQ_CARD] >>
  rw[SpanSpace_def, monoid_component_equality]);

(* Theorem: basis g b /\ (LENGTH b = dim r g op) ==>
            (LinearIndepBasis r g op b <=> (SpanSpace r g op b = g)) *)
(* Proof:
   If part: LinearIndepBasis r g op b ==> SpanSpace r g op b = g
      True by finite_vspace_dim_basis_span.
   Only-if part: SpanSpace r g op b = g ==> LinearIndepBasis r g op b
      True by finite_vspace_dim_basis_indep
*)
val finite_vspace_dim_basis_property = store_thm(
  "finite_vspace_dim_basis_property",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
     !b. basis g b /\ (LENGTH b = dim r g op) ==>
        (LinearIndepBasis r g op b <=> (SpanSpace r g op b = g))``,
  metis_tac[finite_vspace_dim_basis_span, finite_vspace_dim_basis_indep]);

(* Theorem: A basis with a size one more of dimension is linear dependent:
            basis g b /\ (LENGTH b = SUC (dim r g op)) ==> ~LinearIndepBasis r g op b *)
(* Proof:
   By contradiction, assume LinearIndepBasis r g op b.
   Since LENGTH b = SUC (dim r g op)
     ==> 0 < LENGTH b and LENGTH b <> 0
   Hence ?v u. b = v::u                     by LENGTH_NIL, list_CASES
     and basis g b ==> v IN V /\ basis g u  by basis_cons
    Also LENGHT b = SUC (LENGTH u)          by LENGTH
                  = SUC (dim r g op)        by given
      so LENGTH u = dim r g op              by prim_recTheory.INV_SUC_EQ
   By shrinking a linear independent basis,
         LinearIndepBasis r g op u          by vspace_basis_indep_one_less
   Hence SpanSpace r g op u = g             by finite_vspace_dim_basis_property
   Thus v IN V ==>
        v IN (SpanSpace r g op u).carrier   by monoid_component_equality
     or ?n. n IN sticks r (LENGTH u) and
        (v = n |o| u)                       by vspace_span_property
     or |0| = (- #1) o v || (n |o| u)       by vspace_vsub_eq_zero_alt
            = ((- #1)::n) |o| b             by vsum_cons, MAP2
     Let m = (- #1) :: n.
    Then m IN sticks r (LENGTH b)           by stick_cons, LENGTH
     and EL 0 m = -#1                       by EL, HD
     But !k. k < LENGTH b ==> (EL k m = #0) by implication,
      so EL 0 m = #0                        by 0 < LENGTH b
   which is a contradiction with EL 0 m = #1.
*)
val finite_vspace_basis_dep_special = store_thm(
  "finite_vspace_basis_dep_special",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
     !b. basis g b /\ (LENGTH b = SUC (dim r g op)) ==> ~LinearIndepBasis r g op b``,
  rpt (stripDup[FiniteVSpace_def, LinearIndepBasis_def]) >>
  `0 < LENGTH b /\ LENGTH b <> 0` by decide_tac >>
  `?v u. b = v::u` by metis_tac[LENGTH_NIL, list_CASES] >>
  `v IN V /\ basis g u` by metis_tac[basis_cons] >>
  `SUC (LENGTH u) = SUC (dim r g op)` by metis_tac[LENGTH] >>
  `LENGTH u = dim r g op` by decide_tac >>
  `LinearIndepBasis r g op u` by metis_tac[vspace_basis_indep_one_less] >>
  `SpanSpace r g op u = g` by rw[GSYM finite_vspace_dim_basis_property] >>
  `v IN (SpanSpace r g op u).carrier` by rw[monoid_component_equality] >>
  `?n. n IN sticks r (LENGTH u) /\ (v = n |o| u)` by rw[vspace_span_property] >>
  `|0| = (- #1) o v || (n |o| u)` by metis_tac[vspace_vsub_eq_zero_alt] >>
  `_ = ((- #1)::n) |o| b` by rw[vsum_cons] >>
  `Field r` by metis_tac[vspace_has_field] >>
  `Group g` by metis_tac[vspace_has_group] >>
  `- #1 IN R /\ - #1 <> #0` by rw[] >>
  qabbrev_tac `m = (- #1) :: n` >>
  `m IN sticks r (LENGTH b)` by metis_tac[stick_cons, LENGTH] >>
  `EL 0 m = -#1` by rw[Abbr`m`] >>
  metis_tac[]);

(* Theorem: FiniteVSpace r g op ==>
            !b. basis g b /\ (dim r g op < LENGTH b) ==> ~LinearIndepBasis r g op b *)
(* Proof:
   Idea:
   By contradiction, assume LinearIndepBasis r g op b.
   Now remove elements from basis b to become b', with LENGTH b' = dim r g op.
   Then LinearIndepBasis r g op b ==> LinearIndepBasis r g op b' by vspace_basis_indep_one_less
    and SpanSpace r g op b' = g                                  by finite_vspace_dim_basis_property
   Since the removed elements are in V,
   this means they can be expressed as linear combinations of b',
   contradicting LinearIndepBasis r g op b.
   Proof:
   Note: dim r g op < LENGTH b means SUC (dim r g op) <= LENGTH b.
   First, prove the case for LENGTH b = SUC (dim r g op)  in finite_vspace_basis_dep_special
   Then, by induction on (LENGTH b - SUC (dim r g op)).
   Base case: LENGTH b - SUC (dim r g op) = 0 ==> ~LinearIndepBasis r g op b
      Since LENGTH b - SUC (dim r g op) = 0
        ==> LENGTH b <= SUC (dim r g op)      by SUB_EQ_0
        ==> LENGTH b = SUC (dim r g op)       by given SUC (dim r g op) <= LENGTH b.
      Hence ~LinearIndepBasis r g op b        by finite_vspace_basis_dep_special

   Step case: !b r g op. (v = LENGTH b - SUC (dim r g op)) /\
              basis g b /\ dim r g op < LENGTH b ==> ~LinearIndepBasis r g op b ==>
              SUC v = LENGTH b - SUC (dim r g op) ==> ~LinearIndepBasis r g op b
      Aim is to have b = h::t, then replace b by t in induction hypothesis.
      Since dim r g op < LENGTH b, LENGTH b <> 0.
       thus ?h t. b = h::t                               by LENGTH_NIL, list_CASES
       From SUC v = LENGTH b - SUC (dim r g op)
                  = SUC (LENGTH t) - SUC (dim r g op)    by LENGTH
         so     v = LENGTH t - SUC (dim r g op)          by arithmetic
         or     SUC (dim r g op) <= LENGTH t             by 0 <= v
         or          dim r g op  < LENGTH t              by arithmetic
        Now h IN V /\ basis g t                          by basis_cons
        and LinearIndepBasis r g op t                    by vspace_basis_indep_one_less
        but ~LinearIndepBasis r g op t                   by induction hypothesis
      which is a contradiction.
*)
val finite_vspace_basis_dep = store_thm(
  "finite_vspace_basis_dep",
  ``!(r:'a field) (g:'b group) op. FiniteVSpace r g op ==>
     !b. basis g b /\ (dim r g op < LENGTH b) ==> ~LinearIndepBasis r g op b``,
  rpt strip_tac >>
  Induct_on `LENGTH b - SUC (dim r g op)` >| [
    rpt strip_tac >>
    `LENGTH b = SUC (dim r g op)` by decide_tac >>
    metis_tac[finite_vspace_basis_dep_special],
    rpt strip_tac >>
    `LENGTH b <> 0` by decide_tac >>
    `?h t. b = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `SUC v = SUC (LENGTH t) - SUC (dim r g op)` by rw[] >>
    `v = LENGTH t - SUC (dim r g op)` by decide_tac >>
    `dim r g op < LENGTH t` by decide_tac >>
    metis_tac[basis_cons, vspace_basis_indep_one_less, finite_vspace_is_vspace]
  ]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
