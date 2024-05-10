(* ------------------------------------------------------------------------- *)
(* Symmetry Group.                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "symmetry";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib; (* for stripDup *)

open pred_setTheory arithmeticTheory gcdsetTheory numberTheory
     combinatoricsTheory;

open mapCountTheory; (* for on_def *)

open monoidTheory groupTheory;
open ringTheory fieldTheory;
open subgroupTheory;
open groupMapTheory;
open ringMapTheory fieldMapTheory;

val _ = temp_overload_on("over", ``\f s t. !x. x IN s ==> f x IN t``);

(* ------------------------------------------------------------------------- *)
(* Symmetry Group Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
*)
(* Definitions and Theorems (# are exported):

   Symmetric Group:
   symmetric_group_def     |- !s. symmetric_group s =
                                  <|carrier := bij_maps s;
                                         op := (\f g. f o g on s);
                                         id := I on s
                                   |>
   symmetric_group_alt     |- !s. symmetric_group s =
                                  <|carrier := {f on s | f | f PERMUTES s};
                                         op := (\f g. f o g on s);
                                         id := I on s
                                   |>
   symmetric_group_property|- !s. (symmetric_group s).carrier = bij_maps s /\
                                  (symmetric_group s).id = I on s /\
                                  !f g. (symmetric_group s).op f g = f o g on s
   symmetric_group_carrier |- !s. (symmetric_group s).carrier = bij_maps s
   symmetric_group_id      |- !s. (symmetric_group s).id = I on s
   symmetric_group_op      |- !s f g. (symmetric_group s).op f g = f o g on s
   symmetric_group_group   |- !s. Group (symmetric_group s)
   symmetric_group_subset  |- !s. (symmetric_group s).carrier SUBSET inj_set s s
   symmetric_group_finite  |- !s. FINITE s ==> FiniteGroup (symmetric_group s)
   symmetric_group_card    |- !s. FINITE s ==>
                                  CARD (symmetric_group s).carrier = perm (CARD s)

   Maps restricted on a Set:
   monoid_homo_on_homo |- !g h f. Monoid g ==> (MonoidHomo f g h <=> MonoidHomo (f on G) g h)
   monoid_iso_on_iso   |- !g h f. Monoid g ==> (MonoidIso f g h <=> MonoidIso (f on G) g h)
   monoid_auto_on_auto |- !g f. Monoid g ==> (MonoidAuto f g <=> MonoidAuto (f on G) g)
   monoid_auto_on_id   |- !g. Monoid g ==> MonoidAuto (I on G) g
   group_homo_on_homo  |- !g h f. Group g ==> (GroupHomo f g h <=> GroupHomo (f on G) g h)
   group_iso_on_iso    |- !g h f. Group g ==> (GroupIso f g h <=> GroupIso (f on G) g h)
   group_auto_on_auto  |- !g f. Group g ==> (GroupAuto f g <=> GroupAuto (f on G) g)
   group_auto_on_id    |- !g. Group g ==> GroupAuto (I on G) g

   Automorphism Group:
   group_auto_maps_def |- !g. group_auto_maps g = {f on G | f | GroupAuto f g}
   group_auto_maps_element
                       |- !g x. x IN group_auto_maps g <=> ?f. x = f on G /\ GroupAuto f g
   group_auto_maps_alt |- !g. Group g ==>
                              group_auto_maps g = {f | f IN bij_maps G /\ GroupAuto f g}
   group_auto_maps_subset
                       |- !g. Group g ==> group_auto_maps g SUBSET bij_maps G
   group_auto_maps_finite
                       |- !g. FiniteGroup g ==> FINITE (group_auto_maps g)

   group_auto_group_def      |- !g. group_auto_group g =
                                    <|carrier := group_auto_maps g;
                                           op := (\f1 f2. f1 o f2 on G);
                                           id := I on G
                                     |>
   group_auto_group_alt      |- !g. group_auto_group g =
                                    <|carrier := {f on G | f | GroupAuto f g};
                                           op := (\f1 f2. f1 o f2 on G);
                                           id := I on G
                                     |>
   group_auto_group_property |- !g. (group_auto_group g).carrier = group_auto_maps g /\
                                    (group_auto_group g).id = I on G /\
                                    !f1 f2. (group_auto_group g).op f1 f2 = f1 o f2 on G
   group_auto_group_carrier  |- !g. (group_auto_group g).carrier = group_auto_maps g
   group_auto_group_id       |- !g. (group_auto_group g).id = I on G
   group_auto_group_op       |- !g f1 f2. (group_auto_group g).op f1 f2 = f1 o f2 on G
   group_auto_group_group    |- !g. Group g ==> Group (group_auto_group g)
   group_auto_group_subset   |- !g. Group g ==> (group_auto_group g).carrier SUBSET bij_maps G
   group_auto_group_finite   |- !g. FiniteGroup g ==> FiniteGroup (group_auto_group g)
   group_auto_group_subgroup |- !g. Group g ==> group_auto_group g <= symmetric_group G

   Maps restricted on a Set:
   ring_homo_on_homo   |- !r r_ f. Ring r ==> (RingHomo f r r_ <=> RingHomo (f on R) r r_)
   ring_iso_on_iso     |- !r r_ f. Ring r ==> (RingIso f r r_ <=> RingIso (f on R) r r_)
   ring_auto_on_auto   |- !r f. Ring r ==> (RingAuto f r <=> RingAuto (f on R) r)
   ring_auto_on_id     |- !r. Ring r ==> RingAuto (I on R) r
   field_homo_on_homo  |- !r r_ f. Field r ==> (FieldHomo f r r_ <=> FieldHomo (f on R) r r_)
   field_iso_on_iso    |- !r r_ f. Field r ==> (FieldIso f r r_ <=> FieldIso (f on R) r r_)
   field_auto_on_auto  |- !r f. Field r ==> (FieldAuto f r <=> FieldAuto (f on R) r)
   field_auto_on_id    |- !r. Field r ==> FieldAuto (I on R) r

   Symmetric Group of a Field:
   field_symmetric_group_group           |- !r. Group (symmetric_group R)
   field_nonzero_symmetric_group_group   |- !r. Group (symmetric_group R+)

   Automorphism Group of a Field:
   field_group_auto_group_group
                       |- !r. Field r ==> Group (group_auto_group f* )
   field_auto_maps_def |- !r. field_auto_maps r = {f on R | f | FieldAuto f r}
   field_auto_maps_element
                       |- !r x. x IN field_auto_maps r <=> ?f. x = f on R /\ FieldAuto f r
   field_auto_maps_alt |- !r. Field r ==>
                              field_auto_maps r = {f | f IN bij_maps R /\ FieldAuto f r}
   field_auto_maps_subset
                       |- !r. Field r ==> field_auto_maps r SUBSET bij_maps R
   field_auto_maps_finite
                       |- !r. FiniteField r ==> FINITE (field_auto_maps r)

   field_auto_group_def      |- !r. field_auto_group r =
                                    <|carrier := field_auto_maps r;
                                           op := (\f1 f2. f1 o f2 on R);
                                           id := I on R
                                     |>
   field_auto_group_alt      |- !r. field_auto_group r =
                                    <|carrier := {f on R | f | FieldAuto f r};
                                           op := (\f1 f2. f1 o f2 on R);
                                           id := I on R
                                     |>
   field_auto_group_property |- !r. (field_auto_group r).carrier = field_auto_maps r /\
                                    (field_auto_group r).id = I on R /\
                                    !f1 f2. (field_auto_group r).op f1 f2 = f1 o f2 on R
   field_auto_group_carrier  |- !r. (field_auto_group r).carrier = field_auto_maps r
   field_auto_group_id       |- !r. (field_auto_group r).id = I on R
   field_auto_group_op       |- !r f1 f2. (field_auto_group r).op f1 f2 = f1 o f2 on R
   field_auto_group_group    |- !r. Field r ==> Group (field_auto_group r)
   field_auto_group_subset   |- !r. Field r ==> (field_auto_group r).carrier SUBSET bij_maps R
   field_auto_group_finite   |- !r. FiniteField r ==> FiniteGroup (field_auto_group r)
   field_auto_group_subgroup |- !r. Field r ==> field_auto_group r <= symmetric_group R

   Map Fixing a Set:
   fixes_def           |- !f s. f fixes s <=> !x. x IN s ==> (f x = x)
   fixes_compose       |- !f g s. f fixes s /\ g fixes s ==> f o g fixes s
   fixes_I             |- !s. I fixes s
   fixes_inj_linv      |- !f s t. f fixes s /\ INJ f s t ==> LINV f s fixes s
   fixes_bij_linv      |- !f s. f fixes s /\ f PERMUTES s ==> LINV f s fixes s
   fixes_on_subset     |- !f s t. s SUBSET t ==> (f fixes s <=> f on t fixes s)
   fixes_subset_linv   |- !f s t. f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s

   Field Automorphism fixing subfield:
   subfield_auto_def           |- !f r s. subfield_auto f r s <=> FieldAuto f r /\ f fixes B
   subfield_auto_field_auto    |- !r s f. subfield_auto f r s ==> FieldAuto f r
   subfield_auto_fixes         |- !r s f. subfield_auto f r s ==> f fixes B
   subfield_auto_element       |- !r s f x. subfield_auto f r s /\ x IN R ==> f x IN R
   subfield_auto_over          |- !r s f. subfield_auto f r s ==> over f R R
   subfield_auto_bij           |- !r s f. Field r /\ subfield_auto f r s ==> f PERMUTES R
   subfield_auto_compose       |- !r s f1 f2. subfield_auto f1 r s /\ subfield_auto f2 r s ==>
                                              subfield_auto (f1 o f2) r s
   subfield_auto_I             |- !r s. subfield_auto I r s
   subfield_auto_on_compose    |- !r s f1 f2. Field r /\ B SUBSET R /\ subfield_auto f1 r s /\
                                              subfield_auto f2 r s ==> subfield_auto (f1 o f2 on R) r s
   subfield_auto_on_auto       |- !r s f. Field r /\ B SUBSET R ==>
                                          (subfield_auto f r s <=> subfield_auto (f on R) r s)
   subfield_auto_on_id         |- !r s. Field r /\ B SUBSET R ==> subfield_auto (I on R) r s
   subfield_auto_on_linv       |- !r s f. Field r /\ B SUBSET R /\ subfield_auto f r s ==>
                                          subfield_auto (LINV f R) r s /\ (LINV f R o f on R) = (I on R)

   Subfield Fixing Automorphism Group:
   subfield_auto_maps_def      |- !r s. subfield_auto_maps r s = {f on R | f | subfield_auto f r s}
   subfield_auto_maps_element  |- !r s x. x IN subfield_auto_maps r s <=>
                                      ?f. x = f on R /\ subfield_auto f r s
   subfield_auto_maps_alt      |- !r s. Field r /\ B SUBSET R ==>
                                        subfield_auto_maps r s =
                                        {f | f IN bij_maps R /\ subfield_auto f r s}
   subfield_auto_maps_subset   |- !r s. Field r /\ B SUBSET R ==>
                                        subfield_auto_maps r s SUBSET bij_maps R
   subfield_auto_maps_finite   |- !r s. FiniteField r /\ B SUBSET R ==>
                                        FINITE (subfield_auto_maps r s)

   subfield_auto_group_def     |- !r s. subfield_auto_group r s =
                                        <|carrier := subfield_auto_maps r s;
                                               op := (\f1 f2. f1 o f2 on R);
                                               id := I on R
                                         |>
   subfield_auto_group_alt     |- !r s. subfield_auto_group r s =
                                        <|carrier := subfield_auto_maps r s;
                                               op := (\f1 f2. f1 o f2 on R);
                                               id := I on R
                                         |>
   subfield_auto_group_property|- !r s. (subfield_auto_group r s).carrier = subfield_auto_maps r s /\
                                        (subfield_auto_group r s).id = I on R /\
                                        !f1 f2. (subfield_auto_group r s).op f1 f2 = f1 o f2 on R
   subfield_auto_group_carrier |- !r s. (subfield_auto_group r s).carrier = subfield_auto_maps r s
   subfield_auto_group_id      |- !r s. (subfield_auto_group r s).id = I on R
   subfield_auto_group_op      |- !r s f1 f2. (subfield_auto_group r s).op f1 f2 = f1 o f2 on R
   subfield_auto_group_group   |- !r s. Field r /\ B SUBSET R ==> Group (subfield_auto_group r s)
   subfield_auto_group_subset  |- !r s. Field r /\ B SUBSET R ==>
                                        (subfield_auto_group r s).carrier SUBSET bij_maps R
   subfield_auto_group_finite  |- !r s. FiniteField r /\ B SUBSET R ==>
                                        FiniteGroup (subfield_auto_group r s)
   subfield_auto_group_subgroup|- !r s. Field r /\ B SUBSET R ==>
                                        subfield_auto_group r s <= symmetric_group R
   subfield_auto_group_group_1 |- !r s. Field r /\ subfield s r ==> Group (subfield_auto_group r s)
   subfield_auto_group_group_2 |- !r s. s <<= r ==> Group (subfield_auto_group r s)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Symmetric Group                                                           *)
(* ------------------------------------------------------------------------- *)

(*
Given a finite set s of cardinality n,
the set of bijections (permutations) form a group under composition,
called the symmetric group Sym(n), or simply S_n.
*)

(* Define symmetric group *)
Definition symmetric_group_def:
   symmetric_group s =
      <| carrier := bij_maps s;
              op := (\f g. (f o g) on s);
              id := (I on s)
       |>
End

(* Theorem: another representation of symmetric_group. *)
(* Proof: by symmetric_group_def, bij_maps_thm. *)
Theorem symmetric_group_alt:
  !s. symmetric_group s =
      <| carrier := {f on s | f | f PERMUTES s};
              op := (\f g. (f o g) on s);
              id := (I on s)
       |>
Proof
  simp[symmetric_group_def, bij_maps_thm]
QED

(* Theorem: properties of (symmetric_group s). *)
(* Proof: by symmetric_group_def *)
Theorem symmetric_group_property:
  !s. (symmetric_group s).carrier = bij_maps s /\
      (symmetric_group s).id = I on s /\
      !f g. (symmetric_group s).op f g = f o g on s
Proof
  simp[symmetric_group_def]
QED

(* Derive theorems. *)
Theorem symmetric_group_carrier =
   symmetric_group_property |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val symmetric_group_carrier = |- !s. (symmetric_group s).carrier = bij_maps s: thm *)

Theorem symmetric_group_id =
   symmetric_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> GEN_ALL;
(* val symmetric_group_id = |- !s. (symmetric_group s).id = I on s: thm *)

Theorem symmetric_group_op =
   symmetric_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> GEN_ALL;
(* val symmetric_group_op = |- !s f g. (symmetric_group s).op f g = f o g on s: thm *)

(* Theorem: Group (symmetric_group s) *)
(* Proof:
   By group_def_alt, symmetric_group_def, bij_maps_element, this is to show:
   (1) f PERMUTES s /\ g PERMUTES s ==>
       ?x. (f on s) o (g on s) on s = x on s /\ x PERMUTES s
       Take x = f o g.
       Then (f on s) o (g on s) on s = x on s
                                         by on_on_compose, over_bij
        and x PERMUTES s                 by BIJ_COMPOSE
   (2) f PERMUTES s /\ g PERMUTES s /\ h PERMUTES s ==>
       ((f on s) o (g on s) on s) o (h on s) on s =
        (f on s) o ((g on s) o (h on s) on s) on s
       Note (f on s) PERMUTES s          by on_bij
        and (g on s) PERMUTES s          by on_bij
        and (h on s) PERMUTES s          by on_bij
       This is true                      by bij_on_compose_assoc
   (3) ?f. I on s = f on s /\ f PERMUTES s
       Let f = I.
       Then I PERMUTES s                 by BIJ_I_SAME
   (4) f PERMUTES s ==> (I on s) o (f on s) on s = f on s
       Note over f s s                   by over_bij
         (I on s) o (f on s) on s
       = (I o f) on s                    by on_on_compose
       = f on s                          by I_o_ID
   (5) f PERMUTES s ==> ?y. (?x. (y = x on s) /\ x PERMUTES s) /\ (y o (f on s) on s = I on s)
       Let y = (LINV f s) on s. Then this is to show:
       (1) ?x. LINV f s on s = x on s /\ x PERMUTES s
           Let x = LINV f s.
           Then x PERMUTES s             by BIJ_LINV_BIJ
       (2) (LINV f s on s) o (f on s) on s = I on s
           Note over f s s               by over_bij
             (LINV f s on s) o (f on s) on s
           = (LINV f s o f) on s         by on_on_compose
           = I on s                      by bij_on_linv
*)
Theorem symmetric_group_group:
  !s. Group (symmetric_group s)
Proof
  rw_tac std_ss[group_def_alt, symmetric_group_def, bij_maps_element, GSPECIFICATION] >| [
    qexists_tac `f o f'` >>
    metis_tac[on_on_compose, over_bij, BIJ_COMPOSE],
    simp[on_bij, bij_on_compose_assoc],
    metis_tac[BIJ_I_SAME],
    `over f s s` by metis_tac[over_bij] >>
    rw[on_on_compose],
    qexists_tac `(LINV f s) on s` >>
    rpt strip_tac >-
    metis_tac[BIJ_LINV_BIJ] >>
    metis_tac[on_on_compose, bij_on_linv, over_bij]
  ]
QED

(* This is a very good result! *)

(* Theorem: (symmetric_group s).carrier SUBSET inj_set s s *)
(* Proof: symmetric_group_carrier, bij_maps_subset. *)
Theorem symmetric_group_subset:
  !s. (symmetric_group s).carrier SUBSET inj_set s s
Proof
  simp[symmetric_group_carrier, bij_maps_subset]
QED

(* Theorem: FINITE s ==> FiniteGroup (symmetric_group s) *)
(* Proof:
   Note (symmetric_group s).carrier = bij_maps s   by symmetric_group_carrier
    and FINITE (bij_maps s)                        by bij_maps_finite
    and Group (symmetric_group s)                  by symmetric_group_group
   Thus FiniteGroup (symmetric_group s)            by FiniteGroup_def
*)
Theorem symmetric_group_finite:
  !s. FINITE s ==> FiniteGroup (symmetric_group s)
Proof
  simp[FiniteGroup_def, symmetric_group_carrier, bij_maps_finite, symmetric_group_group]
QED

(* Theorem: FINITE s ==> CARD (symmetric_group s).carrier = perm (CARD s) *)
(* Proof:
     CARD (symmetric_group s).carrier
   = CARD (bij_maps s)                   by symmetric_group_carrier
   = perm (CARD s)                       by bij_maps_card
*)
Theorem symmetric_group_card:
  !s. FINITE s ==> CARD (symmetric_group s).carrier = perm (CARD s)
Proof
  simp[symmetric_group_carrier, bij_maps_card]
QED

(* ------------------------------------------------------------------------- *)
(* Maps restricted on a Set                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Monoid g ==> (MonoidHomo f g h <=> MonoidHomo (f on G) g h) *)
(* Proof:
       MonoidHomo f g h
   <=> over f G h.carrier /\ P f   by MonoidHomo_def
   <=> over (f on G) G h.carrier /\ P (f on G)
                                   by on_def, monoid_op_element, monoid_id_element
   <=> Monoid (f on G) g h         by MonoidHomo_def
*)
Theorem monoid_homo_on_homo:
  !(g:'a monoid) (h:'b monoid).
  !f. Monoid g ==> (MonoidHomo f g h <=> MonoidHomo (f on G) g h)
Proof
  simp[MonoidHomo_def, on_def, monoid_op_element, monoid_id_element]
QED

(* Theorem: Monoid g ==> (MonoidIso f g h <=> MonoidIso (f on G) g h) *)
(* Proof:
       MonoidIso f g h
     = MonoidHomo f g h /\ BIJ f G h.carrier                by MonoidIso_def
   <=> MonoidHomo f g h /\ BIJ (f on G) G h.carrier         by on_bij
   <=> MonoidHomo (f on G) g h /\ BIJ (f on G) G h.carrier  by monoid_homo_on_homo
     = MonoidIso (f on G) g h                               by MonoidIso_def
*)
Theorem monoid_iso_on_iso:
  !(g:'a monoid) (h:'b monoid).
  !f. Monoid g ==> (MonoidIso f g h <=> MonoidIso (f on G) g h)
Proof
  metis_tac[MonoidIso_def, on_bij, monoid_homo_on_homo]
QED

(* Theorem: Monoid g ==> (MonoidAuto f g <=> MonoidAuto (f on G) g) *)
(* Proof:
       MonoidAuto f g
   <=> MonoidIso f g g         by MonoidAuto_def
   <=> MonoidIso (f on G) g g  by monoid_iso_on_iso
   <=> MonoidAuto (f on G) g   by MonoidIso_def
*)
Theorem monoid_auto_on_auto:
  !g:'a monoid. !f. Monoid g ==> (MonoidAuto f g <=> MonoidAuto (f on G) g)
Proof
  metis_tac[MonoidAuto_def, monoid_iso_on_iso]
QED

(* Theorem: Monoid g ==> MonoidAuto (I on G) g *)
(* Proof:
   Note MonoidAuto I g         by monoid_auto_I
   Thus MonoidAuto (I on G) g  by monoid_auto_on_auto
*)
Theorem monoid_auto_on_id:
  !(g:'a monoid). Monoid g ==> MonoidAuto (I on G) g
Proof
  metis_tac[monoid_auto_I, monoid_auto_on_auto]
QED

(* Theorem: Group g ==> (GroupHomo f g h <=> GroupHomo (f on G) g h) *)
(* Proof:
       GroupHomo f g h
   <=> over f G h.carrier /\ P f   by GroupHomo_def
   <=> over (f on G) G h.carrier /\ P (f on G)
                                   by on_def, group_op_element
   <=> GroupHomo (f on G) g h      by GroupHomo_def
*)
Theorem group_homo_on_homo:
  !(g:'a group) (h:'b group).
  !f. Group g ==> (GroupHomo f g h <=> GroupHomo (f on G) g h)
Proof
  simp[GroupHomo_def, on_def, group_op_element]
QED

(* Theorem: Group g /\ GroupIso f g h ==> GroupIso (f on G) g h *)
(* Proof:
       GroupIso f g h
     = GroupHomo f g h /\ BIJ f G h.carrier                by GroupIso_def
   <=> GroupHomo f g h /\ BIJ (f on G) G h.carrier         by on_bij
   <=> GroupHomo (f on G) g h /\ BIJ (f on G) G h.carrier  by group_homo_on_homo
     = GroupIso (f on G) g h                               by GroupIso_def
*)
Theorem group_iso_on_iso:
  !(g:'a group) (h:'b group).
  !f. Group g ==> (GroupIso f g h <=> GroupIso (f on G) g h)
Proof
  metis_tac[GroupIso_def, on_bij, group_homo_on_homo]
QED

(* Theorem: Group g ==> (GroupAuto f g <=> GroupAuto (f on G) g) *)
(* Proof:
       GroupAuto f g
   <=> GroupIso f g g          by GroupAuto_def
   <=> GroupIso (f on G) g g   by group_iso_on_iso
   <=> GroupAuto (f on G) g    by GroupAuto_def
*)
Theorem group_auto_on_auto:
  !g:'a group.
  !f. Group g ==> (GroupAuto f g <=> GroupAuto (f on G) g)
Proof
  metis_tac[GroupAuto_def, group_iso_on_iso]
QED

(* Theorem: Group g ==> GroupAuto (I on G) g *)
(* Proof:
   Note GroupAuto I g          by group_auto_I
   Thus GroupAuto (I on G) g   by group_auto_on_auto
*)
Theorem group_auto_on_id:
  !(g:'a group). Group g ==> GroupAuto (I on G) g
Proof
  metis_tac[group_auto_I, group_auto_on_auto]
QED

(* ------------------------------------------------------------------------- *)
(* Automorphism Group                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the set of group automorphisms. *)
Definition group_auto_maps_def[nocompute]:
    group_auto_maps (g:'a group) = {f on G | f | GroupAuto f g}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN group_auto_maps g <=> ?f. x = f on G /\ GroupAuto f g *)
(* Proof: by group_auto_maps_def. *)
Theorem group_auto_maps_element:
  !g:'a group. !x. x IN group_auto_maps g <=> ?f. x = f on G /\ GroupAuto f g
Proof
  simp[group_auto_maps_def]
QED

(* Theorem: Group g ==> group_auto_maps g = {f | f IN fun_set G G /\ GroupAuto f g} *)
(* Proof:
   By group_auto_maps_def, fun_set_element, EXTENSION, this is to show:
   (1) GroupAuto f g ==> ?x. f on G = x on G /\ over x G G
       Take x = f, then over f G G       by group_auto_element
   (2) GroupAuto f g ==> GroupAuto (f on G) g
       This is true                      by group_auto_on_auto
   (3) GroupAuto (f on G) g ==> ?x. f on G = x on G /\ GroupAuto x g
       Take x = f, then GroupAuto f g    by group_auto_on_auto
*)

(* Theorem: Group g ==> group_auto_maps g = {f | f IN bij_maps G /\ GroupAuto f g} *)
(* Proof:
   By group_auto_maps_def, fun_set_element, EXTENSION, this is to show:
   (1) GroupAuto f g ==> ?x. f on G = x on G /\ x PERMUTES G
       Take x = f, then f PERMUTES G     by group_auto_bij
   (2) GroupAuto f g ==> GroupAuto (f on G) g
       This is true                      by group_auto_on_auto
   (3) GroupAuto (f on G) g ==> ?x. f on G = x on G /\ GroupAuto x g
       Take x = f, then GroupAuto f g    by group_auto_on_auto
*)
Theorem group_auto_maps_alt:
  !g:'a group. Group g ==> group_auto_maps g = {f | f IN bij_maps G /\ GroupAuto f g}
Proof
  simp[group_auto_maps_def, bij_maps_element, EXTENSION] >>
  metis_tac[group_auto_bij, group_auto_on_auto]
QED

(* Theorem: Group g ==> (group_auto_maps g) SUBSET bij_maps G *)
(* Proof: by group_auto_maps_alt, SUBSET_DEF. *)
Theorem group_auto_maps_subset:
  !g:'a group. Group g ==> (group_auto_maps g) SUBSET bij_maps G
Proof
  simp[group_auto_maps_alt, SUBSET_DEF]
QED

(* Theorem: FiniteGroup g ==> FINITE (group_auto_maps g) *)
(* Proof:
   Note FINITE G /\ Group g                    by FiniteGroup_def
     so (group_auto_maps g) SUBSET bij_maps G  by group_auto_maps_subset
    and FINITE (bij_maps G)                    by bij_maps_finite
     so FINITE (group_auto_maps g)             by SUBSET_FINITE
*)
Theorem group_auto_maps_finite:
  !g:'a group. FiniteGroup g ==> FINITE (group_auto_maps g)
Proof
  metis_tac[FiniteGroup_def, group_auto_maps_subset, bij_maps_finite, SUBSET_FINITE]
QED

(* All automorphisms of a Group form a Group. *)
Definition group_auto_group_def:
   group_auto_group (g:'a group) =
      <| carrier := group_auto_maps g;
              op := (\f1 f2. (f1 o f2) on G);
              id := I on G
       |>
End

(* Theorem: another representation of group_auto_group. *)
(* Proof: by group_auto_group_def, group_auto_maps_def. *)
Theorem group_auto_group_alt:
  !g:'a group. group_auto_group g =
      <|carrier := {f on G | f | GroupAuto f g};
             op := (\f1 f2. f1 o f2 on G);
             id := I on G
       |>
Proof
  simp[group_auto_group_def, group_auto_maps_def]
QED

(* Theorem: Properties of (group_auto_group g) *)
(* Proof: by group_auto_group_def. *)
Theorem group_auto_group_property:
  !g:'a group. (group_auto_group g).carrier = group_auto_maps g /\
               (group_auto_group g).id = I on G /\
               !f1 f2. (group_auto_group g).op f1 f2 = (f1 o f2) on G
Proof
  simp[group_auto_group_def]
QED

(* Derive theorems. *)
Theorem group_auto_group_carrier =
   group_auto_group_property |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val group_auto_group_carrier = |- !g. (group_auto_group g).carrier = auto_maps g: thm *)

Theorem group_auto_group_id =
   group_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> GEN_ALL;
(* val group_auto_group_id = |- !g. (group_auto_group g).id = I on G: thm *)

Theorem group_auto_group_op =
   group_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> GEN_ALL;
(* val group_auto_group_op = |- !g f1 f2. (group_auto_group g).op f1 f2 = f1 o f2 on G: thm *)

(* Theorem: Group g ==> Group (group_auto_group g) *)
(* Proof:
   By group_def_alt, group_auto_group_def, this is to show:
   (1) GroupAuto f1 g /\ GroupAuto f2 g ==>
       ?f. ((f1 on G) o (f2 on G) on G = f on G) /\ GroupAuto f g
       Let f = f1 o f2.
       Note f1 PERMUTES G /\ f2 PERMUTES G         by group_auto_bij
       Then (f1 on G) o (f2 on G) on G = f on G    by on_on_compose, over_bij
        and GroupAuto f g                          by group_auto_compose
   (2) GroupAuto f g /\ GroupAuto f' g /\ GroupAuto f'' g ==>
       ((f on G) o (f' on G) on G) o (f'' on G) on G = (f on G) o ((f' on G) o (f'' on G) on G) on G
       Note f PERMUTES G /\ f' PERMUTES G /\ f'' PERMUTES G
                                                   by group_auto_bij
       The result follows                          by bij_on_compose_assoc, on_bij
   (3) ?f. (I on G = f on G) /\ GroupAuto f g
       Let f = I, then GroupAuto I g               by group_auto_I
   (4) (I on G) o (f on G) on G = f on G
       Note f PERMUTES G                           by group_auto_bij
        and over f G G                             by over_bij
         (I on G) o (f on G) on G
       = (I o f) on G                              by bij_on_compose
       = f on G                                    by I_o_ID
   (5) GroupAuto f g ==> ?y. (?f. (y = f on G) /\ GroupAuto f g) /\ (y o (f on G) on G = I on G)
       Let y = (LINV f G) on G, Then
       (1) Let f = LINV f G, then GroupAuto f g    by group_auto_linv_auto
       (2) GroupAuto f g ==> (LINV f G on G) o (f on G) on G = I on G
           Note f PERMUTES G                       by group_auto_bij
             (LINV f G on G) o (f on G) on s
           = (LINV f G o f) on G                   by bij_on_compose
           = I on G                                by bij_on_linv
*)
Theorem group_auto_group_group:
  !g:'a group. Group g ==> Group (group_auto_group g)
Proof
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, group_auto_group_def, group_auto_maps_element, GSPECIFICATION] >| [
    qexists_tac `f o f'` >>
    rpt strip_tac >-
    metis_tac[group_auto_bij, on_on_compose, over_bij] >>
    simp[group_auto_compose],
    metis_tac[group_auto_bij, on_bij, bij_on_compose_assoc],
    metis_tac[group_auto_I],
    `f PERMUTES G /\ !x. x IN G ==> f x IN G` by metis_tac[group_auto_bij, over_bij] >>
    rw[bij_on_compose],
    qexists_tac `(LINV f G) on G` >>
    rpt strip_tac >-
    metis_tac[group_auto_linv_auto] >>
    metis_tac[bij_on_compose, bij_on_linv, group_auto_bij]
  ]
QED

(* Another major result. *)

(* Theorem: Group g ==> (group_auto_group g).carrier SUBSET bij_maps G *)
(* Proof: by group_auto_group_carrier, group_auto_maps_subset. *)
Theorem group_auto_group_subset:
  !g:'a group. Group g ==> (group_auto_group g).carrier SUBSET bij_maps G
Proof
  simp[group_auto_group_carrier, group_auto_maps_subset]
QED

(* Theorem: FiniteGroup g ==> FiniteGroup (group_auto_group g) *)
(* Proof:
   Note (group_auto_group g).carrier = group_auto_maps g
                                               by group_auto_group_carrier
    and FINITE (group_auto_maps g)             by group_auto_maps_finite
    and Group (group_auto_group g)             by group_auto_group_group
   Thus FiniteGroup (group_auto_group g)       by FiniteGroup_def
*)
Theorem group_auto_group_finite:
  !g:'a group. FiniteGroup g ==> FiniteGroup (group_auto_group g)
Proof
  simp[FiniteGroup_def, group_auto_group_carrier, group_auto_maps_finite, group_auto_group_group]
QED

(* Theorem: Group g ==> group_auto_group g <= symmetric_group G *)
(* Proof:
   Note Group (group_auto_group g)                     by group_auto_group_group
    and Group (symmetric_group G)                      by symmetric_group_group
   Note (group_auto_group g).carrier = group_auto_maps g
                                                       by group_auto_group_carrier
    and (symmetric_group G).carrier = bij_maps G       by symmetric_group_carrier
    and group_auto_maps g SUBSET bij_maps G            by group_auto_maps_subset
    and (group_auto_group g).op = (symmetric_group G).op
                                                       by symmetric_group_op,
                                                          group_auto_group_op, FUN_EQ_THM
   Thus (group_auto_group g) <= (symmetric_group G)    by Subgroup_def
*)
Theorem group_auto_group_subgroup:
  !g:'a group. Group g ==> group_auto_group g <= symmetric_group G
Proof
  simp[Subgroup_def] >>
  simp[group_auto_group_group, symmetric_group_group,
        group_auto_group_property, symmetric_group_property,
        FUN_EQ_THM, group_auto_maps_subset]
QED

(* ------------------------------------------------------------------------- *)
(* Field Symmetry Group                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Maps restricted on a Set                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> (RingHomo f r r_ <=> RingHomo (f on R) r r_) *)
(* Proof:
   Note Group r.sum                            by ring_add_group
    and Monoid r.prod                          by ring_mult_monoid
       RingHomo f r r_
   <=> over f R R_ /\ GroupHomo f r.sum r_.sum /\ MonoidHomo f r.prod r_.prod
                                               by RingHomo_def
   <=> over (f on R) R R_ /\                   by on_over
       GroupHomo (f on R) r.sum r_.sum  /\     by group_homo_on_homo, ring_carriers
       MonoidHomo (f on R) r.prod r_.prod      by monoid_homo_on_homo, ring_carriers
   <=> RingHomo (f on R) r r_                  by RingHomo_def\
*)
Theorem ring_homo_on_homo:
  !(r:'a ring) (r_:'b ring) f. Ring r ==> (RingHomo f r r_ <=> RingHomo (f on R) r r_)
Proof
  rw[RingHomo_def] >>
  `Group r.sum /\ Monoid r.prod` by rw[ring_add_group, ring_mult_monoid] >>
  `r.sum.carrier = R /\ r.prod.carrier = R` by rw[ring_carriers] >>
  metis_tac[on_over, group_homo_on_homo, monoid_homo_on_homo]
QED

(* Theorem: Ring r ==> (RingIso f r r_ <=> RingIso (f on R) r r_) *)
(* Proof:
       RingIso f r r_
   <=> RingHomo f r r_  /\ BIJ f R R_                by RingIso_def
   <=> RingHomo (f on R) r r_ /\ BIJ f R R_          by ring_homo_on_homo
   <=> RingHomo (f on R) r r_ /\ BIJ (f on R) R R_   by on_bij
   <=> RingIso (f on R) r r_                         by RingIso_def
*)
Theorem ring_iso_on_iso:
  !(r:'a ring) (r_:'b ring) f. Ring r ==> (RingIso f r r_ <=> RingIso (f on R) r r_)
Proof
  metis_tac[RingIso_def, ring_homo_on_homo, on_bij]
QED

(* Theorem: Ring r ==> (RingAuto f r <=> RingAuto (f on R) r) *)
(* Proof:
       RingAuto f r
   <=> RingIso f r r               by RingAuto_def
   <=> RingIso (f on R) r r_       by ring_iso_on_iso
   <=> RingAuto (f on R) r r_      by RingAuto_def
*)
Theorem ring_auto_on_auto:
  !(r:'a ring) f. Ring r ==> (RingAuto f r <=> RingAuto (f on R) r)
Proof
  metis_tac[RingAuto_def, ring_iso_on_iso]
QED

(* Theorem: Ring r ==> RingAuto (I on R) r *)
(* Proof:
       Ring r
   ==> RingAuto I r          by ring_auto_I
   ==> RingAuto (I on R) r   by ring_auto_on_auto
*)
Theorem ring_auto_on_id:
  !(r:'a ring). Ring r ==> RingAuto (I on R) r
Proof
  metis_tac[ring_auto_I, ring_auto_on_auto]
QED

(* Theorem: Field r ==> (FieldHomo f r r_ <=> FieldHomo (f on R) r r_) *)
(* Proof:
   Note Ring r                     by field_is_ring
       FieldHomo f r r_
   <=> RingHomo f r r_             by field_homo_eq_ring_homo
   <=> RingHomo (f on R) r r_      by ring_homo_on_homo
   <=> FieldHomo (f on R) r r_     by field_homo_eq_ring_homo
*)
Theorem field_homo_on_homo:
  !(r:'a field) (r_:'b field) f. Field r ==> (FieldHomo f r r_ <=> FieldHomo (f on R) r r_)
Proof
  metis_tac[field_homo_eq_ring_homo, field_is_ring, ring_homo_on_homo]
QED

(* Theorem: Field r ==> (FieldIso f r r_ <=> FieldIso (f on R) r r_) *)
(* Proof:
   Note Ring r                     by field_is_ring
       FieldIso f r r_
   <=> RingIso f r r_              by field_iso_eq_ring_iso
   <=> RingIso (f on R) r r_       by ring_iso_on_iso
   <=> FieldIso (f on R) r r_      by field_iso_eq_ring_iso
*)
Theorem field_iso_on_iso:
  !(r:'a field) (r_:'b field) f. Field r ==> (FieldIso f r r_ <=> FieldIso (f on R) r r_)
Proof
  metis_tac[field_iso_eq_ring_iso, field_is_ring, ring_iso_on_iso]
QED

(* Theorem: Field r ==> (FieldAuto f r <=> FieldAuto (f on R) r) *)
(* Proof:
       FieldAuto f r
   <=> FieldIso f r r             by FieldAuto_def
   <=> FieldIso (f on R) r r_     by field_iso_on_iso
   <=> FieldAuto (f on R) r r_    by FieldAuto_def
*)
Theorem field_auto_on_auto:
  !(r:'a field) f. Field r ==> (FieldAuto f r <=> FieldAuto (f on R) r)
Proof
  metis_tac[FieldAuto_def, field_iso_on_iso]
QED

(* Theorem: Field r ==> FieldAuto (I on R) r *)
(* Proof:
       Field r
   ==> FieldAuto I r           by field_auto_I
   ==> FieldAuto (I on R) r    by field_auto_on_auto
*)
Theorem field_auto_on_id:
  !(r:'a field). Field r ==> FieldAuto (I on R) r
Proof
  metis_tac[field_auto_I, field_auto_on_auto]
QED

(* ------------------------------------------------------------------------- *)
(* Symmetric Group of a Field                                                *)
(* ------------------------------------------------------------------------- *)

(* All permutations of a field form the Symmetric Group. *)

(* Theorem: Group (symmetric_group R) *)
(* Proof: by symmetric_group_group *)
Theorem field_symmetric_group_group:
  !r:'a field. Group (symmetric_group R)
Proof
  simp[symmetric_group_group]
QED

(* Theorem: Group (symmetric_group R+) *)
(* Proof: by symmetric_group_group.
   Both Group (symmetric_group R)
    and Group (symmetric_group R+) are true
    due to BIJ f R R must map #0 to #0 uniquely,
    and a bijection taking out #0 <-> #0 is still a bijection.
*)
Theorem field_nonzero_symmetric_group_group:
  !r:'a field. Group (symmetric_group R+)
Proof
  simp[symmetric_group_group]
QED

(* ------------------------------------------------------------------------- *)
(* Automorphism Group of a Field                                             *)
(* ------------------------------------------------------------------------- *)

(* All automorphisms of a field form the Automorphism Group. *)

(* Theorem: Field r ==> Group (group_auto_group f* )  *)
(* Proof:
   Note Group f*                         by field_mult_group
   Thus Group (group_auto_group f* )     by group_auto_group_group
*)
Theorem field_group_auto_group_group:
  !r:'a field. Field r ==> Group (group_auto_group f* )
Proof
  simp[field_mult_group, group_auto_group_group]
QED

(* This is true, but this is not the aim. *)

(* Define the set of all field automorphism maps. *)
Definition field_auto_maps_def[nocompute]:
    field_auto_maps (r:'a field) = {f on R | f | FieldAuto f r}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN field_auto_maps r <=> ?f. x = f on R /\ FieldAuto f r *)
(* Proof: by field_auto_maps_def. *)
Theorem field_auto_maps_element:
  !r:'a field. !x. x IN field_auto_maps r <=> ?f. x = f on R /\ FieldAuto f r
Proof
  simp[field_auto_maps_def]
QED

(* Theorem: Field r ==>
            field_auto_maps r = {f | f IN bij_maps R /\ FieldAuto f r} *)
(* Proof:
   By field_auto_maps_def, bij_maps_element, EXTENSION, this is to show:
   (1) FieldAuto f r ==> ?x. f on R = x on R /\ x PERMUTES R
       Take x = f, then f PERMUTES R     by field_auto_bij
   (2) FieldAuto f r ==> FieldAuto (f on R) r
       This is true                      by field_auto_on_auto
   (3) FieldAuto (f on R) r ==> ?x. f on R = x on R /\ FieldAuto x r
       Take x = f, then FieldAuto f r    by field_auto_on_auto
*)
Theorem field_auto_maps_alt:
  !r:'a field. Field r ==>
        field_auto_maps r = {f | f IN bij_maps R /\ FieldAuto f r}
Proof
  simp[field_auto_maps_def, bij_maps_element, EXTENSION] >>
  metis_tac[field_auto_bij, field_auto_on_auto]
QED

(* Theorem: Field r ==> (field_auto_maps r) SUBSET bij_maps R *)
(* Proof: by field_auto_maps_alt, SUBSET_DEF. *)
Theorem field_auto_maps_subset:
  !r:'a field. Field r ==> (field_auto_maps r) SUBSET bij_maps R
Proof
  simp[field_auto_maps_alt, SUBSET_DEF]
QED

(* Theorem: FiniteField r ==> FINITE (field_auto_maps r) *)
(* Proof:
   Note FINITE R /\ Field r                    by FiniteField_def
     so (field_auto_maps r) SUBSET bij_maps R  by field_auto_maps_subset
    and FINITE (bij_maps R)                    by bij_maps_finite
     so FINITE (field_auto_maps r)             by SUBSET_FINITE
*)
Theorem field_auto_maps_finite:
  !r:'a field. FiniteField r ==> FINITE (field_auto_maps r)
Proof
  metis_tac[FiniteField_def, field_auto_maps_subset, bij_maps_finite, SUBSET_FINITE]
QED

(* All automorphisms of a Field form a Group. *)
Definition field_auto_group_def:
   field_auto_group (r:'a field) =
      <| carrier := field_auto_maps r;
              op := \f1 f2. (f1 o f2) on R;
              id := (I on R)
       |>
End

(* Theorem: another representation of field_auto_group. *)
(* Proof: by field_auto_group_def, field_auto_maps_def. *)
Theorem field_auto_group_alt:
  !r:'a field. field_auto_group r =
               <|carrier := {f on R | f | FieldAuto f r};
                      op := (\f1 f2. f1 o f2 on R);
                      id := (I on R)
                |>
Proof
  simp[field_auto_group_def, field_auto_maps_def]
QED

(* Theorem: Properties of (field_auto_group r) *)
(* Proof: by field_auto_group_def. *)
Theorem field_auto_group_property:
  !r:'a field. (field_auto_group r).carrier = field_auto_maps r /\
               (field_auto_group r).id = I on R /\
               !f1 f2. (field_auto_group r).op f1 f2 = (f1 o f2) on R
Proof
  simp[field_auto_group_def]
QED

(* Derive theorems. *)
Theorem field_auto_group_carrier =
   field_auto_group_property |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val field_auto_group_carrier = |- !r. (field_auto_group r).carrier = field_auto_maps r: thm *)

Theorem field_auto_group_id =
   field_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> GEN_ALL;
(* val field_auto_group_id = |- !r. (field_auto_group r).id = I on R: thm *)

Theorem field_auto_group_op =
   field_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> GEN_ALL;
(* val field_auto_group_op = |- !r f1 f2. (field_auto_group r).op f1 f2 = f1 o f2 on R: thm *)

(* Theorem: Field r ==> Group (field_auto_group r) *)
(* Proof:
   By group_def_alt, field_auto_group_def, field_auto_maps_def, this is to show:
   (1) FieldAuto f r /\ FieldAuto f' r ==> ?f''. ((f on R) o (f' on R) on R) = (f'' on R) /\ FieldAuto f'' r
       Let f'' = f o f' on R.
       Note f PERMUTES R /\ f' PERMUTES R                    by field_auto_bij
       Then (f on R) o (f' on R) on R = (f o f' on R) on R   by bij_on_compose, on_on
        and FieldAuto (f o f' on R) r                        by field_auto_compose, field_auto_on_auto
   (2) FieldAuto f r /\ FieldAuto f' r  /\ FieldAuto f'' r ==>
       (((f on R) o (f' on R) on R) o (f'' on R) on R) = ((f on R) o ((f' on R) o (f'' on R) on R) on R)
       Note f PERMUTES R /\ f' PERMUTES R /\ f'' PERMUTES R  by field_auto_bij
       The result follows                                    by bij_on_compose_assoc, bij_on_bij
   (3) ?f. (I on R) = (f on R) /\ FieldAuto f r
       Let f = I, then FieldAuto I g                         by field_auto_I
   (4) ((I on R) o (f on R) on R) = (f on R)
       Note over f R R                                       by field_auto_bij, over_bij
         (I on R) o (f on R) on R
       = (I o f) on R                                        by on_on_compose
       = f on R                                              by I_o_ID
   (5) FieldAuto f r ==> ?y. (?f. y = (f on R) /\ FieldAuto f r) /\ (y o (f on R) on R) = (I on R)
       Let y = (LINV f R) on R, Then
       (1) Let f = LINV f R, then FieldAuto f g              by field_auto_linv_auto
       (2) FieldAuto f r ==> (LINV f R on R) o (f on R) on R = I on R
           Note f PERMUTES R                                 by field_auto_bij
             (LINV f R on R) o (f on R) on R
           = (LINV f R o f) on R                             by bij_on_compose
           = I on R                                          by bij_on_linv
*)
Theorem field_auto_group_group:
  !r:'a field. Field r ==> Group (field_auto_group r)
Proof
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, field_auto_group_def, field_auto_maps_def,
                GSPECIFICATION] >|
  [
    rename [‘(f1 on R) o (f2 on R)’] >>
    qexists_tac `f1 o f2 on R` >>
    rpt strip_tac >-
    metis_tac[bij_on_compose, on_on, field_auto_bij] >>
    metis_tac[field_auto_compose, field_auto_on_auto],

    rename [‘((f1 on R) o (f2 on R) on R) o (f3 on R) on R’] >>
    `f1 PERMUTES R /\ f2 PERMUTES R /\ f3 PERMUTES R` by rw[field_auto_bij] >>
    metis_tac[bij_on_bij, bij_on_compose_assoc],

    metis_tac[field_auto_I],

    rename [‘f on R’, ‘FieldAuto f r’] >>
    `over f R R` by metis_tac[field_auto_bij, over_bij] >>
    rw[on_on_compose],

    rename [‘FieldAuto f r’] >>
    qexists_tac `(LINV f R) on R` >>
    rpt strip_tac >-
    metis_tac[field_auto_linv_auto] >>
    metis_tac[bij_on_compose, bij_on_linv, field_auto_bij]
  ]
QED

(* Another fine result. *)

(* Theorem: Field r ==> (field_auto_group r).carrier SUBSET bij_maps R *)
(* Proof: field_auto_group_carrier, field_auto_maps_subset. *)
Theorem field_auto_group_subset:
  !r:'a field. Field r ==> (field_auto_group r).carrier SUBSET bij_maps R
Proof
  simp[field_auto_group_carrier, field_auto_maps_subset]
QED

(* Theorem: FiniteField r ==> FiniteGroup (field_auto_group r) *)
(* Proof:
   Note FINITE R /\ Field r                            by FiniteField_def
   Note (field_auto_group r).carrier = field_auto_maps r
                                                       by field_auto_group_carrier
    and FINITE (field_auto_maps r)                     by field_auto_maps_finite
    and Group (field_auto_group r)                     by field_auto_group_group
   Thus FiniteGroup (field_auto_group r)               by FiniteGroup_def
*)
Theorem field_auto_group_finite:
  !r:'a field. FiniteField r ==> FiniteGroup (field_auto_group r)
Proof
  simp[FiniteField_def, FiniteGroup_def, field_auto_group_carrier, field_auto_maps_finite, field_auto_group_group]
QED

(* Theorem: Field r ==> field_auto_group r <= symmetric_group R *)
(* Proof:
   Note Group (field_auto_group r)                     by field_auto_group_group
    and Group (symmetric_group R)                      by symmetric_group_group
   Note field_auto_group r).carrier = field_auto_maps r
                                                       by field_auto_group_carrier
    and (symmetric_group R).carrier = bij_maps R       by symmetric_group_carrier
    and field_auto_maps r SUBSET bij_maps R            by field_auto_maps_subset
    and (field_auto_group r).op = (symmetric_group R).op
                                                       by symmetric_group_op,
                                                          field_auto_group_op, FUN_EQ_THM
   Thus (field_auto_group r) <= (symmetric_group R)    by Subgroup_def
*)
Theorem field_auto_group_subgroup:
  !r:'a field. Field r ==> field_auto_group r <= symmetric_group R
Proof
  simp[Subgroup_def] >>
  simp[field_auto_group_group, symmetric_group_group,
        field_auto_group_property, symmetric_group_property,
        FUN_EQ_THM, field_auto_maps_subset]
QED

(* ------------------------------------------------------------------------- *)
(* Map Fixing a Set                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define a map fixing a set *)
(* Overload a map fixing a set -- but hard to control:
val _ = overload_on("fixes", ``\f s. !x. x IN s ==> (f x = x)``);
*)
Definition fixes_def[nocompute]:
    fixes f s <=> (!x. x IN s ==> (f x = x))
End
(* use [nocompute] as this is not effective for evalutaion. *)
val _ = set_fixity "fixes" (Infix(NONASSOC, 450)); (* same as relation *)

(* Note:
   In twosq, for an involution f, that is, f involute s,
       fixes f s = {x | x IN s /\ f x = x}, the set of elements fixed by f,
   and pairs f s = {x | x IN s /\ f x <> x}, the set of elements paired by f.
   Here f fixes s is a predicate, true when f fixes all elements of set s.
*)

(* Theorem: (f fixes s) /\ (g fixes s) ==> (f o g) fixes s *)
(* Proof:
   Let x IN s, then
      (f o g) x
    = f (g x)          by composition
    = f x              by fixes_def, g fixes s
    = x                by fixes_def, f fixes s
*)
Theorem fixes_compose:
  !f g s. (f fixes s) /\ (g fixes s) ==> (f o g) fixes s
Proof
  simp[fixes_def]
QED

(* Theorem: I fixes s *)
(* Proof:
   Let x IN s, then I x = x    by I_THM
   Thus I fixes s              by fixes_def
*)
Theorem fixes_I:
  !s. I fixes s
Proof
  simp[fixes_def]
QED

(* Theorem: f fixes s /\ INJ f s t ==> (LINV f s) fixes s *)
(* Proof:
   Let x IN s.
     (LINV f s) x
   = (LINV f s) (f x)          by fixes_def, f fixes s
   = x                         by LINV_DEF
   Thus (LINV f s) fixes s     by fixes_def
*)
Theorem fixes_inj_linv:
  !f s t. f fixes s /\ INJ f s t ==> (LINV f s) fixes s
Proof
  metis_tac[fixes_def, LINV_DEF]
QED

(* Theorem: f fixes s /\ f PERMUTES s ==> (LINV f s) fixes s *)
(* Proof:
   Note INJ f s s            by BIJ_DEF
   Thus (LINV f s) fixes s   by fixes_inj_linv
*)
Theorem fixes_bij_linv:
  !f s. f fixes s /\ f PERMUTES s ==> (LINV f s) fixes s
Proof
  metis_tac[BIJ_DEF, fixes_inj_linv]
QED

(* Theorem: s SUBSET t ==> (f fixes s <=> (f on t) fixes s) *)
(* Proof: by fixes_def, on_def, SUBSET_DEF *)
Theorem fixes_on_subset:
  !f s t. s SUBSET t ==> (f fixes s <=> (f on t) fixes s)
Proof
  simp[fixes_def, on_def, SUBSET_DEF]
QED

(* Theorem: f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s *)
(* Proof:
   By fixes_def, this is to show:
       !x. x IN s ==> LINV f t (f x) = x
   Note INJ f t univ(:'a)          by metis_tac[INJ_UNIV
     so LINV f t (f x) = x         by LINV_SUBSET, s SUBSET t
*)
Theorem fixes_subset_linv:
  !f s t. f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s
Proof
  metis_tac[fixes_def, INJ_UNIV, LINV_SUBSET]
QED

(* ------------------------------------------------------------------------- *)
(* Field Automorphism fixing subfield.                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the subfield-fixing automorphism *)
Definition subfield_auto_def[nocompute]:
    subfield_auto f (r:'a field) (s:'a field) <=> FieldAuto f r /\ (f fixes B)
End
(* use [nocompute] as this is not effective for evalutaion. *)
(* Note: no subfield or SUBSET relating r and s here. *)
(* Note: including B SUBSET R only simplifies some theorems with subfield_auto f r s in premise,
         but then subfield_auto_I needs explicity B SUBSET R,
         so finally subfield_auto_group_group still requires B SUBSET R for qualification. *)

(* Theorem: subfield_auto f r s ==> FieldAuto f r *)
(* Proof: by subfield_auto_def. *)
Theorem subfield_auto_field_auto:
  !(r s):'a field. !f. subfield_auto f r s ==> FieldAuto f r
Proof
  simp[subfield_auto_def]
QED

(* Theorem: subfield_auto f r s ==> f fixes B *)
(* Proof: by subfield_auto_def. *)
Theorem subfield_auto_fixes:
  !(r s):'a field. !f. subfield_auto f r s ==> f fixes B
Proof
  simp[subfield_auto_def]
QED

(* Theorem: subfield_auto f r s /\ x IN R ==> f x IN R *)
(* Proof: by subfield_auto_field_auto, field_auto_element *)
Theorem subfield_auto_element:
  !(r s):'a field. !f x. subfield_auto f r s /\ x IN R ==> f x IN R
Proof
  metis_tac[subfield_auto_field_auto, field_auto_element]
QED

(* Theorem: subfield_auto f r s ==> over f R R *)
(* Proof: by subfield_auto_field_auto, field_auto_element *)
Theorem subfield_auto_over:
  !(r s):'a field. !f. subfield_auto f r s ==> over f R R
Proof
  metis_tac[subfield_auto_field_auto, field_auto_element]
QED

(* Theorem: Field r /\ subfield_auto f r s ==> f PERMUTES R *)
(* Proof: by subfield_auto_field_auto, field_auto_bij *)
Theorem subfield_auto_bij:
  !(r s):'a field. !f. Field r /\ subfield_auto f r s ==> f PERMUTES R
Proof
  metis_tac[subfield_auto_field_auto, field_auto_bij]
QED

(* Theorem: subfield_auto f1 r s /\ subfield_auto f2 r s ==> subfield_auto (f1 o f2) r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2) r, true by field_auto_compose
       True by field_auto_on_compose
   (2) f1 fixes B /\ f2 fixes B ==> f1 o f2 fixes B
       True by fixes_compose
*)
Theorem subfield_auto_compose:
  !(r s):'a field. !f1 f2. subfield_auto f1 r s /\
                           subfield_auto f2 r s ==> subfield_auto (f1 o f2) r s
Proof
  rw_tac std_ss[subfield_auto_def, field_auto_compose, fixes_compose]
QED

(* Theorem: subfield_auto I r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto I r, true     by field_auto_I
   (2) I fixes B, true         by fixes_I
*)
Theorem subfield_auto_I:
  !(r s):'a field. subfield_auto I r s
Proof
  rw_tac std_ss[subfield_auto_def, field_auto_I, fixes_I]
QED

(* Theorem: Field r /\ B SUBSET R /\
            subfield_auto f r s1 /\ subfield_auto f r s2 ==> subfield_auto r s ((f1 oo f2) R) *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2 on R) r
       Note FieldAuto (f1 o f2) r        by field_auto_compose
       Thus FieldAuto (f1 o f2 on R) r   by field_auto_on_auto, Field r
   (2) f1 fixes B /\ f2 fixes B ==> (f1 o f2 on R) fixes B
       Note (f1 o f2) fixes B            by fixes_compose
       Thus ((f1 o f2) on R) fixes B     by fixes_on_subset, B SUBSET R
*)
Theorem subfield_auto_on_compose:
  !(r s):'a field. !f1 f2. Field r /\ B SUBSET R /\
     subfield_auto f1 r s /\ subfield_auto f2 r s ==> subfield_auto ((f1 o f2) on R) r s
Proof
  rw[subfield_auto_def] >-
  metis_tac[field_auto_compose, field_auto_on_auto] >>
  metis_tac[fixes_compose, fixes_on_subset]
QED

(* Theorem: Field r /\ B SUBSET R ==>
            (subfield_auto f r s <=> subfield_auto (f on R) r s) *)
(* Proof:
       subfield_auto f r s
   <=> FieldAuto f r /\ f fixes B                  by subfield_auto_def
   <=> FieldAuto (f on R) r /\ f fixes B           by field_auto_on_auto
   <=> FieldAuto (f on R) r /\ (f on R) fixes B    by fixes_on_subset
   <=> subfield_auto (f on R) r s                  by subfield_auto_def
*)
Theorem subfield_auto_on_auto:
  !(r s):'a field. !f. Field r /\ B SUBSET R ==>
         (subfield_auto f r s <=> subfield_auto (f on R) r s)
Proof
  metis_tac[subfield_auto_def, field_auto_on_auto, fixes_on_subset]
QED

(* Theorem: Field r /\ B SUBSET R ==> subfield_auto (I on R) r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto (I on R) r, true  by field_auto_on_id
   (2) B SUBSET R ==> (I on R) fixes B
       Note I fixes B              by fixes_I
         so (I on R) fixes B       by fixes_on_subset, B SUBSET R
*)
Theorem subfield_auto_on_id:
  !(r s):'a field. Field r /\ B SUBSET R ==> subfield_auto (I on R) r s
Proof
  rw_tac std_ss[subfield_auto_def] >-
  simp[field_auto_on_id] >>
  simp[fixes_I, GSYM fixes_on_subset]
QED

(* Theorem: Field r /\ B SUBSET R /\ subfield_auto f r s ==>
            subfield_auto (LINV f R) r s /\ (((LINV f R) o f) on R) = (I on R) *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto f r ==> FieldAuto (LINV f R) r,
       This is true                by field_auto_linv_auto
   (2) f fixes B ==> LINV f R fixes B
       Note BIJ f R R              by FieldAuto_def, FieldIso_def
         so INJ f R R              by BIJ_DEF
       Thus LINV f R fixes B       by fixes_subset_linv, B SUBSET R
   (3) LINV f R o f on R = I on R
       Note BIJ f R R                          by FieldAuto_def, FieldIso_def
         so x IN R ==> LINV f R (f x) = x      by bij_on_linv
*)
Theorem subfield_auto_on_linv:
  !(r s):'a field. !f. Field r /\ B SUBSET R /\ subfield_auto f r s ==>
             subfield_auto (LINV f R) r s /\ (((LINV f R) o f) on R) = (I on R)
Proof
  rw_tac std_ss[subfield_auto_def] >-
  rw_tac std_ss[field_auto_linv_auto] >-
 (`INJ f R R` by metis_tac[FieldAuto_def, FieldIso_def, BIJ_DEF] >>
  rw_tac std_ss[fixes_subset_linv]) >>
  `BIJ f R R` by metis_tac[FieldAuto_def, FieldIso_def] >>
  rw_tac std_ss[bij_on_linv]
QED

(* ------------------------------------------------------------------------- *)
(* Subfield Fixing Automorphism Group                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the set of all field automorphism maps. *)
Definition subfield_auto_maps_def[nocompute]:
    subfield_auto_maps (r:'a field) (s:'a field) =
       {f on R | f | subfield_auto f r s}
End
(* use [nocompute] as this is not effective for evalutaion. *)

(* Theorem: x IN subfield_auto_maps r <=> ?f. x = f on R /\ subfield_auto f r s *)
(* Proof: by subfield_auto_maps_def. *)
Theorem subfield_auto_maps_element:
  !(r s):'a field. !x. x IN subfield_auto_maps r s <=>
                   ?f. x = f on R /\ subfield_auto f r s
Proof
  simp[subfield_auto_maps_def]
QED

(* Theorem: Field r /\ B SUBSET R ==>
            subfield_auto_maps r s = {f | f IN bij_maps R /\ subfield_auto f r s} *)
(* Proof:
   By subfield_auto_maps_def, bij_maps_element, EXTENSION, this is to show:
   (1) subfield_auto f r s ==> ?x. f on R = x on R /\ x PERMUTES R
       Take x = f, then f PERMUTES R           by subfield_auto_bij
   (2) subfield_auto f r s ==> subfield_auto (f on R) r s
       This is true                            by subfield_auto_on_auto
   (3) subfield_auto (f on R) r s ==> ?x. f on R = x on R /\ subfield_auto x r s
       Take x = f, then subfield_auto x r s    by subfield_auto_on_auto
*)
Theorem subfield_auto_maps_alt:
  !(r s):'a field. Field r /\ B SUBSET R ==>
        subfield_auto_maps r s = {f | f IN bij_maps R /\ subfield_auto f r s}
Proof
  simp[subfield_auto_maps_def, bij_maps_element, EXTENSION] >>
  metis_tac[subfield_auto_bij, subfield_auto_on_auto]
QED

(* Theorem: Field r /\ B SUBSET R ==> (subfield_auto_maps r s) SUBSET bij_maps R *)
(* Proof: by subfield_auto_maps_alt, SUBSET_DEF. *)
Theorem subfield_auto_maps_subset:
  !(r s):'a field. Field r /\ B SUBSET R ==>
           (subfield_auto_maps r s) SUBSET bij_maps R
Proof
  simp[subfield_auto_maps_alt, SUBSET_DEF]
QED

(* Theorem: FiniteField r /\ B SUBSET R ==> FINITE (subfield_auto_maps r s) *)
(* Proof:
   Note FINITE R /\ Field r                        by FiniteField_def
     so (subfield_auto_maps r) SUBSET bij_maps R   by subfield_auto_maps_subset
    and FINITE (bij_maps R)                        by bij_maps_finite
     so FINITE (subfield_auto_maps r s)            by SUBSET_FINITE
*)
Theorem subfield_auto_maps_finite:
  !(r s):'a field. FiniteField r /\ B SUBSET R ==>
               FINITE (subfield_auto_maps r s)
Proof
  metis_tac[FiniteField_def, subfield_auto_maps_subset, bij_maps_finite, SUBSET_FINITE]
QED

(*
Given a field/subfield pair: s <<= r,
an automorphism f:'a -> 'a is FieldAuto f r.
Those automorphisms that keep the subfield s fixed: f fixes B,
will form a group, the automorphism subfield group: Auto r s, or Galois group.
*)

(* Define the subfield-fixing automorphism group *)
Definition subfield_auto_group_def:
   subfield_auto_group (r:'a field) (s:'a field) =
      <| carrier := subfield_auto_maps r s;
              op := (\f1 f2. (f1 o f2) on R);
              id := (I on R)
       |>
End

(* Theorem: another representation of subfield_auto_group. *)
(* Proof: by subfield_auto_group_def, subfield_auto_maps_def. *)
Theorem subfield_auto_group_alt:
  !(r s):'a field. subfield_auto_group r s =
                   <|carrier := subfield_auto_maps r s;
                          op := (\f1 f2. f1 o f2 on R);
                          id := (I on R)
                    |>
Proof
  simp[subfield_auto_group_def, subfield_auto_maps_def]
QED

(* Theorem: Properties of (subfield_auto_group r s) *)
(* Proof: by subfield_auto_group_def. *)
Theorem subfield_auto_group_property:
  !(r s):'a field. (subfield_auto_group r s).carrier = subfield_auto_maps r s /\
               (subfield_auto_group r s).id = I on R /\
               !f1 f2. (subfield_auto_group r s).op f1 f2 = (f1 o f2) on R
Proof
  simp[subfield_auto_group_def]
QED

(* Derive theorems. *)
Theorem subfield_auto_group_carrier =
   subfield_auto_group_property |> SPEC_ALL |> CONJUNCT1 |> GEN ``s:'a field`` |> GEN_ALL;
(* val subfield_auto_group_carrier = |- !r s. (subfield_auto_group r s).carrier = subfield_auto_maps r s: thm *)

Theorem subfield_auto_group_id =
   subfield_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> GEN ``s:'a field`` |> GEN_ALL;
(* val subfield_auto_group_id = |- !r s. (subfield_auto_group r s).id = I on R: thm *)

Theorem subfield_auto_group_op =
   subfield_auto_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> GEN ``s:'a field`` |> GEN_ALL;
(* val subfield_auto_group_op = |- !r s f1 f2. (subfield_auto_group r s).op f1 f2 = f1 o f2 on R: thm *)

(* Theorem: The subfield-fixing automorphism group is a group.
            Field r /\ B SUBSET R ==> Group (subfield_auto_group r s) *)
(* Proof:
   By group_def_alt, subfield_auto_group_def, subfield_auto_maps_def, this is to show:
   (1) subfield_auto f r s /\ subfield_auto f' r s ==>
       ?f''. ((f on R) o (f' on R) on R = f'' on R) /\ subfield_auto f'' r s
       Let f'' = (f o f') on R.
       Then (f on R) o (f' on R) on R = f'' on R     by bij_on_compose, bij_on_bij
        and subfield_auto (f o f' on R) r s          by subfield_auto_on_compose
   (2) ((f on R) o (f' on R) on R) o (f'' on R) on R = (f on R) o ((f' on R) o (f'' on R) on R) on R
       Note BIJ f R B /\ BIJ f' R B /\ BIJ f'' R B   by subfield_auto_bij
       True by bij_on_bij, bij_on_compose_assoc.
   (3) ?f. (I on R = f on R) /\ subfield_auto f r s
       Let f = I,
       Then subfield_auto r s I               by subfield_auto_I, B SUBSET R
   (4) subfield_auto f r s /\ B SUBSET R ==> (I on R) o (f on R) on R = f on R
       Note over f R R                        by subfield_auto_bij, over_bij
       True by on_on_compose, I_o_ID
   (5) subfield_auto f r s ==> ?y. (?f. (y = f on R) /\ subfield_auto f r s) /\ (y o (f on R) on R = I on R)
       Let y = (LINV f R) on R.
       Then subfield (LINV f r) r s           by subfield_auto_on_linv
       Note BIJ f R B                         by subfield_auto_bij
         y o (f on R) on R
       = ((LINV f R) on R) o (f on R) on R    by notation
       = ((LINV f R) o f) on R                by bij_on_compose
       = I o R                                by subfield_auto_on_linv
*)
Theorem subfield_auto_group_group:
  !(r s):'a field. Field r /\ B SUBSET R ==> Group (subfield_auto_group r s)
Proof
  rw_tac std_ss[group_def_alt, subfield_auto_group_def, subfield_auto_maps_def,
                GSPECIFICATION] >|
  [
    rename [‘(f1 on R) o (f2 on R) on R’] >>
    qexists_tac `f1 o f2 on R` >>
    rpt strip_tac >-
    metis_tac[bij_on_compose, on_on, subfield_auto_bij] >>
    rw_tac std_ss[subfield_auto_on_compose],
    prove_tac[subfield_auto_bij, bij_on_bij, bij_on_compose_assoc],
    metis_tac[subfield_auto_I],
    rename [‘subfield_auto f r s’] >>
    `over f R R` by metis_tac[subfield_auto_bij, over_bij] >>
    rw[on_on_compose],
    metis_tac[subfield_auto_on_linv, subfield_auto_bij, bij_on_compose]
  ]
QED

(* This is a milestone theorem. *)

(* Theorem: (subfield_auto_group r s).carrier SUBSET bij_maps R *)
(* Proof: subfield_auto_group_carrier, subfield_auto_maps_subset. *)
Theorem subfield_auto_group_subset:
  !(r s): 'a field. Field r /\ B SUBSET R ==>
              ((subfield_auto_group r s).carrier SUBSET bij_maps R)
Proof
  simp[subfield_auto_group_carrier, subfield_auto_maps_subset]
QED

(* Theorem: FiniteField r /\ B SUBSET R ==>
            FiniteGroup (subfield_auto_group r s) *)
(* Proof:
   Note FINITE R /\ Field r                        by FiniteField_def
   Note (subfield_auto_group r s).carrier = subfield_auto_maps r s
                                                   by subfield_auto_group_carrier
    and FINITE (subfield_auto_maps r s)            by subfield_auto_maps_finite
    and Group (subfield_auto_group s s)            by subfield_auto_group_group
   Thus FiniteGroup (subfield_auto_group r s)      by FiniteGroup_def
*)
Theorem subfield_auto_group_finite:
  !(r s):'a field. FiniteField r /\ B SUBSET R ==>
                   FiniteGroup (subfield_auto_group r s)
Proof
  simp[FiniteField_def, FiniteGroup_def, subfield_auto_group_carrier,
        subfield_auto_maps_finite, subfield_auto_group_group]
QED

(* Theorem: Field r /\ B SUBSET R ==>
            subfield_auto_group r s <= symmetric_group R *)
(* Proof:
   Note Group (subfield_auto_group r s)                    by subfield_auto_group_group
    and Group (symmetric_group R)                          by symmetric_group_group
   Note (subfield_auto_group r s).carrier = subfield_auto_maps r s
                                                           by subfield_auto_group_carrier
    and (symmetric_group R).carrier = bij_maps R           by symmetric_group_carrier
    and subfield_auto_maps r s SUBSET bij_maps R           by subfield_auto_maps_subset
    and (subfield_auto_group r s).op = (symmetric_group R).op
                                                           by symmetric_group_op,
                                                              subfield_auto_group_op, FUN_EQ_THM
   Thus (subfield_auto_group r s) <= (symmetric_group R)   by Subgroup_def
*)
Theorem subfield_auto_group_subgroup:
  !(r s):'a field. Field r /\ B SUBSET R ==>
                   subfield_auto_group r s <= symmetric_group R
Proof
  simp[Subgroup_def] >>
  simp[subfield_auto_group_group, symmetric_group_group,
        subfield_auto_group_property, symmetric_group_property,
        FUN_EQ_THM, subfield_auto_maps_subset]
QED

(* Theorem: Field r /\ subfield s r ==> Group (subfield_auto_group r s) *)
(* Proof: by subfield_auto_group_group, subfield_carrier_subset *)
Theorem subfield_auto_group_group_1:
  !(r s):'a field. Field r /\ subfield s r ==> Group (subfield_auto_group r s)
Proof
  rw[subfield_auto_group_group, subfield_carrier_subset]
QED

(* Theorem: s <<= r ==> Group (subfield_auto_group r s) *)
(* Proof: by subfield_auto_group_group_1 *)
Theorem subfield_auto_group_group_2:
  !(r s):'a field. s <<= r ==> Group (subfield_auto_group r s)
Proof
  rw[subfield_auto_group_group_1]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
