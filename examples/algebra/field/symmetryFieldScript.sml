(* ------------------------------------------------------------------------- *)
(* Field Symmetry Group                                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "symmetryField";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* val _ = load "fieldMapTheory"; *)
open monoidTheory groupTheory ringTheory fieldTheory;
open monoidOrderTheory groupOrderTheory;
open monoidMapTheory groupMapTheory ringMapTheory fieldMapTheory;
open subgroupTheory;

(* val _ = load "symmetryGroupTheory"; *)
open symmetryGroupTheory;

(* open dependent theories *)
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory;


(* ------------------------------------------------------------------------- *)
(* Field Symmetry Group Documentation                                        *)
(* ------------------------------------------------------------------------- *)
(* Overload:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Maps restricted on a Set:
   ring_homo_on_homo   |- !r r_ f. Ring r /\ RingHomo f r r_ ==> RingHomo (f on R) r r_
   ring_iso_on_iso     |- !r r_ f. Ring r /\ RingIso f r r_ ==> RingIso (f on R) r r_
   ring_auto_on_auto   |- !r f. Ring r /\ RingAuto f r ==> RingAuto (f on R) r
   ring_auto_on_id     |- !r. Ring r ==> RingAuto (I on R) r
   field_homo_on_homo  |- !r r_ f. Field r /\ FieldHomo f r r_ ==> FieldHomo (f on R) r r_
   field_iso_on_iso    |- !r r_ f. Field r /\ FieldIso f r r_ ==> FieldIso (f on R) r r_
   field_auto_on_auto  |- !r f. Field r /\ FieldAuto f r ==> FieldAuto (f on R) r
   field_auto_on_id    |- !r. Field r ==> FieldAuto (I on R) r

   Symmetric Group of a Field:
   field_symmetric_group_group          |- !r. Group (symmetric_group R)
   field_nonzero_symmetric_group_group  |- !r. Group (symmetric_group R+)

   Automorphism Group of a Field:
   field_automorphism_group_group  |- !r. Field r ==> Group (automorphism_group f* )
   automorphism_field_def          |- !r. automorphism_field r =
                                          <|carrier := {f on R | f | FieldAuto f r};
                                                 op := (\f1 f2. f1 o f2 on R);
                                                 id := (I on R)|>
   automorphism_field_group        |- !r. Field r ==> Group (automorphism_field r)

   Map Fixing a Set:
   fixes_def        |- !f s. f fixes s <=> !x. x IN s ==> (f x = x)
   fixes_compose    |- !s f g. f fixes s /\ g fixes s ==> f o g fixes s
   fixes_I          |- !s. I fixes s
   fixes_inj_linv   |- !s t f. f fixes s /\ INJ f s t ==> LINV f s fixes s
   fixes_bij_linv   |- !s f. f fixes s /\ f PERMUTES s ==> LINV f s fixes s
   fixes_on_subset  |- !s t f. f fixes s /\ s SUBSET t ==> (f on t) fixes s
   fixes_on_linv    |- !s t f. f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s

   Field Automorphism fixing subfield:
   subfield_auto_def            |- !f r s. subfield_auto f r s <=> FieldAuto f r /\ f fixes B
   subfield_auto_field_auto     |- !r s f. subfield_auto f r s ==> FieldAuto f r
   subfield_auto_fixes          |- !r s f. subfield_auto f r s ==> f fixes B
   subfield_auto_element        |- !r s f x. subfield_auto f r s /\ x IN R ==> f x IN R
   subfield_auto_bij            |- !r s f. Field r /\ subfield_auto f r s ==> f PERMUTES R
   subfield_auto_compose        |- !r s f1 f2. subfield_auto f1 r s /\ subfield_auto f2 r s ==>
                                               subfield_auto (f1 o f2) r s
   subfield_auto_I              |- !r s. subfield_auto I r s
   subfield_auto_on_compose     |- !r s f1 f2. Field r /\ B SUBSET R /\ subfield_auto f1 r s /\
                                               subfield_auto f2 r s ==> subfield_auto (f1 o f2 on R) r s
   subfield_auto_on_id          |- !r s. Field r /\ B SUBSET R ==> subfield_auto (I on R) r s
   subfield_auto_on_linv        |- !r s f. Field r /\ B SUBSET R /\ subfield_auto f r s ==>
                                           subfield_auto (LINV f R) r s /\ (LINV f R o f on R) = (I on R)

   Subfield Fixing Automorphism Group:
   subfield_auto_group_def      |- !r s. subfield_auto_group r s =
                                         <|carrier := {f on R | f | subfield_auto f r s};
                                                op := (\f1 f2. f1 o f2 on R); id := (I on R)|>
   subfield_auto_group_group    |- !r s. Field r /\ B SUBSET R ==> Group (subfield_auto_group r s)
   subfield_auto_group_group_1  |- !r s. Field r /\ subfield s r ==> Group (subfield_auto_group r s)
   subfield_auto_group_group_2  |- !r s. s <<= r ==> Group (subfield_auto_group r s)
*)

(* ------------------------------------------------------------------------- *)
(* Field Symmetry Group                                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Maps restricted on a Set                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ RingHomo f r r_ ==> RingHomo (f on R) r r_ *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN R ==> (f on R) x IN R_, true      by fun_on_element
   (2) GroupHomo f r.sum r_.sum ==> GroupHomo (f on R) r.sum r_.sum
       Note Group r.sum                       by ring_add_group
       Thus GroupHomo (f on R) r.sum r_.sum   by group_homo_on_homo
   (2) MonoidHomo f r.prod r_.prod ==> MonoidHomo (f on R) r.prod r_.prod
       Note Monoid r.prod                     by ring_mult_monoid
       Thus GroupHomo (f on R) r.sum r_.sum   by monoid_homo_on_homo
*)
val ring_homo_on_homo = store_thm(
  "ring_homo_on_homo",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingHomo f r r_ ==> RingHomo (f on R) r r_``,
  rw_tac std_ss[RingHomo_def] >-
  rw_tac std_ss[fun_on_element] >-
  metis_tac[ring_add_group, group_homo_on_homo] >>
  metis_tac[ring_mult_monoid, monoid_homo_on_homo]);

(* Theorem: Ring r /\ RingIso f r r_ ==> RingIso (f on R) r r_ *)
(* Proof:
       RingIso f r r_
     = RingHomo f r r_  /\ BIJ f R R_                by RingIso_def
   ==> RingHomo (f on R) r r_ /\ BIJ f R R_          by ring_homo_on_homo
   ==> RingHomo (f on R) r r_ /\ BIJ (f on R) R R_   by bij_on_bij
     = RingIso (f on R) r r_                         by RingIso_def
*)
val ring_iso_on_iso = store_thm(
  "ring_iso_on_iso",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingIso f r r_ ==> RingIso (f on R) r r_``,
  rw_tac std_ss[RingIso_def, ring_homo_on_homo, bij_on_bij]);

(* Theorem: Ring r /\ RingAuto f r ==> RingAuto (f on R) r *)
(* Proof:
       RingAuto f r
     = RingIso f r r             by RingAuto_def
   ==> RingIso (f on R) r r_     by ring_iso_on_iso
     = RingAuto (f on R) r r_    by RingAuto_def
*)
val ring_auto_on_auto = store_thm(
  "ring_auto_on_auto",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> RingAuto (f on R) r ``,
  rw_tac std_ss[RingAuto_def, ring_iso_on_iso]);

(* Theorem: Ring r ==> RingAuto (I on R) r *)
(* Proof:
       Ring r
   ==> RingAuto I r          by ring_auto_I
   ==> RingAuto (I on R) r   by ring_auto_on_auto
*)
val ring_auto_on_id = store_thm(
  "ring_auto_on_id",
  ``!(r:'a ring). Ring r ==> RingAuto (I on R) r``,
  rw_tac std_ss[ring_auto_I, ring_auto_on_auto]);

(* Theorem: Field r /\ FieldHomo f r r_ ==> FieldHomo (f on R) r r_ *)
(* Proof:
   Note Ring r                   by field_is_ring
       FieldHomo f r r_
     = RingHomo f r r_           by field_homo_eq_ring_homo
   ==> RingHomo (f on R) r r_    by ring_homo_on_homo
     = FieldHomo (f on R) r r_   by field_homo_eq_ring_homo
*)
val field_homo_on_homo = store_thm(
  "field_homo_on_homo",
  ``!(r:'a field) (r_:'b field) f. Field r /\ FieldHomo f r r_ ==> FieldHomo (f on R) r r_``,
  rw_tac std_ss[field_homo_eq_ring_homo, field_is_ring, ring_homo_on_homo]);

(* Theorem: Field r /\ FieldIso f r r_ ==> FieldIso (f on R) r r_ *)
(* Proof:
   Note Ring r                  by field_is_ring
       FieldIso f r r_
     = RingIso f r r_           by field_iso_eq_ring_iso
   ==> RingIso (f on R) r r_    by ring_iso_on_iso
     = FieldIso (f on R) r r_   by field_iso_eq_ring_iso
*)
val field_iso_on_iso = store_thm(
  "field_iso_on_iso",
  ``!(r:'a field) (r_:'b field) f. Field r /\ FieldIso f r r_ ==> FieldIso (f on R) r r_``,
  rw_tac std_ss[field_iso_eq_ring_iso, field_is_ring, ring_iso_on_iso]);

(* Theorem: Field r /\ FieldAuto f r ==> FieldAuto (f on R) r *)
(* Proof:
   Note Ring r                    by field_is_ring
       FieldAuto f r
     = RingAuto f r               by field_auto_eq_ring_auto
   ==> RingAuto (f on R) r        by ring_auto_on_auto
   ==> FieldAuto (f on R) r       by field_auto_eq_ring_auto
   or
       FieldAuto f r
     = FieldIso f r r             by FieldAuto_def
   ==> FieldIso (f on R) r r_     by field_iso_on_iso
     = FieldAuto (f on R) r r_    by FieldAuto_def
*)
val field_auto_on_auto = store_thm(
  "field_auto_on_auto",
  ``!(r:'a field) f. Field r /\ FieldAuto f r ==> FieldAuto (f on R) r ``,
  rw_tac std_ss[FieldAuto_def, field_iso_on_iso]);

(* Theorem: Field r ==> FieldAuto (I on R) r *)
(* Proof:
       Field r
   ==> FieldAuto I r          by field_auto_I
   ==> FieldAuto (I on R) r   by field_auto_on_auto
*)
val field_auto_on_id = store_thm(
  "field_auto_on_id",
  ``!(r:'a field). Field r ==> FieldAuto (I on R) r``,
  rw_tac std_ss[field_auto_I, field_auto_on_auto]);

(* ------------------------------------------------------------------------- *)
(* Symmetric Group of a Field                                                *)
(* ------------------------------------------------------------------------- *)

(* All permutations of a field form the Symmetric Group. *)

(* Theorem: Group (symmetric_group R) *)
(* Proof: by symmetric_group_group *)
val field_symmetric_group_group = store_thm(
  "field_symmetric_group_group",
  ``!r:'a field. Group (symmetric_group R)``,
  rw_tac std_ss[symmetric_group_group]);

(* Theorem: Group (symmetric_group R+) *)
(* Proof: by symmetric_group_group.
   Both Group (symmetric_group R)
    and Group (symmetric_group R+) are true
    due to BIJ f R R must map #0 to #0 uniquely,
    and a bijection taking out #0 <-> #0 is still a bijection.
*)
val field_nonzero_symmetric_group_group = store_thm(
  "field_nonzero_symmetric_group_group",
  ``!r:'a field. Group (symmetric_group R+)``,
  rw_tac std_ss[symmetric_group_group]);

(* ------------------------------------------------------------------------- *)
(* Automorphism Group of a Field                                             *)
(* ------------------------------------------------------------------------- *)

(* All automorphisms of a field form the Automorphism Group. *)

(* Theorem: Field r ==> Group (automorphism_group f* )  *)
(* Proof:
   Note Group f*                         by field_mult_group
   Thus Group (automorphism_group f* )   by automorphism_group_group
*)
val field_automorphism_group_group = store_thm(
  "field_automorphism_group_group",
  ``!r:'a field. Field r ==> Group (automorphism_group f* )``,
  rw_tac std_ss[field_mult_group, automorphism_group_group]);

(* This is true, but this is not the aim. *)

(* All automorphisms of a Field form a Group. *)
val automorphism_field_def = Define`
    automorphism_field (r:'a field) =
       <| carrier := {f on R | f | FieldAuto f r};
               op := \f1 f2. (f1 o f2) on R;
               id := (I on R)
        |>
`;

(* Theorem: Field r ==> Group (automorphism_field r) *)
(* Proof:
   By group_def_alt, automorphism_field_def, this is to show:
   (1) FieldAuto f r /\ FieldAuto f' r ==> ?f''. ((f on R) o (f' on R) on R) = (f'' on R) /\ FieldAuto f'' r
       Let f'' = f o f' on R.
       Note f PERMUTES R /\ f' PERMUTES R                    by field_auto_bij
       Then (f on R) o (f' on R) on R = (f o f' on R) on R   by bij_on_compose, fun_on_on
        and FieldAuto (f o f' on R) r                        by field_auto_compose, field_auto_on_auto
   (2) FieldAuto f r /\ FieldAuto f' r  /\ FieldAuto f'' r ==>
       (((f on R) o (f' on R) on R) o (f'' on R) on R) = ((f on R) o ((f' on R) o (f'' on R) on R) on R)
       Note f PERMUTES R /\ f' PERMUTES R /\ f'' PERMUTES R  by field_auto_bij
       The result follows                                    by bij_on_compose_assoc, bij_on_bij
   (3) ?f. (I on R) = (f on R) /\ FieldAuto f r
       Let f = I, then FieldAuto I g                         by field_auto_I
   (4) ((I on R) o (f on R) on R) = (f on R)
       Note !x. x IN R ==> f x IN R                          by field_auto_bij, BIJ_ELEMENT
         (I on R) o (f on R) on R
       = (I o f) on R                                        by fun_on_compose
       = f on R                                              by I_o_ID
   (5) FieldAuto f r ==> ?y. (?f. y = (f on R) /\ FieldAuto f r) /\ (y o (f on R) on R) = (I on R)
       Let y = (LINV f R) on R, Then
       (1) Let f = LINV f R, then FieldAuto f g              by field_auto_linv_auto
       (2) FieldAuto f r ==> (LINV f R on R) o (f on R) on R = I on R
           Note f PERMUTES R                                 by field_auto_bij
             (LINV f R on R) o (f on R) on R
           = (LINV f R o f) on R                             by bij_on_compose
           = I on R                                          by bij_on_inv
*)

Theorem automorphism_field_group:
  !r:'a field. Field r ==> Group (automorphism_field r)
Proof
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, automorphism_field_def, GSPECIFICATION] >| [
    rename [‘(f on R) o (f' on R) on R’] >> qexists_tac `f o f' on R` >>
    rpt strip_tac >-
    metis_tac[bij_on_compose, fun_on_on, field_auto_bij] >>
    metis_tac[field_auto_compose, field_auto_on_auto],
    rename [‘((f on R) o (f' on R) on R) o (f'' on R) on R’] >>
    `f PERMUTES R /\ f' PERMUTES R /\ f'' PERMUTES R` by rw[field_auto_bij] >>
    metis_tac[bij_on_bij, bij_on_compose_assoc, field_auto_bij],
    metis_tac[field_auto_I],
    rename [‘FieldAuto f r’] >>
    `!x. x IN R ==> f x IN R` by metis_tac[field_auto_bij, BIJ_ELEMENT] >>
    rw[fun_on_compose],
    rename [‘FieldAuto f r’] >>
    qexists_tac `(LINV f R) on R` >>
    rpt strip_tac >- metis_tac[field_auto_linv_auto] >>
    metis_tac[bij_on_compose, bij_on_inv, field_auto_bij]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Map Fixing a Set                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define a map fixing a set *)
(* Overload a map fixing a set -- but hard to control:
val _ = overload_on("fixes", ``\f s. !x. x IN s ==> (f x = x)``);
*)
val fixes_def = Define`
    fixes f s <=> (!x. x IN s ==> (f x = x))
`;
val _ = set_fixity "fixes" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: (f fixes s) /\ (g fixes s) ==> (f o g) fixes s *)
(* Proof:
   Let x IN s, then
      (f o g) x
    = f (g x)              by composition
    = f x                  by fixes_def, g fixes s
    = x                    by fixes_def, f fixes s
*)
val fixes_compose = store_thm(
  "fixes_compose",
  ``!(s:'a -> bool) f g. (f fixes s) /\ (g fixes s) ==> (f o g) fixes s``,
  rw_tac std_ss[fixes_def]);

(* Theorem: I fixes s *)
(* Proof:
   Let x IN s, then I x = x    by I_THM
   Thus I fixes s              by fixes_def
*)
val fixes_I = store_thm(
  "fixes_I",
  ``!(s:'a -> bool). I fixes s``,
  rw_tac std_ss[fixes_def]);

(* Theorem: f fixes s /\ INJ f s t ==> (LINV f s) fixes s *)
(* Proof:
   Let x IN s.
     (LINV f s) x
   = (LINV f s) (f x)        by fixes_def, f fixes s
   = x                       by LINV_DEF
   Thus (LINV f s) fixes s   by fixes_def
*)
val fixes_inj_linv = store_thm(
  "fixes_inj_linv",
  ``!(s:'a -> bool) t f. f fixes s /\ INJ f s t ==> (LINV f s) fixes s``,
  metis_tac[fixes_def, LINV_DEF]);

(* Theorem: f fixes s /\ f PERMUTES s ==> (LINV f s) fixes s *)
(* Proof:
   Note INJ f s s            by BIJ_DEF
   Thus (LINV f s) fixes s   by fixes_inj_linv
*)
val fixes_bij_linv = store_thm(
  "fixes_bij_linv",
  ``!(s:'a -> bool) f. f fixes s /\ f PERMUTES s ==> (LINV f s) fixes s``,
  metis_tac[BIJ_DEF, fixes_inj_linv]);

(* Theorem: f fixes s /\ s SUBSET t ==> (f on t) fixes s *)
(* Proof: by on_def, fixes_def, SUBSET_DEF *)
val fixes_on_subset = store_thm(
  "fixes_on_subset",
  ``!(s:'a -> bool) t f. f fixes s /\ s SUBSET t ==> (f on t) fixes s``,
  rw_tac std_ss[on_def, fixes_def, SUBSET_DEF]);


(* Theorem: f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s *)
(* Proof: by fixes_def, LINV_SUBSET *)
val fixes_on_linv = store_thm(
  "fixes_on_linv",
  ``!(s:'a -> bool) t f. f fixes s /\ s SUBSET t /\ INJ f t t ==> LINV f t fixes s``,
  metis_tac[fixes_def, LINV_SUBSET]);

(* ------------------------------------------------------------------------- *)
(* Field Automorphism fixing subfield.                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the subfield-fixing automorphism *)
val subfield_auto_def = Define`
    subfield_auto f (r:'a field) (s:'a field) <=> FieldAuto f r /\ (f fixes B)
`;
(* Note: no subfield or SUBSET relating r and s here. *)
(* Note: including B SUBSET R only simplifies some theorems with subfield_auto f r s in premise,
         but then subfield_auto_I needs explicity B SUBSET R,
         so finally subfield_auto_group_group still requires B SUBSET R for qualification. *)

(* Theorem: subfield_auto f r s ==> FieldAuto f r *)
(* Proof: by subfield_auto_def. *)
val subfield_auto_field_auto = store_thm(
  "subfield_auto_field_auto",
  ``!(r s):'a field. !f. subfield_auto f r s ==> FieldAuto f r``,
  rw_tac std_ss[subfield_auto_def]);

(* Theorem: subfield_auto f r s ==> f fixes B *)
(* Proof: by subfield_auto_def. *)
val subfield_auto_fixes = store_thm(
  "subfield_auto_fixes",
  ``!(r s):'a field. !f. subfield_auto f r s ==> f fixes B``,
  rw_tac std_ss[subfield_auto_def]);

(* Theorem: subfield_auto f r s /\ x IN R ==> f x IN R *)
(* Proof: by subfield_auto_field_auto, field_auto_element *)
val subfield_auto_element = store_thm(
  "subfield_auto_element",
  ``!(r s):'a field. !f x. subfield_auto f r s /\ x IN R ==> f x IN R``,
  metis_tac[subfield_auto_field_auto, field_auto_element]);

(* Theorem: Field r /\ subfield_auto f r s ==> f PERMUTES R *)
(* Proof: by subfield_auto_field_auto, field_auto_bij *)
val subfield_auto_bij = store_thm(
  "subfield_auto_bij",
  ``!(r s):'a field. !f. Field r /\ subfield_auto f r s ==> f PERMUTES R``,
  metis_tac[subfield_auto_field_auto, field_auto_bij]);

(* Theorem: subfield_auto f1 r s /\ subfield_auto f2 r s ==> subfield_auto (f1 o f2) r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto f1 r /\ FieldAuto f2 r ==> FieldAuto (f1 o f2) r, true by field_auto_compose
       True by field_auto_on_compose
   (2) f1 fixes B /\ f2 fixes B ==> f1 o f2 fixes B
       True by fixes_compose
*)
val subfield_auto_compose = store_thm(
  "subfield_auto_compose",
  ``!(r s):'a field. !f1 f2. subfield_auto f1 r s /\ subfield_auto f2 r s ==> subfield_auto (f1 o f2) r s``,
  rw_tac std_ss[subfield_auto_def, field_auto_compose, fixes_compose]);

(* Theorem: subfield_auto I r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto I r, true    by field_auto_I
   (2) I fixes B, true        by fixes_I
*)
val subfield_auto_I = store_thm(
  "subfield_auto_I",
  ``!(r s):'a field. subfield_auto I r s``,
  rw_tac std_ss[subfield_auto_def, field_auto_I, fixes_I]);

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
val subfield_auto_on_compose = store_thm(
  "subfield_auto_on_compose",
  ``!(r s):'a field. !f1 f2. Field r /\ B SUBSET R /\
     subfield_auto f1 r s /\ subfield_auto f2 r s ==> subfield_auto ((f1 o f2) on R) r s``,
  rw_tac std_ss[subfield_auto_def] >-
  rw_tac std_ss[field_auto_compose, field_auto_on_auto] >>
  rw_tac std_ss[fixes_compose, fixes_on_subset]);

(* Theorem: Field r /\ B SUBSET R ==> subfield_auto (I on R) r s *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto (I on R) r, true by field_auto_on_id
   (2) B SUBSET R ==> (I on R) fixes B
       Note I fixes B             by fixes_I
         so (I on R) fixes B      by fixes_on_subset, B SUBSET R
*)
val subfield_auto_on_id = store_thm(
  "subfield_auto_on_id",
  ``!(r s):'a field. Field r /\ B SUBSET R ==> subfield_auto (I on R) r s``,
  rw_tac std_ss[subfield_auto_def] >-
  rw_tac std_ss[field_auto_on_id] >>
  rw_tac std_ss[fixes_I, fixes_on_subset]);

(* Theorem: Field r /\ B SUBSET R /\ subfield_auto f r s ==>
            subfield_auto (LINV f R) r s /\ (((LINV f R) o f) on R) = (I on R) *)
(* Proof:
   By subfield_auto_def, this is to show:
   (1) FieldAuto f r ==> FieldAuto (LINV f R) r,
       This is true               by field_auto_linv_auto
   (2) f fixes B ==> LINV f R fixes B
       Note BIJ f R R             by FieldAuto_def, FieldIso_def
         so INJ f R R             by BIJ_DEF
       Thus LINV f R fixes B      by fixes_on_linv, B SUBSET R
   (3) LINV f R o f on R = I on R
       By on_def, FUN_EQ_THM, this is to show:
       (if x IN R then LINV f R (f x) else ARB) = if x IN R then x else ARB
       Note BIJ f R R                      by FieldAuto_def, FieldIso_def
         so INJ f R R                      by BIJ_DEF
       Thus x IN R ==> LINV f R (f x) = x  by LINV_DEF
*)
val subfield_auto_on_linv = store_thm(
  "subfield_auto_on_linv",
  ``!(r s):'a field. !f. Field r /\ B SUBSET R /\ subfield_auto f r s ==>
             subfield_auto (LINV f R) r s /\ (((LINV f R) o f) on R) = (I on R)``,
  rw_tac std_ss[subfield_auto_def] >-
  rw_tac std_ss[field_auto_linv_auto] >-
 (`INJ f R R` by metis_tac[FieldAuto_def, FieldIso_def, BIJ_DEF] >>
  rw_tac std_ss[fixes_on_linv]) >>
  rw[on_def, FUN_EQ_THM] >>
  `INJ f R R` by metis_tac[FieldAuto_def, FieldIso_def, BIJ_DEF] >>
  metis_tac[LINV_DEF]);

(* ------------------------------------------------------------------------- *)
(* Subfield Fixing Automorphism Group                                        *)
(* ------------------------------------------------------------------------- *)

(*
Given a field/subfield pair: s <<= r,
an automorphism f:'a -> 'a is FieldAuto f r.
Those automorphisms that keep the subfield s fixed: f fixes B,
will form a group, the automorphism subfield group: Auto r s, or Galois group.
*)

(* Define the subfield-fixing automorphism group *)
val subfield_auto_group_def = Define`
    subfield_auto_group (r:'a field) (s:'a field) =
        <| carrier := {f on R | f | subfield_auto f r s};
                op := (\f1 f2. (f1 o f2) on R);
                id := (I on R)
         |>
`;

(* Theorem: The subfield-fixing automorphism group is a group.
            Field r /\ B SUBSET R ==> Group (subfield_auto_group r s) *)
(* Proof:
   By group_def_alt, subfield_auto_group_def, this is to show:
   (1) subfield_auto f r s /\ subfield_auto f' r s ==>
       ?f''. ((f on R) o (f' on R) on R = f'' on R) /\ subfield_auto f'' r s
       Let f'' = (f o f') on R.
       Then (f on R) o (f' on R) on R = f'' on R    by bij_on_compose, bij_on_bij
        and subfield_auto (f o f' on R) r s         by subfield_auto_on_compose
   (2) ((f on R) o (f' on R) on R) o (f'' on R) on R = (f on R) o ((f' on R) o (f'' on R) on R) on R
       Note BIJ f R B /\ BIJ f' R B /\ BIJ f'' R B  by subfield_auto_bij
       True by bij_on_bij, bij_on_compose_assoc.
   (3) ?f. (I on R = f on R) /\ subfield_auto f r s
       Let f = I,
       Then subfield_auto r s I               by subfield_auto_I, B SUBSET R
   (4) subfield_auto f r s /\ B SUBSET R ==> (I on R) o (f on R) on R = f on R
       Note !x. x IN R ==> f x IN R           by subfield_auto_bij, BIJ_ELEMENT
       True by fun_on_compose, I_o_ID
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
  rw_tac std_ss[group_def_alt, subfield_auto_group_def, GSPECIFICATION] >| [
    rename [‘(f on R) o (f' on R) on R’] >>
    qexists_tac `f o f' on R` >>
    rpt strip_tac >-
    metis_tac[bij_on_compose, fun_on_on, subfield_auto_bij] >>
    rw_tac std_ss[subfield_auto_on_compose],
    prove_tac[subfield_auto_bij, bij_on_bij, bij_on_compose_assoc],
    metis_tac[subfield_auto_I],
    rename [‘subfield_auto f r s’] >>
    `!x. x IN R ==> f x IN R` by metis_tac[subfield_auto_bij, BIJ_ELEMENT] >>
    rw[fun_on_compose],
    metis_tac[subfield_auto_on_linv, subfield_auto_bij, bij_on_compose]
  ]
QED

(* This is a milestone theorem. *)

(* Theorem: Field r /\ subfield s r ==> Group (subfield_auto_group r s) *)
(* Proof: by subfield_auto_group_group, subfield_carrier_subset *)
val subfield_auto_group_group_1 = store_thm(
  "subfield_auto_group_group_1",
  ``!(r s):'a field. Field r /\ subfield s r ==> Group (subfield_auto_group r s)``,
  rw[subfield_auto_group_group, subfield_carrier_subset]);

(* Theorem: s <<= r ==> Group (subfield_auto_group r s) *)
(* Proof: by subfield_auto_group_group_1 *)
val subfield_auto_group_group_2 = store_thm(
  "subfield_auto_group_group_2",
  ``!(r s):'a field. s <<= r ==> Group (subfield_auto_group r s)``,
  rw[subfield_auto_group_group_1]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
