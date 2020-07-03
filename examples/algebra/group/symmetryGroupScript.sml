(* ------------------------------------------------------------------------- *)
(* Symmetry Group.                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "symmetryGroup";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory;

(* Get dependent theories local *)
(* val _ = load "groupTheory"; *)
open groupTheory monoidTheory;
open monoidOrderTheory;

(* val _ = load "subgroupTheory"; *)
open submonoidTheory;
open subgroupTheory;
open monoidMapTheory groupMapTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperSetTheory";  loaded by monoidTheory *) *)
open helperSetTheory;

(* Load dependent theories *)
(* val _ = load "Satisfysimps"; *)
(* used in coset_id_eq_subgroup: srw_tac[SatisfySimps.SATISFY_ss] *)

(* val _ = load "groupCyclicTheory"; *)
open groupCyclicTheory groupInstancesTheory;


(* ------------------------------------------------------------------------- *)
(* Symmetry Group Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Function on a Set
   on_def                 |- !f s. (f on s) = (\x. if x IN s then f x else ARB)
   fun_on_eq              |- !f1 f2 s. (f1 on s) = (f2 on s) <=> !x. x IN s ==> f1 x = f2 x
   fun_on_element         |- !f s t x. x IN s /\ f x IN t ==> (f on s) x IN t
   fun_on_on              |- !f s. ((f on s) on s) = (f on s)
   fun_on_compose         |- !f1 f2 s. (!x. x IN s ==> f2 x IN s) ==>
                                       ((f1 on s) o (f2 on s) on s) = (f1 o f2 on s)
   fun_on_compose_assoc   |- !f1 f2 f3 s. (!x. x IN s ==> f3 x IN s) ==>
                                          ((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s)

   bij_on_bij             |- !f s t. BIJ f s t ==> BIJ (f on s) s t
   bij_on_compose_bij     |- !f g s t u. BIJ f s t /\ BIJ g t u ==> BIJ (g o f on s) s u
   bij_on_compose         |- !f1 f2 s. f2 PERMUTES s ==> ((f1 on s) o (f2 on s) on s) = (f1 o f2 on s)
   bij_on_compose_assoc   |- !f1 f2 f3 s. f3 PERMUTES s ==> ((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s)
   bij_on_id              |- !s. (I on s) PERMUTES s
   bij_on_inv             |- !f s. f PERMUTES s ==> (LINV f s o f on s) = (I on s)

   Symmetric Group:
   symmetric_group_def    |- !s. symmetric_group s =
                                 <|carrier := {f on s | f | f PERMUTES s};
                                        op := (\f1 f2. f1 o f2 on s);
                                        id := (I on s)
                                  |>
   symmetric_group_group  |- !s. Group (symmetric_group s)

   Maps restricted on a Set:
   monoid_homo_on_homo    |- !g h f. Monoid g /\ MonoidHomo f g h ==> MonoidHomo (f on G) g h
   monoid_iso_on_iso      |- !g h f. Monoid g /\ MonoidIso f g h ==> MonoidIso (f on G) g h
   monoid_auto_on_auto    |- !g f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (f on G) g
   monoid_auto_on_id      |- !g. Monoid g ==> MonoidAuto (I on G) g
   group_homo_on_homo     |- !g h f. Group g /\ GroupHomo f g h ==> GroupHomo (f on G) g h
   group_iso_on_iso       |- !g h f. Group g /\ GroupIso f g h ==> GroupIso (f on G) g h
   group_auto_on_auto     |- !g f. Group g /\ GroupAuto f g ==> GroupAuto (f on G) g
   group_auto_on_id       |- !g. Group g ==> GroupAuto (I on G) g

   Automorphism Group:
   automorphism_group_def     |- !g. automorphism_group g =
                                     <|carrier := {f on G | f | GroupAuto f g};
                                            op := (\f1 f2. f1 o f2 on G);
                                            id := (I on G)|>
   automorphism_group_group   |- !g. Group g ==> Group (automorphism_group g)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Function on a Set                                                         *)
(* ------------------------------------------------------------------------- *)

(* Function with domain on a set *)
(* val _ = overload_on("on", ``\(f:'a -> 'b) (s:'a -> bool) x. if x IN s then f x else ARB``); *)
val on_def = Define`
    on (f:'a -> 'b) (s:'a -> bool) = (\x. if x IN s then f x else ARB)
`;
(* make this an infix operator *)
val _ = set_fixity "on" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: ((f1 on s) = (f2 on s)) <=> (!x. x IN s ==> (f1 x <=> f2 x)) *)
(* Proof: by on_def *)
val fun_on_eq = store_thm(
  "fun_on_eq",
  ``!(f1 f2):'a -> 'b. !s. ((f1 on s) = (f2 on s)) <=> (!x. x IN s ==> (f1 x = f2 x))``,
  rw[on_def, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: x IN s /\ f x IN t ==> (f on s) x IN t *)
(* Proof: by on_def *)
val fun_on_element = store_thm(
  "fun_on_element",
  ``!f:'a -> 'b. !s t x. x IN s /\ f x IN t ==> (f on s) x IN t``,
  rw_tac std_ss[on_def]);

(* Theorem: ((f on s) on s) = (f on s) *)
(* Proof: by on_def *)
val fun_on_on = store_thm(
  "fun_on_on",
  ``!(f:'a -> 'b) s. ((f on s) on s) = (f on s)``,
  rw_tac std_ss[on_def]);

(* Theorem: (!x. x IN s ==> f2 x IN s) ==> ((((f1 on s) o (f2 on s)) on s) = ((f1 o f2) on s)) *)
(* Proof: by on_def *)
val fun_on_compose = store_thm(
  "fun_on_compose",
  ``!(f1 f2):'a -> 'a. !s. (!x. x IN s ==> f2 x IN s) ==>
          ((((f1 on s) o (f2 on s)) on s) = ((f1 o f2) on s))``,
  rw[on_def, FUN_EQ_THM]);

(* Theorem: (!x. x IN s ==> f3 x IN s) ==>
            (((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s)) *)
(* Proof: by on_def, FUN_EQ_THM *)
val fun_on_compose_assoc = store_thm(
  "fun_on_compose_assoc",
  ``!(f1 f2 f3):'a -> 'a. !(s:'a -> bool). (!x. x IN s ==> f3 x IN s) ==>
       (((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s))``,
  rw[on_def, FUN_EQ_THM]);

(* Theorem: BIJ f s t ==> BIJ (f on s) s t *)
(* Proof: by [BIJ_DEF, INJ_DEF, SURJ_DEF, on_def *)
val bij_on_bij = store_thm(
  "bij_on_bij",
  ``!f:'a -> 'b. !s t. BIJ f s t ==> BIJ (f on s) s t``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, on_def] >>
  metis_tac[]);

(* Theorem: BIJ f s t /\ BIJ g t u ==> BIJ (g o f on s) s u *)
(* Proof: by BIJ_DEF, INJ_DEF, SURJ_DEF, on_def *)
val bij_on_compose_bij = store_thm(
  "bij_on_compose_bij",
  ``!f g (s:'a -> bool) t u. BIJ f s t /\ BIJ g t u ==> BIJ ((g o f) on s) s u``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, on_def] >>
  metis_tac[]);

(* Theorem: f2 PERMUTES s ==> ((f1 on s) o (f2 on s) on s) = (f1 o f2 on s) *)
(* Proof: by fun_on_compose, BIJ_ELEMENT *)
val bij_on_compose = store_thm(
  "bij_on_compose",
  ``!(f1 f2):'a -> 'a. !s. f2 PERMUTES s ==> ((f1 on s) o (f2 on s) on s) = (f1 o f2 on s)``,
  metis_tac[fun_on_compose, BIJ_ELEMENT]);

(* Theorem: f3 PERMUTES s ==> ((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s) *)
(* Proof: by fun_on_compose_assoc, BIJ_ELEMENT *)
val bij_on_compose_assoc = store_thm(
  "bij_on_compose_assoc",
  ``!(f1 f2 f3):'a -> 'a. !s. f3 PERMUTES s ==> ((f1 o f2 on s) o f3 on s) = (f1 o (f2 o f3 on s) on s)``,
  metis_tac[fun_on_compose_assoc, BIJ_ELEMENT]);

(* Theorem: (I on s) PERMUTES s *)
(* Proof: by BIJ_DEF, INJ_DEF, SURJ_DEF, on_def *)
val bij_on_id = store_thm(
  "bij_on_id",
  ``!s. (I on s) PERMUTES s``,
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, on_def] >>
  metis_tac[]);

(* Theorem: f PERMUTES s ==> (LINV f s o f on s) = (I on s) *)
(* Proof: by on_def, FUN_EQ_THM, BIJ_DEF, LINV_DEF *)
val bij_on_inv = store_thm(
  "bij_on_inv",
  ``!f (s:'a -> bool). f PERMUTES s ==> (LINV f s o f on s) = (I on s)``,
  rw[on_def, FUN_EQ_THM] >>
  rw[] >>
  metis_tac[BIJ_DEF, LINV_DEF]);

(* ------------------------------------------------------------------------- *)
(* Symmetric Group                                                           *)
(* ------------------------------------------------------------------------- *)

(*
Given a finite set s of cardinality n,
the set of bijections (permutations) form a group under composition,
called the symmetric group Sym(n), or simply S_n.
*)

(* Define symmetric group *)
val symmetric_group_def = Define`
    symmetric_group (s:'a -> bool) =
       <| carrier := {f on s | f | f PERMUTES s};
               op := (\(f1 f2):'a -> 'a. (f1 o f2) on s);
               id := (I on s)
        |>
`;

(* Theorem: Group (symmetric_group s) *)
(* Proof:
   By group_def_alt, sym_group_def, this is to show:
   (1) f PERMUTES s /\ f' PERMUTES s ==> ?f''. ((f on s) o (f' on s) on s = f'' on s) /\ f'' PERMUTES s
       Let f'' = (f o f') on s.
       Then (f on s) o (f' on s) on s = f'' on s    by fun_on_compose, fun_on_on, BIJ_ELEMENT
        and f'' PERMUTES s                          by bij_on_compose_bij
        and the other, by FUN_EQ_THM,
        says: x IN s /\ f' x NOTIN s ==> ARB = f (f' x)
       The premise is F by BIJ_ELEMENT.
   (2) f PERMUTES s /\ f' PERMUTES s /\ f'' PERMUTES s ==>
       ((f on s) o (f' on s) on s) o (f'' on s) on s = (f on s) o ((f' on s) o (f'' on s) on s) on s
       Note (f on s) PERMUTES s          by bij_on_bij
        and (f' on s) PERMUTES s         by bij_on_bij
        and (f'' on s) PERMUTES s        by bij_on_bij
       The result follows                by bij_on_compose_assoc
   (3) ?f. (I on s = f on s) /\ f PERMUTES s
       Let f = I.
       Then I PERMUTES s                 by BIJ_I_SAME
   (4) f PERMUTES s ==> (I on s) o (f on s) on s = f on s
       Note !x. x IN s ==> f x IN s      by BIJ_ELEMENT
         (I on s) o (f on s) on s
       = (I o f) on s                    by fun_on_compose
       = f on s                          by I_o_ID
   (5) f PERMUTES s ==> ?y. (?f. (y = f on s) /\ f PERMUTES s) /\ (y o (f on s) on s = I on s)
       Let y = (LINV f s) on s. Then this is to show:
       (1) ?f'. (LINV f s on s = f' on s) /\ f' PERMUTES s
           Let f' = LINV f s.
           Then f' PERMUTES s            by BIJ_LINV_BIJ
       (2) (LINV f s on s) o (f on s) on s = I on s
           Note !x. x IN s ==> f x IN s  by BIJ_ELEMENT
             (LINV f s on s) o (f on s) on s
           = (LINV f s o f) on s         by fun_on_compose
           = I on s                      by bij_on_inv
*)
Theorem symmetric_group_group:
  !(s:'a -> bool). Group (symmetric_group s)
Proof
  rw_tac std_ss[group_def_alt, symmetric_group_def, GSPECIFICATION] >| [
    rename [‘(f on s) o (f' on s) on s’] >>
    qexists_tac `(f o f') on s` >>
    rpt strip_tac
    >- metis_tac[fun_on_compose, fun_on_on, BIJ_ELEMENT] >>
    metis_tac[bij_on_compose_bij],
    metis_tac[bij_on_compose_assoc, bij_on_bij],
    metis_tac[BIJ_I_SAME],
    rename [‘f PERMUTES s’] >>
    `!x. x IN s ==> f x IN s` by metis_tac[BIJ_ELEMENT] >>
    rw[fun_on_compose],
    rename [‘f PERMUTES s’] >>
    qexists_tac `(LINV f s) on s` >>
    rpt strip_tac >- metis_tac[BIJ_LINV_BIJ] >>
    metis_tac[fun_on_compose, bij_on_inv, BIJ_ELEMENT]
  ]
QED

(* This is a very good result! *)

(* ------------------------------------------------------------------------- *)
(* Maps restricted on a Set                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Monoid g /\ MonoidHomo f g h ==> MonoidHomo (f on G) g h *)
(* Proof: by MonoidHomo_def, on_def, monoid_op_element, monoid_id_element *)
val monoid_homo_on_homo = store_thm(
  "monoid_homo_on_homo",
  ``!(g:'a monoid) (h:'b monoid). !f. Monoid g /\ MonoidHomo f g h ==> MonoidHomo (f on G) g h``,
  rw_tac std_ss[MonoidHomo_def, on_def, monoid_op_element, monoid_id_element]);

(* Theorem: Monoid g /\ MonoidIso f g h ==> MonoidIso (f on G) g h *)
(* Proof:
       MonoidIso f g h
     = MonoidHomo f g h /\ BIJ f G h.carrier                by MonoidIso_def
   ==> MonoidHomo f g h /\ BIJ (f on G) G h.carrier         by bij_on_bij
   ==> MonoidHomo (f on G) g h /\ BIJ (f o G) G h.carrier   by monoid_homo_on_homo
     = MonoidIso (f on G) g h                               by MonoidIso_def
*)
val monoid_iso_on_iso = store_thm(
  "monoid_iso_on_iso",
  ``!(g:'a monoid) (h:'b monoid). !f. Monoid g /\ MonoidIso f g h ==> MonoidIso (f on G) g h``,
  rw_tac std_ss[MonoidIso_def, bij_on_bij, monoid_homo_on_homo]);

(* Theorem: Monoid g /\ MonoidAuto f g ==> MonoidAuto (f on G) g *)
(* Proof: by MonoidAuto_def, monoid_iso_on_iso *)
val monoid_auto_on_auto = store_thm(
  "monoid_auto_on_auto",
  ``!g:'a monoid. !f. Monoid g /\ MonoidAuto f g ==> MonoidAuto (f on G) g``,
  rw_tac std_ss[MonoidAuto_def, monoid_iso_on_iso]);

(* Theorem: Monoid g ==> MonoidAuto (I on G) g *)
(* Proof: by monoid_auto_I, monoid_auto_on_auto. *)
val monoid_auto_on_id = store_thm(
  "monoid_auto_on_id",
  ``!(g:'a monoid). Monoid g ==> MonoidAuto (I on G) g``,
  rw_tac std_ss[monoid_auto_I, monoid_auto_on_auto]);

(* Theorem: Group g /\ GroupHomo f g h ==> GroupHomo (f on G) g h *)
(* Proof: by GroupHomo_def, on_def, group_op_element *)
val group_homo_on_homo = store_thm(
  "group_homo_on_homo",
  ``!(g:'a group) (h:'b group). !f. Group g /\ GroupHomo f g h ==> GroupHomo (f on G) g h``,
  rw_tac std_ss[GroupHomo_def, on_def, group_op_element]);

(* Theorem: Group g /\ GroupIso f g h ==> GroupIso (f on G) g h *)
(* Proof:
       GroupIso f g h
     = GroupHomo f g h /\ BIJ f G h.carrier                by GroupIso_def
   ==> GroupHomo f g h /\ BIJ (f on G) G h.carrier         by bij_on_bij
   ==> GroupHomo (f on G) g h /\ BIJ (f o G) G h.carrier   by group_homo_on_homo
     = GroupIso (f on G) g h                               by GroupIso_def
*)
val group_iso_on_iso = store_thm(
  "group_iso_on_iso",
  ``!(g:'a group) (h:'b group). !f. Group g /\ GroupIso f g h ==> GroupIso (f on G) g h``,
  rw_tac std_ss[GroupIso_def, bij_on_bij, group_homo_on_homo]);

(* Theorem: Group g /\ GroupAuto f g ==> GroupAuto (f on G) g *)
(* Proof: by GroupAuto_def, group_iso_on_iso *)
val group_auto_on_auto = store_thm(
  "group_auto_on_auto",
  ``!g:'a group. !f. Group g /\ GroupAuto f g ==> GroupAuto (f on G) g``,
  rw_tac std_ss[GroupAuto_def, group_iso_on_iso]);

(* Theorem: Group g ==> GroupAuto (I on G) g *)
(* Proof: by group_auto_I, group_auto_on_auto *)
val group_auto_on_id = store_thm(
  "group_auto_on_id",
  ``!(g:'a group). Group g ==> GroupAuto (I on G) g``,
  rw_tac std_ss[group_auto_I, group_auto_on_auto]);

(* ------------------------------------------------------------------------- *)
(* Automorphism Group                                                        *)
(* ------------------------------------------------------------------------- *)

(* All automorphisms of a Group form a Group. *)
val automorphism_group_def = Define`
    automorphism_group (g:'a group) =
       <| carrier := {f on G | f | GroupAuto f g};
               op := \f1 f2. (f1 o f2) on G;
               id := (I on G)
        |>
`;

(* Theorem: Group g ==> Group (automorphism_group g) *)
(* Proof:
   By group_def_alt, automorphism_group_def, this is to show:
   (1) GroupAuto f g /\ GroupAuto f' g ==> ?f''. ((f on G) o (f' on G) on G = f'' on G) /\ GroupAuto f'' g
       Let f'' = f o f' on G.
       Note f PERMUTES G /\ f' PERMUTES G                    by group_auto_bij
       Then (f on G) o (f' on G) on G = (f o f' on G) on G   by bij_on_compose, fun_on_on
        and GroupAuto (f o f' on G) g                        by group_auto_compose, group_auto_on_auto
   (2) GroupAuto f g /\ GroupAuto f' g /\ GroupAuto f'' g ==>
       ((f on G) o (f' on G) on G) o (f'' on G) on G = (f on G) o ((f' on G) o (f'' on G) on G) on G
       Note f PERMUTES G /\ f' PERMUTES G /\ f'' PERMUTES G  by group_auto_bij
       The result follows                                    by bij_on_compose_assoc, bij_on_bij
   (3) ?f. (I on G = f on G) /\ GroupAuto f g
       Let f = I, then GroupAuto I g                         by group_auto_I
   (4) (I on G) o (f on G) on G = f on G
       Note !x. x IN G ==> f x IN G                          by group_auto_bij, BIJ_ELEMENT
         (I on G) o (f on G) on G
       = (I o f) on G                                        by fun_on_compose
       = f on G                                              by I_o_ID
   (5) GroupAuto f g ==> ?y. (?f. (y = f on G) /\ GroupAuto f g) /\ (y o (f on G) on G = I on G)
       Let y = (LINV f G) on G, Then
       (1) Let f = LINV f G, then GroupAuto f g              by group_auto_linv_auto
       (2) GroupAuto f g ==> (LINV f G on G) o (f on G) on G = I on G
           Note f PERMUTES G                                 by group_auto_bij
             (LINV f G on G) o (f on G) on s
           = (LINV f G o f) on G                             by bij_on_compose
           = I on G                                          by bij_on_inv
*)
Theorem automorphism_group_group:
  !g:'a group. Group g ==> Group (automorphism_group g)
Proof
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, automorphism_group_def, GSPECIFICATION] >| [
    rename [‘(f on G) o (f' on G) on G’] >>
    qexists_tac `f o f' on G` >>
    rpt strip_tac >- metis_tac[bij_on_compose, fun_on_on, group_auto_bij] >>
    metis_tac[group_auto_compose, group_auto_on_auto],
    metis_tac[group_auto_bij, bij_on_bij, bij_on_compose_assoc],
    metis_tac[group_auto_I],
    rename [‘(I on G) o (f on G) on G’] >>
    `!x. x IN G ==> f x IN G` by metis_tac[group_auto_bij, BIJ_ELEMENT] >>
    rw[fun_on_compose],
    rename [‘_ o (f on G) on G’] >>
    qexists_tac `(LINV f G) on G` >>
    rpt strip_tac >- metis_tac[group_auto_linv_auto] >>
    metis_tac[bij_on_compose, bij_on_inv, group_auto_bij]
  ]
QED

(* Another major result. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
