(* ------------------------------------------------------------------------- *)
(* Elementary Number Theory - a collection of useful results for numbers     *)
(*                                                                           *)
(* Author: (Joseph) Hing-Lun Chan (Australian National University, 2019)     *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib Parse bossLib;

open prim_recTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     logrootTheory pred_setTheory listTheory rich_listTheory listRangeTheory
     indexedListsTheory;

val _ = new_theory "number";

(* Overload non-decreasing functions with different arity. *)
val _ = overload_on("MONO", ``\f:num -> num. !x y. x <= y ==> f x <= f y``);
val _ = overload_on("MONO2",
      ``\f:num -> num -> num.
           !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x1 y1 <= f x2 y2``);
val _ = overload_on("MONO3",
      ``\f:num -> num -> num -> num.
           !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==>
                               f x1 y1 z1 <= f x2 y2 z2``);

(* Overload non-increasing functions with different arity. *)
val _ = overload_on("RMONO", ``\f:num -> num. !x y. x <= y ==> f y <= f x``);
val _ = overload_on("RMONO2",
      ``\f:num -> num -> num.
           !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x2 y2 <= f x1 y1``);
val _ = overload_on("RMONO3",
      ``\f:num -> num -> num -> num.
           !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==>
                               f x2 y2 z2 <= f x1 y1 z1``);

(* ------------------------------------------------------------------------- *)
(* More Set Theorems                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: DISJOINT (s DIFF t) t /\ DISJOINT t (s DIFF t) *)
(* Proof:
       DISJOINT (s DIFF t) t
   <=> (s DIFF t) INTER t = {}              by DISJOINT_DEF
   <=> !x. x IN (s DIFF t) INTER t <=> F    by MEMBER_NOT_EMPTY
       x IN (s DIFF t) INTER t
   <=> x IN (s DIFF t) /\ x IN t            by IN_INTER
   <=> (x IN s /\ x NOTIN t) /\ x IN t      by IN_DIFF
   <=> x IN s /\ (x NOTIN t /\ x IN t)
   <=> x IN s /\ F
   <=> F
   Similarly for DISJOINT t (s DIFF t)
*)
val DISJOINT_DIFF = store_thm(
  "DISJOINT_DIFF",
  ``!s t. (DISJOINT (s DIFF t) t) /\ (DISJOINT t (s DIFF t))``,
  (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

(* Theorem: DISJOINT s t <=> ((s DIFF t) = s) *)
(* Proof: by DISJOINT_DEF, DIFF_DEF, EXTENSION *)
val DISJOINT_DIFF_IFF = store_thm(
  "DISJOINT_DIFF_IFF",
  ``!s t. DISJOINT s t <=> ((s DIFF t) = s)``,
  rw[DISJOINT_DEF, DIFF_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: s UNION (t DIFF s) = s UNION t *)
(* Proof:
   By EXTENSION,
     x IN (s UNION (t DIFF s))
   = x IN s \/ x IN (t DIFF s)                    by IN_UNION
   = x IN s \/ (x IN t /\ x NOTIN s)              by IN_DIFF
   = (x IN s \/ x IN t) /\ (x IN s \/ x NOTIN s)  by LEFT_OR_OVER_AND
   = (x IN s \/ x IN t) /\ T                      by EXCLUDED_MIDDLE
   = x IN (s UNION t)                             by IN_UNION
*)
val UNION_DIFF_EQ_UNION = store_thm(
  "UNION_DIFF_EQ_UNION",
  ``!s t. s UNION (t DIFF s) = s UNION t``,
  rw_tac std_ss[EXTENSION, IN_UNION, IN_DIFF] >>
  metis_tac[]);

(* Theorem: (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {}) *)
(* Proof: by DISJOINT_DIFF, GSYM DISJOINT_DEF *)
val INTER_DIFF = store_thm(
  "INTER_DIFF",
  ``!s t. (s INTER (t DIFF s) = {}) /\ ((t DIFF s) INTER s = {})``,
  rw[DISJOINT_DIFF, GSYM DISJOINT_DEF]);

(* Theorem: {x} SUBSET s /\ SING s <=> (s = {x}) *)
(* Proof:
   Note {x} SUBSET s ==> x IN s           by SUBSET_DEF
    and SING s ==> ?y. s = {y}            by SING_DEF
   Thus x IN {y} ==> x = y                by IN_SING
*)
Theorem SING_SUBSET :
    !s x. {x} SUBSET s /\ SING s <=> (s = {x})
Proof
    metis_tac[SING_DEF, IN_SING, SUBSET_DEF]
QED

(* Theorem: x IN (if b then {y} else {}) ==> (x = y) *)
(* Proof: by IN_SING, MEMBER_NOT_EMPTY *)
val IN_SING_OR_EMPTY = store_thm(
  "IN_SING_OR_EMPTY",
  ``!b x y. x IN (if b then {y} else {}) ==> (x = y)``,
  rw[]);

(* Theorem: FINITE s ==> ((CARD s = 1) <=> SING s) *)
(* Proof:
   If part: CARD s = 1 ==> SING s
      Since CARD s = 1
        ==> s <> {}        by CARD_EMPTY
        ==> ?x. x IN s     by MEMBER_NOT_EMPTY
      Claim: !y . y IN s ==> y = x
      Proof: By contradiction, suppose y <> x.
             Then y NOTIN {x}             by EXTENSION
               so CARD {y; x} = 2         by CARD_DEF
              and {y; x} SUBSET s         by SUBSET_DEF
             thus CARD {y; x} <= CARD s   by CARD_SUBSET
             This contradicts CARD s = 1.
      Hence SING s         by SING_ONE_ELEMENT (or EXTENSION, SING_DEF)
      Or,
      With x IN s, {x} SUBSET s         by SUBSET_DEF
      If s <> {x}, then {x} PSUBSET s   by PSUBSET_DEF
      so CARD {x} < CARD s              by CARD_PSUBSET
      But CARD {x} = 1                  by CARD_SING
      and this contradicts CARD s = 1.

   Only-if part: SING s ==> CARD s = 1
      Since SING s
        <=> ?x. s = {x}    by SING_DEF
        ==> CARD {x} = 1   by CARD_SING
*)
val CARD_EQ_1 = store_thm(
  "CARD_EQ_1",
  ``!s. FINITE s ==> ((CARD s = 1) <=> SING s)``,
  rw[SING_DEF, EQ_IMP_THM] >| [
    `1 <> 0` by decide_tac >>
    `s <> {} /\ ?x. x IN s` by metis_tac[CARD_EMPTY, MEMBER_NOT_EMPTY] >>
    qexists_tac `x` >>
    spose_not_then strip_assume_tac >>
    `{x} PSUBSET s` by rw[PSUBSET_DEF] >>
    `CARD {x} < CARD s` by rw[CARD_PSUBSET] >>
    `CARD {x} = 1` by rw[CARD_SING] >>
    decide_tac,
    rw[CARD_SING]
  ]);

(* Theorem: x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y)) *)
(* Proof:
       z IN (x INSERT s) DELETE y
   <=> z IN (x INSERT s) /\ z <> y                by IN_DELETE
   <=> (z = x \/ z IN s) /\ z <> y                by IN_INSERT
   <=> (z = x /\ z <> y) \/ (z IN s /\ z <> y)    by RIGHT_AND_OVER_OR
   <=> (z = x) \/ (z IN s /\ z <> y)              by x <> y
   <=> (z = x) \/ (z IN DELETE y)                 by IN_DELETE
   <=> z IN  x INSERT (s DELETE y)                by IN_INSERT
*)
val INSERT_DELETE_COMM = store_thm(
  "INSERT_DELETE_COMM",
  ``!s x y. x <> y ==> ((x INSERT s) DELETE y = x INSERT (s DELETE y))``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: x NOTIN s ==> (x INSERT s) DELETE x = s *)
(* Proof:
    (x INSERT s) DELETE x
   = s DELETE x         by DELETE_INSERT
   = s                  by DELETE_NON_ELEMENT
*)
Theorem INSERT_DELETE_NON_ELEMENT:
  !x s. x NOTIN s ==> (x INSERT s) DELETE x = s
Proof
  simp[DELETE_INSERT, DELETE_NON_ELEMENT]
QED

(* Theorem: s SUBSET u ==> (s INTER t) SUBSET u *)
(* Proof:
   Note (s INTER t) SUBSET s     by INTER_SUBSET
    ==> (s INTER t) SUBSET u     by SUBSET_TRANS
*)
val SUBSET_INTER_SUBSET = store_thm(
  "SUBSET_INTER_SUBSET",
  ``!s t u. s SUBSET u ==> (s INTER t) SUBSET u``,
  metis_tac[INTER_SUBSET, SUBSET_TRANS]);

(* Theorem: s DIFF (s DIFF t) = s INTER t *)
(* Proof: by IN_DIFF, IN_INTER *)
val DIFF_DIFF_EQ_INTER = store_thm(
  "DIFF_DIFF_EQ_INTER",
  ``!s t. s DIFF (s DIFF t) = s INTER t``,
  rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: (s = t) <=> (s SUBSET t /\ (t DIFF s = {})) *)
(* Proof:
       s = t
   <=> s SUBSET t /\ t SUBSET s       by SET_EQ_SUBSET
   <=> s SUBSET t /\ (t DIFF s = {})  by SUBSET_DIFF_EMPTY
*)
val SET_EQ_BY_DIFF = store_thm(
  "SET_EQ_BY_DIFF",
  ``!s t. (s = t) <=> (s SUBSET t /\ (t DIFF s = {}))``,
  rw[SET_EQ_SUBSET, SUBSET_DIFF_EMPTY]);

(* in pred_setTheory:
SUBSET_DELETE_BOTH |- !s1 s2 x. s1 SUBSET s2 ==> s1 DELETE x SUBSET s2 DELETE x
*)

(* Theorem: s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2 *)
(* Proof: by SUBSET_DEF *)
Theorem SUBSET_INSERT_BOTH:
  !s1 s2 x. s1 SUBSET s2 ==> x INSERT s1 SUBSET x INSERT s2
Proof
  simp[SUBSET_DEF]
QED

(* Theorem: x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x) *)
(* Proof: by SUBSET_DEF *)
val INSERT_SUBSET_SUBSET = store_thm(
  "INSERT_SUBSET_SUBSET",
  ``!s t x. x NOTIN s /\ (x INSERT s) SUBSET t ==> s SUBSET (t DELETE x)``,
  rw[SUBSET_DEF]);

(* DIFF_INSERT  |- !s t x. s DIFF (x INSERT t) = s DELETE x DIFF t *)

(* Theorem: (s DIFF t) DELETE x = s DIFF (x INSERT t) *)
(* Proof: by EXTENSION *)
val DIFF_DELETE = store_thm(
  "DIFF_DELETE",
  ``!s t x. (s DIFF t) DELETE x = s DIFF (x INSERT t)``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b) *)
(* Proof:
   Note FINITE b                   by SUBSET_FINITE
     so a INTER b = b              by SUBSET_INTER2
        CARD (a DIFF b)
      = CARD a - CARD (a INTER b)  by CARD_DIFF
      = CARD a - CARD b            by above
*)
Theorem SUBSET_DIFF_CARD:
  !a b. FINITE a /\ b SUBSET a ==> (CARD (a DIFF b) = CARD a - CARD b)
Proof
  metis_tac[CARD_DIFF, SUBSET_FINITE, SUBSET_INTER2]
QED

(* Theorem: s SUBSET {x} <=> ((s = {}) \/ (s = {x})) *)
(* Proof:
   Note !y. y IN s ==> y = x   by SUBSET_DEF, IN_SING
   If s = {}, then trivially true.
   If s <> {},
     then ?y. y IN s           by MEMBER_NOT_EMPTY, s <> {}
       so y = x                by above
      ==> s = {x}              by EXTENSION
*)
Theorem SUBSET_SING_IFF:
  !s x. s SUBSET {x} <=> ((s = {}) \/ (s = {x}))
Proof
  rw[SUBSET_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t) *)
(* Proof:
   If part: CARD s = CARD t ==> s = t
      By contradiction, suppose s <> t.
      Then s PSUBSET t         by PSUBSET_DEF
        so CARD s < CARD t     by CARD_PSUBSET, FINITE t
      This contradicts CARD s = CARD t.
   Only-if part is trivial.
*)
Theorem SUBSET_CARD_EQ:
  !s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `s PSUBSET t` by rw[PSUBSET_DEF] >>
  `CARD s < CARD t` by rw[CARD_PSUBSET] >>
  decide_tac
QED

(* Theorem: (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t *)
(* Proof:
   If part: (!x. x IN s ==> f x IN t) ==> (IMAGE f s) SUBSET t
       y IN (IMAGE f s)
   ==> ?x. (y = f x) /\ x IN s   by IN_IMAGE
   ==> f x = y IN t              by given
   hence (IMAGE f s) SUBSET t    by SUBSET_DEF
   Only-if part: (IMAGE f s) SUBSET t ==>  (!x. x IN s ==> f x IN t)
       x IN s
   ==> f x IN (IMAGE f s)        by IN_IMAGE
   ==> f x IN t                  by SUBSET_DEF
*)
val IMAGE_SUBSET_TARGET = store_thm(
  "IMAGE_SUBSET_TARGET",
  ``!f s t. (!x. x IN s ==> f x IN t) <=> (IMAGE f s) SUBSET t``,
  metis_tac[IN_IMAGE, SUBSET_DEF]);

(* Theorem: SURJ f s t ==> CARD (IMAGE f s) = CARD t *)
(* Proof:
   Note IMAGE f s = t              by IMAGE_SURJ
   Thus CARD (IMAGE f s) = CARD t  by above
*)
Theorem SURJ_CARD_IMAGE:
  !f s t. SURJ f s t ==> CARD (IMAGE f s) = CARD t
Proof
  simp[IMAGE_SURJ]
QED

(* ------------------------------------------------------------------------- *)
(* Image and Bijection (from examples/algebra)                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ f s t ==> INJ f s UNIV *)
(* Proof:
   Note s SUBSET s                        by SUBSET_REFL
    and t SUBSET univ(:'b)                by SUBSET_UNIV
     so INJ f s t ==> INJ f s univ(:'b)   by INJ_SUBSET
*)
val INJ_UNIV = store_thm(
  "INJ_UNIV",
  ``!f s t. INJ f s t ==> INJ f s UNIV``,
  metis_tac[INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV]);

(* Theorem: INJ f s UNIV ==> BIJ f s (IMAGE f s) *)
(* Proof: by definitions. *)
val INJ_IMAGE_BIJ_ALT = store_thm(
  "INJ_IMAGE_BIJ_ALT",
  ``!f s. INJ f s UNIV ==> BIJ f s (IMAGE f s)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: s <> {} ==> !e. IMAGE (K e) s = {e} *)
(* Proof:
       IMAGE (K e) s
   <=> {(K e) x | x IN s}    by IMAGE_DEF
   <=> {e | x IN s}          by K_THM
   <=> {e}                   by EXTENSION, if s <> {}
*)
val IMAGE_K = store_thm(
  "IMAGE_K",
  ``!s. s <> {} ==> !e. IMAGE (K e) s = {e}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s) *)
(* Proof:
   If part: e IN s ==> f e IN IMAGE f s
     True by IMAGE_IN.
   Only-if part: f e IN IMAGE f s ==> e IN s
     ?x. (f e = f x) /\ x IN s   by IN_IMAGE
     f e = f x ==> e = x         by given implication
     Hence x IN s
*)
val IMAGE_ELEMENT_CONDITION = store_thm(
  "IMAGE_ELEMENT_CONDITION",
  ``!f:'a -> 'b. (!x y. (f x = f y) ==> (x = y)) ==> (!s e. e IN s <=> f e IN IMAGE f s)``,
  rw[EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: BIGUNION (IMAGE (\x. {x}) s) = s *)
(* Proof:
       z IN BIGUNION (IMAGE (\x. {x}) s)
   <=> ?t. z IN t /\ t IN (IMAGE (\x. {x}) s)   by IN_BIGUNION
   <=> ?t. z IN t /\ (?y. y IN s /\ (t = {y}))  by IN_IMAGE
   <=> z IN {z} /\ (?y. y IN s /\ {z} = {y})    by picking t = {z}
   <=> T /\ z IN s                              by picking y = z, IN_SING
   Hence  BIGUNION (IMAGE (\x. {x}) s) = s      by EXTENSION
*)
val BIGUNION_ELEMENTS_SING = store_thm(
  "BIGUNION_ELEMENTS_SING",
  ``!s. BIGUNION (IMAGE (\x. {x}) s) = s``,
  rw[EXTENSION, EQ_IMP_THM] >-
  metis_tac[] >>
  qexists_tac `{x}` >>
  metis_tac[IN_SING]);

(* Theorem: s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s)) *)
(* Proof: by SUBSET_DEF, INJ_DEF, EXTENSION, IN_IMAGE, IN_DIFF *)
Theorem IMAGE_DIFF:
  !s t f. s SUBSET t /\ INJ f t UNIV ==> (IMAGE f (t DIFF s) = (IMAGE f t) DIFF (IMAGE f s))
Proof
  rw[SUBSET_DEF, INJ_DEF, EXTENSION] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Set of Proper Subsets                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of all proper subsets of a set *)
val _ = overload_on ("PPOW", ``\s. (POW s) DIFF {s}``);

(* Theorem: !s e. e IN PPOW s ==> e PSUBSET s *)
(* Proof:
     e IN PPOW s
   = e IN ((POW s) DIFF {s})       by notation
   = (e IN POW s) /\ e NOTIN {s}   by IN_DIFF
   = (e SUBSET s) /\ e NOTIN {s}   by IN_POW
   = (e SUBSET s) /\ e <> s        by IN_SING
   = e PSUBSET s                   by PSUBSET_DEF
*)
val IN_PPOW = store_thm(
  "IN_PPOW",
  ``!s e. e IN PPOW s ==> e PSUBSET s``,
  rw[PSUBSET_DEF, IN_POW]);

(* Theorem: FINITE (PPOW s) *)
(* Proof:
   Since PPOW s = (POW s) DIFF {s},
       FINITE s
   ==> FINITE (POW s)     by FINITE_POW
   ==> FINITE ((POW s) DIFF {s})  by FINITE_DIFF
   ==> FINITE (PPOW s)            by above
*)
val FINITE_PPOW = store_thm(
  "FINITE_PPOW",
  ``!s. FINITE s ==> FINITE (PPOW s)``,
  rw[FINITE_POW]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof:
     CARD (PPOW s)
   = CARD ((POW s) DIFF {s})      by notation
   = CARD (POW s) - CARD ((POW s) INTER {s})   by CARD_DIFF
   = CARD (POW s) - CARD {s}      by INTER_SING, since s IN POW s
   = 2 ** CARD s  - CARD {s}      by CARD_POW
   = 2 ** CARD s  - 1             by CARD_SING
   = PRE (2 ** CARD s)            by PRE_SUB1
*)
val CARD_PPOW = store_thm(
  "CARD_PPOW",
  ``!s. FINITE s ==> (CARD (PPOW s) = PRE (2 ** CARD s))``,
  rpt strip_tac >>
  `FINITE {s}` by rw[FINITE_SING] >>
  `FINITE (POW s)` by rw[FINITE_POW] >>
  `s IN (POW s)` by rw[IN_POW, SUBSET_REFL] >>
  `CARD (PPOW s) = CARD (POW s) - CARD ((POW s) INTER {s})` by rw[CARD_DIFF] >>
  `_ = CARD (POW s) - CARD {s}` by rw[INTER_SING] >>
  `_ = 2 ** CARD s  - CARD {s}` by rw[CARD_POW] >>
  `_ = 2 ** CARD s  - 1` by rw[CARD_SING] >>
  `_ = PRE (2 ** CARD s)` by rw[PRE_SUB1] >>
  rw[]);

(* Theorem: FINITE s ==> CARD (PPOW s) = PRE (2 ** CARD s) *)
(* Proof: by CARD_PPOW *)
val CARD_PPOW_EQN = store_thm(
  "CARD_PPOW_EQN",
  ``!s. FINITE s ==> (CARD (PPOW s) = (2 ** CARD s) - 1)``,
  rw[CARD_PPOW]);

(* ------------------------------------------------------------------------- *)
(* Partition Property                                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload partition by split *)
val _ = overload_on("split", ``\s u v. (s = u UNION v) /\ (DISJOINT u v)``);

(* Pretty printing of partition by split *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                       fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                    term_name = "split",
                  pp_elements = [HardSpace 1, TOK "=|=", HardSpace 1, TM,
                                 BreakSpace(1,1), TOK "#", BreakSpace(1,1)]};

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> PROD_SET {} = PROD_SET u * PROD_SET v
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true.
   Step: !u v. (s = u UNION v) /\ DISJOINT u v ==> (PROD_SET s = PROD_SET u * PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> PROD_SET (e INSERT s) = PROD_SET u * PROD_SET v
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT
        PROD_SET (e INSERT s)
      = e * PROD_SET s                       by PROD_SET_INSERT, FINITE s
      = e * (PROD_SET w * PROD_SET v)        by induction hypothesis
      = (e * PROD_SET w) * PROD_SET v        by MULT_ASSOC
      = PROD_SET (e INSERT w) * PROD_SET v   by PROD_SET_INSERT, FINITE w
      = PROD_SET u * PROD_SET v

      Similarly for e IN v.
*)
val PROD_SET_PRODUCT_BY_PARTITION = store_thm(
  "PROD_SET_PRODUCT_BY_PARTITION",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> (PROD_SET s = PROD_SET u * PROD_SET v)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET w * PROD_SET v)` by rw[] >>
    `_ = (e * PROD_SET w) * PROD_SET v` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `PROD_SET (e INSERT s) = e * PROD_SET s` by rw[PROD_SET_INSERT] >>
    `_ = e * (PROD_SET u * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * (e * PROD_SET w)` by rw[] >>
    `_ = PROD_SET u * PROD_SET v` by rw[PROD_SET_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems (from examples/algebra)                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 3 = SUC 2 *)
(* Proof: by arithmetic *)
val THREE = store_thm(
  "THREE",
  ``3 = SUC 2``,
  decide_tac);

(* Theorem: 4 = SUC 3 *)
(* Proof: by arithmetic *)
val FOUR = store_thm(
  "FOUR",
  ``4 = SUC 3``,
  decide_tac);

(* Theorem: 5 = SUC 4 *)
(* Proof: by arithmetic *)
val FIVE = store_thm(
  "FIVE",
  ``5 = SUC 4``,
  decide_tac);

(* Overload squaring (temporalized by Chun Tian) *)
val _ = temp_overload_on("SQ", ``\n. n * n``); (* not n ** 2 *)

(* Overload half of a number (temporalized by Chun Tian) *)
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);

(* Overload twice of a number (temporalized by Chun Tian) *)
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* make divides infix *)
val _ = set_fixity "divides" (Infixl 480); (* relation is 450, +/- is 500, * is 600. *)

(* Theorem alias *)
Theorem ZERO_LE_ALL = ZERO_LESS_EQ;
(* val ZERO_LE_ALL = |- !n. 0 <= n: thm *)

(* Extract theorem *)
Theorem ONE_NOT_0  = DECIDE``1 <> 0``;
(* val ONE_NOT_0 = |- 1 <> 0: thm *)

(* Theorem: !n. 1 < n ==> 0 < n *)
(* Proof: by arithmetic. *)
val ONE_LT_POS = store_thm(
  "ONE_LT_POS",
  ``!n. 1 < n ==> 0 < n``,
  decide_tac);

(* Theorem: !n. 1 < n ==> n <> 0 *)
(* Proof: by arithmetic. *)
val ONE_LT_NONZERO = store_thm(
  "ONE_LT_NONZERO",
  ``!n. 1 < n ==> n <> 0``,
  decide_tac);

(* Theorem: ~(1 < n) <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic. *)
val NOT_LT_ONE = store_thm(
  "NOT_LT_ONE",
  ``!n. ~(1 < n) <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* Theorem: n <> 0 <=> 1 <= n *)
(* Proof: by arithmetic. *)
val NOT_ZERO_GE_ONE = store_thm(
  "NOT_ZERO_GE_ONE",
  ``!n. n <> 0 <=> 1 <= n``,
  decide_tac);

(* Theorem: n <= 1 <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic *)
val LE_ONE = store_thm(
  "LE_ONE",
  ``!n. n <= 1 <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* arithmeticTheory.LESS_EQ_SUC_REFL |- !m. m <= SUC m *)

(* Theorem: n < SUC n *)
(* Proof: by arithmetic. *)
val LESS_SUC = store_thm(
  "LESS_SUC",
  ``!n. n < SUC n``,
  decide_tac);

(* Theorem: 0 < n ==> PRE n < n *)
(* Proof: by arithmetic. *)
val PRE_LESS = store_thm(
  "PRE_LESS",
  ``!n. 0 < n ==> PRE n < n``,
  decide_tac);

(* Theorem: 0 < n ==> ?m. n = SUC m *)
(* Proof: by NOT_ZERO_LT_ZERO, num_CASES. *)
val SUC_EXISTS = store_thm(
  "SUC_EXISTS",
  ``!n. 0 < n ==> ?m. n = SUC m``,
  metis_tac[NOT_ZERO_LT_ZERO, num_CASES]);


(* Theorem: 1 <> 0 *)
(* Proof: by ONE, SUC_ID *)
val ONE_NOT_ZERO = store_thm(
  "ONE_NOT_ZERO",
  ``1 <> 0``,
  decide_tac);

(* Theorem: (SUC m) + (SUC n) = m + n + 2 *)
(* Proof:
     (SUC m) + (SUC n)
   = (m + 1) + (n + 1)     by ADD1
   = m + n + 2             by arithmetic
*)
val SUC_ADD_SUC = store_thm(
  "SUC_ADD_SUC",
  ``!m n. (SUC m) + (SUC n) = m + n + 2``,
  decide_tac);

(* Theorem: (SUC m) * (SUC n) = m * n + m + n + 1 *)
(* Proof:
     (SUC m) * (SUC n)
   = SUC m + (SUC m) * n   by MULT_SUC
   = SUC m + n * (SUC m)   by MULT_COMM
   = SUC m + (n + n * m)   by MULT_SUC
   = m * n + m + n + 1     by arithmetic
*)
val SUC_MULT_SUC = store_thm(
  "SUC_MULT_SUC",
  ``!m n. (SUC m) * (SUC n) = m * n + m + n + 1``,
  rw[MULT_SUC]);

(* Theorem: (SUC m = SUC n) <=> (m = n) *)
(* Proof: by prim_recTheory.INV_SUC_EQ *)
val SUC_EQ = store_thm(
  "SUC_EQ",
  ``!m n. (SUC m = SUC n) <=> (m = n)``,
  rw[]);

(* Theorem: (TWICE n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val TWICE_EQ_0 = store_thm(
  "TWICE_EQ_0",
  ``!n. (TWICE n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val SQ_EQ_0 = store_thm(
  "SQ_EQ_0",
  ``!n. (SQ n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 1) <=> (n = 1) *)
(* Proof: MULT_EQ_1 *)
val SQ_EQ_1 = store_thm(
  "SQ_EQ_1",
  ``!n. (SQ n = 1) <=> (n = 1)``,
  rw[]);

(* Theorem: (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0)) *)
(* Proof: by MULT_EQ_0 *)
val MULT3_EQ_0 = store_thm(
  "MULT3_EQ_0",
  ``!x y z. (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0))``,
  metis_tac[MULT_EQ_0]);

(* Theorem: (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1)) *)
(* Proof: by MULT_EQ_1 *)
val MULT3_EQ_1 = store_thm(
  "MULT3_EQ_1",
  ``!x y z. (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1))``,
  metis_tac[MULT_EQ_1]);

(* Theorem: 0 ** 2 = 0 *)
(* Proof: by ZERO_EXP *)
Theorem SQ_0:
  0 ** 2 = 0
Proof
  simp[]
QED

(* Theorem: (n ** 2 = 0) <=> (n = 0) *)
(* Proof: by EXP_2, MULT_EQ_0 *)
Theorem EXP_2_EQ_0:
  !n. (n ** 2 = 0) <=> (n = 0)
Proof
  simp[]
QED

(* LE_MULT_LCANCEL |- !m n p. m * n <= m * p <=> m = 0 \/ n <= p *)

(* Theorem: n <= p ==> m * n <= m * p *)
(* Proof:
   If m = 0, this is trivial.
   If m <> 0, this is true by LE_MULT_LCANCEL.
*)
Theorem LE_MULT_LCANCEL_IMP:
  !m n p. n <= p ==> m * n <= m * p
Proof
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MAX m n = if m <= n then n else m *)
(* Proof: by MAX_DEF *)
val MAX_ALT = store_thm(
  "MAX_ALT",
  ``!m n. MAX m n = if m <= n then n else m``,
  rw[MAX_DEF]);

(* Theorem: MIN m n = if m <= n then m else n *)
(* Proof: by MIN_DEF *)
val MIN_ALT = store_thm(
  "MIN_ALT",
  ``!m n. MIN m n = if m <= n then m else n``,
  rw[MIN_DEF]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y) *)
(* Proof: by MAX_DEF *)
val MAX_SWAP = store_thm(
  "MAX_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y)``,
  rw[MAX_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y) *)
(* Proof: by MIN_DEF *)
val MIN_SWAP = store_thm(
  "MIN_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y)``,
  rw[MIN_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: SUC (MAX m n) = MAX (SUC m) (SUC n) *)
(* Proof:
   If m < n, then SUC m < SUC n    by LESS_MONO_EQ
      hence true by MAX_DEF.
   If m = n, then true by MAX_IDEM.
   If n < m, true by MAX_COMM of the case m < n.
*)
val SUC_MAX = store_thm(
  "SUC_MAX",
  ``!m n. SUC (MAX m n) = MAX (SUC m) (SUC n)``,
  rw[MAX_DEF]);

(* Theorem: SUC (MIN m n) = MIN (SUC m) (SUC n) *)
(* Proof: by MIN_DEF *)
val SUC_MIN = store_thm(
  "SUC_MIN",
  ``!m n. SUC (MIN m n) = MIN (SUC m) (SUC n)``,
  rw[MIN_DEF]);

(* Reverse theorems *)
val MAX_SUC = save_thm("MAX_SUC", GSYM SUC_MAX);
(* val MAX_SUC = |- !m n. MAX (SUC m) (SUC n) = SUC (MAX m n): thm *)
val MIN_SUC = save_thm("MIN_SUC", GSYM SUC_MIN);
(* val MIN_SUC = |- !m n. MIN (SUC m) (SUC n) = SUC (MIN m n): thm *)

(* Theorem: x < n /\ y < n ==> MAX x y < n *)
(* Proof:
        MAX x y
      = if x < y then y else x    by MAX_DEF
      = either x or y
      < n                         for either case
*)
val MAX_LESS = store_thm(
  "MAX_LESS",
  ``!x y n. x < n /\ y < n ==> MAX x y < n``,
  rw[]);

(* Theorem: m <= MAX m n /\ n <= MAX m n *)
(* Proof: by MAX_DEF *)
val MAX_IS_MAX = store_thm(
  "MAX_IS_MAX",
  ``!m n. m <= MAX m n /\ n <= MAX m n``,
  rw_tac std_ss[MAX_DEF]);

(* Theorem: MIN m n <= m /\ MIN m n <= n *)
(* Proof: by MIN_DEF *)
val MIN_IS_MIN = store_thm(
  "MIN_IS_MIN",
  ``!m n. MIN m n <= m /\ MIN m n <= n``,
  rw_tac std_ss[MIN_DEF]);

(* Theorem: (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n) *)
(* Proof: by MAX_DEF *)
val MAX_ID = store_thm(
  "MAX_ID",
  ``!m n. (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n)``,
  rw[MAX_DEF]);

(* Theorem: (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n) *)
(* Proof: by MIN_DEF *)
val MIN_ID = store_thm(
  "MIN_ID",
  ``!m n. (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n)``,
  rw[MIN_DEF]);

(* Theorem: a <= b /\ c <= d ==> MAX a c <= MAX b d *)
(* Proof: by MAX_DEF *)
val MAX_LE_PAIR = store_thm(
  "MAX_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MAX a c <= MAX b d``,
  rw[]);

(* Theorem: a <= b /\ c <= d ==> MIN a c <= MIN b d *)
(* Proof: by MIN_DEF *)
val MIN_LE_PAIR = store_thm(
  "MIN_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d``,
  rw[]);

(* Theorem: MAX a (b + c) <= MAX a b + MAX a c *)
(* Proof: by MAX_DEF *)
val MAX_ADD = store_thm(
  "MAX_ADD",
  ``!a b c. MAX a (b + c) <= MAX a b + MAX a c``,
  rw[MAX_DEF]);

(* Theorem: MIN a (b + c) <= MIN a b + MIN a c *)
(* Proof: by MIN_DEF *)
val MIN_ADD = store_thm(
  "MIN_ADD",
  ``!a b c. MIN a (b + c) <= MIN a b + MIN a c``,
  rw[MIN_DEF]);

(* Theorem: 0 < n ==> (MAX 1 n = n) *)
(* Proof: by MAX_DEF *)
val MAX_1_POS = store_thm(
  "MAX_1_POS",
  ``!n. 0 < n ==> (MAX 1 n = n)``,
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (MIN 1 n = 1) *)
(* Proof: by MIN_DEF *)
val MIN_1_POS = store_thm(
  "MIN_1_POS",
  ``!n. 0 < n ==> (MIN 1 n = 1)``,
  rw[MIN_DEF]);

(* Theorem: MAX m n <= m + n *)
(* Proof:
   If m < n,  MAX m n = n <= m + n  by arithmetic
   Otherwise, MAX m n = m <= m + n  by arithmetic
*)
val MAX_LE_SUM = store_thm(
  "MAX_LE_SUM",
  ``!m n. MAX m n <= m + n``,
  rw[MAX_DEF]);

(* Theorem: MIN m n <= m + n *)
(* Proof:
   If m < n,  MIN m n = m <= m + n  by arithmetic
   Otherwise, MIN m n = n <= m + n  by arithmetic
*)
val MIN_LE_SUM = store_thm(
  "MIN_LE_SUM",
  ``!m n. MIN m n <= m + n``,
  rw[MIN_DEF]);

(* Theorem: MAX 1 (m ** n) = (MAX 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MAX 1 (0 ** n) = 1       by MAX_DEF
       and (MAX 1 0) ** n = 1       by MAX_DEF, EXP_1
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MAX 1 (m ** n) = m ** n  by MAX_DEF
       and (MAX 1 m) ** n = m ** n  by MAX_DEF, 0 < m
*)
val MAX_1_EXP = store_thm(
  "MAX_1_EXP",
  ``!n m. MAX 1 (m ** n) = (MAX 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MAX_DEF] >>
  `0 < m /\ 0 < m ** n` by rw[] >>
  `MAX 1 (m ** n) = m ** n` by rw[MAX_DEF] >>
  `MAX 1 m = m` by rw[MAX_DEF] >>
  fs[]);

(* Theorem: MIN 1 (m ** n) = (MIN 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MIN 1 (0 ** n) = 0 when n <> 0 or 1 when n = 0  by MIN_DEF
       and (MIN 1 0) ** n = 0 ** n  by MIN_DEF
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MIN 1 (m ** n) = 1 ** n  by MIN_DEF
       and (MIN 1 m) ** n = 1 ** n  by MIN_DEF, 0 < m
*)
val MIN_1_EXP = store_thm(
  "MIN_1_EXP",
  ``!n m. MIN 1 (m ** n) = (MIN 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MIN_DEF] >>
  `0 < m ** n` by rw[] >>
  `MIN 1 (m ** n) = 1` by rw[MIN_DEF] >>
  `MIN 1 m = 1` by rw[MIN_DEF] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Arithmetic Manipulations                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (n * n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: n * n = n ==> (n = 0) \/ (n = 1)
      By contradiction, suppose n <> 0 /\ n <> 1.
      Since n * n = n = n * 1     by MULT_RIGHT_1
       then     n = 1             by MULT_LEFT_CANCEL, n <> 0
       This contradicts n <> 1.
   Only-if part: (n = 0) \/ (n = 1) ==> n * n = n
      That is, 0 * 0 = 0          by MULT
           and 1 * 1 = 1          by MULT_RIGHT_1
*)
val SQ_EQ_SELF = store_thm(
  "SQ_EQ_SELF",
  ``!n. (n * n = n) <=> ((n = 0) \/ (n = 1))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  metis_tac[MULT_RIGHT_1, MULT_LEFT_CANCEL] >-
  rw[] >>
  rw[]);

(* Theorem: m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n *)
(* Proof:
   If b = 0,
      Note 0 < c ** m /\ 0 < c ** n   by EXP_POS, by 0 < c
      Thus 0 ** c ** m = 0            by ZERO_EXP
       and 0 ** c ** n = 0            by ZERO_EXP
      Hence true.
   If b <> 0,
      Then c ** m <= c ** n           by EXP_BASE_LEQ_MONO_IMP, 0 < c
        so b ** c ** m <= b ** c ** n by EXP_BASE_LEQ_MONO_IMP, 0 < b
*)
val EXP_EXP_BASE_LE = store_thm(
  "EXP_EXP_BASE_LE",
  ``!b c m n. m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n``,
  rpt strip_tac >>
  Cases_on `b = 0` >-
  rw[ZERO_EXP] >>
  rw[EXP_BASE_LEQ_MONO_IMP]);

(* Theorem: a <= b ==> a ** n <= b ** n *)
(* Proof:
   Note a ** n <= b ** n                 by EXP_EXP_LE_MONO
   Thus size (a ** n) <= size (b ** n)   by size_monotone_le
*)
val EXP_EXP_LE_MONO_IMP = store_thm(
  "EXP_EXP_LE_MONO_IMP",
  ``!a b n. a <= b ==> a ** n <= b ** n``,
  rw[]);

(* Theorem: m <= n ==> !p. p ** n = p ** m * p ** (n - m) *)
(* Proof:
   Note n = (n - m) + m          by m <= n
        p ** n
      = p ** (n - m) * p ** m    by EXP_ADD
      = p ** m * p ** (n - m)    by MULT_COMM
*)
val EXP_BY_ADD_SUB_LE = store_thm(
  "EXP_BY_ADD_SUB_LE",
  ``!m n. m <= n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rpt strip_tac >>
  `n = (n - m) + m` by decide_tac >>
  metis_tac[EXP_ADD, MULT_COMM]);

(* Theorem: m < n ==> (p ** n = p ** m * p ** (n - m)) *)
(* Proof: by EXP_BY_ADD_SUB_LE, LESS_IMP_LESS_OR_EQ *)
val EXP_BY_ADD_SUB_LT = store_thm(
  "EXP_BY_ADD_SUB_LT",
  ``!m n. m < n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rw[EXP_BY_ADD_SUB_LE]);

(* Theorem: 0 < m ==> m ** (SUC n) DIV m = m ** n *)
(* Proof:
     m ** (SUC n) DIV m
   = (m * m ** n) DIV m    by EXP
   = m ** n                by MULT_TO_DIV, 0 < m
*)
val EXP_SUC_DIV = store_thm(
  "EXP_SUC_DIV",
  ``!m n. 0 < m ==> (m ** (SUC n) DIV m = m ** n)``,
  simp[EXP, MULT_TO_DIV]);

(* Theorem: n <= n ** 2 *)
(* Proof:
   If n = 0,
      Then n ** 2 = 0 >= 0       by ZERO_EXP
   If n <> 0, then 0 < n         by NOT_ZERO_LT_ZERO
      Hence n = n ** 1           by EXP_1
             <= n ** 2           by EXP_BASE_LEQ_MONO_IMP
*)
val SELF_LE_SQ = store_thm(
  "SELF_LE_SQ",
  ``!n. n <= n ** 2``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n /\ 1 <= 2` by decide_tac >>
  metis_tac[EXP_BASE_LEQ_MONO_IMP, EXP_1]);

(* Theorem: a <= b /\ c <= d ==> a + c <= b + d *)
(* Proof: by LESS_EQ_LESS_EQ_MONO, or
   Note a <= b ==>  a + c <= b + c    by LE_ADD_RCANCEL
    and c <= d ==>  b + c <= b + d    by LE_ADD_LCANCEL
   Thus             a + c <= b + d    by LESS_EQ_TRANS
*)
val LE_MONO_ADD2 = store_thm(
  "LE_MONO_ADD2",
  ``!a b c d. a <= b /\ c <= d ==> a + c <= b + d``,
  rw[LESS_EQ_LESS_EQ_MONO]);

(* Theorem: a < b /\ c < d ==> a + c < b + d *)
(* Proof:
   Note a < b ==>  a + c < b + c    by LT_ADD_RCANCEL
    and c < d ==>  b + c < b + d    by LT_ADD_LCANCEL
   Thus            a + c < b + d    by LESS_TRANS
*)
val LT_MONO_ADD2 = store_thm(
  "LT_MONO_ADD2",
  ``!a b c d. a < b /\ c < d ==> a + c < b + d``,
  rw[LT_ADD_RCANCEL, LT_ADD_LCANCEL]);

(* Theorem: a <= b /\ c <= d ==> a * c <= b * d *)
(* Proof: by LESS_MONO_MULT2, or
   Note a <= b ==> a * c <= b * c  by LE_MULT_RCANCEL
    and c <= d ==> b * c <= b * d  by LE_MULT_LCANCEL
   Thus            a * c <= b * d  by LESS_EQ_TRANS
*)
val LE_MONO_MULT2 = store_thm(
  "LE_MONO_MULT2",
  ``!a b c d. a <= b /\ c <= d ==> a * c <= b * d``,
  rw[LESS_MONO_MULT2]);

(* Theorem: a < b /\ c < d ==> a * c < b * d *)
(* Proof:
   Note 0 < b, by a < b.
    and 0 < d, by c < d.
   If c = 0,
      Then a * c = 0 < b * d   by MULT_EQ_0
   If c <> 0, then 0 < c       by NOT_ZERO_LT_ZERO
      a < b ==> a * c < b * c  by LT_MULT_RCANCEL, 0 < c
      c < d ==> b * c < b * d  by LT_MULT_LCANCEL, 0 < b
   Thus         a * c < b * d  by LESS_TRANS
*)
val LT_MONO_MULT2 = store_thm(
  "LT_MONO_MULT2",
  ``!a b c d. a < b /\ c < d ==> a * c < b * d``,
  rpt strip_tac >>
  `0 < b /\ 0 < d` by decide_tac >>
  Cases_on `c = 0` >-
  metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LT_MULT_RCANCEL, LT_MULT_LCANCEL, LESS_TRANS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < m /\ 1 < n ==> (m + n <= m * n) *)
(* Proof:
   Let m = m' + 1, n = n' + 1.
   Note m' <> 0 /\ n' <> 0.
   Thus m' * n' <> 0               by MULT_EQ_0
     or 1 <= m' * n'
       m * n
     = (m' + 1) * (n' + 1)
     = m' * n' + m' + n' + 1       by arithmetic
    >= 1 + m' + n' + 1             by 1 <= m' * n'
     = m + n
*)
val SUM_LE_PRODUCT = store_thm(
  "SUM_LE_PRODUCT",
  ``!m n. 1 < m /\ 1 < n ==> (m + n <= m * n)``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?m' n'. (m = m' + 1) /\ (n = n' + 1)` by metis_tac[num_CASES, ADD1] >>
  `m * n = (m' + 1) * n' + (m' + 1)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = m' * n' + n' + (m' + 1)` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = m + (n' + m' * n')` by decide_tac >>
  `m' * n' <> 0` by fs[] >>
  decide_tac);

(* Theorem: 0 < n ==> k * n + 1 <= (k + 1) * n *)
(* Proof:
        k * n + 1
     <= k * n + n          by 1 <= n
     <= (k + 1) * n        by RIGHT_ADD_DISTRIB
*)
val MULTIPLE_SUC_LE = store_thm(
  "MULTIPLE_SUC_LE",
  ``!n k. 0 < n ==> k * n + 1 <= (k + 1) * n``,
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ 0 < n /\ (m + n = 2) ==> m = 1 /\ n = 1 *)
(* Proof: by arithmetic. *)
val ADD_EQ_2 = store_thm(
  "ADD_EQ_2",
  ``!m n. 0 < m /\ 0 < n /\ (m + n = 2) ==> (m = 1) /\ (n = 1)``,
  rw_tac arith_ss[]);

(* Theorem: EVEN 0 *)
(* Proof: by EVEN. *)
val EVEN_0 = store_thm(
  "EVEN_0",
  ``EVEN 0``,
  simp[]);

(* Theorem: ODD 1 *)
(* Proof: by ODD. *)
val ODD_1 = store_thm(
  "ODD_1",
  ``ODD 1``,
  simp[]);

(* Theorem: EVEN 2 *)
(* Proof: by EVEN_MOD2. *)
val EVEN_2 = store_thm(
  "EVEN_2",
  ``EVEN 2``,
  EVAL_TAC);

(*
EVEN_ADD  |- !m n. EVEN (m + n) <=> (EVEN m <=> EVEN n)
ODD_ADD   |- !m n. ODD (m + n) <=> (ODD m <=/=> ODD n)
EVEN_MULT |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
ODD_MULT  |- !m n. ODD (m * n) <=> ODD m /\ ODD n
*)

(* Derive theorems. *)
val EVEN_SQ = save_thm("EVEN_SQ",
    EVEN_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val EVEN_SQ = |- !n. EVEN (n ** 2) <=> EVEN n: thm *)
val ODD_SQ = save_thm("ODD_SQ",
    ODD_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val ODD_SQ = |- !n. ODD (n ** 2) <=> ODD n: thm *)

(* Theorem: EVEN (2 * a + b) <=> EVEN b *)
(* Proof:
       EVEN (2 * a + b)
   <=> EVEN (2 * a) /\ EVEN b      by EVEN_ADD
   <=>            T /\ EVEN b      by EVEN_DOUBLE
   <=> EVEN b
*)
Theorem EQ_PARITY:
  !a b. EVEN (2 * a + b) <=> EVEN b
Proof
  rw[EVEN_ADD, EVEN_DOUBLE]
QED

(* Theorem: ODD x <=> (x MOD 2 = 1) *)
(* Proof:
   If part: ODD x ==> x MOD 2 = 1
      Since  ODD x
         <=> ~EVEN x          by ODD_EVEN
         <=> ~(x MOD 2 = 0)   by EVEN_MOD2
         But x MOD 2 < 2      by MOD_LESS, 0 < 2
          so x MOD 2 = 1      by arithmetic
   Only-if part: x MOD 2 = 1 ==> ODD x
      By contradiction, suppose ~ODD x.
      Then EVEN x             by ODD_EVEN
       and x MOD 2 = 0        by EVEN_MOD2
      This contradicts x MOD 2 = 1.
*)
val ODD_MOD2 = store_thm(
  "ODD_MOD2",
  ``!x. ODD x <=> (x MOD 2 = 1)``,
  metis_tac[EVEN_MOD2, ODD_EVEN, MOD_LESS,
             DECIDE``0 <> 1 /\ 0 < 2 /\ !n. n < 2 /\ n <> 1 ==> (n = 0)``]);

(* Theorem: (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD *)
val EVEN_ODD_SUC = store_thm(
  "EVEN_ODD_SUC",
  ``!n. (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD]);

(* Theorem: 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ *)
val EVEN_ODD_PRE = store_thm(
  "EVEN_ODD_PRE",
  ``!n. 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ]);

(* Theorem: EVEN (n * (n + 1)) *)
(* Proof:
   If EVEN n, true        by EVEN_MULT
   If ~(EVEN n),
      Then EVEN (SUC n)   by EVEN
        or EVEN (n + 1)   by ADD1
      Thus true           by EVEN_MULT
*)
val EVEN_PARTNERS = store_thm(
  "EVEN_PARTNERS",
  ``!n. EVEN (n * (n + 1))``,
  metis_tac[EVEN, EVEN_MULT, ADD1]);

(* Theorem: EVEN n ==> (n = 2 * HALF n) *)
(* Proof:
   Note EVEN n ==> ?m. n = 2 * m     by EVEN_EXISTS
    and HALF n = HALF (2 * m)        by above
               = m                   by MULT_TO_DIV, 0 < 2
   Thus n = 2 * m = 2 * HALF n       by above
*)
val EVEN_HALF = store_thm(
  "EVEN_HALF",
  ``!n. EVEN n ==> (n = 2 * HALF n)``,
  metis_tac[EVEN_EXISTS, MULT_TO_DIV, DECIDE``0 < 2``]);

(* Theorem: ODD n ==> (n = 2 * HALF n + 1 *)
(* Proof:
   Since n = HALF n * 2 + n MOD 2  by DIVISION, 0 < 2
           = 2 * HALF n + n MOD 2  by MULT_COMM
           = 2 * HALF n + 1        by ODD_MOD2
*)
val ODD_HALF = store_thm(
  "ODD_HALF",
  ``!n. ODD n ==> (n = 2 * HALF n + 1)``,
  metis_tac[DIVISION, MULT_COMM, ODD_MOD2, DECIDE``0 < 2``]);

(* Theorem: EVEN n ==> (HALF (SUC n) = HALF n) *)
(* Proof:
   Note n = (HALF n) * 2 + (n MOD 2)   by DIVISION, 0 < 2
          = (HALF n) * 2               by EVEN_MOD2
    Now SUC n
      = n + 1                          by ADD1
      = (HALF n) * 2 + 1               by above
   Thus HALF (SUC n)
      = ((HALF n) * 2 + 1) DIV 2       by above
      = HALF n                         by DIV_MULT, 1 < 2
*)
val EVEN_SUC_HALF = store_thm(
  "EVEN_SUC_HALF",
  ``!n. EVEN n ==> (HALF (SUC n) = HALF n)``,
  rpt strip_tac >>
  `n MOD 2 = 0` by rw[GSYM EVEN_MOD2] >>
  `n = HALF n * 2 + n MOD 2` by rw[DIVISION] >>
  `SUC n = HALF n * 2 + 1` by rw[] >>
  metis_tac[DIV_MULT, DECIDE``1 < 2``]);

(* Theorem: ODD n ==> (HALF (SUC n) = SUC (HALF n)) *)
(* Proof:
     SUC n
   = SUC (2 * HALF n + 1)              by ODD_HALF
   = 2 * HALF n + 1 + 1                by ADD1
   = 2 * HALF n + 2                    by arithmetic
   = 2 * (HALF n + 1)                  by LEFT_ADD_DISTRIB
   = 2 * SUC (HALF n)                  by ADD1
   = SUC (HALF n) * 2 + 0              by MULT_COMM, ADD_0
   Hence HALF (SUC n) = SUC (HALF n)   by DIV_UNIQUE, 0 < 2
*)
val ODD_SUC_HALF = store_thm(
  "ODD_SUC_HALF",
  ``!n. ODD n ==> (HALF (SUC n) = SUC (HALF n))``,
  rpt strip_tac >>
  `SUC n = SUC (2 * HALF n + 1)` by rw[ODD_HALF] >>
  `_ = SUC (HALF n) * 2 + 0` by rw[] >>
  metis_tac[DIV_UNIQUE, DECIDE``0 < 2``]);

(* Theorem: (HALF n = 0) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (HALF n = 0) ==> ((n = 0) \/ (n = 1))
      Note n = (HALF n) * 2 + (n MOD 2)    by DIVISION, 0 < 2
             = n MOD 2                     by HALF n = 0
       and n MOD 2 < 2                     by MOD_LESS, 0 < 2
        so n < 2, or n = 0 or n = 1        by arithmetic
   Only-if part: HALF 0 = 0, HALF 1 = 0.
      True since both 0 or 1 < 2           by LESS_DIV_EQ_ZERO, 0 < 2
*)
val HALF_EQ_0 = store_thm(
  "HALF_EQ_0",
  ``!n. (HALF n = 0) <=> ((n = 0) \/ (n = 1))``,
  rw[LESS_DIV_EQ_ZERO, EQ_IMP_THM] >>
  `n = (HALF n) * 2 + (n MOD 2)` by rw[DIVISION] >>
  `n MOD 2 < 2` by rw[MOD_LESS] >>
  decide_tac);

(* Theorem: (HALF n = n) <=> (n = 0) *)
(* Proof:
   If part: HALF n = n ==> n = 0
      Note n = 2 * HALF n + (n MOD 2)    by DIVISION, MULT_COMM
        so n = 2 * n + (n MOD 2)         by HALF n = n
        or 0 = n + (n MOD 2)             by arithmetic
      Thus n  = 0  and (n MOD 2 = 0)     by ADD_EQ_0
   Only-if part: HALF 0 = 0, true        by ZERO_DIV, 0 < 2
*)
val HALF_EQ_SELF = store_thm(
  "HALF_EQ_SELF",
  ``!n. (HALF n = n) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
  rw[ADD_EQ_0]);

(* Theorem: 0 < n ==> HALF n < n *)
(* Proof:
   Note HALF n <= n     by DIV_LESS_EQ, 0 < 2
    and HALF n <> n     by HALF_EQ_SELF, n <> 0
     so HALF n < n      by arithmetic
*)
val HALF_LT = store_thm(
  "HALF_LT",
  ``!n. 0 < n ==> HALF n < n``,
  rpt strip_tac >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n <> n` by rw[HALF_EQ_SELF] >>
  decide_tac);

(* Theorem: 2 < n ==> (1 + HALF n < n) *)
(* Proof:
   If EVEN n,
      then     2 * HALF n = n      by EVEN_HALF
        so 2 + 2 * HALF n < n + n  by 2 < n
        or     1 + HALF n < n      by arithmetic
   If ~EVEN n, then ODD n          by ODD_EVEN
      then 1 + 2 * HALF n = 2      by ODD_HALF
        so 1 + 2 * HALF n < n      by 2 < n
      also 2 + 2 * HALF n < n + n  by 1 < n
        or     1 + HALF n < n      by arithmetic
*)
Theorem HALF_ADD1_LT:
  !n. 2 < n ==> 1 + HALF n < n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `2 * HALF n = n` by rw[EVEN_HALF] >>
    decide_tac,
    `1 + 2 * HALF n = n` by rw[ODD_HALF, ODD_EVEN] >>
    decide_tac
  ]
QED

(* Theorem alias *)
Theorem HALF_TWICE = MULT_DIV_2;
(* val HALF_TWICE = |- !n. HALF (2 * n) = n: thm *)

(* Theorem: n * HALF m <= HALF (n * m) *)
(* Proof:
   Let k = HALF m.
   If EVEN m,
      Then m = 2 * k           by EVEN_HALF
        HALF (n * m)
      = HALF (n * (2 * k))     by above
      = HALF (2 * (n * k))     by arithmetic
      = n * k                  by HALF_TWICE
   If ~EVEN m, then ODD m      by ODD_EVEN
      Then m = 2 * k + 1       by ODD_HALF
      so   HALF (n * m)
         = HALF (n * (2 * k + 1))        by above
         = HALF (2 * (n * k) + n)        by LEFT_ADD_DISTRIB
         = HALF (2 * (n * k)) + HALF n   by ADD_DIV_ADD_DIV
         = n * k + HALF n                by HALF_TWICE
         >= n * k                        by arithmetic
*)
Theorem HALF_MULT: !m n. n * (m DIV 2) <= (n * m) DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `k = m DIV 2` >>
  Cases_on `EVEN m`
  >- (`m = 2 * k` by rw[EVEN_HALF, Abbr`k`] >>
      simp[]) >>
  `ODD m` by rw[ODD_EVEN] >>
  `m = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  simp[LEFT_ADD_DISTRIB]
QED

(* Theorem: 2 * HALF n <= n /\ n <= SUC (2 * HALF n) *)
(* Proof:
   If EVEN n,
      Then n = 2 * HALF n         by EVEN_HALF
       and n = n < SUC n          by LESS_SUC
        or n <= n <= SUC n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
   If ~(EVEN n), then ODD n       by EVEN_ODD
      Then n = 2 * HALF n + 1     by ODD_HALF
             = SUC (2 * HALF n)   by ADD1
        or n - 1 < n = n
        or n - 1 <= n <= n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
*)
val TWO_HALF_LE_THM = store_thm(
  "TWO_HALF_LE_THM",
  ``!n. 2 * HALF n <= n /\ n <= SUC (2 * HALF n)``,
  strip_tac >>
  Cases_on `EVEN n` >-
  rw[GSYM EVEN_HALF] >>
  `ODD n` by rw[ODD_EVEN] >>
  `n <> 0` by metis_tac[ODD] >>
  `n = SUC (2 * HALF n)` by rw[ODD_HALF, ADD1] >>
  `2 * HALF n = PRE n` by rw[] >>
  rw[]);

(* Theorem: 2 * ((HALF n) * m) <= n * m *)
(* Proof:
      2 * ((HALF n) * m)
    = 2 * (m * HALF n)      by MULT_COMM
   <= 2 * (HALF (m * n))    by HALF_MULT
   <= m * n                 by TWO_HALF_LE_THM
    = n * m                 by MULT_COMM
*)
val TWO_HALF_TIMES_LE = store_thm(
  "TWO_HALF_TIMES_LE",
  ``!m n. 2 * ((HALF n) * m) <= n * m``,
  rpt strip_tac >>
  `2 * (m * HALF n) <= 2 * (HALF (m * n))` by rw[HALF_MULT] >>
  `2 * (HALF (m * n)) <= m * n` by rw[TWO_HALF_LE_THM] >>
  fs[]);

(* Theorem: 0 < n ==> 1 + HALF n <= n *)
(* Proof:
   If n = 1,
      HALF 1 = 0, hence true.
   If n <> 1,
      Then HALF n <> 0       by HALF_EQ_0, n <> 0, n <> 1
      Thus 1 + HALF n
        <= HALF n + HALF n   by 1 <= HALF n
         = 2 * HALF n
        <= n                 by TWO_HALF_LE_THM
*)
val HALF_ADD1_LE = store_thm(
  "HALF_ADD1_LE",
  ``!n. 0 < n ==> 1 + HALF n <= n``,
  rpt strip_tac >>
  (Cases_on `n = 1` >> simp[]) >>
  `HALF n <> 0` by metis_tac[HALF_EQ_0, NOT_ZERO] >>
  `1 + HALF n <= 2 * HALF n` by decide_tac >>
  `2 * HALF n <= n` by rw[TWO_HALF_LE_THM] >>
  decide_tac);

(* Theorem: (HALF n) ** 2 <= (n ** 2) DIV 4 *)
(* Proof:
   Let k = HALF n.
   Then 2 * k <= n                by TWO_HALF_LE_THM
     so (2 * k) ** 2 <= n ** 2                by EXP_EXP_LE_MONO
    and (2 * k) ** 2 DIV 4 <= n ** 2 DIV 4    by DIV_LE_MONOTONE, 0 < 4
    But (2 * k) ** 2 DIV 4
      = 4 * k ** 2 DIV 4          by EXP_BASE_MULT
      = k ** 2                    by MULT_TO_DIV, 0 < 4
   Thus k ** 2 <= n ** 2 DIV 4.
*)
val HALF_SQ_LE = store_thm(
  "HALF_SQ_LE",
  ``!n. (HALF n) ** 2 <= (n ** 2) DIV 4``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `2 * k <= n` by rw[TWO_HALF_LE_THM, Abbr`k`] >>
  `(2 * k) ** 2 <= n ** 2` by rw[] >>
  `(2 * k) ** 2 DIV 4 <= n ** 2 DIV 4` by rw[DIV_LE_MONOTONE] >>
  `(2 * k) ** 2 DIV 4 = 4 * k ** 2 DIV 4` by rw[EXP_BASE_MULT] >>
  `_ = k ** 2` by rw[MULT_TO_DIV] >>
  decide_tac);

(* Obtain theorems *)
val HALF_LE = save_thm("HALF_LE",
    DIV_LESS_EQ |> SPEC ``2`` |> SIMP_RULE (arith_ss) [] |> SPEC ``n:num`` |> GEN_ALL);
(* val HALF_LE = |- !n. HALF n <= n: thm *)
val HALF_LE_MONO = save_thm("HALF_LE_MONO",
    DIV_LE_MONOTONE |> SPEC ``2`` |> SIMP_RULE (arith_ss) []);
(* val HALF_LE_MONO = |- !x y. x <= y ==> HALF x <= HALF y: thm *)

(* Theorem: HALF (SUC n) <= n *)
(* Proof:
   If EVEN n,
      Then ?k. n = 2 * k                       by EVEN_EXISTS
       and SUC n = 2 * k + 1
        so HALF (SUC n) = k <= k + k = n       by ineqaulities
   Otherwise ODD n,                            by ODD_EVEN
      Then ?k. n = 2 * k + 1                   by ODD_EXISTS
       and SUC n = 2 * k + 2
        so HALF (SUC n) = k + 1 <= k + k + 1 = n
*)
Theorem HALF_SUC:
  !n. HALF (SUC n) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `HALF (SUC n) = k` by simp[ADD1] >>
    decide_tac,
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC n) = k + 1` by simp[ADD1] >>
    decide_tac
  ]
QED

(* Theorem: 0 < n ==> HALF (SUC (SUC n)) <= n *)
(* Proof:
   Note SUC (SUC n) = n + 2        by ADD1
   If EVEN n,
      then ?k. n = 2 * k           by EVEN_EXISTS
      Since n = 2 * k <> 0         by NOT_ZERO, 0 < n
        so k <> 0, or 1 <= k       by MULT_EQ_0
           HALF (n + 2)
         = k + 1                   by arithmetic
        <= k + k                   by above
         = n
   Otherwise ODD n,                by ODD_EVEN
      then ?k. n = 2 * k + 1       by ODD_EXISTS
           HALF (n + 2)
         = HALF (2 * k + 3)        by arithmetic
         = k + 1                   by arithmetic
        <= k + k + 1               by ineqaulities
         = n
*)
Theorem HALF_SUC_SUC:
  !n. 0 < n ==> HALF (SUC (SUC n)) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `1 <= k` by decide_tac >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[],
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[]
  ]
QED

(* Theorem: n < HALF (SUC m) ==> 2 * n + 1 <= m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
       and SUC m = 2 * HALF m + 1              by ADD1
        so     n < (2 * HALF m + 1) DIV 2      by given
        or     n < HALF m                      by arithmetic
           2 * n < 2 * HALF m                  by LT_MULT_LCANCEL
           2 * n < m                           by above
       2 * n + 1 <= m                          by arithmetic
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
        and SUC m = 2 * HALF m + 2             by ADD1
         so     n < (2 * HALF m + 2) DIV 2     by given
         or     n < HALF m + 1                 by arithmetic
        2 * n + 1 < 2 * HALF m + 1             by LT_MULT_LCANCEL, LT_ADD_RCANCEL
         or 2 * n + 1 < m                      by above
    Overall, 2 * n + 1 <= m.
*)
Theorem HALF_SUC_LE:
  !n m. n < HALF (SUC m) ==> 2 * n + 1 <= m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `m = 2 * HALF m` by simp[EVEN_HALF] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1)` by metis_tac[ADD1] >>
    `_ = HALF m` by simp[] >>
    simp[],
    `m = 2 * HALF m + 1` by simp[ODD_HALF, ODD_EVEN] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1 + 1)` by metis_tac[ADD1] >>
    `_ = HALF m + 1` by simp[] >>
    simp[]
  ]
QED

(* Theorem: 2 * n < m ==> n <= HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n < 2 * HALF m                  by above
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n < 2 * HALF m + 1             by above
         so 2 * n <= 2 * HALF m                by removing 1
         or     n <= HALF m                    by LE_MULT_LCANCEL
    Overall, n <= HALF m.
*)
Theorem HALF_EVEN_LE:
  !n m. 2 * n < m ==> n <= HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: 2 * n + 1 < m ==> n < HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n + 1 < 2 * HALF m              by above
        or     2 * n < 2 * HALF m              by removing 1
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n + 1 < 2 * HALF m + 1         by above
         or     2 * n < 2 * HALF m             by LT_ADD_RCANCEL
         or         n < HALF m                 by LT_MULT_LCANCEL
    Overall, n < HALF m.
*)
Theorem HALF_ODD_LT:
  !n m. 2 * n + 1 < m ==> n < HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n + 1 < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n + 1 < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: EVEN n ==> !m. m * n = (TWICE m) * (HALF n) *)
(* Proof:
     (TWICE m) * (HALF n)
   = (2 * m) * (HALF n)   by notation
   = m * TWICE (HALF n)   by MULT_COMM, MULT_ASSOC
   = m * n                by EVEN_HALF
*)
val MULT_EVEN = store_thm(
  "MULT_EVEN",
  ``!n. EVEN n ==> !m. m * n = (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, EVEN_HALF]);

(* Theorem: ODD n ==> !m. m * n = m + (TWICE m) * (HALF n) *)
(* Proof:
     m + (TWICE m) * (HALF n)
   = m + (2 * m) * (HALF n)     by notation
   = m + m * (TWICE (HALF n))   by MULT_COMM, MULT_ASSOC
   = m * (SUC (TWICE (HALF n))) by MULT_SUC
   = m * (TWICE (HALF n) + 1)   by ADD1
   = m * n                      by ODD_HALF
*)
val MULT_ODD = store_thm(
  "MULT_ODD",
  ``!n. ODD n ==> !m. m * n = m + (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, ODD_HALF, MULT_SUC, ADD1]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m) *)
(* Proof:
   Note ?k. m = 2 * k                by EVEN_EXISTS, EVEN m
    and k <> 0                       by MULT_EQ_0, m <> 0
    ==> (n MOD m) MOD 2 = n MOD 2    by MOD_MULT_MOD
   The result follows                by EVEN_MOD2
*)
val EVEN_MOD_EVEN = store_thm(
  "EVEN_MOD_EVEN",
  ``!m. EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m)``,
  rpt strip_tac >>
  `?k. m = 2 * k` by rw[GSYM EVEN_EXISTS] >>
  `(n MOD m) MOD 2 = n MOD 2` by rw[MOD_MULT_MOD] >>
  metis_tac[EVEN_MOD2]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m) *)
(* Proof: by EVEN_MOD_EVEN, ODD_EVEN *)
val EVEN_MOD_ODD = store_thm(
  "EVEN_MOD_ODD",
  ``!m. EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m)``,
  rw_tac std_ss[EVEN_MOD_EVEN, ODD_EVEN]);

(* Theorem: c <= a ==> ((a - b) - (a - c) = c - b) *)
(* Proof:
     a - b - (a - c)
   = a - (b + (a - c))     by SUB_RIGHT_SUB, no condition
   = a - ((a - c) + b)     by ADD_COMM, no condition
   = a - (a - c) - b       by SUB_RIGHT_SUB, no condition
   = a + c - a - b         by SUB_SUB, c <= a
   = c + a - a - b         by ADD_COMM, no condition
   = c + (a - a) - b       by LESS_EQ_ADD_SUB, a <= a
   = c + 0 - b             by SUB_EQUAL_0
   = c - b
*)
val SUB_SUB_SUB = store_thm(
  "SUB_SUB_SUB",
  ``!a b c. c <= a ==> ((a - b) - (a - c) = c - b)``,
  decide_tac);

(* Theorem: c <= a ==> (a + b - (a - c) = c + b) *)
(* Proof:
     a + b - (a - c)
   = a + b + c - a      by SUB_SUB, a <= c
   = a + (b + c) - a    by ADD_ASSOC
   = (b + c) + a - a    by ADD_COMM
   = b + c - (a - a)    by SUB_SUB, a <= a
   = b + c - 0          by SUB_EQUAL_0
   = b + c              by SUB_0
*)
val ADD_SUB_SUB = store_thm(
  "ADD_SUB_SUB",
  ``!a b c. c <= a ==> (a + b - (a - c) = c + b)``,
  decide_tac);

(* Theorem: 0 < p ==> !m n. (m - n = p) <=> (m = n + p) *)
(* Proof:
   If part: m - n = p ==> m = n + p
      Note 0 < m - n          by 0 < p
        so n < m              by LESS_MONO_ADD
        or m = m - n + n      by SUB_ADD, n <= m
             = p + n          by m - n = p
             = n + p          by ADD_COMM
   Only-if part: m = n + p ==> m - n = p
        m - n
      = (n + p) - n           by m = n + p
      = p + n - n             by ADD_COMM
      = p                     by ADD_SUB
*)
val SUB_EQ_ADD = store_thm(
  "SUB_EQ_ADD",
  ``!p. 0 < p ==> !m n. (m - n = p) <=> (m = n + p)``,
  decide_tac);

(* Note: ADD_EQ_SUB |- !m n p. n <= p ==> ((m + n = p) <=> (m = p - n)) *)

(* Theorem: 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b) *)
(* Proof:
   By contradiction, suppose b <= d.
   Since a * b <> 0         by MULT_EQ_0, 0 < a, 0 < b
      so d <> 0, or 0 < d   by MULT_EQ_0, a * b <> 0
     Now a * b <= a * d     by LE_MULT_LCANCEL, b <= d, a <> 0
     and a * d < c * d      by LT_MULT_LCANCEL, a < c, d <> 0
      so a * b < c * d      by LESS_EQ_LESS_TRANS
    This contradicts a * b = c * d.
*)
val MULT_EQ_LESS_TO_MORE = store_thm(
  "MULT_EQ_LESS_TO_MORE",
  ``!a b c d. 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b)``,
  spose_not_then strip_assume_tac >>
  `b <= d` by decide_tac >>
  `0 < d` by decide_tac >>
  `a * b <= a * d` by rw[LE_MULT_LCANCEL] >>
  `a * d < c * d` by rw[LT_MULT_LCANCEL] >>
  decide_tac);

(* Theorem: 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c *)
(* Proof:
   By contradiction, suppose c <= a.
   With d < b, which gives d <= b    by LESS_IMP_LESS_OR_EQ
   Thus c * d <= a * b               by LE_MONO_MULT2
     or a * b = c * d                by a * b <= c * d
   Note 0 < c /\ 0 < d               by given
    ==> a < c                        by MULT_EQ_LESS_TO_MORE
   This contradicts c <= a.

MULT_EQ_LESS_TO_MORE
|- !a b c d. 0 < a /\ 0 < b /\ a < c /\ a * b = c * d ==> d < b
             0 < d /\ 0 < c /\ d < b /\ d * c = b * a ==> a < c
*)
val LE_IMP_REVERSE_LT = store_thm(
  "LE_IMP_REVERSE_LT",
  ``!a b c d. 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c``,
  spose_not_then strip_assume_tac >>
  `c <= a` by decide_tac >>
  `c * d <= a * b` by rw[LE_MONO_MULT2] >>
  `a * b = c * d` by decide_tac >>
  `a < c` by metis_tac[MULT_EQ_LESS_TO_MORE, MULT_COMM]);

(* ------------------------------------------------------------------------- *)
(* Exponential Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EVEN n ==> !m. m ** n = (SQ m) ** (HALF n) *)
(* Proof:
     (SQ m) ** (HALF n)
   = (m ** 2) ** (HALF n)   by notation
   = m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** n                 by EVEN_HALF
*)
val EXP_EVEN = store_thm(
  "EXP_EVEN",
  ``!n. EVEN n ==> !m. m ** n = (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `(SQ m) ** (HALF n) = m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** n` by rw[GSYM EVEN_HALF] >>
  rw[]);

(* Theorem: ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n) *)
(* Proof:
     m * (SQ m) ** (HALF n)
   = m * (m ** 2) ** (HALF n)   by notation
   = m * m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** (SUC (2 * HALF n))    by EXP
   = m ** (2 * HALF n + 1)      by ADD1
   = m ** n                     by ODD_HALF
*)
val EXP_ODD = store_thm(
  "EXP_ODD",
  ``!n. ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `m * (SQ m) ** (HALF n) = m * m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** (2 * HALF n + 1)` by rw[GSYM EXP, ADD1] >>
  `_ = m ** n` by rw[GSYM ODD_HALF] >>
  rw[]);

(* An exponentiation identity *)
(* val EXP_THM = save_thm("EXP_THM", CONJ EXP_EVEN EXP_ODD); *)
(*
val EXP_THM = |- (!n. EVEN n ==> !m. m ** n = SQ m ** HALF n) /\
                  !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n: thm
*)
(* Next is better *)

(* Theorem: m ** n = if n = 0 then 1 else if n = 1 then m else
            if EVEN n then (m * m) ** HALF n else m * ((m * m) ** (HALF n)) *)
(* Proof: mainly by EXP_EVEN, EXP_ODD. *)
Theorem EXP_THM:
  !m n. m ** n = if n = 0 then 1 else if n = 1 then m
                 else if EVEN n then (m * m) ** HALF n
                 else m * ((m * m) ** (HALF n))
Proof
  metis_tac[EXP_0, EXP_1, EXP_EVEN, EXP_ODD, EVEN_ODD]
QED

(* Theorem: m ** n =
            if n = 0 then 1
            else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n) *)
(* Proof:
   If n = 0, to show:
      m ** 0 = 1, true                      by EXP_0
   If EVEN n, to show:
      m ** n = (m * m) ** (HALF n), true    by EXP_EVEN
   If ~EVEN n, ODD n, to show:              by EVEN_ODD
      m ** n = m * (m * m) ** HALF n, true  by EXP_ODD
*)
val EXP_EQN = store_thm(
  "EXP_EQN",
  ``!m n. m ** n =
         if n = 0 then 1
         else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n)``,
  rw[] >-
  rw[Once EXP_EVEN] >>
  `ODD n` by metis_tac[EVEN_ODD] >>
  rw[Once EXP_ODD]);

(* Theorem: m ** n = if n = 0 then 1 else (if EVEN n then 1 else m) * (m * m) ** (HALF n) *)
(* Proof: by EXP_EQN *)
val EXP_EQN_ALT = store_thm(
  "EXP_EQN_ALT",
  ``!m n. m ** n =
         if n = 0 then 1
         else (if EVEN n then 1 else m) * (m * m) ** (HALF n)``,
  rw[Once EXP_EQN]);

(* Theorem: m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n) *)
(* Proof: by EXP_EQN_ALT, EXP_2 *)
val EXP_ALT_EQN = store_thm(
  "EXP_ALT_EQN",
  ``!m n. m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n)``,
  metis_tac[EXP_EQN_ALT, EXP_2]);

(* Theorem: 1 < m ==>
      (b ** n) MOD m = if (n = 0) then 1
                       else let result = (b * b) ** (HALF n) MOD m
                             in if EVEN n then result else (b * result) MOD m *)
(* Proof:
   This is to show:
   (1) 1 < m ==> b ** 0 MOD m = 1
         b ** 0 MOD m
       = 1 MOD m            by EXP_0
       = 1                  by ONE_MOD, 1 < m
   (2) EVEN n ==> b ** n MOD m = (b ** 2) ** HALF n MOD m
         b ** n MOD m
       = (b * b) ** HALF n MOD m    by EXP_EVEN
       = (b ** 2) ** HALF n MOD m   by EXP_2
   (3) ~EVEN n ==> b ** n MOD m = (b * (b ** 2) ** HALF n) MOD m
         b ** n MOD m
       = (b * (b * b) ** HALF n) MOD m      by EXP_ODD, EVEN_ODD
       = (b * (b ** 2) ** HALF n) MOD m     by EXP_2
*)
Theorem EXP_MOD_EQN:
  !b n m. 1 < m ==>
      ((b ** n) MOD m =
       if (n = 0) then 1
       else let result = (b * b) ** (HALF n) MOD m
             in if EVEN n then result else (b * result) MOD m)
Proof
  rw[]
  >- metis_tac[EXP_EVEN, EXP_2] >>
  metis_tac[EXP_ODD, EXP_2, EVEN_ODD]
QED

(* Pretty version of EXP_MOD_EQN, same pattern as EXP_EQN_ALT. *)

(* Theorem: 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m *)
(* Proof: by EXP_MOD_EQN *)
val EXP_MOD_ALT = store_thm(
  "EXP_MOD_ALT",
  ``!b n m. 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m``,
  rpt strip_tac >>
  imp_res_tac EXP_MOD_EQN >>
  last_x_assum (qspecl_then [`n`, `b`] strip_assume_tac) >>
  rw[]);

(* Theorem: x ** (y ** SUC n) = (x ** y) ** y ** n *)
(* Proof:
      x ** (y ** SUC n)
    = x ** (y * y ** n)     by EXP
    = (x ** y) ** (y ** n)  by EXP_EXP_MULT
*)
val EXP_EXP_SUC = store_thm(
  "EXP_EXP_SUC",
  ``!x y n. x ** (y ** SUC n) = (x ** y) ** y ** n``,
  rw[EXP, EXP_EXP_MULT]);

(* Theorem: 1 + n * m <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 + 0 * m <= (1 + m) ** 0
        LHS = 1 + 0 * m = 1            by arithmetic
        RHS = (1 + m) ** 0 = 1         by EXP_0
        Hence true.
   Step: 1 + n * m <= (1 + m) ** n ==>
         1 + SUC n * m <= (1 + m) ** SUC n
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
        <= (1 + m) ** n + m                 by induction hypothesis
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LE_LOW = store_thm(
  "EXP_LOWER_LE_LOW",
  ``!n m. 1 + n * m <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP_0] >>
  `0 < (1 + m) ** n` by rw[] >>
  `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
  `_ = 1 + n * m + m` by decide_tac >>
  `m <= m * (1 + m) ** n` by rw[] >>
  `1 + SUC n * m <= (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
  `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
  `_ = (1 + m) ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 < 0 ==> 1 + 0 * m <= (1 + m) ** 0
        True since 1 < 0 = F.
   Step: 1 < n ==> 1 + n * m < (1 + m) ** n ==>
         1 < SUC n ==> 1 + SUC n * m < (1 + m) ** SUC n
      Note n <> 0, since SUC 0 = 1          by ONE
      If n = 1,
         Note m * m <> 0                    by MULT_EQ_0, m <> 0
           (1 + m) ** SUC 1
         = (1 + m) ** 2                     by TWO
         = 1 + 2 * m + m * m                by expansion
         > 1 + 2 * m                        by 0 < m * m
         = 1 + (SUC 1) * m
      If n <> 1, then 1 < n.
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
         < (1 + m) ** n + m                 by induction hypothesis, 1 < n
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LT_LOW = store_thm(
  "EXP_LOWER_LT_LOW",
  ``!n m. 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `n <> 0` by fs[] >>
  Cases_on `n = 1` >| [
    simp[] >>
    `(m + 1) ** 2 = (m + 1) * (m + 1)` by rw[GSYM EXP_2] >>
    `_ = m * m + 2 * m + 1` by decide_tac >>
    `0 < SQ m` by metis_tac[SQ_EQ_0, NOT_ZERO_LT_ZERO] >>
    decide_tac,
    `1 < n` by decide_tac >>
    `0 < (1 + m) ** n` by rw[] >>
    `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
    `_ = 1 + n * m + m` by decide_tac >>
    `m <= m * (1 + m) ** n` by rw[] >>
    `1 + SUC n * m < (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
    `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
    `_ = (1 + m) ** SUC n` by rw[EXP] >>
    decide_tac
  ]);

(*
Note: EXP_LOWER_LE_LOW collects the first two terms of binomial expansion.
  but EXP_LOWER_LE_HIGH collects the last two terms of binomial expansion.
*)

(* Theorem: n * m ** (n - 1) + m ** n <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 0 * m ** (0 - 1) + m ** 0 <= (1 + m) ** 0
        LHS = 0 * m ** (0 - 1) + m ** 0
            = 0 + 1                      by EXP_0
            = 1
           <= 1 = (1 + m) ** 0 = RHS     by EXP_0
   Step: n * m ** (n - 1) + m ** n <= (1 + m) ** n ==>
         SUC n * m ** (SUC n - 1) + m ** SUC n <= (1 + m) ** SUC n
        If n = 0,
           LHS = 1 * m ** 0 + m ** 1
               = 1 + m                   by EXP_0, EXP_1
               = (1 + m) ** 1 = RHS      by EXP_1
        If n <> 0,
           Then SUC (n - 1) = n          by n <> 0.
           LHS = SUC n * m ** (SUC n - 1) + m ** SUC n
               = (n + 1) * m ** n + m * m ** n     by EXP, ADD1
               = (n + 1 + m) * m ** n              by arithmetic
               = n * m ** n + (1 + m) * m ** n     by arithmetic
               = n * m ** SUC (n - 1) + (1 + m) * m ** n    by SUC (n - 1) = n
               = n * m * m ** (n - 1) + (1 + m) * m ** n    by EXP
               = m * (n * m ** (n - 1)) + (1 + m) * m ** n  by arithmetic
              <= (1 + m) * (n * m ** (n - 1)) + (1 + m) * m ** n   by m < 1 + m
               = (1 + m) * (n * m ** (n - 1) + m ** n)      by LEFT_ADD_DISTRIB
              <= (1 + m) * (1 + m) ** n                     by induction hypothesis
               = (1 + m) ** SUC n                           by EXP
*)
val EXP_LOWER_LE_HIGH = store_thm(
  "EXP_LOWER_LE_HIGH",
  ``!n m. n * m ** (n - 1) + m ** n <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  Cases_on `n = 0` >-
  simp[EXP_0] >>
  `SUC (n - 1) = n` by decide_tac >>
  simp[EXP] >>
  simp[ADD1] >>
  `m * m ** n + (n + 1) * m ** n = (m + (n + 1)) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (n + (m + 1)) * m ** n` by decide_tac >>
  `_ = n * m ** n + (m + 1) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = n * m ** SUC (n - 1) + (m + 1) * m ** n` by rw[] >>
  `_ = n * (m * m ** (n - 1)) + (m + 1) * m ** n` by rw[EXP] >>
  `_ = m * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  `m * (n * m ** (n - 1)) + (m + 1) * m ** n <= (m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  qabbrev_tac `t = n * m ** (n - 1) + m ** n` >>
  `(m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n = (m + 1) * t` by rw[LEFT_ADD_DISTRIB, Abbr`t`] >>
  `t <= (m + 1) ** n` by metis_tac[ADD_COMM] >>
  `(m + 1) * t <= (m + 1) * (m + 1) ** n` by rw[] >>
  decide_tac);

(* Theorem: 1 < n ==> SUC n < 2 ** n *)
(* Proof:
   Note 1 + n < (1 + 1) ** n    by EXP_LOWER_LT_LOW, m = 1
     or SUC n < SUC 1 ** n      by ADD1
     or SUC n < 2 ** n          by TWO
*)
val SUC_X_LT_2_EXP_X = store_thm(
  "SUC_X_LT_2_EXP_X",
  ``!n. 1 < n ==> SUC n < 2 ** n``,
  rpt strip_tac >>
  `1 + n * 1 < (1 + 1) ** n` by rw[EXP_LOWER_LT_LOW] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* DIVIDES Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m) *)
(* Proof:
   Note n = n DIV m * m + n MOD m /\
        n MOD m < m                      by DIVISION
   Thus m * (n DIV m) <= n               by MULT_COMM
    and n < m * (n DIV m) + m
          = m * (n DIV m  + 1)           by LEFT_ADD_DISTRIB
          = m * SUC (n DIV m)            by ADD1
*)
val DIV_MULT_LESS_EQ = store_thm(
  "DIV_MULT_LESS_EQ",
  ``!m n. 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m)``,
  ntac 3 strip_tac >>
  `(n = n DIV m * m + n MOD m) /\ n MOD m < m` by rw[DIVISION] >>
  `n < m * (n DIV m) + m` by decide_tac >>
  `m * (n DIV m) + m = m * (SUC (n DIV m))` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < n ==> (m - n) DIV n = if m < n then 0 else (m DIV n - 1) *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) DIV n = 0     by ZERO_DIV
   Otherwise, n <= m, and (m - n) DIV n = m DIV n - 1 by SUB_DIV
*)
val SUB_DIV_EQN = store_thm(
  "SUB_DIV_EQN",
  ``!m n. 0 < n ==> ((m - n) DIV n = if m < n then 0 else (m DIV n - 1))``,
  rw[SUB_DIV] >>
  `m - n = 0` by decide_tac >>
  rw[ZERO_DIV]);

(* Theorem: 0 < n ==> (m - n) MOD n = if m < n then 0 else m MOD n *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) MOD n = 0     by ZERO_MOD
   Otherwise, n <= m, and (m - n) MOD n = m MOD n     by SUB_MOD
*)
val SUB_MOD_EQN = store_thm(
  "SUB_MOD_EQN",
  ``!m n. 0 < n ==> ((m - n) MOD n = if m < n then 0 else m MOD n)``,
  rw[SUB_MOD]);

(* Theorem: 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m *)
(* Proof:
   Note n = n DIV (SUC m) * (SUC m) + n MOD (SUC m)   by DIVISION
          = n DIV m * m + n MOD m                     by DIVISION
          = n DIV m * m                               by n MOD m = 0
   Thus n DIV SUC m * SUC m <= n DIV m * m            by arithmetic
   Note m < SUC m                                     by LESS_SUC
    and n DIV m <> 0, or 0 < n DIV m                  by DIV_MOD_EQ_0
   Thus n DIV (SUC m) < n DIV m                       by LE_IMP_REVERSE_LT
*)
val DIV_LT_SUC = store_thm(
  "DIV_LT_SUC",
  ``!m n. 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m``,
  rpt strip_tac >>
  `n DIV m * m = n` by metis_tac[DIVISION, ADD_0] >>
  `_ = n DIV (SUC m) * (SUC m) + n MOD (SUC m)` by metis_tac[DIVISION, SUC_POS] >>
  `n DIV SUC m * SUC m <= n DIV m * m` by decide_tac >>
  `m < SUC m` by decide_tac >>
  `0 < n DIV m` by metis_tac[DIV_MOD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LE_IMP_REVERSE_LT]);

(* Theorem: 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x *)
(* Proof:
   Note x < y ==> SUC x <= y                by arithmetic
   Thus n DIV y <= n DIV (SUC x)            by DIV_LE_MONOTONE_REVERSE
    But 0 < x /\ 0 < n /\ (n MOD x = 0)     by given
    ==> n DIV (SUC x) < n DIV x             by DIV_LT_SUC
   Hence n DIV y < n DIV x                  by inequalities
*)
val DIV_LT_MONOTONE_REVERSE = store_thm(
  "DIV_LT_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x``,
  rpt strip_tac >>
  `SUC x <= y` by decide_tac >>
  `n DIV y <= n DIV (SUC x)` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `n DIV (SUC x) < n DIV x` by rw[DIV_LT_SUC] >>
  decide_tac);

(* Theorem: k <> 0 ==> (m divides n <=> (k * m) divides (k * n)) *)
(* Proof:
       m divides n
   <=> ?q. n = q * m             by divides_def
   <=> ?q. k * n = k * (q * m)   by EQ_MULT_LCANCEL, k <> 0
   <=> ?q. k * n = q * (k * m)   by MULT_ASSOC, MULT_COMM
   <=> (k * m) divides (k * n)   by divides_def
*)
val DIVIDES_MULTIPLE_IFF = store_thm(
  "DIVIDES_MULTIPLE_IFF",
  ``!m n k. k <> 0 ==> (m divides n <=> (k * m) divides (k * n))``,
  rpt strip_tac >>
  `m divides n <=> ?q. n = q * m` by rw[GSYM divides_def] >>
  `_ = ?q. (k * n = k * (q * m))` by rw[EQ_MULT_LCANCEL] >>
  metis_tac[divides_def, MULT_COMM, MULT_ASSOC]);

(* Theorem: 0 < n /\ n divides m ==> m = n * (m DIV n) *)
(* Proof:
   n divides m <=> m MOD n = 0    by DIVIDES_MOD_0
   m = (m DIV n) * n + (m MOD n)  by DIVISION
     = (m DIV n) * n              by above
     = n * (m DIV n)              by MULT_COMM
*)
val DIVIDES_FACTORS = store_thm(
  "DIVIDES_FACTORS",
  ``!m n. 0 < n /\ n divides m ==> (m = n * (m DIV n))``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, MULT_COMM]);

(* Theorem: 0 < n /\ n divides m ==> (m DIV n) divides m *)
(* Proof:
   By DIVIDES_FACTORS: m = (m DIV n) * n
   Hence (m DIV n) | m    by divides_def
*)
val DIVIDES_COFACTOR = store_thm(
  "DIVIDES_COFACTOR",
  ``!m n. 0 < n /\ n divides m ==> (m DIV n) divides m``,
  metis_tac[DIVIDES_FACTORS, divides_def]);

(* Theorem: n divides q ==> p * (q DIV n) = (p * q) DIV n *)
(* Proof:
   n divides q ==> q MOD n = 0               by DIVIDES_MOD_0
   p * q = p * ((q DIV n) * n + q MOD n)     by DIVISION
         = p * ((q DIV n) * n)               by ADD_0
         = p * (q DIV n) * n                 by MULT_ASSOC
         = p * (q DIV n) * n + 0             by ADD_0
   Hence (p * q) DIV n = p * (q DIV n)       by DIV_UNIQUE, 0 < n:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULTIPLY_DIV = store_thm(
  "MULTIPLY_DIV",
  ``!n p q. 0 < n /\ n divides q ==> (p * (q DIV n) = (p * q) DIV n)``,
  rpt strip_tac >>
  `q MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `p * q = p * ((q DIV n) * n)` by metis_tac[DIVISION, ADD_0] >>
  `_ = p * (q DIV n) * n + 0` by rw[MULT_ASSOC] >>
  metis_tac[DIV_UNIQUE]);

(* Note: The condition: n divides q is important:
> EVAL ``5 * (10 DIV 3)``;
val it = |- 5 * (10 DIV 3) = 15: thm
> EVAL ``(5 * 10) DIV 3``;
val it = |- 5 * 10 DIV 3 = 16: thm
*)

(* Theorem: 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m *)
(* Proof:
   Note 0 < m                                   by ZERO_DIVIDES, 0 < n
   Given divides m n ==> ?q. n = q * m          by divides_def
   Since x = (x DIV n) * n + (x MOD n)          by DIVISION
           = (x DIV n) * (q * m) + (x MOD n)    by above
           = ((x DIV n) * q) * m + (x MOD n)    by MULT_ASSOC
   Hence     x MOD m
           = ((x DIV n) * q) * m + (x MOD n)) MOD m                by above
           = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m   by MOD_PLUS
           = (0 + (x MOD n) MOD m) MOD m                           by MOD_EQ_0
           = (x MOD n) MOD m                                       by ADD, MOD_MOD
*)
val DIVIDES_MOD_MOD = store_thm(
  "DIVIDES_MOD_MOD",
  ``!m n. 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `x MOD m = ((x DIV n) * n + (x MOD n)) MOD m` by rw[GSYM DIVISION] >>
  `_ = (((x DIV n) * q) * m + (x MOD n)) MOD m` by rw[MULT_ASSOC] >>
  `_ = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m` by rw[MOD_PLUS] >>
  rw[MOD_EQ_0, MOD_MOD]);

(* Theorem: m divides n <=> (m * k) divides (n * k) *)
(* Proof: by divides_def and EQ_MULT_LCANCEL. *)
val DIVIDES_CANCEL = store_thm(
  "DIVIDES_CANCEL",
  ``!k. 0 < k ==> !m n. m divides n <=> (m * k) divides (n * k)``,
  rw[divides_def] >>
  `k <> 0` by decide_tac >>
  `!q. (q * m) * k = q * (m * k)` by rw_tac arith_ss[] >>
  metis_tac[EQ_MULT_LCANCEL, MULT_COMM]);

(* Theorem: m divides n ==> (k * m) divides (k * n) *)
(* Proof:
       m divides n
   ==> ?q. n = q * m              by divides_def
   So  k * n = k * (q * m)
             = (k * q) * m        by MULT_ASSOC
             = (q * k) * m        by MULT_COMM
             = q * (k * m)        by MULT_ASSOC
   Hence (k * m) divides (k * n)  by divides_def
*)
val DIVIDES_CANCEL_COMM = store_thm(
  "DIVIDES_CANCEL_COMM",
  ``!m n k. m divides n ==> (k * m) divides (k * n)``,
  metis_tac[MULT_ASSOC, MULT_COMM, divides_def]);

(* Theorem: 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n) *)
(* Proof:
    n divides x ==> x = n * (x DIV n)              by DIVIDES_FACTORS
   or           m * x = (m * n) * (x DIV n)        by MULT_ASSOC
       n divides x
   ==> divides (m * n) (m * x)                     by DIVIDES_CANCEL_COMM
   ==> m * x = (m * n) * ((m * x) DIV (m * n))     by DIVIDES_FACTORS
   Equating expressions for m * x,
       (m * n) * (x DIV n) = (m * n) * ((m * x) DIV (m * n))
   or              x DIV n = (m * x) DIV (m * n)   by MULT_LEFT_CANCEL
*)
val DIV_COMMON_FACTOR = store_thm(
  "DIV_COMMON_FACTOR",
  ``!m n. 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  `0 < m * n` by metis_tac[MULT_EQ_0] >>
  metis_tac[DIVIDES_CANCEL_COMM, DIVIDES_FACTORS, MULT_ASSOC, MULT_LEFT_CANCEL]);

(* Theorem: 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m)) *)
(* Proof:
     x DIV (m DIV n)
   = (n * x) DIV (n * (m DIV n))   by DIV_COMMON_FACTOR, (m DIV n) divides x, 0 < m DIV n.
   = (n * x) DIV m                 by DIVIDES_FACTORS, n divides m, 0 < n.
   = n * (x DIV m)                 by MULTIPLY_DIV, m divides x, 0 < m.
*)
val DIV_DIV_MULT = store_thm(
  "DIV_DIV_MULT",
  ``!m n x. 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m))``,
  metis_tac[DIV_COMMON_FACTOR, DIVIDES_FACTORS, MULTIPLY_DIV]);

(* ------------------------------------------------------------------------- *)
(* Basic Divisibility                                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: a little trick to make divisibility to mean equality. *)

(* Theorem: 0 < n /\ n < 2 * m ==> (m divides n <=> n = m) *)
(* Proof:
   If part: 0 < n /\ n < 2 * m /\ m divides n ==> n = m
      Note ?k. n = k * m           by divides_def
       Now k * m < 2 * m           by n < 2 * m
        so 0 < m /\ k < 2          by LT_MULT_LCANCEL
       and 0 < k                   by MULT
        so 1 <= k                  by LE_MULT_LCANCEL, 0 < m
      Thus k = 1, or n = m.
   Only-if part: true              by DIVIDES_REFL
*)
Theorem divides_iff_equal:
  !m n. 0 < n /\ n < 2 * m ==> (m divides n <=> n = m)
Proof
  rw[EQ_IMP_THM] >>
  `?k. n = k * m` by rw[GSYM divides_def] >>
  `0 < m /\ k < 2` by fs[LT_MULT_LCANCEL] >>
  `0 < k` by fs[] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Theorem: 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t *)
(* Proof:
   Let k = m DIV n.
   Since m <> 0, n divides m ==> n <> 0       by ZERO_DIVIDES
    Thus m = k * n                            by DIVIDES_EQN, 0 < n
      so 0 < k                                by MULT, NOT_ZERO_LT_ZERO
   Hence k * n divides t * n <=> k divides t  by DIVIDES_CANCEL, 0 < k
*)
val dividend_divides_divisor_multiple = store_thm(
  "dividend_divides_divisor_multiple",
  ``!m n. 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t``,
  rpt strip_tac >>
  qabbrev_tac `k = m DIV n` >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `0 < k` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  metis_tac[DIVIDES_CANCEL]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m *)
(* Proof:
   Since 0 < n means n <> 0,
    then m divides n ==> m <> 0     by ZERO_DIVIDES
      or 0 < m                      by NOT_ZERO_LT_ZERO
*)
(* Theorem: 1 < p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof:
   Note p <> 0 /\ p <> 1                      by 1 < p

   If-part: p ** m divides p ** n ==> m <= n
      By contradiction, suppose n < m.
      Let d = m - n, then d <> 0              by n < m
      Note p ** m = p ** n * p ** d           by EXP_BY_ADD_SUB_LT
       and p ** n <> 0                        by EXP_EQ_0, p <> 0
       Now ?q. p ** n = q * p ** m            by divides_def
                      = q * p ** d * p ** n   by MULT_ASSOC_COMM
      Thus 1 * p ** n = q * p ** d * p ** n   by MULT_LEFT_1
        or          1 = q * p ** d            by MULT_RIGHT_CANCEL
       ==>     p ** d = 1                     by MULT_EQ_1
        or          d = 0                     by EXP_EQ_1, p <> 1
      This contradicts d <> 0.

  Only-if part: m <= n ==> p ** m divides p ** n
      Note p ** n = p ** m * p ** (n - m)     by EXP_BY_ADD_SUB_LE
      Thus p ** m divides p ** n              by divides_def, MULT_COMM
*)
val power_divides_iff = store_thm(
  "power_divides_iff",
  ``!p. 1 < p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rpt strip_tac >>
  `p <> 0 /\ p <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < m /\ m - n <> 0` by decide_tac >>
    qabbrev_tac `d = m - n` >>
    `p ** m = p ** n * p ** d` by rw[EXP_BY_ADD_SUB_LT, Abbr`d`] >>
    `p ** n <> 0` by rw[EXP_EQ_0] >>
    `?q. p ** n = q * p ** m` by rw[GSYM divides_def] >>
    `_ = q * p ** d * p ** n` by metis_tac[MULT_ASSOC_COMM] >>
    `1 = q * p ** d` by metis_tac[MULT_RIGHT_CANCEL, MULT_LEFT_1] >>
    `p ** d = 1` by metis_tac[MULT_EQ_1] >>
    metis_tac[EXP_EQ_1],
    `p ** n = p ** m * p ** (n - m)` by rw[EXP_BY_ADD_SUB_LE] >>
    metis_tac[divides_def, MULT_COMM]
  ]);

(* Theorem: prime p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof: by power_divides_iff, ONE_LT_PRIME *)
val prime_power_divides_iff = store_thm(
  "prime_power_divides_iff",
  ``!p. prime p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rw[power_divides_iff, ONE_LT_PRIME]);

(* Theorem: 0 < n /\ 1 < p ==> p divides p ** n *)
(* Proof:
   Note 0 < n <=> 1 <= n         by arithmetic
     so p ** 1 divides p ** n    by power_divides_iff
     or      p divides p ** n    by EXP_1
*)
val divides_self_power = store_thm(
  "divides_self_power",
  ``!n p. 0 < n /\ 1 < p ==> p divides p ** n``,
  metis_tac[power_divides_iff, EXP_1, DECIDE``0 < n <=> 1 <= n``]);

(* Theorem: a divides b /\ 0 < b /\ b < 2 * a ==> (b = a) *)
(* Proof:
   Note ?k. b = k * a      by divides_def
    and 0 < k              by MULT_EQ_0, 0 < b
    and k < 2              by LT_MULT_RCANCEL, k * a < 2 * a
   Thus k = 1              by 0 < k < 2
     or b = k * a = a      by arithmetic
*)
Theorem divides_eq_thm:
  !a b. a divides b /\ 0 < b /\ b < 2 * a ==> (b = a)
Proof
  rpt strip_tac >>
  `?k. b = k * a` by rw[GSYM divides_def] >>
  `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `k < 2` by metis_tac[LT_MULT_RCANCEL] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Idea: factor equals cofactor iff the number is a square of the factor. *)

(* Theorem: 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2) *)
(* Proof:
        n
      = n DIV m * m + n MOD m    by DIVISION, 0 < m
      = n DIV m * m + 0          by DIVIDES_MOD_0, m divides n
      = n DIV m * m              by ADD_0
   If m = n DIV m,
     then n = m * m = m ** 2     by EXP_2
   If n = m ** 2,
     then n = m * m              by EXP_2
       so m = n DIV m            by EQ_MULT_RCANCEL
*)
Theorem factor_eq_cofactor:
  !m n. 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2)
Proof
  rw[EQ_IMP_THM] >>
  `n = n DIV m * m + n MOD m` by rw[DIVISION] >>
  `_ = m * m + 0` by metis_tac[DIVIDES_MOD_0] >>
  simp[]
QED

(* Theorem alias *)
Theorem euclid_prime = gcdTheory.P_EUCLIDES;
(* |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b *)

(* Theorem alias *)
Theorem euclid_coprime = gcdTheory.L_EUCLIDES;
(* |- !a b c. coprime a b /\ b divides a * c ==> b divides c *)

(* Both MOD_EQ_DIFF and MOD_EQ are required in MOD_MULT_LCANCEL *)

(* Idea: equality exchange for MOD without negative. *)

(* Theorem: b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n) *)
(* Proof:
   Note 0 < n                  by b < n or c < n
   Let x = n - b, y = n - c.
   The goal is: (a + b) MOD n = (c + d) MOD n <=>
                (a + y) MOD n = (d + x) MOD n
   Note n = b + x, n = c + y   by arithmetic
       (a + b) MOD n = (c + d) MOD n
   <=> (a + b + x + y) MOD n = (c + d + x + y) MOD n   by ADD_MOD
   <=> (a + y + n) MOD n = (d + x + n) MOD n           by above
   <=> (a + y) MOD n = (d + x) MOD n                   by ADD_MOD

   For integers, this is simply: a + b = c + d <=> a - c = b - d.
*)
Theorem mod_add_eq_sub:
  !n a b c d. b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n)
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `n = b + (n - b)` by decide_tac >>
  `n = c + (n - c)` by decide_tac >>
  qabbrev_tac `x = n - b` >>
  qabbrev_tac `y = n - c` >>
  `a + b + x + y = a + y + n` by decide_tac >>
  `c + d + x + y = d + x + n` by decide_tac >>
  `(a + b) MOD n = (c + d) MOD n <=>
    (a + b + x + y) MOD n = (c + d + x + y) MOD n` by simp[ADD_MOD] >>
  fs[ADD_MOD]
QED

(* Idea: generalise above equality exchange for MOD. *)

(* Theorem: 0 < n ==>
            ((a + b) MOD n = (c + d) MOD n <=>
             (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n) *)
(* Proof:
   Let b' = b MOD n, c' = c MOD n.
   Note b' < n            by MOD_LESS, 0 < n
    and c' < n            by MOD_LESS, 0 < n
        (a + b) MOD n = (c + d) MOD n
    <=> (a + b') MOD n = (d + c') MOD n              by MOD_PLUS2
    <=> (a + (n - c')) MOD n = (d + (n - b')) MOD n  by mod_add_eq_sub
*)
Theorem mod_add_eq_sub_eq:
  !n a b c d. 0 < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n)
Proof
  rpt strip_tac >>
  `b MOD n < n /\ c MOD n < n` by rw[] >>
  `(a + b) MOD n = (a + b MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  `(c + d) MOD n = (d + c MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  prove_tac[mod_add_eq_sub]
QED

(*
MOD_EQN is a trick to eliminate MOD:
|- !n. 0 < n ==> !a b. a MOD n = b <=> ?c. a = c * n + b /\ b < n
*)

(* Idea: remove MOD for divides: need b divides (a MOD n) ==> b divides a. *)

(* Theorem: 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a *)
(* Proof:
   Note ?k. n = k * b                    by divides_def, b divides n
    and ?h. a MOD n = h * b              by divides_def, b divides (a MOD n)
    and ?c. a = c * n + h * b            by MOD_EQN, 0 < n
              = c * (k * b) + h * b      by above
              = (c * k + h) * b          by RIGHT_ADD_DISTRIB
   Thus b divides a                      by divides_def
*)
Theorem mod_divides:
  !n a b. 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a
Proof
  rpt strip_tac >>
  `?k. n = k * b` by rw[GSYM divides_def] >>
  `?h. a MOD n = h * b` by rw[GSYM divides_def] >>
  `?c. a = c * n + h * b` by metis_tac[MOD_EQN] >>
  `_ = (c * k + h) * b` by simp[] >>
  metis_tac[divides_def]
QED

(* Idea: include converse of mod_divides. *)

(* Theorem: 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a) *)
(* Proof:
   If part: b divides n /\ b divides a MOD n ==> b divides a
      This is true                       by mod_divides
   Only-if part: b divides n /\ b divides a ==> b divides a MOD n
   Note ?c. a = c * n + a MOD n          by MOD_EQN, 0 < n
              = c * n + 1 * a MOD n      by MULT_LEFT_1
   Thus b divides (a MOD n)              by divides_linear_sub
*)
Theorem mod_divides_iff:
  !n a b. 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[mod_divides] >>
  `?c. a = c * n + a MOD n` by metis_tac[MOD_EQN] >>
  metis_tac[divides_linear_sub, MULT_LEFT_1]
QED

(* An application of
DIVIDES_MOD_MOD:
|- !m n. 0 < n /\ m divides n ==> !x. x MOD n MOD m = x MOD m
Let x = a linear combination.
(linear) MOD n MOD m = linear MOD m
change n to a product m * n, for z = linear MOD (m * n).
(linear) MOD (m * n) MOD g = linear MOD g
z MOD g = linear MOD g
requires: g divides (m * n)
*)

(* Idea: generalise for MOD equation: a MOD n = b. Need c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note 0 < c                      by ZERO_DIVIDES, c divides n, 0 < n.
       a MOD n = b
   ==> (a MOD n) MOD c = b MOD c
   ==>         a MOD c = b MOD c   by DIVIDES_MOD_MOD, 0 < n, c divides n
   But a MOD c = 0                 by DIVIDES_MOD_0, c divides a
    so b MOD c = 0, or c divides b by DIVIDES_MOD_0, 0 < c
*)
Theorem mod_divides_divides:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b
Proof
  simp[mod_divides_iff]
QED

(* Idea: include converse of mod_divides_divides. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_divides_divides
   Only-if part: c divides b ==> c divides a
      Note b = a MOD n, so this is true        by mod_divides
*)
Theorem mod_divides_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b)
Proof
  simp[mod_divides_iff]
QED

(* Idea: divides across MOD: from a MOD n = b MOD n to c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note c divides (b MOD n)        by mod_divides_divides
     so c divides b                by mod_divides
   Or, simply have both            by mod_divides_iff
*)
Theorem mod_eq_divides:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b
Proof
  metis_tac[mod_divides_iff]
QED

(* Idea: include converse of mod_eq_divides. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_eq_divides, a MOD n = b MOD n
   Only-if: c divides b ==> c divides a, true  by mod_eq_divides, b MOD n = a MOD n
*)
Theorem mod_eq_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b)
Proof
  metis_tac[mod_eq_divides]
QED

(* Idea: special cross-multiply equality of MOD (m * n) implies pair equality:
         from (m * a) MOD (m * n) = (n * b) MOD (m * n) to a = n /\ b = m. *)

(* Theorem: coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m) *)
(* Proof:
   Given (m * a) MOD (m * n) = (n * b) MOD (m * n)
   Note n divides (n * b)      by factor_divides
    and n divides (m * n)      by factor_divides
     so n divides (m * a)      by mod_eq_divides
    ==> n divides a            by euclid_coprime, MULT_COMM
   Thus a = n                  by divides_iff_equal
   Also m divides (m * a)      by factor_divides
    and m divides (m * n)      by factor_divides
     so m divides (n * b)      by mod_eq_divides
    ==> m divides b            by euclid_coprime, GCD_SYM
   Thus b = m                  by divides_iff_equal
*)
Theorem mod_mult_eq_mult:
  !m n a b. coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m)
Proof
  ntac 5 strip_tac >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < m * n` by rw[] >>
  strip_tac >| [
    `n divides (n * b)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * n)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * a)` by metis_tac[mod_eq_divides] >>
    `n divides a` by metis_tac[euclid_coprime, MULT_COMM] >>
    metis_tac[divides_iff_equal],
    `m divides (m * a)` by rw[DIVIDES_MULTIPLE] >>
    `m divides (m * n)` by metis_tac[DIVIDES_REFL, DIVIDES_MULTIPLE, MULT_COMM] >>
    `m divides (n * b)` by metis_tac[mod_eq_divides] >>
    `m divides b` by metis_tac[euclid_coprime, GCD_SYM] >>
    metis_tac[divides_iff_equal]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Even and Odd Parity.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n /\ EVEN m ==> EVEN (m ** n) *)
(* Proof:
   Since EVEN m, m MOD 2 = 0       by EVEN_MOD2
       EVEN (m ** n)
   <=> (m ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (m MOD 2) ** n MOD 2 = 0    by EXP_MOD, 0 < 2
   ==> 0 ** n MOD 2 = 0            by above
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
(* Note: arithmeticTheory.EVEN_EXP  |- !m n. 0 < n /\ EVEN m ==> EVEN (m ** n) *)

(* Theorem: !m n. 0 < n /\ ODD m ==> ODD (m ** n) *)
(* Proof:
   Since ODD m, m MOD 2 = 1        by ODD_MOD2
       ODD (m ** n)
   <=> (m ** n) MOD 2 = 1          by ODD_MOD2
   <=> (m MOD 2) ** n MOD 2 = 1    by EXP_MOD, 0 < 2
   ==> 1 ** n MOD 2 = 1            by above
   <=> 1 MOD 2 = 1                 by EXP_1, n <> 0
   <=> 1 = 1                       by ONE_MOD, 1 < 2
   <=> T
*)
val ODD_EXP = store_thm(
  "ODD_EXP",
  ``!m n. 0 < n /\ ODD m ==> ODD (m ** n)``,
  rw[ODD_MOD2] >>
  `n <> 0 /\ 0 < 2` by decide_tac >>
  metis_tac[EXP_MOD, EXP_1, ONE_MOD]);

(* Theorem: 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n)) *)
(* Proof:
   First goal: EVEN m <=> EVEN (m ** n)
     If part: EVEN m ==> EVEN (m ** n), true by EVEN_EXP
     Only-if part: EVEN (m ** n) ==> EVEN m.
        By contradiction, suppose ~EVEN m.
        Then ODD m                           by EVEN_ODD
         and ODD (m ** n)                    by ODD_EXP
          or ~EVEN (m ** n)                  by EVEN_ODD
        This contradicts EVEN (m ** n).
   Second goal: ODD m <=> ODD (m ** n)
     Just mirror the reasoning of first goal.
*)
val power_parity = store_thm(
  "power_parity",
  ``!n. 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n))``,
  metis_tac[EVEN_EXP, ODD_EXP, ODD_EVEN]);

(* Theorem: 0 < n ==> EVEN (2 ** n) *)
(* Proof:
       EVEN (2 ** n)
   <=> (2 ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (2 MOD 2) ** n MOD 2 = 0    by EXP_MOD
   <=> 0 ** n MOD 2 = 0            by DIVMOD_ID, 0 < 2
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
Theorem EXP_2_EVEN:  !n. 0 < n ==> EVEN (2 ** n)
Proof rw[EVEN_MOD2, ZERO_EXP]
QED
(* Michael's proof by induction
val EXP_2_EVEN = store_thm(
  "EXP_2_EVEN",
  ``!n. 0 < n ==> EVEN (2 ** n)``,
  Induct >> rw[EXP, EVEN_DOUBLE]);
 *)

(* Theorem: 0 < n ==> ODD (2 ** n - 1) *)
(* Proof:
   Since 0 < 2 ** n                  by EXP_POS, 0 < 2
      so 1 <= 2 ** n                 by LESS_EQ
    thus SUC (2 ** n - 1)
       = 2 ** n - 1 + 1              by ADD1
       = 2 ** n                      by SUB_ADD, 1 <= 2 ** n
     and EVEN (2 ** n)               by EXP_2_EVEN
   Hence ODD (2 ** n - 1)            by EVEN_ODD_SUC
*)
val EXP_2_PRE_ODD = store_thm(
  "EXP_2_PRE_ODD",
  ``!n. 0 < n ==> ODD (2 ** n - 1)``,
  rpt strip_tac >>
  `0 < 2 ** n` by rw[EXP_POS] >>
  `SUC (2 ** n - 1) = 2 ** n` by decide_tac >>
  metis_tac[EXP_2_EVEN, EVEN_ODD_SUC]);

(* ------------------------------------------------------------------------- *)
(* Modulo Inverse                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Cancellation Law for MOD p]
   For prime p, if x MOD p <> 0,
      (x*y) MOD p = (x*z) MOD p ==> y MOD p = z MOD p *)
(* Proof:
       (x*y) MOD p = (x*z) MOD p
   ==> ((x*y) - (x*z)) MOD p = 0   by MOD_EQ_DIFF
   ==>       (x*(y-z)) MOD p = 0   by arithmetic LEFT_SUB_DISTRIB
   ==>           (y-z) MOD p = 0   by EUCLID_LEMMA, x MOD p <> 0
   ==>               y MOD p = z MOD p    if z <= y

   Since this theorem is symmetric in y, z,
   First prove the theorem assuming z <= y,
   then use the same proof for y <= z.
*)
Theorem MOD_MULT_LCANCEL:
  !p x y z. prime p /\ (x * y) MOD p = (x * z) MOD p /\ x MOD p <> 0 ==> y MOD p = z MOD p
Proof
  rpt strip_tac >>
  `!a b c. c <= b /\ (a * b) MOD p = (a * c) MOD p /\ a MOD p <> 0 ==> b MOD p = c MOD p` by
  (rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a * b - a * c) MOD p = 0` by rw[MOD_EQ_DIFF] >>
  `(a * (b - c)) MOD p = 0` by rw[LEFT_SUB_DISTRIB] >>
  metis_tac[EUCLID_LEMMA, MOD_EQ]) >>
  Cases_on `z <= y` >-
  metis_tac[] >>
  `y <= z` by decide_tac >>
  metis_tac[]
QED

(* Theorem: prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p *)
(* Proof: by MOD_MULT_LCANCEL, MULT_COMM *)
Theorem MOD_MULT_RCANCEL:
  !p x y z. prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p
Proof
  metis_tac[MOD_MULT_LCANCEL, MULT_COMM]
QED

(* Theorem: For prime p, 0 < x < p ==> ?y. 0 < y /\ y < p /\ (y*x) MOD p = 1 *)
(* Proof:
       0 < x < p
   ==> ~ divides p x                    by NOT_LT_DIVIDES
   ==> gcd p x = 1                      by gcdTheory.PRIME_GCD
   ==> ?k q. k * x = q * p + 1          by gcdTheory.LINEAR_GCD
   ==> k*x MOD p = (q*p + 1) MOD p      by arithmetic
   ==> k*x MOD p = 1                    by MOD_MULT, 1 < p.
   ==> (k MOD p)*(x MOD p) MOD p = 1    by MOD_TIMES2
   ==> ((k MOD p) * x) MOD p = 1        by LESS_MOD, x < p.
   Now   k MOD p < p                    by MOD_LESS
   and   0 < k MOD p since (k*x) MOD p <> 0  (by 1 <> 0)
                       and x MOD p <> 0      (by ~ divides p x)
                                        by EUCLID_LEMMA
   Hence take y = k MOD p, then 0 < y < p.
*)
val MOD_MULT_INV_EXISTS = store_thm(
  "MOD_MULT_INV_EXISTS",
  ``!p x. prime p /\ 0 < x /\ x < p ==> ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by metis_tac[PRIME_POS, ONE_LT_PRIME] >>
  `gcd p x = 1` by metis_tac[PRIME_GCD, NOT_LT_DIVIDES] >>
  `?k q. k * x = q * p + 1` by metis_tac[LINEAR_GCD, NOT_ZERO_LT_ZERO] >>
  `1 = (k * x) MOD p` by metis_tac[MOD_MULT] >>
  `_ = ((k MOD p) * (x MOD p)) MOD p` by metis_tac[MOD_TIMES2] >>
  `0 < k MOD p` by
  (`1 <> 0` by decide_tac >>
  `x MOD p <> 0` by metis_tac[DIVIDES_MOD_0, NOT_LT_DIVIDES] >>
  `k MOD p <> 0` by metis_tac[EUCLID_LEMMA, MOD_MOD] >>
  decide_tac) >>
  metis_tac[MOD_LESS, LESS_MOD]);

(* Convert this theorem into MUL_INV_DEF *)

(* Step 1: move ?y forward by collecting quantifiers *)
val lemma = prove(
  ``!p x. ?y. prime p /\ 0 < x /\ x < p ==> 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  metis_tac[MOD_MULT_INV_EXISTS]);

(* Step 2: apply SKOLEM_THM *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val MOD_MULT_INV_DEF = new_specification(
  "MOD_MULT_INV_DEF",
  ["MOD_MULT_INV"], (* avoid MOD_MULT_INV_EXISTS: thm *)
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val MOD_MULT_INV_DEF =
    |- !p x.
         prime p /\ 0 < x /\ x < p ==>
         0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\
         ((MOD_MULT_INV p x * x) MOD p = 1) : thm
*)

(* ------------------------------------------------------------------------- *)
(* FACTOR Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ~ prime n ==> n has a proper prime factor p *)
(* Proof: apply PRIME_FACTOR:
   !n. n <> 1 ==> ?p. prime p /\ p divides n : thm
*)
val PRIME_FACTOR_PROPER = store_thm(
  "PRIME_FACTOR_PROPER",
  ``!n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ (p divides n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `?p. prime p /\ p divides n` by metis_tac[PRIME_FACTOR] >>
  `~(n < p)` by metis_tac[NOT_LT_DIVIDES] >>
  Cases_on `n = p` >-
  full_simp_tac std_ss[] >>
  `p < n` by decide_tac >>
  metis_tac[]);

(* Theorem: If p divides n, then there is a (p ** m) that maximally divides n. *)
(* Proof:
   Consider the set s = {k | p ** k divides n}
   Since p IN s, s <> {}           by MEMBER_NOT_EMPTY
   For k IN s, p ** k n divides ==> p ** k <= n    by DIVIDES_LE
   Since ?z. n <= p ** z           by EXP_ALWAYS_BIG_ENOUGH
   p ** k <= p ** z
        k <= z                     by EXP_BASE_LE_MONO
     or k < SUC z
   Hence s SUBSET count (SUC z)    by SUBSET_DEF
   and FINITE s                    by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s
   Then p ** m n divides           by MAX_SET_DEF
   Let q = n DIV (p ** m)
   i.e.  n = q * (p ** m)
   If p divides q, then q = t * p
   or n = t * p * (p ** m)
        = t * (p * p ** m)         by MULT_ASSOC
        = t * p ** SUC m           by EXP
   i.e. p ** SUC m  divides n, or SUC m IN s.
   Since m < SUC m                 by LESS_SUC
   This contradicts the maximal property of m.
*)
val FACTOR_OUT_POWER = store_thm(
  "FACTOR_OUT_POWER",
  ``!n p. 0 < n /\ 1 < p /\ p divides n ==> ?m. (p ** m) divides n /\ ~(p divides (n DIV (p ** m)))``,
  rpt strip_tac >>
  `p <= n` by rw[DIVIDES_LE] >>
  `1 < n` by decide_tac >>
  qabbrev_tac `s = {k | (p ** k) divides n }` >>
  qexists_tac `MAX_SET s` >>
  qabbrev_tac `m = MAX_SET s` >>
  `!k. k IN s <=> (p ** k) divides n` by rw[Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY, EXP_1] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!k. k IN s ==> k <= z` by metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, LESS_EQ_TRANS] >>
  `!k. k <= z ==> k < SUC z` by decide_tac >>
  `s SUBSET (count (SUC z))` by metis_tac[IN_COUNT, SUBSET_DEF, LESS_EQ_TRANS] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `m IN s /\ !y. y IN s ==> y <= m` by metis_tac[MAX_SET_DEF] >>
  `(p ** m) divides n` by metis_tac[] >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by decide_tac >>
  `0 < p ** m` by rw[EXP_POS] >>
  `n = (p ** m) * (n DIV (p ** m))` by rw[DIVIDES_FACTORS] >>
  `?q. n DIV (p ** m) = q * p` by rw[GSYM divides_def] >>
  `n = q * p ** SUC m` by metis_tac[MULT_COMM, MULT_ASSOC, EXP] >>
  `SUC m <= m` by metis_tac[divides_def] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* binomial_add: same as SUM_SQUARED *)

(* Theorem: (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b *)
(* Proof:
     (a + b) ** 2
   = (a + b) * (a + b)                   by EXP_2
   = a * (a + b) + b * (a + b)           by RIGHT_ADD_DISTRIB
   = (a * a + a * b) + (b * a + b * b)   by LEFT_ADD_DISTRIB
   = a * a + b * b + 2 * a * b           by arithmetic
   = a ** 2 + b ** 2 + 2 * a * b         by EXP_2
*)
Theorem binomial_add:
  !a b. (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b
Proof
  rpt strip_tac >>
  `(a + b) ** 2 = (a + b) * (a + b)` by simp[] >>
  `_ = a * a + b * b + 2 * a * b` by decide_tac >>
  simp[]
QED

(* Theorem: b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b) *)
(* Proof:
   If b = 0,
      RHS = a ** 2 + 0 ** 2 - 2 * a * 0
          = a ** 2 + 0 - 0
          = a ** 2
          = (a - 0) ** 2
          = LHS
   If b <> 0,
      Then b * b <= a * b                      by LE_MULT_RCANCEL, b <> 0
       and b * b <= 2 * a * b

      LHS = (a - b) ** 2
          = (a - b) * (a - b)                  by EXP_2
          = a * (a - b) - b * (a - b)          by RIGHT_SUB_DISTRIB
          = (a * a - a * b) - (b * a - b * b)  by LEFT_SUB_DISTRIB
          = a * a - (a * b + (a * b - b * b))  by SUB_PLUS
          = a * a - (a * b + a * b - b * b)    by LESS_EQ_ADD_SUB, b * b <= a * b
          = a * a - (2 * a * b - b * b)
          = a * a + b * b - 2 * a * b          by SUB_SUB, b * b <= 2 * a * b
          = a ** 2 + b ** 2 - 2 * a * b        by EXP_2
          = RHS
*)
Theorem binomial_sub:
  !a b. b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b)
Proof
  rpt strip_tac >>
  Cases_on `b = 0` >-
  simp[] >>
  `b * b <= a * b` by rw[] >>
  `b * b <= 2 * a * b` by decide_tac >>
  `(a - b) ** 2 = (a - b) * (a - b)` by simp[] >>
  `_ = a * a + b * b - 2 * a * b` by decide_tac >>
  rw[]
QED

(* Theorem: 2 * a * b <= a ** 2 + b ** 2 *)
(* Proof:
   If a = b,
      LHS = 2 * a * a
          = a * a + a * a
          = a ** 2 + a ** 2        by EXP_2
          = RHS
   If a < b, then 0 < b - a.
      Thus 0 < (b - a) * (b - a)   by MULT_EQ_0
        or 0 < (b - a) ** 2        by EXP_2
        so 0 < b ** 2 + a ** 2 - 2 * b * a   by binomial_sub, a <= b
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
   If b < a, then 0 < a - b.
      Thus 0 < (a - b) * (a - b)   by MULT_EQ_0
        or 0 < (a - b) ** 2        by EXP_2
        so 0 < a ** 2 + b ** 2 - 2 * a * b   by binomial_sub, b <= a
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
*)
Theorem binomial_means:
  !a b. 2 * a * b <= a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  Cases_on `a = b` >-
  simp[] >>
  Cases_on `a < b` >| [
    `b - a <> 0` by decide_tac >>
    `(b - a) * (b - a) <> 0` by metis_tac[MULT_EQ_0] >>
    `(b - a) * (b - a) = (b - a) ** 2` by simp[] >>
    `_ = b ** 2 + a ** 2 - 2 * b * a` by rw[binomial_sub] >>
    decide_tac,
    `a - b <> 0` by decide_tac >>
    `(a - b) * (a - b) <> 0` by metis_tac[MULT_EQ_0] >>
    `(a - b) * (a - b) = (a - b) ** 2` by simp[] >>
    `_ = a ** 2 + b ** 2 - 2 * a * b` by rw[binomial_sub] >>
    decide_tac
  ]
QED

(* Theorem: b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2 *)
(* Proof:
   Note (a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b     by binomial_sub
    and 2 * a * b <= a ** 2 + b ** 2                   by binomial_means
   Thus (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
*)
Theorem binomial_sub_sum:
  !a b. b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  imp_res_tac binomial_sub >>
  assume_tac (binomial_means |> SPEC_ALL) >>
  decide_tac
QED

(* Theorem: b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2) *)
(* Proof:
   Note: 2 * a * b <= a ** 2 + b ** 2          by binomial_means, as [1]
     (a - b) ** 2 + 4 * a * b
   = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b   by binomial_sub, b <= a
   = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b   by SUB_ADD, [1]
   = a ** 2 + b ** 2 + 2 * a * b
   = (a + b) ** 2                              by binomial_add
*)
Theorem binomial_sub_add:
  !a b. b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2)
Proof
  rpt strip_tac >>
  `2 * a * b <= a ** 2 + b ** 2` by rw[binomial_means] >>
  `(a - b) ** 2 + 4 * a * b = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b` by rw[binomial_sub] >>
  `_ = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b` by decide_tac >>
  `_ = a ** 2 + b ** 2 + 2 * a * b` by decide_tac >>
  `_ = (a + b) ** 2` by rw[binomial_add] >>
  decide_tac
QED

(* Theorem: a ** 2 - b ** 2 = (a - b) * (a + b) *)
(* Proof:
     a ** 2 - b ** 2
   = a * a - b * b                       by EXP_2
   = a * a + a * b - a * b - b * b       by ADD_SUB
   = a * a + a * b - (b * a + b * b)     by SUB_PLUS
   = a * (a + b) - b * (a + b)           by LEFT_ADD_DISTRIB
   = (a - b) * (a + b)                   by RIGHT_SUB_DISTRIB
*)
Theorem difference_of_squares:
  !a b. a ** 2 - b ** 2 = (a - b) * (a + b)
Proof
  rpt strip_tac >>
  `a ** 2 - b ** 2 = a * a - b * b` by simp[] >>
  `_ = a * a + a * b - a * b - b * b` by decide_tac >>
  decide_tac
QED

(* Theorem: a * a - b * b = (a - b) * (a + b) *)
(* Proof:
     a * a - b * b
   = a ** 2 - b ** 2       by EXP_2
   = (a + b) * (a - b)     by difference_of_squares
*)
Theorem difference_of_squares_alt:
  !a b. a * a - b * b = (a - b) * (a + b)
Proof
  rw[difference_of_squares]
QED

(* binomial_2: same as binomial_add, or SUM_SQUARED *)

(* Theorem: (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n *)
(* Proof:
     (m + n) ** 2
   = (m + n) * (m + n)                 by EXP_2
   = m * m + n * m + m * n + n * n     by LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB
   = m ** 2 + n ** 2 + 2 * m * n       by EXP_2
*)
val binomial_2 = store_thm(
  "binomial_2",
  ``!m n. (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n``,
  rpt strip_tac >>
  `(m + n) ** 2 = (m + n) * (m + n)` by rw[] >>
  `_ = m * m + n * m + m * n + n * n` by decide_tac >>
  `_ = m ** 2 + n ** 2 + 2 * m * n` by rw[] >>
  decide_tac);

(* Obtain a corollary *)
val SUC_SQ = save_thm("SUC_SQ",
    binomial_2 |> SPEC ``1`` |> SIMP_RULE (srw_ss()) [GSYM SUC_ONE_ADD]);
(* val SUC_SQ = |- !n. SUC n ** 2 = SUC (n ** 2) + TWICE n: thm *)

(* Theorem: m <= n ==> SQ m <= SQ n *)
(* Proof:
   Since m * m <= n * n    by LE_MONO_MULT2
      so  SQ m <= SQ n     by notation
*)
val SQ_LE = store_thm(
  "SQ_LE",
  ``!m n. m <= n ==> SQ m <= SQ n``,
  rw[]);

(* Theorem: EVEN n /\ prime n <=> n = 2 *)
(* Proof:
   If part: EVEN n /\ prime n ==> n = 2
      EVEN n ==> n MOD 2 = 0       by EVEN_MOD2
             ==> 2 divides n       by DIVIDES_MOD_0, 0 < 2
             ==> n = 2             by prime_def, 2 <> 1
   Only-if part: n = 2 ==> EVEN n /\ prime n
      Note EVEN 2                  by EVEN_2
       and prime 2                 by prime_2
*)
(* Proof:
   EVEN n ==> n MOD 2 = 0    by EVEN_MOD2
          ==> 2 divides n    by DIVIDES_MOD_0, 0 < 2
          ==> n = 2          by prime_def, 2 <> 1
*)
Theorem EVEN_PRIME:
  !n. EVEN n /\ prime n <=> n = 2
Proof
  rw[EQ_IMP_THM] >>
  `0 < 2 /\ 2 <> 1` by decide_tac >>
  `2 divides n` by rw[DIVIDES_MOD_0, GSYM EVEN_MOD2] >>
  metis_tac[prime_def]
QED

(* Theorem: prime n /\ n <> 2 ==> ODD n *)
(* Proof:
   By contradiction, suppose ~ODD n.
   Then EVEN n                        by EVEN_ODD
    but EVEN n /\ prime n ==> n = 2   by EVEN_PRIME
   This contradicts n <> 2.
*)
val ODD_PRIME = store_thm(
  "ODD_PRIME",
  ``!n. prime n /\ n <> 2 ==> ODD n``,
  metis_tac[EVEN_PRIME, EVEN_ODD]);

(* Theorem: prime p ==> 2 <= p *)
(* Proof: by ONE_LT_PRIME *)
val TWO_LE_PRIME = store_thm(
  "TWO_LE_PRIME",
  ``!p. prime p ==> 2 <= p``,
  metis_tac[ONE_LT_PRIME, DECIDE``1 < n <=> 2 <= n``]);

(* Theorem: ~prime 4 *)
(* Proof:
   Note 4 = 2 * 2      by arithmetic
     so 2 divides 4    by divides_def
   thus ~prime 4       by primes_def
*)
Theorem NOT_PRIME_4:
  ~prime 4
Proof
  rpt strip_tac >>
  `4 = 2 * 2` by decide_tac >>
  `4 <> 2 /\ 4 <> 1 /\ 2 <> 1` by decide_tac >>
  metis_tac[prime_def, divides_def]
QED

(* Theorem: prime n /\ prime m ==> (n divides m <=> (n = m)) *)
(* Proof:
   If part: prime n /\ prime m /\ n divides m ==> (n = m)
      Note prime n
       ==> n <> 1           by NOT_PRIME_1
      With n divides m      by given
       and prime m          by given
      Thus n = m            by prime_def
   Only-if part; prime n /\ prime m /\ (n = m) ==> n divides m
      True as m divides m   by DIVIDES_REFL
*)
val prime_divides_prime = store_thm(
  "prime_divides_prime",
  ``!n m. prime n /\ prime m ==> (n divides m <=> (n = m))``,
  rw[EQ_IMP_THM] >>
  `n <> 1` by metis_tac[NOT_PRIME_1] >>
  metis_tac[prime_def]);
(* This is: dividesTheory.prime_divides_only_self;
|- !m n. prime m /\ prime n /\ m divides n ==> (m = n)
*)

(* Theorem: 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1) *)
(* Proof:
   By complete induction on m.
   If m = 1, trivially true               by ONE_MOD
   If m <> 1,
      Then ?p. prime p /\ p divides m     by PRIME_FACTOR, m <> 1
       and ?q. m = q * p                  by divides_def
       and q divides m                    by divides_def, MULT_COMM
      In order to apply induction hypothesis,
      Show: q < m
            Note q <= m                   by DIVIDES_LE, 0 < m
             But p <> 1                   by NOT_PRIME_1
            Thus q <> m                   by MULT_RIGHT_1, EQ_MULT_LCANCEL, m <> 0
             ==> q < m
      Show: 0 < q
            Since m = q * p  and m <> 0   by above
            Thus q <> 0, or 0 < q         by MULT
      Show: !p. prime p /\ p divides q ==> (p MOD n = 1)
            If p divides q, and q divides m,
            Then p divides m              by DIVIDES_TRANS
             ==> p MOD n = 1              by implication

      Hence q MOD n = 1                   by induction hypothesis
        and p MOD n = 1                   by implication
        Now 0 < n                         by 1 < n
            m MDO n
          = (q * p) MOD n                 by m = q * p
          = (q MOD n * p MOD n) MOD n     by MOD_TIMES2, 0 < n
          = (1 * 1) MOD n                 by above
          = 1                             by MULT_RIGHT_1, ONE_MOD
*)
val ALL_PRIME_FACTORS_MOD_EQ_1 = store_thm(
  "ALL_PRIME_FACTORS_MOD_EQ_1",
  ``!m n. 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1)``,
  completeInduct_on `m` >>
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[] >>
  `?p. prime p /\ p divides m` by rw[PRIME_FACTOR] >>
  `?q. m = q * p` by rw[GSYM divides_def] >>
  `q divides m` by metis_tac[divides_def, MULT_COMM] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  `m <> 0` by decide_tac >>
  `q <> m` by metis_tac[MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `q <= m` by metis_tac[DIVIDES_LE] >>
  `q < m` by decide_tac >>
  `q <> 0` by metis_tac[MULT] >>
  `0 < q` by decide_tac >>
  `!p. prime p /\ p divides q ==> (p MOD n = 1)` by metis_tac[DIVIDES_TRANS] >>
  `q MOD n = 1` by rw[] >>
  `p MOD n = 1` by rw[] >>
  `0 < n` by decide_tac >>
  metis_tac[MOD_TIMES2, MULT_RIGHT_1, ONE_MOD]);

(* Theorem: prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b *)
(* Proof:
   If part: p divides b ** n ==> p divides b
      By induction on n.
      Base: 0 < 0 ==> p divides b ** 0 ==> p divides b
         True by 0 < 0 = F.
      Step: 0 < n ==> p divides b ** n ==> p divides b ==>
            0 < SUC n ==> p divides b ** SUC n ==> p divides b
         If n = 0,
              b ** SUC 0
            = b ** 1                  by ONE
            = b                       by EXP_1
            so p divides b.
         If n <> 0, 0 < n.
              b ** SUC n
            = b * b ** n              by EXP
            Thus p divides b,
              or p divides (b ** n)   by P_EUCLIDES
            For the latter case,
                 p divides b          by induction hypothesis, 0 < n

   Only-if part: p divides b ==> p divides b ** n
      Since n <> 0, ?m. n = SUC m     by num_CASES
        and b ** n
          = b ** SUC m
          = b * b ** m                by EXP
       Thus p divides b ** n          by DIVIDES_MULTIPLE, MULT_COMM
*)
val prime_divides_power = store_thm(
  "prime_divides_power",
  ``!p n. prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b``,
  rw[EQ_IMP_THM] >| [
    Induct_on `n` >-
    rw[] >>
    rpt strip_tac >>
    Cases_on `n = 0` >-
    metis_tac[ONE, EXP_1] >>
    `0 < n` by decide_tac >>
    `b ** SUC n = b * b ** n` by rw[EXP] >>
    metis_tac[P_EUCLIDES],
    `n <> 0` by decide_tac >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    `b ** SUC m = b * b ** m` by rw[EXP] >>
    metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
  ]);

(* Theorem: prime p ==> !n. 0 < n ==> p divides p ** n *)
(* Proof:
   Since p divides p        by DIVIDES_REFL
      so p divides p ** n   by prime_divides_power, 0 < n
*)
val prime_divides_self_power = store_thm(
  "prime_divides_self_power",
  ``!p. prime p ==> !n. 0 < n ==> p divides p ** n``,
  rw[prime_divides_power, DIVIDES_REFL]);

(* Theorem: prime p ==> !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m) *)
(* Proof:
   Note 1 < p                    by ONE_LT_PRIME
     so p <> 0, 0 < p, p <> 1    by arithmetic
   also m <> 0                   by 0 < m
   Thus p ** m <> 0              by EXP_EQ_0, p <> 0
    and p ** m <> 1              by EXP_EQ_1, p <> 1, m <> 0
    ==> n <> 0, 0 < n            by EXP, b ** n = p ** m <> 1
   also b <> 0, 0 < b            by EXP_EQ_0, b ** n = p ** m <> 0, 0 < n

   Step 1: show p divides b.
   Note p divides (p ** m)       by prime_divides_self_power, 0 < m
     so p divides (b ** n)       by given, b ** n = p ** m
     or p divides b              by prime_divides_power, 0 < b

   Step 2: express b = q * p ** u  where ~(p divides q).
   Note 1 < p /\ 0 < b /\ p divides b
    ==> ?u. p ** u divides b /\ ~(p divides b DIV p ** u)  by FACTOR_OUT_POWER
    Let q = b DIV p ** u, v = u * n.
   Since p ** u <> 0             by EXP_EQ_0, p <> 0
      so b = q * p ** u          by DIVIDES_EQN, 0 < p ** u
         p ** m
       = (q * p ** u) ** n       by b = q * p ** u
       = q ** n * (p ** u) ** n  by EXP_BASE_MULT
       = q ** n * p ** (u * n)   by EXP_EXP_MULT
       = q ** n * p ** v         by v = u * n

   Step 3: split cases
   If v = m,
      Then q ** n * p ** m = 1 * p ** m     by above
        or          q ** n = 1              by EQ_MULT_RCANCEL, p ** m <> 0
      giving             q = 1              by EXP_EQ_1, 0 < n
      Thus b = p ** u                       by b = q * p ** u
      Take k = u, the result follows.

   If v < m,
      Let d = m - v.
      Then 0 < d /\ (m = d + v)             by arithmetic
       and p ** m = p ** d * p ** v         by EXP_ADD
      Note p ** v <> 0                      by EXP_EQ_0, p <> 0
           q ** n * p ** v = p ** d * p ** v
       ==>          q ** n = p ** d         by EQ_MULT_RCANCEL, p ** v <> 0
      Now p divides p ** d                  by prime_divides_self_power, 0 < d
       so p divides q ** n                  by above, q ** n = p ** d
      ==> p divides q                       by prime_divides_power, 0 < n
      This contradicts ~(p divides q)

   If m < v,
      Let d = v - m.
      Then 0 < d /\ (v = d + m)             by arithmetic
       and q ** n * p ** v
         = q ** n * (p ** d * p ** m)       by EXP_ADD
         = q ** n * p ** d * p ** m         by MULT_ASSOC
         = 1 * p ** m                       by arithmetic, b ** n = p ** m
      Hence q ** n * p ** d = 1             by EQ_MULT_RCANCEL, p ** m <> 0
        ==> (q ** n = 1) /\ (p ** d = 1)    by MULT_EQ_1
        But p ** d <> 1                     by EXP_EQ_1, 0 < d
       This contradicts p ** d = 1.
*)
Theorem power_eq_prime_power:
  !p. prime p ==>
      !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m)
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `m <> 0 /\ 0 < p /\ p <> 0 /\ p <> 1` by decide_tac >>
  `p ** m <> 0` by rw[EXP_EQ_0] >>
  `p ** m <> 1` by rw[EXP_EQ_1] >>
  `n <> 0` by metis_tac[EXP] >>
  `0 < n /\ 0 < p ** m` by decide_tac >>
  `b <> 0` by metis_tac[EXP_EQ_0] >>
  `0 < b` by decide_tac >>
  `p divides (p ** m)` by rw[prime_divides_self_power] >>
  `p divides b` by metis_tac[prime_divides_power] >>
  `?u. p ** u divides b /\ ~(p divides b DIV p ** u)` by metis_tac[FACTOR_OUT_POWER] >>
  qabbrev_tac `q = b DIV p ** u` >>
  `p ** u <> 0` by rw[EXP_EQ_0] >>
  `0 < p ** u` by decide_tac >>
  `b = q * p ** u` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `q ** n * p ** (u * n) = p ** m` by metis_tac[EXP_BASE_MULT, EXP_EXP_MULT] >>
  qabbrev_tac `v = u * n` >>
  Cases_on `v = m` >| [
    `p ** m = 1 * p ** m` by simp[] >>
    `q ** n = 1` by metis_tac[EQ_MULT_RCANCEL] >>
    `q = 1` by metis_tac[EXP_EQ_1] >>
    `b = p ** u` by simp[] >>
    metis_tac[],
    Cases_on `v < m` >| [
      `?d. d = m - v` by rw[] >>
      `0 < d /\ (m = d + v)` by rw[] >>
      `p ** m = p ** d * p ** v` by rw[EXP_ADD] >>
      `p ** v <> 0` by metis_tac[EXP_EQ_0] >>
      `q ** n = p ** d` by metis_tac[EQ_MULT_RCANCEL] >>
      `p divides p ** d` by metis_tac[prime_divides_self_power] >>
      metis_tac[prime_divides_power],
      `m < v` by decide_tac >>
      `?d. d = v - m` by rw[] >>
      `0 < d /\ (v = d + m)` by rw[] >>
      `d <> 0` by decide_tac >>
      `q ** n * p ** d * p ** m = p ** m` by metis_tac[EXP_ADD, MULT_ASSOC] >>
      `_ = 1 * p ** m` by rw[] >>
      `q ** n * p ** d = 1` by metis_tac[EQ_MULT_RCANCEL] >>
      `(q ** n = 1) /\ (p ** d = 1)` by metis_tac[MULT_EQ_1] >>
      metis_tac[EXP_EQ_1]
    ]
  ]
QED

(* Theorem: 1 < n ==> !m. (n ** m = n) <=> (m = 1) *)
(* Proof:
   If part: n ** m = n ==> m = 1
      Note n = n ** 1           by EXP_1
        so n ** m = n ** 1      by given
        or      m = 1           by EXP_BASE_INJECTIVE, 1 < n
   Only-if part: m = 1 ==> n ** m = n
      This is true              by EXP_1
*)
val POWER_EQ_SELF = store_thm(
  "POWER_EQ_SELF",
  ``!n. 1 < n ==> !m. (n ** m = n) <=> (m = 1)``,
  metis_tac[EXP_BASE_INJECTIVE, EXP_1]);

(* Theorem: k < HALF n <=> k + 1 < n - k *)
(* Proof:
   If part: k < HALF n ==> k + 1 < n - k
      Claim: 1 < n - 2 * k.
      Proof: If EVEN n,
                Claim: n - 2 * k <> 0
                Proof: By contradiction, assume n - 2 * k = 0.
                       Then 2 * k = n = 2 * HALF n      by EVEN_HALF
                         or     k = HALF n              by MULT_LEFT_CANCEL, 2 <> 0
                         but this contradicts k < HALF n.
                Claim: n - 2 * k <> 1
                Proof: By contradiction, assume n - 2 * k = 1.
                       Then n = 2 * k + 1               by SUB_EQ_ADD, 0 < 1
                         or ODD n                       by ODD_EXISTS, ADD1
                        but this contradicts EVEN n     by EVEN_ODD
                Thus n - 2 * k <> 1, or 1 < n - 2 * k   by above claims.
      Since 1 < n - 2 * k         by above
         so 2 * k + 1 < n         by arithmetic
         or k + k + 1 < n         by TIMES2
         or     k + 1 < n - k     by arithmetic

   Only-if part: k + 1 < n - k ==> k < HALF n
      Since     k + 1 < n - k
         so 2 * k + 1 < n                by arithmetic
        But n = 2 * HALF n + (n MOD 2)   by DIVISION, MULT_COMM, 0 < 2
        and n MOD 2 < 2                  by MOD_LESS, 0 < 2
         so n <= 2 * HALF n + 1          by arithmetic
       Thus 2 * k + 1 < 2 * HALF n + 1   by LESS_LESS_EQ_TRANS
         or         k < HALF             by LT_MULT_LCANCEL
*)
val LESS_HALF_IFF = store_thm(
  "LESS_HALF_IFF",
  ``!n k. k < HALF n <=> k + 1 < n - k``,
  rw[EQ_IMP_THM] >| [
    `1 < n - 2 * k` by
  (Cases_on `EVEN n` >| [
      `n - 2 * k <> 0` by
  (spose_not_then strip_assume_tac >>
      `2 * HALF n = n` by metis_tac[EVEN_HALF] >>
      decide_tac) >>
      `n - 2 * k <> 1` by
    (spose_not_then strip_assume_tac >>
      `n = 2 * k + 1` by decide_tac >>
      `ODD n` by metis_tac[ODD_EXISTS, ADD1] >>
      metis_tac[EVEN_ODD]) >>
      decide_tac,
      `n MOD 2 = 1` by metis_tac[EVEN_ODD, ODD_MOD2] >>
      `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
      decide_tac
    ]) >>
    decide_tac,
    `2 * k + 1 < n` by decide_tac >>
    `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
    `n MOD 2 < 2` by rw[] >>
    decide_tac
  ]);

(* Theorem: HALF n < k ==> n - k <= HALF n *)
(* Proof:
   If k < n,
      If EVEN n,
         Note HALF n + HALF n < k + HALF n   by HALF n < k
           or      2 * HALF n < k + HALF n   by TIMES2
           or               n < k + HALF n   by EVEN_HALF, EVEN n
           or           n - k < HALF n       by LESS_EQ_SUB_LESS, k <= n
         Hence true.
      If ~EVEN n, then ODD n                 by EVEN_ODD
         Note HALF n + HALF n + 1 < k + HALF n + 1   by HALF n < k
           or      2 * HALF n + 1 < k + HALF n + 1   by TIMES2
           or         n < k + HALF n + 1     by ODD_HALF
           or         n <= k + HALF n        by arithmetic
           so     n - k <= HALF n            by SUB_LESS_EQ_ADD, k <= n
   If ~(k < n), then n <= k.
      Thus n - k = 0, hence n - k <= HALF n  by arithmetic
*)
val MORE_HALF_IMP = store_thm(
  "MORE_HALF_IMP",
  ``!n k. HALF n < k ==> n - k <= HALF n``,
  rpt strip_tac >>
  Cases_on `k < n` >| [
    Cases_on `EVEN n` >| [
      `n = 2 * HALF n` by rw[EVEN_HALF] >>
      `n < k + HALF n` by decide_tac >>
      `n - k < HALF n` by decide_tac >>
      decide_tac,
      `ODD n` by rw[ODD_EVEN] >>
      `n = 2 * HALF n + 1` by rw[ODD_HALF] >>
      decide_tac
    ],
    decide_tac
  ]);

(* Theorem: (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m *)
(* Proof:
   By induction on the difference (m - k):
   Base: 0 = m - k /\ k < m ==> f k < f m
      Note m = k and k < m contradicts, hence true.
   Step: !m k. (v = m - k) ==> k < m ==> f k < f m ==>
         SUC v = m - k /\ k < m ==> f k < f m
      Note v + 1 = m - k        by ADD1
        so v = m - (k + 1)      by arithmetic
      If v = 0,
         Then m = k + 1
           so f k < f (k + 1)   by implication
           or f k < f m         by m = k + 1
      If v <> 0, then 0 < v.
         Then 0 < m - (k + 1)   by v = m - (k + 1)
           or k + 1 < m         by arithmetic
          Now f k < f (k + 1)   by implication, k < m
          and f (k + 1) < f m   by induction hypothesis, put k = k + 1
           so f k < f m         by LESS_TRANS
*)
val MONOTONE_MAX = store_thm(
  "MONOTONE_MAX",
  ``!f m. (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m``,
  rpt strip_tac >>
  Induct_on `m - k` >| [
    rpt strip_tac >>
    decide_tac,
    rpt strip_tac >>
    `v + 1 = m - k` by rw[] >>
    `v = m - (k + 1)` by decide_tac >>
    Cases_on `v = 0` >| [
      `m = k + 1` by decide_tac >>
      rw[],
      `k + 1 < m` by decide_tac >>
      `f k < f (k + 1)` by rw[] >>
      `f (k + 1) < f m` by rw[] >>
      decide_tac
    ]
  ]);

(* Theorem: (multiple gap)
   If n divides m, n cannot divide any x: m - n < x < m, or m < x < m + n
   n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m) *)
(* Proof:
   All these x, when divided by n, have non-zero remainders.
   Since n divides m and n divides x
     ==> ?h. m = h * n, and ?k. x = k * n  by divides_def
   Hence m - n < x
     ==> (h-1) * n < k * n                 by RIGHT_SUB_DISTRIB, MULT_LEFT_1
     and x < m + n
     ==>     k * n < (h+1) * n             by RIGHT_ADD_DISTRIB, MULT_LEFT_1
      so 0 < n, and h-1 < k, and k < h+1   by LT_MULT_RCANCEL
     that is, h <= k, and k <= h
   Therefore  h = k, or m = h * n = k * n = x.
*)
val MULTIPLE_INTERVAL = store_thm(
  "MULTIPLE_INTERVAL",
  ``!n m. n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m)``,
  rpt strip_tac >>
  `(?h. m = h*n) /\ (?k. x = k * n)` by metis_tac[divides_def] >>
  `(h-1) * n < k * n` by metis_tac[RIGHT_SUB_DISTRIB, MULT_LEFT_1] >>
  `k * n < (h+1) * n` by metis_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >>
  `0 < n /\ h-1 < k /\ k < h+1` by metis_tac[LT_MULT_RCANCEL] >>
  `h = k` by decide_tac >>
  metis_tac[]);

(* Theorem: 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m) *)
(* Proof:
   Let x = n DIV m, y = (SUC n) DIV m.
   Let a = SUC (n MOD m), b = (SUC n) MOD m.
   Note SUC n = y * m + b                 by DIVISION, 0 < m, for (SUC n), [1]
    and     n = x * m + (n MOD m)         by DIVISION, 0 < m, for n
     so SUC n = SUC (x * m + (n MOD m))   by above
              = x * m + a                 by ADD_SUC, [2]
   Equating, x * m + a = y * m + b        by [1], [2]
   Now n < SUC n                          by SUC_POS
    so n DIV m <= (SUC n) DIV m           by DIV_LE_MONOTONE, n <= SUC n
    or       x <= y
    so   x * m <= y * m                   by LE_MULT_RCANCEL, m <> 0

   Thus a = b + (y * m - x * m)           by arithmetic
          = b + (y - x) * m               by RIGHT_SUB_DISTRIB
*)
val MOD_SUC_EQN = store_thm(
  "MOD_SUC_EQN",
  ``!m n. 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m)``,
  rpt strip_tac >>
  qabbrev_tac `x = n DIV m` >>
  qabbrev_tac `y = (SUC n) DIV m` >>
  qabbrev_tac `a = SUC (n MOD m)` >>
  qabbrev_tac `b = (SUC n) MOD m` >>
  `SUC n = y * m + b` by rw[DIVISION, Abbr`y`, Abbr`b`] >>
  `n = x * m + (n MOD m)` by rw[DIVISION, Abbr`x`] >>
  `SUC n = x * m + a` by rw[Abbr`a`] >>
  `n < SUC n` by rw[] >>
  `x <= y` by rw[DIV_LE_MONOTONE, Abbr`x`, Abbr`y`] >>
  `x * m <= y * m` by rw[] >>
  `a = b + (y * m - x * m)` by decide_tac >>
  `_ = b + (y - x) * m` by rw[] >>
  rw[]);

(* Note: Compare this result with these in arithmeticTheory:
MOD_SUC      |- 0 < y /\ SUC x <> SUC (x DIV y) * y ==> (SUC x MOD y = SUC (x MOD y))
MOD_SUC_IFF  |- 0 < y ==> ((SUC x MOD y = SUC (x MOD y)) <=> SUC x <> SUC (x DIV y) * y)
*)

(* Theorem: 1 < n ==> 1 < HALF (n ** 2) *)
(* Proof:
       1 < n
   ==> 2 <= n                            by arithmetic
   ==> 2 ** 2 <= n ** 2                  by EXP_EXP_LE_MONO
   ==> (2 ** 2) DIV 2 <= (n ** 2) DIV 2  by DIV_LE_MONOTONE
   ==> 2 <= (n ** 2) DIV 2               by arithmetic
   ==> 1 < (n ** 2) DIV 2                by arithmetic
*)
val ONE_LT_HALF_SQ = store_thm(
  "ONE_LT_HALF_SQ",
  ``!n. 1 < n ==> 1 < HALF (n ** 2)``,
  rpt strip_tac >>
  `2 <= n` by decide_tac >>
  `2 ** 2 <= n ** 2` by rw[] >>
  `(2 ** 2) DIV 2 <= (n ** 2) DIV 2` by rw[DIV_LE_MONOTONE] >>
  `(2 ** 2) DIV 2 = 2` by EVAL_TAC >>
  decide_tac);

(* Theorem: 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1)) *)
(* Proof
   By induction on n.
   Base: 0 < 0 ==> 2 ** 0 DIV 2 = 2 ** (0 - 1)
      This is trivially true as 0 < 0 = F.
   Step:  0 < n ==> HALF (2 ** n) = 2 ** (n - 1)
      ==> 0 < SUC n ==> HALF (2 ** SUC n) = 2 ** (SUC n - 1)
        HALF (2 ** SUC n)
      = HALF (2 * 2 ** n)          by EXP
      = 2 ** n                     by MULT_TO_DIV
      = 2 ** (SUC n - 1)           by SUC_SUB1
*)
Theorem EXP_2_HALF:
  !n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))
Proof
  Induct >> simp[EXP, MULT_TO_DIV]
QED

(*
There is EVEN_MULT    |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
There is EVEN_DOUBLE  |- !n. EVEN (TWICE n)
*)

(* Theorem: EVEN n ==> (HALF (m * n) = m * HALF n) *)
(* Proof:
   Note n = TWICE (HALF n)  by EVEN_HALF
   Let k = HALF n.
     HALF (m * n)
   = HALF (m * (2 * k))  by above
   = HALF (2 * (m * k))  by MULT_COMM_ASSOC
   = m * k               by HALF_TWICE
   = m * HALF n          by notation
*)
val HALF_MULT_EVEN = store_thm(
  "HALF_MULT_EVEN",
  ``!m n. EVEN n ==> (HALF (m * n) = m * HALF n)``,
  metis_tac[EVEN_HALF, MULT_COMM_ASSOC, HALF_TWICE]);

(* Theorem: 0 < k /\ k * m < n ==> m < n *)
(* Proof:
   Note ?h. k = SUC h     by num_CASES, k <> 0
        k * m
      = SUC h * m         by above
      = (h + 1) * m       by ADD1
      = h * m + 1 * m     by LEFT_ADD_DISTRIB
      = h * m + m         by MULT_LEFT_1
   Since 0 <= h * m,
      so k * m < n ==> m < n.
*)
val MULT_LT_IMP_LT = store_thm(
  "MULT_LT_IMP_LT",
  ``!m n k. 0 < k /\ k * m < n ==> m < n``,
  rpt strip_tac >>
  `k <> 0` by decide_tac >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `k * m = h * m + m` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < k /\ k * m <= n ==> m <= n *)
(* Proof:
   Note     1 <= k                 by 0 < k
     so 1 * m <= k * m             by LE_MULT_RCANCEL
     or     m <= k * m <= n        by inequalities
*)
Theorem MULT_LE_IMP_LE:
  !m n k. 0 < k /\ k * m <= n ==> m <= n
Proof
  rpt strip_tac >>
  `1 <= k` by decide_tac >>
  `1 * m <= k * m` by simp[] >>
  decide_tac
QED

(* Theorem: n * HALF ((SQ n) ** 2) <= HALF (n ** 5) *)
(* Proof:
      n * HALF ((SQ n) ** 2)
   <= HALF (n * (SQ n) ** 2)     by HALF_MULT
    = HALF (n * (n ** 2) ** 2)   by EXP_2
    = HALF (n * n ** 4)          by EXP_EXP_MULT
    = HALF (n ** 5)              by EXP
*)
val HALF_EXP_5 = store_thm(
  "HALF_EXP_5",
  ``!n. n * HALF ((SQ n) ** 2) <= HALF (n ** 5)``,
  rpt strip_tac >>
  `n * ((SQ n) ** 2) = n * n ** 4` by rw[EXP_2, EXP_EXP_MULT] >>
  `_ = n ** 5` by rw[EXP] >>
  metis_tac[HALF_MULT]);

(* Theorem: n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m) *)
(* Proof:
   Let k = n - 1, then n = SUC k.
   If part: n <= TWICE m /\ n <> 0 ==> HALF k < m
      Note HALF (SUC k) <= m                by DIV_LE_MONOTONE, HALF_TWICE
      If EVEN n,
         Then ODD k                         by EVEN_ODD_SUC
          ==> HALF (SUC k) = SUC (HALF k)   by ODD_SUC_HALF
         Thus SUC (HALF k) <= m             by above
           or        HALF k < m             by LESS_EQ
      If ~EVEN n, then ODD n                by EVEN_ODD
         Thus EVEN k                        by EVEN_ODD_SUC
          ==> HALF (SUC k) = HALF k         by EVEN_SUC_HALF
          But k <> TWICE m                  by k = n - 1, n <= TWICE m
          ==> HALF k <> m                   by EVEN_HALF
         Thus  HALF k < m                   by HALF k <= m, HALF k <> m

   Only-if part: n <> 0 ==> HALF k < m ==> n <= TWICE m
      If n = 0, trivially true.
      If n <> 0, has HALF k < m.
         If EVEN n,
            Then ODD k                        by EVEN_ODD_SUC
             ==> HALF (SUC k) = SUC (HALF k)  by ODD_SUC_HALF
             But SUC (HALF k) <= m            by HALF k < m
            Thus HALF n <= m                  by n = SUC k
             ==> TWICE (HALF n) <= TWICE m    by LE_MULT_LCANCEL
              or              n <= TWICE m    by EVEN_HALF
         If ~EVEN n, then ODD n               by EVEN_ODD
            Then EVEN k                       by EVEN_ODD_SUC
             ==> TWICE (HALF k) < TWICE m     by LT_MULT_LCANCEL
              or              k < TWICE m     by EVEN_HALF
              or             n <= TWICE m     by n = k + 1
*)
val LE_TWICE_ALT = store_thm(
  "LE_TWICE_ALT",
  ``!m n. n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m)``,
  rw[EQ_IMP_THM] >| [
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    `HALF (SUC k) <= m` by metis_tac[DIV_LE_MONOTONE, HALF_TWICE, DECIDE``0 < 2``] >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      decide_tac,
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = HALF k` by rw[EVEN_SUC_HALF] >>
      `k <> TWICE m` by rw[Abbr`k`] >>
      `HALF k <> m` by metis_tac[EVEN_HALF] >>
      decide_tac
    ],
    Cases_on `n = 0` >-
    rw[] >>
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      `HALF n <= m` by rw[] >>
      metis_tac[LE_MULT_LCANCEL, EVEN_HALF, DECIDE``2 <> 0``],
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `k < TWICE m` by metis_tac[LT_MULT_LCANCEL, EVEN_HALF, DECIDE``0 < 2``] >>
      rw[Abbr`k`]
    ]
  ]);

(* Theorem: (HALF n) DIV 2 ** m = n DIV (2 ** SUC m) *)
(* Proof:
     (HALF n) DIV 2 ** m
   = (n DIV 2) DIV (2 ** m)    by notation
   = n DIV (2 * 2 ** m)        by DIV_DIV_DIV_MULT, 0 < 2, 0 < 2 ** m
   = n DIV (2 ** (SUC m))      by EXP
*)
val HALF_DIV_TWO_POWER = store_thm(
  "HALF_DIV_TWO_POWER",
  ``!m n. (HALF n) DIV 2 ** m = n DIV (2 ** SUC m)``,
  rw[DIV_DIV_DIV_MULT, EXP]);

(* Theorem: 1 + 2 + 3 + 4 = 10 *)
(* Proof: by calculation. *)
Theorem fit_for_10:
  1 + 2 + 3 + 4 = 10
Proof
  decide_tac
QED

(* Theorem: 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100 *)
(* Proof: by calculation. *)
Theorem fit_for_100:
  1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100
Proof
  decide_tac
QED

(* ------------------------------------------------------------------------- *)

(* Theorem: If prime p divides n, ?m. 0 < m /\ (p ** m) divides n /\ n DIV (p ** m) has no p *)
(* Proof:
   Let s = {j | (p ** j) divides n }
   Since p ** 1 = p, 1 IN s, so s <> {}.
       (p ** j) divides n
   ==> p ** j <= n                  by DIVIDES_LE
   ==> p ** j <= p ** z             by EXP_ALWAYS_BIG_ENOUGH
   ==>      j <= z                  by EXP_BASE_LE_MONO
   ==> s SUBSET count (SUC z),
   so FINITE s                      by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s,
   m IN s, so (p ** m) divides n    by MAX_SET_DEF
   1 <= m, or 0 < m.
   ?q. n = q * (p ** m)             by divides_def
   To prove: !k. gcd (p ** k) (n DIV (p ** m)) = 1
   By contradiction, suppose there is a k such that
   gcd (p ** k) (n DIV (p ** m)) <> 1
   So there is a prime pp that divides this gcd, by PRIME_FACTOR
   but pp | p ** k, a pure prime, so pp = p      by DIVIDES_EXP_BASE, prime_divides_only_self
       pp | n DIV (p ** m)
   or  pp * p ** m | n
       p * SUC m | n, making m not MAX_SET s.
*)
val FACTOR_OUT_PRIME = store_thm(
  "FACTOR_OUT_PRIME",
  ``!n p. 0 < n /\ prime p /\ p divides n ==> ?m. 0 < m /\ (p ** m) divides n /\ !k. gcd (p ** k) (n DIV (p ** m)) = 1``,
  rpt strip_tac >>
  qabbrev_tac `s = {j | (p ** j) divides n }` >>
  `!j. j IN s <=> (p ** j) divides n` by rw[Abbr`s`] >>
  `p ** 1 = p` by rw[] >>
  `1 IN s` by metis_tac[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!j. j IN s ==> p ** j <= n` by metis_tac[DIVIDES_LE] >>
  `!j. j IN s ==> p ** j <= p ** z` by metis_tac[LESS_EQ_TRANS] >>
  `!j. j IN s ==> j <= z` by metis_tac[EXP_BASE_LE_MONO] >>
  `!j. j <= z <=> j < SUC z` by decide_tac >>
  `!j. j < SUC z <=> j IN count (SUC z)` by rw[] >>
  `s SUBSET count (SUC z)` by metis_tac[SUBSET_DEF] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  qabbrev_tac `m = MAX_SET s` >>
  `m IN s /\ !y. y IN s ==> y <= m`by rw[MAX_SET_DEF, Abbr`m`] >>
  qexists_tac `m` >>
  CONJ_ASM1_TAC >| [
    `1 <= m` by metis_tac[] >>
    decide_tac,
    CONJ_ASM1_TAC >-
    metis_tac[] >>
    qabbrev_tac `pm = p ** m` >>
    `0 < p` by decide_tac >>
    `0 < pm` by rw[ZERO_LT_EXP, Abbr`pm`] >>
    `n MOD pm = 0` by metis_tac[DIVIDES_MOD_0] >>
    `n = n DIV pm * pm` by metis_tac[DIVISION, ADD_0] >>
    qabbrev_tac `qm = n DIV pm` >>
    spose_not_then strip_assume_tac >>
    `?q. prime q /\ q divides (gcd (p ** k) qm)` by rw[PRIME_FACTOR] >>
    `0 <> pm /\ n <> 0` by decide_tac >>
    `qm <> 0` by metis_tac[MULT] >>
    `0 < qm` by decide_tac >>
    qabbrev_tac `pk = p ** k` >>
    `0 < pk` by rw[ZERO_LT_EXP, Abbr`pk`] >>
    `(gcd pk qm) divides pk /\ (gcd pk qm) divides qm` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0] >>
    `q divides pk /\ q divides qm` by metis_tac[DIVIDES_TRANS] >>
    `k <> 0` by metis_tac[EXP, GCD_1] >>
    `0 < k` by decide_tac >>
    `q divides p` by metis_tac[DIVIDES_EXP_BASE] >>
    `q = p` by rw[prime_divides_only_self] >>
    `?x. qm = x * q` by rw[GSYM divides_def] >>
    `n = x * p * pm` by metis_tac[] >>
    `_ = x * (p * pm)` by rw_tac arith_ss[] >>
    `_ = x * (p ** SUC m)` by rw[EXP, Abbr`pm`] >>
    `(p ** SUC m) divides n` by metis_tac[divides_def] >>
    `SUC m <= m` by metis_tac[] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Consequences of Coprime.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If 1 < n, !x. coprime n x ==> 0 < x /\ 0 < x MOD n *)
(* Proof:
   If x = 0, gcd n x = n. But n <> 1, hence x <> 0, or 0 < x.
   x MOD n = 0 ==> x a multiple of n ==> gcd n x = n <> 1  if n <> 1.
   Hence if 1 < n, coprime n x ==> x MOD n <> 0, or 0 < x MOD n.
*)
val MOD_NONZERO_WHEN_GCD_ONE = store_thm(
  "MOD_NONZERO_WHEN_GCD_ONE",
  ``!n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n``,
  ntac 4 strip_tac >>
  conj_asm1_tac >| [
    `1 <> n` by decide_tac >>
    `x <> 0` by metis_tac[GCD_0R] >>
    decide_tac,
    `1 <> n /\ x <> 0` by decide_tac >>
    `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
    `(k*x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
    spose_not_then strip_assume_tac >>
    `(x MOD n = 0) /\ 0 < n /\ 1 <> 0` by decide_tac >>
    metis_tac[MOD_MULTIPLE_ZERO, MULT_COMM]
  ]);

(* Theorem: If 1 < n, coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k *)
(* Proof:
       gcd n x = 1 ==> x <> 0               by GCD_0R
   Also,
       gcd n x = 1
   ==> ?k q. k * x = q * n + 1              by LINEAR_GCD
   ==> (k * x) MOD n = (q * n + 1) MOD n    by arithmetic
   ==> (k * x) MOD n = 1                    by MOD_MULT, 1 < n.

   Let g = gcd n k.
   Since 1 < n, 0 < n.
   Since q * n+1 <> 0, x <> 0, k <> 0, hence 0 < k.
   Hence 0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)    by GCD_DIVIDES.
   Or  n = a * g /\ k = b * g    for some a, b.
   Therefore:
        (b * g) * x = q * (a * g) + 1
        (b * x) * g = (q * a) * g + 1      by arithmetic
   Hence g divides 1, or g = 1     since 0 < g.
*)
val GCD_ONE_PROPERTY = store_thm(
  "GCD_ONE_PROPERTY",
  ``!n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  `x <> 0` by metis_tac[GCD_0R] >>
  `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
  `(k * x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
  `?g. g = gcd n k` by rw[] >>
  `n <> 0 /\ q*n + 1 <> 0` by decide_tac >>
  `k <> 0` by metis_tac[MULT_EQ_0] >>
  `0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)` by metis_tac[GCD_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `g divides n /\ g divides k` by rw[DIVIDES_MOD_0] >>
  `g divides (n * q) /\ g divides (k*x)` by rw[DIVIDES_MULT] >>
  `g divides (n * q + 1)` by metis_tac [MULT_COMM] >>
  `g divides 1` by metis_tac[DIVIDES_ADD_2] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: For 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
            ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1) *)
(* Proof:
       gcd n x = 1
   ==> ?k. (k * x) MOD n = 1 /\ coprime n k   by GCD_ONE_PROPERTY
       (k * x) MOD n = 1
   ==> (k MOD n * x MOD n) MOD n = 1          by MOD_TIMES2
   ==> ((k MOD n) * x) MOD n = 1              by LESS_MOD, x < n.

   Now   k MOD n < n                          by MOD_LESS
   and   0 < k MOD n                          by MOD_MULTIPLE_ZERO and 1 <> 0.

   Hence take y = k MOD n, then 0 < y < n.
   and gcd n k = 1 ==> gcd n (k MOD n) = 1    by MOD_WITH_GCD_ONE.
*)
val GCD_MOD_MULT_INV = store_thm(
  "GCD_MOD_MULT_INV",
  ``!n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
      ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  rpt strip_tac >>
  `?k. ((k * x) MOD n = 1) /\ coprime n k` by rw_tac std_ss[GCD_ONE_PROPERTY] >>
  `0 < n` by decide_tac >>
  `(k MOD n * x MOD n) MOD n = 1` by rw_tac std_ss[MOD_TIMES2] >>
  `((k MOD n) * x) MOD n = 1` by metis_tac[LESS_MOD] >>
  `k MOD n < n` by rw_tac std_ss[MOD_LESS] >>
  `1 <> 0` by decide_tac >>
  `0 <> k MOD n` by metis_tac[MOD_MULTIPLE_ZERO] >>
  `0 < k MOD n` by decide_tac >>
  metis_tac[MOD_WITH_GCD_ONE]);

(* Convert this into an existence definition *)
val lemma = prove(
  ``!n x. ?y. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
              0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  metis_tac[GCD_MOD_MULT_INV]);

val GEN_MULT_INV_DEF = new_specification(
  "GEN_MULT_INV_DEF",
  ["GCD_MOD_MUL_INV"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val GEN_MULT_INV_DEF =
    |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
       0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\ coprime n (GCD_MOD_MUL_INV n x) /\
       ((GCD_MOD_MUL_INV n x * x) MOD n = 1) : thm *)

(* Theorem: If 1/c = 1/b - 1/a, then lcm a b = lcm a c.
            a * b = c * (a - b) ==> lcm a b = lcm a c *)
(* Proof:
   Idea:
     lcm a c
   = (a * c) DIV (gcd a c)              by lcm_def
   = (a * b * c) DIV (gcd a c) DIV b    by MULT_DIV
   = (a * b * c) DIV b * (gcd a c)      by DIV_DIV_DIV_MULT
   = (a * b * c) DIV gcd b*a b*c        by GCD_COMMON_FACTOR
   = (a * b * c) DIV gcd c*(a-b) c*b    by given
   = (a * b * c) DIV c * gcd (a-b) b    by GCD_COMMON_FACTOR
   = (a * b * c) DIV c * gcd a b        by GCD_SUB_L
   = (a * b * c) DIV c DIV gcd a b      by DIV_DIV_DIV_MULT
   = a * b DIV gcd a b                  by MULT_DIV
   = lcm a b                            by lcm_def

   Details:
   If a = 0,
      lcm 0 b = 0 = lcm 0 c          by LCM_0
   If a <> 0,
      If b = 0, a * b = 0 = c * a    by MULT_0, SUB_0
      Hence c = 0, hence true        by MULT_EQ_0
      If b <> 0, c <> 0.             by MULT_EQ_0
      So 0 < gcd a c, 0 < gcd a b    by GCD_EQ_0
      and  (gcd a c) divides a       by GCD_IS_GREATEST_COMMON_DIVISOR
      thus (gcd a c) divides (a * c) by DIVIDES_MULT
      Note (a - b) <> 0              by MULT_EQ_0
       so  ~(a <= b)                 by SUB_EQ_0
       or  b < a, or b <= a          for GCD_SUB_L later.
   Now,
      lcm a c
    = (a * c) DIV (gcd a c)                      by lcm_def
    = (b * ((a * c) DIV (gcd a c))) DIV b        by MULT_COMM, MULT_DIV
    = ((b * (a * c)) DIV (gcd a c)) DIV b        by MULTIPLY_DIV
    = (b * (a * c)) DIV ((gcd a c) * b)          by DIV_DIV_DIV_MULT
    = (b * a * c) DIV ((gcd a c) * b)            by MULT_ASSOC
    = c * (a * b) DIV (b * (gcd a c))            by MULT_COMM
    = c * (a * b) DIV (gcd (b * a) (b * c))      by GCD_COMMON_FACTOR
    = c * (a * b) DIV (gcd (a * b) (c * b))      by MULT_COMM
    = c * (a * b) DIV (gcd (c * (a-b)) (c * b))  by a * b = c * (a - b)
    = c * (a * b) DIV (c * gcd (a-b) b)          by GCD_COMMON_FACTOR
    = c * (a * b) DIV (c * gcd a b)              by GCD_SUB_L
    = c * (a * b) DIV c DIV (gcd a b)            by DIV_DIV_DIV_MULT
    = a * b DIV gcd a b                          by MULT_COMM, MULT_DIV
    = lcm a b                                    by lcm_def
*)
val LCM_EXCHANGE = store_thm(
  "LCM_EXCHANGE",
  ``!a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c)``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  Cases_on `b = 0` >| [
    `c = 0` by metis_tac[MULT_EQ_0, SUB_0] >>
    rw[],
    `c <> 0` by metis_tac[MULT_EQ_0] >>
    `0 < b /\ 0 < c` by decide_tac >>
    `(gcd a c) divides a` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
    `(gcd a c) divides (a * c)` by rw[DIVIDES_MULT] >>
    `0 < gcd a c /\ 0 < gcd a b` by metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
    `~(a <= b)` by metis_tac[SUB_EQ_0, MULT_EQ_0] >>
    `b <= a` by decide_tac >>
    `lcm a c = (a * c) DIV (gcd a c)` by rw[lcm_def] >>
    `_ = (b * ((a * c) DIV (gcd a c))) DIV b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = ((b * (a * c)) DIV (gcd a c)) DIV b` by rw[MULTIPLY_DIV] >>
    `_ = (b * (a * c)) DIV ((gcd a c) * b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = (b * a * c) DIV ((gcd a c) * b)` by rw[MULT_ASSOC] >>
    `_ = c * (a * b) DIV (b * (gcd a c))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (b * a) (b * c))` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (gcd (a * b) (c * b))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (c * (a-b)) (c * b))` by rw[] >>
    `_ = c * (a * b) DIV (c * gcd (a-b) b)` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (c * gcd a b)` by rw[GCD_SUB_L] >>
    `_ = c * (a * b) DIV c DIV (gcd a b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = a * b DIV gcd a b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = lcm a b` by rw[lcm_def] >>
    decide_tac
  ]);

(* Theorem: LCM (k * m) (k * n) = k * LCM m n *)
(* Proof:
   If m = 0 or n = 0, LHS = 0 = RHS.
   If m <> 0 and n <> 0,
     lcm (k * m) (k * n)
   = (k * m) * (k * n) / gcd (k * m) (k * n)    by GCD_LCM
   = (k * m) * (k * n) / k * (gcd m n)          by GCD_COMMON_FACTOR
   = k * m * n / (gcd m n)
   = k * LCM m n                                by GCD_LCM
*)
val LCM_COMMON_FACTOR = store_thm(
  "LCM_COMMON_FACTOR",
  ``!m n k. lcm (k * m) (k * n) = k * lcm m n``,
  rpt strip_tac >>
  `k * (k * (m * n)) = (k * m) * (k * n)` by rw_tac arith_ss[] >>
  `_ = gcd (k * m) (k * n) * lcm (k * m) (k * n) ` by rw[GCD_LCM] >>
  `_ = k * (gcd m n) * lcm (k * m) (k * n)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * ((gcd m n) * lcm (k * m) (k * n))` by rw_tac arith_ss[] >>
  Cases_on `k = 0` >-
  rw[] >>
  `(gcd m n) * lcm (k * m) (k * n) = k * (m * n)` by metis_tac[MULT_LEFT_CANCEL] >>
  `_ = k * ((gcd m n) * (lcm m n))` by rw_tac std_ss[GCD_LCM] >>
  `_ = (gcd m n) * (k * (lcm m n))` by rw_tac arith_ss[] >>
  Cases_on `n = 0` >-
  rw[] >>
  metis_tac[MULT_LEFT_CANCEL, GCD_EQ_0]);

(* Theorem: coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c *)
(* Proof:
     lcm (a * c) (b * c)
   = lcm (c * a) (c * b)     by MULT_COMM
   = c * (lcm a b)           by LCM_COMMON_FACTOR
   = (lcm a b) * c           by MULT_COMM
   = a * b * c               by LCM_COPRIME
*)
val LCM_COMMON_COPRIME = store_thm(
  "LCM_COMMON_COPRIME",
  ``!a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c``,
  metis_tac[LCM_COMMON_FACTOR, LCM_COPRIME, MULT_COMM]);

(* Theorem: 0 < n /\ m MOD n = 0 ==> gcd m n = n *)
(* Proof:
   Since m MOD n = 0
         ==> n divides m     by DIVIDES_MOD_0
   Hence gcd m n = gcd n m   by GCD_SYM
                 = n         by divides_iff_gcd_fix
*)
val GCD_MULTIPLE = store_thm(
  "GCD_MULTIPLE",
  ``!m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)``,
  metis_tac[DIVIDES_MOD_0, divides_iff_gcd_fix, GCD_SYM]);

(* Theorem: gcd (m * n) n = n *)
(* Proof:
     gcd (m * n) n
   = gcd (n * m) n          by MULT_COMM
   = gcd (n * m) (n * 1)    by MULT_RIGHT_1
   = n * (gcd m 1)          by GCD_COMMON_FACTOR
   = n * 1                  by GCD_1
   = n                      by MULT_RIGHT_1
*)
val GCD_MULTIPLE_ALT = store_thm(
  "GCD_MULTIPLE_ALT",
  ``!m n. gcd (m * n) n = n``,
  rpt strip_tac >>
  `gcd (m * n) n = gcd (n * m) n` by rw[MULT_COMM] >>
  `_ = gcd (n * m) (n * 1)` by rw[] >>
  rw[GCD_COMMON_FACTOR]);


(* Theorem: k * a <= b ==> gcd a b = gcd a (b - k * a) *)
(* Proof:
   By induction on k.
   Base case: 0 * a <= b ==> gcd a b = gcd a (b - 0 * a)
     True since b - 0 * a = b       by MULT, SUB_0
   Step case: k * a <= b ==> (gcd a b = gcd a (b - k * a)) ==>
              SUC k * a <= b ==> (gcd a b = gcd a (b - SUC k * a))
         SUC k * a <= b
     ==> k * a + a <= b             by MULT
        so       a <= b - k * a     by arithmetic [1]
       and   k * a <= b             by 0 <= b - k * a, [2]
       gcd a (b - SUC k * a)
     = gcd a (b - (k * a + a))      by MULT
     = gcd a (b - k * a - a)        by arithmetic
     = gcd a (b - k * a - a + a)    by GCD_ADD_L, ADD_COMM
     = gcd a (b - k * a)            by SUB_ADD, a <= b - k * a [1]
     = gcd a b                      by induction hypothesis, k * a <= b [2]
*)
val GCD_SUB_MULTIPLE = store_thm(
  "GCD_SUB_MULTIPLE",
  ``!a b k. k * a <= b ==> (gcd a b = gcd a (b - k * a))``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[] >>
  rw_tac std_ss[] >>
  `k * a + a <= b` by metis_tac[MULT] >>
  `a <= b - k * a` by decide_tac >>
  `k * a <= b` by decide_tac >>
  `gcd a (b - SUC k * a) = gcd a (b - (k * a + a))` by rw[MULT] >>
  `_ = gcd a (b - k * a - a)` by rw_tac arith_ss[] >>
  `_ = gcd a (b - k * a - a + a)` by rw[GCD_ADD_L, ADD_COMM] >>
  rw_tac std_ss[SUB_ADD]);

(* Theorem: k * a <= b ==> (gcd b a = gcd a (b - k * a)) *)
(* Proof: by GCD_SUB_MULTIPLE, GCD_SYM *)
val GCD_SUB_MULTIPLE_COMM = store_thm(
  "GCD_SUB_MULTIPLE_COMM",
  ``!a b k. k * a <= b ==> (gcd b a = gcd a (b - k * a))``,
  metis_tac[GCD_SUB_MULTIPLE, GCD_SYM]);

(* Idea: a crude upper bound for greatest common divisor.
         A better upper bound is: gcd m n <= MIN m n, by MIN_LE *)

(* Theorem: 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n *)
(* Proof:
   Let g = gcd m n.
   Then g divides m /\ g divides n   by GCD_PROPERTY
     so g <= m /\ g <= n             by DIVIDES_LE,  0 < m, 0 < n
*)
Theorem gcd_le:
  !m n. 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n
Proof
  ntac 3 strip_tac >>
  qabbrev_tac `g = gcd m n` >>
  `g divides m /\ g divides n` by metis_tac[GCD_PROPERTY] >>
  simp[DIVIDES_LE]
QED

(* Idea: a generalisation of GCD_LINEAR:
|- !j k. 0 < j ==> ?p q. p * j = q * k + gcd j k
   This imposes a condition for (gcd a b) divides c.
*)

(* Theorem: 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c) *)
(* Proof:
   Let d = gcd a b.
   If part: d divides c ==> ?p q. p * a = q * b + c
      Note ?k. c = k * d                 by divides_def
       and ?u v. u * a = v * b + d       by GCD_LINEAR, 0 < a
        so (k * u) * a = (k * v) * b + (k * d)
      Take p = k * u, q = k * v,
      Then p * q = q * b + c
   Only-if part: p * a = q * b + c ==> d divides c
      Note d divides a /\ d divides b    by GCD_PROPERTY
        so d divides c                   by divides_linear_sub
*)
Theorem gcd_divides_iff:
  !a b c. 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c)
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  rw_tac bool_ss[EQ_IMP_THM] >| [
    `?k. c = k * d` by rw[GSYM divides_def] >>
    `?p q. p * a = q * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
    `k * (p * a) = k * (q * b + d)` by fs[] >>
    `_ = k * (q * b) + k * d` by decide_tac >>
    metis_tac[MULT_ASSOC],
    `d divides a /\ d divides b` by metis_tac[GCD_PROPERTY] >>
    metis_tac[divides_linear_sub]
  ]
QED

(* Theorem alias *)
Theorem gcd_linear_thm = gcd_divides_iff;
(* val gcd_linear_thm =
|- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c): thm *)

(* Idea: a version of GCD_LINEAR for MOD, without negatives.
   That is: in MOD n. gcd (a b) can be expressed as a linear combination of a b. *)

(* Theorem: 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n *)
(* Proof:
   Let d = gcd a b.
   Then ?h k. h * a = k * b + d                by GCD_LINEAR, 0 < a
   Let p = h, q = k * n - k.
   Then q + k = k * n.
          (p * a) MOD n = (k * b + d) MOD n
   <=>    (p * a + q * b) MOD n = (q * b + k * b + d) MOD n    by ADD_MOD
   <=>    (p * a + q * b) MOD n = (k * b * n + d) MOD n        by above
   <=>    (p * a + q * b) MOD n = d MOD n                      by MOD_TIMES
*)
Theorem gcd_linear_mod_thm:
  !n a b. 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?p k. p * a = k * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
  `k <= k * n` by fs[] >>
  `k * n - k + k = k * n` by decide_tac >>
  qabbrev_tac `q = k * n - k` >>
  qexists_tac `p` >>
  qexists_tac `q` >>
  `(p * a + q * b) MOD n = (q * b + k * b + d) MOD n` by rw[ADD_MOD] >>
  `_ = ((q + k) * b + d) MOD n` by decide_tac >>
  `_ = (k * b * n + d) MOD n` by rfs[] >>
  simp[MOD_TIMES]
QED

(* Idea: a simplification of gcd_linear_mod_thm when n = a. *)

(* Theorem: 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a *)
(* Proof:
   Let g = gcd a b.
   Then ?p q. (p * a + q * b) MOD a = g MOD a  by gcd_linear_mod_thm, n = a
     so               (q * b) MOD a = g MOD a  by MOD_TIMES
*)
Theorem gcd_linear_mod_1:
  !a b. 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a
Proof
  metis_tac[gcd_linear_mod_thm, MOD_TIMES]
QED

(* Idea: symmetric version of of gcd_linear_mod_1. *)

(* Theorem: 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b *)
(* Proof:
   Note ?p. (p * a) MOD b = (gcd b a) MOD b    by gcd_linear_mod_1
     or                   = (gcd a b) MOD b    by GCD_SYM
*)
Theorem gcd_linear_mod_2:
  !a b. 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b
Proof
  metis_tac[gcd_linear_mod_1, GCD_SYM]
QED

(* Idea: replacing n = a * b in gcd_linear_mod_thm. *)

(* Theorem: 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b) *)
(* Proof: by gcd_linear_mod_thm, n = a * b. *)
Theorem gcd_linear_mod_prod:
  !a b. 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b)
Proof
  simp[gcd_linear_mod_thm]
QED

(* Idea: specialise gcd_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b) *)
(* Proof: by gcd_linear_mod_prod. *)
Theorem coprime_linear_mod_prod:
  !a b. 0 < a /\ 0 < b /\ coprime a b ==>
  ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b)
Proof
  metis_tac[gcd_linear_mod_prod]
QED

(* Idea: generalise gcd_linear_mod_thm for multiple of gcd a b. *)

(* Theorem: 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n *)
(* Proof:
   Let d = gcd a b.
   Note k. c = k * d                           by divides_def
    and ?p q. (p * a + q * b) MOD n = d MOD n  by gcd_linear_mod_thm
   Thus (k * d) MOD n
      = (k * (p * a + q * b)) MOD n            by MOD_TIMES2, 0 < n
      = (k * p * a + k * q * b) MOD n          by LEFT_ADD_DISTRIB
   Take (k * p) and (k * q) for the eventual p and q.
*)
Theorem gcd_multiple_linear_mod_thm:
  !n a b c. 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?k. c = k * d` by rw[GSYM divides_def] >>
  `?p q. (p * a + q * b) MOD n = d MOD n` by metis_tac[gcd_linear_mod_thm] >>
  `(k * (p * a + q * b)) MOD n = (k * d) MOD n` by metis_tac[MOD_TIMES2] >>
  `k * (p * a + q * b) = k * p * a + k * q * b` by decide_tac >>
  metis_tac[]
QED

(* Idea: specialise gcd_multiple_linear_mod_thm for n = a * b. *)

(* Theorem: 0 < a /\ 0 < b /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)) *)
(* Proof: by gcd_multiple_linear_mod_thm. *)
Theorem gcd_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ gcd a b divides c ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  simp[gcd_multiple_linear_mod_thm]
QED

(* Idea: specialise gcd_multiple_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b) *)
(* Proof:
   Note coprime a b means gcd a b = 1    by notation
    and 1 divides c                      by ONE_DIVIDES_ALL
     so the result follows               by gcd_multiple_linear_mod_prod
*)
Theorem coprime_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ coprime a b ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  metis_tac[gcd_multiple_linear_mod_prod, ONE_DIVIDES_ALL]
QED

(* ------------------------------------------------------------------------- *)
(* Coprime Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !a b. coprime a b <=> coprime a (b ** n) *)
(* Proof:
   If part: coprime a b ==> coprime a (b ** n)
      True by coprime_exp_comm.
   Only-if part: coprime a (b ** n) ==> coprime a b
      If a = 0,
         then b ** n = 1        by GCD_0L
          and b = 1             by EXP_EQ_1, n <> 0
         Hence coprime 0 1      by GCD_0L
      If a <> 0,
      Since coprime a (b ** n) means
            ?h k. h * a = k * b ** n + 1   by LINEAR_GCD, GCD_SYM
   Let d = gcd a b.
   Since d divides a and d divides b       by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides b ** n                  by divides_exp, 0 < n
      so d divides 1                       by divides_linear_sub
    Thus d = 1                             by DIVIDES_ONE
      or coprime a b                       by notation
*)
val coprime_iff_coprime_exp = store_thm(
  "coprime_iff_coprime_exp",
  ``!n. 0 < n ==> !a b. coprime a b <=> coprime a (b ** n)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_exp_comm] >>
  `n <> 0` by decide_tac >>
  Cases_on `a = 0` >-
  metis_tac[GCD_0L, EXP_EQ_1] >>
  `?h k. h * a = k * b ** n + 1` by metis_tac[LINEAR_GCD, GCD_SYM] >>
  qabbrev_tac `d = gcd a b` >>
  `d divides a /\ d divides b` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides (b ** n)` by rw[divides_exp] >>
  `d divides 1` by metis_tac[divides_linear_sub] >>
  rw[GSYM DIVIDES_ONE]);

(* Theorem: 1 < n /\ coprime n m ==> ~(n divides m) *)
(* Proof:
       coprime n m
   ==> gcd n m = 1       by notation
   ==> n MOD m <> 0      by MOD_NONZERO_WHEN_GCD_ONE, with 1 < n
   ==> ~(n divides m)    by DIVIDES_MOD_0, with 0 < n
*)
val coprime_not_divides = store_thm(
  "coprime_not_divides",
  ``!m n. 1 < n /\ coprime n m ==> ~(n divides m)``,
  metis_tac[MOD_NONZERO_WHEN_GCD_ONE, DIVIDES_MOD_0, ONE_LT_POS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n *)
(* Proof:
   By contradiction. Suppose n <= m.
   Since 1 < n means 0 < n and n <> 1,
   The implication shows
       coprime n n, or n = 1   by notation
   But gcd n n = n             by GCD_REF
   This contradicts n <> 1.
*)
val coprime_all_le_imp_lt = store_thm(
  "coprime_all_le_imp_lt",
  ``!n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n``,
  spose_not_then strip_assume_tac >>
  `n <= m` by decide_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  metis_tac[GCD_REF]);

(* Theorem: (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n) *)
(* Proof:
   If part: (!j. 1 < j /\ j <= m ==> ~(j divides n)) /\ 1 < j /\ j <= m ==> coprime j n
      Let d = gcd j n.
      Then d divides j /\ d divides n         by GCD_IS_GREATEST_COMMON_DIVISOR
       Now 1 < j ==> 0 < j /\ j <> 0
        so d <= j                             by DIVIDES_LE, 0 < j
       and d <> 0                             by GCD_EQ_0, j <> 0
      By contradiction, suppose d <> 1.
      Then 1 < d /\ d <= m                    by d <> 1, d <= j /\ j <= m
        so ~(d divides n), a contradiction    by implication

   Only-if part: (!j. 1 < j /\ j <= m ==> coprime j n) /\ 1 < j /\ j <= m ==> ~(j divides n)
      Since coprime j n                       by implication
         so ~(j divides n)                    by coprime_not_divides
*)
val coprime_condition = store_thm(
  "coprime_condition",
  ``!m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `d = gcd j n` >>
    `d divides j /\ d divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
    `0 < j /\ j <> 0` by decide_tac >>
    `d <= j` by rw[DIVIDES_LE] >>
    `d <> 0` by metis_tac[GCD_EQ_0] >>
    `1 < d /\ d <= m` by decide_tac >>
    metis_tac[],
    metis_tac[coprime_not_divides]
  ]);

(* Note:
The above is the generalization of this observation:
- a prime n  has all 1 < j < n coprime to n. Therefore,
- a number n has all 1 < j < m coprime to n, where m is the first non-trivial factor of n.
  Of course, the first non-trivial factor of n must be a prime.
*)

(* Theorem: 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n *)
(* Proof: by coprime_condition, taking j = m. *)
val coprime_by_le_not_divides = store_thm(
  "coprime_by_le_not_divides",
  ``!m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n``,
  rw[coprime_condition]);

(* Idea: establish coprime (p * a + q * b) (a * b). *)
(* Note: the key is to apply coprime_by_prime_factor. *)

(* Theorem: coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b) *)
(* Proof:
   Let z = p * a + q * b, c = a * b, d = gcd z c.
   Then d divides z /\ d divides c       by GCD_PROPERTY
   By coprime_by_prime_factor, we need to show:
      !t. prime t ==> ~(t divides z /\ t divides c)
   By contradiction, suppose t divides z /\ t divides c.
   Then t divides d                      by GCD_PROPERTY
     or t divides c where c = a * b      by DIVIDES_TRANS
     so t divides a or p divides b       by P_EUCLIDES

   If t divides a,
      Then t divides (q * b)             by divides_linear_sub
       and ~(t divides b)                by coprime_common_factor, NOT_PRIME_1
        so t divides q                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   If t divides b,
      Then t divides (p * a)             by divides_linear_sub
       and ~(t divides a)                by coprime_common_factor, NOT_PRIME_1
        so t divides p                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   Since all lead to contradiction, we have shown:
     !t. prime t ==> ~(t divides z /\ t divides c)
   Thus coprime z c                      by coprime_by_prime_factor
*)
Theorem coprime_linear_mult:
  !a b p q. coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
Proof
  rpt strip_tac >>
  qabbrev_tac `z = p * a + q * b` >>
  qabbrev_tac `c = a * b` >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides a \/ p' divides b` by metis_tac[P_EUCLIDES] >| [
    `p' divides (q * b)` by metis_tac[divides_linear_sub, MULT_LEFT_1] >>
    `~(p' divides b)` by metis_tac[coprime_common_factor, NOT_PRIME_1] >>
    `p' divides q` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1],
    `p' divides (p * a)` by metis_tac[divides_linear_sub, MULT_LEFT_1, ADD_COMM] >>
    `~(p' divides a)` by metis_tac[coprime_common_factor, NOT_PRIME_1, MULT_COMM] >>
    `p' divides p` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1]
  ]
QED

(* Idea: include converse of coprime_linear_mult. *)

(* Theorem: coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b)) *)
(* Proof:
   If part: coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
      This is true by coprime_linear_mult.
   Only-if: coprime (p * a + q * b) (a * b) ==> coprime p b /\ coprime q a
      Let z = p * a + q * b. Consider a prime t.
      For coprime p b.
          If t divides p /\ t divides b,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime p b         by coprime_by_prime_factor
      For coprime q a.
          If t divides q /\ t divides a,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime q a         by coprime_by_prime_factor
*)
Theorem coprime_linear_mult_iff:
  !a b p q. coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b))
Proof
  rw_tac std_ss[EQ_IMP_THM] >-
  simp[coprime_linear_mult] >-
 (irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by rw[DIVIDES_MULTIPLE] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]) >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]
QED

(* Idea: condition for a number to be coprime with prime power. *)

(* Theorem: prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q) *)
(* Proof:
   If part: prime p /\ 0 < n /\ coprime q (p ** n) ==> ~(p divides q)
      By contradiction, suppose p divides q.
      Note p divides (p ** n)  by prime_divides_self_power, 0 < n
      Thus p = 1               by coprime_common_factor
      This contradicts p <> 1  by NOT_PRIME_1
   Only-if part: prime p /\ 0 < n /\ ~(p divides q) ==> coprime q (p ** n)
      Note coprime q p         by prime_not_divides_coprime, GCD_SYM
      Thus coprime q (p ** n)  by coprime_iff_coprime_exp, 0 < n
*)
Theorem coprime_prime_power:
  !p n. prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[prime_divides_self_power, coprime_common_factor, NOT_PRIME_1] >>
  metis_tac[prime_not_divides_coprime, coprime_iff_coprime_exp, GCD_SYM]
QED

(* Theorem: prime n ==> !m. 0 < m /\ m < n ==> coprime n m *)
(* Proof:
   By contradiction. Let d = gcd n m, and d <> 1.
   Since prime n, 0 < n       by PRIME_POS
   Thus d divides n, and d m divides    by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0, m <> 0.
   ==>  d = n                           by prime_def, d <> 1.
   ==>  n divides m                     by d divides m
   ==>  n <= m                          by DIVIDES_LE
   which contradicts m < n.
*)
val prime_coprime_all_lt = store_thm(
  "prime_coprime_all_lt",
  ``!n. prime n ==> !m. 0 < m /\ m < n ==> coprime n m``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd n m` >>
  `0 < n` by rw[PRIME_POS] >>
  `n <> 0 /\ m <> 0` by decide_tac >>
  `d divides n /\ d divides m` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = n` by metis_tac[prime_def] >>
  `n <= m` by rw[DIVIDES_LE] >>
  decide_tac);

(* Theorem: prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) *)
(* Proof:
   Since m < n, all j < n.
   Hence true by prime_coprime_all_lt
*)
val prime_coprime_all_less = store_thm(
  "prime_coprime_all_less",
  ``!m n. prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j)``,
  rpt strip_tac >>
  `j < n` by decide_tac >>
  rw[prime_coprime_all_lt]);

(* Theorem: prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)) *)
(* Proof:
   If part: prime n ==> 1 < n /\ !j. 0 < j /\ j < n ==> coprime n j
      (1) prime n ==> 1 < n                          by ONE_LT_PRIME
      (2) prime n /\ 0 < j /\ j < n ==> coprime n j  by prime_coprime_all_lt
   Only-if part: !j. 0 < j /\ j < n ==> coprime n j ==> prime n
      By contradiction, assume ~prime n.
      Now, 1 < n /\ ~prime n
      ==> ?p. prime p /\ p < n /\ p divides n   by PRIME_FACTOR_PROPER
      and prime p ==> 0 < p and 1 < p           by PRIME_POS, ONE_LT_PRIME
      Hence ~coprime p n                        by coprime_not_divides, 1 < p
      But 0 < p < n ==> coprime n p             by given implication
      This is a contradiction                   by coprime_sym
*)
val prime_iff_coprime_all_lt = store_thm(
  "prime_iff_coprime_all_lt",
  ``!n. prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)``,
  rw[EQ_IMP_THM, ONE_LT_PRIME] >-
  rw[prime_coprime_all_lt] >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p < n /\ p divides n` by rw[PRIME_FACTOR_PROPER] >>
  `0 < p` by rw[PRIME_POS] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[coprime_not_divides, coprime_sym]);

(* Theorem: prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) *)
(* Proof:
   If part: prime n ==> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))
      Note 1 < n                 by ONE_LT_PRIME
      By contradiction, suppose j divides n.
      Then j = 1 or j = n        by prime_def
      This contradicts 1 < j /\ j < n.
   Only-if part: (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) ==> prime n
      This is to show:
      !b. b divides n ==> b = 1 or b = n    by prime_def
      Since 1 < n, so n <> 0     by arithmetic
      Thus b <= n                by DIVIDES_LE
       and b <> 0                by ZERO_DIVIDES
      By contradiction, suppose b <> 1 and b <> n, but b divides n.
      Then 1 < b /\ b < n        by above
      giving ~(b divides n)      by implication
      This contradicts with b divides n.
*)
val prime_iff_no_proper_factor = store_thm(
  "prime_iff_no_proper_factor",
  ``!n. prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  rw[prime_def] >>
  `b <= n` by rw[DIVIDES_LE] >>
  `n <> 0` by decide_tac >>
  `b <> 0` by metis_tac[ZERO_DIVIDES] >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ b < n` by decide_tac >>
  metis_tac[]);

(* Theorem: FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: coprime x (PROD_SET {})
      Note PROD_SET {} = 1         by PROD_SET_EMPTY
       and coprime x 1 = T         by GCD_1
   Step: !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) ==>
        e NOTIN s /\ x NOTIN e INSERT s /\ !z. z IN e INSERT s ==> coprime x z ==>
        coprime x (PROD_SET (e INSERT s))
      Note coprime x e                               by IN_INSERT
       and coprime x (PROD_SET s)                    by induction hypothesis
      Thus coprime x (e * PROD_SET s)                by coprime_product_coprime_sym
        or coprime x PROD_SET (e INSERT s)           by PROD_SET_INSERT
*)
val every_coprime_prod_set_coprime = store_thm(
  "every_coprime_prod_set_coprime",
  ``!s. FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  rw[PROD_SET_INSERT, coprime_product_coprime_sym]);

(* ------------------------------------------------------------------------- *)
(* GCD divisibility condition of Power Predecessors                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)) *)
(* Proof:
   Note !n. 1 <= t ** n                  by ONE_LE_EXP, 0 < t, [1]

   Claim: t ** (n - m) - 1 <= t ** n - 1, because:
   Proof: Note n - m <= n                always
            so t ** (n - m) <= t ** n    by EXP_BASE_LEQ_MONO_IMP, 0 < t
           Now 1 <= t ** (n - m) and
               1 <= t ** n               by [1]
           Hence t ** (n - m) - 1 <= t ** n - 1.

        t ** (n - m) * (t ** m - 1) + t ** (n - m) - 1
      = (t ** (n - m) * t ** m - t ** (n - m)) + t ** (n - m) - 1   by LEFT_SUB_DISTRIB
      = (t ** (n - m + m) - t ** (n - m)) + t ** (n - m) - 1        by EXP_ADD
      = (t ** n - t ** (n - m)) + t ** (n - m) - 1                  by SUB_ADD, m <= n
      = (t ** n - (t ** (n - m) - 1 + 1)) + t ** (n - m) - 1        by SUB_ADD, 1 <= t ** (n - m)
      = (t ** n - (1 + (t ** (n - m) - 1))) + t ** (n - m) - 1      by ADD_COMM
      = (t ** n - 1 - (t ** (n - m) - 1)) + t ** (n - m) - 1        by SUB_PLUS, no condition
      = t ** n - 1                                 by SUB_ADD, t ** (n - m) - 1 <= t ** n - 1
*)
val power_predecessor_division_eqn = store_thm(
  "power_predecessor_division_eqn",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1))``,
  rpt strip_tac >>
  `1 <= t ** n /\ 1 <= t ** (n - m)` by rw[ONE_LE_EXP] >>
  `n - m <= n` by decide_tac >>
  `t ** (n - m) <= t ** n` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `t ** (n - m) - 1 <= t ** n - 1` by decide_tac >>
  qabbrev_tac `z = t ** (n - m) - 1` >>
  `t ** (n - m) * (t ** m - 1) + z =
    t ** (n - m) * t ** m - t ** (n - m) + z` by decide_tac >>
  `_ = t ** (n - m + m) - t ** (n - m) + z` by rw_tac std_ss[EXP_ADD] >>
  `_ = t ** n - t ** (n - m) + z` by rw_tac std_ss[SUB_ADD] >>
  `_ = t ** n - (z + 1) + z` by rw_tac std_ss[SUB_ADD, Abbr`z`] >>
  `_ = t ** n + z - (z + 1)` by decide_tac >>
  `_ = t ** n - 1` by decide_tac >>
  decide_tac);

(* This shows the pattern:
                    1000000    so 9999999999 = 1000000 * 9999 + 999999
               ------------    or (b ** 10 - 1) = b ** 6 * (b ** 4 - 1) + (b ** 6 - 1)
          9999 | 9999999999    where b = 10.
                 9999
                 ----------
                     999999
*)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1) *)
(* Proof: by power_predecessor_division_eqn *)
val power_predecessor_division_alt = store_thm(
  "power_predecessor_division_alt",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1)``,
  rpt strip_tac >>
  imp_res_tac power_predecessor_division_eqn >>
  fs[]);

(* Theorem: m < n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)) *)
(* Proof:
   Case t = 0,
      If n = 0, t ** 0 = 1             by ZERO_EXP
      LHS = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
      If n <> 0, 0 ** n = 0            by ZERO_EXP
      LHS = gcd (0 - 1) x
          = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
   Case t <> 0,
      Note t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)
                                       by power_predecessor_division_eqn
        so t ** (n - m) * (t ** m - 1) <= t ** n - 1    by above, [1]
       and t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1, [2]
        gcd (t ** n - 1) (t ** m - 1)
      = gcd (t ** m - 1) (t ** n - 1)                by GCD_SYM
      = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))
                                                     by GCD_SUB_MULTIPLE, [1]
      = gcd (t ** m - 1)) (t ** (n - m) - 1)         by [2]
*)
val power_predecessor_gcd_reduction = store_thm(
  "power_predecessor_gcd_reduction",
  ``!t n m. m <= n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1))``,
  rpt strip_tac >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP] >>
  `t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)` by rw[power_predecessor_division_eqn] >>
  `t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1` by fs[] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd (t ** m - 1) (t ** n - 1)` by rw_tac std_ss[GCD_SYM] >>
  `_ = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))` by rw_tac std_ss[GCD_SUB_MULTIPLE] >>
  rw_tac std_ss[]);

(* Theorem: gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1 *)
(* Proof:
   By complete induction on (n + m):
   Induction hypothesis: !m'. m' < n + m ==>
                         !n m. (m' = n + m) ==> (gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1)
   Idea: if 0 < m, n < n + m. Put last n = m, m = n - m. That is m' = m + (n - m) = n.
   Also  if 0 < n, m < n + m. Put last n = n, m = m - n. That is m' = n + (m - n) = m.

   Thus to apply induction hypothesis, need 0 < n or 0 < m.
   So take care of these special cases first.

   Case: n = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** 0 - 1) (t ** m - 1)
             = gcd 0 (t ** m - 1)                 by EXP
             = t ** m - 1                         by GCD_0L
             = t ** (gcd 0 m) - 1 = RHS           by GCD_0L
   Case: m = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** n - 1) (t ** 0 - 1)
             = gcd (t ** n - 1) 0                 by EXP
             = t ** n - 1                         by GCD_0R
             = t ** (gcd n 0) - 1 = RHS           by GCD_0R

   Case: m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
      That is, 0 < n, and 0 < m
          also n < n + m, and m < n + m           by arithmetic

      Use trichotomy of numbers:                  by LESS_LESS_CASES
      Case: n = m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** m - 1) (t ** m - 1)
             = t ** m - 1                         by GCD_REF
             = t ** (gcd m m) - 1 = RHS           by GCD_REF

      Case: m < n /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since n < n + m                          by 0 < m
           and m + (n - m) = (n - m) + m          by ADD_COMM
                           = n                    by SUB_ADD, m <= n
           gcd (t ** n - 1) (t ** m - 1)
         = gcd ((t ** m - 1)) (t ** (n - m) - 1)  by power_predecessor_gcd_reduction
         = t ** gcd m (n - m) - 1                 by induction hypothesis, m + (n - m) = n
         = t ** gcd m n - 1                       by GCD_SUB_R, m <= n
         = t ** gcd n m - 1                       by GCD_SYM

      Case: n < m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since m < n + m                          by 0 < n
           and n + (m - n) = (m - n) + n          by ADD_COMM
                           = m                    by SUB_ADD, n <= m
          gcd (t ** n - 1) (t ** m - 1)
        = gcd (t ** m - 1) (t ** n - 1)           by GCD_SYM
        = gcd ((t ** n - 1)) (t ** (m - n) - 1)   by power_predecessor_gcd_reduction
        = t ** gcd n (m - n) - 1                  by induction hypothesis, n + (m - n) = m
        = t ** gcd n m                            by GCD_SUB_R, n <= m
*)
val power_predecessor_gcd_identity = store_thm(
  "power_predecessor_gcd_identity",
  ``!t n m. gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1``,
  rpt strip_tac >>
  completeInduct_on `n + m` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  Cases_on `m = 0` >-
  rw[EXP] >>
  `(n = m) \/ (m < n) \/ (n < m)` by metis_tac[LESS_LESS_CASES] >-
  rw[GCD_REF] >-
 (`0 < m /\ n < n + m` by decide_tac >>
  `m <= n` by decide_tac >>
  `m + (n - m) = n` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)` by rw[power_predecessor_gcd_reduction] >>
  `_ = t ** gcd m (n - m) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R, GCD_SYM]) >>
  `0 < n /\ m < n + m` by decide_tac >>
  `n <= m` by decide_tac >>
  `n + (m - n) = m` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** n - 1)) (t ** (m - n) - 1)` by rw[power_predecessor_gcd_reduction, GCD_SYM] >>
  `_ = t ** gcd n (m - n) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R]);

(* Above is the formal proof of the following pattern:
   For any base
         gcd(999999,9999) = gcd(6 9s, 4 9s) = gcd(6,4) 9s = 2 9s = 99
   or        999999 MOD 9999 = (6 9s) MOD (4 9s) = 2 9s = 99
   Thus in general,
             (m 9s) MOD (n 9s) = (m MOD n) 9s
   Repeating the use of Euclidean algorithm then gives:
             gcd (m 9s, n 9s) = (gcd m n) 9s

Reference: A Mathematical Tapestry (by Jean Pedersen and Peter Hilton)
Chapter 4: A number-theory thread -- Folding numbers, a number trick, and some tidbits.
*)

(* Theorem: 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m) *)
(* Proof:
       (t ** n - 1) divides (t ** m - 1)
   <=> gcd (t ** n - 1) (t ** m - 1) = t ** n - 1   by divides_iff_gcd_fix
   <=> t ** (gcd n m) - 1 = t ** n - 1              by power_predecessor_gcd_identity
   <=> t ** (gcd n m) = t ** n                      by PRE_SUB1, INV_PRE_EQ, EXP_POS, 0 < t
   <=>       gcd n m = n                            by EXP_BASE_INJECTIVE, 1 < t
   <=>       n divides m                            by divides_iff_gcd_fix
*)
val power_predecessor_divisibility = store_thm(
  "power_predecessor_divisibility",
  ``!t n m. 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m)``,
  rpt strip_tac >>
  `0 < t` by decide_tac >>
  `!n. 0 < t ** n` by rw[EXP_POS] >>
  `!x y. 0 < x /\ 0 < y ==> ((x - 1 = y - 1) <=> (x = y))` by decide_tac >>
  `(t ** n - 1) divides (t ** m - 1) <=> ((gcd (t ** n - 1) (t ** m - 1) = t ** n - 1))` by rw[divides_iff_gcd_fix] >>
  `_ = (t ** (gcd n m) - 1 = t ** n - 1)` by rw[power_predecessor_gcd_identity] >>
  `_ = (t ** (gcd n m) = t ** n)` by rw[] >>
  `_ = (gcd n m = n)` by rw[EXP_BASE_INJECTIVE] >>
  rw[divides_iff_gcd_fix]);

(* Theorem: t - 1 divides t ** n - 1 *)
(* Proof:
   If t = 0,
      Then t - 1 = 0        by integer subtraction
       and t ** n - 1 = 0   by ZERO_EXP, either case of n.
      Thus 0 divides 0      by ZERO_DIVIDES
   If t = 1,
      Then t - 1 = 0        by arithmetic
       and t ** n - 1 = 0   by EXP_1
      Thus 0 divides 0      by ZERO_DIVIDES
   Otherwise, 1 < t
       and 1 divides n      by ONE_DIVIDES_ALL
       ==> t ** 1 - 1 divides t ** n - 1   by power_predecessor_divisibility
        or      t - 1 divides t ** n - 1   by EXP_1
*)
Theorem power_predecessor_divisor:
  !t n. t - 1 divides t ** n - 1
Proof
  rpt strip_tac >>
  Cases_on `t = 0` >-
  simp[ZERO_EXP] >>
  Cases_on `t = 1` >-
  simp[] >>
  `1 < t` by decide_tac >>
  metis_tac[power_predecessor_divisibility, EXP_1, ONE_DIVIDES_ALL]
QED

(* Overload power predecessor *)
Overload tops = “\b:num n. b ** n - 1”

(*
   power_predecessor_division_eqn
     |- !t m n. 0 < t /\ m <= n ==> tops t n = t ** (n - m) * tops t m + tops t (n - m)
   power_predecessor_division_alt
     |- !t m n. 0 < t /\ m <= n ==> tops t n - t ** (n - m) * tops t m = tops t (n - m)
   power_predecessor_gcd_reduction
     |- !t n m. m <= n ==> (gcd (tops t n) (tops t m) = gcd (tops t m) (tops t (n - m)))
   power_predecessor_gcd_identity
     |- !t n m. gcd (tops t n) (tops t m) = tops t (gcd n m)
   power_predecessor_divisibility
     |- !t n m. 1 < t ==> (tops t n divides tops t m <=> n divides m)
   power_predecessor_divisor
     |- !t n. t - 1 divides tops t n
*)

(* Overload power predecessor base 10 *)
val _ = overload_on("nines", ``\n. tops 10 n``);

(* Obtain corollaries *)

val nines_division_eqn = save_thm("nines_division_eqn",
    power_predecessor_division_eqn |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_division_alt = save_thm("nines_division_alt",
    power_predecessor_division_alt |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_gcd_reduction = save_thm("nines_gcd_reduction",
    power_predecessor_gcd_reduction |> ISPEC ``10``);
val nines_gcd_identity = save_thm("nines_gcd_identity",
    power_predecessor_gcd_identity |> ISPEC ``10``);
val nines_divisibility = save_thm("nines_divisibility",
    power_predecessor_divisibility |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_divisor = save_thm("nines_divisor",
    power_predecessor_divisor |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
(*
val nines_division_eqn =
   |- !m n. m <= n ==> nines n = 10 ** (n - m) * nines m + nines (n - m): thm
val nines_division_alt =
   |- !m n. m <= n ==> nines n - 10 ** (n - m) * nines m = nines (n - m): thm
val nines_gcd_reduction =
   |- !n m. m <= n ==> gcd (nines n) (nines m) = gcd (nines m) (nines (n - m)): thm
val nines_gcd_identity = |- !n m. gcd (nines n) (nines m) = nines (gcd n m): thm
val nines_divisibility = |- !n m. nines n divides nines m <=> n divides m: thm
val nines_divisor = |- !n. 9 divides nines n: thm
*)

(* ------------------------------------------------------------------------- *)
(* GCD involving Powers                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime m /\ prime n /\ m divides (n ** k) ==> (m = n) *)
(* Proof:
   By induction on k.
   Base: m divides n ** 0 ==> (m = n)
      Since n ** 0 = 1              by EXP
        and m divides 1 ==> m = 1   by DIVIDES_ONE
       This contradicts 1 < m       by ONE_LT_PRIME
   Step: m divides n ** k ==> (m = n) ==> m divides n ** SUC k ==> (m = n)
      Since n ** SUC k = n * n ** k           by EXP
       Also m divides n \/ m divides n ** k   by P_EUCLIDES
         If m divides n, then m = n           by prime_divides_only_self
         If m divides n ** k, then m = n      by induction hypothesis
*)
val prime_divides_prime_power = store_thm(
  "prime_divides_prime_power",
  ``!m n k. prime m /\ prime n /\ m divides (n ** k) ==> (m = n)``,
  rpt strip_tac >>
  Induct_on `k` >| [
    rpt strip_tac >>
    `1 < m` by rw[ONE_LT_PRIME] >>
    `m = 1` by metis_tac[EXP, DIVIDES_ONE] >>
    decide_tac,
    metis_tac[EXP, P_EUCLIDES, prime_divides_only_self]
  ]);

(* This is better than FACTOR_OUT_PRIME *)

(* Theorem: 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q *)
(* Proof:
   If p divides n,
      Then ?m. 0 < m /\ p ** m divides n /\
           !k. coprime (p ** k) (n DIV p ** m)   by FACTOR_OUT_PRIME
      Let q = n DIV (p ** m).
      Note 0 < p                                 by PRIME_POS
        so 0 < p ** m                            by EXP_POS, 0 < p
      Take this q and m,
      Then n = (p ** m) * q                      by DIVIDES_EQN_COMM
       and coprime p q                           by taking k = 1, EXP_1

   If ~(p divides n),
      Then coprime p n                           by prime_not_divides_coprime
      Let q = n, m = 0.
      Then n = 1 * q                             by EXP, MULT_LEFT_1
       and coprime p q.
*)
val prime_power_factor = store_thm(
  "prime_power_factor",
  ``!n p. 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q``,
  rpt strip_tac >>
  Cases_on `p divides n` >| [
    `?m. 0 < m /\ p ** m divides n /\ !k. coprime (p ** k) (n DIV p ** m)` by rw[FACTOR_OUT_PRIME] >>
    qabbrev_tac `q = n DIV (p ** m)` >>
    `0 < p` by rw[PRIME_POS] >>
    `0 < p ** m` by rw[EXP_POS] >>
    metis_tac[DIVIDES_EQN_COMM, EXP_1],
    `coprime p n` by rw[prime_not_divides_coprime] >>
    metis_tac[EXP, MULT_LEFT_1]
  ]);

(* Even this simple theorem is quite difficult to prove, why? *)
(* Because this needs a typical detective-style proof! *)

(* Theorem: prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j) *)
(* Proof:
   Note 0 < p                by PRIME_POS
     so 0 < p ** n           by EXP_POS
   Thus 0 < a                by ZERO_DIVIDES
    ==> ?q m. (a = (p ** m) * q) /\ coprime p q    by prime_power_factor

   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Then ?t. prime t /\ t divides q          by PRIME_FACTOR, q <> 1
           Now q divides a           by divides_def
            so t divides (p ** n)    by DIVIDES_TRANS
           ==> t = p                 by prime_divides_prime_power
           But gcd t q = t           by divides_iff_gcd_fix
            or gcd p q = p           by t = p
           Yet p <> 1                by NOT_PRIME_1
            so this contradicts coprime p q.

   Thus a = p ** m                   by q = 1, Claim.
   Note p ** m <= p ** n             by DIVIDES_LE, 0 < p
    and 1 < p                        by ONE_LT_PRIME
    ==>      m <= n                  by EXP_BASE_LE_MONO, 1 < p
   Take j = m, and the result follows.
*)
val prime_power_divisor = store_thm(
  "prime_power_divisor",
  ``!p n a. prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `0 < p ** n` by rw[EXP_POS] >>
  `0 < a` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `?q m. (a = (p ** m) * q) /\ coprime p q` by rw[prime_power_factor] >>
  `q = 1` by
  (spose_not_then strip_assume_tac >>
  `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
  `q divides a` by metis_tac[divides_def] >>
  `t divides (p ** n)` by metis_tac[DIVIDES_TRANS] >>
  `t = p` by metis_tac[prime_divides_prime_power] >>
  `gcd t q = t` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[NOT_PRIME_1]) >>
  `a = p ** m` by rw[] >>
  metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q ==>
            !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n) *)
(* Proof:
   First goal: p = q.
      Since p divides p        by DIVIDES_REFL
        ==> p divides p ** m   by divides_exp, 0 < m.
         so p divides q ** n   by given, p ** m = q ** n
      Hence p = q              by prime_divides_prime_power
   Second goal: m = n.
      Note p = q               by first goal.
      Since 1 < p              by ONE_LT_PRIME
      Hence m = n              by EXP_BASE_INJECTIVE, 1 < p
*)
val prime_powers_eq = store_thm(
  "prime_powers_eq",
  ``!p q. prime p /\ prime q ==>
   !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n)``,
  ntac 6 strip_tac >>
  conj_asm1_tac >-
  metis_tac[divides_exp, prime_divides_prime_power, DIVIDES_REFL] >>
  metis_tac[EXP_BASE_INJECTIVE, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n) *)
(* Proof:
   Let d = gcd (p ** m) (q ** n).
   By contradiction, d <> 1.
   Then d divides (p ** m) /\ d divides (q ** n)   by GCD_PROPERTY
    ==> ?j. j <= m /\ (d = p ** j)                 by prime_power_divisor, prime p
    and ?k. k <= n /\ (d = q ** k)                 by prime_power_divisor, prime q
   Note j <> 0 /\ k <> 0                           by EXP_0
     or 0 < j /\ 0 < k                             by arithmetic
    ==> p = q, which contradicts p <> q            by prime_powers_eq
*)
val prime_powers_coprime = store_thm(
  "prime_powers_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n)``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd (p ** m) (q ** n)` >>
  `d divides (p ** m) /\ d divides (q ** n)` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_power_divisor, prime_powers_eq, EXP_0, NOT_ZERO_LT_ZERO]);

(* Theorem: prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n)) *)
(* Proof:
   If part: p ** m divides q ** n ==> (p = q) /\ m <= n
      Note p divides (p ** m)         by prime_divides_self_power, 0 < m
        so p divides (q ** n)         by DIVIDES_TRANS
      Thus p = q                      by prime_divides_prime_power
      Note 1 < p                      by ONE_LT_PRIME
      Thus m <= n                     by power_divides_iff
   Only-if part: (p = q) /\ m <= n ==> p ** m divides q ** n
      Note 1 < p                      by ONE_LT_PRIME
      Thus p ** m divides q ** n      by power_divides_iff
*)
val prime_powers_divide = store_thm(
  "prime_powers_divide",
  ``!p q. prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n))``,
  metis_tac[ONE_LT_PRIME, divides_self_power, prime_divides_prime_power, power_divides_iff, DIVIDES_TRANS]);

(* Theorem: prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q) *)
(* Proof:
   By contradiction, suppose q <> 1 /\ ~(p divides q).
   Note ?j. j <= n /\ (q = p ** j)   by prime_power_divisor
    and 0 < j                        by EXP_0, q <> 1
   then p divides q                  by prime_divides_self_power, 0 < j
   This contradicts ~(p divides q).
*)
Theorem PRIME_EXP_FACTOR:
  !p q n. prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q)
Proof
  spose_not_then strip_assume_tac >>
  `?j. j <= n /\ (q = p ** j)` by rw[prime_power_divisor] >>
  `0 < j` by fs[] >>
  metis_tac[prime_divides_self_power]
QED

(* Theorem: gcd (b ** m) (b ** n) = b ** (MIN m n) *)
(* Proof:
   If m = n,
      LHS = gcd (b ** n) (b ** n)
          = b ** n                     by GCD_REF
      RHS = b ** (MIN n n)
          = b ** n                     by MIN_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or gcd (b ** m) (b ** n)
       = b ** m                        by divides_iff_gcd_fix
       = b ** (MIN m n)                by MIN_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use GCD_SYM.
*)
val gcd_powers = store_thm(
  "gcd_powers",
  ``!b m n. gcd (b ** m) (b ** n) = b ** (MIN m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, MIN_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM, MIN_DEF]
  ]);

(* Theorem: lcm (b ** m) (b ** n) = b ** (MAX m n) *)
(* Proof:
   If m = n,
      LHS = lcm (b ** n) (b ** n)
          = b ** n                     by LCM_REF
      RHS = b ** (MAX n n)
          = b ** n                     by MAX_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or lcm (b ** m) (b ** n)
       = b ** n                        by divides_iff_lcm_fix
       = b ** (MAX m n)                by MAX_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use LCM_COMM.
*)
val lcm_powers = store_thm(
  "lcm_powers",
  ``!b m n. lcm (b ** m) (b ** n) = b ** (MAX m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[LCM_REF] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, MAX_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, LCM_COMM, MAX_DEF]
  ]);

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n - 1)
      <=> T                                by coprime_PRE

   Claim: !j. j < m ==> coprime (b ** j) (b ** m - 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (PRE (b ** m))  by divides_imp_coprime_with_predecessor
       or coprime (b ** j) (b ** m - 1)    by PRE_SUB1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z - 1)                        by coprime_PRE
     ==> coprime (z ** (n DIV m)) (z - 1)         by coprime_exp
          gcd (b ** n) (b ** m - 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z - 1)
        = gcd (b ** (n MOD m)) (z - 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_predecessor = store_thm(
  "coprime_power_and_power_predecessor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_PRE] >>
  `!j. j < m ==> coprime (b ** j) (b ** m - 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_predecessor, PRE_SUB1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z - 1)` by rw[coprime_PRE] >>
  `coprime (z ** (n DIV m)) (z - 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* Any counter-example? Theorem proved, no counter-example! *)
(* This is a most unexpected theorem.
   At first I thought it only holds for prime base b,
   but in HOL4 using the EVAL function shows it seems to hold for any base b.
   As for the proof, I don't have a clue initially.
   I try this idea:
   For a prime base b, most likely ODD b, then ODD (b ** n) and ODD (b ** m).
   But then EVEN (b ** m - 1), maybe ODD and EVEN will give coprime.
   If base b is EVEN, then EVEN (b ** n) but ODD (b ** m - 1), so this can work.
   However, in general ODD and EVEN do not give coprime:  gcd 6 9 = 3.
   Of course, if ODD and EVEN arise from powers of same base, like this theorem, then true!
   Actually this follows from divides_imp_coprime_with_predecessor, sort of.
   This success inspires the following theorem.
*)

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n + 1)
      <=> T                                by coprime_SUC

   Claim: !j. j < m ==> coprime (b ** j) (b ** m + 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (SUC (b ** m))  by divides_imp_coprime_with_successor
       or coprime (b ** j) (b ** m + 1)    by ADD1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z + 1)                        by coprime_SUC
     ==> coprime (z ** (n DIV m)) (z + 1)         by coprime_exp
          gcd (b ** n) (b ** m + 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z + 1)
        = gcd (b ** (n MOD m)) (z + 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_successor = store_thm(
  "coprime_power_and_power_successor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_SUC] >>
  `!j. j < m ==> coprime (b ** j) (b ** m + 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_successor, ADD1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z + 1)` by rw[coprime_SUC] >>
  `coprime (z ** (n DIV m)) (z + 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* Note:
> type_of ``prime``;
val it = ":num -> bool": hol_type

Thus prime is also a set, or prime = {p | prime p}
*)

(* Theorem: p IN prime <=> prime p *)
(* Proof: by IN_DEF *)
val in_prime = store_thm(
  "in_prime",
  ``!p. p IN prime <=> prime p``,
  rw[IN_DEF]);

(* Theorem: PROD_SET {x} = x *)
(* Proof:
   Since FINITE {x}           by FINITE_SING
     PROD_SET {x}
   = PROD_SET (x INSERT {})   by SING_INSERT
   = x * PROD_SET {}          by PROD_SET_THM
   = x                        by PROD_SET_EMPTY
*)
val PROD_SET_SING = store_thm(
  "PROD_SET_SING",
  ``!x. PROD_SET {x} = x``,
  rw[PROD_SET_THM, FINITE_SING]);

(* Theorem: FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: 0 NOTIN {} ==> 0 < PROD_SET {}
     Since PROD_SET {} = 1        by PROD_SET_THM
     Hence true.
   Step case: 0 NOTIN s ==> 0 < PROD_SET s ==>
              e NOTIN s /\ 0 NOTIN e INSERT s ==> 0 < PROD_SET (e INSERT s)
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)          by PROD_SET_THM
     = e * PROD_SET s                     by DELETE_NON_ELEMENT
     But e IN e INSERT s                  by COMPONENT
     Hence e <> 0, or 0 < e               by implication
     and !x. x IN s ==> x IN (e INSERT s) by IN_INSERT
     Thus 0 < PROD_SET s                  by induction hypothesis
     Henec 0 < e * PROD_SET s             by ZERO_LESS_MULT
*)
val PROD_SET_NONZERO = store_thm(
  "PROD_SET_NONZERO",
  ``!s. FINITE s /\ 0 NOTIN s ==> 0 < PROD_SET s``,
  `!s. FINITE s ==> 0 NOTIN s ==> 0 < PROD_SET s` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[PROD_SET_THM] >>
  fs[] >>
  `0 < e` by decide_tac >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[ZERO_LESS_MULT]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==>
            !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: {} <> {} ==> PROD_SET {} < PROD_SET (IMAGE f {})
     True since {} <> {} is false.
   Step case: s <> {} /\ 0 NOTIN s ==> !f. INJ f s univ(:num) ==> PROD_SET s < PROD_SET (IMAGE f s) ==>
              e NOTIN s /\ e INSERT s <> {} /\ 0 NOTIN e INSERT s /\ INJ f (e INSERT s) univ(:num) ==>
              PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
     Note INJ f (e INSERT s) univ(:num)
      ==> INJ f s univ(:num) /\
          !y. y IN s /\ (f e = f y) ==> (e = y)   by INJ_INSERT
     First,
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)           by PROD_SET_THM
     = e * PROD_SET s                      by DELETE_NON_ELEMENT
     Next,
       FINITE (IMAGE f s)                  by IMAGE_FINITE
       f e NOTIN IMAGE f s                 by IN_IMAGE, e NOTIN s
       PROD_SET (IMAGE f (e INSERT s))
     = f e * PROD_SET (IMAGE f s)          by PROD_SET_IMAGE_REDUCTION

     If s = {},
        to show: e * PROD_SET {} < f e * PROD_SET {}    by IMAGE_EMPTY
        which is true since PROD_SET {} = 1             by PROD_SET_THM
             and e < f e                                by given
     If s <> {},
     Since e IN e INSERT s                              by COMPONENT
     Hence 0 < e                                        by e <> 0
     and !x. x IN s ==> x IN (e INSERT s)               by IN_INSERT
     Thus PROD_SET s < PROD_SET (IMAGE f s)             by induction hypothesis
       or e * PROD_SET s < e * PROD_SET (IMAGE f s)     by LT_MULT_LCANCEL, 0 < e
     Note 0 < PROD_SET (IMAGE f s)                      by IN_IMAGE, !x. x < f x /\ x <> 0
       so e * PROD_SET (IMAGE f s) < f e * PROD_SET (IMAGE f s) by LT_MULT_LCANCEL, e < f e
     Hence PROD_SET (e INSERT s) < PROD_SET (IMAGE f (e INSERT s))
*)
val PROD_SET_LESS = store_thm(
  "PROD_SET_LESS",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==>
   !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)``,
  `!s. FINITE s ==> s <> {} /\ 0 NOTIN s ==>
    !f. INJ f s univ(:num) /\ (!x. x < f x) ==> PROD_SET s < PROD_SET (IMAGE f s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  fs[INJ_INSERT] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `f e NOTIN IMAGE f s` by metis_tac[IN_IMAGE] >>
  `PROD_SET (IMAGE f (e INSERT s)) = f e * PROD_SET (IMAGE f s)` by rw[PROD_SET_IMAGE_REDUCTION] >>
  Cases_on `s = {}` >-
  rw[PROD_SET_SING, PROD_SET_THM] >>
  `0 < e` by decide_tac >>
  `PROD_SET s < PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET s < e * PROD_SET (IMAGE f s)` by rw[] >>
  `e * PROD_SET (IMAGE f s) < (f e) * PROD_SET (IMAGE f s)` by rw[] >>
  `(IMAGE f (e INSERT s)) = (f e INSERT IMAGE f s)` by rw[] >>
  metis_tac[LESS_TRANS]);

(* Theorem: FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s) *)
(* Proof:
   Since !m n. SUC m = SUC n <=> m = n      by INV_SUC
    thus INJ INJ SUC s univ(:num)           by INJ_DEF
   Hence the result follows                 by PROD_SET_LESS
*)
val PROD_SET_LESS_SUC = store_thm(
  "PROD_SET_LESS_SUC",
  ``!s. FINITE s /\ s <> {} /\ 0 NOTIN s ==> PROD_SET s < PROD_SET (IMAGE SUC s)``,
  rpt strip_tac >>
  (irule PROD_SET_LESS >> simp[]) >>
  rw[INJ_DEF]);

(* Theorem: FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: x IN {} /\ n divides x ==> n divides (PROD_SET {})
     True since x IN {} is false   by NOT_IN_EMPTY
   Step case: !n x. x IN s /\ n divides x ==> n divides (PROD_SET s) ==>
              e NOTIN s /\ x IN e INSERT s /\ n divides x ==> n divides (PROD_SET (e INSERT s))
       PROD_SET (e INSERT s)
     = e * PROD_SET (s DELETE e)   by PROD_SET_THM
     = e * PROD_SET s              by DELETE_NON_ELEMENT
     If x = e,
        n divides x
        means n divides e
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE, MULT_COMM
     If x <> e, x IN s             by IN_INSERT
        n divides (PROD_SET s)     by induction hypothesis
        hence n divides PROD_SET (e INSERT s)   by DIVIDES_MULTIPLE
*)
val PROD_SET_DIVISORS = store_thm(
  "PROD_SET_DIVISORS",
  ``!s. FINITE s ==> !n x. x IN s /\ n divides x ==> n divides (PROD_SET s)``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[NOT_IN_EMPTY] >>
  `PROD_SET (e INSERT s) = e * PROD_SET (s DELETE e)` by rw[PROD_SET_THM] >>
  `_ = e * PROD_SET s` by metis_tac[DELETE_NON_ELEMENT] >>
  `(x = e) \/ (x IN s)` by rw[GSYM IN_INSERT] >-
  metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[DIVIDES_MULTIPLE]);

(* Theorem: (Generalized Euclid's Lemma)
            If prime p divides a PROD_SET, it divides a member of the PROD_SET.
            FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b *)
(* Proof: by induction of the PROD_SET, apply Euclid's Lemma.
- P_EUCLIDES;
> val it =
    |- !p a b. prime p /\ p divides (a * b) ==> p divides a \/ p divides b : thm
   By finite induction on s.
   Base case: prime p /\ p divides (PROD_SET {}) ==> F
     Since PROD_SET {} = 1        by PROD_SET_THM
       and p divides 1 <=> p = 1  by DIVIDES_ONE
       but prime p ==> p <> 1     by NOT_PRIME_1
       This gives the contradiction.
   Step case: FINITE s /\ (!p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b) /\
              e NOTIN s /\ prime p /\ p divides (PROD_SET (e INSERT s)) ==>
              ?b. ((b = e) \/ b IN s) /\ p divides b
     Note PROD_SET (e INSERT s) = e * PROD_SET s   by PROD_SET_THM, DELETE_NON_ELEMENT, e NOTIN s.
     So prime p /\ p divides (PROD_SET (e INSERT s))
     ==> p divides e, or p divides (PROD_SET s)    by P_EUCLIDES
     If p divides e, just take b = e.
     If p divides (PROD_SET s), there is such b    by induction hypothesis
*)
val PROD_SET_EUCLID = store_thm(
  "PROD_SET_EUCLID",
  ``!s. FINITE s ==> !p. prime p /\ p divides (PROD_SET s) ==> ?b. b IN s /\ p divides b``,
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >-
  metis_tac[PROD_SET_EMPTY, DIVIDES_ONE, NOT_PRIME_1] >>
  `PROD_SET (e INSERT s) = e * PROD_SET s`
    by metis_tac[PROD_SET_THM, DELETE_NON_ELEMENT] >>
  Cases_on `p divides e` >-
  metis_tac[] >>
  metis_tac[P_EUCLIDES]);

(* Theorem: FINITE s /\ x IN s ==> x divides PROD_SET s *)
(* Proof:
   Note !n x. x IN s /\ n divides x
    ==> n divides PROD_SET s           by PROD_SET_DIVISORS
    Put n = x, and x divides x = T     by DIVIDES_REFL
    and the result follows.
*)
val PROD_SET_ELEMENT_DIVIDES = store_thm(
  "PROD_SET_ELEMENT_DIVIDES",
  ``!s x. FINITE s /\ x IN s ==> x divides PROD_SET s``,
  metis_tac[PROD_SET_DIVISORS, DIVIDES_REFL]);

(* Theorem: FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
            (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) <= PROD_SET (IMAGE g {})
      Note PROD_SET (IMAGE f {})
         = PROD_SET {}              by IMAGE_EMPTY
         = 1                        by PROD_SET_EMPTY
      Thus true.
   Step: !f g. (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s) ==>
        e NOTIN s /\ !x. x IN e INSERT s ==> f x <= g x ==>
        PROD_SET (IMAGE f (e INSERT s)) <= PROD_SET (IMAGE g (e INSERT s))
        Note INJ f s univ(:num)     by INJ_INSERT
         and INJ g s univ(:num)     by INJ_INSERT
         and f e NOTIN (IMAGE f s)  by IN_IMAGE
         and g e NOTIN (IMAGE g s)  by IN_IMAGE
       Applying LE_MONO_MULT2,
          PROD_SET (IMAGE f (e INSERT s))
        = PROD_SET (f e INSERT IMAGE f s)  by INSERT_IMAGE
        = f e * PROD_SET (IMAGE f s)       by PROD_SET_INSERT
       <= g e * PROD_SET (IMAGE f s)       by f e <= g e
       <= g e * PROD_SET (IMAGE g s)       by induction hypothesis
        = PROD_SET (g e INSERT IMAGE g s)  by PROD_SET_INSERT
        = PROD_SET (IMAGE g (e INSERT s))  by INSERT_IMAGE
*)
val PROD_SET_LESS_EQ = store_thm(
  "PROD_SET_LESS_EQ",
  ``!s. FINITE s ==> !f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
       (!x. x IN s ==> f x <= g x) ==> PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `f e <= g e` by rw[] >>
  `PROD_SET (IMAGE f s) <= PROD_SET (IMAGE g s)` by rw[] >>
  rw[PROD_SET_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET {} <= n ** CARD {}
      Note PROD_SET {}
         = 1             by PROD_SET_EMPTY
         = n ** 0        by EXP_0
         = n ** CARD {}  by CARD_EMPTY
   Step: !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x <= n ==> PROD_SET (e INSERT s) <= n ** CARD (e INSERT s)
      Note !x. (x = e) \/ x IN s ==> x <= n   by IN_INSERT
         PROD_SET (e INSERT s)
       = e * PROD_SET s          by PROD_SET_INSERT
      <= n * PROD_SET s          by e <= n
      <= n * (n ** CARD s)       by induction hypothesis
       = n ** (SUC (CARD s))     by EXP
       = n ** CARD (e INSERT s)  by CARD_INSERT, e NOTIN s
*)
val PROD_SET_LE_CONSTANT = store_thm(
  "PROD_SET_LE_CONSTANT",
  ``!s. FINITE s ==> !n. (!x. x IN s ==> x <= n) ==> PROD_SET s <= n ** CARD s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[] >>
  `e <= n /\ PROD_SET s <= n ** CARD s` by rw[] >>
  rw[PROD_SET_INSERT, EXP, CARD_INSERT, LE_MONO_MULT2]);

(* Theorem: FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\ (!x. x IN s ==> n <= f x * g x) ==>
            n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) *)
(* Proof:
   By finite induction on s.
   Base: n ** CARD {} <= PROD_SET (IMAGE f {}) * PROD_SET (IMAGE g {})
      Note n ** CARD {}
         = n ** 0           by CARD_EMPTY
         = 1                by EXP_0
       and PROD_SET (IMAGE f {})
         = PROD_SET {}      by IMAGE_EMPTY
         = 1                by PROD_SET_EMPTY
   Step: !n f. INJ f s univ(:num) /\ INJ g s univ(:num) /\
               (!x. x IN s ==> n <= f x * g x) ==>
               n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) /\ INJ g (e INSERT s) univ(:num) /\
         !x. x IN e INSERT s ==> n <= f x * g x ==>
         n ** CARD (e INSERT s) <= PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
      Note INJ f s univ(:num) /\ INJ g s univ(:num)         by INJ_INSERT
       and f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)   by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s)) * PROD_SET (IMAGE g (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s)) * PROD_SET (g e INSERT (IMAGE g s))   by INSERT_IMAGE
       = (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))    by PROD_SET_INSERT
       = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))    by MULT_ASSOC, MULT_COMM
       >= n        * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))      by n <= f e * g e
       >= n        * n ** CARD s                                        by induction hypothesis
        = n ** (SUC (CARD s))                               by EXP
        = n ** (CARD (e INSERT s))                          by CARD_INSERT
*)
val PROD_SET_PRODUCT_GE_CONSTANT = store_thm(
  "PROD_SET_PRODUCT_GE_CONSTANT",
  ``!s. FINITE s ==> !n f g. INJ f s univ(:num) /\ INJ g s univ(:num) /\
                    (!x. x IN s ==> n <= f x * g x) ==>
       n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, EXP_0] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s) /\ g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `n <= f e * g e /\ n ** CARD s <= PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s)` by rw[] >>
  `PROD_SET (f e INSERT IMAGE f s) * PROD_SET (g e INSERT IMAGE g s) =
    (f e * PROD_SET (IMAGE f s)) * (g e * PROD_SET (IMAGE g s))` by rw[PROD_SET_INSERT] >>
  `_ = (f e * g e) * (PROD_SET (IMAGE f s) * PROD_SET (IMAGE g s))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[EXP, CARD_INSERT, LE_MONO_MULT2]);

(* ------------------------------------------------------------------------- *)
(* Pairwise Coprime Property                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload pairwise coprime set *)
val _ = overload_on("PAIRWISE_COPRIME", ``\s. !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y``);

(* Theorem: e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
            (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s *)
(* Proof: by IN_INSERT *)
val pairwise_coprime_insert = store_thm(
  "pairwise_coprime_insert",
  ``!s e. e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
        (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s``,
  metis_tac[IN_INSERT]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s) *)
(* Proof:
   Note FINITE t    by SUBSET_FINITE
   By finite induction on t.
   Base case: PROD_SET {} divides PROD_SET s
      Note PROD_SET {} = 1           by PROD_SET_EMPTY
       and 1 divides (PROD_SET s)    by ONE_DIVIDES_ALL
   Step case: t SUBSET s ==> PROD_SET t divides PROD_SET s ==>
              e NOTIN t /\ e INSERT t SUBSET s ==> PROD_SET (e INSERT t) divides PROD_SET s
      Let m = PROD_SET s.
      Note e IN s /\ t SUBSET s                      by INSERT_SUBSET
      Thus e divides m                               by PROD_SET_ELEMENT_DIVIDES
       and (PROD_SET t) divides m                    by induction hypothesis
      Also coprime e (PROD_SET t)                    by every_coprime_prod_set_coprime, SUBSET_DEF
      Note PROD_SET (e INSERT t) = e * PROD_SET t    by PROD_SET_INSERT
       ==> e * PROD_SET t divides m                  by coprime_product_divides
*)
val pairwise_coprime_prod_set_subset_divides = store_thm(
  "pairwise_coprime_prod_set_subset_divides",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s)``,
  rpt strip_tac >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  qpat_x_assum `t SUBSET s` mp_tac >>
  qpat_x_assum `FINITE t` mp_tac >>
  qid_spec_tac `t` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  `e divides PROD_SET s` by rw[PROD_SET_ELEMENT_DIVIDES] >>
  `coprime e (PROD_SET t)` by prove_tac[every_coprime_prod_set_coprime, SUBSET_DEF] >>
  rw[PROD_SET_INSERT, coprime_product_divides]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true                   by GCD_1
   Step: PAIRWISE_COPRIME s ==>
         !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note (!x. x IN s ==> coprime e x) /\
           PAIRWISE_COPRIME s      by IN_INSERT
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT

         Note coprime (PROD_SET w) (PROD_SET v)   by induction hypothesis
          and !x. x IN v ==> coprime e x          by v SUBSET s
         Also FINITE v                            by FINITE_UNION
           so coprime e (PROD_SET v)              by every_coprime_prod_set_coprime, FINITE v
          ==> coprime (e * PROD_SET w) PROD_SET v         by coprime_product_coprime
           or coprime PROD_SET (e INSERT w) PROD_SET v    by PROD_SET_INSERT
            = coprime PROD_SET u PROD_SET v               by above

      Similarly for e IN v.
*)
val pairwise_coprime_partition_coprime = store_thm(
  "pairwise_coprime_partition_coprime",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v)``,
  ntac 2 strip_tac >>
  qpat_x_assum `PAIRWISE_COPRIME s` mp_tac >>
  qpat_x_assum `FINITE s` mp_tac >>
  qid_spec_tac `s` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `(!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s` by metis_tac[IN_INSERT] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `coprime (PROD_SET w) (PROD_SET v)` by rw[] >>
    `(!x. x IN v ==> coprime e x)` by rw[] >>
    `FINITE v` by metis_tac[FINITE_UNION] >>
    `coprime e (PROD_SET v)` by rw[every_coprime_prod_set_coprime] >>
    metis_tac[coprime_product_coprime, PROD_SET_INSERT],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `coprime (PROD_SET u) (PROD_SET w)` by rw[] >>
    `(!x. x IN u ==> coprime e x)` by rw[] >>
    `FINITE u` by metis_tac[FINITE_UNION] >>
    `coprime (PROD_SET u) e` by rw[every_coprime_prod_set_coprime, coprime_sym] >>
    metis_tac[coprime_product_coprime_sym, PROD_SET_INSERT]
  ]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
            (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v)) *)
(* Proof: by PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime *)
val pairwise_coprime_prod_set_partition = store_thm(
  "pairwise_coprime_prod_set_partition",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
       (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v))``,
  metis_tac[PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime]);

(* Theorem: n! = PROD_SET (count (n+1))  *)
(* Proof: by induction on n.
   Base case: FACT 0 = PROD_SET (IMAGE SUC (count 0))
     LHS = FACT 0
         = 1                               by FACT
         = PROD_SET {}                     by PROD_SET_THM
         = PROD_SET (IMAGE SUC {})         by IMAGE_EMPTY
         = PROD_SET (IMAGE SUC (count 0))  by COUNT_ZERO
         = RHS
   Step case: FACT n = PROD_SET (IMAGE SUC (count n)) ==>
              FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n)))
     Note: (SUC n) NOTIN (IMAGE SUC (count n))  by IN_IMAGE, IN_COUNT [1]
     LHS = FACT (SUC n)
         = (SUC n) * (FACT n)                            by FACT
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)))    by induction hypothesis
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)) DELETE (SUC n))         by DELETE_NON_ELEMENT, [1]
         = PROD_SET ((SUC n) INSERT ((IMAGE SUC (count n)) DELETE (SUC n)))  by PROD_SET_THM
         = PROD_SET (IMAGE SUC (n INSERT (count n)))     by IMAGE_INSERT
         = PROD_SET (IMAGE SUC (count (SUC n)))          by COUNT_SUC
         = RHS
*)
val FACT_EQ_PROD = store_thm(
  "FACT_EQ_PROD",
  ``!n. FACT n = PROD_SET (IMAGE SUC (count n))``,
  Induct_on `n` >-
  rw[PROD_SET_THM, FACT] >>
  rw[PROD_SET_THM, FACT, COUNT_SUC] >>
  `(SUC n) NOTIN (IMAGE SUC (count n))` by rw[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: n!/m! = product of (m+1) to n.
            m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m)) *)
(* Proof: by factorial formula.
   By induction on n.
   Base case: m < 0 ==> ...
     True since m < 0 = F.
   Step case: !m. m < n ==>
              (FACT n = PROD_SET (IMAGE SUC (count n DIFF count m)) * FACT m) ==>
              !m. m < SUC n ==>
              (FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m)
     Note that m < SUC n ==> m <= n.
      and FACT (SUC n) = (SUC n) * FACT n     by FACT
     If m = n,
        PROD_SET (IMAGE SUC (count (SUC n) DIFF count n)) * FACT n
      = PROD_SET (IMAGE SUC {n}) * FACT n     by IN_DIFF, IN_COUNT
      = PROD_SET {SUC n} * FACT n             by IN_IMAGE
      = (SUC n) * FACT n                      by PROD_SET_THM
     If m < n,
        n NOTIN (count m)                     by IN_COUNT
     so n INSERT ((count n) DIFF (count m))
      = (n INSERT (count n)) DIFF (count m)   by INSERT_DIFF
      = count (SUC n) DIFF (count m)          by EXTENSION
     Since (SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))  by IN_IMAGE, IN_DIFF, IN_COUNT
       and FINITE (IMAGE SUC ((count n) DIFF (count m)))         by IMAGE_FINITE, FINITE_DIFF, FINITE_COUNT
     Hence PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m
         = ((SUC n) * PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m   by PROD_SET_IMAGE_REDUCTION
         = (SUC n) * (PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m)  by MULT_ASSOC
         = (SUC n) * FACT n                                      by induction hypothesis
         = FACT (SUC n)                                          by FACT
*)
val FACT_REDUCTION = store_thm(
  "FACT_REDUCTION",
  ``!n m. m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m))``,
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[FACT] >>
  `m <= n` by decide_tac >>
  Cases_on `m = n` >| [
    rw_tac std_ss[] >>
    `count (SUC m) DIFF count m = {m}` by
  (rw[DIFF_DEF] >>
    rw[EXTENSION, EQ_IMP_THM]) >>
    `PROD_SET (IMAGE SUC {m}) = SUC m` by rw[PROD_SET_THM] >>
    metis_tac[],
    `m < n` by decide_tac >>
    `n NOTIN (count m)` by srw_tac[ARITH_ss][] >>
    `n INSERT ((count n) DIFF (count m)) = (n INSERT (count n)) DIFF (count m)` by rw[] >>
    `_ = count (SUC n) DIFF (count m)` by srw_tac[ARITH_ss][EXTENSION] >>
    `(SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    `FINITE (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    metis_tac[PROD_SET_IMAGE_REDUCTION, MULT_ASSOC]
  ]);

(* ------------------------------------------------------------------------- *)
(* Logic Theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A)) *)
(* Proof: by logic. *)
val EQ_IMP2_THM = store_thm(
  "EQ_IMP2_THM",
  ``!A B. (A <=> B) <=> (A ==> B) /\ ((A ==> B) ==> (B ==> A))``,
  metis_tac[]);

(* Theorem: (b1 = b2) ==> (f b1 = f b2) *)
(* Proof: by substitution. *)
val BOOL_EQ = store_thm(
  "BOOL_EQ",
  ``!b1:bool b2:bool f. (b1 = b2) ==> (f b1 = f b2)``,
  simp[]);

(* Theorem: b /\ (c ==> d) ==> ((b ==> c) ==> d) *)
(* Proof: by logical implication. *)
val AND_IMP_IMP = store_thm((* was: IMP_IMP *)
  "AND_IMP_IMP",
  ``!b c d. b /\ (c ==> d) ==> ((b ==> c) ==> d)``,
  metis_tac[]);

(* Theorem: p /\ q ==> p \/ ~q *)
(* Proof:
   Note p /\ q ==> p          by AND1_THM
    and p ==> p \/ ~q         by OR_INTRO_THM1
   Thus p /\ q ==> p \/ ~q
*)
val AND_IMP_OR_NEG = store_thm(
  "AND_IMP_OR_NEG",
  ``!p q. p /\ q ==> p \/ ~q``,
  metis_tac[]);

(* Theorem: (p \/ q ==> r) ==> (p /\ ~q ==> r) *)
(* Proof:
       (p \/ q) ==> r
     = ~(p \/ q) \/ r      by IMP_DISJ_THM
     = (~p /\ ~q) \/ r     by DE_MORGAN_THM
   ==> (~p \/ q) \/ r      by AND_IMP_OR_NEG
     = ~(p /\ ~q) \/ r     by DE_MORGAN_THM
     = (p /\ ~q) ==> r     by IMP_DISJ_THM
*)
val OR_IMP_IMP = store_thm(
  "OR_IMP_IMP",
  ``!p q r. ((p \/ q) ==> r) ==> ((p /\ ~q) ==> r)``,
  metis_tac[]);

(* Theorem: x IN (if b then s else t) <=> if b then x IN s else x IN t *)
(* Proof: by boolTheory.COND_RAND:
   |- !f b x y. f (if b then x else y) = if b then f x else f y
*)
val PUSH_IN_INTO_IF = store_thm(
  "PUSH_IN_INTO_IF",
  ``!b x s t. x IN (if b then s else t) <=> if b then x IN s else x IN t``,
  rw_tac std_ss[]);

(* ------------------------------------------------------------------------- *)
(* More Theorems and Sets for Counting                                       *)
(* ------------------------------------------------------------------------- *)

(* Have simple (count n) *)

(* Theorem: count 1 = {0} *)
(* Proof: rename COUNT_ZERO *)
val COUNT_0 = save_thm("COUNT_0", COUNT_ZERO);
(* val COUNT_0 = |- count 0 = {}: thm *)

(* Theorem: count 1 = {0} *)
(* Proof: by count_def, EXTENSION *)
val COUNT_1 = store_thm(
  "COUNT_1",
  ``count 1 = {0}``,
  rw[count_def, EXTENSION]);

(* Theorem: n NOTIN (count n) *)
(* Proof: by IN_COUNT *)
val COUNT_NOT_SELF = store_thm(
  "COUNT_NOT_SELF",
  ``!n. n NOTIN (count n)``,
  rw[]);

(* Theorem: m <= n ==> count m SUBSET count n *)
(* Proof: by LENGTH_TAKE_EQ *)
val COUNT_SUBSET = store_thm(
  "COUNT_SUBSET",
  ``!m n. m <= n ==> count m SUBSET count n``,
  rw[SUBSET_DEF]);

(* Theorem: count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t *)
(* Proof:
       count (SUC n) SUBSET t
   <=> (n INSERT count n) SUBSET t     by COUNT_SUC
   <=> n IN t /\ (count n) SUBSET t    by INSERT_SUBSET
   <=> (count n) SUBSET t /\ n IN t    by CONJ_COMM
*)
val COUNT_SUC_SUBSET = store_thm(
  "COUNT_SUC_SUBSET",
  ``!n t. count (SUC n) SUBSET t <=> count n SUBSET t /\ n IN t``,
  metis_tac[COUNT_SUC, INSERT_SUBSET]);

(* Theorem: t DIFF (count (SUC n)) = t DIFF (count n) DELETE n *)
(* Proof:
     t DIFF (count (SUC n))
   = t DIFF (n INSERT count n)    by COUNT_SUC
   = t DIFF (count n) DELETE n    by EXTENSION
*)
val DIFF_COUNT_SUC = store_thm(
  "DIFF_COUNT_SUC",
  ``!n t. t DIFF (count (SUC n)) = t DIFF (count n) DELETE n``,
  rw[EXTENSION, EQ_IMP_THM]);

(* COUNT_SUC  |- !n. count (SUC n) = n INSERT count n *)

(* Theorem: count (SUC n) = 0 INSERT (IMAGE SUC (count n)) *)
(* Proof: by EXTENSION *)
val COUNT_SUC_BY_SUC = store_thm(
  "COUNT_SUC_BY_SUC",
  ``!n. count (SUC n) = 0 INSERT (IMAGE SUC (count n))``,
  rw[EXTENSION, EQ_IMP_THM] >>
  (Cases_on `x` >> simp[]));

(* Theorem: IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (n INSERT (count n))    by COUNT_SUC
   = f n INSERT IMAGE f (count n)    by IMAGE_INSERT
*)
val IMAGE_COUNT_SUC = store_thm(
  "IMAGE_COUNT_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f n) INSERT IMAGE f (count n)``,
  rw[COUNT_SUC]);

(* Theorem: IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n) *)
(* Proof:
     IMAGE f (count (SUC n))
   = IMAGE f (0 INSERT (IMAGE SUC (count n)))    by COUNT_SUC_BY_SUC
   = f 0 INSERT IMAGE f (IMAGE SUC (count n))    by IMAGE_INSERT
   = f 0 INSERT IMAGE (f o SUC) (count n)        by IMAGE_COMPOSE
*)
val IMAGE_COUNT_SUC_BY_SUC = store_thm(
  "IMAGE_COUNT_SUC_BY_SUC",
  ``!f n. IMAGE f (count (SUC n)) = (f 0) INSERT IMAGE (f o SUC) (count n)``,
  rw[COUNT_SUC_BY_SUC, IMAGE_COMPOSE]);

(* Introduce countFrom m n, the set {m, m + 1, m + 2, ...., m + n - 1} *)
val _ = overload_on("countFrom", ``\m n. IMAGE ($+ m) (count n)``);

(* Theorem: countFrom m 0 = {} *)
(* Proof:
     countFrom m 0
   = IMAGE ($+ m) (count 0)     by notation
   = IMAGE ($+ m) {}            by COUNT_0
   = {}                         by IMAGE_EMPTY
*)
val countFrom_0 = store_thm(
  "countFrom_0",
  ``!m. countFrom m 0 = {}``,
  rw[]);

(* Theorem: countFrom m (SUC n) = m INSERT countFrom (m + 1) n *)
(* Proof: by IMAGE_COUNT_SUC_BY_SUC *)
val countFrom_SUC = store_thm(
  "countFrom_SUC",
  ``!m n. !m n. countFrom m (SUC n) = m INSERT countFrom (m + 1) n``,
  rpt strip_tac >>
  `$+ m o SUC = $+ (m + 1)` by rw[FUN_EQ_THM] >>
  rw[IMAGE_COUNT_SUC_BY_SUC]);

(* Theorem: 0 < n ==> m IN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_first = store_thm(
  "countFrom_first",
  ``!m n. 0 < n ==> m IN countFrom m n``,
  rw[] >>
  metis_tac[ADD_0]);

(* Theorem: x < m ==> x NOTIN countFrom m n *)
(* Proof: by IN_COUNT *)
val countFrom_less = store_thm(
  "countFrom_less",
  ``!m n x. x < m ==> x NOTIN countFrom m n``,
  rw[]);

(* Theorem: count n = countFrom 0 n *)
(* Proof: by EXTENSION *)
val count_by_countFrom = store_thm(
  "count_by_countFrom",
  ``!n. count n = countFrom 0 n``,
  rw[EXTENSION]);

(* Theorem: count (SUC n) = 0 INSERT countFrom 1 n *)
(* Proof:
      count (SUC n)
   = 0 INSERT IMAGE SUC (count n)     by COUNT_SUC_BY_SUC
   = 0 INSERT IMAGE ($+ 1) (count n)  by FUN_EQ_THM
   = 0 INSERT countFrom 1 n           by notation
*)
val count_SUC_by_countFrom = store_thm(
  "count_SUC_by_countFrom",
  ``!n. count (SUC n) = 0 INSERT countFrom 1 n``,
  rpt strip_tac >>
  `SUC = $+ 1` by rw[FUN_EQ_THM] >>
  rw[COUNT_SUC_BY_SUC]);

(* Inclusion-Exclusion for two sets:

CARD_UNION
|- !s. FINITE s ==> !t. FINITE t ==>
       (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)
CARD_UNION_EQN
|- !s t. FINITE s /\ FINITE t ==>
         (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t))
CARD_UNION_DISJOINT
|- !s t. FINITE s /\ FINITE t /\ DISJOINT s t ==>
         (CARD (s UNION t) = CARD s + CARD t)
*)

(* Inclusion-Exclusion for three sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c ==>
            (CARD (a UNION b UNION c) =
             CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
             CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)) *)
(* Proof:
   Note FINITE (a UNION b)                            by FINITE_UNION
    and FINITE (a INTER c)                            by FINITE_INTER
    and FINITE (b INTER c)                            by FINITE_INTER
   Also (a INTER c) INTER (b INTER c)
       = a INTER b INTER c                            by EXTENSION
    and CARD (a INTER b) <= CARD a                    by CARD_INTER_LESS_EQ
    and CARD (a INTER b INTER c) <= CARD (b INTER c)  by CARD_INTER_LESS_EQ, INTER_COMM

        CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)
                                                      by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)          by CARD_UNION_EQN
      = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))
                                                      by UNION_OVER_INTER
      = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD ((a INTER c) INTER (b INTER c)))
                                                      by CARD_UNION_EQN
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))
                                                      by CARD (a INTER b) <= CARD a
      = CARD a + CARD b + CARD c - CARD (a INTER b) -
        (CARD (b INTER c) + CARD (a INTER c) - CARD (a INTER b INTER c))
                                                      by ADD_COMM
      = CARD a + CARD b + CARD c - CARD (a INTER b)
        + CARD (a INTER b INTER c) - CARD (b INTER c) - CARD (a INTER c)
                                                      by CARD (a INTER b INTER c) <= CARD (b INTER c)
      = CARD a + CARD b + CARD c + CARD (a INTER b INTER c)
        - CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)
                                                      by arithmetic
*)
Theorem CARD_UNION_3_EQN:
  !a b c. FINITE a /\ FINITE b /\ FINITE c ==>
          (CARD (a UNION b UNION c) =
           CARD a + CARD b + CARD c + CARD (a INTER b INTER c) -
           CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c))
Proof
  rpt strip_tac >>
  `FINITE (a UNION b) /\ FINITE (a INTER c) /\ FINITE (b INTER c)` by rw[] >>
  (`(a INTER c) INTER (b INTER c) = a INTER b INTER c` by (rw[EXTENSION] >> metis_tac[])) >>
  `CARD (a INTER b) <= CARD a` by rw[CARD_INTER_LESS_EQ] >>
  `CARD (a INTER b INTER c) <= CARD (b INTER c)` by metis_tac[INTER_COMM, CARD_INTER_LESS_EQ] >>
  `CARD (a UNION b UNION c)
      = CARD (a UNION b) + CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a UNION b) INTER c)` by rw[CARD_UNION_EQN] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) +
         CARD c - CARD ((a INTER c) UNION (b INTER c))` by fs[UNION_OVER_INTER, INTER_COMM] >>
  `_ = (CARD a + CARD b - CARD (a INTER b)) + CARD c -
        (CARD (a INTER c) + CARD (b INTER c) - CARD (a INTER b INTER c))` by metis_tac[CARD_UNION_EQN] >>
  decide_tac
QED

(* Simplification of the above result for 3 disjoint sets. *)

(* Theorem: FINITE a /\ FINITE b /\ FINITE c /\
            DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
            (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c) *)
(* Proof: by DISJOINT_DEF, CARD_UNION_3_EQN *)
Theorem CARD_UNION_3_DISJOINT:
  !a b c. FINITE a /\ FINITE b /\ FINITE c /\
           DISJOINT a b /\ DISJOINT b c /\ DISJOINT a c ==>
           (CARD (a UNION b UNION c) = CARD a + CARD b + CARD c)
Proof
  rw[DISJOINT_DEF] >>
  rw[CARD_UNION_3_EQN]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and Minimum of a Set                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s) *)
(* Proof:
   Let m = MIN_SET s, t = s DELETE m.
    Then t SUBSET s              by DELETE_SUBSET
      so FINITE t                by SUBSET_FINITE]);
   Since m IN s                  by MIN_SET_IN_SET
      so t <> {}                 by DELETE_EQ_SING, s <> {m}
     ==> ?x. x IN t              by MEMBER_NOT_EMPTY
     and x IN s /\ x <> m        by IN_DELETE
    From x IN s ==> m <= x       by MIN_SET_PROPERTY
    With x <> m ==> m < x        by LESS_OR_EQ
    Also x <= MAX_SET s          by MAX_SET_PROPERTY
    Thus MAX_SET s <> m          since m < x <= MAX_SET s
     But MAX_SET s IN s          by MAX_SET_IN_SET
    Thus MAX_SET s IN t          by IN_DELETE
     Now !y. y IN t ==>
             y IN s              by SUBSET_DEF
          or y <= MAX_SET s      by MAX_SET_PROPERTY
   Hence MAX_SET s = MAX_SET t   by MAX_SET_TEST
*)
val MAX_SET_DELETE = store_thm(
  "MAX_SET_DELETE",
  ``!s. FINITE s /\ s <> {} /\ s <> {MIN_SET s} ==> (MAX_SET (s DELETE (MIN_SET s)) = MAX_SET s)``,
  rpt strip_tac >>
  qabbrev_tac `m = MIN_SET s` >>
  qabbrev_tac `t = s DELETE m` >>
  `t SUBSET s` by rw[Abbr`t`] >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  `t <> {}` by metis_tac[MIN_SET_IN_SET, DELETE_EQ_SING] >>
  `?x. x IN t /\ x IN s /\ x <> m` by metis_tac[IN_DELETE, MEMBER_NOT_EMPTY] >>
  `m <= x` by rw[MIN_SET_PROPERTY, Abbr`m`] >>
  `m < x` by decide_tac >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MAX_SET s <> m` by decide_tac >>
  `MAX_SET s IN t` by rw[MAX_SET_IN_SET, Abbr`t`] >>
  metis_tac[SUBSET_DEF, MAX_SET_PROPERTY, MAX_SET_TEST]);

(* Theorem: MAX_SET (IMAGE SUC (count n)) = n *)
(* Proof:
   By induction on n.
   Base case: MAX_SET (IMAGE SUC (count 0)) = 0
      LHS = MAX_SET (IMAGE SUC (count 0))
          = MAX_SET (IMAGE SUC {})       by COUNT_ZERO
          = MAX_SET {}                   by IMAGE_EMPTY
          = 0                            by MAX_SET_THM
          = RHS
   Step case: MAX_SET (IMAGE SUC (count n)) = n ==>
              MAX_SET (IMAGE SUC (count (SUC n))) = SUC n
      LHS = MAX_SET (IMAGE SUC (count (SUC n)))
          = MAX_SET (IMAGE SUC (n INSERT count n))           by COUNT_SUC
          = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))   by IMAGE_INSERT
          = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))      by MAX_SET_THM
          = MAX (SUC n) n                                    by induction hypothesis
          = SUC n                                            by LESS_SUC, MAX_DEF
          = RHS
*)
Theorem MAX_SET_IMAGE_SUC_COUNT:
  !n. MAX_SET (IMAGE SUC (count n)) = n
Proof
  Induct_on ‘n’ >-
  rw[] >>
  ‘MAX_SET (IMAGE SUC (count (SUC n))) =
   MAX_SET (IMAGE SUC (n INSERT count n))’ by rw[COUNT_SUC] >>
  ‘_ = MAX_SET ((SUC n) INSERT (IMAGE SUC (count n)))’ by rw[] >>
  ‘_ = MAX (SUC n) (MAX_SET (IMAGE SUC (count n)))’ by rw[MAX_SET_THM] >>
  ‘_ = MAX (SUC n) n’ by rw[] >>
  ‘_ = SUC n’ by metis_tac[LESS_SUC, MAX_DEF, MAX_COMM] >>
  rw[]
QED

(* Theorem: HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c} *)
(* Proof:
   Let s = {f x | HALF x <= c}
   Note !x. HALF x <= c
    ==> SUC (2 * HALF x) <= SUC (2 * c)         by arithmetic
    and x <= SUC (2 * HALF x)                   by TWO_HALF_LE_THM
     so x <= SUC (2 * c) < 2 * c + 2            by arithmetic
   Thus s SUBSET (IMAGE f (count (2 * c + 2)))  by SUBSET_DEF
   Note FINITE (count (2 * c + 2))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_HALF = store_thm(
  "MAX_SET_IMAGE_with_HALF",
  ``!f c x. HALF x <= c ==> f x <= MAX_SET {f x | HALF x <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | HALF x <= c}` >>
  `s SUBSET (IMAGE f (count (2 * c + 2)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `SUC (2 * HALF x'') <= SUC (2 * c)` by rw[] >>
  `x'' <= SUC (2 * HALF x'')` by rw[TWO_HALF_LE_THM] >>
  `x'' < 2 * c + 2` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(*
Note: A more general version, replacing HALF x by g x, would be desirable.
However, there is no way to show FINITE s for arbitrary g x.
*)

(* Theorem: 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c} *)
(* Proof:
   Let s = {f x | x DIV b <= c}.
   Note !x. x DIV b <= c
    ==> b * SUC (x DIV b) <= b * SUC c          by arithmetic
    and x < b * SUC (x DIV b)                   by DIV_MULT_LESS_EQ, 0 < b
     so x < b * SUC c                           by arithmetic
   Thus s SUBSET (IMAGE f (count (b * SUC c)))  by SUBSET_DEF
   Note FINITE (count (b * SUC c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by HALF x <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DIV = store_thm(
  "MAX_SET_IMAGE_with_DIV",
  ``!f b c x. 0 < b /\ x DIV b <= c ==> f x <= MAX_SET {f x | x DIV b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x DIV b <= c}` >>
  `s SUBSET (IMAGE f (count (b * SUC c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `b * SUC (x'' DIV b) <= b * SUC c` by rw[] >>
  `x'' < b * SUC (x'' DIV b)` by rw[DIV_MULT_LESS_EQ] >>
  `x'' < b * SUC c` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  (`f x IN s` by (rw[Abbr`s`] >> metis_tac[])) >>
  rw[MAX_SET_PROPERTY]);

(* Theorem: x - b <= c ==> f x <= MAX_SET {f x | x - b <= c} *)
(* Proof:
   Let s = {f x | x - b <= c}
   Note !x. x - b <= c ==> x <= b + c           by arithmetic
     so x <= 1 + b + c                          by arithmetic
   Thus s SUBSET (IMAGE f (count (1 + b + c)))  by SUBSET_DEF
   Note FINITE (count (1 + b + c))              by FINITE_COUNT
     so FINITE s                                by IMAGE_FINITE, SUBSET_FINITE
    and f x IN s                                by x - b <= c
   Thus f x <= MAX_SET s                        by MAX_SET_PROPERTY
*)
val MAX_SET_IMAGE_with_DEC = store_thm(
  "MAX_SET_IMAGE_with_DEC",
  ``!f b c x. x - b <= c ==> f x <= MAX_SET {f x | x - b <= c}``,
  rpt strip_tac >>
  qabbrev_tac `s = {f x | x - b <= c}` >>
  `s SUBSET (IMAGE f (count (1 + b + c)))` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `x'' < b + (c + 1)` by decide_tac >>
  metis_tac[]) >>
  `FINITE s` by metis_tac[FINITE_COUNT, IMAGE_FINITE, SUBSET_FINITE] >>
  `f x IN s` by
    (rw[Abbr`s`] >>
  `x <= b + c` by decide_tac >>
  metis_tac[]) >>
  rw[MAX_SET_PROPERTY]);

(* ------------------------------------------------------------------------- *)
(* Finite and Cardinality Theorems                                           *)
(* ------------------------------------------------------------------------- *)


(* Theorem: INJ f s UNIV /\ FINITE s ==> CARD (IMAGE f s) = CARD s *)
(* Proof:
   !x y. x IN s /\ y IN s /\ f x = f y == x = y   by INJ_DEF
   FINITE s ==> FINITE (IMAGE f s)                by IMAGE_FINITE
   Therefore   BIJ f s (IMAGE f s)                by BIJ_DEF, INJ_DEF, SURJ_DEF
   Hence       CARD (IMAGE f s) = CARD s          by FINITE_BIJ_CARD_EQ
*)
val INJ_CARD_IMAGE_EQN = store_thm(
  "INJ_CARD_IMAGE_EQN",
  ``!f s. INJ f s UNIV /\ FINITE s ==> (CARD (IMAGE f s) = CARD s)``,
  rw[INJ_DEF] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `BIJ f s (IMAGE f s)` by rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[FINITE_BIJ_CARD_EQ]);


(* Theorem: FINTIE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> SURJ f s t *)
(* Proof:
   For any map f from s to t,
   (IMAGE f s) SUBSET t            by IMAGE_SUBSET_TARGET
   FINITE s ==> FINITE (IMAGE f s) by IMAGE_FINITE
   CARD (IMAGE f s) = CARD s       by INJ_CARD_IMAGE
                    = CARD t       by given
   Hence (IMAGE f s) = t           by SUBSET_EQ_CARD, FINITE t
   or SURJ f s t                   by IMAGE_SURJ
*)
val FINITE_INJ_AS_SURJ = store_thm(
  "FINITE_INJ_AS_SURJ",
  ``!f s t. INJ f s t /\ FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> SURJ f s t``,
  rw[INJ_DEF] >>
  `(IMAGE f s) SUBSET t` by rw[GSYM IMAGE_SUBSET_TARGET] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `CARD (IMAGE f s) = CARD t` by metis_tac[INJ_DEF, INJ_CARD_IMAGE, INJ_SUBSET, SUBSET_REFL, SUBSET_UNIV] >>
  rw[SUBSET_EQ_CARD, IMAGE_SURJ]);

(* Reformulate theorem *)

(* Theorem: FINITE s /\ FINITE t /\ CARD s = CARD t /\
            INJ f s t ==> SURJ f s t *)
(* Proof: by FINITE_INJ_AS_SURJ *)
Theorem FINITE_INJ_IS_SURJ:
  !f s t. FINITE s /\ FINITE t /\ CARD s = CARD t /\
          INJ f s t ==> SURJ f s t
Proof
  simp[FINITE_INJ_AS_SURJ]
QED

(* Theorem: FINITE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> BIJ f s t *)
(* Proof:
   Note SURJ f s t             by FINITE_INJ_IS_SURJ
     so BIJ f s t              by BIJ_DEF, INJ f s t
*)
Theorem FINITE_INJ_IS_BIJ:
  !f s t. FINITE s /\ FINITE t /\ CARD s = CARD t /\ INJ f s t ==> BIJ f s t
Proof
  simp[FINITE_INJ_IS_SURJ, BIJ_DEF]
QED

(* Note: FINITE_SURJ_IS_BIJ is not easy, see helperFunction. *)

(* Theorem: FINITE {P x | x < n}  *)
(* Proof:
   Since IMAGE (\i. P i) (count n) = {P x | x < n},
   this follows by
   IMAGE_FINITE  |- !s. FINITE s ==> !f. FINITE (IMAGE f s) : thm
   FINITE_COUNT  |- !n. FINITE (count n) : thm
*)
val FINITE_COUNT_IMAGE = store_thm(
  "FINITE_COUNT_IMAGE",
  ``!P n. FINITE {P x | x < n }``,
  rpt strip_tac >>
  `IMAGE (\i. P i) (count n) = {P x | x < n}` by rw[IMAGE_DEF] >>
  metis_tac[IMAGE_FINITE, FINITE_COUNT]);

(* Idea: improve FINITE_BIJ_COUNT to include CARD information. *)

(* Theorem: FINITE s ==> ?f. BIJ f (count (CARD s)) s *)
(* Proof:
   Note ?f b. BIJ f (count b) s    by FINITE_BIJ_COUNT
    and FINITE (count b)           by FINITE_COUNT
     so CARD s
      = CARD (count b)             by FINITE_BIJ
      = b                          by CARD_COUNT
*)
Theorem FINITE_BIJ_COUNT_CARD:
  !s. FINITE s ==> ?f. BIJ f (count (CARD s)) s
Proof
  rpt strip_tac >>
  imp_res_tac FINITE_BIJ_COUNT >>
  metis_tac[FINITE_COUNT, CARD_COUNT, FINITE_BIJ]
QED

(* Theorem: !n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n) *)
(* Proof: by SUBSET_DEF, MOD_LESS. *)
val image_mod_subset_count = store_thm(
  "image_mod_subset_count",
  ``!s n. 0 < n ==> IMAGE (\x. x MOD n) s SUBSET (count n)``,
  rw[SUBSET_DEF] >>
  rw[MOD_LESS]);

(* Theorem: !n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
*)
val card_mod_image = store_thm(
  "card_mod_image",
  ``!s n. 0 < n ==> CARD (IMAGE (\x. x MOD n) s) <= n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  metis_tac[CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);
(* not used *)

(* Theorem: !n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n *)
(* Proof:
   Let t = IMAGE (\x. x MOD n) s
   Since   t SUBSET count n          by SUBSET_DEF, MOD_LESS
     Now   FINITE (count n)          by FINITE_COUNT
     and   CARD (count n) = n        by CARD_COUNT
      So   CARD t <= n               by CARD_SUBSET
     and   FINITE t                  by SUBSET_FINITE
     But   0 IN (count n)            by IN_COUNT
     yet   0 NOTIN t                 by given
   Hence   t <> (count n)            by NOT_EQUAL_SETS
      So   CARD t <> n               by SUBSET_EQ_CARD
     Thus  CARD t < n
*)
val card_mod_image_nonzero = store_thm(
  "card_mod_image_nonzero",
  ``!s n. 0 < n /\ 0 NOTIN (IMAGE (\x. x MOD n) s) ==> CARD (IMAGE (\x. x MOD n) s) < n``,
  rpt strip_tac >>
  qabbrev_tac `t = IMAGE (\x. x MOD n) s` >>
  (`t SUBSET count n` by (rw[SUBSET_DEF, Abbr`t`] >> metis_tac[MOD_LESS])) >>
  `FINITE (count n) /\ (CARD (count n) = n) ` by rw[] >>
  `CARD t <= n` by metis_tac[CARD_SUBSET] >>
  `0 IN (count n)` by rw[] >>
  `t <> (count n)` by metis_tac[NOT_EQUAL_SETS] >>
  `CARD t <> n` by metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE] >>
  decide_tac);
(* not used *)

(* ------------------------------------------------------------------------- *)
(* Partition Property                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s)) *)
(* Proof:
   If part: u = {} ==> v = s
      Note  s = {} UNION v        by given, u = {}
              = v                 by UNION_EMPTY
   Only-if part: v = s ==> u = {}
      Note FINITE u /\ FINITE v       by FINITE_UNION
       ==> CARD v = CARD u + CARD v   by CARD_UNION_DISJOINT
       ==>      0 = CARD u            by arithmetic
      Thus u = {}                     by CARD_EQ_0
*)
val finite_partition_property = store_thm(
  "finite_partition_property",
  ``!s. FINITE s ==> !u v. s =|= u # v ==> ((u = {}) <=> (v = s))``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `FINITE u /\ FINITE v` by metis_tac[FINITE_UNION] >>
  `CARD v = CARD u + CARD v` by metis_tac[CARD_UNION_DISJOINT] >>
  `CARD u <> 0` by rw[CARD_EQ_0] >>
  decide_tac);

(* Theorem: FINITE s ==> !P. let u = {x | x IN s /\ P x} in let v = {x | x IN s /\ ~P x} in
            FINITE u /\ FINITE v /\ s =|= u # v *)
(* Proof:
   This is to show:
   (1) FINITE u, true      by SUBSET_DEF, SUBSET_FINITE
   (2) FINITE v, true      by SUBSET_DEF, SUBSET_FINITE
   (3) u UNION v = s       by IN_UNION
   (4) DISJOINT u v, true  by IN_DISJOINT, MEMBER_NOT_EMPTY
*)
Theorem finite_partition_by_predicate:
  !s. FINITE s ==>
      !P. let u = {x | x IN s /\ P x} ;
              v = {x | x IN s /\ ~P x}
          in
              FINITE u /\ FINITE v /\ s =|= u # v
Proof
  rw_tac std_ss[] >| [
    `u SUBSET s` by rw[SUBSET_DEF, Abbr`u`] >>
    metis_tac[SUBSET_FINITE],
    `v SUBSET s` by rw[SUBSET_DEF, Abbr`v`] >>
    metis_tac[SUBSET_FINITE],
    simp[EXTENSION, Abbr‘u’, Abbr‘v’] >>
    metis_tac[],
    simp[Abbr‘u’, Abbr‘v’, DISJOINT_DEF, EXTENSION] >> metis_tac[]
  ]
QED

(* Theorem: u SUBSET s ==> let v = s DIFF u in s =|= u # v *)
(* Proof:
   This is to show:
   (1) u SUBSET s ==> s = u UNION (s DIFF u), true   by UNION_DIFF
   (2) u SUBSET s ==> DISJOINT u (s DIFF u), true    by DISJOINT_DIFF
*)
val partition_by_subset = store_thm(
  "partition_by_subset",
  ``!s u. u SUBSET s ==> let v = s DIFF u in s =|= u # v``,
  rw[UNION_DIFF, DISJOINT_DIFF]);

(* Theorem: x IN s ==> s =|= {x} # (s DELETE x) *)
(* Proof:
   Note x IN s ==> {x} SUBSET s    by SUBSET_DEF, IN_SING
    and s DELETE x = s DIFF {x}    by DELETE_DEF
   Thus s =|= {x} # (s DELETE x)   by partition_by_subset
*)
val partition_by_element = store_thm(
  "partition_by_element",
  ``!s x. x IN s ==> s =|= {x} # (s DELETE x)``,
  metis_tac[partition_by_subset, DELETE_DEF, SUBSET_DEF, IN_SING]);

(* ------------------------------------------------------------------------- *)
(* Splitting of a set                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: s =|= {} # t <=> (s = t) *)
(* Proof:
       s =|= {} # t
   <=> (s = {} UNION t) /\ (DISJOINT {} t)     by notation
   <=> (s = {} UNION t) /\ T                   by DISJOINT_EMPTY
   <=> s = t                                   by UNION_EMPTY
*)
val SPLIT_EMPTY = store_thm(
  "SPLIT_EMPTY",
  ``!s t. s =|= {} # t <=> (s = t)``,
  rw[]);

(* Theorem: s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
    and v =|= a # b <=> (v = a UNION b) /\ (DISJOINT a b)   by notation
   Let c = u UNION a.
   Then s = u UNION v                   by above
          = u UNION (a UNION b)         by above
          = (u UNION a) UNION b         by UNION_ASSOC
          = c UNION b
   Note  DISJOINT u v
     <=> DISJOINT u (a UNION b)
     <=> DISJOINT (a UNION b) u         by DISJOINT_SYM
     <=> DISJOINT a u /\ DISJOINT b u   by DISJOINT_UNION
     <=> DISJOINT u a /\ DISJOINT u b   by DISJOINT_SYM

   Thus  DISJOINT c b
     <=> DISJOINT (u UNION a) b         by above
     <=> DISJOINT u b /\ DISJOINT a b   by DISJOINT_UNION
     <=> T /\ T                         by above
     <=> T
   Therefore,
         s =|= c # b       by s = c UNION b /\ DISJOINT c b
     and c =|= u # a       by c = u UNION a /\ DISJOINT u a
*)
val SPLIT_UNION = store_thm(
  "SPLIT_UNION",
  ``!s u v a b. s =|= u # v /\ v =|= a # b ==> s =|= u UNION a # b /\ u UNION a =|= u # a``,
  metis_tac[DISJOINT_UNION, DISJOINT_SYM, UNION_ASSOC]);

(* Theorem: s =|= u # v <=> u SUBSET s /\ (v = s DIFF u) *)
(* Proof:
   Note s =|= u # v <=> (s = u UNION v) /\ (DISJOINT u v)   by notation
   If part: s =|= u # v ==> u SUBSET s /\ (v = s DIFF u)
      Note u SUBSET (u UNION v)         by SUBSET_UNION
           s DIFF u
         = (u UNION v) DIFF u           by s = u UNION v
         = v DIFF u                     by DIFF_SAME_UNION
         = v                            by DISJOINT_DIFF_IFF, DISJOINT_SYM

   Only-if part: u SUBSET s /\ (v = s DIFF u) ==> s =|= u # v
      Note s = u UNION (s DIFF u)       by UNION_DIFF, u SUBSET s
       and DISJOINT u (s DIFF u)        by DISJOINT_DIFF
      Thus s =|= u # v                  by notation
*)
val SPLIT_EQ = store_thm(
  "SPLIT_EQ",
  ``!s u v. s =|= u # v <=> u SUBSET s /\ (v = s DIFF u)``,
  rw[DISJOINT_DEF, SUBSET_DEF, EXTENSION] >>
  metis_tac[]);

(* Theorem: (s =|= u # v) = (s =|= v # u) *)
(* Proof:
     s =|= u # v
   = (s = u UNION v) /\ DISJOINT u v    by notation
   = (s = v UNION u) /\ DISJOINT u v    by UNION_COMM
   = (s = v UNION u) /\ DISJOINT v u    by DISJOINT_SYM
   = s =|= v # u                        by notation
*)
val SPLIT_SYM = store_thm(
  "SPLIT_SYM",
  ``!s u v. (s =|= u # v) = (s =|= v # u)``,
  rw_tac std_ss[UNION_COMM, DISJOINT_SYM]);

(* Theorem: (s =|= u # v) ==> (s =|= v # u) *)
(* Proof: by SPLIT_SYM *)
val SPLIT_SYM_IMP = store_thm(
  "SPLIT_SYM_IMP",
  ``!s u v. (s =|= u # v) ==> (s =|= v # u)``,
  rw_tac std_ss[SPLIT_SYM]);

(* Theorem: s =|= {x} # v <=> (x IN s /\ (v = s DELETE x)) *)
(* Proof:
       s =|= {x} # v
   <=> {x} SUBSET s /\ (v = s DIFF {x})   by SPLIT_EQ
   <=> x IN s       /\ (v = s DIFF {x})   by SUBSET_DEF
   <=> x IN s       /\ (v = s DELETE x)   by DELETE_DEF
*)
val SPLIT_SING = store_thm(
  "SPLIT_SING",
  ``!s v x. s =|= {x} # v <=> (x IN s /\ (v = s DELETE x))``,
  rw[SPLIT_EQ, SUBSET_DEF, DELETE_DEF]);

(* Theorem: s =|= u # v ==> u SUBSET s /\ v SUBSET s *)
(* Proof: by SUBSET_UNION *)
Theorem SPLIT_SUBSETS:
  !s u v. s =|= u # v ==> u SUBSET s /\ v SUBSET s
Proof
  rw[]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v *)
(* Proof: by SPLIT_SUBSETS, SUBSET_FINITE *)
Theorem SPLIT_FINITE:
  !s u v. FINITE s /\ s =|= u # v ==> FINITE u /\ FINITE v
Proof
  simp[SPLIT_SUBSETS, SUBSET_FINITE]
QED

(* Theorem: FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v) *)
(* Proof:
   Note FINITE u /\ FINITE v   by SPLIT_FINITE
     CARD s
   = CARD (u UNION v)          by notation
   = CARD u + CARD v           by CARD_UNION_DISJOINT
*)
Theorem SPLIT_CARD:
  !s u v. FINITE s /\ s =|= u # v ==> (CARD s = CARD u + CARD v)
Proof
  metis_tac[CARD_UNION_DISJOINT, SPLIT_FINITE]
QED

(* Theorem: s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u) *)
(* Proof:
   If part: s =|= u # v ==> (u = s DIFF v) /\ (v = s DIFF u)
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
   Only-if part: (u = s DIFF v) /\ (v = s DIFF u) ==> s =|= u # v
      True by EXTENSION, IN_UNION, IN_DISJOINT, IN_DIFF.
*)
val SPLIT_EQ_DIFF = store_thm(
  "SPLIT_EQ_DIFF",
  ``!s u v. s =|= u # v <=> (u = s DIFF v) /\ (v = s DIFF u)``,
  rpt strip_tac >>
  eq_tac >| [
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF],
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DISJOINT, IN_DIFF]
    ],
    rpt strip_tac >| [
      rw[EXTENSION] >>
      metis_tac[IN_UNION, IN_DIFF],
      metis_tac[IN_DISJOINT, IN_DIFF]
    ]
  ]);

(* Theorem alias *)
val SPLIT_BY_SUBSET = save_thm("SPLIT_BY_SUBSET", partition_by_subset);
(* val SPLIT_BY_SUBSET = |- !s u. u SUBSET s ==> (let v = s DIFF u in s =|= u # v): thm *)

(* Theorem alias *)
val SUBSET_DIFF_DIFF = save_thm("SUBSET_DIFF_DIFF", DIFF_DIFF_SUBSET);
(* val SUBSET_DIFF_DIFF = |- !s t. t SUBSET s ==> (s DIFF (s DIFF t) = t) *)

(* Theorem: s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2) *)
(* Proof:
   Let u = t DIFF s2.
   Then u = t DIFF s1             by given
    ==> t =|= u # s1              by SPLIT_BY_SUBSET, s1 SUBSET t
   Thus s1 = t DIFF u             by SPLIT_EQ
           = t DIFF (t DIFF s2)   by notation
           = s2                   by SUBSET_DIFF_DIFF, s2 SUBSET t
*)
val SUBSET_DIFF_EQ = store_thm(
  "SUBSET_DIFF_EQ",
  ``!s1 s2 t. s1 SUBSET t /\ s2 SUBSET t /\ (t DIFF s1 = t DIFF s2) ==> (s1 = s2)``,
  metis_tac[SPLIT_BY_SUBSET, SPLIT_EQ, SUBSET_DIFF_DIFF]);

(* ------------------------------------------------------------------------- *)
(* Bijective Inverses.                                                       *)
(* ------------------------------------------------------------------------- *)

(* In pred_setTheory:
LINV_DEF        |- !f s t. INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)
BIJ_LINV_INV    |- !f s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)
BIJ_LINV_BIJ    |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
RINV_DEF        |- !f s t. SURJ f s t ==> !x. x IN t ==> (f (RINV f s x) = x)

That's it, must be missing some!
Must assume: !y. y IN t ==> RINV f s y IN s
*)

(* Theorem: BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s *)
(* Proof:
   Since BIJ f s t ==> BIJ (LINV f s) t s   by BIJ_LINV_BIJ
      so x IN t ==> (LINV f s x) IN s       by BIJ_DEF, INJ_DEF
*)
val BIJ_LINV_ELEMENT = store_thm(
  "BIJ_LINV_ELEMENT",
  ``!f s t. BIJ f s t ==> !x. x IN t ==> (LINV f s x) IN s``,
  metis_tac[BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]);

(* Theorem: (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x)) *)
(* Proof:
   Since BIJ f s t ==> INJ f s t      by BIJ_DEF
     and INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)    by LINV_DEF
    also BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)    by BIJ_LINV_INV
*)
val BIJ_LINV_THM = store_thm(
  "BIJ_LINV_THM",
  ``!(f:'a -> 'b) s t. BIJ f s t ==>
    (!x. x IN s ==> (LINV f s (f x) = x)) /\ (!x. x IN t ==> (f (LINV f s x) = x))``,
  metis_tac[BIJ_DEF, LINV_DEF, BIJ_LINV_INV]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
            !x. x IN s ==> (RINV f s (f x) = x) *)
(* Proof:
   BIJ f s t means INJ f s t /\ SURJ f s t     by BIJ_DEF
   Hence x IN s ==> f x IN t                   by INJ_DEF or SURJ_DEF
                ==> f (RINV f s (f x)) = f x   by RINV_DEF, SURJ f s t
                ==> RINV f s (f x) = x         by INJ_DEF
*)
val BIJ_RINV_INV = store_thm(
  "BIJ_RINV_INV",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==>
   !x. x IN s ==> (RINV f s (f x) = x)``,
  rw[BIJ_DEF] >>
  `f x IN t` by metis_tac[INJ_DEF] >>
  `f (RINV f s (f x)) = f x` by metis_tac[RINV_DEF] >>
  metis_tac[INJ_DEF]);

(* Theorem: BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (RINV f s) t s
       By INJ_DEF, this is to show:
       x IN t /\ y IN t /\ RINV f s x = RINV f s y ==> x = y
       But  SURJ f s t           by BIJ_DEF
        so  f (RINV f s x) = x   by RINV_DEF, SURJ f s t
       and  f (RINV f s y) = y   by RINV_DEF, SURJ f s t
       Thus x = y.
   (2) SURJ (RINV f s) t s
       By SURJ_DEF, this is to show:
       x IN s ==> ?y. y IN t /\ (RINV f s y = x)
       But  INJ f s t            by BIJ_DEF
        so  f x IN t             by INJ_DEF
       and  RINV f s (f x) = x   by BIJ_RINV_INV
       Take y = f x to meet the criteria.
*)
val BIJ_RINV_BIJ = store_thm(
  "BIJ_RINV_BIJ",
  ``!(f:'a -> 'b) s t. BIJ f s t /\ (!y. y IN t ==> RINV f s y IN s) ==> BIJ (RINV f s) t s``,
  rpt strip_tac >>
  rw[BIJ_DEF] >-
  metis_tac[INJ_DEF, BIJ_DEF, RINV_DEF] >>
  rw[SURJ_DEF] >>
  metis_tac[INJ_DEF, BIJ_DEF, BIJ_RINV_INV]);

(* Theorem: INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x) *)
(* Proof: by LINV_DEF, SUBSET_DEF *)
Theorem LINV_SUBSET:
  !(f:'a -> 'b) s t. INJ f t univ(:'b) /\ s SUBSET t ==> !x. x IN s ==> (LINV f t (f x) = x)
Proof
  metis_tac[LINV_DEF, SUBSET_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* SUM_IMAGE and PROD_IMAGE Theorems                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SIGMA I (IMAGE f s)) *)
(* Proof:
   By finite induction on s.
   Base case: SIGMA f {} = SIGMA I {}
        SIGMA f {}
      = 0              by SUM_IMAGE_THM
      = SIGMA I {}     by SUM_IMAGE_THM
      = SUM_SET {}     by SUM_SET_DEF
   Step case: !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s)) ==>
              e NOTIN s ==> SIGMA f (e INSERT s) = SUM_SET (f e INSERT IMAGE f s)
      Note FINITE s ==> FINITE (IMAGE f s)   by IMAGE_FINITE
       and e NOTIN s ==> f e NOTIN f s       by the injective property
        SIGMA f (e INSERT s)
      = f e + SIGMA f (s DELETE e))    by SUM_IMAGE_THM
      = f e + SIGMA f s                by DELETE_NON_ELEMENT
      = f e + SUM_SET (IMAGE f s))     by induction hypothesis
      = f e + SUM_SET ((IMAGE f s) DELETE (f e))   by DELETE_NON_ELEMENT, f e NOTIN f s
      = SUM_SET (f e INSERT IMAGE f s)             by SUM_SET_THM
*)
val SUM_IMAGE_AS_SUM_SET = store_thm(
  "SUM_IMAGE_AS_SUM_SET",
  ``!s. FINITE s ==> !f. (!x y. (f x = f y) ==> (x = y)) ==> (SIGMA f s = SUM_SET (IMAGE f s))``,
  HO_MATCH_MP_TAC FINITE_INDUCT >>
  rw[SUM_SET_DEF] >-
  rw[SUM_IMAGE_THM] >>
  rw[SUM_IMAGE_THM, SUM_IMAGE_DELETE] >>
  metis_tac[]);

(* Theorem: x <> y ==> SIGMA f {x; y} = f x + f y *)
(* Proof:
   Let s = {x; y}.
   Then FINITE s                   by FINITE_UNION, FINITE_SING
    and x INSERT s                 by INSERT_DEF
    and s DELETE x = {y}           by DELETE_DEF
        SIGMA f s
      = SIGMA f (x INSERT s)       by above
      = f x + SIGMA f (s DELETE x) by SUM_IMAGE_THM
      = f x + SIGMA f {y}          by above
      = f x + f y                  by SUM_IMAGE_SING
*)
Theorem SUM_IMAGE_DOUBLET:
  !f x y. x <> y ==> SIGMA f {x; y} = f x + f y
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {x; y}` >>
  `FINITE s` by fs[Abbr`s`] >>
  `x INSERT s = s` by fs[Abbr`s`] >>
  `s DELETE x = {x; y} DELETE x` by simp[Abbr`s`] >>
  `_ = if y = x then {} else {y}` by EVAL_TAC >>
  `_ = {y}` by simp[] >>
  metis_tac[SUM_IMAGE_THM, SUM_IMAGE_SING]
QED

(* Theorem: x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z *)
(* Proof:
   Let s = {x; y; z}.
   Then FINITE s                   by FINITE_UNION, FINITE_SING
    and x INSERT s                 by INSERT_DEF
    and s DELETE x = {y; z}        by DELETE_DEF
        SIGMA f s
      = SIGMA f (x INSERT s)       by above
      = f x + SIGMA f (s DELETE x) by SUM_IMAGE_THM
      = f x + SIGMA f {y; z}       by above
      = f x + f y + f z            by SUM_IMAGE_DOUBLET
*)
Theorem SUM_IMAGE_TRIPLET:
  !f x y z. x <> y /\ y <> z /\ z <> x ==> SIGMA f {x; y; z} = f x + f y + f z
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {x; y; z}` >>
  `FINITE s` by fs[Abbr`s`] >>
  `x INSERT s = s` by fs[Abbr`s`] >>
  `s DELETE x = {x; y; z} DELETE x` by simp[Abbr`s`] >>
  `_ = if y = x then if z = x then {} else {z}
      else y INSERT if z = x then {} else {z}` by EVAL_TAC >>
  `_ = {y; z}` by simp[] >>
  `SIGMA f s = f x + (f y + f z)` by metis_tac[SUM_IMAGE_THM, SUM_IMAGE_DOUBLET, SUM_IMAGE_SING] >>
  decide_tac
QED

(*
CARD_BIGUNION_SAME_SIZED_SETS
|- !n s. FINITE s /\ (!e. e IN s ==> FINITE e /\ CARD e = n) /\
         PAIR_DISJOINT s ==> CARD (BIGUNION s) = CARD s * n
*)

(* Theorem: If n divides CARD e for all e in s, then n divides SIGMA CARD s.
            FINITE s /\ (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s) *)
(* Proof:
   Use finite induction and SUM_IMAGE_THM.
   Base: n divides SIGMA CARD {}
         Note SIGMA CARD {} = 0        by SUM_IMAGE_THM
          and n divides 0              by ALL_DIVIDES_0
   Step: e NOTIN s /\ n divides (CARD e) ==> n divides SIGMA CARD (e INSERT s)
           SIGMA CARD (e INSERT s)
         = CARD e + SIGMA CARD (s DELETE e)      by SUM_IMAGE_THM
         = CARD e + SIGMA CARD s                 by DELETE_NON_ELEMENT
         Note n divides (CARD e)                 by given
          and n divides SIGMA CARD s             by induction hypothesis
         Thus n divides SIGMA CARD (e INSERT s)  by DIVIDES_ADD_1
*)
Theorem SIGMA_CARD_FACTOR:
  !n s. FINITE s /\ (!e. e IN s ==> n divides (CARD e)) ==> n divides (SIGMA CARD s)
Proof
  strip_tac >>
  Induct_on `FINITE` >>
  rw[] >-
  rw[SUM_IMAGE_THM] >>
  metis_tac[SUM_IMAGE_THM, DELETE_NON_ELEMENT, DIVIDES_ADD_1]
QED

(* Theorem: FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s *)
(* Proof:
   Note t SUBSET s /\ t <> s      by PSUBSET_DEF
   Thus SIGMA f t <= SIGMA f s    by SUM_IMAGE_SUBSET_LE
   By contradiction, suppose ~(SIGMA f t < SIGMA f s).
   Then SIGMA f t = SIGMA f s     by arithmetic [1]

   Let u = s DIFF t.
   Then DISJOINT u t                        by DISJOINT_DIFF
    and u UNION t = s                       by UNION_DIFF
   Note FINITE u /\ FINITE t                by FINITE_UNION
    ==> SIGMA f s = SIGMA f u + SIGMA f t   by SUM_IMAGE_DISJOINT
   Thus SIGMA f u = 0                       by arithmetic, [1]

    Now u SUBSET s                          by SUBSET_UNION
    and u <> {}                             by finite_partition_property, t <> s
   Thus ?x. x IN u                          by MEMBER_NOT_EMPTY
    and f x <> 0                            by SUBSET_DEF, implication
   This contradicts f x = 0                 by SUM_IMAGE_ZERO
*)
val SUM_IMAGE_PSUBSET_LT = store_thm(
  "SUM_IMAGE_PSUBSET_LT",
  ``!f s t. FINITE s /\ t PSUBSET s /\ (!x. x IN s ==> f x <> 0) ==> SIGMA f t < SIGMA f s``,
  rw[PSUBSET_DEF] >>
  `SIGMA f t <= SIGMA f s` by rw[SUM_IMAGE_SUBSET_LE] >>
  spose_not_then strip_assume_tac >>
  `SIGMA f t = SIGMA f s` by decide_tac >>
  qabbrev_tac `u = s DIFF t` >>
  `DISJOINT u t` by rw[DISJOINT_DIFF, Abbr`u`] >>
  `u UNION t = s` by rw[UNION_DIFF, Abbr`u`] >>
  `FINITE u /\ FINITE t` by metis_tac[FINITE_UNION] >>
  `SIGMA f s = SIGMA f u + SIGMA f t` by rw[GSYM SUM_IMAGE_DISJOINT] >>
  `SIGMA f u = 0` by decide_tac >>
  `u SUBSET s` by rw[] >>
  `u <> {}` by metis_tac[finite_partition_property] >>
  metis_tac[SUM_IMAGE_ZERO, SUBSET_DEF, MEMBER_NOT_EMPTY]);

(* Idea: Let s be a set of sets. If CARD s = SIGMA CARD s,
         and all elements in s are non-empty, then all elements in s are SING. *)

(* Theorem: FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s *)
(* Proof:
   By finite induction on set s.
   Base: (!e. e IN {} ==> CARD e <> 0) ==> CARD {} <= SIGMA CARD {}
      LHS = CARD {} = 0            by CARD_EMPTY
      RHS = SIGMA CARD {} = 0      by SUM_IMAGE_EMPTY
      Hence true.
   Step: FINITE s /\ ((!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s) ==>
         !e. e NOTIN s ==>
             (!e'. e' IN e INSERT s ==> CARD e' <> 0) ==>
             CARD (e INSERT s) <= SIGMA CARD (e INSERT s)

      Note !e'. e' IN s
            ==> e' IN e INSERT s   by IN_INSERT, e NOTIN s
            ==> CARD e' <> 0       by implication, so induction hypothesis applies.
       and CARD e <> 0             by e IN e INSERT s
            CARD (e INSERT s)
          = SUC (CARD s)           by CARD_INSERT, e NOTIN s
          = 1 + CARD s             by SUC_ONE_ADD

         <= 1 + SIGMA CARD s       by induction hypothesis
         <= CARD e + SIGMA CARD s  by 1 <= CARD e
          = SIGMA (e INSERT s)     by SUM_IMAGE_INSERT, e NOTIN s.
*)
Theorem card_le_sigma_card:
  !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) ==> CARD s <= SIGMA CARD s
Proof
  Induct_on `FINITE` >>
  rw[] >>
  `CARD e <> 0` by fs[] >>
  `1 <= CARD e` by decide_tac >>
  fs[] >>
  simp[SUM_IMAGE_INSERT]
QED

(* Theorem: FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
            CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1 *)
(* Proof:
   By finite induction on set s.
   Base: (!e. e IN {} ==> CARD e <> 0) /\ CARD {} = SIGMA CARD {} ==>
         !e. e IN {} ==> CARD e = 1
      Since e IN {} = F, this is trivially true.
   Step: !s. FINITE s /\
             ((!e. e IN s ==> CARD e <> 0) /\ CARD s = SIGMA CARD s ==>
              !e. e IN s ==> CARD e = 1) ==>
         !e. e NOTIN s ==>
             (!e'. e' IN e INSERT s ==> CARD e' <> 0) /\
             CARD (e INSERT s) = SIGMA CARD (e INSERT s) ==>
             !e'. e' IN e INSERT s ==> CARD e' = 1
      Note !e'. e' IN s
           ==> e' IN e INSERT s    by IN_INSERT, e NOTIN s
           ==> CARD e' <> 0        by implication, helps in induction hypothesis
      Also e IN e INSERT s         by IN_INSERT
        so CARD e <> 0             by implication

           CARD e + CARD s
        <= CARD e + SIGMA CARD s   by card_le_sigma_card
         = SIGMA CARD (e INSERT s) by SUM_IMAGE_INSERT, e NOTIN s
         = CARD (e INSERT s)       by given
         = SUC (CARD s)            by CARD_INSERT, e NOTIN s
         = 1 + CARD s              by SUC_ONE_ADD
      Thus CARD e <= 1             by arithmetic
        or CARD e = 1              by CARD e <> 0
       ==> CARD s = SIGMA CARD s   by arithmetic, helps in induction hypothesis
      Thus !e. e IN s ==> CARD e = 1               by induction hypothesis
      and  !e'. e' IN e INSERT s ==> CARD e' = 1   by CARD e = 1
*)
Theorem card_eq_sigma_card:
  !s. FINITE s /\ (!e. e IN s ==> CARD e <> 0) /\
      CARD s = SIGMA CARD s ==> !e. e IN s ==> CARD e = 1
Proof
  Induct_on `FINITE` >>
  simp[] >>
  ntac 6 strip_tac >>
  `CARD e <> 0 /\ !e. e IN s ==> CARD e <> 0` by fs[] >>
  imp_res_tac card_le_sigma_card >>
  `CARD e + CARD s <= CARD e + SIGMA CARD s` by decide_tac >>
  `CARD e + SIGMA CARD s = SIGMA CARD (e INSERT s)` by fs[SUM_IMAGE_INSERT] >>
  `_ = 1 + CARD s` by rw[] >>
  `CARD e <= 1` by fs[] >>
  `CARD e = 1` by decide_tac >>
  `CARD s = SIGMA CARD s` by fs[] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* SUM_SET and PROD_SET Theorems                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s) *)
(* Proof:
   By finite induction on s.
   Base: SUM_SET (IMAGE f {}) = SIGMA f {}
         SUM_SET (IMAGE f {})
       = SUM_SET {}                  by IMAGE_EMPTY
       = 1                           by SUM_SET_EMPTY
       = SIGMA f {}                  by SUM_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (SUM_SET (IMAGE f s) = SIGMA f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> SUM_SET (IMAGE f (e INSERT s)) = SIGMA f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         SUM_SET (IMAGE f (e INSERT s))
       = SUM_SET (f e INSERT (IMAGE f s))    by IMAGE_INSERT
       = f e * SUM_SET (IMAGE f s)           by SUM_SET_INSERT
       = f e * SIGMA f s                     by induction hypothesis
       = SIGMA f (e INSERT s)                by SUM_IMAGE_INSERT
*)
val SUM_SET_IMAGE_EQN = store_thm(
  "SUM_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (SUM_SET (IMAGE f s) = SIGMA f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_SET_EMPTY, SUM_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[SUM_SET_INSERT, SUM_IMAGE_INSERT]);

(* Theorem: SUM_SET (count n) = (n * (n - 1)) DIV 2*)
(* Proof:
   By induction on n.
   Base case: SUM_SET (count 0) = 0 * (0 - 1) DIV 2
     LHS = SUM_SET (count 0)
         = SUM_SET {}           by COUNT_ZERO
         = 0                    by SUM_SET_THM
         = 0 DIV 2              by ZERO_DIV
         = 0 * (0 - 1) DIV 2    by MULT
         = RHS
   Step case: SUM_SET (count n) = n * (n - 1) DIV 2 ==>
              SUM_SET (count (SUC n)) = SUC n * (SUC n - 1) DIV 2
     If n = 0, to show: SUM_SET (count 1) = 0
        SUM_SET (count 1) = SUM_SET {0} = 0  by SUM_SET_SING
     If n <> 0, 0 < n.
     First, FINITE (count n)               by FINITE_COUNT
            n NOTIN (count n)              by IN_COUNT
     LHS = SUM_SET (count (SUC n))
         = SUM_SET (n INSERT count n)      by COUNT_SUC
         = n + SUM_SET (count n DELETE n)  by SUM_SET_THM
         = n + SUM_SET (count n)           by DELETE_NON_ELEMENT
         = n + n * (n - 1) DIV 2           by induction hypothesis
         = (n * 2 + n * (n - 1)) DIV 2     by ADD_DIV_ADD_DIV
         = (n * (2 + (n - 1))) DIV 2       by LEFT_ADD_DISTRIB
         = n * (n + 1) DIV 2               by arithmetic, 0 < n
         = (SUC n - 1) * (SUC n) DIV 2     by ADD1, SUC_SUB1
         = SUC n * (SUC n - 1) DIV 2       by MULT_COMM
         = RHS
*)
val SUM_SET_COUNT = store_thm(
  "SUM_SET_COUNT",
  ``!n. SUM_SET (count n) = (n * (n - 1)) DIV 2``,
  Induct_on `n` >-
  rw[] >>
  Cases_on `n = 0` >| [
    rw[] >>
    EVAL_TAC,
    `0 < n` by decide_tac >>
    `FINITE (count n)` by rw[] >>
    `n NOTIN (count n)` by rw[] >>
    `SUM_SET (count (SUC n)) = SUM_SET (n INSERT count n)` by rw[COUNT_SUC] >>
    `_ = n + SUM_SET (count n DELETE n)` by rw[SUM_SET_THM] >>
    `_ = n + SUM_SET (count n)` by metis_tac[DELETE_NON_ELEMENT] >>
    `_ = n + n * (n - 1) DIV 2` by rw[] >>
    `_ = (n * 2 + n * (n - 1)) DIV 2` by rw[ADD_DIV_ADD_DIV] >>
    `_ = (n * (2 + (n - 1))) DIV 2` by rw[LEFT_ADD_DISTRIB] >>
    `_ = n * (n + 1) DIV 2` by rw_tac arith_ss[] >>
    `_ = (SUC n - 1) * SUC n DIV 2` by rw[ADD1, SUC_SUB1] >>
    `_ = SUC n * (SUC n - 1) DIV 2 ` by rw[MULT_COMM] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)


(* Theorem: FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s) *)
(* Proof:
   By finite induction on s.
   Base: PROD_SET (IMAGE f {}) = PI f {}
         PROD_SET (IMAGE f {})
       = PROD_SET {}              by IMAGE_EMPTY
       = 1                        by PROD_SET_EMPTY
       = PI f {}                  by PROD_IMAGE_EMPTY
   Step: !f. INJ f s univ(:num) ==> (PROD_SET (IMAGE f s) = PI f s) ==>
         e NOTIN s /\ INJ f (e INSERT s) univ(:num) ==> PROD_SET (IMAGE f (e INSERT s)) = PI f (e INSERT s)
       Note INJ f s univ(:num)               by INJ_INSERT
        and f e NOTIN (IMAGE f s)            by IN_IMAGE
         PROD_SET (IMAGE f (e INSERT s))
       = PROD_SET (f e INSERT (IMAGE f s))   by IMAGE_INSERT
       = f e * PROD_SET (IMAGE f s)          by PROD_SET_INSERT
       = f e * PI f s                        by induction hypothesis
       = PI f (e INSERT s)                   by PROD_IMAGE_INSERT
*)
val PROD_SET_IMAGE_EQN = store_thm(
  "PROD_SET_IMAGE_EQN",
  ``!s. FINITE s ==> !f. INJ f s UNIV ==> (PROD_SET (IMAGE f s) = PI f s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY, PROD_IMAGE_EMPTY] >>
  fs[INJ_INSERT] >>
  `f e NOTIN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  rw[PROD_SET_INSERT, PROD_IMAGE_INSERT]);

(* Theorem: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m)) *)
(* Proof:
   By induction on m.
   Base case: PROD_SET (IMAGE (\j. n ** j) (count 0)) = n ** SUM_SET (count 0)
     LHS = PROD_SET (IMAGE (\j. n ** j) (count 0))
         = PROD_SET (IMAGE (\j. n ** j) {})          by COUNT_ZERO
         = PROD_SET {}                               by IMAGE_EMPTY
         = 1                                         by PROD_SET_THM
     RHS = n ** SUM_SET (count 0)
         = n ** SUM_SET {}                           by COUNT_ZERO
         = n ** 0                                    by SUM_SET_THM
         = 1                                         by EXP
         = LHS
   Step case: PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** SUM_SET (count m) ==>
              PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) = n ** SUM_SET (count (SUC m))
     First,
          FINITE (count m)                                   by FINITE_COUNT
          FINITE (IMAGE (\j. n ** j) (count m))              by IMAGE_FINITE
          m NOTIN count m                                    by IN_COUNT
     and  (\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)  by EXP_BASE_INJECTIVE, 1 < n

     LHS = PROD_SET (IMAGE (\j. n ** j) (count (SUC m)))
         = PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))  by COUNT_SUC
         = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))  by PROD_SET_IMAGE_REDUCTION
         = n ** m * n ** SUM_SET (count m)                   by induction hypothesis
         = n ** (m + SUM_SET (count m))                      by EXP_ADD
         = n ** SUM_SET (m INSERT count m)                   by SUM_SET_INSERT
         = n ** SUM_SET (count (SUC m))                      by COUNT_SUC
         = RHS
*)
val PROD_SET_IMAGE_EXP = store_thm(
  "PROD_SET_IMAGE_EXP",
  ``!n. 1 < n ==> !m. PROD_SET (IMAGE (\j. n ** j) (count m)) = n ** (SUM_SET (count m))``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[PROD_SET_THM] >>
  `FINITE (IMAGE (\j. n ** j) (count m))` by rw[] >>
  `(\j. n ** j) m NOTIN IMAGE (\j. n ** j) (count m)` by rw[] >>
  `m NOTIN count m` by rw[] >>
  `PROD_SET (IMAGE (\j. n ** j) (count (SUC m))) =
    PROD_SET (IMAGE (\j. n ** j) (m INSERT count m))` by rw[COUNT_SUC] >>
  `_ = n ** m * PROD_SET (IMAGE (\j. n ** j) (count m))` by rw[PROD_SET_IMAGE_REDUCTION] >>
  `_ = n ** m * n ** SUM_SET (count m)` by rw[] >>
  `_ = n ** (m + SUM_SET (count m))` by rw[EXP_ADD] >>
  `_ = n ** SUM_SET (m INSERT count m)` by rw[SUM_SET_INSERT] >>
  `_ = n ** SUM_SET (count (SUC m))` by rw[COUNT_SUC] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Partition and Equivalent Class                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: y IN equiv_class R s x <=> y IN s /\ R x y *)
(* Proof: by GSPECIFICATION *)
val equiv_class_element = store_thm(
  "equiv_class_element",
  ``!R s x y. y IN equiv_class R s x <=> y IN s /\ R x y``,
  rw[]);

(* Theorem: partition R {} = {} *)
(* Proof: by partition_def *)
val partition_on_empty = store_thm(
  "partition_on_empty",
  ``!R. partition R {} = {}``,
  rw[partition_def]);

(*
> partition_def;
val it = |- !R s. partition R s = {t | ?x. x IN s /\ (t = equiv_class R s x)}: thm
*)

(* Theorem: t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x) *)
(* Proof: by partition_def *)
Theorem partition_element:
  !R s t. t IN partition R s <=> ?x. x IN s /\ (t = equiv_class R s x)
Proof
  rw[partition_def]
QED

(* Theorem: partition R s = IMAGE (equiv_class R s) s *)
(* Proof:
     partition R s
   = {t | ?x. x IN s /\ (t = {y | y IN s /\ R x y})}   by partition_def
   = {t | ?x. x IN s /\ (t = equiv_class R s x)}       by notation
   = IMAGE (equiv_class R s) s                         by IN_IMAGE
*)
val partition_elements = store_thm(
  "partition_elements",
  ``!R s. partition R s = IMAGE (equiv_class R s) s``,
  rw[partition_def, EXTENSION] >>
  metis_tac[]);

(* Theorem alias *)
val partition_as_image = save_thm("partition_as_image", partition_elements);
(* val partition_as_image =
   |- !R s. partition R s = IMAGE (\x. equiv_class R s x) s: thm *)

(* Theorem: (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2) *)
(* Proof: by identity *)
val partition_cong = store_thm(
  "partition_cong",
  ``!R1 R2 s1 s2. (R1 = R2) /\ (s1 = s2) ==> (partition R1 s1 = partition R2 s2)``,
  rw[]);
(* Just in case this is needed. *)

(*
EMPTY_NOT_IN_partition
val it = |- R equiv_on s ==> {} NOTIN partition R s: thm
*)

(* Theorem: R equiv_on s /\ e IN partition R s ==> e <> {} *)
(* Proof: by EMPTY_NOT_IN_partition. *)
Theorem partition_element_not_empty:
  !R s e. R equiv_on s /\ e IN partition R s ==> e <> {}
Proof
  metis_tac[EMPTY_NOT_IN_partition]
QED

(* Theorem: R equiv_on s /\ x IN s ==> equiv_class R s x <> {} *)
(* Proof:
   Note equiv_class R s x IN partition_element R s     by partition_element
     so equiv_class R s x <> {}                        by partition_element_not_empty
*)
Theorem equiv_class_not_empty:
  !R s x. R equiv_on s /\ x IN s ==> equiv_class R s x <> {}
Proof
  metis_tac[partition_element, partition_element_not_empty]
QED

(* Theorem: R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e) *)
(* Proof:
       x IN s
   <=> x IN (BIGUNION (partition R s))         by BIGUNION_partition
   <=> ?e. e IN partition R s /\ x IN e        by IN_BIGUNION
*)
Theorem partition_element_exists:
  !R s x. R equiv_on s ==> (x IN s <=> ?e. e IN partition R s /\ x IN e)
Proof
  rpt strip_tac >>
  imp_res_tac BIGUNION_partition >>
  metis_tac[IN_BIGUNION]
QED

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s)) *)
(* Proof:
   Note FINITE (partition R s)               by FINITE_partition
     so CARD s = SIGMA CARD (partition R s)  by partition_CARD
               = n * CARD (partition R s)    by SIGMA_CARD_CONSTANT
*)
val equal_partition_card = store_thm(
  "equal_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           (CARD s = n * CARD (partition R s))``,
  rw_tac std_ss[partition_CARD, FINITE_partition, GSYM SIGMA_CARD_CONSTANT]);

(* Theorem: When the partitions are equal size of n, CARD s = n * CARD (partition of s).
           FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
           n divides (CARD s) *)
(* Proof: by equal_partition_card, divides_def. *)
Theorem equal_partition_factor:
  !R s n. FINITE s /\ R equiv_on s /\ (!e. e IN partition R s ==> (CARD e = n)) ==>
          n divides (CARD s)
Proof
  metis_tac[equal_partition_card, divides_def, MULT_COMM]
QED

(* Theorem: When the partition size has a factor n, then n divides CARD s.
            FINITE s /\ R equiv_on s /\
            (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)  *)
(* Proof:
   Note FINITE (partition R s)                by FINITE_partition
   Thus CARD s = SIGMA CARD (partition R s)   by partition_CARD
    But !e. e IN partition R s ==> n divides (CARD e)
    ==> n divides SIGMA CARD (partition R s)  by SIGMA_CARD_FACTOR
   Hence n divdes CARD s                      by above
*)
val factor_partition_card = store_thm(
  "factor_partition_card",
  ``!R s n. FINITE s /\ R equiv_on s /\
   (!e. e IN partition R s ==> n divides (CARD e)) ==> n divides (CARD s)``,
  metis_tac[FINITE_partition, partition_CARD, SIGMA_CARD_FACTOR]);

(* Note:
When a set s is partitioned by an equivalence relation R,
partition_CARD  |- !R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))
Can this be generalized to:   f s = SIGMA f (partition R s)  ?
If so, we can have         (SIGMA f) s = SIGMA (SIGMA f) (partition R s)
Sort of yes, but have to use BIGUNION, and for a set_additive function f.
*)

(* Overload every element finite of a superset *)
val _ = overload_on("EVERY_FINITE", ``\P. (!s. s IN P ==> FINITE s)``);

(*
> FINITE_BIGUNION;
val it = |- !P. FINITE P /\ EVERY_FINITE P ==> FINITE (BIGUNION P): thm
*)

(* Overload pairwise disjoint of a superset *)
val _ = overload_on("PAIR_DISJOINT", ``\P. (!s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t)``);

(*
> partition_elements_disjoint;
val it = |- R equiv_on s ==> PAIR_DISJOINT (partition R s): thm
*)

(* Theorem: t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t *)
(* Proof: by SUBSET_DEF *)
Theorem pair_disjoint_subset:
  !s t. t SUBSET s /\ PAIR_DISJOINT s ==> PAIR_DISJOINT t
Proof
  rw[SUBSET_DEF]
QED

(* Overload an additive set function *)
val _ = overload_on("SET_ADDITIVE",
   ``\f. (f {} = 0) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) + f (s INTER t) = f s + f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = SIGMA f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 0                   by SET_ADDITIVE f
       = SIGMA f {} = RHS    by SUM_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = SIGMA f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 0  by SET_ADDITIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) + f (e INTER (BIGUNION P))     by ADD_0
       = f e + f (BIGUNION P)                                     by SET_ADDITIVE f
       = f e + SIGMA f P                   by induction hypothesis
       = f e + SIGMA f (P DELETE e)        by DELETE_NON_ELEMENT
       = SIGMA f (e INSERT P)              by SUM_IMAGE_THM
*)
val disjoint_bigunion_add_fun = store_thm(
  "disjoint_bigunion_add_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_ADDITIVE f ==> (f (BIGUNION P) = SIGMA f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, SUM_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, SUM_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 0` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) + f (e INTER (BIGUNION P))` by decide_tac >>
  `_ = f e + f (BIGUNION P)` by metis_tac[] >>
  `_ = f e + SIGMA f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: SET_ADDITIVE CARD *)
(* Proof:
   Since CARD {} = 0                    by CARD_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t   by CARD_UNION
   Hence SET_ADDITIVE CARD              by notation
*)
val set_additive_card = store_thm(
  "set_additive_card",
  ``SET_ADDITIVE CARD``,
  rw[FUN_EQ_THM, CARD_UNION]);

(* Note: DISJ_BIGUNION_CARD is only a prove_thm in pred_setTheoryScript.sml *)
(*
g `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)`
e (PSet_ind.SET_INDUCT_TAC FINITE_INDUCT);
Q. use of this changes P to s, s to s', how?
*)

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P) *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_card *)
val disjoint_bigunion_card = store_thm(
  "disjoint_bigunion_card",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)``,
  rw[disjoint_bigunion_add_fun, set_additive_card]);

(* Theorem alias *)
Theorem CARD_BIGUNION_PAIR_DISJOINT = disjoint_bigunion_card;
(*
val CARD_BIGUNION_PAIR_DISJOINT =
   |- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
          CARD (BIGUNION P) = SIGMA CARD P: thm
*)

(* Theorem: SET_ADDITIVE (SIGMA f) *)
(* Proof:
   Since SIGMA f {} = 0         by SUM_IMAGE_EMPTY
     and !s t. FINITE s /\ FINITE t
     ==> SIGMA f (s UNION t) + SIGMA f (s INTER t) = SIGMA f s + SIGMA f t   by SUM_IMAGE_UNION_EQN
   Hence SET_ADDITIVE (SIGMA f)
*)
val set_additive_sigma = store_thm(
  "set_additive_sigma",
  ``!f. SET_ADDITIVE (SIGMA f)``,
  rw[SUM_IMAGE_EMPTY, SUM_IMAGE_UNION_EQN]);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P *)
(* Proof: by disjoint_bigunion_add_fun, set_additive_sigma *)
val disjoint_bigunion_sigma = store_thm(
  "disjoint_bigunion_sigma",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> !f. SIGMA f (BIGUNION P) = SIGMA (SIGMA f) P``,
  rw[disjoint_bigunion_add_fun, set_additive_sigma]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ !t. t IN P ==> FINITE t    by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = SIGMA f P   by disjoint_bigunion_add_fun
      or f s = SIGMA f P              by above, BIGUNION_partition
*)
val set_add_fun_by_partition = store_thm(
  "set_add_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_ADDITIVE f ==> (f s = SIGMA f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_add_fun]);

(* Theorem: R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s)) *)
(* Proof: by set_add_fun_by_partition, set_additive_card *)
val set_card_by_partition = store_thm(
  "set_card_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> (CARD s = SIGMA CARD (partition R s))``,
  rw[set_add_fun_by_partition, set_additive_card]);

(* This is pred_setTheory.partition_CARD *)

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s) *)
(* Proof: by set_add_fun_by_partition, set_additive_sigma *)
val set_sigma_by_partition = store_thm(
  "set_sigma_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SIGMA f s = SIGMA (SIGMA f) (partition R s)``,
  rw[set_add_fun_by_partition, set_additive_sigma]);

(* Overload a multiplicative set function *)
val _ = overload_on("SET_MULTIPLICATIVE",
   ``\f. (f {} = 1) /\ (!s t. FINITE s /\ FINITE t ==> (f (s UNION t) * f (s INTER t) = f s * f t))``);

(* Theorem: FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
            !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P) *)
(* Proof:
   By finite induction on P.
   Base: f (BIGUNION {}) = PI f {}
         f (BIGUNION {})
       = f {}                by BIGUNION_EMPTY
       = 1                   by SET_MULTIPLICATIVE f
       = PI f {} = RHS       by PROD_IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = PI f (e INSERT P)
       Given !s. s IN e INSERT P ==> FINITE s
        thus !s. (s = e) \/ s IN P ==> FINITE s   by IN_INSERT
       hence FINITE e              by implication
         and EVERY_FINITE P        by IN_INSERT
         and FINITE (BIGUNION P)   by FINITE_BIGUNION
       Given PAIR_DISJOINT (e INSERT P)
          so PAIR_DISJOINT P               by IN_INSERT
         and !s. s IN P ==> DISJOINT e s   by IN_INSERT
       hence DISJOINT e (BIGUNION P)       by DISJOINT_BIGUNION
          so e INTER (BIGUNION P) = {}     by DISJOINT_DEF
         and f (e INTER (BIGUNION P)) = 1  by SET_MULTIPLICATIVE f
         f (BIGUNION (e INSERT P)
       = f (BIGUNION (e INSERT P)) * f (e INTER (BIGUNION P))     by MULT_RIGHT_1
       = f e * f (BIGUNION P)                                     by SET_MULTIPLICATIVE f
       = f e * PI f P                      by induction hypothesis
       = f e * PI f (P DELETE e)           by DELETE_NON_ELEMENT
       = PI f (e INSERT P)                 by PROD_IMAGE_THM
*)
val disjoint_bigunion_mult_fun = store_thm(
  "disjoint_bigunion_mult_fun",
  ``!P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)``,
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P ==>
   !f. SET_MULTIPLICATIVE f ==> (f (BIGUNION P) = PI f P)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw_tac std_ss[BIGUNION_EMPTY, PROD_IMAGE_EMPTY] >>
  rw_tac std_ss[BIGUNION_INSERT, PROD_IMAGE_THM] >>
  `FINITE e /\ FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `EVERY_FINITE P /\ PAIR_DISJOINT P` by rw[] >>
  `!s. s IN P ==> DISJOINT e s` by metis_tac[IN_INSERT] >>
  `f (e INTER (BIGUNION P)) = 1` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) * f (e INTER (BIGUNION P))` by metis_tac[MULT_RIGHT_1] >>
  `_ = f e * f (BIGUNION P)` by metis_tac[] >>
  `_ = f e * PI f P` by prove_tac[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s)) *)
(* Proof:
   Let P = partition R s.
    Then FINITE s
     ==> FINITE P /\ EVERY_FINITE P   by FINITE_partition
     and R equiv_on s
     ==> BIGUNION P = s               by BIGUNION_partition
     ==> PAIR_DISJOINT P              by partition_elements_disjoint
   Hence f (BIGUNION P) = PI f P      by disjoint_bigunion_mult_fun
      or f s = PI f P                 by above, BIGUNION_partition
*)
val set_mult_fun_by_partition = store_thm(
  "set_mult_fun_by_partition",
  ``!R s. R equiv_on s /\ FINITE s ==> !f. SET_MULTIPLICATIVE f ==> (f s = PI f (partition R s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition R s` >>
  `FINITE P /\ !t. t IN P ==> FINITE t` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  rw[disjoint_bigunion_mult_fun]);

(* Theorem: FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
      LHS = SIGMA f (IMAGE g {})
          = SIGMA f {}                    by IMAGE_EMPTY
          = 0                             by SUM_IMAGE_EMPTY
          = SIGMA (f o g) {} = RHS        by SUM_IMAGE_EMPTY
   Step: e NOTIN s ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note INJ g (e INSERT s) univ(:'a)
       ==> INJ g s univ(:'a) /\ g e IN univ(:'a) /\
           !y. y IN s /\ (g e = g y) ==> (e = y)       by INJ_INSERT
      Thus g e NOTIN (IMAGE g s)                       by IN_IMAGE
        SIGMA f (IMAGE g (e INSERT s))
      = SIGMA f (g e INSERT IMAGE g s)    by IMAGE_INSERT
      = f (g e) + SIGMA f (IMAGE g s)     by SUM_IMAGE_THM, g e NOTIN (IMAGE g s)
      = f (g e) + SIGMA (f o g) s         by induction hypothesis
      = (f o g) e + SIGMA (f o g) s       by composition
      = SIGMA (f o g) (e INSERT s)        by SUM_IMAGE_THM, e NOTIN s
*)
val sum_image_by_composition = store_thm(
  "sum_image_by_composition",
  ``!s. FINITE s ==> !g. INJ g s univ(:'a) ==> !f. SIGMA f (IMAGE g s) = SIGMA (f o g) s``,
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  `INJ g s univ(:'a) /\ g e IN univ(:'a) /\ !y. y IN s /\ (g e = g y) ==> (e = y)` by metis_tac[INJ_INSERT] >>
  `g e NOTIN (IMAGE g s)` by metis_tac[IN_IMAGE] >>
  `(s DELETE e = s) /\ (IMAGE g s DELETE g e = IMAGE g s)` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[SUM_IMAGE_THM]);

(* Overload on permutation *)
val _ = overload_on("PERMUTES", ``\f s. BIJ f s s``);
val _ = set_fixity "PERMUTES" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s *)
(* Proof:
   Given permutate g s = BIJ g s s       by notation
     ==> INJ g s s /\ SURJ g s s         by BIJ_DEF
     Now SURJ g s s ==> IMAGE g s = s    by IMAGE_SURJ
    Also s SUBSET univ(:'a)              by SUBSET_UNIV
     and s SUBSET s                      by SUBSET_REFL
   Hence INJ g s univ(:'a)               by INJ_SUBSET
    With FINITE s,
      SIGMA (f o g) s
    = SIGMA f (IMAGE g s)                by sum_image_by_composition
    = SIGMA f s                          by above
*)
val sum_image_by_permutation = store_thm(
  "sum_image_by_permutation",
  ``!s. FINITE s ==> !g. g PERMUTES s ==> !f. SIGMA (f o g) s = SIGMA f s``,
  rpt strip_tac >>
  `INJ g s s /\ SURJ g s s` by metis_tac[BIJ_DEF] >>
  `IMAGE g s = s` by rw[GSYM IMAGE_SURJ] >>
  `s SUBSET univ(:'a)` by rw[SUBSET_UNIV] >>
  `INJ g s univ(:'a)` by metis_tac[INJ_SUBSET, SUBSET_REFL] >>
  `SIGMA (f o g) s = SIGMA f (IMAGE g s)` by rw[sum_image_by_composition] >>
  rw[]);

(* Theorem: FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
            !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:num -> bool)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   Let s1 = {x | x IN s /\ (g x = {})},
       s2 = {x | x IN s /\ (g x <> {})}.
    Then s = s1 UNION s2                             by EXTENSION
     and DISJOINT s1 s2                              by EXTENSION, DISJOINT_DEF
     and DISJOINT (IMAGE g s1) (IMAGE g s2)          by EXTENSION, DISJOINT_DEF
     Now s1 SUBSET s /\ s1 SUBSET s                  by SUBSET_DEF
   Since FINITE s                                    by given
    thus FINITE s1 /\ FINITE s2                      by SUBSET_FINITE
     and FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)  by IMAGE_FINITE

   Step 1: decompose left summation
         SIGMA f (IMAGE g s)
       = SIGMA f (IMAGE g (s1 UNION s2))             by above, s = s1 UNION s2
       = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))   by IMAGE_UNION
       = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2) by SUM_IMAGE_DISJOINT

   Claim: SIGMA f (IMAGE g s1) = 0
   Proof: If s1 = {},
            SIGMA f (IMAGE g {})
          = SIGMA f {}                               by IMAGE_EMPTY
          = 0                                        by SUM_IMAGE_EMPTY
          If s1 <> {},
            Note !x. x IN s1 ==> (g x = {})          by definition of s1
            Thus !y. y IN (IMAGE g s1) ==> (y = {})  by IN_IMAGE, IMAGE_EMPTY
           Since s1 <> {}, IMAGE g s1 = {{}}         by SING_DEF, IN_SING, SING_ONE_ELEMENT
            SIGMA f (IMAGE g {})
          = SIGMA f {{}}                             by above
          = f {}                                     by SUM_IMAGE_SING
          = 0                                        by given

   Step 2: decompose right summation
    Also SIGMA (f o g) s
       = SIGMA (f o g) (s1 UNION s2)                 by above, s = s1 UNION s2
       = SIGMA (f o g) s1 + SIGMA (f o g) s2         by SUM_IMAGE_DISJOINT

   Claim: SIGMA (f o g) s1 = 0
   Proof: Note !x. x IN s1 ==> (g x = {})            by definition of s1
             (f o g) x
            = f (g x)                                by function application
            = f {}                                   by above
            = 0                                      by given
          Hence SIGMA (f o g) s1
              = 0 * CARD s1                          by SIGMA_CONSTANT
              = 0                                    by MULT

   Claim: SIGMA f (IMAGE g s2) = SIGMA (f o g) s2
   Proof: Note !x. x IN s2 ==> g x <> {}             by definition of s2
          Thus INJ g s2 univ(:'b -> bool)            by given
          Hence SIGMA f (IMAGE g s2)
              = SIGMA (f o g) (s2)                   by sum_image_by_composition

   Result follows by combining all the claims and arithmetic.
*)
val sum_image_by_composition_with_partial_inj = store_thm(
  "sum_image_by_composition_with_partial_inj",
  ``!s. FINITE s ==> !f:('b -> bool) -> num. (f {} = 0) ==>
   !g. (!t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==> INJ g t univ(:'b -> bool)) ==>
   (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  rpt strip_tac >>
  qabbrev_tac `s1 = {x | x IN s /\ (g x = {})}` >>
  qabbrev_tac `s2 = {x | x IN s /\ (g x <> {})}` >>
  (`s = s1 UNION s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION] >> metis_tac[])) >>
  (`DISJOINT s1 s2` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  (`DISJOINT (IMAGE g s1) (IMAGE g s2)` by (rw[Abbr`s1`, Abbr`s2`, EXTENSION, DISJOINT_DEF] >> metis_tac[])) >>
  `s1 SUBSET s /\ s2 SUBSET s` by rw[Abbr`s1`, Abbr`s2`, SUBSET_DEF] >>
  `FINITE s1 /\ FINITE s2` by metis_tac[SUBSET_FINITE] >>
  `FINITE (IMAGE g s1) /\ FINITE (IMAGE g s2)` by rw[] >>
  `SIGMA f (IMAGE g s) = SIGMA f ((IMAGE g s1) UNION (IMAGE g s2))` by rw[] >>
  `_ = SIGMA f (IMAGE g s1) + SIGMA f (IMAGE g s2)` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA f (IMAGE g s1) = 0` by
  (Cases_on `s1 = {}` >-
  rw[SUM_IMAGE_EMPTY] >>
  `!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!y. y IN (IMAGE g s1) ==> (y = {})` by metis_tac[IN_IMAGE, IMAGE_EMPTY] >>
  `{} IN {{}} /\ IMAGE g s1 <> {}` by rw[] >>
  `IMAGE g s1 = {{}}` by metis_tac[SING_DEF, IN_SING, SING_ONE_ELEMENT] >>
  `SIGMA f (IMAGE g s1) = f {}` by rw[SUM_IMAGE_SING] >>
  rw[]
  ) >>
  `SIGMA (f o g) s = SIGMA (f o g) s1 + SIGMA (f o g) s2` by rw[SUM_IMAGE_DISJOINT] >>
  `SIGMA (f o g) s1 = 0` by
    (`!x. x IN s1 ==> (g x = {})` by rw[Abbr`s1`] >>
  `!x. x IN s1 ==> ((f o g) x = 0)` by rw[] >>
  metis_tac[SIGMA_CONSTANT, MULT]) >>
  `SIGMA f (IMAGE g s2) = SIGMA (f o g) s2` by
      (`!x. x IN s2 ==> g x <> {}` by rw[Abbr`s2`] >>
  `INJ g s2 univ(:'b -> bool)` by rw[] >>
  rw[sum_image_by_composition]) >>
  decide_tac);

(* Theorem: FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
            (SIGMA f (IMAGE g s) = SIGMA (f o g) s) *)
(* Proof:
   By finite induction on s.
   Base: SIGMA f (IMAGE g {}) = SIGMA (f o g) {}
        SIGMA f (IMAGE g {})
      = SIGMA f {}                 by IMAGE_EMPTY
      = 0                          by SUM_IMAGE_EMPTY
      = SIGMA (f o g) {}           by SUM_IMAGE_EMPTY
   Step: !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
         (SIGMA f (IMAGE g s) = SIGMA (f o g) s) ==>
         e NOTIN s /\ !x y. x IN e INSERT s /\ y IN e INSERT s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)
         ==> SIGMA f (IMAGE g (e INSERT s)) = SIGMA (f o g) (e INSERT s)
      Note !x y. ((x = e) \/ x IN s) /\ ((y = e) \/ y IN s) /\ (g x = g y) ==>
                 (x = y) \/ (f (g y) = 0)       by IN_INSERT
      If g e IN IMAGE g s,
         Then ?x. x IN s /\ (g x = g e)         by IN_IMAGE
          and x <> e /\ (f (g e) = 0)           by implication
           SIGMA f (g e INSERT IMAGE g s)
         = SIGMA f (IMAGE g s)                  by ABSORPTION, g e IN IMAGE g s
         = SIGMA (f o g) s                      by induction hypothesis
         = f (g x) + SIGMA (f o g) s            by ADD
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
      If g e NOTIN IMAGE g s,
           SIGMA f (g e INSERT IMAGE g s)
         = f (g e) + SIGMA f (IMAGE g s)        by SUM_IMAGE_INSERT, g e NOTIN IMAGE g s
         = f (g e) + SIGMA (f o g) s            by induction hypothesis
         = (f o g) e + SIGMA (f o g) s          by o_THM
         = SIGMA (f o g) (e INSERT s)           by SUM_IMAGE_INSERT, e NOTIN s
*)
val sum_image_by_composition_without_inj = store_thm(
  "sum_image_by_composition_without_inj",
  ``!s. FINITE s ==> !f g. (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y) \/ (f (g x) = 0)) ==>
       (SIGMA f (IMAGE g s) = SIGMA (f o g) s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[SUM_IMAGE_EMPTY] >>
  fs[] >>
  Cases_on `g e IN IMAGE g s` >| [
    `?x. x IN s /\ (g x = g e)` by metis_tac[IN_IMAGE] >>
    `x <> e /\ (f (g e) = 0)` by metis_tac[] >>
    `SIGMA f (g e INSERT IMAGE g s) = SIGMA f (IMAGE g s)` by metis_tac[ABSORPTION] >>
    `_ = SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[],
    `SIGMA f (g e INSERT IMAGE g s) = f (g e) + SIGMA f (IMAGE g s)` by rw[SUM_IMAGE_INSERT] >>
    `_ = f (g e) + SIGMA (f o g) s` by rw[] >>
    `_ = (f o g) e + SIGMA (f o g) s` by rw[] >>
    `_ = SIGMA (f o g) (e INSERT s)` by rw[SUM_IMAGE_INSERT] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Pre-image Theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

(*
- IN_IMAGE;
> val it = |- !y s f. y IN IMAGE f s <=> ?x. (y = f x) /\ x IN s : thm
*)

(* Define preimage *)
val preimage_def = Define `preimage f s y = { x | x IN s /\ (f x = y) }`;

(* Theorem: x IN (preimage f s y) <=> x IN s /\ (f x = y) *)
(* Proof: by preimage_def *)
val preimage_element = store_thm(
  "preimage_element",
  ``!f s x y. x IN (preimage f s y) <=> x IN s /\ (f x = y)``,
  rw[preimage_def]);

(* Theorem: x IN preimage f s y <=> (x IN s /\ (f x = y)) *)
(* Proof: by preimage_def *)
val in_preimage = store_thm(
  "in_preimage",
  ``!f s x y. x IN preimage f s y <=> (x IN s /\ (f x = y))``,
  rw[preimage_def]);
(* same as theorem above. *)

(* Theorem: (preimage f s y) SUBSET s *)
(* Proof:
       x IN preimage f s y
   <=> x IN s /\ f x = y           by in_preimage
   ==> x IN s
   Thus (preimage f s y) SUBSET s  by SUBSET_DEF
*)
Theorem preimage_subset:
  !f s y. (preimage f s y) SUBSET s
Proof
  simp[preimage_def, SUBSET_DEF]
QED

(* Theorem: FINITE s ==> FINITE (preimage f s y) *)
(* Proof:
   Note (preimage f s y) SUBSET s  by preimage_subset
   Thus FINITE (preimage f s y)    by SUBSET_FINITE
*)
Theorem preimage_finite:
  !f s y. FINITE s ==> FINITE (preimage f s y)
Proof
  metis_tac[preimage_subset, SUBSET_FINITE]
QED

(* Theorem: !x. x IN preimage f s y ==> f x = y *)
(* Proof: by definition. *)
val preimage_property = store_thm(
  "preimage_property",
  ``!f s y. !x. x IN preimage f s y ==> (f x = y)``,
  rw[preimage_def]);

(* This is bad: every pattern of f x = y (i.e. practically every equality!) will invoke the check: x IN preimage f s y! *)
(* val _ = export_rewrites ["preimage_property"]; *)

(* Theorem: x IN s ==> x IN preimage f s (f x) *)
(* Proof: by IN_IMAGE. preimage_def. *)
val preimage_of_image = store_thm(
  "preimage_of_image",
  ``!f s x. x IN s ==> x IN preimage f s (f x)``,
  rw[preimage_def]);

(* Theorem: y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ f (CHOICE (preimage f s y)) = y *)
(* Proof:
   (1) prove: y IN IMAGE f s ==> CHOICE (preimage f s y) IN s
   By IN_IMAGE, this is to show:
   x IN s ==> CHOICE (preimage f s (f x)) IN s
   Now, preimage f s (f x) <> {}   since x is a pre-image.
   hence CHOICE (preimage f s (f x)) IN preimage f s (f x) by CHOICE_DEF
   hence CHOICE (preimage f s (f x)) IN s                  by preimage_def
   (2) prove: y IN IMAGE f s /\ CHOICE (preimage f s y) IN s ==> f (CHOICE (preimage f s y)) = y
   By IN_IMAGE, this is to show: x IN s ==> f (CHOICE (preimage f s (f x))) = f x
   Now, x IN preimage f s (f x)   by preimage_of_image
   hence preimage f s (f x) <> {}  by MEMBER_NOT_EMPTY
   thus  CHOICE (preimage f s (f x)) IN (preimage f s (f x))  by CHOICE_DEF
   hence f (CHOICE (preimage f s (f x))) = f x  by preimage_def
*)
val preimage_choice_property = store_thm(
  "preimage_choice_property",
  ``!f s y. y IN (IMAGE f s) ==> CHOICE (preimage f s y) IN s /\ (f (CHOICE (preimage f s y)) = y)``,
  rpt gen_tac >>
  strip_tac >>
  conj_asm1_tac >| [
    full_simp_tac std_ss [IN_IMAGE] >>
    `CHOICE (preimage f s (f x)) IN preimage f s (f x)` suffices_by rw[preimage_def] >>
    metis_tac[CHOICE_DEF, preimage_of_image, MEMBER_NOT_EMPTY],
    full_simp_tac std_ss [IN_IMAGE] >>
    `x IN preimage f s (f x)` by rw_tac std_ss[preimage_of_image] >>
    `CHOICE (preimage f s (f x)) IN (preimage f s (f x))` by metis_tac[CHOICE_DEF, MEMBER_NOT_EMPTY] >>
    full_simp_tac std_ss [preimage_def, GSPECIFICATION]
  ]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x}) *)
(* Proof:
     preimage f s (f x)
   = {x' | x' IN s /\ (f x' = f x)}    by preimage_def
   = {x' | x' IN s /\ (x' = x)}        by INJ_DEF
   = {x}                               by EXTENSION
*)
val preimage_inj = store_thm(
  "preimage_inj",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (preimage f s (f x) = {x})``,
  rw[preimage_def, EXTENSION] >>
  metis_tac[INJ_DEF]);

(* Theorem: INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x) *)
(* Proof:
     CHOICE (preimage f s (f x))
   = CHOICE {x}                     by preimage_inj, INJ f s univ(:'b)
   = x                              by CHOICE_SING
*)
val preimage_inj_choice = store_thm(
  "preimage_inj_choice",
  ``!f s. INJ f s univ(:'b) ==> !x. x IN s ==> (CHOICE (preimage f s (f x)) = x)``,
  rw[preimage_inj]);

(* Theorem: INJ (preimage f s) (IMAGE f s) (POW s) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN s ==> preimage f s (f x) IN POW s
       Let y = preimage f s (f x).
       Then y SUBSET s                         by preimage_subset
         so y IN (POW s)                       by IN_POW
   (2) x IN s /\ y IN s /\ preimage f s (f x) = preimage f s (f y) ==> f x = f y
       Note (f x) IN preimage f s (f x)        by in_preimage
         so (f y) IN preimage f s (f y)        by given
       Thus f x = f y                          by in_preimage
*)
Theorem preimage_image_inj:
  !f s. INJ (preimage f s) (IMAGE f s) (POW s)
Proof
  rw[INJ_DEF] >-
  simp[preimage_subset, IN_POW] >>
  metis_tac[in_preimage]
QED

(* ------------------------------------------------------------------------- *)
(* Function Equivalence as Relation                                          *)
(* ------------------------------------------------------------------------- *)

(* For function f on a domain D, x, y in D are "equal" if f x = f y. *)
Definition fequiv_def:
  fequiv x y f <=> (f x = f y)
End
Overload "==" = ``fequiv``
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [Reflexive] (x == x) f *)
(* Proof: by definition,
   and f x = f x.
*)
Theorem fequiv_refl[simp]:  !f x. (x == x) f
Proof rw_tac std_ss[fequiv_def]
QED

(* Theorem: [Symmetric] (x == y) f ==> (y == x) f *)
(* Proof: by defintion,
   and f x = f y means the same as f y = f x.
*)
val fequiv_sym = store_thm(
  "fequiv_sym",
  ``!f x y. (x == y) f ==> (y == x) f``,
  rw_tac std_ss[fequiv_def]);

(* no export of commutativity *)

(* Theorem: [Transitive] (x == y) f /\ (y == z) f ==> (x == z) f *)
(* Proof: by defintion,
   and f x = f y
   and f y = f z
   implies f x = f z.
*)
val fequiv_trans = store_thm(
  "fequiv_trans",
  ``!f x y z. (x == y) f /\ (y == z) f ==> (x == z) f``,
  rw_tac std_ss[fequiv_def]);

(* Theorem: fequiv (==) is an equivalence relation on the domain. *)
(* Proof: by reflexive, symmetric and transitive. *)
val fequiv_equiv_class = store_thm(
  "fequiv_equiv_class",
  ``!f. (\x y. (x == y) f) equiv_on univ(:'a)``,
  rw_tac std_ss[equiv_on_def, fequiv_def, EQ_IMP_THM]);

(* ------------------------------------------------------------------------- *)
(* Function-based Equivalence                                                *)
(* ------------------------------------------------------------------------- *)

Overload feq = “flip (flip o fequiv)”
Overload feq_class[inferior] = “preimage”

(* Theorem: x IN feq_class f s n <=> x IN s /\ (f x = n) *)
(* Proof: by feq_class_def *)
Theorem feq_class_element = in_preimage

(* Note:
    y IN equiv_class (feq f) s x
<=> y IN s /\ (feq f x y)      by equiv_class_element
<=> y IN s /\ (f x = f y)      by feq_def
*)

(* Theorem: feq_class f s (f x) = equiv_class (feq f) s x *)
(* Proof:
     feq_class f s (f x)
   = {y | y IN s /\ (f y = f x)}    by feq_class_def
   = {y | y IN s /\ (f x = f y)}
   = {y | y IN s /\ (feq f x y)}    by feq_def
   = equiv_class (feq f) s x        by notation
*)
val feq_class_property = store_thm(
  "feq_class_property",
  ``!f s x. feq_class f s (f x) = equiv_class (feq f) s x``,
  rw[in_preimage, EXTENSION, fequiv_def] >> metis_tac[]);

(* Theorem: (feq_class f s) o f = equiv_class (feq f) s *)
(* Proof: by FUN_EQ_THM, feq_class_property *)
val feq_class_fun = store_thm(
  "feq_class_fun",
  ``!f s. (feq_class f s) o f = equiv_class (feq f) s``,
  rw[FUN_EQ_THM, feq_class_property]);

(* Theorem: feq f equiv_on s *)
(* Proof: by equiv_on_def, feq_def *)
val feq_equiv = store_thm(
  "feq_equiv",
  ``!s f. feq f equiv_on s``,
  rw[equiv_on_def, fequiv_def] >>
  metis_tac[]);

(* Theorem: partition (feq f) s = IMAGE ((feq_class f s) o f) s *)
(* Proof:
   Use partition_def |> ISPEC ``feq f`` |> ISPEC ``(s:'a -> bool)``;

    partition (feq f) s
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ feq f x y})}     by partition_def
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ (f x = f y)})}   by feq_def
  = {t | ?x. x IN s /\ (t = feq_class f s (f x))}           by feq_class_def
  = {feq_class f s (f x) | x | x IN s }                     by rewriting
  = IMAGE (feq_class f s) (IMAGE f s)                       by IN_IMAGE
  = IMAGE ((feq_class f s) o f) s                           by IMAGE_COMPOSE
*)
val feq_partition = store_thm(
  "feq_partition",
  ``!s f. partition (feq f) s = IMAGE ((feq_class f s) o f) s``,
  rw[partition_def, fequiv_def, in_preimage, EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: t IN partition (feq f) s <=> ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z)) *)
(* Proof: by feq_partition, feq_class_def, EXTENSION *)
Theorem feq_partition_element:
  !s f t. t IN partition (feq f) s <=>
          ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z))
Proof
  rw[feq_partition, in_preimage, EXTENSION] >> metis_tac[]
QED

(* Theorem: x IN s <=> ?e. e IN partition (feq f) s /\ x IN e *)
(* Proof:
   Note (feq f) equiv_on s         by feq_equiv
   This result follows             by partition_element_exists
*)
Theorem feq_partition_element_exists:
  !f s x. x IN s <=> ?e. e IN partition (feq f) s /\ x IN e
Proof
  simp[feq_equiv, partition_element_exists]
QED

(* Theorem: e IN partition (feq f) s ==> e <> {} *)
(* Proof:
   Note (feq f) equiv_on s     by feq_equiv
     so e <> {}                by partition_element_not_empty
*)
Theorem feq_partition_element_not_empty:
  !f s e. e IN partition (feq f) s ==> e <> {}
Proof
  metis_tac[feq_equiv, partition_element_not_empty]
QED

(* Theorem: partition (feq f) s = IMAGE (preimage f s o f) s *)
(* Proof:
       x IN partition (feq f) s
   <=> ?z. z IN s /\ !j. j IN x <=> j IN s /\ (f j = f z)      by feq_partition_element
   <=> ?z. z IN s /\ !j. j IN x <=> j IN (preimage f s (f z))  by preimage_element
   <=> ?z. z IN s /\ (x = preimage f s (f z))                  by EXTENSION
   <=> ?z. z IN s /\ (x = (preimage f s o f) z)                by composition (o_THM)
   <=> x IN IMAGE (preimage f s o f) s                         by IN_IMAGE
   Hence partition (feq f) s = IMAGE (preimage f s o f) s      by EXTENSION

   or,
     partition (feq f) s
   = IMAGE (feq_class f s o f) s     by feq_partition
   = IMAGE (preiamge f s o f) s      by feq_class_eq_preimage
*)
val feq_partition_by_preimage = feq_partition

(* Theorem: FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s) *)
(* Proof:
   Since (feq f) equiv_on s   by feq_equiv
   Hence !g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)  by set_sigma_by_partition
*)
val feq_sum_over_partition = store_thm(
  "feq_sum_over_partition",
  ``!s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s) *)
(* Proof:
   Note feq equiv_on s   by feq_equiv
   The result follows    by partition_CARD
*)
val finite_card_by_feq_partition = store_thm(
  "finite_card_by_feq_partition",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)``,
  rw[feq_equiv, partition_CARD]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s) *)
(* Proof:
   Note (feq f) equiv_on s                       by feq_equiv
        CARD s
      = SIGMA CARD (partition (feq f) s)         by partition_CARD
      = SIGMA CARD (IMAGE (preimage f s o f) s)  by feq_partition_by_preimage
*)
val finite_card_by_image_preimage = store_thm(
  "finite_card_by_image_preimage",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s)``,
  rw[feq_equiv, partition_CARD, GSYM feq_partition]);

(* Theorem: FINITE s /\ SURJ f s t ==>
            CARD s = SIGMA CARD (IMAGE (preimage f s) t) *)
(* Proof:
     CARD s
   = SIGMA CARD (IMAGE (preimage f s o f) s)           by finite_card_by_image_preimage
   = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))     by IMAGE_COMPOSE
   = SIGMA CARD (IMAGE (preimage f s) t)               by IMAGE_SURJ
*)
Theorem finite_card_surj_by_image_preimage:
  !f s t. FINITE s /\ SURJ f s t ==>
          CARD s = SIGMA CARD (IMAGE (preimage f s) t)
Proof
  rpt strip_tac >>
  `CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)` by rw[finite_card_by_image_preimage] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))` by rw[IMAGE_COMPOSE] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) t)` by fs[IMAGE_SURJ] >>
  simp[]
QED

(* Theorem: BIJ (preimage f s) (IMAGE f s) (partition (feq f) s) *)
(* Proof:
   Let g = preimage f s, t = IMAGE f s.
   Note INJ g t (POW s)                        by preimage_image_inj
     so BIJ g t (IMAGE g t)                    by INJ_IMAGE_BIJ
    But IMAGE g t
      = IMAGE (preimage f s) (IMAGE f s)       by notation
      = IMAGE (preimage f s o f) s             by IMAGE_COMPOSE
      = partition (feq f) s                    by feq_partition_by_preimage
   Thus BIJ g t (partition (feq f) s)          by above
*)
Theorem preimage_image_bij:
  !f s. BIJ (preimage f s) (IMAGE f s) (partition (feq f) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = preimage f s` >>
  qabbrev_tac `t = IMAGE f s` >>
  `BIJ g t (IMAGE g t)` by metis_tac[preimage_image_inj, INJ_IMAGE_BIJ] >>
  simp[IMAGE_COMPOSE, feq_partition, Abbr`g`, Abbr`t`]
QED

(* ------------------------------------------------------------------------- *)
(* Condition for surjection to be a bijection.                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e *)
(* Proof:
   If part: e IN partition (feq f) s ==> SING e
          e IN partition (feq f) s
      <=> ?z. z IN s /\ !x. x IN e <=> x IN s /\ f x = f z
                                               by feq_partition_element
      Thus z IN e, so e <> {}                  by MEMBER_NOT_EMPTY
       and !x. x IN e ==> x = z                by INJ_DEF
        so SING e                              by SING_ONE_ELEMENT
   Only-if part: !e. e IN partition (feq f) s ==> SING e ==> INJ f s (IMAGE f s)
      By INJ_DEF, IN_IMAGE, this is to show:
         !x y. x IN s /\ y IN s /\ f x = f y ==> x = y
      Note ?e. e IN (partition (feq f) s) /\ x IN e
                                               by feq_partition_element_exists
       and y IN e                              by feq_partition_element
      then SING e                              by implication
        so x = y                               by IN_SING
*)
Theorem inj_iff_partition_element_sing:
  !f s. INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e
Proof
  rw[EQ_IMP_THM] >| [
    fs[feq_partition_element, INJ_DEF] >>
    `e <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    simp[SING_ONE_ELEMENT],
    rw[INJ_DEF] >>
    `?e. e IN (partition (feq f) s) /\ x IN e` by fs[GSYM feq_partition_element_exists] >>
    `y IN e` by metis_tac[feq_partition_element] >>
    metis_tac[SING_DEF, IN_SING]
  ]
QED

(* Theorem: FINITE s ==>
            (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1) *)
(* Proof:
       INJ f s (IMAGE f s)
   <=> !e. e IN (partition (feq f) s) ==> SING e       by inj_iff_partition_element_sing
   <=> !e. e IN (partition (feq f) s) ==> CARD e = 1   by FINITE_partition, CARD_EQ_1
*)
Theorem inj_iff_partition_element_card_1:
  !f s. FINITE s ==>
        (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1)
Proof
  metis_tac[inj_iff_partition_element_sing, FINITE_partition, CARD_EQ_1]
QED

(* Idea: for a finite domain, with target same size, surjection means injection. *)

(* Theorem: FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t *)
(* Proof:
   Let p = partition (feq f) s.
   Note IMAGE f s = t              by IMAGE_SURJ
     so FINITE t                   by IMAGE_FINITE
    and CARD s = SIGMA CARD p      by finite_card_by_feq_partition
    and CARD t = CARD p            by preimage_image_bij, bij_eq_card
   Thus CARD p = SIGMA CARD p      by given CARD s = CARD t
    Now FINITE p                   by FINITE_partition
    and !e. e IN p ==> FINITE e    by FINITE_partition
    and !e. e IN p ==> e <> {}     by feq_partition_element_not_empty
     so !e. e IN p ==> CARD e <> 0 by CARD_EQ_0
   Thus !e. e IN p ==> CARD e = 1  by card_eq_sigma_card
     or INJ f s (IMAGE f s)        by inj_iff_partition_element_card_1
     so INJ f s t                  by IMAGE f s = t
*)
Theorem FINITE_SURJ_IS_INJ:
  !f s t. FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t
Proof
  rpt strip_tac >>
  imp_res_tac finite_card_by_feq_partition >>
  first_x_assum (qspec_then `f` strip_assume_tac) >>
  qabbrev_tac `p = partition (feq f) s` >>
  `IMAGE f s = t` by fs[IMAGE_SURJ] >>
  `FINITE t` by rw[] >>
  `CARD t = CARD p` by metis_tac[preimage_image_bij, FINITE_BIJ_CARD] >>
  `FINITE p /\ !e. e IN p ==> FINITE e` by metis_tac[FINITE_partition] >>
  `!e. e IN p ==> CARD e <> 0` by metis_tac[feq_partition_element_not_empty, CARD_EQ_0] >>
  `!e. e IN p ==> CARD e = 1` by metis_tac[card_eq_sigma_card] >>
  metis_tac[inj_iff_partition_element_card_1]
QED

(* ------------------------------------------------------------------------- *)
(* Function Iteration                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f (n*k) e = e *)
(* Proof:
   By induction on n:
   Base case: FUNPOW f (0 * k) e = e
     FUNPOW f (0 * k) e
   = FUNPOW f 0 e          by arithmetic
   = e                     by FUNPOW_0
   Step case: FUNPOW f (n * k) e = e ==> FUNPOW f (SUC n * k) e = e
     FUNPOW f (SUC n * k) e
   = FUNPOW f (k + n * k) e         by arithmetic
   = FUNPOW f k (FUNPOW (n * k) e)  by FUNPOW_ADD.
   = FUNPOW f k e                   by induction hypothesis
   = e                              by given
*)
val FUNPOW_MULTIPLE = store_thm(
  "FUNPOW_MULTIPLE",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f (n*k) e = e``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[MULT_COMM, MULT_SUC, FUNPOW_ADD]);

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e *)
(* Proof:
     FUNPOW f n e
   = FUNPOW f ((n DIV k) * k + (n MOD k)) e       by division algorithm
   = FUNPOW f ((n MOD k) + (n DIV k) * k) e       by arithmetic
   = FUNPOW f (n MOD k) (FUNPOW (n DIV k) * k e)  by FUNPOW_ADD
   = FUNPOW f (n MOD k) e                         by FUNPOW_MULTIPLE
*)
val FUNPOW_MOD = store_thm(
  "FUNPOW_MOD",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e``,
  rpt strip_tac >>
  `n = (n MOD k) + (n DIV k) * k` by metis_tac[DIVISION, ADD_COMM] >>
  metis_tac[FUNPOW_ADD, FUNPOW_MULTIPLE]);

(* Overload a RISING function (temporalizaed by Chun Tian) *)
val _ = temp_overload_on ("RISING", ``\f. !x:num. x <= f x``);

(* Overload a FALLING function (temporalizaed by Chun Tian) *)
val _ = temp_overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* Theorem: RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f m x <= FUNPOW f 0 x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x ==>
          !m. m <= SUC n ==> FUNPOW f m x <= FUNPOW f (SUC n) x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
             FUNPOW f m x
          <= FUNPOW f n x            by induction hypothesis
          <= f (FUNPOW f n x)        by RISING f
           = FUNPOW f (SUC n) x      by FUNPOW_SUC
*)
val FUNPOW_LE_RISING = store_thm(
  "FUNPOW_LE_RISING",
  ``!f m n. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f m x <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= f (FUNPOW f n x)` by rw[] >>
    `f (FUNPOW f n x) = FUNPOW f (SUC n) x` by rw[FUNPOW_SUC] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f 0 x <= FUNPOW f m x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x ==>
          !m. m <= SUC n ==> FUNPOW f (SUC n) x <= FUNPOW f m x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
            FUNPOW f (SUC n) x
          = f (FUNPOW f n x)         by FUNPOW_SUC
         <= FUNPOW f n x             by FALLING f
         <= FUNPOW f m x             by induction hypothesis
*)
val FUNPOW_LE_FALLING = store_thm(
  "FUNPOW_LE_FALLING",
  ``!f m n. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f (SUC n) x = f (FUNPOW f n x)` by rw[FUNPOW_SUC] >>
    `f (FUNPOW f n x) <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= FUNPOW f m x` by rw[] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= g (FUNPOW f n x)      by !x. f x <= g x
      <= g (FUNPOW g n x)      by induction hypothesis, MONO g
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_LE_MONO = store_thm(
  "FUNPOW_LE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= g (FUNPOW f n x)` by rw[] >>
  `g (FUNPOW f n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note:
There is no FUNPOW_LE_RMONO. FUNPOW_LE_MONO says:
|- !f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x
To compare the terms in these two sequences:
     x, f x, f (f x), f (f (f x)), ......
     x, g x, g (g x), g (g (g x)), ......
For the first pair:       x <= x.
For the second pair:    f x <= g x,      as g is cover.
For the third pair: f (f x) <= g (f x)   by g is cover,
                            <= g (g x)   by MONO g, and will not work if RMONO g.
*)

(* Theorem: (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= f (FUNPOW g n x)      by induction hypothesis, MONO f
      <= g (FUNPOW g n x)      by !x. f x <= g x
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_GE_MONO = store_thm(
  "FUNPOW_GE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= f (FUNPOW g n x)` by rw[] >>
  `f (FUNPOW g n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note: the name FUNPOW_SUC is taken:
FUNPOW_SUC  |- !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
*)

(* Theorem: FUNPOW SUC n m = m + n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW SUC 0 m = m + 0
      LHS = FUNPOW SUC 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW SUC n m = m + n ==>
         !m. FUNPOW SUC (SUC n) m = m + SUC n
       FUNPOW SUC (SUC n) m
     = FUNPOW SUC n (SUC m)    by FUNPOW
     = (SUC m) + n             by induction hypothesis
     = m + SUC n               by arithmetic
*)
val FUNPOW_ADD1 = store_thm(
  "FUNPOW_ADD1",
  ``!m n. FUNPOW SUC n m = m + n``,
  Induct_on `n` >>
  rw[FUNPOW]);

(* Theorem: FUNPOW PRE n m = m - n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW PRE 0 m = m - 0
      LHS = FUNPOW PRE 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW PRE n m = m - n ==>
         !m. FUNPOW PRE (SUC n) m = m - SUC n
       FUNPOW PRE (SUC n) m
     = FUNPOW PRE n (PRE m)    by FUNPOW
     = (PRE m) - n             by induction hypothesis
     = m - PRE n               by arithmetic
*)
val FUNPOW_SUB1 = store_thm(
  "FUNPOW_SUB1",
  ``!m n. FUNPOW PRE n m = m - n``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW]);

(* Theorem: FUNPOW ($* b) n m = m * b ** n *)
(* Proof:
   By induction on n.
   Base: !m. !m. FUNPOW ($* b) 0 m = m * b ** 0
      LHS = FUNPOW ($* b) 0 m
          = m                  by FUNPOW_0
          = m * 1              by MULT_RIGHT_1
          = m * b ** 0 = RHS   by EXP_0
   Step: !m. FUNPOW ($* b) n m = m * b ** n ==>
         !m. FUNPOW ($* b) (SUC n) m = m * b ** SUC n
       FUNPOW ($* b) (SUC n) m
     = FUNPOW ($* b) n (b * m)    by FUNPOW
     = b * m * b ** n             by induction hypothesis
     = m * (b * b ** n)           by arithmetic
     = m * b ** SUC n             by EXP
*)
val FUNPOW_MUL = store_thm(
  "FUNPOW_MUL",
  ``!b m n. FUNPOW ($* b) n m = m * b ** n``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW, EXP]);

(* Theorem: 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n)) *)
(* Proof:
   By induction on n.
   Let f = combin$C $DIV b.
   Base: !m. FUNPOW f 0 m = m DIV b ** 0
      LHS = FUNPOW f 0 m
          = m                     by FUNPOW_0
          = m DIV 1               by DIV_1
          = m DIV (b ** 0) = RHS  by EXP_0
   Step: !m. FUNPOW f n m = m DIV b ** n ==>
         !m. FUNPOW f (SUC n) m = m DIV b ** SUC n
       FUNPOW f (SUC n) m
     = FUNPOW f n (f m)           by FUNPOW
     = FUNPOW f n (m DIV b)       by C_THM
     = (m DIV b) DIV (b ** n)     by induction hypothesis
     = m DIV (b * b ** n)         by DIV_DIV_DIV_MULT, 0 < b, 0 < b ** n
     = m DIV b ** SUC n           by EXP
*)
val FUNPOW_DIV = store_thm(
  "FUNPOW_DIV",
  ``!b m n. 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n))``,
  strip_tac >>
  qabbrev_tac `f = combin$C $DIV b` >>
  Induct_on `n` >-
  rw[EXP_0] >>
  rpt strip_tac >>
  `FUNPOW f (SUC n) m = FUNPOW f n (m DIV b)` by rw[FUNPOW, Abbr`f`] >>
  `_ = (m DIV b) DIV (b ** n)` by rw[] >>
  `_ = m DIV (b * b ** n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = m DIV b ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: FUNPOW SQ n m = m ** (2 ** n) *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW (\n. SQ n) 0 m = m ** 2 ** 0
        FUNPOW SQ 0 m
      = m               by FUNPOW_0
      = m ** 1          by EXP_1
      = m ** 2 ** 0     by EXP_0
   Step: !m. FUNPOW (\n. SQ n) n m = m ** 2 ** n ==>
         !m. FUNPOW (\n. SQ n) (SUC n) m = m ** 2 ** SUC n
        FUNPOW (\n. SQ n) (SUC n) m
      = SQ (FUNPOW (\n. SQ n) n m)    by FUNPOW_SUC
      = SQ (m ** 2 ** n)              by induction hypothesis
      = (m ** 2 ** n) ** 2            by EXP_2
      = m ** (2 * 2 ** n)             by EXP_EXP_MULT
      = m ** 2 ** SUC n               by EXP
*)
val FUNPOW_SQ = store_thm(
  "FUNPOW_SQ",
  ``!m n. FUNPOW SQ n m = m ** (2 ** n)``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC, GSYM EXP_EXP_MULT, EXP]);

(* Theorem: 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m) *)
(* Proof:
   Lef f = (\n. SQ n MOD m).
   By induction on n.
   Base: !k. 0 < m /\ 0 < 0 ==> FUNPOW f 0 k = k ** 2 ** 0 MOD m
      True since 0 < 0 = F.
   Step: !k. 0 < m /\ 0 < n ==> FUNPOW f n k = k ** 2 ** n MOD m ==>
         !k. 0 < m /\ 0 < SUC n ==> FUNPOW f (SUC n) k = k ** 2 ** SUC n MOD m
     If n = 1,
       FUNPOW f (SUC 0) k
     = FUNPOW f 1 k             by ONE
     = f k                      by FUNPOW_1
     = SQ k MOD m               by notation
     = (k ** 2) MOD m           by EXP_2
     = (k ** (2 ** 1)) MOD m    by EXP_1
     If n <> 0,
       FUNPOW f (SUC n) k
     = f (FUNPOW f n k)         by FUNPOW_SUC
     = f (k ** 2 ** n MOD m)    by induction hypothesis
     = (k ** 2 ** n MOD m) * (k ** 2 ** n MOD m) MOD m     by notation
     = (k ** 2 ** n * k ** 2 ** n) MOD m                   by MOD_TIMES2
     = (k ** (2 ** n + 2 ** n)) MOD m          by EXP_BASE_MULT
     = (k ** (2 * 2 ** n)) MOD m               by arithmetic
     = (k ** 2 ** SUC n) MOD m                 by EXP
*)
val FUNPOW_SQ_MOD = store_thm(
  "FUNPOW_SQ_MOD",
  ``!m n k. 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m)``,
  strip_tac >>
  qabbrev_tac `f = \n. SQ n MOD m` >>
  Induct >>
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[Abbr`f`] >>
  rw[FUNPOW_SUC, Abbr`f`] >>
  `(k ** 2 ** n) ** 2 = k ** (2 * 2 ** n)` by rw[GSYM EXP_EXP_MULT] >>
  `_ = k ** 2 ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MAX x m) 0 k = MAX k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MAX x m) n k = MAX k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MAX x m) (SUC n) k = MAX k m
      If n = 0,
           FUNPOW (\x. MAX x m) (SUC 0) k
         = FUNPOW (\x. MAX x m) 1 k          by ONE
         = (\x. MAX x m) k                   by FUNPOW_1
         = MAX k m                           by function application
      If n <> 0,
           FUNPOW (\x. MAX x m) (SUC n) k
         = f (FUNPOW (\x. MAX x m) n k)      by FUNPOW_SUC
         = (\x. MAX x m) (MAX k m)           by induction hypothesis
         = MAX (MAX k m) m                   by function application
         = MAX k m                           by MAX_IS_MAX, m <= MAX k m
*)
val FUNPOW_MAX = store_thm(
  "FUNPOW_MAX",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `m <= MAX k m` by rw[] >>
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MIN x m) 0 k = MIN k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MIN x m) n k = MIN k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MIN x m) (SUC n) k = MIN k m
      If n = 0,
           FUNPOW (\x. MIN x m) (SUC 0) k
         = FUNPOW (\x. MIN x m) 1 k          by ONE
         = (\x. MIN x m) k                   by FUNPOW_1
         = MIN k m                           by function application
      If n <> 0,
           FUNPOW (\x. MIN x m) (SUC n) k
         = f (FUNPOW (\x. MIN x m) n k)      by FUNPOW_SUC
         = (\x. MIN x m) (MIN k m)           by induction hypothesis
         = MIN (MIN k m) m                   by function application
         = MIN k m                           by MIN_IS_MIN, MIN k m <= m
*)
val FUNPOW_MIN = store_thm(
  "FUNPOW_MIN",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `MIN k m <= m` by rw[] >>
  rw[MIN_DEF]);

(* Theorem: FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y). (f x,g y)) 0 (x,y) = (FUNPOW f 0 x,FUNPOW g 0 y)
          FUNPOW (\(x,y). (f x,g y)) 0 (x,y)
        = (x,y)                           by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y)    by FUNPOW_0
   Step: FUNPOW (\(x,y). (f x,g y)) n (x,y) = (FUNPOW f n x,FUNPOW g n y) ==>
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y) = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y)
       = (\(x,y). (f x,g y)) (FUNPOW (\(x,y). (f x,g y)) n (x,y)) by FUNPOW_SUC
       = (\(x,y). (f x,g y)) (FUNPOW f n x,FUNPOW g n y)          by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y))                      by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)                  by FUNPOW_SUC
*)
val FUNPOW_PAIR = store_thm(
  "FUNPOW_PAIR",
  ``!f g n x y. FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);

(* Theorem: FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) = (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z) = (FUNPOW f 0 x,FUNPOW g 0 y,FUNPOW h 0 z)
          FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z)
        = (x,y)                                         by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y, FUNPOW h 0 z)    by FUNPOW_0
   Step: FUNPOW (\(x,y,z). (f x,g y,h z)) n (x,y,z) =
                (FUNPOW f n x,FUNPOW g n y,FUNPOW h n z) ==>
         FUNPOW (\(x,y,z). (f x,g y,h z)) (SUC n) (x,y,z) =
                (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y,FUNPOW h (SUC n) z)
       Let fun = (\(x,y,z). (f x,g y,h z)).
         FUNPOW fun (SUC n) (x,y, z)
       = fun (FUNPOW fun n (x,y,z))                                   by FUNPOW_SUC
       = fun (FUNPOW f n x,FUNPOW g n y, FUNPOW h n z)                by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y), h (FUNPOW h n z))        by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y, FUNPOW h (SUC n) z)  by FUNPOW_SUC
*)
val FUNPOW_TRIPLE = store_thm(
  "FUNPOW_TRIPLE",
  ``!f g h n x y z. FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) =
                  (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);


(* Theorem: f PERMUTES s ==> (LINV f s) PERMUTES s *)
(* Proof: by BIJ_LINV_BIJ *)
Theorem LINV_permutes:
  !f s. f PERMUTES s ==> (LINV f s) PERMUTES s
Proof
  rw[BIJ_LINV_BIJ]
QED

(* Theorem: f PERMUTES s ==> (FUNPOW f n) PERMUTES s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 PERMUTES s
      Note FUNPOW f 0 = I         by FUN_EQ_THM, FUNPOW_0
       and I PERMUTES s           by BIJ_I_SAME
      thus true.
   Step: f PERMUTES s /\ FUNPOW f n PERMUTES s ==>
         FUNPOW f (SUC n) PERMUTES s
      Note FUNPOW f (SUC n)
         = f o (FUNPOW f n)       by FUN_EQ_THM, FUNPOW_SUC
      Thus true                   by BIJ_COMPOSE
*)
Theorem FUNPOW_permutes:
  !f s n. f PERMUTES s ==> (FUNPOW f n) PERMUTES s
Proof
  rpt strip_tac >>
  Induct_on `n` >| [
    `FUNPOW f 0 = I` by rw[FUN_EQ_THM] >>
    simp[BIJ_I_SAME],
    `FUNPOW f (SUC n) = f o (FUNPOW f n)` by rw[FUN_EQ_THM, FUNPOW_SUC] >>
    metis_tac[BIJ_COMPOSE]
  ]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x IN s
         Since FUNPOW f 0 x = x      by FUNPOW_0
         This is trivially true.
   Step: FUNPOW f n x IN s ==> FUNPOW f (SUC n) x IN s
           FUNPOW f (SUC n) x
         = f (FUNPOW f n x)          by FUNPOW_SUC
         But FUNPOW f n x IN s       by induction hypothesis
          so f (FUNPOW f n x) IN s   by BIJ_ELEMENT, f PERMUTES s
*)
Theorem FUNPOW_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* Theorem: f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s *)
(* Proof: by LINV_permutes, FUNPOW_permutes *)
Theorem FUNPOW_LINV_permutes:
  !f s n. f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s
Proof
  simp[LINV_permutes, FUNPOW_permutes]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 x IN s
         Since FUNPOW (LINV f s) 0 x = x   by FUNPOW_0
         This is trivially true.
   Step: FUNPOW (LINV f s) n x IN s ==> FUNPOW (LINV f s) (SUC n) x IN s
           FUNPOW (LINV f s) (SUC n) x
         = (LINV f s) (FUNPOW (LINV f s) n x)   by FUNPOW_SUC
         But FUNPOW (LINV f s) n x IN s         by induction hypothesis
         and (LINV f s) PERMUTES s              by LINV_permutes
          so (LINV f s) (FUNPOW (LINV f s) n x) IN s
                                                by BIJ_ELEMENT
*)
Theorem FUNPOW_LINV_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `(LINV f s) PERMUTES s` by rw[LINV_permutes] >>
  prove_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 (FUNPOW (LINV f s) 0 x) = x
           FUNPOW f 0 (FUNPOW (LINV f s) 0 x)
         = FUNPOW f 0 x              by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW f n (FUNPOW (LINV f s) n x) = x ==>
         FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x) = x
         Note (FUNPOW (LINV f s) n x) IN s        by FUNPOW_LINV_closure
           FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
         = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))  by FUNPOW_SUC
         = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))    by FUNPOW
         = FUNPOW f n (FUNPOW (LINV f s) n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_LINV_EQ:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
    = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW f n (FUNPOW (LINV f s) n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 (FUNPOW f 0 x) = x
           FUNPOW (LINV f s) 0 (FUNPOW f 0 x)
         = FUNPOW (LINV f s) 0 x     by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW (LINV f s) n (FUNPOW f n x) = x ==>
         FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x) = x
         Note (FUNPOW f n x) IN s                 by FUNPOW_closure
           FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
         = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))           by FUNPOW_SUC
         = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))    by FUNPOW
         = FUNPOW (LINV f s) n (FUNPOW f n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_EQ_LINV:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
    = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW (LINV f s) n (FUNPOW f n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x) *)
(* Proof:
     FUNPOW f n (FUNPOW (LINV f s) m x)
   = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)   by SUB_ADD, m <= n
   = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                             by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_SUB_LINV1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x)
Proof
  rpt strip_tac >>
  `FUNPOW f n (FUNPOW (LINV f s) m x)
  = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)` by simp[] >>
  `_ = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_LINV_EQ] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x) *)
(* Proof:
   Note FUNPOW f (n - m) x IN s                      by FUNPOW_closure
     FUNPOW (LINV f s) m (FUNPOW f n x)
   = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)  by ADD_COMM
   = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                              by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_SUB_LINV2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) m (FUNPOW f n x)
  = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)` by simp[] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_EQ_LINV, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x) *)
(* Proof:
     FUNPOW (LINV f s) n (FUNPOW f m x)
   = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_LINV_SUB1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) n (FUNPOW f m x)
  = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)` by simp[] >>
  `_ = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_EQ_LINV] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x) *)
(* Proof:
   Note FUNPOW (LINV f s) (n - m) x IN s             by FUNPOW_LINV_closure
     FUNPOW f m (FUNPOW (LINV f s) n x)
   = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)  by ADD_COMM
   = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_SUB2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x)
Proof
  rpt strip_tac >>
  `FUNPOW f m (FUNPOW (LINV f s) n x)
  = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)` by simp[] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_LINV_EQ, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ y IN s ==>
            (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x) *)
(* Proof:
   If part: x = FUNPOW f n y ==> y = FUNPOW (LINV f s) n x)
        FUNPOW (LINV f s) n x)
      = FUNPOW (LINV f s) n (FUNPOW f n y))   by x = FUNPOW f n y
      = y                                     by FUNPOW_EQ_LINV
   Only-if part: y = FUNPOW (LINV f s) n x) ==> x = FUNPOW f n y
        FUNPOW f n y
      = FUNPOW f n (FUNPOW (LINV f s) n x))   by y = FUNPOW (LINV f s) n x)
      = x                                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_INV:
  !f s x y n. f PERMUTES s /\ x IN s /\ y IN s ==>
              (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x)
Proof
  rw[EQ_IMP_THM] >-
  rw[FUNPOW_EQ_LINV] >>
  rw[FUNPOW_LINV_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function Documentation                              *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   natural n    = IMAGE SUC (count n)
   upto n       = count (SUC n)
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   Residues:
   residue_def       |- !n. residue n = {i | 0 < i /\ i < n}
   residue_element   |- !n j. j IN residue n ==> 0 < j /\ j < n
   residue_0         |- residue 0 = {}
   residue_1         |- residue 1 = {}
   residue_nonempty  |- !n. 1 < n ==> residue n <> {}
   residue_no_zero   |- !n. 0 NOTIN residue n
   residue_no_self   |- !n. n NOTIN residue n
!  residue_thm       |- !n. residue n = count n DIFF {0}
   residue_insert    |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_delete    |- !n. 0 < n ==> (residue n DELETE n = residue n)
   residue_suc       |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n)
   residue_count     |- !n. 0 < n ==> (count n = 0 INSERT residue n)
   residue_finite    |- !n. FINITE (residue n)
   residue_card      |- !n. 0 < n ==> (CARD (residue n) = n - 1)
   residue_prime_neq |- !p a n. prime p /\ a IN residue p /\ n <= p ==>
                        !x. x IN residue n ==> (a * n) MOD p <> (a * x) MOD p
   prod_set_residue  |- !n. PROD_SET (residue n) = FACT (n - 1)

   Naturals:
   natural_element  |- !n j. j IN natural n <=> 0 < j /\ j <= n
   natural_property |- !n. natural n = {j | 0 < j /\ j <= n}
   natural_finite   |- !n. FINITE (natural n)
   natural_card     |- !n. CARD (natural n) = n
   natural_not_0    |- !n. 0 NOTIN natural n
   natural_0        |- natural 0 = {}
   natural_1        |- natural 1 = {1}
   natural_has_1    |- !n. 0 < n ==> 1 IN natural n
   natural_has_last |- !n. 0 < n ==> n IN natural n
   natural_suc      |- !n. natural (SUC n) = SUC n INSERT natural n
   natural_thm      |- !n. natural n = set (GENLIST SUC n)
   natural_divisor_natural   |- !n a b. 0 < n /\ a IN natural n /\ b divides a ==> b IN natural n
   natural_cofactor_natural  |- !n a b. 0 < n /\ 0 < a /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural n
   natural_cofactor_natural_reduced
                             |- !n a b. 0 < n /\ a divides n /\ b IN natural n /\ a divides b ==>
                                        b DIV a IN natural (n DIV a)

   Uptos:
   upto_finite      |- !n. FINITE (upto n)
   upto_card        |- !n. CARD (upto n) = SUC n
   upto_has_last    |- !n. n IN upto n
   upto_delete      |- !n. upto n DELETE n = count n
   upto_split_first |- !n. upto n = {0} UNION natural n
   upto_split_last  |- !n. upto n = count n UNION {n}
   upto_by_count    |- !n. upto n = n INSERT count n
   upto_by_natural  |- !n. upto n = 0 INSERT natural n
   natural_by_upto  |- !n. natural n = upto n DELETE 0

   Euler Set and Totient Function:
   Euler_def            |- !n. Euler n = {i | 0 < i /\ i < n /\ coprime n i}
   totient_def          |- !n. totient n = CARD (Euler n)
   Euler_element        |- !n x. x IN Euler n <=> 0 < x /\ x < n /\ coprime n x
!  Euler_thm            |- !n. Euler n = residue n INTER {j | coprime j n}
   Euler_finite         |- !n. FINITE (Euler n)
   Euler_0              |- Euler 0 = {}
   Euler_1              |- Euler 1 = {}
   Euler_has_1          |- !n. 1 < n ==> 1 IN Euler n
   Euler_nonempty       |- !n. 1 < n ==> Euler n <> {}
   Euler_empty          |- !n. (Euler n = {}) <=> (n = 0 \/ n = 1)
   Euler_card_upper_le  |- !n. totient n <= n
   Euler_card_upper_lt  |- !n. 1 < n ==> totient n < n
   Euler_card_bounds    |- !n. totient n <= n /\ (1 < n ==> 0 < totient n /\ totient n < n)
   Euler_prime          |- !p. prime p ==> (Euler p = residue p)
   Euler_card_prime     |- !p. prime p ==> (totient p = p - 1)

   Summation of Geometric Sequence:
   sigma_geometric_natural_eqn   |- !p. 0 < p ==>
                                    !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)
   sigma_geometric_natural       |- !p. 1 < p ==>
                                    !n. SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) DIV (p - 1)

   Chinese Remainder Theorem:
   mod_mod_prod_eq     |- !m n a b. 0 < m /\ 0 < n /\ a MOD (m * n) = b MOD (m * n) ==>
                                    a MOD m = b MOD m /\ a MOD n = b MOD n
   coprime_mod_mod_prod_eq
                       |- !m n a b. 0 < m /\ 0 < n /\ coprime m n /\
                                    a MOD m = b MOD m /\ a MOD n = b MOD n ==>
                                    a MOD (m * n) = b MOD (m * n)
   coprime_mod_mod_prod_eq_iff
                       |- !m n. 0 < m /\ 0 < n /\ coprime m n ==>
                          !a b. a MOD (m * n) = b MOD (m * n) <=>
                                a MOD m = b MOD m /\ a MOD n = b MOD n
   coprime_mod_mod_solve
                       |- !m n a b. 0 < m /\ 0 < n /\ coprime m n ==>
                               ?!x. x < m * n /\ x MOD m = a MOD m /\ x MOD n = b MOD n

   Useful Theorems:
   PROD_SET_IMAGE_EXP_NONZERO    |- !n m. PROD_SET (IMAGE (\j. n ** j) (count m)) =
                                          PROD_SET (IMAGE (\j. n ** j) (residue m))
*)

(* ------------------------------------------------------------------------- *)
(* Residues -- close-relative of COUNT                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the set of residues = nonzero remainders *)
val residue_def = zDefine `residue n = { i | (0 < i) /\ (i < n) }`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN residue n ==> 0 < j /\ j < n *)
(* Proof: by residue_def. *)
val residue_element = store_thm(
  "residue_element",
  ``!n j. j IN residue n ==> 0 < j /\ j < n``,
  rw[residue_def]);

(* Theorem: residue 0 = EMPTY *)
(* Proof: by residue_def *)
Theorem residue_0:
  residue 0 = {}
Proof
  simp[residue_def]
QED

(* Theorem: residue 1 = EMPTY *)
(* Proof: by residue_def. *)
Theorem residue_1:
  residue 1 = {}
Proof
  simp[residue_def]
QED

(* Theorem: 1 < n ==> residue n <> {} *)
(* Proof:
   By residue_def, this is to show: 1 < n ==> ?x. x <> 0 /\ x < n
   Take x = 1, this is true.
*)
val residue_nonempty = store_thm(
  "residue_nonempty",
  ``!n. 1 < n ==> residue n <> {}``,
  rw[residue_def, EXTENSION] >>
  metis_tac[DECIDE``1 <> 0``]);

(* Theorem: 0 NOTIN residue n *)
(* Proof: by residue_def *)
Theorem residue_no_zero:
  !n. 0 NOTIN residue n
Proof
  simp[residue_def]
QED

(* Theorem: n NOTIN residue n *)
(* Proof: by residue_def *)
Theorem residue_no_self:
  !n. n NOTIN residue n
Proof
  simp[residue_def]
QED

(* Theorem: residue n = (count n) DIFF {0} *)
(* Proof:
     residue n
   = {i | 0 < i /\ i < n}   by residue_def
   = {i | i < n /\ i <> 0}  by NOT_ZERO_LT_ZERO
   = {i | i < n} DIFF {0}   by IN_DIFF
   = (count n) DIFF {0}     by count_def
*)
val residue_thm = store_thm(
  "residue_thm[compute]",
  ``!n. residue n = (count n) DIFF {0}``,
  rw[residue_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``residue 10``;
val it = |- residue 10 = {9; 8; 7; 6; 5; 4; 3; 2; 1}: thm
*)

(* Theorem: For n > 0, residue (SUC n) = n INSERT residue n *)
(* Proof:
     residue (SUC n)
   = {1, 2, ..., n}
   = n INSERT {1, 2, ..., (n-1) }
   = n INSERT residue n
*)
val residue_insert = store_thm(
  "residue_insert",
  ``!n. 0 < n ==> (residue (SUC n) = n INSERT residue n)``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: (residue n) DELETE n = residue n *)
(* Proof: Because n is not in (residue n). *)
val residue_delete = store_thm(
  "residue_delete",
  ``!n. 0 < n ==> ((residue n) DELETE n = residue n)``,
  rpt strip_tac >>
  `n NOTIN (residue n)` by rw[residue_def] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem alias: rename *)
val residue_suc = save_thm("residue_suc", residue_insert);
(* val residue_suc = |- !n. 0 < n ==> (residue (SUC n) = n INSERT residue n): thm *)

(* Theorem: count n = 0 INSERT (residue n) *)
(* Proof: by definition. *)
val residue_count = store_thm(
  "residue_count",
  ``!n. 0 < n ==> (count n = 0 INSERT (residue n))``,
  srw_tac[ARITH_ss][residue_def, EXTENSION]);

(* Theorem: FINITE (residue n) *)
(* Proof: by FINITE_COUNT.
   If n = 0, residue 0 = {}, hence FINITE.
   If n > 0, count n = 0 INSERT (residue n)  by residue_count
   hence true by FINITE_COUNT and FINITE_INSERT.
*)
val residue_finite = store_thm(
  "residue_finite",
  ``!n. FINITE (residue n)``,
  Cases >-
  rw[residue_def] >>
  metis_tac[residue_count, FINITE_INSERT, count_def, FINITE_COUNT, DECIDE ``0 < SUC n``]);

(* Theorem: For n > 0, CARD (residue n) = n-1 *)
(* Proof:
   Since 0 INSERT (residue n) = count n by residue_count
   the result follows by CARD_COUNT.
*)
val residue_card = store_thm(
  "residue_card",
  ``!n. 0 < n ==> (CARD (residue n) = n-1)``,
  rpt strip_tac >>
  `0 NOTIN (residue n)` by rw[residue_def] >>
  `0 INSERT (residue n) = count n` by rw[residue_count] >>
  `SUC (CARD (residue n)) = n` by metis_tac[residue_finite, CARD_INSERT, CARD_COUNT] >>
  decide_tac);

(* Theorem: For prime m, a in residue m, n <= m, a*n MOD m <> a*x MOD m  for all x in residue n *)
(* Proof:
   Assume the contrary, that a*n MOD m = a*x MOD m
   Since a in residue m and m is prime, MOD_MULT_LCANCEL gives: n MOD m = x MOD m
   If n = m, n MOD m = 0, but x MOD m <> 0, hence contradiction.
   If n < m, then since x < n <= m, n = x, contradicting x < n.
*)
val residue_prime_neq = store_thm(
  "residue_prime_neq",
  ``!p a n. prime p /\ a IN (residue p) /\ n <= p ==> !x. x IN (residue n) ==> (a*n) MOD p <> (a*x) MOD p``,
  rw[residue_def] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a MOD p <> 0) /\ (x MOD p <> 0)` by rw_tac arith_ss[] >>
  `n MOD p = x MOD p` by metis_tac[MOD_MULT_LCANCEL] >>
  Cases_on `n = p` >-
  metis_tac [DIVMOD_ID] >>
  `n < p` by decide_tac >>
  `(n MOD p = n) /\ (x MOD p = x)` by rw_tac arith_ss[] >>
  decide_tac);

(* Idea: the product of residues is a factorial. *)

(* Theorem: PROD_SET (residue n) = FACT (n - 1) *)
(* Proof:
   By induction on n.
   Base: PROD_SET (residue 0) = FACT (0 - 1)
        PROD_SET (residue 0)
      = PROD_SET {}            by residue_0
      = 1                      by PROD_SET_EMPTY
      = FACT 0                 by FACT_0
      = FACT (0 - 1)           by arithmetic
   Step: PROD_SET (residue n) = FACT (n - 1) ==>
         PROD_SET (residue (SUC n)) = FACT (SUC n - 1)
      If n = 0,
        PROD_SET (residue (SUC 0))
      = PROD_SET (residue 1)   by ONE
      = PROD_SET {}            by residue_1
      = 1                      by PROD_SET_EMPTY
      = FACT 0                 by FACT_0

      If n <> 0, then 0 < n.
      Note FINITE (residue n)                  by residue_finite
        PROD_SET (residue (SUC n))
      = PROD_SET (n INSERT residue n)          by residue_insert
      = n * PROD_SET ((residue n) DELETE n)    by PROD_SET_THM
      = n * PROD_SET (residue n)               by residue_delete
      = n * FACT (n - 1)                       by induction hypothesis
      = FACT (SUC (n - 1))                     by FACT
      = FACT (SUC n - 1)                       by arithmetic
*)
Theorem prod_set_residue:
  !n. PROD_SET (residue n) = FACT (n - 1)
Proof
  Induct >-
  simp[residue_0, PROD_SET_EMPTY, FACT_0] >>
  Cases_on `n = 0` >-
  simp[residue_1, PROD_SET_EMPTY, FACT_0] >>
  `FINITE (residue n)` by rw[residue_finite] >>
  `n = SUC (n - 1)` by decide_tac >>
  `SUC (n - 1) = SUC n - 1` by decide_tac >>
  `PROD_SET (residue (SUC n)) = PROD_SET (n INSERT residue n)` by rw[residue_insert] >>
  `_ = n * PROD_SET ((residue n) DELETE n)` by rw[PROD_SET_THM] >>
  `_ = n * PROD_SET (residue n)` by rw[residue_delete] >>
  `_ = n * FACT (n - 1)` by rw[] >>
  metis_tac[FACT]
QED

(* Theorem: natural n = set (GENLIST SUC n) *)
(* Proof:
   By induction on n.
   Base: natural 0 = set (GENLIST SUC 0)
      LHS = natural 0 = {}         by natural_0
      RHS = set (GENLIST SUC 0)
          = set []                 by GENLIST_0
          = {}                     by LIST_TO_SET
   Step: natural n = set (GENLIST SUC n) ==>
         natural (SUC n) = set (GENLIST SUC (SUC n))
         natural (SUC n)
       = SUC n INSERT natural n                 by natural_suc
       = SUC n INSERT (set (GENLIST SUC n))     by induction hypothesis
       = set (SNOC (SUC n) (GENLIST SUC n))     by LIST_TO_SET_SNOC
       = set (GENLIST SUC (SUC n))              by GENLIST
*)
val natural_thm = store_thm(
  "natural_thm",
  ``!n. natural n = set (GENLIST SUC n)``,
  Induct >-
  rw[] >>
  rw[natural_suc, LIST_TO_SET_SNOC, GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Uptos -- counting from 0 and inclusive.                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload on another count-related set *)
val _ = overload_on("upto", ``\n. count (SUC n)``);

(* Theorem: FINITE (upto n) *)
(* Proof: by FINITE_COUNT *)
val upto_finite = store_thm(
  "upto_finite",
  ``!n. FINITE (upto n)``,
  rw[]);

(* Theorem: CARD (upto n) = SUC n *)
(* Proof: by CARD_COUNT *)
val upto_card = store_thm(
  "upto_card",
  ``!n. CARD (upto n) = SUC n``,
  rw[]);

(* Theorem: n IN (upto n) *)
(* Proof: byLESS_SUC_REFL *)
val upto_has_last = store_thm(
  "upto_has_last",
  ``!n. n IN (upto n)``,
  rw[]);

(* Theorem: (upto n) DELETE n = count n *)
(* Proof:
     (upto n) DELETE n
   = (count (SUC n)) DELETE n      by notation
   = (n INSERT count n) DELETE n   by COUNT_SUC
   = count n DELETE n              by DELETE_INSERT
   = count n                       by DELETE_NON_ELEMENT, COUNT_NOT_SELF
*)
Theorem upto_delete:
  !n. (upto n) DELETE n = count n
Proof
  metis_tac[COUNT_SUC, COUNT_NOT_SELF, DELETE_INSERT, DELETE_NON_ELEMENT]
QED

(* Theorem: upto n = {0} UNION (natural n) *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> (x = 0) \/ ?x'. (x = SUC x') /\ x' < n
       If x = 0, trivially true.
       If x <> 0, x = SUC m.
          Take x' = m,
          then SUC m = x < SUC n ==> m < n   by LESS_MONO_EQ
   (2) (x = 0) \/ ?x'. (x = SUC x') /\ x' < n ==> x < SUC n
       If x = 0, 0 < SUC n                   by SUC_POS
       If ?x'. (x = SUC x') /\ x' < n,
          x' < n ==> SUC x' = x < SUC n      by LESS_MONO_EQ
*)
val upto_split_first = store_thm(
  "upto_split_first",
  ``!n. upto n = {0} UNION (natural n)``,
  rw[EXTENSION, EQ_IMP_THM] >>
  Cases_on `x` >-
  rw[] >>
  metis_tac[LESS_MONO_EQ]);

(* Theorem: upto n = (count n) UNION {n} *)
(* Proof:
   By UNION_DEF, EXTENSION, this is to show:
   (1) x < SUC n ==> x < n \/ (x = n)
       True by LESS_THM.
   (2) x < n \/ (x = n) ==> x < SUC n
       True by LESS_THM.
*)
val upto_split_last = store_thm(
  "upto_split_last",
  ``!n. upto n = (count n) UNION {n}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: upto n = n INSERT (count n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | (x = n) \/ (x < n)}  by prim_recTheory.LESS_THM
   = x INSERT {x| x < n}       by INSERT_DEF
   = x INSERT (count n)        by count_def
*)
val upto_by_count = store_thm(
  "upto_by_count",
  ``!n. upto n = n INSERT (count n)``,
  rw[EXTENSION]);

(* Theorem: upto n = 0 INSERT (natural n) *)
(* Proof:
     upto n
   = count (SUC n)             by notation
   = {x | x < SUC n}           by count_def
   = {x | ((x = 0) \/ (?m. x = SUC m)) /\ x < SUC n)}            by num_CASES
   = {x | (x = 0 /\ x < SUC n) \/ (?m. x = SUC m /\ x < SUC n)}  by SUC_POS
   = 0 INSERT {SUC m | SUC m < SUC n}   by INSERT_DEF
   = 0 INSERT {SUC m | m < n}           by LESS_MONO_EQ
   = 0 INSERT (IMAGE SUC (count n))     by IMAGE_DEF
   = 0 INSERT (natural n)               by notation
*)
val upto_by_natural = store_thm(
  "upto_by_natural",
  ``!n. upto n = 0 INSERT (natural n)``,
  rw[EXTENSION] >>
  metis_tac[num_CASES, LESS_MONO_EQ, SUC_POS]);

(* Theorem: natural n = count (SUC n) DELETE 0 *)
(* Proof:
     count (SUC n) DELETE 0
   = {x | x < SUC n} DELETE 0    by count_def
   = {x | x < SUC n} DIFF {0}    by DELETE_DEF
   = {x | x < SUC n /\ x <> 0}   by DIFF_DEF
   = {SUC m | SUC m < SUC n}     by num_CASES
   = {SUC m | m < n}             by LESS_MONO_EQ
   = IMAGE SUC (count n)         by IMAGE_DEF
   = natural n                   by notation
*)
val natural_by_upto = store_thm(
  "natural_by_upto",
  ``!n. natural n = count (SUC n) DELETE 0``,
  (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[num_CASES, LESS_MONO_EQ]));

(* ------------------------------------------------------------------------- *)
(* Euler Set and Totient Function                                            *)
(* ------------------------------------------------------------------------- *)

(* Euler's totient function *)
val Euler_def = zDefine`
  Euler n = { i | 0 < i /\ i < n /\ (gcd n i = 1) }
`;
(* that is, Euler n = { i | i in (residue n) /\ (gcd n i = 1) }; *)
(* use zDefine as this is not computationally effective. *)

val totient_def = Define`
  totient n = CARD (Euler n)
`;

(* Theorem: x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x *)
(* Proof: by Euler_def. *)
val Euler_element = store_thm(
  "Euler_element",
  ``!n x. x IN (Euler n) <=> 0 < x /\ x < n /\ coprime n x``,
  rw[Euler_def]);

(* Theorem: Euler n = (residue n) INTER {j | coprime j n} *)
(* Proof: by Euler_def, residue_def, EXTENSION, IN_INTER *)
val Euler_thm = store_thm(
  "Euler_thm[compute]",
  ``!n. Euler n = (residue n) INTER {j | coprime j n}``,
  rw[Euler_def, residue_def, GCD_SYM, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``Euler 10``;
val it = |- Euler 10 = {9; 7; 3; 1}: thm
> EVAL ``totient 10``;
val it = |- totient 10 = 4: thm
*)

(* Theorem: FINITE (Euler n) *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     ==> FINITE (Euler n)          by SUBSET_FINITE
*)
val Euler_finite = store_thm(
  "Euler_finite",
  ``!n. FINITE (Euler n)``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[FINITE_COUNT, SUBSET_FINITE]);

(* Theorem: Euler 0 = {} *)
(* Proof: by Euler_def *)
val Euler_0 = store_thm(
  "Euler_0",
  ``Euler 0 = {}``,
  rw[Euler_def]);

(* Theorem: Euler 1 = {} *)
(* Proof: by Euler_def *)
val Euler_1 = store_thm(
  "Euler_1",
  ``Euler 1 = {}``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> 1 IN (Euler n) *)
(* Proof: by Euler_def *)
val Euler_has_1 = store_thm(
  "Euler_has_1",
  ``!n. 1 < n ==> 1 IN (Euler n)``,
  rw[Euler_def]);

(* Theorem: 1 < n ==> (Euler n) <> {} *)
(* Proof: by Euler_has_1, MEMBER_NOT_EMPTY *)
val Euler_nonempty = store_thm(
  "Euler_nonempty",
  ``!n. 1 < n ==> (Euler n) <> {}``,
  metis_tac[Euler_has_1, MEMBER_NOT_EMPTY]);

(* Theorem: (Euler n = {}) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: Euler n = {} ==> n = 0 \/ n = 1
      By contradiction, suppose ~(n = 0 \/ n = 1).
      Then 1 < n, but Euler n <> {}   by Euler_nonempty
      This contradicts Euler n = {}.
   Only-if part: n = 0 \/ n = 1 ==> Euler n = {}
      Note Euler 0 = {}               by Euler_0
       and Euler 1 = {}               by Euler_1
*)
val Euler_empty = store_thm(
  "Euler_empty",
  ``!n. (Euler n = {}) <=> ((n = 0) \/ (n = 1))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    metis_tac[Euler_nonempty],
    rw[Euler_0],
    rw[Euler_1]
  ]);

(* Theorem: totient n <= n *)
(* Proof:
   Since (Euler n) SUBSET count n  by Euler_def, SUBSET_DEF
     and FINITE (count n)          by FINITE_COUNT
     and (CARD (count n) = n       by CARD_COUNT
   Hence CARD (Euler n) <= n       by CARD_SUBSET
      or totient n <= n            by totient_def
*)
val Euler_card_upper_le = store_thm(
  "Euler_card_upper_le",
  ``!n. totient n <= n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  metis_tac[totient_def, CARD_SUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: 1 < n ==> totient n < n *)
(* Proof:
   First, (Euler n) SUBSET count n     by Euler_def, SUBSET_DEF
     Now, ~(coprime 0 n)               by coprime_0L, n <> 1
      so  0 NOTIN (Euler n)            by Euler_def
     but  0 IN (count n)               by IN_COUNT, 0 < n
    Thus  (Euler n) <> (count n)       by EXTENSION
     and  (Euler n) PSUBSET (count n)  by PSUBSET_DEF
   Since  FINITE (count n)             by FINITE_COUNT
     and  (CARD (count n) = n          by CARD_COUNT
   Hence  CARD (Euler n) < n           by CARD_PSUBSET
      or  totient n < n                by totient_def
*)
val Euler_card_upper_lt = store_thm(
  "Euler_card_upper_lt",
  ``!n. 1 < n ==> totient n < n``,
  rpt strip_tac >>
  `(Euler n) SUBSET count n` by rw[Euler_def, SUBSET_DEF] >>
  `0 < n /\ n <> 1` by decide_tac >>
  `~(coprime 0 n)` by metis_tac[coprime_0L] >>
  `0 NOTIN (Euler n)` by rw[Euler_def] >>
  `0 IN (count n)` by rw[] >>
  `(Euler n) <> (count n)` by metis_tac[EXTENSION] >>
  `(Euler n) PSUBSET (count n)` by rw[PSUBSET_DEF] >>
  metis_tac[totient_def, CARD_PSUBSET, FINITE_COUNT, CARD_COUNT]);

(* Theorem: (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n) *)
(* Proof:
   This is to show:
   (1) totient n <= n,
       True by Euler_card_upper_le.
   (2) 1 < n ==> 0 < totient n
       Since (Euler n) <> {}      by Euler_nonempty
        Also FINITE (Euler n)     by Euler_finite
       Hence CARD (Euler n) <> 0  by CARD_EQ_0
          or 0 < totient n        by totient_def
   (3) 1 < n ==> totient n < n
       True by Euler_card_upper_lt.
*)
val Euler_card_bounds = store_thm(
  "Euler_card_bounds",
  ``!n. (totient n <= n) /\ (1 < n ==> 0 < totient n /\ totient n < n)``,
  rw[] >-
  rw[Euler_card_upper_le] >-
 (`(Euler n) <> {}` by rw[Euler_nonempty] >>
  `FINITE (Euler n)` by rw[Euler_finite] >>
  `totient n <> 0` by metis_tac[totient_def, CARD_EQ_0] >>
  decide_tac) >>
  rw[Euler_card_upper_lt]);

(* Theorem: For prime p, (Euler p = residue p) *)
(* Proof:
   By Euler_def, residue_def, this is to show:
   For prime p, gcd p x = 1   for 0 < x < p.
   Since x < p, x does not divide p, result follows by PRIME_GCD.
   or, this is true by prime_coprime_all_lt
*)
val Euler_prime = store_thm(
  "Euler_prime",
  ``!p. prime p ==> (Euler p = residue p)``,
  rw[Euler_def, residue_def, EXTENSION, EQ_IMP_THM] >>
  rw[prime_coprime_all_lt]);

(* Theorem: For prime p, totient p = p - 1 *)
(* Proof:
      totient p
    = CARD (Euler p)    by totient_def
    = CARD (residue p)  by Euler_prime
    = p - 1             by residue_card, and prime p > 0.
*)
val Euler_card_prime = store_thm(
  "Euler_card_prime",
  ``!p. prime p ==> (totient p = p - 1)``,
  rw[totient_def, Euler_prime, residue_card, PRIME_POS]);

(* ------------------------------------------------------------------------- *)
(* Summation of Geometric Sequence                                           *)
(* ------------------------------------------------------------------------- *)

(* Geometric Series:
   Let s = p + p ** 2 + p ** 3
   p * s = p ** 2 + p ** 3 + p ** 4
   p * s - s = p ** 4 - p
   (p - 1) * s = p * (p ** 3 - 1)
*)

(* Theorem: 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) *)
(* Proof:
   By induction on n.
   Base: (p - 1) * SIGMA (\j. p ** j) (natural 0) = p * (p ** 0 - 1)
      LHS = (p - 1) * SIGMA (\j. p ** j) (natural 0)
          = (p - 1) * SIGMA (\j. p ** j) {}          by natural_0
          = (p - 1) * 0                              by SUM_IMAGE_EMPTY
          = 0                                        by MULT_0
      RHS = p * (p ** 0 - 1)
          = p * (1 - 1)                              by EXP
          = p * 0                                    by SUB_EQUAL_0
          = 0 = LHS                                  by MULT_0
   Step: (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1) ==>
         (p - 1) * SIGMA (\j. p ** j) (natural (SUC n)) = p * (p ** SUC n - 1)
      Note FINITE (natural n)                        by natural_finite
       and (SUC n) NOTIN (natural n)                 by natural_element
      Also p <= p ** (SUC n)                         by X_LE_X_EXP, SUC_POS
       and 1 <= p                                    by 0 < p
      thus p ** (SUC n) <> 0                         by EXP_POS, 0 < p
        so p ** (SUC n) <= p * p ** (SUC n)          by LE_MULT_LCANCEL, p ** (SUC n) <> 0
        (p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
      = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))                   by natural_suc
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))  by SUM_IMAGE_THM
      = (p - 1) * ((p ** SUC n) + SIGMA (\j. p ** j) (natural n))                   by DELETE_NON_ELEMENT
      = (p - 1) * (p ** SUC n) + (p - 1) * SIGMA (\j. p ** j) (natural n)           by LEFT_ADD_DISTRIB
      = (p - 1) * (p ** SUC n) + p * (p ** n - 1)        by induction hypothesis
      = (p - 1) * (p ** SUC n) + (p * p ** n - p)        by LEFT_SUB_DISTRIB
      = (p - 1) * (p ** SUC n) + (p ** (SUC n) - p)      by EXP
      = (p * p ** SUC n - p ** SUC n) + (p ** SUC n - p) by RIGHT_SUB_DISTRIB
      = (p * p ** SUC n - p ** SUC n + p ** SUC n - p    by LESS_EQ_ADD_SUB, p <= p ** (SUC n)
      = p ** p ** SUC n - p                              by SUB_ADD, p ** (SUC n) <= p * p ** (SUC n)
      = p * (p ** SUC n - 1)                             by LEFT_SUB_DISTRIB
 *)
val sigma_geometric_natural_eqn = store_thm(
  "sigma_geometric_natural_eqn",
  ``!p. 0 < p ==> !n. (p - 1) * SIGMA (\j. p ** j) (natural n) = p * (p ** n - 1)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[natural_0, SUM_IMAGE_EMPTY, EXP, MULT_0] >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(SUC n) NOTIN (natural n)` by rw[natural_element] >>
  qabbrev_tac `q = p ** SUC n` >>
  `p <= q` by rw[X_LE_X_EXP, Abbr`q`] >>
  `1 <= p` by decide_tac >>
  `q <> 0` by rw[EXP_POS, Abbr`q`] >>
  `q <= p * q` by rw[LE_MULT_LCANCEL] >>
  `(p - 1) * SIGMA (\j. p ** j) (natural (SUC n))
  = (p - 1) * SIGMA (\j. p ** j) ((SUC n) INSERT (natural n))` by rw[natural_suc] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) ((natural n) DELETE (SUC n)))` by rw[SUM_IMAGE_THM, Abbr`q`] >>
  `_ = (p - 1) * (q + SIGMA (\j. p ** j) (natural n))` by metis_tac[DELETE_NON_ELEMENT] >>
  `_ = (p - 1) * q + (p - 1) * SIGMA (\j. p ** j) (natural n)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (p - 1) * q + p * (p ** n - 1)` by rw[] >>
  `_ = (p - 1) * q + (p * p ** n - p)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = (p - 1) * q + (q - p)` by rw[EXP, Abbr`q`] >>
  `_ = (p * q - q) + (q - p)` by rw[RIGHT_SUB_DISTRIB] >>
  `_ = (p * q - q + q) - p` by rw[LESS_EQ_ADD_SUB] >>
  `_ = p * q - p` by rw[SUB_ADD] >>
  `_ = p * (q - 1)` by rw[LEFT_SUB_DISTRIB] >>
  rw[]);

(* Theorem: 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1) *)
(* Proof:
   Since 1 < p,
     ==> 0 < p - 1, and 0 < p                          by arithmetic
   Let t = SIGMA (\j. p ** j) (natural n)
    With 0 < p,
         (p - 1) * t = p * (p ** n - 1)                by sigma_geometric_natural_eqn, 0 < p
   Hence           t = (p * (p ** n - 1)) DIV (p - 1)  by DIV_SOLVE, 0 < (p - 1)
*)
val sigma_geometric_natural = store_thm(
  "sigma_geometric_natural",
  ``!p. 1 < p ==> !n. SIGMA (\j. p ** j) (natural n) = (p * (p ** n - 1)) DIV (p - 1)``,
  rpt strip_tac >>
  `0 < p - 1 /\ 0 < p` by decide_tac >>
  rw[sigma_geometric_natural_eqn, DIV_SOLVE]);

(* ------------------------------------------------------------------------- *)
(* Chinese Remainder Theorem.                                                *)
(* ------------------------------------------------------------------------- *)

(* Idea: when a MOD (m * n) = b MOD (m * n), break up modulus m * n. *)

(* Theorem: 0 < m /\ 0 < n /\ a MOD (m * n) = b MOD (m * n) ==>
            a MOD m = b MOD m /\ a MOD n = b MOD n *)
(* Proof:
   Either b <= a, or a < b, which implies a <= b.
   The statement is symmetrical in a and b,
   so proceed by lemma with b <= a, without loss of generality.
   Note 0 < m * n                  by MULT_POS
     so ?c. a = b + c * (m * n)    by MOD_MOD_EQN, 0 < m * n
   Thus a = b + (c * m) * n        by arithmetic
    and a = b + (c * n) * m        by arithmetic
    ==> a MOD m = b MOD m          by MOD_MOD_EQN, 0 < m
    and a MOD n = b MOD n          by MOD_MOD_EQN, 0 < n
*)
Theorem mod_mod_prod_eq:
  !m n a b. 0 < m /\ 0 < n /\ a MOD (m * n) = b MOD (m * n) ==>
            a MOD m = b MOD m /\ a MOD n = b MOD n
Proof
  ntac 5 strip_tac >>
  `!a b. b <= a /\ a MOD (m * n) = b MOD (m * n) ==>
            a MOD m = b MOD m /\ a MOD n = b MOD n` by
  (ntac 3 strip_tac >>
  `0 < m * n` by fs[] >>
  `?c. a' = b' + c * (m * n)` by metis_tac[MOD_MOD_EQN] >>
  `a' = b' + (c * m) * n` by decide_tac >>
  `a' = b' + (c * n) * m` by decide_tac >>
  metis_tac[MOD_MOD_EQN]) >>
  (Cases_on `b <= a` >> simp[])
QED

(* Idea: converse of mod_mod_prod_eq when coprime. *)

(* Theorem: 0 < m /\ 0 < n /\ coprime m n /\
            a MOD m = b MOD m /\ a MOD n = b MOD n ==>
            a MOD (m * n) = b MOD (m * n) *)
(* Proof:
   Either b <= a, or a < b, which implies a <= b.
   The statement is symmetrical in a and b,
   so proceed by lemma with b <= a, without loss of generality.
   Note 0 < m * n                  by MULT_POS
    and ?h. a = b + h * m          by MOD_MOD_EQN, 0 < m
    and ?k. a = b + k * n          by MOD_MOD_EQN, 0 < n
    ==> h * m = k * n              by EQ_ADD_LCANCEL
   Thus n divides (h * m)          by divides_def
     or n divides h                by euclid_coprime, coprime m n
    ==> ?c. h = c * n              by divides_def
     so a = b + c * (m * n)        by above
   Thus a MOD (m * n) = b MOD (m * n)
                                   by MOD_MOD_EQN, 0 < m * n
*)
Theorem coprime_mod_mod_prod_eq:
  !m n a b. 0 < m /\ 0 < n /\ coprime m n /\
            a MOD m = b MOD m /\ a MOD n = b MOD n ==>
            a MOD (m * n) = b MOD (m * n)
Proof
  rpt strip_tac >>
  `!a b. b <= a /\ a MOD m = b MOD m /\ a MOD n = b MOD n ==>
             a MOD (m * n) = b MOD (m * n)` by
  (rpt strip_tac >>
  `0 < m * n` by fs[] >>
  `?h. a' = b' + h * m` by metis_tac[MOD_MOD_EQN] >>
  `?k. a' = b' + k * n` by metis_tac[MOD_MOD_EQN] >>
  `h * m = k * n` by decide_tac >>
  `n divides (h * m)` by metis_tac[divides_def] >>
  `n divides h` by metis_tac[euclid_coprime, MULT_COMM] >>
  `?c. h = c * n` by rw[GSYM divides_def] >>
  `a' = b' + c * (m * n)` by fs[] >>
  metis_tac[MOD_MOD_EQN]) >>
  (Cases_on `b <= a` >> simp[])
QED

(* Idea: combine both parts for a MOD (m * n) = b MOD (m * n). *)

(* Theorem: 0 < m /\ 0 < n /\ coprime m n ==>
            !a b. a MOD (m * n) = b MOD (m * n) <=> a MOD m = b MOD m /\ a MOD n = b MOD n *)
(* Proof:
   If part is true             by mod_mod_prod_eq
   Only-if part is true        by coprime_mod_mod_prod_eq
*)
Theorem coprime_mod_mod_prod_eq_iff:
  !m n. 0 < m /\ 0 < n /\ coprime m n ==>
        !a b. a MOD (m * n) = b MOD (m * n) <=> a MOD m = b MOD m /\ a MOD n = b MOD n
Proof
  metis_tac[mod_mod_prod_eq, coprime_mod_mod_prod_eq]
QED

(* Idea: application, the Chinese Remainder Theorem for two coprime moduli. *)

(* Theorem: 0 < m /\ 0 < n /\ coprime m n ==>
            ?!x. x < m * n /\ x MOD m = a MOD m /\ x MOD n = b MOD n *)
(* Proof:
   By EXISTS_UNIQUE_THM, this is to show:
   (1) Existence: ?x. x < m * n /\ x MOD m = a MOD m /\ x MOD n = b MOD n
   Note ?p q. (p * m + q * n) MOD (m * n) = 1 MOD (m * n)
                                               by coprime_linear_mod_prod
     so (p * m + q * n) MOD m = 1 MOD m
    and (p * m + q * n) MOD n = 1 MOD n        by mod_mod_prod_eq
     or (q * n) MOD m = 1 MOD m                by MOD_TIMES
    and (p * m) MOD n = 1 MOD n                by MOD_TIMES
   Let z = b * p * m + a * q * n.
           z MOD m
         = (b * p * m + a * q * n) MOD m
         = (a * q * n) MOD m                   by MOD_TIMES
         = ((a MOD m) * (q * n) MOD m) MOD m   by MOD_TIMES2
         = a MOD m                             by MOD_TIMES, above
   and     z MOD n
         = (b * p * m + a * q * n) MDO n
         = (b * p * m) MOD n                   by MOD_TIMES
         = ((b MOD n) * (p * m) MOD n) MOD n   by MOD_TIMES2
         = b MOD n                             by MOD_TIMES, above
   Take x = z MOD (m * n).
   Then x < m * n                              by MOD_LESS
    and x MOD m = z MOD m = a MOD m            by MOD_MULT_MOD
    and x MOD n = z MOD n = b MOD n            by MOD_MULT_MOD
   (2) Uniqueness:
       x < m * n /\ x MOD m = a MOD m /\ x MOD n = b MOD n /\
       y < m * n /\ y MOD m = a MOD m /\ y MOD n = b MOD n ==> x = y
   Note x MOD m = y MOD m                      by both equal to a MOD m
    and x MOD n = y MOD n                      by both equal to b MOD n
   Thus x MOD (m * n) = y MOD (m * n)          by coprime_mod_mod_prod_eq
     so             x = y                      by LESS_MOD, both < m * n
*)
Theorem coprime_mod_mod_solve:
  !m n a b. 0 < m /\ 0 < n /\ coprime m n ==>
            ?!x. x < m * n /\ x MOD m = a MOD m /\ x MOD n = b MOD n
Proof
  rw[EXISTS_UNIQUE_THM] >| [
    `?p q. (p * m + q * n) MOD (m * n) = 1 MOD (m * n)` by rw[coprime_linear_mod_prod] >>
    qabbrev_tac `u = p * m + q * n` >>
    `u MOD m = 1 MOD m /\ u MOD n = 1 MOD n` by metis_tac[mod_mod_prod_eq] >>
    `(q * n) MOD m = 1 MOD m /\ (p * m) MOD n = 1 MOD n` by rfs[MOD_TIMES, Abbr`u`] >>
    qabbrev_tac `z = b * p * m + a * q * n` >>
    qexists_tac `z MOD (m * n)` >>
    rw[] >| [
      `z MOD (m * n) MOD m = z MOD m` by rw[MOD_MULT_MOD] >>
      `_ = (a * q * n) MOD m` by rw[Abbr`z`] >>
      `_ = ((a MOD m) * (q * n) MOD m) MOD m` by rw[MOD_TIMES2] >>
      `_ = a MOD m` by fs[] >>
      decide_tac,
      `z MOD (m * n) MOD n = z MOD n` by metis_tac[MOD_MULT_MOD, MULT_COMM] >>
      `_ = (b * p * m) MOD n` by rw[Abbr`z`] >>
      `_ = ((b MOD n) * (p * m) MOD n) MOD n` by rw[MOD_TIMES2] >>
      `_ = b MOD n` by fs[] >>
      decide_tac
    ],
    metis_tac[coprime_mod_mod_prod_eq, LESS_MOD]
  ]
QED

(* Yes! The Chinese Remainder Theorem with two modular equations. *)

(*
For an algorithm:
* define bezout, input pair (m, n), output pair (p, q)
* define a dot-product:
        (p, q) dot (m, n) = p * m + q * n
  with  (p, q) dot (m, n) MOD (m * n) = (gcd m n) MOD (m * n)
* define a scale-product:
        (a, b) scale (p, q) = (a * p, b * q)
  with  z = ((a, b) scale (p, q)) dot (m, n)
   and  x = z MOD (m * n)
          = (((a, b) scale (p, q)) dot (m, n)) MOD (m * n)
          = (((a, b) scale (bezout (m, n))) dot (m, n)) MOD (m * n)

Note that bezout (m, n) is the extended Euclidean algorithm.

*)

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
   count m = {i | i < m}                  defined in pred_set
   residue m = {i | 0 < i /\ i < m}       defined in Euler
   The difference i = 0 gives n ** 0 = 1, which does not make a difference for PROD_SET.
*)

(* Theorem: PROD_SET (IMAGE (\j. n ** j) (count m)) =
            PROD_SET (IMAGE (\j. n ** j) (residue m)) *)
(* Proof:
   Let f = \j. n ** j.
   When m = 0,
      Note count 0 = {}            by COUNT_0
       and residue 0 = {}          by residue_0
      Thus LHS = RHS.
   When m = 1,
      Note count 1 = {0}           by COUNT_1
       and residue 1 = {}          by residue_1
      Thus LHS = PROD_SET (IMAGE f {0})
               = PROD_SET {f 0}    by IMAGE_SING
               = f 0               by PROD_SET_SING
               = n ** 0 = 1        by EXP_0
           RHS = PROD_SET (IMAGE f {})
               = PROD_SET {}       by IMAGE_EMPTY
               = 1                 by PROD_SET_EMPTY
               = LHS
   For m <> 0, m <> 1,
   When n = 0,
      Note !j. f j = f j = 0 then 1 else 0     by ZERO_EXP
      Thus IMAGE f (count m) = {0; 1}          by count_def, EXTENSION, 1 < m
       and IMAGE f (residue m) = {0}           by residue_def, EXTENSION, 1 < m
      Thus LHS = PROD_SET {0; 1}
               = 0 * 1 = 0                     by PROD_SET_THM
           RHS = PROD_SET {0}
               = 0 = LHS                       by PROD_SET_SING
   When n = 1,
      Note f = K 1                             by EXP_1, FUN_EQ_THM
       and count m <> {}                       by COUNT_NOT_EMPTY, 0 < m
       and residue m <> {}                     by residue_nonempty, 1 < m
      Thus LHS = PROD_SET (IMAGE (K 1) (count m))
               = PROD_SET {1}                          by IMAGE_K
               = PROD_SET (IMAGE (K 1) (residue m))    by IMAGE_K
               = RHS
   For 1 < m, and 1 < n,
   Note 0 IN count m                                   by IN_COUNT, 0 < m
   also (IMAGE f (count m)) DELETE 1
       = IMAGE f (residue m)                           by IMAGE_DEF, EXP_EQ_1, EXP, 1 < n
     PROD_SET (IMAGE f (count m))
   = PROD_SET (IMAGE f (0 INSERT count m))             by ABSORPTION
   = PROD_SET (f 0 INSERT IMAGE f (count m))           by IMAGE_INSERT
   = n ** 0 * PROD_SET ((IMAGE f (count m)) DELETE n ** 0)  by PROD_SET_THM
   = PROD_SET ((IMAGE f (count m)) DELETE 1)           by EXP_0
   = PROD_SET ((IMAGE f (residue m)))                  by above
*)
Theorem PROD_SET_IMAGE_EXP_NONZERO:
  !n m. PROD_SET (IMAGE (\j. n ** j) (count m)) =
        PROD_SET (IMAGE (\j. n ** j) (residue m))
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \j. n ** j` >>
  Cases_on `m = 0` >-
  simp[residue_0] >>
  Cases_on `m = 1` >-
  simp[residue_1, COUNT_1, Abbr`f`, PROD_SET_THM] >>
  `0 < m /\ 1 < m` by decide_tac >>
  Cases_on `n = 0` >| [
    `!j. f j = if j = 0 then 1 else 0` by rw[Abbr`f`] >>
    `IMAGE f (count m) = {0; 1}` by
  (rw[EXTENSION, EQ_IMP_THM] >-
    metis_tac[ONE_NOT_ZERO] >>
    metis_tac[]
    ) >>
    `IMAGE f (residue m) = {0}` by
    (rw[residue_def, EXTENSION, EQ_IMP_THM] >>
    `0 < 1` by decide_tac >>
    metis_tac[]) >>
    simp[PROD_SET_THM],
    Cases_on `n = 1` >| [
      `f = K 1` by rw[FUN_EQ_THM, Abbr`f`] >>
      `count m <> {}` by fs[COUNT_NOT_EMPTY] >>
      `residue m <> {}` by fs[residue_nonempty] >>
      simp[IMAGE_K],
      `0 < n /\ 1 < n` by decide_tac >>
      `0 IN count m` by rw[] >>
      `FINITE (IMAGE f (count m))` by rw[] >>
      `(IMAGE f (count m)) DELETE 1 = IMAGE f (residue m)` by
  (rw[residue_def, IMAGE_DEF, Abbr`f`, EXTENSION, EQ_IMP_THM] >-
      metis_tac[EXP, NOT_ZERO] >-
      metis_tac[] >>
      `j <> 0` by decide_tac >>
      metis_tac[EXP_EQ_1]
      ) >>
      `PROD_SET (IMAGE f (count m)) = PROD_SET (IMAGE f (0 INSERT count m))` by metis_tac[ABSORPTION] >>
      `_ = PROD_SET (f 0 INSERT IMAGE f (count m))` by rw[] >>
      `_ = n ** 0 * PROD_SET ((IMAGE f (count m)) DELETE n ** 0)` by rw[PROD_SET_THM, Abbr`f`] >>
      `_ = 1 * PROD_SET ((IMAGE f (count m)) DELETE 1)` by metis_tac[EXP_0] >>
      `_ = PROD_SET ((IMAGE f (residue m)))` by rw[] >>
      decide_tac
    ]
  ]
QED

(* Overload sublist by infix operator *)
val _ = temp_overload_on ("<=", ``sublist``);

(* Theorem: m < n ==> [m; n] <= [m .. n] *)
(* Proof:
   By induction on n.
   Base: !m. m < 0 ==> [m; 0] <= [m .. 0], true       by m < 0 = F.
   Step: !m. m < n ==> [m; n] <= [m .. n] ==>
         !m. m < SUC n ==> [m; SUC n] <= [m .. SUC n]
        Note m < SUC n means m <= n.
        If m = n, LHS = [n; SUC n]
                  RHS = [n .. (n + 1)] = [n; SUC n]   by ADD1
                      = LHS, thus true                by sublist_refl
        If m < n,              [m; n] <= [m .. n]     by induction hypothesis
                  SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n] by sublist_snoc
                        [m; n; SUC n] <= [m .. SUC n]          by SNOC, listRangeINC_SNOC
           But [m; SUC n] <= [m; n; SUC n]            by sublist_def
           Thus [m; SUC n] <= [m .. SUC n]            by sublist_trans
*)
val listRangeINC_sublist = store_thm(
  "listRangeINC_sublist",
  ``!m n. m < n ==> [m; n] <= [m .. n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m = n) \/ m < n` by decide_tac >| [
    rw[listRangeINC_def, ADD1] >>
    rw[sublist_refl],
    `[m; n] <= [m .. n]` by rw[] >>
    `SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n]` by rw[sublist_snoc] >>
    `SNOC (SUC n) [m; n] = [m; n; SUC n]` by rw[] >>
    `SNOC (SUC n) [m .. n] = [m .. SUC n]` by rw[listRangeINC_SNOC, ADD1] >>
    `[m; SUC n] <= [m; n; SUC n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* Theorem: m + 1 < n ==> [m; (n - 1)] <= [m ..< n] *)
(* Proof:
   By induction on n.
   Base: !m. m + 1 < 0 ==> [m; 0 - 1] <= [m ..< 0], true  by m + 1 < 0 = F.
   Step: !m. m + 1 < n ==> [m; n - 1] <= [m ..< n] ==>
         !m. m + 1 < SUC n ==> [m; SUC n - 1] <= [m ..< SUC n]
        Note m + 1 < SUC n means m + 1 <= n.
        If m + 1 = n, LHS = [m; SUC n - 1] = [m; n]
                  RHS = [m ..< (n + 1)] = [m; n]          by ADD1
                      = LHS, thus true                    by sublist_refl
        If m + 1 < n,    [m; n - 1] <= [m ..< n]          by induction hypothesis
                  SNOC n [m; n - 1] <= SNOC n [m ..< n]   by sublist_snoc
                      [m; n - 1; n] <= [m ..< SUC n]      by SNOC, listRangeLHI_SNOC, ADD1
           But [m; SUC n - 1] <= [m; n] <= [m; n - 1; n]  by sublist_def
           Thus [m; SUC n - 1] <= [m ..< SUC n]           by sublist_trans
*)
val listRangeLHI_sublist = store_thm(
  "listRangeLHI_sublist",
  ``!m n. m + 1 < n ==> [m; (n - 1)] <= [m ..< n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `SUC n - 1 = n` by decide_tac >>
  `(m + 1 = n) \/ m + 1 < n` by decide_tac >| [
    rw[listRangeLHI_def, ADD1] >>
    rw[sublist_refl],
    `[m; n - 1] <= [m ..< n]` by rw[] >>
    `SNOC n [m; n - 1] <= SNOC n [m ..< n]` by rw[sublist_snoc] >>
    `SNOC n [m; n - 1] = [m; n - 1; n]` by rw[] >>
    `SNOC n [m ..< n] = [m ..< SUC n]` by rw[listRangeLHI_SNOC, ADD1] >>
    `[m; SUC n - 1] <= [m; n - 1; n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* Theorem: sl <= ls /\ ALL_DISTINCT ls /\ j < h /\ h < LENGTH sl ==>
            findi (EL j sl) ls < findi (EL h sl) ls *)
(* Proof:
   Let x = EL j sl,
       y = EL h sl,
       p = findi x ls,
       q = findi y ls.
   Then MEM x sl /\ MEM y sl                   by EL_MEM
    and ALL_DISTINCT sl                        by sublist_ALL_DISTINCT

   With MEM x sl,
   Note ?l1 l2 l3 l4. ls = l1 ++ [x] ++ l2 /\
                      sl = l3 ++ [x] ++ l4 /\
                      l3 <= l1 /\ l4 <= l2     by sublist_order, sl <= ls
   Thus j = LENGTH l3                          by ALL_DISTINCT_EL_APPEND, j < LENGTH sl

   Claim: MEM y l4
   Proof: By contradiction, suppose ~MEM y l4.
          Note y <> x                          by ALL_DISTINCT_EL_IMP, j <> h
           ==> MEM y l3                        by MEM_APPEND
           ==> ?k. k < LENGTH l3 /\ y = EL k l3   by MEM_EL
           But LENGTH l3 < LENGTH sl           by LENGTH_APPEND
           and y = EL k sl                     by EL_APPEND1
          Thus k = h                           by ALL_DISTINCT_EL_IMP, k < LENGTH sl
            or h < j, contradicting j < h      by j = LENGTH l3

   Thus ?l5 l6 l7 l8. l2 = l5 ++ [x] ++ l6 /\
                      l4 = l7 ++ [x] ++ l8 /\
                      l7 <= l5 /\ l8 <= l6     by sublist_order, l4 <= l2

   Hence, ls = l1 ++ [x] ++ l5 ++ [y] ++ l6.
    Now p < LENGTH ls /\ q < LENGTH ls         by MEM_findi
     so x = EL p ls /\ y = EL q ls             by findi_EL_iff
    and p = LENGTH l1                          by ALL_DISTINCT_EL_APPEND
    and q = LENGTH (l1 ++ [x] ++ l5)           by ALL_DISTINCT_EL_APPEND
   Thus p < q                                  by LENGTH_APPEND
*)
Theorem sublist_element_order:
  !ls sl j h. sl <= ls /\ ALL_DISTINCT ls /\ j < h /\ h < LENGTH sl ==>
              findi (EL j sl) ls < findi (EL h sl) ls
Proof
  rpt strip_tac >>
  qabbrev_tac `x = EL j sl` >>
  qabbrev_tac `y = EL h sl` >>
  qabbrev_tac `p = findi x ls` >>
  qabbrev_tac `q = findi y ls` >>
  `MEM x sl /\ MEM y sl` by fs[EL_MEM, Abbr`x`, Abbr`y`] >>
  assume_tac sublist_order >>
  last_x_assum (qspecl_then [`ls`, `sl`, `x`] strip_assume_tac) >>
  rfs[] >>
  `ALL_DISTINCT sl` by metis_tac[sublist_ALL_DISTINCT] >>
  `j = LENGTH l3` by metis_tac[ALL_DISTINCT_EL_APPEND, LESS_TRANS] >>
  `MEM y l4` by
  (spose_not_then strip_assume_tac >>
  `y <> x` by fs[ALL_DISTINCT_EL_IMP, Abbr`x`, Abbr`y`] >>
  `MEM y l3` by fs[] >>
  `?k. k < LENGTH l3 /\ y = EL k l3` by simp[GSYM MEM_EL] >>
  `LENGTH l3 < LENGTH sl` by fs[] >>
  `y = EL k sl` by fs[EL_APPEND1] >>
  `k = h` by metis_tac[ALL_DISTINCT_EL_IMP, LESS_TRANS] >>
  decide_tac) >>
  assume_tac sublist_order >>
  last_x_assum (qspecl_then [`l2`, `l4`, `y`] strip_assume_tac) >>
  rfs[] >>
  rename1 `l2 = l5 ++ [y] ++ l6` >>
  `p < LENGTH ls /\ q < LENGTH ls` by fs[MEM_findi, Abbr`p`, Abbr`q`] >>
  `x = EL p ls /\ y = EL q ls` by fs[findi_EL_iff, Abbr`p`, Abbr`q`] >>
  `p = LENGTH l1` by metis_tac[ALL_DISTINCT_EL_APPEND] >>
  `ls = l1 ++ [x] ++ l5 ++ [y] ++ l6` by fs[] >>
  `q = LENGTH (l1 ++ [x] ++ l5)` by metis_tac[ALL_DISTINCT_EL_APPEND] >>
  fs[]
QED

(* Theorem: let fs = FILTER P ls in ALL_DISTINCT ls /\ j < h /\ h < LENGTH fs ==>
            findi (EL j fs) ls < findi (EL h fs) l *)
(* Proof:
   Let fs = FILTER P ls.
   Then fs <= ls                   by FILTER_sublist
   Thus findi (EL j fs) ls
      < findi (EL h fs) ls         by sublist_element_order
*)
Theorem FILTER_element_order:
  !P ls j h. let fs = FILTER P ls in ALL_DISTINCT ls /\ j < h /\ h < LENGTH fs ==>
             findi (EL j fs) ls < findi (EL h fs) ls
Proof
  rw_tac std_ss[] >>
  `fs <= ls` by simp[FILTER_sublist, Abbr`fs`] >>
  fs[sublist_element_order]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
