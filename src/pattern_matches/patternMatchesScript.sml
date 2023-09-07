open HolKernel Parse boolLib Drule BasicProvers
open simpLib TotalDefn ConseqConv numLib
open quantHeuristicsLib
open optionTheory
open listTheory
open metisLib

val _ = new_theory "patternMatches"

val std_ss = numLib.std_ss
val list_ss  = numLib.arith_ss ++ listSimps.LIST_ss
val zDefine    = Lib.with_flag (computeLib.auto_import_definitions,false) Define

val _ = ParseExtras.temp_loose_equality()


(***************************************************)
(* Auxiliary stuff                                 *)
(***************************************************)

val IS_SOME_OPTION_MAP = prove (
  ``!f v. IS_SOME (OPTION_MAP f v) = IS_SOME v``,
Cases_on `v` THEN
SIMP_TAC list_ss [])

val some_eq_SOME = prove (
  ``!P x. ((some x. P x) = SOME x) ==> (P x)``,
SIMP_TAC std_ss [some_def] THEN
REPEAT STRIP_TAC THEN
SELECT_ELIM_TAC THEN
PROVE_TAC[])

val some_var_bool_T = store_thm ("some_var_bool_T",
  ``(some x. x) = SOME T``,
  `(some x. x) = (some x. (x = T))` by REWRITE_TAC[] THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  PURE_REWRITE_TAC[optionTheory.some_EQ] THEN
  REWRITE_TAC[]
)

val some_var_bool_F = store_thm ("some_var_bool_F",
  ``(some x. ~x) = SOME F``,
  `(some x. ~x) = (some x. (x = F))` by REWRITE_TAC[] THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  PURE_REWRITE_TAC[optionTheory.some_EQ] THEN
  REWRITE_TAC[]
)

val some_eq_NONE = prove (
  ``!P. ((some x. P x) = NONE) <=> (!x. ~(P x))``,
SIMP_TAC std_ss [some_def])

val some_IS_SOME = prove (
  ``!P. (IS_SOME (some x. P x)) <=> (?x. P x)``,
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [some_def])

val some_IS_SOME_EXISTS = prove (
  ``!P. (IS_SOME (some x. P x)) <=> (?x. P x /\ ((some x. P x) = SOME x))``,
GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN (
  ASM_SIMP_TAC std_ss []
) THEN
Cases_on `some x. P x` THEN FULL_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC some_eq_SOME THEN
ASM_REWRITE_TAC[])

val OPTION_MAP_EQ_OPTION_MAP = prove (
``(OPTION_MAP f x = OPTION_MAP f' x') =
  (((x = NONE) /\ (x' = NONE)) \/
   (?y y'. (x = SOME y) /\ (x' = SOME y') /\ (f y = f' y')))``,

Cases_on `x` THEN Cases_on `x'` THEN (
  SIMP_TAC std_ss []
))


(***************************************************)
(* Main Definitions                                *)
(***************************************************)

(* rows of a case-expression consist of a
   - pattern p
   - guard g
   - rhs r

   A row matches an input value i with a variable
   binding v, iff the following
   predicate holds. *)
val PMATCH_ROW_COND_def = zDefine `PMATCH_ROW_COND pat guard inp v =
  (pat v = inp) /\ (guard v)`

(* With this we can easily define the semantics of a row *)
val PMATCH_ROW_def = zDefine `PMATCH_ROW pat guard rhs i =
  (OPTION_MAP rhs (some v. PMATCH_ROW_COND pat guard i v))`


(* We defined semantics of single rows. Let's extend
   it to multiple ones, i.e. full pattern matches now. *)
val PMATCH_INCOMPLETE_def = Define `PMATCH_INCOMPLETE = ARB`
val PMATCH_def = zDefine `
  (PMATCH v [] = PMATCH_INCOMPLETE) /\
  (PMATCH v (r::rs) = option_CASE (r v) (PMATCH v rs) I)`


(***************************************************)
(* Constants for parsing magic                     *)
(***************************************************)

(* We need some dummy constant without any semnatic meaning
   for setting up some parser magic. It is HOL 4 specific
   and boring technical stuff. You can safely ignore the following. *)

val _ = new_constant ("PMATCH_magic_1", type_of ``PMATCH``)

val _ = new_constant ("PMATCH_ROW_magic_1", type_of
   ``\abc. PMATCH_ROW (\x. FST (abc x)) (\x. FST (SND (abc x))) (\x. SND (SND ((abc x))))``)

val _ = new_constant ("PMATCH_ROW_magic_0", type_of
   ``\abc. PMATCH_ROW (\x:unit. FST abc) (\x. FST (SND abc)) (\x. SND (SND (abc)))``)

val _ = new_constant ("PMATCH_ROW_magic_4", type_of
   ``\abc. PMATCH_ROW (\x:unit. FST abc) (\x. FST (SND abc)) (\x. SND (SND (abc)))``)

val _ = new_constant ("PMATCH_ROW_magic_2", type_of
   ``\(pat:'a) (g:bool) (res:'b). (pat,g,res)``)

val _ = new_constant ("PMATCH_ROW_magic_3", type_of
   ``\(pat:'a) (res:'b). (pat,T,res)``)



(***************************************************)
(* Congruences for termination                     *)
(***************************************************)

(* Pattern matches expressed via PMATCH should
   be usable in recursive function defintions. In  order
   to be able to do this, we need to set up some
   congruence theorems that guide the automatic
   wellfoundedness (termination) checker. *)

val PMATCH_ROW_CONG = store_thm ("PMATCH_ROW_CONG",
``!p p' g g' r r' v v'.
     (p = p') /\ (v = v') /\
     (!x. (v = (p x)) ==> (g x = g' x)) /\
     (!x. ((v = (p x)) /\ (g x)) ==>
          (r x = r' x)) ==>
  (PMATCH_ROW p g r v = PMATCH_ROW p' g' r' v')``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [PMATCH_ROW_def,
  PMATCH_ROW_COND_def] THEN
Cases_on `some x. (p' x = v') /\ (g' x)` THEN (
  ASM_SIMP_TAC std_ss []
) THEN
POP_ASSUM (fn thm => MP_TAC (HO_MATCH_MP (SPEC_ALL some_eq_SOME) thm)) THEN
ASM_SIMP_TAC std_ss [])


val PMATCH_CONG = store_thm ("PMATCH_CONG",
``!v v' rows rows' r r'. ((v = v') /\ (r v' = r' v') /\
        (PMATCH v' rows = PMATCH v' rows')) ==>
  (PMATCH v (r :: rows) = PMATCH v' (r' :: rows'))``,
SIMP_TAC std_ss [PMATCH_def])

val _ = DefnBase.export_cong "PMATCH_ROW_CONG";
val _ = DefnBase.export_cong "PMATCH_CONG";


(***************************************************)
(* Rewrites                                        *)
(***************************************************)

val PMATCH_ROW_EQ_AUX = store_thm ("PMATCH_ROW_EQ_AUX",
  ``((!i. (?x. PMATCH_ROW_COND p  g  i x) =
          (?x'. PMATCH_ROW_COND p' g' i x')) /\
     (!x x'. ((p x = p' x') /\ g x /\ g' x') ==> (r x = r' x'))) ==>
    (PMATCH_ROW p  g  r  = PMATCH_ROW p' g' r')``,
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [FUN_EQ_THM, PMATCH_ROW_def,
  OPTION_MAP_EQ_OPTION_MAP] THEN
CONV_TAC (RENAME_VARS_CONV ["i"]) THEN
GEN_TAC THEN
Q.PAT_X_ASSUM `!i. (_ = _)` (fn thm => ASSUME_TAC (Q.SPEC `i` thm))  THEN
Tactical.REVERSE (Cases_on `?x. PMATCH_ROW_COND p g i x`) THEN (
  FULL_SIMP_TAC std_ss []
) THEN
DISJ2_TAC THEN
`IS_SOME (some x. PMATCH_ROW_COND p g i x) /\
 IS_SOME (some x. PMATCH_ROW_COND p' g' i x)` by (
  ASM_SIMP_TAC std_ss [some_IS_SOME] THEN
  PROVE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [some_IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [PMATCH_ROW_COND_def])

val PMATCH_ROW_EQ_NONE = store_thm ("PMATCH_ROW_EQ_NONE",
  ``(PMATCH_ROW p g r i = NONE) <=>
    (!x. ~(PMATCH_ROW_COND p g i x))``,
SIMP_TAC std_ss [PMATCH_ROW_def, some_eq_NONE]);

val PMATCH_ROW_EQ_SOME = store_thm ("PMATCH_ROW_EQ_SOME",
  ``(PMATCH_ROW p g r i = SOME y) ==>
    (?x. (PMATCH_ROW_COND p g i x) /\ (y = r x))``,
SIMP_TAC std_ss [PMATCH_ROW_def] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `z` THEN
IMP_RES_TAC some_eq_SOME THEN
ASM_SIMP_TAC std_ss []);


val PMATCH_COND_SELECT_UNIQUE = store_thm ("PMATCH_COND_SELECT_UNIQUE",
  ``!p g i.
    (!x1 x2. (g x1 /\ g x2 /\ (p x1 = p x2)) ==> (x1 = x2)) ==>
    !x. PMATCH_ROW_COND p g i x ==>
    ((@y. PMATCH_ROW_COND p g i y) = x)``,

SIMP_TAC std_ss [PMATCH_ROW_COND_def] THEN
METIS_TAC[]);

val PMATCH_ROW_COND_DEF_GSYM = store_thm ("PMATCH_ROW_COND_DEF_GSYM",
  ``PMATCH_ROW_COND pat guard inp v =
    ((inp = pat v) /\ (guard v))``,
SIMP_TAC std_ss [PMATCH_ROW_COND_def] THEN
PROVE_TAC[])


val PMATCH_EVAL = store_thm ("PMATCH_EVAL",
 ``(PMATCH v [] = PMATCH_INCOMPLETE) /\
   (PMATCH v ((PMATCH_ROW p g r) :: rs) =
      if (?x. (PMATCH_ROW_COND p g v x)) then
         (r (@x. PMATCH_ROW_COND p g v x)) else PMATCH v rs)``,

SIMP_TAC std_ss [PMATCH_def] THEN
Cases_on `PMATCH_ROW p g r v` THENL [
  FULL_SIMP_TAC std_ss [PMATCH_ROW_def, some_eq_NONE],

  FULL_SIMP_TAC std_ss [PMATCH_ROW_def, some_def] THEN
  METIS_TAC[]
])

val PMATCH_EVAL_MATCH = store_thm ("PMATCH_EVAL_MATCH",
 ``~(PMATCH_ROW p g r v = NONE) ==>
   (PMATCH v ((PMATCH_ROW p g r) :: rs) =
      (r (@x. PMATCH_ROW_COND p g v x)))``,

SIMP_TAC std_ss [PMATCH_EVAL,
 PMATCH_ROW_EQ_NONE]);


(***************************************************)
(* Changing rows and removing redundant ones       *)
(***************************************************)

(* For many of automatic methods, we need to show
   that two PMATCH expressions which are derived from
   each other by modifying or dropping rows are equivalent.
   We want to perform these proofs in an a way that can be
   automated nicely. In the following, we provide lemmata that
   given an established equivalence, allow adding
   a row to both or a single side.
   By starting with an empty list and iterating, one can
   use this method to construct the desired correspondance. *)
val PMATCH_EXTEND_BASE = store_thm ("PMATCH_EXTEND_BASE",
``!v_old v_new. (PMATCH v_old [] = PMATCH v_new [])``,
SIMP_TAC std_ss [PMATCH_def])

val PMATCH_EXTEND_BOTH = store_thm ("PMATCH_EXTEND_BOTH",
``!v_old v_new rows_old rows_new r_old r_new.
  (r_old v_old = r_new v_new) ==>
  (PMATCH v_old rows_old = PMATCH v_new rows_new) ==>
  (PMATCH v_old (r_old::rows_old) = PMATCH v_new (r_new :: rows_new))``,
SIMP_TAC std_ss [PMATCH_def])

val PMATCH_EXTEND_BOTH_ID = store_thm ("PMATCH_EXTEND_BOTH_ID",
``!v rows_old rows_new r.
  (PMATCH v rows_old = PMATCH v rows_new) ==>
  (PMATCH v (r::rows_old) = PMATCH v (r :: rows_new))``,
SIMP_TAC std_ss [PMATCH_def])

val PMATCH_EXTEND_OLD = store_thm ("PMATCH_EXTEND_OLD",
``!v_old v_new rows_old rows_new r_old.
  (r_old v_old = NONE) ==>
  (PMATCH v_old rows_old = PMATCH v_new rows_new) ==>
  (PMATCH v_old (r_old::rows_old) = PMATCH v_new rows_new)``,
SIMP_TAC std_ss [PMATCH_def])



(***************************************************)
(* Simplifying case expressions                    *)
(***************************************************)

(* We can now construct equivalences of case expressions, provided
   we can reason about the semantics of single rows. So,
   let's now consider useful theorems for single rows. *)

(* Add an injective function to the pattern and the value.
   This can be used to eliminate constructors. *)
val PMATCH_ROW_REMOVE_FUN = store_thm ("PMATCH_ROW_REMOVE_FUN",
``!ff v p g r. (!x y. (ff x = ff y) ==> (x = y)) ==>

  (PMATCH_ROW (\x. (ff (p x))) g r (ff v) =
   PMATCH_ROW (\x. (p x)) g r v)``,

REPEAT STRIP_TAC THEN
`!x y. (ff x = ff y) = (x = y)` by PROVE_TAC[] THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def, PMATCH_ROW_COND_def])


(* The following lemma looks rather complicated. It is
   intended to work together with PMATCH_ROW_REMOVE_FUN to
   propagate information in the var cases.

   as an example consider

   val t = ``PMATCH (SOME x, y) [
     PMATCH_ROW (\x. (SOME x, 0)) (K T) (\x. (SOME (x + y)));
     PMATCH_ROW (\(x', y). (x', y)) (K T) (\(x', y). x')
   ]``

   We want to simplify this to

   val t = ``PMATCH (x, y) [
     PMATCH_ROW (\x. (x, 0)) (K T) (\x. (SOME (x + y)));
     PMATCH_ROW (\(x'', y). (x'', y)) (K T) (\(x'', y). SOME x'')
   ]``

   This is done via PMATCH_ROWS_SIMP and PMATCH_ROWS_SIMP_SOUNDNESS.
   We need to show that the rows correspond to each other.

   For the first row, PMATCH_ROW_REMOVE_FUN is used with

   v := (x, y)
   ff (x, y) := (SOME x, y)

   p x := (x, 0)
   r x := SOME (x + y)


   For the second row, PMATCH_ROW_REMOVE_FUN is used with

   v := (SOME x, y)
   v' := (x, y)
   p (x', y) := (x', y)
   r (x', y) := x'
   p' (x'', y) = (x'', y)
   f (x'', y) := (SOME x'', y)
*)

val PMATCH_ROW_EXTEND_INPUT = store_thm ("PMATCH_ROW_EXTEND_INPUT",
``!v v' f' f p g r p' .
  ((!x'. (v' = p' x') ==> (p (f x') = v)) /\
   (!x. (v = p x) ==> ?x'. (p' x' = v')) /\
   (!x y. (p x = p y) ==> (x = y))) ==>
  (PMATCH_ROW p (g (f' v')) (r (f' v')) v =
   PMATCH_ROW p' (\x. g (f' (p' x)) (f x)) (\x. r (f' (p' x)) (f x)) v')``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
`IS_SOME (some x. PMATCH_ROW_COND p' (\x. g (f' (p' x)) (f x)) v' x) =
 IS_SOME (some x. PMATCH_ROW_COND p (g (f' v')) v x)` by (
   ASM_SIMP_TAC std_ss [some_IS_SOME, PMATCH_ROW_COND_def] THEN
   METIS_TAC[]
) THEN
Tactical.REVERSE (Cases_on `IS_SOME (some x. PMATCH_ROW_COND p (g (f' v')) v x)`) THEN (
  FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [some_IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [PMATCH_ROW_COND_def] THEN
METIS_TAC[]);


val PMATCH_ROW_REMOVE_FUN_VAR = store_thm ("PMATCH_ROW_REMOVE_FUN_VAR",
``!v v' f p g r p' .
  ((!x'. (v' = p' x') = (p (f x') = v)) /\
  ((!x. (v = p x) ==> ?x'. f x' = x)) /\
  ((!x y. (p x = p y) ==> (x = y)))) ==>
  (PMATCH_ROW p g r v =
   PMATCH_ROW p' (\x. g (f x)) (\x. r (f x)) v')``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
`IS_SOME (some x. PMATCH_ROW_COND p' (\x. g (f x)) v' x) =
 IS_SOME (some x. PMATCH_ROW_COND p g v x)` by (
   ASM_SIMP_TAC std_ss [some_IS_SOME, PMATCH_ROW_COND_def] THEN
   METIS_TAC[]
) THEN
Tactical.REVERSE (Cases_on `IS_SOME (some x. PMATCH_ROW_COND p g v x)`) THEN (
  FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [some_IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [PMATCH_ROW_COND_def] THEN
METIS_TAC[]);


(***************************************************)
(* Equivalent sets of rows                         *)
(***************************************************)

val PMATCH_EQUIV_ROWS_def = Define `
 PMATCH_EQUIV_ROWS v rows1 rows2 = (
 (PMATCH v rows1 = PMATCH v rows2) /\
 ((?r. MEM r rows1 /\ IS_SOME (r v)) =
  (?r. MEM r rows2 /\ IS_SOME (r v))))`


val PMATCH_EQUIV_ROWS_EQUIV_EXPAND = store_thm ("PMATCH_EQUIV_ROWS_EQUIV_EXPAND",
  ``PMATCH_EQUIV_ROWS v rows1 rows2 = (
    PMATCH_EQUIV_ROWS v rows1 = PMATCH_EQUIV_ROWS v rows2)``,

SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def, FUN_EQ_THM] THEN
METIS_TAC[])

val PMATCH_EQUIV_ROWS_is_equiv_1 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_1",
  ``(!v rows. (PMATCH_EQUIV_ROWS v rows rows))``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def])


val PMATCH_EQUIV_ROWS_is_equiv_2 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_2",
  ``(!v rows1 rows2. ((PMATCH_EQUIV_ROWS v rows1 rows2) =
                      (PMATCH_EQUIV_ROWS v rows2 rows1)))``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def] THEN METIS_TAC[])

val PMATCH_EQUIV_ROWS_is_equiv_3 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_3",
  ``(!v rows1 rows2 rows3.
       (PMATCH_EQUIV_ROWS v rows1 rows2) ==>
       (PMATCH_EQUIV_ROWS v rows2 rows3) ==>
       (PMATCH_EQUIV_ROWS v rows1 rows3))``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def]);

val PMATCH_EQUIV_ROWS_MATCH = store_thm ("PMATCH_EQUIV_ROWS_MATCH",
  ``PMATCH_EQUIV_ROWS v rows1 rows2 ==>
    (PMATCH v rows1 = PMATCH v rows2)``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def])

val PMATCH_APPEND_SEM = store_thm ("PMATCH_APPEND_SEM",
  ``!v rows1 rows2. PMATCH v (rows1 ++ rows2) = (
      if (?r. MEM r rows1 /\ IS_SOME (r v)) then PMATCH v rows1 else PMATCH v rows2)``,
REPEAT GEN_TAC THEN
Induct_on `rows1` THEN1 (
  SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC list_ss [PMATCH_def, RIGHT_AND_OVER_OR, EXISTS_OR_THM] THEN
GEN_TAC THEN
Cases_on `h v` THEN (
  ASM_SIMP_TAC std_ss []
))

val PMATCH_EQUIV_APPEND = store_thm ("PMATCH_EQUIV_APPEND",
``!v rows1a rows1b rows2a rows2b.
  (PMATCH_EQUIV_ROWS v rows1a rows1b) ==>
  (PMATCH_EQUIV_ROWS v rows2a rows2b) ==>
  (PMATCH_EQUIV_ROWS v (rows1a ++ rows2a) (rows1b ++ rows2b))``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [PMATCH_EQUIV_ROWS_def, RIGHT_AND_OVER_OR,
  EXISTS_OR_THM, PMATCH_APPEND_SEM]);


val PMATCH_EQUIV_ROWS_CONS_NONE = store_thm("PMATCH_EQUIV_ROWS_CONS_NONE",
``(row v = NONE) ==> (
  PMATCH_EQUIV_ROWS v (row::rows) =
  PMATCH_EQUIV_ROWS v rows)``,

SIMP_TAC list_ss [GSYM PMATCH_EQUIV_ROWS_EQUIV_EXPAND,
  PMATCH_EQUIV_ROWS_def, RIGHT_AND_OVER_OR,
  EXISTS_OR_THM, PMATCH_def])



(***************************************************)
(* Simple removal of redundant rows                *)
(***************************************************)

(* If we have a row that matches, everything after it can be dropped *)
val PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS_EQUIV = store_thm ("PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS_EQUIV",
``!v rows n. ((n < LENGTH rows) /\ (IS_SOME ((EL n rows) v))) ==>
  (PMATCH_EQUIV_ROWS v rows (TAKE (SUC n) rows))``,

REPEAT STRIP_TAC THEN
`PMATCH_EQUIV_ROWS v (TAKE (SUC n) rows ++ DROP (SUC n) rows)
                     (TAKE (SUC n) rows)`
   suffices_by FULL_SIMP_TAC list_ss [] THEN

SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def, PMATCH_APPEND_SEM] THEN
SIMP_TAC list_ss [] THEN

`?r. MEM r (TAKE (SUC n) rows) /\ IS_SOME (r v)` suffices_by METIS_TAC[] THEN
Q.EXISTS_TAC `EL n (TAKE (SUC n) rows)` THEN
ASM_SIMP_TAC list_ss [rich_listTheory.MEM_TAKE, rich_listTheory.EL_MEM,
  listTheory.LENGTH_TAKE, rich_listTheory.EL_TAKE]);


val PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS = store_thm ("PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS",
``!v rows n. ((n < LENGTH rows) /\ (IS_SOME ((EL n rows) v))) ==>
  (PMATCH v rows = PMATCH v (TAKE (SUC n) rows))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC PMATCH_EQUIV_ROWS_MATCH THEN
MATCH_MP_TAC PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS_EQUIV THEN
ASM_REWRITE_TAC[])



(* A row is redundant, if (but not(!) only if) it is made
   redundant by exactly one
   row above. This is simple to test and often already very
   helful. More fancy tests involving multiple rows follow below. *)
val PMATCH_ROWS_DROP_REDUNDANT = store_thm (
  "PMATCH_ROWS_DROP_REDUNDANT",
``!r1 r2 rows1 rows2 rows3 v.
  (IS_SOME (r2 v) ==> IS_SOME (r1 v)) ==>
  (PMATCH v (rows1 ++ (r1 :: rows2) ++ (r2 :: rows3)) =
   PMATCH v (rows1 ++ (r1 :: rows2) ++ rows3))``,

REPEAT STRIP_TAC THEN
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [PMATCH_APPEND_SEM, RIGHT_AND_OVER_OR, EXISTS_OR_THM] THEN

Cases_on `?r. MEM r rows1 /\ IS_SOME (r v)` THEN (
  ASM_REWRITE_TAC []
) THEN
Cases_on `IS_SOME (r1 v)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `?r. MEM r rows2 /\ IS_SOME (r v)` THEN (
  ASM_REWRITE_TAC []
) THEN
FULL_SIMP_TAC std_ss [PMATCH_def]);


val PMATCH_ROWS_DROP_REDUNDANT_PMATCH_ROWS = store_thm (
  "PMATCH_ROWS_DROP_REDUNDANT_PMATCH_ROWS",
``!p g r p' g' r' rows1 rows2 rows3 v.
  (!x'. (v = p' x') /\ (g' x') ==> (?x. (p' x' = p x) /\ (g x))) ==>
  (PMATCH v (rows1 ++ (PMATCH_ROW p g r :: rows2) ++ (PMATCH_ROW p' g' r' :: rows3)) =
   PMATCH v (rows1 ++ (PMATCH_ROW p g r :: rows2) ++ rows3))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC PMATCH_ROWS_DROP_REDUNDANT THEN
SIMP_TAC std_ss [PMATCH_ROW_def, optionTheory.some_def,
  PMATCH_ROW_COND_def, IS_SOME_OPTION_MAP] THEN
Cases_on `?x'. (p' x' = v) /\ g' x'` THEN (
  ASM_SIMP_TAC std_ss []
) THEN
METIS_TAC[IS_SOME_DEF]);



(***************************************************)
(* Simple removal of subsumed rows                 *)
(***************************************************)

(* Some rows are not redundant in the classical sense, but can
   safely be dropped nevertheless. A redundant row never matches,
   because it is shaddowed by a previous row. One can also
   drop rows, if a later row matches if they match and returns the
   same value. I will call such rows subsumed. *)

val PMATCH_ROWS_DROP_SUBSUMED = store_thm (
  "PMATCH_ROWS_DROP_SUBSUMED",
``!r1 r2 rows1 rows2 rows3 v.
  ((!x. (r1 v = SOME x) ==> (r2 v = SOME x)) /\
   (IS_SOME (r1 v) ==> EVERY (\row. (row v = NONE)) rows2)) ==>
  (PMATCH v (rows1 ++ (r1 :: (rows2 ++ (r2 :: rows3)))) =
   PMATCH v (rows1 ++ rows2 ++ (r2 :: rows3)))``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [GSYM rich_listTheory.APPEND_ASSOC_CONS] THEN
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [PMATCH_APPEND_SEM, RIGHT_AND_OVER_OR, EXISTS_OR_THM] THEN

Cases_on `?r. MEM r rows1 /\ IS_SOME (r v)` THEN (
  ASM_REWRITE_TAC []
) THEN
Cases_on `?r. MEM r rows2 /\ IS_SOME (r v)` THEN (
  ASM_REWRITE_TAC []
) THENL [
  SIMP_TAC std_ss [PMATCH_def] THEN
  Cases_on `r1 v` THEN (
    FULL_SIMP_TAC std_ss [EVERY_MEM]
  ) THEN
  RES_TAC THEN
  FULL_SIMP_TAC std_ss [],

  Cases_on `r1 v` THEN (
    ASM_SIMP_TAC std_ss []
  ) THEN
  FULL_SIMP_TAC std_ss [PMATCH_def]
]);

val PMATCH_ROWS_DROP_SUBSUMED_PMATCH_ROWS = store_thm (
  "PMATCH_ROWS_DROP_SUBSUMED_PMATCH_ROWS",
``!p g r p' g' r' rows1 rows2 rows3 v.
  ((!x. (v = p x) /\ (g x) ==> (?x'. (p x = p' x') /\ (g' x'))) /\
   (!x x'. ((v = p x) /\ (p x = p' x') /\ g x /\ g' x') ==>
           (r x = r' x')) /\
   (!x. ((v = p x) /\ (g x)) ==> EVERY (\row. (row (p x) = NONE)) rows2)) ==>
  (PMATCH v (rows1 ++ (PMATCH_ROW p g r :: (rows2 ++ (PMATCH_ROW p' g' r' :: rows3)))) =
   PMATCH v (rows1 ++ rows2 ++ (PMATCH_ROW p' g' r' :: rows3)))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC PMATCH_ROWS_DROP_SUBSUMED THEN
SIMP_TAC std_ss [PMATCH_ROW_def, optionTheory.some_def,
  PMATCH_ROW_COND_def, IS_SOME_OPTION_MAP] THEN
Cases_on `?x. (p x = v) /\ g x` THEN (
  ASM_SIMP_TAC std_ss []
) THEN
REPEAT STRIP_TAC THENL [
  PROVE_TAC[],

  SELECT_ELIM_TAC THEN
  CONJ_TAC THEN1 PROVE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SELECT_ELIM_TAC THEN
  PROVE_TAC[],

  FULL_SIMP_TAC std_ss [] THEN
  METIS_TAC[]
]);


(* A common case for removing subsumed rows
   is removing ARB rows that are introduced by
   translating a classical case-expression naively. *)
val PMATCH_REMOVE_ARB = store_thm ("PMATCH_REMOVE_ARB",
``!p g r v rows.
  (!x. r x = ARB) ==>
  (PMATCH v (SNOC (PMATCH_ROW p g r) rows) =
   PMATCH v rows)``,

Induct_on `rows` THENL [
  SIMP_TAC list_ss [PMATCH_EVAL, PMATCH_INCOMPLETE_def],
  ASM_SIMP_TAC list_ss [PMATCH_def]
])

(* Introduce explicit catch-all at end *)
val PMATCH_INTRO_CATCHALL = store_thm ("PMATCH_INTRO_CATCHALL",
``PMATCH v rows = PMATCH v (SNOC (PMATCH_ROW (\_0. _0) (\_0. T) (\_0. ARB)) rows)``,
SIMP_TAC std_ss [PMATCH_REMOVE_ARB]);


val PMATCH_REMOVE_ARB_NO_OVERLAP = store_thm ("PMATCH_REMOVE_ARB_NO_OVERLAP",
``!v p g r rows1 rows2.
  ((!x. (r x = ARB)) /\
   (!x. ((v = p x) /\ (g x)) ==> EVERY (\row. (row (p x) = NONE)) rows2)) ==>
  (PMATCH v (rows1 ++ ((PMATCH_ROW p g r) :: rows2)) =
   PMATCH v (rows1 ++ rows2))``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [PMATCH_INTRO_CATCHALL] THEN
SIMP_TAC list_ss [SNOC_APPEND,
  rich_listTheory.APPEND_ASSOC_CONS] THEN
MATCH_MP_TAC PMATCH_ROWS_DROP_SUBSUMED_PMATCH_ROWS THEN
ASM_SIMP_TAC std_ss [])



(***************************************************)
(* Fancy redundancy check                          *)
(***************************************************)

(* Let's first define when a row is redundant.
   The predicate PMATCH_ROW_REDUNDANT v rs i holds,
   iff row number i is redundant for input v in the
   list of rows rs. *)
val PMATCH_ROW_REDUNDANT_def = Define `
  PMATCH_ROW_REDUNDANT v rs i = (
  (i < LENGTH rs /\ (IS_SOME ((EL i rs) v) ==>
    (?j. ((j < i) /\ IS_SOME ((EL j rs) v))))))`;

val PMATCH_ROW_REDUNDANT_NIL = store_thm ("PMATCH_ROW_REDUNDANT_NIL",
  ``PMATCH_ROW_REDUNDANT v [] i = F``,
SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_def]);

val PMATCH_ROW_REDUNDANT_0 = store_thm ("PMATCH_ROW_REDUNDANT_0",
  ``PMATCH_ROW_REDUNDANT v (r::rs) 0 <=> (r v = NONE)``,
SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_def]);

Theorem PMATCH_ROW_REDUNDANT_SUC:
  !v r rs i.
     PMATCH_ROW_REDUNDANT v (r::rs) (SUC i) <=>
     (r v <> NONE /\ i < LENGTH rs) \/ PMATCH_ROW_REDUNDANT v rs i
Proof
  SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [PMATCH_ROW_REDUNDANT_def] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [
    STRIP_TAC THEN
    Cases_on `j` THENL [
      Cases_on `r v` THEN FULL_SIMP_TAC list_ss [],

      Q.RENAME1_TAC `SUC j' < SUC i` THEN STRIP_TAC THEN
      Q.EXISTS_TAC `j'` THEN
      FULL_SIMP_TAC list_ss []
    ],

    REPEAT STRIP_TAC THEN Cases_on ‘r v’ >> FULL_SIMP_TAC list_ss [] >| [
      Q.EXISTS_TAC `SUC j` THEN SRW_TAC[][],
      Q.EXISTS_TAC ‘0’ >> SRW_TAC[][]
    ]
  ]
QED


val PMATCH_ROW_REDUNDANT_APPEND_LT = store_thm ("PMATCH_ROW_REDUNDANT_APPEND_LT",
  ``!v rs1 rs2 i.
    i < LENGTH rs1 ==>
    (PMATCH_ROW_REDUNDANT v (rs1 ++ rs2) i =
     PMATCH_ROW_REDUNDANT v rs1 i)``,
SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (list_ss++boolSimps.CONJ_ss) [rich_listTheory.EL_APPEND1]);

val PMATCH_ROW_REDUNDANT_APPEND_GE = store_thm ("PMATCH_ROW_REDUNDANT_APPEND_GE",
  ``!v rs1 rs2 i.
    ~(i < LENGTH rs1) ==>
    (PMATCH_ROW_REDUNDANT v (rs1 ++ rs2) i <=> (
     (~(EVERY (\r. r v = NONE) rs1) /\
        (i < LENGTH rs1 + LENGTH rs2)) \/
     PMATCH_ROW_REDUNDANT v rs2 (i - LENGTH rs1)))``,

SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_def, MEM_EL, EXISTS_MEM, GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [arithmeticTheory.NOT_LESS, rich_listTheory.EL_APPEND2,
  quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
  Cases_on `j < LENGTH rs1` THENL [
    FULL_SIMP_TAC list_ss [rich_listTheory.EL_APPEND1] THEN
    METIS_TAC[],

    FULL_SIMP_TAC list_ss [arithmeticTheory.NOT_LESS, rich_listTheory.EL_APPEND2] THEN
    DISJ2_TAC THEN
    Q.EXISTS_TAC `j - LENGTH rs1` THEN
    FULL_SIMP_TAC arith_ss []
  ],

  Q.RENAME1_TAC `j' < LENGTH rs1` THEN
  Q.EXISTS_TAC `j'` THEN
  ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1],


  Q.EXISTS_TAC `j + LENGTH rs1` THEN
  ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2]
]);


(* We can accumulate redundancy information for all rows.
   This is done via IS_REDUNDANT_ROWS_INFO v rows c infos.
   If the n-th entry of list infos is true, then the n-th
   row of rows is redundant for input v. If it is not true,
   it may or may not be redundant.

   The parameter c is used for accumulating information
   of all rows already in the info. If none of the rows
   in rows matches, c holds. *)
val IS_REDUNDANT_ROWS_INFO_def = Define `
  IS_REDUNDANT_ROWS_INFO v rows c infos <=> (
  (LENGTH rows = LENGTH infos) /\
  (!i. i < LENGTH rows ==> EL i infos ==>
     PMATCH_ROW_REDUNDANT v rows i) /\
  (EVERY (\r. r v = NONE) rows ==> c))`


(* This setup allows to build up such an info
   row by row. We start with a list of empty rows
   and add new rows at the end using the information in c. *)
val IS_REDUNDANT_ROWS_INFO_NIL = store_thm (
  "IS_REDUNDANT_ROWS_INFO_NIL",
``!v. IS_REDUNDANT_ROWS_INFO v [] T []``,
SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def]);


val IS_REDUNDANT_ROWS_INFO_SNOC = store_thm (
  "IS_REDUNDANT_ROWS_INFO_SNOC",
``!v rows c infos r i c'.
  IS_REDUNDANT_ROWS_INFO v rows c infos ==>
  ((r v = NONE) ==> c ==> c') ==>
  (c ==> i ==> (r v = NONE)) ==>
  IS_REDUNDANT_ROWS_INFO v (SNOC r rows) c' (SNOC i infos)
``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def, SNOC_APPEND] THEN
REPEAT STRIP_TAC THEN
Cases_on `i' < LENGTH infos` THEN1 (
  FULL_SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_APPEND_LT, rich_listTheory.EL_APPEND1]
) THEN

`i' = LENGTH infos` by DECIDE_TAC THEN
Cases_on `c` THEN FULL_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, PMATCH_ROW_REDUNDANT_APPEND_GE,
  PMATCH_ROW_REDUNDANT_0]
);


(* However, we still need to specialise this for
   rows of the from PMATCH_ROW. For this case, it is handy
   to use an auxiliary definition. *)
val PMATCH_ROW_COND_EX_def = Define `PMATCH_ROW_COND_EX i p g =
?x. PMATCH_ROW_COND p g i x`


val IS_REDUNDANT_ROWS_INFO_SNOC_PMATCH_ROW = store_thm (
  "IS_REDUNDANT_ROWS_INFO_SNOC_PMATCH_ROW",
``!v rows c infos p g r c'.
  IS_REDUNDANT_ROWS_INFO v rows c infos ==>
  (~(PMATCH_ROW_COND_EX v p g) ==> (c = c')) ==>
  IS_REDUNDANT_ROWS_INFO v (SNOC (PMATCH_ROW p g r) rows) c' (SNOC (c ==> ~(PMATCH_ROW_COND_EX v p g)) infos)
``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] IS_REDUNDANT_ROWS_INFO_SNOC) THEN
Q.EXISTS_TAC `c` THEN
FULL_SIMP_TAC std_ss [PMATCH_ROW_EQ_NONE, PMATCH_ROW_COND_EX_def] THEN
METIS_TAC[])

(* A rewrite rule useful for proofs. *)
val IS_REDUNDANT_ROWS_INFO_CONS = store_thm (
  "IS_REDUNDANT_ROWS_INFO_CONS",
``
  IS_REDUNDANT_ROWS_INFO v (row::rows) c (i::infos') = (
  (LENGTH rows = LENGTH infos') /\
  (i ==> ((row v) = NONE)) /\
  ((row v = NONE) ==> IS_REDUNDANT_ROWS_INFO v rows c infos')
)``,

EQ_TAC THEN SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def] THEN
REPEAT STRIP_TAC THENL [
  Q.PAT_X_ASSUM `!i'. _` (MP_TAC o SPEC ``0``) THEN
  ASM_SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_0],

  Q.PAT_X_ASSUM `!i'. _` (MP_TAC o Q.SPEC `SUC i'`) THEN
  FULL_SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_SUC],

  sg `(i'=0) \/ (?i''. (i' = SUC i''))` THENL [
     Cases_on `i'` THEN SIMP_TAC std_ss [],
    FULL_SIMP_TAC list_ss [],
    ALL_TAC
  ] THEN
  FULL_SIMP_TAC list_ss [PMATCH_ROW_REDUNDANT_0, PMATCH_ROW_REDUNDANT_SUC] THEN
  Tactical.REVERSE (Cases_on `row v`) THEN (
    FULL_SIMP_TAC std_ss []
  )
])


(* We can use such a REDUNDANT_ROWS_INFO to prune
   the a pattern match *)

val APPLY_REDUNDANT_ROWS_INFO_def = Define `
  (APPLY_REDUNDANT_ROWS_INFO is xs = MAP SND (
    FILTER (\x. ~ (FST  x)) (ZIP (is, xs))))`

val APPLY_REDUNDANT_ROWS_INFO_THMS = store_thm (
  "APPLY_REDUNDANT_ROWS_INFO_THMS",
``(APPLY_REDUNDANT_ROWS_INFO [] [] = []) /\
  (!is x xs. (APPLY_REDUNDANT_ROWS_INFO (T::is) (x::xs) =
     (APPLY_REDUNDANT_ROWS_INFO is xs))) /\
  (!is x xs. (APPLY_REDUNDANT_ROWS_INFO (F::is) (x::xs) =
     x::(APPLY_REDUNDANT_ROWS_INFO is xs)))``,

SIMP_TAC list_ss [APPLY_REDUNDANT_ROWS_INFO_def]);


val PMATCH_ROWS_DROP_REDUNDANT_ROWS_INFO_EQUIV = store_thm ("PMATCH_ROWS_DROP_REDUNDANT_ROWS_INFO_EQUIV",
``!v c rows infos. IS_REDUNDANT_ROWS_INFO v rows c infos ==>
  (PMATCH_EQUIV_ROWS v rows (APPLY_REDUNDANT_ROWS_INFO infos rows))``,

GEN_TAC THEN
Induct_on `rows` THEN1 (
  SIMP_TAC (list_ss++QUANT_INST_ss [std_qp]) [
    IS_REDUNDANT_ROWS_INFO_def,
    APPLY_REDUNDANT_ROWS_INFO_def,
    PMATCH_EQUIV_ROWS_is_equiv_1]
) THEN
CONV_TAC (RENAME_VARS_CONV ["row"]) THEN
REPEAT STRIP_TAC THEN
`?i infos'. infos = i::infos'` by (
  Cases_on `infos` THEN
  FULL_SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def]
) THEN
FULL_SIMP_TAC std_ss [IS_REDUNDANT_ROWS_INFO_CONS] THEN
Q.PAT_X_ASSUM `!c infos. _` (MP_TAC o Q.SPECL [`c`, `infos'`]) THEN
Cases_on `i` THENL [
  FULL_SIMP_TAC std_ss [APPLY_REDUNDANT_ROWS_INFO_THMS,
    PMATCH_EQUIV_ROWS_CONS_NONE],

  Cases_on `row v` THEN (
    FULL_SIMP_TAC std_ss [APPLY_REDUNDANT_ROWS_INFO_THMS,
      PMATCH_EQUIV_ROWS_CONS_NONE, PMATCH_EQUIV_ROWS_EQUIV_EXPAND]
  ) THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC list_ss [PMATCH_EQUIV_ROWS_def,
    GSYM PMATCH_EQUIV_ROWS_EQUIV_EXPAND, RIGHT_AND_OVER_OR,
    EXISTS_OR_THM, PMATCH_def]
])

val REDUNDANT_ROWS_INFO_TO_PMATCH_EQ = store_thm ("REDUNDANT_ROWS_INFO_TO_PMATCH_EQ",
``!v c rows infos. IS_REDUNDANT_ROWS_INFO v rows c infos ==>
  (PMATCH v rows =
   PMATCH v (APPLY_REDUNDANT_ROWS_INFO infos rows))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC PMATCH_EQUIV_ROWS_MATCH THEN
MATCH_MP_TAC PMATCH_ROWS_DROP_REDUNDANT_ROWS_INFO_EQUIV THEN
PROVE_TAC[])


(* We get exhautiveness information for free using
   the accumulated information in c *)
val PMATCH_IS_EXHAUSTIVE_def = Define `
   PMATCH_IS_EXHAUSTIVE v rs = (
   EXISTS (\r. IS_SOME (r v)) rs)`


val PMATCH_IS_EXHAUSTIVE_REWRITES = store_thm ("PMATCH_IS_EXHAUSTIVE_REWRITES", ``
   (!v. (PMATCH_IS_EXHAUSTIVE v [] = F)) /\

   (!v r rs. (PMATCH_IS_EXHAUSTIVE v (r::rs) =
     ~(r v = NONE) \/ PMATCH_IS_EXHAUSTIVE v rs))``,

SIMP_TAC list_ss [PMATCH_IS_EXHAUSTIVE_def,
quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])


val IS_REDUNDANT_ROWS_INFO_EXTRACT_IS_EXHAUSTIVE =
  store_thm ("IS_REDUNDANT_ROWS_INFO_EXTRACT_IS_EXHAUSTIVE",
  ``!v rows c infos.
    IS_REDUNDANT_ROWS_INFO v rows c infos ==>
    ~c ==> PMATCH_IS_EXHAUSTIVE v rows``,

SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def,
  PMATCH_IS_EXHAUSTIVE_def, combinTheory.o_DEF,
  quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE
])


(* One can easily mark rows as not redundant without proof.
   This is handy for avoiding complicated procedures to check,
   whether some element of infos is true or false. If in doub
   replace it with false. Technically this is done by
   building a pairwise conjunction with a given list.  *)
val REDUNDANT_ROWS_INFOS_CONJ_def = Define `
  REDUNDANT_ROWS_INFOS_CONJ ip1 ip2 =
     (MAP2 (\i1 i2. i1 /\ i2) ip1 ip2)`;

val REDUNDANT_ROWS_INFOS_CONJ_REWRITE = store_thm (
  "REDUNDANT_ROWS_INFOS_CONJ_REWRITE",
``(REDUNDANT_ROWS_INFOS_CONJ [] [] = []) /\
  (REDUNDANT_ROWS_INFOS_CONJ (i1 :: is1) (i2::is2) =
  (i1 /\ i2) :: (REDUNDANT_ROWS_INFOS_CONJ is1 is2))``,
SIMP_TAC list_ss [REDUNDANT_ROWS_INFOS_CONJ_def])

(* So, we can weaken an existing REDUNDANT_ROWS_INFOS *)
val REDUNDANT_ROWS_INFOS_CONJ_THM = store_thm ("REDUNDANT_ROWS_INFOS_CONJ_THM",
``!v rows c infos c' infos'.
    IS_REDUNDANT_ROWS_INFO v rows c infos ==>
    (LENGTH infos' = LENGTH infos) ==>
    IS_REDUNDANT_ROWS_INFO v rows (c \/ c') (REDUNDANT_ROWS_INFOS_CONJ infos infos')``,

SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def,
  REDUNDANT_ROWS_INFOS_CONJ_def, MAP2_MAP, EL_MAP, EL_ZIP])


(* Strengthening requires proof though *)
val REDUNDANT_ROWS_INFOS_DISJ_def = Define `
  REDUNDANT_ROWS_INFOS_DISJ ip1 ip2 =
     (MAP2 (\i1 i2. i1 \/ i2) ip1 ip2)`;

val REDUNDANT_ROWS_INFOS_DISJ_THM = store_thm ("REDUNDANT_ROWS_INFOS_DISJ_THM",
``!v rows c infos c' infos'.
    IS_REDUNDANT_ROWS_INFO v rows c infos ==>
    IS_REDUNDANT_ROWS_INFO v rows c' infos' ==>
    IS_REDUNDANT_ROWS_INFO v rows (c /\ c') (REDUNDANT_ROWS_INFOS_DISJ infos infos')``,

SIMP_TAC list_ss [IS_REDUNDANT_ROWS_INFO_def,
  REDUNDANT_ROWS_INFOS_DISJ_def, MAP2_MAP, EL_MAP, EL_ZIP] THEN
METIS_TAC[])


(* One can use the always correct, but usually much too complicated
   strongest redundant_rows_info for strengthening *)

val STRONGEST_REDUNDANT_ROWS_INFO_AUX_def = Define `
  (STRONGEST_REDUNDANT_ROWS_INFO_AUX v [] p infos = (p, infos)) /\
  (STRONGEST_REDUNDANT_ROWS_INFO_AUX v (r::rows) p infos =
   STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows (p /\ (r v = NONE))
   (SNOC (p ==> (r v = NONE)) infos))`

val STRONGEST_REDUNDANT_ROWS_INFO_def = Define `
  STRONGEST_REDUNDANT_ROWS_INFO v rows =
  SND (STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows T [])`

val LENGTH_STRONGEST_REDUNDANT_ROWS_INFO_AUX = store_thm (
  "LENGTH_STRONGEST_REDUNDANT_ROWS_INFO_AUX",
  ``!v rows p infos.
      LENGTH (SND (STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows p infos)) =
      (LENGTH rows + LENGTH infos)``,

Induct_on `rows` THEN (
  ASM_SIMP_TAC list_ss [STRONGEST_REDUNDANT_ROWS_INFO_AUX_def]
))

val FST_STRONGEST_REDUNDANT_ROWS_INFO_AUX = store_thm (
  "FST_STRONGEST_REDUNDANT_ROWS_INFO_AUX",
  ``!v rows p infos.
      FST (STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows p infos) =
      (p /\ EVERY (\r. r v = NONE) rows)``,

Induct_on `rows` THEN (
  ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [STRONGEST_REDUNDANT_ROWS_INFO_AUX_def]
))



val EL1_STRONGEST_REDUNDANT_ROWS_INFO_AUX = store_thm (
  "EL1_STRONGEST_REDUNDANT_ROWS_INFO_AUX",
  ``!v rows p infos i.
      (i < LENGTH infos) ==>
      (EL i (SND (STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows p infos)) =
       EL i infos)``,

Induct_on `rows` THEN (
  ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [STRONGEST_REDUNDANT_ROWS_INFO_AUX_def, SNOC_APPEND, rich_listTheory.EL_APPEND1]
))


val EL2_STRONGEST_REDUNDANT_ROWS_INFO_AUX = store_thm (
  "EL2_STRONGEST_REDUNDANT_ROWS_INFO_AUX",
  ``!v rows p infos i.
      (i >= LENGTH infos /\ i < LENGTH rows + LENGTH infos) ==>
      (EL i (SND (STRONGEST_REDUNDANT_ROWS_INFO_AUX v rows p infos)) =
       ((p /\ EVERY (\r. r v = NONE) (TAKE (i - LENGTH infos) rows)) ==> ((EL (i - LENGTH infos) rows) v = NONE)))``,

GEN_TAC THEN
Induct_on `rows` THEN1 (
  SIMP_TAC list_ss []
) THEN
SIMP_TAC list_ss [STRONGEST_REDUNDANT_ROWS_INFO_AUX_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `i = LENGTH infos` THEN1 (
  ASM_SIMP_TAC list_ss [SNOC_APPEND, EL1_STRONGEST_REDUNDANT_ROWS_INFO_AUX, rich_listTheory.EL_APPEND2]
) THEN
Q.PAT_X_ASSUM `!p infos. _` (MP_TAC o Q.SPECL [
  `p /\ (h (v:'a) = NONE)`, `SNOC (p ==> (h (v:'a) = NONE)) infos`, `i`]) THEN
ASM_SIMP_TAC list_ss [SNOC_APPEND, GSYM arithmeticTheory.ADD1] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
`(i - LENGTH infos) = SUC (i - SUC (LENGTH infos))` by DECIDE_TAC THEN
ASM_SIMP_TAC list_ss [])


val LENGTH_STRONGEST_REDUNDANT_ROWS_INFO = store_thm (
  "LENGTH_STRONGEST_REDUNDANT_ROWS_INFO",
  ``LENGTH (STRONGEST_REDUNDANT_ROWS_INFO v rows) = LENGTH rows``,

SIMP_TAC list_ss [STRONGEST_REDUNDANT_ROWS_INFO_def,
  LENGTH_STRONGEST_REDUNDANT_ROWS_INFO_AUX])

val EL_STRONGEST_REDUNDANT_ROWS_INFO = store_thm (
  "EL_STRONGEST_REDUNDANT_ROWS_INFO",
  ``!v rows i.
      (i < LENGTH rows) ==>
      (EL i (STRONGEST_REDUNDANT_ROWS_INFO v rows) =
       ((EVERY (\r. r v = NONE) (TAKE i rows)) ==>
        ((EL i rows) v = NONE)))``,

SIMP_TAC list_ss [STRONGEST_REDUNDANT_ROWS_INFO_def,
  EL2_STRONGEST_REDUNDANT_ROWS_INFO_AUX])


val STRONGEST_REDUNDANT_ROWS_INFO_OK = store_thm ("STRONGEST_REDUNDANT_ROWS_INFO_OK",

  ``IS_REDUNDANT_ROWS_INFO v rows (EVERY (\r. r v = NONE) rows)
      (STRONGEST_REDUNDANT_ROWS_INFO v rows)``,

SIMP_TAC std_ss [IS_REDUNDANT_ROWS_INFO_def,
  EL_STRONGEST_REDUNDANT_ROWS_INFO,
  LENGTH_STRONGEST_REDUNDANT_ROWS_INFO,
  PMATCH_ROW_REDUNDANT_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `EL i rows v` THEN1 (
  FULL_SIMP_TAC list_ss []
) THEN
FULL_SIMP_TAC list_ss [EXISTS_MEM] THEN
`?j. j < i /\ (EL j rows = e)` suffices_by (
  STRIP_TAC THEN Q.EXISTS_TAC `j` THEN
  ASM_SIMP_TAC std_ss [] THEN
  Cases_on `e v` THEN FULL_SIMP_TAC std_ss []
) THEN
Q.PAT_X_ASSUM `MEM e _` MP_TAC THEN
ASM_SIMP_TAC (list_ss++boolSimps.CONJ_ss) [MEM_EL,rich_listTheory.EL_TAKE] THEN
PROVE_TAC[])


(* IN order to automate this procedure, we need a few
   simple, additional lemmata  *)

val PMATCH_ROW_COND_EX_FULL_DEF = store_thm ("PMATCH_ROW_COND_EX_FULL_DEF",
 ``PMATCH_ROW_COND_EX i p g =
   ?x. (i = p x) /\ g x``,
SIMP_TAC std_ss [PMATCH_ROW_COND_EX_def, PMATCH_ROW_COND_def] THEN
METIS_TAC[])

val PMATCH_ROW_COND_EX_WEAKEN = store_thm ("PMATCH_ROW_COND_EX_WEAKEN",
``!f v p g p' g'.

  ~(PMATCH_ROW_COND_EX v p g) ==>
  (!x. p' x = p (f x)) ==>
  (PMATCH_ROW_COND_EX v p' g' =
   PMATCH_ROW_COND_EX v p' (\x. g' x /\ ~(g (f x))))``,

SIMP_TAC std_ss [PMATCH_ROW_COND_EX_def, PMATCH_ROW_COND_def] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] THEN
METIS_TAC[]);

val PMATCH_ROW_COND_EX_FALSE = store_thm ("PMATCH_ROW_COND_EX_FALSE",
``!v p g.
  (!x. ~(g x)) ==>
  (PMATCH_ROW_COND_EX v p g = F)``,

SIMP_TAC std_ss [PMATCH_ROW_COND_EX_def, PMATCH_ROW_COND_def])

val PMATCH_ROW_COND_EX_IMP_REWRITE = store_thm ("PMATCH_ROW_COND_EX_IMP_REWRITE",
``!v p g p' g' RES.
  PMATCH_ROW_COND_EX v p g ==>
  (!x. g x ==> ((?x'. (p' x' = p x) /\ g' x') = RES)) ==>
  (PMATCH_ROW_COND_EX v p' g' = RES)``,

SIMP_TAC std_ss [PMATCH_ROW_COND_EX_def, PMATCH_ROW_COND_def,
  GSYM LEFT_FORALL_IMP_THM]);

(* Use this simple contradiction to bring
   PMATCH_IS_EXHAUSTIVE in the form we need for
   automation *)
val PMATCH_IS_EXHAUSTIVE_CONTRADICT = store_thm (
  "PMATCH_IS_EXHAUSTIVE_CONTRADICT",
``!v rs.
  (EVERY (\r. r v = NONE) rs ==> F) ==>
  (PMATCH_IS_EXHAUSTIVE v rs)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [PMATCH_IS_EXHAUSTIVE_def,
  combinTheory.o_DEF, quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])


val PMATCH_ROW_EVAL_COND_EX = store_thm ("PMATCH_ROW_EVAL_COND_EX",
  ``PMATCH_ROW_COND_EX i p g ==>
    ((PMATCH_ROW p g r i) = SOME (r (@x. PMATCH_ROW_COND p g i x)))``,

SIMP_TAC std_ss [PMATCH_ROW_def, some_def, PMATCH_ROW_COND_EX_def])

val PMATCH_ROW_NEQ_NONE = store_thm ("PMATCH_ROW_NEQ_NONE",
  ``(PMATCH_ROW p g r i <> NONE) <=>
    (PMATCH_ROW_COND_EX i p g)``,

SIMP_TAC std_ss [PMATCH_ROW_def, some_eq_NONE,
  PMATCH_ROW_COND_EX_def]);


(***************************************************)
(* ELIMINATE DOUBLE VAR-BINDS                      *)
(***************************************************)

(* If a variable is used multiple times in a pattern,
   we can via the following theorem introduce a fresh variable
   and add the connection between the old and the newly created
   var to the guard. *)
val PMATCH_ROW_REMOVE_DOUBLE_BINDS_THM =
  store_thm ("PMATCH_ROW_REMOVE_DOUBLE_BINDS_THM",
``!g p1 g1 r1 p2 g2 r2.
   ((!x y. (p1 x = p1 y) ==> (x = y)) /\
   (!x. (p2 (g x) = p1 x)) /\
   (!x'. g2 x' = (?x. (x' = g x) /\ g1 x)) /\
   (!x. r2 (g x) = r1 x)) ==>

  (PMATCH_ROW p1 g1 r1 = PMATCH_ROW p2 g2 r2)``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [PMATCH_ROW_def, FUN_EQ_THM,
  optionTheory.some_def, PMATCH_ROW_COND_def,
  GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `?x'. (p1 x' = x) /\ g1 x'` THEN (
  ASM_REWRITE_TAC[optionTheory.OPTION_MAP_DEF]
) THEN
SELECT_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
SELECT_ELIM_TAC THEN
REPEAT STRIP_TAC THEN (
  METIS_TAC[]
))



(***************************************************)
(* ELIMINATE GUARDS                                *)
(***************************************************)

(* We can eliminate guards by replacing them with true
   and add the guard in form of a conditional.
   Notice that all the rows after the guard are
   duplicated. We heavily rely on simplification
   of PMATCH to avoid a huge blowup of term-size,
   when applying the following rule. *)
val GUARDS_ELIM_THM = store_thm ("GUARDS_ELIM_THM",
``!v rs1 rs2 p g r.
  (!x1 x2. (p x1 = p x2) ==> (x1 = x2)) ==> (
  PMATCH v (rs1++(PMATCH_ROW p g r)::rs2) =
  PMATCH v (rs1++(PMATCH_ROW p (\x. T) (\x.
   if g x then r x else
   PMATCH (p x) rs2))::rs2))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_APPEND_SEM] THEN
Cases_on `?r. MEM r rs1 /\ IS_SOME (r v)` THEN (
  ASM_REWRITE_TAC[]
) THEN
SIMP_TAC std_ss [PMATCH_EVAL, PMATCH_ROW_COND_def] THEN
Tactical.REVERSE (Cases_on `?x. p x = v`) THEN (
  FULL_SIMP_TAC std_ss []
) THEN
`!x'. (p x' = v) <=> (x' = x)` by METIS_TAC[] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) []);



(***************************************************)
(* THEOREMS ABOUT FLATTENING                       *)
(***************************************************)

(* The content of this section is still experimental.
   It is likely to chnage quite a bit still. *)
val PMATCH_FLATTEN_FUN_def = Define `
  PMATCH_FLATTEN_FUN p g row v = (
    option_CASE (some x. PMATCH_ROW_COND p g v x)
      NONE (\x. row x x))`;


val PMATCH_FLATTEN_THM_AUX = prove (
 ``(PMATCH v [PMATCH_ROW p g (\x. (PMATCH x (MAP (\r. r x) rows')))]) =
   (PMATCH v (MAP (\r. (PMATCH_FLATTEN_FUN p g r)) rows'))``,

REPEAT GEN_TAC THEN
Induct_on `rows'` THEN1 (
  Cases_on `some x. PMATCH_ROW_COND p g v x` THEN
  ASM_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def]
) THEN

Q.PAT_X_ASSUM `_ = _` (ASSUME_TAC o GSYM) THEN
FULL_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def] THEN
Q.PAT_X_ASSUM `_ = _` (K ALL_TAC) THEN

Cases_on `some x. PMATCH_ROW_COND p g v x` THEN (
  ASM_SIMP_TAC std_ss [PMATCH_FLATTEN_FUN_def]
));


val PMATCH_FLATTEN_THM_SINGLE = store_thm ("PMATCH_FLATTEN_THM_SINGLE",
 ``!v p g rows.
 (!x. PMATCH_IS_EXHAUSTIVE x (MAP (\r. r x) rows)) ==>
PMATCH_EQUIV_ROWS v [PMATCH_ROW p g (\x. (PMATCH x (MAP (\r. r x) rows)))] (MAP (\r. (PMATCH_FLATTEN_FUN p g r)) rows)``,

REPEAT STRIP_TAC THEN
SIMP_TAC list_ss [PMATCH_EQUIV_ROWS_def, PMATCH_FLATTEN_THM_AUX] THEN
SIMP_TAC list_ss [PMATCH_ROW_def, IS_SOME_OPTION_MAP, some_IS_SOME,
  listTheory.MEM_MAP, GSYM LEFT_EXISTS_AND_THM] THEN

SIMP_TAC std_ss [PMATCH_FLATTEN_FUN_def, some_def] THEN
Cases_on `?x. PMATCH_ROW_COND p g v x` THEN (
  ASM_SIMP_TAC std_ss [PMATCH_ROW_COND_def]
) THEN
FULL_SIMP_TAC std_ss [PMATCH_IS_EXHAUSTIVE_def,
  listTheory.EXISTS_MEM, listTheory.MEM_MAP,
  GSYM LEFT_EXISTS_AND_THM])


val PMATCH_FLATTEN_THM = store_thm ("PMATCH_FLATTEN_THM",
 ``!v p g rows1 rows2 rows.
 (!x. PMATCH_IS_EXHAUSTIVE x (MAP (\r. r x) rows)) ==>
(PMATCH v (rows1 ++ (PMATCH_ROW p g (\x. (PMATCH x (MAP (\r. r x) rows))))::rows2) =
 PMATCH v (rows1 ++ (MAP (\r. (PMATCH_FLATTEN_FUN p g r)) rows) ++ rows2))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC PMATCH_EQUIV_ROWS_MATCH THEN
REWRITE_TAC[GSYM APPEND_ASSOC] THEN
MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] PMATCH_EQUIV_APPEND) THEN
REWRITE_TAC[PMATCH_EQUIV_ROWS_is_equiv_1] THEN
ONCE_REWRITE_TAC [prove (``x::xs = [x] ++ xs``, SIMP_TAC list_ss [])] THEN
MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] PMATCH_EQUIV_APPEND) THEN
REWRITE_TAC[PMATCH_EQUIV_ROWS_is_equiv_1] THEN
MATCH_MP_TAC PMATCH_FLATTEN_THM_SINGLE THEN
ASM_REWRITE_TAC[]);


val PMATCH_FLATTEN_FUN_PMATCH_ROW = store_thm ("PMATCH_FLATTEN_FUN_PMATCH_ROW",
``!p.
  (!x1 x2. (p x1 = p x2) ==> (x1 = x2)) ==> (

  !g p' g' r'.
  PMATCH_FLATTEN_FUN p g (\x. PMATCH_ROW p' (g' x) (r' x)) =
  PMATCH_ROW (\x. (p (p' x))) (\x. (g (p' x)) /\ (g' (p' x) x)) (\x. r' (p' x) x))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_FLATTEN_FUN_def, FUN_EQ_THM, PMATCH_ROW_def] THEN
CONV_TAC (RENAME_VARS_CONV ["v"]) THEN GEN_TAC THEN
Cases_on ` some x. PMATCH_ROW_COND p g v x` THEN1 (
  FULL_SIMP_TAC list_ss [some_eq_NONE, PMATCH_ROW_COND_def] THEN
  PROVE_TAC[]
) THEN

ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [PMATCH_ROW_COND_def] THEN
Q.PAT_X_ASSUM `_ = SOME x` (fn thm =>
  ASSUME_TAC (HO_MATCH_MP some_eq_SOME thm)) THEN
`!x'. (p x' = v) = (x' = x)` by PROVE_TAC[] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
Cases_on `(some x'. (p' x' = x) /\ g' x x')` THEN (
  ASM_SIMP_TAC std_ss []
) THEN
Q.PAT_X_ASSUM `_ = SOME x'` (fn thm =>
  ASSUME_TAC (HO_MATCH_MP some_eq_SOME thm)) THEN
ASM_SIMP_TAC std_ss [])





(***************************************************)
(* UNROLLING PREDICATES                            *)
(***************************************************)

val PMATCH_ROW_COND_NOT_EX_OR_EQ_def = Define `PMATCH_ROW_COND_NOT_EX_OR_EQ (i:'a) (r : 'a -> 'b option) rows =
(~(r i <> NONE) \/ ((EXISTS (\row. row i <> NONE) rows) /\
     (THE (r i) = PMATCH i rows)))`

val PMATCH_ROW_COND_NOT_EX_OR_EQ_FIRST_ROW = store_thm ("PMATCH_ROW_COND_NOT_EX_OR_EQ_FIRST_ROW",
  ``!i r r' rows.

    (r' i <> NONE) ==>
    ((PMATCH_ROW_COND_NOT_EX_OR_EQ i r (r'::rows)) =
    ((r i <> NONE) ==>
      (r i = r' i)))``,

SIMP_TAC list_ss [PMATCH_ROW_COND_NOT_EX_OR_EQ_def, PMATCH_def] THEN
REPEAT GEN_TAC THEN
Cases_on `r' i` THEN Cases_on `r i` THEN (
  SIMP_TAC std_ss []
))


val PMATCH_ROW_COND_NOT_EX_OR_EQ_NIL = store_thm ("PMATCH_ROW_COND_NOT_EX_OR_EQ_NIL",
  ``PMATCH_ROW_COND_NOT_EX_OR_EQ i r [] =
    ((r i <> NONE) ==> F)``,

SIMP_TAC list_ss [PMATCH_ROW_COND_NOT_EX_OR_EQ_def]);


val PMATCH_ROW_COND_NOT_EX_OR_EQ_NOT_FIRST_ROW = store_thm ("PMATCH_ROW_COND_NOT_EX_OR_EQ_NOT_FIRST_ROW",
  ``PMATCH_ROW_COND_NOT_EX_OR_EQ i r' rows ==>
    (PMATCH_ROW_COND_NOT_EX_OR_EQ i r (r'::rows) =
    (PMATCH_ROW_COND_NOT_EX_OR_EQ i r rows))``,

SIMP_TAC list_ss [PMATCH_ROW_COND_NOT_EX_OR_EQ_def, PMATCH_def] THEN
Cases_on `r i` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `r' i` THEN ASM_SIMP_TAC std_ss []
);

val PMATCH_PRED_UNROLL_NIL = store_thm ("PMATCH_PRED_UNROLL_NIL",
  ``!P v. P (PMATCH v []) = P ARB``,
  SIMP_TAC std_ss [PMATCH_def, PMATCH_INCOMPLETE_def]);


val PMATCH_PRED_UNROLL_CONS = store_thm ("PMATCH_PRED_UNROLL_CONS",
``!P v r rows.
     P (PMATCH v (r::rows)) <=> (
       ((r v <> NONE) ==> P (THE (r v))) /\
       ((PMATCH_ROW_COND_NOT_EX_OR_EQ v r rows) ==>
         P (PMATCH v rows)))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_def, PMATCH_ROW_def, some_def,
  PMATCH_ROW_COND_NOT_EX_OR_EQ_def,
  PMATCH_ROW_COND_EX_def] THEN
Cases_on `r v` THEN ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);


val PMATCH_EXPAND_PRED_def = Define `(PMATCH_EXPAND_PRED P v rows_before [] = (~(PMATCH_IS_EXHAUSTIVE v (REVERSE rows_before)) ==> P ARB)) /\

  (PMATCH_EXPAND_PRED P v rows_before (r::rows_after) = (
  ((r v <> NONE) ==> (EVERY (\r'. (r' v <> NONE) ==> (r' v = r v)) rows_before)
  ==> P (THE (r v))) /\ PMATCH_EXPAND_PRED P v (r::rows_before) rows_after))`;


val PMATCH_EXPAND_PRED_THM_GEN = store_thm ("PMATCH_EXPAND_PRED_THM_GEN",
``!P v rows_before rows_after.
         PMATCH_EXPAND_PRED P v rows_before rows_after <=> (
         EVERY (\r. PMATCH_ROW_COND_NOT_EX_OR_EQ v r rows_after ) rows_before ==>
         P (PMATCH v rows_after))``,

Induct_on `rows_after` THEN1 (
  SIMP_TAC list_ss [PMATCH_EXPAND_PRED_def, PMATCH_IS_EXHAUSTIVE_def, PMATCH_def, PMATCH_INCOMPLETE_def, PMATCH_ROW_COND_NOT_EX_OR_EQ_NIL, combinTheory.o_DEF, rich_listTheory.EVERY_REVERSE]
) THEN

ASM_SIMP_TAC list_ss [PMATCH_EXPAND_PRED_def, PMATCH_IS_EXHAUSTIVE_def, PMATCH_PRED_UNROLL_CONS] THEN
POP_ASSUM (K ALL_TAC) THEN
REPEAT GEN_TAC THEN
Q.RENAME1_TAC `P (THE (r v))` THEN
Cases_on `r v` THENL [
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [EVERY_MEM] THEN
  REPEAT STRIP_TAC THEN
  METIS_TAC[PMATCH_ROW_COND_NOT_EX_OR_EQ_NOT_FIRST_ROW],


  Q.RENAME1_TAC `r v = SOME x` THEN
  ASM_SIMP_TAC std_ss [PMATCH_ROW_COND_NOT_EX_OR_EQ_FIRST_ROW] THEN

  Cases_on `PMATCH_ROW_COND_NOT_EX_OR_EQ v r rows_after` THEN (
    ASM_SIMP_TAC std_ss []
  ) THEN
  Cases_on `EVERY (\r'. r' v <> NONE ==> (r' v = SOME x)) rows_before` THENL [
    FULL_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [EVERY_MEM, PMATCH_ROW_COND_NOT_EX_OR_EQ_def] THEN
    METIS_TAC[],


    ASM_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [EVERY_MEM, PMATCH_ROW_COND_NOT_EX_OR_EQ_def] THEN1 (FULL_SIMP_TAC std_ss []) THEN

    STRIP_TAC THEN
    POP_ASSUM (MP_TAC o Q.SPEC `r'`) THEN
    Q.PAT_X_ASSUM `THE (r v) = _` (ASSUME_TAC o GSYM) THEN
    ASM_SIMP_TAC std_ss [] THEN
    Cases_on `r' v` THEN FULL_SIMP_TAC std_ss []
  ]
]);


val PMATCH_EXPAND_PRED_THM = store_thm ("PMATCH_EXPAND_PRED_THM",
``!P v rows.
         P (PMATCH v rows) <=>
         PMATCH_EXPAND_PRED P v [] rows``,

SIMP_TAC list_ss [PMATCH_EXPAND_PRED_THM_GEN]);


val PMATCH_ROW_LIFT_def = Define `PMATCH_ROW_LIFT f r = \x. OPTION_MAP f (r x)`

val PMATCH_LIFT_THM = store_thm ("PMATCH_LIFT_THM",
``!f v rows.
    PMATCH_IS_EXHAUSTIVE v rows ==>
    (f (PMATCH v rows) =
     PMATCH v (MAP (PMATCH_ROW_LIFT f) rows))``,

GEN_TAC THEN GEN_TAC THEN
Induct_on `rows` THEN (
  FULL_SIMP_TAC list_ss [PMATCH_def, PMATCH_IS_EXHAUSTIVE_def]
) THEN
CONV_TAC (RENAME_VARS_CONV ["r"]) THEN
GEN_TAC THEN
Cases_on `r v` THEN (
  ASM_SIMP_TAC std_ss [PMATCH_ROW_LIFT_def]
));


val PMATCH_ROW_LIFT_THM = store_thm ("PMATCH_ROW_LIFT_THM",
  ``!f p g r.
    PMATCH_ROW_LIFT f (PMATCH_ROW p g r) =
    PMATCH_ROW p g (\x. f (r x))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_ROW_LIFT_def, PMATCH_ROW_def, FUN_EQ_THM] THEN
Cases_on `some v. PMATCH_ROW_COND p g x v` THEN (
  ASM_SIMP_TAC std_ss []
));


val PMATCH_IS_EXHAUSTIVE_LIFT = store_thm ("PMATCH_IS_EXHAUSTIVE_LIFT",
  ``!f v rows.
    PMATCH_IS_EXHAUSTIVE v rows ==>
    PMATCH_IS_EXHAUSTIVE v (MAP (PMATCH_ROW_LIFT f) rows)``,

SIMP_TAC list_ss [PMATCH_IS_EXHAUSTIVE_def, EXISTS_MAP, PMATCH_ROW_LIFT_def,
  IS_SOME_MAP]);


val _ = export_theory();
