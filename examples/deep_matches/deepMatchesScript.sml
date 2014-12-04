open HolKernel Parse boolLib bossLib;
open quantHeuristicsLib

val _ = new_theory "deepMatches"

(***************************************************)
(* Main Definitions                                *)
(***************************************************)

(* rows of a pattern match are pairs of a pattern to match 
   against p and a result r. The result and pattern are linked
   with free variables [v] bound in both. So it looks like
   (\v. (p v, r v)) *)
val PMATCH_ROW_def = Define `PMATCH_ROW row i =
  (if ?x. FST (row x) = i then
   SOME (SND (row (@x. FST (row x) = i)))
   else NONE)`

(* We defined semantics or single rows. Let's extend  
   it to multiple ones, i.e. full pattern matches now *)
val PMATCH_INCOMPLETE_def = Define `PMATCH_INCOMPLETE = ARB`
val PMATCH_def = Define `
  (PMATCH v [] = PMATCH_INCOMPLETE) /\
  (PMATCH v (r::rs) = option_CASE (r v) (PMATCH v rs) I)`


val PMATCH_IS_EXHAUSTIVE_def = Define `
   PMATCH_IS_EXHAUSTIVE rs = (
   !v. EXISTS (\r. IS_SOME (r v)) rs)`

val PMATCH_ROW_REDUNDANT_def = Define `
  PMATCH_ROW_REDUNDANT rs i = (
  (i < LENGTH rs /\ (!v. ?j. ((j < i) /\
   (IS_SOME ((EL i rs) v) ==>
    IS_SOME ((EL j rs) v))))))`

val PMATCH_REDUNDANT_ROWS_def = Define `
  PMATCH_REDUNDANT_ROWS rs = {i | (PMATCH_ROW_REDUNDANT rs i)}`


(***************************************************)
(* Rewrites                                        *)
(***************************************************)

val PMATCH_ROW_EQ_AUX = store_thm ("PMATCH_ROW_EQ_AUX",
  ``((!i. (?x. (g x = i)) = (?x'. (g' x' = i))) /\
     (!x x'. (g x = g' x') ==> (f x = f' x'))) ==>
    (PMATCH_ROW (\x:'a. (g x, f x)) = 
     PMATCH_ROW (\x':'b. (g' x', f' x')))``,
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_ROW_def, FUN_EQ_THM] THEN
CONV_TAC (RENAME_VARS_CONV ["i"]) THEN
GEN_TAC THEN
Q.PAT_ASSUM `!i. (_ = _)` (fn thm => ASSUME_TAC (Q.SPEC `i` thm))  THEN
Cases_on `?x'. g' x' = i` THEN (
  ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
SELECT_ELIM_TAC THEN
REPEAT STRIP_TAC THEN1 PROVE_TAC[] THEN
SELECT_ELIM_TAC THEN
REPEAT STRIP_TAC THEN1 PROVE_TAC[] THEN
PROVE_TAC[])

val PMATCH_ROW_EQ_NONE = store_thm ("PMATCH_ROW_EQ_NONE",
  ``(PMATCH_ROW (\x. (g x, f x)) v = NONE) <=>
    (!x. ~(g x = v))``,
SIMP_TAC std_ss [PMATCH_ROW_def]);

val PMATCH_EVAL = store_thm ("PMATCH_EVAL",
 ``(PMATCH v [] = PMATCH_INCOMPLETE) /\
   (PMATCH v ((PMATCH_ROW (\x. (g x, f x))) :: rs) =
      if (?x. (g x = v)) then 
         (f (@x. g x = v)) else PMATCH v rs)``,

SIMP_TAC std_ss [PMATCH_def] THEN
Cases_on `PMATCH_ROW (\x. (g x,f x)) v` THEN (
  FULL_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
  METIS_TAC[]
))

val PMATCH_EVAL_MATCH = store_thm ("PMATCH_EVAL_MATCH",
 ``~(PMATCH_ROW (\x. (g x, f x)) v = NONE) ==>
   (PMATCH v ((PMATCH_ROW (\x. (g x, f x))) :: rs) =
      (f (@x. g x = v)))``,

SIMP_TAC std_ss [PMATCH_def] THEN
Cases_on `PMATCH_ROW (\x. (g x,f x)) v` THEN (
  FULL_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
  METIS_TAC[]
))


(***************************************************)
(* Changing rows and removing redundant ones       *)
(***************************************************)

(* An easy way is to start with an empty set of rows 
   and then step by step add rows to either one or both
   sides till the desired correspondance is shown. This
   is achieved by the following theorems. *)
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
(* Equivalent sets of rows                         *)
(***************************************************)

val PMATCH_EQUIV_ROWS_def = Define `
 PMATCH_EQUIV_ROWS v rows1 rows2 = (
 (PMATCH v rows1 = PMATCH v rows2) /\
 ((?r. MEM r rows1 /\ IS_SOME (r v)) =
  (?r. MEM r rows2 /\ IS_SOME (r v))))`

val PMATCH_EQUIV_ROWS_is_equiv_1 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_1",
  ``(!rows. (PMATCH_EQUIV_ROWS v rows rows))``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def])

    
val PMATCH_EQUIV_ROWS_is_equiv_2 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_2",
  ``(!rows1 rows2. ((PMATCH_EQUIV_ROWS v rows1 rows2) =
                    (PMATCH_EQUIV_ROWS v rows2 rows1)))``,
SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def] THEN METIS_TAC[])

val PMATCH_EQUIV_ROWS_is_equiv_3 = store_thm ("PMATCH_EQUIV_ROWS_is_equiv_3",
  ``(!rows1 rows2 rows3. 
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

val PMATCH_APPEND = store_thm ("PMATCH_EXTEND_APPEND",
``!v rows1a rows1b rows2a rows2b.   
  (PMATCH_EQUIV_ROWS v rows1a rows1b) ==> 
  (PMATCH_EQUIV_ROWS v rows2a rows2b) ==> 
  (PMATCH_EQUIV_ROWS v (rows1a ++ rows2a) (rows1b ++ rows2b))``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [PMATCH_EQUIV_ROWS_def, RIGHT_AND_OVER_OR, 
  EXISTS_OR_THM, PMATCH_APPEND_SEM])


(* If we have a row that matches, everything after it can be dropped *)
val PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS_EQUIV = store_thm ("PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS_EQUIV",
``!v rows n. ((n < LENGTH rows) /\ (IS_SOME ((EL n rows) v))) ==>
  (PMATCH_EQUIV_ROWS v rows (TAKE (SUC n) rows))``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (`PMATCH_EQUIV_ROWS v (TAKE (SUC n) rows ++ DROP (SUC n) rows) (TAKE (SUC n) rows)` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC list_ss []
) THEN

SIMP_TAC std_ss [PMATCH_EQUIV_ROWS_def, PMATCH_APPEND_SEM] THEN
SIMP_TAC list_ss [] THEN

Tactical.REVERSE (`?r. MEM r (TAKE (SUC n) rows) /\ IS_SOME (r v)` by ALL_TAC) THEN1 (
  METIS_TAC[]
) THEN
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


val PMATCH_REMOVE_ARB = store_thm ("PMATCH_REMOVE_ARB",
``(PMATCH v (SNOC (PMATCH_ROW (\x. (f x, ARB))) rows) = 
   PMATCH v rows)``,

Induct_on `rows` THENL [
  SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def] THEN
  Cases_on `?x. f x = v` THEN (
    ASM_SIMP_TAC std_ss [PMATCH_INCOMPLETE_def]
  ),

  ASM_SIMP_TAC list_ss [PMATCH_def]
])

(* ARB rows can be removed, since a match failiure is the same 
   as ARB *)
val PMATCH_REMOVE_ARB_NO_OVERLAP = store_thm ("PMATCH_REMOVE_ARB_NO_OVERLAP",
``!v ff rows1 rows2.
  (!x. (v = ff x) ==> EVERY (\r. (r (ff x) = NONE)) rows2) ==>
  (PMATCH v (rows1 ++ ((PMATCH_ROW (\x. (ff x, ARB))) :: rows2)) = 
   PMATCH v (rows1 ++ rows2))``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (Induct_on `rows1`) THEN (
  ASM_SIMP_TAC list_ss [PMATCH_def]
) THEN

ASM_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def] THEN
Cases_on `?x. ff x = v` THEN (
  ASM_SIMP_TAC std_ss [PMATCH_INCOMPLETE_def]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `_ = v` (ASSUME_TAC o GSYM) THEN
Induct_on `rows2` THEN (
  FULL_SIMP_TAC list_ss [PMATCH_def, PMATCH_INCOMPLETE_def]
))



(* Add an injective function to the pattern and the value.
   This can be used to eliminate constructors. *)   
val PMATCH_ROW_REMOVE_FUN = store_thm ("PMATCH_ROW_REMOVE_FUN",
``!ff v f g. (!x y. (ff x = ff y) ==> (x = y)) ==>

  (PMATCH_ROW (\x. (ff (f x), g x)) (ff v) =
   PMATCH_ROW (\x. (f x, g x)) v)``,

REPEAT STRIP_TAC THEN
`!x y. (ff x = ff y) = (x = y)` by PROVE_TAC[] THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def])


val PMATCH_ROW_REMOVE_FUN_EXT = store_thm ("PMATCH_ROW_REMOVE_FUN_EXT",
``!ff v f f' g g'. 

  ((?x. f' x = ff v) = (?x. f x = v)) ==>
  (!x x'. (f' x = ff v) ==> (f x' = v) ==> (g x v = g' x')) ==>

  (PMATCH_ROW (\x. (f' x, g x v)) (ff v) =
   PMATCH_ROW (\x. (f x, g' x)) v)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
Cases_on `?x. f x = v` THEN (
  ASM_REWRITE_TAC[]
) THEN
SELECT_ELIM_TAC THEN
ASM_REWRITE_TAC [] THEN
REPEAT STRIP_TAC THEN
SELECT_ELIM_TAC THEN
ASM_REWRITE_TAC [] THEN
REPEAT STRIP_TAC THEN
PROVE_TAC[])



(* The following lemma looks rather complicated. It is
   intended to work together with PMATCH_ROW_REMOVE_FUN to
   propagate information in the var cases.

   as an example consider

   val t = ``PMATCH (SOME x, y) [
     PMATCH_ROW (\ x. ((SOME x, 0), SOME (x + y)));
     PMATCH_ROW (\ (x', y). ((x', y), x'))
   ]``

   We want to simplify this to 

   val t' = ``PMATCH (x, y) [
     PMATCH_ROW (\ x. ((x, 0), SOME (x + y)));
     PMATCH_ROW (\ (x'', y). ((x'', y), SOME x''))
   ]``
   
   This is done via PMATCH_ROWS_SIMP and PMATCH_ROWS_SIMP_SOUNDNESS.
   We need to show that the rows correspond to each other.

   For the first row, PMATCH_ROW_REMOVE_FUN is used with

   v := (x, y)
   ff (x, y) := (SOME x, y)
   
   f x := (x, 0)
   g x := SOME (x + y)


   For the second row, PMATCH_ROW_REMOVE_FUN is used with

   v := (SOME x, y)
   v' := (x, y)
   f (x', y) := (x', y)
   g (x', y) := x' 
   f' (x'', y) = (x'', y)
   g' (x'', y) := (SOME x'', y)
*)

val PMATCH_ROW_REMOVE_FUN_VAR = store_thm ("PMATCH_ROW_REMOVE_FUN_VAR",
``!v v' f g f' g'.
  ((!x'. (f' x' = v') = (f (g' x') = v)) /\
  ((!x. (f x = v) ==> ?x'. g' x' = x)) /\
  ((!x y. (f x = f y) ==> (x = y)))) ==>
  (PMATCH_ROW (\x. (f x, g x)) v =
   PMATCH_ROW (\x'. (f' x'), g (g' x')) v')``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [PMATCH_ROW_def] THEN
`(?x'. f (g' x') = v) = (?x. f x = v)` by ALL_TAC THEN1 (
  METIS_TAC[]
) THEN
Cases_on `?x. f x = v` THEN (
  ASM_SIMP_TAC std_ss []
) THEN

SELECT_ELIM_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
SELECT_ELIM_TAC THEN
REPEAT STRIP_TAC THEN (
  METIS_TAC[]
));



(***************************************************)
(* THEOREMS ABOUT FLATTENING                       *)
(***************************************************)

val PMATCH_FLATTEN_FUN_def = Define `
  PMATCH_FLATTEN_FUN f g h v = 
   if (?x. g x = v) then h (f (@x. g x = v)) else NONE`

val PMATCH_FLATTEN_THM_AUX = prove (
 ``(PMATCH v [PMATCH_ROW (\x. (g x, (PMATCH (f x) (MAP (\r. r x) rows'))))]) =
   (PMATCH v (MAP (\r. (PMATCH_FLATTEN_FUN f g) (r (@x. g x = v))) rows'))``,

Induct_on `rows'` THEN1 (
  Cases_on `?x. g x = v` THEN
  ASM_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def]
) THEN

Cases_on `?x. g x = v` THENL [
  GEN_TAC THEN
  ASM_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def, PMATCH_FLATTEN_FUN_def] THEN
  FULL_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def],

  GEN_TAC THEN
  `!r. (PMATCH_FLATTEN_FUN f g r v) = NONE` by ALL_TAC THEN1 (
    ASM_SIMP_TAC std_ss [PMATCH_FLATTEN_FUN_def]
  ) THEN
  FULL_SIMP_TAC list_ss [PMATCH_def, PMATCH_ROW_def]
])


val PMATCH_FLATTEN_FUN_PMATCH_ROW = store_thm ("PMATCH_FLATTEN_FUN_PMATCH_ROW",
``(!x1 x2. (g x1 = g x2) ==> (x1 = x2)) ==> 
  (!x y. (g'' x = y) = (g' x = f y)) ==> (
  PMATCH_FLATTEN_FUN f g (PMATCH_ROW (\x'. (g' x', f' x'))) = 
  PMATCH_ROW (\x. (g (g'' x), f' x)))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [PMATCH_FLATTEN_FUN_def, FUN_EQ_THM, PMATCH_ROW_def] THEN
GEN_TAC THEN
Tactical.REVERSE (Cases_on `?x'. g x' = x`) THEN1 (
  `~(?x'. g (g'' x') = x)` by METIS_TAC[] THEN
  ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
`!x''. (g x'' = x) = (x'' = x')` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[])


val _ = export_theory()

