open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) ::
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "stringTheory",
   "vars_as_resourceTheory", "containerTheory"];
show_assums := true;
*)

open generalHelpersTheory finite_mapTheory relationTheory pred_setTheory 
     sortingTheory listTheory rich_listTheory arithmeticTheory
     operatorTheory optionTheory separationLogicTheory 
     vars_as_resourceTheory;
open stringTheory ConseqConv boolSimps treeTheory 
     quantHeuristicsLib bagTheory containerTheory

(*
quietdec := false;
*)

val _ = new_theory "holfoot";

val MP_CANON = 
    CONV_RULE (REPEATC (
    CHANGED_CONV (REWRITE_CONV [AND_IMP_INTRO]) ORELSEC
    REDEPTH_CONV RIGHT_IMP_FORALL_CONV))


fun EQ_IMP_RULE_CANON thm =
   let
      val (vL, body) = strip_forall (concl thm)
      val pre = is_imp_only body
      val pre_term = if pre then fst (dest_imp body) else T
      val thm0 = if pre then UNDISCH (SPEC_ALL thm) else SPEC_ALL thm
      val thm1 = snd (EQ_IMP_RULE thm0);
      val thm2 = if pre then 
             (CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH pre_term thm1)) 
             else thm1
      val thm3 = GENL vL thm2
   in
      thm3
   end;


(*=====================================================================
 =
 = Basic constructs of the new language and the specification logic
 =
 =====================================================================*)


(**********************
 * States
 *********************)

val holfoot_tag = Hol_datatype `holfoot_tag =
   holfoot_tag of string`
val holfoot_tag_11 = DB.fetch "-" "holfoot_tag_11";

val holfoot_var = Hol_datatype `holfoot_var =
   holfoot_var of string`
val holfoot_var_11 = DB.fetch "-" "holfoot_var_11";



val INFINITE_UNIV_STRING = store_thm ("INFINITE_UNIV_STRING",
   ``INFINITE (UNIV:string set)``,
SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `\s. c::s` THEN
SIMP_TAC std_ss [CONS_11] THEN
Q.EXISTS_TAC `""` THEN
SIMP_TAC list_ss []);


val INFINITE_UNIV_HOLFOOT_TAG = store_thm ("INFINITE_UNIV_HOLFOOT_TAG",
    ``INFINITE (UNIV:holfoot_tag set)``,

`UNIV:holfoot_tag set = IMAGE (holfoot_tag) UNIV` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_IMAGE] THEN
      Cases_on `x` THEN
      PROVE_TAC[]
) THEN
METIS_TAC[IMAGE_11_INFINITE, INFINITE_UNIV_STRING, holfoot_tag_11]);



val INFINITE_UNIV_HOLFOOT_VAR = store_thm ("INFINITE_UNIV_HOLFOOT_VAR",
    ``INFINITE (UNIV:holfoot_var set)``,

`UNIV:holfoot_var set = IMAGE (holfoot_var) UNIV` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_IMAGE] THEN
      Cases_on `x` THEN
      PROVE_TAC[]
) THEN
METIS_TAC[IMAGE_11_INFINITE, INFINITE_UNIV_STRING, holfoot_var_11]);



val INFINITE_UNIV_NUM = store_thm ("INFINITE_UNIV_NUM",
    ``INFINITE (UNIV:num set)``,

SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `SUC` THEN
SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `0` THEN
SIMP_TAC arith_ss []);

val _ = type_abbrev("holfoot_heap", Type `:num |-> (holfoot_tag -> num)`)
val _ = type_abbrev("holfoot_stack", Type `:(num, holfoot_var) var_res_state`)
val _ = type_abbrev("holfoot_state", Type `:(holfoot_stack # holfoot_heap)`)

(* equivalent to x:(num,holfoot_var) var_res_expression*)
val _ = type_abbrev("holfoot_a_expression", Type `:holfoot_stack -> num option`)

(* equivalent to (num,holfoot_var,holfoot_heap) var_res_proposition*)
val _ = type_abbrev("holfoot_a_proposition", Type `:holfoot_state -> bool`);



(***************************************
 * Separation combinator on these states
 **************************************)

val holfoot_separation_combinator_def = Define `
   holfoot_separation_combinator =
   (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION):   holfoot_state bin_option_function`;


val IS_SEPARATION_ALGEBRA___holfoot_separation_combinator =
   store_thm ("IS_SEPARATION_ALGEBRA___holfoot_separation_combinator",
``IS_SEPARATION_ALGEBRA holfoot_separation_combinator (FEMPTY, FEMPTY)``,

REWRITE_TAC [holfoot_separation_combinator_def] THEN
MATCH_MP_TAC IS_SEPARATION_ALGEBRA___VAR_RES_COMBINATOR THEN
REWRITE_TAC[IS_SEPARATION_ALGEBRA___FINITE_MAP]);



val IS_SEPARATION_COMBINATOR___holfoot_separation_combinator =
   store_thm ("IS_SEPARATION_COMBINATOR___holfoot_separation_combinator",
``IS_SEPARATION_COMBINATOR holfoot_separation_combinator``,
PROVE_TAC[IS_SEPARATION_ALGEBRA___IS_COMBINATOR, IS_SEPARATION_ALGEBRA___holfoot_separation_combinator]);


val holfoot_separation_combinator___COMM = store_thm ("holfoot_separation_combinator___COMM",
``!s1 s2. holfoot_separation_combinator s1 s2 = holfoot_separation_combinator s2 s1``,
PROVE_TAC[IS_SEPARATION_ALGEBRA___holfoot_separation_combinator, IS_SEPARATION_ALGEBRA_def, COMM_DEF]);



val IS_VAR_RES_COMBINATOR___holfoot_separation_combinator =
store_thm ("IS_VAR_RES_COMBINATOR___holfoot_separation_combinator",
``IS_VAR_RES_COMBINATOR holfoot_separation_combinator``,
SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def, holfoot_separation_combinator_def] THEN
Q.EXISTS_TAC `DISJOINT_FMAP_UNION` THEN
REWRITE_TAC[IS_SEPARATION_COMBINATOR___FINITE_MAP]);


val GET_VAR_RES_COMBINATOR___holfoot_separation_combinator =
store_thm ("GET_VAR_RES_COMBINATOR___holfoot_separation_combinator",
``GET_VAR_RES_COMBINATOR holfoot_separation_combinator = DISJOINT_FMAP_UNION``,

SIMP_TAC std_ss [holfoot_separation_combinator_def] THEN
MATCH_MP_TAC GET_VAR_RES_COMBINATOR_THM THEN
REWRITE_TAC[IS_SEPARATION_COMBINATOR___FINITE_MAP]);


val holfoot_separation_combinator___REWRITE_helper = prove (``
!s1 s2. holfoot_separation_combinator (SOME s1) (SOME s2) =
           (if (VAR_RES_STACK_IS_SEPARATE (FST s1) (FST s2) /\ (DISJOINT (FDOM (SND s1)) (FDOM (SND s2)))) then
              SOME (THE (VAR_RES_STACK_COMBINE (SOME (FST s1)) (SOME (FST s2))),FUNION (SND s1) (SND s2))
            else
              NONE)``,

Cases_on `s1` THEN Cases_on `s2` THEN
SIMP_TAC std_ss [holfoot_separation_combinator_def, VAR_RES_COMBINATOR_def,
   PRODUCT_SEPARATION_COMBINATOR_REWRITE, LET_THM,
   DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
Cases_on `DISJOINT (FDOM r) (FDOM r')` THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_REWRITE]);



val holfoot_separation_combinator___REWRITE =
save_thm ("holfoot_separation_combinator___REWRITE",

let
   val thm0 = IS_SEPARATION_ALGEBRA___holfoot_separation_combinator;
   val thm1 = SIMP_RULE std_ss [IS_SEPARATION_ALGEBRA_EXPAND_THM] thm0;
in CONJ thm1 holfoot_separation_combinator___REWRITE_helper end);



val holfoot_separation_combinator___asl_emp___REWRITE =
store_thm ("holfoot_separation_combinator___asl_emp___REWRITE",
``(holfoot_separation_combinator (SOME (FEMPTY,FEMPTY)) X = X) /\
  (holfoot_separation_combinator X (SOME (FEMPTY,FEMPTY)) = X)``,
Cases_on `X` THEN
SIMP_TAC std_ss [holfoot_separation_combinator___REWRITE]);



val SOME___holfoot_separation_combinator = store_thm ("SOME___holfoot_separation_combinator",
``!s1 s2 s. 
((holfoot_separation_combinator (SOME s1) (SOME s2) = SOME s) =

(DISJOINT (FDOM (SND s1)) (FDOM (SND s2)) /\
(VAR_RES_STACK_COMBINE (SOME (FST s1)) (SOME (FST s2)) = SOME (FST s)) /\
((SND s) = FUNION (SND s1) (SND s2))))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [holfoot_separation_combinator___REWRITE, COND_NONE_SOME_REWRITES,
SOME___VAR_RES_STACK_COMBINE] THEN
Cases_on `VAR_RES_STACK_IS_SEPARATE (FST s1) (FST s2)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `s` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_EXPAND] THEN
METIS_TAC[]);




val holfoot_separation_combinator___asl_emp = store_thm ("holfoot_separation_combinator___asl_emp",
``asl_emp holfoot_separation_combinator = {(FEMPTY, FEMPTY)}``,

SIMP_TAC std_ss [asl_emp_def, holfoot_separation_combinator___REWRITE,
   EXTENSION, IN_ABS, IN_SING]);

val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star___holfoot =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star___holfoot",
``!exS P1 P2.
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P1 /\
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P2 ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS
       (asl_star holfoot_separation_combinator P1 P2)``,
REWRITE_TAC [holfoot_separation_combinator_def,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star])


val VAR_RES_IS_STACK_IMPRECISE___asl_star___holfoot =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___asl_star___holfoot",
``!P1 P2.
     VAR_RES_IS_STACK_IMPRECISE P1 /\
     VAR_RES_IS_STACK_IMPRECISE P2 ==>
     VAR_RES_IS_STACK_IMPRECISE (asl_star holfoot_separation_combinator P1 P2)``,
REWRITE_TAC [holfoot_separation_combinator_def,
   VAR_RES_IS_STACK_IMPRECISE___asl_star])


val asl_star_holfoot_THM = store_thm ("asl_star_holfoot_THM",
``(asl_star holfoot_separation_combinator P (asl_emp holfoot_separation_combinator) = P) /\
  (asl_star holfoot_separation_combinator (asl_emp holfoot_separation_combinator) P = P) /\
  (asl_star holfoot_separation_combinator (var_res_bool_proposition DISJOINT_FMAP_UNION b1) (var_res_bool_proposition DISJOINT_FMAP_UNION b2) =
         var_res_bool_proposition DISJOINT_FMAP_UNION (b1 /\ b2)) /\
  (asl_star holfoot_separation_combinator (var_res_bool_proposition DISJOINT_FMAP_UNION b1) (asl_star holfoot_separation_combinator 
           (var_res_bool_proposition DISJOINT_FMAP_UNION b2) P) =
         asl_star holfoot_separation_combinator (var_res_bool_proposition DISJOINT_FMAP_UNION (b1 /\ b2)) P) /\
  (asl_star holfoot_separation_combinator (var_res_bool_proposition DISJOINT_FMAP_UNION b1) (var_res_prop_stack_true DISJOINT_FMAP_UNION) =
         var_res_bool_proposition DISJOINT_FMAP_UNION b1) /\
  (asl_star holfoot_separation_combinator (var_res_prop_stack_true DISJOINT_FMAP_UNION) (var_res_bool_proposition DISJOINT_FMAP_UNION b1) =
         var_res_bool_proposition DISJOINT_FMAP_UNION b1)``, 
  SIMP_TAC std_ss [REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES,
         IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
  SIMP_TAC std_ss [asl_star___var_res_bool_proposition, holfoot_separation_combinator_def,
         IS_SEPARATION_COMBINATOR___FINITE_MAP, var_res_prop_stack_true_def]);


val var_res_prop_varlist_update___asl_star___holfoot =
store_thm ("var_res_prop_varlist_update___asl_star___holfoot",
``!vL p1 p2.
     VAR_RES_IS_STACK_IMPRECISE p1 /\ VAR_RES_IS_STACK_IMPRECISE p2 ==>
     (var_res_prop_varlist_update vL (asl_star holfoot_separation_combinator p1 p2) =
      asl_star holfoot_separation_combinator
        (var_res_prop_varlist_update vL p1)
        (var_res_prop_varlist_update vL p2))``,
SIMP_TAC std_ss [holfoot_separation_combinator_def,
  var_res_prop_varlist_update___asl_star]);


(***************************************
 * SUBSTATES
 **************************************)

val HOLFOOT_IS_SUBSTATE_def = Define
`HOLFOOT_IS_SUBSTATE =
 ASL_IS_SUBSTATE holfoot_separation_combinator`;



val HOLFOOT_IS_SUBSTATE___IS_PREORDER =
    store_thm ("HOLFOOT_IS_SUBSTATE___IS_PREORDER",
``PreOrder HOLFOOT_IS_SUBSTATE``,

PROVE_TAC[HOLFOOT_IS_SUBSTATE_def, ASL_IS_SUBSTATE___IS_PREORDER,
     IS_SEPARATION_COMBINATOR___holfoot_separation_combinator]);



val HOLFOOT_IS_SUBSTATE___TRANS =
    save_thm ("HOLFOOT_IS_SUBSTATE___TRANS",
CONJUNCT2 (
REWRITE_RULE[PreOrder, transitive_def] HOLFOOT_IS_SUBSTATE___IS_PREORDER));

val HOLFOOT_IS_SUBSTATE___REFL =
    save_thm ("HOLFOOT_IS_SUBSTATE___REFL",
CONJUNCT1 (
REWRITE_RULE[PreOrder, reflexive_def] HOLFOOT_IS_SUBSTATE___IS_PREORDER));




val HOLFOOT_IS_SUBSTATE_INTRO = store_thm ("HOLFOOT_IS_SUBSTATE_INTRO",
``!x1 x2 x.
   (holfoot_separation_combinator (SOME x1) (SOME x2) = SOME x) ==>
   (HOLFOOT_IS_SUBSTATE x1 x /\
    HOLFOOT_IS_SUBSTATE x2 x)``,

SIMP_TAC std_ss [HOLFOOT_IS_SUBSTATE_def,
       ASL_IS_SUBSTATE_def] THEN
ASSUME_TAC IS_SEPARATION_COMBINATOR___holfoot_separation_combinator THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
METIS_TAC[]);



val HOLFOOT_IS_SUBSTATE_REWRITE = store_thm (
"HOLFOOT_IS_SUBSTATE_REWRITE",
``!s1 s2.
HOLFOOT_IS_SUBSTATE s1 s2 =
VAR_RES_STACK_IS_SUBSTATE (FST s1) (FST s2) /\
ASL_IS_SUBSTATE DISJOINT_FMAP_UNION (SND s1) (SND s2)``,

SIMP_TAC std_ss [HOLFOOT_IS_SUBSTATE_def,
       holfoot_separation_combinator_def, VAR_RES_COMBINATOR_def,
       ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR,
       VAR_RES_STACK_IS_SUBSTATE_def]);



val HOLFOOT_SUBSTATE_IMPLS = store_thm ("HOLFOOT_SUBSTATE_IMPLS",
``!s1 s2. ASL_IS_SUBSTATE holfoot_separation_combinator s1 s2 ==>
 (((SND s1) SUBMAP (SND s2)) /\
 (!v. (v IN FDOM (FST s1)) ==> (
   (v IN FDOM (FST s2)) /\ (FST ((FST s2) ' v) = (FST ((FST s1) ' v))) /\
   (IS_VAR_RES_SUBPERMISSION (SND ((FST s1) ' v)) (SND ((FST s2) ' v))))))``,


SIMP_TAC std_ss [GSYM HOLFOOT_IS_SUBSTATE_def,
       HOLFOOT_IS_SUBSTATE_REWRITE,
       VAR_RES_STACK_IS_SUBSTATE_REWRITE,
       ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
       SUBMAP_DEF, SUBSET_DEF]);


(******************************************
 * not in heap
 ******************************************)

val holfoot_not_in_heap_def = Define `
holfoot_not_in_heap (e:holfoot_a_expression) =
\s. ?c. (e (FST s) = SOME c) /\ (~(c IN FDOM (SND s)))`


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_not_in_heap =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_not_in_heap",
``!vs e.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_not_in_heap e)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
   holfoot_not_in_heap_def, IN_ABS, GSYM IS_SOME_EXISTS] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `c` THEN
FULL_SIMP_TAC std_ss [] THEN

Tactical.REVERSE (`e (FST s) = e (FST s2)` by ALL_TAC) THEN1 ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN

Q.EXISTS_TAC `vs'` THEN Q.EXISTS_TAC `vs'` THEN
ASM_SIMP_TAC std_ss [SUBSET_REFL] THEN

MATCH_MP_TAC (prove (``(((A /\ B) ==> C) /\ (B /\ (B ==> A))) ==> (A /\ B /\ C)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!v. X v` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF]
) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
   METIS_TAC[optionTheory.option_CLAUSES]
) THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]);



(******************************************
 * implies in heap
 ******************************************)

val holfoot_implies_in_heap_pred_def = Define `
  holfoot_implies_in_heap_pred p B b e =
  (!st:holfoot_stack st2:holfoot_stack h1:holfoot_heap h2:holfoot_heap.
       VAR_RES_STACK_IS_SUBSTATE st2 st /\
       (st,  h1) IN (var_res_bigstar DISJOINT_FMAP_UNION B) /\
       (st2, h2) IN (var_res_bigstar DISJOINT_FMAP_UNION b) ==>
      (IS_SOME ((e:holfoot_a_expression) st) /\ (p (FDOM h2) (THE (e st)))))`;

val holfoot_implies_in_heap_def = Define `
  holfoot_implies_in_heap =
  holfoot_implies_in_heap_pred (\X x. ~(x = 0) /\ x IN X)`

val holfoot_implies_in_heap_or_null_def = Define `
  holfoot_implies_in_heap_or_null =
  holfoot_implies_in_heap_pred (\X x. (x = 0) \/ x IN X)`


val holfoot_implies_in_heap___implies___or_null =
store_thm ("holfoot_implies_in_heap___implies___or_null",

``!B b e. holfoot_implies_in_heap B b e ==>
          holfoot_implies_in_heap_or_null B b e``,

SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
  holfoot_implies_in_heap_def, holfoot_implies_in_heap_pred_def] THEN
METIS_TAC[]);


val holfoot_implies_in_heap_or_null___const_null =
store_thm ("holfoot_implies_in_heap_or_null___const_null",
``!B b. holfoot_implies_in_heap_or_null B b (var_res_exp_const 0)``,
SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
  holfoot_implies_in_heap_pred_def, var_res_exp_const_def]);


val holfoot_implies_in_heap___or_null___implies_unequal =
store_thm ("holfoot_implies_in_heap___or_null___implies_unequal",
``!sfb b1 b2 e1 e2.
SUB_BAG (BAG_UNION b1 b2) sfb /\
holfoot_implies_in_heap sfb b1 e1 /\
holfoot_implies_in_heap_or_null sfb b2 e2 ==>

var_res_implies_unequal DISJOINT_FMAP_UNION sfb e1 e2``,

SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
   holfoot_implies_in_heap_def, SUB_BAG_EXISTS,
   holfoot_implies_in_heap_pred_def,
   GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   var_res_implies_unequal_def,
   holfoot_separation_combinator_def] THEN
REPEAT STRIP_TAC THEN
`?st h. s = (st, h)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
REPEAT (Q.PAT_ASSUM `!st st2 h1 h2. X`
    (MP_TAC o Q.SPEC `h` o CONV_RULE SWAP_FORALL_CONV o Q.SPEC `st`)) THEN
FULL_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [
   var_res_bigstar_UNION, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   asl_star_def, IN_ABS, GSYM holfoot_separation_combinator_def,
   SOME___holfoot_separation_combinator] THEN
REPEAT STRIP_TAC THEN
`?st1 st2 h1 h2. (p' = (st1, h1)) /\ (q' = (st2, h2))` by
  (Cases_on `p'` THEN Cases_on `q'` THEN SIMP_TAC std_ss []) THEN
Q.PAT_ASSUM `!st2 h2. X` (MP_TAC o Q.SPECL [`st2`, `h2`]) THEN
Q.PAT_ASSUM `!st2 h2. X` (MP_TAC o Q.SPECL [`st1`, `h1`]) THEN

`VAR_RES_STACK_IS_SUBSTATE st1 st /\
 VAR_RES_STACK_IS_SUBSTATE st2 st` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC [VAR_RES_STACK_IS_SUBSTATE_INTRO,
      VAR_RES_STACK_IS_SUBSTATE___TRANS]
) THEN
FULL_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS] THEN
REPEAT STRIP_TAC THEN (
   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
   METIS_TAC[]
));




val holfoot_implies_in_heap___implies_unequal =
store_thm ("holfoot_implies_in_heap___implies_unequal",
``!sfb b1 b2 e1 e2.
SUB_BAG (BAG_UNION b1 b2) sfb /\
holfoot_implies_in_heap sfb b1 e1 /\
holfoot_implies_in_heap sfb b2 e2 ==>

var_res_implies_unequal DISJOINT_FMAP_UNION sfb e1 e2``,

METIS_TAC[holfoot_implies_in_heap___or_null___implies_unequal,
          holfoot_implies_in_heap___implies___or_null]);


val holfoot_implies_in_heap___implies_unequal___null =
store_thm ("holfoot_implies_in_heap___implies_unequal___null",
``!sfb b e.
SUB_BAG b sfb /\ holfoot_implies_in_heap sfb b e ==>
var_res_implies_unequal DISJOINT_FMAP_UNION sfb e (var_res_exp_const 0)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap___or_null___implies_unequal THEN
Q.EXISTS_TAC `b` THEN Q.EXISTS_TAC `EMPTY_BAG` THEN
ASM_SIMP_TAC std_ss [BAG_UNION_EMPTY,
   holfoot_implies_in_heap_or_null___const_null]);



val holfoot_implies_in_heap_or_null___implies_equal =
store_thm ("holfoot_implies_in_heap_or_null___implies_equal",
``!wpb rpb sfb b1 b2 e.

SUB_BAG (BAG_UNION b1 b2) sfb /\
holfoot_implies_in_heap_or_null sfb b1 e /\
holfoot_implies_in_heap_or_null sfb b2 e ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e  ==>

var_res_prop_implies DISJOINT_FMAP_UNION (wpb,rpb) sfb
   {|var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0)|}``,


SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
   SUB_BAG_EXISTS,
   holfoot_implies_in_heap_pred_def,
   GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   var_res_implies_unequal_def,
   holfoot_separation_combinator_def,
   var_res_prop_implies_REWRITE,
   BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
       ((var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0)):holfoot_a_proposition)` by ALL_TAC THEN1 (
      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
      ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
         EMPTY_SUBSET]
) THEN
Tactical.REVERSE (`!s.
    (var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) (b1 + b2 + b) /\
     s IN var_res_prop___PROP DISJOINT_FMAP_UNION (wpb,rpb) (b1 + b2 + b)) ==>
        (e (FST s) = SOME 0)` by ALL_TAC) THEN1 (

   ASM_SIMP_TAC std_ss [var_res_prop___REWRITE,
       var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT] THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [COND_RAND, COND_RATOR,
      var_res_prop_equal_unequal_EXPAND, IN_ABS,
      var_res_exp_const_def, asl_emp_DISJOINT_FMAP_UNION,
      IN_SING, DISJOINT_FMAP_UNION___FEMPTY,
      IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM] THEN
   SIMP_TAC std_ss [IN_ABS3]
) THEN

REPEAT STRIP_TAC THEN
`s IN var_res_bigstar DISJOINT_FMAP_UNION (b1 + b2 + b)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
     IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS]
) THEN

`?st h. s = (st, h)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
Q.PAT_ASSUM `s IN var_res_prop___PROP f X Z` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION,
   var_res_prop___PROP_UNION, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!st st2 h1 h2. X` (MP_TAC o Q.SPECL [`st`, `st`, `h`, `s2'`]) THEN
Q.PAT_ASSUM `!st st2 h1 h2. X` (MP_TAC o Q.SPECL [`st`, `st`, `h`, `s1'`]) THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE___REFL] THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IN_ABS] THEN
SIMP_TAC (std_ss++CONJ_ss) [IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE, EXTENSION,
   DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
METIS_TAC[]);



val holfoot_implies_in_heap_pred___asl_and =
store_thm ("holfoot_implies_in_heap_pred___asl_and",

``!p B P1 P2 sfb e.
    (holfoot_implies_in_heap_pred p B (BAG_INSERT P1 sfb) e \/
     holfoot_implies_in_heap_pred p B (BAG_INSERT P2 sfb) e) ==>
    (holfoot_implies_in_heap_pred p B (BAG_INSERT
        (asl_and P1 P2) sfb) e)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
   var_res_bigstar_REWRITE_EXT,
   holfoot_separation_combinator_def,
   BAG_INSERT_NOT_EMPTY,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT GEN_TAC THEN
Q.HO_MATCH_ABBREV_TAC `((!st st2 h1 h2. PP1 st st2 h1 h2 ==> Q st h1 h2) \/ (!st st2 h1 h2. PP2 st st2 h1 h2 ==> Q st h1 h2)) ==>
                        (!st st2 h1 h2. PP st st2 h1 h2 ==> Q st h1 h2)` THEN
Tactical.REVERSE (`!st st2 h1 h2. PP st st2 h1 h2 ==> PP1 st st2 h1 h2 /\  PP2 st st2 h1 h2` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN
UNABBREV_ALL_TAC THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS, asl_bool_EVAL] THEN
METIS_TAC[]);



val holfoot_implies_in_heap_pred___asl_exists =
store_thm ("holfoot_implies_in_heap_pred___asl_exists",
``!p B P sfb e.
    (holfoot_implies_in_heap_pred p B (BAG_INSERT
        (asl_exists x. P x) sfb) e) =
    (!x. holfoot_implies_in_heap_pred p B (BAG_INSERT (P x) sfb) e)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
   var_res_bigstar_REWRITE_EXT,
   holfoot_separation_combinator_def,
   GSYM asl_exists___asl_star_THM, asl_bool_EVAL,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   GSYM LEFT_FORALL_IMP_THM,
   BAG_INSERT_NOT_EMPTY] THEN
METIS_TAC[]);


val holfoot_implies_in_heap_pred___asl_false =
store_thm ("holfoot_implies_in_heap_pred___asl_false",
``!p B sfb e.
    (holfoot_implies_in_heap_pred p B (BAG_INSERT
        asl_false sfb) e)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
   var_res_bigstar_REWRITE_EXT,
   holfoot_separation_combinator_def,
   asl_false___asl_star_THM, asl_bool_EVAL,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   BAG_INSERT_NOT_EMPTY]);


val holfoot_implies_in_heap_pred___asl_star =
store_thm ("holfoot_implies_in_heap_pred___asl_star",

``!p B P1 P2 sfb e.
    (holfoot_implies_in_heap_pred p B (BAG_INSERT
        (asl_star holfoot_separation_combinator P1 P2) sfb) e) =
    holfoot_implies_in_heap_pred p B (BAG_INSERT P1 (BAG_INSERT P2 sfb)) e``,

SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
   var_res_bigstar_REWRITE_EXT, 
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   holfoot_separation_combinator_def,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES,
   BAG_INSERT_NOT_EMPTY]);


val holfoot_implies_in_heap_pred___asl_bigstar =
store_thm ("holfoot_implies_in_heap_pred___asl_bigstar",

``!p B sfb1 sfb2 e.
    ((holfoot_implies_in_heap_pred p B (BAG_INSERT
        (asl_bigstar holfoot_separation_combinator sfb1) sfb2) e) =
    (holfoot_implies_in_heap_pred p B (BAG_UNION sfb1 sfb2) e))``,

REPEAT GEN_TAC THEN
Tactical.REVERSE (Cases_on `FINITE_BAG sfb1`) THEN1 (
   SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
      asl_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
   FULL_SIMP_TAC std_ss [var_res_bigstar_REWRITE_EXT,
       IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
   ASM_SIMP_TAC std_ss [var_res_bigstar_def, asl_bigstar_def, FINITE_BAG_UNION,
       BAG_INSERT_NOT_EMPTY, BAG_UNION_EMPTY, FINITE_BAG_THM, asl_bool_EVAL,
       asl_false___asl_star_THM]
) THEN
Q.SPEC_TAC (`sfb2`, `sfb2`) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`sfb1`, `sfb1`) THEN
HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
     asl_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
     asl_star___PROPERTIES, BAG_UNION_EMPTY, var_res_bigstar_REWRITE,
     IS_SEPARATION_COMBINATOR___FINITE_MAP,
     GSYM holfoot_separation_combinator_def],

   ASM_SIMP_TAC std_ss [holfoot_implies_in_heap_pred___asl_star,
      asl_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
   ONCE_REWRITE_TAC[BAG_INSERT_commutes] THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [BAG_UNION_INSERT]
]);




val holfoot_implies_in_heap_pred___SUB_BAG =
store_thm ("holfoot_implies_in_heap_pred___SUB_BAG",
``!p B sfb1 sfb2 e.
    SUB_BAG sfb1 sfb2 /\
    (!s1 s2 x. s1 SUBSET s2 /\ p s1 x ==> p s2 x) /\
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
    (holfoot_implies_in_heap_pred p B sfb1 e) ==>
    (holfoot_implies_in_heap_pred p B sfb2 e)``,

SIMP_TAC (std_ss++CONJ_ss) [holfoot_implies_in_heap_pred_def,
   SUB_BAG_EXISTS, 
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, asl_star_def, IN_ABS,
   var_res_bigstar_UNION, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `!st st2 h1 h2. X` (MP_TAC o Q.SPECL [
   `st`,  `FST (p':holfoot_state)`,
   `h1`, `SND (p':holfoot_state)`]) THEN
`(VAR_RES_STACK_IS_SUBSTATE (FST p') st) /\
   FDOM (SND p') SUBSET FDOM h2` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
      FDOM_FUNION, SUBSET_UNION, GSYM holfoot_separation_combinator_def] THEN
   METIS_TAC[VAR_RES_STACK_IS_SUBSTATE___TRANS, VAR_RES_STACK_IS_SUBSTATE_INTRO]
) THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);


val holfoot_implies_in_heap_or_null___SUB_BAG =
store_thm ("holfoot_implies_in_heap_or_null___SUB_BAG",
``!B sfb1 sfb2 e.
    SUB_BAG sfb1 sfb2 ==>
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
    ((holfoot_implies_in_heap_or_null B sfb1 e) ==>
     (holfoot_implies_in_heap_or_null B sfb2 e))``,

REWRITE_TAC[holfoot_implies_in_heap_or_null_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap_pred___SUB_BAG THEN
Q.EXISTS_TAC `sfb1` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF] THEN
METIS_TAC[]);


val holfoot_implies_in_heap___SUB_BAG =
store_thm ("holfoot_implies_in_heap___SUB_BAG",
``!B sfb1 sfb2 e.
    SUB_BAG sfb1 sfb2 ==>
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
    ((holfoot_implies_in_heap B sfb1 e) ==>
     (holfoot_implies_in_heap B sfb2 e))``,

REWRITE_TAC[holfoot_implies_in_heap_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap_pred___SUB_BAG THEN
Q.EXISTS_TAC `sfb1` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF]);


val holfoot_implies_in_heap_pred___FIRST =
store_thm ("holfoot_implies_in_heap_pred___FIRST",
``!p B P sfb e.
    (!s1 s2 x. s1 SUBSET s2 /\ p s1 x ==> p s2 x) /\
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
    (!st h. (st, h) IN P ==>
            (IS_SOME (e st) /\ p (FDOM h) (THE (e st)))) ==>
    (holfoot_implies_in_heap_pred p B (BAG_INSERT P sfb) e)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_pred_def,
   BAG_INSERT_NOT_EMPTY, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [asl_star_def, IN_ABS,
   holfoot_separation_combinator_def,
   VAR_RES_COMBINATOR_REWRITE, LET_THM,
   DISJOINT_FMAP_UNION___REWRITE,
   COND_NONE_SOME_REWRITES] THEN
`?st' h'. p' = (st', h')` by (Cases_on `p'` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN
`e st = e st'` by ALL_TAC THEN1 (
   MATCH_MP_TAC
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT THEN
   ASM_SIMP_TAC std_ss [] THEN
   PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO,
      VAR_RES_STACK_IS_SUBSTATE___TRANS]
) THEN
FULL_SIMP_TAC std_ss [IN_UNION, FDOM_FUNION] THEN
Q.PAT_ASSUM `!s1 s2 x. X` MATCH_MP_TAC THEN
Q.EXISTS_TAC `FDOM h'` THEN
ASM_SIMP_TAC std_ss [SUBSET_UNION]);


val holfoot_implies_in_heap___FIRST =
store_thm ("holfoot_implies_in_heap___FIRST",
``!B P sfb e.
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
    (!st h. (st, h) IN P ==>
            (IS_SOME (e st) /\ (THE (e st)) IN (FDOM h) /\
             ~(THE (e st) = 0))) ==>
    (holfoot_implies_in_heap B (BAG_INSERT P sfb) e)``,

REWRITE_TAC [holfoot_implies_in_heap_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap_pred___FIRST THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF] THEN
PROVE_TAC[]);


val holfoot_implies_in_heap_or_null___FIRST =
store_thm ("holfoot_implies_in_heap_or_null___FIRST",
``!B P sfb e.
    IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
    (!st h. (st, h) IN P ==>
            (IS_SOME (e st) /\ ((THE (e st)) IN (FDOM h) \/
             (THE (e st) = 0)))) ==>
    (holfoot_implies_in_heap_or_null B (BAG_INSERT P sfb) e)``,

REWRITE_TAC [holfoot_implies_in_heap_or_null_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap_pred___FIRST THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF] THEN
PROVE_TAC[]);





val holfoot_implies_in_heap_or_null___equal_null =
store_thm ("holfoot_implies_in_heap_or_null___equal_null",
``(!B e sfb. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
 holfoot_implies_in_heap_or_null B
    (BAG_INSERT
      (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_const 0) e) sfb) e) /\
(!B e sfb. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
 holfoot_implies_in_heap_or_null B
    (BAG_INSERT
      (var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0)) sfb) e) /\
(!B e sfb. ~(B = EMPTY_BAG) /\ IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
 holfoot_implies_in_heap_or_null B
    (BAG_INSERT
      (var_res_prop_weak_equal (var_res_exp_const 0) e) sfb) e) /\
(!B e sfb. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
 holfoot_implies_in_heap_or_null B
    (BAG_INSERT
      (var_res_prop_weak_equal e (var_res_exp_const 0)) sfb) e)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def] THEN
CONSEQ_REWRITE_TAC ([], [holfoot_implies_in_heap_pred___FIRST], []) THEN
SIMP_TAC std_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM, SUBSET_DEF,
   var_res_prop_equal_unequal_EXPAND,
   IN_ABS, var_res_exp_const_def]);






(******************************************
 * Expressions & Propositions
 ******************************************)


(*-----------------
 * Points to
 *-----------------*)
val holfoot_ap_points_to_def = Define `
   holfoot_ap_points_to e1 L = \state:holfoot_state.
      let stack = FST state in
      let heap = SND state in
      let loc_opt = (e1 stack) in (IS_SOME (loc_opt) /\
      let (loc = THE loc_opt) in (~(loc = 0) /\  ((FDOM heap)= {loc}) /\
      (FEVERY (\(tag,exp).
            (IS_SOME (exp stack)) /\
            (THE (exp stack) = (heap ' loc) tag)) L)))`;



val holfoot_ap_points_to___null =
store_thm ("holfoot_ap_points_to___null",
``!L. holfoot_ap_points_to (var_res_exp_const 0) L = asl_false``,
SIMP_TAC std_ss [holfoot_ap_points_to_def, var_res_exp_const_def,
                 LET_THM, PAIR_BETA_THM, asl_false_def,
                 EMPTY_DEF]);


val holfoot_ap_points_to___SUBMAP =
store_thm ("holfoot_ap_points_to___SUBMAP",
``!e L1 L2 s.
(s IN holfoot_ap_points_to e L1 /\ L2 SUBMAP L1) ==>
(s IN holfoot_ap_points_to e L2)``,
Cases_on `s` THEN
SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM] THEN
SIMP_TAC std_ss [SUBMAP_DEF, FEVERY_DEF]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to",
``!vs e1 L.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1 /\
FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (SND x)) L) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_points_to e1 L)``,



SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
       IN_ABS, LET_THM, holfoot_ap_points_to_def] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN

`!e:holfoot_a_expression. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
      IS_SOME (e (FST s2))) ==>
     (e (FST s2) = e (FST s))` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   `vs'' SUBSET FDOM (FST s2)` by METIS_TAC[] THEN
   `vs'' SUBSET FDOM (FST s)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `FDOM (FST s2) INTER X SUBSET Y` MP_TAC THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
   ) THEN
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF]
) THEN

RES_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT (Q.PAT_ASSUM `FEVERY X L` MP_TAC) THEN
Q.SPEC_TAC (`L`, `L`) THEN

HO_MATCH_MP_TAC fmap_INDUCT THEN
SIMP_TAC std_ss [FEVERY_FEMPTY, FEVERY_FUPDATE, NOT_FDOM_DRESTRICT] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN
`y (FST s2) = y (FST s)` by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss []);



val VAR_RES_IS_STACK_IMPRECISE___points_to =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___points_to",
``!e L.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
FEVERY (\x. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (SND x))) L) ==>

VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_points_to e L)``,

REWRITE_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
        GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
             VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to]);


val var_res_prop_varlist_update___holfoot_ap_points_to =
store_thm ("var_res_prop_varlist_update___holfoot_ap_points_to",
``!vcL e L.
var_res_prop_varlist_update vcL (holfoot_ap_points_to e L) =
holfoot_ap_points_to (var_res_exp_varlist_update vcL e)
                     ((var_res_exp_varlist_update vcL) o_f L)``,

SIMP_TAC std_ss [holfoot_ap_points_to_def,
   var_res_prop_varlist_update_def, IN_ABS, LET_THM,
   var_res_ext_state_varlist_update_def,
   var_res_exp_varlist_update_def,
   FEVERY_o_f] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [FEVERY_DEF])




val holfoot_ap_points_to___implies_in_heap = store_thm (
"holfoot_ap_points_to___implies_in_heap",
``!B e L sfb. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
        holfoot_implies_in_heap B
        (BAG_INSERT (holfoot_ap_points_to e L) sfb) e``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap___FIRST THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def,
   IN_ABS, LET_THM, IN_SING]);

val holfoot_ap_points_to___implies_in_heap___COMPUTE = store_thm (
"holfoot_ap_points_to___implies_in_heap___COMPUTE",
``!B e L. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
        holfoot_implies_in_heap B
        ({| (holfoot_ap_points_to e L) |}) e``,
SIMP_TAC std_ss [holfoot_ap_points_to___implies_in_heap]);



val holfoot_ap_points_to___implies_in_heap_or_null = store_thm (
"holfoot_ap_points_to___implies_in_heap_or_null",
``!B e L sfb. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
        holfoot_implies_in_heap_or_null B
        (BAG_INSERT (holfoot_ap_points_to e L) sfb) e``,

PROVE_TAC[holfoot_ap_points_to___implies_in_heap,
   holfoot_implies_in_heap___implies___or_null]);



val holfoot_ap_points_to___ADD_TAG = store_thm ("holfoot_ap_points_to___ADD_TAG",
``!t e L.
~(t IN FDOM L) ==>
(holfoot_ap_points_to e L =
 asl_exists c. holfoot_ap_points_to e (L |+ (t, var_res_exp_const c)))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_points_to_def, EXTENSION, asl_bool_EVAL,
   IN_ABS, LET_THM, FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
   IN_INSERT, DISJ_IMP_THM, var_res_exp_const_def, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THEN
DEPTH_CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
`~(x' = t)` by PROVE_TAC[] THEN
ASM_SIMP_TAC std_ss []);





val HOLFOOT_COND_INFERENCE___points_to___ADD_TAG =
store_thm ("HOLFOOT_COND_INFERENCE___points_to___ADD_TAG",
``!t wpb rpb e L sfb prog Q.

~(t IN FDOM L) ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
FEVERY (\x.
  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) (SND x)) L ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT (holfoot_ap_points_to e L) sfb))
    prog Q) =
(!c. (VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT (holfoot_ap_points_to e (L |+ (t, var_res_exp_const c))) sfb))
    prog Q)))``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC holfoot_ap_points_to___ADD_TAG THEN
ASM_SIMP_TAC std_ss [] THEN
HO_MATCH_MP_TAC VAR_RES_COND_INFERENCE___asl_exists_pre THEN
CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
   FEVERY_STRENGTHEN_THM], []) THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]);




val VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP___REWRITE = prove (
``!l' L L' e wpb rpb sfb_context sfb_split sfb_imp.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (wpb + rpb)) e /\
FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L /\
FEVERY (\x. ~(MEM (FST x) l') \/ VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L' /\
(FEVERY (\ (t,a). (t IN FDOM L) /\ ((MEM t l') \/ (a = L ' t))) L') /\
(EVERY (\t. t IN FDOM L') l')  ==>

VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) sfb_context
 (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
 (BAG_INSERT (holfoot_ap_points_to e L') sfb_imp) 

 (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
 sfb_split (BAG_INSERT (asl_bigstar_list holfoot_separation_combinator     
    ((MAP (\t. var_res_prop_equal DISJOINT_FMAP_UNION (L ' t) (L' ' t)) l')++
     [var_res_prop_stack_true DISJOINT_FMAP_UNION])) sfb_imp)``,


SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_INSERT, BAG_UNION_INSERT, BAG_UNION_EMPTY,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition] THEN
REPEAT STRIP_TAC THEN
`FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [FEVERY_DEF] THEN
   METIS_TAC[]
) THEN
`EVERY (\t. 
   (t IN FDOM L) /\ (t IN FDOM L') /\
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (L ' t) /\
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (L' ' t)) l'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [FEVERY_DEF, EVERY_MEM] THEN
   METIS_TAC[]
) THEN

`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
      (holfoot_ap_points_to e L')` by ALL_TAC THEN1 (
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to THEN
   FULL_SIMP_TAC std_ss [FEVERY_DEF]
) THEN
Q.ABBREV_TAC `eq_pred = 
  (asl_bigstar_list holfoot_separation_combinator
     ((MAP (\t. var_res_prop_equal DISJOINT_FMAP_UNION (L ' t) (L' ' t)) l')++
      [var_res_prop_stack_true DISJOINT_FMAP_UNION]))` THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) eq_pred` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `eq_pred` THEN
   REWRITE_TAC [holfoot_separation_combinator_def] THEN
   MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list) THEN
   SIMP_TAC list_ss [DISJ_IMP_THM, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      FORALL_AND_THM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM]
) THEN
ASM_REWRITE_TAC[] THEN
`eq_pred = \x. (SND x = FEMPTY) /\ EVERY (\t. (IS_SOME ((L ' t) (FST x))) /\
   IS_SOME ((L' ' t) (FST x)) /\ (THE ((L ' t) (FST x)) = (THE ((L' ' t) (FST x))))) l'` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `eq_pred` THEN
   Q.PAT_ASSUM `EVERY X l'` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [EXTENSION, EVERY_MEM, IN_ABS] THEN
   Induct_on `l'` THEN1 (
      SIMP_TAC list_ss [asl_bigstar_list_REWRITE, asl_star___PROPERTIES,
         IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
      SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE, asl_emp_DISJOINT_FMAP_UNION, 
         IN_SING, IN_ABS]
   ) THEN

   SIMP_TAC list_ss [asl_bigstar_list_REWRITE, DISJ_IMP_THM, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.MATCH_ABBREV_TAC `x IN asl_star holfoot_separation_combinator P1 P2 = XXX` THEN
   Q.UNABBREV_TAC `XXX` THEN
   Tactical.REVERSE (
      `VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [holfoot_separation_combinator_def,
         asl_star___VAR_RES_IS_STACK_IMPRECISE] THEN
      Q.UNABBREV_TAC `P1` THEN
      ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS,
         asl_emp_DISJOINT_FMAP_UNION, IN_SING, DISJOINT_FMAP_UNION___FEMPTY] THEN
      SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
      Cases_on `L ' h (FST x)` THEN
      Cases_on `L' ' h (FST x)` THEN
      SIMP_TAC std_ss []
   ) THEN
   Q.UNABBREV_TAC `P1` THEN Q.UNABBREV_TAC `P2` THEN
   EXT_CONSEQ_REWRITE_TAC [] [holfoot_separation_combinator_def] ([], 
      [VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
       MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list], []) THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      IS_SEPARATION_COMBINATOR___FINITE_MAP,
      VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true,
      MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal]
) THEN
Q.PAT_ASSUM `var_res_prop___PROP f X Y s` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_UNION, var_res_prop___COND_INSERT,
   IN_ABS, DISJOINT_FMAP_UNION___FEMPTY,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN

REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

Q.PAT_ASSUM `(FST s, s1) IN X` MP_TAC THEN

ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def,
   IN_ABS, LET_THM] THEN

Tactical.REVERSE (Cases_on `?ve. e (FST s) = SOME ve`) THEN1 (
   Cases_on `e (FST s)` THEN FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

REPEAT STRIP_TAC THEN
`s1' = s1` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, IN_SING] THEN
   FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE] THEN
   `(s1' ' ve = (FUNION s1' s2') ' ve) /\
    (s1 ' ve = (FUNION s1 s2) ' ve)` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [FUNION_DEF, IN_SING]
   ) THEN
   ASM_REWRITE_TAC[] 
) THEN
ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC std_ss [FEVERY_DEF, EVERY_MEM] THEN
EQ_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [],
   
   Cases_on `MEM x l'` THEN1 FULL_SIMP_TAC std_ss [] THEN
   `L' ' x = L ' x` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss []
]);








val VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP = store_thm ("VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP",
``!l' L L' e wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (wpb + rpb)) e /\
FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L /\
FEVERY (\x. ~(MEM (FST x) l') \/ VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L' /\
(FEVERY (\ (t,a). (t IN FDOM L) /\ ((MEM t l') \/ (a = L ' t))) L') /\
(EVERY (\t. t IN FDOM L') l')  ==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' sfb_context
 (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
 (BAG_INSERT (holfoot_ap_points_to e L') sfb_imp) sfb_restP) =

 (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
 (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
 sfb_split (BAG_INSERT (asl_bigstar_list holfoot_separation_combinator     
    ((MAP (\t. var_res_prop_equal DISJOINT_FMAP_UNION (L ' t) (L' ' t)) l')++
     [var_res_prop_stack_true DISJOINT_FMAP_UNION])) sfb_imp) sfb_restP))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP___REWRITE THEN
ASM_REWRITE_TAC[]);


val VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP_NULL___REWRITE = prove (
``!L L' e wpb rpb sfb_context sfb_split sfb_imp.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (wpb + rpb)) e /\
FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L /\
(FEVERY (\ (t,a). (t IN FDOM L) /\ (a = L ' t)) L') ==>

VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) sfb_context
 (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
 (BAG_INSERT (holfoot_ap_points_to e L') sfb_imp) 

 (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
 sfb_split sfb_imp``,

REPEAT STRIP_TAC THEN
MP_TAC (SIMP_RULE list_ss []
   (Q.SPECL [`[]:holfoot_tag list`, `L`, `L'`, `e`, `wpb`, `rpb`, `sfb_context`, 
         `sfb_split`, `sfb_imp`] VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP___REWRITE)) THEN
ASM_REWRITE_TAC [] THEN
SIMP_TAC std_ss [asl_bigstar_list_REWRITE, asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
   FEVERY_DEF, VAR_RES_FRAME_SPLIT___REWRITE_OK___stack_true]);




val VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP_NULL = 
store_thm ("VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP_NULL",
``!L L' e wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (wpb + rpb)) e /\
FEVERY (\x. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
   (SET_OF_BAG (wpb + rpb)) (SND x)) L /\
FEVERY (\ (t,a). (t IN FDOM L) /\ (a = L ' t)) L' ==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_points_to e L') sfb_imp) sfb_restP) =
 (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split sfb_imp
   sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP_NULL___REWRITE THEN
ASM_REWRITE_TAC[]);


    



(*-----------------
 * Trees
 *-----------------*)

val holfoot_ap_data_tree_seg_defn = Defn.Hol_defn "holfoot_ap_data_tree_seg" `
  (holfoot_ap_data_tree_seg tagL startExp (dtagL, leaf) endExpP =
      if ALL_DISTINCT (tagL++dtagL) then endExpP startExp else asl_false) /\
  (holfoot_ap_data_tree_seg tagL startExp (dtagL, node v tL) endExpP =
  asl_exists lL. if ((LENGTH lL = LENGTH tagL) /\ (LENGTH v = LENGTH dtagL) /\
                     (LENGTH tL = LENGTH tagL) /\ ALL_DISTINCT (tagL++dtagL)) then
    (asl_bigstar_list holfoot_separation_combinator ((holfoot_ap_points_to startExp (LIST_TO_FMAP (ZIP (tagL++dtagL, (MAP var_res_exp_const (lL++v))))))::
       ((MAP (\ (l,t). holfoot_ap_data_tree_seg tagL (var_res_exp_const l) (dtagL, t) endExpP) (ZIP (lL, tL))) ++
        (MAP (\l. var_res_prop_unequal DISJOINT_FMAP_UNION (var_res_exp_const l) startExp) lL))))
    else asl_false)`;


val (holfoot_ap_data_tree_seg_def,_) =
Defn.tprove (holfoot_ap_data_tree_seg_defn,
Q.EXISTS_TAC `measure (\ (tag,startExp,(dtagL,t),endExpP). tree_size0 t)` THEN
REWRITE_TAC[prim_recTheory.WF_measure] THEN
SIMP_TAC (std_ss++CONJ_ss) [prim_recTheory.measure_thm, MEM_ZIP] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC DIRECT_SUBTREES_size THEN
SIMP_TAC std_ss [DIRECT_SUBTREES_EXISTS, tree_11] THEN
PROVE_TAC[MEM_EL]);

val _ = save_thm ("holfoot_ap_data_tree_seg_def", holfoot_ap_data_tree_seg_def);

val holfoot_ap_data_tree___WELL_FORMED_DATA_def =
Define `holfoot_ap_data_tree___WELL_FORMED_DATA tagL data =
((TREE_EVERY (\v. LENGTH v = LENGTH (FST data)) (SND data)) /\
 (NARY (SND data) (LENGTH tagL)) /\
 (ALL_DISTINCT (tagL++(FST data))))`;

val holfoot_ap_data_tree_seg___TREE_PROPS = store_thm ("holfoot_ap_data_tree_seg___TREE_PROPS",
``
!t tagL startExp endExpP dtagL.
(~(holfoot_ap_data_tree___WELL_FORMED_DATA tagL (dtagL, t))) ==>
(holfoot_ap_data_tree_seg tagL startExp (dtagL, t) endExpP = asl_false)``,

HO_MATCH_MP_TAC tree_INDUCT THEN
SIMP_TAC std_ss [NARY_REWRITE, TREE_EVERY_EXISTS_REWRITE,
                 holfoot_ap_data_tree___WELL_FORMED_DATA_def,
                 DISJ_IMP_THM, FORALL_AND_THM, asl_exists_ELIM,
                 holfoot_ap_data_tree_seg_def] THEN
SIMP_TAC std_ss [GSYM DISJ_IMP_THM, GSYM FORALL_AND_THM,
                 NOT_EVERY, GSYM SOME_EL_DISJ] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL, COND_RAND, COND_RATOR] THEN
CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `x IN X` MP_TAC THEN
MATCH_MP_TAC (prove (``(X = asl_false) ==> (x IN X ==> F)``,
                       SIMP_TAC std_ss [asl_false_def, NOT_IN_EMPTY])) THEN
MATCH_MP_TAC asl_bigstar_list_false THEN
FULL_SIMP_TAC list_ss [MEM_MAP, MEM_ZIP, GSYM RIGHT_FORALL_IMP_THM,
                       AND_IMP_INTRO, EVERY_MEM,
                       GSYM RIGHT_EXISTS_AND_THM, MEM_EL,
                       GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
DISJ2_TAC THEN DISJ1_TAC THEN
FULL_SIMP_TAC std_ss [EXISTS_MEM, MEM_EL] THEN (
   Q.EXISTS_TAC `n'` THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_SYM THEN
   Q.PAT_ASSUM `!tagL' startExp. X` MATCH_MP_TAC THEN
   PROVE_TAC[]
));




val holfoot_ap_data_tree_def = Define `
  holfoot_ap_data_tree tagL startExp data =
  holfoot_ap_data_tree_seg tagL startExp data (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_const 0))`;


val holfoot_ap_tree_def = Define `
   holfoot_ap_tree tagL startExp =
   asl_exists dataTree. holfoot_ap_data_tree tagL startExp ([],dataTree)`;


val holfoot_ap_bintree_def = Define `
   holfoot_ap_bintree (lt,rt) startExp =
   holfoot_ap_tree [lt;rt] startExp`;



val holfoot_ap_data_tree___TREE_PROPS = store_thm ("holfoot_ap_data_tree___TREE_PROPS",
``!t tagL startExp dtagL.
(~(holfoot_ap_data_tree___WELL_FORMED_DATA tagL (dtagL, t))) ==>
(holfoot_ap_data_tree tagL startExp (dtagL, t) = asl_false)``,
SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg___TREE_PROPS]);


val holfoot_ap_tree___TREE_PROPS = store_thm ("holfoot_ap_tree___TREE_PROPS",
``!tagL startExp. ~(ALL_DISTINCT tagL) ==>
(holfoot_ap_tree tagL startExp = asl_false)``,
SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_tree_def] THEN
SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
POP_ASSUM MP_TAC THEN
Cases_on `dataTree` THEN (
   ASM_SIMP_TAC list_ss [holfoot_ap_data_tree_seg_def, asl_bool_EVAL]
));


val holfoot_ap_data_tree___null = store_thm ("holfoot_ap_data_tree___null",
``!tagL data. holfoot_ap_data_tree tagL (var_res_exp_const 0) data =
              var_res_bool_proposition DISJOINT_FMAP_UNION (IS_LEAF (SND data) /\
                     ALL_DISTINCT (tagL ++ FST data))``,

Cases_on `data` THEN
Cases_on `r` THEN (
   SIMP_TAC std_ss [holfoot_ap_data_tree_def,
      holfoot_ap_data_tree_seg_def, IS_LEAF_def,
      var_res_prop_equal_unequal_REWRITES,
      COND_RAND, COND_RATOR,
      var_res_bool_proposition_TF,
      holfoot_ap_points_to___null,
      asl_bigstar_list_false, MEM, 
      asl_exists_ELIM]
));

val holfoot_ap_tree___null = store_thm ("holfoot_ap_tree___null",
``!tagL. holfoot_ap_tree tagL (var_res_exp_const 0) =
         var_res_bool_proposition DISJOINT_FMAP_UNION (ALL_DISTINCT tagL)``,
SIMP_TAC list_ss [holfoot_ap_tree_def, holfoot_ap_data_tree___null,
   EXTENSION, asl_bool_EVAL, var_res_bool_proposition_REWRITE, IN_ABS,
   IS_LEAF_REWRITE]);

val holfoot_ap_bintree___null = store_thm ("holfoot_ap_bintree___null",
``!lt rt. holfoot_ap_bintree (lt, rt) (var_res_exp_const 0) =
          var_res_bool_proposition DISJOINT_FMAP_UNION (~(lt = rt))``,
SIMP_TAC list_ss [holfoot_ap_bintree_def, holfoot_ap_tree___null])


val holfoot_ap_data_tree___leaf = store_thm ("holfoot_ap_data_tree___leaf",
``!tagL e dtagL. holfoot_ap_data_tree tagL e (dtagL, leaf) =
       asl_trivial_cond (ALL_DISTINCT (tagL ++ dtagL))
           (var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0))``,
SIMP_TAC std_ss [holfoot_ap_data_tree_def,
   holfoot_ap_data_tree_seg_def,
   asl_trivial_cond_def,
   var_res_prop_equal_symmetric]);

val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree_seg =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree_seg",

``!vs tagL startExp data endExpP.

((!se. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs se ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (endExpP se)) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp) ==>

VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
   (holfoot_ap_data_tree_seg tagL startExp data endExpP)``,


REPEAT STRIP_TAC THEN
`?dtagL t. data = (dtagL,t)` by (Cases_on `data` THEN SIMP_TAC std_ss []) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs X` MP_TAC THEN
Q.SPEC_TAC (`startExp`, `startExp`) THEN
Q.SPEC_TAC (`t`, `t`) THEN
HO_MATCH_MP_TAC tree_INDUCT THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_seg_def,
      COND_RAND, COND_RATOR,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false]
) THEN

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_seg_def] THEN
HO_MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `lL` THEN
ASM_SIMP_TAC std_ss [holfoot_separation_combinator_def] THEN

MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list) THEN
ASM_SIMP_TAC list_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP, DISJ_IMP_THM,
   FORALL_AND_THM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
   MEM_ZIP] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FEVERY_LIST_TO_FMAP THEN
   ASM_SIMP_TAC list_ss [EVERY_MEM, MEM_ZIP,
     GSYM LEFT_FORALL_IMP_THM] THEN
   ASM_SIMP_TAC arith_ss [EL_MAP, GSYM MAP_APPEND, LENGTH_MAP, LENGTH_APPEND,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL],


   Q.PAT_ASSUM `EVERY X Y` MP_TAC THEN
   ASM_SIMP_TAC std_ss [EVERY_MEM, MEM_EL, GSYM LEFT_FORALL_IMP_THM,
      GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `n'` THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL],


   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal THEN
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
]);




val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree_seg =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree_seg",
``!tagL startExp data endExpP.
((!se. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS se) ==>
       VAR_RES_IS_STACK_IMPRECISE (endExpP se)) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp)) ==>

VAR_RES_IS_STACK_IMPRECISE
   (holfoot_ap_data_tree_seg tagL startExp data endExpP)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree_seg]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree",
``!vs tagL startExp data.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
   (holfoot_ap_data_tree tagL startExp data)``,

SIMP_TAC std_ss [holfoot_ap_data_tree_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree_seg THEN
ASM_REWRITE_TAC[] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]);



val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree",
``!tagL startExp data.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) ==>
VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_data_tree tagL startExp data)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree",
``!vs tagL startExp.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
   (holfoot_ap_tree tagL startExp)``,

SIMP_TAC std_ss [holfoot_ap_tree_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree THEN
ASM_REWRITE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_tree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_tree",
``!tagL startExp.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) ==>
VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_tree tagL startExp)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_bintree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_bintree",
``!vs lt rt startExp.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
   (holfoot_ap_bintree (lt,rt) startExp)``,

SIMP_TAC std_ss [holfoot_ap_bintree_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree THEN
ASM_REWRITE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_bintree =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_bintree",
``!lt rt startExp.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) ==>
VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_bintree (lt,rt) startExp)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_bintree]);



val holfoot_ap_data_tree___implies_in_heap_or_null___SIMPLE_THM =
store_thm ("holfoot_ap_data_tree___implies_in_heap_or_null___SIMPLE_THM",
``!tagL st h data c. (st, h) IN holfoot_ap_data_tree tagL (var_res_exp_const c) data ==>
   ~(c = 0) ==> (c IN FDOM h)``,
   Cases_on `data` THEN Cases_on `r` THEN
   SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg_def,
      COND_RAND, COND_RATOR, asl_bool_EVAL, var_res_prop_equal_unequal_EXPAND,
      IN_ABS, var_res_exp_const_def, LET_THM, asl_bigstar_list_REWRITE,
      asl_star_def, holfoot_ap_points_to_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM, IN_SING,
      SOME___holfoot_separation_combinator, FDOM_FUNION, IN_UNION]
);


val holfoot_ap_data_tree___REWRITE = store_thm ("holfoot_ap_data_tree___REWRITE",
``!tagL e dtagL data. 
      IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==> 
      (holfoot_ap_data_tree tagL e (dtagL, data) =
      asl_or
        (asl_trivial_cond (ALL_DISTINCT (tagL ++ dtagL) /\ IS_LEAF data)
           (var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0)))

        (asl_exists_list dtagL (\v.
        asl_exists_list tagL (\lL.
        asl_exists_list tagL (\tL.
        asl_trivial_cond ((NULL tagL ==> ALL_DISTINCT dtagL) /\ (data = node v tL))
           (asl_bigstar_list holfoot_separation_combinator
             (holfoot_ap_points_to e
                (LIST_TO_FMAP
                   (ZIP (tagL ++ dtagL,MAP var_res_exp_const (lL ++ v))))::
                  (MAP
                     (\lt.
                        holfoot_ap_data_tree tagL (var_res_exp_const (FST lt))
                          (dtagL,SND lt)) (ZIP (lL,tL))))))))))``,

Cases_on `data` THEN (
   SIMP_TAC std_ss [holfoot_ap_data_tree___leaf, tree_distinct,
      asl_trivial_cond_TF, IS_LEAF_REWRITE] THEN
   SIMP_TAC std_ss [asl_exists_list___ELIM, asl_trivial_cond___asl_false,
      asl_exists_ELIM, asl_bool_REWRITES]
) THEN
SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg_def,
   asl_exists_def, asl_trivial_cond_def, COND_RAND, COND_RATOR,
   asl_bool_EVAL, IN_ABS, tree_11, GSYM RIGHT_EXISTS_AND_THM] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS] THEN 
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [GSYM holfoot_ap_data_tree_def] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `ALL_DISTINCT (tagL ++ dtagL)`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `tagL` THEN1 FULL_SIMP_TAC list_ss [] THEN
   `!l t'. holfoot_ap_data_tree (h::t) (var_res_exp_const l) (dtagL,t') = asl_false` by ALL_TAC THEN1 (
      Cases_on `t'` THEN
      ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg_def,
        asl_exists_ELIM]
   ) THEN
   `?x1' xs'. x' = x1'::xs'` by (Cases_on `x'` THEN FULL_SIMP_TAC list_ss []) THEN
   `?l1 ls. l = l1::ls` by (Cases_on `l` THEN FULL_SIMP_TAC list_ss []) THEN
   ASM_SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
      asl_false___asl_star_THM, asl_bool_EVAL]
) THEN
`ALL_DISTINCT dtagL` by FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND] THEN
Cases_on `NULL tagL` THEN1 (
   FULL_SIMP_TAC list_ss [NULL_EQ, LENGTH_NIL]
) THEN
`~(NULL x') /\ ~(NULL l)` by ALL_TAC THEN1 (
   Cases_on `tagL` THEN 
   FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
) THEN
ASM_SIMP_TAC std_ss [asl_bigstar_list_REWRITE,
   asl_bigstar_list_APPEND, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
Q.MATCH_ABBREV_TAC `x IN asl_star holfoot_separation_combinator
   points_toP (asl_star holfoot_separation_combinator 
     (asl_bigstar_list holfoot_separation_combinator treePL) 
     (asl_bigstar_list holfoot_separation_combinator unequalPL)) = 
   x IN asl_star holfoot_separation_combinator
      points_toP (asl_bigstar_list holfoot_separation_combinator treePL')` THEN
Q.ABBREV_TAC `treeP = asl_bigstar_list holfoot_separation_combinator treePL` THEN
Q.ABBREV_TAC `unequalP = asl_bigstar_list holfoot_separation_combinator unequalPL` THEN

`treePL' = treePL` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`treePL`, `treePL'`] THEN
   SIMP_TAC std_ss [pairTheory.ELIM_UNCURRY]
) THEN
ASM_SIMP_TAC std_ss [] THEN
POP_ASSUM (K ALL_TAC) THEN Q.UNABBREV_TAC `treePL'` THEN
REWRITE_TAC [holfoot_separation_combinator_def] THEN 

`EVERY VAR_RES_IS_STACK_IMPRECISE treePL /\
 EVERY VAR_RES_IS_STACK_IMPRECISE unequalPL` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `treePL` THEN
   Q.UNABBREV_TAC `unequalPL` THEN
   ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [EVERY_MAP,
      VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree, EVERY_MEM]
) THEN
`VAR_RES_IS_STACK_IMPRECISE points_toP /\
 VAR_RES_IS_STACK_IMPRECISE treeP /\
 VAR_RES_IS_STACK_IMPRECISE unequalP` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `points_toP` THEN
   Q.UNABBREV_TAC `treeP` THEN
   Q.UNABBREV_TAC `unequalP` THEN
   
   REWRITE_TAC[holfoot_separation_combinator_def] THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___points_to,
       FEVERY_LIST_TO_FMAP, MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list], []) THEN
   FULL_SIMP_TAC arith_ss [EVERY_MEM, MEM_ZIP, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      MEM_ZIP, LENGTH_MAP, LENGTH_APPEND, GSYM LEFT_FORALL_IMP_THM,
      EL_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   Q.UNABBREV_TAC `treePL` THEN Q.UNABBREV_TAC `unequalPL` THEN
   FULL_SIMP_TAC std_ss [NULL_EQ, MAP_EQ_NIL] THEN
   Cases_on `x'` THEN FULL_SIMP_TAC list_ss [] THEN
   Cases_on `l` THEN FULL_SIMP_TAC list_ss []
) THEN

ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   VAR_RES_IS_STACK_IMPRECISE___asl_star,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   IN_ABS, DISJOINT_FMAP_UNION___REWRITE] THEN
Cases_on `e (FST x) = NONE` THEN1 (
   Q.UNABBREV_TAC `points_toP` THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM]
) THEN
`?ec. e (FST x) = SOME ec` by ALL_TAC THEN1 (
   Cases_on `e (FST x)` THEN FULL_SIMP_TAC std_ss []
) THEN
`!h. (FST x, h) IN unequalP =
     (h = FEMPTY) /\ EVERY (\x. ~(x = ec)) x'` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `unequalP` THEN
   Q.UNABBREV_TAC `unequalPL` THEN
   Q.PAT_ASSUM `IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` MP_TAC THEN
   Q.PAT_ASSUM `e (FST x) = SOME ec` MP_TAC THEN
   Q.PAT_ASSUM `~(NULL x')` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Induct_on `x'` THEN SIMP_TAC list_ss [asl_bigstar_list_REWRITE] THEN
   REPEAT STRIP_TAC THEN 
   Cases_on `x'` THEN1 (
     FULL_SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
        asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
        var_res_prop_equal_unequal_EXPAND, IN_ABS, var_res_exp_const_def,
        asl_emp_DISJOINT_FMAP_UNION, IN_SING]
   ) THEN
   Q.ABBREV_TAC `PP = asl_bigstar_list holfoot_separation_combinator
         (MAP (\l. var_res_prop_unequal DISJOINT_FMAP_UNION (var_res_exp_const l) e) (h''::t))` THEN
   `VAR_RES_IS_STACK_IMPRECISE PP` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `PP` THEN
       REWRITE_TAC [holfoot_separation_combinator_def] THEN
       MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list) THEN
       ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
           MEM_MAP, GSYM LEFT_FORALL_IMP_THM, MAP_EQ_NIL, 
           VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal, NOT_CONS_NIL,
           IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
   ) THEN
   FULL_SIMP_TAC list_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, holfoot_separation_combinator_def,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      IN_ABS] THEN
   ASM_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___FEMPTY, var_res_prop_equal_unequal_EXPAND,
      IN_ABS, asl_emp_DISJOINT_FMAP_UNION, IN_SING, var_res_exp_const_def] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []
) THEN
ASM_SIMP_TAC std_ss [FDOM_FEMPTY, FUNION_FEMPTY_1, FUNION_FEMPTY_2,
   DISJOINT_EMPTY] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

`(FDOM es1 = {ec}) /\ ~(ec = 0)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(FST x, es1) IN Y` MP_TAC THEN
   Q.UNABBREV_TAC `points_toP` THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM]
) THEN
`EVERY (\x. ~(x = 0) ==> (x IN FDOM es2)) x'` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(FST x, es2) IN treeP` MP_TAC THEN
   Q.PAT_ASSUM `EVERY X treePL` MP_TAC THEN
   `LENGTH l = LENGTH x'` by ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
   Q.PAT_ASSUM `~NULL x'` MP_TAC THEN
   Q.UNABBREV_TAC `treeP` THEN
   Q.UNABBREV_TAC `treePL` THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Q.SPEC_TAC (`es2`, `h`) THEN
   Q.SPEC_TAC (`l`, `l`) THEN
   Induct_on `x'` THEN (
      SIMP_TAC list_ss [LENGTH_EQ_NUM,
         GSYM LEFT_FORALL_IMP_THM, asl_bigstar_list_REWRITE,
         holfoot_separation_combinator_def]
   ) THEN
   Cases_on `x'` THEN1 (
      FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM, asl_bigstar_list_REWRITE,
        asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___FINITE_MAP,
        IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
      METIS_TAC[holfoot_ap_data_tree___implies_in_heap_or_null___SIMPLE_THM]
   ) THEN
   REPEAT GEN_TAC THEN
   Q.PAT_ASSUM `!l. X l` (ASSUME_TAC o Q.SPEC `l'`) THEN
   REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
   FULL_SIMP_TAC list_ss [holfoot_separation_combinator_def] THEN
   Q.ABBREV_TAC `PP = asl_bigstar_list (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
               (MAP (\ (l,t). holfoot_ap_data_tree tagL (var_res_exp_const l)
                    (dtagL,t)) (ZIP (h::t,l')))` THEN
   `VAR_RES_IS_STACK_IMPRECISE PP` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `PP` THEN
      MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list) THEN
      FULL_SIMP_TAC list_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM, MAP_EQ_NIL,
        EVERY_MEM, IS_SEPARATION_COMBINATOR___FINITE_MAP, LENGTH_EQ_NUM]
   ) THEN
   Q.PAT_ASSUM `(FST x, h'') IN X` MP_TAC THEN
   FULL_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS,
      GSYM LEFT_FORALL_IMP_THM, DISJOINT_FMAP_UNION___REWRITE, FDOM_FUNION,
      IN_UNION, EVERY_MEM] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   METIS_TAC[holfoot_ap_data_tree___implies_in_heap_or_null___SIMPLE_THM]
) THEN
FULL_SIMP_TAC std_ss [EVERY_MEM, DISJOINT_DEF, EXTENSION, IN_SING, IN_INTER, NOT_IN_EMPTY] THEN
METIS_TAC[]);



val holfoot_ap_tree___REWRITE = store_thm ("holfoot_ap_tree___REWRITE",
``!tagL e. 
      IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==> 
      (holfoot_ap_tree tagL e =
      asl_or
        (asl_trivial_cond (ALL_DISTINCT tagL)
           (var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0)))

        (asl_exists_list tagL (\lL.
           (asl_bigstar_list holfoot_separation_combinator
             (holfoot_ap_points_to e
                (LIST_TO_FMAP
                   (ZIP (tagL,MAP var_res_exp_const lL)))::
                  (MAP (\l. holfoot_ap_tree tagL (var_res_exp_const l)) lL))))))``,

SIMP_TAC list_ss [holfoot_ap_tree_def, holfoot_ap_data_tree___REWRITE,
   asl_exists_list___REWRITE, asl_exists___asl_or_THM] THEN
REPEAT STRIP_TAC THEN 
BINOP_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL, IS_LEAF_REWRITE,
      asl_trivial_cond_def, COND_RAND, COND_RATOR,
      asl_bool_REWRITES, asl_exists_ELIM]
) THEN
SIMP_TAC std_ss [asl_exists_list_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, asl_exists_def,
   asl_trivial_cond_def, COND_RAND, COND_RATOR, asl_bool_EVAL,
   asl_bigstar_list_REWRITE] THEN
Tactical.REVERSE (`!l P. asl_bigstar_list holfoot_separation_combinator
   (MAP (\l:num. asl_exists (x:num list tree). P l x) l) =
   asl_exists xL.
   asl_trivial_cond (LENGTH xL = LENGTH l) 
      (asl_bigstar_list holfoot_separation_combinator 
          (MAP (\lx. P (FST lx) (SND lx)) (ZIP (l, xL))))` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [asl_exists_def,
      asl_trivial_cond_def, COND_RAND, COND_RATOR, asl_bool_EVAL] THEN
   SIMP_TAC std_ss [EXTENSION, IN_ABS, asl_star_def,
       GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN
Induct_on `l` THEN (
   FULL_SIMP_TAC list_ss [asl_bigstar_list_REWRITE, asl_trivial_cond_def,
      asl_exists_def, COND_RAND, COND_RATOR, asl_bool_EVAL,
      LENGTH_EQ_NUM, IN_ABS3, GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM, asl_star_def, IN_ABS]
) THEN
METIS_TAC[]);



val var_res_prop_varlist_update___holfoot_ap_data_tree =
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_tree",
``!vcL tagL data e.
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  (var_res_prop_varlist_update vcL (holfoot_ap_data_tree tagL e data) =
   (holfoot_ap_data_tree tagL (var_res_exp_varlist_update vcL e) data))``,

NTAC 3 GEN_TAC THEN
`?dtagL data_tree. data = (dtagL, data_tree)` by ALL_TAC THEN1 (
   Cases_on `data` THEN SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

Tactical.REVERSE (Cases_on `holfoot_ap_data_tree___WELL_FORMED_DATA tagL (dtagL, data_tree)`) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_def,
       holfoot_ap_data_tree_seg___TREE_PROPS, var_res_prop_varlist_update___BOOL]
) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`data_tree`, `data_tree`) THEN
HO_MATCH_MP_TAC tree_INDUCT THEN
REPEAT CONJ_TAC THEN1 (
   SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg_def,
      holfoot_ap_data_tree___WELL_FORMED_DATA_def,
      var_res_prop_varlist_update___equal_unequal,
      var_res_exp_varlist_update___const_EVAL]
) THEN
REPEAT STRIP_TAC THEN
`(LENGTH n = LENGTH dtagL) /\
 (LENGTH tL = LENGTH tagL) /\ 
  ALL_DISTINCT (tagL ++ dtagL)` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [holfoot_ap_data_tree___WELL_FORMED_DATA_def,
      TREE_EVERY_EXISTS_REWRITE, NARY_REWRITE]
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_seg_def, holfoot_ap_data_tree_def,
   var_res_prop_varlist_update___BOOL,
   COND_RAND, COND_RATOR] THEN
AP_TERM_TAC THEN ABS_TAC THEN
Tactical.REVERSE (Cases_on `LENGTH lL = LENGTH tagL`) THEN (
   ASM_SIMP_TAC std_ss []   
) THEN

Q.MATCH_ABBREV_TAC `
var_res_prop_varlist_update vcL
   (asl_bigstar_list holfoot_separation_combinator pL) =
(asl_bigstar_list holfoot_separation_combinator pL')` THEN

`pL <> [] /\ (!p. MEM p pL ==> VAR_RES_IS_STACK_IMPRECISE p)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `pL` THEN
   ASM_SIMP_TAC list_ss [MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, MEM_ZIP] THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree_seg,
       VAR_RES_IS_STACK_IMPRECISE___points_to, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
       FEVERY_LIST_TO_FMAP, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal], []) THEN
   ASM_SIMP_TAC list_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      EVERY_MEM, MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC std_ss [GSYM MAP_APPEND] THEN
   REPEAT STRIP_TAC THEN
   `LENGTH dtagL + LENGTH tagL = LENGTH (lL ++ n)` by ASM_SIMP_TAC list_ss [] THEN
   ASM_SIMP_TAC arith_ss [EL_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN   
ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___asl_bigstar_list,
   IS_SEPARATION_COMBINATOR___FINITE_MAP, holfoot_separation_combinator_def] THEN
AP_TERM_TAC THEN


Q.UNABBREV_TAC `pL` THEN Q.UNABBREV_TAC `pL'` THEN
FULL_SIMP_TAC list_ss [MEM_MAP, DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
   FORALL_AND_THM, MAP_MAP_o, combinTheory.o_DEF, APPEND_11_LENGTH] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___holfoot_ap_points_to,
      o_f_LIST_TO_FMAP] THEN
   `LENGTH (tagL ++ dtagL) = LENGTH (lL ++ n)` by ASM_SIMP_TAC list_ss [] THEN
   ASM_SIMP_TAC arith_ss [GSYM MAP_APPEND, ZIP_MAP, MAP_MAP_o,
      combinTheory.o_DEF, var_res_exp_varlist_update___const_EVAL],


   MATCH_MP_TAC (prove (``!L f f'. (!l t. MEM (l,t) L ==> (f (l, t) = f' (l,t))) ==>
        (MAP f L = MAP f' L)``, 
        Induct_on `L` THEN ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, PAIR_FORALL_THM])) THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, GSYM holfoot_ap_data_tree_def] THEN
   REPEAT STRIP_TAC THEN
   `MEM t tL` by ALL_TAC THEN1 (
       Q.PAT_ASSUM `MEM (l,t) (ZIP (lL,tL))` MP_TAC THEN
       ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_IS_EL]
   ) THEN
   `holfoot_ap_data_tree___WELL_FORMED_DATA tagL (dtagL,t)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [holfoot_ap_data_tree___WELL_FORMED_DATA_def,
         NARY_REWRITE, EVERY_MEM, TREE_EVERY_EXISTS_REWRITE]
   ) THEN
   Q.PAT_ASSUM `!data_tree. MEM data_tree tL ==> X` (MP_TAC o Q.SPEC `t`) THEN
   ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      var_res_exp_varlist_update___const_EVAL],


   SIMP_TAC std_ss [var_res_prop_varlist_update___equal_unequal,
       var_res_exp_varlist_update___const_EVAL]
]);


val var_res_prop_varlist_update___holfoot_ap_tree =
store_thm ("var_res_prop_varlist_update___holfoot_ap_tree",
``!vcL tagL e.
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  (var_res_prop_varlist_update vcL (holfoot_ap_tree tagL e) =
   (holfoot_ap_tree tagL (var_res_exp_varlist_update vcL e)))``,

 SIMP_TAC std_ss [holfoot_ap_tree_def, var_res_prop_varlist_update___BOOL,
    var_res_prop_varlist_update___holfoot_ap_data_tree]);


val var_res_prop_varlist_update___holfoot_ap_bintree =
store_thm ("var_res_prop_varlist_update___holfoot_ap_bintree",
``!vcL lt rt e.
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  (var_res_prop_varlist_update vcL (holfoot_ap_bintree (lt,rt) e) =
   (holfoot_ap_bintree (lt,rt) (var_res_exp_varlist_update vcL e)))``,
SIMP_TAC std_ss [holfoot_ap_bintree_def, var_res_prop_varlist_update___holfoot_ap_tree]);


val holfoot_ap_data_tree___implies_in_heap_or_null = store_thm ("holfoot_ap_data_tree___implies_in_heap_or_null",
``!e B tagL data sfb.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  holfoot_implies_in_heap_or_null B
 (BAG_INSERT (holfoot_ap_data_tree tagL e data) sfb) e``,

REPEAT STRIP_TAC THEN
`?dtagL t. data = (dtagL, t)` by (Cases_on `data` THEN SIMP_TAC std_ss []) THEN
Tactical.REVERSE (Cases_on `holfoot_ap_data_tree___WELL_FORMED_DATA tagL (dtagL, t)`) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_def, holfoot_ap_data_tree_seg___TREE_PROPS,
      holfoot_implies_in_heap_or_null_def, holfoot_implies_in_heap_pred___asl_false]
) THEN
FULL_SIMP_TAC std_ss [holfoot_ap_data_tree___WELL_FORMED_DATA_def] THEN
Cases_on `t` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_def,
      holfoot_ap_data_tree_seg_def,
      holfoot_implies_in_heap_or_null___equal_null]
) THEN

ASM_SIMP_TAC std_ss [holfoot_ap_data_tree_def,
   holfoot_ap_data_tree_seg_def, asl_bool_EVAL,
   COND_RAND, COND_RATOR, GSYM LEFT_FORALL_IMP_THM,
   holfoot_implies_in_heap_or_null_def,
   holfoot_implies_in_heap_pred___asl_exists,
   holfoot_implies_in_heap_pred___asl_false,
   asl_bigstar_list_REWRITE,
   holfoot_implies_in_heap_pred___asl_star
] THEN
ASM_SIMP_TAC std_ss [GSYM holfoot_implies_in_heap_or_null_def,
   holfoot_ap_points_to___implies_in_heap_or_null]);


val holfoot_ap_data_tree___implies_in_heap_or_null___COMPUTE = store_thm (
   "holfoot_ap_data_tree___implies_in_heap_or_null___COMPUTE",
``!e tagL data B.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  holfoot_implies_in_heap_or_null B {|holfoot_ap_data_tree tagL e data|} e``,
SIMP_TAC std_ss [holfoot_ap_data_tree___implies_in_heap_or_null]);


val holfoot_ap_tree___implies_in_heap_or_null = store_thm ("holfoot_ap_tree___implies_in_heap_or_null",
``!e B tagL sfb.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  holfoot_implies_in_heap_or_null B
 (BAG_INSERT (holfoot_ap_tree tagL e) sfb) e``,

SIMP_TAC std_ss [holfoot_ap_tree_def,
   holfoot_implies_in_heap_or_null_def,
   holfoot_implies_in_heap_pred___asl_exists] THEN
SIMP_TAC std_ss [GSYM holfoot_implies_in_heap_or_null_def,
   holfoot_ap_data_tree___implies_in_heap_or_null]);



val holfoot_ap_tree___implies_in_heap_or_null___COMPUTE = store_thm (
   "holfoot_ap_tree___implies_in_heap_or_null___COMPUTE",
``!e tagL B.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  holfoot_implies_in_heap_or_null B {|holfoot_ap_tree tagL e|} e``,
SIMP_TAC std_ss [holfoot_ap_tree___implies_in_heap_or_null]);



val holfoot_ap_data_tree___var_res_prop_implies_eq___split = 
store_thm ("holfoot_ap_data_tree___var_res_prop_implies_eq___split",
``!tagL e1 dtagL data sfb1 sfb2 wpb rpb.
  (var_res_implies_unequal DISJOINT_FMAP_UNION (BAG_UNION
     sfb1 (BAG_INSERT (holfoot_ap_data_tree tagL e1 (dtagL, data)) sfb2)) e1 (var_res_exp_const 0)) ==>

  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
        (SET_OF_BAG (BAG_UNION wpb rpb)) e1  ==>

  (var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb, rpb) sfb1
     (BAG_INSERT (holfoot_ap_data_tree tagL e1 (dtagL, data)) sfb2) 

     (BAG_INSERT (asl_exists_list dtagL (\v. asl_exists_list tagL (\lL. asl_exists_list tagL (\tL.
                  asl_trivial_cond ((NULL tagL ==> ALL_DISTINCT dtagL) /\ (data = node v tL))
                     (asl_bigstar_list holfoot_separation_combinator
                        (holfoot_ap_points_to e1 (LIST_TO_FMAP (ZIP (tagL ++ dtagL, MAP var_res_exp_const (lL ++ v))))::
                        MAP (\lt. holfoot_ap_data_tree tagL
                            (var_res_exp_const (FST lt)) (dtagL,(SND lt))) (ZIP (lL,tL)))))))) 
      sfb2))``,

REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC `
   var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb,rpb) sfb1
      (BAG_INSERT (holfoot_ap_data_tree tagL e1 (dtagL,data)) sfb2)
      (BAG_INSERT PP sfb2)` THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) 
     (holfoot_ap_data_tree tagL e1 (dtagL,data))` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree]
) THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) PP` by ALL_TAC THEN1 ( 
   Q.UNABBREV_TAC `PP` THEN
   ASM_SIMP_TAC std_ss [asl_exists_list___ELIM, holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list], []) THEN
   SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [
      GSYM RIGHT_FORALL_IMP_THM, MEM_MAP, FORALL_AND_THM,
      DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      MEM, NOT_CONS_NIL] THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
          FEVERY_LIST_TO_FMAP, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree], []) THEN
   ASM_SIMP_TAC arith_ss [EVERY_MEM, MEM_ZIP, LENGTH_MAP, LENGTH_APPEND,
      GSYM LEFT_FORALL_IMP_THM, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
      EL_MAP]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop_implies_eq_def, var_res_prop___EQ,
   var_res_prop___COND_UNION, var_res_prop___COND_INSERT] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
      BAG_UNION_INSERT, IN_ABS,
      var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
   REPEAT STRIP_TAC THEN
   Q.LIST_EXISTS_TAC [`s1`, `s2`] THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE, asl_bool_EVAL]
) THEN
STRIP_TAC THEN
`(x:holfoot_state) IN var_res_prop_weak_unequal e1 (var_res_exp_const 0)` by ALL_TAC THEN1 (
   MATCH_MP_TAC (ISPECL [``DISJOINT_FMAP_UNION:holfoot_heap bin_option_function``,
       ``e1:holfoot_a_expression``]
       var_res_implies_unequal___var_res_prop___PROP) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   METIS_TAC[]
) THEN
REPEAT (Q.PAT_ASSUM `x IN XXX` MP_TAC) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_INSERT, var_res_prop_equal_unequal_EXPAND,
   IN_ABS, var_res_exp_const_def,
   var_res_prop___PROP_INSERT, var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT] THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE, asl_bool_EVAL,
   asl_trivial_cond_def, var_res_prop_equal_unequal_EXPAND,
   COND_RAND, COND_RATOR, IN_ABS, var_res_exp_const_def, 
   asl_emp_DISJOINT_FMAP_UNION, DISJOINT_FMAP_UNION___FEMPTY, IN_SING] THEN
METIS_TAC[]);




val holfoot_ap_tree___var_res_prop_implies_eq___split = 
store_thm ("holfoot_ap_tree___var_res_prop_implies_eq___split",
``!tagL e1 sfb1 sfb2 wpb rpb.
  (var_res_implies_unequal DISJOINT_FMAP_UNION (BAG_UNION
     sfb1 (BAG_INSERT (holfoot_ap_tree tagL e1) sfb2)) e1 (var_res_exp_const 0)) ==>

  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
        (SET_OF_BAG (BAG_UNION wpb rpb)) e1  ==>

  (var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb, rpb) sfb1
     (BAG_INSERT (holfoot_ap_tree tagL e1) sfb2) 

     (BAG_INSERT (asl_exists_list tagL (\lL.
                  asl_bigstar_list holfoot_separation_combinator
                    (holfoot_ap_points_to e1 (LIST_TO_FMAP (ZIP (tagL,MAP var_res_exp_const lL)))::
                    MAP (\l. holfoot_ap_tree tagL (var_res_exp_const l)) lL)))
      sfb2))``,

REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC `
   var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb,rpb) sfb1
      (BAG_INSERT (holfoot_ap_tree tagL e1) sfb2)
      (BAG_INSERT PP sfb2)` THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) 
     (holfoot_ap_tree tagL e1)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree]
) THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) PP` by ALL_TAC THEN1 ( 
   Q.UNABBREV_TAC `PP` THEN
   ASM_SIMP_TAC std_ss [asl_exists_list___ELIM, holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list], []) THEN
   SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [
      GSYM RIGHT_FORALL_IMP_THM, MEM_MAP, FORALL_AND_THM,
      DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      MEM, NOT_CONS_NIL] THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
          FEVERY_LIST_TO_FMAP, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree], []) THEN
   ASM_SIMP_TAC arith_ss [EVERY_MEM, MEM_ZIP, LENGTH_MAP, LENGTH_APPEND,
      GSYM LEFT_FORALL_IMP_THM, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
      EL_MAP]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop_implies_eq_def, var_res_prop___EQ,
   var_res_prop___COND_UNION, var_res_prop___COND_INSERT] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
      BAG_UNION_INSERT, IN_ABS,
      var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
   REPEAT STRIP_TAC THEN
   Q.LIST_EXISTS_TAC [`s1`, `s2`] THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_tree___REWRITE, asl_bool_EVAL]
) THEN
STRIP_TAC THEN
`(x:holfoot_state) IN var_res_prop_weak_unequal e1 (var_res_exp_const 0)` by ALL_TAC THEN1 (
   MATCH_MP_TAC (ISPECL [``DISJOINT_FMAP_UNION:holfoot_heap bin_option_function``,
       ``e1:holfoot_a_expression``]
       var_res_implies_unequal___var_res_prop___PROP) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   METIS_TAC[]
) THEN
REPEAT (Q.PAT_ASSUM `x IN XXX` MP_TAC) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_INSERT, var_res_prop_equal_unequal_EXPAND,
   IN_ABS, var_res_exp_const_def,
   var_res_prop___PROP_INSERT, var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT] THEN
ASM_SIMP_TAC std_ss [holfoot_ap_tree___REWRITE, asl_bool_EVAL,
   asl_trivial_cond_def, var_res_prop_equal_unequal_EXPAND,
   COND_RAND, COND_RATOR, IN_ABS, var_res_exp_const_def,
   asl_emp_DISJOINT_FMAP_UNION, DISJOINT_FMAP_UNION___FEMPTY, IN_SING] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___points_to___data_tree___REWRITE = prove (
``!v tL e tagL dtagL data L wpb rpb sfb_context sfb_split sfb_imp.

(LIST_TO_SET (tagL++dtagL) SUBSET FDOM L) /\ ~(NULL tagL) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L)
==>
 VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data)) sfb_imp) 


   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split
   (BAG_INSERT (asl_exists_list dtagL (\v. asl_exists_list tagL (\lL. asl_exists_list tagL (\tL.
    (asl_trivial_cond (data = node v tL)
     (asl_bigstar_list holfoot_separation_combinator 
        ((MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (SND x)))) (ZIP (tagL++dtagL, lL++v))++
          MAP (\lt. holfoot_ap_data_tree tagL
            (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,tL))))))))) sfb_imp)``,

REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT,
   BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN

MATCH_MP_TAC (prove (``((A /\ A') /\ (A /\ A' ==> (B = B'))) ==> ((A ==> B) = (A' ==> B'))``,
   SIMP_TAC (std_ss++CONJ_ss) [])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [asl_exists_list___ELIM, holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list], []) THEN
   ASM_SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM,
      MEM_MAP,  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
      PAIR_FORALL_THM] THEN
   REPEAT STRIP_TAC THEN1 (
      Cases_on `tagL` THEN
      FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
   ) THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
   Tactical.REVERSE (`x1 IN FDOM L` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [FEVERY_DEF, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
   ) THEN
   Tactical.REVERSE (`MEM x1 (tagL ++ dtagL)` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET]
   ) THEN
   Q.PAT_ASSUM `MEM x Y` MP_TAC THEN
   ASM_SIMP_TAC arith_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
       LENGTH_APPEND, EL_IS_EL]
) THEN
STRIP_TAC THEN
Q.PAT_ASSUM `var_res_prop___PROP DISJOINT_FMAP_UNION f X s` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
ASM_SIMP_TAC std_ss [IN_ABS, asl_exists_list___ELIM,
   GSYM RIGHT_EXISTS_AND_THM, asl_bool_EVAL, GSYM LEFT_EXISTS_AND_THM,
   DISJOINT_FMAP_UNION___REWRITE,
   asl_bigstar_list_APPEND, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
REPEAT STRIP_TAC THEN
`?ec. (e (FST s) = SOME ec) /\ ~(ec = 0)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(FST s, _) IN holfoot_ap_points_to e L` MP_TAC THEN
   SIMP_TAC std_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS] THEN
   Cases_on `e (FST s)` THEN SIMP_TAC std_ss []
) THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
`!h. ~((FST s, h:holfoot_heap) IN var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0))` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS, var_res_exp_const_def]
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE,
   asl_bool_EVAL, asl_exists_list___ELIM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM] THEN
Tactical.REVERSE (Cases_on `?v tL. data = node v tL`) THEN1 (
   Cases_on `data` THEN FULL_SIMP_TAC std_ss [tree_11, tree_distinct]
) THEN
FULL_SIMP_TAC std_ss [tree_11] THEN
HO_MATCH_MP_TAC (prove (``(!lL s2. ((?s1. X s1 s2 lL) = (?s1 s1'. Y s1 s1' s2 lL))) ==>
   ((?s1 s2 lL. X s1 s2 lL) = (?s1 lL s1' s2'. Y s1 s1' s2' lL))``, METIS_TAC[])) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

ASM_SIMP_TAC std_ss [asl_bigstar_list_REWRITE] THEN
Q.ABBREV_TAC `treeP = asl_bigstar_list holfoot_separation_combinator
  (MAP (\lt. holfoot_ap_data_tree tagL (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,tL)))` THEN
Q.ABBREV_TAC `LL = ZIP (tagL ++ dtagL, lL ++ v)` THEN
Q.ABBREV_TAC `eqP = (asl_bigstar_list holfoot_separation_combinator
           (MAP (\x. var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) (var_res_exp_const (SND x))) LL))` THEN
`(ZIP (tagL:holfoot_tag list ++ dtagL,
   ((MAP var_res_exp_const (lL ++ v)):holfoot_a_expression list))) =
 MAP (\x. (FST x, var_res_exp_const (SND x))) LL` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   ASM_SIMP_TAC list_ss [ZIP_MAP]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
Q.ABBREV_TAC `L' = LIST_TO_FMAP ((MAP (\x. (FST x,var_res_exp_const (SND x))) LL): (holfoot_tag # holfoot_a_expression) list)` THEN
`EVERY (\x. FST x IN FDOM L) LL` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   FULL_SIMP_TAC arith_ss [EVERY_MEM, MEM_ZIP,
     GSYM LEFT_FORALL_IMP_THM, FEVERY_DEF, SUBSET_DEF,
     IN_LIST_TO_SET, LENGTH_APPEND, EL_IS_EL]
) THEN
`~(NULL LL)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   Cases_on `tagL` THEN FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
) THEN
Tactical.REVERSE (Cases_on `ALL_DISTINCT (tagL ++ dtagL)`) THEN1 (
   Tactical.REVERSE (`treeP = asl_false` by ALL_TAC) THEN1 (
     ASM_SIMP_TAC std_ss [asl_false___asl_star_THM, NOT_IN_asl_false]
   ) THEN
   Q.UNABBREV_TAC `treeP` THEN
   MATCH_MP_TAC asl_bigstar_list_false THEN
   SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   `?y. MEM y (ZIP (lL, tL))` by ALL_TAC THEN1 (
      Cases_on `tagL` THEN FULL_SIMP_TAC std_ss [LENGTH_EQ_NUM, NULL_DEF, LENGTH] THEN
      SIMP_TAC list_ss [EXISTS_OR_THM]) THEN
   Q.EXISTS_TAC `y` THEN ASM_REWRITE_TAC[holfoot_ap_data_tree_def] THEN
   MATCH_MP_TAC (GSYM holfoot_ap_data_tree_seg___TREE_PROPS) THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___WELL_FORMED_DATA_def]
) THEN
`ALL_DISTINCT (MAP FST LL)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN 
   ASM_SIMP_TAC list_ss [MAP_ZIP]
) THEN
Q.PAT_ASSUM `Abbrev (LL = _)` (K ALL_TAC) THEN
`VAR_RES_IS_STACK_IMPRECISE treeP /\
 VAR_RES_IS_STACK_IMPRECISE eqP /\
 VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_points_to e L')` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`treeP`, `eqP`, `L'`] THEN
   REWRITE_TAC [holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list,
      VAR_RES_IS_STACK_IMPRECISE___points_to, FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      MAP_EQ_NIL, MEM_MAP, GSYM LEFT_FORALL_IMP_THM, EVERY_MEM,
      MEM_ZIP, LENGTH_APPEND, LENGTH_MAP, EL_MAP,
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      GSYM NULL_EQ] THEN
   CONJ_TAC THEN1 (
      Cases_on `tagL` THEN FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
   ) THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, 
      FEVERY_DEF, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   holfoot_separation_combinator_def, IN_ABS, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, DISJOINT_FMAP_UNION___REWRITE] THEN

HO_MATCH_MP_TAC (prove (``(!s1. ((?s2. X s1 s2) = (?s2 s3. Y s1 s2 s3))) ==>
   ((?s1 s2. X s1 s2) = (?s1 s2 s3. Y s1 s2 s3))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `s1'' = s1`) THEN1 (
   POP_ASSUM MP_TAC THEN
   MATCH_MP_TAC (prove (``((A ==> C) /\ (B ==> C)) ==> (~C ==> (A = B))``, 
     METIS_TAC [])) THEN
   Q.PAT_ASSUM `(FST s, s1) IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def,
     IN_ABS, LET_THM, GSYM fmap_EQ_THM, GSYM LEFT_FORALL_IMP_THM,
     FDOM_FUNION, IN_UNION, IN_SING] THEN
   SIMP_TAC (std_ss++CONJ_ss) [
      IN_SING, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM, IN_SING,
      FUNION_DEF, DISJOINT_INSERT, DISJOINT_UNION_BOTH]
) THEN
Q.ABBREV_TAC `lL_v_cond = EVERY (\x. (L ' (FST x)) (FST s) = SOME (SND x)) LL` THEN
`!h. (FST s, h:holfoot_heap) IN eqP = (h = FEMPTY) /\ lL_v_cond` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `Abbrev (L' = _)` (K ALL_TAC) THEN
   Q.UNABBREV_TAC `eqP` THEN Q.UNABBREV_TAC `lL_v_cond` THEN
   Induct_on `LL` THEN1 SIMP_TAC list_ss [] THEN
   Cases_on `NULL LL` THEN1 (
      FULL_SIMP_TAC std_ss [NULL_EQ] THEN
      SIMP_TAC (list_ss++pairSimps.gen_beta_ss++CONJ_ss) [asl_bigstar_list_REWRITE,
        asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
        var_res_prop_equal_unequal_EXPAND, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
        IN_SING, var_res_exp_const_def, IS_SOME_EXISTS,
        GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
   ) THEN   
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [FEVERY_DEF, asl_bigstar_list_REWRITE] THEN
   Q.MATCH_ABBREV_TAC `(FST s, h') IN asl_star holfoot_separation_combinator
      P1 P2 = XXX` THEN Q.UNABBREV_TAC `XXX` THEN
   `VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
      MAP_EVERY Q.UNABBREV_TAC [`P1`, `P2`] THEN
      SIMP_TAC std_ss [holfoot_separation_combinator_def] THEN
      CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
         MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list], []) THEN
      FULL_SIMP_TAC list_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM, NULL_EQ,
         IS_SEPARATION_COMBINATOR___FINITE_MAP,
         IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
         VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal, EVERY_MEM, FEVERY_DEF,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
   ) THEN
   ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, holfoot_separation_combinator_def,
     IN_ABS, DISJOINT_FMAP_UNION___FEMPTY] THEN
   Q.UNABBREV_TAC `P1` THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
     var_res_exp_const_def, asl_emp_DISJOINT_FMAP_UNION, IN_SING, IS_SOME_EXISTS,
     GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
) THEN
ASM_SIMP_TAC std_ss [FUNION_FEMPTY_2, FUNION_FEMPTY_1, FDOM_FEMPTY,
   DISJOINT_EMPTY, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [FDOM_FUNION, DISJOINT_UNION_BOTH,
   DISJOINT_SYM, FUNION_ASSOC] THEN
REPEAT STRIP_TAC THEN
BINOP_TAC THEN1 METIS_TAC[FUNION_COMM] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

MAP_EVERY Q.UNABBREV_TAC [`L'`, `lL_v_cond`] THEN
Q.PAT_ASSUM `(FST s, s1) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM,
   GSYM o_f_LIST_TO_FMAP, FEVERY_LIST_TO_FMAP_EQ,
   FEVERY_o_f, var_res_exp_const_def] THEN
SIMP_TAC std_ss [EVERY_MEM, FEVERY_DEF] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x. x IN FDOM L ==> X x` (MP_TAC o Q.SPEC `FST (x:(holfoot_tag # num))`) THEN
FULL_SIMP_TAC std_ss [EVERY_MEM, IS_SOME_EXISTS,
  GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
  GSYM LEFT_FORALL_IMP_THM] THEN
SIMP_TAC (std_ss++CONJ_ss) [] THEN
METIS_TAC[]);




val VAR_RES_FRAME_SPLIT___points_to___data_tree = store_thm (
"VAR_RES_FRAME_SPLIT___points_to___data_tree",
``!e tagL dtagL data L wpb wpb' rpb sfb_context sfb_split sfb_imp sfb_restP sr.

(LIST_TO_SET (tagL++dtagL) SUBSET FDOM L) /\ ~(NULL tagL) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L)
==>
 ((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data)) sfb_imp) sfb_restP) =
  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split
   (BAG_INSERT (asl_exists_list dtagL (\v. asl_exists_list tagL (\lL. asl_exists_list tagL (\tL.
    (asl_trivial_cond (data = node v tL)
     (asl_bigstar_list holfoot_separation_combinator 
        ((MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (SND x)))) (ZIP (tagL++dtagL, lL++v))++
          MAP (\lt. holfoot_ap_data_tree tagL
            (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,tL))))))))) sfb_imp) sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___points_to___data_tree___REWRITE]);



val VAR_RES_FRAME_SPLIT___points_to___data_tree___NODE = store_thm (
"VAR_RES_FRAME_SPLIT___points_to___data_tree___NODE",
``!v tL e tagL dtagL L wpb wpb' rpb sfb_context sfb_split sfb_imp sfb_restP sr.

(LIST_TO_SET (tagL++dtagL) SUBSET FDOM L) /\ ~(NULL tagL) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L)
==>
 ((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, node v tL)) sfb_imp) sfb_restP) =
  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split
   (BAG_INSERT (
     asl_exists_list tagL (\lL. 
     asl_trivial_cond ((LENGTH v = LENGTH dtagL) /\ (LENGTH tL = LENGTH tagL)) (
     (asl_bigstar_list holfoot_separation_combinator 
        ((MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (SND x)))) (ZIP (tagL++dtagL, lL++v))++
          MAP (\lt. holfoot_ap_data_tree tagL
            (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,tL)))))))
       sfb_imp) sfb_restP))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___points_to___data_tree,
   tree_11] THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
SIMP_TAC std_ss [asl_exists_list_def,
   IN_ABS, GSYM RIGHT_EXISTS_AND_THM, asl_bool_EVAL,
   EXTENSION] THEN
METIS_TAC[]);



val holfoot_ap_data_tree___var_res_prop_implies_eq___split___NODE = 
store_thm ("holfoot_ap_data_tree___var_res_prop_implies_eq___split___NODE",
``!tagL e1 dtagL v tL sfb1 sfb2 wpb rpb.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) ==>

  (var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb, rpb) sfb1
     (BAG_INSERT (holfoot_ap_data_tree tagL e1 (dtagL, node v tL)) sfb2) 

     (BAG_INSERT (asl_exists_list tagL (\lL. 
                  asl_trivial_cond ((NULL tagL ==> ALL_DISTINCT dtagL) /\ 
                     (LENGTH v = LENGTH dtagL) /\ (LENGTH tL = LENGTH tagL))
                     (asl_bigstar_list holfoot_separation_combinator
                        (holfoot_ap_points_to e1 (LIST_TO_FMAP (ZIP (tagL ++ dtagL, MAP var_res_exp_const (lL ++ v))))::
                        MAP (\lt. holfoot_ap_data_tree tagL
                            (var_res_exp_const (FST lt)) (dtagL,(SND lt))) (ZIP (lL,tL))))))
      sfb2))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE,
   IS_LEAF_REWRITE, tree_distinct, asl_trivial_cond_TF, asl_bool_REWRITES,
   tree_11] THEN
SIMP_TAC std_ss [var_res_prop_implies_eq_def] THEN
AP_TERM_TAC THEN AP_TERM_TAC THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
SIMP_TAC std_ss [asl_exists_list_def,
   IN_ABS, GSYM RIGHT_EXISTS_AND_THM, asl_bool_EVAL,
   EXTENSION] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___points_to___tree___REWRITE = prove (
``!v tL e tagL L wpb rpb sfb_context sfb_split sfb_imp.

(LIST_TO_SET tagL SUBSET FDOM L) /\ ~(NULL tagL) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L)
==>
 VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_tree tagL e) sfb_imp) 


   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split
   (BAG_INSERT (asl_exists_list tagL (\lL. 
     (asl_bigstar_list holfoot_separation_combinator 
        ((MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (SND x))) (ZIP (tagL, lL)))++
         (MAP (\l. holfoot_ap_tree tagL (var_res_exp_const l)) lL))))) sfb_imp)``,

REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT,
   BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN

MATCH_MP_TAC (prove (``((A /\ A') /\ (A /\ A' ==> (B = B'))) ==> ((A ==> B) = (A' ==> B'))``,
   SIMP_TAC (std_ss++CONJ_ss) [])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [asl_exists_list___ELIM, holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list], []) THEN
   ASM_SIMP_TAC (list_ss++pairSimps.gen_beta_ss) [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM,
      MEM_MAP,  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree, PAIR_FORALL_THM,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
   REPEAT STRIP_TAC THEN1 (
      Cases_on `tagL` THEN
      FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
   ) THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
   Tactical.REVERSE (`x1 IN FDOM L` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [FEVERY_DEF, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
   ) THEN
   Tactical.REVERSE (`MEM x1 tagL` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET]
   ) THEN
   Q.PAT_ASSUM `MEM x Y` MP_TAC THEN
   ASM_SIMP_TAC arith_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
       LENGTH_APPEND, EL_IS_EL]
) THEN
STRIP_TAC THEN
Q.PAT_ASSUM `var_res_prop___PROP DISJOINT_FMAP_UNION f X s` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
ASM_SIMP_TAC std_ss [IN_ABS, asl_exists_list___ELIM,
   GSYM RIGHT_EXISTS_AND_THM, asl_bool_EVAL, GSYM LEFT_EXISTS_AND_THM,
   DISJOINT_FMAP_UNION___REWRITE,
   asl_bigstar_list_APPEND, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
REPEAT STRIP_TAC THEN
`?ec. (e (FST s) = SOME ec) /\ ~(ec = 0)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(FST s, _) IN holfoot_ap_points_to e L` MP_TAC THEN
   SIMP_TAC std_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS] THEN
   Cases_on `e (FST s)` THEN SIMP_TAC std_ss []
) THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
`!h. ~((FST s, h:holfoot_heap) IN var_res_prop_equal DISJOINT_FMAP_UNION e (var_res_exp_const 0))` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS, var_res_exp_const_def]
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_tree___REWRITE,
   asl_bool_EVAL, asl_exists_list___ELIM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM] THEN
HO_MATCH_MP_TAC (prove (``(!lL s2. ((?s1. X s1 s2 lL) = (?s1 s1'. Y s1 s1' s2 lL))) ==>
   ((?s1 s2 lL. X s1 s2 lL) = (?s1 lL s1' s2'. Y s1 s1' s2' lL))``, METIS_TAC[])) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

ASM_SIMP_TAC std_ss [asl_bigstar_list_REWRITE] THEN
Q.ABBREV_TAC `treeP = asl_bigstar_list holfoot_separation_combinator
  (MAP (\l. holfoot_ap_tree tagL (var_res_exp_const l)) lL)` THEN
Q.ABBREV_TAC `LL = ZIP (tagL, lL)` THEN
Q.ABBREV_TAC `eqP = (asl_bigstar_list holfoot_separation_combinator
           (MAP (\x. var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) (var_res_exp_const (SND x))) LL))` THEN
`(ZIP (tagL:holfoot_tag list,
   ((MAP var_res_exp_const lL)):holfoot_a_expression list)) =
 MAP (\x. (FST x, var_res_exp_const (SND x))) LL` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   ASM_SIMP_TAC list_ss [ZIP_MAP]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
Q.ABBREV_TAC `L' = LIST_TO_FMAP ((MAP (\x. (FST x,var_res_exp_const (SND x))) LL): (holfoot_tag # holfoot_a_expression) list)` THEN
`EVERY (\x. FST x IN FDOM L) LL` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   FULL_SIMP_TAC arith_ss [EVERY_MEM, MEM_ZIP,
     GSYM LEFT_FORALL_IMP_THM, FEVERY_DEF, SUBSET_DEF,
     IN_LIST_TO_SET, LENGTH_APPEND, EL_IS_EL]
) THEN
`~(NULL LL)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN
   Cases_on `tagL` THEN FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
) THEN
Tactical.REVERSE (Cases_on `ALL_DISTINCT tagL`) THEN1 (
   Tactical.REVERSE (`treeP = asl_false` by ALL_TAC) THEN1 (
     ASM_SIMP_TAC std_ss [asl_false___asl_star_THM, NOT_IN_asl_false]
   ) THEN
   Q.UNABBREV_TAC `treeP` THEN
   MATCH_MP_TAC asl_bigstar_list_false THEN
   SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   `?l. MEM l lL` by ALL_TAC THEN1 (
      Cases_on `tagL` THEN FULL_SIMP_TAC std_ss [LENGTH_EQ_NUM, NULL_DEF, LENGTH] THEN
      SIMP_TAC list_ss [EXISTS_OR_THM]) THEN
   Q.EXISTS_TAC `l` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (GSYM holfoot_ap_tree___TREE_PROPS) THEN
   ASM_REWRITE_TAC[]
) THEN
`ALL_DISTINCT (MAP FST LL)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `LL` THEN 
   ASM_SIMP_TAC list_ss [MAP_ZIP]
) THEN
Q.PAT_ASSUM `Abbrev (LL = _)` (K ALL_TAC) THEN
`VAR_RES_IS_STACK_IMPRECISE treeP /\
 VAR_RES_IS_STACK_IMPRECISE eqP /\
 VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_points_to e L')` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`treeP`, `eqP`, `L'`] THEN
   REWRITE_TAC [holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([], [MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list,
      VAR_RES_IS_STACK_IMPRECISE___points_to, FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
      MAP_EQ_NIL, MEM_MAP, GSYM LEFT_FORALL_IMP_THM, EVERY_MEM,
      MEM_ZIP, LENGTH_APPEND, LENGTH_MAP, EL_MAP,
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_tree,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      GSYM NULL_EQ] THEN
   CONJ_TAC THEN1 (
      Cases_on `tagL` THEN FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM]
   ) THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, 
      FEVERY_DEF, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   holfoot_separation_combinator_def, IN_ABS, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, DISJOINT_FMAP_UNION___REWRITE] THEN

HO_MATCH_MP_TAC (prove (``(!s1. ((?s2. X s1 s2) = (?s2 s3. Y s1 s2 s3))) ==>
   ((?s1 s2. X s1 s2) = (?s1 s2 s3. Y s1 s2 s3))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `s1'' = s1`) THEN1 (
   POP_ASSUM MP_TAC THEN
   MATCH_MP_TAC (prove (``((A ==> C) /\ (B ==> C)) ==> (~C ==> (A = B))``, 
     METIS_TAC [])) THEN
   Q.PAT_ASSUM `(FST s, s1) IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def,
     IN_ABS, LET_THM, GSYM fmap_EQ_THM, GSYM LEFT_FORALL_IMP_THM,
     FDOM_FUNION, IN_UNION, IN_SING] THEN
   SIMP_TAC (std_ss++CONJ_ss) [
      IN_SING, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM, IN_SING,
      FUNION_DEF, DISJOINT_INSERT, DISJOINT_UNION_BOTH]
) THEN
Q.ABBREV_TAC `lL_v_cond = EVERY (\x. (L ' (FST x)) (FST s) = SOME (SND x)) LL` THEN
`!h. (FST s, h:holfoot_heap) IN eqP = (h = FEMPTY) /\ lL_v_cond` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `Abbrev (L' = _)` (K ALL_TAC) THEN
   Q.UNABBREV_TAC `eqP` THEN Q.UNABBREV_TAC `lL_v_cond` THEN
   Induct_on `LL` THEN1 SIMP_TAC list_ss [] THEN
   Cases_on `NULL LL` THEN1 (
      FULL_SIMP_TAC std_ss [NULL_EQ] THEN
      SIMP_TAC (list_ss++pairSimps.gen_beta_ss++CONJ_ss) [asl_bigstar_list_REWRITE,
        asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
        var_res_prop_equal_unequal_EXPAND, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
        IN_SING, var_res_exp_const_def, IS_SOME_EXISTS,
        GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
   ) THEN   
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [FEVERY_DEF, asl_bigstar_list_REWRITE] THEN
   Q.MATCH_ABBREV_TAC `(FST s, h') IN asl_star holfoot_separation_combinator
      P1 P2 = XXX` THEN Q.UNABBREV_TAC `XXX` THEN
   `VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
      MAP_EVERY Q.UNABBREV_TAC [`P1`, `P2`] THEN
      SIMP_TAC std_ss [holfoot_separation_combinator_def] THEN
      CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
         MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list], []) THEN
      FULL_SIMP_TAC list_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM, NULL_EQ,
         IS_SEPARATION_COMBINATOR___FINITE_MAP,
         IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
         VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal, EVERY_MEM, FEVERY_DEF,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
   ) THEN
   ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, holfoot_separation_combinator_def,
     IN_ABS, DISJOINT_FMAP_UNION___FEMPTY] THEN
   Q.UNABBREV_TAC `P1` THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
     var_res_exp_const_def, asl_emp_DISJOINT_FMAP_UNION, IN_SING, IS_SOME_EXISTS,
     GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]
) THEN
ASM_SIMP_TAC std_ss [FUNION_FEMPTY_2, FUNION_FEMPTY_1, FDOM_FEMPTY,
   DISJOINT_EMPTY, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [FDOM_FUNION, DISJOINT_UNION_BOTH,
   DISJOINT_SYM, FUNION_ASSOC] THEN
REPEAT STRIP_TAC THEN
BINOP_TAC THEN1 METIS_TAC[FUNION_COMM] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

MAP_EVERY Q.UNABBREV_TAC [`L'`, `lL_v_cond`] THEN
Q.PAT_ASSUM `(FST s, s1) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM,
   GSYM o_f_LIST_TO_FMAP, FEVERY_LIST_TO_FMAP_EQ,
   FEVERY_o_f, var_res_exp_const_def] THEN
SIMP_TAC std_ss [EVERY_MEM, FEVERY_DEF] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x. x IN FDOM L ==> X x` (MP_TAC o Q.SPEC `FST (x:(holfoot_tag # num))`) THEN
FULL_SIMP_TAC std_ss [EVERY_MEM, IS_SOME_EXISTS,
  GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
  GSYM LEFT_FORALL_IMP_THM] THEN
SIMP_TAC (std_ss++CONJ_ss) [] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___points_to___tree = store_thm (
"VAR_RES_FRAME_SPLIT___points_to___tree",
``!e tagL L wpb wpb' rpb sfb_context sfb_split sfb_imp sfb_restP sr.

(LIST_TO_SET tagL SUBSET FDOM L) /\ ~(NULL tagL) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L)
==>
 ((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (holfoot_ap_tree tagL e) sfb_imp) sfb_restP) =
  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb' 
   (BAG_INSERT (holfoot_ap_points_to e L) sfb_context)
   sfb_split
   (BAG_INSERT (asl_exists_list tagL (\lL.
     (asl_bigstar_list holfoot_separation_combinator 
        ((MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (SND x))) (ZIP (tagL, lL)))++
         (MAP (\l. holfoot_ap_tree tagL (var_res_exp_const l)) lL))))) sfb_imp) sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___points_to___tree___REWRITE]);





val holfoot_ap_data_tree___REWRITE_EXP =
store_thm ("holfoot_ap_data_tree___REWRITE_EXP",
``!tagL dtagL data e e' s.
((e (FST s) = (e' (FST s))) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e'))) ==>

(s IN (holfoot_ap_data_tree tagL e (dtagL, data)) =
 s IN (holfoot_ap_data_tree tagL e' (dtagL, data)))``,


SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE, asl_bool_EVAL,
   asl_exists_list___ELIM, var_res_prop_equal_unequal_EXPAND, IN_ABS,
   asl_emp_DISJOINT_FMAP_UNION, GSYM RIGHT_EXISTS_AND_THM, IN_SING] THEN
REPEAT STRIP_TAC THEN
BINOP_TAC THEN1 REWRITE_TAC[] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
REPEAT STRIP_TAC THEN
Cases_on `NULL tagL ==> ALL_DISTINCT dtagL` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

Cases_on `tagL` THEN1 (
   FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM,
     asl_bigstar_list_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
     asl_star___PROPERTIES] THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS]
) THEN
FULL_SIMP_TAC list_ss [
  asl_bigstar_list_REWRITE, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
  asl_star___PROPERTIES] THEN
Q.MATCH_ABBREV_TAC `s IN asl_star holfoot_separation_combinator P1 P2 =
                    s IN asl_star holfoot_separation_combinator P1' P2` THEN
`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P1' /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P1`, `P1'`, `P2`] THEN
   REWRITE_TAC [holfoot_separation_combinator_def] THEN
   CONSEQ_REWRITE_TAC ([], 
     [VAR_RES_IS_STACK_IMPRECISE___points_to, FEVERY_LIST_TO_FMAP,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list],
     []) THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [IS_SEPARATION_COMBINATOR___FINITE_MAP, MEM_MAP,
     GSYM LEFT_FORALL_IMP_THM, VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   ASM_SIMP_TAC arith_ss [GSYM MAP_APPEND, ZIP_MAP, LENGTH, EVERY_MAP,
      LENGTH_APPEND, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      MAP_EQ_NIL] THEN
   FULL_SIMP_TAC list_ss [EVERY_MEM, LENGTH_EQ_NUM]
) THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   holfoot_separation_combinator_def, IN_ABS] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
MAP_EVERY Q.UNABBREV_TAC [`P1`, `P1'`] THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM]);




val holfoot_ap_data_tree___SAME_START = store_thm ("holfoot_ap_data_tree___SAME_START",
``!data data' e e' tagL dtagL st h1 h2 h.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e') /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 h /\
 (st, h1) IN holfoot_ap_data_tree tagL e  (dtagL, data) /\
 (st, h2) IN holfoot_ap_data_tree tagL e' (dtagL, data') /\
 (e st = e' st)) ==> ((h1 = h2) /\ (data = data'))``,

HO_MATCH_MP_TAC tree_INDUCT THEN
CONJ_TAC THEN1 (
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REPEAT (Q.PAT_ASSUM `X IN Y` MP_TAC) THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___leaf,
      asl_bool_EVAL, var_res_prop_equal_unequal_EXPAND,
      IN_ABS, var_res_exp_const_def] THEN
   STRIP_TAC THEN
   `e' st = SOME 0` by ALL_TAC THEN1 (
      Cases_on `e' st` THEN FULL_SIMP_TAC std_ss []
   ) THEN
   `(st,h2) IN holfoot_ap_data_tree tagL e' (dtagL,data') =
    (st,h2) IN holfoot_ap_data_tree tagL (var_res_exp_const 0) (dtagL,data')` by ALL_TAC THEN1 (
     MATCH_MP_TAC holfoot_ap_data_tree___REWRITE_EXP THEN
     ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
     SIMP_TAC std_ss [var_res_exp_const_def]
   ) THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_data_tree___null,
      var_res_bool_proposition_REWRITE, IS_LEAF_REWRITE,
      asl_emp_DISJOINT_FMAP_UNION, IN_ABS, IN_SING]  
) THEN   
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN
`ALL_DISTINCT (tagL ++ dtagL)` by ALL_TAC THEN1 (
   CCONTR_TAC THEN 
   Tactical.REVERSE (`holfoot_ap_data_tree tagL e' (dtagL,data') = asl_false` by ALL_TAC) THEN1 (
     FULL_SIMP_TAC std_ss [asl_bool_EVAL]
   ) THEN
   MATCH_MP_TAC holfoot_ap_data_tree___TREE_PROPS THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___WELL_FORMED_DATA_def]
) THEN
Q.PAT_ASSUM `(st,h1) IN Y` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE,
   asl_bool_EVAL, IS_LEAF_def, tree_11, asl_exists_list___ELIM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
GEN_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P1 = \a lL e. (holfoot_ap_points_to e
       (LIST_TO_FMAP (ZIP (tagL ++ dtagL,MAP var_res_exp_const (lL ++ a)))))` THEN
Q.ABBREV_TAC `PL = \lL l. MAP (\lt. holfoot_ap_data_tree tagL
         (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,l))` THEN

`(!lL l. MAP (\lt. holfoot_ap_data_tree tagL
         (var_res_exp_const (FST lt)) (dtagL,SND lt)) (ZIP (lL,l)) = PL lL l) /\
(!a lL e. (holfoot_ap_points_to e
       (LIST_TO_FMAP (ZIP (tagL ++ dtagL,MAP var_res_exp_const (lL ++ a))))) = P1 a lL e)` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P1` THEN Q.UNABBREV_TAC `PL` THEN
  SIMP_TAC std_ss []
) THEN
`!a lL e l. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
   (LENGTH a = LENGTH dtagL) /\ (LENGTH lL = LENGTH tagL) ==>
   EVERY VAR_RES_IS_STACK_IMPRECISE ((P1 a lL e)::(PL lL l))` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P1`, `PL`] THEN
   SIMP_TAC list_ss [EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM,
     MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
     VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___points_to THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FEVERY_LIST_TO_FMAP THEN
   ASM_SIMP_TAC arith_ss [GSYM MAP_APPEND, ZIP_MAP,
      LENGTH_APPEND] THEN
   SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
Q.PAT_ASSUM `(st, h1) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [asl_bigstar_list___VAR_RES_IS_STACK_IMPRECISE,
  holfoot_separation_combinator_def, IS_SEPARATION_COMBINATOR___FINITE_MAP,
  IN_ABS] THEN
STRIP_TAC THEN
`?ec. (e st = SOME ec) /\ ~(ec = 0)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P1` THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM] THEN
   Cases_on `e st` THEN FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`e' st = SOME ec` by PROVE_TAC[] THEN
Q.PAT_ASSUM `(st,h2) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_tree___REWRITE,
   asl_bool_EVAL, asl_exists_list___ELIM,
   GSYM RIGHT_EXISTS_AND_THM, DISJ_IMP_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS,
      var_res_exp_const_def]
) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `(st,h2) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [asl_bigstar_list___VAR_RES_IS_STACK_IMPRECISE,
  holfoot_separation_combinator_def, IS_SEPARATION_COMBINATOR___FINITE_MAP,
  IN_ABS, tree_11] THEN
STRIP_TAC THEN
`(v = n) /\ (lL' = lL) /\ (es1' = es1)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(st, es1') IN X` MP_TAC THEN
   Q.PAT_ASSUM `(st, es1) IN X` MP_TAC THEN
   Q.UNABBREV_TAC `P1` THEN
   Q.ABBREV_TAC `tagL' = tagL++dtagL` THEN
   Q.ABBREV_TAC `lL'' = lL' ++ v` THEN
   Q.ABBREV_TAC `lL''' = lL ++ n` THEN
   `(LENGTH lL'' = LENGTH tagL') /\ (LENGTH lL''' = LENGTH tagL')` by ALL_TAC THEN1 (
      MAP_EVERY Q.UNABBREV_TAC [`lL''`, `lL'''`, `tagL'`] THEN
      ASM_SIMP_TAC list_ss []
   ) THEN
   ASM_SIMP_TAC arith_ss [IN_ABS, LET_THM, holfoot_ap_points_to_def,
     GSYM fmap_EQ_THM, IN_SING, FEVERY_LIST_TO_FMAP_EQ, MAP_ZIP,
     LENGTH_APPEND, LENGTH_MAP] THEN
   ASM_SIMP_TAC arith_ss [ZIP_MAP, EVERY_MAP, var_res_exp_const_def,
      LENGTH_MAP, LENGTH_APPEND] THEN
   STRIP_TAC THEN STRIP_TAC THEN
   `es1' ' ec = es1 ' ec` by ALL_TAC THEN1 (
      `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es1 h /\
       ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es1' h` by ALL_TAC THEN1 (
         METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP,
            ASL_IS_SUBSTATE___TRANS]
      ) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION, IN_SING]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   Tactical.REVERSE (`lL'' = lL'''` by ALL_TAC) THEN1 (
      POP_ASSUM MP_TAC THEN
      MAP_EVERY Q.UNABBREV_TAC [`lL''`, `lL'''`] THEN
      FULL_SIMP_TAC list_ss [APPEND_11_LENGTH]
   ) THEN
   REPEAT (Q.PAT_ASSUM `EVERY X (ZIP Y)` MP_TAC) THEN
   Q.PAT_ASSUM `LENGTH lL'' = X` MP_TAC THEN
   Q.PAT_ASSUM `LENGTH lL''' = X` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Q.SPEC_TAC (`tagL'`, `tagL'`) THEN
   Q.SPEC_TAC (`lL''`, `lL''`) THEN
   Q.SPEC_TAC (`lL'''`, `lL'''`) THEN
   Induct_on `tagL'` THEN (
      ASM_SIMP_TAC list_ss [LENGTH_EQ_NUM,
         GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM]
   )
) THEN
Tactical.REVERSE (`(es2' = es2) /\ (tL = tL')` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss []
) THEN
Q.PAT_ASSUM `(st, es2) IN X` MP_TAC THEN
Q.PAT_ASSUM `(st, es2') IN X` MP_TAC THEN
Q.PAT_ASSUM `EVERY P X` MP_TAC THEN
Q.UNABBREV_TAC `PL` THEN
ASM_SIMP_TAC std_ss [] THEN
`(LENGTH tL = LENGTH lL) /\ (LENGTH tL' = LENGTH lL)` by ASM_SIMP_TAC std_ss [] THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es2 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es2' h` by ALL_TAC THEN1 (
   METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      ASL_IS_SUBSTATE___TRANS]
) THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
MAP_EVERY (fn x => Q.SPEC_TAC (x,x)) [`es2`, `es2'`, `tL`, `tL'`, `lL`] THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `lL` THEN1 (
   SIMP_TAC list_ss [LENGTH_EQ_NUM, asl_bigstar_list_REWRITE,
     asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___FINITE_MAP,
     IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
   SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE, IN_ABS,
     asl_emp_DISJOINT_FMAP_UNION, IN_SING]
) THEN
SIMP_TAC list_ss [LENGTH_EQ_NUM, GSYM LEFT_FORALL_IMP_THM,
   GSYM RIGHT_FORALL_IMP_THM, asl_bigstar_list_REWRITE,
   asl_star___swap_var_res_prop_stack_true,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
Q.PAT_ASSUM `(st, es2) IN X` MP_TAC THEN
Q.PAT_ASSUM `(st, es2') IN X` MP_TAC THEN
Q.HO_MATCH_ABBREV_TAC `
   (st, es2') IN asl_star f P1 P1L ==>
   (st, es2) IN asl_star f P2 P2L ==>
   XXX` THEN
Q.UNABBREV_TAC `f` THEN Q.UNABBREV_TAC `XXX` THEN
Q.PAT_ASSUM `!tL' tL. X` (MP_TAC o Q.SPECL [`l''`, `l'`]) THEN
ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [GSYM asl_bigstar_list_REWRITE] THEN
`VAR_RES_IS_STACK_IMPRECISE P1 /\
 VAR_RES_IS_STACK_IMPRECISE P1L /\
 VAR_RES_IS_STACK_IMPRECISE P2 /\
 VAR_RES_IS_STACK_IMPRECISE P2L` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P1`, `P2`, `P1L`, `P2L`] THEN
   CONSEQ_REWRITE_TAC ([], 
      [VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree,
       MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list],
      []) THEN
   SIMP_TAC list_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
     IS_SEPARATION_COMBINATOR___FINITE_MAP, DISJ_IMP_THM, FORALL_AND_THM,
     MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
     VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_tree,
     VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true]
) THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN

`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es1 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es1' h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es2'' h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION es2''' h` by ALL_TAC THEN1 (
   METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      ASL_IS_SUBSTATE___TRANS]
) THEN

`(es2'' = es2''') /\ (l' = l'')` by METIS_TAC[] THEN
ASM_REWRITE_TAC[] THEN
Q.PAT_ASSUM `!data' e e' tagL dtagL st h1 h2 h. X`
  (MP_TAC o Q.SPECL [`h'''`, `(var_res_exp_const h'):holfoot_a_expression`,
     `(var_res_exp_const h'):holfoot_a_expression`,
     `tagL`, `dtagL`, `st`, `es1'`, `es1`, `h`]) THEN
ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE]);




val VAR_RES_FRAME_SPLIT___data_tree___SAME_EXP___REMOVE___REWRITE = prove (
``!wpb rpb e tagL dtagL data1 data2 sfb_context sfb_split sfb_imp.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e ==>

(VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data1)) sfb_split)
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data2)) sfb_imp)

   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data1)) sfb_context)
   sfb_split  
     (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (data1 = data2)) sfb_imp))``,

REPEAT STRIP_TAC THEN
Cases_on `data2 = data1` THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___stack_true,
      var_res_bool_proposition_TF, VAR_RES_FRAME_SPLIT___REWRITE_OK___FRAME]
) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_bool_proposition_TF,
   VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   BAG_UNION_INSERT, var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION,
   var_res_prop___PROP___asl_false, asl_bool_EVAL,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false] THEN
REPEAT STRIP_TAC THEN

REPEAT (Q.PAT_ASSUM `var_res_prop___PROP f x y s` MP_TAC) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_UNION, var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree] THEN
REPEAT STRIP_TAC THEN CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN

`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` by 
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1  (SND s) /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1' (SND s)` by ALL_TAC THEN1 (
   METIS_TAC [ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]) THEN
METIS_TAC[holfoot_ap_data_tree___SAME_START]);



val VAR_RES_FRAME_SPLIT___data_tree___SAME_EXP___REMOVE = store_thm (
"VAR_RES_FRAME_SPLIT___data_tree___SAME_EXP___REMOVE",
``!wpb rpb e tagL dtagL data1 data2 sfb_context sfb_split sfb_imp sr wpb' sfb_restP.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e ==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data1)) sfb_split)
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data2)) sfb_imp) sfb_restP) =
 (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_tree tagL e (dtagL, data1)) sfb_context)
   sfb_split  
     (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (data1 = data2)) sfb_imp)) sfb_restP)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___data_tree___SAME_EXP___REMOVE___REWRITE THEN
ASM_REWRITE_TAC[]);



(*-----------------
 * Lists
 *-----------------*)


val holfoot_ap_gendl_data_list_seg_num_def = Define `
  (holfoot_ap_gendl_data_list_seg_num 0 np startExp data endExp =
    if (EVERY (\x. NULL (SND x)) data) /\ ALL_DISTINCT (MAP FST data) then
       (var_res_prop_equal DISJOINT_FMAP_UNION startExp endExp)
    else asl_false) /\
  (holfoot_ap_gendl_data_list_seg_num (SUC n) np startExp data endExp =
    if EVERY (\x. ~NULL (SND x)) data /\ ALL_DISTINCT (MAP FST data) then
     asl_and (var_res_prop_weak_unequal startExp endExp) 
     asl_exists n':num. 
      asl_star holfoot_separation_combinator
                      (asl_and (np startExp (var_res_exp_const n')) 
                      (holfoot_ap_points_to startExp
                         (LIST_TO_FMAP (ZIP (MAP FST data,
                            (MAP (\x. var_res_exp_const (HD (SND x))) data))))))
                      (holfoot_ap_gendl_data_list_seg_num n np
               (var_res_exp_const n') (MAP (\ (t, l). (t, TL l)) data) endExp)
     else asl_false)`;

val holfoot_ap_data_list_seg_num_def = Define `
  holfoot_ap_data_list_seg_num n tl startExp data endExp =
  if MEM tl (MAP FST data) then asl_false else
  holfoot_ap_gendl_data_list_seg_num n
    (\e1 e2 state. 
     let v1 = e1 (FST state) in
     let v2 = e2 (FST state) in
     (IS_SOME v1 /\ IS_SOME v2 /\
      ((THE v1) IN FDOM (SND state)) /\
      ((SND state) ' (THE v1) tl = THE v2))) startExp data endExp`;

val holfoot_ap_data_list_seg_num_REWRITE = store_thm ("holfoot_ap_data_list_seg_num_REWRITE",
``(holfoot_ap_data_list_seg_num 0 tl startExp data endExp =
    if (EVERY (\x. NULL (SND x)) data) /\ ALL_DISTINCT (tl::(MAP FST data)) then
       (var_res_prop_equal DISJOINT_FMAP_UNION startExp endExp)
    else asl_false) /\
  (holfoot_ap_data_list_seg_num (SUC n) tl startExp data endExp =
    if EVERY (\x. ~NULL (SND x)) data /\ ALL_DISTINCT (tl::(MAP FST data)) then
     asl_and (var_res_prop_weak_unequal startExp endExp) (
     asl_exists n':num. asl_star holfoot_separation_combinator
                      (holfoot_ap_points_to startExp
                         (LIST_TO_FMAP (ZIP (tl::MAP FST data,
                            MAP (var_res_exp_const) (n'::(MAP (\x. HD (SND x)) data))))))
                      (holfoot_ap_data_list_seg_num n tl
               (var_res_exp_const n') (MAP (\ (t, l). (t, TL l)) data) endExp)
     ) else asl_false)``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [holfoot_ap_data_list_seg_num_def, holfoot_ap_gendl_data_list_seg_num_def] THEN
Cases_on `ALL_DISTINCT (tl::(MAP FST data))` THEN FULL_SIMP_TAC std_ss [ALL_DISTINCT] THEN
Cases_on `EVERY (\x. ~NULL (SND x)) data` THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [FUN_EQ_THM, asl_bool_EVAL, IN_ABS, asl_star_def, GSYM RIGHT_EXISTS_AND_THM,
   MAP_MAP_o, combinTheory.o_DEF, ETA_THM] THEN
REPEAT STRIP_TAC THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [holfoot_ap_points_to_def, IN_ABS, LET_THM,
   LIST_TO_FMAP_THM, FEVERY_FUPDATE, MAP_MAP_o, combinTheory.o_DEF,
   var_res_exp_const_EVAL] THEN
Q.ABBREV_TAC `dL:holfoot_tag |-> holfoot_a_expression = (LIST_TO_FMAP (ZIP (MAP FST data, MAP (\x. var_res_exp_const (HD (SND x))) data)))` THEN
`DRESTRICT dL (COMPL {tl}) = dL` by ALL_TAC THEN1 (
   MATCH_MP_TAC NOT_FDOM_DRESTRICT THEN
   Q.UNABBREV_TAC `dL` THEN
   ASM_SIMP_TAC list_ss [FDOM_LIST_TO_FMAP, IN_LIST_TO_SET, MAP_ZIP]
) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_SING]);



val holfoot_ap_list_seg_num_def = Define `
  holfoot_ap_list_seg_num n tl startExp endExp =
  holfoot_ap_data_list_seg_num n tl startExp [] endExp`;


val holfoot_ap_gendl_data_list_seg_num___DATA_PROPS =
store_thm ("holfoot_ap_gendl_data_list_seg_num___DATA_PROPS",
``!n data np startExp endExp.
  ~((EVERY (\x. LENGTH (SND x) = n) data) /\ (ALL_DISTINCT (MAP FST data))) ==>
  (holfoot_ap_gendl_data_list_seg_num n np startExp data endExp =
   asl_false)``,

Induct_on `n` THENL [
   SIMP_TAC std_ss [holfoot_ap_gendl_data_list_seg_num_def, LENGTH_NIL, NULL_EQ,
                    DISJ_IMP_THM],

   SIMP_TAC std_ss [holfoot_ap_gendl_data_list_seg_num_def, COND_RAND, COND_RATOR,
                    DISJ_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL] THEN
   GEN_TAC THEN DISJ2_TAC THEN GEN_TAC THEN
   MATCH_MP_TAC (prove (``(Y = asl_false) ==> x NOTIN Y``, SIMP_TAC std_ss [asl_bool_EVAL])) THEN
   MATCH_MP_TAC (prove (``(P2 = asl_false) ==> (asl_star holfoot_separation_combinator P1 P2 = asl_false)``,
                   SIMP_TAC std_ss [asl_false___asl_star_THM])) THEN
   Q.PAT_ASSUM `!data tl. X` MATCH_MP_TAC THEN
   Induct_on `data` THEN1 SIMP_TAC list_ss [] THEN
   SIMP_TAC list_ss [combinTheory.o_DEF, PAIR_FORALL_THM] THEN
   Cases_on `x2` THEN SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [combinTheory.o_DEF]
]);



val holfoot_ap_data_list_seg_num___DATA_PROPS =
store_thm ("holfoot_ap_data_list_seg_num___DATA_PROPS",
``!n data tl startExp endExp.
  ~((EVERY (\x. LENGTH (SND x) = n) data) /\ (ALL_DISTINCT (tl::(MAP FST data)))) ==>
  (holfoot_ap_data_list_seg_num n tl startExp data endExp =
   asl_false)``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_def,
   ALL_DISTINCT, COND_RAND, COND_RATOR] THEN
METIS_TAC[holfoot_ap_gendl_data_list_seg_num___DATA_PROPS]);


val holfoot_ap_gendl_data_list_seg_num___EXP_DEFINED =
store_thm ("holfoot_ap_gendl_data_list_seg_num___EXP_DEFINED",
``!n data pn startExp endExp s.

  (s IN holfoot_ap_gendl_data_list_seg_num n pn startExp data endExp ==>
   IS_SOME (startExp (FST s)) /\ IS_SOME (endExp (FST s)))``,

Cases_on `n` THEN (
   SIMP_TAC std_ss [holfoot_ap_gendl_data_list_seg_num_def,
      COND_RAND, COND_RATOR, asl_bool_EVAL,
      var_res_prop_equal_unequal_EXPAND, IN_ABS]
));


val holfoot_ap_data_list_seg_num___EXP_DEFINED =
store_thm ("holfoot_ap_data_list_seg_num___EXP_DEFINED",
``!n data tl startExp endExp s.
  (s IN holfoot_ap_data_list_seg_num n tl startExp data endExp ==>
   IS_SOME (startExp (FST s)) /\ IS_SOME (endExp (FST s)))``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_def,
   COND_RAND, COND_RATOR, NOT_IN_asl_false] THEN
METIS_TAC[holfoot_ap_gendl_data_list_seg_num___EXP_DEFINED]);



val holfoot_ap_gendl_data_list_seg_num___ELIM_DATA =
store_thm ("holfoot_ap_gendl_data_list_seg_num___ELIM_DATA",
``!data data' n pn startExp endExp s.
  ((!x. MEM x data' ==> MEM x data) /\ ALL_DISTINCT (MAP FST data') /\
   (s IN holfoot_ap_gendl_data_list_seg_num n pn startExp data endExp)) ==>
    s IN holfoot_ap_gendl_data_list_seg_num n pn startExp data' endExp``,

Induct_on `n` THENL [
   SIMP_TAC std_ss [holfoot_ap_gendl_data_list_seg_num_def,
          asl_bool_EVAL, IN_ABS, EVERY_MEM, COND_RATOR, COND_RAND,
          ALL_DISTINCT, MEM_MAP] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [holfoot_ap_gendl_data_list_seg_num_def, COND_RAND, COND_RATOR,
                    asl_bool_EVAL] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, ALL_DISTINCT, MEM_MAP] THEN
   Q.EXISTS_TAC `n'` THEN
   FULL_SIMP_TAC std_ss [asl_star_def, IN_ABS, asl_bool_EVAL] THEN
   Q.EXISTS_TAC `p` THEN
   Q.EXISTS_TAC `q` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Tactical.REVERSE CONJ_TAC THENL [
      Q.PAT_ASSUM `!data data'. X` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `(MAP (\(t,l). (t,TL l)) data)` THEN
      ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, PAIR_EXISTS_THM,
                           PAIR_FORALL_THM,
                           PAIR_BETA_THM, prove (``(\ (x1,x2). x1) = FST``, SIMP_TAC std_ss [FUN_EQ_THM, PAIR_FORALL_THM])] THEN
      METIS_TAC[],


      MATCH_MP_TAC holfoot_ap_points_to___SUBMAP THEN
      Q.EXISTS_TAC `LIST_TO_FMAP (ZIP
               (MAP FST data,
                MAP (\x. var_res_exp_const (HD (SND x))) data))` THEN
      ASM_SIMP_TAC list_ss [MAP_MAP_o, LIST_TO_FMAP_THM,
         combinTheory.o_DEF, ZIP_MAP, MAP_ZIP_EQ] THEN
      SIMP_TAC std_ss [SUBMAP_DEF, FDOM_FUPDATE_LIST, IN_INSERT,
         FDOM_LIST_TO_FMAP, IN_LIST_TO_SET, MEM_MAP, MAP_MAP_o,
         combinTheory.o_DEF, GSYM RIGHT_EXISTS_AND_THM,
         FDOM_FUPDATE] THEN
      GEN_TAC THEN
      REPEAT STRIP_TAC THEN1 PROVE_TAC[] THEN

      MATCH_MP_TAC (prove (``(?z. (X = z) /\ (Y = z)) ==> (X = Y)``, PROVE_TAC[])) THEN
      CONSEQ_REWRITE_TAC ([LIST_TO_FMAP___ALL_DISTINCT], [], []) THEN
      ASM_SIMP_TAC std_ss [MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, ETA_THM] THEN
      PROVE_TAC[]
    ]
]);



val holfoot_ap_data_list_seg_num___ELIM_DATA =
store_thm ("holfoot_ap_data_list_seg_num___ELIM_DATA",
``!data data' n tl startExp endExp s.
  ((!x. MEM x data' ==> MEM x data) /\ ALL_DISTINCT (MAP FST data') /\
   (s IN holfoot_ap_data_list_seg_num n tl startExp data endExp)) ==>
    s IN holfoot_ap_data_list_seg_num n tl startExp data' endExp``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `MEM tl (MAP FST data)` THEN1 FULL_SIMP_TAC std_ss [NOT_IN_asl_false] THEN
`~(MEM tl (MAP FST data'))` by METIS_TAC[MEM_MAP] THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[holfoot_ap_gendl_data_list_seg_num___ELIM_DATA]);



val holfoot_ap_data_list_seg_num___ELIM_DATA___COMPLETE =
store_thm ("holfoot_ap_data_list_seg_num___ELIM_DATA___COMPLETE",

``!data n tl startExp endExp s.
   s IN holfoot_ap_data_list_seg_num n tl startExp data endExp ==>
   s IN holfoot_ap_list_seg_num n tl startExp endExp``,

SIMP_TAC std_ss [holfoot_ap_list_seg_num_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_ap_data_list_seg_num___ELIM_DATA THEN
Q.EXISTS_TAC `data` THEN
ASM_SIMP_TAC list_ss []);




val holfoot_ap_data_list_seg_def = Define `
   holfoot_ap_data_list_seg tl startExp data endExp =
   asl_exists n. holfoot_ap_data_list_seg_num n tl startExp data endExp`


val holfoot_ap_data_list_seg_REWRITE = store_thm ("holfoot_ap_data_list_seg_REWRITE",
``holfoot_ap_data_list_seg tl startExp data endExp =
  asl_or
    (asl_and (var_res_prop_equal DISJOINT_FMAP_UNION startExp endExp)
             (\s. EVERY (\x. NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data)))
    (asl_and (var_res_prop_weak_unequal startExp endExp)
     (asl_and (\s. (EVERY (\x. ~(NULL (SND x))) data) /\
                    ALL_DISTINCT (tl::MAP FST data))
      asl_exists n'.
                asl_star holfoot_separation_combinator
                  (holfoot_ap_points_to startExp
                     (LIST_TO_FMAP (ZIP
                        (tl::MAP FST data,
                         MAP var_res_exp_const
                           (n'::MAP (\x. HD (SND x)) data)))))
                  (holfoot_ap_data_list_seg tl (var_res_exp_const n')
                     (MAP (\ (t,l). (t,TL l)) data) endExp)))``,

SIMP_TAC std_ss [EXTENSION, IN_ABS, asl_bool_EVAL,
                 holfoot_ap_data_list_seg_def,
                 GSYM asl_exists___asl_star_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `n` THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
     asl_bool_EVAL, IN_ABS, COND_RAND, COND_RATOR] THEN
   PROVE_TAC[],

   Q.EXISTS_TAC `0` THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
                        asl_bool_EVAL, asl_bool_REWRITES],

   Q.EXISTS_TAC `SUC n` THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
                        asl_bool_EVAL, asl_bool_REWRITES] THEN
   Q.EXISTS_TAC `n'` THEN
   ASM_REWRITE_TAC[]
]);



val holfoot_ap_list_seg_def = Define `
   holfoot_ap_list_seg tl startExp endExp =
   holfoot_ap_data_list_seg tl startExp [] endExp`


val holfoot_ap_list_seg_REWRITE = save_thm ("holfoot_ap_list_seg_REWRITE",
  let
     val thm0 = CONV_RULE (ONCE_REWRITE_CONV [holfoot_ap_data_list_seg_REWRITE]) holfoot_ap_list_seg_def;
     val thm1 = SIMP_RULE list_ss [asl_bool_REWRITES, LIST_TO_FMAP_def] thm0;
     val thm2 = CONV_RULE (ONCE_REWRITE_CONV [GSYM holfoot_ap_list_seg_def]) thm1;
  in
     thm2
  end);

val holfoot_ap_data_list_def = Define `
   holfoot_ap_data_list tl startExp data =
   holfoot_ap_data_list_seg tl startExp data (var_res_exp_const 0)`

val holfoot_ap_list_def = Define `
   holfoot_ap_list tl startExp =
   holfoot_ap_list_seg tl startExp (var_res_exp_const 0)`



val holfoot_ap_data_list_seg___DATA_PROPS =
store_thm ("holfoot_ap_data_list_seg___DATA_PROPS",
``!data tl startExp endExp.

  ~((?n. EVERY (\x. LENGTH (SND x) = n) data) /\ ALL_DISTINCT (tl::MAP FST data)) ==>
  (holfoot_ap_data_list_seg tl startExp data endExp =
   asl_false)``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_def, EXTENSION, asl_bool_EVAL] THEN
METIS_TAC[asl_bool_EVAL, holfoot_ap_data_list_seg_num___DATA_PROPS]);



val holfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF =
store_thm ("holfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF",
``
holfoot_ap_data_list_seg tl startExp ((t, tvL)::data) endExp =
holfoot_ap_data_list_seg_num (LENGTH tvL) tl startExp ((t, tvL)::data) endExp``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_def,
       EXTENSION, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN (Tactical.REVERSE EQ_TAC) THEN1 METIS_TAC[] THEN
REPEAT STRIP_TAC THEN
Cases_on `LENGTH tvL = n` THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC list_ss [holfoot_ap_data_list_seg_num___DATA_PROPS] THEN
FULL_SIMP_TAC std_ss [NOT_IN_asl_false]);



val holfoot_ap_data_list_seg___NOT_EMPTY_DATA___0 =
store_thm ("holfoot_ap_data_list_seg___NOT_EMPTY_DATA___0",
``holfoot_ap_data_list_seg tl startExp ((t, [])::data) endExp =
  asl_trivial_cond (EVERY (\x. NULL (SND x)) data /\
      ALL_DISTINCT (tl::t::MAP FST data)) 
     (var_res_prop_equal DISJOINT_FMAP_UNION startExp endExp)``,

SIMP_TAC list_ss [holfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF,
   asl_trivial_cond_def,
   holfoot_ap_data_list_seg_num_REWRITE]);


val holfoot_ap_data_list_seg___SAME_START_END =
store_thm ("holfoot_ap_data_list_seg___SAME_START_END",
``holfoot_ap_data_list_seg tl e data e =
  asl_trivial_cond (EVERY (\x. NULL (SND x)) data /\
      ALL_DISTINCT (tl::MAP FST data))
      (var_res_prop_equal DISJOINT_FMAP_UNION e e)``,

ONCE_REWRITE_TAC [holfoot_ap_data_list_seg_REWRITE] THEN
SIMP_TAC std_ss [var_res_prop_equal_unequal_REWRITES,
   asl_bool_REWRITES] THEN
Q.MATCH_ABBREV_TAC `asl_and p (\s. c) = asl_trivial_cond c p` THEN
Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_def, asl_bool_REWRITES]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num",

``!vs n tl startExp data endExp.
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp /\
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs endExp) ==>
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_data_list_seg_num n tl startExp data endExp)``,


Induct_on `n` THENL [
   SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE] THEN
   SIMP_TAC std_ss [COND_RAND, COND_RATOR,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false],

   SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
       COND_RATOR, COND_RAND, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
       holfoot_separation_combinator_def] THEN
   CONSEQ_HO_REWRITE_TAC ([],[VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
       FEVERY_STRENGTHEN_THM],[]) THEN

   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
                        VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_unequal] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC FEVERY_LIST_TO_FMAP THEN
   SIMP_TAC list_ss [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_ZIP_EQ] THEN
   SIMP_TAC std_ss[EVERY_MAP, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
   SIMP_TAC std_ss [EVERY_MEM]
]);


val VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num =
save_thm ("VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num",

SIMP_RULE std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
        GSYM VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF]
 (SPEC ``UNIV:holfoot_var set`` VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num)
);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg",

``!vs tl startExp data endExp.
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp /\
  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs endExp) ==>
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_data_list_seg tl startExp data endExp)``,


SIMP_TAC std_ss [holfoot_ap_data_list_seg_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num]);



val VAR_RES_IS_STACK_IMPRECISE___data_list_seg =
save_thm ("VAR_RES_IS_STACK_IMPRECISE___data_list_seg",

SIMP_RULE std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
        GSYM VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF]
 (SPEC ``UNIV:holfoot_var set`` VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg)

);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list",

``!vs tl startExp data.
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs startExp) ==>
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_data_list tl startExp data)``,

SIMP_TAC std_ss [holfoot_ap_data_list_def,
       VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg]);


val VAR_RES_IS_STACK_IMPRECISE___data_list =
save_thm ("VAR_RES_IS_STACK_IMPRECISE___data_list",

SIMP_RULE std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
        GSYM VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF]
 (SPEC ``UNIV:holfoot_var set`` VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list)

);




val holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE =
store_thm ("holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE",
``(!tl data startExp endExp.
((holfoot_ap_data_list_seg_num 0 tl startExp data endExp) = \s.
 EVERY (\x. NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data) /\
 s IN var_res_prop_equal DISJOINT_FMAP_UNION startExp endExp)) /\

(!n tl data startExp endExp.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp))) ==>

(holfoot_ap_data_list_seg_num (SUC n) tl startExp data endExp = \s.
 (EVERY (\x. ~NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data) /\
 s IN var_res_prop_weak_unequal startExp endExp /\
 ?n' s1 s2. (DISJOINT_FMAP_UNION (SOME s1) (SOME s2) = SOME (SND s)) /\
            (FST s,s1) IN holfoot_ap_points_to startExp
                (LIST_TO_FMAP (ZIP (tl::MAP FST data,
                   MAP var_res_exp_const (n'::MAP (\x. HD (SND x)) data)))) /\
            (FST s,s2) IN
                (holfoot_ap_data_list_seg_num n tl (var_res_exp_const n')
                   (MAP (\ (t,l). (t,TL l)) data) endExp))))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_list_seg_num_REWRITE,
  asl_bool_EVAL, EXTENSION, IN_ABS, COND_RAND, COND_RATOR] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
GEN_TAC THEN

Q.MATCH_ABBREV_TAC `s IN asl_star holfoot_separation_combinator P1 P2 = X` THEN
Tactical.REVERSE (`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_separation_combinator_def,
      asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS]
) THEN
UNABBREV_ALL_TAC THEN
CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___points_to,
   VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num,
   FEVERY_LIST_TO_FMAP], []) THEN
ASM_SIMP_TAC list_ss [
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP]);



val var_res_prop_varlist_update___holfoot_ap_data_list_seg_num =
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_list_seg_num",
``!vcL tl startExp data endExp n.
   IS_SOME
     (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
   IS_SOME
       (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp) ==>

  (var_res_prop_varlist_update vcL
     (holfoot_ap_data_list_seg_num n tl startExp data endExp) =
  holfoot_ap_data_list_seg_num n tl (var_res_exp_varlist_update vcL startExp)
      data (var_res_exp_varlist_update vcL endExp))``,

Induct_on `n` THEN1 (
   SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE] THEN
   REPEAT STRIP_TAC THEN
   Q.ABBREV_TAC `c = EVERY (\x. NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data)` THEN
   Cases_on `c` THEN
      ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___BOOL,
         var_res_prop_varlist_update___equal_unequal]
) THEN

SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE] THEN
REPEAT STRIP_TAC THEN
Cases_on `EVERY (\x. ~NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data)` THEN
ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___BOOL] THEN

SIMP_TAC std_ss [var_res_prop_varlist_update___equal_unequal] THEN
AP_TERM_TAC THEN AP_TERM_TAC THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
BETA_TAC THEN GEN_TAC THEN
Q.MATCH_ABBREV_TAC `var_res_prop_varlist_update vcL
   (asl_star holfoot_separation_combinator P1 P2) = X` THEN
Q.UNABBREV_TAC `X` THEN

`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P1` THEN Q.UNABBREV_TAC `P2` THEN
  CONSEQ_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num,
      FEVERY_LIST_TO_FMAP], []) THEN
  ASM_SIMP_TAC list_ss [MAP_MAP_o, combinTheory.o_DEF, ZIP_MAP,
    EVERY_MAP, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const]
) THEN
Q.UNABBREV_TAC `P1` THEN Q.UNABBREV_TAC `P2` THEN
ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___asl_star,
   holfoot_separation_combinator_def,
   var_res_prop_varlist_update___holfoot_ap_points_to,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const] THEN
SIMP_TAC list_ss [o_f_LIST_TO_FMAP, ZIP_MAP,
   MAP_MAP_o, combinTheory.o_DEF, var_res_exp_varlist_update___const_EVAL]);




val var_res_prop_varlist_update___holfoot_ap_data_list_seg =
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_list_seg",
``!vcL tl startExp data endExp.
   IS_SOME
     (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
   IS_SOME
       (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp) ==>

  (var_res_prop_varlist_update vcL
     (holfoot_ap_data_list_seg tl startExp data endExp) =
  holfoot_ap_data_list_seg tl (var_res_exp_varlist_update vcL startExp)
      data (var_res_exp_varlist_update vcL endExp))``,

SIMP_TAC std_ss [
   holfoot_ap_data_list_seg_def,
   var_res_prop_varlist_update___BOOL,
   var_res_prop_varlist_update___holfoot_ap_data_list_seg_num]);


val var_res_prop_varlist_update___holfoot_ap_data_list =
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_list",
``!vcL tl startExp data.
   IS_SOME
     (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) ==>

  (var_res_prop_varlist_update vcL
     (holfoot_ap_data_list tl startExp data) =
  holfoot_ap_data_list tl (var_res_exp_varlist_update vcL startExp)
      data)``,

SIMP_TAC std_ss [
   holfoot_ap_data_list_def,
   var_res_prop_varlist_update___holfoot_ap_data_list_seg,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
   var_res_exp_varlist_update___const_EVAL]);




val holfoot_ap_data_list_seg_num___null = store_thm ("holfoot_ap_data_list_seg_num___null",
``!tl n data endExp. holfoot_ap_data_list_seg_num n tl (var_res_exp_const 0) data endExp =
  asl_trivial_cond ((n = 0) /\ EVERY (\x. NULL (SND x)) data /\  ALL_DISTINCT (tl::MAP FST data))
     (var_res_prop_equal DISJOINT_FMAP_UNION endExp (var_res_exp_const 0))``,


Cases_on `n` THENL [
   SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
      COND_RAND, COND_RATOR, COND_EXPAND_IMP,
      asl_trivial_cond_def] THEN
   PROVE_TAC[var_res_prop_equal_symmetric],

   SIMP_TAC arith_ss [holfoot_ap_data_list_seg_num_REWRITE,
      holfoot_ap_points_to___null,
      asl_false___asl_star_THM, asl_bool_REWRITES,
      asl_exists_ELIM, asl_trivial_cond_def]
]);


val holfoot_ap_data_list_seg___null = store_thm ("holfoot_ap_data_list_seg___null",
``!tl data endExp. holfoot_ap_data_list_seg tl (var_res_exp_const 0) data endExp =
  asl_trivial_cond
     (EVERY (\x. NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data))
     (var_res_prop_equal DISJOINT_FMAP_UNION endExp (var_res_exp_const 0))``,

SIMP_TAC std_ss [holfoot_ap_data_list_seg_def,
  holfoot_ap_data_list_seg_num___null, asl_exists_def,
  asl_trivial_cond_def, COND_RAND, COND_RATOR, EXTENSION,
  IN_ABS, asl_bool_EVAL] THEN
METIS_TAC[]);



val holfoot_ap_data_list_seg_num_SUC___implies_in_heap = store_thm ("holfoot_ap_data_list_seg_num_SUC___implies_in_heap",
``!n B e1 e2 tl data sfb.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) ==>
  holfoot_implies_in_heap B
 (BAG_INSERT (holfoot_ap_data_list_seg_num (SUC n) tl e1 data e2) sfb) e1``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
   COND_RAND, COND_RATOR,
   holfoot_implies_in_heap_def,
   holfoot_implies_in_heap_pred___asl_false] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap_pred___asl_and THEN
DISJ2_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_implies_in_heap_pred___asl_exists,
   holfoot_implies_in_heap_pred___asl_star] THEN
ASM_SIMP_TAC std_ss [
   GSYM holfoot_implies_in_heap_def,
   holfoot_ap_points_to___implies_in_heap]);


val holfoot_ap_data_list_seg_num___implies_in_heap = store_thm ("holfoot_ap_data_list_seg_num___implies_in_heap",
``!e1 e2 B n tl data sfb.   
  (var_res_implies_unequal DISJOINT_FMAP_UNION B e1 e2 /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>

  holfoot_implies_in_heap B
 (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data e2) sfb) e1``,


Tactical.REVERSE (Cases_on `n`) THEN1 (
   PROVE_TAC[holfoot_ap_data_list_seg_num_SUC___implies_in_heap]
) THEN

SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
   COND_RAND, COND_RATOR,
   holfoot_implies_in_heap_def,
   holfoot_implies_in_heap_pred___asl_false,
   SUB_BAG_EXISTS] THEN
REPEAT STRIP_TAC THEN

FULL_SIMP_TAC std_ss [var_res_implies_unequal_def,
   BAG_INSERT_NOT_EMPTY, holfoot_separation_combinator_def,
   holfoot_implies_in_heap_pred_def] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `!s. X` (MP_TAC o Q.SPEC `(st, h1)`) THEN
ASM_REWRITE_TAC [] THEN 
Q.PAT_ASSUM `(st2, h2) IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND,
   var_res_bigstar_REWRITE_EXT,
   IN_ABS, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star_def, VAR_RES_COMBINATOR_REWRITE,
   IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, PAIR_EXISTS_THM,
   asl_emp_DISJOINT_FMAP_UNION, IN_SING,
   DISJOINT_FMAP_UNION___FEMPTY] THEN
SIMP_TAC (std_ss++CONJ_ss) [GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (`(e1 st = e1 x1)  /\ (e2 st = e2 x1) /\
                   (e1 st2 = e1 x1) /\ (e2 st2 = e2 x1)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
CONSEQ_REWRITE_TAC ([],[
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT], []) THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO,
   VAR_RES_STACK_IS_SUBSTATE___TRANS]);



val holfoot_ap_data_list_seg___implies_in_heap = store_thm ("holfoot_ap_data_list_seg___implies_in_heap",
``!e1 e2 B tl data sfb.
  (~(B = {||}) /\
  (var_res_implies_unequal DISJOINT_FMAP_UNION B e1 e2) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>

  (holfoot_implies_in_heap B
     (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb) e1)``,

SIMP_TAC std_ss [holfoot_implies_in_heap_def,
   holfoot_ap_data_list_seg_def,
   holfoot_implies_in_heap_pred___asl_exists,
   var_res_implies_unequal___asl_exists,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
SIMP_TAC std_ss [GSYM holfoot_implies_in_heap_def,
   holfoot_ap_data_list_seg_num___implies_in_heap]);



val holfoot_ap_data_list___implies_in_heap_or_null = store_thm ("holfoot_ap_data_list___implies_in_heap_or_null",
``!B e1 tl data sfb.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) ==>
  (holfoot_implies_in_heap_or_null B
     (BAG_INSERT (holfoot_ap_data_list tl e1 data) sfb) e1)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_list_def,
   holfoot_implies_in_heap_or_null_def,
   holfoot_ap_data_list_seg_def,
   holfoot_implies_in_heap_pred___asl_exists] THEN
Cases_on `n` THENL [
   SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_REWRITE,
      COND_RAND, COND_RATOR, holfoot_implies_in_heap_pred___asl_false] THEN
   ASM_SIMP_TAC std_ss [GSYM holfoot_implies_in_heap_or_null_def,
      holfoot_implies_in_heap_or_null___equal_null],


   SIMP_TAC std_ss [GSYM holfoot_implies_in_heap_or_null_def] THEN
   MATCH_MP_TAC holfoot_implies_in_heap___implies___or_null THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num_SUC___implies_in_heap]
]);



val holfoot_ap_data_list_seg___implies_in_heap___COMPUTE = store_thm ("holfoot_ap_data_list_seg___implies_in_heap___COMPUTE",
``!e1 e2 B tl data.
  var_res_implies_unequal DISJOINT_FMAP_UNION B e1 e2 ==>
  ~(B = {||}) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>

  (holfoot_implies_in_heap B
     {| holfoot_ap_data_list_seg tl e1 data e2 |} e1)``,
SIMP_TAC std_ss [holfoot_ap_data_list_seg___implies_in_heap]);


val holfoot_ap_data_list___implies_in_heap_or_null___COMPUTE = store_thm ("holfoot_ap_data_list___implies_in_heap_or_null___COMPUTE",
``!B e1 tl data.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) ==>
  (holfoot_implies_in_heap_or_null B
     {|holfoot_ap_data_list_seg tl e1 data (var_res_exp_const 0)|} e1)``,
SIMP_TAC std_ss [holfoot_ap_data_list___implies_in_heap_or_null,
       GSYM holfoot_ap_data_list_def]);





val holfoot_ap_data_list_seg___var_res_prop_implies_eq___split = 
store_thm ("holfoot_ap_data_list_seg___var_res_prop_implies_eq___split",
``!tl e1 e2 data sfb1 sfb2 wpb rpb.
  (var_res_implies_unequal DISJOINT_FMAP_UNION (BAG_UNION
     sfb1 (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb2)) e1 e2) ==>

  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (var_res_prop_implies_eq DISJOINT_FMAP_UNION (wpb, rpb) sfb1
     (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb2) 
     (BAG_INSERT (asl_exists c. 
         asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
           (holfoot_ap_points_to e1 (LIST_TO_FMAP
              (ZIP (tl::MAP FST data, 
                    MAP var_res_exp_const (c::MAP (\x. HD (SND x)) data)))))                  
            (holfoot_ap_data_list_seg tl (var_res_exp_const c) (MAP (\(t,l). (t,TL l)) data) e2))
      (BAG_INSERT (var_res_prop_unequal DISJOINT_FMAP_UNION e1 e2)
      (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
           (EVERY (\x. ~NULL (SND x)) data /\ ALL_DISTINCT (tl::MAP FST data))) sfb2))))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
SIMP_TAC std_ss [var_res_prop_implies_eq_def] THEN
`var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (sfb1 + BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb2) =
 var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_UNION 
       (sfb1 + BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb2)
       {|(var_res_prop_unequal DISJOINT_FMAP_UNION e1 e2)|})` by ALL_TAC THEN1 (
   REWRITE_TAC [GSYM var_res_prop_implies_REWRITE] THEN
   MATCH_MP_TAC (MP_CANON var_res_implies_unequal___prop_implies) THEN
   ASM_REWRITE_TAC[]
) THEN
ASM_REWRITE_TAC[BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
POP_ASSUM (K ALL_TAC) THEN
Q.PAT_ASSUM `var_res_implies_unequal X Y e1 e2` (K ALL_TAC) THEN

ASM_SIMP_TAC std_ss [
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_prop___EQ] THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___COND_UNION, var_res_prop___COND_INSERT,
        VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
        VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg,
        VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg,
       FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
       ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF,
       EVERY_MAP, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN
REPEAT STRIP_TAC THEN


FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION, var_res_prop___PROP_UNION,
   var_res_prop___PROP_INSERT, IN_ABS,
   GSYM RIGHT_EXISTS_AND_THM] THEN

ASM_SIMP_TAC std_ss [var_res_bool_proposition_REWRITE,
   IN_ABS, asl_emp_DISJOINT_FMAP_UNION, asl_bool_EVAL,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   var_res_prop_equal_unequal_EXPAND,
   IN_SING, DISJOINT_FMAP_UNION___FEMPTY] THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

REPEAT GEN_TAC THEN
Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE___USED_VARS XXX ($asl_exists XX)` 
    (K ALL_TAC) THEN
Tactical.REVERSE (
   Cases_on `?c1 c2. (e1 (FST x) = SOME c1) /\ (e2 (FST x) = SOME c2) /\ ~(c1 = c2)`) THEN1 (
   Cases_on `e1 (FST x)` THEN Cases_on `e2 (FST x)` THEN
   FULL_SIMP_TAC std_ss []
) THEN
DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN

CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [holfoot_ap_data_list_seg_REWRITE])) THEN
FULL_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC std_ss [asl_bool_EVAL, IN_ABS,
   var_res_prop_equal_unequal_EXPAND]  THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_separation_combinator_def]);





val holfoot_ap_data_list_seg_num___REWRITE_START_EXP =
store_thm ("holfoot_ap_data_list_seg_num___REWRITE_START_EXP",
``
!n tl data startExp endExp startExp' s.
((startExp (FST s) = (startExp' (FST s))) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp)) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp')) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp))) ==>

(s IN (holfoot_ap_data_list_seg_num n tl startExp data endExp) =
 s IN (holfoot_ap_data_list_seg_num n tl startExp' data endExp))``,

Cases_on `n` THEN (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
     var_res_prop_equal_unequal_EXPAND, IN_ABS,
     holfoot_ap_points_to_def, LET_THM]
));




val holfoot_ap_data_list_seg_num___REWRITE_END_EXP =
store_thm ("holfoot_ap_data_list_seg_num___REWRITE_END_EXP",
``
!n tl data startExp endExp endExp' s.
((endExp (FST s) = (endExp' (FST s))) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp)) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp)) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp'))) ==>

(s IN (holfoot_ap_data_list_seg_num n tl startExp data endExp) =
 s IN (holfoot_ap_data_list_seg_num n tl startExp data endExp'))``,


Induct_on `n` THEN (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
     var_res_prop_equal_unequal_EXPAND, IN_ABS]
) THEN
REPEAT STRIP_TAC THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!tl data. X` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]);



val holfoot_ap_data_list_seg_num___START_EXP_IN_FDOM =
store_thm ("holfoot_ap_data_list_seg_num___START_EXP_IN_FDOM",
``!n tl data startExp endExp s.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp)) /\
(s IN (holfoot_ap_data_list_seg_num (SUC n) tl startExp data endExp))) ==>  
((IS_SOME (startExp (FST s)) /\ (THE (startExp (FST s)) IN FDOM (SND s))))``,

SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
   IN_ABS, holfoot_ap_points_to_def, LET_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE,
   FDOM_FUNION, IN_UNION, IN_SING]);


val holfoot_ap_data_list_seg_num___END_EXP_NOT_IN_FDOM =
store_thm ("holfoot_ap_data_list_seg_num___END_EXP_NOT_IN_FDOM",
``!n tl data startExp endExp s.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp)) /\
(s IN (holfoot_ap_data_list_seg_num n tl startExp data endExp))) ==>  
s IN holfoot_not_in_heap endExp``,

Induct_on `n` THEN1 (
   SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
      var_res_prop_equal_unequal_EXPAND, IN_ABS, LET_THM,
      asl_emp_DISJOINT_FMAP_UNION, IN_SING, FDOM_FEMPTY, NOT_IN_EMPTY,
      holfoot_not_in_heap_def, GSYM IS_SOME_EXISTS]
) THEN
SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE, IN_ABS] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `data' = MAP (\ (t,l). (t,TL l)) data` THEN
Q.PAT_ASSUM `!tl data startExp. X` (MP_TAC o Q.SPECL [`tl`, `data'`, `var_res_exp_const n'`, `endExp`, `(FST (s:holfoot_state), s2)`]) THEN
ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN

FULL_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS] THEN
Q.PAT_ASSUM `IS_SOME (endExp (FST s))` ASSUME_TAC THEN
Q.PAT_ASSUM `IS_SOME (startExp (FST s))` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE,
   holfoot_not_in_heap_def, IS_SOME_EXISTS,
   FDOM_FUNION, IN_UNION, holfoot_ap_points_to_def, LET_THM,
   IN_SING, IN_ABS, var_res_prop_equal_unequal_EXPAND, GSYM LEFT_FORALL_IMP_THM] THEN
FULL_SIMP_TAC std_ss []);



val holfoot_ap_data_list_seg_num___NULL_NOT_IN_FDOM =
store_thm ("holfoot_ap_data_list_seg_num___NULL_NOT_IN_FDOM",
``!n tl data startExp endExp s.
(s IN (holfoot_ap_data_list_seg_num n tl startExp data endExp)) ==>  
~(0 IN FDOM (SND s))``,

Induct_on `n` THEN1 (
   SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
      var_res_prop_equal_unequal_EXPAND, IN_ABS, LET_THM,
      asl_emp_DISJOINT_FMAP_UNION, IN_SING, FDOM_FEMPTY, NOT_IN_EMPTY,
      holfoot_not_in_heap_def, GSYM IS_SOME_EXISTS]
) THEN
SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num_REWRITE, IN_ABS,
   COND_RAND, COND_RATOR, asl_bool_EVAL, asl_star_def,
   holfoot_separation_combinator___REWRITE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, FDOM_FUNION, IN_UNION] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE CONJ_TAC THEN1 METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM,
   IN_SING]);



val holfoot_ap_data_list_seg_num___SPLIT = store_thm ("holfoot_ap_data_list_seg_num___SPLIT",
``!n m e1 e2 tl data.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>

(holfoot_ap_data_list_seg_num (n+m) tl e1 data e2 =
 asl_and (holfoot_not_in_heap e2)
 asl_exists c.
   asl_star holfoot_separation_combinator
   (holfoot_ap_data_list_seg_num n tl e1 
       (MAP (\x. (FST x, TAKE n (SND x))) data) (var_res_exp_const c))
   (holfoot_ap_data_list_seg_num m tl (var_res_exp_const c)
       (MAP (\x. (FST x, DROP n (SND x))) data) e2))``,

Induct_on `n` THEN1 (
   SIMP_TAC (list_ss++boolSimps.ETA_ss) [holfoot_ap_data_list_seg_num_REWRITE, EVERY_MAP,
      MAP_MAP_o, combinTheory.o_DEF] THEN
   REPEAT GEN_TAC THEN
   Tactical.REVERSE (Cases_on `ALL_DISTINCT (tl::MAP FST data)`) THEN1 (
      ASM_SIMP_TAC std_ss [GSYM ALL_DISTINCT, asl_false___asl_star_THM] THEN
      SIMP_TAC std_ss [asl_exists_ELIM, asl_bool_REWRITES] THEN
      METIS_TAC[holfoot_ap_data_list_seg_num___DATA_PROPS]
   ) THEN
   `MAP (\x. x) data = data` by ALL_TAC THEN1 (
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on `data` THEN ASM_SIMP_TAC list_ss []
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL] THEN
   ASM_SIMP_TAC std_ss [
      asl_star___VAR_RES_IS_STACK_IMPRECISE,
      holfoot_separation_combinator_def, IN_ABS,
      VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
      VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   GEN_TAC THEN
   SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
      asl_emp_DISJOINT_FMAP_UNION, DISJOINT_FMAP_UNION___FEMPTY, IN_SING,
      var_res_exp_const_def, COND_RAND, COND_RATOR, asl_bool_EVAL] THEN
   SIMP_TAC std_ss [GSYM var_res_exp_const_def] THEN
   Tactical.REVERSE (Cases_on `?c1. e1 (FST x) = SOME c1`) THEN1 (
      Cases_on `e1 (FST x)` THEN FULL_SIMP_TAC std_ss [] THEN
      METIS_TAC [holfoot_ap_data_list_seg_num___EXP_DEFINED, optionTheory.option_CLAUSES]
   ) THEN
   Tactical.REVERSE (Cases_on `?c2. e2 (FST x) = SOME c2`) THEN1 (
      Cases_on `e2 (FST x)` THEN FULL_SIMP_TAC std_ss [] THEN
      METIS_TAC [holfoot_ap_data_list_seg_num___EXP_DEFINED, optionTheory.option_CLAUSES]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC (prove (``((A = B2) /\ (A ==> B1)) ==> (A = (B1 /\ B2))``, METIS_TAC[])) THEN
   CONJ_TAC THENL [
      MATCH_MP_TAC  holfoot_ap_data_list_seg_num___REWRITE_START_EXP THEN
      FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
      SIMP_TAC std_ss [var_res_exp_const_def],



      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC holfoot_ap_data_list_seg_num___END_EXP_NOT_IN_FDOM THEN
      Q.EXISTS_TAC `m` THEN Q.EXISTS_TAC `tl` THEN
      Q.EXISTS_TAC `data` THEN Q.EXISTS_TAC `e1` THEN
      ASM_SIMP_TAC std_ss []
   ]
) THEN

REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `ALL_DISTINCT (tl::MAP FST data)`) THEN1 (
   ASM_SIMP_TAC (std_ss++boolSimps.ETA_ss) [ADD_CLAUSES, holfoot_ap_data_list_seg_num_REWRITE,
      MAP_MAP_o, combinTheory.o_DEF, asl_false___asl_star_THM,
      asl_exists_ELIM, asl_bool_REWRITES]
) THEN
Q.ABBREV_TAC `data1 = (MAP (\x. (FST x,TAKE (SUC n) (SND x))) data)` THEN
Q.ABBREV_TAC `data2 = (MAP (\x. (FST x,DROP (SUC n) (SND x))) data)` THEN
`ALL_DISTINCT (tl::MAP FST data1) /\ ALL_DISTINCT (tl::MAP FST data2)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `data1` THEN Q.UNABBREV_TAC `data2` THEN
   ASM_SIMP_TAC (std_ss++boolSimps.ETA_ss) [MAP_MAP_o, combinTheory.o_DEF]
) THEN
`EVERY (\x. LENGTH (SND x) = SUC n + m) data =
 (EVERY (\x. LENGTH (SND x) = SUC n) data1 /\
  EVERY (\x. LENGTH (SND x) = m) data2)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `data1` THEN Q.UNABBREV_TAC `data2` THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Induct_on `data` THEN (
       ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) []
   ) THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN1 (
      ASM_SIMP_TAC list_ss []
   ) THEN
   `SND h = TAKE (SUC n) (SND h) ++ DROP (SUC n) (SND h)` by
         REWRITE_TAC[TAKE_DROP] THEN
   ONCE_ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN
   REWRITE_TAC[LENGTH_APPEND] THEN
   ASM_SIMP_TAC list_ss []
) THEN

Tactical.REVERSE (Cases_on `EVERY (\x. LENGTH (SND x) = SUC n + m) data`) THEN1 (
   `(holfoot_ap_data_list_seg_num (SUC n + m) tl e1 data e2 = asl_false) /\
    ((!c. (holfoot_ap_data_list_seg_num (SUC n) tl e1 data1
          (var_res_exp_const c)) = asl_false) \/
     (!c. holfoot_ap_data_list_seg_num m tl (var_res_exp_const c) data2 e2 = 
          asl_false))` by 
       METIS_TAC[holfoot_ap_data_list_seg_num___DATA_PROPS] THEN
   ASM_SIMP_TAC std_ss [asl_false___asl_star_THM, asl_exists_ELIM, asl_bool_REWRITES]
) THEN
FULL_SIMP_TAC std_ss [ADD_CLAUSES, numTheory.NOT_SUC] THEN

`EVERY (\x. ~(NULL (SND x))) data /\
 EVERY (\x. ~(NULL (SND x))) data1` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   Cases_on `SND x` THEN FULL_SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC std_ss [asl_bool_EVAL, EXTENSION, holfoot_separation_combinator_def,
   asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS,
   VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
ASM_SIMP_TAC std_ss [ADD_CLAUSES, holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   holfoot_separation_combinator_def, asl_bool_EVAL, IN_ABS] THEN

GEN_TAC THEN
Tactical.REVERSE (Cases_on `x IN holfoot_not_in_heap e2`) THEN1 (
   FULL_SIMP_TAC std_ss [holfoot_not_in_heap_def, IN_ABS] THEN
   Cases_on `e2 (FST x)` THEN FULL_SIMP_TAC std_ss [] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE, holfoot_ap_points_to_def, IN_ABS,
     LET_THM] THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING,
     var_res_prop_equal_unequal_EXPAND, IN_ABS, IS_SOME_EXISTS] THEN
   METIS_TAC[optionTheory.option_CLAUSES]
) THEN
ASM_SIMP_TAC std_ss [
   asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS,
   VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   DISJOINT_FMAP_UNION___REWRITE, FDOM_FUNION, DISJOINT_UNION_BOTH,
   asl_bool_EVAL, holfoot_separation_combinator_def,
   MAP_MAP_o, combinTheory.o_DEF] THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [DISJOINT_SYM] THEN
REPEAT STRIP_TAC THEN

Q.PAT_ASSUM `!m' e1' e2'. X` (K ALL_TAC) THEN

CONV_TAC (LHS_CONV (RESORT_EXISTS_CONV (fn [x1,x2,x3,x4,x5] => [x3,x5,x1,x2,x4]))) THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [DISJOINT_SYM, FUNION_ASSOC] THEN
REPEAT STRIP_TAC THEN


Q.ABBREV_TAC `L =  LIST_TO_FMAP (ZIP (tl::MAP FST data,
                   MAP (var_res_exp_const:num -> holfoot_a_expression) (n'::MAP (\x. HD (SND x)) data)))` THEN
`(LIST_TO_FMAP (ZIP (tl::MAP FST data1,
      MAP var_res_exp_const (n'::MAP (\x. HD (SND x)) data1)))) = L` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `L` THEN
   Q.UNABBREV_TAC `data1` THEN
   SIMP_TAC (std_ss++boolSimps.ETA_ss) [MAP_MAP_o, combinTheory.o_DEF] THEN
   Tactical.REVERSE (`MAP (\x. HD (TAKE (SUC n) (SND x))) data =
    MAP (\x. HD (SND x)) data` by ALL_TAC) THEN1 ASM_REWRITE_TAC[] THEN

   Q.PAT_ASSUM `EVERY X data` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Induct_on `data` THEN
   ASM_SIMP_TAC list_ss [] THEN
   GEN_TAC THEN Cases_on `SND h` THEN
   SIMP_TAC list_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

Q.ABBREV_TAC `data1' = MAP (\ (t,l). (t,TL l)) data1` THEN
`(MAP (\x. (FST x,TAKE n (TL (SND x)))) data = data1') /\
 (MAP (\x. (FST x,DROP n (TL (SND x)))) data = data2)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `EVERY X data` MP_TAC THEN
   Q.UNABBREV_TAC `data1'` THEN Q.UNABBREV_TAC `data1` THEN
   Q.UNABBREV_TAC `data2` THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN

   Induct_on `data` THEN ASM_SIMP_TAC list_ss [] THEN
   GEN_TAC THEN Cases_on `SND h` THEN
   SIMP_TAC list_ss []
) THEN
ASM_REWRITE_TAC[] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

SIMP_TAC std_ss [holfoot_not_in_heap_def, var_res_prop_equal_unequal_EXPAND, IN_ABS,
   var_res_exp_const_def, FDOM_FUNION, IN_UNION] THEN
Tactical.REVERSE (Cases_on `?c1 c2. (e1 (FST x) = SOME c1) /\ (e2 (FST x) = SOME c2)`) THEN1 (
   Cases_on `e1 (FST x)` THEN SIMP_TAC std_ss [] THEN
   IMP_RES_TAC holfoot_ap_data_list_seg_num___EXP_DEFINED THEN
   Cases_on `e2 (FST x)` THEN FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN

`FDOM s1 = {c1}` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM]
) THEN
FULL_SIMP_TAC std_ss [holfoot_not_in_heap_def, IN_ABS,
   FDOM_FUNION, IN_UNION, IN_SING] THEN

Q.PAT_ASSUM `(FST x, es2) IN X` MP_TAC THEN
Cases_on `m` THENL [
   ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
     IN_ABS, var_res_prop_equal_unequal_EXPAND, var_res_exp_const_def],

   STRIP_TAC THEN
   `c IN FDOM es2` by ALL_TAC THEN1 (
      MP_TAC (Q.SPECL [`n''`, `tl`, `data2`, `var_res_exp_const c`, `e2`, `(FST (x:holfoot_state), es2)`] 
           holfoot_ap_data_list_seg_num___START_EXP_IN_FDOM) THEN
      ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
      SIMP_TAC std_ss [var_res_exp_const_def]
   ) THEN
   Q.PAT_ASSUM `DISJOINT (FDOM es2) {c1}` MP_TAC THEN
   ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
      IN_SING] THEN
   METIS_TAC[]
]);

      




val holfoot_ap_data_list_seg_num___SAME_START_END = store_thm ("holfoot_ap_data_list_seg_num___SAME_START_END",
``!n n' e1 e2 e1' e2' tl data data' st h1 h2 h.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1') /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2') /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 h /\
 (st, h1) IN holfoot_ap_data_list_seg_num n tl e1  data  e2 /\
 (st, h2) IN holfoot_ap_data_list_seg_num n' tl e1' data' e2' /\
 (e1 st = e1' st) /\
 (e2 st = e2' st)) ==> (n = n')``,

Induct_on `n` THEN1 (
   Cases_on `n'` THEN (
      SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
          IN_ABS, var_res_prop_equal_unequal_EXPAND]
   )
) THEN
Cases_on `n'` THEN (
   SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
       IN_ABS, var_res_prop_equal_unequal_EXPAND]
) THEN
REPEAT STRIP_TAC THEN
`n' = n'''` by ALL_TAC THEN1 (
   `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1  h /\
    ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1' h` by 
      METIS_TAC[ASL_IS_SUBSTATE_INTRO, ASL_IS_SUBSTATE___TRANS,
         IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN
   FULL_SIMP_TAC list_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS,
      LIST_TO_FMAP_THM, FEVERY_DEF, FDOM_FUPDATE, IN_INSERT, 
      DISJ_IMP_THM, FORALL_AND_THM, FAPPLY_FUPDATE_THM,
      var_res_exp_const_def] THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION, IN_SING]
) THEN
`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2  h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2' h`by ALL_TAC THEN1 (
    METIS_TAC[ASL_IS_SUBSTATE_INTRO, ASL_IS_SUBSTATE___TRANS,
       IS_SEPARATION_COMBINATOR___FINITE_MAP]
) THEN    
Q.PAT_ASSUM `!n' e1 e2 e1' e2'. X` 
   (MP_TAC o Q.SPECL [`n''`, 
      `var_res_exp_const n'`, `e2`,
      `var_res_exp_const n'''`, `e2'`, `tl`,
      `(MAP (\ (t,l). (t,TL l)) data)`,
      `(MAP (\ (t,l). (t,TL l)) data')`,
      `st`, `s2`, `s2'`, `h`]) THEN
FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]);





val holfoot_ap_data_list_seg_num___SAME_LENGTH_START = store_thm ("holfoot_ap_data_list_seg_num___SAME_LENGTH_START",
``!n e1 e2 e1' e2' tl data data' st h1 h2 h.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1') /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2') /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 h /\
 (st,h1) IN holfoot_ap_data_list_seg_num n tl e1  data  e2 /\
 (st,h2) IN holfoot_ap_data_list_seg_num n tl e1' data' e2' /\
 (e1 st = e1' st)) ==>

((e2 st = e2' st) /\ (h1 = h2) /\
 (!x x'. (MEM x data /\ MEM x' data' /\ (FST x = FST x')) ==>
         (SND x = SND x')))``,


Induct_on `n` THEN1 (
   SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
      IN_ABS, var_res_prop_equal_unequal_EXPAND, asl_emp_DISJOINT_FMAP_UNION, IN_SING] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   Cases_on `e2 st` THEN FULL_SIMP_TAC std_ss [] THEN
   Cases_on `e2' st` THEN FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, NULL_EQ]
) THEN

SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
   IN_ABS, var_res_prop_equal_unequal_EXPAND, asl_emp_DISJOINT_FMAP_UNION, IN_SING] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `!e1 e2 e1' e2'. X` (MP_TAC o
   Q.SPECL [`var_res_exp_const n'`, `e2`, `var_res_exp_const n'`, 
            `e2'`, `tl`, `MAP (\ (t,l). (t,TL l)) data`,
            `MAP (\ (t,l). (t,TL l)) data'`, `st`, `s2`, `s2'`, `h`]) THEN
`?c1 c2 c2'. (e1 st = SOME c1) /\ (e1' st = SOME c1) /\ (e2 st = SOME c2) /\ (e2' st = SOME c2')` by
   METIS_TAC[IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN


`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1  h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1' h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2  h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2' h` by 
      METIS_TAC[ASL_IS_SUBSTATE_INTRO, ASL_IS_SUBSTATE___TRANS,
         IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
`(s1 = s1')` by ALL_TAC THEN1 (
   REPEAT (Q.PAT_ASSUM `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION X h` MP_TAC) THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def,
      LET_THM, IN_ABS, GSYM fmap_EQ_THM, IN_SING,
      ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION]
) THEN
`n'' = n'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC list_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS,
      LIST_TO_FMAP_THM, FEVERY_DEF, FDOM_FUPDATE, IN_INSERT, 
      DISJ_IMP_THM, FORALL_AND_THM, FAPPLY_FUPDATE_THM,
      var_res_exp_const_def]
) THEN
FULL_SIMP_TAC std_ss [] THEN
SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [MEM_MAP,
   GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
`?d_h1 d_tl1 d_h2 d_tl2.
   ((SND x) = d_h1 :: d_tl1) /\
   ((SND x') = d_h2 :: d_tl2)` by ALL_TAC THEN1 (

   Cases_on `SND x` THEN
   Cases_on `SND x'` THEN
   FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
   METIS_TAC[EVERY_MEM, NULL]
) THEN

`TL (d_h1::d_tl1) = TL (d_h2::d_tl2)` by METIS_TAC[] THEN
FULL_SIMP_TAC list_ss [] THEN

FULL_SIMP_TAC list_ss [holfoot_ap_points_to_def, IN_ABS,
   LET_THM, FEVERY_DEF, FDOM_LIST_TO_FMAP, IN_LIST_TO_SET,
   ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, DISJ_IMP_THM, FORALL_AND_THM,
   LIST_TO_FMAP_THM, FAPPLY_FUPDATE_THM, MEM_ZIP_EQ, MEM_MAP,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, IN_INSERT] THEN

Q.PAT_ASSUM `!x''. MEM x'' data' ==> XXX x''` 
   (MP_TAC o Q.SPEC `x'`) THEN
Q.PAT_ASSUM `!x''. MEM x'' data ==> XXX x''` 
   (MP_TAC o Q.SPEC `x`) THEN

`~(FST x' = tl)` by METIS_TAC[] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [IS_SOME_EXISTS,
  GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
  MAP_ZIP_EQ] THEN

Q.ABBREV_TAC `L  = (MAP (\x''. (FST x'',(var_res_exp_const (HD (SND x''))):holfoot_a_expression)) data)` THEN
Q.ABBREV_TAC `L' = (MAP (\x''. (FST x'',(var_res_exp_const (HD (SND x''))):holfoot_a_expression)) data')` THEN

`ALL_DISTINCT (MAP FST L) /\
 ALL_DISTINCT (MAP FST L') /\
 MEM (FST x', var_res_exp_const d_h1) L /\
 MEM (FST x', var_res_exp_const d_h2) L'` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   ASM_SIMP_TAC (std_ss++boolSimps.ETA_ss) [MAP_MAP_o, combinTheory.o_DEF,
       MEM_MAP, var_res_exp_eq_THM] THEN
   REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `x`  THEN ASM_SIMP_TAC list_ss [],
      Q.EXISTS_TAC `x'` THEN ASM_SIMP_TAC list_ss []
   ]
) THEN
`(LIST_TO_FMAP L ' (FST x') = (var_res_exp_const d_h1)) /\
 (LIST_TO_FMAP L' ' (FST x') = (var_res_exp_const d_h2))` by ALL_TAC THEN1 (
   METIS_TAC [LIST_TO_FMAP___ALL_DISTINCT]
) THEN
ASM_SIMP_TAC std_ss [var_res_exp_const_def]);









val VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num___REWRITE",
``!e3 e1 e2 tl data L wpb rpb sfb_context sfb_split sfb_imp n.

((tl IN FDOM L) /\ (L ' tl = e3) /\ (LIST_TO_SET (MAP FST data) SUBSET FDOM L) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
==>
 VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (SUC n) tl e1 data e2) sfb_imp) 


   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_context)
   sfb_split
   (BAG_UNION (LIST_TO_BAG (MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (HD (SND x)))) data))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          ((EVERY (\x. ~(NULL (SND x))) data) /\
           ALL_DISTINCT (tl::MAP FST data)))
    (BAG_INSERT (var_res_prop_unequal DISJOINT_FMAP_UNION e1 e2) (
    BAG_INSERT (holfoot_ap_data_list_seg_num n tl e3 (MAP (\x. (FST x, TL (SND x))) data) e2) sfb_imp)
   )))``,

REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN

`(!x. MEM x data ==>
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
      (SET_OF_BAG (wpb + rpb)) (L ' (FST x))) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
      (SET_OF_BAG (wpb + rpb)) e3` by ALL_TAC THEN1 (

   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET,
      MEM_MAP, GSYM LEFT_FORALL_IMP_THM, FEVERY_DEF] THEN
   METIS_TAC[]
) THEN

MATCH_MP_TAC (prove (``((A /\ B) /\ (A /\ B ==> (P = Q))) ==>
((A ==> P) = (B ==> Q))``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      FINITE_LIST_TO_BAG, containerTheory.IN_LIST_TO_BAG] THEN
   SIMP_TAC std_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      PAIR_FORALL_THM] THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal],
       []) THEN
   ASM_SIMP_TAC list_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN   
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN
REPEAT STRIP_TAC THEN

Q.ABBREV_TAC `sfb_const = sfb_imp + (sfb_rest + sfb_context)` THEN
ASM_SIMP_TAC std_ss [GSYM ASSOC_BAG_UNION, BAG_UNION_EMPTY,
   BAG_UNION_INSERT] THEN

`var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb_const` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfb_const` THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND_UNION]
) THEN

`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___PROP_UNION,
   var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION, IN_ABS,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE, 
   COND_RATOR, COND_RAND, asl_bool_EVAL,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition] THEN

SIMP_TAC std_ss [var_res_bool_proposition_REWRITE,
   var_res_prop_weak_unequal_def,
   var_res_prop_unequal_def, var_res_prop_weak_binexpression_def,
   asl_emp_DISJOINT_FMAP_UNION, var_res_prop_binexpression_def,
   IN_SING, IN_ABS, LET_THM, var_res_stack_proposition_def,
   DISJOINT_FMAP_UNION___FEMPTY] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
Tactical.REVERSE (Cases_on `?c1 c2. (e1 (FST s) = SOME c1) /\ (e2 (FST s) = SOME c2)`) THEN1 (
   SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN


Q.ABBREV_TAC `eq_props:holfoot_a_proposition = var_res_prop___PROP DISJOINT_FMAP_UNION (wpb,rpb)
  (LIST_TO_BAG (MAP (\x.
     var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x))
         (var_res_exp_const (HD (SND x)))) data))` THEN

`eq_props = \s.
    ((SND s = FEMPTY) /\ 
     (!v. v <: wpb ==> var_res_sl___has_write_permission v (FST s)) /\
     (!v. v <: rpb ==> var_res_sl___has_read_permission v (FST s)) /\
     EVERY (\x. (L ' (FST x) (FST s) = SOME (HD (SND x)))) data)` by ALL_TAC THEN1 (
    
    Q.PAT_ASSUM `FEVERY XXX L` MP_TAC THEN
    Q.PAT_ASSUM `XXX SUBSET FDOM L` MP_TAC THEN
    Q.UNABBREV_TAC `eq_props` THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [
       var_res_prop___PROP___REWRITE,
       IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS,
       containerTheory.LIST_TO_BAG_def, EXTENSION] THEN
    Induct_on `data` THEN1 (
       SIMP_TAC list_ss [
          IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS,
          containerTheory.LIST_TO_BAG_def,
          var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___FINITE_MAP,
          asl_emp_DISJOINT_FMAP_UNION, IN_SING,
          var_res_prop_stack_true_REWRITE]
    ) THEN
    ASM_SIMP_TAC list_ss [
       IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS,
       containerTheory.LIST_TO_BAG_def,
       var_res_bigstar_REWRITE_EXT, INSERT_SUBSET] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `h` THEN
    FULL_SIMP_TAC std_ss [] THEN
    Q.MATCH_ABBREV_TAC `x IN asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION) P1 P2 = X` THEN
    `(VAR_RES_IS_STACK_IMPRECISE P1) /\ (VAR_RES_IS_STACK_IMPRECISE P2)` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `P1` THEN
       Q.UNABBREV_TAC `P2` THEN
       CONSEQ_REWRITE_TAC ([], [
              VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
              VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar], []) THEN
       FULL_SIMP_TAC std_ss [FEVERY_DEF, IS_SEPARATION_COMBINATOR___FINITE_MAP,
           IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
           FEVERY_DEF, BAG_EVERY, BAG_IN_LIST_TO_BAG, MEM_MAP,
           DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM,
          VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def, FEVERY_DEF,
          SUBSET_DEF, IN_INSERT, IN_LIST_TO_SET] THEN
       REPEAT STRIP_TAC THEN
       MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal THEN
       ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
    ) THEN
    ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
       IS_SEPARATION_COMBINATOR___FINITE_MAP, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
       IN_ABS, DISJOINT_FMAP_UNION___FEMPTY] THEN
    Q.UNABBREV_TAC `P1` THEN
    Q.UNABBREV_TAC `X` THEN
    ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
       asl_emp_DISJOINT_FMAP_UNION, IN_SING, var_res_exp_const_def, IS_SOME_EXISTS,
       GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM, DISJOINT_FMAP_UNION___FEMPTY]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN Q.UNABBREV_TAC `eq_props` THEN

ASM_SIMP_TAC (std_ss++CONJ_ss++EQUIV_EXTRACT_ss) [var_res_prop_equal_unequal_EXPAND,
   asl_bool_EVAL, IN_ABS, var_res_bool_proposition_REWRITE,
   asl_emp_DISJOINT_FMAP_UNION, IN_SING,
   DISJOINT_FMAP_UNION___FEMPTY, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, var_res_exp_const_def, IS_SOME_EXISTS] THEN

REPEAT STRIP_TAC THEN

SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE] THEN
HO_MATCH_MP_TAC (prove (``
((!s1 s2 s3. ((?n. X s1 n s2 s3) = Y s3 s2 s1))) ==>
((?s2 n' es1 es2. X s2 n' es1 es2) = (?s1' s1'' s2''. Y s1' s1'' s2''))``,
   METIS_TAC[])) THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [FDOM_FUNION,
   DISJOINT_UNION_BOTH, DISJOINT_SYM] THEN
REPEAT STRIP_TAC THEN
`(!v. v <: wpb ==> var_res_sl___has_write_permission v (FST s)) /\
 (!v. v <: rpb ==> var_res_sl___has_read_permission v (FST s))` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
       IS_SEPARATION_COMBINATOR___FINITE_MAP]
) THEN
`FUNION (FUNION s1''' s1'') s2''' = FUNION s1'' (FUNION s1''' s2''')` by ALL_TAC THEN1 (
    METIS_TAC[FUNION_ASSOC, FUNION_COMM]
) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `var_res_prop___PROP f (wpb,rpb) XX s` MP_TAC THEN

ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT,    var_res_prop___COND_UNION,
   DISJOINT_FMAP_UNION___REWRITE] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FDOM s1''' = {c1}`) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM]
) THEN
`s1 = s1'''` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `X = SOME c1` ASSUME_TAC THEN
   REWRITE_TAC[GSYM fmap_EQ_THM] THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def,
      IN_ABS, LET_THM, IN_ABS, IN_SING] THEN
   `s1''' ' c1 = FUNION s1'' (FUNION s1''' s2''') ' c1` by ALL_TAC THEN1 (
       FULL_SIMP_TAC std_ss [FUNION_DEF, IN_SING, DISJOINT_DEF,
           EXTENSION, IN_SING, IN_INTER, NOT_IN_EMPTY]
   ) THEN
   ASM_REWRITE_TAC[] THEN  
   ASM_SIMP_TAC std_ss [FUNION_DEF, IN_SING]
) THEN
FULL_SIMP_TAC std_ss [] THEN

ASM_SIMP_TAC list_ss [holfoot_ap_points_to_def,
   LET_THM, IN_ABS, ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF,
   LIST_TO_FMAP_THM, FEVERY_DEF] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [FDOM_FUPDATE, IN_INSERT,
   FDOM_LIST_TO_FMAP, IN_LIST_TO_SET,
   MAP_MAP_o, combinTheory.o_DEF, IS_SOME_EXISTS,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [DISJ_IMP_THM, FORALL_AND_THM,
   MEM_MAP, GSYM LEFT_FORALL_IMP_THM, MEM_ZIP_EQ,
   FAPPLY_FUPDATE_THM, var_res_exp_const_def] THEN
`c1 <> 0` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `X = SOME c1` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_points_to_def,
      IN_ABS, LET_THM]
) THEN
`!x''. MEM x'' data ==> ((if FST x'' = tl then
           K (SOME (s1''' ' c1 tl))
         else
           LIST_TO_FMAP
             (MAP (\x. (FST (FST x),K (SOME (HD (SND (SND x))))))
                (ZIP (data,data))) ' (FST x'')) (FST s) =
         SOME (HD (SND x'')))` by ALL_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++CONJ_ss) [PAIR_FORALL_THM, holfoot_ap_points_to_def,
      IN_ABS, LET_THM, FEVERY_DEF, IS_SOME_EXISTS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [ALL_DISTINCT, MEM_MAP, MAP_ZIP_EQ] THEN
   `~(x1 = tl)` by METIS_TAC[pairTheory.FST] THEN
   `LIST_TO_FMAP (MAP (\x. (FST x,(K (SOME (HD (SND x)))):holfoot_a_expression)) data) ' x1 = (K (SOME (HD x2)))` by ALL_TAC THEN1 (
      MATCH_MP_TAC LIST_TO_FMAP___ALL_DISTINCT THEN
      SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF,
        MEM_MAP, PAIR_EXISTS_THM] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
SIMP_TAC std_ss [GSYM EVERY_MEM] THEN

`(EVERY (\x'. HD (SND x') = s1''' ' c1 (FST x')) data =
  EVERY (\x. L ' (FST x) (FST s) = SOME (HD (SND x))) data) /\
 (e3 (FST s) = SOME (s1''' ' c1 tl))` by ALL_TAC THEN1 (
   Tactical.REVERSE (
      `(e3 (FST s) = SOME (s1''' ' c1 tl)) /\
       EVERY (\x'. L ' (FST x') (FST s) = SOME (s1''' ' c1 (FST x'))) data` by ALL_TAC) THEN1 (
          FULL_SIMP_TAC std_ss [EVERY_MEM, PAIR_FORALL_THM] THEN
          METIS_TAC[SOME_11]
   ) THEN
   Q.PAT_ASSUM `(FST s, s1''') IN XXXX` MP_TAC THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_points_to_def, IN_ABS,
     LET_THM, FEVERY_DEF, IS_SOME_EXISTS, 
     GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
     EVERY_MEM] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[],

      Tactical.REVERSE (`FST x' IN FDOM L` by ALL_TAC) THEN1 ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET, MEM_MAP, GSYM LEFT_FORALL_IMP_THM]
   ]
) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

Q.ABBREV_TAC `data' = (MAP (\ (t,l). (t,TL l)) data)` THEN
`MAP (\x. (FST x,TL (SND x))) data = data'` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `data'` THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [FUN_EQ_THM, PAIR_FORALL_THM]
) THEN
ASM_SIMP_TAC std_ss [] THEN

MATCH_MP_TAC holfoot_ap_data_list_seg_num___REWRITE_START_EXP THEN
ASM_SIMP_TAC std_ss [] THEN

FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
   GSYM var_res_exp_const_def, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   FEVERY_DEF] THEN
METIS_TAC[]);











val VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num = store_thm ("VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num",
``!e3 e1 e2 tl data L wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr n.

((tl IN FDOM L) /\ (L ' tl = e3) /\ (LIST_TO_SET (MAP FST data) SUBSET FDOM L) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (SUC n) tl e1 data e2) sfb_imp) sfb_restP) =
(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_context)
   sfb_split
   (BAG_UNION (LIST_TO_BAG (MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (HD (SND x)))) data))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          ((EVERY (\x. ~(NULL (SND x))) data) /\
           ALL_DISTINCT (tl::MAP FST data)))
    (BAG_INSERT (var_res_prop_unequal DISJOINT_FMAP_UNION e1 e2) (
    BAG_INSERT (holfoot_ap_data_list_seg_num n tl e3 (MAP (\x. (FST x, TL (SND x))) data) e2) sfb_imp)
   ))) sfb_restP))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num___REWRITE THEN
ASM_REWRITE_TAC[]);






val VAR_RES_FRAME_SPLIT___points_to___data_list_seg___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___points_to___data_list_seg___REWRITE",
``!e3 e1 e2 tl data L wpb rpb sfb_context sfb_split sfb_imp.

((tl IN FDOM L) /\ (L ' tl = e3) /\ (LIST_TO_SET (MAP FST data) SUBSET FDOM L) /\
(var_res_implies_unequal DISJOINT_FMAP_UNION
  (sfb_context + (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)) e1 e2) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
==>
 VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb_imp) 


   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_context)
   sfb_split
   (BAG_UNION (LIST_TO_BAG (MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (HD (SND x)))) data))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          ((EVERY (\x. ~(NULL (SND x))) data) /\
           ALL_DISTINCT (tl::MAP FST data))) ( 
    BAG_INSERT (holfoot_ap_data_list_seg tl e3 (MAP (\x. (FST x, TL (SND x))) data) e2) sfb_imp)
   ))``,


REPEAT STRIP_TAC THEN
`(!x. MEM x data ==>
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
      (SET_OF_BAG (wpb + rpb)) (L ' (FST x))) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
      (SET_OF_BAG (wpb + rpb)) e3` by ALL_TAC THEN1 (

   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET,
      MEM_MAP, GSYM LEFT_FORALL_IMP_THM, FEVERY_DEF] THEN
   METIS_TAC[]
) THEN

MP_TAC (Q.SPECL [`e3`, `e1`, `e2`, `tl`, `data`, `L`, `wpb`, `rpb`, `sfb_context`,
  `sfb_split`, `sfb_imp`] VAR_RES_FRAME_SPLIT___points_to___data_list_seg_num___REWRITE) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_INSERT,
   prove (
   ``BAG_INSERT sf (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data e2) B) =
    (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data e2) (BAG_INSERT sf B))``,
   PROVE_TAC[bagTheory.BAG_INSERT_commutes]),
   prove (
   ``BAG_INSERT sf (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) B) =
    (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) (BAG_INSERT sf B))``,
   PROVE_TAC[bagTheory.BAG_INSERT_commutes])] THEN
STRIP_TAC THEN
POP_ASSUM (fn thm =>
   MP_TAC (HO_PART_MATCH 
         (el 3 o strip_conj o fst o dest_imp o snd o strip_forall)
         VAR_RES_FRAME_SPLIT___REWRITE_OK___exists_imp
          (concl thm)) THEN
   ASM_REWRITE_TAC[thm]) THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num] THEN



ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_def,
   prove (
   ``BAG_INSERT sf (BAG_INSERT (var_res_prop_unequal f e1 e2) B) =
    (BAG_INSERT (var_res_prop_unequal f e1 e2) (BAG_INSERT sf B))``,
   PROVE_TAC[bagTheory.BAG_INSERT_commutes])] THEN

Q.ABBREV_TAC `sfb_imp' = (BAG_INSERT
 (asl_exists n.
   holfoot_ap_data_list_seg_num n tl e3
     (MAP (\x. (FST x,TL (SND x))) data) e2)
   (BAG_INSERT
     (var_res_bool_proposition DISJOINT_FMAP_UNION
     (EVERY (\x. ~NULL (SND x)) data /\
         ALL_DISTINCT (tl::MAP FST data)))
     (LIST_TO_BAG (MAP
        (\x. var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x))
             (var_res_exp_const (HD (SND x)))) data) + sfb_imp)))` THEN


`var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb_imp' =
 var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb_imp` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfb_imp'`    THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___COND_INSERT,
       var_res_prop___COND_UNION,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition] THEN
   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      FINITE_LIST_TO_BAG, BAG_IN_LIST_TO_BAG, MEM_MAP,
      GSYM LEFT_FORALL_IMP_THM, IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
   REPEAT STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
   ) THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN

ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
   BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
REPEAT STRIP_TAC THEN

Q.PAT_ASSUM `!sfb_rest s. X` (MP_TAC o Q.SPECL [`sfb_rest`, `s`]) THEN
ASM_SIMP_TAC std_ss [] THEN

`?c1 c2. (e1 (FST s) = SOME c1) /\ (e2 (FST s) = SOME c2) /\ ~(c1 = c2)` by ALL_TAC THEN1 (
   Tactical.REVERSE (`s IN var_res_prop_weak_unequal e1 e2` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS,
         IS_SOME_EXISTS] THEN
      Q.PAT_ASSUM `~(THE X = THE Y)` MP_TAC THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   MATCH_MP_TAC var_res_implies_unequal___var_res_prop___PROP THEN
   Q.EXISTS_TAC `DISJOINT_FMAP_UNION` THEN 
   Q.EXISTS_TAC `wpb` THEN Q.EXISTS_TAC `rpb` THEN
   Q.EXISTS_TAC `sfb_context + BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_UNION_EMPTY, BAG_UNION_INSERT, IN_DEF] THEN
   METIS_TAC[COMM_BAG_UNION]
) THEN


Q.ABBREV_TAC `sfb1 = sfb_imp + (sfb_rest + sfb_context)` THEN
Q.ABBREV_TAC `sfb2 = BAG_INSERT (holfoot_ap_points_to e1 L)
             (sfb_imp' + (sfb_rest + sfb_context))` THEN

MATCH_MP_TAC (prove (``((A = A') /\ (B = B')) ==> ((A = B) ==> (A' = B'))``,
               SIMP_TAC std_ss [])) THEN

CONJ_TAC THENL [
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___asl_exists,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, asl_bool_EVAL] THEN
   EQ_TAC THEN STRIP_TAC THEN1 (
      Q.EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[]
   ) THEN
   Tactical.REVERSE (Cases_on `n`) THEN1 (
      Q.EXISTS_TAC `n'` THEN ASM_REWRITE_TAC[]
   ) THEN
   `var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb1` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `sfb1` THEN
       ASM_REWRITE_TAC [var_res_prop___COND_UNION]
   ) THEN
   Q.PAT_ASSUM `s IN X` MP_TAC THEN
   MATCH_MP_TAC (prove (``~A ==> (A ==> B)``, SIMP_TAC std_ss [])) THEN
   ASM_SIMP_TAC std_ss [
      holfoot_ap_data_list_seg_num_REWRITE, COND_RAND, COND_RATOR,
      var_res_prop___PROP___asl_false, asl_bool_EVAL] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
      var_res_prop___COND_INSERT, IN_ABS,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal] THEN
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS],


   `var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb2` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `sfb2` THEN
       ASM_SIMP_TAC std_ss [var_res_prop___COND_UNION,
          var_res_prop___COND_INSERT, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to]
   ) THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
      var_res_prop___COND_INSERT, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal,
      IN_ABS] THEN
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND,
     IN_ABS, asl_emp_DISJOINT_FMAP_UNION, IN_SING, DISJOINT_FMAP_UNION___FEMPTY] THEN
   SIMP_TAC std_ss [IN_DEF]
])
   



val VAR_RES_FRAME_SPLIT___points_to___data_list_seg = store_thm ("VAR_RES_FRAME_SPLIT___points_to___data_list_seg",
``!e1 e2 tl data L wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

var_res_implies_unequal DISJOINT_FMAP_UNION
  (sfb_context + (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)) e1 e2 ==>
((tl IN FDOM L) /\ (LIST_TO_SET (MAP FST data) SUBSET FDOM L) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
(FEVERY (\x.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data e2) sfb_imp) sfb_restP) =
(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_points_to e1 L) sfb_context)
   sfb_split
   (BAG_UNION (LIST_TO_BAG (MAP (\x. 
           var_res_prop_equal DISJOINT_FMAP_UNION (L ' (FST x)) 
                (var_res_exp_const (HD (SND x)))) data))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          ((EVERY (\x. ~(NULL (SND x))) data) /\
           ALL_DISTINCT (tl::MAP FST data))) (
    BAG_INSERT (holfoot_ap_data_list_seg tl (L ' tl) (MAP (\x. (FST x, TL (SND x))) data) e2) sfb_imp)
   )) sfb_restP))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___points_to___data_list_seg___REWRITE THEN
ASM_REWRITE_TAC[]);




val VAR_RES_FRAME_SPLIT___data_list_seg_num___SAME_LENGTH___REMOVE___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___SAME_LENGTH___REMOVE___REWRITE",
``!wpb rpb e1 e2 e3 tl data1 data2 sfb_context sfb_split sfb_imp n.
((LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
  ALL_DISTINCT (MAP FST data2) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data2 e3) sfb_imp)

   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e2 e3)
       (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM x data1) data2)) sfb_imp)))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN

Q.ABBREV_TAC `sfb_const = sfb_imp + (sfb_rest + sfb_context)` THEN
ASM_SIMP_TAC std_ss [GSYM ASSOC_BAG_UNION, BAG_UNION_EMPTY,
   BAG_UNION_INSERT] THEN
`var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb) sfb_const` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfb_const` THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND_UNION]
) THEN

Q.PAT_ASSUM `var_res_prop___PROP f X Y s` MP_TAC THEN

ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition] THEN

ASM_SIMP_TAC std_ss [IN_ABS, var_res_bool_proposition_REWRITE,
   asl_emp_DISJOINT_FMAP_UNION, IN_SING, var_res_prop_equal_unequal_EXPAND,
   DISJOINT_FMAP_UNION___FEMPTY] THEN

REPEAT STRIP_TAC THEN
`?c1 c2. (e1 (FST s) = SOME c1) /\ (e2 (FST s) = SOME c2)` by ALL_TAC THEN1 (
   IMP_RES_TAC holfoot_ap_data_list_seg_num___EXP_DEFINED THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
Tactical.REVERSE (Cases_on `?c3. (e3 (FST s) = SOME c3)`) THEN1 (
   Cases_on `e3 (FST s)` THEN
   FULL_SIMP_TAC std_ss [] THEN
   CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
   IMP_RES_TAC holfoot_ap_data_list_seg_num___EXP_DEFINED THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN

HO_MATCH_MP_TAC (prove (``(?s1' s2'.
(((!s1 s2. P  s1 s2 ==> (s1 = s1') /\ (s2 = s2')) /\
 (!s1 s2. P' s1 s2 ==> (s1 = s1') /\ (s2 = s2'))) /\
(P s1' s2' = P' s1' s2'))) ==>
((?s1 s2. P s1 s2) = (?s1 s2. P' s1 s2))``, METIS_TAC[])) THEN
Q.EXISTS_TAC `s1` THEN Q.EXISTS_TAC `s2` THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

REPEAT CONJ_TAC THENL [
   CONV_TAC (RENAME_VARS_CONV ["sp1", "sp2"]) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   `sp1 = s1` by ALL_TAC THEN1 (
       MP_TAC (Q.SPECL [`n`, `e1`, `e2`, `e1`, `e3`, `tl`, `data1`, 
                `data2`, `FST (s:holfoot_state)`, `s1`, `sp1`, `SND (s:holfoot_state)`]
           holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
       FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
       METIS_TAC[IS_SEPARATION_COMBINATOR___FINITE_MAP, ASL_IS_SUBSTATE_INTRO]
   ) THEN
   METIS_TAC[DISJOINT_FMAP_UNION___CANCELLATIVE],

   CONV_TAC (RENAME_VARS_CONV ["sp1", "sp2"]) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   `sp1 = s1` by ALL_TAC THEN1 (
       MP_TAC (Q.SPECL [`n`, `e1`, `e2`, `e1`, `e2`, `tl`, `data1`, 
                `data1`, `FST (s:holfoot_state)`, `s1`, `sp1`, `SND (s:holfoot_state)`]
           holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
       FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
       METIS_TAC[IS_SEPARATION_COMBINATOR___FINITE_MAP, ASL_IS_SUBSTATE_INTRO]
   ) THEN
   METIS_TAC[DISJOINT_FMAP_UNION___CANCELLATIVE],

   ALL_TAC
] THEN

REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   MP_TAC (Q.SPECL [`n`, `e1`, `e2`, `e1`, `e3`, `tl`, `data1`, 
            `data2`, `FST (s:holfoot_state)`, `s1`, `s1`, `s1`]
       holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      ASL_IS_SUBSTATE___REFL, SUBSET_DEF, IN_LIST_TO_SET,
       MEM_MAP, GSYM LEFT_FORALL_IMP_THM, EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   `?x'. MEM x' data1 /\ (FST x' = FST x) /\ (SND x' = SND x)` by METIS_TAC[] THEN
   Cases_on `x'` THEN
   FULL_SIMP_TAC std_ss [],


   `(FST s,s1) IN holfoot_ap_data_list_seg_num n tl e1 data2 e3 =
    (FST s,s1) IN holfoot_ap_data_list_seg_num n tl e1 data2 e2` by ALL_TAC THEN1 (
       MATCH_MP_TAC holfoot_ap_data_list_seg_num___REWRITE_END_EXP THEN
       FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
   ) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC holfoot_ap_data_list_seg_num___ELIM_DATA THEN
   Q.EXISTS_TAC `data1` THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM]
]);





val VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE___REWRITE",
``!wpb rpb e1 e2 tl data1 data2 sfb_context sfb_split sfb_imp.
((LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
  ALL_DISTINCT (MAP FST data2) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

(VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data2 e2) sfb_imp)

   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split  
     (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM x data1) data2)) sfb_imp))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`wpb`, `rpb`, `e1`, `e2`, `e2`, `tl`,
 `data1`, `data2`, `sfb_context`, `sfb_split`, `sfb_imp`]
   VAR_RES_FRAME_SPLIT___data_list_seg_num___SAME_LENGTH___REMOVE___REWRITE) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_list_seg_def,
   VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, BAG_UNION_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!n sfb_rest s. X`
   (MP_TAC o Q.SPECL [`sfb_rest`, `s`] o 
      (CONV_RULE (RESORT_FORALL_CONV (fn [x1,x2,x3] => [x2,x3,x1])))) THEN
Q.PAT_ASSUM `var_res_prop___PROP f X Y s` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num] THEN
SIMP_TAC std_ss [var_res_bool_proposition_REWRITE, asl_bool_EVAL,
   var_res_prop_equal_unequal_EXPAND, IN_ABS, IN_SING,
   asl_emp_DISJOINT_FMAP_UNION, DISJOINT_FMAP_UNION___FEMPTY,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN

Q.HO_MATCH_ABBREV_TAC
`(?s1 s2 n. P1 s1 s2 n) ==> 
 (!n. (?s1 s2. P1 s1 s2 n) ==> 
      ((?s1 s2. P2 s1 s2 n) = (?s1 s2. P1' s1 s2 n))) ==>
 ((?s1 s2 n. P2 s1 s2 n) = (?s1 s2 n. P1'' s1 s2 n))` THEN

`P1'' = P1'` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P1''` THEN Q.UNABBREV_TAC `P1'` THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC holfoot_ap_data_list_seg_num___EXP_DEFINED THEN
   FULL_SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
Q.UNABBREV_TAC `P1''` THEN
STRIP_TAC THEN
Tactical.REVERSE (`
(!s1 s2 n'. P1 s1 s2 n' ==> (n = n')) /\
(!s1 s2 n'. P2 s1 s2 n' ==> (n = n')) /\
(!s1 s2 n'. P1' s1 s2 n' ==> (n = n'))` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

Tactical.REVERSE (
`!s1 s2 n' data. 
    (DISJOINT_FMAP_UNION (SOME s1) (SOME s2) = SOME (SND s)) /\
    (FST s,s1) IN holfoot_ap_data_list_seg_num n' tl e1 data e2 ==>
    (n' = n)` by ALL_TAC) THEN1 (
   UNABBREV_ALL_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN

UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_ap_data_list_seg_num___SAME_START_END THEN

EVERY (map Q.EXISTS_TAC [`e1`, `e2`, `e1`, `e2`, `tl`, `data`,
   `data1`, `FST (s:holfoot_state)`, `s1'`, `s1`, `SND (s:holfoot_state)`]) THEN

FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
METIS_TAC [ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]);





val VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE",
``!wpb rpb wpb' sr sfb_restP e1 e2 tl data1 data2 sfb_context sfb_split sfb_imp.
((LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
  ALL_DISTINCT (MAP FST data2)) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 ==>

(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data2 e2) sfb_imp) 
   sfb_restP =

VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split  
     (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM x data1) data2)) sfb_imp) sfb_restP)``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE___REWRITE THEN
ASM_REWRITE_TAC[]);







val VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE",
``!wpb rpb e2 e3 tl n m e1 data1 data2 sfb_context sfb_split sfb_imp.

(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (n+m) tl e1 data2 e3) sfb_imp)

   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)

   (BAG_INSERT (asl_and (holfoot_not_in_heap e3) 
               (holfoot_ap_data_list_seg_num n tl e1 data1 e2))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM (FST x, TAKE n (SND x)) data1) data2))
   (BAG_INSERT (holfoot_ap_data_list_seg_num m tl e2 
      (MAP (\x. (FST x, (DROP n (SND x)))) data2) e3) sfb_imp))))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e3)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num___SPLIT] THEN

Tactical.REVERSE (Cases_on `ALL_DISTINCT (tl::(MAP FST data1))`) THEN1 (
   `holfoot_ap_data_list_seg_num n tl e1 data1 e2 = asl_false` by ALL_TAC THEN1 (
       MATCH_MP_TAC (holfoot_ap_data_list_seg_num___DATA_PROPS) THEN
       ASM_SIMP_TAC std_ss []
   ) THEN
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES, VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
     var_res_prop___COND_INSERT, BAG_UNION_INSERT,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
     var_res_prop___PROP___asl_false, asl_bool_EVAL]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.HO_MATCH_ABBREV_TAC `
VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb)
      sfb_context
      (BAG_INSERT listP1 sfb_split)
      (BAG_INSERT
         (asl_and (holfoot_not_in_heap e3)
            (asl_exists c.
               asl_star holfoot_separation_combinator
                 (listP1' c)
                 (listP2' c))) sfb_imp)
      sfb_context
      (BAG_INSERT listP1 sfb_split)
      (BAG_INSERT (asl_and (holfoot_not_in_heap e3) listP1) 
         (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION data2_cond) (BAG_INSERT listP2 sfb_imp)))` THEN

`(!c. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (listP1' c)) /\
 (!c. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (listP2' c)) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) listP1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) listP2` by ALL_TAC THEN1 (
    UNABBREV_ALL_TAC THEN
    ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num,
       VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN

`(!c. VAR_RES_IS_STACK_IMPRECISE (listP1' c)) /\
 (!c. VAR_RES_IS_STACK_IMPRECISE (listP2' c))` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
) THEN

ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star, 
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_not_in_heap,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   holfoot_separation_combinator_def,
   var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION,
   BAG_UNION_INSERT] THEN

ASM_SIMP_TAC std_ss [asl_bool_EVAL, holfoot_not_in_heap_def,
   IN_ABS, asl_star___VAR_RES_IS_STACK_IMPRECISE,
   asl_emp_DISJOINT_FMAP_UNION, IN_SING,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   var_res_bool_proposition_REWRITE,
   DISJOINT_FMAP_UNION___FEMPTY] THEN
REPEAT STRIP_TAC THEN

`SET_OF_BAG (wpb + rpb) SUBSET FDOM (FST s)` by ALL_TAC THEN1 (
   METIS_TAC [var_res_prop___PROP___VARS, pairTheory.FST, IN_DEF]
) THEN

`?c. e3 (FST s) = SOME c` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [GSYM IS_SOME_EXISTS] THEN
   METIS_TAC [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL]
) THEN

`?s3. ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s3 (SND s) /\
   (FST s,s3) IN listP1` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `var_res_prop___PROP f X Y s` MP_TAC THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
      var_res_prop___COND_UNION, var_res_prop___COND_INSERT] THEN
   METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]
) THEN

ASM_SIMP_TAC std_ss [] THEN

CONV_TAC (LHS_CONV (RESORT_EXISTS_CONV
  (fn [s1, s2, c'', es1, es2] => [es1, es2, s2, c'', s1])) THENC
  RHS_CONV (RESORT_EXISTS_CONV
  (fn [s1, s2, s1', s2'] => [s1, s1', s2', s2]))) THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN

REPEAT STRIP_TAC THEN
EQ_TAC THENL [
   SIMP_TAC (std_ss++CONJ_ss) [DISJOINT_FMAP_UNION___REWRITE,
         FDOM_FUNION, DISJOINT_UNION_BOTH, IN_UNION] THEN
   STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [DISJOINT_SYM, FUNION_ASSOC] THEN
   `(e2 (FST s) = SOME c'') /\ (s1 = s3) /\ data2_cond` by ALL_TAC THEN1 (
      MP_TAC (
         Q.SPECL [`n`, `e1`, `e2`, `e1`, `var_res_exp_const c''`, `tl`, `data1`, ` (MAP (\x. (FST x,TAKE n (SND x))) data2)`, 
               `FST (s:holfoot_state)`, `s3`, `s1`, `SND (s:holfoot_state)`]  
         holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
      Q.UNABBREV_TAC `listP1'` THEN
      Q.UNABBREV_TAC `data2_cond` THEN
      FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
        GSYM FUNION_ASSOC] THEN
      SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
        FUNION_DEF, var_res_exp_const_def, SUBSET_UNION,
        EVERY_MEM, MEM_MAP, GSYM RIGHT_EXISTS_AND_THM,
        GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET, MEM_MAP,
         GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[pairTheory.FST, pairTheory.SND, pairTheory.PAIR]
   ) THEN
   ASM_REWRITE_TAC[] THEN

   Q.UNABBREV_TAC `listP2` THEN Q.UNABBREV_TAC `listP2'` THEN
   FULL_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC (EQ_IMP_RULE_CANON
         holfoot_ap_data_list_seg_num___REWRITE_START_EXP) THEN
   Q.EXISTS_TAC `var_res_exp_const c''` THEN
   ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
   SIMP_TAC std_ss [var_res_exp_const_def],



   Q.UNABBREV_TAC `data2_cond` THEN
   SIMP_TAC (std_ss++CONJ_ss) [DISJOINT_FMAP_UNION___REWRITE,
         FDOM_FUNION, DISJOINT_UNION_BOTH, IN_UNION] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [DISJOINT_SYM, FUNION_ASSOC] THEN
   `?c''. (e2 (FST s) = SOME c'')` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `listP1` THEN
      FULL_SIMP_TAC std_ss [GSYM IS_SOME_EXISTS] THEN       
      METIS_TAC[holfoot_ap_data_list_seg_num___EXP_DEFINED,
        pairTheory.FST]
   ) THEN
   Q.EXISTS_TAC `c''` THEN
   REPEAT STRIP_TAC THENL [
      Q.UNABBREV_TAC `listP2` THEN
      FULL_SIMP_TAC std_ss [] THEN
      `(FST s,s1') IN holfoot_not_in_heap e3` by
        METIS_TAC[holfoot_ap_data_list_seg_num___END_EXP_NOT_IN_FDOM] THEN
      FULL_SIMP_TAC std_ss [holfoot_not_in_heap_def, IN_ABS] THEN
      FULL_SIMP_TAC std_ss [] THEN
      METIS_TAC[],


      Q.UNABBREV_TAC `listP1` THEN
      Q.UNABBREV_TAC `listP1'` THEN
      FULL_SIMP_TAC std_ss [EVERY_MEM,
        SUBSET_DEF, IN_LIST_TO_SET, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC (EQ_IMP_RULE_CANON holfoot_ap_data_list_seg_num___REWRITE_END_EXP) THEN
      Q.EXISTS_TAC `e2` THEN
      ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
      CONJ_TAC THEN1 SIMP_TAC std_ss [var_res_exp_const_def] THEN
      MATCH_MP_TAC holfoot_ap_data_list_seg_num___ELIM_DATA THEN
      Q.EXISTS_TAC `data1` THEN
      ASM_SIMP_TAC (std_ss++boolSimps.ETA_ss) [MEM_MAP,
         GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
         GSYM LEFT_FORALL_IMP_THM, MAP_MAP_o, combinTheory.o_DEF],


      Q.UNABBREV_TAC `listP2` THEN
      Q.UNABBREV_TAC `listP2'` THEN
      FULL_SIMP_TAC std_ss [] THEN
      MATCH_MP_TAC (EQ_IMP_RULE_CANON holfoot_ap_data_list_seg_num___REWRITE_START_EXP) THEN
      Q.EXISTS_TAC `e2` THEN
      ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
      SIMP_TAC std_ss [var_res_exp_const_def]
   ]
]);



val VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START",
``!sr sfb_restP wpb rpb wpb' e2 e3 tl n m e1 data1 data2 sfb_context sfb_split sfb_imp.

(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (n+m) tl e1 data2 e3) sfb_imp)
   sfb_restP =

VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)

   (BAG_INSERT (asl_and (holfoot_not_in_heap e3) 
               (holfoot_ap_data_list_seg_num n tl e1 data1 e2))
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM (FST x, TAKE n (SND x)) data1) data2))
   (BAG_INSERT (holfoot_ap_data_list_seg_num m tl e2 
      (MAP (\x. (FST x, (DROP n (SND x)))) data2) e3) sfb_imp)))
   sfb_restP)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE) THEN
ASM_REWRITE_TAC[]);



val VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE___not_in_heap = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE___not_in_heap",
``!wpb rpb e2 e3 tl n m e1 data1 data2 sfb_context sfb_split sfb_imp.

((holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_imp sfb_context)
   (BAG_UNION sfb_imp sfb_context) e3) \/
(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_split sfb_context)
   (BAG_UNION sfb_split sfb_context) e3)) /\
(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (n+m) tl e1 data2 e3) sfb_imp)

   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM (FST x, TAKE n (SND x)) data1) data2))
   (BAG_INSERT (holfoot_ap_data_list_seg_num m tl e2 
      (MAP (\x. (FST x, (DROP n (SND x)))) data2) e3) sfb_imp)))``,

REPEAT GEN_TAC THEN
Q.ABBREV_TAC `e3_imp = ((holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_imp sfb_context)
   (BAG_UNION sfb_imp sfb_context) e3) \/
(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_split sfb_context)
   (BAG_UNION sfb_split sfb_context) e3))` THEN
REPEAT STRIP_TAC THEN
Q.UNABBREV_TAC `e3_imp` THEN
MP_TAC (
Q.SPECL [`wpb`, `rpb`, `e2`, `e3`, `tl`, `n`, `m`, `e1`, `data1`, `data2`, `sfb_context`, `sfb_split`, `sfb_imp`] 
   VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE) THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE] THEN
DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
SIMP_TAC std_ss [GSYM VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE] THEN

Q.HO_MATCH_ABBREV_TAC `VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb)
   sfb_context (BAG_INSERT listP1 sfb_split)
      (BAG_INSERT (asl_and (holfoot_not_in_heap e3) listP1)
         (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
              data2_cond) (BAG_INSERT listP2 sfb_imp)))
   (BAG_INSERT listP1 sfb_context) sfb_split 
        (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
              data2_cond) (BAG_INSERT listP2 sfb_imp))` THEN

Tactical.REVERSE (Cases_on `data2_cond = T`) THEN1 (
   FULL_SIMP_TAC std_ss [var_res_bool_proposition_TF] THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
     IS_SEPARATION_COMBINATOR___FINITE_MAP,
     var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
     BAG_UNION_INSERT,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_not_in_heap
   ] THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP,
     var_res_prop___PROP___REWRITE, var_res_bigstar_REWRITE,
     IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
     asl_false___asl_star_THM, asl_bool_EVAL]
) THEN
Q.UNABBREV_TAC `data2_cond` THEN
Tactical.REVERSE (`
   VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb)
      sfb_context (BAG_INSERT listP1 sfb_split)
      (BAG_INSERT (asl_and (holfoot_not_in_heap e3) listP1)
         (BAG_INSERT listP2 sfb_imp)) 
      sfb_context (BAG_INSERT listP1 sfb_split)
      (BAG_INSERT listP1 (BAG_INSERT listP2 sfb_imp))` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [var_res_bool_proposition_TF,
      VAR_RES_FRAME_SPLIT___REWRITE_OK___stack_true,
      prove (``BAG_INSERT X (BAG_INSERT (var_res_prop_stack_true f) b) =
            (BAG_INSERT (var_res_prop_stack_true f) (BAG_INSERT X b))``, PROVE_TAC[BAG_INSERT_commutes])] THEN
   FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE] THEN
   SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___FRAME,
      GSYM VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE]
) THEN

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   var_res_prop___PROP_INSERT, BAG_UNION_INSERT] THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_ABS, GSYM RIGHT_EXISTS_AND_THM, 
  GSYM LEFT_EXISTS_AND_THM, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and,
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_not_in_heap] THEN

REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_not_in_heap_def,
   IN_ABS] THEN

REPEAT STRIP_TAC THEN

`?c. (e3 (FST s) = SOME c)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `listP2` THEN
   FULL_SIMP_TAC std_ss [GSYM IS_SOME_EXISTS] THEN
   METIS_TAC[holfoot_ap_data_list_seg_num___EXP_DEFINED,
     pairTheory.FST]
) THEN
ASM_SIMP_TAC std_ss [] THEN
Cases_on `c = 0` THEN1 (
   METIS_TAC[holfoot_ap_data_list_seg_num___NULL_NOT_IN_FDOM,
     pairTheory.SND]
) THEN
Tactical.REVERSE (`c IN FDOM s2` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, DISJOINT_FMAP_UNION___REWRITE,
      NOT_IN_EMPTY, IN_INTER, IN_UNION, FDOM_FUNION] THEN
   METIS_TAC[]
) THEN

`?sfb s22. 
     holfoot_implies_in_heap_or_null sfb sfb e3 /\
     ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s22 s2 /\
     (FST s, s22) IN var_res_bigstar DISJOINT_FMAP_UNION sfb` by ALL_TAC THEN1 (

   FULL_SIMP_TAC std_ss [] THENL [
     Q.ABBREV_TAC `sfb = sfb_imp + sfb_context` THEN
     `sfb_imp + (sfb_rest + sfb_context) = sfb + sfb_rest` by 
        METIS_TAC[ASSOC_BAG_UNION, COMM_BAG_UNION] THEN
     FULL_SIMP_TAC std_ss [] THEN
     Q.EXISTS_TAC `sfb` THEN
     Q.PAT_ASSUM `(FST s, s2') IN X` MP_TAC THEN
     ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
       IS_SEPARATION_COMBINATOR___FINITE_MAP,
       IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
       GSYM asl_bigstar_REWRITE, IN_ABS] THEN
     ASM_SIMP_TAC std_ss [var_res_bigstar_UNION,
         IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
     REPEAT STRIP_TAC THEN
     `VAR_RES_IS_STACK_IMPRECISE (var_res_bigstar DISJOINT_FMAP_UNION sfb) /\
      VAR_RES_IS_STACK_IMPRECISE (var_res_bigstar DISJOINT_FMAP_UNION sfb_rest)` by ALL_TAC THEN1 (
         CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar], []) THEN
         ASM_SIMP_TAC std_ss [] THEN
         Q.UNABBREV_TAC `sfb` THEN
         FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
             BAG_IN_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM,
             VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def, BAG_EVERY]
     ) THEN
     FULL_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
        IN_ABS] THEN
     Q.EXISTS_TAC `es1` THEN
     ASM_REWRITE_TAC[holfoot_separation_combinator_def] THEN
     METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP,
        ASL_IS_SUBSTATE___TRANS],



     Q.PAT_ASSUM `X s` MP_TAC THEN
     ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
       var_res_prop___COND_INSERT,
       var_res_prop___COND_UNION] THEN
     REPEAT STRIP_TAC THEN
     `s1'' = s1` by ALL_TAC THEN1 (
        MP_TAC (Q.SPECL [`n`, `e1`, `e2`, `e1`, `e2`, `tl`, `data1`, 
                  `data1`, `FST (s:holfoot_state)`, `s1`, `s1''`, `SND (s:holfoot_state)`]
             holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
        FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
        METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]
     ) THEN
     `s2'' = s2` by METIS_TAC[DISJOINT_FMAP_UNION___CANCELLATIVE] THEN
     Q.ABBREV_TAC `sfb = sfb_split + sfb_context` THEN
     Q.EXISTS_TAC `sfb` THEN Q.EXISTS_TAC `s2` THEN
     ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___REFL] THEN
     Q.PAT_ASSUM `(FST s, s2'') IN XXX` MP_TAC THEN
     ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
       IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS]
   ]
) THEN
Q.PAT_ASSUM `X \/ Y` (K ALL_TAC) THEN

Tactical.REVERSE (`c IN FDOM s22` by ALL_TAC) THEN1 (  
   FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
      SUBSET_DEF]
) THEN

Q.PAT_ASSUM `holfoot_implies_in_heap_or_null sfb sfb e3` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
   holfoot_implies_in_heap_pred_def, GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `FST (s:holfoot_state)` THEN  
Q.EXISTS_TAC `FST (s:holfoot_state)` THEN  
Q.EXISTS_TAC `s22` THEN  
Q.EXISTS_TAC `s22` THEN  
ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE___REFL]);








val VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___not_in_heap___imp = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___not_in_heap___imp",
``!wpb rpb wpb' e2 e3 tl n m e1 data1 data2 sfb_context sfb_split sfb_imp sfb_restP sr.

(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_imp sfb_context)
   (BAG_UNION sfb_imp sfb_context) e3) /\
(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (n+m) tl e1 data2 e3) sfb_imp) sfb_restP =

 VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM (FST x, TAKE n (SND x)) data1) data2))
   (BAG_INSERT (holfoot_ap_data_list_seg_num m tl e2 
      (MAP (\x. (FST x, (DROP n (SND x)))) data2) e3) sfb_imp))
   sfb_restP)``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE___not_in_heap) THEN
ASM_REWRITE_TAC[]);




val VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___not_in_heap___split = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___not_in_heap___split",
``!wpb rpb wpb' e2 e3 tl n m e1 data1 data2 sfb_context sfb_split sfb_imp sfb_restP sr.

(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_split sfb_context)
   (BAG_UNION sfb_split sfb_context) e3) /\
(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

(VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg_num (n+m) tl e1 data2 e3) sfb_imp) sfb_restP =

 VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_list_seg_num n tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
           (EVERY (\x. MEM (FST x, TAKE n (SND x)) data1) data2))
   (BAG_INSERT (holfoot_ap_data_list_seg_num m tl e2 
      (MAP (\x. (FST x, (DROP n (SND x)))) data2) e3) sfb_imp))
   sfb_restP)``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE___not_in_heap) THEN
ASM_REWRITE_TAC[]);





val VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START___REWRITE = 
store_thm ("VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START___REWRITE",
``!data1 data2 wpb rpb sfb_context sfb_split sfb_imp e1 e2 e3 tl.

(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_split sfb_context)
   (BAG_UNION sfb_split sfb_context) e3) /\
(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
(ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) ==>

(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

((VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data2 e3) sfb_imp))

   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
                 (EVERY (\x. MEM (FST x,TAKE (LENGTH (SND (HD data1))) (SND x)) data1) data2)) (
     BAG_INSERT
       (holfoot_ap_data_list_seg tl e2
      (MAP (\x. (FST x, (DROP (LENGTH (SND (HD data1))) (SND x)))) data2) e3) sfb_imp)))``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_list_seg_def] THEN

Q.HO_MATCH_ABBREV_TAC `
   VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb)
      sfb_context
      (BAG_INSERT (asl_exists n. listP1 n) sfb_split)
      (BAG_INSERT (asl_exists n. listP2 n) sfb_imp)
      (BAG_INSERT (asl_exists n. listP1 n) sfb_context) 
      sfb_split
      (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION data2_cond)
         (BAG_INSERT (asl_exists n. listP3 n) sfb_imp))` THEN


`(!n. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (listP1 n)) /\
 (!n. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (listP2 n)) /\
 (!n. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (listP3 n))` by ALL_TAC THEN1 (
    UNABBREV_ALL_TAC THEN
    ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg_num]
) THEN

`!n m. VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb)
      sfb_context (BAG_INSERT (listP1 n) sfb_split)
      (BAG_INSERT (listP2 (n+m)) sfb_imp)
      (BAG_INSERT (listP1 n) sfb_context) sfb_split
      (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION data2_cond)
         (BAG_INSERT (listP3 m) sfb_imp))` by ALL_TAC THEN1 (

   UNABBREV_ALL_TAC THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `data2 <> [] /\ (LENGTH (SND (HD data1)) <> n)`) THEN1 (
       `(EVERY (\x. MEM (FST x,TAKE (LENGTH (SND (HD data1))) (SND x)) data1) data2 =
         EVERY (\x. MEM (FST x,TAKE n (SND x)) data1) data2) /\
        (MAP (\x. (FST x,DROP (LENGTH (SND (HD data1))) (SND x))) data2 =
         MAP (\x. (FST x,DROP n (SND x))) data2)` by ALL_TAC THEN1 (
           Cases_on `data2` THEN FULL_SIMP_TAC list_ss []) THEN
       ASM_SIMP_TAC std_ss [] THEN
       MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_list_seg_num___REMOVE_START___REWRITE___not_in_heap) THEN
       ASM_REWRITE_TAC[]
   ) THEN
   `holfoot_ap_data_list_seg_num n tl e1 data1 e2 = asl_false` by ALL_TAC THEN1 (
      MATCH_MP_TAC holfoot_ap_data_list_seg_num___DATA_PROPS THEN

      Cases_on `data2` THEN FULL_SIMP_TAC list_ss [] THEN
      Cases_on `data1` THEN FULL_SIMP_TAC list_ss [INSERT_SUBSET, MEM_MAP]
   ) THEN

   ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
      var_res_prop___PROP___asl_false, asl_bool_EVAL, BAG_UNION_INSERT]
) THEN


POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
  var_res_prop___COND_INSERT,
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
  BAG_UNION_INSERT,
  prove (
   ``BAG_INSERT (var_res_bool_proposition f b) (BAG_INSERT sf B) =
    (BAG_INSERT sf (BAG_INSERT (var_res_bool_proposition f b) B))``,
   PROVE_TAC[bagTheory.BAG_INSERT_commutes])] THEN
SIMP_TAC std_ss [var_res_prop___PROP___asl_exists,
   asl_bool_EVAL, prove (
   ``BAG_INSERT sf (BAG_INSERT (asl_exists x. P x) B) =
    (BAG_INSERT (asl_exists x. P x) (BAG_INSERT sf B))``,
   PROVE_TAC[bagTheory.BAG_INSERT_commutes]),
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM, IN_DEF] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (`n'' = n` by ALL_TAC) THEN1 (
      Q.EXISTS_TAC `n + n'` THEN
      Q.PAT_ASSUM `!n m sfb_rest s. X` (MP_TAC o
         Q.SPECL [`n`, `n'`, `sfb_rest`, `s`]) THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[BAG_INSERT_commutes]
   ) THEN
   `?s1 s2. (FST s, s1) IN listP1 n /\
            (FST s, s2) IN listP1 n'' /\
            (ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1 (SND s)) /\
            (ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2 (SND s))` by ALL_TAC THEN1 (
         REPEAT (Q.PAT_ASSUM `var_res_prop___PROP f X Y s` MP_TAC) THEN
         ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
           var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
           VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
           IN_ABS] THEN
         REPEAT STRIP_TAC THEN
         Q.EXISTS_TAC `s1` THEN Q.EXISTS_TAC `s1'` THEN
         ASM_REWRITE_TAC[] THEN
         METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]
   ) THEN
   MATCH_MP_TAC holfoot_ap_data_list_seg_num___SAME_START_END THEN
   Q.EXISTS_TAC `e1` THEN Q.EXISTS_TAC `e2` THEN
   Q.EXISTS_TAC `e1` THEN Q.EXISTS_TAC `e2` THEN
   Q.EXISTS_TAC `tl` THEN 
   Q.EXISTS_TAC `data1` THEN Q.EXISTS_TAC `data1` THEN
   Q.EXISTS_TAC `FST (s:holfoot_state)` THEN
   Q.EXISTS_TAC `s2` THEN
   Q.EXISTS_TAC `s1` THEN
   Q.EXISTS_TAC `SND (s:holfoot_state)` THEN
   Q.UNABBREV_TAC `listP1` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `n' < n`) THEN1 (
   `?m. n' = n + m` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `n' - n` THEN
      DECIDE_TAC
   ) THEN
   Q.PAT_ASSUM `!n m sfb_rest s. X s` (MP_TAC o Q.SPECL 
      [`n`, `m`, `sfb_rest`, `s`]) THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[BAG_INSERT_commutes]
) THEN
`?m. n = n' + SUC m` by ALL_TAC THEN1 (
   Q.EXISTS_TAC `PRE (n - n')` THEN
   DECIDE_TAC
) THEN
CCONTR_TAC THEN POP_ASSUM (K ALL_TAC) THEN

REPEAT (Q.PAT_ASSUM `var_res_prop___PROP X Y Z s` MP_TAC) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
Q.UNABBREV_TAC `listP1` THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e3)` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num___SPLIT, IN_ABS,
   asl_bool_EVAL, holfoot_separation_combinator_def,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN

ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   VAR_RES_IS_STACK_IMPRECISE___data_list_seg_num, IN_ABS,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
REPEAT STRIP_TAC THEN
CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
`(e3 (FST s) = SOME c) /\ (s1' = es1)` by ALL_TAC THEN1 (
    MP_TAC (Q.SPECL [`n'`, `e1`, `e3`, `e1`, `var_res_exp_const c`, `tl`, `data2`, 
             `MAP (\x. (FST x,TAKE n' (SND x))) data1`, `FST (s:holfoot_state)`, `s1'`, `es1`, `SND (s:holfoot_state)`]
             holfoot_ap_data_list_seg_num___SAME_LENGTH_START) THEN
    Q.UNABBREV_TAC `listP2` THEN 
    FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
    MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, METIS_TAC[])) THEN
    SIMP_TAC std_ss [var_res_exp_const_def] THEN
    METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP,
       ASL_IS_SUBSTATE___TRANS]
) THEN
`~(c = 0) /\ (c IN FDOM es2)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(FST s, es2) IN X` MP_TAC THEN
   FULL_SIMP_TAC std_ss [holfoot_ap_data_list_seg_num___STACK_IMPRECISE___REWRITE,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      IN_ABS, holfoot_ap_points_to_def, LET_THM] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_exp_const_def, DISJOINT_FMAP_UNION___REWRITE,
      FDOM_FUNION, IN_UNION, IN_SING]
) THEN
Tactical.REVERSE (`c IN FDOM s2` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE,
      FDOM_FUNION, DISJOINT_UNION_BOTH] THEN
   FULL_SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
   METIS_TAC[]
) THEN
Q.PAT_ASSUM `(FST s, s2) IN Y` MP_TAC THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, IN_ABS] THEN
STRIP_TAC THEN

Q.PAT_ASSUM `holfoot_implies_in_heap_or_null x y e3` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_implies_in_heap_or_null_def,
   holfoot_implies_in_heap_pred_def, GSYM LEFT_EXISTS_IMP_THM] THEN

Q.EXISTS_TAC `FST (s:holfoot_state)` THEN
Q.EXISTS_TAC `FST (s:holfoot_state)` THEN
Q.EXISTS_TAC `s2` THEN
Q.EXISTS_TAC `s2` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE___REFL,
   holfoot_separation_combinator_def]);




val VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START = store_thm (
"VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START",
``!data1 data2 wpb rpb wpb' sr sfb_restP sfb_context sfb_split sfb_imp e1 e2 e3 tl.

(holfoot_implies_in_heap_or_null
   (BAG_UNION sfb_split sfb_context)
   (BAG_UNION sfb_split sfb_context) e3) ==>
((LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1)) /\
 (ALL_DISTINCT (tl::(MAP FST data1)) ==> ALL_DISTINCT (MAP FST data2)) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e3) ==>

((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data2 e3) sfb_imp) sfb_restP) =

  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION
                 (EVERY (\x. MEM (FST x,TAKE (LENGTH (SND (HD data1))) (SND x)) data1) data2)) (
     BAG_INSERT
       (holfoot_ap_data_list_seg tl e2
      (MAP (\x. (FST x, (DROP (LENGTH (SND (HD data1))) (SND x)))) data2) e3) sfb_imp))
   sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START___REWRITE) THEN
ASM_REWRITE_TAC[]);


(*-----------------
 * Queues
 *-----------------*)

val holfoot_ap_data_queue_def = Define `
   holfoot_ap_data_queue tl startExp data endExp =
      var_res_prop_binexpression_cond DISJOINT_FMAP_UNION $=
          startExp (var_res_exp_const 0)
          (var_res_bool_proposition DISJOINT_FMAP_UNION 
              (EVERY (\td. NULL (SND td)) data))
          (asl_star holfoot_separation_combinator
              (asl_star holfoot_separation_combinator
                  (var_res_bool_proposition DISJOINT_FMAP_UNION 
                     (EVERY (\td. ~(NULL (SND td))) data))
                  (holfoot_ap_data_list_seg tl startExp
                         (MAP (\td. (FST td, FRONT (SND td))) data) endExp))
                  (holfoot_ap_points_to endExp
                      (LIST_TO_FMAP (ZIP
                          (tl::MAP FST data, MAP var_res_exp_const
                          (0::MAP (\x. LAST (SND x)) data))))))`;


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_queue = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_queue",
`` !tl startExp data endExp vs.
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs
       startExp /\
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs
       endExp ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
       (holfoot_ap_data_queue tl startExp data endExp)``,

SIMP_TAC std_ss [holfoot_ap_data_queue_def] THEN 
REPEAT STRIP_TAC THEN
CONSEQ_REWRITE_TAC ([], 
   [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression_cond,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star___holfoot,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
    FEVERY_LIST_TO_FMAP], []) THEN
ASM_SIMP_TAC list_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
   ZIP_MAP, EVERY_MAP]);


val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_queue = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_queue",
`` !tl startExp data endExp.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp) ==>
     VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_data_queue tl startExp data endExp)``,

REWRITE_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
        GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
             VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_queue]);


val var_res_prop_varlist_update___holfoot_ap_data_queue = 
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_queue",
``!vcL tl startExp data endExp.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS startExp) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS endExp) ==>
  
     (var_res_prop_varlist_update vcL (holfoot_ap_data_queue tl startExp data endExp) =
      holfoot_ap_data_queue tl (var_res_exp_varlist_update vcL startExp) data (var_res_exp_varlist_update vcL endExp))``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [holfoot_ap_data_queue_def] THEN
Q.ABBREV_TAC `points_pred = (holfoot_ap_points_to endExp
           (LIST_TO_FMAP
              (ZIP
                 (tl::MAP FST data,
                  MAP var_res_exp_const
                    (0::MAP (\x. LAST (SND x)) data)))))` THEN
`VAR_RES_IS_STACK_IMPRECISE points_pred` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `points_pred` THEN
   CONSEQ_REWRITE_TAC ([],
       [VAR_RES_IS_STACK_IMPRECISE___points_to,
        FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [ZIP_MAP, EVERY_MAP,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC list_ss [holfoot_separation_combinator_def,
   var_res_exp_varlist_update___const_EVAL,
   var_res_prop_varlist_update___BOOL,
   var_res_prop_varlist_update___asl_star,
   var_res_prop_varlist_update___var_res_prop_binexpression_cond,
   var_res_prop_varlist_update___holfoot_ap_data_list_seg,
   VAR_RES_IS_STACK_IMPRECISE___var_res_bool_proposition,
   VAR_RES_IS_STACK_IMPRECISE___asl_star,
   VAR_RES_IS_STACK_IMPRECISE___data_list_seg,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
Q.UNABBREV_TAC `points_pred` THEN
ASM_SIMP_TAC list_ss [var_res_prop_varlist_update___holfoot_ap_points_to,
  o_f_LIST_TO_FMAP, ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_ZIP_EQ,
  var_res_exp_varlist_update___const_EVAL]);




val holfoot_ap_data_queue___startExp_null = store_thm (
"holfoot_ap_data_queue___startExp_null",
``holfoot_ap_data_queue tl (var_res_exp_const 0) data endExp =
  var_res_bool_proposition DISJOINT_FMAP_UNION
    (EVERY (\td. NULL (SND td)) data)``,
SIMP_TAC std_ss [holfoot_ap_data_queue_def,
   var_res_prop_binexpression_cond___CONST_REWRITE]);


val holfoot_ap_data_queue___endExp_null = store_thm (
"holfoot_ap_data_queue___endExp_null",
``holfoot_ap_data_queue tl startExp data (var_res_exp_const 0) =
  asl_trivial_cond 
    (EVERY (\td. NULL (SND td)) data) 
    (var_res_prop_equal DISJOINT_FMAP_UNION startExp (var_res_exp_const 0))``,

SIMP_TAC std_ss [holfoot_ap_data_queue_def,
   holfoot_ap_points_to___null, asl_false___asl_star_THM,
   var_res_prop_binexpression_cond_def,
   asl_bool_EVAL, asl_trivial_cond_def,
   var_res_bool_proposition_REWRITE, IN_ABS] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR,
   asl_bool_EVAL, var_res_prop_equal_unequal_EXPAND] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);



(*-----------------
 * Arrays
 *-----------------*)



val holfoot_ap_data_array_MAP_LIST_def = Define 
`holfoot_ap_data_array_MAP_LIST (e:holfoot_a_expression) (n:num) 
      (data:((holfoot_tag # num list) list)) = 
    (MAP (\n. (var_res_exp_add e n,
               LIST_TO_FMAP (MAP (\tl. (FST tl,  (var_res_exp_const (EL n (SND tl))):holfoot_a_expression)) data)))
         (COUNT_LIST n))`


val holfoot_ap_data_array_def = Define `
   holfoot_ap_data_array e ne data =
      var_res_exp_prop ne (\n. 
      (asl_trivial_cond (EVERY (\tl. (LENGTH (SND tl) = n)) data /\ 
                         ALL_DISTINCT (MAP FST data))      
      (var_res_map DISJOINT_FMAP_UNION
         (\el. holfoot_ap_points_to (FST el) (SND el))
         (holfoot_ap_data_array_MAP_LIST e n data))))`


val LENGTH___holfoot_ap_data_array_MAP_LIST = store_thm ("LENGTH___holfoot_ap_data_array_MAP_LIST",
``LENGTH (holfoot_ap_data_array_MAP_LIST e n data) = n``,
SIMP_TAC list_ss [holfoot_ap_data_array_MAP_LIST_def, LENGTH_COUNT_LIST]);


val EL___holfoot_ap_data_array_MAP_LIST = store_thm ("EL___holfoot_ap_data_array_MAP_LIST",
``!e n data m. (m < n) ==>
(EL m (holfoot_ap_data_array_MAP_LIST e n data) = 
 (var_res_exp_add e m,
   LIST_TO_FMAP (MAP (\tl. (FST tl), var_res_exp_const (EL m (SND tl))) data)))``,
SIMP_TAC list_ss [holfoot_ap_data_array_MAP_LIST_def, EL_MAP, LENGTH_COUNT_LIST,
   EL_COUNT_LIST]);


val MEM___holfoot_ap_data_array_MAP_LIST = store_thm ("MEM___holfoot_ap_data_array_MAP_LIST",
``!x e n data. MEM x (holfoot_ap_data_array_MAP_LIST e n data) = 
 (?m. m < n /\ (x = (var_res_exp_add e m,
   LIST_TO_FMAP (MAP (\tl. (FST tl), var_res_exp_const (EL m (SND tl))) data))))``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [MEM_EL, EL___holfoot_ap_data_array_MAP_LIST,
   LENGTH___holfoot_ap_data_array_MAP_LIST]);


val holfoot_ap_data_array_MAP_LIST___REWRITE = store_thm ("holfoot_ap_data_array_MAP_LIST___REWRITE",
``(!e data. (holfoot_ap_data_array_MAP_LIST e 0 data) = []) /\
  (!e n data. (holfoot_ap_data_array_MAP_LIST e (SUC n) data) =
  ((e, LIST_TO_FMAP (MAP (\tl. (FST tl), var_res_exp_const (HD (SND tl))) data))::
   (holfoot_ap_data_array_MAP_LIST (var_res_exp_add e 1) n 
       (MAP (\tl. (FST tl, TL (SND tl))) data))))``,

SIMP_TAC list_ss [holfoot_ap_data_array_MAP_LIST_def, COUNT_LIST_def] THEN
SIMP_TAC list_ss [var_res_exp_add_sub_REWRITES, MAP_MAP_o, combinTheory.o_DEF,
   EL, GSYM arithmeticTheory.ADD1]);


val holfoot_ap_data_array_MAP_LIST___REWRITE_EVAL = save_thm
 ("holfoot_ap_data_array_MAP_LIST___REWRITE_EVAL",
   CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV holfoot_ap_data_array_MAP_LIST___REWRITE);


val holfoot_ap_data_array___CONST = store_thm ("holfoot_ap_data_array___CONST",
``holfoot_ap_data_array e (var_res_exp_const n) data =
      (asl_trivial_cond (EVERY (\tl. (LENGTH (SND tl) = n)) data /\ 
                         ALL_DISTINCT (MAP FST data))      
      (var_res_map DISJOINT_FMAP_UNION
         (\el. holfoot_ap_points_to (FST el) (SND el))
         (holfoot_ap_data_array_MAP_LIST e n data)))``,
SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop___CONST]);



val holfoot_ap_data_array_0 = store_thm ("holfoot_ap_data_array_0",
``!e data. holfoot_ap_data_array e (var_res_exp_const 0) data = 
  var_res_bool_proposition DISJOINT_FMAP_UNION (EVERY (\tl. NULL (SND tl)) data /\
      ALL_DISTINCT (MAP FST data))``,

SIMP_TAC list_ss [holfoot_ap_data_array___CONST, holfoot_ap_data_array_MAP_LIST___REWRITE,
   var_res_map___REWRITES, IS_SEPARATION_COMBINATOR___FINITE_MAP, 
   asl_trivial_cond___var_res_stack_true, LENGTH_NIL, GSYM NULL_EQ_NIL]);


val holfoot_ap_data_array_0_start = store_thm ("holfoot_ap_data_array_0_start",
``!n data. holfoot_ap_data_array (var_res_exp_const 0) n data = 
  asl_trivial_cond ((EVERY (\tl. NULL (SND tl)) data /\
      ALL_DISTINCT (MAP FST data)))
     (var_res_prop_equal DISJOINT_FMAP_UNION n (var_res_exp_const 0))``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, LET_THM,
   asl_bool_EVAL, var_res_prop_equal_unequal_EXPAND, IN_ABS,
   var_res_exp_const_EVAL, IN_SING, asl_emp_DISJOINT_FMAP_UNION] THEN
REPEAT STRIP_TAC THEN
Cases_on `n (FST x)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x'` THENL [
   ASM_SIMP_TAC list_ss [LENGTH_NIL, NULL_EQ_NIL,
      holfoot_ap_data_array_MAP_LIST___REWRITE, var_res_map___REWRITES,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, var_res_prop_stack_true_REWRITE,
      IN_ABS, asl_emp_DISJOINT_FMAP_UNION, IN_SING],


   ASM_SIMP_TAC list_ss [
      holfoot_ap_data_array_MAP_LIST___REWRITE, var_res_map___REWRITES,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, holfoot_ap_points_to___null,
      asl_false___asl_star_THM, asl_bool_EVAL]
]);



val holfoot_ap_data_array_SUC = store_thm ("holfoot_ap_data_array_SUC",
``!e n data. 
  (holfoot_ap_data_array e (var_res_exp_const (SUC n)) data = 
  asl_trivial_cond (EVERY (\tl. ~(NULL (SND tl))) data)
       (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
           (holfoot_ap_points_to e (LIST_TO_FMAP 
                 (MAP (\tl. (FST tl,var_res_exp_const (HD (SND tl)))) data)))
           (holfoot_ap_data_array (var_res_exp_add e 1) (var_res_exp_const n)
               (MAP (\tl. (FST tl, TL (SND tl))) data))))``,

REPEAT STRIP_TAC THEN
SIMP_TAC list_ss [holfoot_ap_data_array___CONST, holfoot_ap_data_array_MAP_LIST___REWRITE,
   var_res_map___REWRITES, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   EVERY_MAP] THEN
SIMP_TAC std_ss [asl_trivial_cond___asl_star, asl_trivial_cond___asl_trivial_cond,
   GSYM EVERY_CONJ, CONJ_ASSOC, MAP_MAP_o, combinTheory.o_DEF, ETA_THM] THEN
`!l:num list. (~NULL l /\ (LENGTH (TL l) = n)) = (LENGTH l = SUC n)` by ALL_TAC THEN1 (
   Cases_on `l` THEN SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC std_ss []);


val holfoot_ap_data_array_SNOC = store_thm ("holfoot_ap_data_array_SNOC",
``!e n data. 
  (holfoot_ap_data_array e (var_res_exp_const (SUC n)) data = 
  asl_trivial_cond (EVERY (\tl. ~(NULL (SND tl))) data)
       (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
           (holfoot_ap_data_array e (var_res_exp_const n)
               (MAP (\tl. (FST tl, FRONT (SND tl))) data))
           (holfoot_ap_points_to (var_res_exp_add e n) (LIST_TO_FMAP 
                 (MAP (\tl. (FST tl,var_res_exp_const (EL n (SND tl)))) data)))))``,

REPEAT STRIP_TAC THEN
SIMP_TAC list_ss [holfoot_ap_data_array___CONST, holfoot_ap_data_array_MAP_LIST_def,
   COUNT_LIST_SNOC, MAP_SNOC, var_res_map_SNOC, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_map_MAP, combinTheory.o_DEF, EVERY_MAP, MAP_MAP_o] THEN
SIMP_TAC std_ss [asl_trivial_cond___asl_star, asl_trivial_cond___asl_trivial_cond,
   GSYM EVERY_CONJ, CONJ_ASSOC, ETA_THM] THEN
`!l:num list. (~NULL l /\ (LENGTH (FRONT l) = n)) = (LENGTH l = SUC n)` by ALL_TAC THEN1 (
   Cases_on `l` THEN SIMP_TAC list_ss [LENGTH_FRONT_CONS]
) THEN
ASM_SIMP_TAC std_ss [] THEN
Cases_on `EVERY (\tl. LENGTH (SND tl) = SUC n) data /\ 
          ALL_DISTINCT (MAP FST data)` THEN (
   FULL_SIMP_TAC std_ss [asl_trivial_cond_TF]
) THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
MATCH_MP_TAC var_res_map___FUN_EQ THEN
SIMP_TAC std_ss [MEM_COUNT_LIST, IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN AP_TERM_TAC THEN
Induct_on `data` THEN SIMP_TAC list_ss [] THEN
METIS_TAC[EL_FRONT]);


val holfoot_ap_data_array_1 = store_thm ("holfoot_ap_data_array_1",
``!e data.
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  (holfoot_ap_data_array e (var_res_exp_const 1) data = 
   asl_trivial_cond (EVERY (\tl. (LENGTH (SND tl) = 1)) data /\ (ALL_DISTINCT (MAP FST data)))
      (holfoot_ap_points_to e (LIST_TO_FMAP 
           (MAP (\tl. (FST tl,var_res_exp_const (HD (SND tl)))) data))))``,

SIMP_TAC std_ss [CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV holfoot_ap_data_array_SUC,
   holfoot_ap_data_array_0, EVERY_MAP] THEN
REPEAT STRIP_TAC THEN 
Q.ABBREV_TAC `p = (holfoot_ap_points_to e (LIST_TO_FMAP
        (MAP (\tl. (FST tl,var_res_exp_const (HD (SND tl)))) data)))` THEN
`VAR_RES_IS_STACK_IMPRECISE p` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `p` THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___points_to,
      FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [EVERY_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC std_ss [asl_trivial_cond___asl_star_var_res_bool_proposition,
   IS_SEPARATION_COMBINATOR___FINITE_MAP, GSYM EVERY_CONJ,
   asl_trivial_cond___asl_trivial_cond, CONJ_ASSOC, MAP_MAP_o,
   combinTheory.o_DEF, ETA_THM] THEN
`!l:num list. (~NULL l /\ (NULL (TL l))) = (LENGTH l = 1)` by ALL_TAC THEN1 (
   Cases_on `l` THEN SIMP_TAC list_ss [] THEN
   Cases_on `t` THEN SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC std_ss []);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array",
``!e n data vs.
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs n ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
       (holfoot_ap_data_array e n data)``,

SIMP_TAC std_ss [holfoot_ap_data_array_def] THEN 
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_prop THEN
ASM_SIMP_TAC std_ss [] THEN
CONSEQ_REWRITE_TAC ([], 
   [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map], []) THEN
ASM_SIMP_TAC std_ss [EVERY_MEM, MEM___holfoot_ap_data_array_MAP_LIST,
   IS_SEPARATION_COMBINATOR___FINITE_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
CONSEQ_REWRITE_TAC ([], 
   [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
    VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub,
    FEVERY_LIST_TO_FMAP], []) THEN
ASM_SIMP_TAC list_ss [EVERY_MAP,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]);



val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array",
`` !e n data.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>
     VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_data_array e n data)``,

REWRITE_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
        GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
             VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array]);


val var_res_prop_varlist_update___holfoot_ap_data_array = 
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_array",
``!vcL e n data.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>
     (var_res_prop_varlist_update vcL (holfoot_ap_data_array e n data) =
      holfoot_ap_data_array (var_res_exp_varlist_update vcL e) (var_res_exp_varlist_update vcL n) data)``,

SIMP_TAC std_ss [holfoot_ap_data_array_def,
   var_res_prop_varlist_update___var_res_exp_prop,
   var_res_prop_varlist_update___asl_trivial_cond,
   holfoot_ap_data_array_MAP_LIST_def,
   var_res_map_MAP, combinTheory.o_DEF] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
Q.MATCH_ABBREV_TAC `var_res_prop_varlist_update vcL (var_res_map DISJOINT_FMAP_UNION P l) = XXX` THEN
Q.UNABBREV_TAC `XXX` THEN
`!l. VAR_RES_IS_STACK_IMPRECISE (P l)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [] THEN
   CONSEQ_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
      FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [EVERY_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___var_res_map,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
AP_THM_TAC THEN AP_TERM_TAC THEN 
Q.UNABBREV_TAC `P` THEN
ASM_SIMP_TAC std_ss [combinTheory.o_DEF,
   var_res_prop_varlist_update___holfoot_ap_points_to,
   var_res_exp_varlist_update___var_res_exp_add_sub_EVAL,
   var_res_exp_varlist_update___const_EVAL,
   o_f_LIST_TO_FMAP, MAP_MAP_o]);


val holfoot_ap_data_array___not_def_start = store_thm ("holfoot_ap_data_array___not_def_start",
``!n e data s. 
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
  (e (FST s) = NONE)  ==>
 
  (holfoot_ap_data_array e n data s = 
   (EVERY (\tl. NULL (SND tl)) data /\ ALL_DISTINCT (MAP FST data) /\
    (n (FST s) = SOME 0) /\ (SND s = FEMPTY)))``,

REPEAT STRIP_TAC THEN
Cases_on `n (FST s)` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, LET_THM]
) THEN
`holfoot_ap_data_array e n data s =
 holfoot_ap_data_array e (var_res_exp_const x) data s` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def,
      LET_THM, var_res_exp_const_EVAL]
) THEN
Cases_on `x` THEN1 (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_array_0,
      var_res_bool_proposition_REWRITE, asl_emp_DISJOINT_FMAP_UNION, IN_SING]
) THEN

ASM_SIMP_TAC arith_ss [holfoot_ap_data_array_SUC, asl_bool_EVAL] THEN
DISJ2_TAC THEN
Q.MATCH_ABBREV_TAC `~(s IN asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION) P1 P2)` THEN
`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   CONSEQ_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
      FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      EVERY_MAP]
) THEN

ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS] THEN
Q.UNABBREV_TAC `P1` THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, LET_THM, IN_ABS]);


val holfoot_ap_array_def = Define `
   holfoot_ap_array e n = holfoot_ap_data_array e n []`;

val holfoot_ap_array___ALTERNATIVE_DEF = store_thm ("holfoot_ap_array___ALTERNATIVE_DEF",
``!e en. holfoot_ap_array e en = 
        var_res_exp_prop en (\n.
        var_res_map DISJOINT_FMAP_UNION  (\n.
           holfoot_ap_points_to (var_res_exp_add e n) FEMPTY)
           (COUNT_LIST n))``,
SIMP_TAC list_ss [holfoot_ap_array_def, holfoot_ap_data_array_def,
   holfoot_ap_data_array_MAP_LIST_def, LIST_TO_FMAP_def, asl_trivial_cond_TF,
   FUPDATE_LIST_THM, var_res_map_MAP, MAP_MAP_o, combinTheory.o_DEF]);

val holfoot_ap_array_SNOC = store_thm ("holfoot_ap_array_SNOC",
   ``!e n. holfoot_ap_array e (var_res_exp_const (SUC n)) = 
       (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
       (holfoot_ap_array e (var_res_exp_const n))
       (holfoot_ap_points_to (var_res_exp_add e n) FEMPTY))``,

SIMP_TAC std_ss [holfoot_ap_array___ALTERNATIVE_DEF, COUNT_LIST_SNOC,
   var_res_map_SNOC, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_exp_prop___CONST]);




val holfoot_ap_array_REWRITE = store_thm ("holfoot_ap_array_REWRITE",
``(!e. (holfoot_ap_array e (var_res_exp_const 0) = var_res_prop_stack_true DISJOINT_FMAP_UNION)) /\
  (!e n. (holfoot_ap_array e (var_res_exp_const (SUC n)) = 
      (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
      (holfoot_ap_points_to e FEMPTY)
      (holfoot_ap_array (var_res_exp_add e 1) (var_res_exp_const n)))))``,
SIMP_TAC list_ss [holfoot_ap_array___ALTERNATIVE_DEF,
   var_res_exp_prop___CONST,
   COUNT_LIST_def, var_res_map___REWRITES,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_exp_add_sub_REWRITES, var_res_map_MAP,
   combinTheory.o_DEF, GSYM arithmeticTheory.ADD1]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array",
``!e n vs.
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs n ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_array e n)``,

SIMP_TAC std_ss [holfoot_ap_array_def,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array]);


val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_array = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_array",
`` !e n.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>
     VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_array e n)``,
SIMP_TAC std_ss [holfoot_ap_array_def, VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array]);


val var_res_prop_varlist_update___holfoot_ap_array = 
store_thm ("var_res_prop_varlist_update___holfoot_ap_array",
``!vcL e n.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>
     (var_res_prop_varlist_update vcL (holfoot_ap_array e n) =
      holfoot_ap_array (var_res_exp_varlist_update vcL e) (var_res_exp_varlist_update vcL n))``,
SIMP_TAC std_ss [holfoot_ap_array_def, var_res_prop_varlist_update___holfoot_ap_data_array]);


val holfoot_ap_array___ALTERNATIVE_DEF2 = store_thm ("holfoot_ap_array___ALTERNATIVE_DEF2",
``!e en. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
     (holfoot_ap_array e en =
     var_res_exp_prop en (\n.
        if (n = 0) then var_res_prop_stack_true DISJOINT_FMAP_UNION else
        var_res_exp_prop e (\loc.
            (\state. loc <> 0 /\ (FDOM (SND state) = (IMAGE (\m. loc + m) (count n)))))))``,

SIMP_TAC std_ss [holfoot_ap_array___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN ABS_TAC THEN
POP_ASSUM MP_TAC THEN
MAP_EVERY (fn q => Q.SPEC_TAC (q, q)) [`e`, `n`] THEN
Induct_on `n` THEN1 (
   SIMP_TAC list_ss [COUNT_LIST_def, var_res_map___REWRITES,
      IS_SEPARATION_COMBINATOR___FINITE_MAP]
) THEN
SIMP_TAC std_ss [var_res_map_SNOC, IS_SEPARATION_COMBINATOR___FINITE_MAP, COUNT_LIST_SNOC] THEN
REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC `asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION) P1 P2 = XXX` THEN
Q.UNABBREV_TAC `XXX` THEN
`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P1`, `P2`] THEN
   EXT_CONSEQ_REWRITE_TAC [K (DEPTH_CONV BETA_CONV)] [EVERY_MEM] ([], [
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      VAR_RES_IS_STACK_IMPRECISE___var_res_map,
      FEVERY_FEMPTY, 
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub], []) THEN
  ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
     IS_SEPARATION_COMBINATOR___FINITE_MAP]
) THEN
ASM_SIMP_TAC arith_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE] THEN
UNABBREV_ALL_TAC THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
ASM_SIMP_TAC list_ss [IN_ABS, LET_THM, holfoot_ap_points_to_def,
   var_res_exp_add_def, var_res_exp_binop_const_REWRITE,
   var_res_exp_const_EVAL, FEVERY_FEMPTY, var_res_exp_prop_def, IN_SING,
   var_res_prop_stack_true_REWRITE, asl_emp_DISJOINT_FMAP_UNION] THEN
Cases_on `e (FST x)` THEN (
   ASM_SIMP_TAC std_ss []
) THEN
Cases_on `n = 0` THEN (
   ASM_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___FEMPTY, FEVERY_FEMPTY,
      CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV COUNT_SUC,
      COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY, COUNT_SUC, IN_ABS]
) THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE,
      FDOM_FUNION, EXTENSION, IN_SING, IN_UNION, IN_INSERT] THEN
   METIS_TAC[],

   Q.ABBREV_TAC `s2 = (IMAGE (\m. m + x') (count n))` THEN
   Q.ABBREV_TAC `n'' = n + x'` THEN
   Q.EXISTS_TAC `DRESTRICT (SND x) s2` THEN
   Q.EXISTS_TAC `DRESTRICT (SND x) {n''}` THEN
   `~(n'' IN s2) /\ (s2 INTER {n''} = EMPTY)` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [IN_IMAGE, IN_COUNT, EXTENSION, IN_INTER, NOT_IN_EMPTY,
         IN_SING]
   ) THEN
   ASM_SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE, FDOM_DRESTRICT,
      INSERT_INTER] THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF,
      DRESTRICT_DEF, IN_INTER, IN_SING, DISJOINT_DEF,
      NOT_IN_EMPTY, IN_INSERT, IN_UNION] THEN
   METIS_TAC[]
]);


val holfoot_ap_array_1 = store_thm ("holfoot_ap_array_1",
``!e. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
      (holfoot_ap_array e (var_res_exp_const 1) = holfoot_ap_points_to e FEMPTY)``,
SIMP_TAC list_ss [CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV holfoot_ap_array_REWRITE,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM,
   VAR_RES_IS_STACK_IMPRECISE___points_to, FEVERY_FEMPTY,
   IS_SEPARATION_COMBINATOR___FINITE_MAP]);



val holfoot_ap_data_array___ELIM_DATA =
store_thm ("holfoot_ap_data_array___ELIM_DATA",
``!e n data1 data2 s.
(s IN holfoot_ap_data_array e n data2 /\ (!x. MEM x data1 ==> MEM x data2) /\
   ALL_DISTINCT (MAP FST data1)) ==>
(s IN holfoot_ap_data_array e n data1)``,

SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, IN_ABS, LET_THM] THEN
REPEAT STRIP_TAC THEN
`?cn. n (FST s) = SOME cn` by METIS_TAC[IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [asl_bool_EVAL] THEN
POP_ASSUM (K ALL_TAC) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [EVERY_MEM]
) THEN
Q.PAT_ASSUM `EVERY X data2` (K ALL_TAC) THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
MAP_EVERY (fn x => Q.SPEC_TAC (x,x)) [`data1`, `data2`, `s`, `e`, `cn`] THEN

Induct_on `cn` THEN1 (
   SIMP_TAC std_ss [holfoot_ap_data_array_MAP_LIST___REWRITE]
) THEN
FULL_SIMP_TAC std_ss [holfoot_ap_data_array_MAP_LIST___REWRITE,
   var_res_map_REWRITE, IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `s IN X` MP_TAC THEN
Q.MATCH_ABBREV_TAC `s IN asl_star f P1 P2 ==> s IN asl_star f P1' P2'` THEN
Tactical.REVERSE (`(!s. s IN P1 ==> s IN P1') /\ (!s. s IN P2 ==> s IN P2')` by ALL_TAC) THEN1 (
   SIMP_TAC std_ss [asl_star_def, IN_ABS] THEN METIS_TAC[]
) THEN

UNABBREV_ALL_TAC THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC holfoot_ap_points_to___SUBMAP THEN
   Q.EXISTS_TAC `LIST_TO_FMAP (MAP (\tl. (FST tl,var_res_exp_const (HD (SND tl)))) data2)` THEN
   ASM_SIMP_TAC std_ss [SUBMAP_DEF, FDOM_LIST_TO_FMAP, IN_LIST_TO_SET, MAP_MAP_o,
      combinTheory.o_DEF, ETA_THM] THEN
   GEN_TAC THEN STRIP_TAC THEN
   `MEM x (MAP FST data2)` by ALL_TAC THEN1 (
       FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC[]
   ) THEN
   ASM_REWRITE_TAC[] THEN
   Q.MATCH_ABBREV_TAC `LIST_TO_FMAP L1 ' x = LIST_TO_FMAP L2 ' x` THEN
   `(MAP FST L1 = MAP FST data1) /\ (MAP FST L2 = MAP FST data2)` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, ETA_THM]
   ) THEN
   `?x2. MEM (x,x2) L1 /\ MEM (x,x2) L2` by ALL_TAC THEN1 (
       UNABBREV_ALL_TAC THEN
       FULL_SIMP_TAC std_ss [MEM_MAP] THEN
       METIS_TAC[]
   ) THEN
   METIS_TAC [LIST_TO_FMAP___ALL_DISTINCT],


   Q.PAT_ASSUM `!e s data2 data1. X ==> Y` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `MAP (\tl. (FST tl,TL (SND tl))) data2` THEN
   ASM_SIMP_TAC std_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      MAP_MAP_o, combinTheory.o_DEF, ETA_THM, EVERY_MAP] THEN
   METIS_TAC[]
]);


val holfoot_ap_data_array___ELIM_DATA___COMPLETE =
store_thm ("holfoot_ap_data_array___ELIM_DATA___COMPLETE",
``!e n data s.
(s IN holfoot_ap_data_array e n data) ==>
(s IN holfoot_ap_array e n)``,

SIMP_TAC std_ss [holfoot_ap_array_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_ap_data_array___ELIM_DATA THEN
Q.EXISTS_TAC `data` THEN
ASM_SIMP_TAC list_ss []);



val holfoot_ap_data_array___DATA_PERM =
store_thm ("holfoot_ap_data_array___DATA_PERM",
``!e n data1 data2.
(PERM data1 data2) ==>
(holfoot_ap_data_array e n data1 =
 holfoot_ap_data_array e n data2)``,

SIMP_TAC std_ss [holfoot_ap_data_array_def] THEN
REPEAT STRIP_TAC THEN
`(!n. (EVERY (\tl. LENGTH (SND tl) = n) data2 =
       EVERY (\tl. LENGTH (SND tl) = n) data1)) /\
 (ALL_DISTINCT (MAP FST data2) = ALL_DISTINCT (MAP FST data1))` by ALL_TAC THEN1 (

   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [EVERY_MEM] THEN
      METIS_TAC[sortingTheory.PERM_MEM_EQ],

      MATCH_MP_TAC (sortingTheory.ALL_DISTINCT_PERM) THEN
      MATCH_MP_TAC sortingTheory.PERM_MAP THEN
      ASM_SIMP_TAC std_ss [sortingTheory.PERM_SYM]
   ]
) THEN

ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [EXTENSION, var_res_exp_prop_def,
   LET_THM, IN_ABS, asl_bool_EVAL] THEN
SIMP_TAC (std_ss++CONJ_ss) [IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM,
  GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`
   (holfoot_ap_data_array_MAP_LIST e y data2 = 
    holfoot_ap_data_array_MAP_LIST e y data1)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN

SIMP_TAC list_ss [holfoot_ap_data_array_MAP_LIST_def,
   LIST_EQ_REWRITE, LENGTH_COUNT_LIST,
   EL_MAP, EL_COUNT_LIST] THEN
SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_LIST_TO_FMAP,
  MAP_MAP_o, combinTheory.o_DEF, ETA_THM, IN_LIST_TO_SET, EXTENSION,
  MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[sortingTheory.PERM_MEM_EQ],

   Cases_on `y'` THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC (prove (``!c. ((A = c) /\ (B = c)) ==> (A = B)``, SIMP_TAC std_ss [])) THEN
   Q.EXISTS_TAC `var_res_exp_const (EL x' r)` THEN
   CONSEQ_REWRITE_TAC ([], [LIST_TO_FMAP___ALL_DISTINCT], []) THEN
   ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, ETA_THM,
      MEM_MAP, var_res_exp_eq_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM] THEN
   NTAC 2 (Q.EXISTS_TAC `(q, r)`) THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[sortingTheory.PERM_MEM_EQ]
]);


val holfoot_ap_data_array___NOT_EMPTY_DATA = store_thm ("holfoot_ap_data_array___NOT_EMPTY_DATA",
``!e n t tvL data.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>

(holfoot_ap_data_array e n ((t,tvL)::data) =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (var_res_prop_equal DISJOINT_FMAP_UNION n (var_res_exp_const (LENGTH tvL)))
   (holfoot_ap_data_array e (var_res_exp_const (LENGTH tvL)) ((t,tvL)::data)))``,

ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, var_res_exp_const_def, IN_ABS,
   asl_emp_DISJOINT_FMAP_UNION, IN_SING, DISJOINT_FMAP_UNION___FEMPTY] THEN
Tactical.REVERSE (Cases_on `n (FST x) = SOME (LENGTH tvL)`) THEN1 (
   ASM_SIMP_TAC list_ss [holfoot_ap_data_array_def, var_res_exp_prop_def,
      LET_THM, IN_ABS, asl_bool_EVAL] THEN
   Cases_on `n (FST x)` THEN FULL_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_array_def,
   var_res_exp_prop_def, LET_THM, IN_ABS]);



val holfoot_ap_data_array___LENGTH_NOT_EQ_REWRITE = store_thm (
"holfoot_ap_data_array___LENGTH_NOT_EQ_REWRITE",
``!e nc t tvL data.
~(LENGTH tvL = nc) ==> 
(holfoot_ap_data_array e (var_res_exp_const nc) ((t,tvL)::data) =
 asl_false)``,
SIMP_TAC list_ss [holfoot_ap_data_array___CONST, asl_trivial_cond_TF]);


val holfoot_ap_data_array___var_res_prop_implies___length_eq = store_thm ("holfoot_ap_data_array___var_res_prop_implies___length_eq",
``!wpb rpb sfb e n t tvL data.
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET 
    (SET_OF_BAG (BAG_UNION wpb rpb)) n ==>

(var_res_prop_implies DISJOINT_FMAP_UNION (wpb, rpb) 
    (BAG_INSERT (holfoot_ap_data_array e n ((t,tvL)::data)) sfb)
    {|var_res_prop_equal DISJOINT_FMAP_UNION n (var_res_exp_const (LENGTH tvL))|})``,

SIMP_TAC std_ss [var_res_prop_implies_REWRITE, BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___EQ,
   var_res_prop___COND_INSERT,  var_res_prop___PROP___REWRITE,
   var_res_prop___PROP_INSERT, IN_ABS,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND, IN_ABS,
  asl_emp_DISJOINT_FMAP_UNION, var_res_exp_const_EVAL, IN_SING,
  DISJOINT_FMAP_UNION___FEMPTY, EXTENSION] THEN
GEN_TAC THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

SIMP_TAC list_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, LET_THM, IN_ABS,
  asl_bool_EVAL]);



val holfoot_ap_data_array___implies_in_heap = store_thm ("holfoot_ap_data_array___implies_in_heap",
``!c B sfb e n data.
((e <= c) /\ (c < e + n)) ==>
(holfoot_implies_in_heap B 
    (BAG_INSERT (holfoot_ap_data_array (var_res_exp_const e) (var_res_exp_const n) data) sfb)
    (var_res_exp_const c))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_implies_in_heap___FIRST THEN
ASM_SIMP_TAC std_ss [var_res_exp_const_EVAL,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
IMP_RES_TAC holfoot_ap_data_array___ELIM_DATA___COMPLETE THEN
FULL_SIMP_TAC std_ss [holfoot_ap_array___ALTERNATIVE_DEF2,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   var_res_exp_prop___CONST] THEN
Cases_on `n = 0` THEN1 (
   FULL_SIMP_TAC arith_ss []
) THEN
FULL_SIMP_TAC arith_ss [IN_ABS, IN_IMAGE, IN_COUNT] THEN
Q.EXISTS_TAC `c - e` THEN
DECIDE_TAC);



val holfoot_ap_data_array___implies_in_heap___COMPUTE = store_thm (
   "holfoot_ap_data_array___implies_in_heap___COMPUTE",
``!e n data B c.
((e <= c) /\ (c < e + n)) ==>
(holfoot_implies_in_heap B 
    {|holfoot_ap_data_array (var_res_exp_const e) (var_res_exp_const n) data|}
    (var_res_exp_const c))``,
SIMP_TAC std_ss [holfoot_ap_data_array___implies_in_heap]);


val holfoot_ap_data_array___NOT_EMPTY_DATA_0 = store_thm ("holfoot_ap_data_array___NOT_EMPTY_DATA_0",
``!e n t data.
holfoot_ap_data_array e n ((t,[])::data) =
asl_trivial_cond (EVERY (\tl. NULL (SND tl)) data /\ ALL_DISTINCT (t::(MAP FST data)))
   (var_res_prop_equal DISJOINT_FMAP_UNION n (var_res_exp_const 0))``,

ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC list_ss [holfoot_ap_data_array_def,
  var_res_exp_prop_def, LET_THM, asl_bool_EVAL,
  var_res_prop_equal_unequal_EXPAND, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
  var_res_exp_const_def, IN_SING] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `0:num = XXX` (ASSUME_TAC o GSYM) THEN
ASM_SIMP_TAC std_ss [LENGTH_NIL, NULL_EQ_NIL,
   holfoot_ap_data_array_MAP_LIST___REWRITE,
   var_res_map_REWRITE, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   var_res_prop_stack_true_REWRITE,
   IN_ABS, asl_emp_DISJOINT_FMAP_UNION, IN_SING]);


val holfoot_ap_data_array___SPLIT = store_thm ("holfoot_ap_data_array___SPLIT",
``!e n1 n2 data.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>

(holfoot_ap_data_array e (var_res_exp_const (n1+n2)) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_array e (var_res_exp_const n1)
       (MAP (\tl. (FST tl, FIRSTN n1 (SND tl))) data))
   (holfoot_ap_data_array (var_res_exp_add e n1) (var_res_exp_const n2)
       (MAP (\tl. (FST tl, BUTFIRSTN n1 (SND tl))) data)))``,


Induct_on `n1` THEN1 (
   SIMP_TAC list_ss [holfoot_ap_data_array_0, EVERY_MAP,
      MAP_MAP_o, combinTheory.o_DEF, ETA_THM, var_res_exp_add_sub_REWRITES] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `ALL_DISTINCT (MAP FST data)` THENL [
      ASM_SIMP_TAC std_ss [var_res_bool_proposition_TF,
         IS_SEPARATION_COMBINATOR___FINITE_MAP,
         asl_star___var_res_prop_stack_true___STACK_IMPRECISE,
         VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
         IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL],


      ASM_SIMP_TAC std_ss [var_res_bool_proposition_TF, asl_false___asl_star_THM,
         holfoot_ap_data_array___CONST, asl_trivial_cond_TF]
   ]
) THEN

ASM_SIMP_TAC std_ss [holfoot_ap_data_array_SUC, ADD,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub] THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
SIMP_TAC list_ss [MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP,
   var_res_exp_add_sub_REWRITES, GSYM ADD1] THEN
REPEAT STRIP_TAC THEN

Q.MATCH_ABBREV_TAC `
    asl_trivial_cond c1 (asl_star f p1 (asl_star f a11 a12)) = 
    asl_star f (asl_trivial_cond c1' (asl_star f p1' a11')) a12'` THEN

`c1' = c1` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
   Cases_on `SND tl` THEN SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN 
MAP_EVERY Q.UNABBREV_TAC  [`c1`, `c1'`] THEN

Cases_on `EVERY (\tl. ~NULL (SND tl)) data` THEN (
   ASM_SIMP_TAC std_ss [asl_trivial_cond_TF, asl_false___asl_star_THM]
) THEN

`(MAP (\tl. (FST tl, (var_res_exp_const (HD (SND tl))):holfoot_a_expression)) data=
  MAP (\tl. (FST tl, var_res_exp_const (HD (TAKE (SUC n1) (SND tl))))) data) /\
 (MAP (\tl. (FST tl,TL (TAKE (SUC n1) (SND tl)))) data =
  MAP (\tl. (FST tl,TAKE n1 (TL (SND tl)))) data) /\
 (MAP (\tl. (FST tl,DROP (SUC n1) (SND tl))) data =
  MAP (\tl. (FST tl,DROP n1 (TL (SND tl)))) data)` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   FULL_SIMP_TAC list_ss [LIST_EQ_REWRITE, EVERY_MEM, EL_MAP,
     var_res_exp_eq_THM, GSYM FORALL_AND_THM] THEN
   GEN_TAC THEN
   Cases_on `x < LENGTH data` THEN ASM_REWRITE_TAC[] THEN
   `?n ns. SND (EL x data) = n::ns` by ALL_TAC THEN1 (
      `MEM (EL x data) data` by METIS_TAC[EL_IS_EL] THEN
      RES_TAC THEN
      Cases_on `SND (EL x data)` THEN 
      FULL_SIMP_TAC list_ss []
   ) THEN
   ASM_SIMP_TAC list_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN

METIS_TAC[asl_star___PROPERTIES, ASSOC_DEF,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);


val holfoot_ap_data_array___LENGTH_EXP_REWRITE = store_thm ("holfoot_ap_data_array___LENGTH_EXP_REWRITE",
``!e n1 n2 data s.
     (n1 (FST s) = n2 (FST s)) ==>
     (s IN holfoot_ap_data_array e n1 data =
      s IN holfoot_ap_data_array e n2 data)``,
SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def,
   IN_ABS, LET_THM]);

val holfoot_ap_data_array___START_EXP_REWRITE = store_thm ("holfoot_ap_data_array___START_EXP_REWRITE",
``!e1 e2 n data s.
     (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
     (e1 (FST s) = e2 (FST s)) ==>
     (s IN holfoot_ap_data_array e1 (var_res_exp_const n) data =
      s IN holfoot_ap_data_array e2 (var_res_exp_const n) data))``,


Induct_on `n` THEN1 (
   SIMP_TAC std_ss [holfoot_ap_data_array_0]
) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_array_SUC, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC `s IN asl_star f P1 P2 = s IN asl_star f P1' P2'` THEN

`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P1' /\
 VAR_RES_IS_STACK_IMPRECISE P2 /\ VAR_RES_IS_STACK_IMPRECISE P2'` by ALL_TAC THEN1 (

   UNABBREV_ALL_TAC THEN
   CONSEQ_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
      FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [EVERY_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
Q.UNABBREV_TAC `f` THEN

ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (`((FST s, es1) IN P1 = (FST s, es1) IN P1') /\
                   ((FST s, es2) IN P2 = (FST s, es2) IN P2')` by ALL_TAC) THEN1 (
   ASM_REWRITE_TAC[]
) THEN
UNABBREV_ALL_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM] THEN

Q.PAT_ASSUM `!e1 e2 data s. X` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub] THEN
ASM_SIMP_TAC std_ss [var_res_exp_add_def, var_res_exp_binop_const_REWRITE]);





val holfoot_ap_data_array___EXP_REWRITE = store_thm ("holfoot_ap_data_array___EXP_REWRITE",
``!e1 e2 n1 n2 data s.
     (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
     (e1 (FST s) = e2 (FST s)) /\ (n1 (FST s) = n2 (FST s))) ==>
     (s IN holfoot_ap_data_array e1 n1 data =
      s IN holfoot_ap_data_array e2 n2 data)``,

REPEAT STRIP_TAC THEN
Cases_on `n2 (FST s)` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, LET_THM, IN_ABS]
) THEN
`(s IN holfoot_ap_data_array e1 n1 data =
  s IN holfoot_ap_data_array e1 (var_res_exp_const x) data) /\
 (s IN holfoot_ap_data_array e2 n2 data =
  s IN holfoot_ap_data_array e2 (var_res_exp_const x) data)` by 
   METIS_TAC[holfoot_ap_data_array___LENGTH_EXP_REWRITE, var_res_exp_const_EVAL] THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[holfoot_ap_data_array___START_EXP_REWRITE]);




val holfoot_ap_data_array___var_res_exp_const_INTRO = store_thm ("holfoot_ap_data_array___var_res_exp_const_INTRO",
``(!e n data nc s.
     (n (FST s) = SOME nc) ==>
     (s IN holfoot_ap_data_array e n data =
      s IN holfoot_ap_data_array e (var_res_exp_const nc) data)) /\

(!e n data ec s.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
     (e (FST s) = SOME ec) ==>
     (s IN holfoot_ap_data_array e n data =
      s IN holfoot_ap_data_array (var_res_exp_const ec) n data))``,

REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC holfoot_ap_data_array___LENGTH_EXP_REWRITE THEN
   ASM_SIMP_TAC std_ss [var_res_exp_const_EVAL],

   MATCH_MP_TAC holfoot_ap_data_array___EXP_REWRITE THEN
   ASM_SIMP_TAC std_ss [var_res_exp_const_EVAL, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
]);




val holfoot_ap_data_array___SAME_START_LENGTH___const = prove (
``!e n data1 data2 st h1 h2 h.
     ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\
     ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 h /\
     (st,h1) IN holfoot_ap_data_array (var_res_exp_const e) (var_res_exp_const n) data1 /\
     (st,h2) IN holfoot_ap_data_array (var_res_exp_const e) (var_res_exp_const n) data2 ==>
     ((h1 = h2) /\ (!tag dl1 dl2. MEM (tag, dl1) data1 /\ MEM (tag, dl2) data2 ==> (dl1 = dl2)))``,

Induct_on `n` THEN1 (
   SIMP_TAC std_ss [holfoot_ap_data_array_0, var_res_bool_proposition_REWRITE,
     IN_ABS, asl_emp_DISJOINT_FMAP_UNION, IN_SING, NULL_EQ_NIL,
     ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FEMPTY, EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN


SIMP_TAC (std_ss++CONJ_ss) [holfoot_ap_data_array_SUC, asl_bool_EVAL,
   var_res_exp_add_sub_REWRITES] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

REPEAT (Q.PAT_ASSUM `s IN asl_star f X Y` MP_TAC) THEN

Q.MATCH_ABBREV_TAC `
   (st, h1) IN asl_star f P1 P2 ==>
   (st, h2) IN asl_star f P1' P2' ==> XXX` THEN
Q.UNABBREV_TAC `XXX` THEN

`VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P1' /\
 VAR_RES_IS_STACK_IMPRECISE P2 /\ VAR_RES_IS_STACK_IMPRECISE P2'` by ALL_TAC THEN1 (

   UNABBREV_ALL_TAC THEN
   CONSEQ_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
      VAR_RES_IS_STACK_IMPRECISE___points_to,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
      FEVERY_LIST_TO_FMAP], []) THEN
   ASM_SIMP_TAC list_ss [EVERY_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
Q.UNABBREV_TAC `f` THEN

ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS,
   DISJOINT_FMAP_UNION___REWRITE, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

`(es1' = es1) /\ 
 !tag dl1 dl2. MEM (tag,dl1) data1 /\ MEM (tag,dl2) data2 ==> (HD dl1 = HD dl2)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `(st, es1) IN X` MP_TAC THEN
   Q.PAT_ASSUM `(st, es1') IN X` MP_TAC THEN   
   UNABBREV_ALL_TAC THEN
   SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM,
     var_res_exp_const_EVAL, GSYM fmap_EQ_THM, IN_SING] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   `(es1' ' e = h ' e) /\ (es1 ' e = h ' e)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
         FUNION_DEF, IN_SING, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (Q.PAT_ASSUM `FEVERY X L` MP_TAC) THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [FEVERY_DEF, FDOM_LIST_TO_FMAP, MAP_MAP_o,
         combinTheory.o_DEF, IN_LIST_TO_SET, IS_SOME_EXISTS, ETA_THM,
         MEM_MAP, GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   Q.ABBREV_TAC `L1 = MAP (\tl. (FST tl,(var_res_exp_const (HD (SND tl))):holfoot_a_expression)) data1` THEN
   Q.ABBREV_TAC `L2 = MAP (\tl. (FST tl,(var_res_exp_const (HD (SND tl))):holfoot_a_expression)) data2` THEN
   REPEAT STRIP_TAC THEN
   `(LIST_TO_FMAP L1 ' tag st = LIST_TO_FMAP L2 ' tag st)` by 
      METIS_TAC[pairTheory.FST] THEN
   Tactical.REVERSE (`(LIST_TO_FMAP L1 ' tag = var_res_exp_const (HD dl1)) /\
    (LIST_TO_FMAP L2 ' tag = var_res_exp_const (HD dl2))` by ALL_TAC) THEN1 (
      FULL_SIMP_TAC std_ss [var_res_exp_const_EVAL]
   ) THEN
   `ALL_DISTINCT (MAP FST L1) /\ ALL_DISTINCT (MAP FST L2)` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, ETA_THM, 
          holfoot_ap_data_array___CONST, asl_bool_EVAL]
   ) THEN
   `MEM (tag, var_res_exp_const (HD dl1)) L1 /\
    MEM (tag, var_res_exp_const (HD dl2)) L2` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      ASM_SIMP_TAC std_ss [MEM_MAP, var_res_exp_eq_THM] THEN
      METIS_TAC[pairTheory.FST, pairTheory.SND]
   ) THEN
   ASM_SIMP_TAC std_ss [LIST_TO_FMAP___ALL_DISTINCT]
) THEN
Q.ABBREV_TAC `data1' = (MAP (\tl. (FST tl,TL (SND tl))) data1)` THEN
Q.ABBREV_TAC `data2' = (MAP (\tl. (FST tl,TL (SND tl))) data2)` THEN
`(es2 = es2') /\ 
 !tag dl1 dl2. MEM (tag,dl1) data1' /\ MEM (tag,dl2) data2' ==> (dl1 = dl2)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!e data1 data2 st h1 h2 h. X` MATCH_MP_TAC THEN
   MAP_EVERY Q.EXISTS_TAC [`e+1`, `st`, `h`] THEN
   MAP_EVERY Q.UNABBREV_TAC [`P2`, `P2'`] THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[ ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION]
) THEN

ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!e data1 data2 st h1 h2 h. X` (K ALL_TAC) THEN
`?dl_h dl1_l dl2_l. (dl1 = dl_h::dl1_l) /\ (dl2 = dl_h::dl2_l)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   RES_TAC THEN
   Cases_on `dl2` THEN Cases_on `dl1` THEN
   FULL_SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC list_ss [] THEN

Q.PAT_ASSUM `!tag dl1 dl2. X` MATCH_MP_TAC THEN
Q.EXISTS_TAC `tag` THEN
MAP_EVERY Q.UNABBREV_TAC [`data1'`, `data2'`] THEN
SIMP_TAC std_ss [MEM_MAP, PAIR_EXISTS_THM, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM] THEN
MAP_EVERY Q.EXISTS_TAC [`dl1`, `dl2`] THEN
ASM_SIMP_TAC list_ss []);




val holfoot_ap_data_array___SAME_START_LENGTH = store_thm ("holfoot_ap_data_array___SAME_START_LENGTH",
``!e1 e2 n1 n2 data1 data2 st h1 h2 h.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n2) /\
     ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\
     ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 h /\
     (st,h1) IN holfoot_ap_data_array e1 n1 data1 /\
     (st,h2) IN holfoot_ap_data_array e2 n2 data2 /\
     (e1 st = e2 st) /\ (n1 st = n2 st) ==>
     ((h1 = h2) /\ (!tag dl1 dl2. MEM (tag, dl1) data1 /\ MEM (tag, dl2) data2 ==> (dl1 = dl2)))``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (Cases_on `?nc. n2 st = SOME nc`) THEN1 (
  Cases_on `n2 st` THEN
  FULL_SIMP_TAC std_ss [holfoot_ap_data_array_def, var_res_exp_prop_def, IN_ABS, LET_THM]
) THEN
FULL_SIMP_TAC std_ss [] THEN
`(st,h1) IN holfoot_ap_data_array e1 (var_res_exp_const nc) data1 /\
 (st,h2) IN holfoot_ap_data_array e2 (var_res_exp_const nc) data2` by 
   METIS_TAC[holfoot_ap_data_array___var_res_exp_const_INTRO, pairTheory.FST] THEN

Cases_on `nc` THEN1 (
   FULL_SIMP_TAC std_ss [holfoot_ap_data_array_0, IN_SING,
     var_res_bool_proposition_REWRITE, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
     EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN 
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [NULL_EQ_NIL]
) THEN
Tactical.REVERSE (Cases_on `?ec. e2 st = SOME ec`) THEN1 (
  Cases_on `e2 st` THEN
  FULL_SIMP_TAC std_ss [holfoot_ap_data_array_SUC, asl_bool_EVAL] THEN
  Q.PAT_ASSUM `(st, h1) IN X` MP_TAC THEN
  Q.MATCH_ABBREV_TAC `(st, h1) IN asl_star f P1 P2 ==> XXX` THEN
  `VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC THEN1 (
     UNABBREV_ALL_TAC THEN
     CONSEQ_REWRITE_TAC ([], 
        [VAR_RES_IS_STACK_IMPRECISE___points_to,
         VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_array,
         IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
         FEVERY_LIST_TO_FMAP], []) THEN
     ASM_SIMP_TAC list_ss [EVERY_MAP, IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
  ) THEN
  Q.UNABBREV_TAC `f` THEN
  Q.UNABBREV_TAC `P1` THEN
  ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, IN_ABS, 
     holfoot_ap_points_to_def, LET_THM]
) THEN
FULL_SIMP_TAC std_ss [] THEN

`(st,h1) IN holfoot_ap_data_array (var_res_exp_const ec) (var_res_exp_const (SUC n)) data1 /\
 (st,h2) IN holfoot_ap_data_array (var_res_exp_const ec) (var_res_exp_const (SUC n)) data2` by 
   METIS_TAC[holfoot_ap_data_array___var_res_exp_const_INTRO, pairTheory.FST] THEN
METIS_TAC[holfoot_ap_data_array___SAME_START_LENGTH___const]);




val VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH___REWRITE",
``!e n data1 data2 wpb rpb sfb_context sfb_split sfb_imp.

(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1) /\
 ALL_DISTINCT (MAP FST data2)) ==>

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) n

==>
 VAR_RES_FRAME_SPLIT___REWRITE_OK DISJOINT_FMAP_UNION (wpb,rpb) 
   sfb_context
   (BAG_INSERT (holfoot_ap_data_array e n data1) sfb_split)
   (BAG_INSERT (holfoot_ap_data_array e n data2) sfb_imp) 


   (BAG_INSERT (holfoot_ap_data_array e n data1) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          (EVERY (\x. MEM x data1) data2)) sfb_imp)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_UNION, IN_ABS,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array,
   BAG_UNION_INSERT,
   var_res_prop___PROP_INSERT] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_bool_proposition_REWRITE, IN_ABS,
  asl_emp_DISJOINT_FMAP_UNION, IN_SING,
  DISJOINT_FMAP_UNION___FEMPTY, GSYM RIGHT_EXISTS_AND_THM] THEN
REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

Tactical.REVERSE (Cases_on `s1' = s1`) THEN1 (
   FULL_SIMP_TAC std_ss [
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
   `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1 (SND s) /\
    ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1' (SND s)` by ALL_TAC THEN1 (
       METIS_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___FINITE_MAP]
   ) THEN
   METIS_TAC[holfoot_ap_data_array___SAME_START_LENGTH]
) THEN
FULL_SIMP_TAC std_ss [] THEN
EQ_TAC THENL [   
   REPEAT STRIP_TAC THEN
   `!tag dl1 dl2.
       MEM (tag,dl1) data1 /\ MEM (tag,dl2) data2 ==> (dl1 = dl2)` by ALL_TAC THEN1 (
      METIS_TAC[holfoot_ap_data_array___SAME_START_LENGTH,
         ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___REFL,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
   ) THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   REPEAT STRIP_TAC  THEN
   `?tag dl1. x = (tag, dl1)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
   `?dl2. MEM (tag, dl2) data1` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_LIST_TO_SET,
         MEM_MAP, GSYM LEFT_FORALL_IMP_THM, PAIR_EXISTS_THM] THEN
      METIS_TAC[pairTheory.FST]
   ) THEN
   METIS_TAC[],


   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC holfoot_ap_data_array___ELIM_DATA THEN
   Q.EXISTS_TAC `data1` THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM]
]);





val VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH = store_thm (
"VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH",
``!e n data1 data2 sfb_restP wpb wpb' rpb sfb_context sfb_split sfb_imp sr.

(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1) /\
 ALL_DISTINCT (MAP FST data2) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) n)

==>
 ((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_array e n data1) sfb_split)
   (BAG_INSERT (holfoot_ap_data_array e n data2) sfb_imp) sfb_restP) =

  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_array e n data1) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          (EVERY (\x. MEM x data1) data2)) sfb_imp)
   sfb_restP))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___REWRITE_OK___THM THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH___REWRITE) THEN
ASM_REWRITE_TAC[]);




val holfoot_ap_data_interval_def = Define `
   holfoot_ap_data_interval e1 e2 data =
   holfoot_ap_data_array e1 (var_res_exp_binop $- (var_res_exp_add e2 1) e1) data`

val holfoot_ap_data_interval___CONST = store_thm ("holfoot_ap_data_interval___CONST",
``holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data =
  holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const ((SUC c2) - c1)) data``,
SIMP_TAC arith_ss [holfoot_ap_data_interval_def,
   var_res_exp_add_sub_REWRITES, 
    var_res_exp_binop___const_eval, arithmeticTheory.ADD1]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_interval = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_interval",
``!e1 e2 data vs.
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1 /\
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2 ==>
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs
       (holfoot_ap_data_interval e1 e2 data)``,

SIMP_TAC std_ss [holfoot_ap_data_interval_def] THEN 
REPEAT STRIP_TAC THEN
CONSEQ_REWRITE_TAC ([], [
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub], 
   []) THEN
ASM_REWRITE_TAC[]);

val VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_interval = 
store_thm ("VAR_RES_IS_STACK_IMPRECISE___holfoot_ap_data_interval",
`` !e1 e2 data.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>
     VAR_RES_IS_STACK_IMPRECISE (holfoot_ap_data_interval e1 e2 data)``,

REWRITE_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
        GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
             VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_interval]);


val var_res_prop_varlist_update___holfoot_ap_data_interval = 
store_thm ("var_res_prop_varlist_update___holfoot_ap_data_interval",
``!vcL e1 e2 data.
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
     IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>
     (var_res_prop_varlist_update vcL (holfoot_ap_data_interval e1 e2 data) =
      holfoot_ap_data_interval (var_res_exp_varlist_update vcL e1) (var_res_exp_varlist_update vcL e2) data)``,

SIMP_TAC std_ss [holfoot_ap_data_interval_def,   
   var_res_prop_varlist_update___holfoot_ap_data_array,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop,
   var_res_exp_varlist_update___var_res_exp_add_sub_EVAL,
   var_res_exp_varlist_update___var_res_exp_binop_EVAL]);


val holfoot_ap_data_interval___TRIVIAL_LENGTH = store_thm (
   "holfoot_ap_data_interval___TRIVIAL_LENGTH",
``IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
  ((holfoot_ap_data_interval e e data =
   holfoot_ap_data_array e (var_res_exp_const 1) data) /\
  (holfoot_ap_data_interval e (var_res_exp_add e n) data =
   holfoot_ap_data_array e (var_res_exp_const (SUC n)) data))``,

STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_interval_def,
   var_res_exp_add_sub_REWRITES] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
GEN_TAC THEN
Cases_on `e (FST x)` THEN1 (
   `!n. var_res_exp_sub e n (FST x) = NONE` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [var_res_exp_sub_def, var_res_exp_binop_const_REWRITE]
   ) THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array___not_def_start, IN_DEF,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub] THEN
   ASM_SIMP_TAC arith_ss [var_res_exp_const_EVAL, var_res_exp_binop_REWRITE,
      var_res_exp_add_def, var_res_exp_sub_def, var_res_exp_binop_const_REWRITE]
) THEN
CONSEQ_REWRITE_TAC ([], [holfoot_ap_data_array___EXP_REWRITE,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub], []) THEN
ASM_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC arith_ss [var_res_exp_binop_REWRITE, var_res_exp_add_def,
   var_res_exp_sub_def, var_res_exp_binop_const_REWRITE,
   var_res_exp_const_EVAL]);


val holfoot_ap_data_interval_0_start = store_thm (
"holfoot_ap_data_interval_0_start",
``!n data.
     holfoot_ap_data_interval (var_res_exp_const 0) n data =
     asl_false``,

SIMP_TAC std_ss [holfoot_ap_data_interval_def,
   holfoot_ap_data_array_0_start, EXTENSION, asl_bool_EVAL,
   var_res_prop_equal_unequal_EXPAND, IN_ABS,
   var_res_exp_binop_REWRITE, var_res_exp_const_EVAL,
   var_res_exp_add_def, var_res_exp_binop_const_REWRITE] THEN
REPEAT GEN_TAC THEN
Cases_on `n (FST x)` THEN ASM_SIMP_TAC std_ss []);

val holfoot_ap_data_interval_0 = store_thm (
"holfoot_ap_data_interval_0",
``!e data.
     holfoot_ap_data_interval (var_res_exp_const e) (var_res_exp_const 0) data =
     var_res_bool_proposition DISJOINT_FMAP_UNION 
         (EVERY (\tl. NULL (SND tl)) data /\ ALL_DISTINCT (MAP FST data) /\
          ~(e = 0))``,

SIMP_TAC std_ss [holfoot_ap_data_interval_def,
   var_res_exp_add_sub_REWRITES,
   var_res_exp_binop___const_eval] THEN
Cases_on `e` THENL [
   SIMP_TAC std_ss [holfoot_ap_data_array_0_start,
      var_res_prop_equal_unequal_REWRITES,
      var_res_bool_proposition_TF, asl_trivial_cond___asl_false],

   `1 - SUC n = 0` by DECIDE_TAC THEN
   ASM_SIMP_TAC arith_ss [holfoot_ap_data_array_0]
]);


val holfoot_ap_data_interval___end_before_begin = store_thm (
"holfoot_ap_data_interval___end_before_begin",
``!b e data. (e < b) ==>
     (holfoot_ap_data_interval (var_res_exp_const b) (var_res_exp_const e) data =
     var_res_bool_proposition DISJOINT_FMAP_UNION 
         (EVERY (\tl. NULL (SND tl)) data /\ ALL_DISTINCT (MAP FST data)))``,

SIMP_TAC arith_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN
`SUC e - b = 0` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_array_0]);


val holfoot_ap_data_interval___LENGTH_NOT_EQ_REWRITE = store_thm (
"holfoot_ap_data_interval___LENGTH_NOT_EQ_REWRITE",
``!ec nc t tvL data.
     LENGTH tvL <> ((nc + 1) - ec) ==>
     (holfoot_ap_data_interval (var_res_exp_const ec) (var_res_exp_const nc) ((t,tvL)::data) =
      asl_false)``,
SIMP_TAC std_ss [holfoot_ap_data_interval_def,
   var_res_exp_binop___const_eval,
   var_res_exp_add_sub_REWRITES,
   holfoot_ap_data_array___LENGTH_NOT_EQ_REWRITE]);


val holfoot_ap_data_interval___SPLIT = store_thm (
"holfoot_ap_data_interval___SPLIT",
``!e1 e2 e3 data. (e1 <= e2) /\ (e2 <= e3) ==>
 (holfoot_ap_data_interval (var_res_exp_const e1) (var_res_exp_const e3) data =
  asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
     (holfoot_ap_data_interval (var_res_exp_const e1) (var_res_exp_const e2)
           (MAP (\tl. (FST tl,TAKE (e2 + 1 - e1) (SND tl))) data))
     (holfoot_ap_data_interval (var_res_exp_const (SUC e2))
        (var_res_exp_const e3)
        (MAP (\tl. (FST tl,DROP (e2 +1 - e1) (SND tl))) data)))``,

REPEAT STRIP_TAC THEN
Cases_on `e1 = 0` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_interval_0_start, asl_false___asl_star_THM]
) THEN
SIMP_TAC std_ss [holfoot_ap_data_interval_def,
   var_res_exp_add_sub_REWRITES, var_res_exp_binop___const_eval] THEN
`e3 + 1 - SUC e2 = e3 - e2` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `l1 = (e2 + 1) - e1` THEN
Q.ABBREV_TAC `l2 = (e3 - e2)` THEN
`((e3 + 1) - e1 = l1 + l2) /\ (e1 + l1 = SUC e2)` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   IMP_RES_TAC LESS_EQUAL_ADD THEN
   Cases_on `e1` THEN FULL_SIMP_TAC std_ss [] THEN
   SIMP_TAC arith_ss []
) THEN
FULL_SIMP_TAC std_ss [holfoot_ap_data_array___SPLIT,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   var_res_exp_add_sub_REWRITES]);


val holfoot_ap_data_interval___DATA_PERM =
store_thm ("holfoot_ap_data_interval___DATA_PERM",
``!e n data1 data2.
(PERM data1 data2) ==>
(holfoot_ap_data_interval e n data1 =
 holfoot_ap_data_interval e n data2)``,
SIMP_TAC std_ss [holfoot_ap_data_interval_def,
  holfoot_ap_data_array___DATA_PERM]);



val VAR_RES_FRAME_SPLIT___data_interval___data_interval___SAME_EXP_LENGTH = store_thm (
"VAR_RES_FRAME_SPLIT___data_interval___data_interval___SAME_EXP_LENGTH",
``!e1 e2 data1 data2 sfb_restP wpb wpb' rpb sfb_context sfb_split sfb_imp sr.

(LIST_TO_SET (MAP FST data2) SUBSET LIST_TO_SET (MAP FST data1) /\
 ALL_DISTINCT (MAP FST data2) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2)

==>
 ((VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT (holfoot_ap_data_interval e1 e2 data1) sfb_split)
   (BAG_INSERT (holfoot_ap_data_interval e1 e2 data2) sfb_imp) sfb_restP) =

  (VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION sr (wpb,rpb) wpb'
   (BAG_INSERT (holfoot_ap_data_interval e1 e2 data1) sfb_context)
   sfb_split
   (BAG_INSERT (var_res_bool_proposition DISJOINT_FMAP_UNION 
          (EVERY (\x. MEM x data1) data2)) sfb_imp)
   sfb_restP))``,


SIMP_TAC std_ss [holfoot_ap_data_interval_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop]);



val holfoot_ap_data_interval___NOT_EMPTY_DATA_0 = store_thm ("holfoot_ap_data_interval___NOT_EMPTY_DATA_0",
``!b e t data.
holfoot_ap_data_interval b e ((t,[])::data) =
asl_trivial_cond (EVERY (\tl. NULL (SND tl)) data /\ ALL_DISTINCT (t::(MAP FST data)))
   (var_res_prop_binexpression DISJOINT_FMAP_UNION T $< e b)``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_interval_def,
   holfoot_ap_data_array___NOT_EMPTY_DATA_0,
   EXTENSION, asl_bool_EVAL, var_res_prop_equal_def,
   var_res_prop_binexpression_def, var_res_exp_const_EVAL,
   var_res_stack_proposition_def, IN_ABS, LET_THM] THEN

SIMP_TAC list_ss [var_res_exp_binop_REWRITE,
   var_res_exp_add_def,var_res_exp_binop_const_REWRITE] THEN
REPEAT STRIP_TAC THEN
Cases_on `e (FST x)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `b (FST x)` THEN ASM_SIMP_TAC std_ss [] THEN
DECIDE_TAC);




val holfoot_ap_data_array_interval___same_start___SPLIT___aa = store_thm (
   "holfoot_ap_data_array_interval___same_start___SPLIT___aa",
``!c1 c2 c3 c4 c5 lc data.
(c3 <= c2) ==>
((c1+c3 = c4) /\ ((c2 - c3) = c5) /\ (c3 = lc)) ==>

(holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c3)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_array (var_res_exp_const c4) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

REPEAT STRIP_TAC THEN
`c2 = (c3 + c5)` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [holfoot_ap_data_array___SPLIT,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
ASM_REWRITE_TAC [var_res_exp_add_sub_REWRITES]);


val holfoot_ap_data_array_interval___same_start___SPLIT___ai = store_thm (
   "holfoot_ap_data_array_interval___same_start___SPLIT___ai",
``!c1 c2 c3 c4 c5 lc data.
(c1 <= SUC c3) /\ (c3 < c1 + c2) ==>
((SUC c3 = c4) /\ (c2 − (SUC c3 − c1) = c5) /\ (SUC c3 − c1 = lc)) ==>

(holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c3)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_array (var_res_exp_const c4) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN 
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array_interval___same_start___SPLIT___aa) THEN
DECIDE_TAC);


val holfoot_ap_data_array_interval___same_start___SPLIT___ii = store_thm (
   "holfoot_ap_data_array_interval___same_start___SPLIT___ii",
``!c1 c2 c3 c4 c5 lc data.
(c1 <= SUC c3) /\ (c3 <= c2) ==>
((SUC c3 = c4) /\ (c2 = c5) /\ (SUC c3 - c1 = lc)) ==>

(holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c3)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_interval (var_res_exp_const c4) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN 
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array_interval___same_start___SPLIT___aa) THEN
DECIDE_TAC);


val holfoot_ap_data_array_interval___same_start___SPLIT___ia = store_thm (
   "holfoot_ap_data_array_interval___same_start___SPLIT___ia",
``!c1 c2 c3 c4 c5 lc data.
(c3 <= c2 - c1) ==>
((c1 + c3 = c4) /\ (c2 = c5) /\ (c3 = lc)) ==>

(holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c3)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_interval (var_res_exp_const c4) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN 
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array_interval___same_start___SPLIT___aa) THEN
DECIDE_TAC);


val holfoot_ap_data_array___SPLIT___intro_same_start = store_thm (
   "holfoot_ap_data_array___SPLIT___intro_same_start",
``!c1 c2 c3 c4 c5 lc data.
(c1 <= c3) /\ (c3 <= c1 + c2) ==>
((c3 - c1 = c4) /\ (c2 - (c3 - c1) = c5) /\ (c3 - c1 = lc)) ==>

(holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_array (var_res_exp_const c1) (var_res_exp_const c4)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_array (var_res_exp_const c3) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN 
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array_interval___same_start___SPLIT___aa) THEN
DECIDE_TAC);


val holfoot_ap_data_interval___SPLIT___intro_same_start = store_thm (
   "holfoot_ap_data_interval___SPLIT___intro_same_start",
``!c1 c2 c3 c4 c5 lc data.
(c1 <= c3) /\ (c3 <= c2 + 1) ==>
((PRE c3 = c4) /\ (c2 = c5) /\ (c3 - c1 = lc)) ==>

(holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data =
asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
   (holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c4)
       (MAP (\tl. (FST tl, FIRSTN lc (SND tl))) data))
   (holfoot_ap_data_interval (var_res_exp_const c3) (var_res_exp_const c5)
       (MAP (\tl. (FST tl, BUTFIRSTN lc (SND tl))) data)))``,

REPEAT STRIP_TAC THEN
Cases_on `c1` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_interval_0_start,
      asl_false___asl_star_THM]
) THEN
SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN 
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array_interval___same_start___SPLIT___aa) THEN
DECIDE_TAC);



val holfoot_ap_data_interval___var_res_prop_implies___length_eq = store_thm (
   "holfoot_ap_data_interval___var_res_prop_implies___length_eq",
``!wpb rpb sfb ec1 ec2 t tvL data.
(var_res_prop_implies DISJOINT_FMAP_UNION (wpb, rpb) 
    (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const ec1) (var_res_exp_const ec2) ((t,tvL)::data)) sfb)
    {|var_res_bool_proposition DISJOINT_FMAP_UNION (LENGTH tvL = SUC ec2 - ec1)|})``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_interval___CONST,
   var_res_prop_implies_REWRITE, BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
Tactical.REVERSE (Cases_on `LENGTH tvL = SUC ec2 - ec1`) THEN1 (
   ASM_SIMP_TAC std_ss [var_res_bool_proposition_TF,
       holfoot_ap_data_array___LENGTH_NOT_EQ_REWRITE] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___REWRITE,
      var_res_prop___PROP___asl_false,
      var_res_prop___COND_INSERT]
) THEN ASM_SIMP_TAC std_ss [var_res_bool_proposition_TF] THEN
METIS_TAC[var_res_prop___var_res_prop_stack_true, BAG_INSERT_commutes]);



val holfoot_ap_data_interval___implies_in_heap = store_thm ("holfoot_ap_data_interval___implies_in_heap",
``!c B sfb c1 c2 data.
((c1 <= c) /\ (c <= c2)) ==>
(holfoot_implies_in_heap B 
    (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data) sfb)
    (var_res_exp_const c))``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC holfoot_ap_data_array___implies_in_heap THEN
DECIDE_TAC);



val holfoot_ap_data_interval___implies_in_heap___COMPUTE = store_thm (
   "holfoot_ap_data_interval___implies_in_heap___COMPUTE",
``!c1 c2 data B c.
((c1 <= c) /\ (c <= c2)) ==>
(holfoot_implies_in_heap B 
    {|(holfoot_ap_data_interval (var_res_exp_const c1) (var_res_exp_const c2) data)|}
    (var_res_exp_const c))``,
SIMP_TAC std_ss [holfoot_ap_data_interval___implies_in_heap]);


val holfoot_ap_data_interval___EXP_REWRITE = store_thm ("holfoot_ap_data_interval___EXP_REWRITE",
``!e1 e2 e1' e2' data s.
     (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
      IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1') /\
     (e1 (FST s) = e1' (FST s)) /\ (e2 (FST s) = e2' (FST s))) ==>
     (s IN holfoot_ap_data_interval e1  e2  data =
      s IN holfoot_ap_data_interval e1' e2' data)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_interval_def] THEN
MATCH_MP_TAC holfoot_ap_data_array___EXP_REWRITE THEN
ASM_SIMP_TAC std_ss [var_res_exp_binop_REWRITE,
   var_res_exp_add_def, var_res_exp_binop_const_REWRITE]);


val holfoot_ap_data_interval___implies_inequal_0_start = store_thm ("holfoot_ap_data_interval___implies_inequal_0_start",
``!e1 e2 sfb data.
var_res_implies_unequal DISJOINT_FMAP_UNION 
    (BAG_INSERT (holfoot_ap_data_interval e1 e2 data) sfb)
    e1 (var_res_exp_const 0)``,

SIMP_TAC std_ss [var_res_implies_unequal_def,
   var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   var_res_prop_weak_unequal_def, var_res_prop_weak_binexpression_def,
   var_res_prop_binexpression_def, var_res_stack_proposition_def,
   IN_ABS, LET_THM, asl_star_def, var_res_exp_const_EVAL] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on `e1 (FST p)` THEN1 (
    FULL_SIMP_TAC std_ss [holfoot_ap_data_interval_def,
       holfoot_ap_data_array_def, var_res_exp_prop_def,
       var_res_exp_binop_REWRITE, var_res_exp_add_def,
       var_res_exp_binop_const_REWRITE, IN_ABS, LET_THM]
) THEN
`e1 (FST s) = SOME x` by ALL_TAC THEN1 (
   Tactical.REVERSE (`e1 (FST s) = e1 (FST p)` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT THEN
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE] THEN
   METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]
) THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
`p IN holfoot_ap_data_interval (var_res_exp_const 0) e2 data` by ALL_TAC THEN1 (
   MATCH_MP_TAC (EQ_IMP_RULE_CANON holfoot_ap_data_interval___EXP_REWRITE) THEN
   MAP_EVERY Q.EXISTS_TAC [`e1`, `e2`] THEN
   ASM_SIMP_TAC std_ss [var_res_exp_const_EVAL,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL]
) THEN
FULL_SIMP_TAC std_ss [holfoot_ap_data_interval_0_start, asl_bool_EVAL]);



val holfoot_ap_data_array___ADD_TAG = store_thm ("holfoot_ap_data_array___ADD_TAG",
``!t n e data.
~MEM t (MAP FST data) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n) ==>
(holfoot_ap_data_array e n data =
asl_exists tdata. holfoot_ap_data_array e n
      ((t,tdata)::data))``,

SIMP_TAC std_ss [EXTENSION, asl_exists_def, IN_ABS,
   GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `n (FST x)` THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array_def,
     var_res_exp_prop_def, IN_ABS, LET_THM]
) THEN
`!X. (x IN holfoot_ap_data_array e n X =
      x IN holfoot_ap_data_array e (var_res_exp_const x') X)` by ALL_TAC THEN1 (
   METIS_TAC[holfoot_ap_data_array___var_res_exp_const_INTRO]
) THEN
ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN
Q.PAT_ASSUM `~(MEM t X)` MP_TAC THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
MAP_EVERY Q.SPEC_TAC [(`data`, `data`), (`x`, `s`), (`e`, `e`), (`x'`, `n`)] THEN
Induct_on `n` THEN1 (
   ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_array_0,
      var_res_bool_proposition_REWRITE, IN_ABS, NULL_EQ_NIL]
) THEN
ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [holfoot_ap_data_array_SUC, asl_bool_EVAL,
   NULL_EQ_NIL, LIST_NOT_NIL___HD_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.HO_MATCH_ABBREV_TAC 
`       s IN asl_star f P1 P2 = 
?e' l'. s IN asl_star f (P1' e') (P2' l')` THEN

Tactical.REVERSE (
   `(!s. (s IN P1 = ?e'. s IN P1' e')) /\
    (!s. (s IN P2 = ?l'. s IN P2' l'))` by ALL_TAC) THEN1 (
   SIMP_TAC std_ss [asl_star_def, IN_ABS] THEN
   METIS_TAC[]
) THEN
UNABBREV_ALL_TAC THEN
BETA_TAC THEN
CONJ_TAC THENL [
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [holfoot_ap_points_to_def, IN_ABS, LET_THM,
         FEVERY_DEF, FDOM_FUPDATE, IN_INSERT,
         DISJ_IMP_THM, FORALL_AND_THM, 
         FAPPLY_FUPDATE_THM, LIST_TO_FMAP_THM,
         var_res_exp_const_def] THEN
   REPEAT STRIP_TAC THEN
   DEPTH_CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   REPEAT STRIP_TAC THEN
   `~(x = t)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FDOM_LIST_TO_FMAP, IN_LIST_TO_SET,
         MAP_MAP_o, combinTheory.o_DEF, ETA_THM] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [],


   GEN_TAC THEN
   Q.PAT_ASSUM `!e s data. X` MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, ETA_THM]
]);



val holfoot_ap_data_interval___ADD_TAG = store_thm ("holfoot_ap_data_interval___ADD_TAG",
``!t e1 e2 data.
~MEM t (MAP FST data) /\
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
(holfoot_ap_data_interval e1 e2 data =
asl_exists tdata. holfoot_ap_data_interval e1 e2 ((t,tdata)::data))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [holfoot_ap_data_interval_def] THEN
MATCH_MP_TAC (MP_CANON holfoot_ap_data_array___ADD_TAG) THEN
CONSEQ_REWRITE_TAC ([], [
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop], 
   []) THEN
ASM_SIMP_TAC std_ss []);





(***************************************
 * Some holfoot rewrites   
 **************************************)

val holfoot_disjoint_fmap_union_term = ``DISJOINT_FMAP_UNION :holfoot_heap bin_option_function``;
fun init_holfoot_sep_comb_RULE thmL =
let
   val thmL1 = flatten (map CONJUNCTS thmL);
   val thmL2 = map (ISPEC holfoot_disjoint_fmap_union_term) thmL1
   val thmL3 = map (REWRITE_RULE [IS_SEPARATION_COMBINATOR___FINITE_MAP]) thmL2
in
   LIST_CONJ thmL3
end;

val holfoot_var_res_map_REWRITES = save_thm ("holfoot_var_res_map_REWRITES",
init_holfoot_sep_comb_RULE [var_res_map___REWRITES]);


(***************************************
 * Export some informations
 **************************************)

val holfoot_ap_data_array___SIMP_THMS = 
  save_thm ("holfoot_ap_data_array___SIMP_THMS",
  LIST_CONJ [
        holfoot_ap_data_array_0,
        holfoot_ap_data_array_0_start,
        holfoot_ap_data_array___NOT_EMPTY_DATA_0,
        holfoot_ap_data_interval_0,
        holfoot_ap_data_interval_0_start,
        holfoot_ap_data_interval___NOT_EMPTY_DATA_0]);

val holfoot_ap_data_array___SIMP_THMS___PRECOND = 
  save_thm ("holfoot_ap_data_array___SIMP_THMS___PRECOND",
  LIST_CONJ [
        holfoot_ap_data_array___LENGTH_NOT_EQ_REWRITE,
        holfoot_ap_data_interval___LENGTH_NOT_EQ_REWRITE,
        holfoot_ap_data_interval___end_before_begin])


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___HOLFOOT_REWRITES =
  save_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___HOLFOOT_REWRITES",
  LIST_CONJ [
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star___holfoot,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___data_list_seg,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree_seg,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_tree,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_tree,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_bintree,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_interval,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_queue])


val holfoot___varlist_update_NO_VAR_THM =
  save_thm ("holfoot___varlist_update_NO_VAR_THM",
  LIST_CONJ [
     var_res_prop_varlist_update___holfoot_ap_data_list_seg_num,
     var_res_prop_varlist_update___holfoot_ap_data_list_seg,
     var_res_prop_varlist_update___holfoot_ap_data_list,
     var_res_prop_varlist_update___asl_star___holfoot,
     var_res_prop_varlist_update___holfoot_ap_points_to,
     var_res_prop_varlist_update___holfoot_ap_data_tree,
     var_res_prop_varlist_update___holfoot_ap_tree,
     var_res_prop_varlist_update___holfoot_ap_bintree,
     var_res_prop_varlist_update___holfoot_ap_array,
     var_res_prop_varlist_update___holfoot_ap_data_array,
     var_res_prop_varlist_update___holfoot_ap_data_interval,
     var_res_prop_varlist_update___holfoot_ap_data_queue])



(***************************************
 * Holfoot actions and programs
 **************************************)

val _ = type_abbrev("holfoot_program",
Type `:((holfoot_var list # num list), (*procedure args*)
        string (*locks*),
        string, (*procedure names*)
        holfoot_state (*states*)
   ) asl_program`);


(*==============
 = field lookup
 ===============*)

val holfoot_field_lookup_action_def = Define `
   (holfoot_field_lookup_action v e t) (s:holfoot_state) =
      let loc_opt = e (FST s) in
      if (~(var_res_sl___has_write_permission v (FST s)) \/ (IS_NONE loc_opt)) then NONE else
      let loc = (THE loc_opt) in (
      if (~(loc IN FDOM (SND s)) \/ (loc = 0)) then NONE else
      SOME {var_res_ext_state_var_update (v, (((SND s) ' loc) t)) s})`;


val ASL_IS_LOCAL_ACTION___holfoot_field_lookup_action = store_thm (
"ASL_IS_LOCAL_ACTION___holfoot_field_lookup_action",
``!e v t.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
ASL_IS_LOCAL_ACTION holfoot_separation_combinator (holfoot_field_lookup_action v e t)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   holfoot_field_lookup_action_def, LET_THM, COND_NONE_SOME_REWRITES,
   NOT_NONE_IS_SOME, holfoot_separation_combinator_def, IN_SING] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`?c. e (FST s1) = SOME c` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
IMP_RES_TAC VAR_RES_WRITE_PERM___SUBSTATE THEN
FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE,
   SOME___VAR_RES_STACK_COMBINE, DISJOINT_FMAP_UNION___REWRITE] THEN
`e (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC (FST s1) (FST s2)) = SOME c` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
   `vs SUBSET FDOM (FST s1)` by PROVE_TAC[IS_SOME_EXISTS] THEN
   Q.PAT_ASSUM `e (FST s1) = X` (fn thm => REWRITE_TAC [GSYM thm]) THEN
   Q.PAT_ASSUM `!st1 st2. X ==> (e st1 = e st2)` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [FMERGE_DEF, SUBSET_DEF, IN_UNION,
      VAR_RES_STACK_COMBINE___MERGE_FUNC_def, COND_REWRITES]
) THEN
ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION,
  var_res_ext_state_var_update_def, var_res_state_var_update_def] THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, IN_DISJOINT,
  FDOM_FUPDATE, IN_INSERT, GSYM fmap_EQ_THM, FMERGE_DEF,
  FAPPLY_FUPDATE_THM] THEN
`v IN FDOM (FST s1) /\ ~(v IN FDOM (FST s2))` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def] THEN
    Q.PAT_ASSUM `!x. x IN X1 /\ x IN X2 ==> Y x` (MP_TAC o Q.SPEC `v`) THEN
    ASM_SIMP_TAC std_ss [var_res_permission_THM2]) THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL [
   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [],
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [EXTENSION, IN_INSERT, IN_UNION],
   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss []
]);



val holfoot_prog_field_lookup_def = Define `
(holfoot_prog_field_lookup v e t):holfoot_program =
asl_prog_prim_command (asl_pc_shallow_command (\f. holfoot_field_lookup_action v e t))`;



val VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_lookup = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_lookup",
``!v c t e L vs e'.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e) /\
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e') /\
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_points_to e L)) /\
   (t IN FDOM L) /\ (L ' t = e') ==>

   (VAR_RES_PROGRAM_IS_ABSTRACTION DISJOINT_FMAP_UNION
    (holfoot_prog_field_lookup v e t)
    (var_res_prog_cond_best_local_action
      (var_res_prop DISJOINT_FMAP_UNION ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v) (var_res_exp_const c); holfoot_ap_points_to e L|})
      (var_res_prop DISJOINT_FMAP_UNION ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v) (var_res_exp_var_update (v, c) e');
          (var_res_prop_var_update (v, c) (holfoot_ap_points_to e L))|})))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` by
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION_def, holfoot_prog_field_lookup_def,
   ASL_PROGRAM_SEM___prim_command, EVAL_asl_prim_command_THM,
   ASL_ATOMIC_ACTION_SEM_def, GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_field_lookup_action,
   var_res_prog_cond_best_local_action_REWRITE,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
SIMP_TAC std_ss [var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, COND_RAND, COND_RATOR] THEN
MATCH_MP_TAC (prove (``((~c) /\ (~c ==> x2)) ==> if c then x1 else x2``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___COND___REWRITE,
      FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      DISJ_IMP_THM, FORALL_AND_THM, IS_SEPARATION_COMBINATOR___FINITE_MAP,
      BAG_ALL_DISTINCT_THM, BAG_UNION_INSERT, BAG_UNION_EMPTY,
      BAG_IN_BAG_OF_SET, IN_DELETE, BAG_ALL_DISTINCT_BAG_OF_SET] THEN

   `(SET_OF_BAG (BAG_INSERT v (BAG_OF_SET (vs DELETE v)))) =  v INSERT vs` by ALL_TAC THEN1 (
      ONCE_REWRITE_TAC[EXTENSION] THEN
      SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_INSERT, IN_SET_OF_BAG,
         BAG_IN_BAG_INSERT, BAG_IN_BAG_OF_SET, IN_DELETE]
   ) THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
      ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
         IN_INSERT],

      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `vs` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT],

      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
      ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
         IN_INSERT] THEN
      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_var_update THEN
      FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
         SUBSET_DEF, IN_INSERT],


      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update THEN
      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `vs` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT]
   ]
) THEN
SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN REPEAT STRIP_TAC THEN
Cases_on `holfoot_field_lookup_action v e t s = NONE` THEN1 (
   FULL_SIMP_TAC std_ss [fasl_order_THM,
      var_res_best_local_action_def, NONE___quant_best_local_action, IN_ABS,
      var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      var_res_bigstar_REWRITE, IN_ABS] THEN
   ASM_SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND,
      var_res_prop_stack_true_REWRITE, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
      IN_SING, DISJOINT_FMAP_UNION___REWRITE, FUNION_FEMPTY_1, LET_THM,
      FUNION_FEMPTY_2, DISJOINT_EMPTY, FDOM_FEMPTY,
      var_res_exp_const_def, var_res_exp_var_def, IN_DELETE,
      var_res_sl___has_write_permission_def, BAG_IN_BAG_OF_SET,
      var_res_sl___has_read_permission_def] THEN
   SIMP_TAC (std_ss++CONJ_ss) [] THEN
   CCONTR_TAC THEN
   Q.PAT_ASSUM `holfoot_field_lookup_action v e t s = NONE` MP_TAC THEN
   FULL_SIMP_TAC std_ss [holfoot_field_lookup_action_def,
      LET_THM, SOME___holfoot_separation_combinator,
      SOME___VAR_RES_STACK_COMBINE,
      holfoot_ap_points_to_def, IN_ABS, COND_NONE_SOME_REWRITES,
      var_res_sl___has_write_permission_def, FMERGE_DEF, FUNION_DEF,
      IN_UNION] THEN
   Tactical.REVERSE (`~(v IN FDOM (FST s0)) /\
      (e (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC (FST s0) (FST x)) = e (FST x))` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [NOT_NONE_IS_SOME, IN_SING]
   ) THEN
   CONJ_TAC THENL [
      Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE (FST s0) (FST x)` MP_TAC THEN
      SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, GSYM LEFT_EXISTS_IMP_THM] THEN
      Q.EXISTS_TAC `v` THEN ASM_SIMP_TAC std_ss [var_res_permission_THM2],


      MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT THEN
      Tactical.REVERSE (`VAR_RES_STACK_COMBINE (SOME (FST s0)) (SOME (FST x)) = SOME (FST s)` by ALL_TAC) THEN1 (
         ASM_SIMP_TAC std_ss [] THEN
         METIS_TAC [VAR_RES_STACK_IS_SUBSTATE_INTRO]
      ) THEN
      ASM_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE]
   ]
) THEN
FULL_SIMP_TAC std_ss [holfoot_field_lookup_action_def, LET_THM,
   COND_NONE_SOME_REWRITES, var_res_sl___has_write_permission_def] THEN
`?ev. e (FST s) = SOME ev` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, NOT_NONE_IS_SOME] THEN
FULL_SIMP_TAC std_ss [fasl_order_THM2, var_res_best_local_action_def,
   SUBSET_DEF, IN_SING, SOME___quant_best_local_action, IN_ABS,
   asl_star_def, IN_SING] THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
REPEAT STRIP_TAC THEN

Q.EXISTS_TAC `var_res_ext_state_var_update (v, (SND s ' ev t)) x'` THEN
Q.PAT_ASSUM `x' IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP_INSERT, IN_ABS,
   var_res_prop___COND_INSERT] THEN
SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_IN_BAG_INSERT,
   NOT_IN_EMPTY_BAG, IN_ABS, BAG_IN_BAG_OF_SET,
   var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___PROPERTIES] THEN
SIMP_TAC std_ss [var_res_prop_stack_true_def, var_res_bool_proposition_def,
   var_res_prop_equal_def, var_res_stack_proposition_def, asl_emp_DISJOINT_FMAP_UNION,
   IN_ABS, IN_SING, DISJOINT_FMAP_UNION___REWRITE, FUNION_FEMPTY_2, FUNION_FEMPTY_1,
   var_res_prop_binexpression_def, var_res_sl___has_write_permission_def,
   var_res_sl___has_read_permission_def, var_res_exp_const_def,
   var_res_exp_var_def, LET_THM, FDOM_FEMPTY,
   var_res_ext_state_var_update_def, var_res_state_var_update_def,
   FDOM_FUPDATE, IN_INSERT, DISJOINT_EMPTY,
   FAPPLY_FUPDATE_THM, var_res_exp_var_update_def,
   var_res_prop_var_update_def, FUPDATE_EQ] THEN
SIMP_TAC (std_ss++CONJ_ss) [] THEN
STRIP_TAC THEN
`(FST x' |+ (v,c,var_res_write_permission)) = FST x'` by ALL_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      GSYM fmap_EQ_THM, FDOM_FUPDATE, EXTENSION, IN_INSERT,
      FAPPLY_FUPDATE_THM, COND_RAND, COND_RATOR] THEN
   Cases_on `FST x' ' v` THEN
   FULL_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [] THEN

Q.PAT_ASSUM `x' IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM,
   FEVERY_DEF] THEN
STRIP_TAC THEN
`e (FST x') = SOME ev` by ALL_TAC THEN1 (
   Tactical.REVERSE (`e (FST x') = e (FST s)` by ALL_TAC) THEN1 ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT THEN
   Cases_on `x'` THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
      holfoot_ap_points_to_def, IN_ABS, LET_THM] THEN
   PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]
) THEN
`SND x' ' ev = SND s ' ev` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `holfoot_separation_combinator (SOME s0') X = Y` MP_TAC THEN
   ONCE_REWRITE_TAC[holfoot_separation_combinator___COMM] THEN
   ASM_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
      FUNION_DEF, IN_SING]
) THEN
FULL_SIMP_TAC std_ss [] THEN
`e' (FST x') = SOME ((SND s) ' ev t)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x. x IN FDOM L ==> Y` (MP_TAC o Q.SPEC `t`) THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [
     IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
     GSYM LEFT_FORALL_IMP_THM]
) THEN
ASM_SIMP_TAC std_ss [] THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++CONJ_ss) [
      VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def, FDOM_FUPDATE, IN_INSERT,
      FAPPLY_FUPDATE_THM, COND_RAND, COND_RATOR]
) THEN
ONCE_REWRITE_TAC [holfoot_separation_combinator___COMM] THEN
Q.PAT_ASSUM `X = SOME s` MP_TAC THEN
ASM_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
   SOME___VAR_RES_STACK_COMBINE, GSYM fmap_EQ_THM] THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   FMERGE_DEF, FDOM_FUPDATE, EXTENSION, IN_UNION, IN_INSERT,
   IN_DISJOINT, IN_SING, FAPPLY_FUPDATE_THM,
   VAR_RES_STACK_IS_SEPARATE_def] THEN
STRIP_TAC THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN GEN_TAC THEN
Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [] THEN
Tactical.REVERSE (`~(v IN FDOM (FST s0))` by ALL_TAC) THEN ASM_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x. x IN FDOM (FST s0) /\ x IN Y ==> Z` (MP_TAC o Q.SPEC `v`) THEN
ASM_SIMP_TAC std_ss [var_res_permission_THM2]);




val HOLFOOT_COND_INFERENCE___prog_field_lookup =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_lookup",
``
 !wpb rpb v e L t c sfb progL Q.

((BAG_IN v wpb) /\ (t IN FDOM L) /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) (L ' t))
==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                     (var_res_exp_varlist_update [(v, c)] (L ' t)))
     (BAG_IMAGE (var_res_prop_varlist_update [(v, c)] )
       (BAG_INSERT (holfoot_ap_points_to e L)
          sfb))))
    (asl_prog_block progL) Q) ==>


(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                      (var_res_exp_const c))
      (BAG_INSERT (holfoot_ap_points_to e L)
       sfb)))

   (asl_prog_block ((holfoot_prog_field_lookup v e t)::progL))

   Q))
``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   var_res_prop_varlist_update_SING,
   var_res_exp_varlist_update_SING] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `(FST Q) /\
   var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v) (var_res_exp_const c))
      (BAG_INSERT (holfoot_ap_points_to e L) sfb))`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
MP_TAC (Q.SPECL [`v`, `c`, `t`, `e`, `L`, `SET_OF_BAG (BAG_UNION wpb rpb)`]
   VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_lookup) THEN
ASM_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT] THEN
DISCH_TAC THEN POP_ASSUM (fn thm => EXISTS_TAC (rand (concl thm)) THEN REWRITE_TAC[thm]) THEN
SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___FINITE_MAP, GSYM VAR_RES_COND_INFERENCE___prog_block] THEN
HO_MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_OF_SET, IN_DELETE,
   BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, VAR_RES_FRAME_SPLIT_NORMALISE] THEN
ONCE_REWRITE_TAC [VAR_RES_FRAME_SPLIT___FRAME] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___equal_const___context_SING) THEN
`FINITE_BAG sfb` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, FINITE_BAG_THM] THEN
ASM_SIMP_TAC std_ss [BAG_IMAGE_EMPTY, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
   BAG_IMAGE_FINITE_INSERT, BAG_IMAGE_EMPTY, FINITE_BAG_THM] THEN
ONCE_REWRITE_TAC [VAR_RES_FRAME_SPLIT___FRAME] THEN

MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY,
      BAG_IN_FINITE_BAG_IMAGE, GSYM LEFT_FORALL_IMP_THM, BAG_IN_BAG_INSERT,
      DISJ_IMP_THM, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, IN_INSERT, IN_UNION, IN_DIFF,
      BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, BAG_IN_BAG_UNION,
      BAG_IN_BAG_DIFF_ALL_DISTINCT]
) THEN
FULL_SIMP_TAC std_ss [BAG_IMAGE_FINITE_INSERT, BAG_UNION_INSERT, BAG_UNION_EMPTY]);




val HOLFOOT_COND_INFERENCE___prog_field_lookup___exp_rewrite =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_lookup___exp_rewrite",
``!wpb rpb v e e' t sfb progL Q.
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e') ==>

 ((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e e') sfb))
   (asl_prog_block ((holfoot_prog_field_lookup v e t)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e e') sfb))
   (asl_prog_block ((holfoot_prog_field_lookup v e' t)::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_field_lookup_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_field_lookup_action] THEN

Tactical.REVERSE (`e (FST s) = e' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_field_lookup_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);



val var_res_prop___asl_star___holfoot =
save_thm ("var_res_prop___asl_star___holfoot",
let
  val thm0 = ISPEC ``(VAR_RES_COMBINATOR DISJOINT_FMAP_UNION):holfoot_state bin_option_function``
        var_res_prop___asl_star
  val thm1 = SIMP_RULE std_ss [GSYM holfoot_separation_combinator_def,
     GET_VAR_RES_COMBINATOR___holfoot_separation_combinator,
     IS_VAR_RES_COMBINATOR___holfoot_separation_combinator] thm0
  val thm2 = SIMP_RULE std_ss [holfoot_separation_combinator_def] thm1
in
  thm2
end);




val HOLFOOT_COND_INFERENCE___prog_field_lookup___array =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_lookup___array",
``!tdata v e ds dl data t c wpb rpb  sfb progL Q.

((ds <= e) /\ (e < ds + dl)) ==>
(BAG_IN v wpb) /\ (MEM (t, tdata) data)  ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                     (var_res_exp_const (EL (e - ds) tdata)))
     (BAG_IMAGE (var_res_prop_varlist_update [(v, c)] )
       (BAG_INSERT (holfoot_ap_data_array (var_res_exp_const ds) (var_res_exp_const dl) data)
          sfb))))
    (asl_prog_block progL) Q) ==>


(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                      (var_res_exp_const c))
      (BAG_INSERT (holfoot_ap_data_array (var_res_exp_const ds) (var_res_exp_const dl) data)
       sfb)))

   (asl_prog_block ((holfoot_prog_field_lookup v (var_res_exp_const e) t)::progL))

   Q))
``,

REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN

Tactical.REVERSE (Cases_on `EVERY (\tl. LENGTH (SND tl) = dl)
   data /\ ALL_DISTINCT (MAP FST data)`) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array___CONST, asl_trivial_cond_TF] THEN
   SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
     var_res_prop___REWRITE, var_res_prop___PROP_INSERT,
     var_res_prop___COND_INSERT, asl_bool_EVAL,
     VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
     HOARE_TRIPLE_def]
) THEN

`?dl1. ds + dl1 = e` by METIS_TAC[LESS_EQUAL_ADD] THEN
`dl1 + 1 <= dl` by DECIDE_TAC  THEN
`?dl2. dl = dl1 + 1 + dl2` by METIS_TAC[LESS_EQUAL_ADD] THEN
Tactical.REVERSE (Cases_on `FINITE_BAG sfb`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE, var_res_prop___COND___REWRITE,
      FINITE_BAG_THM]
) THEN

ASM_SIMP_TAC std_ss [BAG_IMAGE_FINITE_INSERT,
   FINITE_BAG_THM, var_res_prop_varlist_update___asl_star___holfoot,
   var_res_prop_varlist_update___holfoot_ap_data_array,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   var_res_exp_varlist_update___const_EVAL] THEN
ASM_SIMP_TAC arith_ss [holfoot_ap_data_array___SPLIT,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   MAP_MAP_o, combinTheory.o_DEF,
   var_res_exp_add_sub_REWRITES] THEN

Q.MATCH_ABBREV_TAC `XXX ==> VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
  (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT
        (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
           (var_res_exp_const c))
        (BAG_INSERT (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
              (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
                 array_pred_1 array_pred_2) array_pred_3) sfb))) prog Q` THEN
Q.UNABBREV_TAC `XXX` THEN


`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) array_pred_1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) array_pred_2 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) array_pred_3` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array], []) THEN
   SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN
ASM_SIMP_TAC std_ss [prove (``(BAG_INSERT x (BAG_INSERT (asl_star f P1 P2) sfb) =
                          (BAG_INSERT (asl_star f P1 P2) (BAG_INSERT x sfb)))``,
                 METIS_TAC[BAG_INSERT_commutes]),
    var_res_prop___asl_star___holfoot,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star] THEN
Q.PAT_ASSUM `Abbrev (array_pred_2 = XXX)` MP_TAC THEN
FULL_SIMP_TAC list_ss [holfoot_ap_data_array_1,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, ETA_THM,
   EVERY_MEM, asl_trivial_cond_TF] THEN
STRIP_TAC THEN


`!x sfb. (BAG_INSERT array_pred_1 (BAG_INSERT array_pred_2
    (BAG_INSERT array_pred_3 (BAG_INSERT x sfb))) =
  BAG_INSERT x (BAG_INSERT array_pred_2
    (BAG_INSERT array_pred_1 (BAG_INSERT array_pred_3 sfb))))` by
   METIS_TAC[BAG_INSERT_commutes] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
Q.UNABBREV_TAC `array_pred_2` THEN
Q.UNABBREV_TAC `prog` THEN
MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_field_lookup) THEN

Q.ABBREV_TAC `L' = LIST_TO_FMAP (MAP (\tl.
      (FST tl, (var_res_exp_const
      (HD (DROP dl1 (TAKE (dl1 + 1) (SND tl))))):holfoot_a_expression)) data)` THEN

Tactical.REVERSE (
   `(t IN FDOM L') /\ (L' ' t = var_res_exp_const (EL (e - ds) tdata))` by ALL_TAC) THEN1 (
  UNABBREV_ALL_TAC THEN
  ASM_SIMP_TAC std_ss [var_res_exp_varlist_update___const_EVAL,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
     BAG_IMAGE_FINITE_INSERT, FINITE_BAG_THM,
     var_res_prop_varlist_update___holfoot_ap_data_array,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
     var_res_prop_varlist_update___holfoot_ap_points_to, o_f_LIST_TO_FMAP,
     MAP_MAP_o, combinTheory.o_DEF]   
) THEN

Q.UNABBREV_TAC `L'` THEN
CONJ_TAC THEN1 (
  SIMP_TAC std_ss [FDOM_LIST_TO_FMAP, IN_LIST_TO_SET, MEM_MAP,
    GSYM RIGHT_EXISTS_AND_THM] THEN
  Q.EXISTS_TAC `(t, tdata)` THEN 
  ASM_SIMP_TAC std_ss []
) THEN
MATCH_MP_TAC LIST_TO_FMAP___ALL_DISTINCT THEN

ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, MEM_MAP,
   var_res_exp_eq_THM, ETA_THM] THEN
Q.EXISTS_TAC `(t, tdata)` THEN
`e - ds = dl1` by DECIDE_TAC THEN
`LENGTH tdata = dl` by ALL_TAC THEN1 (
   RES_TAC THEN
   FULL_SIMP_TAC arith_ss []
) THEN
ASM_SIMP_TAC list_ss [HD_BUTFIRSTN, EL_FIRSTN]);



val HOLFOOT_COND_INFERENCE___prog_field_lookup___interval =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_lookup___interval",
``!tdata v b e m data t c wpb rpb  sfb progL Q.
((b <= m) /\ (m <= e)) ==>
(BAG_IN v wpb) /\ (MEM (t, tdata) data)  ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
     (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                     (var_res_exp_const (EL (m - b) tdata)))
     (BAG_IMAGE (var_res_prop_varlist_update [(v, c)] )
       (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const b) (var_res_exp_const e) data)
          sfb))))
    (asl_prog_block progL) Q) ==>


(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
                                      (var_res_exp_const c))
      (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const b) (var_res_exp_const e) data)
       sfb)))

   (asl_prog_block ((holfoot_prog_field_lookup v (var_res_exp_const m) t)::progL))

   Q))
``,

SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_field_lookup___array) THEN
Q.EXISTS_TAC `tdata` THEN
ASM_SIMP_TAC arith_ss []);




(*==============
 = field assign
 ===============*)

val holfoot_field_assign_action_def = Define `
   holfoot_field_assign_action e1 t e2 (s:holfoot_state) =
      let e1_opt = e1 (FST s) in
      let e2_opt = e2 (FST s) in
      if ((IS_NONE e1_opt) \/ (IS_NONE e2_opt)) then NONE else
      let e1_v = (THE e1_opt) in
      let e2_v = (THE e2_opt) in (
      if (~(e1_v IN FDOM (SND s)) \/ (e1_v = 0)) then NONE else
      (SOME {(FST s, (SND s) |+ (e1_v, ((t =+ e2_v) ((SND s) ' e1_v))))}))`




val ASL_IS_LOCAL_ACTION___holfoot_field_assign_action = store_thm (
"ASL_IS_LOCAL_ACTION___holfoot_field_assign_action",
``!e1 e2 t.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>
ASL_IS_LOCAL_ACTION holfoot_separation_combinator (holfoot_field_assign_action e1 t e2)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   holfoot_field_assign_action_def, LET_THM, COND_NONE_SOME_REWRITES,
   NOT_NONE_IS_SOME, holfoot_separation_combinator_def, IN_SING] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`(e1 (FST s3) = e1 (FST s1)) /\ (e2 (FST s3) = e2 (FST s1))` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT], [], []) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE] THEN
   PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]
) THEN
`?ev1 ev2. (e1 (FST s1) = SOME ev1) /\ (e2 (FST s1) = SOME ev2)` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE, SOME___VAR_RES_STACK_COMBINE,
   DISJOINT_FMAP_UNION___REWRITE, IN_DISJOINT, FUNION_DEF, FDOM_FUPDATE, IN_UNION,
   IN_INSERT] THEN
CONJ_TAC THEN1 METIS_TAC[] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF, FDOM_FUPDATE,
   FAPPLY_FUPDATE_THM, IN_INSERT, IN_UNION, combinTheory.UPDATE_def] THEN
GEN_TAC THEN
Cases_on `x = ev1` THEN ASM_SIMP_TAC std_ss []);





val holfoot_prog_field_assign_def = Define `
(holfoot_prog_field_assign e1 t e2):holfoot_program =
asl_prog_prim_command (asl_pc_shallow_command (\f. holfoot_field_assign_action e1 t e2))`;



val VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_assign = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_assign",
``!t e1 e2 L vs.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2) /\
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_points_to e1 L)) /\
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (holfoot_ap_points_to e1 (L |+ (t, e2)))) ==>
   (VAR_RES_PROGRAM_IS_ABSTRACTION DISJOINT_FMAP_UNION
    (holfoot_prog_field_assign e1 t e2)
    (var_res_prog_cond_best_local_action
      (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_OF_SET vs)
        {|holfoot_ap_points_to e1 L|})
      (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_OF_SET vs)
        {|holfoot_ap_points_to e1 (L|+(t,e2))|})))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)` by
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION_def, holfoot_prog_field_assign_def,
   ASL_PROGRAM_SEM___prim_command, EVAL_asl_prim_command_THM,
   ASL_ATOMIC_ACTION_SEM_def, GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_field_assign_action,
   var_res_prog_cond_best_local_action_REWRITE,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
SIMP_TAC std_ss [var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, COND_RAND, COND_RATOR] THEN
MATCH_MP_TAC (prove (``((~c) /\ (~c ==> x2)) ==> if c then x1 else x2``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___COND___REWRITE,
      FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_UNION_EMPTY,
      BAG_ALL_DISTINCT_BAG_OF_SET, SET_BAG_I]
) THEN
SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN REPEAT STRIP_TAC THEN
Cases_on `holfoot_field_assign_action e1 t e2 s = NONE` THEN1 (
   FULL_SIMP_TAC std_ss [fasl_order_THM,
      var_res_best_local_action_def, NONE___quant_best_local_action, IN_ABS,
      var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR, var_res_bigstar_REWRITE_EXT,
      asl_star___PROPERTIES, IN_ABS] THEN
   ASM_SIMP_TAC std_ss [var_res_prop_stack_true_def, var_res_bool_proposition_def,
      var_res_stack_proposition_def, IN_ABS, asl_emp_DISJOINT_FMAP_UNION,
      IN_SING, DISJOINT_FMAP_UNION___REWRITE, FDOM_FEMPTY, DISJOINT_EMPTY,
      FUNION_FEMPTY_2, BAG_IN_BAG_OF_SET, var_res_sl___has_read_permission_def,
      GSYM SUBSET_DEF, holfoot_ap_points_to_def, LET_THM] THEN
   CCONTR_TAC THEN
   Q.PAT_ASSUM `holfoot_field_assign_action e1 t e2 s = NONE` MP_TAC THEN
   FULL_SIMP_TAC std_ss [holfoot_field_assign_action_def,
      LET_THM, SOME___holfoot_separation_combinator,
      IN_ABS, COND_NONE_SOME_REWRITES] THEN
   Tactical.REVERSE (`(e1 (FST s) = e1 (FST x)) /\ (IS_SOME (e2 (FST s)))` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [NOT_NONE_IS_SOME, FUNION_DEF, IN_UNION, IN_SING]
   ) THEN
   CONJ_TAC THENL [
      MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT THEN
      ASM_SIMP_TAC std_ss [] THEN
      PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO],


      FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
         SUBSET_DEF, FMERGE_DEF, IN_UNION]
   ]
) THEN
FULL_SIMP_TAC std_ss [holfoot_field_assign_action_def, LET_THM,
   COND_NONE_SOME_REWRITES, NOT_NONE_IS_SOME] THEN
`?ev1. e1 (FST s) = SOME ev1` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, NOT_NONE_IS_SOME] THEN
`?ev2. e2 (FST s) = SOME ev2` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, NOT_NONE_IS_SOME] THEN
FULL_SIMP_TAC std_ss [fasl_order_THM2, var_res_best_local_action_def,
   SUBSET_DEF, IN_SING, SOME___quant_best_local_action, IN_ABS,
   asl_star_def, IN_SING] THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
REPEAT STRIP_TAC THEN

Q.EXISTS_TAC `(FST x',SND x' |+ (ev1,(t =+ ev2) (SND s ' ev1)))` THEN

Q.PAT_ASSUM `x' IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL,
   var_res_prop___PROP_INSERT] THEN
ASM_SIMP_TAC std_ss [IN_ABS, var_res_prop___PROP___REWRITE,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR, IS_SEPARATION_COMBINATOR___FINITE_MAP,
   NOT_IN_EMPTY_BAG, BAG_IN_BAG_OF_SET, var_res_bigstar_REWRITE,
   asl_star___PROPERTIES, var_res_sl___has_read_permission_def,
   GSYM SUBSET_DEF, var_res_prop_stack_true_def,
   var_res_bool_proposition_def, var_res_stack_proposition_def,
   LET_THM, DISJOINT_FMAP_UNION___REWRITE, asl_emp_DISJOINT_FMAP_UNION,
   IN_SING, FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN
SIMP_TAC std_ss [holfoot_ap_points_to_def, IN_ABS, LET_THM] THEN
STRIP_TAC THEN
`e1 (FST x') = SOME ev1` by ALL_TAC THEN1 (
   Tactical.REVERSE (`e1 (FST x') = e1 (FST s)` by ALL_TAC) THEN1 ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator] THEN
   PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]
) THEN
`e2 (FST x') = SOME ev2` by ALL_TAC THEN1 (
   Tactical.REVERSE (`e2 (FST x') = e2 (FST s)` by ALL_TAC) THEN1 ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator] THEN
   CONJ_TAC THEN1 PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE, SUBSET_DEF]
) THEN
FULL_SIMP_TAC std_ss [FDOM_FUPDATE, INSERT_INSERT, FEVERY_DEF, IN_INSERT] THEN
CONJ_TAC THENL [
   ONCE_REWRITE_TAC [holfoot_separation_combinator___COMM] THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
      FDOM_FUPDATE, IN_DISJOINT, INSERT_INSERT, IN_SING] THEN
   SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      EXTENSION, FUNION_DEF,
      FDOM_FUPDATE, FAPPLY_FUPDATE_THM, INSERT_INSERT, IN_UNION, IN_INSERT,
      NOT_IN_EMPTY, combinTheory.UPDATE_def] THEN
   GEN_TAC THEN
   Cases_on `x = ev1` THEN ASM_SIMP_TAC std_ss [],


   SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, combinTheory.UPDATE_def] THEN
   GEN_TAC THEN
   Cases_on `x = t` THEN ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
      FUNION_DEF, IN_DISJOINT, IN_SING]
]);




val HOLFOOT_COND_INFERENCE___prog_field_assign =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_assign",
``!wpb rpb e1 L e2 t sfb progL Q.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (holfoot_ap_points_to e1 (L |+ (t,e2)))) ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_points_to e1 (L |+ (t, e2))) sfb))
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_points_to e1 L) sfb))
   (asl_prog_block ((holfoot_prog_field_assign e1 t e2)::progL)) Q))``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `(FST Q) /\
   var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb)
         (BAG_INSERT (holfoot_ap_points_to e1 L) sfb)`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
MP_TAC (Q.SPECL [`t`, `e1`, `e2`, `L`, `SET_OF_BAG (BAG_UNION wpb rpb)`]
   VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_field_assign) THEN
ASM_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT] THEN
DISCH_TAC THEN POP_ASSUM (fn thm => EXISTS_TAC (rand (concl thm)) THEN REWRITE_TAC[thm]) THEN
SIMP_TAC std_ss [GSYM VAR_RES_COND_INFERENCE___prog_block,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
HO_MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET, SET_BAG_I, SUBSET_REFL,
   VAR_RES_FRAME_SPLIT_NORMALISE] THEN
ONCE_REWRITE_TAC [VAR_RES_FRAME_SPLIT___FRAME] THEN

MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY,
      BAG_OF_EMPTY, DIFF_EMPTY,
      BAG_IN_FINITE_BAG_IMAGE, GSYM LEFT_FORALL_IMP_THM, BAG_IN_BAG_INSERT,
      DISJ_IMP_THM, FORALL_AND_THM, SET_OF_BAG_UNION,BAG_DIFF_EMPTY]
) THEN
FULL_SIMP_TAC std_ss [BAG_IMAGE_FINITE_INSERT, BAG_UNION_INSERT, BAG_UNION_EMPTY]);




val HOLFOOT_COND_INFERENCE___prog_field_assign___array =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_assign___array",
``!tdata e ds dl c data wpb rpb t sfb progL Q.
ds <= e /\ e < ds + dl ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_array (var_res_exp_const ds) 
            (var_res_exp_const dl) ((t, REPLACE_ELEMENT c (e - ds) tdata)::data)) sfb))
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_array (var_res_exp_const ds) (var_res_exp_const dl) ((t, tdata)::data)) sfb))
   (asl_prog_block ((holfoot_prog_field_assign (var_res_exp_const e) t (var_res_exp_const c))::progL)) Q))``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (Cases_on `(LENGTH tdata = dl) /\ EVERY (\tl. LENGTH (SND tl) = dl)
   data /\ ALL_DISTINCT (t::(MAP FST data))`) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_ap_data_array___CONST, asl_trivial_cond_TF,
      EVERY_DEF, MAP, GSYM CONJ_ASSOC] THEN
   SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
     var_res_prop___REWRITE, var_res_prop___PROP_INSERT,
     var_res_prop___COND_INSERT, asl_bool_EVAL,
     VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
     HOARE_TRIPLE_def]
) THEN

`?dl1. ds + dl1 = e` by METIS_TAC[LESS_EQUAL_ADD] THEN
`dl1 + 1 <= dl` by DECIDE_TAC  THEN
`?dl2. dl = dl1 + 1 + dl2` by METIS_TAC[LESS_EQUAL_ADD] THEN
`e - ds = dl1` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_data_array___SPLIT,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   MAP_MAP_o, combinTheory.o_DEF, MAP,
   var_res_exp_add_sub_REWRITES] THEN
FULL_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC arith_ss [FIRSTN_FIRSTN, REPLACE_ELEMENT_SEM,
   BUTFIRSTN_REPLACE_ELEMENT, FIRSTN_REPLACE_ELEMENT] THEN
FULL_SIMP_TAC list_ss [holfoot_ap_data_array_1,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, ETA_THM, EVERY_MEM,
   asl_trivial_cond_TF, HD_BUTFIRSTN, EL_FIRSTN,
   REPLACE_ELEMENT_SEM, LIST_TO_FMAP_THM] THEN

Q.MATCH_ABBREV_TAC `XXX ==> VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
  (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
           (asl_star (VAR_RES_COMBINATOR DISJOINT_FMAP_UNION)
                array_pred_1 (holfoot_ap_points_to (var_res_exp_const e)
                     (L' |+ (t, var_res_exp_const c')))) array_pred_3) sfb)) prog Q` THEN
Q.UNABBREV_TAC `XXX` THEN


`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) array_pred_1 /\
 !cc. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) 
   (holfoot_ap_points_to (var_res_exp_const e) (L' |+ (t, var_res_exp_const cc))) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) array_pred_3` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_data_array,
        VAR_RES_IS_STACK_IMPRECISE___USED_VARS___points_to, FEVERY_LIST_TO_FMAP, FEVERY_STRENGTHEN_THM], []) THEN
   SIMP_TAC list_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL, EVERY_MAP]
) THEN
ASM_SIMP_TAC std_ss [prove (``(BAG_INSERT x (BAG_INSERT (asl_star f P1 P2) sfb) =
                          (BAG_INSERT (asl_star f P1 P2) (BAG_INSERT x sfb)))``,
                 METIS_TAC[BAG_INSERT_commutes]),
    var_res_prop___asl_star___holfoot,
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star] THEN

`!x y sfb. (BAG_INSERT array_pred_1 (BAG_INSERT y
    (BAG_INSERT array_pred_3 sfb)) =
  BAG_INSERT y (BAG_INSERT array_pred_1 (BAG_INSERT array_pred_3 sfb)))` by
   METIS_TAC[BAG_INSERT_commutes] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
Q.UNABBREV_TAC `prog` THEN
MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_field_assign) THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
   FUPDATE_EQ]);


val HOLFOOT_COND_INFERENCE___prog_field_assign___interval =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_assign___interval",
``!tdata m b e c data wpb rpb t sfb progL Q.
((b <= m) /\ (m <= e)) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const b) 
            (var_res_exp_const e) ((t, REPLACE_ELEMENT c (m - b) tdata)::data)) sfb))
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_interval (var_res_exp_const b) (var_res_exp_const e) ((t, tdata)::data)) sfb))
   (asl_prog_block ((holfoot_prog_field_assign (var_res_exp_const m) t (var_res_exp_const c))::progL)) Q))``,


SIMP_TAC std_ss [holfoot_ap_data_interval___CONST] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_field_assign___array) THEN
ASM_SIMP_TAC arith_ss []);


val HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite",
``!wpb rpb e1 e1' e2 t sfb progL Q.

IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1') /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e1 e1') sfb))
   (asl_prog_block ((holfoot_prog_field_assign e1 t e2)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e1 e1') sfb))
   (asl_prog_block ((holfoot_prog_field_assign e1' t e2)::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_field_assign_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_field_assign_action] THEN

Tactical.REVERSE (`e1 (FST s) = e1' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_field_assign_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);



val HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite___value =
store_thm ("HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite___value",
``!wpb rpb e1 e1' e2 t sfb progL Q.

IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1') /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e1 e1') sfb))
   (asl_prog_block ((holfoot_prog_field_assign e2 t e1)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e1 e1') sfb))
   (asl_prog_block ((holfoot_prog_field_assign e2 t e1')::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_field_assign_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_field_assign_action] THEN

Tactical.REVERSE (`e1 (FST s) = e1' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_field_assign_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);





(*==================
 = new heap location
 ===================*)

val holfoot_new_action_def = Define `
   holfoot_new_action me v (tagL:holfoot_tag list) (s:holfoot_state) =
      if ~(var_res_sl___has_write_permission v (FST s)) \/
         ~(IS_SOME (me (FST s))) then NONE else
      let m = THE (me (FST s)) in
      SOME (\s'. ?n XL. ~(n = 0:num) /\ 
                (!m'. (n <= m' /\ (m' < n + m)) ==> ~(m' IN FDOM (SND s))) /\
                (LENGTH XL = m) /\
                (s' = ((FST s) |+ (v, n, var_res_write_permission),
                       (SND s) |++ MAP (\m'. (n+m', EL m' XL)) (COUNT_LIST m))))`;


val holfoot_new_action_1 = store_thm ("holfoot_new_action_1",
``holfoot_new_action (var_res_exp_const 1) v tagL s =
      if ~(var_res_sl___has_write_permission v (FST s)) then NONE else
      SOME (\s'. ?n X. ~(n = 0:num) /\ ~(n IN FDOM (SND s)) /\
                (s' = ((FST s) |+ (v, n, var_res_write_permission),
                       (SND s) |+ (n, X))))``,
SIMP_TAC list_ss [holfoot_new_action_def, LENGTH_EQ_NUM_compute, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, FUPDATE_LIST_THM, COUNT_LIST_compute,
   GSYM arithmeticTheory.ADD1, COND_RAND, COND_RATOR, LET_THM,
   var_res_exp_const_EVAL] THEN
`!n:num m:num. ((n <= m) /\ (m < SUC n)) = (n = m)` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss []);


val ASL_IS_LOCAL_ACTION___holfoot_new_action = store_thm (
"ASL_IS_LOCAL_ACTION___holfoot_new_action",
``!ne v tL. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne) ==>
ASL_IS_LOCAL_ACTION holfoot_separation_combinator (holfoot_new_action ne v tL)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   holfoot_new_action_def, COND_NONE_SOME_REWRITES, IN_ABS,
   SOME___holfoot_separation_combinator, SOME___VAR_RES_STACK_COMBINE,
   var_res_sl___has_write_permission_def, FMERGE_DEF, IN_UNION,
   FUNION_DEF, VAR_RES_STACK_IS_SEPARATE_def, LET_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`~(v IN FDOM (FST s2))` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
`?n. ne (FST s1) = SOME n` by (
   Cases_on `ne (FST s1)` THEN FULL_SIMP_TAC std_ss []) THEN
`ne (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC (FST s1) (FST s2)) = SOME n` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
   `vs SUBSET FDOM (FST s1)` by PROVE_TAC[IS_SOME_EXISTS] THEN
   Q.PAT_ASSUM `ne (FST s1) = X` (fn thm => REWRITE_TAC [GSYM thm]) THEN
   Q.PAT_ASSUM `!st1 st2. X ==> (ne st1 = ne st2)` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [FMERGE_DEF, SUBSET_DEF, IN_UNION,
      VAR_RES_STACK_COMBINE___MERGE_FUNC_def, COND_REWRITES]
) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM, FDOM_FUPDATE,
   DISJOINT_INSERT, FDOM_FUPDATE_LIST, DISJOINT_UNION_BOTH] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.EXISTS_TAC `n'` THEN
Q.EXISTS_TAC `XL` THEN
Q.ABBREV_TAC `upL = MAP (\m'. (n' + m',EL m' XL)) (COUNT_LIST n)` THEN
`ALL_DISTINCT (MAP FST upL) /\
 (!x. (n' <= x /\ x < n' + n) = MEM x (MAP FST upL))` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `upL` THEN
   SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF] THEN
   REPEAT STRIP_TAC THENL [
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on `n` THEN
      FULL_SIMP_TAC list_ss [COUNT_LIST_SNOC, MAP_MAP_o, combinTheory.o_DEF,
         MAP_SNOC, ALL_DISTINCT_SNOC, MEM_MAP, MEM_COUNT_LIST],


      ASM_SIMP_TAC list_ss [MEM_MAP, MEM_COUNT_LIST] THEN
      EQ_TAC THEN SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `x - n'` THEN
      DECIDE_TAC
  ]
) THEN
FULL_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   GSYM fmap_EQ_THM, FUNION_DEF,
   FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT, IN_UNION,
   FMERGE_DEF, EXTENSION,
   FDOM_FUPDATE_LIST, IN_LIST_TO_SET] THEN
REPEAT CONJ_TAC THENL [
   SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
      IN_LIST_TO_SET] THEN METIS_TAC[],

   GEN_TAC THEN Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [],
   GEN_TAC THEN Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [],

   GEN_TAC THEN Cases_on `MEM x (MAP FST upL)` THENL [
      `?x2. MEM (x, x2) upL` by ALL_TAC THEN1 (
          FULL_SIMP_TAC std_ss [MEM_MAP, PAIR_EXISTS_THM] THEN
          METIS_TAC[]
      ) THEN
      METIS_TAC [FUPDATE_LIST_APPLY___ALL_DISTINCT],

      ASM_SIMP_TAC std_ss [FUPDATE_LIST_APPLY_NOT_MEM, FUNION_DEF]
   ]
]);


val holfoot_prog_new_def = Define `
(holfoot_prog_new n v tL):holfoot_program =
asl_prog_prim_command (asl_pc_shallow_command (\f. holfoot_new_action n v tL))`;


val VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_new = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_new",
``!n c v vs tL. 
    (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs n) ==>

    VAR_RES_PROGRAM_IS_ABSTRACTION DISJOINT_FMAP_UNION (holfoot_prog_new n v tL)
    (var_res_prog_cond_best_local_action
      (var_res_prop DISJOINT_FMAP_UNION ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v) (var_res_exp_const c)|})
      (var_res_prop DISJOINT_FMAP_UNION ({|v|}, BAG_OF_SET (vs DELETE v))
        {|holfoot_ap_array (var_res_exp_var v) (var_res_exp_var_update (v, c) n)|}))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n)` by
  METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
ASM_SIMP_TAC std_ss [holfoot_prog_new_def, VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_REWRITE,
   ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM, GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_new_action,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   IS_SEPARATION_COMBINATOR___holfoot_separation_combinator] THEN
SIMP_TAC std_ss [var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, COND_RAND, COND_RATOR] THEN
REPEAT GEN_TAC THEN
MATCH_MP_TAC (prove (``
   (~c /\ (~c ==> x2)) ==> if c then x1 else x2``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___COND___REWRITE,
      FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      BAG_UNION_EMPTY, DISJ_IMP_THM, FORALL_AND_THM,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_ALL_DISTINCT_THM,
      BAG_ALL_DISTINCT_BAG_UNION, BAG_ALL_DISTINCT_BAG_OF_SET,
      BAG_DISJOINT_BAG_INSERT, BAG_IN_BAG_OF_SET, IN_DELETE,
      BAG_DISJOINT_EMPTY, SET_OF_BAG_UNION, SET_BAG_I,
      SET_OF_BAG_INSERT, BAG_OF_EMPTY] THEN
   CONSEQ_REWRITE_TAC ([], [
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
       VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_var_update], []) THEN
   SIMP_TAC std_ss [
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
      IN_UNION, IN_INSERT] THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___SUBSET THEN
   Q.EXISTS_TAC `vs` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_DELETE, IN_SING]
) THEN
SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
   holfoot_new_action_def, COND_RATOR, COND_RAND,
   fasl_order_THM2, var_res_best_local_action_def, IN_ABS,
   SOME___quant_best_local_action, NONE___quant_best_local_action,
   COND_EXPAND_IMP, var_res_exp_const_EVAL, LET_THM] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT] THEN
SIMP_TAC std_ss [
   var_res_prop___PROP___REWRITE,
   IS_SEPARATION_COMBINATOR___FINITE_MAP, IN_ABS,
   var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___PROPERTIES, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
   var_res_prop_stack_true_def, var_res_bool_proposition_def,
   var_res_stack_proposition_def, LET_THM, asl_emp_DISJOINT_FMAP_UNION,
   IN_SING, SOME___holfoot_separation_combinator,
   FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_2, FUNION_FEMPTY_1,
   PAIR_EXISTS_THM, PAIR_FORALL_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   DISJOINT_FMAP_UNION___REWRITE,
   var_res_prop_equal_unequal_EXPAND, var_res_prop_binexpression_def,
   COND_NONE_SOME_REWRITES, var_res_exp_const_EVAL] THEN
REPEAT GEN_TAC THEN CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE, IN_UNION,
      var_res_sl___has_write_permission_def, FMERGE_DEF,
      COND_REWRITES, VAR_RES_STACK_IS_SEPARATE_def,
      BAG_IN_BAG_OF_SET, IN_DELETE] THENL [

      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `v`) THEN
      ASM_SIMP_TAC std_ss [var_res_permission_THM2],

      `~(vs SUBSET (FDOM (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC x1'' x1')))` by
         METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL,
            IS_SOME_DEF] THEN
      POP_ASSUM MP_TAC THEN      
      Tactical.REVERSE (`vs SUBSET FDOM x1'` by ALL_TAC) THEN1 (
         FULL_SIMP_TAC std_ss [SUBSET_DEF, FMERGE_DEF, IN_UNION]
      ) THEN
      FULL_SIMP_TAC std_ss [var_res_sl___has_read_permission_def, SUBSET_DEF] THEN
      METIS_TAC[]
   ]
) THEN
STRIP_TAC THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
SIMP_TAC std_ss [SUBSET_DEF, IN_ABS, GSYM LEFT_FORALL_IMP_THM,
   asl_star_def, IN_SING, PAIR_EXISTS_THM,
   VAR_RES_COMBINATOR_REWRITE, DISJOINT_FMAP_UNION___REWRITE,
   FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_1, FUNION_FEMPTY_2,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN

`(var_res_exp_var v x1' = SOME c) /\ (v IN FDOM x1') /\ (FST (x1' ' v) = c)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_exp_var_def, COND_NONE_SOME_REWRITES, COND_RAND, COND_RATOR] THEN
   Q.PAT_ASSUM `v IN FDOM x1'` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN
`?nc. n x1 = SOME nc` by ALL_TAC THEN1 (
   Cases_on `n x1` THEN FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `upL = MAP (\m'. (n' + m',EL m' XL)) (COUNT_LIST nc)` THEN
`ALL_DISTINCT (MAP FST upL) /\
 (!x. (n' <= x /\ x < n' + nc) = MEM x (MAP FST upL))` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `upL` THEN
   SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF] THEN
   REPEAT STRIP_TAC THENL [
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on `nc` THEN
      FULL_SIMP_TAC list_ss [COUNT_LIST_SNOC, MAP_MAP_o, combinTheory.o_DEF,
         MAP_SNOC, ALL_DISTINCT_SNOC, MEM_MAP, MEM_COUNT_LIST],


      ASM_SIMP_TAC list_ss [MEM_MAP, MEM_COUNT_LIST] THEN
      EQ_TAC THEN SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `x - n'` THEN
      DECIDE_TAC
  ]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `x1' |+ (v,n',var_res_write_permission)` THEN
Q.EXISTS_TAC `FEMPTY |++ upL` THEN

ONCE_REWRITE_TAC [holfoot_separation_combinator___COMM] THEN
FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator,
   FDOM_FUPDATE, FAPPLY_FUPDATE_THM, FDOM_FEMPTY, FDOM_FUPDATE_LIST,
   var_res_sl___has_write_permission_def, IN_INSERT, NOT_IN_EMPTY,
   IN_DISJOINT, IN_SING, SOME___VAR_RES_STACK_COMBINE,
   FMERGE_DEF, IN_UNION, VAR_RES_STACK_IS_SEPARATE_def,
   IN_LIST_TO_SET, var_res_sl___has_read_permission_def] THEN
`~(v IN FDOM x1'')` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x. Y1 x /\ Y2 x ==> X x` (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [] THEN

SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss++EQUIV_EXTRACT_ss) [
   FMERGE_DEF, FDOM_FUPDATE, IN_UNION, IN_INSERT,
   FAPPLY_FUPDATE_THM, FUNION_DEF, FDOM_FEMPTY, NOT_IN_EMPTY,
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def, FDOM_FUPDATE_LIST,
   IN_LIST_TO_SET] THEN
REPEAT (GEN_TAC ORELSE CONJ_TAC) THENL [
   METIS_TAC[],

   Cases_on `x IN FDOM x1''` THEN ASM_SIMP_TAC std_ss [] THEN
   `~(x = v)` by PROVE_TAC[] THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
      COND_REWRITES],

   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [],

   Cases_on `MEM x (MAP FST upL)` THENL [
      FULL_SIMP_TAC std_ss [MEM_MAP, PAIR_EXISTS_THM] THEN
      METIS_TAC [FUPDATE_LIST_APPLY___ALL_DISTINCT],

      ASM_SIMP_TAC std_ss [FUPDATE_LIST_APPLY_NOT_MEM]
   ],

   `vs SUBSET FDOM x1'` by ALL_TAC THEN1 (
       FULL_SIMP_TAC std_ss [BAG_IN_BAG_OF_SET, IN_DELETE, SUBSET_DEF] THEN
       METIS_TAC[]
   ) THEN    
   `(var_res_exp_var_update (v,c) n) (x1' |+ (v,n',var_res_write_permission)) = n x1` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [var_res_exp_var_update_def] THEN
      MATCH_MP_TAC 
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ THEN
      Q.EXISTS_TAC `vs` THEN
      FULL_SIMP_TAC std_ss [FMERGE_DEF, FDOM_FUNION, IN_INTER, IN_UNION, FDOM_FUPDATE,
        SUBSET_DEF, IN_INSERT, var_res_state_var_update_def] THEN
      REPEAT STRIP_TAC THEN
      `FST ((x1' |+ (v,n',var_res_write_permission) |+
         (v,c,var_res_write_permission)) ' v') = FST (x1' ' v')` by ALL_TAC THEN1 (
         Cases_on `v' = v` THEN
         ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
      ) THEN
      ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      METIS_TAC[]
   ) THEN
   Q.UNABBREV_TAC `upL` THEN 
   ASM_SIMP_TAC list_ss [holfoot_ap_array___ALTERNATIVE_DEF2,
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
      LET_THM, IN_ABS, COUNT_LIST_def, FUPDATE_LIST_THM,
      var_res_exp_var_def, FDOM_FUPDATE_LIST, FDOM_FUPDATE, IN_INSERT,
      FDOM_FEMPTY, UNION_EMPTY, FAPPLY_FUPDATE_THM, MAP_MAP_o,
      combinTheory.o_DEF, LIST_TO_SET_MAP, COUNT_LIST___COUNT,
      GSYM IMAGE_COMPOSE, var_res_exp_prop_def, COND_RAND, COND_RATOR,
      var_res_prop_stack_true_REWRITE, asl_emp_DISJOINT_FMAP_UNION, IN_SING],

   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss []
]);



val HOLFOOT_COND_INFERENCE___prog_new =
store_thm ("HOLFOOT_COND_INFERENCE___prog_new",
``!wpb rpb v n tL c sfb progL Q.
((BAG_IN v wpb) /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) n) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_array (var_res_exp_var v) (var_res_exp_varlist_update [(v,c)] n) [])
         (BAG_IMAGE (var_res_prop_varlist_update [(v, c)]) sfb)))
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION
           (var_res_exp_var v) (var_res_exp_const c)) sfb))
   (asl_prog_block ((holfoot_prog_new n v tL)::progL)) Q))``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   var_res_prop_varlist_update_SING, GSYM holfoot_ap_array_def] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb)
         (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION (var_res_exp_var v)
               (var_res_exp_const c)) sfb)`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
MP_TAC (Q.SPECL [`n`, `c`, `v`, `SET_OF_BAG (BAG_UNION wpb rpb)`, `tL`] VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_new) THEN
ASM_REWRITE_TAC[] THEN
DISCH_TAC THEN POP_ASSUM (fn thm => EXISTS_TAC (rand (concl thm)) THEN REWRITE_TAC[thm]) THEN
SIMP_TAC std_ss [GSYM VAR_RES_COND_INFERENCE___prog_block,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN

HO_MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
ASM_SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET, SUBSET_DEF, IN_SET_OF_BAG,
  NOT_IN_EMPTY_BAG, BAG_IN_BAG_INSERT, IN_DELETE,
  VAR_RES_FRAME_SPLIT_NORMALISE, BAG_IN_BAG_OF_SET,
  VAR_RES_FRAME_SPLIT___FRAME] THEN    
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___equal_const___context_SING THEN
ASM_SIMP_TAC std_ss [BAG_IMAGE_EMPTY, IN_SET_OF_BAG, BAG_IN_BAG_UNION] THEN

MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY,
      BAG_IN_FINITE_BAG_IMAGE, GSYM LEFT_FORALL_IMP_THM, BAG_IN_BAG_INSERT,
      FINITE_BAG_THM, SET_OF_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG wpb UNION SET_OF_BAG rpb` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_DIFF, IN_INSERT,
      IN_SET_OF_BAG, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_IN_BAG_UNION]
) THEN
FULL_SIMP_TAC std_ss [BAG_IMAGE_FINITE_INSERT, BAG_UNION_INSERT, BAG_UNION_EMPTY,
   var_res_exp_varlist_update_SING]);



val HOLFOOT_COND_INFERENCE___prog_new_1 =
store_thm ("HOLFOOT_COND_INFERENCE___prog_new_1",
``!wpb rpb v c tL sfb progL Q.
(BAG_IN v wpb) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_points_to (var_res_exp_var v) FEMPTY)
         (BAG_IMAGE (var_res_prop_varlist_update [(v, c)]) sfb)))
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION
           (var_res_exp_var v) (var_res_exp_const c)) sfb))
   (asl_prog_block ((holfoot_prog_new (var_res_exp_const 1) v tL)::progL)) Q))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_new) THEN
ASM_SIMP_TAC list_ss [holfoot_ap_data_array_1, asl_trivial_cond_TF,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
   var_res_exp_varlist_update___const_EVAL, LIST_TO_FMAP_THM]);




val HOLFOOT_COND_INFERENCE___prog_new___exp_rewrite___count =
store_thm ("HOLFOOT_COND_INFERENCE___prog_new___exp_rewrite___count",
``!wpb rpb v ne ne' tL sfb progL Q.

IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne') ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION ne ne') sfb))
   (asl_prog_block ((holfoot_prog_new ne v tL)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION ne ne') sfb))
   (asl_prog_block ((holfoot_prog_new ne' v tL)::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_new_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   IS_SEPARATION_COMBINATOR___FINITE_MAP,
   ASL_IS_LOCAL_ACTION___holfoot_new_action] THEN

Tactical.REVERSE (`ne (FST s) = ne' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_new_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);





(*=======================
 = dispose heap location
 ========================*)


val holfoot_dispose_action_def = Define `
   holfoot_dispose_action me e (s:holfoot_state) =
      let loc_opt = e (FST s) in
      let m_opt   = me (FST s) in
      if (IS_NONE m_opt) then NONE else
      let m = (THE m_opt) in if (m = 0) then SOME {s} else
      if (IS_NONE loc_opt) then NONE else
      let loc = (THE loc_opt) in  (
      if (~((IMAGE (\n'. loc + n') (count m)) SUBSET FDOM (SND s)) \/ (loc = 0)) then NONE else
      (SOME {(FST s, DRESTRICT (SND s) (COMPL (IMAGE (\n'. loc + n') (count m))))}))`;


val ASL_IS_LOCAL_ACTION___holfoot_dispose_action = store_thm (
"ASL_IS_LOCAL_ACTION___holfoot_dispose_action",
``!ne e.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
ASL_IS_LOCAL_ACTION holfoot_separation_combinator (holfoot_dispose_action ne e)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   holfoot_dispose_action_def, COND_NONE_SOME_REWRITES, IN_ABS, LET_THM,
   SOME___holfoot_separation_combinator, NOT_NONE_IS_SOME, IN_SING,
   COND_NONE_SOME_REWRITES, ASL_IS_SUBSTATE_def] THEN
REPEAT STRIP_TAC THEN
`?n. ne (FST s1) = SOME n` by ALL_TAC THEN1 (
   Cases_on `ne (FST s1)` THEN FULL_SIMP_TAC std_ss []
) THEN
`(ne (FST s3) = ne (FST s1))` by METIS_TAC[
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT,
   VAR_RES_STACK_IS_SUBSTATE_INTRO, IS_SOME_EXISTS] THEN
Cases_on `n = 0` THEN (
   FULL_SIMP_TAC list_ss [COUNT_ZERO, IN_SING] THEN
   Q.PAT_ASSUM `v1 = X` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [IN_SING]
) THEN
`?ev. e (FST s1) = SOME ev` by ALL_TAC THEN1 (
   Cases_on `e (FST s1)` THEN FULL_SIMP_TAC std_ss []
) THEN
`(e (FST s3) = e (FST s1))` by METIS_TAC[
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT,
   VAR_RES_STACK_IS_SUBSTATE_INTRO, IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `loc_set =  IMAGE (\n'. n' + ev) (count n)` THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   FDOM_DRESTRICT, IN_DELETE, FUNION_DEF, DOMSUB_FAPPLY_THM,
   IN_UNION, IN_INTER, IN_COMPL, SUBSET_DEF, IN_UNION,
   DRESTRICT_DEF, DISJOINT_DEF, GSYM fmap_EQ_THM, EXTENSION,
   NOT_IN_EMPTY] THEN
METIS_TAC[]);



val holfoot_prog_dispose_def = Define `
(holfoot_prog_dispose ne e):holfoot_program =
asl_prog_prim_command (asl_pc_shallow_command (\f. holfoot_dispose_action ne e))`;


val holfoot_prog_dispose_0 = store_thm ("holfoot_prog_dispose_0",
``!e. (holfoot_prog_dispose (var_res_exp_const 0) e) = asl_prog_skip``,
SIMP_TAC std_ss [holfoot_prog_dispose_def, asl_pc_skip_def,
   asl_prog_skip_def, asl_prim_command_11, asl_prog_prim_command_11] THEN
SIMP_TAC std_ss [FUN_EQ_THM, asla_skip_def, holfoot_dispose_action_def,
   var_res_exp_const_EVAL, LET_THM]);

val VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_dispose = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_dispose",
``!n e vs.
    (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs n) ==>

    VAR_RES_PROGRAM_IS_ABSTRACTION DISJOINT_FMAP_UNION (holfoot_prog_dispose n e)
    (var_res_prog_cond_best_local_action
      (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_OF_SET vs)
        {|holfoot_ap_array e n|})
      (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_OF_SET vs)
        EMPTY_BAG))``,

REPEAT STRIP_TAC THEN
`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS n)` by 
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
ASM_SIMP_TAC std_ss [
   holfoot_prog_dispose_def, VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_REWRITE,
   ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM, GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_dispose_action,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
SIMP_TAC std_ss [var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, COND_RAND, COND_RATOR] THEN
MATCH_MP_TAC (prove (``
   (~c /\ (~c ==> x2)) ==> if c then x1 else x2``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
      BAG_UNION_EMPTY, IS_SEPARATION_COMBINATOR___FINITE_MAP, BAG_ALL_DISTINCT_THM,
      SET_BAG_I, BAG_ALL_DISTINCT_BAG_OF_SET,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array]
) THEN

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Cases_on `holfoot_dispose_action n e s` THENL [
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM2, var_res_best_local_action_def,
      NONE___quant_best_local_action, IN_ABS, holfoot_dispose_action_def,
      LET_THM, COND_NONE_SOME_REWRITES, COND_NONE_SOME_REWRITES3,
      var_res_prop___PROP_INSERT, var_res_exp_const_EVAL,
      GSYM LEFT_FORALL_IMP_THM] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_OF_SET, var_res_bigstar_REWRITE,
      asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      var_res_sl___has_read_permission_def,
      var_res_prop_stack_true_def, var_res_bool_proposition_def,
      var_res_stack_proposition_def, asl_emp_DISJOINT_FMAP_UNION,
      IN_ABS, IN_SING, DISJOINT_FMAP_UNION___FEMPTY, GSYM SUBSET_DEF] THEN
   ASM_SIMP_TAC std_ss [holfoot_ap_array___ALTERNATIVE_DEF2, LET_THM, IN_ABS,
      GSYM RIGHT_FORALL_IMP_THM, NOT_NONE_IS_SOME, var_res_exp_prop_def] THEN
   REPEAT GEN_TAC THEN
   Cases_on `SOME s = holfoot_separation_combinator (SOME s0) (SOME x)` THEN ASM_REWRITE_TAC[] THEN
   Cases_on `vs SUBSET FDOM (FST x)` THEN ASM_REWRITE_TAC[] THEN
   `IS_SOME (e (FST x)) /\ IS_SOME (n (FST x))` by
      METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL] THEN
   FULL_SIMP_TAC std_ss [SOME___holfoot_separation_combinator] THEN
   `(e (FST s) = e (FST x)) /\ (n (FST s) = n (FST x))` by METIS_TAC[
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT,
      VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   `?ev. e (FST x) = SOME ev` by PROVE_TAC[IS_SOME_EXISTS] THEN
   `?nv. n (FST x) = SOME nv` by PROVE_TAC[IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_DISJOINT,
      COND_NONE_SOME_REWRITES3] THEN   
   Q.ABBREV_TAC `locS = (IMAGE (\n'. ev + n') (count nv))` THEN
   Cases_on `FDOM (SND x) = locS` THEN ASM_SIMP_TAC std_ss [SUBSET_UNION],


   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM2, var_res_best_local_action_def,
      SOME___quant_best_local_action, IN_ABS, holfoot_dispose_action_def,
      LET_THM, COND_NONE_SOME_REWRITES, NOT_NONE_IS_SOME,
      var_res_exp_const_EVAL, COND_NONE_SOME_REWRITES3,
      COND_NONE_SOME_REWRITES2] THEN
   STRIP_TAC THEN
   DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_ABS, asl_star_def,
      var_res_prop___PROP_INSERT] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
      IS_SEPARATION_COMBINATOR___FINITE_MAP, NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_OF_SET, var_res_bigstar_REWRITE,
      asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      var_res_sl___has_read_permission_def,
      var_res_prop_stack_true_def, var_res_bool_proposition_def,
      var_res_stack_proposition_def, asl_emp_DISJOINT_FMAP_UNION,
      IN_ABS, IN_SING, DISJOINT_FMAP_UNION___FEMPTY, GSYM SUBSET_DEF] THEN
   ASM_SIMP_TAC std_ss [PAIR_EXISTS_THM, SOME___holfoot_separation_combinator,
      FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_1, holfoot_ap_points_to_def,
      IN_ABS, LET_THM, holfoot_ap_array___ALTERNATIVE_DEF2, var_res_exp_prop_def] THEN
   REPEAT STRIP_TAC THEN
   `n (FST s) = n (FST x'')` by METIS_TAC[
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT,
      VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   `?nv. n (FST x'') = SOME nv` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss [] THEN
   Cases_on `nv = 0` THEN1 (
      FULL_SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE, asl_emp_DISJOINT_FMAP_UNION,
        IN_SING, FUNION_FEMPTY_2] THEN
      Q.PAT_ASSUM `X = x` (ASSUME_TAC o GSYM) THEN
      FULL_SIMP_TAC std_ss [IN_SING] THEN
      METIS_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL,
                VAR_RES_STACK_COMBINE___COMM]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `X = x` (ASSUME_TAC o GSYM) THEN
   `e (FST s) = e (FST x'')` by METIS_TAC[
      IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT,
      VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   `?ev. e (FST x'') = SOME ev` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC (std_ss++CONJ_ss) [IN_SING] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `FST x''` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL] THEN
   CONJ_TAC THEN1 METIS_TAC[VAR_RES_STACK_COMBINE___COMM] THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION] THEN
   FULL_SIMP_TAC std_ss [FDOM_DOMSUB, FUNION_DEF, DOMSUB_FAPPLY_THM,
      IN_UNION, IN_DELETE, IN_DISJOINT, IN_SING, DRESTRICT_DEF, IN_INTER,
      IN_COMPL] THEN
   METIS_TAC[]
]);





val HOLFOOT_COND_INFERENCE___prog_dispose___SIMPLE =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose___SIMPLE",
``!wpb rpb e n sfb progL Q.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) n) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb) sfb)
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_array e n) sfb))
   (asl_prog_block ((holfoot_prog_dispose n e)::progL)) Q))``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND DISJOINT_FMAP_UNION (wpb,rpb)
         (BAG_INSERT (holfoot_ap_array e n) sfb)`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
MP_TAC (Q.SPECL [`n`, `e`, `(SET_OF_BAG (BAG_UNION wpb rpb))`] VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_dispose) THEN
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT] THEN
DISCH_TAC THEN POP_ASSUM (fn thm => EXISTS_TAC (rand (concl thm)) THEN REWRITE_TAC[thm]) THEN
SIMP_TAC std_ss [GSYM VAR_RES_COND_INFERENCE___prog_block,
   IS_SEPARATION_COMBINATOR___FINITE_MAP] THEN
HO_MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
ASM_SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET, SET_BAG_I, SUBSET_REFL,
   VAR_RES_FRAME_SPLIT_NORMALISE] THEN
REWRITE_TAC[VAR_RES_FRAME_SPLIT___FRAME] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY,
      BAG_IN_FINITE_BAG_IMAGE, GSYM LEFT_FORALL_IMP_THM, BAG_IN_BAG_INSERT,
      FINITE_BAG_THM, DISJ_IMP_THM, FORALL_AND_THM,
      BAG_OF_EMPTY, DIFF_EMPTY, GSYM SET_OF_BAG_UNION,
      BAG_DIFF_EMPTY]
) THEN
FULL_SIMP_TAC std_ss [BAG_UNION_EMPTY]);





val HOLFOOT_COND_INFERENCE___prog_dispose =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose",
``!wpb rpb e n data sfb progL Q.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) n) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb) sfb)
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_data_array e n data) sfb))
   (asl_prog_block ((holfoot_prog_dispose n e)::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP) THEN
Q.EXISTS_TAC `var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
                  (BAG_INSERT (holfoot_ap_array e n) sfb)` THEN
Tactical.REVERSE CONJ_TAC THEN1 METIS_TAC[HOLFOOT_COND_INFERENCE___prog_dispose___SIMPLE] THEN

SIMP_TAC (std_ss++CONJ_ss) [COND_PROP___IMP_def, var_res_prop___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT, IN_ABS] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array]
) THEN
Q.EXISTS_TAC `s1` THEN Q.EXISTS_TAC `s2` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[holfoot_ap_data_array___ELIM_DATA___COMPLETE]);




val HOLFOOT_COND_INFERENCE___prog_dispose_1 =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose_1",
``!wpb rpb e L sfb progL Q.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb) sfb)
    (asl_prog_block progL) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (holfoot_ap_points_to e L) sfb))
   (asl_prog_block ((holfoot_prog_dispose (var_res_exp_const 1) e)::progL)) Q))``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP) THEN
Q.EXISTS_TAC `var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
                  (BAG_INSERT (holfoot_ap_array e (var_res_exp_const 1)) sfb)` THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   MATCH_MP_TAC (MP_CANON HOLFOOT_COND_INFERENCE___prog_dispose___SIMPLE) THEN
   ASM_SIMP_TAC std_ss [
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN
SIMP_TAC (std_ss++CONJ_ss) [COND_PROP___IMP_def, var_res_prop___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT, IN_ABS] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[VAR_RES_IS_STACK_IMPRECISE___USED_VARS___holfoot_ap_array,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL]
) THEN
Q.EXISTS_TAC `s1` THEN Q.EXISTS_TAC `s2` THEN
ASM_SIMP_TAC std_ss [] THEN

`IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)` by
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
`count 1 = {0}` by ALL_TAC THEN1 (
   `1 = SUC 0` by DECIDE_TAC THEN
   ASM_REWRITE_TAC[COUNT_SUC, COUNT_ZERO]
) THEN
Q.PAT_ASSUM `X IN holfoot_ap_points_to e L` MP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_ap_array___ALTERNATIVE_DEF2, IN_ABS, LET_THM,
   COUNT_SUC, IMAGE_INSERT, IMAGE_EMPTY, holfoot_ap_points_to_def,
   var_res_exp_prop_def, var_res_exp_const_EVAL]);






val HOLFOOT_COND_INFERENCE___prog_dispose___FRAME =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose___FRAME",
``!wpb rpb e n sfb progL Q.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) n) ==>
((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb) sfb)
    (asl_prog_block 
       ((var_res_prog_cond_best_local_action
            (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_UNION wpb rpb)
               {| holfoot_ap_array e n |})
            (var_res_prop DISJOINT_FMAP_UNION (EMPTY_BAG, BAG_UNION wpb rpb)
                EMPTY_BAG))::progL)) Q) ==>

(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb) sfb)
   (asl_prog_block ((holfoot_prog_dispose n e)::progL)) Q))``,


SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb rpb)`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE,
      var_res_prop___COND___REWRITE]
) THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
MP_TAC (Q.SPECL [`n`, `e`, `(SET_OF_BAG (BAG_UNION wpb rpb))`] VAR_RES_PROGRAM_IS_ABSTRACTION___holfoot_prog_dispose) THEN
FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_SET] THEN
DISCH_TAC THEN POP_ASSUM (fn thm => EXISTS_TAC (rand (concl thm)) THEN REWRITE_TAC[thm]) THEN
ASM_SIMP_TAC std_ss []);




val HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite",
``!wpb rpb ne e e' sfb progL Q.

IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e') ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e e') sfb))
   (asl_prog_block ((holfoot_prog_dispose ne e)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION e e') sfb))
   (asl_prog_block ((holfoot_prog_dispose ne e')::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_dispose_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_dispose_action] THEN

Tactical.REVERSE (`e (FST s) = e' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_dispose_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);


val HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite___count =
store_thm ("HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite___count",
``!wpb rpb e ne ne' sfb progL Q.

IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS ne') ==>

((VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION ne ne') sfb))
   (asl_prog_block ((holfoot_prog_dispose ne e)::progL)) Q) = 
(VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION
   (var_res_prop DISJOINT_FMAP_UNION (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal DISJOINT_FMAP_UNION ne ne') sfb))
   (asl_prog_block ((holfoot_prog_dispose ne' e)::progL)) Q))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM THEN

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [holfoot_prog_dispose_def, 
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   GSYM holfoot_separation_combinator_def,
   ASL_IS_LOCAL_ACTION___holfoot_dispose_action] THEN

Tactical.REVERSE (`ne (FST s) = ne' (FST s)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [holfoot_dispose_action_def, LET_THM]
) THEN

Q.PAT_ASSUM `s IN X` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS,
   IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]);






(*******************************************************
 * PROCCALL FREE
 ******************************************************)


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_SIMPLE_REWRITES =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_SIMPLE_REWRITES",
``asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (holfoot_prog_dispose n e) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (holfoot_prog_new n v tL) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (holfoot_prog_field_assign e1 t e2) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (holfoot_prog_field_lookup v e t)``,

SIMP_TAC std_ss [holfoot_prog_dispose_def,
   holfoot_prog_new_def, holfoot_prog_field_lookup_def,
   holfoot_prog_field_assign_def,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_REWRITES =
  save_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_REWRITES",
  LIST_CONJ [
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_SIMPLE_REWRITES])


val _ = export_theory();
